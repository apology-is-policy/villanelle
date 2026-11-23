//! `vn2`: the command line of the v2 oracle.

use std::process::ExitCode;
use villanelle_v2::host::{Arithmetic, Host, Script};
use villanelle_v2::int::Int;
use villanelle_v2::oracle::{Config, End, Value, run};
use villanelle_v2::{
    certificate, check, codegen, erased, expand, fuzz, load, load_surface, script, surface, text,
};

const USAGE: &str = "\
vn2 test FILE...                          carry out the directives of core or Rails files
vn2 check FILE... [--certificates]        check core or Rails files in the Phase 3 checker;
                                          with --certificates, print the certificate text
vn2 validate FILE...                      read certificate texts and validate them in the kernel
vn2 format FILE... [--write | --check]    format Rails files into canonical Rails glyph form
vn2 expand FILE                           expand decisions on defined controls (Theorem 4)
vn2 emit-llvm FILE [--usize 32|64]        emit Phase 4 typed LLVM IR for a core or Rails file
vn2 emit-c FILE [--usize 32|64]           emit Phase 4 typed C ABI header for a core or Rails file
vn2 run FILE ENTRY [VALUE...] [OPTIONS]   run one control in the oracle
vn2 print FILE                            print a core or Rails program in the core glyph form
vn2 fuzz [OPTIONS]                        try generated programs in reader, oracle and checker

Options of `run`:
  --arithmetic   the host computes the checked arithmetic of the prelude
  --usize 32     the greatest usize is 2^32 - 1 (default: 2^64 - 1)
  --fuel N       stop after N steps (default: 1000000)
  --erased       run under the erased semantics, which checks nothing

Options of `fuzz`:
  --seed N       the first seed (default: 1); a program is a function of its seed
  --count N      the number of seeds (default: 100)
  --mutants      try the mutants of each program too
  --native       compile each accepted program and run it too (needs clang)
  --show         print the programs and try nothing
  --out DIR      write each finding to a file in DIR
  --fuel N       steps of one run (default: 200000)
  --mutant-fuel N  steps of one run of a mutant (default: 20000)
  --seconds N    time for the checker on one program (default: 20)
";

fn is_core_file(path: &str) -> bool {
    path.ends_with(".core")
}

fn read(path: &str) -> Result<String, String> {
    std::fs::read_to_string(path).map_err(|error| format!("{path}: {error}"))
}

fn test(files: &[String]) -> Result<bool, String> {
    let mut failed = 0;
    let mut runs = 0;
    let mut compared = 0;
    for path in files {
        let source = read(path)?;
        let report = if is_core_file(path) {
            script::check(&source)
        } else {
            script::check_surface(&source)
        };
        runs += report.runs;
        compared += report.compared;
        for failure in &report.failures {
            println!("{path}: {failure}");
        }
        failed += report.failures.len();
    }
    println!(
        "{} files, {runs} runs, {compared} of them compared with the erased semantics, {failed} failures",
        files.len()
    );
    Ok(failed == 0)
}

fn value(text: &str) -> Result<Value, String> {
    match text {
        "true" => Ok(Value::Bool(true)),
        "false" => Ok(Value::Bool(false)),
        digits => Int::parse(digits)
            .map(Value::Int)
            .ok_or(format!("`{digits}` is not a value")),
    }
}

fn run_one(arguments: &[String]) -> Result<bool, String> {
    let [path, entry, rest @ ..] = arguments else {
        return Err(USAGE.to_string());
    };
    let source = read(path)?;
    let program = if is_core_file(path) {
        load(&source)?
    } else {
        load_surface(&source)?
    };
    let mut config = Config::default();
    let mut arithmetic = false;
    let mut erase = false;
    let mut values = Vec::new();
    let mut rest = rest.iter();
    while let Some(argument) = rest.next() {
        match argument.as_str() {
            "--arithmetic" => arithmetic = true,
            "--erased" => erase = true,
            "--usize" => {
                let bits = rest
                    .next()
                    .and_then(|bits| bits.parse().ok())
                    .ok_or("--usize 32 or 64")?;
                config.usize_max = Config::with_usize_bits(bits).usize_max;
            }
            "--fuel" => {
                config.fuel = rest
                    .next()
                    .and_then(|fuel| fuel.parse().ok())
                    .ok_or("--fuel N")?;
            }
            other => values.push(value(other)?),
        }
    }
    let mut host = Arithmetic(Script::default());
    let host: &mut dyn Host = if arithmetic { &mut host } else { &mut host.0 };
    if erase {
        let outcome = erased::run(&program, entry, values, host, &config);
        for event in &outcome.trace {
            println!("{event}");
        }
        println!("{}", outcome.end);
        return Ok(matches!(outcome.end, erased::End::Done { .. }));
    }
    let outcome = run(&program, entry, values, host, &config);
    for event in &outcome.trace {
        println!("{event}");
    }
    println!("{}", outcome.end);
    Ok(matches!(outcome.end, End::Done { .. }))
}

fn check_files(arguments: &[String]) -> Result<bool, String> {
    let mut show_certificates = false;
    let mut files = Vec::new();
    for argument in arguments {
        if argument == "--certificates" {
            show_certificates = true;
        } else {
            files.push(argument);
        }
    }
    if files.is_empty() {
        return Err(USAGE.to_string());
    }
    // With `--certificates` the output is one certificate text, and what is
    // not a part of it is on lines that begin with `#`.
    let note = if show_certificates { "# " } else { "" };
    if show_certificates {
        println!("{}", certificate::HEADER);
    }
    let mut failed = 0usize;
    let mut total_certificates = 0usize;
    for path in &files {
        let source = read(path)?;
        let program = if is_core_file(path) {
            load(&source)
        } else {
            load_surface(&source)
        };
        let report = program
            .and_then(|program| check::check(&program).map_err(|error| error.to_string()))
            .and_then(|report| {
                let mut text = String::new();
                if show_certificates {
                    report.write_certificates(&mut text)?;
                }
                Ok((report.certificates.len(), text))
            });
        match report {
            Ok((certificates, text)) => {
                total_certificates += certificates;
                if show_certificates {
                    println!("# {path}");
                    print!("{text}");
                }
            }
            Err(error) => {
                println!("{note}{path}: {error}");
                failed += 1;
            }
        }
    }
    println!(
        "{note}{} files checked, {total_certificates} certificates validated, {failed} failures",
        files.len()
    );
    Ok(failed == 0)
}

fn validate_files(files: &[String]) -> Result<bool, String> {
    let mut failed = 0usize;
    let mut total_certificates = 0usize;
    for path in files {
        match certificate::validate(&read(path)?) {
            Ok(certificates) => total_certificates += certificates,
            Err(error) => {
                println!("{path}: {error}");
                failed += 1;
            }
        }
    }
    println!(
        "{} texts read, {total_certificates} certificates validated, {failed} failures",
        files.len()
    );
    Ok(failed == 0)
}

fn format_files(arguments: &[String]) -> Result<bool, String> {
    let mut write_in_place = false;
    let mut check_only = false;
    let mut files = Vec::new();
    for argument in arguments {
        match argument.as_str() {
            "--write" => write_in_place = true,
            "--check" => check_only = true,
            _ => files.push(argument),
        }
    }
    if files.is_empty() || (write_in_place && check_only) {
        return Err(USAGE.to_string());
    }
    let mut ok = true;
    for path in &files {
        let source = read(path)?;
        let formatted = match surface::format(&source) {
            Ok(text) => text,
            Err(error) => {
                println!("{path}:{error}");
                ok = false;
                continue;
            }
        };
        if check_only {
            if formatted != source {
                println!("{path}: not in canonical Rails form");
                ok = false;
            }
        } else if write_in_place {
            if formatted != source {
                std::fs::write(path, formatted).map_err(|error| format!("{path}: {error}"))?;
            }
        } else {
            print!("{formatted}");
        }
    }
    Ok(ok)
}

fn parse_emit_args(arguments: &[String]) -> Result<(&str, u32), String> {
    match arguments {
        [path] => Ok((path, 64)),
        [path, flag, bits] if flag == "--usize" => {
            let b: u32 = bits.parse().map_err(|_| "--usize 32 or 64".to_string())?;
            if b != 32 && b != 64 {
                return Err("--usize 32 or 64".to_string());
            }
            Ok((path, b))
        }
        _ => Err(USAGE.to_string()),
    }
}

/// `vn2 fuzz [--seed N] [--count N] [--mutants] [--show] [--out DIR]`.
fn fuzz_command(arguments: &[String]) -> Result<bool, String> {
    let mut first = 1u64;
    let mut count = 100u64;
    let mut show = false;
    let mut out: Option<String> = None;
    let mut options = fuzz::Options::default();
    let mut rest = arguments.iter();
    while let Some(argument) = rest.next() {
        let mut number = |what: &str| -> Result<u64, String> {
            rest.next()
                .and_then(|text| text.parse().ok())
                .ok_or_else(|| format!("`{what}` takes a number"))
        };
        match argument.as_str() {
            "--seed" => first = number("--seed")?,
            "--count" => count = number("--count")?,
            "--fuel" => options.fuel = number("--fuel")?,
            "--mutant-fuel" => options.mutant_fuel = number("--mutant-fuel")?,
            "--seconds" => options.seconds = number("--seconds")?,
            "--mutants" => options.mutants = true,
            "--native" => options.native = true,
            "--show" => show = true,
            "--out" => out = Some(rest.next().ok_or("`--out` takes a directory")?.clone()),
            _ => return Err(USAGE.to_string()),
        }
    }
    if show {
        for seed in first..first + count {
            println!("┄ seed {seed}\n{}", fuzz::program_of(seed).print());
        }
        return Ok(true);
    }
    // A panic of the checker is a finding, and is reported as one.
    std::panic::set_hook(Box::new(|_| {}));
    let report = fuzz::campaign(first, count, &options);
    println!("{}", report.summary());
    for finding in &report.findings {
        println!("seed {} {}: {}", finding.seed, finding.kind, finding.detail);
    }
    if let Some(directory) = out {
        std::fs::create_dir_all(&directory).map_err(|error| format!("{directory}: {error}"))?;
        for (index, finding) in report.findings.iter().enumerate() {
            let path = format!(
                "{directory}/seed{}-{}-{index}.core",
                finding.seed, finding.kind
            );
            let text = format!(
                "┄ vn2 fuzz --seed {} --count 1: {}\n┄ {}\n{}",
                finding.seed,
                finding.kind,
                finding.detail.replace('\n', " "),
                finding.program
            );
            std::fs::write(&path, text).map_err(|error| format!("{path}: {error}"))?;
        }
    }
    Ok(report.findings.is_empty())
}

fn main() -> ExitCode {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let result = match arguments.split_first() {
        Some((command, rest)) if command == "fuzz" => fuzz_command(rest),
        Some((command, rest)) if command == "test" && !rest.is_empty() => test(rest),
        Some((command, rest)) if command == "check" && !rest.is_empty() => check_files(rest),
        Some((command, rest)) if command == "validate" && !rest.is_empty() => validate_files(rest),
        Some((command, rest)) if command == "format" && !rest.is_empty() => format_files(rest),
        Some((command, [path])) if command == "expand" => read(path).and_then(|source| {
            let tree = if is_core_file(path) {
                text::parse(&source).map_err(|error| error.to_string())?
            } else {
                surface::elaborate(&source).map_err(|error| error.to_string())?
            };
            let expanded = expand::expand(&tree).map_err(|error| error.to_string())?;
            print!("{}", expanded.print());
            Ok(true)
        }),
        Some((command, rest)) if command == "emit-llvm" => {
            parse_emit_args(rest).and_then(|(path, usize_bits)| {
                let source = read(path)?;
                let program = if is_core_file(path) {
                    load(&source)?
                } else {
                    load_surface(&source)?
                };
                print!("{}", codegen::emit_llvm(&program, usize_bits));
                Ok(true)
            })
        }
        Some((command, rest)) if command == "emit-c" => {
            parse_emit_args(rest).and_then(|(path, usize_bits)| {
                let source = read(path)?;
                let program = if is_core_file(path) {
                    load(&source)?
                } else {
                    load_surface(&source)?
                };
                print!("{}", codegen::emit_c_header(&program, usize_bits));
                Ok(true)
            })
        }
        Some((command, rest)) if command == "run" => run_one(rest),
        Some((command, [path])) if command == "print" => read(path).and_then(|source| {
            let tree = if is_core_file(path) {
                text::parse(&source).map_err(|error| error.to_string())?
            } else {
                surface::elaborate(&source).map_err(|error| error.to_string())?
            };
            print!("{}", tree.print());
            Ok(true)
        }),
        _ => Err(USAGE.to_string()),
    };
    match result {
        Ok(true) => ExitCode::SUCCESS,
        Ok(false) => ExitCode::FAILURE,
        Err(message) => {
            eprintln!("{message}");
            ExitCode::from(2)
        }
    }
}
