//! Fuzzing with generated programs: the reader, the two semantics, the
//! checker and, when asked, the compiled code are held against each other on
//! programs that are valid by construction ([`crate::generate::valid`]) and
//! on their mutants ([`crate::mutate`]).
//!
//! What must hold, and what a **finding** is when it does not:
//!
//! | Kind | Must hold |
//! | --- | --- |
//! | `reader` | The printed program reads back to the same text |
//! | `resolve` | A valid program resolves |
//! | `stuck` | No run of a valid program is stuck in the oracle |
//! | `host`, `fuel` | The host has an answer for every call, and a run ends |
//! | `erased` | The erased semantics gives the same observation ([R1] to [R3]) |
//! | `rejected` | The checker accepts a valid program ([N3], [J5]) |
//! | `panic`, `timeout` | The checker answers, and in time |
//! | `unsound` | A mutant that the checker accepts has no stuck run |
//! | `native` | The compiled program, at `-O0` and `-O2`, ends as the oracle does and with the same trace ([R1] to [R3]) |
//!
//! Every program is a function of its seed, so a finding is reproduced by
//! its seed alone.

use crate::check;
use crate::codegen::{NativeRunSpec, run_native_batch, run_native_counted};
use crate::counts::{self, Counts};
use crate::differential::{Verdict, compare};
use crate::erased;
use crate::generate::{Coverage, entry_runs, valid, valid_borrows, valid_data};
use crate::host::{Arithmetic, Seeded};
use crate::mutate::{Kind, mutate};
use crate::oracle::{self, Config, End, HOST_SCOPE, RuntimeStep, Value};
use crate::rng::{Rng, mix};
use crate::{resolve, text};
use std::collections::{BTreeMap, BTreeSet};
use std::sync::mpsc;
use std::time::{Duration, Instant};

#[derive(Clone, Debug)]
pub struct Options {
    /// Whether the checker is asked about each program.
    pub checker: bool,
    /// Whether the mutants of each program are tried too.
    pub mutants: bool,
    pub fuel: u64,
    /// The steps of one run of a mutant. A mutant that goes on without end
    /// uses all of them in every run, so they are fewer.
    pub mutant_fuel: u64,
    /// Entries for each control, on each target.
    pub entries: usize,
    /// Hosts for each entry.
    pub hosts: u64,
    /// How long the checker may take on one program.
    pub seconds: u64,
    /// Whether an accepted program is compiled and run too. Needs `clang`.
    pub native: bool,
    /// The slice whose constructs the programs have: 1, or 2 for data.
    pub slice: u8,
}

impl Default for Options {
    fn default() -> Options {
        Options {
            checker: true,
            mutants: false,
            fuel: 200_000,
            mutant_fuel: 20_000,
            entries: 6,
            hosts: 2,
            seconds: 20,
            native: false,
            slice: 1,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Finding {
    pub seed: u64,
    pub kind: &'static str,
    pub detail: String,
    /// The program, or the mutant, in the core text form.
    pub program: String,
}

/// What became of the mutants of one kind.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct KindCount {
    pub mutants: u64,
    /// Those that `resolve` refuses.
    pub refused: u64,
    /// Those that the checker rejects, and of them those with a stuck run.
    pub rejected: u64,
    pub rejected_stuck: u64,
    /// Those that the checker accepts and that no tried run leaves stuck.
    pub survived: u64,
}

#[derive(Clone, Debug, Default)]
pub struct Report {
    pub programs: u64,
    pub runs: u64,
    /// The runs that ended in a fault that left the entry, and those that
    /// ended with `terminate n`.
    pub faulted: u64,
    pub terminated: u64,
    pub accepted: u64,
    /// Runs of compiled programs that ended as the oracle's did.
    pub native_runs: u64,
    /// The allocations that the compiled runs made. A run that does not
    /// release every one of its own does not end as the oracle's ([R4]).
    pub native_allocations: u64,
    pub mutants: u64,
    /// Mutants that `resolve` refuses.
    pub refused: u64,
    /// Mutants that the checker rejects.
    pub rejected: u64,
    /// Rejected mutants for which a stuck run was found as well.
    pub rejected_stuck: u64,
    /// Mutants that the checker accepts and that no tried run leaves stuck.
    pub survived: u64,
    /// The same counts for each kind of mutation.
    pub kinds: BTreeMap<Kind, KindCount>,
    pub coverage: Coverage,
    /// The slice whose constructs the campaign is to reach.
    pub slice: u8,
    pub rules: BTreeSet<&'static str>,
    /// The places that hosts lent in the runs, by the last step to them:
    /// a whole argument, a field, the field of a variant, an element, the
    /// value or the key of a map.
    pub host_places: BTreeMap<&'static str, u64>,
    /// The work of the search in every check that gave an answer in time.
    pub search: Counts,
    pub findings: Vec<Finding>,
}

/// What the checker says of a program, given as text so that the answer can
/// be awaited from another thread.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Checked {
    Accepted,
    Rejected(String),
    Panicked(String),
    TimedOut,
}

pub fn checker(source: &str, seconds: u64) -> Checked {
    checker_with_counts(source, seconds).0
}

/// As [`checker`], with the work of the search. A check runs on a thread of
/// its own, so the counts of that thread are the counts of the check. The
/// check ends when its time is up ([`counts::set_deadline`]): one that went
/// on after nobody waits for it would take the processor, and memory where
/// its diagrams grow.
pub fn checker_with_counts(source: &str, seconds: u64) -> (Checked, Counts) {
    let (sender, receiver) = mpsc::channel();
    let source = source.to_string();
    std::thread::spawn(move || {
        counts::set_deadline(Some(Instant::now() + Duration::from_secs(seconds)));
        let answer = std::panic::catch_unwind(|| match crate::load(&source) {
            Ok(program) => match check::check(&program) {
                Ok(_) => Checked::Accepted,
                Err(error) => Checked::Rejected(error.to_string()),
            },
            Err(error) => Checked::Rejected(format!("not resolved: {error}")),
        });
        let answer = answer.unwrap_or_else(|panic| {
            if panic.is::<counts::OutOfTime>() {
                return Checked::TimedOut;
            }
            let message = panic
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| panic.downcast_ref::<&str>().map(|text| (*text).to_string()))
                .unwrap_or_else(|| "a panic without a message".to_string());
            Checked::Panicked(message)
        });
        // The work of a check that gave no answer depends on the clock, and
        // is not counted.
        let work = if answer == Checked::TimedOut {
            Counts::default()
        } else {
            counts::now()
        };
        let _ = sender.send((answer, work));
    });
    // The check ends itself where the search asks for the time; this is for
    // a stretch of it that does not ask.
    receiver
        .recv_timeout(Duration::from_secs(seconds.saturating_add(30)))
        .unwrap_or((Checked::TimedOut, Counts::default()))
}

/// The answer of the checker, with its work added to the report.
fn checked(report: &mut Report, source: &str, seconds: u64) -> Checked {
    let (answer, work) = checker_with_counts(source, seconds);
    report.search = report.search.plus(&work);
    answer
}

/// The answers of a host as a script writes them.
fn answers(answers: &[(String, crate::host::Answer)]) -> String {
    let shown: Vec<String> = answers
        .iter()
        .map(|(control, answer)| {
            if answer.payload.is_empty() {
                format!("{control} -> {}", answer.alternative)
            } else {
                format!(
                    "{control} -> {} {{{}}}",
                    answer.alternative,
                    show(&answer.payload)
                )
            }
        })
        .collect();
    shown.join("; ")
}

fn show(arguments: &[oracle::Value]) -> String {
    let shown: Vec<String> = arguments.iter().map(ToString::to_string).collect();
    shown.join(", ")
}

fn configs(fuel: u64) -> [(u32, Config); 2] {
    [
        (
            64,
            Config {
                fuel,
                ..Config::default()
            },
        ),
        (
            32,
            Config {
                fuel,
                ..Config::with_usize_bits(32)
            },
        ),
    ]
}

/// A run that ended, for the compiled program: the width of `usize`, the
/// entry with the answers of the host, and how the oracle's run ended and
/// what it did.
type Ended = (u32, NativeRunSpec, String, Vec<oracle::Event>);

/// The program of `seed`, with the constructs of slice 1.
pub fn program_of(seed: u64) -> crate::syntax::Program {
    program_in(seed, 1)
}

/// The program of `seed` with the constructs of `slice`.
pub fn program_in(seed: u64, slice: u8) -> crate::syntax::Program {
    if slice >= 3 {
        valid_borrows(&mut Rng::new(mix(&[seed, 0x626f72726f77])))
    } else if slice >= 2 {
        valid_data(&mut Rng::new(mix(&[seed, 0x64617461])))
    } else {
        valid(&mut Rng::new(mix(&[seed, 0x76616c6964])))
    }
}

/// Tries the program of `seed`, and its mutants if asked, and adds what it
/// sees to `report`.
pub fn one(seed: u64, options: &Options, report: &mut Report) {
    let tree = program_in(seed, options.slice);
    let printed = tree.print();
    report.programs += 1;
    report.coverage.observe(&tree);
    let find = |report: &mut Report, kind: &'static str, detail: String, program: &str| {
        report.findings.push(Finding {
            seed,
            kind,
            detail,
            program: program.to_string(),
        });
    };

    let reparsed = match text::parse(&printed) {
        Ok(reparsed) => reparsed,
        Err(error) => {
            find(report, "reader", error.to_string(), &printed);
            return;
        }
    };
    if reparsed.print() != printed {
        find(
            report,
            "reader",
            "the program reads back to another text".to_string(),
            &printed,
        );
        return;
    }
    let program = match resolve::resolve(&reparsed) {
        Ok(program) => program,
        Err(error) => {
            find(report, "resolve", error.to_string(), &printed);
            return;
        }
    };

    // The runs that ended, for the compiled program: the entry, the answers
    // of the host, and how the oracle's run ended and what it did.
    let mut ended: Vec<Ended> = Vec::new();
    let mut rng = Rng::new(mix(&[seed, 0x72756e73]));
    for (bits, config) in configs(options.fuel) {
        for (index, (entry, arguments)) in entry_runs(&mut rng, &program, &config, options.entries)
            .into_iter()
            .enumerate()
        {
            for host_seed in 0..options.hosts {
                let mut host = Arithmetic(host_of(
                    &program,
                    mix(&[seed, index as u64, host_seed, u64::from(bits)]),
                    options.slice,
                ));
                let outcome = compare(&program, &entry, arguments.clone(), &mut host, &config);
                report.runs += 1;
                for (_, answer) in &outcome.answers {
                    for value in &answer.payload {
                        note_places(value, &mut report.host_places);
                    }
                }
                report.rules.extend(outcome.oracle.rules.keys().copied());
                let run = format!(
                    "`{entry}({})`, usize of {bits} bits, host {host_seed}",
                    show(&arguments)
                );
                // A run that ended is one for the compiled program too.
                let keep = |ended: &mut Vec<Ended>, end: erased::End| {
                    if options.native {
                        ended.push((
                            bits,
                            NativeRunSpec {
                                entry: entry.clone(),
                                arguments: arguments.clone(),
                                arithmetic: false,
                                answers: outcome.answers.clone(),
                            },
                            end.to_string(),
                            outcome.oracle.trace.clone(),
                        ));
                    }
                };
                let kind = match &outcome.oracle.end {
                    End::Done {
                        alternative,
                        payload,
                    } => match &outcome.verdict {
                        Verdict::Differ(difference) => {
                            find(report, "erased", format!("{run}: {difference}"), &printed);
                            continue;
                        }
                        _ => {
                            let end = erased::End::Done {
                                alternative: alternative.clone(),
                                payload: payload.clone(),
                            };
                            keep(&mut ended, end);
                            continue;
                        }
                    },
                    // A fault that leaves the entry and `terminate n` end a
                    // run as an outcome does ([E-Root], [E-Contingency]).
                    End::Faulted(message) => {
                        report.faulted += 1;
                        if let Verdict::Differ(difference) = &outcome.verdict {
                            find(report, "erased", format!("{run}: {difference}"), &printed);
                        } else {
                            keep(&mut ended, erased::End::Faulted(message.clone()));
                        }
                        continue;
                    }
                    End::Terminated(status) => {
                        report.terminated += 1;
                        if let Verdict::Differ(difference) = &outcome.verdict {
                            find(report, "erased", format!("{run}: {difference}"), &printed);
                        } else {
                            keep(&mut ended, erased::End::Terminated(*status));
                        }
                        continue;
                    }
                    End::Stuck(_) => "stuck",
                    End::OutOfFuel => "fuel",
                    _ => "host",
                };
                find(
                    report,
                    kind,
                    format!("{run} ends in `{}`", outcome.oracle.end),
                    &printed,
                );
            }
        }
    }

    if !options.checker {
        return;
    }
    let accepted = match checked(report, &printed, options.seconds) {
        Checked::Accepted => {
            report.accepted += 1;
            true
        }
        Checked::Rejected(message) => {
            find(report, "rejected", message, &printed);
            false
        }
        Checked::Panicked(message) => {
            find(report, "panic", message, &printed);
            false
        }
        Checked::TimedOut => {
            find(
                report,
                "timeout",
                format!("the checker took more than {} seconds", options.seconds),
                &printed,
            );
            false
        }
    };

    // The compiled program is what a checked program becomes, so only an
    // accepted program is compiled.
    if options.native && accepted {
        for bits in [64, 32] {
            let runs: Vec<_> = ended.iter().filter(|run| run.0 == bits).collect();
            let specs: Vec<NativeRunSpec> = runs.iter().map(|run| run.1.clone()).collect();
            for level in [0, 2] {
                let target = format!("usize of {bits} bits, -O{level}");
                let results = match run_native_counted(&program, &specs, bits, level) {
                    Ok(batch) => {
                        report.native_allocations += batch.allocations;
                        batch.runs
                    }
                    Err(error) => {
                        // The runs of a batch share a process. Each one
                        // alone says which of them ended it.
                        let mut alone = Vec::new();
                        for (_, spec, end, _) in runs.iter().copied() {
                            let one = std::slice::from_ref(spec);
                            if let Err(error) = run_native_batch(&program, one, bits, level) {
                                let error: String = error.chars().take(300).collect();
                                alone.push(format!(
                                    "`{}({})` with the answers [{}], which the oracle ends in `{end}`: {error}",
                                    spec.entry,
                                    show(&spec.arguments),
                                    answers(&spec.answers)
                                ));
                            }
                        }
                        let error: String = error.chars().take(1500).collect();
                        let detail = if alone.is_empty() {
                            format!("{target}: {error}")
                        } else {
                            format!("{target}: {}", alone.join("; "))
                        };
                        find(report, "native", detail, &printed);
                        continue;
                    }
                };
                if results.len() != runs.len() {
                    let detail = format!(
                        "{target}: {} runs asked, {} answered",
                        runs.len(),
                        results.len()
                    );
                    find(report, "native", detail, &printed);
                    continue;
                }
                for ((_, spec, end, trace), (native_end, native_trace)) in
                    runs.iter().copied().zip(&results)
                {
                    let run = format!("`{}({})`, {target}", spec.entry, show(&spec.arguments));
                    if native_end.to_string() != *end {
                        let detail =
                            format!("{run}: ends in `{native_end}`, and the oracle in `{end}`");
                        find(report, "native", detail, &printed);
                    } else if native_trace != trace {
                        let detail = format!("{run}: the trace is not the oracle's");
                        find(report, "native", detail, &printed);
                    } else {
                        report.native_runs += 1;
                    }
                }
            }
        }
    }

    if !options.mutants {
        return;
    }
    for mutant in mutate(&tree) {
        report.mutants += 1;
        report.kinds.entry(mutant.kind).or_default().mutants += 1;
        let source = mutant.program.print();
        let Ok(typed) = resolve::resolve(&mutant.program) else {
            report.refused += 1;
            report.kinds.entry(mutant.kind).or_default().refused += 1;
            continue;
        };
        // The first stuck run of the mutant, if a tried run is stuck.
        let mut stuck: Option<String> = None;
        let mut rng = Rng::new(mix(&[seed, 0x6d7574]));
        'runs: for (bits, config) in configs(options.mutant_fuel) {
            for (index, (entry, arguments)) in
                entry_runs(&mut rng, &typed, &config, options.entries)
                    .into_iter()
                    .enumerate()
            {
                for host_seed in 0..options.hosts {
                    let mut host = Arithmetic(host_of(
                        &typed,
                        mix(&[seed, index as u64, host_seed, u64::from(bits)]),
                        options.slice,
                    ));
                    let run = oracle::run(&typed, &entry, arguments.clone(), &mut host, &config);
                    if let End::Stuck(state) = &run.end {
                        stuck = Some(format!(
                            "`{entry}({})`, usize of {bits} bits, host {host_seed}: stuck X{} {} at {}:{}: {}",
                            show(&arguments),
                            state.state,
                            state.clause,
                            state.control,
                            state.line,
                            state.detail
                        ));
                        break 'runs;
                    }
                }
            }
        }
        let about = format!(
            "{:?} in `{}` ({})",
            mutant.kind, mutant.control, mutant.detail
        );
        match checked(report, &source, options.seconds) {
            Checked::Accepted => match stuck {
                Some(run) => find(report, "unsound", format!("{about}; {run}"), &source),
                None => {
                    report.survived += 1;
                    report.kinds.entry(mutant.kind).or_default().survived += 1;
                }
            },
            Checked::Rejected(_) => {
                let of_kind = report.kinds.entry(mutant.kind).or_default();
                report.rejected += 1;
                of_kind.rejected += 1;
                if stuck.is_some() {
                    report.rejected_stuck += 1;
                    of_kind.rejected_stuck += 1;
                }
            }
            Checked::Panicked(message) => {
                find(report, "panic", format!("{about}; {message}"), &source)
            }
            Checked::TimedOut => find(
                report,
                "timeout",
                format!(
                    "{about}; the checker took more than {} seconds",
                    options.seconds
                ),
                &source,
            ),
        }
    }
}

/// The host of the runs of a program of `slice`. From slice 3 on it writes
/// behind the arguments lent exclusively too.
fn host_of(program: &crate::typed::Program, seed: u64, slice: u8) -> Seeded<'_> {
    if slice >= 3 {
        Seeded::writing(program, seed)
    } else {
        Seeded::new(program, seed)
    }
}

/// Counts the places that a host lent in `value`, a payload value, by the
/// last step to each.
fn note_places(value: &Value, out: &mut BTreeMap<&'static str, u64>) {
    match value {
        Value::Ref { place, .. } if place.scope == HOST_SCOPE => {
            let step = match place.steps.last() {
                None => "whole arguments",
                Some(RuntimeStep::Field(_)) => "fields",
                Some(RuntimeStep::VariantField(_, _)) => "fields of variants",
                Some(RuntimeStep::Index(_)) => "elements",
                Some(RuntimeStep::MapValue(_)) => "values of maps",
                Some(RuntimeStep::MapKey(_)) => "keys of maps",
            };
            *out.entry(step).or_insert(0) += 1;
        }
        Value::Struct { fields, .. } => {
            for field in fields {
                note_places(field, out);
            }
        }
        _ => {}
    }
}

/// Tries the programs of `count` seeds from `first`.
pub fn campaign(first: u64, count: u64, options: &Options) -> Report {
    let mut report = Report {
        slice: options.slice,
        ..Report::default()
    };
    for seed in first..first + count {
        one(seed, options, &mut report);
    }
    report
}

/// As [`campaign`], for the reader and the two semantics alone.
pub fn campaign_without_checker(first: u64, count: u64, options: &Options) -> Report {
    let options = Options {
        checker: false,
        mutants: false,
        ..options.clone()
    };
    campaign(first, count, &options)
}

impl Report {
    /// The counts, one to a line.
    pub fn summary(&self) -> String {
        let mut by_kind: BTreeMap<&str, u64> = BTreeMap::new();
        for finding in &self.findings {
            *by_kind.entry(finding.kind).or_insert(0) += 1;
        }
        let mut out = format!(
            "{} programs, {} runs, {} accepted by the checker\n",
            self.programs, self.runs, self.accepted
        );
        if self.faulted + self.terminated > 0 {
            out.push_str(&format!(
                "{} of the runs end in a fault and {} with `terminate n`\n",
                self.faulted, self.terminated
            ));
        }
        if self.native_runs > 0 {
            out.push_str(&format!(
                "{} runs of compiled programs end as the oracle's do\n",
                self.native_runs
            ));
            out.push_str(&format!(
                "the compiled runs made {} allocations\n",
                self.native_allocations
            ));
        }
        if self.mutants > 0 {
            out.push_str(&format!(
                "{} mutants: {} refused by resolve, {} rejected by the checker ({} of them with a stuck run), {} accepted with no stuck run\n",
                self.mutants, self.refused, self.rejected, self.rejected_stuck, self.survived
            ));
            for (kind, count) in &self.kinds {
                out.push_str(&format!(
                    "  {kind:?}: {} mutants, {} refused, {} rejected ({} with a stuck run), {} accepted\n",
                    count.mutants,
                    count.refused,
                    count.rejected,
                    count.rejected_stuck,
                    count.survived
                ));
            }
        }
        if !self.host_places.is_empty() {
            let places: Vec<String> = self
                .host_places
                .iter()
                .map(|(step, count)| format!("{count} {step}"))
                .collect();
            out.push_str(&format!("the hosts lent: {}\n", places.join(", ")));
        }
        let mut missing = self.coverage.missing();
        if self.slice >= 2 {
            missing.extend(self.coverage.missing_data());
        }
        if self.slice >= 3 {
            missing.extend(self.coverage.missing_borrows());
        }
        out.push_str(&format!(
            "constructs not reached: {}\n",
            if missing.is_empty() {
                "none".to_string()
            } else {
                missing.join(", ")
            }
        ));
        if self.search != Counts::default() {
            out.push_str(&format!("the search: {}\n", self.search));
        }
        out.push_str(&format!("{} findings", self.findings.len()));
        for (kind, count) in by_kind {
            out.push_str(&format!("\n  {kind}: {count}"));
        }
        out
    }
}
