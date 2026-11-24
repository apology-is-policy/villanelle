//! Differential fuzzing, construct coverage and mutation tests for slice 1.

use std::collections::BTreeSet;
use villanelle_v2::differential::{Verdict, compare};
use villanelle_v2::fuzz;
use villanelle_v2::generate::{CONSTRUCTS, Coverage, free, sample_runs, template};
use villanelle_v2::host::{Arithmetic, Seeded};
use villanelle_v2::mutate::{Class, Kind, classify, mutate};
use villanelle_v2::oracle::{Config, End};
use villanelle_v2::rng::Rng;
use villanelle_v2::{resolve, text};

const RULES: [&str; 12] = [
    "E-Skip", "E-Bind", "E-Assign", "E-Oblige", "E-Test", "E-Decide", "E-Call", "E-Exit",
    "E-Extern", "E-Loop", "E-Again", "E-Leave",
];

const STUCK: [&str; 15] = [
    "X1 E-End",
    "X2 E-Var",
    "X2 E-Assign",
    "X3 E-Bind",
    "X6 E-Impossible",
    "X7 E-Arith",
    "X7 E-Fn",
    "X7 E-Oblige",
    "X7 E-Call",
    "X7 E-Extern",
    "X7 E-Exit",
    "X7 E-Loop",
    "X7 E-Again",
    "X9 E-Effect",
    "X10 E-Decide",
];

/// The generator of valid programs ([`villanelle_v2::generate::valid`]): what
/// it writes reads back, resolves, runs to an end on every tried entry under
/// both widths of `usize`, and gives the same observation under the erased
/// semantics. Over these seeds it reaches every construct of the slice and
/// every statement rule. What the checker says of the same programs is not
/// asserted here yet: `docs/v2/review.md` (RC12, RC16) has the count.
#[test]
fn generated_valid_programs_run_to_an_end_and_reach_every_construct() {
    let options = fuzz::Options::default();
    let report = fuzz::campaign_without_checker(1, 120, &options);
    let failures: Vec<String> = report
        .findings
        .iter()
        .map(|finding| format!("seed {} {}: {}", finding.seed, finding.kind, finding.detail))
        .collect();
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    assert!(
        report.coverage.missing().is_empty(),
        "constructs not reached: {:?}",
        report.coverage.missing()
    );
    for rule in RULES {
        assert!(report.rules.contains(rule), "no run applied [{rule}]");
    }
    assert!(report.runs >= 2_000, "runs = {}", report.runs);
}

/// The generator with the data of slice 2
/// ([`villanelle_v2::generate::valid_data`]): as for slice 1, what it writes
/// reads back, resolves, runs to an end and gives the same observation under
/// the erased semantics. An end is an outcome, a fault that leaves the entry
/// or `terminate n`, and each of the three occurs. It reaches every
/// construct of slice 1 and every construct of slice 2: data, operations on
/// data, resources, captured outcomes, faults and boundaries.
#[test]
fn generated_programs_with_data_run_to_an_end_and_reach_the_data_constructs() {
    let options = fuzz::Options {
        slice: 2,
        ..fuzz::Options::default()
    };
    let report = fuzz::campaign_without_checker(1, 240, &options);
    let failures: Vec<String> = report
        .findings
        .iter()
        .map(|finding| format!("seed {} {}: {}", finding.seed, finding.kind, finding.detail))
        .collect();
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    assert!(
        report.coverage.missing().is_empty(),
        "constructs not reached: {:?}",
        report.coverage.missing()
    );
    assert!(
        report.coverage.missing_data().is_empty(),
        "constructs of slice 2 not reached: {:?}",
        report.coverage.missing_data()
    );
    assert!(report.runs >= 4_000, "runs = {}", report.runs);
    assert!(report.faulted >= 100, "faulted = {}", report.faulted);
    assert!(
        report.terminated >= 20,
        "terminated = {}",
        report.terminated
    );
    assert_eq!(
        fuzz::program_in(7, 2).print(),
        fuzz::program_in(7, 2).print()
    );
    assert_ne!(fuzz::program_in(7, 2).print(), fuzz::program_of(7).print());
}

/// The seeds, of the first 30, whose programs the checker does not answer
/// in a time that a test can wait for (`docs/v2/review.md`, RC22).
const NO_ANSWER: [u64; 0] = [];

/// The checker accepts the programs with data that the generator calls
/// valid, the ones of [`NO_ANSWER`] apart. `vn2 fuzz --slice 2` tries more
/// seeds.
#[test]
fn the_checker_accepts_generated_programs_with_data() {
    let options = fuzz::Options {
        slice: 2,
        entries: 1,
        hosts: 1,
        seconds: 120,
        ..fuzz::Options::default()
    };
    let mut accepted = 0;
    let mut findings: Vec<String> = Vec::new();
    for seed in (1..=30).filter(|seed| !NO_ANSWER.contains(seed)) {
        let report = fuzz::campaign(seed, 1, &options);
        accepted += report.accepted;
        findings.extend(
            report.findings.iter().map(|finding| {
                format!("seed {} {}: {}", finding.seed, finding.kind, finding.detail)
            }),
        );
    }
    assert!(findings.is_empty(), "{}", findings.join("\n"));
    assert_eq!(accepted, 30 - NO_ANSWER.len() as u64);
}

/// The kinds of place that a host may lend from its arguments, by the last
/// step to them, as `fuzz::Report::host_places` counts them.
const HOST_PLACES: [&str; 6] = [
    "whole arguments",
    "fields",
    "fields of variants",
    "elements",
    "values of maps",
    "keys of maps",
];

/// The generator with the borrows of slice 3
/// ([`villanelle_v2::generate::valid_borrows`]): as for slices 1 and 2, what
/// it writes reads back, resolves, runs to an end and gives the same
/// observation under the erased semantics, with seeded hosts that write
/// behind arguments lent exclusively and lend places within the arguments.
/// It reaches every construct of slices 1 and 2 and every construct of the
/// borrows, and the hosts lend every kind of place. Seed 204 is in the range:
/// its loop payload was written in an order that moved a name before an
/// operand read it (`docs/v2/review.md`, RG8).
#[test]
fn generated_programs_with_borrows_run_to_an_end_and_reach_the_borrow_constructs() {
    let options = fuzz::Options {
        slice: 3,
        ..fuzz::Options::default()
    };
    let report = fuzz::campaign_without_checker(1, 300, &options);
    let failures: Vec<String> = report
        .findings
        .iter()
        .map(|finding| format!("seed {} {}: {}", finding.seed, finding.kind, finding.detail))
        .collect();
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    assert!(
        report.coverage.missing().is_empty(),
        "constructs not reached: {:?}",
        report.coverage.missing()
    );
    assert!(
        report.coverage.missing_data().is_empty(),
        "constructs of slice 2 not reached: {:?}",
        report.coverage.missing_data()
    );
    assert!(
        report.coverage.missing_borrows().is_empty(),
        "constructs of slice 3 not reached: {:?}",
        report.coverage.missing_borrows()
    );
    for kind in HOST_PLACES {
        assert!(
            report.host_places.get(kind).is_some_and(|count| *count > 0),
            "no host lent {kind}: {:?}",
            report.host_places
        );
    }
    assert!(report.runs >= 10_000, "runs = {}", report.runs);
    assert!(report.faulted >= 100, "faulted = {}", report.faulted);
    assert!(
        report.terminated >= 20,
        "terminated = {}",
        report.terminated
    );
    assert_eq!(
        fuzz::program_in(7, 3).print(),
        fuzz::program_in(7, 3).print()
    );
    assert_ne!(
        fuzz::program_in(7, 3).print(),
        fuzz::program_in(7, 2).print()
    );
}

/// The checker accepts the programs with borrows that the generator calls
/// valid: those of the first 30 seeds, and that of seed 157, which divides by
/// a name that borrows a constant. The checker takes a name bound once to a
/// constant expression as that constant ([I3]) and a borrow name as no
/// constant, and a generator that took the borrow name as the constant wrote
/// a product there that the checker cannot bound. `vn2 fuzz --slice 3` tries
/// more seeds.
#[test]
fn the_checker_accepts_generated_programs_with_borrows() {
    let options = fuzz::Options {
        slice: 3,
        entries: 1,
        hosts: 1,
        seconds: 120,
        ..fuzz::Options::default()
    };
    let seeds: Vec<u64> = (1..=30).chain([157]).collect();
    let mut accepted = 0;
    let mut findings: Vec<String> = Vec::new();
    for &seed in &seeds {
        let report = fuzz::campaign(seed, 1, &options);
        accepted += report.accepted;
        findings.extend(
            report.findings.iter().map(|finding| {
                format!("seed {} {}: {}", finding.seed, finding.kind, finding.detail)
            }),
        );
    }
    assert!(findings.is_empty(), "{}", findings.join("\n"));
    assert_eq!(accepted, seeds.len() as u64);
}

/// The calls of functions in one expression nest to a depth and no deeper
/// (`docs/v2/review.md`, RG4): the arguments of a call began with a budget
/// of their own, and writing the program of this seed did not end.
#[test]
fn a_generated_expression_ends_where_calls_nest() {
    assert!(fuzz::program_in(151, 2).print().lines().count() > 10);
}

/// A program is a function of its seed, and seeds give different programs.
#[test]
fn a_generated_program_is_a_function_of_its_seed() {
    let texts: BTreeSet<String> = (1..=40)
        .map(|seed| fuzz::program_of(seed).print())
        .collect();
    assert_eq!(texts.len(), 40);
    assert_eq!(fuzz::program_of(7).print(), fuzz::program_of(7).print());
    let lines: Vec<usize> = texts.iter().map(|text| text.lines().count()).collect();
    assert!(lines.iter().max() > lines.iter().min());
}

#[test]
fn the_template_covers_every_construct_and_rule_and_never_sticks() {
    let mut rng = Rng::new(2026);
    let mut coverage = Coverage::new();
    let mut rules_seen = BTreeSet::new();
    let mut total_runs = 0usize;

    let config_64 = Config {
        fuel: 10_000,
        ..Config::default()
    };
    let config_32 = Config {
        fuel: 10_000,
        ..Config::with_usize_bits(32)
    };

    for seed in 0..80u64 {
        let tree = template(&mut rng);
        coverage.observe(&tree);

        // Every generated program prints as core text and reads back to the
        // same text.
        let printed = tree.print();
        let reparsed = text::parse(&printed)
            .unwrap_or_else(|error| panic!("seed {seed}: parse failed: {error}\n{printed}"));
        assert_eq!(printed, reparsed.print(), "seed {seed}");

        let program = resolve::resolve(&reparsed)
            .unwrap_or_else(|error| panic!("seed {seed}: resolve failed: {error}\n{printed}"));

        for config in [&config_64, &config_32] {
            let runs = sample_runs(&mut rng, &program, config);
            assert!(!runs.is_empty(), "seed {seed}: no runs generated");
            for (index, (entry, arguments)) in runs.into_iter().enumerate() {
                let mut host = Arithmetic(Seeded::new(&program, seed * 100 + index as u64));
                let outcome = compare(&program, &entry, arguments.clone(), &mut host, config);
                assert!(
                    matches!(outcome.oracle.end, End::Done { .. }),
                    "seed {seed}: `{entry}({arguments:?})` ended in `{}`\n{printed}",
                    outcome.oracle.end
                );
                assert_eq!(
                    outcome.verdict,
                    Verdict::Same,
                    "seed {seed}: `{entry}({arguments:?})` differed: {:?}\n{printed}",
                    outcome.verdict
                );
                for clause in outcome.oracle.rules.keys() {
                    rules_seen.insert(*clause);
                }
                total_runs += 1;
            }
        }
    }

    assert!(
        coverage.missing().is_empty(),
        "valid generator missed constructs: {:?}",
        coverage.missing()
    );
    assert_eq!(coverage.counts.len(), CONSTRUCTS.len());
    for rule in RULES {
        assert!(
            rules_seen.contains(rule),
            "valid runs never applied [{rule}]"
        );
    }
    assert!(total_runs >= 800);
}

#[test]
fn free_programs_cover_every_construct_and_agree_with_erased_when_unstuck() {
    let mut rng = Rng::new(4096);
    let mut coverage = Coverage::new();
    let mut compared = 0usize;
    let mut stuck = 0usize;
    let config = Config {
        fuel: 500,
        ..Config::default()
    };

    for seed in 0..250u64 {
        let tree = free(&mut rng);
        coverage.observe(&tree);

        let printed = tree.print();
        let reparsed = text::parse(&printed)
            .unwrap_or_else(|error| panic!("free seed {seed}: parse failed: {error}\n{printed}"));
        assert_eq!(printed, reparsed.print(), "free seed {seed}");

        let program = resolve::resolve(&reparsed)
            .unwrap_or_else(|error| panic!("free seed {seed}: resolve failed: {error}\n{printed}"));

        for (index, (entry, arguments)) in sample_runs(&mut rng, &program, &config)
            .into_iter()
            .enumerate()
        {
            let mut host = Arithmetic(Seeded::new(&program, seed * 37 + index as u64));
            let outcome = compare(&program, &entry, arguments.clone(), &mut host, &config);
            match outcome.verdict {
                Verdict::Same => compared += 1,
                Verdict::NotCompared => {
                    if matches!(outcome.oracle.end, End::Stuck(_)) {
                        stuck += 1;
                    }
                }
                Verdict::Differ(difference) => {
                    panic!("free seed {seed}: `{entry}({arguments:?})`: {difference}\n{printed}");
                }
            }
        }
    }

    assert!(
        coverage.missing().is_empty(),
        "free generator missed constructs: {:?}",
        coverage.missing()
    );
    assert!(compared > 100, "compared = {compared}");
    assert!(stuck > 50, "stuck = {stuck}");
}

#[test]
fn mutations_of_the_template_reach_every_stuck_state_of_the_slice() {
    let mut rng = Rng::new(9001);
    let config = Config {
        fuel: 5_000,
        ..Config::default()
    };
    let mut kinds_seen = BTreeSet::new();
    let mut stuck_seen = BTreeSet::new();
    let mut refused_count = 0usize;
    let mut stuck_count = 0usize;
    let mut unstuck_count = 0usize;

    for seed in 0..16u64 {
        let tree = template(&mut rng);
        let program = resolve::resolve(&tree).expect("a valid program");
        let runs = sample_runs(&mut rng, &program, &config);
        for mutant in mutate(&tree) {
            kinds_seen.insert(mutant.kind);
            match classify(&mutant, &runs, seed * 100, &config) {
                Class::Refused(_) => refused_count += 1,
                Class::Stuck(stuck) => {
                    stuck_count += 1;
                    stuck_seen.insert(format!("X{} {}", stuck.state, stuck.clause));
                }
                Class::Unstuck => unstuck_count += 1,
            }
        }
    }

    for kind in [
        Kind::RemoveArm,
        Kind::RemoveDisposition,
        Kind::DropGuard,
        Kind::DropInvariant,
        Kind::DropEffect,
        Kind::ShiftLiteral,
        Kind::FlipComparison,
    ] {
        assert!(kinds_seen.contains(&kind), "missing mutation kind {kind:?}");
    }
    for expected in STUCK {
        assert!(
            stuck_seen.contains(expected),
            "no mutant of a valid program was stuck at {expected}; seen: {stuck_seen:?}"
        );
    }
    assert!(stuck_count > 100);
    assert!(refused_count > 0);
    assert!(unstuck_count > 0);
}

#[test]
fn seeded_host_honors_contracts_and_purity() {
    let source = "
extern control pure_ bounded(x : i32) ■ { ok {v : i32} ⇐ v ≥ x ∧ v ≤ x + 4 }
extern control noisy(x : i32) ■ { a {v : i32} ⇐ v ≥ 0 ∧ v ≤ 3 │ b } uses io
extern control impossible_host(x : u8) ■ { bad {v : u8} ⇐ v > 300 }

control check(x : i32) ■ { same {v : i32} } uses io
⊤ ▷ d1 : Δ pure_bounded(x) ▸ ok {v1}
⊤ ▷ d2 : Δ pure_bounded(x) ▸ ok {v2}
⊤ ▷ ⊢ v1 = v2 ∧ v1 ≥ x ∧ v1 ≤ x + 4
⊤ ▷ n1 : Δ noisy(x) ▸ a {w1} │ b
⊤ ▷ n2 : Δ noisy(x) ▸ a {w2} │ b
⊤ ▷ ■ same {v1}

control unachievable(x : u8) ■ { done }
⊤ ▷ d : Δ impossible_host(x) ▸ bad {v}
⊤ ▷ ■ done
"
    .replace("pure_ bounded", "pure_bounded");
    let program = villanelle_v2::load(&source).expect("resolved");
    let config = Config::default();
    for seed in 0..30u64 {
        let mut host = Seeded::new(&program, seed);
        let outcome = compare(
            &program,
            "check",
            vec![villanelle_v2::oracle::Value::Int(
                villanelle_v2::int::Int::from_i128(10),
            )],
            &mut host,
            &config,
        );
        assert!(matches!(outcome.oracle.end, End::Done { .. }));
        assert_eq!(outcome.verdict, Verdict::Same);
    }
    let mut host = Seeded::new(&program, 1);
    let failed = villanelle_v2::oracle::run(
        &program,
        "unachievable",
        vec![villanelle_v2::oracle::Value::Int(
            villanelle_v2::int::Int::from_u64(1),
        )],
        &mut host,
        &config,
    );
    assert!(matches!(failed.end, End::HostFailed(_)));
}

/// The checker accepts what the generator calls valid ([N3], [J5]): it gives
/// no rejection, no limit and no fault, and its certificates pass the
/// kernel. More seeds are tried by `vn2 fuzz`.
#[test]
fn the_checker_accepts_generated_valid_programs() {
    let options = fuzz::Options {
        entries: 1,
        hosts: 1,
        ..fuzz::Options::default()
    };
    let report = fuzz::campaign(1, 40, &options);
    let findings: Vec<String> = report
        .findings
        .iter()
        .map(|finding| format!("seed {} {}: {}", finding.seed, finding.kind, finding.detail))
        .collect();
    assert!(findings.is_empty(), "{}", findings.join("\n"));
    assert_eq!(report.accepted, 40);
}

/// A program in which a value of an outcome type crosses contracts: `taker`
/// is given one, and `asker` receives one in the answer of a host. The
/// checker accepts both controls by what the conditions of `scale` say of
/// the payload, over names for arguments that it does not see ([I12]).
const OUTCOMES_ACROSS_CONTRACTS: &str = r#"
extern control scale(by : u32)
    ⊢ by ≤ 9
    ■ { low {v : u32} ⇐ by ≤ 4 ∧ v ≤ by │ high {v : u32} ⇐ by > 4 ∧ by ≤ 9 ∧ v ≥ 100 ∧ v ≤ 100 + by }

extern control source(n : u32)
    ■ { given {o : outcome⟨scale⟩, k : u32} ⇐ k ≤ n │ none {} }
    uses net

control taker(o : outcome⟨scale⟩)
    ■ { small {v : u32} ⇐ v ≤ 4 │ large {v : u32} ⇐ v ≥ 100 ∧ v ≤ 109 }
    1  ⊤ ▷ d : Δ outcome(▾o) ▸ low {v} │ high {v}
    2  d.low ▷ ■ small {v}
    3  d.high ▷ ■ large {v}

control asker(n : u32)
    ■ { small {v : u32} ⇐ v ≤ 4 │ large {v : u32} ⇐ v ≥ 100 ∧ v ≤ 109 │ none {} }
    uses net
    1  ⊤ ▷ s : Δ source(n) ▸ given {o, k} │ none {}
    2  s.none ▷ ■ none {}
    3  s.given ▷ d : Δ outcome(▾o) ▸ low {v} │ high {v}
    4  d.low ▷ ■ small {v}
    5  d.high ▷ ■ large {v}
"#;

/// Review finding RG7. A value of an outcome type that an entry is given or
/// that a host answers with is one that the operation could have given: its
/// alternative and payload satisfy the condition of the alternative for
/// some arguments. A checked program may assume that much of a value whose
/// capture it does not see, so a harness that drew any value of the type
/// would report a stuck run of a program that the checker rightly accepts.
#[test]
fn a_drawn_value_of_an_outcome_type_is_one_that_its_operation_gives_i12() {
    use villanelle_v2::generate::entry_runs;
    use villanelle_v2::oracle::Value;

    let program = villanelle_v2::load(OUTCOMES_ACROSS_CONTRACTS).expect("resolved");
    let checked = villanelle_v2::check::check(&program);
    assert!(checked.is_ok(), "the checker accepts the program");
    let config = Config::default();
    // What the conditions of `scale` allow: `low` up to 4, `high` from 100
    // to 109.
    let allowed = |value: &Value| {
        let Value::Outcome {
            alternative_name,
            payload,
            ..
        } = value
        else {
            return false;
        };
        let Some(Value::Int(number)) = payload.first() else {
            return false;
        };
        let number = number.to_i128().expect("a small number");
        match alternative_name.as_str() {
            "low" => number <= 4,
            "high" => (100..=109).contains(&number),
            _ => false,
        }
    };

    // The entries of `taker`.
    let mut rng = Rng::new(7);
    let entries = entry_runs(&mut rng, &program, &config, 60);
    let mut alternatives = BTreeSet::new();
    let mut taken = 0;
    for (entry, arguments) in &entries {
        if entry != "taker" {
            continue;
        }
        taken += 1;
        assert!(allowed(&arguments[0]), "{:?}", arguments[0]);
        if let Value::Outcome {
            alternative_name, ..
        } = &arguments[0]
        {
            alternatives.insert(alternative_name.clone());
        }
        let mut host = Seeded::new(&program, taken);
        let outcome = compare(&program, entry, arguments.clone(), &mut host, &config);
        assert!(
            matches!(outcome.oracle.end, End::Done { .. }),
            "{:?}",
            outcome.oracle.end
        );
        assert_eq!(outcome.verdict, Verdict::Same);
    }
    assert_eq!(taken, 60);
    assert_eq!(alternatives.len(), 2, "{alternatives:?}");

    // The answers of the host of `asker`.
    let mut ends = BTreeSet::new();
    for seed in 0..200u64 {
        let mut host = Seeded::new(&program, seed);
        let arguments = vec![Value::Int(villanelle_v2::int::Int::from_u64(seed % 12))];
        let outcome = compare(&program, "asker", arguments, &mut host, &config);
        let End::Done { alternative, .. } = &outcome.oracle.end else {
            panic!("seed {seed}: {:?}", outcome.oracle.end);
        };
        ends.insert(alternative.clone());
        assert_eq!(outcome.verdict, Verdict::Same);
    }
    assert_eq!(ends.len(), 3, "{ends:?}");

    // A value that the operation could not have given leaves the program
    // stuck, which the checker accepted: that is what the harness must not
    // draw.
    let stuck = villanelle_v2::script::check(&format!(
        "{OUTCOMES_ACROSS_CONTRACTS}
//! run taker(outcome.low {{3}}) => done small {{3}}
//! run taker(outcome.high {{105}}) => done large {{105}}
//! run taker(outcome.low {{7}}) => stuck X7 E-Exit
//! run asker(1) with [source -> given {{outcome.high {{300}}, 1}}] => stuck X7 E-Exit
"
    ));
    assert!(stuck.failures.is_empty(), "{:?}", stuck.failures);
    assert_eq!(stuck.runs, 4);
}
