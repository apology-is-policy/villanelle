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

/// The constructs of slice 2 that the generator does not write yet: faults
/// and boundaries (`docs/v2/review.md`, section 3).
const DATA_NOT_WRITTEN: [&str; 11] = [
    "named-boundary",
    "retains",
    "faults",
    "boundary",
    "boundary-care",
    "supervise",
    "fault",
    "escalate",
    "recover",
    "terminate-status",
    "terminate",
];

/// The generator with the data of slice 2
/// ([`villanelle_v2::generate::valid_data`]): as for slice 1, what it writes
/// reads back, resolves, runs to an end and gives the same observation under
/// the erased semantics. It reaches every construct of slice 1 and the
/// constructs of slice 2 that are data, operations on data, resources and
/// captured outcomes.
#[test]
fn generated_programs_with_data_run_to_an_end_and_reach_the_data_constructs() {
    let options = fuzz::Options {
        slice: 2,
        ..fuzz::Options::default()
    };
    let report = fuzz::campaign_without_checker(1, 160, &options);
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
    assert_eq!(report.coverage.missing_data(), DATA_NOT_WRITTEN);
    assert!(report.runs >= 4_000, "runs = {}", report.runs);
    assert_eq!(
        fuzz::program_in(7, 2).print(),
        fuzz::program_in(7, 2).print()
    );
    assert_ne!(fuzz::program_in(7, 2).print(), fuzz::program_of(7).print());
}

/// The seeds, of the first 30, whose programs the checker does not answer
/// in a time that a test can wait for (`docs/v2/review.md`, RC22).
const NO_ANSWER: [u64; 2] = [11, 23];

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
