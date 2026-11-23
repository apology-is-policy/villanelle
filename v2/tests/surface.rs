//! Conformance and clause-coverage tests for the Rails surface reader and
//! elaborator (`docs/v2/surface.md`).
//!
//! Every layout (`[Y1]` to `[Y10]`), grammar (`[G1]` to `[G9]`) and
//! elaboration (`[U1]` to `[U4]`, `[U6]` to `[U9]`, `[U13]` to `[U15]`) clause
//! of slice 1 has both an accepting test (elaborated, resolved and executed in
//! the oracle and under the erased semantics) and a rejecting test (refused
//! with the clause's identifier).

use std::collections::BTreeSet;
use std::path::PathBuf;
use villanelle_v2::{script, surface};

const SURFACE_CLAUSES: [&str; 29] = [
    "Y1", "Y2", "Y3", "Y4", "Y5", "Y6", "Y7", "Y8", "Y9", "Y10", "G1", "G2", "G3", "G4", "G5",
    "G6", "G8", "G9", "U1", "U2", "U3", "U4", "U6", "U7", "U8", "U9", "U13", "U14", "U15",
];

fn surface_files() -> Vec<(String, String)> {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/slice1_surface");
    let mut out = Vec::new();
    for entry in std::fs::read_dir(&root).expect("tests/slice1_surface") {
        let path = entry.expect("an entry").path();
        if path.extension().is_some_and(|ext| ext == "rails") {
            let name = path
                .file_name()
                .expect("a file name")
                .to_string_lossy()
                .into_owned();
            out.push((name, std::fs::read_to_string(&path).expect("readable")));
        }
    }
    out.sort();
    assert!(!out.is_empty());
    out
}

#[test]
fn surface_files_run_and_agree_with_erased_semantics() {
    let mut runs = 0;
    let mut compared = 0;
    let mut failures = Vec::new();
    for (name, source) in surface_files() {
        let report = script::check_surface(&source);
        if report.runs == 0 && report.rejected.is_none() {
            failures.push(format!("{name}: no directives"));
        }
        for failure in report.failures {
            failures.push(format!("{name}: {failure}"));
        }
        runs += report.runs;
        compared += report.compared;
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    assert!(runs >= 14 && compared == runs);
}

#[test]
fn every_surface_clause_of_slice_one_accepts_and_rejects() {
    let accepting: &[(&[&str], &str)] = &[
        // Y1, Y2, Y3, Y8, Y9, G1
        (
            &["Y1", "Y2", "Y3", "Y8", "Y9", "G1"],
            "\
control add(a: u32, b: u32)
    ■ sum {value: u32}
    ■ zero
│ ┄ comment on rail
│
│ x: u32 := a +
│     b
│ ? x = 0 → ■ zero
│ ■ sum {x}
╵
//! run add(2, 3) => done sum {5}
//! run add(0, 0) => done zero
",
        ),
        // Y4, Y5, Y6, G5, G6, U4, U9
        (
            &["Y4", "Y5", "Y6", "G5", "G6", "U4", "U9"],
            "\
extern control probe(x: u32) ■ hit │ miss

control count_down(n: u32) ■ ended {steps: u32}
│ Δ probe(n): hit │ miss
│ ↻ step(rem: u32 := n, ~acc: u32 := 0)
│ ║ ⊢ rem ≤ n
│ ║ ? rem = 0 →
│ ║ ┆ □ done {acc}
│ ╠═ ¬miss ∧ hit: acc ← acc + 1
│ ╠═ miss
│ ║ ┆ acc ← acc + 2
│ ║ ↑ step(rem - 1, acc)
╞═ done: ■ ended {acc}
╵
//! run count_down(2) with [probe -> hit] => done ended {2}
//! run count_down(2) with [probe -> miss] => done ended {4}
",
        ),
        // Y7, U1, U2, U3, U6, U7, U8, U15
        (
            &["Y7", "U1", "U2", "U3", "U6", "U7", "U8", "U15"],
            "\
extern control ping(x: u32) ■ ok {v: u32} │ err
extern control log(x: u32) ■ logged

control check(x: u32, flag: bool) ■ out {v: u32} │ bad
│ first : Δ ping(x)
│ ├ ok {v: u32} → got
│ └ err →
│   ┆ log(x)
│   ┆ ■ bad
│ second : Δ ping(x): ok {w} → got │ err → ■ bad
│ Δ flag: true → high │ false → low
╞═ first.ok ∧ second.ok ∧ (high ∨ low) ∧ got
│ ┆ ■ out {x}
╵
//! run check(5, true) with [ping -> ok {5}; ping -> ok {5}] => done out {5}
//! run check(5, false) with [ping -> err; log -> logged] => done bad
",
        ),
        // G2, G3, G4, U13, U14
        (
            &["G2", "G3", "G4", "U13", "U14"],
            "\
outcome err_group: e1 ↦ 1 │ e2 {code: u32} ↦ 2

extern control step(x: u32) ■ good {v: u32} │ …err_group

control adapt(x: u32) ■ auto
│ ■ Δ step(x): good {v} → wrapped {v} │ …err_group
╵

control caller(x: u32) ■ wrapped {v: u32} │ …err_group
│ forward adapt(x)
╵
//! run caller(3) with [step -> good {9}] => done wrapped {9}
//! run caller(3) with [step -> e2 {4}] => done e2 {4}
",
        ),
        // G8, G9, Y10
        (
            &["G8", "G9", "Y10"],
            "\
function inc(x: u32) where x < 100 : u32 := x + 1

outcome res { ok {v: u32} |-> 0, fail |-> 1 }

extern control ask(x: u32) exits ..res

control run_plain(x: u32) exits ..res {
    mutable y: u32 := inc(x)
    delta ask(y) { ok {v} => got, fail => exit fail }
    [got]: {
        if v != 0 && v <= 50 => exit ok {v}
        exit fail
    }
}
//! run run_plain(4) with [ask -> ok {5}] => done ok {5}
",
        ),
    ];

    let mut accepted_clauses = BTreeSet::new();
    for (clauses, source) in accepting {
        let report = script::check_surface(source);
        assert!(
            report.failures.is_empty(),
            "accepting test for {clauses:?} failed: {:?}\n{source}",
            report.failures
        );
        assert!(report.runs > 0);
        for clause in *clauses {
            accepted_clauses.insert(*clause);
        }
    }

    let rejecting: &[(&str, &str)] = &[
        // Y1: declaration indented or continuation indented < 4 spaces
        ("Y1", "  control bad() ■ ok\n│ ■ ok\n╵\n//! reject Y1\n"),
        // Y2: rail character without trailing space
        (
            "Y2",
            "\
control bad() ■ ok
│■ ok
╵
//! reject Y2
",
        ),
        // Y3: control body not closed with `╵`
        (
            "Y3",
            "\
control bad() ■ ok
│ ■ ok
//! reject Y3
",
        ),
        // Y4: loop header without `║` body lines
        (
            "Y4",
            "\
control bad() ■ ok
│ ↻ spin
│ ■ ok
╵
//! reject Y4
",
        ),
        // Y5: label inside a `┆` test block
        (
            "Y5",
            "\
extern control ask() ■ a │ b

control bad(x: u32) ■ ok
│ Δ ask(): a │ b
│ ? x = 0 →
│ ┆ ╞═ a: ■ ok
│ ■ ok
╵
//! reject Y5
",
        ),
        // Y6: test `?` without `→`
        (
            "Y6",
            "\
control bad(x: u32) ■ ok
│ ? x = 0
│ ■ ok
╵
//! reject Y6
",
        ),
        // Y7: vertical decision arms not ending with `└`
        (
            "Y7",
            "\
extern control ask() ■ a │ b

control bad() ■ ok
│ Δ ask()
│ ├ a → ■ ok
│ ├ b → ■ ok
╵
//! reject Y7
",
        ),
        // Y8: continuation line at the start of a body with no statement above it
        (
            "Y8",
            "\
control bad() ■ ok
│   ■ ok
╵
//! reject Y8
",
        ),
        // Y9: blank line inside a body without its rail prefix
        (
            "Y9",
            "\
control bad() ■ ok
│ x := 1

│ ■ ok
╵
//! reject Y9
",
        ),
        // Y10: rail prefix `│ ┆ ` when no label, test or arm block is open
        (
            "Y10",
            "\
control bad() ■ ok
│ ┆ ■ ok
╵
//! reject Y10
",
        ),
        // G1: empty contract
        (
            "G1",
            "\
control bad() ■
│ ■ ok
╵
//! reject G1
",
        ),
        // G2: `…unknown` outcome group in contract
        (
            "G2",
            "\
control bad() ■ …unknown_group
│ ■ ok
╵
//! reject G2
",
        ),
        // G3: `■ auto` on a `pub` control
        (
            "G3",
            "\
pub control bad() ■ auto
│ ■ ok
╵
//! reject G3
",
        ),
        // G4: `↦` on a control contract instead of an `outcome` declaration
        (
            "G4",
            "\
control bad() ■ ok ↦ 0
│ ■ ok
╵
//! reject G4
",
        ),
        // G5: `¬` applied to a parenthesized mask `¬(a ∧ b)`
        (
            "G5",
            "\
extern control ask() ■ a │ b

control bad() ■ ok
│ Δ ask(): a │ b
╞═ ¬(a ∧ b): ■ ok
│ ■ ok
╵
//! reject G5
",
        ),
        // G6: first `⊢` line in loop body is the loop's invariant (stuck at X7 E-Again when violated)
        // and for syntax rejection, a malformed token in G8 / unclosed brace in G9:
        (
            "G8",
            "\
control bad() ■ ok
│ x := @
│ ■ ok
╵
//! reject G8
",
        ),
        (
            "G9",
            "\
control bad() exits ok {
    exit ok
//! reject G9
",
        ),
        // U1: two decisions share default site name `ask` and a label qualifies `ask.a`
        (
            "U1",
            "\
extern control ask() ■ a │ b

control bad() ■ ok
│ Δ ask(): a │ b
│ Δ ask(): a │ b
╞═ ask.a: ■ ok
│ ■ ok
╵
//! reject U1
",
        ),
        // U2: referencing original alternative name `a` after it was renamed by a route `a → routed`
        (
            "U2",
            "\
extern control ask() ■ a │ b

control bad() ■ ok
│ Δ ask(): a → routed │ b → ■ ok
╞═ a: ■ ok
╵
//! reject U2
",
        ),
        // U3: unqualified `failed` when two decisions have `failed` by default
        (
            "U3",
            "\
extern control first() ■ ok │ failed
extern control second() ■ ok │ failed

control bad() ■ done
│ Δ first(): ok │ failed
│ Δ second(): ok │ failed
╞═ failed: ■ done
│ ■ done
╵
//! reject U3
",
        ),
        // U4: mask references a path of a decision that appears after the label
        (
            "U4",
            "\
extern control ask() ■ a │ b

control bad() ■ ok
╞═ a: ■ ok
│ Δ ask(): a │ b
│ ■ ok
╵
//! reject U4
",
        ),
        // U6: calling a multi-outcome operation without `Δ`
        (
            "U6",
            "\
extern control ask() ■ a │ b

control bad() ■ ok
│ ask()
│ ■ ok
╵
//! reject U6
",
        ),
        // U7: decision omits an alternative of the operation's contract
        (
            "U7",
            "\
extern control ask() ■ a │ b

control bad() ■ ok
│ Δ ask(): a
│ ■ ok
╵
//! reject U7
",
        ),
        // U8: arm pattern has wrong number of payload fields
        (
            "U8",
            "\
extern control ask() ■ a {x: u32}

control bad() ■ ok
│ Δ ask(): a {x, y}
│ ■ ok
╵
//! reject U8
",
        ),
        // U9: loop mixes bare `□` with named `□ done`
        (
            "U9",
            "\
control bad(n: u32) ■ ok
│ ↻ step(i: u32 := n)
│ ║ ? i = 0 → □
│ ║ ? i = 1 → □ done
│ ║ ↑ step(i - 1)
│ ■ ok
╵
//! reject U9
",
        ),
        // U13: adapter `■ Δ` arm opens a block instead of exiting
        (
            "U13",
            "\
extern control ask() ■ a │ b

control bad() ■ a │ b
│ ■ Δ ask()
│ ├ a →
│ │ ┆ x := 1
│ │ ┆ ■ a
│ └ b
╵
//! reject U13
",
        ),
        // U14: `forward` where callee includes group `…err` and caller lists alternatives individually
        (
            "U14",
            "\
outcome err: e1 │ e2

extern control step() ■ ok │ …err

control bad() ■ ok │ e1 │ e2
│ forward step()
╵
//! reject U14
",
        ),
        // U15: exit with an alternative not in the control's contract
        (
            "U15",
            "\
control bad() ■ ok
│ ■ missing
╵
//! reject U15
",
        ),
    ];

    let mut rejected_clauses = BTreeSet::new();
    for (clause, source) in rejecting {
        let report = script::check_surface(source);
        assert!(
            report.failures.is_empty(),
            "rejecting test for [{clause}] failed: {:?}\n{source}",
            report.failures
        );
        assert_eq!(
            report.rejected.as_deref(),
            Some(*clause),
            "expected rejection by [{clause}]\n{source}"
        );
        rejected_clauses.insert(*clause);
    }

    // [G6] negative test: the first `⊢` line of a loop body is the loop's
    // invariant, so when it is false on `↑`, the oracle is stuck at `X7 E-Again`
    // (whereas a second `⊢` line is an obligation, stuck at `X7 E-Oblige`).
    let g6_check = "\
control inv_fails(n: u32) ■ ok
│ ↻ step(i: u32 := 0)
│ ║ ⊢ i < 1
│ ║ ⊢ i < 10
│ ║ ↑ step(i + 1)
╵
//! run inv_fails(2) => stuck X7 E-Again
";
    let g6_report = script::check_surface(g6_check);
    assert!(g6_report.failures.is_empty(), "{:?}", g6_report.failures);
    rejected_clauses.insert("G6");

    for clause in SURFACE_CLAUSES {
        assert!(
            accepted_clauses.contains(clause),
            "no accepting surface test covers [{clause}]"
        );
        assert!(
            rejected_clauses.contains(clause),
            "no rejecting surface test covers [{clause}]"
        );
    }

    // Also verify `surface::elaborate` produces a tree whose printed core text
    // re-parses identically.
    for (name, source) in surface_files() {
        let tree = surface::elaborate(&source).unwrap_or_else(|e| panic!("{name}: {e}"));
        let printed = tree.print();
        let reparsed = villanelle_v2::text::parse(&printed)
            .unwrap_or_else(|e| panic!("{name}: core parse failed: {e}\n{printed}"));
        assert_eq!(printed, reparsed.print(), "{name}");
    }
}

#[test]
fn g10_formatter_canonical_rails_idempotence_and_semantic_equivalence() {
    // [G10]: Every Rails file is either already a fixed point of `surface::format`
    // (for canonical Rails files) or formats plain-form declarations into
    // canonical Rails while preserving elaborated core semantics and idempotence.
    for (name, source) in surface_files() {
        let formatted =
            surface::format(&source).unwrap_or_else(|e| panic!("{name}: format failed: {e}"));
        let reformatted =
            surface::format(&formatted).unwrap_or_else(|e| panic!("{name}: reformat failed: {e}"));
        assert_eq!(
            formatted, reformatted,
            "{name}: surface::format is not idempotent"
        );
        let orig_core = surface::elaborate(&source).unwrap().print();
        let fmt_core = surface::elaborate(&formatted).unwrap().print();
        assert_eq!(
            orig_core, fmt_core,
            "{name}: formatting changed elaborated core program"
        );
        // `spend.rails` holds one control in the plain form ([G9]) on
        // purpose, so that the plain form runs through every stage. Its
        // canonical text is kept beside the formatter's tests.
        if name == "spend.rails" {
            assert_eq!(formatted, include_str!("format/spend_canonical.rails"));
        } else {
            assert_eq!(
                source, formatted,
                "{name} is not in canonical Rails form ([G10])"
            );
        }
    }

    // [G10] accepting: word-form ([G8]) and plain braced form ([G9]) format into
    // canonical Rails glyph form with aligned arrows and aligned short labels.
    let plain_and_word = "\
// Top-level comment in slash form.
pub outcome err { bad_input {code: u32} |-> 2, timeout |-> 3 }

extern control check_item(x: u32) exits ok {val: u32} when val == x | missing | denied

pub control handle(x: u32) where x <= 100 exits done {out: u32} | absent | failed {
    if x == 0 => exit absent
    delta check_item(x) {
        ok {~v: u32},
        missing => no_item,
        denied => {
            where x > 0;
            exit failed
        }
    }
    [ok]: v <- v + 1; exit done {v}
    [no_item]: exit absent
}
";
    let expected_rails = "\
┄ Top-level comment in slash form.
pub outcome err
├ bad_input {code: u32} ↦ 2
└ timeout ↦ 3

extern control check_item(x: u32)
    ■ ok {val: u32} ⇐ val = x
    ■ missing
    ■ denied

pub control handle(x: u32) ⊢ x ≤ 100 ■ done {out: u32} │ absent │ failed
│ ? x = 0 → ■ absent
│ Δ check_item(x)
│ ├ ok {~v: u32}
│ ├ missing → no_item
│ └ denied →
│   ┆ ⊢ x > 0
│   ┆ ■ failed
╞═ ok:      v ← v + 1; ■ done {v}
╞═ no_item: ■ absent
╵
";
    let formatted = surface::format(plain_and_word).expect("format plain_and_word");
    assert_eq!(formatted, expected_rails);
    assert_eq!(
        surface::format(&formatted).unwrap(),
        formatted,
        "idempotence on formatted plain_and_word"
    );
    assert_eq!(
        surface::elaborate(plain_and_word).unwrap().print(),
        surface::elaborate(&formatted).unwrap().print(),
        "elaborated core semantics preserved by format"
    );

    // [G10] rejecting: invalid surface text is refused by `surface::format` with
    // the exact clause of the violation.
    let invalid = "\
control bad(x: u32) ■ ok
│ ? x = 0
│ ■ ok
╵
";
    let err = surface::format(invalid).expect_err("invalid test line must be refused");
    assert_eq!(err.clause, "Y6");
}

#[test]
fn u5_u17_u18_surface_warnings() {
    // [U5] / [U18]: Warn when `¬` is applied to a path of a decision that has
    // only one other continuing path, and suggest that path.
    let two_path_negation = "\
extern control step(x: u32) ■ a │ b │ c

pub control run_two(x: u32) ■ done
│ Δ step(x): a │ b │ c → ■ done
╞═ a:  ■ done
╞═ ¬a: ■ done
╵
//! check
//! warn U5
//! warn U18
";
    let report = script::check_surface(two_path_negation);
    assert!(
        report.failures.is_empty(),
        "expected U5/U18 warning, got failures: {:?}",
        report.failures
    );
    let elab = surface::elaborate_with_warnings(two_path_negation).unwrap();
    assert_eq!(elab.warnings.len(), 1);
    assert_eq!(elab.warnings[0].clause, "U5");
    assert!(
        elab.warnings[0].message.contains("`b`"),
        "expected suggestion of `b`, got: {}",
        elab.warnings[0].message
    );

    // When a decision has TWO other continuing paths (`b` and `c`), `¬a` does
    // NOT trigger [U5] / [U18].
    let three_path_negation = "\
extern control step(x: u32) ■ a │ b │ c

pub control run_three(x: u32) ■ done
│ Δ step(x): a │ b │ c
╞═ a:  ■ done
╞═ ¬a: ■ done
╵
";
    let elab3 = surface::elaborate_with_warnings(three_path_negation).unwrap();
    assert!(
        elab3.warnings.is_empty(),
        "expected no warning on 3-continuing-path negation, got {:?}",
        elab3.warnings
    );

    // [U17]: Warn when an arm introduces a route `→ name` and no later label in
    // the body mentions `name`.
    let unused_route = "\
extern control step(x: u32) ■ a │ b

pub control bad_route(x: u32) ■ done
│ Δ step(x): a → unused_path │ b → ■ done
│ ■ done
╵
//! check
//! warn U17
";
    let report_u17 = script::check_surface(unused_route);
    assert!(
        report_u17.failures.is_empty(),
        "expected U17 warning, got failures: {:?}",
        report_u17.failures
    );
    let elab_u17 = surface::elaborate_with_warnings(unused_route).unwrap();
    assert_eq!(elab_u17.warnings.len(), 1);
    assert_eq!(elab_u17.warnings[0].clause, "U17");
    assert!(elab_u17.warnings[0].message.contains("unused_path"));
}

#[test]
fn g10_keeps_comments_in_order_through_layout_changes() {
    let rails = include_str!("format/comments.rails");
    let plain = include_str!("format/plain_comments.rails");
    for (source, marker) in [(rails, '┄'), (plain, '/')] {
        let comments: Vec<_> = source
            .lines()
            .filter_map(|line| {
                let (_, comment) = line.split_once(marker)?;
                Some(comment.trim_start_matches('/').trim())
            })
            .collect();
        let printed = surface::format(source).unwrap();
        let kept: Vec<_> = printed
            .lines()
            .filter_map(|line| {
                let (_, comment) = line.split_once('┄')?;
                Some(comment.trim())
            })
            .collect();
        assert_eq!(kept, comments);
        assert_eq!(surface::format(&printed).unwrap(), printed);
        assert_eq!(
            surface::elaborate(source).unwrap().print(),
            surface::elaborate(&printed).unwrap().print()
        );
    }

    // A comment cannot take the place of the required last decision arm.
    let invalid = rails.replace("│ └ c → ■ failed", "│ ┄ └ c → ■ failed");
    assert!(surface::format(&invalid).is_err());
}

#[test]
fn g10_keeps_comments_on_folded_lines_and_delimiters() {
    let source = r#"control f(s: string) ■ done
│ x: string := "// not a comment ┄ either" // same
│ n: u32 := 1 + // same
│     2 // sum
│ ■ done // end
╵ // close
"#;
    let printed = surface::format(source).unwrap();
    assert_eq!(printed.matches("┄ same").count(), 2);
    assert!(printed.contains("\"// not a comment ┄ either\" ┄ same"));
    assert!(printed.contains("│ ┄ sum\n│ ■ done ┄ end\n╵ ┄ close"));
    assert_eq!(surface::format(&printed).unwrap(), printed);

    let plain = include_str!("format/plain_comments.rails");
    assert!(surface::format(plain).unwrap().contains("│ ┄ P8 last\n╵"));
}

#[test]
fn g10_keeps_plain_boundary_comments_next_to_the_work_body() {
    let source = "boundary guard() {\n    terminate\n} // work closed\n// between\ncontingency (m: string) {\n    terminate\n} // handler closed\n";
    let printed = surface::format(source).unwrap();
    assert!(printed.contains("│ ┄ work closed\n│ ┄ between\n╵\ncontingency"));
    assert_eq!(surface::format(&printed).unwrap(), printed);
}

#[test]
fn u9_renames_inner_binders_and_the_places_that_use_them() {
    for source in [
        include_str!("loop_names/capture_and_place.rails"),
        include_str!("loop_names/unpack.rails"),
        include_str!("loop_names/index_and_root.rails"),
    ] {
        let report = script::check_surface(source);
        assert_eq!(report.runs, 1);
        assert!(report.failures.is_empty(), "{:?}", report.failures);
    }
    // A similarly spelled free name is still free after the loop is lowered.
    let source = include_str!("loop_names/capture_and_place.rails")
        .replace("cells[0] ← total", "cells[0] ← missing");
    assert!(villanelle_v2::load_surface(&source).is_err());
}

#[test]
fn u14_forwards_named_contracts_and_builtin_calls() {
    let named = r#"outcome answer: ok {n: u32} │ missing
control one() ■ ok {n: u32} │ missing
│ ■ ok {1}
╵
control direct() ■ answer
│ forward one()
╵
control captured() ■ answer
│ r := capture one()
│ ■ ▾r
╵
//! run direct() => done ok {1}
//! run captured() => done ok {1}
"#;
    let builtin = r#"control method() ■ done
│ ~xs: [u32] := [0]
│ forward xs.push(1)
╵
control direct() ■ done
│ ~xs: [u32] := [0]
│ forward push(&~xs, 1)
╵
//! run method() => done done
//! run direct() => done done
"#;
    for source in [named, builtin] {
        let printed = surface::format(source).unwrap();
        assert_eq!(surface::format(&printed).unwrap(), printed);
        let report = script::check_surface(&printed);
        assert_eq!(report.runs, 2, "{:?}", report.failures);
        assert!(report.failures.is_empty(), "{:?}", report.failures);
    }
    let wrong_type = named.replacen("n: u32", "n: bool", 1);
    assert_eq!(surface::elaborate(&wrong_type).unwrap_err().clause, "U14");
    let bad_arity = builtin.replace("xs.push(1)", "xs.push()");
    assert_eq!(surface::elaborate(&bad_arity).unwrap_err().clause, "C1");
}

#[test]
fn layout_reads_decision_tokens_and_leaves_string_contents_alone() {
    let source = r#"extern control ask() ■ yes │ no

control plain() exits done {
    emit("}")
    exit done
}

control on_rails() exits done
│ exits    delta ask()
│ ├ yes → done
│ └ no → done
╵

control label(x: bool) ■ done
│ Δ x: true → selected │ false → ■ done
╞═ selected: emit("a; \"b\" {"); ■ done
╵
//! run plain() => done done trace [emit("}") -> done]
//! run on_rails() with [ask -> yes] => done done
"#;
    let formatted = surface::format(source).unwrap();
    assert_eq!(surface::format(&formatted).unwrap(), formatted);
    assert!(formatted.contains(r#"emit("a; \"b\" {")"#));
    let report = script::check_surface(&formatted);
    assert!(report.failures.is_empty(), "{:?}", report.failures);
    assert_eq!(report.runs, 2);
    let no_last_arm = source.replace("│ └ no → done\n", "");
    assert_eq!(surface::format(&no_last_arm).unwrap_err().clause, "Y7");
}

#[test]
fn hidden_payload_names_are_inaccessible_and_auto_needs_type_evidence() {
    let source = "extern control ask() ■ ok {value: u32}\ncontrol f(_v0: u32) ■ result {n: u32}\n│ Δ ask(): ok\n│ ■ result {_v0}\n╵\n//! run f(7) with [ask -> ok {41}] => done result {7}\n";
    assert!(script::check_surface(source).failures.is_empty());
    assert!(villanelle_v2::load_surface(&source.replace("f(_v0: u32)", "f()")).is_err());

    let vector = "control f() ■ auto\n│ xs := [1, 2]\n│ ■ ok {xs}\n╵\n";
    assert!(villanelle_v2::load_surface(vector).is_ok());
    for payload in ["[]", "∅", "4294967296"] {
        let s = format!("control sample() ■ auto\n│ ■ ok {{{payload}}}\n╵\n");
        assert_eq!(surface::elaborate(&s).unwrap_err().clause, "G3");
    }
    let inferred = "control sample(x: u64) ■ auto\n│ ? x = 0 → ■ ok {4294967296}\n│ ■ ok {x}\n╵\n//! run sample(0) => done ok {4294967296}\n";
    assert!(script::check_surface(inferred).failures.is_empty());
}

/// The comments of a Rails text, in order: what follows `┄` or `//` outside
/// a text literal, to the end of the line. A directive (`//!`) is not one.
fn comments_of(text: &str) -> Vec<String> {
    let mut out = Vec::new();
    for line in text.lines() {
        if line.trim_start().starts_with("//!") {
            continue;
        }
        let mut quoted = false;
        let mut escaped = false;
        for (at, ch) in line.char_indices() {
            if quoted {
                if escaped {
                    escaped = false;
                } else if ch == '\\' {
                    escaped = true;
                } else if ch == '"' {
                    quoted = false;
                }
                continue;
            }
            if ch == '"' {
                quoted = true;
                continue;
            }
            let rest = &line[at..];
            if let Some(comment) = rest.strip_prefix('┄').or_else(|| rest.strip_prefix("//")) {
                out.push(comment.trim().to_string());
                break;
            }
        }
    }
    out
}

#[test]
fn g10_keeps_a_comment_in_every_position() {
    // [G10]: the formatter keeps comments. A comment is put after each line,
    // and on a line of its own before each line, of every Rails file of the
    // suite, one position at a time. The reader may refuse the text (a
    // comment in column 1 where a rail or a continuation is required); what
    // it reads, the formatter prints with every comment, in order, and is
    // the identity on.
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests");
    let mut files = Vec::new();
    for directory in [
        "slice1_surface",
        "slice2_surface",
        "slice3_surface",
        "slice4_surface",
        "format",
        "loop_names",
        "kernels",
    ] {
        for entry in std::fs::read_dir(root.join(directory)).expect(directory) {
            let path = entry.expect("an entry").path();
            if path.extension().is_some_and(|ext| ext == "rails") {
                files.push(path);
            }
        }
    }
    files.sort();
    let (mut kept, mut refused) = (0, 0);
    for path in files {
        let source = std::fs::read_to_string(&path).expect("readable");
        surface::format(&source).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
        let lines: Vec<&str> = source.lines().collect();
        for (index, line) in lines.iter().enumerate() {
            if line.trim_start().starts_with("//!") {
                continue;
            }
            let rails: String = line
                .chars()
                .take_while(|c| matches!(c, '│' | '║' | '┆' | ' '))
                .collect();
            let rails = rails.trim_end();
            let space = if rails.is_empty() { "" } else { " " };
            let before = {
                let mut changed: Vec<String> = lines.iter().map(|l| l.to_string()).collect();
                changed.insert(index, format!("{rails}{space}┄ probe {index}"));
                changed
            };
            let after = (!line.trim().is_empty() && comments_of(line).is_empty()).then(|| {
                let mut changed: Vec<String> = lines.iter().map(|l| l.to_string()).collect();
                changed[index] = format!("{line} ┄ probe {index}");
                changed
            });
            for changed in std::iter::once(before).chain(after) {
                let text = changed.join("\n") + "\n";
                let Ok(printed) = surface::format(&text) else {
                    refused += 1;
                    continue;
                };
                assert_eq!(
                    comments_of(&printed),
                    comments_of(&text),
                    "{}: a comment at line {} is lost or out of order",
                    path.display(),
                    index + 1
                );
                assert_eq!(
                    surface::format(&printed).unwrap(),
                    printed,
                    "{}: with a comment at line {} the formatter is not the identity on its output",
                    path.display(),
                    index + 1
                );
                kept += 1;
            }
        }
    }
    assert!(
        kept >= 1000 && refused * 8 < kept,
        "{kept} positions kept, {refused} refused"
    );
}
