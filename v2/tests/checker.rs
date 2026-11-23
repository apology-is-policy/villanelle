//! Phase 3 checker conformance tests for slice 1.
//!
//! Tests every checking clause of `docs/v2/core.md` (`[K1]`–`[K8]`,
//! `[N1]`–`[N5]`, `[C2]`, `[O1]`, `[O2]`, `[O4]`, `[O6]`, `[P1]`–`[P8]`,
//! `[F3]`) and every fact-logic, certificate and counterexample clause of
//! `docs/v2/facts.md` (`[S1]`–`[S6]`, `[I1]`–`[I6]`, `[I8]`–`[I10]`, `[I13]`,
//! `[A1]`, `[A2]`, `[A7]`–`[A9]`, `[J1]`–`[J6]`, `[V1]`–`[V5]`,
//! `[M1]`–`[M6]`).

use villanelle_v2::check::{self, CheckedProgram};
use villanelle_v2::counts::{self, Counts};
use villanelle_v2::facts;
use villanelle_v2::generate;
use villanelle_v2::int::Int;
use villanelle_v2::kernel;
use villanelle_v2::mutate::{self, Class};
use villanelle_v2::oracle::Config;
use villanelle_v2::rng::Rng;
use villanelle_v2::terms::{Certificate, End, Instance, Part, Proof, Step};
use villanelle_v2::{
    certificate, expand, fuzz, load, load_surface, resolve, surface, syntax, text, typed,
};

fn check_core(source: &str) -> Result<CheckedProgram, check::Error> {
    let program = load(source).unwrap_or_else(|error| panic!("resolve failed: {error}\n{source}"));
    check::check(&program)
}

fn check_rails(source: &str) -> Result<CheckedProgram, check::Error> {
    let program =
        load_surface(source).unwrap_or_else(|error| panic!("resolve failed: {error}\n{source}"));
    check::check(&program)
}

fn accept_core(clause: &str, source: &str) -> CheckedProgram {
    match check_core(source) {
        Ok(report) => {
            // A kernel that has seen nothing of the check validates every
            // certificate again ([V1]).
            report
                .revalidate()
                .unwrap_or_else(|error| panic!("[{clause}] the kernel rejected {error}"));
            report
        }
        Err(error) => panic!("[{clause}] expected acceptance, got: {error}\n{source}"),
    }
}

/// What the kernel says of `certificate` as an answer to the question that
/// `proved` answered.
fn kernel_says(
    report: &CheckedProgram,
    proved: &check::Proved,
    certificate: &Certificate,
) -> Result<(), String> {
    kernel::validate(&report.bodies[proved.body].query(proved.goal), certificate)
}

fn reject_core(clause: &str, source: &str) -> check::Error {
    match check_core(source) {
        Ok(_) => panic!(
            "[{clause}] expected rejection by [{clause}], but program was accepted:\n{source}"
        ),
        Err(error) => {
            assert_eq!(
                error.clause, clause,
                "[{clause}] expected rejection by [{clause}], got [{}]: {error}\n{source}",
                error.clause
            );
            error
        }
    }
}

fn accept_rails(clause: &str, source: &str) -> CheckedProgram {
    match check_rails(source) {
        Ok(report) => report,
        Err(error) => panic!("[{clause}] expected Rails acceptance, got: {error}\n{source}"),
    }
}

fn reject_rails(clause: &str, source: &str) -> check::Error {
    match check_rails(source) {
        Ok(_) => panic!(
            "[{clause}] expected Rails rejection by [{clause}], but program was accepted:\n{source}"
        ),
        Err(error) => {
            assert_eq!(
                error.clause, clause,
                "[{clause}] expected Rails rejection by [{clause}], got [{}]: {error}\n{source}",
                error.clause
            );
            error
        }
    }
}

#[test]
fn coverage_and_history_clauses_k1_to_k8() {
    // [K1], [K2], [K3], [K4], [K5], [K7]: Boolean selectors, site structure,
    // test totality, and full coverage across split dispositions.
    accept_core(
        "K1-K7",
        "
        extern control probe(x : u32) ■ { a │ b │ c }

        pub control cover(x : u32) ■ { ok {v : u32} │ nope } :=
            ⊤ ▷ d : Δ probe(x) ▸ a │ b │ c
            d.a ▷ t : ? x > 10
            d.a ∧ t.true ▷ ■ ok {x}
            d.a ∧ ¬t.true ▷ ■ nope
            d.b ∨ d.c ▷ ■ nope
        ",
    );

    // [K7] rejection: `d.c` is not disposed and can reach the end of the body.
    let err = reject_core(
        "K7",
        "
        extern control probe(x : u32) ■ { a │ b │ c }

        pub control uncover(x : u32) ■ { ok │ nope } :=
            ⊤ ▷ d : Δ probe(x) ▸ a │ b │ c
            d.a ▷ ■ ok
            d.b ▷ ■ nope
        ",
    );
    let cex = err.counterexample.expect("counterexample for K7");
    assert!(
        cex.history.contains(&("d".to_string(), "c".to_string())),
        "counterexample history should witness d.c: {cex}"
    );

    // [K6], [K7], [K8]: Loop body coverage and exact loop arm reachability.
    // Here `□ unused` is guarded by `t.true ∧ t.false`, so `[K8]` makes
    // `lp.unused ↔ ⊥`; the body after the loop only needs to dispose `lp.done`.
    accept_core(
        "K6-K8",
        "
        pub control loop_exact(n : u32) ⊢ n ≤ 100 ■ { finished {v : u32} } :=
            ⊤ ▷ lp : ↻ step(i : u32 := 0) {
                ⊢ i ≤ n
                ⊤ ▷ t : ? i < n
                t.true ∧ t.false ▷ □ unused
                t.true ▷ ↑ step(i + 1)
                t.false ▷ □ done {i}
            } ▸ done {res} │ unused
            lp.done ▷ ■ finished {res}
        ",
    );

    // [K6], [K7] rejection inside a loop body: `t.false` neither repeats with
    // `↑` nor leaves with `□`/`■`/`⊥`.
    reject_core(
        "K7",
        "
        pub control loop_uncovered(n : u32) ⊢ n ≤ 100 ■ { finished } :=
            ⊤ ▷ lp : ↻ step(i : u32 := 0) {
                ⊢ i ≤ n
                ⊤ ▷ t : ? i < n
                t.true ▷ □ done
            } ▸ done
            lp.done ▷ ■ finished
        ",
    );
}

#[test]
fn facts_and_renaming_clauses_n1_to_n5() {
    // [N1], [N2], [N3], [N4], [N5]: Parameter bounds + precondition at entry,
    // binding and assignment equality facts, `⊢` assumption, test and decision
    // outcome conditions, and SSA renaming across assignments and loops.
    accept_core(
        "N1-N5",
        "
        extern control step_down(x : u32) ⊢ x > 0
            ■ { next {y : u32} ⇐ y = x - 1 }

        pub control facts_flow(a : u32) ⊢ a ≥ 10 ∧ a ≤ 200
            ■ { done {out : u32} ⇐ out = a } :=
            ⊤ ▷ ~cur : u32 := a
            ⊤ ▷ d : Δ step_down(cur) ▸ next {y}
            d.next ▷ ⊢ y = a - 1
            d.next ▷ cur ← y + 1
            d.next ▷ ⊢ cur = a
            d.next ▷ ■ done {cur}
        ",
    );

    // [N5] rejection: after `cur ← cur + 1`, the old fact `cur = 5` no longer
    // holds for the new version of `cur`.
    reject_core(
        "P1",
        "
        pub control stale_version() ■ { done } :=
            ⊤ ▷ ~cur : u32 := 5
            ⊤ ▷ cur ← cur + 1
            ⊤ ▷ ⊢ cur = 5
            ⊤ ▷ ■ done
        ",
    );

    // [N5] rejection across a loop boundary: `acc` is modified inside the loop,
    // so `acc = 0` before the loop does not survive into or after the loop
    // without an invariant.
    reject_core(
        "P1",
        "
        pub control loop_clobbers_outer(n : u32) ■ { done } :=
            ⊤ ▷ ~acc : u32 := 0
            ⊤ ▷ lp : ↻ step(i : u32 := 0) {
                ⊤ ▷ t : ? i < n
                t.true ▷ acc ← 1
                t.true ▷ □ left
                t.false ▷ □ left
            } ▸ left
            lp.left ▷ ⊢ acc = 0
            lp.left ▷ ■ done
        ",
    );
}

#[test]
fn contract_acknowledgement_c2() {
    // [C2] acceptance: every alternative of the operation is listed.
    accept_core(
        "C2",
        "
        extern control two_way(x : u32) ■ { yes │ no }

        pub control handle_both(x : u32) ■ { done } :=
            ⊤ ▷ d : Δ two_way(x) ▸ yes │ no
            d.yes ∨ d.no ▷ ■ done
        ",
    );

    // [C2] rejection on a typed program whose decision lists fewer arms than
    // the callee's contract.
    let tree = text::parse(
        "
        extern control two_way(x : u32) ■ { yes │ no }

        pub control handle_one(x : u32) ■ { done } :=
            ⊤ ▷ d : Δ two_way(x) ▸ yes │ no
            d.yes ∨ d.no ▷ ■ done
        ",
    )
    .unwrap();
    let mut program = resolve::resolve(&tree).unwrap();
    let body = program.controls[1].body.as_mut().unwrap();
    if let villanelle_v2::typed::Command::Decide { arms, .. } =
        &mut body.bodies[0].statements[0].command
    {
        arms.pop();
    }
    let err = check::check(&program).expect_err("missing arm must fail C2");
    assert_eq!(err.clause, "C2");
}

#[test]
fn availability_clauses_o1_o2_o4_o6() {
    // [O1], [O2], [O4], [O6] acceptance: `v` is bound on disjoint histories
    // (`t.true` and `t.false`), read after the join, and a mutable outer
    // variable `m` bound on `t.true` is updated inside a loop and read under
    // `t.true`.
    accept_core(
        "O1-O6",
        "
        pub control avail_ok(flag : bool) ■ { done {res : u32} } :=
            ⊤ ▷ t : ? flag
            t.true ▷ v : u32 := 10
            t.false ▷ v : u32 := 20
            t.true ▷ ~m : u32 := 1
            ⊤ ▷ lp : ↻ step(i : u32 := 0) {
                t.true ▷ m ← 2
                ⊤ ▷ □ out
            } ▸ out
            t.true ▷ ⊢ m ≥ 1
            ⊤ ▷ ■ done {v}
        ",
    );

    // [O1] rejection: two bindings of `v` can both execute on the same feasible
    // history (`t1.true ∧ t2.true`).
    reject_core(
        "O1",
        "
        pub control double_bind(a : bool, b : bool) ■ { done {res : u32} } :=
            ⊤ ▷ t1 : ? a
            ⊤ ▷ t2 : ? b
            t1.true ▷ v : u32 := 1
            t2.true ▷ v : u32 := 2
            t1.true ∧ t2.true ▷ ■ done {v}
            ¬(t1.true ∧ t2.true) ▷ ■ done {0}
        ",
    );

    // [O2] rejection: `v` is bound only on `t.true`, but read on `⊤`.
    reject_core(
        "O2",
        "
        pub control read_unbound(flag : bool) ■ { done {res : u32} } :=
            ⊤ ▷ t : ? flag
            t.true ▷ v : u32 := 10
            ⊤ ▷ ■ done {v}
        ",
    );

    // [O4] rejection: mutable `~m` is bound only on `t.true`, but assigned on `⊤`.
    reject_core(
        "O4",
        "
        pub control assign_unbound(flag : bool) ■ { done } :=
            ⊤ ▷ t : ? flag
            t.true ▷ ~m : u32 := 10
            ⊤ ▷ m ← 20
            ⊤ ▷ ■ done
        ",
    );
}

#[test]
fn obligation_clauses_p1_to_p8() {
    // [P1] acceptance and rejection.
    accept_core(
        "P1",
        "
        pub control p1_ok(x : u32) ⊢ x < 100 ■ { done } :=
            ⊤ ▷ ⊢ x ≤ 99
            ⊤ ▷ ■ done
        ",
    );
    reject_core(
        "P1",
        "
        pub control p1_bad(x : u32) ⊢ x < 100 ■ { done } :=
            ⊤ ▷ ⊢ x ≤ 50
            ⊤ ▷ ■ done
        ",
    );

    // [P2] acceptance, entry rejection, and repetition (`↑`) rejection.
    accept_core(
        "P2",
        "
        pub control p2_ok(n : u32) ⊢ n ≤ 10 ■ { done } :=
            ⊤ ▷ lp : ↻ step(i : u32 := 0) {
                ⊢ i ≤ n
                ⊤ ▷ t : ? i < n
                t.true ▷ ↑ step(i + 1)
                t.false ▷ □ out
            } ▸ out
            lp.out ▷ ■ done
        ",
    );
    reject_core(
        "P2",
        "
        pub control p2_bad_entry(n : u32) ■ { done } :=
            ⊤ ▷ lp : ↻ step(i : u32 := 5) {
                ⊢ i ≤ 3
                ⊤ ▷ □ out
            } ▸ out
            lp.out ▷ ■ done
        ",
    );
    reject_core(
        "P2",
        "
        pub control p2_bad_again() ■ { done } :=
            ⊤ ▷ lp : ↻ step(i : u32 := 0) {
                ⊢ i ≤ 3
                ⊤ ▷ t : ? i ≤ 3
                t.true ▷ ↑ step(i + 1)
                t.false ▷ □ out
            } ▸ out
            lp.out ▷ ■ done
        ",
    );

    // [P3] acceptance and rejection for function and control preconditions.
    accept_core(
        "P3",
        "
        function dec(x : u32) ⊢ x > 0 : u32 := x - 1
        extern control req_pos(x : u32) ⊢ x > 0 ■ { ok }

        pub control p3_ok(x : u32) ■ { done } :=
            ⊤ ▷ t : ? x > 0
            t.true ▷ y : u32 := dec(x)
            t.true ▷ d : Δ req_pos(x) ▸ ok
            t.true ∧ d.ok ▷ ■ done
            t.false ▷ ■ done
        ",
    );
    reject_core(
        "P3",
        "
        function dec(x : u32) ⊢ x > 0 : u32 := x - 1

        pub control p3_bad_fn(x : u32) ■ { done {v : u32} } :=
            ⊤ ▷ ■ done {dec(x)}
        ",
    );
    reject_core(
        "P3",
        "
        extern control req_pos(x : u32) ⊢ x > 0 ■ { ok }

        pub control p3_bad_call(x : u32) ■ { done } :=
            ⊤ ▷ d : Δ req_pos(x) ▸ ok
            d.ok ▷ ■ done
        ",
    );

    // [P4] acceptance and rejection for exit contract condition `⇐ φₐ`.
    accept_core(
        "P4",
        "
        pub control p4_ok(x : u32) ⊢ x < 10
            ■ { small {v : u32} ⇐ v ≤ 10 } :=
            ⊤ ▷ ■ small {x + 1}
        ",
    );
    reject_core(
        "P4",
        "
        pub control p4_bad(x : u32) ⊢ x < 10
            ■ { small {v : u32} ⇐ v < 10 } :=
            ⊤ ▷ ■ small {x + 1}
        ",
    );

    // [P5]: Checked arithmetic, unary negation, fixed-width bounds (`[A1]`),
    // target-independent `usize` bounds (`[A2]`), and non-zero divisors.
    accept_core(
        "P5",
        "
        pub control p5_ok(a : u8, b : i8, n : usize) ⊢ a ≤ 200 ∧ b > -128 ∧ n ≤ 1000
            ■ { done {x : u8, y : i8, z : usize} } :=
            ⊤ ▷ t : ? a > 0
            t.true ▷ q : u8 := 200 ÷ a
            t.true ▷ r : u8 := 200 mod a
            ⊤ ▷ ■ done {a + 55, -b, n + 1}
        ",
    );
    // Overflow on `u8`: `a + 56` can reach 256 when `a = 200`.
    reject_core(
        "P5",
        "
        pub control p5_overflow_u8(a : u8) ⊢ a ≤ 200 ■ { done {x : u8} } :=
            ⊤ ▷ ■ done {a + 56}
        ",
    );
    // Overflow on unary negation of `i8`: `-(-128) = 128 > 127`.
    reject_core(
        "P5",
        "
        pub control p5_negate_i8_min(b : i8) ■ { done {y : i8} } :=
            ⊤ ▷ ■ done {-b}
        ",
    );
    // `[A2]` on `usize`: `n + 1` without an upper bound on `n` is rejected,
    // while `n ≤ 4294967294` (`2^32 - 2`) is accepted because `high(usize) ≥ 2^32 - 1`.
    accept_core(
        "A2-P5",
        "
        pub control usize_within_32bit(n : usize) ⊢ n ≤ 4294967294 ■ { done {z : usize} } :=
            ⊤ ▷ ■ done {n + 1}
        ",
    );
    reject_core(
        "P5",
        "
        pub control usize_unbounded(n : usize) ■ { done {z : usize} } :=
            ⊤ ▷ ■ done {n + 1}
        ",
    );
    // Division and remainder by a possibly-zero divisor fail [P5].
    reject_core(
        "P5",
        "
        pub control p5_div_zero(a : u32, b : u32) ■ { done {q : u32} } :=
            ⊤ ▷ ■ done {a ÷ b}
        ",
    );
    reject_core(
        "P5",
        "
        pub control p5_rem_zero(a : u32, b : u32) ■ { done {r : u32} } :=
            ⊤ ▷ ■ done {a mod b}
        ",
    );

    // [P6]: `⊥` is accepted when unreachable and rejected when reachable.
    accept_core(
        "P6",
        "
        extern control checked_sub(a : u32, b : u32)
            ■ { difference {value : u32} ⇐ value = a - b │ underflow ⇐ a < b }

        pub control spend(total : u32, used : u32) ■ { left {value : u32} │ over } :=
            ⊤ ▷ t : ? used > total
            t.true ▷ ■ over
            t.false ▷ d : Δ checked_sub(total, used) ▸ difference {value} │ underflow
            t.false ∧ d.underflow ▷ ⊥
            t.false ∧ d.difference ▷ ■ left {value}
        ",
    );
    reject_core(
        "P6",
        "
        extern control checked_sub(a : u32, b : u32)
            ■ { difference {value : u32} ⇐ value = a - b │ underflow ⇐ a < b }

        pub control spend_bug(total : u32, used : u32) ■ { left {value : u32} │ over } :=
            ⊤ ▷ t : ? used ≥ total
            t.false ▷ ■ over
            t.true ▷ d : Δ checked_sub(total, used) ▸ difference {value} │ underflow
            t.true ∧ d.underflow ▷ ⊥
            t.true ∧ d.difference ▷ ■ left {value}
        ",
    );

    // [P7]: Short-circuit evaluation order of `∧` and `∨` (`e₂` is checked
    // under `e₁` for `∧`, and under `¬e₁` for `∨`).
    accept_core(
        "P7",
        "
        pub control short_circuit_ok(x : u32) ■ { done {a : bool, b : bool} } :=
            ⊤ ▷ a : bool := x > 0 ∧ 100 ÷ x > 2
            ⊤ ▷ b : bool := x = 0 ∨ 100 ÷ x > 2
            ⊤ ▷ ■ done {a, b}
        ",
    );
    reject_core(
        "P5",
        "
        pub control short_circuit_bad(x : u32) ■ { done {a : bool} } :=
            ⊤ ▷ a : bool := x = 0 ∧ 100 ÷ x > 2
            ⊤ ▷ ■ done {a}
        ",
    );

    // [P8]: Function declarations have their body obligations checked under
    // parameter range facts and the function's precondition.
    accept_core(
        "P8",
        "
        function safe_step(x : u8) ⊢ x < 255 : u8 := x + 1

        pub control use_fn(x : u8) ⊢ x < 100 ■ { done {v : u8} } :=
            ⊤ ▷ ■ done {safe_step(x)}
        ",
    );
    reject_core(
        "P5",
        "
        function unsafe_step(x : u8) : u8 := x + 1

        pub control use_fn() ■ { done } :=
            ⊤ ▷ ■ done
        ",
    );
}

#[test]
fn effects_clause_f3() {
    // [F3] acceptance: `pub` control lists `uses io`; dead call on an
    // infeasible history does not require the effect; private surface control
    // infers `uses io`.
    accept_core(
        "F3",
        "
        extern control write_byte(b : u8) ■ { ok } uses io

        pub control allowed(b : u8) ■ { done } uses io :=
            ⊤ ▷ d : Δ write_byte(b) ▸ ok
            d.ok ▷ ■ done

        pub control dead_effect_call(b : u8) ■ { done } :=
            ⊤ ▷ t : ? b < 0
            t.true ▷ d : Δ write_byte(b) ▸ ok
            t.true ∧ d.ok ▷ ■ done
            t.false ▷ ■ done
        ",
    );

    // [F3] rejection in core: calling `write_byte` on a feasible history without `uses io`.
    reject_core(
        "F3",
        "
        extern control write_byte(b : u8) ■ { ok } uses io

        pub control forbidden(b : u8) ■ { done } :=
            ⊤ ▷ d : Δ write_byte(b) ▸ ok
            d.ok ▷ ■ done
        ",
    );

    // [F3] in Rails surface syntax: private control infers `uses io`, while a
    // `pub` caller without `uses io` is rejected by `[F3]`.
    accept_rails(
        "F3-surface-ok",
        "\
extern control write_byte(b: u8) ■ ok uses io

control helper(b: u8) ■ done
│ write_byte(b)
│ ■ done
╵

pub control entry(b: u8) ■ done uses io
│ helper(b)
│ ■ done
╵
",
    );
    reject_rails(
        "F3",
        "\
extern control write_byte(b: u8) ■ ok uses io

control helper(b: u8) ■ done
│ write_byte(b)
│ ■ done
╵

pub control entry(b: u8) ■ done
│ helper(b)
│ ■ done
╵
",
    );
}

#[test]
fn fact_logic_axioms_a7_a8_a9_i10_and_chvatal_gomory_j3() {
    // [A7]: Division and remainder by a constant (`e₁ = k·q + r`, `0 ≤ r < |k|`).
    accept_core(
        "A7",
        "
        pub control div_mod_const(x : u32) ⊢ x ≤ 100 ■ { done } :=
            ⊤ ▷ q : u32 := x ÷ 4
            ⊤ ▷ r : u32 := x mod 4
            ⊤ ▷ ⊢ r ≤ 3 ∧ q ≤ 25 ∧ x = 4 * q + r
            ⊤ ▷ ■ done
        ",
    );

    // [A8]: Division and remainder by a non-constant term (`t ≥ 1, s ≥ 0` and
    // `t ≤ -1, s ≥ 0`).
    accept_core(
        "A8",
        "
        pub control div_mod_var(a : u32, d : u32, s : i32, t : i32)
            ⊢ d > 0 ∧ s ≥ 0 ∧ s ≤ 100 ∧ t < 0 ∧ t ≥ -50
            ■ { done } :=
            ⊤ ▷ r : u32 := a mod d
            ⊤ ▷ q : u32 := a ÷ d
            ⊤ ▷ ⊢ r < d ∧ r ≤ a ∧ q ≤ a
            ⊤ ▷ qs : i32 := s ÷ t
            ⊤ ▷ rs : i32 := s mod t
            ⊤ ▷ ⊢ qs ≥ -s ∧ qs ≤ 0 ∧ rs ≥ 0 ∧ rs ≤ -t - 1
            ⊤ ▷ ■ done
        ",
    );

    // [A9]: Product bounds from declared intervals (`[0, 7] * [0, 7] ⊆ [0, 49]`,
    // `[-7, 7] * [-7, 7] ⊆ [-49, 49]`, and `u8 * u8` fitting in `u16`).
    accept_core(
        "A9",
        "
        pub control product_bounds(a : u8, s : i8) ■ { done {p : u8, q : i8} } :=
            ⊤ ▷ p : u8 := (a mod 8) * ((a ÷ 2) mod 8)
            ⊤ ▷ ⊢ p ≤ 49
            ⊤ ▷ q : i8 := (s mod 8) * (-(s mod 8))
            ⊤ ▷ ⊢ q ≥ -49 ∧ q ≤ 49
            ⊤ ▷ ■ done {p, q}
        ",
    );

    // [I10]: Pure operation congruence (`alt_f` and `pay_{f, a, i}`): calling a
    // pure extern control twice with equal arguments cannot take two different
    // alternatives, and on the same alternative yields equal payloads.
    accept_core(
        "I10",
        "
        extern control lookup(key : u32)
            ■ { found {val : u32} │ missing }

        pub control pure_congruence(k1 : u32, k2 : u32) ⊢ k1 = k2 ■ { done } :=
            ⊤ ▷ d1 : Δ lookup(k1) ▸ found {v1} │ missing
            ⊤ ▷ d2 : Δ lookup(k2) ▸ found {v2} │ missing
            d1.found ∧ d2.missing ▷ ⊥
            d1.missing ∧ d2.found ▷ ⊥
            d1.found ∧ d2.found ▷ ⊢ v1 = v2
            d1.found ∧ d2.found ▷ ■ done
            d1.missing ∧ d2.missing ▷ ■ done
        ",
    );

    // [V3] Round: `x = 2 * q` and `x = 2 * r + 1` have rational solutions and
    // no integer one. Replacing `x` leaves `2 * q - 2 * r = 1`, which rounds
    // to a contradiction.
    let report = accept_core(
        "V3",
        "
        pub control parity_impossible(x : i32, q : i32, r : i32)
            ⊢ q ≥ -100 ∧ q ≤ 100 ∧ r ≥ -100 ∧ r ≤ 100
            ■ { done } :=
            ⊤ ▷ t1 : ? x = 2 * q
            ⊤ ▷ t2 : ? x = 2 * r + 1
            t1.true ∧ t2.true ▷ ⊥
            ¬(t1.true ∧ t2.true) ▷ ■ done
        ",
    );
    let saw_round = report.certificates.iter().any(|proved| {
        proved
            .certificate
            .lemmas()
            .any(|lemma| lemma.proof.rounds())
    });
    assert!(saw_round, "expected a [V3] Round step in a certificate");
}

/// Review finding RC12. The procedure is exact on integers ([J5]): a
/// precondition with rational solutions and no integer one makes `⊥`
/// unreachable, and the proof splits. It gives up only at the counted limit
/// of [J6], which is reported as the compiler's limit and never as a verdict
/// on the program.
#[test]
fn the_procedure_is_exact_on_integers_and_gives_up_only_at_a_counted_limit() {
    let source = "
        pub control c(x : i32, y : i32)
            ⊢ 11 * x + 13 * y ≥ 27 ∧ 11 * x + 13 * y ≤ 45 ∧ 7 * x - 9 * y ≥ -10 ∧ 7 * x - 9 * y ≤ 4
            ■ { r } :=
            ⊤ ▷ ⊥
    ";
    let report = accept_core("J5", source);
    assert!(
        report.certificates.iter().any(|proved| proved
            .certificate
            .lemmas()
            .any(|lemma| lemma.proof.splits() > 0)),
        "only a split refutes the precondition"
    );

    // With three steps the same question has no answer. That is an error
    // of its own kind, with no counterexample.
    let error = facts::with_step_limit(3, || check_core(source)).expect_err("no answer");
    assert_eq!(error.clause, "J6", "{error}");
    assert!(error.counterexample.is_none());
    assert!(
        error.to_string().contains("limit of 3 steps"),
        "the report names the limit: {error}"
    );

    // An obligation that does not hold is refuted with a model, not with a
    // limit: `x` and `y` may be 2 and 1.
    let error = reject_core(
        "P6",
        "
        pub control c(x : i32, y : i32)
            ⊢ 11 * x + 13 * y ≥ 27 ∧ 11 * x + 13 * y ≤ 45 ∧ 7 * x - 9 * y ≥ -10 ∧ 7 * x - 9 * y ≤ 5
            ■ { r } :=
            ⊤ ▷ ⊥
        ",
    );
    assert!(error.counterexample.is_some());
}

/// Review finding RC12, the rest of it. The procedure is complete without
/// bounds. The precondition speaks of the difference of two parameters, so
/// its four rows bound neither, and the splits on one of them do not end:
/// the answer was the limit of [J6]. The Omega test refutes the rows by
/// their splinters, and the kernel validates its proof from the text.
#[test]
fn a_condition_without_a_bound_is_decided_by_the_omega_test() {
    let source = "
        pub control c(u : i64, v : i64, y : i64)
            ⊢ 11 * (u - v) + 13 * y ≥ 27 ∧ 11 * (u - v) + 13 * y ≤ 45 ∧ 7 * (u - v) - 9 * y ≥ -10 ∧ 7 * (u - v) - 9 * y ≤ 4
            ■ { r } :=
            ⊤ ▷ ⊥
    ";
    let before = counts::now();
    let report = accept_core("J5", source);
    let done = counts::now().since(&before);
    assert_eq!(done.omega_tests, 1, "{done}");
    assert_eq!(done.splinters, 16, "{done}");
    assert!(
        report.certificates.iter().any(|proved| proved
            .certificate
            .lemmas()
            .any(|lemma| lemma.proof.splits() >= 16)),
        "the proof splits for every splinter"
    );
    let text = report.certificate_text().expect("a text");
    assert_eq!(
        certificate::validate(&text),
        Ok(report.certificates.len()),
        "the text validates"
    );

    // One more value of the last row, and the obligation does not hold:
    // the difference may be 2 and `y` 1.
    let error = reject_core(
        "P6",
        "
        pub control c(u : i64, v : i64, y : i64)
            ⊢ 11 * (u - v) + 13 * y ≥ 27 ∧ 11 * (u - v) + 13 * y ≤ 45 ∧ 7 * (u - v) - 9 * y ≥ -10 ∧ 7 * (u - v) - 9 * y ≤ 5
            ■ { r } :=
            ⊤ ▷ ⊥
        ",
    );
    assert!(error.counterexample.is_some());

    // The limit of [J6] remains for a search that is too long. With
    // `1 ≤ m·x - (m - 1)·y ≤ 3` and `4 ≤ y ≤ m` there is no `x`, every `y`
    // has a rational one, and the splinters are about `m`: a million.
    let wedge = "
        pub control c(x : i64, y : i64)
            ⊢ 1000000 * x - 999999 * y ≥ 1 ∧ 1000000 * x - 999999 * y ≤ 3 ∧ y ≥ 4 ∧ y ≤ 1000000
            ■ { r } :=
            ⊤ ▷ ⊥
    ";
    let before = counts::now();
    let error = facts::with_step_limit(100_000, || check_core(wedge)).expect_err("no answer");
    let done = counts::now().since(&before);
    assert_eq!(error.clause, "J6", "{error}");
    assert!(error.counterexample.is_none());
    assert!(done.splinters > 1_000, "{done}");
}

/// Review finding RC11. Whether a history is feasible is an entailment like
/// any other: a history that is ruled out is ruled out by a certificate that
/// the kernel validated ([V1]), and the certificate is listed.
#[test]
fn an_infeasible_history_is_ruled_out_by_a_validated_certificate() {
    let report = accept_core(
        "V1",
        "
        extern control read(port : u32) ■ { value {v : u32} │ closed } uses io

        pub control c(a : u8) ■ { r } :=
            ⊤ ▷ t : ? a > 255
            t.true ▷ d : Δ read(1) ▸ value {v} │ closed
            ⊤ ▷ ■ r
        ",
    );
    let feasibility: Vec<_> = report
        .certificates
        .iter()
        .filter(|proved| proved.clause == "N1")
        .collect();
    assert!(
        !feasibility.is_empty(),
        "the decision on `read` needs `uses io` unless its history is infeasible"
    );
    for proved in feasibility {
        kernel_says(&report, proved, &proved.certificate)
            .expect("the kernel validates the certificate");
    }
}

#[test]
fn certificate_kernel_rejects_corrupted_proofs_v1_to_v5() {
    let report = accept_core(
        "V1-V5",
        "
        extern control checked_sub(a : u32, b : u32)
            ■ { difference {value : u32} ⇐ value = a - b │ underflow ⇐ a < b }

        pub control spend(total : u32, used : u32) ■ { left {value : u32} │ over } :=
            ⊤ ▷ t : ? used > total
            t.true ▷ ■ over
            t.false ▷ d : Δ checked_sub(total, used) ▸ difference {value} │ underflow
            t.false ∧ d.underflow ▷ ⊥
            t.false ∧ d.difference ▷ ⊢ value ≤ total
            t.false ∧ d.difference ▷ ■ left {value}
        ",
    );
    assert!(
        !report.certificates.is_empty(),
        "expected validated certificates"
    );
    for proved in &report.certificates {
        kernel_says(&report, proved, &proved.certificate)
            .expect("the kernel validates every certificate of the check");
        let printed = proved.certificate.to_string();
        assert!(
            printed.contains("certificate (premises:"),
            "the text of a certificate:\n{printed}"
        );
    }

    // The certificate of `value ≤ total`: it needs the range of `used`
    // ([A1]), the fact that `checked_sub` states, and a lemma.
    let proved = report
        .certificates
        .iter()
        .find(|proved| {
            proved.certificate.lemmas().next().is_some()
                && proved.certificate.instances().next().is_some()
        })
        .expect("a certificate with an instance and a lemma");
    let whole = &proved.certificate;
    let without = |drop: fn(&Part) -> bool| Certificate {
        parts: whole
            .parts
            .iter()
            .filter(|part| !drop(part))
            .cloned()
            .collect(),
    };
    let with_proof = |proof: Proof| Certificate {
        parts: whole
            .parts
            .iter()
            .map(|part| match part {
                Part::Lemma(lemma) => {
                    let mut lemma = lemma.clone();
                    lemma.proof = proof.clone();
                    Part::Lemma(lemma)
                }
                other => other.clone(),
            })
            .collect(),
    };
    let with_part = |part: Part| {
        let mut certificate = whole.clone();
        certificate.parts.push(part);
        certificate
    };
    let refused = |certificate: &Certificate, why: &str| {
        assert!(
            kernel_says(&report, proved, certificate).is_err(),
            "the kernel must refuse {why}"
        );
    };

    // [V2]: the Boolean step is recomputed. Without its lemmas, without its
    // instances or without its facts, the certificate leaves a case open.
    refused(
        &without(|part| matches!(part, Part::Lemma(_))),
        "a certificate without its lemmas",
    );
    refused(
        &without(|part| matches!(part, Part::Instance(_))),
        "a certificate without its instances",
    );
    refused(
        &without(|part| matches!(part, Part::Fact(_))),
        "a certificate without its facts",
    );

    // [V3]: the steps of a proof.
    refused(
        &with_proof(Proof {
            steps: vec![
                Step::Literal(0),
                Step::Combine(vec![(0, Int::from_i128(-1))]),
            ],
            end: End::Close(1),
        }),
        "a sum with a negative multiplier",
    );
    refused(
        &with_proof(Proof {
            steps: vec![
                Step::Literal(0),
                Step::Combine(vec![(99, Int::from_i128(1))]),
            ],
            end: End::Close(1),
        }),
        "a sum of a row that is not on the path",
    );
    refused(
        &with_proof(Proof {
            steps: vec![Step::Literal(0)],
            end: End::Close(0),
        }),
        "a branch that closes on a row that is no contradiction",
    );

    // [V2], review finding RC9: an instance is named, and the kernel makes
    // its formula. A name that is not the name of an instance is refused,
    // even beside a certificate that is complete without it.
    let terms = report.bodies[proved.body].terms.len();
    refused(
        &with_part(Part::Instance(Instance::Term(terms))),
        "an instance of a term that the query does not have",
    );
    let names: Vec<usize> = whole
        .instances()
        .filter_map(|instance| match instance {
            Instance::Term(term) => Some(*term),
            _ => None,
        })
        .collect();
    refused(
        &with_part(Part::Instance(Instance::Pair(names[0], names[0]))),
        "an instance for two terms of which the theory says nothing together",
    );
    refused(
        &with_part(Part::Instance(Instance::Frame {
            update: names[0],
            element: names[0],
            original: names[0],
        })),
        "a frame instance for a term that is no update",
    );
    refused(
        &with_part(Part::Instance(Instance::Extension {
            structure: 0,
            left: names[0],
            left_fields: Vec::new(),
            right: names[0],
            right_fields: Vec::new(),
        })),
        "an extension instance for a struct that the program does not have",
    );

    // [V2]: a premise is read from the checker's list, by its position.
    let body = &report.bodies[proved.body];
    refused(
        &with_part(Part::Fact(body.facts.len())),
        "a fact that the checker did not state",
    );
    refused(
        &with_part(Part::Structure(body.structure.len())),
        "a formula that is not in `Ω`",
    );

    // [V1], review finding RC10: the kernel is told the goal by the checker.
    // The same certificate is no answer to another question: here, whether
    // the premises alone have no model.
    let other = body.query(villanelle_v2::bdd::TRUE);
    assert!(
        kernel::validate(&other, whole).is_err(),
        "the kernel must refuse a certificate as the answer to another goal"
    );
    // And the kernel reads only what it is given: a certificate with no
    // part is an answer to a goal that is false, and to no other.
    let nothing = Certificate::default();
    assert!(kernel::validate(&body.query(villanelle_v2::bdd::FALSE), &nothing).is_ok());
    refused(&nothing, "a certificate that names nothing");
}

#[test]
fn counterexample_clauses_m1_to_m6() {
    // [M1], [M2], [M6]: Counterexample includes history witness, integer
    // valuation satisfying all active facts and negating the obligation, and
    // readable display.
    let err = reject_core(
        "P1",
        "
        pub control cex_basic(x : u8) ⊢ x ≥ 10 ■ { done } :=
            ⊤ ▷ t : ? x < 20
            t.true ▷ ⊢ x < 15
            t.true ▷ ■ done
            t.false ▷ ■ done
        ",
    );
    let cex = err.counterexample.expect("counterexample for P1");
    assert!(cex.history.contains(&("t".to_string(), "true".to_string())));
    let x_str = cex.values.get("x").expect("valuation for x");
    let x_val = Int::parse(x_str).expect("integer value for x");
    assert!(
        x_val >= Int::from_i128(15) && x_val < Int::from_i128(20),
        "x = {x_val} must satisfy 15 <= x < 20"
    );

    // [M3]: Nonlinear incompleteness note when a nonlinear product is treated
    // as an abstract term with `[A9]` bounds.
    let err_nl = reject_core(
        "P1",
        "
        pub control cex_nonlinear(a : u8, b : u8) ■ { done } :=
            ⊤ ▷ p : u8 := (a mod 8) * (b mod 8)
            ⊤ ▷ ⊢ p ≠ 11
            ⊤ ▷ ■ done
        ",
    );
    let cex_nl = err_nl
        .counterexample
        .expect("counterexample for nonlinear P1");
    assert!(
        cex_nl.assumed_remark.is_some(),
        "expected [M3] nonlinear remark on unproved product obligation"
    );
    assert!(
        cex_nl.to_string().contains("depends on `*`"),
        "expected [M3] text in counterexample output:\n{cex_nl}"
    );

    // [M4]: Loop boundary note when an obligation fails inside a loop body.
    let err_loop = reject_core(
        "P1",
        "
        pub control cex_loop(n : u32) ■ { done } :=
            ⊤ ▷ lp : ↻ step(i : u32 := 0) {
                ⊢ i ≤ 10
                ⊤ ▷ ⊢ i < 10
                ⊤ ▷ □ out
            } ▸ out
            lp.out ▷ ■ done
        ",
    );
    let cex_loop = err_loop.counterexample.expect("counterexample inside loop");
    assert!(
        cex_loop.in_loop,
        "expected [M4] loop boundary note inside loop body"
    );
    assert!(
        cex_loop.to_string().contains("start of an iteration"),
        "expected [M4] text in counterexample output:\n{cex_loop}"
    );
}

#[test]
fn surface_files_and_generated_valid_programs_pass_the_checker() {
    for path in [
        "tests/slice1_surface/spend.rails",
        "tests/slice1_surface/show_file.rails",
        "tests/slice1_surface/groups_and_auto.rails",
        "tests/slice1_surface/loops_and_paths.rails",
    ] {
        let source = std::fs::read_to_string(path).unwrap();
        accept_rails(path, &source);
    }

    // The fixed program of the first harness, with 80 sets of numbers: the
    // checker accepts each, and a kernel that saw nothing of the check
    // validates every certificate again.
    let mut total_certificates = 0usize;
    for seed in 1..=80 {
        let mut rng = Rng::new(seed);
        let syntax_program = generate::template(&mut rng);
        let program = resolve::resolve(&syntax_program).unwrap();
        let report = check::check(&program).unwrap_or_else(|error| {
            panic!(
                "seed {seed}: the template is rejected: {error}\n{}",
                syntax_program.print()
            )
        });
        total_certificates += report.certificates.len();
    }
    assert!(
        total_certificates >= 80 * 10,
        "expected at least 800 validated certificates across 80 seeds, got {total_certificates}"
    );

    // Programs of the generator, which differ in shape. Seeds 1 to 40 are
    // tried with their runs in `tests/harness.rs`; these are others.
    let mut total_certificates = 0usize;
    for seed in 41..=50 {
        let syntax_program = fuzz::program_of(seed);
        let program = resolve::resolve(&syntax_program).unwrap();
        let report = check::check(&program).unwrap_or_else(|error| {
            panic!(
                "seed {seed}: a generated program is rejected: {error}\n{}",
                syntax_program.print()
            )
        });
        report
            .revalidate()
            .unwrap_or_else(|error| panic!("seed {seed}: the kernel rejected {error}"));
        total_certificates += report.certificates.len();
    }
    assert!(
        total_certificates >= 10 * 50,
        "expected at least 500 validated certificates across 10 seeds, got {total_certificates}"
    );
}

/// Every mutant of a generated program that has a stuck run is rejected:
/// by `resolve`, or by the checker. The runs of a mutant are drawn for its
/// own preconditions, so that a run that is stuck is the program's doing.
#[test]
fn every_stuck_mutant_of_a_generated_program_is_rejected() {
    let config = Config {
        fuel: 5_000,
        ..Config::default()
    };
    let mut stuck: std::collections::BTreeMap<mutate::Kind, usize> = Default::default();
    for seed in 1..=4 {
        let tree = fuzz::program_of(seed);
        for mutant in mutate::mutate(&tree) {
            let Ok(typed) = resolve::resolve(&mutant.program) else {
                continue;
            };
            let mut rng = Rng::new(seed);
            let runs = generate::entry_runs(&mut rng, &typed, &config, 4);
            let Class::Stuck(state) = mutate::classify(&mutant, &runs, seed, &config) else {
                continue;
            };
            *stuck.entry(mutant.kind).or_default() += 1;
            assert!(
                check::check(&typed).is_err(),
                "seed {seed}: {:?} in `{}` ({}) is stuck (X{} {}: {}) and the checker accepts it:\n{}",
                mutant.kind,
                mutant.control,
                mutant.detail,
                state.state,
                state.clause,
                state.detail,
                mutant.program.print()
            );
        }
    }
    // A dropped invariant leaves no run stuck: the oracle does not ask for
    // one. Every other kind does.
    for kind in [
        mutate::Kind::RemoveArm,
        mutate::Kind::RemoveDisposition,
        mutate::Kind::DropGuard,
        mutate::Kind::ShiftLiteral,
        mutate::Kind::FlipComparison,
    ] {
        assert!(
            stuck.get(&kind).copied().unwrap_or(0) > 0,
            "no stuck mutant of the kind {kind:?}: {stuck:?}"
        );
    }
    let total: usize = stuck.values().sum();
    assert!(total >= 60, "{total} stuck mutants: {stuck:?}");
}

#[test]
fn every_stuck_mutation_and_dropped_invariant_is_rejected_by_the_checker() {
    let config = Config {
        fuel: 5_000,
        ..Config::default()
    };
    let mut stuck_mutants = 0usize;
    let mut dropped_invariants = 0usize;

    for seed in 1..=8 {
        let mut rng = Rng::new(seed);
        let syntax_program = generate::template(&mut rng);
        let typed_program = resolve::resolve(&syntax_program).unwrap();
        let runs = generate::sample_runs(&mut rng, &typed_program, &config);

        for mutant in mutate::mutate(&syntax_program) {
            let class = mutate::classify(&mutant, &runs, seed * 100, &config);
            let is_stuck = matches!(class, Class::Stuck(_));
            let is_drop_inv = mutant.kind == mutate::Kind::DropInvariant;
            if !is_stuck && !is_drop_inv {
                continue;
            }
            if is_stuck {
                stuck_mutants += 1;
            }
            if is_drop_inv {
                dropped_invariants += 1;
            }
            let rejected = match resolve::resolve(&mutant.program) {
                Err(_) => true,
                Ok(resolved) => check::check(&resolved).is_err(),
            };
            assert!(
                rejected,
                "seed {seed} ({:?}, {}, class {:?}) was NOT rejected by resolve or check:\n{}",
                mutant.kind,
                mutant.detail,
                class,
                mutant.program.print()
            );
        }
    }
    assert!(
        stuck_mutants >= 180,
        "expected >= 180 stuck mutants, got {stuck_mutants}"
    );
    assert_eq!(dropped_invariants, 8, "expected 8 DropInvariant mutants");
}

#[test]
fn u16_warns_when_alternative_is_proved_impossible_without_bottom() {
    // [U16]: When the fact logic proves that an alternative of a decision
    // cannot happen and the arm is not `⊥`, the compiler warns and suggests `⊥`.
    let with_exit_instead_of_bottom = "\
extern control checked_sub(a: u32, b: u32)
    ■ difference {value: u32} ⇐ value = a - b
    ■ underflow ⇐ a < b

pub control spend(total: u32, used: u32) ■ left {value: u32} │ over
│ ? used > total → ■ over
│ Δ checked_sub(total, used): difference {value} │ underflow → ■ over
│ ■ left {value}
╵
//! warn U16
";
    let report = villanelle_v2::script::check_surface(with_exit_instead_of_bottom);
    assert!(
        report.failures.is_empty(),
        "expected U16 warning, got failures: {:?}",
        report.failures
    );

    // When the arm IS marked `→ ⊥`, no [U16] warning is emitted.
    let with_bottom = "\
extern control checked_sub(a: u32, b: u32)
    ■ difference {value: u32} ⇐ value = a - b
    ■ underflow ⇐ a < b

pub control spend(total: u32, used: u32) ■ left {value: u32} │ over
│ ? used > total → ■ over
│ Δ checked_sub(total, used): difference {value} │ underflow → ⊥
│ ■ left {value}
╵
";
    let prog = villanelle_v2::load_surface(with_bottom).unwrap();
    let checked = check::check(&prog).unwrap();
    assert!(
        checked.warnings.is_empty(),
        "expected no U16 warning when `→ ⊥` is used, got {:?}",
        checked.warnings
    );

    // Pure operation Determinism ([I10]) also triggers [U16] when a second call
    // with the same arguments leaves a contradicting arm without `→ ⊥`.
    let pure_second_call = "\
extern control classify(x: u32) ■ low │ high

pub control twice(x: u32) ■ same │ diff
│ Δ classify(x)
│ ├ low →
│ │ ┆ Δ classify(x): low → ■ same │ high → ■ diff
│ └ high → ■ same
╵
//! warn U16
";
    let report2 = villanelle_v2::script::check_surface(pure_second_call);
    assert!(
        report2.failures.is_empty(),
        "expected U16 warning on second pure call, got failures: {:?}",
        report2.failures
    );
}

/// The certificate text of a check, and the work of the search as counts.
fn text_and_counts(program: &typed::Program) -> (String, Counts) {
    let before = counts::now();
    let report = check::check(program).expect("the program is accepted");
    let done = counts::now().since(&before);
    (report.certificate_text().expect("a text"), done)
}

/// The surface programs of the three slices and the kernel program, and
/// generated programs, each with its expansion.
fn trees_for_repetition() -> Vec<(String, syntax::Program)> {
    let mut trees = Vec::new();
    for directory in [
        "slice1_surface",
        "slice2_surface",
        "slice3_surface",
        "kernels",
    ] {
        let root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("tests")
            .join(directory);
        let mut paths: Vec<_> = std::fs::read_dir(&root)
            .expect("a directory of programs")
            .map(|entry| entry.expect("an entry").path())
            .filter(|path| {
                path.extension()
                    .is_some_and(|extension| extension == "rails")
            })
            .collect();
        paths.sort();
        for path in paths {
            let source = std::fs::read_to_string(&path).expect("a readable program");
            let tree = surface::elaborate(&source)
                .unwrap_or_else(|error| panic!("{}: {error}", path.display()));
            trees.push((path.display().to_string(), tree));
        }
    }
    for seed in 1..=4 {
        trees.push((format!("seed {seed}"), fuzz::program_of(seed)));
    }
    let expanded: Vec<_> = trees
        .iter()
        .map(|(name, tree)| {
            let expansion = expand::expand(tree).unwrap_or_else(|error| panic!("{name}: {error}"));
            (format!("the expansion of {name}"), expansion)
        })
        .collect();
    trees.extend(expanded);
    trees
}

/// [J6] makes the limit a count so that an answer does not depend on the
/// machine. It must not depend on the run either: a program that is checked
/// again, on another thread, gives the same certificate text and the same
/// counts. The checker once numbered the terms of a loop in the
/// order of a hash table, which differs from table to table.
#[test]
fn a_check_is_the_same_every_time() {
    let trees = trees_for_repetition();
    assert!(trees.len() >= 30, "{} programs", trees.len());
    let mut certificates = 0;
    for (name, tree) in &trees {
        let first = {
            let program = resolve::resolve(tree).unwrap_or_else(|error| panic!("{name}: {error}"));
            text_and_counts(&program)
        };
        let elsewhere = std::thread::scope(|scope| {
            scope
                .spawn(|| {
                    let program = resolve::resolve(tree).expect("resolved before");
                    text_and_counts(&program)
                })
                .join()
                .expect("the thread ends")
        });
        assert!(
            first.0 == elsewhere.0,
            "{name}: the text differs on the second check"
        );
        assert_eq!(first.1, elsewhere.1, "{name}");
        certificates += first
            .0
            .lines()
            .filter(|line| line.starts_with("goal "))
            .count();
    }
    assert!(certificates >= 2_000, "{certificates} certificates");
}

/// Review finding RC16, held by counts: the data kernel of slice 2 and its
/// expansion are checked with a search that stays small. Before the search
/// looked for a model ahead of the rounded sums, the expansion took 2,538
/// theory checks and its exchanges wrote 29.7 million entries of tableaus.
#[test]
fn the_search_stays_small_on_the_kernel_program_of_slice_two() {
    let tree = surface::elaborate(include_str!("kernels/slice2_data.rails")).expect("elaborated");
    let expansion = expand::expand(&tree).expect("expanded");
    for (name, tree) in [("the program", &tree), ("its expansion", &expansion)] {
        let program = resolve::resolve(tree).expect("resolved");
        let before = counts::now();
        let report = check::check(&program).unwrap_or_else(|error| panic!("{name}: {error}"));
        let done = counts::now().since(&before);
        report.revalidate().expect("the kernel validates again");
        assert!(report.certificates.len() >= 170, "{name}");
        assert!(done.theory_checks <= 1_200, "{name}: {done}");
        assert!(done.entries <= 600_000, "{name}: {done}");
        assert!(done.tableaus <= done.theory_checks, "{name}: {done}");
    }
}

/// The exit condition `7 ≥ r0` holds of
/// `v17 * 5 mod 4 + v17 mod 4 * (v17 mod 8) mod 6` for `-18 ≤ v17 ≤ 18`,
/// and it takes the remainders case by case to see it. The program is a
/// mutant of a generated one (seed 18, a literal 3 shifted to 4). When the
/// search added every instance that a model failed, whether or not the
/// model failed a premise too, the candidates of this question had rows that
/// the splits did not decide, and the question reached the limit of [J6].
#[test]
fn a_condition_on_remainders_and_products_is_decided() {
    let program = load(include_str!("kernels/remainders_and_products.core")).expect("resolved");
    let before = counts::now();
    let report = check::check(&program).unwrap_or_else(|error| panic!("{error}"));
    let done = counts::now().since(&before);
    report.revalidate().expect("the kernel validates again");
    assert!(
        report.certificates.len() >= 300,
        "{}",
        report.certificates.len()
    );
    assert!(done.theory_checks <= 1_400, "{done}");
    assert!(done.entries <= 300_000, "{done}");
}
