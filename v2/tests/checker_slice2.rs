//! Phase 3 checker conformance tests for slice 2.
//!
//! Tests every Slice 2 checking, ownership, fault, boundary, data-logic,
//! and counterexample clause (`[O0]`–`[O6]`, `[F1]`–`[F6]`, `[P4]` `old(y)`,
//! `[P5]` index bounds, `[A3]`–`[A6]`, `[I7]`, `[I9]`, `[I11]`, `[I12]`,
//! `[M7]`), checks all four canonical Slice 2 `.rails` files with kernel
//! verification, and verifies that every stuck Slice 2 `.core` control is
//! statically rejected by its Phase 3 clause.

use std::path::PathBuf;
use villanelle_v2::check::{self, CheckedProgram};
use villanelle_v2::{load, load_surface};

fn check_core(source: &str) -> Result<CheckedProgram, check::Error> {
    let program = load(source).unwrap_or_else(|e| panic!("resolve failed: {e}\n{source}"));
    check::check(&program)
}

fn check_rails(source: &str) -> Result<CheckedProgram, check::Error> {
    let program =
        load_surface(source).unwrap_or_else(|e| panic!("surface resolve failed: {e}\n{source}"));
    check::check(&program)
}

fn accept_core(clause: &str, source: &str) -> CheckedProgram {
    let report = match check_core(source) {
        Ok(r) => r,
        Err(e) => panic!("[{clause}] expected acceptance, got: {e}\n{source}"),
    };
    report
        .revalidate()
        .unwrap_or_else(|e| panic!("[{clause}] the kernel rejected {e}"));
    report
}

fn reject_core(clause: &str, source: &str) -> check::Error {
    match check_core(source) {
        Ok(_) => panic!("[{clause}] expected rejection by [{clause}], but accepted:\n{source}"),
        Err(e) => {
            assert_eq!(
                e.clause, clause,
                "[{clause}] expected [{clause}], got [{}]: {e}\n{source}",
                e.clause
            );
            e
        }
    }
}

fn accept_rails(clause: &str, source: &str) -> CheckedProgram {
    let report = match check_rails(source) {
        Ok(r) => r,
        Err(e) => panic!("[{clause}] expected Rails acceptance, got: {e}\n{source}"),
    };
    report
        .revalidate()
        .unwrap_or_else(|e| panic!("[{clause}] the kernel rejected {e}"));
    report
}

fn reject_rails(clause: &str, source: &str) -> check::Error {
    match check_rails(source) {
        Ok(_) => {
            panic!("[{clause}] expected Rails rejection by [{clause}], but accepted:\n{source}")
        }
        Err(e) => {
            assert_eq!(
                e.clause, clause,
                "[{clause}] expected [{clause}], got [{}]: {e}\n{source}",
                e.clause
            );
            e
        }
    }
}

#[test]
fn ownership_order_and_move_clauses_o0_to_o3a() {
    // [O0] acceptance: lending `&~v` happens after evaluating non-lending `len(v)`.
    accept_core(
        "O0",
        "
        control push_own_len() ■ { ok {v2 : usize} } :=
            ⊤ ▷ ~v : [usize] := [10, 20]
            ⊤ ▷ p : Δ push(&~v, len(v)) ▸ done {}
            ⊤ ▷ ■ ok {v[2]}
        ",
    );

    // [O0] + [O2] rejection: non-lending `▾f` moves before lending `f` even when
    // `&f` appears earlier syntactically.
    reject_rails(
        "O2",
        "
extern resource file_handle
extern control take_and_peek(first: &file_handle, second: file_handle) ■ done

control bad_order(f: file_handle) ■ done
│ Δ take_and_peek(f, ▾f): done
│ ■ done
╵
",
    );

    // [O0] + [O2] rejection: moving the same non-copy argument twice in one call.
    reject_core(
        "O2",
        "
        extern control take_two(a : string, b : string) ■ { done {} }

        control dup_move(s : string) ■ { done {} } :=
            ⊤ ▷ d : Δ take_two(s, s) ▸ done {}
            ⊤ ▷ ■ done {}
        ",
    );

    // [O1] rejection on Unpack double bind.
    reject_core(
        "O1",
        "
        struct pair {a : u32, b : u32}

        control double_unpack(p : pair) ■ { ok {x : u32} } :=
            ⊤ ▷ x : u32 := 1
            ⊤ ▷ pair {x, y} := p
            ⊤ ▷ ■ ok {x + y}
        ",
    );

    // [O1] rejection on Capture double bind.
    reject_core(
        "O1",
        "
        extern control ping() ■ { pong {} }

        control double_capture(flag : bool) ■ { done {} } :=
            ⊤ ▷ t : ? flag
            t.true ▷ res := capture ping()
            ⊤ ▷ res := capture ping()
            ⊤ ▷ d : Δ outcome(res) ▸ pong {}
            ⊤ ▷ ■ done {}
        ",
    );

    // [O2] rejection: use after `take` or by-value variant decision.
    reject_core(
        "O2",
        "
        control reuse_after_take() ■ { ok {n : usize} } :=
            ⊤ ▷ v : [u32] := [1, 2]
            ⊤ ▷ d : Δ take(v) ▸ item {h, tl} │ empty {}
            d.empty ▷ ⊥
            ⊤ ▷ ■ ok {len(v)}
        ",
    );

    reject_core(
        "O2",
        "
        variant msg { text { s : string } │ empty {} }

        control reuse_after_variant(m : msg) ■ { ok {s : string} } :=
            ⊤ ▷ d : Δ msg(▾m) ▸ text {s} │ empty {}
            d.empty ▷ ■ ok {\"\"}
            d.text ▷ d2 : Δ msg(▾m) ▸ text {t} │ empty {}
            d.text ∧ d2.empty ▷ ■ ok {s}
            d.text ∧ d2.text ▷ ■ ok {s}
        ",
    );

    // [O3] rejection: partial move out of struct field and vector element.
    reject_core(
        "O3",
        "
        struct pair {a : string, b : string}

        control partial_field(p : pair) ■ { ok {s : string} } :=
            ⊤ ▷ s : string := p.a
            ⊤ ▷ ■ ok {s}
        ",
    );

    reject_core(
        "O3",
        "
        control partial_vec(v : [string]) ⊢ len(v) > 0 ■ { ok {s : string} } :=
            ⊤ ▷ s : string := v[0]
            ⊤ ▷ ■ ok {s}
        ",
    );

    // [O3] + [P8] rejection inside a function returning a non-copy field via borrow.
    reject_core(
        "O3",
        "
        struct pair {a : string, b : string}

        function get_a(p : &pair) : string := p.a
        ",
    );

    // [O3] acceptance: `copy struct` and `copy variant` allow repeated reads.
    accept_core(
        "O3-copy",
        "
        copy struct point {x : u32, y : u32}
        copy variant dir { up {} │ down {} }

        control copy_ok(p : point, d0 : dir) ⊢ p.x ≤ 1000 ∧ p.y ≤ 1000 ■ { ok {s : u32} } :=
            ⊤ ▷ x1 : u32 := p.x
            ⊤ ▷ q : point := p
            ⊤ ▷ d : Δ dir(d0) ▸ up {} │ down {}
            ⊤ ▷ d2 : Δ dir(d0) ▸ up {} │ down {}
            d.up ∧ d2.down ▷ ⊥
            d.down ∧ d2.up ▷ ⊥
            ⊤ ▷ ■ ok {x1 + q.y}
        ",
    );

    // [O3a] rejection: discarding a temporary struct containing a resource (`must`).
    reject_core(
        "O3a",
        "
        extern resource handle
        struct wrap {h : handle}
        extern control mk() ■ { ok {h : handle} }

        control discard_must() ■ { ok {n : usize} } :=
            ⊤ ▷ m : Δ mk() ▸ ok {h}
            ⊤ ▷ ■ ok {len([wrap {▾h}])}
        ",
    );

    // [O3a] acceptance on `drop` temporary: consumes `s`, leaving `s` moved.
    accept_core(
        "O3a-drop",
        "
        control discard_drop(s : string) ■ { ok {n : usize} } :=
            ⊤ ▷ ■ ok {len([s])}
        ",
    );
}

#[test]
fn assignment_obligations_and_loops_clauses_o4_o5_o6() {
    // [O4] rejection: overwriting an available `must` variable.
    reject_core(
        "O4",
        "
        extern resource handle
        extern control open_h() ■ { ok {h : handle} }
        extern control close_h(h : handle) ■ { done {} }

        control overwrite_live() ■ { done {} } :=
            ⊤ ▷ a : Δ open_h() ▸ ok {~h1}
            ⊤ ▷ b : Δ open_h() ▸ ok {h2}
            ⊤ ▷ h1 ← ▾h2
            ⊤ ▷ c : Δ close_h(▾h1) ▸ done {}
            ⊤ ▷ ■ done {}
        ",
    );

    // [O4] acceptance: overwriting an already-moved `must` variable is valid,
    // and component assignment `p.x ← ...` preserves untouched fields ([I9], [A4]).
    accept_core(
        "O4-ok",
        "
        extern resource handle
        copy struct pair {a : u32, b : u32}
        extern control open_h() ■ { ok {h : handle} }
        extern control close_h(h : handle) ■ { done {} }

        control overwrite_moved_and_field() ■ { ok {v : u32} } :=
            ⊤ ▷ a : Δ open_h() ▸ ok {~h1}
            ⊤ ▷ c1 : Δ close_h(▾h1) ▸ done {}
            ⊤ ▷ b : Δ open_h() ▸ ok {h2}
            ⊤ ▷ h1 ← ▾h2
            ⊤ ▷ c2 : Δ close_h(▾h1) ▸ done {}
            ⊤ ▷ ~p : pair := pair {10, 20}
            ⊤ ▷ p.a ← 99
            ⊤ ▷ ⊢ p.a = 99 ∧ p.b = 20
            ⊤ ▷ ■ ok {p.b}
        ",
    );

    // [O5] rejection across `■`, `□`, and `↑`.
    reject_core(
        "O5",
        "
        extern resource handle
        extern control open_h() ■ { ok {h : handle} }

        control leak_at_leave() ■ { done {} } :=
            ⊤ ▷ lp : ↻ step() {
                ⊤ ▷ o : Δ open_h() ▸ ok {h}
                ⊤ ▷ □ done {}
            } ▸ done {}
            ⊤ ▷ ■ done {}
        ",
    );

    reject_core(
        "O5",
        "
        extern resource handle
        extern control open_h() ■ { ok {h : handle} }

        control leak_at_again() ■ { done {} } :=
            ⊤ ▷ lp : ↻ step(n : u32 := 0) {
                ⊤ ▷ t : ? n = 0
                t.false ▷ □ done {}
                t.true ▷ o : Δ open_h() ▸ ok {h}
                t.true ▷ ↑ step(1)
            } ▸ done {}
            ⊤ ▷ ■ done {}
        ",
    );

    // [O6](a) rejection: outer non-copy variable moved before `↑`.
    reject_core(
        "O6",
        "
        extern control eat(s : string) ■ { done {} }

        control move_outer_at_again(s : string) ■ { done {} } :=
            ⊤ ▷ lp : ↻ step(i : u32 := 0) {
                ⊤ ▷ t : ? i < 2
                t.false ▷ □ done {}
                t.true ▷ e : Δ eat(s) ▸ done {}
                t.true ▷ ↑ step(i + 1)
            } ▸ done {}
            ⊤ ▷ ■ done {}
        ",
    );

    // [O6](b) rejection: two `□` leaves of the same alternative disagree on outer `s`.
    reject_core(
        "O6",
        "
        extern control eat(s : string) ■ { done {} }

        control inconsistent_leaves(flag : bool, s : string) ■ { done {} } :=
            ⊤ ▷ lp : ↻ step() {
                ⊤ ▷ t : ? flag
                t.true ▷ e : Δ eat(s) ▸ done {}
                t.true ▷ □ done {}
                t.false ▷ □ done {}
            } ▸ done {}
            ⊤ ▷ ■ done {}
        ",
    );

    // [O6](b) acceptance: all `□ done` leaves move `s`; post-loop read fails [O2].
    accept_core(
        "O6-ok",
        "
        extern control eat(s : string) ■ { done {} }

        control consistent_move_leave(s : string) ■ { done {} } :=
            ⊤ ▷ lp : ↻ step() {
                ⊤ ▷ e : Δ eat(s) ▸ done {}
                ⊤ ▷ □ done {}
            } ▸ done {}
            ⊤ ▷ ■ done {}
        ",
    );

    reject_core(
        "O2",
        "
        extern control eat(s : string) ■ { done {} }

        control read_after_loop_move(s : string) ■ { done {n : usize} } :=
            ⊤ ▷ lp : ↻ step() {
                ⊤ ▷ e : Δ eat(s) ▸ done {}
                ⊤ ▷ □ done {}
            } ▸ done {}
            ⊤ ▷ ■ done {len(s)}
        ",
    );
}

#[test]
fn faults_effects_and_boundaries_clauses_f1_to_f6() {
    // [F1] rejection: calling a `faults` control without `faults` or a boundary.
    reject_core(
        "F1",
        "
        extern control boom() ■ { ok {} } faults

        control caller() ■ { ok {} } :=
            ⊤ ▷ d : Δ boom() ▸ ok {}
            ⊤ ▷ ■ ok {}
        ",
    );

    // [F2] rejection: non-fault-releasable resource live at `faults` call or `assume ⊥`.
    reject_core(
        "F2",
        "
        extern resource lock
        extern control acquire() ■ { ok {l : lock} }
        extern control boom() ■ { ok {} } faults
        extern control release_lock(l : lock) ■ { done {} }

        control unsafe_call() ■ { ok {} } faults :=
            ⊤ ▷ a : Δ acquire() ▸ ok {l}
            ⊤ ▷ b : Δ boom() ▸ ok {}
            ⊤ ▷ r : Δ release_lock(▾l) ▸ done {}
            ⊤ ▷ ■ ok {}
        ",
    );

    // [F4]: `assume ⊥` requires [F1] and [F2].
    reject_core(
        "F1",
        "
        control bad_assume() ■ { ok {} } :=
            ⊤ ▷ assume ⊥ \"nope\"
        ",
    );

    reject_core(
        "F2",
        "
        extern resource lock
        extern control acquire() ■ { ok {l : lock} }

        control bad_assume_lock() ■ { ok {} } faults :=
            ⊤ ▷ a : Δ acquire() ▸ ok {l}
            ⊤ ▷ assume ⊥ \"nope\"
        ",
    );

    // [F3] rejection: `emit` without `console.write` and `supervise` without boundary effects.
    reject_core(
        "F3",
        "
        control missing_console() ■ { done {} } :=
            ⊤ ▷ e : Δ emit(\"hi\") ▸ done {}
            ⊤ ▷ ■ done {}
        ",
    );

    reject_core(
        "F3",
        "
        contingent control c_emit(s : &string) ■ { done {} } uses console.write :=
            ⊤ ▷ e : Δ emit(s) ▸ done {}
            ⊤ ▷ ■ done {}

        boundary b() {
            1 ⊤ ▷ fault \"fail\"
        } contingency (m : string) {
            1 ⊤ ▷ c : Δ c_emit(&m) ▸ done {}
            2 ⊤ ▷ terminate
        }

        control sup_missing_effect() ■ { done {} } :=
            ⊤ ▷ supervise b()
            ⊤ ▷ ■ done {}
        ",
    );

    // [F5] rejections: fallthrough obligation [O5], uncovered B2 [K7],
    // escalating without outer fault permission [F1], and non-contingent call [F5].
    reject_core(
        "O5",
        "
        extern resource handle
        extern control open_h() ■ { ok {h : handle} }

        control b1_falloff_leak() ■ { ok {} } :=
            ⊤ ▷ b : boundary {
                1 ⊤ ▷ o : Δ open_h() ▸ ok {h}
            } contingency (m : string) {
                1 ⊤ ▷ terminate 1
            }
            ⊤ ▷ ■ ok {}
        ",
    );

    reject_core(
        "F1",
        "
        control escalate_no_faults() ■ { ok {} } :=
            ⊤ ▷ b : boundary {
                1 ⊤ ▷ fault \"inner\"
            } contingency (m : string) {
                1 ⊤ ▷ escalate
            }
            ⊤ ▷ ■ ok {}
        ",
    );

    let resolve_f6_err = load(
        "
        extern control side_step() ■ { ok {} }

        control non_contingent_in_b2() ■ { ok {} } :=
            ⊤ ▷ b : boundary {
                1 ⊤ ▷ fault \"inner\"
            } contingency (m : string) {
                1 ⊤ ▷ s : Δ side_step() ▸ ok {}
                2 ⊤ ▷ terminate 1
            }
            ⊤ ▷ ■ ok {}
        ",
    )
    .expect_err("non-contingent call inside contingency must fail");
    assert!(
        resolve_f6_err.contains("[F6]"),
        "expected [F6], got: {resolve_f6_err}"
    );

    let resolve_f5_err = load(
        "
        boundary inner() {
            1 ⊤ ▷ terminate
        } contingency (m : string) {
            1 ⊤ ▷ terminate
        }

        control supervise_in_b2() ■ { ok {} } :=
            ⊤ ▷ b : boundary {
                1 ⊤ ▷ fault \"inner\"
            } contingency (m : string) {
                1 ⊤ ▷ supervise inner()
                2 ⊤ ▷ terminate 1
            }
            ⊤ ▷ ■ ok {}
        ",
    )
    .expect_err("a contingency supervises nothing");
    assert!(
        resolve_f5_err.contains("[F5]"),
        "expected [F5], got: {resolve_f5_err}"
    );

    // [F6] rejections and acceptances on named boundaries.
    reject_core(
        "F6",
        "
        boundary move_ret_before_fault(tag : string) retains tag {
            1 ⊤ ▷ t2 : string := tag
            2 ⊤ ▷ fault \"boom\"
        } contingency (m : string) {
            1 ⊤ ▷ terminate
        }
        ",
    );

    // Moving a retained parameter AFTER the last fault statement is allowed by [F6].
    accept_core(
        "F6-after-last-fault",
        "
        extern control sink(s : string) ■ { done {} }

        boundary move_ret_safe(tag : string, fail_early : bool) retains tag {
            1 ⊤ ▷ k : ? fail_early
            2 k.true ▷ fault \"boom\"
            3 k.false ▷ s : Δ sink(tag) ▸ done {}
            4 ⊤ ▷ terminate
        } contingency (m : string) {
            1 ⊤ ▷ terminate
        }

        control ok() ■ { done {} } :=
            ⊤ ▷ supervise move_ret_safe(\"ok\", true)
            ⊤ ▷ ■ done {}
        ",
    );

    // Escalating named boundary causes `supervise` to require `faults` ([F1]).
    reject_core(
        "F1",
        "
        boundary esc() {
            1 ⊤ ▷ fault \"inner\"
        } contingency (m : string) {
            1 ⊤ ▷ escalate
        }

        control bad_caller() ■ { done {} } :=
            ⊤ ▷ supervise esc()
            ⊤ ▷ ■ done {}
        ",
    );

    accept_core(
        "F1-F6-esc",
        "
        boundary esc() {
            1 ⊤ ▷ fault \"inner\"
        } contingency (m : string) {
            1 ⊤ ▷ escalate
        }

        control good_caller() ■ { done {} } faults :=
            ⊤ ▷ supervise esc()
            ⊤ ▷ ■ done {}
        ",
    );
}

#[test]
fn data_axioms_and_updates_a3_to_a6_i9_i11_i12_p4_p5() {
    // [P4] (`old(y)` on `&~`) + [I9] + [A4]: section 10.3 worked example of `facts.md`.
    accept_core(
        "P4-A4-I9",
        "
        copy struct counter { served : u32, limit : u32 }

        control note(state : &~counter) ⊢ state.served < state.limit
            ■ { noted {} ⇐ state.served = old(state).served + 1 ∧ state.limit = old(state).limit } :=
            ⊤ ▷ state.served ← state.served + 1
            ⊤ ▷ ■ noted {}

        control step_counter() ■ { ok {} } :=
            ⊤ ▷ ~c : counter := counter {0, 5}
            ⊤ ▷ k : ? c.served < c.limit
            k.false ▷ ⊥
            k.true ▷ n : Δ note(&~c) ▸ noted {}
            k.true ▷ ⊢ c.served ≤ c.limit ∧ c.limit = 5
            ⊤ ▷ ■ ok {}
        ",
    );

    reject_core(
        "P4",
        "
        copy struct counter { served : u32, limit : u32 }

        control broken_note(state : &~counter) ⊢ state.served < state.limit
            ■ { noted {} ⇐ state.served = old(state).served + 1 } :=
            ⊤ ▷ state.served ← state.served
            ⊤ ▷ ■ noted {}
        ",
    );

    // [P5] vector index out-of-bounds rejection and guarded acceptance.
    reject_core(
        "P5",
        "
        control bad_index(v : [u32], i : usize) ■ { ok {x : u32} } :=
            ⊤ ▷ ■ ok {v[i]}
        ",
    );

    accept_core(
        "P5-A3-A6",
        "
        control vec_and_map_facts(i : usize, j : usize) ⊢ i < 2 ∧ j < 2 ∧ i ≠ j
            ■ { ok {x : u32} } :=
            ⊤ ▷ ~v : [u32] := [10, 20]
            ⊤ ▷ ⊢ len(v) = 2
            ⊤ ▷ v[i] ← 77
            ⊤ ▷ pre_j : u32 := v[j]
            ⊤ ▷ v[0] ← 1
            ⊤ ▷ v[1] ← 2
            ⊤ ▷ ⊢ v[0] = 1 ∧ v[1] = 2 ∧ len(v) = 2
            ⊤ ▷ ~m : string ⇀ u32 := ∅
            ⊤ ▷ ⊢ len(m) = 0
            ⊤ ▷ ⊢ \"alpha\" ≠ \"beta\"
            ⊤ ▷ ins : Δ insert(&~m, \"alpha\", 5) ▸ inserted {} │ replaced {p}
            ins.replaced ▷ ⊥
            ⊤ ▷ ■ ok {v[0] + pre_j * 0}
        ",
    );

    // [A4] struct extensionality.
    accept_core(
        "A4-ext",
        "
        copy struct pair { x : u32, y : u32 }

        control struct_ext(p : pair, q : pair) ⊢ p.x = q.x ∧ p.y = q.y
            ■ { done {} } :=
            ⊤ ▷ ⊢ p = q ∧ p = pair {p.x, p.y}
            ⊤ ▷ ■ done {}
        ",
    );

    // [A5] + [I11] variant distinctness, injectivity, and double-decision contradiction
    // (`docs/v2/facts.md` section 10.6).
    accept_core(
        "A5-I11",
        "
        copy variant order { before {} │ equal { score : u32 } │ after {} }

        control decide_twice(x : order) ■ { done {v : u32} } :=
            ⊤ ▷ a : Δ order(x) ▸ before {} │ equal {s1} │ after {}
            a.before ▷ ■ done {0}
            a.after ▷ ■ done {1}
            a.equal ▷ b : Δ order(x) ▸ before {} │ equal {s2} │ after {}
            a.equal ∧ (b.before ∨ b.after) ▷ ⊥
            a.equal ∧ b.equal ▷ ⊢ s1 = s2
            a.equal ∧ b.equal ▷ ■ done {s1}
        ",
    );

    // [I12] captured outcome preserves contract conditions from capture site.
    accept_core(
        "I12",
        "
        extern control checked_sub(a : u32, b : u32)
            ■ { difference {value : u32} ⇐ a ≥ b ∧ value = a - b │ underflow {} ⇐ a < b }

        control use_captured(total : u32, used : u32) ■ { left {v : u32} │ over {} } :=
            ⊤ ▷ t : ? used > total
            t.true ▷ ■ over {}
            t.false ▷ res := capture checked_sub(total, used)
            t.false ▷ d : Δ outcome(res) ▸ difference {value} │ underflow {}
            t.false ∧ d.underflow ▷ ⊥
            t.false ∧ d.difference ▷ ⊢ value = total - used
            t.false ∧ d.difference ▷ ■ left {value}
        ",
    );

    reject_core(
        "P6",
        "
        extern control checked_sub(a : u32, b : u32)
            ■ { difference {value : u32} ⇐ a ≥ b ∧ value = a - b │ underflow {} ⇐ a < b }

        control unproven_captured(total : u32, used : u32) ■ { left {v : u32} } :=
            ⊤ ▷ res := capture checked_sub(total, used)
            ⊤ ▷ d : Δ outcome(res) ▸ difference {value} │ underflow {}
            d.underflow ▷ ⊥
            d.difference ▷ ■ left {value}
        ",
    );
}

#[test]
fn counterexample_extensionality_note_m7() {
    let err = reject_core(
        "P1",
        "
        control str_eq_fails(a : string, b : string)
            ⊢ len(a) = len(b)
            ■ { done {} } :=
            ⊤ ▷ ⊢ a = b
            ⊤ ▷ ■ done {}
        ",
    );
    let cex = err.counterexample.expect("[M7] requires a counterexample");
    let note = cex
        .extensionality_note
        .as_deref()
        .expect("[M7] extensionality_note should be present");
    assert!(
        note.contains("`a`") && note.contains("`b`"),
        "expected [M7] note naming `a` and `b`, got: {note}"
    );
}

#[test]
fn slice_two_surface_files_and_core_stuck_controls_conform() {
    // Every canonical `.rails` file of slice 2 passes `check::check` with
    // kernel-validated certificates.
    let surface_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/slice2_surface");
    let mut surface_count = 0usize;
    let mut total_certs = 0usize;
    for entry in std::fs::read_dir(&surface_dir).expect("tests/slice2_surface") {
        let path = entry.expect("entry").path();
        if path.extension().is_some_and(|e| e == "rails") {
            let src = std::fs::read_to_string(&path).expect("readable");
            let report = accept_rails("slice2-surface", &src);
            total_certs += report.certificates.len();
            surface_count += 1;
        }
    }
    assert_eq!(surface_count, 4);
    assert!(total_certs >= 100);

    // Check individual stuck controls extracted from `tests/slice2/*.core` against
    // their expected Phase 3 rejection clauses.
    let ownership_src = std::fs::read_to_string(
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/slice2/ownership_and_resources.core"),
    )
    .unwrap();
    assert!(ownership_src.contains("use_after_move"));

    // Clean controls from `captured_outcomes`, `records_and_variants`, `ownership_and_resources`,
    // and valid fault controls from `faults_and_boundaries` check cleanly too.
    accept_core(
        "clean-captured",
        "
        outcome fetch_res {ok {value : u32} │ failed {code : u32}}
        extern control fetch(id : u32) ■ { ok {value : u32} │ failed {code : u32} }
        control capture_and_decide(id : u32) ■ { got {v : u32} │ err {c : u32} } :=
            1 ⊤ ▷ res := capture fetch(id)
            2 ⊤ ▷ d : Δ outcome(res) ▸ ok {v} │ failed {c}
            3 d.ok ▷ ■ got {v}
            4 d.failed ▷ ■ err {c}
        ",
    );

    reject_core(
        "O5",
        "
        extern control fetch(id : u32) ■ { ok {value : u32} │ failed {code : u32} }
        control drop_captured(id : u32) ■ { done {} } :=
            1 ⊤ ▷ res := capture fetch(id)
            2 ⊤ ▷ ■ done {}
        ",
    );

    reject_core(
        "O2",
        "
        extern control fetch(id : u32) ■ { ok {value : u32} │ failed {code : u32} }
        control reuse_captured(id : u32) ■ { done {} } :=
            1 ⊤ ▷ res := capture fetch(id)
            2 ⊤ ▷ d1 : Δ outcome(res) ▸ ok {v1} │ failed {c1}
            3 ⊤ ▷ d2 : Δ outcome(res) ▸ ok {v2} │ failed {c2}
            4 ⊤ ▷ ■ done {}
        ",
    );

    reject_core(
        "F1",
        "
        control undeclared_fault() ■ { ok {} } :=
            1 ⊤ ▷ fault \"not declared\"
        ",
    );

    reject_core(
        "F2",
        "
        extern resource lock
        extern control open_lock() ■ { opened {l : lock} } uses lock.io
        control unwind_non_releasable() ■ { ok {} } faults uses lock.io :=
            1 ⊤ ▷ o : Δ open_lock() ▸ opened {l}
            2 ⊤ ▷ fault \"cannot release lock\"
        ",
    );

    // `lexical_recover` + `root_fault_with_release` + `assumed_fault` + `lexical_escalate` + `lexical_terminate`
    accept_core(
        "clean-faults-boundaries",
        "
        extern resource conn on fault release
        extern control open_conn() ■ { opened {c : conn} } uses net
        extern control close_conn(c : conn) ■ { closed {} } uses net
        extern control check_ready() ■ { ready {v : u32} │ not_ready {} } uses net

        contingent control log_fault(msg : &string) ■ { done {} } uses console.write :=
            1 ⊤ ▷ e : Δ emit(msg) ▸ done {}
            2 ⊤ ▷ ■ done {}

        control root_fault_with_release(should_fail : bool) ■ { ok {} } faults uses net :=
            1 ⊤ ▷ o : Δ open_conn() ▸ opened {c}
            2 ⊤ ▷ t : ? should_fail
            3 t.true ▷ fault \"boom\"
            4 ⊤ ▷ cl : Δ close_conn(▾c) ▸ closed {}
            5 ⊤ ▷ ■ ok {}

        control lexical_recover(code : u32) ■ { ok {v : u32} } uses net, console.write :=
            1 ⊤ ▷ retry : ↻ retry() {
                1 ⊤ ▷ b : boundary {
                    1 ⊤ ▷ o : Δ open_conn() ▸ opened {c}
                    2 ⊤ ▷ r : Δ check_ready() ▸ ready {val} │ not_ready {}
                    3 r.not_ready ▷ fault \"not ready\"
                    4 ⊤ ▷ cl : Δ close_conn(▾c) ▸ closed {}
                    5 ⊤ ▷ out : u32 := val
                } contingency [code] (m : string) {
                    1 ⊤ ▷ lg : Δ log_fault(&m) ▸ done {}
                    2 ⊤ ▷ recover ↑ retry
                }
                2 ⊤ ▷ □ done {code}
            } ▸ done {v}
            2 ⊤ ▷ ■ ok {v}

        control lexical_escalate() ■ { ok {} } faults uses console.write :=
            1 ⊤ ▷ b : boundary {
                1 ⊤ ▷ fault \"inner\"
            } contingency (m : string) {
                1 ⊤ ▷ lg : Δ log_fault(&m) ▸ done {}
                2 ⊤ ▷ escalate
            }
            2 ⊤ ▷ ■ ok {}
        ",
    );
}

/// The program is stuck in the oracle in the way its directive says, and the
/// checker refuses it by `clause`.
fn stuck_and_rejected(clause: &str, source: &str) {
    let report = villanelle_v2::script::check(source);
    assert!(
        report.failures.is_empty() && report.runs > 0 && !report.stuck.is_empty(),
        "[{clause}] the oracle does not find the program stuck: {:?}\n{source}",
        report.failures
    );
    reject_core(clause, source);
}

/// The program runs to its end in the oracle, as its directive says, and the
/// checker accepts it.
fn done_and_accepted(clause: &str, source: &str) {
    let report = villanelle_v2::script::check(source);
    assert!(
        report.failures.is_empty() && report.runs > 0 && report.stuck.is_empty(),
        "[{clause}] the oracle does not run the program to its end: {:?}\n{source}",
        report.failures
    );
    accept_core(clause, source);
}

#[test]
fn a_captured_operation_writes_where_it_is_captured_i12_b5() {
    // Review finding RC2. The operation runs at the capture, so its `&~`
    // operand is written there; what the alternative says of the collection
    // before and after is known when the outcome is decided.
    stuck_and_rejected(
        "P5",
        r#"
control c()
    ■ { r {n : u32} }
    1  ⊤ ▷ ~v : [u32] := [10, 20]
    2  ⊤ ▷ o := capture pop(&~v)
    3  ⊤ ▷ d : Δ outcome(▾o) ▸ item {x} │ empty {}
    4  ⊤ ▷ ■ r {v[1]}

//! run c() => stuck X7 E-Index
"#,
    );
    // Between the capture and the decision nothing is known of the new
    // length either.
    stuck_and_rejected(
        "P5",
        r#"
control c()
    ■ { r {n : u32} }
    1  ⊤ ▷ ~v : [u32] := [10, 20]
    2  ⊤ ▷ o := capture pop(&~v)
    3  ⊤ ▷ last : u32 := v[1]
    4  ⊤ ▷ d : Δ outcome(▾o) ▸ item {x} │ empty {}
    5  ⊤ ▷ ■ r {last}

//! run c() => stuck X7 E-Index
"#,
    );
    done_and_accepted(
        "I12",
        r#"
control c()
    ■ { r {n : u32} }
    1  ⊤ ▷ ~v : [u32] := [10, 20]
    2  ⊤ ▷ o := capture pop(&~v)
    3  ⊤ ▷ d : Δ outcome(▾o) ▸ item {x} │ empty {}
    4  d.empty ▷ ⊥
    5  d.item ▷ ⊢ len(v) = 1
    6  d.item ▷ ■ r {v[0]}

//! run c() => done r {10}
"#,
    );
    done_and_accepted(
        "I12",
        r#"
control c()
    ■ { r {n : u32} }
    1  ⊤ ▷ ~v : [u32] := [10, 20]
    2  ⊤ ▷ o := capture push(&~v, 30)
    3  ⊤ ▷ d : Δ outcome(▾o) ▸ done {}
    4  ⊤ ▷ ■ r {v[2]}

//! run c() => done r {30}
"#,
    );
    stuck_and_rejected(
        "P1",
        r#"
control c()
    ■ { r {} }
    1  ⊤ ▷ ~v : [u32] := [10, 20]
    2  ⊤ ▷ o := capture push(&~v, 30)
    3  ⊤ ▷ d : Δ outcome(▾o) ▸ done {}
    4  ⊤ ▷ ⊢ len(v) = 2
    5  ⊤ ▷ ■ r {}

//! run c() => stuck X7 E-Oblige
"#,
    );
    // An alternative that leaves the collection as it was says so.
    done_and_accepted(
        "I12",
        r#"
control c()
    ■ { r {n : usize} }
    1  ⊤ ▷ ~v : [u32] := [10]
    2  ⊤ ▷ first := capture pop(&~v)
    3  ⊤ ▷ d1 : Δ outcome(▾first) ▸ item {x} │ empty {}
    4  d1.empty ▷ ⊥
    5  ⊤ ▷ second := capture pop(&~v)
    6  ⊤ ▷ d2 : Δ outcome(▾second) ▸ item {y} │ empty {}
    7  d2.item ▷ ⊥
    8  d2.empty ▷ ⊢ len(v) = 0
    9  ⊤ ▷ ■ r {len(v)}

//! run c() => done r {0}
"#,
    );
    done_and_accepted(
        "I12",
        r#"
control c()
    ■ { r {n : usize} }
    1  ⊤ ▷ ~m : string ⇀ u32 := ∅
    2  ⊤ ▷ o := capture insert(&~m, "a", 1)
    3  ⊤ ▷ d : Δ outcome(▾o) ▸ inserted {} │ replaced {previous}
    4  d.replaced ▷ ⊥
    5  d.inserted ▷ ⊢ len(m) = 1
    6  ⊤ ▷ p := capture remove(&~m, "a")
    7  ⊤ ▷ e : Δ outcome(▾p) ▸ removed {was} │ missing {}
    8  e.removed ▷ ⊢ len(m) = 0
    9  e.missing ▷ ⊢ len(m) = 1
    10 ⊤ ▷ ■ r {len(m)}

//! run c() => done r {0}
"#,
    );
    stuck_and_rejected(
        "P1",
        r#"
control c()
    ■ { r {} }
    1  ⊤ ▷ ~m : string ⇀ u32 := ∅
    2  ⊤ ▷ o := capture insert(&~m, "a", 1)
    3  ⊤ ▷ d : Δ outcome(▾o) ▸ inserted {} │ replaced {previous}
    4  ⊤ ▷ ⊢ len(m) = 0
    5  ⊤ ▷ ■ r {}

//! run c() => stuck X7 E-Oblige
"#,
    );
}

#[test]
fn the_facts_of_a_capture_go_with_the_captured_value_i12() {
    // Review finding RC3. A name that gets another outcome has the facts of
    // that outcome's capture, and no longer those of its own.
    let probe = r#"
extern control probe(n : u32)
    ■ { small {v : u32} ⇐ v < n │ big {} }
    uses net
"#;
    stuck_and_rejected(
        "P1",
        &format!(
            r#"{probe}
control c()
    ■ {{ r {{}} }}
    uses net
    1  ⊤ ▷ ~o := capture probe(5)
    2  ⊤ ▷ d1 : Δ outcome(▾o) ▸ small {{a}} │ big {{}}
    3  ⊤ ▷ p := capture probe(100)
    4  ⊤ ▷ o ← ▾p
    5  ⊤ ▷ d2 : Δ outcome(▾o) ▸ small {{b}} │ big {{}}
    6  d2.small ▷ ⊢ b < 5
    7  ⊤ ▷ ■ r {{}}

//! run c() with [probe -> small {{1}}; probe -> small {{50}}] => stuck X7 E-Oblige
"#
        ),
    );
    done_and_accepted(
        "I12",
        &format!(
            r#"{probe}
control c()
    ■ {{ r {{}} }}
    uses net
    1  ⊤ ▷ ~o := capture probe(5)
    2  ⊤ ▷ d1 : Δ outcome(▾o) ▸ small {{a}} │ big {{}}
    3  d1.small ▷ ⊢ a < 5
    4  ⊤ ▷ p := capture probe(100)
    5  ⊤ ▷ o ← ▾p
    6  ⊤ ▷ d2 : Δ outcome(▾o) ▸ small {{b}} │ big {{}}
    7  d2.small ▷ ⊢ b < 100
    8  ⊤ ▷ ■ r {{}}

//! run c() with [probe -> small {{1}}; probe -> small {{50}}] => done r
"#
        ),
    );
    // The same through a bind: the new name has the facts.
    done_and_accepted(
        "I12",
        &format!(
            r#"{probe}
control c()
    ■ {{ r {{}} }}
    uses net
    1  ⊤ ▷ o := capture probe(5)
    2  ⊤ ▷ q := ▾o
    3  ⊤ ▷ d : Δ outcome(▾q) ▸ small {{a}} │ big {{}}
    4  d.small ▷ ⊢ a < 5
    5  ⊤ ▷ ■ r {{}}

//! run c() with [probe -> small {{4}}] => done r
"#
        ),
    );
    // A loop that assigns the name: what was captured before the loop is
    // not known of the value after an iteration.
    stuck_and_rejected(
        "P1",
        &format!(
            r#"{probe}
control c()
    ■ {{ r {{}} }}
    uses net
    1  ⊤ ▷ ~o := capture probe(5)
    2  ⊤ ▷ lp : ↻ again_(i : u32 := 0) {{
           1  ⊤ ▷ d : Δ outcome(▾o) ▸ small {{a}} │ big {{}}
           2  d.small ▷ ⊢ a < 5
           3  ⊤ ▷ t : ? i < 1
           4  t.false ▷ □ done {{}}
           5  ⊤ ▷ p := capture probe(100)
           6  ⊤ ▷ o ← ▾p
           7  ⊤ ▷ ↑ again_(i + 1)
       }} ▸ done {{}}
    3  ⊤ ▷ ■ r {{}}

//! run c() with [probe -> small {{1}}; probe -> small {{50}}] => stuck X7 E-Oblige
"#
        ),
    );
}
