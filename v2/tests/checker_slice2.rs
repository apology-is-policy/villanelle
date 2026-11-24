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

/// The declarations that the programs of the fault boundaries share.
const FAULT_PRELUDE: &str = r#"
extern resource conn on fault release
extern resource lock

extern control open_conn()
    ■ { opened {c : conn} }
    uses net

extern control close_conn(c : conn)
    ■ { closed {} }
    uses net

extern control open_lock()
    ■ { opened {l : lock} }
    uses lock.io

contingent extern control close_lock(l : lock)
    ■ { closed {} }
    uses lock.io

extern control keep(s : string)
    ■ { kept {} }
    uses net

control risky(fail_now : bool)
    ■ { fine {} }
    faults
    1  ⊤ ▷ t : ? fail_now
    2  t.true ▷ fault "risk"
    3  ⊤ ▷ ■ fine {}

contingent control helper_faults()
    ■ { done {} }
    faults
    1  ⊤ ▷ fault "helper"

contingent control helper()
    ■ { done {} }
    1  ⊤ ▷ ■ done {}
"#;

fn with_fault_prelude(program: &str) -> String {
    format!("{FAULT_PRELUDE}{program}")
}

#[test]
fn a_contingency_ends_in_the_state_of_the_fault_f5_o5() {
    // Review finding RC4. `B₂` runs after a fault at a statement of `B₁`, so
    // its terminators meet the names around the boundary as `B₁` left them
    // there, and not as they were when the boundary was entered.

    // The work consumes the connection before it faults: nothing is left
    // for `terminate` to abandon.
    done_and_accepted(
        "O5",
        &with_fault_prelude(
            r#"
control c()
    ■ { ok {} }
    uses net
    1  ⊤ ▷ o : Δ open_conn() ▸ opened {x}
    2  ⊤ ▷ b : boundary {
           1  ⊤ ▷ k : Δ close_conn(x) ▸ closed {}
           2  ⊤ ▷ fault "stop"
       } contingency (m : string) {
           1  ⊤ ▷ terminate 1
       }
    3  ⊤ ▷ ⊥

//! run c() with [open_conn -> opened {conn#1}; close_conn -> closed] => terminated 1
"#,
        ),
    );
    // The work fills an outer name again before it faults, and `terminate`
    // abandons what it holds.
    stuck_and_rejected(
        "O5",
        &with_fault_prelude(
            r#"
control c()
    ■ { ok {} }
    uses net
    1  ⊤ ▷ o : Δ open_conn() ▸ opened {x0}
    2  ⊤ ▷ ~x : conn := x0
    3  ⊤ ▷ k : Δ close_conn(x) ▸ closed {}
    4  ⊤ ▷ b : boundary {
           1  ⊤ ▷ o2 : Δ open_conn() ▸ opened {y}
           2  ⊤ ▷ x ← y
           3  ⊤ ▷ fault "stop"
       } contingency (m : string) {
           1  ⊤ ▷ terminate 1
       }
    5  ⊤ ▷ ⊥

//! run c() with [open_conn -> opened {conn#1}; close_conn -> closed; open_conn -> opened {conn#2}] => stuck X5 E-Scope
"#,
        ),
    );
    // Every statement that may fault counts: the first of two leaves the
    // connection open.
    stuck_and_rejected(
        "O5",
        &with_fault_prelude(
            r#"
control c(early : bool)
    ■ { ok {} }
    uses net
    1  ⊤ ▷ o : Δ open_conn() ▸ opened {x}
    2  ⊤ ▷ b : boundary {
           1  ⊤ ▷ r : Δ risky(early) ▸ fine {}
           2  ⊤ ▷ k : Δ close_conn(x) ▸ closed {}
           3  ⊤ ▷ fault "stop"
       } contingency (m : string) {
           1  ⊤ ▷ terminate 1
       }
    3  ⊤ ▷ ⊥

//! run c(true) with [open_conn -> opened {conn#1}] => stuck X5 E-Scope
//! run c(false) with [open_conn -> opened {conn#1}; close_conn -> closed] => terminated 1
"#,
        ),
    );
}

#[test]
fn a_fault_of_an_inner_contingency_is_a_fault_of_the_work_around_it_f5() {
    // RC4: `escalate` in the `B₂` of an inner boundary is, for the boundary
    // around it, a statement of its `B₁` that may fault, in the states in
    // which the inner `B₁` faulted.
    stuck_and_rejected(
        "O5",
        &with_fault_prelude(
            r#"
control c()
    ■ { ok {} }
    uses net
    1  ⊤ ▷ o : Δ open_conn() ▸ opened {x0}
    2  ⊤ ▷ ~x : conn := x0
    3  ⊤ ▷ k : Δ close_conn(x) ▸ closed {}
    4  ⊤ ▷ outer : boundary {
           1  ⊤ ▷ inner : boundary {
                  1  ⊤ ▷ o2 : Δ open_conn() ▸ opened {y}
                  2  ⊤ ▷ x ← y
                  3  ⊤ ▷ fault "stop"
              } contingency (m : string) {
                  1  ⊤ ▷ escalate
              }
           2  ⊤ ▷ ⊥
       } contingency (m2 : string) {
           1  ⊤ ▷ terminate 1
       }
    5  ⊤ ▷ ⊥

//! run c() with [open_conn -> opened {conn#1}; close_conn -> closed; open_conn -> opened {conn#2}] => stuck X5 E-Scope
"#,
        ),
    );
    done_and_accepted(
        "O5",
        &with_fault_prelude(
            r#"
control c()
    ■ { ok {} }
    uses net
    1  ⊤ ▷ o : Δ open_conn() ▸ opened {x}
    2  ⊤ ▷ outer : boundary {
           1  ⊤ ▷ inner : boundary {
                  1  ⊤ ▷ k : Δ close_conn(x) ▸ closed {}
                  2  ⊤ ▷ fault "stop"
              } contingency (m : string) {
                  1  ⊤ ▷ escalate
              }
           2  ⊤ ▷ ⊥
       } contingency (m2 : string) {
           1  ⊤ ▷ terminate 1
       }
    3  ⊤ ▷ ⊥

//! run c() with [open_conn -> opened {conn#1}; close_conn -> closed] => terminated 1
"#,
        ),
    );
}

#[test]
fn recover_reads_the_parameters_and_ends_the_iteration_o2_o5_o6() {
    // RC4, for `recover ↑ ℓ`: it reads the parameters of the loop as
    // operands ([O2]), ends the scopes of the iteration ([O5]) and leaves
    // the names around the loop as the loop found them ([O6]), all in the
    // state of the fault.
    stuck_and_rejected(
        "O2",
        &with_fault_prelude(
            r#"
control c(start : string)
    ■ { ok {} }
    uses net
    1  ⊤ ▷ lp : ↻ retry(s : string := start) {
           1  ⊤ ▷ k : Δ keep(s) ▸ kept {}
           2  ⊤ ▷ b : boundary {
                  1  ⊤ ▷ fault "again"
              } contingency (m : string) {
                  1  ⊤ ▷ recover ↑ retry
              }
           3  ⊤ ▷ □ done {}
       } ▸ done {}
    2  ⊤ ▷ ■ ok {}

//! run c("a") with [keep -> kept] => stuck X2 E-Var
"#,
        ),
    );
    // The work closes what the iteration opened before it may fault.
    done_and_accepted(
        "O5",
        &with_fault_prelude(
            r#"
control c(first : bool)
    ■ { ok {} }
    uses net
    1  ⊤ ▷ lp : ↻ retry(s : string := "x") {
           1  ⊤ ▷ o : Δ open_conn() ▸ opened {x}
           2  ⊤ ▷ b : boundary {
                  1  ⊤ ▷ k : Δ close_conn(x) ▸ closed {}
                  2  ⊤ ▷ r : Δ risky(first) ▸ fine {}
              } contingency (m : string) {
                  1  ⊤ ▷ recover ↑ retry
              }
           3  ⊤ ▷ □ done {}
       } ▸ done {}
    2  ⊤ ▷ ■ ok {}

//! run c(false) with [open_conn -> opened {conn#1}; close_conn -> closed] => done ok
"#,
        ),
    );
    // It may fault before it closes it.
    stuck_and_rejected(
        "O5",
        &with_fault_prelude(
            r#"
control c(first : bool)
    ■ { ok {} }
    uses net
    1  ⊤ ▷ lp : ↻ retry(s : string := "x") {
           1  ⊤ ▷ o : Δ open_conn() ▸ opened {x}
           2  ⊤ ▷ b : boundary {
                  1  ⊤ ▷ r : Δ risky(first) ▸ fine {}
                  2  ⊤ ▷ k : Δ close_conn(x) ▸ closed {}
              } contingency (m : string) {
                  1  ⊤ ▷ recover ↑ retry
              }
           3  ⊤ ▷ □ done {}
       } ▸ done {}
    2  ⊤ ▷ ■ ok {}

//! run c(true) with [open_conn -> opened {conn#1}] => stuck X5 E-Scope
"#,
        ),
    );
    // The work moves a name from around the loop before it faults, and the
    // next iteration finds it gone.
    stuck_and_rejected(
        "O6",
        &with_fault_prelude(
            r#"
control c(start : string)
    ■ { ok {} }
    uses net
    1  ⊤ ▷ lp : ↻ retry(n : u32 := 0) {
           1  ⊤ ▷ b : boundary {
                  1  ⊤ ▷ k : Δ keep(start) ▸ kept {}
                  2  ⊤ ▷ fault "again"
              } contingency (m : string) {
                  1  ⊤ ▷ recover ↑ retry
              }
           2  ⊤ ▷ □ done {}
       } ▸ done {}
    2  ⊤ ▷ ■ ok {}

//! run c("a") with [keep -> kept] => stuck X2 E-Var
"#,
        ),
    );
}

#[test]
fn a_loop_further_out_is_restarted_as_the_one_around_is_o2_o5_o6() {
    // The shapes that the generator of slice 2 writes since 24 November: a
    // boundary in the work of another, and `recover ↑ ℓ` for a loop further
    // out than the body in which the boundary stands. The restart ends
    // every body from that of `ℓ` to the contingency ([O5]), it reads the
    // parameters of `ℓ` ([O2]) and it leaves the names around `ℓ` as the
    // loop found them ([O6]), all in the state of the fault, also where the
    // fault came through a contingency that passed it on. The programs that
    // the checker accepts are in
    // `tests/slice2/checked_nested_boundaries.core`.

    // The work around holds a connection where the work inside it faults,
    // and the contingency of that one restarts the loop.
    stuck_and_rejected(
        "O5",
        &with_fault_prelude(
            r#"
control c(first : bool)
    ■ { ok {} }
    faults
    uses net
    1  ⊤ ▷ lp : ↻ retry(~i : u32 := 0) {
           ⊢ i ≤ 2
           1  ⊤ ▷ t : ? i < 2
           2  t.false ▷ □ done {}
           3  ⊤ ▷ i ← i + 1
           4  ⊤ ▷ outer : boundary {
                  1  ⊤ ▷ o : Δ open_conn() ▸ opened {x}
                  2  ⊤ ▷ inner : boundary {
                         1  ⊤ ▷ r : Δ risky(first) ▸ fine {}
                     } contingency (m : string) {
                         1  ⊤ ▷ recover ↑ retry
                     }
                  3  ⊤ ▷ k : Δ close_conn(x) ▸ closed {}
              } contingency (m2 : string) {
                  1  ⊤ ▷ escalate
              }
           5  ⊤ ▷ □ done {}
       } ▸ done {}
    2  ⊤ ▷ ■ ok {}

//! run c(true) with [open_conn -> opened {conn#1}] => stuck X5 E-Scope
//! run c(false) with [open_conn -> opened {conn#1}; close_conn -> closed] => done ok
"#,
        ),
    );
    // The body of a loop between holds it.
    stuck_and_rejected(
        "O5",
        &with_fault_prelude(
            r#"
control c(first : bool)
    ■ { ok {} }
    uses net
    1  ⊤ ▷ lp : ↻ retry(~i : u32 := 0) {
           ⊢ i ≤ 2
           1  ⊤ ▷ t : ? i < 2
           2  t.false ▷ □ done {}
           3  ⊤ ▷ i ← i + 1
           4  ⊤ ▷ l2 : ↻ within(j : u32 := 0) {
                  1  ⊤ ▷ o : Δ open_conn() ▸ opened {x}
                  2  ⊤ ▷ b : boundary {
                         1  ⊤ ▷ r : Δ risky(first) ▸ fine {}
                     } contingency (m : string) {
                         1  ⊤ ▷ recover ↑ retry
                     }
                  3  ⊤ ▷ k : Δ close_conn(x) ▸ closed {}
                  4  ⊤ ▷ □ end {}
              } ▸ end {}
           5  ⊤ ▷ □ done {}
       } ▸ done {}
    2  ⊤ ▷ ■ ok {}

//! run c(true) with [open_conn -> opened {conn#1}] => stuck X5 E-Scope
//! run c(false) with [open_conn -> opened {conn#1}; close_conn -> closed] => done ok
"#,
        ),
    );
    // The inner contingency passes the fault on and the outer one restarts
    // the loop, whose body holds the connection where the inner work
    // faults.
    stuck_and_rejected(
        "O5",
        &with_fault_prelude(
            r#"
control c(first : bool)
    ■ { ok {} }
    uses net
    1  ⊤ ▷ lp : ↻ retry(~i : u32 := 0) {
           ⊢ i ≤ 2
           1  ⊤ ▷ t : ? i < 2
           2  t.false ▷ □ done {}
           3  ⊤ ▷ i ← i + 1
           4  ⊤ ▷ o : Δ open_conn() ▸ opened {x}
           5  ⊤ ▷ outer : boundary {
                  1  ⊤ ▷ inner : boundary {
                         1  ⊤ ▷ r : Δ risky(first) ▸ fine {}
                         2  ⊤ ▷ k : Δ close_conn(x) ▸ closed {}
                     } contingency (m : string) {
                         1  ⊤ ▷ escalate
                     }
              } contingency (m2 : string) {
                  1  ⊤ ▷ recover ↑ retry
              }
           6  ⊤ ▷ □ done {}
       } ▸ done {}
    2  ⊤ ▷ ■ ok {}

//! run c(true) with [open_conn -> opened {conn#1}] => stuck X5 E-Scope
//! run c(false) with [open_conn -> opened {conn#1}; close_conn -> closed] => done ok
"#,
        ),
    );
    // The work, in the body of a loop between, moves a name from around the
    // loop that is restarted, and the next iteration finds it gone.
    stuck_and_rejected(
        "O6",
        &with_fault_prelude(
            r#"
control c(start : string)
    ■ { ok {} }
    uses net
    1  ⊤ ▷ lp : ↻ retry(~i : u32 := 0) {
           ⊢ i ≤ 2
           1  ⊤ ▷ t : ? i < 2
           2  t.false ▷ □ done {}
           3  ⊤ ▷ i ← i + 1
           4  ⊤ ▷ l2 : ↻ within(j : u32 := 0) {
                  1  ⊤ ▷ b : boundary {
                         1  ⊤ ▷ k : Δ keep(start) ▸ kept {}
                         2  ⊤ ▷ fault "again"
                     } contingency (m : string) {
                         1  ⊤ ▷ recover ↑ retry
                     }
                  2  ⊤ ▷ □ end {}
              } ▸ end {}
           5  ⊤ ▷ □ done {}
       } ▸ done {}
    2  ⊤ ▷ ■ ok {}

//! run c("a") with [keep -> kept] => stuck X2 E-Var
"#,
        ),
    );
    // The same where the fault comes through a contingency that passes it
    // on.
    stuck_and_rejected(
        "O6",
        &with_fault_prelude(
            r#"
control c(start : string)
    ■ { ok {} }
    uses net
    1  ⊤ ▷ lp : ↻ retry(~i : u32 := 0) {
           ⊢ i ≤ 2
           1  ⊤ ▷ t : ? i < 2
           2  t.false ▷ □ done {}
           3  ⊤ ▷ i ← i + 1
           4  ⊤ ▷ outer : boundary {
                  1  ⊤ ▷ inner : boundary {
                         1  ⊤ ▷ k : Δ keep(start) ▸ kept {}
                         2  ⊤ ▷ fault "again"
                     } contingency (m : string) {
                         1  ⊤ ▷ escalate
                     }
              } contingency (m2 : string) {
                  1  ⊤ ▷ recover ↑ retry
              }
           5  ⊤ ▷ □ done {}
       } ▸ done {}
    2  ⊤ ▷ ■ ok {}

//! run c("a") with [keep -> kept] => stuck X2 E-Var
"#,
        ),
    );
    // The body of a loop between consumes a parameter of the loop that is
    // restarted, and `recover` reads it.
    stuck_and_rejected(
        "O2",
        &with_fault_prelude(
            r#"
control c(start : string)
    ■ { ok {} }
    uses net
    1  ⊤ ▷ lp : ↻ retry(~i : u32 := 0, s : string := start) {
           ⊢ i ≤ 2
           1  ⊤ ▷ t : ? i < 2
           2  t.false ▷ □ done {}
           3  ⊤ ▷ i ← i + 1
           4  ⊤ ▷ l2 : ↻ within(j : u32 := 0) {
                  1  ⊤ ▷ k : Δ keep(s) ▸ kept {}
                  2  ⊤ ▷ b : boundary {
                         1  ⊤ ▷ fault "again"
                     } contingency (m : string) {
                         1  ⊤ ▷ recover ↑ retry
                     }
                  3  ⊤ ▷ □ end {}
              } ▸ end {}
           5  ⊤ ▷ □ done {}
       } ▸ done {}
    2  ⊤ ▷ ■ ok {}

//! run c("a") with [keep -> kept] => stuck X2 E-Var
"#,
        ),
    );
}

#[test]
fn a_name_in_the_care_of_a_boundary_is_the_constant_it_was_i3() {
    // Review finding RC24. A name with a single binder that is bound to a
    // constant expression is a constant expression ([I3]), and the care
    // list of a boundary binds nothing: in the contingency the name is the
    // one that the boundary took. The checker held it for a name of which
    // only the value is known, so a product with it was no linear term and
    // a valid program was refused.
    done_and_accepted(
        "I3",
        &with_fault_prelude(
            r#"
control c(first : bool)
    ■ { ok {} }
    faults
    1  ⊤ ▷ k : u32 := 2 + 1
    2  ⊤ ▷ b : boundary {
           1  ⊤ ▷ r : Δ risky(first) ▸ fine {}
       } contingency [k] (m : string) {
           1  ⊤ ▷ twice : u32 := k + k
           2  ⊤ ▷ ⊢ k * (k mod 2) = 3 ∧ twice * k = 18
           3  ⊤ ▷ escalate
       }
    3  ⊤ ▷ ■ ok {}

//! run c(true) => faulted "risk"
//! run c(false) => done ok
"#,
        ),
    );
    // The constant is the one that the name has.
    stuck_and_rejected(
        "P1",
        &with_fault_prelude(
            r#"
control c(first : bool)
    ■ { ok {} }
    faults
    1  ⊤ ▷ k : u32 := 2 + 1
    2  ⊤ ▷ b : boundary {
           1  ⊤ ▷ r : Δ risky(first) ▸ fine {}
       } contingency [k] (m : string) {
           1  ⊤ ▷ ⊢ k * (k mod 2) = 4
           2  ⊤ ▷ escalate
       }
    3  ⊤ ▷ ■ ok {}

//! run c(true) => stuck X7 E-Oblige
"#,
        ),
    );
}

#[test]
fn what_a_boundary_has_in_its_care_ends_with_its_work_o5() {
    // Review finding RC5 ([E-Boundary]): when `B₁` ends otherwise than by a
    // fault, what the boundary took into its care ends with it.
    stuck_and_rejected(
        "O5",
        &with_fault_prelude(
            r#"
control c()
    ■ { ok {} }
    faults
    uses lock.io
    1  ⊤ ▷ o : Δ open_lock() ▸ opened {l}
    2  ⊤ ▷ b : boundary {
           1  ⊤ ▷ x : u32 := 1
       } contingency [l] (m : string) {
           1  ⊤ ▷ escalate
       }
    3  ⊤ ▷ ■ ok {}

//! run c() with [open_lock -> opened {lock#1}] => stuck X5 E-Scope
"#,
        ),
    );
    stuck_and_rejected(
        "O5",
        &with_fault_prelude(
            r#"
control c()
    ■ { ok {} }
    faults
    uses lock.io
    1  ⊤ ▷ o : Δ open_lock() ▸ opened {l}
    2  ⊤ ▷ b : boundary {
           1  ⊤ ▷ ■ ok {}
       } contingency [l] (m : string) {
           1  ⊤ ▷ escalate
       }
    3  ⊤ ▷ ⊥

//! run c() with [open_lock -> opened {lock#1}] => stuck X5 E-Scope
"#,
        ),
    );
    // A work that always faults passes its care to the contingency, which
    // consumes it.
    done_and_accepted(
        "O5",
        &with_fault_prelude(
            r#"
control c()
    ■ { ok {} }
    faults
    uses lock.io
    1  ⊤ ▷ o : Δ open_lock() ▸ opened {l}
    2  ⊤ ▷ b : boundary {
           1  ⊤ ▷ fault "stop"
       } contingency [l] (m : string) {
           1  ⊤ ▷ k : Δ close_lock(l) ▸ closed {}
           2  ⊤ ▷ escalate
       }
    3  ⊤ ▷ ⊥

//! run c() with [open_lock -> opened {lock#1}; close_lock -> closed] => faulted "stop"
"#,
        ),
    );
    // Something that holds no obligation may be in its care when the work
    // ends.
    done_and_accepted(
        "O5",
        &with_fault_prelude(
            r#"
control c(tag : string)
    ■ { ok {} }
    faults
    1  ⊤ ▷ b : boundary {
           1  ⊤ ▷ x : u32 := 1
       } contingency [tag] (m : string) {
           1  ⊤ ▷ escalate
       }
    2  ⊤ ▷ ■ ok {}

//! run c("t") => done ok
"#,
        ),
    );
}

#[test]
fn nothing_encloses_the_contingency_of_a_named_boundary_f1_f6() {
    // Review finding RC6 ([E-Supervise]): a call that may fault in the
    // contingency of a named boundary is stuck when it does.
    stuck_and_rejected(
        "F1",
        &with_fault_prelude(
            r#"
boundary guarded() {
    1  ⊤ ▷ fault "work"
} contingency (m : string) {
    1  ⊤ ▷ h : Δ helper_faults() ▸ done {}
    2  ⊤ ▷ terminate
}

control c()
    ■ { done {} }
    faults
    1  ⊤ ▷ supervise guarded()
    2  ⊤ ▷ ■ done {}

//! run c() => stuck X8 E-Unwind
"#,
        ),
    );
    done_and_accepted(
        "F1",
        &with_fault_prelude(
            r#"
boundary guarded() {
    1  ⊤ ▷ fault "work"
} contingency (m : string) {
    1  ⊤ ▷ h : Δ helper() ▸ done {}
    2  ⊤ ▷ terminate
}

control c()
    ■ { done {} }
    1  ⊤ ▷ supervise guarded()
    2  ⊤ ▷ ■ done {}

//! run c() => done done
"#,
        ),
    );
    // `fault` and `escalate` are the ends of that contingency, and the
    // lexical one inside a control may call what faults when the control
    // permits it.
    done_and_accepted(
        "F1",
        &with_fault_prelude(
            r#"
control c()
    ■ { done {} }
    faults
    1  ⊤ ▷ b : boundary {
           1  ⊤ ▷ fault "work"
       } contingency (m : string) {
           1  ⊤ ▷ h : Δ helper_faults() ▸ done {}
           2  ⊤ ▷ escalate
       }
    2  ⊤ ▷ ⊥

//! run c() => faulted "helper"
"#,
        ),
    );
}

#[test]
fn the_effects_of_a_supervised_boundary_count_toward_what_supervises_f3_f6() {
    // Review finding RC20 ([F6]): the effects of both bodies of a boundary
    // count toward the control that supervises, through a boundary that
    // supervises another as well.
    let program = r#"
boundary inner() {
    1  ⊤ ▷ e : Δ emit("in") ▸ done {}
    2  ⊤ ▷ terminate
} contingency (m : string) {
    1  ⊤ ▷ terminate
}

boundary outer() {
    1  ⊤ ▷ supervise inner()
    2  ⊤ ▷ terminate
} contingency (m : string) {
    1  ⊤ ▷ terminate
}

control c()
    ■ { done {} }
    USES
    1  ⊤ ▷ supervise outer()
    2  ⊤ ▷ ■ done {}

//! run c() => RESULT
"#;
    done_and_accepted(
        "F3",
        &program
            .replace("USES", "uses console.write")
            .replace("RESULT", r#"done done trace [emit("in") -> done]"#),
    );
    stuck_and_rejected(
        "F3",
        &program
            .replace("    USES\n", "")
            .replace("RESULT", "stuck X9 E-Effect"),
    );
}

#[test]
fn the_names_around_a_boundary_are_judged_where_the_work_faults_f2_f6() {
    // RC4, for [F2] and [F6]: a statement of `B₂` that may fault leaves the
    // names around the boundary as they were where `B₁` faulted, and that
    // is where the two rules are required of them.

    // The work closes the lock before it faults, so `escalate` unwinds
    // nothing that a fault cannot release.
    done_and_accepted(
        "F2",
        &with_fault_prelude(
            r#"
extern control shut(l : lock)
    ■ { closed {} }
    uses lock.io

control c()
    ■ { ok {} }
    faults
    uses lock.io
    1  ⊤ ▷ o : Δ open_lock() ▸ opened {l}
    2  ⊤ ▷ b : boundary {
           1  ⊤ ▷ k : Δ shut(l) ▸ closed {}
           2  ⊤ ▷ fault "stop"
       } contingency (m : string) {
           1  ⊤ ▷ escalate
       }
    3  ⊤ ▷ ⊥

//! run c() with [open_lock -> opened {lock#1}; shut -> closed] => faulted "stop"
"#,
        ),
    );
    // It faults with the lock open, and the fault that `escalate` passes on
    // meets it.
    stuck_and_rejected(
        "F2",
        &with_fault_prelude(
            r#"
control c()
    ■ { ok {} }
    faults
    uses lock.io
    1  ⊤ ▷ o : Δ open_lock() ▸ opened {l}
    2  ⊤ ▷ b : boundary {
           1  ⊤ ▷ fault "stop"
       } contingency (m : string) {
           1  ⊤ ▷ escalate
       }
    3  ⊤ ▷ ⊥

//! run c() with [open_lock -> opened {lock#1}] => stuck X8 E-Unwind
"#,
        ),
    );
    // A retained name of a named boundary, with a lexical boundary inside
    // its work whose contingency passes the fault on.
    let program = r#"
boundary guarded(tag : string) retains tag {
    1  ⊤ ▷ inner : boundary {
           WORK
           9  ⊤ ▷ fault "work"
       } contingency (m : string) {
           1  ⊤ ▷ escalate
       }
    2  ⊤ ▷ terminate
} contingency (m : string) {
    1  ⊤ ▷ g : Δ note(&tag) ▸ done {}
    2  ⊤ ▷ terminate
}

contingent control note(msg : &string)
    ■ { done {} }
    uses console.write
    1  ⊤ ▷ e : Δ emit(msg) ▸ done {}
    2  ⊤ ▷ ■ done {}

control c()
    ■ { done {} }
    uses console.write
    1  ⊤ ▷ supervise guarded("t")
    2  ⊤ ▷ ■ done {}

//! run c() => RESULT
"#;
    done_and_accepted(
        "F6",
        &program
            .replace("           WORK\n", "")
            .replace("RESULT", r#"done done trace [emit("t") -> done]"#),
    );
    stuck_and_rejected(
        "F6",
        &program
            .replace("WORK", "1  ⊤ ▷ gone : string := tag")
            .replace("RESULT", "stuck X2 E-Supervise"),
    );
}

#[test]
fn a_component_read_out_of_a_constructor_has_no_declared_interval_a9() {
    // Review finding RC8. The declared interval of [A9] belongs to a place.
    // A component read out of a constructor is the term that was written
    // there, and a formula does not hold that term to the range of the
    // field's type, at any depth of the constructor.
    let declarations = "struct pair {left : u32, right : u32}\nstruct wrap {inner : pair}\n";
    stuck_and_rejected(
        "P1",
        &[
            declarations,
            r#"
control c(a : u32)
    ■ { r {} }
    1  ⊤ ▷ ⊢ wrap {pair {a + 1, 0}}.inner.left * wrap {pair {a + 1, 0}}.inner.left ≤ 18446744065119617025
    2  ⊤ ▷ ■ r {}

//! run c(4294967295) => stuck X7 E-Oblige
//! run c(3) => done r
"#,
        ]
        .concat(),
    );
    // A component of a name has the interval of its type.
    done_and_accepted(
        "A9",
        &[
            declarations,
            r#"
control c(a : u32)
    ■ { r {} }
    1  ⊤ ▷ w : wrap := wrap {pair {a, 0}}
    2  ⊤ ▷ ⊢ w.inner.left * w.inner.left ≤ 18446744065119617025
    3  ⊤ ▷ ■ r {}

//! run c(4294967295) => done r
"#,
        ]
        .concat(),
    );
}

#[test]
fn a_move_mark_stands_on_what_is_consumed_o3() {
    // Review finding RC7. The oracle moved `v` at `len(▾v)` and the checker
    // read it. The position decides whether an expression is consumed
    // ([E-Var]), and a read moves nothing ([O3]), so the mark on a read is
    // refused when the text is resolved.
    for (read, consumed) in [
        ("n : usize := len(▾v)", "w : [u32] := ▾v"),
        ("n : u32 := (▾v)[0]", "w : [[u32]] := [▾v]"),
        ("t : ? len(▾v) = 2", "w : holder := holder {▾v}"),
    ] {
        let program = |statement: &str| {
            format!(
                "struct holder {{items : [u32]}}\ncontrol c()\n    ■ {{ r {{}} }}\n    1  ⊤ ▷ v : [u32] := [1, 2]\n    2  ⊤ ▷ {statement}\n    3  ⊤ ▷ ■ r {{}}\n\n//! run c() => done r\n"
            )
        };
        match load(&program(read)) {
            Ok(_) => panic!("[O3] a move mark on a read is resolved:\n{}", program(read)),
            Err(error) => assert!(error.to_string().contains("[O3]"), "{error}"),
        }
        done_and_accepted("O3", &program(consumed));
    }
}

#[test]
fn a_contingency_runs_on_the_histories_that_fault_f5_f6_p6() {
    // `B₂` runs after a fault at a statement of `B₁` ([F5]), so the
    // histories of its statements are those of the statements of `B₁` that
    // may fault. The checker gave them every history of the boundary, and
    // refused `⊥` in the contingency of work that cannot fault.
    done_and_accepted(
        "P6",
        r#"
control quiet(n : u32)
    ■ { ok {v : u32} }
    1  ⊤ ▷ b : boundary {
           1  ⊤ ▷ inside : u32 := n
       } contingency (m : string) {
           1  ⊤ ▷ ⊥
       }
    2  ⊤ ▷ ■ ok {n}

//! run quiet(4) => done ok {4}
"#,
    );
    // What holds where the work faults holds in the contingency.
    done_and_accepted(
        "P1",
        r#"
control guarded(n : u32)
    ■ { ok {v : u32} }
    faults
    1  ⊤ ▷ b : boundary {
           1  ⊤ ▷ t : ? n > 5
           2  t.true ▷ fault "big"
       } contingency [n] (m : string) {
           1  ⊤ ▷ ⊢ n > 5
           2  ⊤ ▷ escalate
       }
    2  ⊤ ▷ ■ ok {n}

//! run guarded(4) => done ok {4}
//! run guarded(9) => faulted "big"
"#,
    );
    // Work that may fault has a contingency that runs.
    stuck_and_rejected(
        "P6",
        r#"
control loud(n : u32)
    ■ { ok {v : u32} }
    1  ⊤ ▷ b : boundary {
           1  ⊤ ▷ t : ? n > 5
           2  t.true ▷ fault "big"
       } contingency (m : string) {
           1  ⊤ ▷ ⊥
       }
    2  ⊤ ▷ ■ ok {n}

//! run loud(9) => stuck X6 E-Impossible
//! run loud(1) => done ok {1}
"#,
    );
    // The same of a named boundary ([F6]).
    done_and_accepted(
        "P6",
        r#"
boundary calm(tag : string) retains tag {
    1  ⊤ ▷ terminate
} contingency (m : string) {
    1  ⊤ ▷ ⊥
}

control uses_calm()
    ■ { done {} }
    1  ⊤ ▷ supervise calm("x")
    2  ⊤ ▷ ■ done {}

//! run uses_calm() => done done
"#,
    );
    stuck_and_rejected(
        "P6",
        r#"
boundary rough(tag : string) retains tag {
    1  ⊤ ▷ fault "x"
} contingency (m : string) {
    1  ⊤ ▷ ⊥
}

control uses_rough()
    ■ { done {} }
    1  ⊤ ▷ supervise rough("x")
    2  ⊤ ▷ ■ done {}

//! run uses_rough() => stuck X6 E-Impossible
"#,
    );
}

#[test]
fn a_captured_outcome_keeps_its_conditions_where_the_capture_is_not_visible_i12() {
    // Review finding RC23. A decision on a captured outcome adds the
    // conditions of the captured operation; where the capture is not
    // visible, because the value arrived as a parameter or as a payload,
    // they are over fresh names for the arguments. The checker added none.
    let header = r#"
extern control fetch(id : u32)
    ■ { ok {} │ failed {code : u32} ⇐ code ≤ 9 }

extern control scale(by : u32)
    ■ { low {v : u32} ⇐ by ≤ 4 ∧ v ≤ by │ high {v : u32} ⇐ by > 4 }
"#;
    // Through the payload of a loop.
    done_and_accepted(
        "P4",
        &format!(
            r#"{header}
control c(id : u32)
    ■ {{ fine {{}} │ code {{c : u32}} ⇐ c ≤ 9 }}
    1  ⊤ ▷ kept := capture fetch(id)
    2  ⊤ ▷ s : ↻ once(i : u32 := 0) {{
           1  ⊤ ▷ □ out {{▾kept}}
       }} ▸ out {{given}}
    3  ⊤ ▷ d : Δ outcome(▾given) ▸ ok {{}} │ failed {{code}}
    4  d.ok ▷ ■ fine {{}}
    5  d.failed ▷ ■ code {{code}}

//! run c(1) with [fetch -> failed {{9}}] => done code {{9}}
//! run c(1) with [fetch -> ok] => done fine
"#
        ),
    );
    // As the parameter of a loop, which is one name for every iteration.
    done_and_accepted(
        "P1",
        &format!(
            r#"{header}
control c(id : u32)
    ■ {{ fine {{}} }}
    1  ⊤ ▷ kept := capture fetch(id)
    2  ⊤ ▷ s : ↻ once(i : u32 := 0, held : outcome⟨fetch⟩ := ▾kept) {{
           1  ⊤ ▷ d : Δ outcome(▾held) ▸ ok {{}} │ failed {{code}}
           2  d.failed ▷ ⊢ code ≤ 9
           3  ⊤ ▷ □ out {{}}
       }} ▸ out {{}}
    3  ⊤ ▷ ■ fine {{}}

//! run c(1) with [fetch -> failed {{9}}] => done fine
"#
        ),
    );
    // One fresh name stands for an argument in the whole condition: `by ≤ 4`
    // and `v ≤ by` give `v ≤ 4`.
    done_and_accepted(
        "P4",
        &format!(
            r#"{header}
control c(by : u32)
    ■ {{ small {{v : u32}} ⇐ v ≤ 4 │ large {{}} }}
    1  ⊤ ▷ kept := capture scale(by)
    2  ⊤ ▷ s : ↻ once(i : u32 := 0) {{
           1  ⊤ ▷ □ out {{▾kept}}
       }} ▸ out {{given}}
    3  ⊤ ▷ d : Δ outcome(▾given) ▸ low {{v}} │ high {{w}}
    4  d.low ▷ ■ small {{v}}
    5  d.high ▷ ■ large {{}}

//! run c(3) with [scale -> low {{2}}] => done small {{2}}
//! run c(7) with [scale -> high {{70}}] => done large
"#
        ),
    );
    // The conditions say no more than they say.
    stuck_and_rejected(
        "P4",
        &format!(
            r#"{header}
control c(id : u32)
    ■ {{ fine {{}} │ code {{c : u32}} ⇐ c ≤ 8 }}
    1  ⊤ ▷ kept := capture fetch(id)
    2  ⊤ ▷ s : ↻ once(i : u32 := 0) {{
           1  ⊤ ▷ □ out {{▾kept}}
       }} ▸ out {{given}}
    3  ⊤ ▷ d : Δ outcome(▾given) ▸ ok {{}} │ failed {{code}}
    4  d.ok ▷ ■ fine {{}}
    5  d.failed ▷ ■ code {{code}}

//! run c(1) with [fetch -> failed {{9}}] => stuck X7 E-Exit
"#
        ),
    );
    // A fresh name is not the argument of the capture: what the condition
    // says of the argument is not known of the name that was given.
    reject_core(
        "P4",
        &format!(
            r#"{header}
control c(by : u32)
    ■ {{ small {{v : u32}} ⇐ v ≤ by │ large {{}} }}
    1  ⊤ ▷ kept := capture scale(by)
    2  ⊤ ▷ s : ↻ once(i : u32 := 0) {{
           1  ⊤ ▷ □ out {{▾kept}}
       }} ▸ out {{given}}
    3  ⊤ ▷ d : Δ outcome(▾given) ▸ low {{v}} │ high {{w}}
    4  d.low ▷ ■ small {{v}}
    5  d.high ▷ ■ large {{}}
"#
        ),
    );
}

/// A program for the mutations of ownership: each control owns something
/// that a statement of it gives back, and a mutation of one statement
/// leaves it owed, gives it twice, or lets a fault meet it.
const OWNERSHIP: &str = r#"
extern resource conn

extern resource lease on fault release

extern control open_conn()
    ■ { opened {c : conn} }
    uses net

extern control close_conn(c : conn)
    ■ { closed {} }
    uses net

extern control take_lease()
    ■ { taken {l : lease} }
    uses net

extern control give_lease(l : lease)
    ■ { given {} }
    uses net

extern control keep(s : string)
    ■ { done {} }
    uses net

control may(n : u32)
    ■ { done {} }
    faults
    ⊤ ▷ t : ? n = 0
    t.true ▷ fault "zero"
    t.false ▷ ■ done {}

pub control owns(s : string)
    ■ { done {} }
    uses net
    ⊤ ▷ d0 : Δ open_conn() ▸ opened {c}
    ⊤ ▷ d1 : Δ keep(clone(s)) ▸ done {}
    ⊤ ▷ d2 : Δ keep(▾s) ▸ done {}
    ⊤ ▷ d3 : Δ close_conn(▾c) ▸ closed {}
    ⊤ ▷ ■ done {}

pub control leases(n : u32)
    ■ { done {} }
    faults
    uses net
    ⊤ ▷ d0 : Δ take_lease() ▸ taken {l}
    ⊤ ▷ d1 : Δ may(n) ▸ done {}
    ⊤ ▷ d2 : Δ give_lease(▾l) ▸ given {}
    ⊤ ▷ ■ done {}

pub control guards(n : u32)
    ■ { done {} }
    faults
    uses net
    ⊤ ▷ d0 : Δ open_conn() ▸ opened {c}
    ⊤ ▷ d1 : Δ close_conn(▾c) ▸ closed {}
    ⊤ ▷ d2 : Δ may(n) ▸ done {}
    ⊤ ▷ ■ done {}
"#;

/// The runs of [`OWNERSHIP`]: each control, with a fault and without one.
fn ownership_runs() -> Vec<(String, Vec<villanelle_v2::oracle::Value>)> {
    use villanelle_v2::int::Int;
    use villanelle_v2::oracle::Value;
    let number = |n: u64| vec![Value::Int(Int::from_u64(n))];
    vec![
        ("owns".to_string(), vec![Value::String("text".to_string())]),
        ("leases".to_string(), number(0)),
        ("leases".to_string(), number(1)),
        ("guards".to_string(), number(0)),
        ("guards".to_string(), number(1)),
    ]
}

/// The kinds of mutation that slice 2 adds seed the defects of ownership:
/// each has a mutant of [`OWNERSHIP`] that is stuck in the oracle, in the
/// state the kind is for, and the checker rejects every mutant that is
/// stuck. The program itself runs to its ends and is accepted.
#[test]
fn mutations_of_ownership_are_stuck_and_rejected() {
    use std::collections::{BTreeMap, BTreeSet};
    use villanelle_v2::mutate::{self, Class, Kind};
    use villanelle_v2::oracle::Config;

    let tree = villanelle_v2::text::parse(OWNERSHIP).expect("the program reads");
    let typed = villanelle_v2::resolve::resolve(&tree).expect("the program resolves");
    accept_core("O4", OWNERSHIP);
    let config = Config::default();
    let runs = ownership_runs();
    let whole = mutate::Mutant {
        kind: Kind::DropGuard,
        control: String::new(),
        detail: String::new(),
        program: tree.clone(),
    };
    assert!(
        matches!(mutate::classify(&whole, &runs, 1, &config), Class::Unstuck),
        "a run of the program is stuck"
    );
    drop(typed);

    let mut stuck: BTreeMap<Kind, BTreeSet<String>> = BTreeMap::new();
    for mutant in mutate::mutate(&tree) {
        let Class::Stuck(state) = mutate::classify(&mutant, &runs, 1, &config) else {
            continue;
        };
        stuck
            .entry(mutant.kind)
            .or_default()
            .insert(format!("X{} {}", state.state, state.clause));
        let resolved = villanelle_v2::resolve::resolve(&mutant.program).expect("it ran");
        assert!(
            check::check(&resolved).is_err(),
            "{:?} in `{}` ({}) is stuck (X{} {}: {}) and the checker accepts it:\n{}",
            mutant.kind,
            mutant.control,
            mutant.detail,
            state.state,
            state.clause,
            state.detail,
            mutant.program.print()
        );
    }
    let states = |kind: Kind| -> Vec<String> {
        stuck
            .get(&kind)
            .map(|set| set.iter().cloned().collect())
            .unwrap_or_default()
    };
    // Removed: a body without its end, a connection still owed where its
    // scope ends, and a fault that meets what is owed.
    assert_eq!(
        states(Kind::RemoveStatement),
        ["X1 E-End", "X5 E-Scope", "X8 E-Unwind"],
        "{stuck:?}"
    );
    // Swapped: the text is given away before its clone is made, the
    // connection is still owed at the exit, or the fault comes before the
    // connection is closed.
    assert_eq!(
        states(Kind::SwapStatements),
        ["X2 E-Var", "X5 E-Scope", "X8 E-Unwind"],
        "{stuck:?}"
    );
    assert_eq!(states(Kind::ConsumeClone), ["X2 E-Var"], "{stuck:?}");
    assert_eq!(
        states(Kind::DropFaults),
        ["X8 E-Fault", "X8 E-Unwind"],
        "{stuck:?}"
    );
    assert_eq!(states(Kind::DropFaultRelease), ["X8 E-Unwind"], "{stuck:?}");
}

#[test]
fn constructor_terms_are_one_value_exactly_where_their_contents_are_a4_m1() {
    // Review finding RC22. The model that the search completes for a
    // candidate gives a constructor term the number of its content
    // (`facts/completion.rs`), and nothing of that decides an answer: a
    // premise or an instance that the model fails is added, and a model
    // that fails none is evaluated in the goal and in every premise
    // ([M1]). The programs here are decided by what [A4] says of two
    // constructor terms, with the terms equal and different in every way
    // that the completion numbers them: by an argument that is a value of
    // the program, by a pattern that takes a term apart, and by a copy.
    let declarations = "copy struct flag {on : bool}\nstruct pair {left : flag, right : u8}\n";
    done_and_accepted(
        "A4",
        &[
            declarations,
            r#"
control c(p : u32)
    ■ { r {} }
    1  ⊤ ▷ flag {a} := flag {p = 6}
    2  ⊤ ▷ flag {b} := flag {p ≠ 6}
    3  ⊤ ▷ f : flag := flag {p > 5 ∧ p < 7}
    4  ⊤ ▷ g : flag := f
    5  ⊤ ▷ pair {h, n} := pair {g, 3}
    6  ⊤ ▷ ⊢ (a ∨ b) ∧ ¬(a ∧ b)
    7  ⊤ ▷ ⊢ (h.on ∧ a ∨ ¬h.on ∧ b) ∧ n = 3
    8  ⊤ ▷ ■ r {}

//! run c(6) => done r
//! run c(7) => done r
"#,
        ]
        .concat(),
    );
    // Two terms with the same argument are one value, so a field of one is
    // the field of the other: the claim that they differ is refuted, with a
    // model in which the two are one number.
    stuck_and_rejected(
        "P1",
        &[
            declarations,
            r#"
control c(p : u32)
    ■ { r {} }
    1  ⊤ ▷ flag {a} := flag {p = 6}
    2  ⊤ ▷ f : flag := flag {p > 5 ∧ p < 7}
    3  ⊤ ▷ ⊢ a ∧ ¬f.on ∨ ¬a ∧ f.on
    4  ⊤ ▷ ■ r {}

//! run c(6) => stuck X7 E-Oblige
"#,
        ]
        .concat(),
    );
    // Two terms with different arguments are two values: the claim that a
    // field of one is that of the other is refuted for the argument that
    // makes them differ.
    stuck_and_rejected(
        "P1",
        &[
            declarations,
            r#"
control c(p : u32)
    ■ { r {} }
    1  ⊤ ▷ flag {a} := flag {p = 6}
    2  ⊤ ▷ flag {b} := flag {p ≠ 6}
    3  ⊤ ▷ pair {h, n} := pair {flag {b}, 3}
    4  ⊤ ▷ ⊢ h.on ∧ a ∨ ¬h.on ∧ ¬a
    5  ⊤ ▷ ■ r {}

//! run c(6) => stuck X7 E-Oblige
"#,
        ]
        .concat(),
    );
}

/// The files of the suite that hold a rule of the data each, with the runs
/// that apply it and the runs that are stuck by it.
const RULE_FILES: [&str; 14] = [
    "e_var",
    "e_field_index",
    "e_build",
    "e_temp",
    "e_bind_unpack",
    "e_assign",
    "e_operands",
    "e_outcome",
    "e_resource_scope",
    "e_unwind_values",
    "op_vectors",
    "op_maps",
    "op_text",
    "checked_release_order",
];

/// The controls of the rule files that the checker refuses although no run
/// of them is stuck, with the clause and the reason. The checker goes by
/// the type of a name where the instrumented semantics looks at the value,
/// and by the allowance of the caller where the run is stuck at the effect.
const ASKS_MORE: [(&str, &str, &str, &str); 3] = [
    (
        "e_resource_scope",
        "nothing_owed",
        "O5",
        "an empty vector of resources holds no obligation, and its type has kind `must`",
    ),
    (
        "e_unwind_values",
        "fault_with_plain",
        "F2",
        "an empty vector of locks is destroyed under a fault, and its type is not fault-releasable",
    ),
    (
        "op_text",
        "caller_unallowed",
        "F3",
        "the run is stuck in `says`, at the effect, and the control that does not allow it is this one",
    ),
];

/// The controls in which a run is stuck although the checker accepts them:
/// the statement that is stuck is theirs, and the clause is broken by a
/// control further out on the stack ([E-Effect]).
const STUCK_BY_ANOTHER: [(&str, &str); 1] = [("op_text", "says")];

/// Holds the checker against the oracle on files of the suite, control by
/// control: a control in which a run is stuck must be rejected, and any
/// other must be accepted, apart from those of `asks_more`, which the
/// checker refuses by the clause named, and those of `stuck_by_another`.
/// Gives the numbers of the controls rejected and accepted.
fn held_against_the_oracle(
    files: &[&str],
    asks_more: &[(&str, &str, &str, &str)],
    stuck_by_another: &[(&str, &str)],
) -> (usize, usize) {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/slice2");
    let mut failures = Vec::new();
    let mut rejected = 0;
    let mut accepted = 0;
    let mut asked_more = 0;
    for name in files {
        let source = std::fs::read_to_string(dir.join(format!("{name}.core"))).unwrap();
        let report = villanelle_v2::script::check(&source);
        assert!(
            report.failures.is_empty(),
            "{name}: {}",
            report.failures.join("\n")
        );
        let program = load(&source).unwrap_or_else(|e| panic!("{name}: {e}"));
        let verdicts = check::check_each(&program).unwrap_or_else(|e| panic!("{name}: {e}"));
        for (control, verdict) in verdicts {
            if let Some((_, _, clause, _)) = asks_more
                .iter()
                .find(|(file, asked, _, _)| file == name && *asked == control)
            {
                // No run of the control is stuck, and the checker refuses
                // it by the clause that the table names.
                assert!(!report.stuck_in.contains_key(&control), "{name}: {control}");
                match verdict {
                    Some(error) if error.clause == *clause => asked_more += 1,
                    Some(error) => {
                        failures.push(format!("{name}: [{clause}] is expected, and {error}"))
                    }
                    None => failures.push(format!("{name}: `{control}` is accepted")),
                }
                continue;
            }
            let stuck = report
                .stuck_in
                .get(&control)
                .filter(|_| !stuck_by_another.contains(&(*name, control.as_str())));
            match (stuck, verdict) {
                (Some(states), None) => failures.push(format!(
                    "{name}: `{control}` is accepted, and a run of it is stuck ({})",
                    states.iter().cloned().collect::<Vec<_>>().join(", ")
                )),
                (None, Some(error)) => {
                    failures.push(format!("{name}: no run is stuck, and {error}"))
                }
                (Some(_), Some(_)) => rejected += 1,
                (None, None) => accepted += 1,
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    assert_eq!(asked_more, asks_more.len());
    (rejected, accepted)
}

/// Every control of the rule files in which a run of the oracle is stuck is
/// rejected by the checker, and every other control of them is accepted:
/// the checker draws the line where the instrumented semantics does, clause
/// by clause ([O1] to [O5], [O3a], [P5], [F1] to [F3]).
#[test]
fn the_rule_files_of_the_data_are_rejected_exactly_where_a_run_is_stuck() {
    let counts = held_against_the_oracle(&RULE_FILES, &ASKS_MORE, &STUCK_BY_ANOTHER);
    assert_eq!(counts, (62, 59));
}

/// The statements of `facts_data.core` that are true of every run and that
/// the checker does not prove: two that the logic leaves out ([A3]), and
/// three of review finding RC26, which [A4] and [A5] entail.
const LEFT_OUT: [(&str, &str, &str, &str); 5] = [
    (
        "facts_data",
        "literal_elements",
        "P1",
        "the logic knows the length of a vector literal and nothing of its elements",
    ),
    (
        "facts_data",
        "literal_text_length",
        "P1",
        "what `len` counts in a string is for the text library to say",
    ),
    (
        "facts_data",
        "one_value",
        "P1",
        "RC26: a struct without fields has no field that says its values are equal",
    ),
    (
        "facts_data",
        "one_constructor",
        "P1",
        "RC26: a value is known to be of a constructor only where a decision took it apart",
    ),
    (
        "facts_data",
        "one_of_its_constructors",
        "P1",
        "RC26: the same, for a type of three constructors",
    ),
];

/// Section 5 of the fact logic, held against the oracle. Each axiom of [A3]
/// to [A6] is a statement of a program that every run finds true and the
/// checker proves, and beside it is a statement that some run finds false:
/// the run is stuck, and the checker refuses the control. So the instances
/// of the crate decide the axioms as statements ([J1], [J3]), apart from
/// what `LEFT_OUT` lists.
#[test]
fn the_axioms_of_the_data_are_proved_and_what_they_do_not_say_is_not() {
    let counts = held_against_the_oracle(&["facts_data"], &LEFT_OUT, &[]);
    assert_eq!(counts, (21, 23));
}

/// Review finding RC25 ([M2], [M7]): a name of a data type has no number,
/// and a counterexample gives none. It gives the length of such a name
/// where the model has one, and the values of the integer names as before.
#[test]
fn a_counterexample_gives_no_number_for_a_name_of_a_data_type_m2() {
    let error = reject_core(
        "P5",
        r#"
struct label {name : string, count : u32}

control c(l : label, v : [u32], s : string, n : u32)
    ■ { r {x : u32, k : usize} }
    1  ⊤ ▷ k : usize := len(s)
    2  ⊤ ▷ ■ r {v[0], k}
"#,
    );
    let values = &error.counterexample.as_ref().expect("a model").values;
    for name in ["l", "v", "s"] {
        assert!(!values.contains_key(name), "{name} = {}", values[name]);
    }
    assert_eq!(values.get("len(v)").map(String::as_str), Some("0"));
    assert!(values.contains_key("n") && values.contains_key("k"));
    let text = error.to_string();
    assert!(text.contains("len(v) = 0"), "{text}");
}
