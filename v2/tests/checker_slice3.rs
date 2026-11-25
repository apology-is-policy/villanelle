//! Phase 3 checker conformance tests for slice 3.
//!
//! Tests static ROBDD loan checking (`[L1]`–`[L5]`, `[L2a]`, `[RM7]`),
//! borrow ownership refinements (`[O0]`, `[O3]`), and borrow/view fact-logic
//! propagation and invalidation (`[I7]`, `[I9]`):
//! - all 34 synchronous worked examples in `docs/v2/references.md` (§§4–10),
//! - both canonical Slice 3 `.rails` surface programs with kernel validation,
//! - every stuck Slice 3 `.core` control plus `[RM7]` `disjoint_elements`.

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

fn accept_core(label: &str, source: &str) -> CheckedProgram {
    let report = match check_core(source) {
        Ok(r) => r,
        Err(e) => panic!("[{label}] expected acceptance, got: {e}\n{source}"),
    };
    report
        .revalidate()
        .unwrap_or_else(|e| panic!("[{label}] the kernel rejected {e}"));
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

fn accept_rails(label: &str, source: &str) -> CheckedProgram {
    let report = match check_rails(source) {
        Ok(r) => r,
        Err(e) => panic!("[{label}] expected Rails acceptance, got: {e}\n{source}"),
    };
    report
        .revalidate()
        .unwrap_or_else(|e| panic!("[{label}] the kernel rejected {e}"));
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
fn references_shared_and_exclusive_examples_4_to_6() {
    // Examples 4.1 & 4.2 (Rails + Core): shared borrow return (`∈`) and write after last use.
    accept_rails(
        "ex4.1-4.2",
        "
extern control emit(text: &string) ■ done

control widest(a: &string, b: &string) ■ pick {text: &string ∈ a, b}
│ ? len(a) ≥ len(b) → ■ pick {a}
│ ■ pick {b}
╵

control announce() ■ done
│ ~left: string := \"alder\"
│ right: string := \"birch\"
│ Δ widest(left, right): pick {text}
│ emit(text)
│ emit(left)
│ left ← \"cedar\"
│ ■ done
╵
",
    );

    // Example 4.3: assign lender before last use of shared borrow holder -> [L3].
    reject_rails(
        "L3",
        "
extern control emit(text: &string) ■ done

control widest(a: &string, b: &string) ■ pick {text: &string ∈ a, b}
│ ? len(a) ≥ len(b) → ■ pick {a}
│ ■ pick {b}
╵

control bad_announce() ■ done
│ ~left: string := \"alder\"
│ right: string := \"birch\"
│ Δ widest(left, right): pick {text}
│ left ← \"cedar\"
│ emit(text)
│ ■ done
╵
",
    );

    // Example 4.4 (accepted): copy scalar & clone string through shared borrow.
    accept_rails(
        "ex4.4-ok",
        "
struct tally {count: u64, note: string}

control describe(item: &tally) ■ seen {count: u64, note: string}
│ count: u64 := item.count
│ note: string := clone(item.note)
│ ■ seen {count, note}
╵
",
    );

    // Example 4.4 (rejected): moving non-copy `string` out through shared borrow -> [O3].
    reject_rails(
        "O3",
        "
struct tally {count: u64, note: string}

control bad_describe(item: &tally) ■ seen {count: u64, note: string}
│ count: u64 := item.count
│ note: string := item.note
│ ■ seen {count, note}
╵
",
    );

    // Example 5.1: lending exclusive field sequentially.
    accept_rails(
        "ex5.1",
        "
struct tally {count: u64, note: string}
extern control emit(text: &string) ■ done

control bump(counter: &~u64) ■ done
│ ? counter < 1000 → counter ← counter + 1
│ ■ done
╵

control count_twice() ■ done
│ ~t: tally := tally {0, \"start\"}
│ bump(~t.count)
│ bump(~t.count)
│ emit(t.note)
│ ■ done
╵
",
    );

    // Example 5.3: named borrow of one field, write to disjoint field, then re-lend.
    accept_rails(
        "ex5.3",
        "
struct tally {count: u64, note: string}

control bump(counter: &~u64) ■ done
│ ? counter < 1000 → counter ← counter + 1
│ ■ done
╵

control restart(item: &~tally) ■ done
│ slot: &~u64 := ~item.count
│ slot ← 0
│ item.note ← \"restarted\"
│ bump(~slot)
│ ■ done
╵
",
    );

    // Example 5.4: write lent field through parent while child borrow `slot` is used afterwards -> [L3].
    reject_rails(
        "L3",
        "
struct tally {count: u64, note: string}

control bump(counter: &~u64) ■ done
│ ? counter < 1000 → counter ← counter + 1
│ ■ done
╵

control bad_restart(item: &~tally) ■ done
│ slot: &~u64 := ~item.count
│ slot ← 0
│ item.note ← \"restarted\"
│ item.count ← 5
│ bump(~slot)
│ ■ done
╵
",
    );

    // Example 5.5 & 5.7 & 5.8: disjoint field borrows from `&~`, `[E-Operands]`, sequential index swaps.
    accept_rails(
        "ex5.5-5.7-5.8",
        "
struct pair {left: [u32], right: [u32]}

control halves(both: &~pair) ■ split {left: &~[u32] ∈ both, right: &~[u32] ∈ both}
│ ■ split {~both.left, ~both.right}
╵

control fill() ■ done
│ ~p: pair := pair {[1, 2], [3]}
│ Δ halves(~p): split {left, right}
│ left.push(4)
│ right.push(5)
│ left.push(6)
│ ~values: [usize] := [1, 2]
│ values.push(len(values))
│ ■ done
╵

control swap_first_two(grid: &~[u32]) ⊢ len(grid) ≥ 2 ■ done
│ first: u32 := grid[0]
│ grid[0] ← grid[1]
│ grid[1] ← first
│ ■ done
╵
",
    );

    // Example 5.6: returning the same field exclusively twice in one exit -> [L3].
    reject_rails(
        "L3",
        "
struct pair {left: [u32], right: [u32]}

control bad_halves(both: &~pair) ■ split {left: &~[u32] ∈ both, right: &~[u32] ∈ both}
│ ■ split {~both.left, ~both.left}
╵
",
    );

    // Example 5.9: two exclusive element borrows of one vector at once -> [L3] ([RM7]).
    reject_rails(
        "L3",
        "
control two_elems(grid: &~[u32]) ⊢ len(grid) ≥ 2 ■ done
│ a: &~u32 := ~grid[0]
│ b: &~u32 := ~grid[1]
│ a ← b
│ ■ done
╵
",
    );

    // Example 6.1: map lookup and clone.
    accept_rails(
        "ex6.1",
        "
control greeting(settings: &string ⇀ string) ■ text {value: string}
│ Δ settings.get(\"greeting\"): found {value} │ missing
╞═ found:   ■ text {clone(value)}
╞═ missing: ■ text {\"hello\"}
╵
",
    );

    // Example 6.2: keeping borrowed map `string` without cloning -> [O3].
    reject_rails(
        "O3",
        "
control bad_greeting(settings: &string ⇀ string) ■ text {value: string}
│ Δ settings.get(\"greeting\"): found {value} │ missing
╞═ found:   ■ text {value}
╞═ missing: ■ text {\"hello\"}
╵
",
    );

    // Example 6.3 & 6.4 (reordered): loan only on `get.found`; `insert` on `get.missing` allowed,
    // and `get.found` accepted when `value` is read before `insert`.
    accept_rails(
        "ex6.3-6.4-reordered",
        "
control touch(settings: &~string ⇀ string, key: &string) ■ kept {length: usize} │ added
│ Δ settings.get(key): found {value} │ missing
│
╞═ missing
│ ┆ Δ settings.insert(clone(key), \"\"): inserted │ replaced
│ ┆ ■ added
╞═ found
│ ┆ length: usize := len(value)
│ ┆ Δ settings.insert(clone(key), clone(value)): inserted │ replaced
│ ┆ ■ kept {length}
╵
",
    );

    // Example 6.4 (rejected): mutating map on `get.found` while `value` is used afterwards -> [L3].
    reject_rails(
        "L3",
        "
control bad_touch(settings: &~string ⇀ string, key: &string) ■ kept {length: usize} │ added
│ Δ settings.get(key): found {value} │ missing
│
╞═ missing
│ ┆ Δ settings.insert(clone(key), \"\"): inserted │ replaced
│ ┆ ■ added
╞═ found
│ ┆ Δ settings.insert(clone(key), clone(value)): inserted │ replaced
│ ┆ ■ kept {len(value)}
╵
",
    );

    // Examples 6.5 & 6.6: shared and exclusive borrowed variant decisions.
    accept_rails(
        "ex6.5-6.6",
        "
variant shape
├ circle {radius: u32}
└ rect {width: u32, height: u32}

control longest_side(figure: &shape) ■ side {length: u32}
│ Δ figure: circle {radius} → ■ side {radius} │ rect {width, height}
│ ? width ≥ height → ■ side {width}
│ ■ side {height}
╵

control make_square(figure: &~shape) ■ done
│ Δ ~figure: circle │ rect {width, height}
╞═ rect: height ← width
│ ■ done
╵
",
    );

    // Example 6.7: replacing variant while borrowed field `height` is still used -> [L3].
    reject_rails(
        "L3",
        "
variant shape
├ circle {radius: u32}
└ rect {width: u32, height: u32}

control bad_square(figure: &~shape) ■ done
│ Δ ~figure: circle │ rect {width, height}
╞═ rect
│ ┆ figure ← shape.circle {1}
│ ┆ height ← 0
│ ■ done
╵
",
    );

    // Example 6.8: returning a borrow of a local variable -> [L4].
    reject_rails(
        "L4",
        "
control first_or_default(words: &[string]) ■ pick {word: &string ∈ words}
│ fallback: string := \"none\"
│ ? len(words) = 0 → ■ pick {fallback}
│ ■ pick {words[0]}
╵
",
    );

    // Wrong `∈` parameter escape -> [L4].
    reject_rails(
        "L4",
        "
control wrong_origin(a: &string, b: &string) ■ pick {out: &string ∈ a}
│ ■ pick {b}
╵
",
    );

    // Conditional [L4] accepted when impossible branch has `⊥` vs rejected on feasible branch.
    accept_core(
        "cond-L4-ok",
        "
        control ok_cond(a : &string, b : &string, flag : bool)
            ■ { out {v : &string ∈ a} } :=
            1 ⊤ ▷ c : ? flag
            2 c.true  ▷ ■ out {a}
            3 c.false ▷ a2 : &string := a
            4 c.false ▷ ■ out {a2}
        ",
    );
    reject_core(
        "L4",
        "
        control bad_cond_l4(a : &string, flag : bool)
            ■ { out {v : &string ∈ a} } :=
            1 ⊤ ▷ local : string := \"x\"
            2 ⊤ ▷ c : ? flag
            3 c.true  ▷ ■ out {a}
            4 c.false ▷ ■ out {&local}
        ",
    );

    // Evaluation-order & assignment order checks (`[E-Formula]` / `[L3]` / non-lexical liveness):
    // `r + x` (RHS `x` after unused `r` -> OK) vs `x + r` (LHS `x` while `r` used in RHS -> L3).
    // `x ← r + 1` (value `r` evaluated before `x` written -> OK) vs `r ← r + x` (`r` live for LHS -> L3).
    accept_core(
        "eval-order-ok",
        "
        control order_ok() ■ { sum {v : u32} } :=
            1 ⊤ ▷ ~x : u32 := 10
            2 ⊤ ▷ r : &~u32 := &~x
            3 ⊤ ▷ a : u32 := r + x
            4 ⊤ ▷ s : &~u32 := &~x
            5 ⊤ ▷ x ← s + 1
            6 ⊤ ▷ ■ sum {a + x}
        ",
    );
    reject_core(
        "L3",
        "
        control x_plus_r() ■ { sum {v : u32} } :=
            1 ⊤ ▷ ~x : u32 := 10
            2 ⊤ ▷ r : &~u32 := &~x
            3 ⊤ ▷ ■ sum {x + r}
        ",
    );
    reject_core(
        "L3",
        "
        control r_assign_x() ■ { sum {v : u32} } :=
            1 ⊤ ▷ ~x : u32 := 10
            2 ⊤ ▷ r : &~u32 := &~x
            3 ⊤ ▷ r ← r + x
            4 ⊤ ▷ ■ sum {r}
        ",
    );

    // Passing `&~pair` whole while field `&pair.a` is still lent -> [L3].
    reject_core(
        "L3",
        "
        struct two {a : u32, b : u32}
        extern control take_both(p : &~two) ■ { done {} }

        control partial_then_whole() ■ { v {x : u32} } :=
            1 ⊤ ▷ ~p : two := two {1, 2}
            2 ⊤ ▷ fa : &u32 := &p.a
            3 ⊤ ▷ d : Δ take_both(&~p) ▸ done {}
            4 ⊤ ▷ ■ v {fa}
        ",
    );

    // `eval_loan_operands` `Temp` check: `value` is a `Var` holding a borrow of `m` (unused after
    // the call), evaluated in Pass 1 (`lends == false`) while `&~m` is evaluated in Pass 2 -> [L3].
    reject_core(
        "L3",
        "
        extern control use_mut_and_ref(m : &~[u32], val : &u32) ■ { done {} }

        control conflict_var_and_mut_borrow() ■ { done {} } :=
            1 ⊤ ▷ ~m : [u32] := [10, 20]
            2 ⊤ ▷ value : &u32 := &m[0]
            3 ⊤ ▷ d : Δ use_mut_and_ref(&~m, value) ▸ done {}
            4 ⊤ ▷ ■ done {}
        ",
    );
}

#[test]
fn references_loops_and_views_examples_7_to_10() {
    // Examples 7.1, 7.4, 7.5, 7.7: loop borrow state, index idiom, leaving with borrow, `∀`.
    accept_rails(
        "ex7.1-7.4-7.5-7.7",
        "
extern control emit(text: &string) ■ done
extern control starts_with(text: &string, prefix: &string) ■ yes │ no

control longest(words: &[string]) ⊢ len(words) > 0 ■ found {word: &string ∈ words}
│ ↻ scan(next: usize := 1, best: &string := words[0])
│ ║ ⊢ next ≤ len(words) ∧ next ≥ 1
│ ║ ? next = len(words) → ■ found {best}
│ ║ ? len(words[next]) > len(best) → ↑ scan(next + 1, words[next])
│ ║ ↑ scan(next + 1, best)
╵

control zero_smallest(values: &~[u32]) ⊢ len(values) > 0 ■ done
│ ↻ scan(next: usize := 1, low: usize := 0)
│ ║ ⊢ low < next ∧ next ≤ len(values) ∧ next ≥ 1
│ ║ ? next = len(values) →
│ ║ ┆ values[low] ← 0
│ ║ ┆ ■ done
│ ║ ? values[next] < values[low] → ↑ scan(next + 1, next)
│ ║ ↑ scan(next + 1, low)
╵

control report(words: &[string], prefix: &string) ■ done
│ ↻ scan(next: usize := 0)
│ ║ ⊢ next ≤ len(words)
│ ║ ? next = len(words) → □ none
│ ║ word: &string := words[next]
│ ║ Δ starts_with(word, prefix): yes → □ hit {word} │ no
│ ║ ↑ scan(next + 1)
│
╞═ hit:  emit(word)
╞═ none: emit(\"no word starts with it\")
│ ■ done
╵

control first_nonempty(words: &[string]) ■ found {word: &string ∈ words} │ missing
│ ∀ w ∈ words
│ ║ ? len(w) > 0 → □ found {word: w}
╞═ found: ■ found {word}
│ ■ missing
╵
",
    );

    // Example 7.2: carrying a borrow of an iteration-local string in `↑` -> [L3].
    reject_rails(
        "L3",
        "
control bad_longest(words: &[string]) ⊢ len(words) > 0 ■ found {word: &string ∈ words}
│ ↻ scan(next: usize := 1, best: &string := words[0])
│ ║ ⊢ next ≤ len(words) ∧ next ≥ 1
│ ║ ? next = len(words) → ■ found {best}
│ ║ copy: string := clone(words[next])
│ ║ ? len(copy) > len(best) → ↑ scan(next + 1, copy)
│ ║ ↑ scan(next + 1, best)
╵
",
    );

    // Example 7.3: exclusive element borrow carried across iterations -> [L3] ([L2a]).
    reject_rails(
        "L3",
        "
control bad_zero_smallest(values: &~[u32]) ⊢ len(values) > 0 ■ done
│ ↻ scan(next: usize := 1, low: &~u32 := ~values[0])
│ ║ ⊢ next ≤ len(values) ∧ next ≥ 1
│ ║ ? next = len(values) →
│ ║ ┆ low ← 0
│ ║ ┆ ■ done
│ ║ ? values[next] < low → ↑ scan(next + 1, ~values[next])
│ ║ ↑ scan(next + 1, ~low)
╵
",
    );

    // Example 7.6: leaving loop with borrow of iteration-local `copy` -> [L3].
    reject_rails(
        "L3",
        "
extern control emit(text: &string) ■ done
extern control starts_with(text: &string, prefix: &string) ■ yes │ no

control bad_report(words: &[string], prefix: &string) ■ done
│ ↻ scan(next: usize := 0)
│ ║ ⊢ next ≤ len(words)
│ ║ ? next = len(words) → □ none
│ ║ copy: string := clone(words[next])
│ ║ shown: &string := copy
│ ║ Δ starts_with(shown, prefix): yes → □ hit {word: shown} │ no
│ ║ ↑ scan(next + 1)
│
╞═ hit:  emit(word)
╞═ none: emit(\"no word starts with it\")
│ ■ done
╵
",
    );

    // Cross-iteration outer borrow invalidation: outer `r` used in loop BEFORE `push(&~v, 1)`,
    // which kills `r` for the next iteration -> [L3].
    reject_core(
        "L3",
        "
        control outer_borrow_invalidated_in_loop() ■ { out {s : u32} } :=
            1 ⊤ ▷ ~v : [u32] := [10]
            2 ⊤ ▷ r : &u32 := &v[0]
            3 ⊤ ▷ lp : ↻ lp(i : u32 := 0, acc : u32 := 0) {
                1 ⊤ ▷ c : ? i < 2
                2 c.false ▷ □ done {acc}
                3 ⊤ ▷ acc2 : u32 := r
                4 ⊤ ▷ p : Δ push(&~v, 1) ▸ done {}
                5 ⊤ ▷ ↑ lp(i + 1, acc2)
            } ▸ done {res}
            4 ⊤ ▷ ■ out {res}
        ",
    );

    // `↑` introduces a new loan on `b` while loop body mutates `b` -> [L3] (`seed_loop_again_loans`).
    reject_core(
        "L3",
        "
        control again_introduces_loan_on_b(n : u32) ■ { out {v : u32} } :=
            1 ⊤ ▷ ~a : u32 := 1
            2 ⊤ ▷ ~b : u32 := 2
            3 ⊤ ▷ lp : ↻ lp(i : u32 := 0, p : &~u32 := &~a) {
                ⊢ i ≤ n
                1 ⊤ ▷ c : ? i ≥ n
                2 c.true ▷ □ done {p}
                3 ⊤ ▷ b ← 10
                4 ⊤ ▷ _u : u32 := p
                5 ⊤ ▷ ↑ lp(i + 1, &~b)
            } ▸ done {res}
            4 ⊤ ▷ ■ out {res}
        ",
    );

    // Loop parameter `&~` reborrowed across iterations with `↑ go(&~r)` when disjoint from body writes.
    accept_core(
        "reborrow-loop-param",
        "
        control walk_reborrow(n : u32) ■ { out {v : u32} } :=
            1 ⊤ ▷ ~a : u32 := 1
            2 ⊤ ▷ lp : ↻ lp(i : u32 := 0, r : &~u32 := &~a) {
                ⊢ i ≤ n
                1 ⊤ ▷ c : ? i ≥ n
                2 c.true ▷ □ done {r}
                3 ⊤ ▷ r ← 10
                4 ⊤ ▷ ↑ lp(i + 1, &~r)
            } ▸ done {res}
            3 ⊤ ▷ ■ out {res}
        ",
    );

    // Examples 8.1, 8.2, 8.5 & 9: views (`window`, `tail`), chained view lookup `second_of`,
    // and one bind on each of two mutually exclusive paths.
    accept_rails(
        "ex8.1-8.2-8.5-ex9",
        "
extern control emit(text: &string) ■ done
pub view struct window {values: &[string], start: usize, end: usize}
pub view struct tail {values: &~[u32], from: usize}

function bounded(view: window): bool := view.start ≤ view.end ∧ view.end ≤ len(view.values)

pub control range(values: &[string], start: usize, end: usize)
    ■ ready {view: window ∈ values} ⇐ bounded(view)
    ■ invalid
│ ? start > end ∨ end > len(values) → ■ invalid
│ ■ ready {window {values, start, end}}
╵

pub control get_elem(view: window, offset: usize) ⊢ bounded(view)
    ■ found {value: &string ∈ view} │ finished
│ ? offset ≥ view.end - view.start → ■ finished
│ ■ found {view.values[view.start + offset]}
╵

control second_of(names: &[string]) ■ found {name: &string ∈ names} │ missing
│ Δ range(names, 1, len(names)): ready {rest} │ invalid → ■ missing
│ Δ get_elem(rest, 0): found {value} → ■ found {value} │ finished → ■ missing
╵

control clear(rest: tail) ⊢ rest.from ≤ len(rest.values) ■ done
│ ↻ each(next: usize := rest.from)
│ ║ ⊢ next ≤ len(rest.values)
│ ║ ? next = len(rest.values) → ■ done
│ ║ rest.values[next] ← 0
│ ║ ↑ each(next + 1)
╵

control wipe() ■ done
│ ~numbers: [u32] := [4, 5, 6]
│ ? len(numbers) ≥ 2 → clear(tail {~numbers, 2})
│ ■ done
╵

control two_path_bind(a: &string, b: &string) ■ done
│ Δ len(a) ≥ len(b): true → first │ false → second
╞═ first:  pick: &string := a
╞═ second: pick: &string := b
│ emit(pick)
│ ■ done
╵
",
    );

    // Example 8.3: reshaping vector with `push` while shared view `front` is used afterwards -> [L3].
    reject_rails(
        "L3",
        "
pub view struct window {values: &[string], start: usize, end: usize}
function bounded(view: window): bool := view.start ≤ view.end ∧ view.end ≤ len(view.values)

pub control range(values: &[string], start: usize, end: usize)
    ■ ready {view: window ∈ values} ⇐ bounded(view)
    ■ invalid
│ ? start > end ∨ end > len(values) → ■ invalid
│ ■ ready {window {values, start, end}}
╵

pub control get_elem(view: window, offset: usize) ⊢ bounded(view)
    ■ found {value: &string ∈ view} │ finished
│ ? offset ≥ view.end - view.start → ■ finished
│ ■ found {view.values[view.start + offset]}
╵

control grow() ■ done
│ ~names: [string] := [\"ash\", \"elm\", \"oak\"]
│ Δ range(names, 0, 2): ready {front} │ invalid → ■ done
│ names.push(\"yew\")
│ Δ get_elem(front, 0): found {value} │ finished
│ ■ done
╵
",
    );

    // Example 10 (section 10 tag trace): rejected at statement 5 (`t.count ← 0`) by [L3].
    let err_ex10 = reject_core(
        "L3",
        "
        struct tally {count : u64, note : string}

        control trace_ex10() ■ { done {} } :=
            1 ⊤ ▷ ~t : tally := tally {0, \"start\"}
            2 ⊤ ▷ slot : &~u64 := &~t.count
            3 ⊤ ▷ slot ← 7
            4 ⊤ ▷ t.note ← \"seen\"
            5 ⊤ ▷ t.count ← 0
            6 ⊤ ▷ slot ← 1
            7 ⊤ ▷ ■ done {}
        ",
    );
    assert_eq!(
        err_ex10.line, 9,
        "Example 10 must fail at statement 5 (`t.count ← 0`, line 9 of snippet)"
    );

    // Exclusive view partial-and-whole conflict: constructing view holding `&t.count` and `&~t`
    // (or `&~pair.left` and `&pair.left`) -> [L3].
    reject_core(
        "L3",
        "
        struct two {a : u32, b : u32}
        view struct bad_view {whole : &~two, part : &u32}

        control view_partial_whole() ■ { done {} } :=
            1 ⊤ ▷ ~t : two := two {1, 2}
            2 ⊤ ▷ v : bad_view := bad_view {&~t, &t.a}
            3 ⊤ ▷ ■ done {}
        ",
    );
}

#[test]
fn borrow_and_view_facts_i7_and_i9() {
    // [I7] local + multi-hop chained local borrow propagation across assignments.
    accept_core(
        "I7-chained",
        "
        struct tally {count : u64, note : string}

        control chained_i7() ■ { done {} } :=
            1 ⊤ ▷ ~t : tally := tally {0, \"start\"}
            2 ⊤ ▷ r1 : &~u64 := &~t.count
            3 ⊤ ▷ r2 : &~u64 := &~r1
            4 ⊤ ▷ r2 ← 7
            5 ⊤ ▷ ⊢ t.count = 7 ∧ t.note = \"start\"
            6 ⊤ ▷ ■ done {}
        ",
    );

    // [I9] write through exclusive payload borrow invalidates the caller's underlying root fact.
    reject_rails(
        "P1",
        "
struct pair {left: [u32], right: [u32]}

control halves(both: &~pair) ■ split {left: &~[u32] ∈ both, right: &~[u32] ∈ both}
│ ■ split {~both.left, ~both.right}
╵

control stale_after_payload_write() ■ done
│ ~p: pair := pair {[1, 2], [3]}
│ Δ halves(~p): split {left, right}
│ left.push(4)
│ ⊢ len(p.left) = 2
│ ■ done
╵
",
    );

    // [I9] exclusive view call invalidates underlying root fact when `view` holds `&~τ`.
    reject_rails(
        "P1",
        "
pub view struct tail {values: &~[u32], from: usize}

control clear(rest: tail) ⊢ rest.from ≤ len(rest.values) ■ done
│ ↻ each(next: usize := rest.from)
│ ║ ⊢ next ≤ len(rest.values)
│ ║ ? next = len(rest.values) → ■ done
│ ║ rest.values[next] ← 0
│ ║ ↑ each(next + 1)
╵

control stale_after_view_call() ■ done
│ ~numbers: [u32] := [4, 5, 6]
│ clear(tail {~numbers, 2})
│ ⊢ len(numbers) = 3
│ ■ done
╵
",
    );

    // [I9] loop body mutating outer root through a borrow/view renames outer root at loop entry.
    reject_rails(
        "P1",
        "
pub view struct tail {values: &~[u32], from: usize}

control clear(rest: tail) ⊢ rest.from ≤ len(rest.values) ■ done
│ ↻ each(next: usize := rest.from)
│ ║ ⊢ next ≤ len(rest.values)
│ ║ ? next = len(rest.values) → ■ done
│ ║ rest.values[next] ← 0
│ ║ ↑ each(next + 1)
╵

control stale_outer_in_loop() ■ done
│ ~numbers: [u32] := [4, 5, 6]
│ ↻ lp(k: u32 := 0)
│ ║ ⊢ k ≤ 2
│ ║ ? k ≥ 2 → □
│ ║ clear(tail {~numbers, 0})
│ ║ ↑ lp(k + 1)
│ ⊢ len(numbers) = 3
│ ■ done
╵
",
    );

    // [O3] moving non-copy out through `&` parameter (local bind and direct exit), plus `clone` ok.
    reject_core(
        "O3",
        "
        control bad_bind_deref(s : &string) ■ { out {res : string} } :=
            1 ⊤ ▷ res : string := s
            2 ⊤ ▷ ■ out {res}
        ",
    );
    reject_core(
        "O3",
        "
        control bad_exit_deref(s : &string) ■ { out {res : string} } :=
            1 ⊤ ▷ ■ out {s}
        ",
    );
    accept_core(
        "O3-clone-ok",
        "
        control good_clone_deref(s : &string) ■ { out {res : string} } :=
            1 ⊤ ▷ ■ out {clone(s)}
        ",
    );
}

#[test]
fn slice_three_surface_files_and_core_stuck_controls_conform() {
    // Both canonical Slice 3 `.rails` programs must pass `check::check` with kernel validation.
    let surface_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/slice3_surface");
    let mut surface_count = 0usize;
    let mut total_certs = 0usize;
    for entry in std::fs::read_dir(&surface_dir).expect("tests/slice3_surface") {
        let path = entry.expect("entry").path();
        if path.extension().is_some_and(|e| e == "rails") {
            let src = std::fs::read_to_string(&path).expect("readable");
            let report = accept_rails(&path.display().to_string(), &src);
            total_certs += report.certificates.len();
            surface_count += 1;
        }
    }
    assert_eq!(surface_count, 2);
    assert!(total_certs >= 100);

    // Helper to extract type headers + single control from `.core` files and verify each stuck
    // control individually.
    let borrows_core = std::fs::read_to_string(
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/slice3/borrows_and_tags.core"),
    )
    .unwrap();
    for (name, clause) in [
        ("stuck_write_kills_shared", "L3"),
        ("stuck_read_kills_exclusive", "L3"),
        ("stuck_parent_kills_reborrow", "L3"),
        ("stuck_move_kills_borrow", "L3"),
        ("stuck_dangling_return", "L4"),
        ("stuck_push_kills_elem_borrow", "L3"),
        ("stuck_remove_kills_map_borrow", "L3"),
        // Checker is intentionally stricter than the tag oracle on distinct vector indices ([RM7]).
        ("disjoint_elements", "L3"),
    ] {
        let mut snippet = extract_core_control(&borrows_core, &[], name);
        if name == "stuck_move_kills_borrow" {
            // [A3] bounds string lengths as non-negative rather than exact byte counts, so
            // rewrite `len(r) + len(moved)` to avoid Pass 1 `[P5]` overflow and reach Pass 2 `[L3]`.
            snippet = snippet.replace("len(r) + len(moved)", "len(r)");
        }
        if name == "disjoint_elements" {
            // [A3] tracks vector literal lengths rather than element values, so avoid Pass 1 `[P5]`
            // addition overflow on `r0 + 1`/`v[0] + v[1] + v[2]` and reach Pass 2 `[L3]` (`[RM7]`).
            snippet = snippet
                .replace("r0 + 1", "11")
                .replace("r1 + 2", "22")
                .replace("v[0] + v[1] + v[2]", "v[0]");
        }
        if name == "stuck_remove_kills_map_borrow" {
            // [A3] does not model map keys or bound recovered values, so replace `missing ▷ ⊥`
            // and `va + vb` with `■ ok {0}` / `va` to pass Pass 1 `[P5]`/`[P6]` and reach Pass 2
            // `[L3]` on `remove(&~m, "b")` while `va` stays live.
            snippet = snippet
                .replace("g1.missing ▷ ⊥", "g1.missing ▷ ■ ok {0}")
                .replace("r1.missing ▷ ⊥", "r1.missing ▷ ■ ok {0}")
                .replace("va + vb", "va");
        }
        reject_core(clause, &snippet);
    }

    let views_core = std::fs::read_to_string(
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/slice3/views_and_variants.core"),
    )
    .unwrap();
    let view_headers = [
        "view struct window {items : &[u32], start : usize, stop : usize}",
        "variant entry {value {text : string} │ empty {}}",
    ];
    for (name, clause) in [
        ("stuck_overwrite_variant", "L3"),
        ("stuck_dangling_view", "L4"),
    ] {
        let snippet = extract_core_control(&views_core, &view_headers, name);
        reject_core(clause, &snippet);
    }
}

fn extract_core_control(file_src: &str, headers: &[&str], control_name: &str) -> String {
    let mut out = headers.join("\n");
    if !out.is_empty() {
        out.push('\n');
    }
    let needle = format!("control {control_name}(");
    let mut capturing = false;
    for line in file_src.lines() {
        if line.starts_with(&needle) {
            capturing = true;
            out.push_str(line);
            out.push('\n');
            continue;
        }
        if capturing {
            if line.trim().is_empty()
                || line.starts_with("control ")
                || line.starts_with("//! ")
                || line.starts_with("// ")
            {
                break;
            }
            out.push_str(line);
            out.push('\n');
        }
    }
    assert!(
        capturing,
        "could not find control `{control_name}` in core file"
    );
    out
}

/// The program is stuck in the oracle, as its directive says, and the
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

/// Review finding RC1: a borrow bound in a loop body writes a name around
/// the loop, and the checker kept what it knew of the name before the loop
/// on every turn, because no loan of it was recorded when the loop was
/// entered. Each of these was accepted with validated certificates and is
/// stuck in the oracle: an assertion on a later turn, an overflow, an index
/// past the end, a write through a field of a view, the precondition of a
/// call through the borrow, and an assertion after the loop.
const RC1_STUCK: [(&str, &str); 6] = [
    (
        "P1",
        r#"
control c(n : u8) ■ { r {v : u8} }
⊤ ▷ ~x : u8 := 0
⊤ ▷ s : ↻ l(i : u8 := 0) {
    ⊢ i ≤ 10
    ⊤ ▷ ⊢ x = 0
    ⊤ ▷ t : ? i = 10
    t.true ▷ □ out
    ⊤ ▷ p : &~u8 := &~x
    ⊤ ▷ p ← 1
    ⊤ ▷ ↑ l(i + 1)
} ▸ out
⊤ ▷ ■ r {x}

//! run c(0) => stuck X7 E-Oblige
"#,
    ),
    (
        "P5",
        r#"
control c() ■ { r {v : u8} }
⊤ ▷ ~x : u8 := 0
⊤ ▷ s : ↻ l() {
    ⊤ ▷ p : &~u8 := &~x
    ⊤ ▷ p ← p + 1
    ⊤ ▷ ↑ l()
}

//! run c() => stuck X7 E-Arith
"#,
    ),
    (
        "P5",
        r#"
control c() ■ { r {v : u32} }
⊤ ▷ v : [u32] := [1, 2, 3]
⊤ ▷ ~i : usize := 0
⊤ ▷ s : ↻ l() {
    ⊤ ▷ e : u32 := v[i]
    ⊤ ▷ p : &~usize := &~i
    ⊤ ▷ p ← p + 1
    ⊤ ▷ ↑ l()
}

//! run c() => stuck X7 E-Index
"#,
    ),
    (
        "P5",
        r#"
view struct cell {slot : &~u8}
control c() ■ { r {v : u8} }
⊤ ▷ ~x : u8 := 0
⊤ ▷ s : ↻ l() {
    ⊤ ▷ w : cell := cell {&~x}
    ⊤ ▷ w.slot ← w.slot + 1
    ⊤ ▷ ↑ l()
}

//! run c() => stuck X7 E-Arith
"#,
    ),
    (
        "P3",
        r#"
control bump(x : &~u8) ⊢ x < 255 ■ { done {} ⇐ x = old(x) + 1 }
⊤ ▷ x ← x + 1
⊤ ▷ ■ done {}
control c() ■ { r {v : u8} }
⊤ ▷ ~x : u8 := 0
⊤ ▷ s : ↻ l() {
    ⊤ ▷ p : &~u8 := &~x
    ⊤ ▷ d : Δ bump(p) ▸ done {}
    ⊤ ▷ ↑ l()
}

//! run c() => stuck X7 E-Call
"#,
    ),
    (
        "P1",
        r#"
control c() ■ { r {v : u8} }
⊤ ▷ ~x : u8 := 0
⊤ ▷ s : ↻ l(i : u8 := 0) {
    ⊢ i ≤ 3
    ⊤ ▷ t : ? i = 3
    t.true ▷ □ out
    ⊤ ▷ p : &~u8 := &~x
    ⊤ ▷ p ← 9
    ⊤ ▷ ↑ l(i + 1)
} ▸ out
⊤ ▷ ⊢ x = 0
⊤ ▷ ■ r {x}

//! run c() => stuck X7 E-Oblige
"#,
    ),
];

/// The same loops, with an invariant that says what the borrow writes: the
/// name is renamed at the entry of the loop ([I9]: a place that the body
/// lends exclusively), the invariant gives the new name its value, and a
/// write through the local borrow name is an update of the place it
/// abbreviates ([I7]).
const RC1_DONE: [&str; 3] = [
    r#"
control c() ■ { r {v : u8} }
⊤ ▷ ~x : u8 := 0
⊤ ▷ s : ↻ l(i : u8 := 0) {
    ⊢ i ≤ 10 ∧ x = i
    ⊤ ▷ t : ? i = 10
    t.true ▷ □ out
    ⊤ ▷ p : &~u8 := &~x
    ⊤ ▷ p ← p + 1
    ⊤ ▷ ↑ l(i + 1)
} ▸ out
⊤ ▷ ⊢ x = 10
⊤ ▷ ■ r {x}

//! run c() => done r {10}
"#,
    r#"
control c() ■ { r {v : u32} }
⊤ ▷ v : [u32] := [1, 2, 3]
⊤ ▷ ~i : usize := 0
⊤ ▷ s : ↻ l() {
    ⊢ i ≤ 3
    ⊤ ▷ t : ? i = 3
    t.true ▷ □ out
    ⊤ ▷ e : u32 := v[i]
    ⊤ ▷ p : &~usize := &~i
    ⊤ ▷ p ← p + 1
    ⊤ ▷ ↑ l()
} ▸ out
⊤ ▷ ■ r {v[0]}

//! run c() => done r {1}
"#,
    r#"
control bump(x : &~u8) ⊢ x < 255 ■ { done {} ⇐ x = old(x) + 1 }
⊤ ▷ x ← x + 1
⊤ ▷ ■ done {}
control c() ■ { r {v : u8} }
⊤ ▷ ~x : u8 := 0
⊤ ▷ s : ↻ l(i : u8 := 0) {
    ⊢ i ≤ 10 ∧ x = i
    ⊤ ▷ t : ? i = 10
    t.true ▷ □ out
    ⊤ ▷ p : &~u8 := &~x
    ⊤ ▷ d : Δ bump(p) ▸ done {}
    ⊤ ▷ ↑ l(i + 1)
} ▸ out
⊤ ▷ ■ r {x}

//! run c() => done r {10}
"#,
];

#[test]
fn a_loop_renames_what_its_body_lends_exclusively_i9() {
    for (clause, source) in RC1_STUCK {
        stuck_and_rejected(clause, source);
    }
    for source in RC1_DONE {
        done_and_accepted("I9", source);
    }
}

/// The rule files of the borrows (`v2/tests/slice3/`), each with the runs
/// that apply its rule and the runs that are stuck by it.
const RULE_FILES: [&str; 8] = [
    "b1_access",
    "b2_invalidation",
    "b3_creation",
    "b4_moves_and_scopes",
    "b5_shapes",
    "e_borrow_operands",
    "e_extern_writes",
    "e_views",
];

/// The controls of the rule files that the checker refuses although no run
/// of them is stuck, with the clause and the reason: the loans go by places
/// and not by values ([RM7], [L2]), and the logic knows a place through a
/// local borrow name only ([I7]).
const ASKS_MORE: [(&str, &str, &str, &str); 4] = [
    (
        "b5_shapes",
        "element_beside_element",
        "L3",
        "[RM7]: all elements of one collection overlap, so `r[1]` is lent when `r[0]` is written",
    ),
    (
        "e_borrow_operands",
        "lends_two_places",
        "L3",
        "[RM7]: `xs[0]` and `xs[1]` overlap for the checker, which does not compare indices",
    ),
    (
        "e_views",
        "copy_field_beside_dead",
        "L3",
        "[L2]: a use of a view uses every borrow it holds, although `w.start` is a `copy` field",
    ),
    (
        "e_views",
        "moves_a_view",
        "P5",
        "[I7], [I9]: a write through a field of a view gives `xs` a fresh name with no fact, so its length is not known after it",
    ),
];

/// The runs that are stuck in a control that the checker accepts, because a
/// control further out broke the clause and the checker refuses that one:
/// the file, the control in which the run is stuck, the control that broke
/// the clause, the clause by which the checker refuses it, and how.
const STUCK_BY_ANOTHER: [(&str, &str, &str, &str, &str); 3] = [
    (
        "b1_access",
        "shows",
        "passes_dead",
        "L3",
        "`passes_dead` passes a borrow that its assignment ended, and `shows` reads through it",
    ),
    (
        "b4_moves_and_scopes",
        "reads_a_dead_payload",
        "lends_a_local",
        "L4",
        "`lends_a_local` returns a borrow of its own local, and the caller reads through it",
    ),
    (
        "e_borrow_operands",
        "copy_from",
        "lends_twice",
        "L3",
        "`lends_twice` reads `x` in the operand after `&~x`, and `copy_from` writes through the borrow that the read ended",
    ),
];

/// Whether a clause of the checker is the one that excludes a stuck state
/// of the oracle: a dead borrow by the loans ([L1] to [L5]), a name used
/// after it moved by [O2], an index out of range by [P5].
fn excludes(clause: &str, state: &str) -> bool {
    match state {
        "X4 B1" => clause.starts_with('L'),
        "X2 E-Var" => clause == "O2",
        "X7 E-Index" => clause == "P5",
        _ => false,
    }
}

/// Holds the checker against the oracle on files of the suite of slice 3,
/// control by control: a control in which a run is stuck must be rejected,
/// and any other must be accepted, apart from those of `asks_more`, which
/// the checker refuses by the clause named, and the pairs of
/// `stuck_by_another`. Gives the numbers of the controls rejected and
/// accepted.
fn held_against_the_oracle(
    files: &[&str],
    asks_more: &[(&str, &str, &str, &str)],
    stuck_by_another: &[(&str, &str, &str, &str, &str)],
) -> (usize, usize) {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/slice3");
    let mut failures = Vec::new();
    let mut rejected = 0;
    let mut accepted = 0;
    let mut asked_more = 0;
    let mut paired = 0;
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
            let stuck = report.stuck_in.get(&control);
            if let Some((_, _, _, clause, _)) = stuck_by_another
                .iter()
                .find(|(file, _, culprit, _, _)| file == name && *culprit == control)
            {
                // The control that broke the clause: no run is stuck in it,
                // and the checker refuses it.
                match (stuck, verdict) {
                    (None, Some(error)) if error.clause == *clause => paired += 1,
                    (_, verdict) => failures.push(format!(
                        "{name}: `{control}` is to be refused by [{clause}] with no run stuck in it: {verdict:?}, {stuck:?}"
                    )),
                }
                continue;
            }
            if stuck_by_another
                .iter()
                .any(|(file, in_control, _, _, _)| file == name && *in_control == control)
            {
                // The control in which the run is stuck keeps its contract.
                match (stuck, verdict) {
                    (Some(_), None) => paired += 1,
                    (_, verdict) => failures.push(format!(
                        "{name}: `{control}` is to be stuck and accepted: {verdict:?}, {stuck:?}"
                    )),
                }
                continue;
            }
            if let Some((_, _, clause, _)) = asks_more
                .iter()
                .find(|(file, asked, _, _)| file == name && *asked == control)
            {
                assert!(stuck.is_none(), "{name}: {control}");
                match verdict {
                    Some(error) if error.clause == *clause => asked_more += 1,
                    Some(error) => {
                        failures.push(format!("{name}: [{clause}] is expected, and {error}"))
                    }
                    None => failures.push(format!("{name}: `{control}` is accepted")),
                }
                continue;
            }
            match (stuck, verdict) {
                (Some(states), None) => failures.push(format!(
                    "{name}: `{control}` is accepted, and a run of it is stuck ({})",
                    states.iter().cloned().collect::<Vec<_>>().join(", ")
                )),
                (None, Some(error)) => {
                    failures.push(format!("{name}: `{control}`: no run is stuck, and {error}"))
                }
                (Some(states), Some(error)) => {
                    // The checker refuses the control by a clause that
                    // excludes the stuck state, and not by another.
                    if states.iter().any(|state| excludes(error.clause, state)) {
                        rejected += 1;
                    } else {
                        failures.push(format!(
                            "{name}: `{control}` is stuck ({}), and refused by another clause: {error}",
                            states.iter().cloned().collect::<Vec<_>>().join(", ")
                        ));
                    }
                }
                (None, None) => accepted += 1,
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    assert_eq!(asked_more, asks_more.len());
    assert_eq!(paired, 2 * stuck_by_another.len());
    (rejected, accepted)
}

/// Every control of the rule files of the borrows in which a run of the
/// oracle is stuck is rejected by the checker, and every other control is
/// accepted, apart from the four that ask more and the three pairs in which
/// a run is stuck in one control by what another did ([L1] to [L5], [O2],
/// [P1] to [P5], [I7], [I9]).
#[test]
fn the_rule_files_of_the_borrows_are_rejected_exactly_where_a_run_is_stuck() {
    let counts = held_against_the_oracle(&RULE_FILES, &ASKS_MORE, &STUCK_BY_ANOTHER);
    assert_eq!(counts, (39, 35));
}

/// Review finding RC27: an assignment through a name of exclusive borrow
/// type that a bind or an operation had moved was accepted, and is stuck in
/// the oracle (`X2 E-Var`). [E-Assign] reads the name as [E-Var] does, so
/// the checker asks [O2] of it. The bind with a move mark says the same.
const RC27_STUCK: [&str; 3] = [
    r#"
control c()
    ■ { ok {v : u32} }
    ⊤ ▷ ~x : u32 := 1
    ⊤ ▷ r : &~u32 := &~x
    ⊤ ▷ q : &~u32 := r
    ⊤ ▷ r ← 4
    ⊤ ▷ ■ ok {x}

//! run c() => stuck X2 E-Var
"#,
    r#"
control c()
    ■ { ok {v : u32} }
    ⊤ ▷ ~x : u32 := 1
    ⊤ ▷ r : &~u32 := &~x
    ⊤ ▷ q : &~u32 := ▾r
    ⊤ ▷ r ← 4
    ⊤ ▷ ■ ok {x}

//! run c() => stuck X2 E-Var
"#,
    r#"
control set(p : &~u32)
    ■ { done {} }
    ⊤ ▷ p ← 7
    ⊤ ▷ ■ done {}
control c()
    ■ { ok {v : u32} }
    ⊤ ▷ ~x : u32 := 1
    ⊤ ▷ r : &~u32 := &~x
    ⊤ ▷ d : Δ set(r) ▸ done {}
    ⊤ ▷ r ← 4
    ⊤ ▷ ■ ok {x}

//! run c() => stuck X2 E-Var
"#,
];

/// The new name writes, and an operand with the move mark passes the borrow
/// on as the bare name does: what the callee's condition says of it holds.
const RC27_DONE: &str = r#"
control set(p : &~u32)
    ■ { done {} ⇐ p = 7 }
    ⊤ ▷ p ← 7
    ⊤ ▷ ■ done {}
control c()
    ■ { ok {v : u32} }
    ⊤ ▷ ~x : u32 := 1
    ⊤ ▷ r : &~u32 := &~x
    ⊤ ▷ q : &~u32 := ▾r
    ⊤ ▷ q ← 4
    ⊤ ▷ s : &~u32 := &~x
    ⊤ ▷ d : Δ set(▾s) ▸ done {}
    ⊤ ▷ ⊢ x = 7
    ⊤ ▷ ■ ok {x}

//! run c() => done ok {7}
"#;

#[test]
fn a_borrow_name_that_moved_is_not_written_through_o2() {
    for source in RC27_STUCK {
        stuck_and_rejected("O2", source);
    }
    done_and_accepted("O2", RC27_DONE);
}

/// The loans of the checker, a clause at a time (`tests/slice3/l_loans.core`).
/// Each row: the rule, the control that the checker refuses and the clause by
/// which it does, the control in which a run is stuck, and beside it a
/// control that runs to its end and is accepted. The refused control is the
/// stuck one, but where a run is stuck in another control that keeps its
/// contract: in the callee that reads a borrow which the operands of its
/// call ended ([L2]), or in the caller that reads a borrow which its callee
/// returned ([L4]). Every other control of the file is a callee, accepted
/// with no run stuck.
const LOANS: [(&str, &str, &str, &str, &str); 28] = [
    (
        "L1",
        "bound_name_holds",
        "L3",
        "bound_name_holds",
        "bound_name_read_first",
    ),
    (
        "L1",
        "payload_holds",
        "L3",
        "payload_holds",
        "payload_written_first",
    ),
    (
        "L1",
        "decision_derives",
        "L3",
        "decision_derives",
        "decision_read_first",
    ),
    (
        "L1",
        "leave_payload_holds",
        "L3",
        "leave_payload_holds",
        "leave_payload_read_first",
    ),
    ("L1", "copy_holds", "L3", "copy_holds", "copy_read_first"),
    (
        "L1",
        "reborrow_inherits",
        "L3",
        "reborrow_inherits",
        "reborrow_beside_a_field",
    ),
    (
        "L2",
        "used_after_write",
        "L3",
        "used_after_write",
        "last_use_before_write",
    ),
    (
        "L2",
        "used_on_the_same_history",
        "L3",
        "used_on_the_same_history",
        "used_on_another_history",
    ),
    (
        "L2",
        "command_uses_operand",
        "L3",
        "both",
        "command_uses_another_place",
    ),
    (
        "L2",
        "later_operand_uses",
        "L3",
        "later_operand_uses",
        "earlier_operand_uses",
    ),
    (
        "L2",
        "formula_mentions",
        "L3",
        "formula_mentions",
        "formula_before_write",
    ),
    (
        "L2a",
        "parameter_goes_round",
        "L3",
        "parameter_goes_round",
        "parameter_goes_round_with_another",
    ),
    (
        "L2a",
        "parameter_goes_round",
        "L3",
        "parameter_goes_round",
        "borrow_bound_in_the_body",
    ),
    (
        "L2a",
        "round_with_a_local",
        "L3",
        "round_with_a_local",
        "round_with_an_outer_name",
    ),
    (
        "L3",
        "read_beside_exclusive",
        "L3",
        "read_beside_exclusive",
        "reads_beside_shared",
    ),
    (
        "L3",
        "exclusive_beside_shared",
        "L3",
        "exclusive_beside_shared",
        "exclusive_after_shared",
    ),
    (
        "L3",
        "move_beside_borrow",
        "L3",
        "move_beside_borrow",
        "move_after_last_use",
    ),
    (
        "L3",
        "push_beside_element",
        "L3",
        "push_beside_element",
        "push_after_last_use",
    ),
    ("L3", "same_field", "L3", "same_field", "other_field"),
    (
        "L3",
        "passes_exclusive_name",
        "L3",
        "passes_exclusive_name",
        "copies_shared_name",
    ),
    (
        "L4",
        "lends_a_local",
        "L4",
        "reads_a_local_payload",
        "reads_a_parameter_payload",
    ),
    (
        "L4",
        "pick_second",
        "L4",
        "reads_the_other_payload",
        "reads_the_named_payload",
    ),
    (
        "L4",
        "field_of_a_local",
        "L4",
        "reads_a_local_field",
        "reads_the_parameter_field",
    ),
    (
        "L4",
        "leaves_with_a_local",
        "L3",
        "leaves_with_a_local",
        "leaves_with_an_outer_name",
    ),
    ("L5", "view_holds", "L3", "view_holds", "view_written_first"),
    (
        "L5",
        "moved_view_holds",
        "L3",
        "moved_view_holds",
        "copied_shared_view",
    ),
    (
        "L5",
        "exclusive_field_read",
        "L3",
        "exclusive_field_read",
        "shared_field_read",
    ),
    (
        "L5",
        "move_ends_exclusive_field",
        "L3",
        "move_ends_exclusive_field",
        "move_keeps_shared_field",
    ),
];

#[test]
fn each_loan_rule_refuses_where_a_run_is_stuck_and_accepts_beside_it() {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/slice3/l_loans.core");
    let source = std::fs::read_to_string(path).unwrap();
    let report = villanelle_v2::script::check(&source);
    assert!(report.failures.is_empty(), "{}", report.failures.join("\n"));
    let program = load(&source).unwrap_or_else(|e| panic!("l_loans: {e}"));
    let verdicts: std::collections::BTreeMap<String, Option<check::Error>> =
        check::check_each(&program)
            .unwrap_or_else(|e| panic!("l_loans: {e}"))
            .into_iter()
            .collect();
    let accepted = |control: &str| matches!(verdicts.get(control), Some(None));
    let stuck = |control: &str| report.stuck_in.contains_key(control);
    let mut failures = Vec::new();
    let mut named = std::collections::BTreeSet::new();
    for (rule, refused, clause, stuck_in, done) in LOANS {
        match verdicts.get(refused) {
            Some(Some(error)) if error.clause == clause => {}
            other => failures.push(format!(
                "[{rule}] `{refused}` is to be refused by [{clause}]: {other:?}"
            )),
        }
        if !stuck(stuck_in) {
            failures.push(format!("[{rule}] no run of `{stuck_in}` is stuck"));
        }
        if refused != stuck_in && (!accepted(stuck_in) || stuck(refused)) {
            failures.push(format!(
                "[{rule}] `{stuck_in}` keeps the contract of `{refused}`, which broke [{clause}]"
            ));
        }
        if stuck(done) || !accepted(done) {
            failures.push(format!(
                "[{rule}] `{done}` is to run to its end and be accepted: {:?}",
                verdicts.get(done)
            ));
        }
        named.extend([refused, stuck_in, done]);
    }
    let mut callees = 0;
    for (control, verdict) in &verdicts {
        if named.contains(control.as_str()) {
            continue;
        }
        callees += 1;
        if verdict.is_some() || stuck(control) {
            failures.push(format!(
                "the callee `{control}` is refused or stuck: {verdict:?}"
            ));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    assert_eq!((named.len(), callees), (59, 6));
}

/// Review finding RC28: the arguments of a function applied in an operand
/// were checked as if the statement lent nothing, so a read of a name that
/// an earlier operand lends exclusively was accepted, and the run is stuck
/// when the callee writes through the borrow that the read ended ([L2]: the
/// command uses every borrow among the operands, and a later part of the
/// statement is an access while it is live). A function applied to another
/// name is no conflict.
const RC28_STUCK: &str = r#"
control two(a : &~u32, b : u32)
    ■ { done {} }
    ⊤ ▷ a ← b
    ⊤ ▷ ■ done {}

function id(v : u32) : u32 := v

control c()
    ■ { ok {v : u32} }
    ⊤ ▷ ~x : u32 := 1
    ⊤ ▷ r : &~u32 := &~x
    ⊤ ▷ d : Δ two(r, id(x)) ▸ done {}
    ⊤ ▷ ■ ok {x}

//! run c() => stuck X4 B1
"#;

const RC28_DONE: &str = r#"
control two(a : &~u32, b : u32)
    ■ { done {} }
    ⊤ ▷ a ← b
    ⊤ ▷ ■ done {}

function id(v : u32) : u32 := v

control c()
    ■ { ok {v : u32} }
    ⊤ ▷ ~x : u32 := 1
    ⊤ ▷ y : u32 := 2
    ⊤ ▷ r : &~u32 := &~x
    ⊤ ▷ d : Δ two(r, id(y)) ▸ done {}
    ⊤ ▷ ■ ok {x}

//! run c() => done ok {2}
"#;

#[test]
fn a_function_in_an_operand_reads_while_the_statement_lends_l2() {
    stuck_and_rejected("L3", RC28_STUCK);
    done_and_accepted("L2", RC28_DONE);
}

/// Review finding RC29: a borrow made in the operand of `len` counted as used
/// by the command of the statement, so the end of the scope at an exit or a
/// leave conflicted with it, and each of these was refused by [L3] although
/// every run ends. `len` uses the borrow where it is applied, and its value
/// carries none ([L2]).
const RC29_DONE: &str = r#"
control len_at_exit()
    ■ { ok {n : usize} }
    ⊤ ▷ v : [u32] := [1, 2]
    ⊤ ▷ ■ ok {len(&v)}

control len_then_move()
    ■ { ok {n : usize, w : [u32]} }
    ⊤ ▷ v : [u32] := [1, 2]
    ⊤ ▷ ■ ok {len(&v), ▾v}

control len_in_a_loop_payload()
    ■ { ok {n : usize} }
    ⊤ ▷ l : ↻ l() {
        ⊤ ▷ v : [u32] := [1, 2, 3]
        ⊤ ▷ □ out {len(&v)}
    } ▸ out {m}
    ⊤ ▷ ■ ok {m}

//! run len_at_exit() => done ok {2}
//! run len_then_move() => done ok {2, [1, 2]}
//! run len_in_a_loop_payload() => done ok {3}
"#;

#[test]
fn a_borrow_in_the_operand_of_len_is_not_used_after_it_l2() {
    done_and_accepted("L2", RC29_DONE);
}

/// Review finding RC30: at `recover ↑ ℓ` the checker took a name bound in a
/// body within the restarted loop, a boundary around the one that recovers,
/// as live after the restart, so a borrow that the payload of a decision
/// there holds was in use when the scope of what it borrows ended, and the
/// program was refused by [L3] although every run ends. The next iteration
/// binds such a name anew ([L2a]), as the head of the loop already said. A
/// borrow that goes on into the next iteration through a parameter of the
/// loop does outlive the scope of what it borrows, and is refused.
const RC30_DONE: &str = r#"
extern control e0(p0 : &[u32])
    ■ { high {r1 : &u32 ∈ p0} }

control nested() ■ { stop {} }
    ⊤ ▷ s3 : ↻ l4(~i5 : u16 := 0) {
        ⊤ ▷ t7 : ? i5 < 3
        t7.true ▷ i5 ← i5 + 1
        t7.true ▷ b28 : boundary {
            ⊤ ▷ h1 : [u32] := [1, 2]
            ⊤ ▷ d9 : Δ e0(&h1) ▸ high {v15}
            ⊤ ▷ b21 : boundary {
                ⊤ ▷ v16 : u32 := v15
                ⊤ ▷ fault "bad input"
            } contingency (m22 : string) {
                ⊤ ▷ recover ↑ l4
            }
            b21.done ▷ ⊥
            ⊤ ▷ □ stop {}
        } contingency (m29 : string) {
            ⊤ ▷ ⊥
        }
        t7.true ∧ b28.done ▷ ⊥
        t7.false ▷ □ stop {}
} ▸ stop {}
    ⊤ ▷ ■ stop {}

//! run nested() with [e0 -> high {&p0[1]}; e0 -> high {&p0[1]}; e0 -> high {&p0[1]}] => done stop {}
"#;

const RC30_STUCK: &str = r#"
extern control e0(p0 : &[u32])
    ■ { high {r1 : &u32 ∈ p0} }

control carried() ■ { stop {v : u32} }
    ⊤ ▷ g : u32 := 7
    ⊤ ▷ s3 : ↻ l4(i5 : u16 := 0, x : &u32 := &g) {
        ⊢ i5 ≤ 3
        ⊤ ▷ y : u32 := x
        ⊤ ▷ t7 : ? i5 < 3
        t7.false ▷ □ stop {y}
        t7.true ▷ b28 : boundary {
            ⊤ ▷ h1 : [u32] := [1, 2]
            ⊤ ▷ d9 : Δ e0(&h1) ▸ high {v15}
            ⊤ ▷ ↑ l4(i5 + 1, v15)
        } contingency (m29 : string) {
            ⊤ ▷ ⊥
        }
        t7.true ▷ ⊥
} ▸ stop {w}
    ⊤ ▷ ■ stop {w}

//! run carried() with [e0 -> high {&p0[1]}] => stuck X4 B1
"#;

#[test]
fn a_name_bound_within_the_restarted_loop_is_not_live_after_recover_l2a() {
    done_and_accepted("L2a", RC30_DONE);
    stuck_and_rejected("L3", RC30_STUCK);
}

/// A program for the kinds of mutation of the borrows. Each control runs to
/// its end and is accepted; `put` moves the exclusive borrow it is given.
const BORROWING: &str = r#"
struct pair {a : u32, b : u32}

control flips(n : u32)
    ■ { ok {v : u32} }
    ⊤ ▷ ~x : u32 := n
    ⊤ ▷ r : &u32 := &x
    ⊤ ▷ s : &u32 := &x
    ⊤ ▷ a : u32 := r
    ⊤ ▷ b : u32 := s
    ⊤ ▷ ■ ok {a}

control extends(n : u32)
    ■ { ok {v : u32} }
    ⊤ ▷ ~x : u32 := n
    ⊤ ▷ r : &u32 := &x
    ⊤ ▷ a : u32 := r
    ⊤ ▷ x ← 2
    ⊤ ▷ ■ ok {a}

control reads_lent(n : u32)
    ■ { ok {v : u32} }
    ⊤ ▷ ~y : u32 := n
    ⊤ ▷ w : &~u32 := &~y
    ⊤ ▷ w ← 3
    ⊤ ▷ ■ ok {y}

control put(c : &~u32)
    ■ { ok {} }
    ⊤ ▷ c ← 7
    ⊤ ▷ ■ ok {}

control moves_borrow(n : u32)
    ■ { ok {v : u32} }
    ⊤ ▷ ~y : u32 := n
    ⊤ ▷ w : &~u32 := &~y
    ⊤ ▷ d : Δ put(▾w) ▸ ok {}
    ⊤ ▷ ■ ok {y}

control moves_lent(t : string)
    ■ { ok {v : string} }
    ⊤ ▷ r : &string := &t
    ⊤ ▷ u : string := clone(r)
    ⊤ ▷ ■ ok {u}

control first_of(p : &pair)
    ■ { got {r : &u32 ∈ p} }
    ⊤ ▷ ■ got {&p.a}

control payloads(n : u32)
    ■ { ok {v : u32} }
    ⊤ ▷ ~q : pair := pair {n, 1}
    ⊤ ▷ d : Δ first_of(&q) ▸ got {r}
    ⊤ ▷ a : u32 := r
    ⊤ ▷ ■ ok {a}
"#;

/// The runs of [`BORROWING`], one for each control that is an entry.
fn borrowing_runs() -> Vec<(String, Vec<villanelle_v2::oracle::Value>)> {
    use villanelle_v2::int::Int;
    use villanelle_v2::oracle::Value;
    let number = |n: u64| vec![Value::Int(Int::from_u64(n))];
    vec![
        ("flips".to_string(), number(5)),
        ("extends".to_string(), number(5)),
        ("reads_lent".to_string(), number(5)),
        ("moves_borrow".to_string(), number(5)),
        (
            "moves_lent".to_string(),
            vec![Value::String("text".to_string())],
        ),
        ("payloads".to_string(), number(5)),
    ]
}

/// The kinds of mutation that slice 3 adds seed a use of a borrow after it
/// ended: each has a mutant of [`BORROWING`] that is stuck in the oracle by a
/// dead borrow (X4 B1), or by a borrow name that moved (X2 E-Var), in the
/// controls where the kind meets a conflict, and the checker rejects every
/// mutant that is stuck. The program itself runs to its ends and is
/// accepted.
#[test]
fn mutations_of_borrows_are_stuck_and_rejected() {
    use std::collections::{BTreeMap, BTreeSet};
    use villanelle_v2::mutate::{self, Class, Kind};
    use villanelle_v2::oracle::Config;

    let tree = villanelle_v2::text::parse(BORROWING).expect("the program reads");
    accept_core("B1", BORROWING);
    let config = Config::default();
    let runs = borrowing_runs();
    let whole = mutate::Mutant {
        kind: Kind::FlipBorrow,
        control: String::new(),
        detail: String::new(),
        program: tree.clone(),
    };
    assert!(
        matches!(mutate::classify(&whole, &runs, 1, &config), Class::Unstuck),
        "a run of the program is stuck"
    );

    let mut stuck: BTreeMap<Kind, BTreeSet<String>> = BTreeMap::new();
    let mut made: BTreeMap<Kind, usize> = BTreeMap::new();
    for mutant in mutate::mutate(&tree) {
        *made.entry(mutant.kind).or_default() += 1;
        let Class::Stuck(state) = mutate::classify(&mutant, &runs, 1, &config) else {
            continue;
        };
        stuck.entry(mutant.kind).or_default().insert(format!(
            "{} X{} {}",
            mutant.control, state.state, state.clause
        ));
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
    // Six borrows bound to names and one payload name that borrows within
    // `q`, each mentioned once after; eleven places after a later statement
    // that is no last disposition.
    let kinds = [
        Kind::FlipBorrow,
        Kind::ConflictingBorrow,
        Kind::AccessLent,
        Kind::ExtendBorrow,
    ];
    let counts: Vec<usize> = kinds.iter().map(|kind| made[kind]).collect();
    assert_eq!(counts, [6, 7, 7, 11], "{made:?}");
    // Flipped: `&~x` ends the borrow of `x` that `r` holds in `flips`; the
    // others write through a shared borrow, pass one for an exclusive one,
    // or borrow a parameter exclusively, and are refused. Conflicting:
    // `&~x` ends `r` or `s`, `&y` ends `w` (in `moves_borrow` the run is
    // stuck in `put`, which writes through it), and `&~q` ends the payload
    // name `r` that borrows within `q`. Accessed: `y` is read while `w`
    // holds it, and `t` and `q` move while `r` borrows them; a read of `x`
    // while `r` and `s` share it ends neither. Extended: `r` after `x ← 2`,
    // and `w` after `put` took it.
    assert_eq!(states(Kind::FlipBorrow), ["flips X4 B1"], "{stuck:?}");
    assert_eq!(
        states(Kind::ConflictingBorrow),
        [
            "extends X4 B1",
            "flips X4 B1",
            "moves_borrow X4 B1",
            "payloads X4 B1",
            "reads_lent X4 B1"
        ],
        "{stuck:?}"
    );
    assert_eq!(
        states(Kind::AccessLent),
        [
            "moves_borrow X4 B1",
            "moves_lent X4 B1",
            "payloads X4 B1",
            "reads_lent X4 B1"
        ],
        "{stuck:?}"
    );
    assert_eq!(
        states(Kind::ExtendBorrow),
        ["extends X4 B1", "moves_borrow X2 E-Var"],
        "{stuck:?}"
    );
}

/// [I9], RC33. Each write in one invocation updates the record left by the
/// preceding write. Its other fields keep their facts.
#[test]
fn exclusive_call_operands_update_the_same_record_rc33() {
    let direct = r#"
control update(one : &~u32, two : &~u32) ■ { done {} }
    ⊤ ▷ one ← 8
    ⊤ ▷ two ← 9
    ⊤ ▷ ■ done {}"#;
    let view = r#"
view struct slots {one : &~u32, two : &~u32}
control update(s : slots) ■ { done {} }
    ⊤ ▷ s.one ← 8
    ⊤ ▷ s.two ← 9
    ⊤ ▷ ■ done {}"#;
    for (callee, setup, args) in [
        (direct, "", "&~t.a, &~t.b"),
        (view, "", "slots {&~t.a, &~t.b}"),
        (
            direct,
            "⊤ ▷ a : &~u32 := &~t.a\n    ⊤ ▷ b : &~u32 := &~t.b",
            "a, b",
        ),
    ] {
        for (field, value, expected) in [
            ("a", 1, "stuck X7 E-Oblige"),
            ("b", 2, "stuck X7 E-Oblige"),
            ("c", 3, "done ok"),
        ] {
            let source = format!(
                r#"
struct triple {{a : u32, b : u32, c : u32}}
{callee}

control start() ■ {{ ok {{}} }}
    ⊤ ▷ ~t : triple := triple {{1, 2, 3}}
    {setup}
    ⊤ ▷ d : Δ update({args}) ▸ done {{}}
    d.done ▷ ⊢ t.{field} = {value}
    d.done ▷ ■ ok {{}}

//! run start() => {expected}
"#
            );
            if field == "c" {
                done_and_accepted("I9", &source);
            } else {
                stuck_and_rejected("P1", &source);
            }
        }
    }
}

/// [I12] records a post-call term for each exclusive operand. A decision
/// on a captured value must relate both terms to the caller's fields.
#[test]
fn a_capture_keeps_both_exclusive_postconditions_rc33() {
    for (fact, expected) in [
        ("t.a = 8 ∧ t.b = 9 ∧ t.c = 3", "done ok"),
        ("t.a = 1", "stuck X7 E-Oblige"),
    ] {
        let source = format!(
            r#"
struct triple {{a : u32, b : u32, c : u32}}

control update(one : &~u32, two : &~u32) ⊢ one = 1 ∧ two = 2
    ■ {{ done {{}} ⇐ one = old(two) + 6 ∧ two = old(one) + 8 }}
    ⊤ ▷ one ← 8
    ⊤ ▷ two ← 9
    ⊤ ▷ ■ done {{}}

control start() ■ {{ ok {{}} }}
    ⊤ ▷ ~t : triple := triple {{1, 2, 3}}
    ⊤ ▷ result := capture update(&~t.a, &~t.b)
    ⊤ ▷ d : Δ outcome(▾result) ▸ done {{}}
    d.done ▷ ⊢ {fact}
    d.done ▷ ■ ok {{}}

//! run start() => {expected}
"#
        );
        if expected == "done ok" {
            done_and_accepted("I12", &source);
        } else {
            stuck_and_rejected("P1", &source);
        }
    }
}
