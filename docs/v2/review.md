# Review of the v2 implementation of 21 and 22 November 2026

Status: **open**, 23 November 2026. This is the record of what the v2 crate
is verified to do and what it is not. It governs the status statements of the
[index](README.md), of [`oracle.md`](oracle.md) and of the repository's
`README.md`: where one of them says more than this document, this document is
right.

[Index of the v2 design](README.md) · [Oracle and crate](oracle.md) ·
[Core calculus](core.md) · [Fact logic](facts.md) · [Surface](surface.md) ·
[Plan](../redesign-plan.md)

## 1. What was reviewed, and how

The implementation of 21 and 22 November is commits `eb4a6b6` to `17423c9`:
13 commits and 54,802 added lines in two days. It took the crate from the
oracle of slice 1 to an erased interpreter, a generator, mutations, the Rails
reader and formatter, a checker with fact logic and kernel, call expansion and
an LLVM backend for slices 1 to 3, and an oracle for slice 4. Its documents
called slices 1 to 3 complete through phases 2, 3 and 4.

The review was made on 23 November at the author's request. Four reviewers
worked independently, one each on the checker, the backend and expansion, the
oracle and erased interpreter of slices 2 to 4, and the Rails reader. Each was
asked to break its part with small programs and to keep every program. Two
further probes ran the generator and its mutants through the oracle and the
checker, and ran the checker over every control of the conformance suite that
has a stuck run. At least one finding of each reviewer was reproduced by hand;
those are marked **(reproduced)**.

The 561 probe programs are kept outside the repository. A finding is closed
when it is fixed and a test for it is in `v2/tests/`; section 9 records that.
Line numbers refer to `17423c9`.

## 2. Verdict

The code is real and much of it works. It is not verified to the standard
that the plan and the checkpoint rule set, and no slice meets its exit:

- What looked like fuzzing is one fixed program (section 4).
- The checker accepts programs of slices 2 and 3 that are stuck in the
  oracle, and its kernel does not check what the fact logic requires of it
  (section 5).
- The oracle is wrong for fault boundaries, and the erased interpreter
  repeats its structure (section 6).
- The backend emits a double free for checked programs (section 7).
- The reader reads 1 of the 17 corpus files, and the formatter deletes
  comments (section 8).

The code stays. It is requalified slice by slice (section 10).

## 3. What each slice still owes

The plan builds phases 2 to 4 as vertical slices, and a slice passes
specification, oracle, checker, backend and differential fuzzing before the
next begins. The exits are those of the [plan](../redesign-plan.md), phases 2
to 4. The checkpoint rule asks for a test that accepts and a test that rejects
for every clause implemented.

| Requirement | 1. Scalars and decisions | 2. Data | 3. Borrows | 4. Tasks |
| --- | --- | --- | --- | --- |
| Oracle: accepting and rejecting test for each clause | Met: 41 files, 126 runs, 12 rules, 15 stuck states, 9 refusals | Met since 24 November: 100 files, 358 runs, 20 rules, 18 stuck labels, 15 clauses of refusal. Requalified since 23 November: the fault-boundary rules (RO1, RO3, RO4), pure operations (RO8), the operands and contracts of the built-in operations (RO9, RO10), and on 24 November the rules of the data: a file for each rule with the runs that apply it and the runs that are stuck by it, the order of release under a fault (RO12), and 38 refusals of the reader. Open: an outcome type that names a control is refused in a declaration (RO13) | Met since 24 November: 25 files, 216 runs, 13 rules, 3 stuck labels, refusals by [C1]. A file for each rule of the borrows ([B1] to [B5], the operands that lend, views, and the loans of the checker), with the runs that apply it and the runs that are stuck by it; a run stuck by a dead borrow says what ended it, and the test holds the cause of each of the 67 (an assignment, a read, a borrow made, a move, a change of shape, the end of a scope, a write of the host). The reader asks for `&p` where a borrow type is expected (RO14); a formula reads through a live borrow only (RO15); a function makes no borrow of its argument (RO16); passing a borrow is no access (RO17); a host writes behind an argument lent exclusively, and the write ends the borrows made through it (RO11). Since 24 November compiled code runs such hosts as the oracle does (RO6, RO11) | Met since 24 November: 11 files, 95 runs (72 compared with the erased semantics), 11 rules, 10 stuck labels, and 23 refusals of [W10] to [W12] and [TK1]. A file for each rule of the tasks ([E-Run] to [E-Stop], and [E-Exhaust]) with the runs that apply it and the runs stuck by it, and each stuck run is stuck in the control and the state the test lists. The rules answer RT1 to RT4 since that day, and the oracle holds RT1 to RT3: a run of an extern control is a run whose root waits for the operation and can be withdrawn, the operation that an owner awaits is withdrawn when the fault of a member reaches it, and a step that would pass the capacity ends the execution `exhausted`. The host of the instrumented profile cancels the root of the innermost run only |
| Checker: accepting and rejecting test for each clause | Met | Partly. The findings of the review in this slice are closed since 23 November (RC2 to RC8, RC20, RC21, RC23, RC24), with tests that run each program in the oracle as well; since 24 November the checker is held against the oracle on the rule files of the data, control by control: of their 124 controls it refuses the 62 in which a run is stuck and accepts 59, and the other three are refused by a clause that goes by the type of a name or by the allowance of a caller where no run is stuck. The instances of [A3] to [A6] are held against real values since 24 November: every instance that the search makes for terms over values of the oracle is true, a wrong value makes the instance of its axiom false, and each axiom is a statement of a program that the checker proves beside one that a run finds false and the checker refuses (49 controls: 21 refused, 23 proved, and five that are true and not proved, three of them RC26). Open: RC26. The shapes that the generator writes since 24 November (a boundary in the work of another, `recover ↑ ℓ` of a loop further out) have six programs that are stuck and rejected and six controls that are accepted and compiled | Partly: the worked examples of the reference model. Since 24 November a loop renames every place its body lends exclusively, so a borrow bound in the body no longer leaves the facts of the name it writes in place (RC1: six programs stuck and refused, three accepted), and the checker is held against the rule files of the borrows, control by control: of their 84 controls it refuses the 39 in which a run is stuck, each by the clause that excludes the stuck state (a loan for a dead borrow, [O2] for a moved name, [P5] for an index), and accepts 35. Four are refused where no run is stuck, by rules that go by places ([RM7]: elements overlap; [L2]: a use of a view uses each of its borrows) or because a write through a field of a view leaves its root with no fact ([I7], [I9]); in three pairs a run is stuck in a control that keeps its contract, by what a caller or a callee did, and the checker refuses that one. Found and closed on the way: RC27 (an assignment through a moved borrow name was accepted). Since 24 November the loans have a test for each clause (`v2/tests/slice3/l_loans.core`, 65 controls): 28 rows of [L1] to [L5], each a control in which a run is stuck and the checker refuses the control that broke the rule, by [L3] or [L4], beside one that runs to its end and is accepted; a test with two rules of the loans taken out fails on six rows. Found and closed there: RC28 (a function in an operand hid a read of a name that the statement lends; accepted and stuck) and RC29 (`■ ok {len(&v)}` was refused), and [L5] of the core says what the checker does, that a use of a view uses each field in its own mode. Since 24 November the checker accepts every generated program with borrows of the campaigns below; found and closed there: RC30 (a name bound within the loop that `recover ↑ ℓ` restarts was live after it, and a valid program was refused). It rejects every mutant of them that a run finds stuck (the row of mutations below). RC33 closed on 25 November. An ordinary call updates both exclusively lent fields of one record and preserves its untouched fields (section 5) | Met for the task clauses. The checker and oracle are held against all 160 controls in the 11 task rule files. Eighteen controls are refused where a run gets stuck and 134 are accepted. In four further pairs a run gets stuck in one control and the checker refuses the control that broke its contract. The clause tests in `v2/tests/checker_slice4.rs` exercise preconditions at spawn, await and run, set ownership ([O2], [O5]), stopping permissions ([TK4]), member faults ([F1]), effects ([F3]), coverage of `empty` ([C2]) and task-set loans ([TK3], [L3]). The first checker checkpoint caught 18 deliberate mutations and the TK3 tests caught six more. RC31 closed on 25 November. RC32 remains a question for the author about the rule for awaited extern payloads. Ordinary calls use the same cumulative field updates as spawns (RC33) |
| Generator reaches every construct of the slice (phase 2 exit) | Met since 23 November (section 9, RG1) | Met since 23 November for the constructs: `generate::valid_data` (`vn2 fuzz --slice 2`) writes the data of the slice and the operations on it, resources with the obligations they bring, captured outcomes, faults, and lexical and named boundaries, valid by construction as slice 1 is, and reaches all 56 constructs that `generate::DATA_CONSTRUCTS` lists, beside the 61 of slice 1. Since 24 November it writes the three shapes that were missing. Of the first 300 programs, 105 have a boundary in the work of another, 63 a `recover ↑ ℓ` and 19 one of a loop further out than the body the boundary stands in; 148 have an operation with a parameter of an outcome type and 130 one with such a payload field (RG7) | Met since 24 November for the constructs: `generate::valid_borrows` (`vn2 fuzz --slice 3`) is the generator of slice 2 with the borrows, valid by construction: for each name on each history it keeps the loans the name holds, a statement does not use what a live loan lends against its mode, and a borrow ends where the generator stops mentioning every name that holds it ([L2]). It writes borrows of names, fields and elements, borrows through borrow names, copies and moves of them, writes through them, borrow names and borrows of them as operands, controls with borrowed parameters, and extern controls whose payloads borrow places within their arguments; the seeded hosts write behind the arguments lent exclusively and lend every kind of place. It reaches all 20 constructs that `generate::BORROW_CONSTRUCTS` lists, beside those of slices 1 and 2, and the hosts lend every kind of place, in 300 programs (`generated_programs_with_borrows_run_to_an_end_and_reach_the_borrow_constructs`, `v2/tests/harness.rs`; the checker accepts 31 of them in `the_checker_accepts_generated_programs_with_borrows`). Over 900 programs the hosts lent 8,691 whole arguments, 758 fields, 42 fields of variants, 731 elements, 23 values and 38 keys of maps. Found on the way: RG8 (a defect of the generator of slice 2) and RC30 | No generator |
| Oracle against erased semantics | 62 runs of the suite and 11,728 runs of 300 generated programs | The erased interpreter is a transcription of the oracle (RO7). Since 23 November it releases under a fault as the oracle does where one task runs (RO5; the part with tasks is open for slice 4), also after a boundary or a loop that did not run (RB12). 36,348 runs of 900 generated programs with data, resources, captured outcomes, faults and boundaries give the same observation; 3,732 of them end in a fault that leaves the entry and 1,338 with `terminate n` | As slice 2. Since 24 November 36,396 runs of 900 generated programs with borrows, with hosts that lend from their arguments and write behind them, give the same observation; 3,590 of them end in a fault and 1,076 with `terminate n` | Since 24 November the erased semantics releases as the oracle does where a task is stopped, or the fault of a member arrives, while the task is ready (RO5); the 72 compared runs of the 11 rule files give the same observation. The six defined-root runs and six runs covering defined awaits added on 25 November also agree. No generated programs with tasks |
| Mutations rejected at the rate the author sets (phase 3 exit) | Seven kinds on generated programs since 23 November, and with those of slice 2 nine that apply since 24 November. Every mutant for which a stuck run was found is rejected: 769 of 6,851 mutants of 25 programs (761 of 5,403 with the seven kinds), and 72 in the suite. The checker accepts 4,951 for which none was found. The rate is not set | Twelve kinds since 24 November: the seven of slice 1, in the bodies of boundaries too, and a statement removed, two statements in each other's place, a clone consumed, `faults` removed and `on fault release` removed. Every mutant for which a stuck run was found is rejected: 1,460 of 13,176 mutants of 40 generated programs; `resolve` refuses 1,675, and the checker accepts 9,413 for which none was found (21 of the mutants are of the kinds of slice 3, since 24 November: a payload of `get` borrowed after a later statement; none is stuck), and gives an answer in ten seconds on every one (since 24 November, when the programs began to bind a value that an operand lends to a name first, RO14; before, 1,454 of 13,073). A program written for the five kinds has a stuck mutant of each, in the states X1, X2, X5 and X8. The rate is not set | Sixteen kinds since 24 November: the twelve of slice 2 and four for the borrows, each aimed at a borrow that a run uses after it ended: a borrow made in the other mode, with the type of the name it is bound to; a borrow of the same place in the other mode, or an access of its root, before a statement that mentions the name that holds it; and a borrow of a name of borrow type after a later statement. Every mutant for which a stuck run was found is rejected: 1,261 of 11,088 mutants of 40 generated programs; `resolve` refuses 1,408, and the checker accepts 7,948 for which none was found, and gives an answer in ten seconds on every one. The four kinds make 508 of them and only 20 with a stuck run: the generated programs give them few conflicts, since most of their borrows are of names that nothing writes or moves afterwards (19 of the 83 borrows bound to names are mentioned after the statement that binds them). A program written for the four kinds has a stuck mutant of each in the controls where the kind meets a conflict and in no other, in the states X4 and X2 (`mutations_of_borrows_are_stuck_and_rejected`). Open: generated programs whose borrows meet conflicts. The rate is not set | None |
| No generated checked program is stuck over a long campaign (phase 3 exit) | No long campaign yet. The checker accepts all of 300 generated programs, none of which is stuck in 11,728 runs, and 5,403 mutants of 25 of them gave none that was accepted and stuck | The checker accepts all of 900 generated programs with data, resources, captured outcomes, faults and boundaries, none of which is stuck in 36,348 runs (896 before RC22 was closed, with no answer in ten seconds on the other four). 13,176 mutants of 40 of them gave none that was accepted and stuck. No long campaign yet | Since 24 November the checker accepts all of 900 generated programs with borrows, none of which is stuck in 36,396 runs (two of them were refused before RC30 was closed). 11,088 mutants of 40 of them, of sixteen kinds, gave none that was accepted and stuck. No long campaign yet | None |
| Compiled code agrees with the oracle on generated programs (phase 4 exit) | Since 23 November: 300 generated programs at both widths of `usize`, at `-O0` and `-O2`, 23,456 runs with no difference (`vn2 fuzz --native`); six of them with their expansions in the suite. No longer campaign yet | Since 23 November: 300 generated programs with data, resources, captured outcomes, faults and boundaries at both widths of `usize`, at `-O0` and `-O2`, 23,432 runs with no difference; the runs that end in a fault (1,249 of the 11,716 runs in the oracle) and with `terminate n` (325) are compared as the others are. The five files of the suite that the checker accepts whole run in compiled code too, 68 runs (RB1 to RB3, RB10, RB12, RO12). Since RB11 the harness counts the allocations of every compiled run, in this slice and the others, and a run that leaves one live is a difference: the 23,432 runs make 26,768 allocations and release each. No longer campaign yet | Since 24 November: 300 generated programs with borrows at both widths of `usize`, at `-O0` and `-O2`, 25,736 runs with no difference (`vn2 fuzz --slice 3 --native`), making 29,692 allocations and releasing each; their hosts lent places within the arguments of every kind, among them 12 fields of variants, 26 keys and 11 values of maps, steps that no file of the suite reaches. No longer campaign yet. Since 24 November the hosts that lend from their arguments and write behind them run in compiled code: 28 runs of three files of the suite, of the controls that the checker accepts, at both widths and at `-O0` and `-O2`, with the end, the trace and the allocations of the oracle (RO6, RO11, RB13) | Draft (RB9). Six defined-root runs and six more runs covering defined awaits agree with both interpreters at both widths of `usize`, at `-O0` and `-O2`. A stateful C host sees each turn before the awaited body starts. Seven more runs cover one task set with top-level spawns of nonsuspending members and a host choice among ready tasks. Six runs cover defined awaits in members with ready siblings, including repeated loop suspension. Four runs cover owner awaits, and a C host reproduces both schedules of `runs_parent`. Nested suspension and generated task comparisons are still owed |
| Every kernel under `experiments/` within 1.2× of optimized Rust (phase 4 exit) | None measured (RB6) | None measured | None measured | |

Two exits concern the whole language and are not met: the oracle does not run
the paper corpus (RS1), and the rewritten library has not been checked.

## 4. The generator and what rests on it

**RG1. `generate::valid` is one fixed program** (`v2/src/generate.rs:452`).
It is 53 lines long for every seed. The seed picks the integer types, two
comparison operators and a few subexpressions masked with `mod 8`. It holds
dead statements such as `t0.true ∧ t0.false ▷ ⊥`, which are there to reach a
construct. `sample_runs` treats it specially by name (`generate.rs:1144`).
**(reproduced: seeds 1 to 10, 50 and 100 print 53 lines each; 200 seeds give
identical counts of mutants.)**

Everything built on it has one program shape: "reaches all 61 constructs",
"generated valid programs pass the checker", "every stuck mutant is rejected"
(8 seeds) and "generated programs agree natively".

**RG2.** `generate::free` is random and shallow: 10 to 20 lines, mostly stuck
in the first statements.

**RG3.** The generator, the differential fuzzing and the mutations cover
slice 1 only. Since 23 November the generator writes the data of slice 2 as
well, with resources and captured outcomes (`generate::valid_data`,
`v2/src/generate/valid/data.rs`), and faults and boundaries
(`v2/src/generate/valid/faults.rs`), and since 24 November the shapes that
section 3 had listed as not written. The mutations have five kinds for
slice 2 since 24 November (section 3).

**RG4.** Found on 23 November by `vn2 fuzz --slice 2`: writing the program
of one seed did not end. The arguments of a call of a function were written
with a budget of depth of their own, so calls nested in the arguments of
calls without a bound, and with several integer parameters the nesting grows
faster than it ends. The defect is in the expressions of slice 1; no seed of
the campaigns before had met it.

**RG5.** Found the same day, a defect of the first programs with data: an
integer operand of a decision, an initial value of a loop parameter and an
argument of `↑` were written over the names as they were before the
statement, so one could read a field of a name that an operand before it had
consumed ([O0]). One program of 300 was stuck by `X2`, and the checker
refused it.

**RG6.** Found the same day, a defect of the harness: `generate::entry_runs`
numbered the resources that it gives an entry from 1, as `host::Seeded`
numbers the ones that a host opens. A host then gave a handle a second
time, which the oracle reports as a host that does not keep [E-Host].

**RG7.** Found on 23 November, closed on 24 November.
`generate::entry_runs` and `host::Seeded` drew a value of an outcome type
without regard to the conditions of the operation it is an outcome of,
which the checker may assume of it ([I12], RC23). So the generator gave no
operation a parameter or a payload field of an outcome type, and a captured
outcome stayed in the body that captured it. `host::draw_outcome` now draws
arguments that satisfy the precondition of the operation and then, as a
host answers a call, an alternative and a payload of which the condition
holds for them. A host and an entry give no other value of the type, and
the native harness writes one as a capture lays it out. The generator gives
controls, extern controls and named boundaries parameters and payload
fields of the outcome types of operations declared before them. The
finding was a question for the specification: nothing said what a value of
an outcome type is that comes into an execution from outside, and Theorem 1
was false without it; [E-Host] and section 8 of the core say it now.
`a_drawn_value_of_an_outcome_type_is_one_that_its_operation_gives_i12`
(`v2/tests/harness.rs`) has a program that the checker accepts and that is
stuck by `X7` on a value that the operation could not have given, as an
argument of the entry and in the answer of a host; 60 drawn entries and the
answers of 200 hosts hold none. The oracle does not test what a host gives
here: it would have to find the arguments.

**RG8.** Found on 24 November by the generator of slice 3 (seed 204), a
defect of the generator of slice 2, and closed. Where the payload of a `□`
cannot say the type of an operand (a literal of data, an integer expression
with no anchor, a bare borrow name), the generator binds the operand to a
name in a statement before the leave. That statement runs before the
operands that stay in the payload, so `□ more {x7.m1, vt0.low {x7}}` became
`v18 : vt0 := vt0.low {x7}` and `□ more {x7.m1, v18}`, which reads `x7`
after it moved (`X2`); the checker refused it by [O2]. An operand before a
bound one that mentions a name the bound one moves is bound first now, in
their order ([O0]). No program of slices 1 and 2 changes (600 seeds of
each, text for text).

The review's own run over 200 seeds, 9,800 mutants and 200 free programs at
both `usize` widths found no program that the checker accepts and the oracle
leaves stuck. On one shape that shows little. All 52 controls of
`v2/tests/slice1` to `slice3` that have a stuck run are rejected by the
checker.

## 5. Checker (`check.rs`, `facts.rs`, `kernel.rs`, `bdd.rs`)

Each program below is accepted by `vn2 check` and stuck in the oracle.

**RC1. Loop entry does not rename an outer name that is written through a
borrow or view bound inside the loop body** (`check.rs:1706-1764`,
`2754-2770`, `4162-4172`). **(reproduced)** The checker reports 9 validated
certificates for this program, and the oracle is stuck with
`X7 E-Arith: 255 + 1 = 256 is not a value of u8`:

```text
control c() ■ { r {v : u8} }
⊤ ▷ ~x : u8 := 0
⊤ ▷ s : ↻ l() {
    ⊤ ▷ p : &~u8 := &~x
    ⊤ ▷ p ← p + 1
    ⊤ ▷ ↑ l()
}
```

The same defect gives an index out of bounds and a failed precondition of a
call.

Closed on 24 November. At the entry of a loop the checker renamed what the
body assigns, the operands of its calls that lend exclusively, and the
roots of the loans recorded by then; a borrow bound in the body has no loan
recorded when the loop is entered, so the name it writes kept its facts on
every turn. [I9] reads what a body changes off its text: the places it
lends exclusively, wherever the borrow stands. `collect_modified_vars`
(`check.rs`) now takes them from binds, assignments, the arguments of `↑`,
of a nested loop, of a supervised boundary and of a spawn, and the payloads
of `□` and `■`. The contingency of a lexical boundary had no such defect:
what it takes into its care is the value at the entry of the boundary.

**RC2. `capture` of a built-in that changes a shape leaves the facts about
its `&~` operand in place** (`check.rs:3639-3647`). **(reproduced)** Accepted
with 9 validated certificates; stuck with
`X7 E-Index: index 1 is out of bounds for length 1`:

```text
control c() ■ { r {n : u32} }
⊤ ▷ ~v : [u32] := [10, 20]
⊤ ▷ o := capture pop(&~v)
⊤ ▷ d : Δ outcome(▾o) ▸ item {x} │ empty {}
⊤ ▷ ■ r {v[1]}
```

**RC3.** The facts of a capture ([I12]) survive a new assignment to the
outcome variable (`check.rs:3671`, `3882-3892`).

**RC4. The contingency of a lexical boundary is checked against ownership as
it was at the entry of the boundary** (`check.rs:4444-4458`). A value that
B₁ moved before its fault is used in the contingency: `X2 E-Var`
**(reproduced)**; with a resource, `X5 E-Scope`.

**RC5.** A `must` value that `contingency [c]` captures is not checked on the
normal completion of B₁ (`check.rs:4403-4414`). Whether the checker or the
oracle is wrong is open.

**RC6.** A call that can fault inside the contingency of a named boundary is
accepted (`check.rs:5023`, `4707-4717`): `X8 E-Unwind`. Whether the checker
or the oracle is wrong is open.

**RC7.** A move mark in a read position, `len(▾v)`, moves in the oracle and
is a read in the checker (`check.rs:2267-2273`). `resolve` should probably
refuse the form.

**RC8.** The [A9] interval of a field of a nested constructor
(`check.rs:383-396`). Contrived.

Where the code departs from the [fact logic](facts.md):

**RC9. The kernel does not check that an instance is an instance ([V2]).**
It compares the clause label with a list of ten strings
(`kernel.rs:142-150`). A certificate whose query is true and whose one
instance is `[A1] := FALSE` validates. All reasoning about congruence,
constructors, updates and products reaches the kernel this way. The steps of
a lemma are checked properly.

**RC10.** The kernel is not independent and is not told the goal ([V1]). It
imports `Row`, `div_floor`, `complement` and `combine` from `facts` and
recomputes on a copy of the search's own diagram (`kernel.rs:11`, `159`).

**RC11. Not every entailment is validated.** `is_feasible`
(`check.rs:2000-2013`) trusts a `Proved` that no kernel saw, and it decides
whether errors of [O3], [O3a], [O4], [F3] and [F5] are reported.
**(reproduced)** In this program the decision on `read` has no `uses io` to
stand on; it is accepted because its history is infeasible, and no
certificate for that is listed:

```text
extern control read(port : u32) ■ { value {v : u32} │ closed } uses io
control c(a : u8) ■ { r }
⊤ ▷ t : ? a > 255
t.true ▷ d : Δ read(1) ▸ value {v} │ closed
⊤ ▷ ■ r
```

**RC12. The procedure is not exact on integers, and it gives up by
panicking.** It is Fourier–Motzkin elimination with rounding by the greatest
common divisor, without a split, without an Omega step and without a bound.
`Decision` has only `Proved` and `Refuted`. **(reproduced)** The precondition
below has rational solutions and no integer one, so `⊥` is unreachable; the
checker panics at `facts.rs:1775`. Decision Q7 allows a proof to be given up
only as a counted limit.

```text
control c(x : i32, y : i32) ⊢ 11 * x + 13 * y ≥ 27 ∧ 11 * x + 13 * y ≤ 45 ∧ 7 * x - 9 * y ≥ -10 ∧ 7 * x - 9 * y ≤ 4 ■ { r }
⊤ ▷ ⊥
```

**RC13.** The text of a certificate ([V5]) is counts only. A second checker
cannot read it.

**RC14.** The terminators that [F5] allows in a contingency are not enforced.

**RC15.** Tampering with a certificate is tested on lemma steps only. No test
compares the checker with the oracle for slices 2 and 3.

**RC16.** The checker did not finish on the expansion of one generated
program in 63 seconds of processor time. `check_body_inner` is one function
of 1,582 lines. (Both are closed: section 9.)

**RC17. The type of an element that only a frame instance speaks of was
guessed.** Found on 23 November, while the kernel's matcher was written. For
an update `t[i ↦ e]` and an index `j`, the instance of [A6] speaks of `t[j]`.
The search gave that term the element type of another vector on which `j` is
an index, when the sorts of the two vectors were equal or when one of them was
not known to the solver, and with the type its range. An element of a vector
of `u32` could so be given the range of `u8`. No wrong acceptance was
reproduced.

Closed in two steps. Since 23 November neither the search nor the kernel
gives a range to a term that the checker did not write. That left the
element without the range that [A1] gives it, and the record said that a
proof could be lost. None can: the term stands only as a side of the
equalities that instances of [A6] and [S5] conclude, so a model says of it
only which other elements it equals, and an element that the program
mentions has its range (section 8 of the [fact logic](facts.md)). On 24
November the same examination found one term for a literal at every type:
`[]` of `[u8]` and `[]` of `[label]` were one term, as were `∅` at two
types and `[1, 0]` beside `[true, false]`, so that a value of one type was
the same number as a value of another. The names of two such values have
their sorts and the search pairs elements of one sort only, and no wrong
acceptance was reproduced. A literal term has its type now, and every term
one sort.

**RC18.** Found on 23 November by the comparison of the kernel with the
search. For two constructor terms of one struct that differ in the number of
arguments, the search concluded from the equality of the arguments they share
that the terms are equal. A program that resolves has no such terms.

**RC19. A check was not the same from run to run.** Found on 23 November,
when the work of the search was first measured by counts. The checker kept
the names that a loop changes, and other sets of names, in hash tables, and
numbered the terms of a body in the order in which a table gave them. The
certificate text of one program then differed between two runs of one
binary, against [J6], which names the order of a hash table. No answer was
seen to differ. The count of steps of a query differed, and with it whether
a query near the limit reaches it.

Held up under attack: the arithmetic of slice 1 at the bounds of every type
and at both `usize` widths, loops and invariants, mutable names in branches
and effects; in slice 2, leaks at `↑`, `□` and `■`, overwriting a `must`
value, [F1] and [F2]; in slice 3, the loan rules, where 25 programs that are
stuck with X4 were all rejected.

**RC20.** Found on 23 November while the fault boundaries of the oracle
were requalified: the checker refuses by [F3] a named boundary that
supervises another whose body has an effect. A boundary declares no effects;
those of both bodies count toward the control that supervises.

**RC21.** Found on 23 November by the first programs of the generator of
slice 2. The checker gave the statements of a contingency every history of
the boundary. So it refused `⊥` in the contingency of work that cannot
fault, which no execution runs (`falls_off` of
`v2/tests/slice2/lexical_boundaries.core` is such a control; the suite ran
that file in the oracle only), and it knew in a contingency nothing of the
histories on which the work faults.

**RC22.** Found on 23 November by `vn2 fuzz --slice 2`: one of the first 300
programs (80 lines, no run of it stuck) got no answer from the checker in
two minutes. The generators of the days after gave four more: one that got
no answer either and whose check held 800 megabytes after five seconds, one
with faults and boundaries, one with a boundary in the work of another (65
lines, accepted after a minute in 275 theory checks with no tableau
exchanged), and one that the checker accepted after 27 seconds in which 136
theory checks wrote 81,786,060 entries of tableaus. With the generator of
24 November four of 900 programs got no answer in ten seconds. The five
programs are in `v2/tests/kernels/`.

Closed on 24 November. There were two defects, and a bound was missing.

The first was in the models of the search. `Solver::decide` conjoins a
premise or an instance where the model of a candidate fails it. The model
had the number zero for every constructor term that the candidate did not
speak of, and the theory check gave one number to all the terms of a sort
without arithmetic that no row kept apart. Two constructor terms with
different arguments were then one value in the model. That fails the
instance of [A4] which says that equal terms have equal arguments, and the
search conjoined it for every two such terms. Each brings the disequality
of two numbers, which the diagram holds as a choice of their order, and
the lemmas refute the orders one at a time. On the smallest program the
formula of one question passed 540,000 nodes, and the check held 1.3
gigabytes after twelve seconds. A model now gives a content one number
(`v2/src/facts/completion.rs`; section 7 of the
[fact logic](facts.md) says what a model of the crate is). The four
programs are checked in 115 to 327 theory checks, and the diagrams of all
their questions together hold 26,819 to 52,049 nodes.

The second was in the theory check. One candidate of
`kernels/exchanges.core` has no model, and the splits went on with it for
26,213 tableaus before the Omega test refuted it in seven splinters. The
test is now asked as soon as a search without a turn has found nothing,
and the splits take turns after it. A search for a model is made after
every round of rounded sums as well: a round has several times the rows of
the round before (7,298 rows from 25 on one candidate of the data kernel),
and a model that the first search missed is found with the rows of one
round. The program takes 8,845,759 entries.

The bound: nothing limited a diagram. A node that the diagram of a
question grows by is now a step of [J6], and the nodes are a count that
`vn2 check --counts` prints.

**RC23.** Found on 23 November by probes for the generator of captured
outcomes. [I12] of the fact logic gives a decision on a captured outcome the
conditions of the captured operation, over fresh names for the arguments
where the capture is not visible. The checker added the conditions only
where it had seen the capture. Of an outcome that arrived as a parameter of
a control or of a loop, or as the payload of a loop, it knew nothing, and
refused programs that are valid. It accepted nothing false by this.

**RC24.** Found on 24 November by `vn2 fuzz --slice 2` (seed 781 of the
programs with boundaries in the work of boundaries), and closed. A name
with a single binder that is bound to a constant expression is a constant
expression ([I3]), and a product with a constant is a linear term. The
checker lost that of a name which a boundary takes into its care: in the
contingency it knew the value of the name and did not hold the name for a
constant, so `v mod 3 * (v mod 5) = v` with `v` bound to 1 was not decided
and `⊥` on its false side was refused. The care list binds nothing, and
[I3] of the fact logic says so now. The checker refused a valid program by
this and accepted nothing false.

**RC25.** Found on 24 November, and closed. A counterexample printed a
number for every name in scope, also for a name of a struct, a string, a
vector or another data type, which has none: the number is the one the
model of the search gives the term, zero before RC22 was closed and a
number above 2⁹⁵ since. The report leaves such a name out now and gives
its length where the model has one, as `len(v) = 1` ([M2], [M7]).

**RC26. The checker knows the constructor of a variant value only from a
decision, and no struct without fields.** Found on 24 November, when the
axioms of the data were written as statements of a program and held against
the oracle (`v2/tests/slice2/facts_data.core`). [A5] says that `t is c`
holds for exactly one constructor `c` of the type of `t`, and that then
`t = V.c {ū}` for some `ū`. [A4] says `t = S {t.x₁, …, t.xₙ}`, which for a
struct without fields is `t = S {}`. [J1] has both in the base logic, so
both are entailed of every value. The crate has the first only as the fact
that a decision adds on each of its alternatives ([I11]), and the second
only as an instance for two values whose fields the checker wrote, of which
a struct without fields has none. Three statements that every run finds
true are refused:

```text
copy struct unit {}
copy variant one {only}
copy variant color {red │ green │ blue}

control one_value(u : unit, w : unit)
    ■ { ok {} }
    ⊤ ▷ ⊢ u = w
    ⊤ ▷ ■ ok {}

control one_constructor(t : one, u : one)
    ■ { ok {} }
    ⊤ ▷ ⊢ t = u
    ⊤ ▷ ■ ok {}

control one_of_its_constructors(c : color)
    ■ { ok {} }
    ⊤ ▷ ⊢ c = color.red ∨ c = color.green ∨ c = color.blue
    ⊤ ▷ ■ ok {}
```

The crate proves less than [J1] entails, which [J5] does not allow; it
accepts nothing wrong. After a decision on `c` each of the three is
proved. Open, and a choice: the crate gets an instance for every term of a
variant type, with a term for each field of each constructor, and writes
the fields of every struct value, at a cost in terms for every program
with data; or [J1] and [J3] say that the logic knows the constructor of a
value from a decision, which section 11 of the fact logic lists among the
ways to state a missing fact.

**RC27.** Found on 24 November by the checker against the rule files of
the borrows, and closed. An assignment through a name of exclusive borrow
type that a bind or an operation had moved was accepted with validated
certificates; the oracle is stuck with `X2 E-Var` (`old_name_is_moved` in
`v2/tests/slice3/b4_moves_and_scopes.core`):

```text
control c() ■ { ok {v : u32} }
⊤ ▷ ~x : u32 := 1
⊤ ▷ r : &~u32 := &~x
⊤ ▷ q : &~u32 := r
⊤ ▷ r ← 4
⊤ ▷ ■ ok {x}
```

A read of `r` was refused by [O2]; the assignment through it wrote the
place without asking whether the name was there. [E-Assign] reads a name
of borrow type through which it writes as [E-Var] does, and
`check_assign` asks [O2] of it now, as `check_assign_place` does of a
root.

**RC28.** Found on 24 November by the clause tests of the loans, and
closed. The checker evaluated the arguments of a function applied in an
operand with an empty set of the borrows the statement holds for its
command, so a read of a name that an earlier operand lends exclusively was
accepted with validated certificates; the oracle is stuck with `X4 B1` when
the callee writes through the borrow that the read ended:

```text
control two(a : &~u32, b : u32) ■ { done {} }
⊤ ▷ a ← b
⊤ ▷ ■ done {}
function id(v : u32) : u32 := v
control c() ■ { ok {v : u32} }
⊤ ▷ ~x : u32 := 1
⊤ ▷ r : &~u32 := &~x
⊤ ▷ d : Δ two(r, id(x)) ▸ done {}
⊤ ▷ ■ ok {x}
```

`two(r, x)` was refused by [L3]; `id(x)` hid the read. The arguments of the
function are checked with the borrows of the statement now, and the borrows
they make themselves are dropped after the function (`eval_loan_expr`,
`Expr::Call`).

**RC29.** Found with RC28, and closed. A borrow made in the operand of
`len` was held by the statement until its command, so the end of the scope
at an exit or a leave was a write while it was live, and `■ ok {len(&v)}`
was refused by [L3] although every run ends. `len` uses the borrow where it
is applied and its value carries none; `eval_loan_expr` drops the borrows
of the operand of `len`, `clone`, `trim`, `-` and `¬` after it. [L2] of the
core says so now.

**RC30.** Found on 24 November by the generator of slice 3 (two programs
of 900), and closed. At `recover ↑ ℓ` the checker took as live after the
restart every name that the body of the restarted loop did not bind itself,
so a name bound in a body within it, the work of a boundary around the one
that recovers, was live too. Where that name held a borrow from the payload
of a decision, the end of the scope of the value it borrows was a write
while the borrow was in use, and the program was refused by [L3], although
every run ends:

```text
extern control e0(p0 : &[u32]) ■ { high {r1 : &u32 ∈ p0} }
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
```

With the fault in the work of `b28` itself the program was accepted. The
next iteration binds every name of a body within the loop anew ([L2a]), as
the checker already said at the head of the loop; `compute_body_liveness`
asks `var_in_body_tree` of the restarted body now. A borrow that goes on
into the next iteration through a parameter of the loop does outlive the
scope of what it borrows, and is still refused.

**RC31.** Closed on 25 November. The checker used to refuse every spawn
that could lend to a member. It now attaches the borrow to the set on the
histories where the spawn runs. Ending the lender's scope or writing to it
while the set still holds the borrow is refused by [L3]. A shared or
exclusive loan may survive a loop iteration, including a spawn in an
earlier iteration of an inner loop. A borrow returned by `await next` can
outlive the set. The accepting and rejecting histories are exercised in
`v2/tests/checker_slice4.rs`. On the task rule files `shared_pool` and
`excl_pool` are accepted, and `race_write` is refused at the write. Section
18.3 of the oracle document gives the measurements and the arithmetic
correction to the positive fixture.

**RC32.** Found on 25 November with the checker of slice 4. It is for the
author and does not block. [TK4] asks that the payload of an `extern async
control` that a task awaits be fault-releasable, so that a task stopped
before it runs again can release it. The host completes an operation only
when no task of the run is ready ([E-Turn]). The task whose operation it
completed is then the only ready task, and it takes the next turn. That
turn ends at the task's next `await`, where [TK4] asks about every name in
scope; or at the task's end, where the payload of a producer is asked
about; or at a fault, where [F2] asks. A cancellation can make several
tasks ready at once, but only with `cancelled`, which has no payload
([W12]). So in a checked program no schedule stops a task that holds such a
payload. `awaits_fetch` in
`the_payload_of_an_awaited_extern_control_is_fault_releasable_tk4`
(`v2/tests/checker_slice4.rs`) is refused, and each of its runs ends.
Dropping the condition from [TK4] would make no checked program stuck; the
checker keeps it as the rules state it. The same reasoning took the
condition off a `run` of an extern control, since no task receives that
payload (core section 12, 25 November).

**RC33.** Found on 25 November while checking the field updates of a
spawn. An ordinary call takes a view constructed from exclusive borrows
of two fields of one record. Its callee sets the fields to 8 and 9.
Before the repair each update in the caller started from the same entry
record, so the second one restored the old logical value of the first field. With
initial fields 1 and 2, the checker proved the obligation that the first
field still equalled 1. The oracle reaches `X7 E-Oblige` there.

Before the repair `vn2 check` accepted this program with nine certificates.
Its run directive is checked by `vn2 test`.

```text
struct triple {a : u32, b : u32, c : u32}
view struct slots {one : &~u32, two : &~u32}

control update(s : slots) ■ { done {} }
    ⊤ ▷ s.one ← 8
    ⊤ ▷ s.two ← 9
    ⊤ ▷ ■ done {}

control start() ■ { ok {} }
    ⊤ ▷ ~t : triple := triple {1, 2, 3}
    ⊤ ▷ d : Δ update(slots {&~t.a, &~t.b}) ▸ done {}
    d.done ▷ ⊢ t.a = 1
    d.done ▷ ■ ok {}

//! run start() => stuck X7 E-Oblige
```

The same run gets stuck if `update` takes two separate `&~u32` parameters
and the caller passes `&~t.a` and `&~t.b` directly. Before the repair the
checker accepted that version with eleven certificates.

Closed on 25 November. Each exclusive operand now updates the root left
by the preceding operand. Both examples are refused at the assertion by
[P1]. Section 16.5 of the oracle document records the accepting and
rejecting tests, including named borrows and a captured call.

## 6. Oracle and erased interpreter, slices 2 to 4

Each probe states what the core requires as a run directive. 21 of 56 fail.

**RO1. A lexical boundary inside the body of a named boundary is skipped**
(`oracle.rs:2722-2738`, `2796-2812`; `erased.rs:1757-1773` does the same).
**(reproduced)** By [E-Contingency] the fault below reaches the inner
contingency first. The trace is `[emit("outer") -> done {}]`:

```text
boundary worker(tag : string) retains tag {
    1  ⊤ ▷ lp : ↻ retry(n : u32 := 0) {
           1  ⊤ ▷ b : boundary {
                  1  ⊤ ▷ z : ? n = 0
                  2  z.true ▷ fault "inner"
              } contingency (m : string) {
                  1  ⊤ ▷ e : Δ emit(&m) ▸ done {}
                  2  ⊤ ▷ escalate
              }
           2  ⊤ ▷ □ done {}
         } ▸ done {}
    2  ⊤ ▷ terminate
} contingency (m : string) {
    1  ⊤ ▷ e2 : Δ emit(&tag) ▸ done {}
    2  ⊤ ▷ terminate
}

control run_it()
    ■ { done {} }
    uses console.write
    1  ⊤ ▷ supervise worker("outer")
    2  ⊤ ▷ ■ done {}

//! run run_it() => done done trace [emit("inner") -> done; emit("outer") -> done]
```

**RO2. [E-Exit] evaluates the condition of an `&~` parameter on its value at
entry when the borrow was passed on** (`oracle.rs:4136-4148`). A true
condition is stuck and a false one passes. **(reproduced)** The checker has
both right.

**RO3. A lexical contingency may end in ways that [E-Contingency] forbids,
and `terminate` has meanings the core does not give it.** A contingency may
exit or continue a loop. A run ends `done terminated` while its caller holds
an open resource. `terminate` in a loop inside B₂ panics at `oracle.rs:1484`
**(reproduced)**.

**RO4.** `recover ↑ ℓ` restarts from a snapshot taken at the entry of the
iteration and not at the entry of the boundary (`oracle.rs:2935-2937`,
`4361-4384`).

**RO5. The erased semantics releases wrongly under faults.**
(`erased.rs:636-644`, `659-667`, `1685-1708`) A value moved in a loop is
released twice. Under another schedule, a release is missed on the
repository's own `tests/slice4/tasks_faults_and_cancel.core`, and the two
traces differ **(reproduced)**.

The first of the two is closed on 23 November, when generated programs began
to fault and showed it in two of 900. The layout of a body took nothing from
the bodies inside it: after a loop or a boundary, a name of the body around
was as it had been before, and a fault in the work of a boundary released
the names around the boundary as they were at the boundary statement. Now
the work of a boundary leaves a name as it is at its end ([E-Boundary]); a
loop leaves it as the `□` that ended the loop left it, for which the erased
interpreter keeps one bit for each such `□`, and only where some `□` leaves
the name otherwise than the loop found it ([O6](b) makes the answers of one
alternative agree, so for a checked program the bit says no more than the
atom of the alternative); and a fault releases by the formulas of the
statement that faulted ([F5]). For the names around its boundary a
contingency first remembered that statement; since the backend was brought
to the same layout (RB1, later that day) the layout keeps a bit for each
statement of the work that may fault and leaves some such name otherwise
than the boundary found it, and the formulas of the contingency are written
over these bits. The interpreter and compiled code evaluate the same
formulas (`erased::layout`), and [R3] and [R4] of the core say what they
keep of a history.
The second, the release that is missed under another schedule of tasks, is
open for slice 4.

**RO6.** No host can answer an extern control whose payload is borrowed.
Every such call ends in `violation`.
Closed for the two semantics on 23 November (section 9). Compiled code was
owed: the native driver answered a borrow with a value in a cell of its
own, which is no place within an argument, and the one test of it gave
such values and compared compiled code with the erased semantics alone,
which takes them. Closed on 24 November: in the stub of a host, a borrow
in a payload is the address of the place that the host names, along its
steps through the fields of a view, the borrow a view holds, struct and
variant fields, vector elements and map values; the cell is gone, and a
value where a borrow belongs stops the driver, as the oracle stops the run.
No test reaches a variant field or a map key in compiled code yet: a
directive has no step for either. The generator of the slice is to.

**RO7. The erased interpreter is a parallel transcription of the oracle.**
34% of its substantial lines are in `oracle.rs` word for word; for unwinding
and the scheduler it is 61%. An error of structure appears in both and
compares as `Same`, as RO1 does.

**RO8.** An extern control that returns a resource inside a struct is treated
as pure (`typed.rs:431-455`).

**RO9.** The built-in `insert` does not have the contract of the
[reference model](references.md) (`resolve.rs:1891-1905`); the document's
example 6.3 is refused. `take`, `entry_at`, `trim`, `done terminated`,
`X5 E-Resource`, `X2 E-Field` and `X2 E-Supervise` are choices of the code
with no entry in section 12 of the [core](core.md).

**RO10.** The written borrow mode of the collection operand of a built-in is
ignored (`resolve.rs:1691-1702`).

**RO11.** Found on 23 November with RO6. A host cannot write through an `&~`
argument: it is given values, and [E-Extern] gives the host relation no part
of the store. [W7] reads an `&~` parameter at completion in the contract of
an extern control as well, so a condition such as `x = old(x) + 1` on one
has no faithful host. The checker forgets what such an argument refers to
after the call, which is sound either way. The rule and the host interface
are owed with slice 3; the core names the question in its section 12.
Closed on 24 November: the host relation gives, beside the payload, the
value that the host leaves behind each argument lent exclusively, and
[E-Extern] writes it there as a write access through the tag of the
argument, before the borrows of the payload are made (the event holds the
arguments as they were at the call); the condition reads the argument after the write and `old` of it before.
Nothing is written behind an argument of kind `must`. [E-Host] makes a
value of the wrong type, a value behind an argument that was not lent
exclusively, and a change to a value of kind `must` violations. In a
directive the write is `~x <- v` after the answer, with `x` the parameter.
The native driver wrote nothing behind an argument, as it made no
reborrow of one (RO6), and the runs whose host writes were left out of
compiled code. Since 24 November the stub of a host prints the event with
the arguments as they were, writes what the host leaves behind each
argument (the new value is made before the old one is released, so the two
never share an address), and then makes the borrows of the payload.

**RO12.** Found on 24 November by the clause tests of the data rules, and
closed. Under a fault the oracle released the names of a scope in the
reverse of the order in which the run had bound them, and the erased
semantics and compiled code in the reverse of the order in which the text
first binds them. The two orders differ where a name has a binder on each
of two histories, or where two alternatives of a decision name their
payloads in different orders, and a release is an event of the trace:

```text
⊤       ▷ t : ? first
t.true  ▷ o1 : Δ open_conn() ▸ opened {a}
⊤       ▷ o2 : Δ open_conn() ▸ opened {b}
t.false ▷ o3 : Δ open_conn() ▸ opened {a}
⊤       ▷ fault "either"
```

With `first` false the oracle released `a` and then `b`, the erased
semantics `b` and then `a`. The core did not say which. [E-Unwind] gives
the order of the text now, which needs no record of a run ([R4]), and the
oracle follows it. No generated program had shown the difference: the
generator binds a name once.

**RO13.** Found on 24 November, open. The core text names the contract of
an outcome type by a declared outcome or by a control, `outcome⟨f⟩`, and a
capture of `f` has that type. The reader resolves the fields of struct and
variant declarations before the contracts of controls, and the signature of
a control before those of the controls after it. So `outcome⟨f⟩` is refused
as undeclared ([C1]) in a field of a declared type, and in the signature of
a control that stands before `f` in the text; for a control whose payload
holds a borrow the same message stands where [T6] is the clause. A struct
or a variant can therefore not hold a captured outcome, though a vector, a
map, a parameter and a payload can. Nothing wrong is accepted. The surface
has no way to write the type, so no Rails program meets it.

**RO14.** Seen on 24 November, open for slice 3. The reader of the core
text takes any expression of type `τ` as the argument for an `&τ` parameter
of a function or a control and reads it where it is, a constructor among
them. [C1] and [W5a] of the core ask for `&p` or a place, and [U11] of the
surface binds such an expression to a hidden name first. The oracle
document describes what the reader does. Either the core says so or the
reader asks for the place.

Closed on 24 November. The reader asks for the place. Where a borrow type
is expected (a parameter of an operation, a payload field, a loop
parameter, a field of a view, a bind with a written borrow type) an operand
is `&p` or `&~p` in the mode of that type, or a name or a field of a view of
that very type; [C1] of the core says so. A name of exclusive borrow type is
no operand for a shared borrow: `&r` lends what is behind it again. The
argument of a function for a borrow parameter is a place, written without
`&` ([W5a]). Nine files of the suite and the generator of slice 2 gave a
literal key or text for an `&` parameter of `get`, `remove` or `emit`, or a
constructor to an extern control; they bind it to a name first now, as the
surface does. The programs of slice 1 are unchanged.

**RO15.** Found on 24 November by the clause tests of the borrow rules, and
closed. A formula makes no access ([E-Formula]), so [B1] did not apply to
it, and the core did not say what a formula is worth that reads through a
dead borrow. The oracle read the place as it stood: `⊢ s = 2` after
`x ← 2` held, and where the place was gone (an element popped) the run was
stuck by `X7 E-Index`. [E-Formula] says now that a formula reads through a
borrow only while its tag is alive, and the row X4 of section 6.10 names
it. A formula is a mention for [L2], so the checker excludes the state.

**RO16.** Found on 24 November with RO15, and closed. A place given for a
borrow parameter of a function made a shared borrow in the oracle, where
[W5a] and [E-Fn] say that it is read where it is and that no borrow is
made. No verdict of the suite differed, since a shared borrow is made by a
read; the borrow lived on, and a later write named it as the cause of a
death. The oracle reads the place now, a read access, and makes no tag.

**RO17.** Found on 24 November with RO15, and closed. Passing a borrow on
is no access (section 6.3), and the oracle read every argument through its
borrow at a call to keep its value at entry, and every borrowed parameter
and payload field at an exit for the condition. A call that passed a dead
borrow was stuck where nothing read it. Now a value at entry or at
completion is read where a formula of the signature mentions it, by
[E-Formula].

**RO18.** Found on 24 November with RC27, and closed. RO14 left one path
of the reader as it was: the operands of a decision or a capture for a
parameter of type `&~τ` (`Resolver::arguments`) took any place as `&~p`,
so `set(x)` lent `x` exclusively unwritten, and refused `set(▾s)` for a
name `s` of that type, which moves there. [C1] asks for `&~p` or a name of
the type, which may carry the move mark; a name of shared borrow type is
read where a borrow is expected, and a mark on it is refused, as RC7 has
it for a read.

The suites:

| Slice | Files | Runs | Stuck labels reached | What the test asserts |
| --- | ---: | ---: | --- | --- |
| 1 | 41 | 126 | 15 | 12 rules, 15 stuck states, 9 refusals |
| 2 | 13 | 33 | 10 | 9 rules, 10 labels, 6 refusals. Since 24 November: 100 files, 358 runs, 20 rules, 18 labels, 15 clauses of refusal |
| 3 | 2 | 22 | 1 | at least 20 runs, at least 12 compared. Since 23 November: 5 files, 55 runs, and the seeded host on the controls of one file. Since 24 November: 25 files, 216 runs, 13 rules, 3 labels, 1 clause of refusal, and the cause of each of 67 dead borrows; 28 runs of three files in compiled code too (RO6, RO11) |
| 4 | 2 | 16 | 5 | 10 rules; no stuck state |

Held up: the ownership rules of slice 2 (23 runs), the tags [B1] to [B5]
(16 runs and the examples of the reference model), the scheduler,
cancellation and `await next`. 338,985 variants of schedules gave no panic
and no difference other than RO5.

## 7. Backend and expansion (`codegen.rs`, `expand.rs`)

**RB1. A change of ownership inside a nested body is invisible to the
cleanup of the enclosing scope** (`erased.rs:636-667`, `codegen.rs:311`,
`3858-3865`, `4354-4426`). Checked programs that both interpreters run to
`done` crash natively at `-O0` and `-O2`: a value moved inside a loop is
freed again when the scope ends **(reproduced; the process ends in a trap)**.
Expansion produces the pattern by itself.

Closed on 23 November. The backend ended the scopes around a statement by
the formulas of the statement that holds the loop or the boundary, which do
not see what the body inside did. It takes the layout of the erased
semantics now (`erased::layout`, see RO5): the formulas of a statement cover
the names of every body around it, and a terminator or a fault ends each
scope by the formulas of its own statement. A `□` and a statement of the
work of a boundary set a bit where a formula asks which of them ended the
loop or faulted. Before, 10 of the 12 runs of
`v2/tests/slice2/erased_nested_ownership.core` and 9 of the 24 of
`checked_faults_and_boundaries.core` differed in compiled code, by a trap,
a wrong end or a release event too many.

**RB2.** `recover ↑ ℓ` restarts with the parameters of the entry
(`codegen.rs:4251-4276`, `4530-4551`). Closed on 23 November with RO4, when
the copies of the parameters went; the controls `retries` and `collects` of
`checked_faults_and_boundaries.core` hold it in compiled code since RB1.

**RB3.** `escalate` with a fault message on the heap frees the message and
passes it on (`codegen.rs:3866-3873`, `4457-4478`). Closed on 23 November.
The message of a fault has one owner. A contingency holds it in a slot of
its own for `escalate`, and that slot ends with the contingency where the
fault does not go on with it (`recover`, `terminate`, a new fault). The name
that the contingency gives the message reads that slot where no statement
consumes the name, and owns a copy otherwise. `fault x` consumes `x`, which
the layout did not count: the message was freed with the scope and passed
on. The controls `passes_on`, `keeps_message`, `faults_again`,
`retries_with_text` and `supervises` hold it, with messages that own memory.

**RB4.** Narrow integers reach C host functions without `signext` or
`zeroext` (`codegen.rs:477-485`). An `i8` of -1 arrives as 255.

**RB5.** The C wrapper reads slots that were never written, for `bool`
payloads of alternatives not taken (`codegen.rs:5576-5616`).

**RB6. The performance figures are not the measurement the plan asks for.**
The ratios reproduce (0.99, 1.01 and 1.02). They belong to three synthetic
kernels written inside the tests, which are dominated by remainders by
constants. The exit of phase 4 is every kernel under `experiments/`, for
time, allocations and peak memory; none is measured. No test measures
allocations. The test of slice 1 prints its ratio and asserts nothing about
it. Maps are sorted arrays: inserting 20,000 keys in descending order takes
55 ms against 0.52 ms for Rust's `BTreeMap`, and this was recorded nowhere.
Since 23 November the paired tests of slices 2 and 3 go on measuring, up to
40 rounds, until the best times are within their bound of 1.20: on a machine
with a load average of 40 to 60, five rounds gave ratios of 1.49, 1.14 and
0.98 for the same two binaries. The bound and the kernels are as they were.

**RB7.** The tests do run native code (113 compilations, 352 runs) and
compare outcomes and traces. Every string they supply is static, so a drop
does nothing; 32 of the 59 modules never allocate.

**RB8.** Expansion: the prefix `_exp{N}_` is not checked against the names in
use, so a checked program can have an expansion that [O1] refuses; a
recursive control is returned unexpanded as a success; a callee with an exit
inside a boundary is skipped without a word.

**RB9. Open.** On 23 November `emit-llvm` panicked on the task suite.
On 25 November the first native [E-Run] checkpoint covers a defined root
with no suspension, task set or external async operation. Six runs in
`v2/tests/slice4/checked_run.core` exercise a decision and a capture with an
owned vector on either alternative, fault propagation with two ordered
resource releases, and a nested run with three ordered host events.
`cargo test --test backend_slice4` compares all six with both interpreters
at 32- and 64-bit `usize` and at `-O0` and `-O2`. Each six-run batch
makes four allocations and releases all four.

The second checkpoint on 25 November covers [E-Await] of a defined control
when the same task is the only one ready. The six runs of
`v2/tests/slice4/checked_await.core` include a captured outcome, a fault
with an owned vector, a write through an exclusive borrow, and two nested
awaits. Each six-run batch makes two allocations and releases both.
`the_host_picks_the_turn_before_the_awaited_body_starts` links the emitted
module and C header to a host that returns the number of turns so far.
Across four samples it observes 0, 1, 2, 2. Skipping the awaits gives one
sample at 0. The oracle and erased interpreter agree on the full sequence
of samples and turn choices at both widths. The earlier diagnostic for
defined await has been replaced by these execution tests.

The third checkpoint on 25 November schedules multiple ready tasks in one
set. Each top-level spawn site binds a stack activation. The producer takes
and returns owned or copy values and finishes in one turn. A done member
retains its tag and payload until delivery. In
`v2/tests/slice4/checked_spawn.core`, `turns [1]` reverses the two pairs of
emits. Another schedule lets both members finish before the owner takes its
vector. Two further schedules select among three children and append a
fourth after a delivery. The seven runs give 28 compiled comparisons at
both widths and optimization levels. The six allocated vectors per batch
are all released. Forcing every host choice to zero gives a different trace
at 32-bit `usize`, `-O0`, in
`spawned_members_run_on_the_chosen_turn_and_keep_their_payloads`.
The same Rust suite checks diagnostics on oracle-backed examples.

The fourth checkpoint on 25 November lets a member give up its turn at
a defined await. The awaited callee must finish in one turn. The member
keeps its bound operands, result destinations and place in spawn order.
In `v2/tests/slice4/checked_member_await.core`, one host schedule lets the
second member finish and the owner receive its vector before the first
member resumes. Other runs exercise a write through a borrow of a member
local, a captured outcome, a loop that suspends twice at the same site,
and the same producer invoked as a root. The six runs give 24 compiled
comparisons across both widths of `usize` and at `-O0` and `-O2`. Each batch
makes seven allocations, all released. The separately linked C host in
`the_host_sees_a_suspended_member_in_spawn_order_until_it_finishes` observes
the same eight ready counts as both interpreters. Resuming the yielding
member immediately changed the trace and the ready counts at 32-bit
`usize`, `-O0`, and both tests failed. The earlier refusal of a
producer that awaits a defined callee is covered by these execution tests.
Diagnostics still cover an awaited callee that suspends again or owns a set.

The fifth checkpoint on 25 November replaces the blanket refusal of an
await in the owner with execution tests. The defined callee must finish
in one turn without a fault or termination. In
`a_defined_owner_await_preserves_completions_until_next` two children can
finish before the owner resumes. Its captured vector and both child results
survive that schedule, and `count` includes both completions until delivery.
The four runs give 16 native comparisons with the two interpreters at both
widths and optimization levels, with eight allocations per batch, all released.
`the_host_chooses_between_an_awaiting_owner_and_its_child` links a C host to
`runs_parent` in `e_await.core`. Choosing the child first reverses the emits.
Resuming the owner immediately made both tests fail at 32-bit `usize`, `-O0`.
The C host saw one ready task at the first offer where both interpreters saw two.

Repeated spawn sites, multiple sets, borrowed inputs and payloads of a
spawn, nested suspension in an owner or member,
host completion, cancellation, member
faults, capacity and generated task comparisons remain open. The width
setting selects the integer representation of `usize`. The LLVM module
still has no target triple or data layout, and these runs use the native
host ABI.

**RB10.** Found on 23 November by the first generated programs of slice 2 in
compiled code, and closed. The functions emitted for a variant or an outcome
(equality, order, clone, destruction) defined one local name once for each
constructor with components, so a type with two such constructors did not
compile; and the destruction of a captured outcome without components
indexed into a number. No program of the suite had either type: 2 of the
first 30 generated programs had the first, and 5 of 300 the second.
`vn2 fuzz --slice 2 --native` holds both.

**RB11.** Found on 23 November on reading the code, and closed. What a
boundary has in its care was destroyed only where the work fell off its end:
where the work ended by `■`, `□` or `↑`, it leaked ([E-Boundary]). It ends
with the scope of the work now. No test could observe a leak, so the native
harness counts allocations since 23 November: in the module it compiles,
every call of `malloc`, `realloc` and `free` goes through a function that
keeps the number of live allocations; the harness frees what it kept itself
(what a host was given by value, the places it lent to the entry control and
those its hosts lent); and a run that ends with a number other than zero
ends `undefined`, which no run of the oracle does. With the repair of this
finding taken out, run 10 of `cares` in `checked_faults_and_boundaries.core`
ends with one allocation live at `-O0` and at `-O2`.
`a_run_of_compiled_code_that_leaves_an_allocation_live_is_seen` takes the
release of a string out of the compiled text of the checked files and
requires that the count sees it: 40 of 116 runs. So [R4] is tested on every
run of compiled code. How much that tests is the number of allocations,
which `vn2 fuzz --native` prints: the 23,432 runs of 300 programs of slice 2
make 26,768, the programs of slice 1 none (they have no data), and the
checked files of the suite 78 (`erased_nested_ownership.core` none). The
first campaign with the count found RB12; the suites of slices 1 to 3 had
nothing live. Limits: the count is one number for a run, so a leak and a
second release in one run would cancel; it is the harness that counts, so a
program linked to a C host is not counted; and a value on the heap that a
host is given was rare in the generated programs of 23 November (one of the
first 60 of slice 2).

**RB12.** Found on 23 November by the allocation count of RB11, in the
program of seed 107 of slice 2, and closed. The layout that the erased
semantics and compiled code share (RB1) gave a name of the bodies around a
boundary the state in which the work left it on every history after the
boundary, also on those on which the boundary did not run; and after a loop
it asked only which `□` had ended the loop, so on a history on which the
loop did not run, a name that was moved before the loop counted as there. A
name that counts as moved is not destroyed, and one that counts as there is
destroyed again. `checked_skipped_bodies.core` has five controls for it.
Before the repair 5 of its 10 runs differed in compiled code, at both
levels: an allocation left live, which only the count sees; a connection
not released under a fault; one released twice; and two runs that the
allocator ended for a second free. The two with a connection differed in
the erased semantics too. No run of the 900 generated programs had shown
it there, where it needs a fault after the body that did not run. After a
boundary a name is now as the work left it where the site has its
alternative, and as it was before otherwise; after a loop, as the `□` left
it that ended the loop, and as it was before where none did ([R4] of the
core says so since).

**RB13.** Found on 24 November with the native driver of RO6 and RO11, and
closed. A call of an extern control passed an argument `&bool` or `&~bool`
as the address of a byte in a temporary that held a copy of the value. A
host that wrote behind it wrote the copy, which nobody read again, and a
borrow that it lent from it pointed at the temporary, so a write through
that borrow was lost too. The call passes the place itself now, as for
every other type behind a borrow: a `bool` is a byte that holds 0 or 1.
`flips` and `flips_through_a_slot` of `checked_host_places.core` hold it.

Held up: every construct of slices 1 to 3 lowers to typed IR with no
fallback to an interpreter; no `nsw`, `nuw`, `exact` or `inbounds` is
emitted; signedness and both widths agree; outside RB1, ownership is free of
leaks under an allocation tracker (the reviewer's then; the harness counts
since RB11, and found RB12).

## 8. Rails reader and formatter (`surface.rs`)

**RS1. 1 of the 17 corpus files reads** **(reproduced)**, and that one prints
its interpolated text literally. The reader has no `import`, no qualified
names, no generics or type arguments, no traits and no `implement`
(`surface.rs:3265-3294`, `1694-1733`). None of the 11 Rails test files is a
corpus program. With the modules flattened by hand and the generics written
out, every body of the library, the application and the parser reads.

**RS2.** The renaming of inner names ([U9]) is incomplete, and valid programs
are refused (`surface.rs:7956-8036`).

**RS3.** Text interpolation is read as literal text without a word, and the
formatter removes the escape `\{`.

**RS4. The formatter deletes comments**: 17 of 24 in one file
**(reproduced)**. With `--write` this loses source text. [G10] says comments
are kept.

**RS5.** `pub` on a function is dropped by the reader and removed by the
formatter.

**RS6.** The method form is refused when the module has a control with the
name of the built-in ([U12]).

**RS7.** `forward` and `■ ▾x` into a contract that is one outcome name are
refused ([G2], [U14]).

**RS8.** `forward` accepts neither a call in method form nor a built-in.

**RS9.** The layout stage matches prefixes of the raw text. `exits delta
f(x)` with vertical arms, and `;` or braces inside a string, break it.

**RS10.** Deep nesting overflows the stack: 460 parentheses, or 190 blocks.

**RS11.** Hidden names are ordinary identifiers; `_v0` can be read and can
collide. `■ auto` gives `u32` to a payload it cannot type.

**RS12.** The corpus and the specification disagree in places the reader
showed: `)` in column 1 against [Y1] (7 files), `run` and `next` used as
names against [G7b], and `prelude.txt` and `host.txt` are not Rails.
`resolve.rs:3582-3590` refuses a payload field with the name of a parameter
and cites [W7], which does not say so.

Held up: layout [Y1] to [Y10] with errors that name their clause (60
malformed inputs), the word form, paths and masks [U1] to [U5], the
elaboration of statements ([U6] to [U8], [U10], [U11], [U13]) on the
specification's worked example, and a formatter that is idempotent on 400
programs.

## 9. Records, and the state of each finding

**RD1.** The status statements called phases 2 to 4 complete for slices 1 to
3. They were corrected on 23 November with this document.

**RD2.** The second review of the task rules, which the author named as owed
at acceptance, was made by the implementation itself in the commit that
implemented tasks, and left no written review. Its changes to [W11],
[E-AwaitHost], [TK6] and [I10] read as correct and stay. An independent
review is still owed.

**RD3.** Section 12 of the core has no entry for any choice made while
implementing slices 2 to 4 (RO9). Sections 3, 4 and 7 of `oracle.md` describe
slice 1 only.

A finding is closed here with the date and the test that holds it.

| Finding | State |
| --- | --- |
| RD1 | Closed 23 November 2026 by the corrected status statements |
| RD2 | Closed 23 November 2026: the independent second review of the task rules is [task-review.md](task-review.md), made by a reviewer that had written neither the rules nor the implementation. It read the rules against the semantics and probed the oracle of slice 4. The repairs of 22 November hold up. Its findings RT1 to RT4 are open |
| RT1 to RT4 | Of 23 November 2026 ([task-review.md](task-review.md)). RT1: a cancelled `run` of an extern control can discard an argument that it cannot release, and [E-Run] does not say how an extern root asks the host. RT2: no rule withdraws the host operation that an owner waits for when a member's fault reaches the owner. RT3: nothing bounds `spawn`, so `count` can pass the range that [A3] gives it. RT4: the expansion of Theorem 4 loses the turn that `await` on a defined control gives up. The rules answer all four since 24 November 2026 (core section 12): [E-Run] and [TK4] for RT1, [E-MemberFault] for RT2, [E-Exhaust] for RT3 (which `push` and `insert` had too, for `len`), Theorem 4 for RT4; RT1 and RT3 by the author's choices of that day (core section 11). RT2 is closed on 24 November 2026: `runs_owner_waits` (`v2/tests/slice4/e_member_fault.core`) fails with the release taken out. RT4 is closed on 24 November 2026: `expand.rs` expanded only plain decisions already, and `slice_four_expansion_keeps_turns_and_runs_rt4` (`v2/tests/slice4.rs`) found and holds the case the theorem now leaves out, a control that runs an async one put into an async control. RT1 and RT3 are closed in the oracle and the erased semantics (`e_run.core`, `e_exhaust.core`). Since 25 November 2026 they are closed in the checker as well. For RT1, [TK4] refuses `bridge_lock` and `runs_finish_lock` (`e_run.core`), which give a lock by value to a run of a cancellable extern control and leave a run stuck. It accepts `bridge` and `runs_finish`, which give a lease. For RT3, a spawn adds one to the count with no condition, and [A3] bounds the count ([TK6]). `order` (`e_spawn_next.core`) proves `⊥` on the alternatives that the counts exclude, and `count_is_a_measure_that_spawn_and_await_next_change_tk6` holds the facts. Both tests are in `v2/tests/checker_slice4.rs`, and each fails when its part of the checker is taken out. Compiled code still lacks extern roots, member faults and capacity exhaustion (RB9) |
| RG1 | Closed 23 November 2026. `generate::valid` writes programs from their histories; `generated_valid_programs_run_to_an_end_and_reach_every_construct` and `the_checker_accepts_generated_valid_programs` (`v2/tests/harness.rs`) hold it, and `vn2 fuzz --seed 1 --count 300 --native` reports no finding. The mutation and backend tests run on generated programs too: `every_stuck_mutant_of_a_generated_program_is_rejected` (`v2/tests/checker.rs`) and `generated_valid_programs_agree_across_oracle_expansion_and_native_o0_o2` (`v2/tests/backend.rs`). The tests that run on `generate::template` name it |
| RC9 | Closed 23 November 2026. A certificate names its instances and holds no formula; the kernel makes the formula of each with its own matcher for the axiom list, and refuses a name that names none. `the_kernel_refuses_what_is_not_an_instance`, `the_kernel_grants_every_instance_that_the_search_makes` and `the_instances_of_the_arithmetic_axioms_hold_for_the_real_operations` (`v2/tests/kernel.rs`) hold it, with `certificate_kernel_rejects_corrupted_proofs_v1_to_v5` (`v2/tests/checker.rs`). The instances of [A3] to [A6] are held against real values since 24 November, as the last of these tests does for [A1], [A2] and [A7] to [A9]: `the_instances_of_the_data_axioms_hold_for_real_values`, `a_wrong_value_makes_the_instance_of_its_axiom_false` (`v2/tests/kernel.rs`) and `the_axioms_of_the_data_are_proved_and_what_they_do_not_say_is_not` (`v2/tests/checker_slice2.rs`) |
| RC10 | Closed 23 November 2026. The checker gives the kernel the goal, the premises, the terms and the rows (`kernel::Query`); the certificate names premises by their position in the checker's lists. The kernel has its own arithmetic and its own diagram, and uses of the crate the integers, the diagram package and the data of `terms`. `certificate_kernel_rejects_corrupted_proofs_v1_to_v5` holds it: the same certificate is refused for another goal, and so is a premise that the checker did not state. `CheckedProgram::revalidate` validates every certificate of a check again with a kernel that saw nothing of it, and the tests of the three slices call it |
| RC11 | Closed 23 November 2026: every question the checker asks goes through one function that validates a yes in the kernel and lists the certificate, with the clause `N1` for the feasibility of a history. `an_infeasible_history_is_ruled_out_by_a_validated_certificate` (`v2/tests/checker.rs`) holds it |
| RC12 | Closed 23 November 2026. The theory check (`v2/src/lia.rs`) gives a proof that the kernel validates (with the Split step of [V3]), a model that is evaluated, or the counted limit, which the checker reports with the clause `J6`. It is complete without bounds: where its splits do not end, the Omega test (`v2/src/lia/omega.rs`) decides the rows, by changes of variable in an equality without a unit coefficient and by the splinters of a variable that no side bounds with units, in the steps of [V3] as they are. `the_procedure_is_exact_on_integers_and_gives_up_only_at_a_counted_limit` and `a_condition_without_a_bound_is_decided_by_the_omega_test` (`v2/tests/checker.rs`) hold it: the second is a precondition on the difference of two parameters, whose answer was the limit. The tests of `lia.rs` compare 3,000 sets of rows with a search of every point, and those of `lia/omega.rs` compare the Omega test alone with it on 3,000 sets of rows in a box, 1,500 without a bound on any variable and 1,500 thin bands that only splinters refute; the kernel validates every proof. The limit remains for a search that is too long: the number of splinters grows with the coefficients. One theory check in the 1,252,564 of the mutant campaign goes on to the Omega test (the program of `a_condition_on_remainders_and_products_is_decided`), and none of the 300 generated programs or of the programs of the three slices |
| RC13 | Closed 23 November 2026. `vn2 check --certificates` writes a text that holds the tables of each body and, for every question, the goal and the premises as formulas, the names of the instances and the lemmas with their proofs (`v2/src/certificate.rs`; the format is in section 10 of the [oracle document](oracle.md)). `vn2 validate` reads a text and validates every certificate from it alone. `the_text_of_the_surface_programs_reads_back_and_validates`, `the_text_of_generated_programs_reads_back_and_validates`, `a_text_written_by_hand_validates`, `a_text_that_was_changed_is_refused`, `the_reader_refuses_what_is_not_a_text` and `a_proof_as_deep_as_the_search_goes_is_read_and_validated` (`v2/tests/certificate.rs`) hold it. Not there: a second checker by another hand; the reader is in the crate and uses its kernel |
| RC16 | Closed: 23 November 2026 for the time of a check, 24 November for the size of `check_body_inner`. The data kernel of the slice 2 backend test took 2,267 theory checks, and its expansion 2,538, in which the exchanges of the simplex method wrote 2.5 and 29.7 million entries of tableaus. They take 581 and 583 theory checks and write 120,731 and 5,333 entries; a check of either takes under half a second where it took 2.4 and 8.9, and the 300 generated programs take 5 seconds where they took 26. Four changes: the theory check looks for a model along its splits before it adds rounded sums, which had made 10,149 rows of 25; a model is asked only for the rows that a formula reads; every premise and every instance that a model fails is added at once; and the tables of the diagram have a hasher for small keys. The mutant campaign of 25 programs gives the numbers it gave before, mutant for mutant. While the theory check was not complete, adding the instances with the premises lost one valid mutant of the 5,403 to the limit of [J6], and they were added only for a model that failed no premise; since the Omega test decides that mutant (RC12), they are added together, which takes a fifth fewer theory checks over the campaign. `a_condition_on_remainders_and_products_is_decided` holds that program. `the_search_stays_small_on_the_kernel_program_of_slice_two` (`v2/tests/checker.rs`) holds it by counts, which `vn2 check --counts` prints, and `a_model_behind_a_refuted_branch_is_found_in_the_first_tableau` (`v2/src/lia.rs`) holds the first change. `check_body_inner` had grown to one function of 1,686 lines. Since 24 November it is the loop over the statements of a body, 58 lines: it makes the `Point` of each statement (its line, its selector, the histories that run it and the names they see), gives the statement to the method of its command (`check_bind`, `check_decide`, `check_loop`, `check_boundary` and the others), and keeps the histories that go on by [K3], whose three cases are the type `Flow`. There are 47 methods where there were two, the longest of 113 lines; what a call asks is one method for a capture and for a decision (`check_call`), and a leave of a loop is a `Leave` with a name for each part. The text of each rule was moved by a script and not retyped, and nothing that the checker does changed: the whole gate gives what it gave before, file for file, which is the certificates of the surface suites (450), the verdict on every generated program and on every mutant of both campaigns (6,851 of slice 1, 13,073 of slice 2), and the counts of the search of every campaign, number for number |
| RC15 | Partly. Since 23 November tampering is tested on the instances, the premises and the goal of a certificate as well as on the steps of a lemma (`v2/tests/checker.rs`, `v2/tests/kernel.rs`). Since 24 November the checker is compared with the oracle for slice 2: control by control on the rule files of the data and on `facts_data.core` (`v2/tests/checker_slice2.rs`), and by `vn2 fuzz --slice 2` on generated programs and their mutants. Open: no test compares the two for slice 3 |
| RC17 | Closed 23 November 2026 for soundness: the kernel grants a range, the planes of a product and the constructor of a variant value only for a term that the checker wrote, and the search gives a term that it adds no range either. `a_term_that_the_search_added_has_no_range` (`v2/tests/kernel.rs`) holds it. Closed 24 November 2026 for the rest: the range that the element lacks cannot change an answer (the note in section 8 of the [fact logic](facts.md)), and a literal is a term of its type, so that every term has one sort; `a_literal_at_two_types_is_two_terms` (`v2/tests/kernel.rs`) |
| RC18 | Closed 23 November 2026: the search pairs constructor terms only when they have one number of arguments, and the kernel refuses the pair otherwise. `the_kernel_grants_every_instance_that_the_search_makes` and `the_kernel_refuses_what_is_not_an_instance` hold it |
| RC19 | Closed 23 November 2026: the checker keeps its names in ordered tables. `a_check_is_the_same_every_time` (`v2/tests/checker.rs`) checks 30 programs twice, the second time on another thread, and requires one certificate text (2,136 certificates) and one set of counts |
| RO1 | Closed 23 November 2026. A fault ends the scopes of an activation innermost first (`Machine::unwind` in `oracle.rs`, `trigger_unwind` in `erased.rs`), so a lexical boundary inside the body of a named boundary takes it first. The run `supervises` of `v2/tests/slice2/lexical_boundaries.core` holds it, with the trace of the finding |
| RO3 | Closed 23 November 2026. `resolve` refuses the ends that [E-Contingency] forbids, by [F5] and [F6] as the [core](core.md) lists them since that day: 22 files `v2/tests/slice2/reject_*.core`, one for each requirement. `terminate n` has a literal status, belongs to the entry control, which nothing invokes, ends its scopes by [E-Scope], and gives the end `terminated n` and no outcome; inside a loop of the contingency it ends the execution where it panicked (`ends_execution`, and `terminate_abandons` in `lexical_boundaries_stuck.core`). `□` in the body of a boundary, which `resolve` refused, leaves the loop around it (`leaves_inside`) |
| RO4 | Closed 23 November 2026. `recover ↑ ℓ` restarts the loop with its own parameters, read as operands, and no copy of them is kept; the body of the boundary does not mention them ([F5], `reject_f5_recover_parameter_in_work.core`). The runs `retries` and `recovers_outer` hold it, with `recover_without_parameter`, `recover_breaks_invariant` and `recover_abandons` for its stuck states. The backend restored a copy taken when the loop was first entered; its parameters stay in their slots now, and the twelve runs of `lexical_boundaries.core` agree with the oracle in compiled code |
| RC14 | Closed 23 November 2026 with RO3: the terminators of a contingency are requirements of form, and its end without one is `X1` by coverage ([K7]). The `reject` files hold it |
| RO2 | Closed 23 November 2026. An activation keeps the borrows it was passed, and the condition of an alternative reads the value at completion through them ([E-Formula], which says so since that day). `v2/tests/slice3/exit_conditions.core` holds it: the two controls of the finding, one that passes its parameter on with a true condition and one with a false one, beside the same two with a reborrow |
| RO6 | Closed 23 November 2026 for the two semantics and their hosts. A host names a place within one of its arguments and the step makes the reborrow ([E-Extern]); in a directive the place is written `&x…` or `&~x…`. `v2/tests/slice3/host_borrows.core` holds it with 11 runs that end and 10 violations, one for each way an answer can fail to be such a reborrow, and `the_seeded_host_answers_borrowed_payloads_with_places_within_its_arguments` (`v2/tests/slice3.rs`) for the seeded host. Closed for compiled code on 24 November 2026: a borrow in a payload points at the place the host names. `hosts_that_lend_from_and_write_behind_arguments_run_natively_ro6_ro11` (`v2/tests/backend_slice3.rs`) compiles the runs of the controls that the checker accepts in `checked_host_places.core`, `host_borrows.core` and `e_extern_writes.core` (28 runs; 15 with a host that lends) at both widths, at `-O0` and `-O2`, and compares them with the oracle and the erased semantics, end, trace and allocations; with the place replaced by a null pointer it fails. `slice_three_core_programs_agree_natively` names places now and is compared with the oracle too. ASan and `leaks` by hand: 73 runs, no error, no leak |
| RO8 | Closed 23 November 2026. A resource type that occurs at any depth of a parameter or a payload makes a control impure (`Program::resource_occurs`), and the checker asks `control_is_pure`, which also looks for `run` in what the control reaches ([I10]). `v2/tests/slice2/pure_operations.core` holds it: two calls that return a resource inside a struct, and inside a variant, give two resources, and a pure control that answers in two ways is a violation |
| RO9 | Closed 23 November 2026. The contract of `insert` is that of the corpus prelude, `replaced {previous: v}`; the listing of section 3 of the [reference model](references.md) and the core form of its example 6.3 were short of the payload and are corrected (its section 16). The example runs as `touch` in `v2/tests/slice3/builtin_operands.core`. Section 6.6 of the [core](core.md) names the built-in operations, and the row X2 of its section 6.10 the clauses of the labels `X2 E-Field`, `X2 E-Index` and `X2 E-Supervise`, with an entry in its section 12; `X5 E-Resource` is a check of the oracle on its own table. `done terminated` went with RO3 |
| RO10 | Closed 23 November 2026. The operand of a built-in follows the rule of any operand for a parameter of that type. `reject_c1_push_shared.core`, `reject_c1_push_by_value.core`, `reject_c1_get_exclusive.core` and `reject_c1_remove_key_exclusive.core` (`v2/tests/slice2/`) hold the refusals, and `builtin_operands.core` (`v2/tests/slice3/`) the runs: `&~p` lends, and a name of type `&~` passes the borrow itself, after which a second use of it is `X2` |
| RO11 | Closed 24 November 2026 for the two semantics and their hosts. A host leaves a value behind an argument lent exclusively, and the step writes it through the argument's tag ([E-Extern], [E-Host]). `v2/tests/slice3/e_extern_writes.core` holds it with 13 runs: the write is what the condition reads, through a borrow name as well, a struct written whole or left, the write ends a borrow made through the argument before the call (`X4 B1`, with that cause in `DEATHS` of `v2/tests/slice3.rs`), the borrow of the payload is made after it, and six violations (a condition false after the write or without one, a value of the wrong type, a write behind an argument lent shared, in two controls, a change to a token). Closed for compiled code on 24 November 2026, with RO6: the stub of a host writes behind the argument, releasing what it replaces, after it prints the event and before it makes the borrows of the payload, and `script::native_runs` keeps the runs whose host writes. The same test holds it with 10 such runs; each of these fails it: no write behind a `bool` lent to a host (RB13), no release of the old value, the event printed after the write, and the borrows of the payload made before it. The test of the stand-in, `runs_whose_host_writes_are_left_out_of_compiled_code_ro11`, is gone with it |
| RO12 | Closed 24 November 2026. [E-Unwind] of the core gives the order of release under a fault (the names of a body in the reverse of the order in which its text first binds them, the parts of a value from the first), and the oracle follows it. `v2/tests/slice2/checked_release_order.core` holds it with ten runs in the oracle, the erased semantics and compiled code at `-O0` and `-O2`; one of them differed before |
| RO13 | Open, found on 24 November 2026: `outcome⟨f⟩` for a control `f` is refused in a field of a struct or variant declaration and in the signature of a control that stands before `f` |
| RO14 | Closed 24 November 2026. Where a borrow type is expected the reader takes `&p`, `&~p`, or a name or a field of a view of that type, and a function a place ([C1] and [W5a] of the [core](core.md), section 12). Eight files `v2/tests/slice3/reject_c1_*.core` hold the refusals: a value, a constructor and a literal key for a borrow parameter, a name of exclusive borrow type for a shared one, a value in a bind of borrow type and in a field of a view, `&p` and a constructor for a function |
| RO15 | Closed 24 November 2026. A formula reads through a borrow only while its tag is alive ([E-Formula], row X4 of section 6.10 of the [core](core.md)). `formula_through_dead`, `formula_through_gone` and `condition_through_dead` in `v2/tests/slice3/b1_access.core`; `formula_is_no_access` holds that a formula still changes no tag |
| RO16 | Closed 24 November 2026. A function reads a place given for a borrow parameter where it is and makes no borrow ([E-Fn]). `reads_in_place` and `function_read_ends_exclusive` in `v2/tests/slice3/e_borrow_operands.core`; the death of the second is named as a read |
| RO17 | Closed 24 November 2026. A call and an exit read a borrow for a formula only where the signature mentions it. `passes_dead` in `v2/tests/slice3/b1_access.core`: a dead borrow passed to a control that does not read it ends, and one passed to a control that does is stuck in the callee |
| RO18 | Closed 24 November 2026. The operand of a decision or a capture for a parameter `&~τ` is `&~p` or a name of that type, with or without the move mark ([C1]). `reject_c1_place_for_exclusive_parameter.core` and `reject_c1_move_mark_on_shared_borrow.core` (`v2/tests/slice3/`); the program of RC27 with `▾` is read and accepted |
| RC1 | Closed 24 November 2026. A loop renames at its entry every place its body lends exclusively ([I9]), a borrow bound in the body among them. `a_loop_renames_what_its_body_lends_exclusively_i9` (`v2/tests/checker_slice3.rs`): the six programs of the review (an assertion on a later turn, an overflow, an index past the end, a write through a field of a view, the precondition of a call through the borrow, an assertion after the loop), each stuck in the oracle and refused ([P1], [P3], [P5]) where it was accepted with validated certificates, and three of them with an invariant that says what the borrow writes, which run to their end and are accepted |
| RC2 | Closed 23 November 2026. A captured operation writes its `&~` operand at the capture: the place gets a fresh name there, and the conditions of the alternative relate the collection before and after when the outcome is decided ([I12] of the [fact logic](facts.md), which says so since that day). `a_captured_operation_writes_where_it_is_captured_i12_b5` (`v2/tests/checker_slice2.rs`) holds it with the program of the finding and three more that are stuck in the oracle and refused, and four that end and are accepted with what the alternative says of the length |
| RC3 | Closed 23 November 2026. The record of a capture goes with the value: an assignment to the name drops it, a bind or an assignment of a captured outcome carries it to the new name, and a loop that assigns the name drops it at its entry. `the_facts_of_a_capture_go_with_the_captured_value_i12` holds it, with a program that is stuck and refused for the assignment and one for the loop |
| RC4 | Closed 23 November 2026. The checker records the ownership of every name at each statement of `B₁` that may fault, and checks the terminators of `B₂` once for each such state, with the names around the boundary as they were then: [O5] at `terminate n`, and at `recover ↑ ℓ` [O2] for the parameters it reads, [O5] and [O6]. A statement of `B₂` that may fault passes those states on to the boundary around it, and [F2] and [F6] are required of the names around a boundary where its `B₁` faults ([F5] of the [core](core.md) says so since that day). `a_contingency_ends_in_the_state_of_the_fault_f5_o5`, `a_fault_of_an_inner_contingency_is_a_fault_of_the_work_around_it_f5`, `recover_reads_the_parameters_and_ends_the_iteration_o2_o5_o6` and `the_names_around_a_boundary_are_judged_where_the_work_faults_f2_f6` (`v2/tests/checker_slice2.rs`): 13 programs, each run in the oracle as well; the checker of before refused the valid ones and accepted the stuck ones |
| RC5 | Closed 23 November 2026. [E-Boundary] answers the question: what the boundary has in its care ends with the scope of `B₁`, so a terminator that ends that scope, and the end of `B₁`, are refused by [O5] where a value in its care holds an obligation. `what_a_boundary_has_in_its_care_ends_with_its_work_o5` (`v2/tests/checker_slice2.rs`): both programs of the oracle suite are refused, and a work that always faults, whose contingency consumes what it was given, is accepted |
| RC6 | Closed 23 November 2026. [E-Supervise] and [F6] answer the question: nothing encloses a statement of the contingency of a named boundary, so a call there that may fault is refused by [F1]; `fault` and `escalate` are its ends, and the contingency of a lexical boundary may call what faults where the control permits it. `nothing_encloses_the_contingency_of_a_named_boundary_f1_f6` |
| RC7 | Closed 23 November 2026. The move mark of the core text stands only on an expression that is consumed, which its position decides ([E-Var]); on an operand of an operator, an argument of a function, the base of a field or an index or the place of `len` or `clone` it is refused when the text is resolved, by [O3]: a read moves nothing. `a_move_mark_stands_on_what_is_consumed_o3` (`v2/tests/checker_slice2.rs`) refuses three such forms and accepts and runs the mark on a bind, a field of a constructor and an element of a vector |
| RC8 | Closed 23 November 2026. A component has the declared interval of its type only as a component of a value term, as [A9] of the [fact logic](facts.md) has it; read out of a constructor at any depth it is the term written there and has none. `a_component_read_out_of_a_constructor_has_no_declared_interval_a9`: a formula that holds for every `u32` and fails for `a + 1` at the end of the range is stuck in the oracle and refused, and the same formula of a component of a name is accepted |
| RC20 | Closed 23 November 2026. The effects of a named boundary include those of the boundaries its `B₁` supervises (`resolve.rs`), as [F6] says of what supervises. `the_effects_of_a_supervised_boundary_count_toward_what_supervises_f3_f6`: a boundary that supervises one that writes is accepted, and the control that supervises it must allow the effect |
| RC21 | Closed 23 November 2026. The statements of `B₂` have the histories of the statements of `B₁` that may fault: for a lexical boundary the disjunction of their reach, and for a named boundary, whose `B₂` is checked in a diagram of its own, all or none by whether one of them can happen. [F5] of the [core](core.md) says so now (section 12). `a_contingency_runs_on_the_histories_that_fault_f5_f6_p6` (`v2/tests/checker_slice2.rs`): five programs, each run in the oracle as well. |
| RC22 | Closed 24 November 2026. A model of a candidate gives a content one number (`v2/src/facts/completion.rs`), the theory check asks the Omega test before its splits take turns and looks for a model after every round of rounded sums, and a node of a diagram is a step of [J6] and a count. The five programs are in `v2/tests/kernels/`. Tests: `the_diagram_stays_small_on_programs_with_constructor_terms` (four programs: at most 500 theory checks and 150,000 nodes each, where one question had passed 540,000 nodes), `rows_that_keep_the_splits_are_decided_by_the_omega_test` (8.8 million entries where there were 81.8 million) and `the_nodes_of_a_diagram_are_steps_j6` in `v2/tests/checker.rs`; `constructor_terms_are_one_value_exactly_where_their_contents_are_a4_m1` in `v2/tests/checker_slice2.rs` (one program accepted, two stuck and rejected). All 900 generated programs of slice 2 are answered, and both mutant campaigns give the answers they gave before, mutant for mutant: 6,851 mutants of 25 programs of slice 1 and 13,073 of 40 of slice 2 |
| RC23 | Closed 23 November 2026. On the histories that did not see the capture, a decision on a captured outcome adds the conditions of the captured operation over fresh names, each of the type of its parameter; `old(p)` is another name than `p` for an `&~` parameter alone ([I12], section 14 of the [fact logic](facts.md)). `a_captured_outcome_keeps_its_conditions_where_the_capture_is_not_visible_i12` (`v2/tests/checker_slice2.rs`): through the payload of a loop, as the parameter of a loop, with one fresh name in two conjuncts of a condition; a condition that says less than the exit claims is stuck in the oracle and refused, and what a condition says of an argument is not known of the name that was the argument |
| RC24 | Closed 24 November 2026. A name in the care of a boundary is, in the contingency, the constant expression that it was ([I3]). Test: `a_name_in_the_care_of_a_boundary_is_the_constant_it_was_i3` in `v2/tests/checker_slice2.rs` (a program that was refused, and one that is stuck and rejected); seed 781 of `vn2 fuzz --slice 2` |
| RC25 | Closed 24 November 2026. A counterexample gives no number for a name of a data type, and its length where the model has one ([M2]). `a_counterexample_gives_no_number_for_a_name_of_a_data_type_m2` (`v2/tests/checker_slice2.rs`) |
| RC27 | Closed 24 November 2026. An assignment through a name of exclusive borrow type asks [O2] of the name ([E-Assign]). `a_borrow_name_that_moved_is_not_written_through_o2` (`v2/tests/checker_slice3.rs`): three programs stuck in the oracle and refused (the name moved by a bind, by a bind with the move mark, by a call), one with the move mark accepted; and `old_name_is_moved` of the rule files |
| RC28 | Closed 24 November 2026. The arguments of a function applied in an operand are accesses while the borrows of the operands before them are live ([L2]). `a_function_in_an_operand_reads_while_the_statement_lends_l2` (`v2/tests/checker_slice3.rs`): the program above stuck in the oracle and refused, and the function applied to another name accepted; accepted before |
| RC29 | Closed 24 November 2026. A borrow in the operand of `len` is used where `len` is applied ([L2]). `a_borrow_in_the_operand_of_len_is_not_used_after_it_l2` (`v2/tests/checker_slice3.rs`): `len(&v)` in the payload of an exit, beside a move of `v`, and in the payload of a leave, each run in the oracle and accepted; refused before |
| RC30 | Closed 24 November 2026. At `recover ↑ ℓ` a name bound in a body within the restarted loop is not live after the restart ([L2a]). `a_name_bound_within_the_restarted_loop_is_not_live_after_recover_l2a` (`v2/tests/checker_slice3.rs`): the program above runs to its end in the oracle and is accepted (refused before), and one that carries the borrow on through a parameter of the loop is stuck (`X4 B1`) and refused by [L3]; the test fails with the old condition |
| RC31 | Closed on 25 November 2026. Held by `a_task_set_holds_shared_and_exclusive_loans_until_drained_tk3`, `an_inner_iteration_can_lend_to_a_set_carried_by_an_outer_loop_tk3`, and the scope, availability, payload and exclusive-write tests in `v2/tests/checker_slice4.rs` |
| RC32 | Open since 25 November 2026, for the author. [TK4]'s condition on the payload of an awaited `extern async control` makes no checked program safer: a completion of the host leaves one task ready, and it takes the next turn. `the_payload_of_an_awaited_extern_control_is_fault_releasable_tk4` (`v2/tests/checker_slice4.rs`) holds the condition as the rules give it |
| RC33 | Closed on 25 November 2026. `exclusive_call_operands_update_the_same_record_rc33` and `a_capture_keeps_both_exclusive_postconditions_rc33` in `v2/tests/checker_slice3.rs` hold the caller’s field values against the oracle. See section 5 |
| RC26 | Open. The checker knows that a value is of one of the constructors of its type only where a decision took the value apart, and does not know that a struct without fields has one value; [J1] entails both. Nothing wrong is accepted. The three statements are in the table `LEFT_OUT` of `v2/tests/checker_slice2.rs`, which holds the present answers. Whether the crate or [J1] changes is a choice of the author's |
| RO5 | Closed 24 November 2026 for tasks: the erased semantics stopped a task that is ready by the formulas of the statement it stood before, which count that statement's arguments as moved, and so missed the release of a lease the statement would give away (the review's probe `r6_repo_suite_other_schedule.core`); the same where the fault of a member arrives at an owner that is ready. `erased::Layout.before_at` holds the formulas before each statement's arguments move. Runs `runs_stops_keeper` (`v2/tests/slice4/e_stop.core`, the probe's schedule) and `runs_owner_ready` (`e_member_fault.core`) differed before; `slice_four_core_conforms_and_matches_erased`. Closed 23 November 2026 for one task. `the_erased_semantics_follows_ownership_through_nested_bodies` (`v2/tests/slice2.rs`) runs `v2/tests/slice2/erased_nested_ownership.core`: nine controls in which a loop, the work of a boundary or a loop inside the work consumes or assigns a name of the body around it before a fault, 12 runs, each with the trace of the oracle and each compared with the erased semantics; the checker accepts the file. Ten of the 12 runs differed before. The campaigns of `vn2 fuzz --slice 2` hold it on generated programs |
| RG3 | Closed 23 November 2026 for the generator and the differential fuzzing of slice 2 (section 3); the mutations of slice 2 are open. `generated_programs_with_data_run_to_an_end_and_reach_the_data_constructs` (`v2/tests/harness.rs`) requires every construct of the slice in 240 programs, and runs that end in a fault and with `terminate n` |
| RG4 | Closed 23 November 2026. Calls nest eight deep in one expression and no deeper (`MAX_CALLS`, `v2/src/generate/valid.rs`). `a_generated_expression_ends_where_calls_nest` (`v2/tests/harness.rs`) writes the program of the seed, which without the bound overflows the stack. Of the first 600 programs of slice 1, 599 are what they were; seed 511, whose expressions had nested deeper while they were written, gives another program |
| RG5 | Closed 23 November 2026. An operand is written over the names as the operands before it left them (`Generator::arguments`, the initial values of `make_loop`, the arguments of `↑`). `generated_programs_with_data_run_to_an_end_and_reach_the_data_constructs` (`v2/tests/harness.rs`), whose 160 seeds have no stuck run, holds it with the campaigns of section 3 |
| RG6 | Closed 23 November 2026. The resources of an entry are numbered from 1,000,000 (`ENTRY_RESOURCES`, `v2/src/generate.rs`). The same test holds it: among its 240 programs are controls that take a resource and call an operation that opens one |
| RG7 | Closed 24 November 2026. A value of an outcome type that an entry or a host gives is one that its operation gives ([E-Host] and section 8 of the core), and the generator writes parameters and payload fields of outcome types. Tests: `a_drawn_value_of_an_outcome_type_is_one_that_its_operation_gives_i12` in `v2/tests/harness.rs`; `vn2 fuzz --slice 2`, also with `--native` |
| RG8 | Closed 24 November 2026. `generated_programs_with_borrows_run_to_an_end_and_reach_the_borrow_constructs` (`v2/tests/harness.rs`) runs seed 204 among its 300 programs, and fails without the fix |
| RB1 | Closed 23 November 2026. `checked_core_programs_of_slice_two_run_natively_as_the_oracle_does` (`v2/tests/backend_slice2.rs`) compiles the files of `v2/tests/slice2/` that the checker accepts whole, `erased_nested_ownership.core` and `checked_faults_and_boundaries.core`, and compares the 36 runs of their directives with the oracle at `-O0` and `-O2`, end and trace; 19 of them differed before. `vn2 fuzz --slice 2 --native` gave no difference on 300 programs |
| RB2 | Closed 23 November 2026 (with RO4). The controls `retries` and `collects` of `checked_faults_and_boundaries.core`, in the same test |
| RB3 | Closed 23 November 2026. The controls `passes_on`, `keeps_message`, `faults_again`, `retries_with_text` and `supervises` of the same file, whose messages own memory, in the same test |
| RB10 | Closed 23 November 2026. `vn2 fuzz --slice 2 --native`: the programs of seeds 6, 11, 61, 116, 141, 201 and 259 did not compile |
| RB11 | Closed 23 November 2026. What a boundary has in its care ends with the scope of its work, and the native harness counts allocations, so a leak is a difference from the oracle in every compiled run. Tests: `checked_core_programs_of_slice_two_run_natively_as_the_oracle_does` (run 10 of `cares` had one allocation live without the repair) and `a_run_of_compiled_code_that_leaves_an_allocation_live_is_seen` in `v2/tests/backend_slice2.rs`; `vn2 fuzz --native` |
| RB12 | Closed 23 November 2026. After a boundary or a loop that did not run, a name of the bodies around it is as it was before. Tests: `v2/tests/slice2/checked_skipped_bodies.core` in the oracle, the erased semantics (2 of 10 runs differed) and compiled code (`checked_core_programs_of_slice_two_run_natively_as_the_oracle_does`, 5 of 10); seed 107 of `vn2 fuzz --slice 2 --native` |
| RB13 | Closed 24 November 2026. An argument `&bool` of an extern control is passed as the place itself, not as a copy in a temporary. `flips` and `flips_through_a_slot` of `v2/tests/slice3/checked_host_places.core`, in `hosts_that_lend_from_and_write_behind_arguments_run_natively_ro6_ro11`: both differ with the temporary |
| RS2 | Closed 23 November 2026. The renaming of [U9] reaches the name of a capture, the names of an unpacking, the root and the indexes of an assigned place, the parameters of an inner loop, the set of `await next`, and what a boundary captures. `u9_renames_inner_binders_and_the_places_that_use_them` (`v2/tests/surface.rs`) runs the three files of `v2/tests/loop_names/` in both semantics and refuses a free name that is spelled like a renamed one |
| RS4 | Closed 23 November 2026. The formatter prints from a tree that holds no comment at the end of a line, so it now notes the source line of each thing it prints and puts the comments of the source back between those lines (`FormatLines` in `surface.rs`); a comment between the two bodies of a named boundary in the plain form goes to the end of the first, since [Y12] makes the bodies touch. `g10_keeps_comments_in_order_through_layout_changes` (the 24 comments of `v2/tests/format/comments.rails` and the 9 of `plain_comments.rails`, which changes from braces to rails), `g10_keeps_comments_on_folded_lines_and_delimiters`, `g10_keeps_plain_boundary_comments_next_to_the_work_body`, and `g10_keeps_a_comment_in_every_position`, which puts a comment after every line and before every line of every Rails file of the suite, one at a time, and requires that the text is refused or every comment is kept in order by a formatter that is the identity on its output |
| RS7, RS8 | Closed 23 November 2026. `forward` takes any call that a decision takes (a control, the method form, a built-in), and the entries of a contract that is one outcome name are those of the declaration ([G2]), for `forward` and for `■ ▾x`. `u14_forwards_named_contracts_and_builtin_calls` (`v2/tests/surface.rs`) runs both; a payload of another type is refused by [U14] and a built-in with the wrong number of operands by [C1] |
| RS9 | Closed 23 November 2026. The layout stage finds `;`, braces, `:`, arrows and comment marks outside text literals only (one scan, `unquoted`), and recognizes a decision by its words and not by a prefix of the line. `layout_reads_decision_tokens_and_leaves_string_contents_alone` (`v2/tests/surface.rs`) holds it; a decision whose last arm is missing is still refused by [Y7] |
| RS11 | Closed 23 November 2026. A name that elaboration makes equals no identifier of the source ([U9] says a hidden name equals no name of the program), so a parameter may be called `_v0` and a read of an unbound `_v0` stays unbound. `■ auto` gives `u32` to a payload only when every exit gives an integer literal for it, as [G3] says, and refuses a payload that nothing types, or a literal that does not fit, by [G3]. `hidden_payload_names_are_inaccessible_and_auto_needs_type_evidence` (`v2/tests/surface.rs`) |
| RS3, RS5, RS6, RS10 | Open. RS3 waits for the library operation that interpolation is defined by. RS5 and RS6 reach past the reader: the core form of a function has no visibility, and `resolve` looks for a control of the module before a built-in (`extern control pop() ■ unrelated` makes `xs.pop()` on a vector an error of [U12]); both are taken up with RS1. RS10: measured on 23 November, a level of blocks costs the reader about 42 KiB of stack in a debug build and a level of an expression about 18 KiB, so a limit that fits any caller's stack would refuse ordinary programs; the reader is to count the depth, refuse above a limit that the surface document states, and bring a stack of its own for that limit |
| All others | Open |

## 10. The course

Approved by the author on 23 November 2026, in this order:

1. Withdraw the claims of completion and state what is verified (this
   document).
2. A real generator for slice 1, then fuzz the checker and the backend with
   it, and repair what that finds.
3. Bring the kernel and the decision procedure to the fact logic: validate
   instances (RC9, RC10), validate every proof the checker relies on (RC11),
   and report a counted limit where the procedure now panics (RC12).
4. Requalify slices 2, 3 and 4 in order, each with tests for every clause as
   slice 1 has, and repair the findings above. The fault-boundary rules of
   the oracle come first (RO1, RO3, RO4).
5. Extend the reader to imports, generics and traits so that the corpus runs
   (RS1), and repair the formatter (RS4). The formatter keeps comments
   since 23 November 2026, and RS2, RS7 to RS9 and RS11 are closed with it
   (section 9); the reader of the corpus is still owed.
6. An independent second review of the task rules (RD2). Made on 23
   November 2026: [task-review.md](task-review.md). Its findings are taken
   up with slice 4.
