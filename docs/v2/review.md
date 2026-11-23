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
| Oracle: accepting and rejecting test for each clause | Met: 41 files, 126 runs, 12 rules, 15 stuck states, 9 refusals | Partly: 42 files, 68 runs, 12 stuck labels. Requalified since 23 November: the fault-boundary rules (RO1, RO3, RO4), pure operations (RO8) and the operands and contracts of the built-in operations (RO9, RO10). Open: a test for each clause of the data rules, as the fault boundaries have | No: 5 files, 55 runs. Three of the files are of 23 November, with the findings they close (RO2, RO6, RO10); the two before them reach one stuck label, `X4 B1`, which the oracle raises in 17 places, and the test asserts counts of runs. A host cannot write through an `&~` argument (RO11) | No: 2 files; the test asserts no stuck state; one run varies the order of turns |
| Checker: accepting and rejecting test for each clause | Met | Partly; unsound (RC4 to RC6). RC2 and RC3 are closed since 23 November, with tests that run each program in the oracle as well | Partly: the worked examples of the reference model; unsound (RC1); the loan checker was tested from outside only | No checker |
| Generator reaches every construct of the slice (phase 2 exit) | Met since 23 November (section 9, RG1) | No generator | No generator | No generator |
| Oracle against erased semantics | 62 runs of the suite and 11,728 runs of 300 generated programs | The erased interpreter is a transcription of the oracle (RO7) and wrong under faults (RO5) | As slice 2 | As slice 2 |
| Mutations rejected at the rate the author sets (phase 3 exit) | Seven kinds on generated programs since 23 November. Every mutant for which a stuck run was found is rejected: 761 of 5,403 mutants of 25 programs, and 72 in the suite. The checker accepts 4,066 for which none was found. The rate is not set | None | None | None |
| No generated checked program is stuck over a long campaign (phase 3 exit) | No long campaign yet. The checker accepts all of 300 generated programs, none of which is stuck in 11,728 runs, and 5,403 mutants of 25 of them gave none that was accepted and stuck | None | None | None |
| Compiled code agrees with the oracle on generated programs (phase 4 exit) | Since 23 November: 300 generated programs at both widths of `usize`, at `-O0` and `-O2`, 23,456 runs with no difference (`vn2 fuzz --native`); six of them with their expansions in the suite. No longer campaign yet | None; double free (RB1) | None | No backend; `emit-llvm` panics (RB9) |
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
slice 1 only.

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
of 1,582 lines.

**RC17. The type of an element that only a frame instance speaks of was
guessed.** Found on 23 November, while the kernel's matcher was written. For
an update `t[i ↦ e]` and an index `j`, the instance of [A6] speaks of `t[j]`.
The search gave that term the element type of another vector on which `j` is
an index, when the sorts of the two vectors were equal or when one of them was
not known to the solver, and with the type its range. An element of a vector
of `u32` could so be given the range of `u8`. No wrong acceptance was
reproduced.

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

**RO6.** No host can answer an extern control whose payload is borrowed.
Every such call ends in `violation`.

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

The suites:

| Slice | Files | Runs | Stuck labels reached | What the test asserts |
| --- | ---: | ---: | --- | --- |
| 1 | 41 | 126 | 15 | 12 rules, 15 stuck states, 9 refusals |
| 2 | 13 | 33 | 10 | 9 rules, 10 labels, 6 refusals. Since 23 November: 42 files, 68 runs, 9 rules, 12 labels, 10 refusals |
| 3 | 2 | 22 | 1 | at least 20 runs, at least 12 compared. Since 23 November: 5 files, 55 runs, and the seeded host on the controls of one file |
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

**RB2.** `recover ↑ ℓ` restarts with the parameters of the entry
(`codegen.rs:4251-4276`, `4530-4551`).

**RB3.** `escalate` with a fault message on the heap frees the message and
passes it on (`codegen.rs:3866-3873`, `4457-4478`).

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

**RB7.** The tests do run native code (113 compilations, 352 runs) and
compare outcomes and traces. Every string they supply is static, so a drop
does nothing; 32 of the 59 modules never allocate.

**RB8.** Expansion: the prefix `_exp{N}_` is not checked against the names in
use, so a checked program can have an expansion that [O1] refuses; a
recursive control is returned unexpanded as a success; a callee with an exit
inside a boundary is skipped without a word.

**RB9.** `emit-llvm` panics on every file of slice 4. `--usize 32` means
`i32` on a 64-bit host. The module has no target triple and no data layout.

Held up: every construct of slices 1 to 3 lowers to typed IR with no
fallback to an interpreter; no `nsw`, `nuw`, `exact` or `inbounds` is
emitted; signedness and both widths agree; outside RB1, ownership is free of
leaks under an allocation tracker.

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
| RT1 to RT4 | Open, of 23 November 2026 ([task-review.md](task-review.md)). RT1: a cancelled `run` of an extern control can discard an argument that it cannot release, and [E-Run] does not say how an extern root asks the host. RT2: no rule withdraws the host operation that an owner waits for when a member's fault reaches the owner. RT3: nothing bounds `spawn`, so `count` can pass the range that [A3] gives it. RT4: the expansion of Theorem 4 loses the turn that `await` on a defined control gives up. The first three are for the rules of slice 4, and the fourth for the statement of the theorem; RT1 and RT3 each need a choice that is the author's |
| RG1 | Closed 23 November 2026. `generate::valid` writes programs from their histories; `generated_valid_programs_run_to_an_end_and_reach_every_construct` and `the_checker_accepts_generated_valid_programs` (`v2/tests/harness.rs`) hold it, and `vn2 fuzz --seed 1 --count 300 --native` reports no finding. The mutation and backend tests run on generated programs too: `every_stuck_mutant_of_a_generated_program_is_rejected` (`v2/tests/checker.rs`) and `generated_valid_programs_agree_across_oracle_expansion_and_native_o0_o2` (`v2/tests/backend.rs`). The tests that run on `generate::template` name it |
| RC9 | Closed 23 November 2026. A certificate names its instances and holds no formula; the kernel makes the formula of each with its own matcher for the axiom list, and refuses a name that names none. `the_kernel_refuses_what_is_not_an_instance`, `the_kernel_grants_every_instance_that_the_search_makes` and `the_instances_of_the_arithmetic_axioms_hold_for_the_real_operations` (`v2/tests/kernel.rs`) hold it, with `certificate_kernel_rejects_corrupted_proofs_v1_to_v5` (`v2/tests/checker.rs`). Owed with slice 2: the instances of [A3] to [A6] against real values, as the last of these tests does for [A1], [A2] and [A7] to [A9] |
| RC10 | Closed 23 November 2026. The checker gives the kernel the goal, the premises, the terms and the rows (`kernel::Query`); the certificate names premises by their position in the checker's lists. The kernel has its own arithmetic and its own diagram, and uses of the crate the integers, the diagram package and the data of `terms`. `certificate_kernel_rejects_corrupted_proofs_v1_to_v5` holds it: the same certificate is refused for another goal, and so is a premise that the checker did not state. `CheckedProgram::revalidate` validates every certificate of a check again with a kernel that saw nothing of it, and the tests of the three slices call it |
| RC11 | Closed 23 November 2026: every question the checker asks goes through one function that validates a yes in the kernel and lists the certificate, with the clause `N1` for the feasibility of a history. `an_infeasible_history_is_ruled_out_by_a_validated_certificate` (`v2/tests/checker.rs`) holds it |
| RC12 | Closed 23 November 2026. The theory check (`v2/src/lia.rs`) gives a proof that the kernel validates (with the Split step of [V3]), a model that is evaluated, or the counted limit, which the checker reports with the clause `J6`. It is complete without bounds: where its splits do not end, the Omega test (`v2/src/lia/omega.rs`) decides the rows, by changes of variable in an equality without a unit coefficient and by the splinters of a variable that no side bounds with units, in the steps of [V3] as they are. `the_procedure_is_exact_on_integers_and_gives_up_only_at_a_counted_limit` and `a_condition_without_a_bound_is_decided_by_the_omega_test` (`v2/tests/checker.rs`) hold it: the second is a precondition on the difference of two parameters, whose answer was the limit. The tests of `lia.rs` compare 3,000 sets of rows with a search of every point, and those of `lia/omega.rs` compare the Omega test alone with it on 3,000 sets of rows in a box, 1,500 without a bound on any variable and 1,500 thin bands that only splinters refute; the kernel validates every proof. The limit remains for a search that is too long: the number of splinters grows with the coefficients. One theory check in the 1,252,564 of the mutant campaign goes on to the Omega test (the program of `a_condition_on_remainders_and_products_is_decided`), and none of the 300 generated programs or of the programs of the three slices |
| RC13 | Closed 23 November 2026. `vn2 check --certificates` writes a text that holds the tables of each body and, for every question, the goal and the premises as formulas, the names of the instances and the lemmas with their proofs (`v2/src/certificate.rs`; the format is in section 10 of the [oracle document](oracle.md)). `vn2 validate` reads a text and validates every certificate from it alone. `the_text_of_the_surface_programs_reads_back_and_validates`, `the_text_of_generated_programs_reads_back_and_validates`, `a_text_written_by_hand_validates`, `a_text_that_was_changed_is_refused`, `the_reader_refuses_what_is_not_a_text` and `a_proof_as_deep_as_the_search_goes_is_read_and_validated` (`v2/tests/certificate.rs`) hold it. Not there: a second checker by another hand; the reader is in the crate and uses its kernel |
| RC16 | Closed 23 November 2026 for the time of a check; the size of `check_body_inner` is open. The data kernel of the slice 2 backend test took 2,267 theory checks, and its expansion 2,538, in which the exchanges of the simplex method wrote 2.5 and 29.7 million entries of tableaus. They take 581 and 583 theory checks and write 120,731 and 5,333 entries; a check of either takes under half a second where it took 2.4 and 8.9, and the 300 generated programs take 5 seconds where they took 26. Four changes: the theory check looks for a model along its splits before it adds rounded sums, which had made 10,149 rows of 25; a model is asked only for the rows that a formula reads; every premise and every instance that a model fails is added at once; and the tables of the diagram have a hasher for small keys. The mutant campaign of 25 programs gives the numbers it gave before, mutant for mutant. While the theory check was not complete, adding the instances with the premises lost one valid mutant of the 5,403 to the limit of [J6], and they were added only for a model that failed no premise; since the Omega test decides that mutant (RC12), they are added together, which takes a fifth fewer theory checks over the campaign. `a_condition_on_remainders_and_products_is_decided` holds that program. `the_search_stays_small_on_the_kernel_program_of_slice_two` (`v2/tests/checker.rs`) holds it by counts, which `vn2 check --counts` prints, and `a_model_behind_a_refuted_branch_is_found_in_the_first_tableau` (`v2/src/lia.rs`) holds the first change. Open: `check_body_inner` is one function of 1,573 lines; it is taken apart as the clauses of slices 2 and 3 in it are requalified |
| RC15 | Partly. Since 23 November tampering is tested on the instances, the premises and the goal of a certificate as well as on the steps of a lemma (`v2/tests/checker.rs`, `v2/tests/kernel.rs`). Open: no test compares the checker with the oracle for slices 2 and 3 |
| RC17 | Closed 23 November 2026 for soundness: the kernel grants a range, the planes of a product and the constructor of a variant value only for a term that the checker wrote, and the search gives a term that it adds no range either. `a_term_that_the_search_added_has_no_range` (`v2/tests/kernel.rs`) holds it. Open: the element has the range by [A1], so a proof that needs it fails until the solver knows the sort of every vector term (the note in section 8 of the [fact logic](facts.md)); for slice 2 |
| RC18 | Closed 23 November 2026: the search pairs constructor terms only when they have one number of arguments, and the kernel refuses the pair otherwise. `the_kernel_grants_every_instance_that_the_search_makes` and `the_kernel_refuses_what_is_not_an_instance` hold it |
| RC19 | Closed 23 November 2026: the checker keeps its names in ordered tables. `a_check_is_the_same_every_time` (`v2/tests/checker.rs`) checks 30 programs twice, the second time on another thread, and requires one certificate text (2,136 certificates) and one set of counts |
| RO1 | Closed 23 November 2026. A fault ends the scopes of an activation innermost first (`Machine::unwind` in `oracle.rs`, `trigger_unwind` in `erased.rs`), so a lexical boundary inside the body of a named boundary takes it first. The run `supervises` of `v2/tests/slice2/lexical_boundaries.core` holds it, with the trace of the finding |
| RO3 | Closed 23 November 2026. `resolve` refuses the ends that [E-Contingency] forbids, by [F5] and [F6] as the [core](core.md) lists them since that day: 22 files `v2/tests/slice2/reject_*.core`, one for each requirement. `terminate n` has a literal status, belongs to the entry control, which nothing invokes, ends its scopes by [E-Scope], and gives the end `terminated n` and no outcome; inside a loop of the contingency it ends the execution where it panicked (`ends_execution`, and `terminate_abandons` in `lexical_boundaries_stuck.core`). `□` in the body of a boundary, which `resolve` refused, leaves the loop around it (`leaves_inside`) |
| RO4 | Closed 23 November 2026. `recover ↑ ℓ` restarts the loop with its own parameters, read as operands, and no copy of them is kept; the body of the boundary does not mention them ([F5], `reject_f5_recover_parameter_in_work.core`). The runs `retries` and `recovers_outer` hold it, with `recover_without_parameter`, `recover_breaks_invariant` and `recover_abandons` for its stuck states. The backend restored a copy taken when the loop was first entered; its parameters stay in their slots now, and the twelve runs of `lexical_boundaries.core` agree with the oracle in compiled code |
| RC14 | Closed 23 November 2026 with RO3: the terminators of a contingency are requirements of form, and its end without one is `X1` by coverage ([K7]). The `reject` files hold it |
| RO2 | Closed 23 November 2026. An activation keeps the borrows it was passed, and the condition of an alternative reads the value at completion through them ([E-Formula], which says so since that day). `v2/tests/slice3/exit_conditions.core` holds it: the two controls of the finding, one that passes its parameter on with a true condition and one with a false one, beside the same two with a reborrow |
| RO6 | Closed 23 November 2026 for the two semantics and their hosts. A host names a place within one of its arguments and the step makes the reborrow ([E-Extern]); in a directive the place is written `&x…` or `&~x…`. `v2/tests/slice3/host_borrows.core` holds it with 11 runs that end and 10 violations, one for each way an answer can fail to be such a reborrow, and `the_seeded_host_answers_borrowed_payloads_with_places_within_its_arguments` (`v2/tests/slice3.rs`) for the seeded host. Open with the backend of slice 3: the native driver answers a borrowed payload with a value in a cell of its own, and the one test that does so compares compiled code with the erased interpreter alone (`backend_slice3.rs`). See RO11 for writes |
| RO8 | Closed 23 November 2026. A resource type that occurs at any depth of a parameter or a payload makes a control impure (`Program::resource_occurs`), and the checker asks `control_is_pure`, which also looks for `run` in what the control reaches ([I10]). `v2/tests/slice2/pure_operations.core` holds it: two calls that return a resource inside a struct, and inside a variant, give two resources, and a pure control that answers in two ways is a violation |
| RO9 | Closed 23 November 2026. The contract of `insert` is that of the corpus prelude, `replaced {previous: v}`; the listing of section 3 of the [reference model](references.md) and the core form of its example 6.3 were short of the payload and are corrected (its section 16). The example runs as `touch` in `v2/tests/slice3/builtin_operands.core`. Section 6.6 of the [core](core.md) names the built-in operations, and the row X2 of its section 6.10 the clauses of the labels `X2 E-Field`, `X2 E-Index` and `X2 E-Supervise`, with an entry in its section 12; `X5 E-Resource` is a check of the oracle on its own table. `done terminated` went with RO3 |
| RO10 | Closed 23 November 2026. The operand of a built-in follows the rule of any operand for a parameter of that type. `reject_c1_push_shared.core`, `reject_c1_push_by_value.core`, `reject_c1_get_exclusive.core` and `reject_c1_remove_key_exclusive.core` (`v2/tests/slice2/`) hold the refusals, and `builtin_operands.core` (`v2/tests/slice3/`) the runs: `&~p` lends, and a name of type `&~` passes the borrow itself, after which a second use of it is `X2` |
| RO11 | Open, found on 23 November 2026: a host cannot write through an `&~` argument. For slice 3 |
| RC2 | Closed 23 November 2026. A captured operation writes its `&~` operand at the capture: the place gets a fresh name there, and the conditions of the alternative relate the collection before and after when the outcome is decided ([I12] of the [fact logic](facts.md), which says so since that day). `a_captured_operation_writes_where_it_is_captured_i12_b5` (`v2/tests/checker_slice2.rs`) holds it with the program of the finding and three more that are stuck in the oracle and refused, and four that end and are accepted with what the alternative says of the length |
| RC3 | Closed 23 November 2026. The record of a capture goes with the value: an assignment to the name drops it, a bind or an assignment of a captured outcome carries it to the new name, and a loop that assigns the name drops it at its entry. `the_facts_of_a_capture_go_with_the_captured_value_i12` holds it, with a program that is stuck and refused for the assignment and one for the loop |
| RC5 | Open. The question is answered in [E-Boundary]: what the boundary has in its care ends with the scope of `B₁`, so the oracle is right (`care_ends_with_work`, `care_ends_with_exit`) and the checker owes [O5] there |
| RC6 | Open. The question is answered in [E-Supervise] and [F6]: nothing encloses a statement of the contingency of a named boundary, so the oracle is right (`run_calls_faulting` in `faults_and_boundaries.core`) and the checker owes [F1] there |
| RC20 | Open, found on 23 November 2026: the checker refuses by [F3] a named boundary that supervises another whose body has an effect, since a boundary declares none. It refuses a valid program and accepts no stuck one |
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
