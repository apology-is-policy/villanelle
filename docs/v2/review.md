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
| Oracle: accepting and rejecting test for each clause | Met: 41 files, 126 runs, 12 rules, 15 stuck states, 9 refusals | Partly: 13 files, 33 runs, 10 stuck labels; the fault-boundary rules are wrong (RO1, RO3, RO4) | No: 2 files; one stuck label, `X4 B1`, which the oracle raises in 17 places; the test asserts counts of runs | No: 2 files; the test asserts no stuck state; one run varies the order of turns |
| Checker: accepting and rejecting test for each clause | Met | Partly; unsound (RC2 to RC6) | Partly: the worked examples of the reference model; unsound (RC1); the loan checker was tested from outside only | No checker |
| Generator reaches every construct of the slice (phase 2 exit) | Only through one fixed program (RG1) | No generator | No generator | No generator |
| Oracle against erased semantics | 62 runs and the fixed program | The erased interpreter is a transcription of the oracle (RO7) and wrong under faults (RO5) | As slice 2 | As slice 2 |
| Mutations rejected at the rate the author sets (phase 3 exit) | Five kinds on one program shape, 8 seeds | None | None | None |
| No generated checked program is stuck over a long campaign (phase 3 exit) | No campaign | None | None | None |
| Compiled code agrees with the oracle on generated programs (phase 4 exit) | One program shape | None; double free (RB1) | None | No backend; `emit-llvm` panics (RB9) |
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

Held up under attack: the arithmetic of slice 1 at the bounds of every type
and at both `usize` widths, loops and invariants, mutable names in branches
and effects; in slice 2, leaks at `↑`, `□` and `■`, overwriting a `must`
value, [F1] and [F2]; in slice 3, the loan rules, where 25 programs that are
stuck with X4 were all rejected.

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

The suites:

| Slice | Files | Runs | Stuck labels reached | What the test asserts |
| --- | ---: | ---: | --- | --- |
| 1 | 41 | 126 | 15 | 12 rules, 15 stuck states, 9 refusals |
| 2 | 13 | 33 | 10 | 9 rules, 10 labels, 6 refusals |
| 3 | 2 | 22 | 1 | at least 20 runs, at least 12 compared |
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
   (RS1), and repair the formatter (RS4).
6. An independent second review of the task rules (RD2).
