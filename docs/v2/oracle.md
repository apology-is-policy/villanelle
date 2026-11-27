# Villanelle v2 oracle, checker and typed backend

Status: **under requalification**, 23 November 2026. Phases 2, 3 and 4 of
the [redesign plan](../redesign-plan.md). The crate holds code for slices 1 to
3 through oracle, erased interpreter, checker, call expansion and typed LLVM
IR backend. Slice 4 has an oracle, a checker, and native code for defined
roots, direct runs of nonfaulting and noncancellable host operations, and
task sets whose owners and members can yield at a defined await. Roots and members can
wait for the host in their own activations or in a callee (sections 18.4 to
18.22). The oracle of slice 1 and its conformance suite (sections 1 to 7) are qualified. Everything described from
section 8 on was written on 21 and 22 November and is **draft**: the
[review](review.md) of 23 November found that no slice meets its exit, and
lists the defects. Sections 8 to 18 describe what the code does and which
tests exist; where they say "verified", "complete" or "parity", read it as
"on the programs of the test suite". Section 19 lists what is owed.

[Index of the v2 design](README.md) · [Review](review.md) ·
[Core calculus](core.md) · [Fact logic](facts.md) · [Surface](surface.md)

## 1. What it is

The oracle is the instrumented semantics of the [core](core.md), section 6,
written as a program. It runs a core program and is stuck on every violation
the checker is meant to exclude. A stuck run names the row of the table of
stuck states (X1 to X10) and the clause that had no successor. The checker of
phase 3 and the compiled code of phase 4 are tested against it.

It lives in `v2/`, a crate of its own beside v1. The crate has no
dependencies and shares no code with the v1 compiler, so that the definition
can be read on its own. Nothing in it is built for speed.

| Module | Holds |
| --- | --- |
| `int` | Mathematical integers. A formula is evaluated over them ([E-Formula]), and a result fits its type when the mathematical result lies within the type's bounds ([E-Arith]). |
| `syntax`, `text` | The core text form (section 3): its tree, printer and reader |
| `surface` | The Rails surface syntax ([surface](surface.md)): layout ([Y1] to [Y10]), grammar ([G1] to [G10]), elaboration ([U1] to [U15]) into `syntax::Program` and surface warnings ([U5], [U17], [U18]) (section 9) |
| `typed`, `resolve` | The typed core, and what is checked on the way to it (section 4) |
| `bdd`, `facts`, `kernel` | The ROBDD engine; the `Th_Z` fact logic with its search, the models of its candidates (`facts/completion.rs`) and its counterexamples ([M1] to [M6]); and the certificate kernel, which is given the query by the checker, makes the formula of every instance from its name with its own matcher for the axiom list, checks the proof of every lemma (a tree of the steps of [V3], with Split) and recomputes the Boolean step in a diagram of its own ([V1] to [V4]) (section 10) |
| `certificate` | The text of certificates ([V5]): the writer, and a reader that makes the tables, the goals and the premises from a text alone and gives them to the kernel (section 10) |
| `counts` | The work of the search as counts for each thread, which `vn2 check --counts` prints; nothing reads them to decide anything (section 10) |
| `terms`, `lia`, `rational` | The terms, rows, proofs, names of instances and certificates that the search and the kernel both read; the theory check for the rows of a candidate, which answers with a model, a proof or the counted limit of [J6], and whose last part, the Omega test (`lia/omega.rs`), decides rows without bounds (section 7 of the [fact logic](facts.md) has a note on the method); and the rationals of its simplex method |
| `check` | The phase 3 checker: coverage ([K1] to [K8]), conditional facts and SSA renaming ([N1] to [N5]), acknowledgement ([C2]), availability ([O1], [O2], [O4], [O6]), obligations ([P1] to [P8]), effects ([F3]) and impossible-arm warnings ([U16]) (section 10). `check_body_inner` goes through the statements of a body and keeps the histories that reach each ([K2], [K3]); a statement is checked by the method of its command (`check_bind`, `check_decide`, `check_loop`, `check_boundary` and the others) |
| `expand` | Theorem 4 call expansion: in-place expansion of decisions on defined controls, lifting loop exits and preserving checking and observations (section 11) |
| `codegen` | The phase 4 typed LLVM IR and C ABI backend under the erased semantics ([R1] to [R3]), with native `-O0`/`-O2`/`-O3` compilation and differential execution (section 11) |
| `oracle` | Section 6 of the core, one function for each rule |
| `erased` | Section 9 of the core ([R1] to [R3]): machine-word slots, wrapping arithmetic and one bit for each atom a selector mentions |
| `differential` | Theorem 3 tested run by run: where the oracle is not stuck, the erased run with the host's answers replayed gives the same observation |
| `host` | Hosts for extern controls (section 5): `Script`, `Arithmetic` and `Seeded` |
| `script` | The directives that state runs beside a program (section 6) |
| `rng` | A seeded SplitMix64 generator and stateless word mixer |
| `generate` | Core programs as `syntax::Program` trees (`valid`, one fixed program with seeded choices, and `free`, random), and a counter for the 61 constructs of the slice (section 8) |
| `mutate` | Single-step mutations of valid programs, classified by the oracle (section 8) |

Slice 1 is the scalar language: `bool`, the integer types, functions, tests,
decisions on defined and extern controls, loops, exits, obligations and `⊥`.
Every value has kind `copy`, so no slot is moved and no borrow tag exists yet.

## 2. Running it

```sh
cd v2
cargo test                                     # unit tests and the conformance suite
cargo run --bin vn2 -- test tests/slice1/*.core tests/slice1_surface/*.rails
cargo run --bin vn2 -- check tests/slice1_surface/*.rails
cargo run --bin vn2 -- check tests/slice1_surface/*.rails --certificates > certificates.txt
cargo run --bin vn2 -- validate certificates.txt   # the kernel, from the text alone
cargo run --bin vn2 -- check tests/slice1_surface/*.rails --counts   # the work of the search
cargo run --bin vn2 -- format tests/slice1_surface/show_file.rails --check
cargo run --bin vn2 -- expand tests/slice1_surface/groups_and_auto.rails
cargo run --bin vn2 -- emit-llvm tests/slice1_surface/spend.rails
cargo run --bin vn2 -- emit-c tests/slice1_surface/spend.rails
cargo run --bin vn2 -- run tests/slice1/e-loop.core gcd 48 18
cargo run --bin vn2 -- run tests/slice1_surface/spend.rails spend 10 4 --arithmetic
cargo run --bin vn2 -- print tests/slice1_surface/show_file.rails
```

`vn2 run FILE ENTRY VALUES...` prints the events of the run and how it ends:

```text
$ vn2 run tests/slice1/e-arith.core add 250 6
stuck X7 E-Arith at add:5: 250 + 6 = 256 is not a value of u8
```

`--arithmetic` gives the run a host that computes checked arithmetic,
`--usize 32` makes the greatest `usize` `2³² - 1`, `--fuel N` bounds the
steps, and `--erased` runs the program under the erased semantics.

## 3. The core text form

The oracle reads the notation of the core document: a body is a list of
guarded statements, `selector ▷ command`. This is a form for tests and for
reports. Programs are written in Rails, and the reader of Rails, which
elaborates into this form, is a later checkpoint.

```text
Program    ::= Declaration*
Declaration ::= function name ( Param,* ) [⊢ Formula] : Type := Expr
              | [pub] control name ( Param,* ) Signature Statement*
              | extern control name ( Param,* ) Signature
Signature  ::= [⊢ Formula] ■ { Alt (│ Alt)* } [uses name,*]
Alt        ::= name [{ Param,* }] [⇐ Formula]
Param      ::= name : Type
Type       ::= bool | u8 | u16 | u32 | u64 | i8 | i16 | i32 | i64 | usize

Statement  ::= [number] Selector ▷ Command
Selector   ::= ⊤ | name . name | ¬ Selector | Selector ∧ Selector
             | Selector ∨ Selector | ( Selector )
Command    ::= [~] name [: Type] := Expr
             | name ← Expr
             | ⊢ Formula
             | name : ? Expr
             | name : Δ name ( Expr,* ) [▸ Arm (│ Arm)*]
             | name : ↻ name [( LoopParam,* )] { [⊢ Formula] Statement* }
                   [▸ Arm (│ Arm)*]
             | ↑ name ( Expr,* )
             | □ name [{ Expr,* }]
             | ■ name [{ Expr,* }]
             | ⊥
Arm        ::= name [{ name,* }]
LoopParam  ::= [~] name : Type := Expr

Expr       ::= number | true | false | name | name ( Expr,* ) | ( Expr )
             | ¬ Expr | - Expr | Expr op Expr
```

The operators and their order are those of the [surface](surface.md), section
4.3. A formula is an expression of type `bool`.

- The body of a control is the statements after its signature, up to the next
  declaration. The body of a loop is in braces, and a `⊢` line that opens it
  is the loop's invariant.
- A statement may begin with a number, as the documents print them. The
  number means nothing.
- A comment runs from `┄` or `//` to the end of the line.
- The text has no layout, with one exception: a `(` that is the first token
  on its line does not continue the expression before it. A statement may
  therefore begin with a selector in parentheses.
- `x<-1` is an assignment. A comparison with a negative number needs the
  space: `x < -1`.

Every glyph has a spelling in ASCII. They are those of the surface ([G8]),
with three more that only the core form needs:

| Glyph | Word | Glyph | Word | Glyph | Word |
| --- | --- | --- | --- | --- | --- |
| `⊤` | `top` | `▷` | `\|>` | `▸` | `>>` |
| `Δ` | `delta` | `■` | `exit`, `exits` | `□` | `leave` |
| `↻` | `loop` | `↑` | `again` | `?` | `if` |
| `⊢` | `where` | `⇐` | `when` | `⊥` | `impossible` |
| `←` | `<-` | `~` | `mutable` | `│` | `\|` |
| `≠ ≤ ≥` | `!= <= >=` | `∧ ∨ ¬` | `&& \|\| !` | `÷` | `/` |

`=` may be written `==`. `vn2 print` gives a program in the glyph form, and
reading the print gives the same program.

## 4. What is refused, and what is stuck

A program has to be resolved and typed before it can run. `resolve` does that
and refuses a program whose text is not well formed. Everything that depends
on which history runs is left to the oracle, which runs the program and is
stuck where it goes wrong. The checker of phase 3 starts from the same
`resolve` and adds the judgments that exclude the stuck states.

| Refused by `resolve` | Clause |
| --- | --- |
| A site name used twice in one control | [W1] |
| A selector that mentions a site which does not precede it in its body or around its loop | [W2] |
| `↑` outside its loop, `□` outside a loop | [W3] |
| A name bound in two nested bodies; binders of one name that differ in type or mutability | [W4] |
| A function that reaches itself | [W5] |
| A contract that lists an alternative twice | [W7] |
| An expression that is not typed: operands of two types, a literal outside its type, an unknown name, an assignment to a name that is not mutable | [C1] |
| An arm for an alternative the operation does not have, a repeated arm, a wrong number of payload names | [C2] |
| An exit or a `□` with an alternative that is not listed, a listed alternative that no `□` uses, `□` statements that differ in a payload type | [C3] |

| Stuck in the oracle | State | Clause |
| --- | --- | --- |
| A body reaches its end | X1 | [E-End] |
| A name is read where it has no slot | X2 | [E-Var] |
| A name is assigned where it has no slot | X2 | [E-Assign] |
| A name is bound twice in one run of its body | X3 | [E-Bind] |
| `⊥` runs | X6 | [E-Impossible] |
| A result leaves its type; a divisor is zero | X7 | [E-Arith] |
| A false precondition of a function, a defined control, an extern control | X7 | [E-Fn], [E-Call], [E-Extern] |
| A false obligation | X7 | [E-Oblige] |
| A false condition of the alternative at an exit | X7 | [E-Exit] |
| A false invariant at entry, at `↑` | X7 | [E-Loop], [E-Again] |
| An effect that an activation on the stack does not allow | X9 | [E-Effect] |
| An operation completes with an alternative the decision does not list | X10 | [E-Decide] |

A missing arm is left to the oracle on purpose: it is the gap that decision
D3 closes, and the checker's rejection of it ([C2]) is tested against a run
that is stuck.

## 5. Hosts

An extern control is a step of the host: given the arguments, an alternative
and a payload ([E-Extern]). The oracle checks each answer against the
contract ([E-Host]): the alternative is listed, the payload has the types of
its fields, the condition of the alternative is true, and a control without
an effect gives the same answer to the same arguments. An answer that fails
ends the run in `violation`. That is a fault of the trusted host and not a
stuck state. A step of a control with an effect is recorded as an event.

A control is without an effect, in the sense of [I10], when it declares none,
is not `async`, and no resource type occurs in its parameters or payloads at
any depth: a struct, a variant or an outcome that holds a resource counts
(`Program::resource_occurs`).

A host is given values and sees no slots. For a field of the payload that is
a borrow it names a place within one of its arguments
(`Value::within(mode, argument, steps)`), and the step of the oracle makes the
reborrow: a tag under the tag of that argument, by [B3]. A view in the
payload holds such a place for each of its borrows. The oracle refuses, as a
violation, a value where a borrow is expected, a place that is not there or
holds a value of another type, an exclusive borrow of what was lent shared,
an argument that the field does not list after `∈`, and two places of one
payload that overlap unless both are shared. The erased interpreter makes
the same borrow without a tag.

Beside the payload a host may name, for an argument lent exclusively, the
value it leaves behind that borrow (`Answer.writes`), and the step writes it
there through the argument's tag before it makes the borrows of the payload
(RO11, section 15.1). A write behind an argument that was not lent
exclusively, a value of another type, and a change to a value of kind
`must` are violations. The seeded host writes nothing.

Three hosts exist. `Script` answers from a list, in order, and a run whose list
is exhausted or names another control ends in `host-failed`: a defect of the
test. `Arithmetic` computes the checked arithmetic of the prelude: a control
whose name begins with `checked_add`, `checked_sub`, `checked_mul`,
`checked_div` or `checked_rem`, with two alternatives of which the first
carries the result, and passes every other call on. `Seeded` draws answers from
a seeded generator and checks each candidate against the alternative's
condition (`signature_holds`) before returning it; a control without an effect
derives its generator from the host's seed, the control's name and the
arguments (`rng::mix`), so two calls with the same arguments get the same
answer. For a borrow it draws one of the places of the wanted type within
the origins of the field, and passes over an alternative for which the
arguments hold none. A value of an outcome type, in an answer or among the
arguments that `generate::entry_runs` draws for an entry, is one that its
operation gives ([E-Host]): `draw_outcome` draws arguments that satisfy the
precondition of the operation, and then an alternative and a payload as for
an answer. The oracle does not test this of a host, and a checked program
relies on it ([I12]); the native harness writes such a value as a capture
lays it out.

## 6. Directives

A line that begins with `//!` states a run beside the program, and what it
must yield.

```text
//! run add(250, 5) => done sum {255}
//! run add(250, 6) => stuck X7 E-Arith
//! run pump(2) with [read -> value {7}; read -> closed] => done total {7}
//!     trace [read(2) -> value {7}; read(2) -> closed {}]
//! run reads(8) with [first_item -> item {&xs[1]}] => done ok {8}
//! run bumps(4) with [bump -> done ~x <- 5] => done ok {5}
//! run address(4294967295) usize 32 => stuck X7 E-Arith
//! reject W1
```

`run` names an entry control and its arguments. The options follow: `with
arithmetic`, `with [...]` for a scripted host, `usize 32`, `fuel N`, and for
tasks `turns [i, …]` (each time the host gives a turn, the index of the task
among those that are ready, in the order of the run's tasks), `waiting [i,
…]` (each time no task is ready, the index of the operation the host
completes among those that wait), `cancel_at N` (the host sets the flag of
the root of the innermost run at its `N`th turn), and `capacity N` (the
largest length of a collection and count of a set that a step may make,
[E-Exhaust]). In a scripted answer, `~x <- v` after the alternative and its payload is the
value that the host leaves behind its parameter `x`. After
`=>` comes the expected end: `done` with the alternative and its payload,
`faulted` with the message, `terminated` with the status of `terminate n`,
`stuck` with the state and the clause, `exhausted`, `violation`,
`host-failed`, `fuel`, or `not-an-execution` (the arguments are not values of the parameter types, or
the precondition of the entry is false; section 8 of the core does not count
such a run as an execution). `trace [...]` states the events. `reject` names
the clause by which `resolve` must refuse the program.

In the answer of a scripted host a borrow is written as the place it refers
to: `&x` or `&~x`, with `x` a parameter of the control that is answered,
followed by any number of `.field` and `[value]` steps, where `[n]` is an
element of a vector and `[key]` the value at a key of a map.

Every `run` that ends in `done`, `faulted`, `terminated`, `exhausted` or `fuel` is also carried out under the erased
semantics with the host's answers replayed, and the two observations must agree
(Theorem 3). `erased` in the place of `run` states a run of the erased
semantics alone; it may also end in `undefined` (`⊥`, the end of a body, an
alternative that the waiting decision does not list, or a division by zero).

## 7. Conformance of slice 1

`v2/tests/slice1` holds 41 programs with 126 runs (62 of them compared with the
erased semantics). The suite carries them out
and then checks that together they reach what the slice has: each of the
twelve rules a statement can apply, each of the fifteen ways of being stuck,
and each of the nine clauses of refusal.

| Clause | File |
| --- | --- |
| [E-Arith], [A2] | `e-arith.core` |
| [E-Bool] | `e-bool.core` |
| [E-Fn] | `e-fn.core` |
| [E-Formula] | `e-formula.core`, `e-fn.core` |
| [E-Oblige] | `e-oblige.core` |
| [E-Skip], [E-End] | `e-end.core` |
| [E-Var] | `e-var.core` |
| [E-Bind] | `e-bind.core` |
| [E-Assign] | `e-assign.core` |
| [E-Test], [H2], [H3] | `e-test.core` |
| [E-Decide], [E-Call], [E-Exit] | `e-decide.core` |
| [E-Impossible] | `e-impossible.core` |
| [E-Extern], [E-Host], [E-Effect] | `e-extern.core` |
| [E-Loop], [E-Again], [E-Leave], [H1], [H4] | `e-loop.core` |
| [R1], [R2], [R3] | `r-erasure.core` |
| [C3], [W9] | `c3-leave-types.core` |
| [G8] | `words.core` |
| [W1] to [W5], [W7], [C1] to [C3] | `reject-*.core`, 24 files |

The clauses of checking (K, N, P) have no test here. They are judgments, and
their accepting and rejecting tests come with the checker. Each has its
stuck state above: coverage [K7] is X1, [P1] to [P5] are X7, and [P6] is X6.

## 8. Generator, differential harness, mutations and axioms

- **Fact-logic axioms (`v2/tests/axioms.rs`).** The nonlinear axioms of the
  [fact logic](facts.md) — division by a constant ([A7]), division by a term
  ([A8]) and the four bounding planes of a product ([A9]) — are tested across
  100,000 random and boundary integer draws against `Int::divide` and
  `Int::times`, and across 20,000 runs as `⊢` obligations of a core program in
  the oracle.
- **Program generator (`generate`, `v2/tests/harness.rs`).** Every generated
  program is built as a `syntax::Program`, printed as core text, parsed back
  and resolved. `generate::valid` writes a body statement by statement and
  keeps beside it every history that is still running ([K1] to [K3]): its
  atoms, the names bound on it and an interval for each integer. A statement
  runs on the histories that satisfy its selector, a test or a decision
  splits each of them, a terminator ends them, and the body is complete when
  none is left ([K7]). Every obligation ([P1] to [P6]) is discharged on the
  intervals of the histories that run the statement, and the partial
  operators are bounded as the fact logic bounds them ([A7] to [A9],
  `generate/interval.rs`), so the generator concludes nothing that the fact
  logic does not entail. A history whose intervals become empty gets `⊥` or
  nothing. Loops have a counter that every `↑` moves; preconditions,
  invariants and the conditions of alternatives are intervals, and the
  conditions of a defined control are what held at its exits. A program is a
  function of its seed (`fuzz::program_of`). Over seeds 1 to 300, at both
  widths of `usize`, 11,728 runs end in `done`, none is stuck, each gives
  the same observation under the erased semantics, and the programs reach
  all 61 constructs and all 12 statement rules. `generate::template` is the
  fixed program of 53 lines that was `valid` until 23 November
  ([review](review.md), RG1); it is kept as one regression program, and the
  tests that run on it say so. The checker, mutation and backend tests run
  on programs of the generator as well.
  `generate::free` builds
  unconstrained well-resolved programs of 10 to 20 lines; across 250 seeds it
  reaches all 61 constructs, and every run that is not stuck in the oracle
  agrees with the erased semantics. Most of its runs are stuck in the first
  statements.
- **Mutations (`mutate`, `v2/tests/harness.rs`, `v2/tests/checker.rs`).**
  `mutate::mutate` produces all single-step mutants of a valid program
  across seven kinds: `RemoveArm` ([C2], X10), `RemoveDisposition` ([K7],
  X1), `DropGuard` ([O2] to [O4], [P1] to [P8], X2, X3, X6, X7),
  `DropInvariant` ([K4], [P4]), `DropEffect` ([F3], X9), `ShiftLiteral` (an
  integer literal is one greater or one less) and `FlipComparison` (`<` and
  `≤`, `>` and `≥`, `=` and `≠` are replaced by each other). The last two
  change one expression of a control: of its precondition, of the conditions
  of its contract or of its body ([P1] to [P8], X6, X7). Since 24 November
  2026 there are five more, for the ownership of slice 2:
  `RemoveStatement` (a statement that is no disposition and holds no body
  is removed: what it consumed is still owed, [O4], [O5], X5),
  `SwapStatements` (two statements that follow one another in a body change
  places: what the second gives away is gone when the first runs, or a
  fault comes while something is owed, [O2] to [O5], [F2], X2, X5, X8),
  `ConsumeClone` (`clone(e)` becomes `e`, [O2], X2), `DropFaults` (a control
  loses `faults`, [F1], X8) and `DropFaultRelease` (a resource loses `on
  fault release`, [F2], X8). The kinds that change a body reach into the
  bodies of loops, of the work and the contingency of a boundary, and of a
  named boundary, and `RemoveDisposition` takes `terminate`, `escalate` and
  `recover` too. Taking a name out of the care of a boundary or out of what
  a named boundary retains is no kind: where the contingency mentions the
  name `resolve` refuses, and where it does not the program means the same
  (21 such mutants of 8 generated programs: none stuck).
  `mutations_of_ownership_are_stuck_and_rejected`
  (`v2/tests/checker_slice2.rs`) has a program with a stuck mutant of each
  of the five kinds, in the states the kind is for, and requires that the
  checker rejects every stuck mutant of it. Since 24 November 2026 there are
  four more, for the borrows of slice 3, each aimed at a run that uses a
  borrow after it ended: `FlipBorrow` (a borrow `&p` that a name or a loop
  parameter is bound to becomes `&~p`, or the reverse, and the declared
  type of the name with it, [B1] to [B3], X4), `ConflictingBorrow` (before
  a statement that mentions a name that holds a borrow of `p`, a borrow of
  `p` in the other mode is bound to a fresh name, [B2], [B3], X4),
  `AccessLent` (there, the root of `p` is bound to a fresh name, which reads
  a value that is copied and moves one that is not, [B2], [B4], X4) and
  `ExtendBorrow` (a name of borrow type is borrowed again after a later
  statement of its body, [B1], [L2], X4, and [O2], X2 where a statement
  between moved it). Which names are of borrow type is read from the program
  as `resolve` types it. A name holds a borrow of `p` where it is bound to
  `&p` or `&~p`, or where it is a payload name that the contract derives
  from a parameter (`∈ y`) for which the argument is `&p` or `&~p`. A write
  through a shared borrow name is no kind: `resolve` refuses it.
  `mutations_of_borrows_are_stuck_and_rejected`
  (`v2/tests/checker_slice3.rs`) has a program of eight controls in which
  each of the four kinds has a stuck mutant in the controls where it meets a
  conflict and in no other, and requires that the checker rejects every
  stuck mutant of it (section 16.4). `mutate::classify`
  runs a mutant in the oracle; across 16 sets of numbers of the template,
  the stuck mutants reach all 15 stuck states of slice 1. They are the
  target rejection set for the phase 3 checker.
  `every_stuck_mutant_of_a_generated_program_is_rejected`
  (`v2/tests/checker.rs`) takes every mutant of four generated programs,
  draws the runs of each for its own preconditions, and requires that
  `resolve` or the checker rejects each mutant with a stuck run: 72 of them,
  of every kind but `DropInvariant`, which leaves no run stuck.
- **Data in generated programs (`generate::valid_data`,
  `v2/src/generate/valid/data.rs`, `vn2 fuzz --slice 2`).** The same
  generator writes the data of slice 2 when it is asked to. It declares
  structs and variants, and gives names, parameters, payloads and loop
  parameters the types of data as well. Beside the interval of an integer it
  keeps, for every name on every history, whether its value has moved ([O3])
  and what the fact logic knows of it: a struct field by field ([A4]), a
  variant by the constructors it can be ([A5]), a vector, a map or a string
  by the interval of its length ([A3] and the conditions of the built-in
  operations). One statement evaluates its operands in an order
  ([E-Operands], [O0]): a name that an operand has consumed is gone for the
  operands after it, and a name that one operand lends is not consumed by
  another. A body moves no name of a body around a loop it is in ([O6]).
  What it writes: binds of constructors, clones and moves; `S {x̄} := e`;
  assignments to names, fields and elements; decisions on variants, with
  `⊥` on a constructor that the value cannot be; `push`, `pop`, `take`,
  `get`, `entry_at`, `insert`, `remove` and `emit`, with `⊥` on an
  alternative that the length excludes; fields, elements at an index known
  to be in range, and lengths, inside any integer expression;
  `t : ? i < len(v)` followed by `v[i]`, where the test alone puts the
  index in range; preconditions on the length of a vector; and `&τ` and
  `&~τ` parameters of extern controls. A program of slice 1 is unchanged by
  this: the generator draws nothing more for it, and the programs of 600
  seeds were compared text for text. `generate::DATA_CONSTRUCTS` lists the
  56 constructs of the slice, and a campaign names those it did not reach.
  `v2/tests/harness.rs` runs 240 seeds in the two semantics and asks the
  checker about 30; over 900 seeds `vn2 fuzz --slice 2` gives
  36,348 runs with no stuck run and no difference, of which 3,732 end in a
  fault and 1,338 with `terminate n`, and the
  checker accepts all 900 (it gave no answer in ten seconds on four of
  them before review finding RC22 was closed).
- **Obligations in generated programs.** A program with data declares up to
  two resources, and for each a contingent extern control that takes a
  value of it and ends it. A value of kind `must` ([T1]) is a resource, a
  struct or a variant that holds one, or a captured outcome. It comes from
  the payload of a decision, from a parameter or from `x := capture f(ō)`,
  and it moves like other data: into a name, a constructor, a payload, an
  operand, a parameter of a loop. A name that holds one is lent as `&x` and
  is never a temporary ([O3a]); it is assigned only where its value has
  moved on every history ([O4]). Before every terminator the generator
  discharges what the histories of its selector still hold in the scopes
  that the terminator ends ([O5]): all bodies of the control for `■`, the
  loop body for `□`, the bodies up to the loop for `↑ ℓ`. It closes a
  resource, takes a struct apart, and decides on a variant or on a captured
  outcome, until nothing is held. Where only some of the histories hold a
  name, the statement stands under the selector and one more atom that
  picks them, or under every atom of one history. The expressions of the
  terminator are written first, since they may give an obligation away, and
  they read nothing of a name that holds one. A loop is entered only where
  every obligation is held by all of the histories that enter or by none:
  the others are discharged before it, since its body could not end them.
  Inside a body, a name of a body around it is not consumed ([O6]), except
  before `■` and before the `↑` of a loop further out, which end its scope.
  One alternative of every contract and of every loop has no obligation in
  its payload, so that a history can end whatever it holds. A captured
  outcome keeps, for each history, the intervals of the arguments at its
  capture; a decision on it gives each alternative what the conditions of
  the captured operation say over them ([I12]), and what they say over
  names of which nothing is known once the outcome has passed through a
  loop. A parameter or a payload field of a control, of an extern control
  or of a named boundary has, now and then, the outcome type of an
  operation declared before it. Such a value is decided where its capture
  is not visible, by what the conditions say over names of which nothing is
  known. The hosts and the entries give only values of the type that its
  operation gives (`host::draw_outcome`, review finding RG7).
- **Faults and boundaries in generated programs
  (`v2/src/generate/valid/faults.rs`).** A control of a program with data
  may say `faults`, may be `contingent`, and may be an entry control, which
  nothing invokes. A statement that may fault ([F1]) is `fault e`, a
  decision or a capture on an operation that says `faults`, or `supervise`
  of a boundary whose contingency lets a fault out. It is written where a
  fault is permitted, and before it the histories that run it give up what
  may not be held there: every obligation that is not fault-releasable
  ([F2], [T3]), and what the end of the contingency asks of the bodies
  around the boundary. A statement that goes on consumes only names of the
  loop body it is in ([O6]) and is not written where another name would have
  to go; `fault e` ends its histories and may consume any name that the
  fault and the contingency end. The operands of such a statement read no
  name that holds an obligation and lend none.
  A lexical boundary is written with the end of its contingency chosen
  first: none (no statement of the work may fault, and the contingency is
  `⊥`), `escalate` or a new `fault` (where a fault is permitted around the
  boundary), `terminate n` (in an entry control), or `recover ↑ ℓ` for a
  loop around the boundary that the bodies between let end (`recoveries`).
  For `recover` an assignment has moved the counter of the loop since the
  loop went round, so that a fault that comes again does not come for ever.
  The counter is declared `~` in three of four loops, and an assignment
  moves it just before the boundary; or it has moved on these histories
  already, before another boundary or before a loop between (`prime`),
  whose body does not assign the counters of the loops around it; or a work
  around the boundary restarts the same loop. A counter that has moved may
  go round as it is (`↑ ℓ(i)`). The parameters of the loop are available
  and within the invariant at the boundary, none holds what a fault does not
  release, and the work does not see them ([F5](c)). The work
  is a body that sees the names around it and may consume them; it may end
  with the terminators of the bodies around it, with `fault`, or by falling
  off its end, before which it ends its own obligations and makes those of
  the bodies around it even. After the boundary a name that the work may
  have assigned is known by what the histories that fell off know of it.
  The boundary takes names into its care: values that may be dropped, and an
  obligation only where every history of the work ends in a fault
  ([E-Boundary], [O5]). The contingency is written as a body that nothing
  encloses, with the names in care as they were at the boundary and the
  message; it calls contingent operations and built-in ones, and each of its
  histories ends as chosen, after what [O5] or [F2] asks of its names.
  A named boundary takes owned parameters, retains some of them, and is
  written as a control that permits faults and ends with `terminate`; a
  retained name is consumed nowhere before that ([F6]). Its contingency
  sees the retained names and the message and ends with `terminate`, or
  with `escalate` or a new `fault` when it is drawn to let faults out, which
  makes `supervise` a statement that may fault. A campaign counts the runs
  that end in a fault that leaves the entry and with `terminate n`: both
  are ends, compared with the erased semantics as an outcome is.
  A boundary may stand in the work of another, to two works and five bodies
  in all. A fault then goes to the contingency of the inner one and, where
  that passes it on, to the next one around, so a statement that may fault
  answers for the ends of all the contingencies on its way (`settled`):
  what `recover` or `terminate n` of an outer one ends is given up before a
  statement of the inner work that may fault. `terminate n` belongs to a
  boundary that stands in the work of no other ([F5](e)).
- **Borrows in generated programs (`generate::valid_borrows`,
  `v2/src/generate/valid/borrows.rs`, `vn2 fuzz --slice 3`).** The
  generator of slice 2 with the borrows of slice 3; programs of slices 1 and
  2 are unchanged (600 seeds of each, text for text). For every name on
  every history it keeps the loans the name holds ([L1]): a place, as a
  root and the fields and indexes from it, and a mode. The name a borrow is
  bound to holds it, and so do the copies of a shared one, the name an
  exclusive one moves to, a borrow made through it, and a payload name of a
  decision whose contract field borrows from the argument. While a
  statement is written, a name that a live loan lends exclusively is not
  available to it, and one lent shared is read and not written, moved or
  lent exclusively ([L3]); the steps of slice 2 therefore keep the loans
  without knowing of them. A borrow of a place is made where no live loan
  overlaps it, unless both are shared; the test goes by places, so two
  fields of one struct may be lent exclusively at once. A loan ends where
  the generator stops mentioning each name that holds it ([L2]): a holder
  bound in the body being written is retired now and then and never named
  again. A loop body keeps what was lent around it lent throughout ([L2a]):
  an exclusive borrow name of a body around is either written in the body,
  and then nothing is known of it or of what it borrows, or kept read-only.
  What is known of the value behind a borrow name is what was known of the
  place ([I7]), with no integer taken as a constant ([I3] takes a name bound
  to a constant as that constant, and a borrow name is no such name); a write
  through it leaves what its exclusive loans are on known by its type alone
  ([I9]). Statements: `r : &τ := &p` and `r : &~τ := &~p` of names, fields
  and elements, also through borrow names; copies of shared and moves of
  exclusive borrow names; `r ← e`, `r.f ← e`, `r[i] ← e`; borrow names read
  in expressions; a borrow name or `&r`, `&~r` as an operand, of a built-in
  operation too; controls with borrowed parameters. An extern control may
  borrow its data, now and then one map or vector more (with a precondition
  on the length of a vector), and its payload fields may borrow places
  within the borrowed arguments, `&τ ∈ p` or `&~τ ∈ p`: a struct field, the
  whole value, a field of a variant, an element, a value or a key of a map
  (keys shared only). An alternative that the conditions may leave as the
  only one an argument allows asks only for a place that every argument
  has. A value that no name holds is bound to a name first where an operand
  borrows it, with `~` where it is lent exclusively. The seeded host of
  slice 3 (`host::Seeded::writing`) writes, now and then, a drawn value
  behind an argument lent exclusively whose referent holds no obligation and
  that the condition of the alternative does not mention, and then names
  the places of the payload in what it left ([E-Extern], [E-Host]).
  `generate::BORROW_CONSTRUCTS` lists the 20 constructs of the slice;
  `v2/tests/harness.rs` runs 300 seeds in the two semantics, requires every
  construct of the three slices and every kind of place lent, and asks the
  checker about 31 seeds. Over 900 seeds `vn2 fuzz --slice 3` gives 36,396
  runs with no stuck run and no difference, 3,590 of them ending in a fault
  and 1,076 with `terminate n`, the checker accepts all 900, and the hosts
  lent 8,691 whole arguments, 758 fields, 42 fields of variants, 731
  elements, 23 values and 38 keys of maps. With `--native`, 300 programs
  give 25,736 compiled runs that end as the oracle's do, with 29,692
  allocations, each released. Review findings RG8 and RC30 came from it.
- **Fuzzing (`fuzz`, `vn2 fuzz`).** `vn2 fuzz --seed N --count N` takes the
  program of each seed through the reader, the oracle and the erased
  semantics on entries that satisfy its precondition, and asks the checker.
  `--native` compiles each accepted program at `-O0` and `-O2`, for both
  widths of `usize`, and requires that every run ends as the oracle's did
  and with the same trace; a run that ends in a fault or with `terminate n`
  is compared as one that ends in an outcome. The runs of a program share a
  process, which has 60 seconds; where it fails, each run is compiled and
  run alone, and the finding names the runs that fail with the answers of
  their hosts. The harness counts the allocations of each run, and a run
  that ends with one live, or with more released than made, ends
  `undefined` and so differs from the oracle ([R4]); the report says how
  many allocations the compiled runs made. With
  `VN2_KEEP_IR=DIR` in the environment the text of every
  compiled module is kept in `DIR`. For slice 2 on 24 November 2026:
  300 programs, 23,432 runs of compiled programs with no difference, which
  make 26,768 allocations.
  `--mutants` tries every mutant too, where a
  mutant that the checker accepts must have no stuck run. A run of a mutant
  has 20,000 steps (`--mutant-fuel`), a tenth of the steps of a run of a
  program: a mutant that never ends uses all of them in every run. Each
  failure is a finding with its seed, and `--out DIR` writes the programs.
  The state on 23 November 2026: the reader, the two semantics, the checker
  and the compiled code have no finding over 300 seeds, in 11,728 runs in
  the oracle and 23,456 runs of compiled programs. The first run of the
  checker on these programs accepted 268, rejected 13, panicked on 16 and
  gave no answer within 20 seconds on 3; all 32 were defects of the decision
  procedure and of the declared interval of a multiple by a literal, and are
  repaired ([review](review.md), RC12, RC16). Of 5,403 mutants of the
  first 25 programs, `resolve` refuses 285, the checker rejects
  1,052 (a stuck run was found for 761 of them) and accepts
  4,066, none of which has a stuck run among those tried. With the kinds
  of 24 November these programs have 6,851 mutants: 832 refused, 1,068
  rejected (769 with a stuck run), 4,951 accepted; the report gives the
  counts for each kind, and the seven kinds of before have their numbers
  of before. For slice 2 (`--slice 2 --mutants`, 40 programs): 13,073
  mutants, 1,608 refused, 2,080 rejected (1,454 with a stuck run), 9,385
  accepted with no stuck run, and gives an answer in ten seconds on every one.
  These numbers are the same before and after the search was changed for
  review finding RC22. The time
  limit of the checker is of the clock. A check that reaches it ends
  (`counts::set_deadline`: the search asks for the time now and then, and
  so does the diagram package as a diagram grows); before 23 November it
  went on in its thread after the campaign had stopped waiting, and on a
  program of review finding RC22 it took 800 megabytes of memory in five
  seconds. On a machine under load, a campaign
  with a limit of four seconds reported four mutants as unanswered that the
  checker accepts in a third of a second; the numbers here are of a campaign
  with the limit of 20 seconds. `the_checker_accepts_generated_valid_programs`
  (`v2/tests/harness.rs`) holds the first part for 40 seeds.

## 9. The Rails surface reader and elaborator

`surface::elaborate` reads a program in the Rails surface syntax (or the plain
braced form of [G9]) and translates it into a `syntax::Program`, which
`resolve::resolve` then turns into the typed core. Every refusal names the
clause of [surface.md](surface.md) that excludes the text:

- **Layout ([Y1] to [Y10]).** Column-1 declarations and 4-space signature
  continuations ([Y1]); two-column rail segments `│ `, `║ `, `┆ ` and finished
  arm rails `  ` before `┆ ` ([Y2]); control rails `│ ` closed by `╵` ([Y3]);
  loop rails `║ ` ([Y4]); label junctions `╞═` on a control's rail and `╠═` on
  a loop's rail, never inside a `┆ ` block ([Y5]); tests `? e →` on one line or
  opening a `┆ ` block ([Y6]); vertical arms `├ ` and `└ ` with `│ ┆ ` and
  `  ┆ ` blocks, and horizontal arms `: a │ b` ([Y7]); content-indented
  statement continuations ([Y8]); blank rail lines and `┄` / `//` comments
  ([Y9]); prefix mismatch rejection ([Y10]).
- **Grammar and formatter ([G1] to [G10]).** Multi-line `■` contract entries
  ([G1]); `outcome` declarations, `…group` entries and single-name outcome
  contracts ([G2]); callee-first `■ auto` contract inference on private controls
  with group preservation and literal type agreement ([G3]); `↦ number` process
  exit statuses on outcome alternatives ([G4]); mask precedence and single-path
  `¬` ([G5]); first-line `⊢` loop invariants ([G6]); ASCII word spellings for
  all glyphs ([G7], [G8]); plain braced bodies, arms and `[mask]:` labels
  ([G9]); and `surface::format` (`vn2 format FILE... [--write | --check]`),
  which writes Rails, word-form and plain-form programs in canonical Rails glyph
  text with aligned vertical `→` arrows and aligned consecutive short labels
  while preserving elaborated core semantics and idempotence ([G10]).
- **Elaboration and warnings ([U1] to [U9], [U13] to [U18]).** Default and
  explicit (`name : Δ`) site names with collision checking ([U1]); path names
  from continuing arms, routes `→ name` and loop leaves `□ a`, and suppression
  on terminators and blocks ([U2]); qualified `site.alt` and unqualified path
  disjunctions with default-name ambiguity checking and route merging ([U3]);
  preceding-site scope checking ([U4]); two-path negation warnings ([U5],
  [U18]); statement elaboration under selection `σ`, including `? e → B`,
  Boolean decisions `Δ e` and single-outcome bare calls ([U6]); the
  acknowledgement rule for explicit and `…group` arms ([U7]); arm patterns
  `[~] name [: Type]`, patternless arms with hidden payload vars, and targets
  including `→ ■` ([U8]); loop alternatives collected from `□`,
  `{name, field: expr}` outputs, inner variable renaming for [W4], bare `□` and
  zero-`□` loops ([U9]); adapters `■ Δ` ([U13]); `forward` with group and
  entry matching ([U14]); exit arity checking ([U15]); impossible-arm warnings
  when the fact logic proves an alternative cannot happen and the arm is not `⊥`
  ([U16]); and unused-route warnings when a route `→ name` is never mentioned in
  a later label mask ([U17]).

`v2/tests/surface.rs`, `v2/tests/checker.rs` and `v2/tests/slice1_surface/*.rails`
test every one of the 33 surface clauses of slice 1 with both an accepting
program and a rejecting or warning (`//! reject` / `//! warn`) test.

Since 23 November 2026 `v2/tests/surface.rs` also holds the tests that close
the reader's findings of the [review](review.md) (RS2, RS4, RS7 to RS9,
RS11), with their programs in `v2/tests/format/` (comments through the
formatter, and the canonical text of `spend.rails`, whose second control is
in the plain form on purpose) and `v2/tests/loop_names/` (the renaming of
[U9]). One of them puts a comment at every position of every Rails file of
the suite and requires that the formatter keeps it.

## 10. The phase 3 checker, certificates and counterexamples

`check::check` judges a resolved `typed::Program` against every checking clause
of slice 1:

- **ROBDD histories and Boolean structure (`bdd`, [K1] to [K8]).** Each site
  alternative `d.a` and each canonical positive linear inequality atom
  `Σ aᵢ·uᵢ ≤ b` is a variable of one reduced ordered binary decision diagram.
  Selectors ([K1]), statement reachability `Rᵢ = Lᵢ ∧ gᵢ` ([K2]), live-history
  updates across dispositions, decisions and loops ([K3]), site implications
  and mutual exclusion ([K4]), test totality ([K5]), generic loop iterations
  with `L₁ = R_d` ([K6]), body coverage `Θ ⊨ ¬Lₙ₊₁` ([K7]) and exact loop-arm
  reachability `d.a ↔ R_{j₁} ∨ … ∨ R_{jₖ}` ([K8]) are formulas of that diagram.
- **Facts, SSA renaming and availability ([N1] to [N5], [C2], [O1], [O2], [O4],
  [O6], [F3]).** Entry parameter bounds and preconditions ([N1]), binding and
  assignment equalities with multiplexer collapse at joins ([N2]), `⊢`
  assumptions ([N3]), test, decision and loop outcome facts ([N4]), fresh
  logical versions on assignment and loop entry ([N5]), full decision
  acknowledgement ([C2]), definedness `D(x)` on histories for disjoint binding
  ([O1]), reads ([O2]), assignments ([O4]) and outer names across loops ([O6]),
  and effect inclusion on feasible histories with private-control effect
  inference in `surface::elaborate` ([F3]).
- **Fact logic `Th_Z` and obligations (`facts`, [S1] to [S6], [I1] to [I13],
  [A1], [A2], [A7] to [A9], [J1] to [J6], [P1] to [P8]).** Transparent function
  unfolding ([I8]), pure operation congruence `alt_f` and `pay_{f,a,i}` ([I10]),
  Boolean value terms ([I13]), fixed-width and `usize` ranges ([A1], [A2]),
  division and remainder by constants ([A7]) and terms ([A8]), four-corner
  product envelopes from declared intervals ([A9]), lazy CEGAR refinement over
  `Ω`, `Ψ` and `[J3]`, and the theory check of `lia`: equalities replaced,
  variables with a unit coefficient projected out, the simplex method over
  the rationals, a search for a model along the splits before each round
  of rounded sums, the Omega test, and behind it splits that take turns,
  with a proof as a tree of the steps of [V3] that is pruned to what its
  ends rely on. The Omega test has half of the steps that are left and
  starts from the rows as they were given; where it does not end, the
  splits have the other half. It changes variables in an
  equality without a unit coefficient, and for a variable that no side
  bounds with units it tries the sums of the bounds as they are, then the
  sums of the bounds tightened by the distance that the coefficients fix,
  and then one equality, a splinter, for each value within that distance.
  Its search has the shape of its proof: a split for each bound, with the
  splinters on one side and the tightened bound on the other. The refinement
  starts from the goal and the structure. A candidate that has a model is
  completed to one of every term (`facts/completion.rs`): a quotient, a
  remainder and a product are what their operands make them; a constructor
  term, a vector literal and a string literal are the number of their
  content, one number for one content; the terms that the candidate only
  says are equal, or in an order, get the numbers of their contents in
  that order; and a field, a length and a tag are those of the constructor
  term that has the number. Every premise and every instance that
  this model fails is conjoined before the next candidate is taken: a model
  that fails one fails several, and each would cost a candidate. A model
  that had one number for two contents failed an instance for every two
  constructor terms (review finding RC22). A node that the diagram grows
  by is a step of the limit of [J6].
  A model that fails nothing is the counterexample, and the goal and every premise are
  evaluated in it before it is shown ([M1]). The truth of a row in a model
  is worked out when a formula reads it. A query has three
  answers besides a fault of the procedure itself: proved, refuted with a
  model, and the counted limit of [J6], which is reported with the clause
  `J6` and is not a verdict. Checked obligations cover
  `⊢ φ` ([P1]), loop invariants at entry and `↑` ([P2]), function and control
  preconditions ([P3]), exit contract conditions `⇐ φₐ` ([P4]), arithmetic
  bounds and non-zero divisors ([P5]), unreachable `⊥` ([P6]), left-to-right
  and short-circuit `∧` / `∨` order ([P7]) and function bodies ([P8]).
- **Certificate kernel and counterexamples (`kernel`, [V1] to [V4],
  [M1] to [M6]).** For every yes the search returns a `Certificate`: the
  positions of the premises it used, the names of the instances
  (`terms::Instance`) and the lemmas with their proofs. The checker has
  `Kernel::validate` check it against the goal that the checker itself asked
  about (`kernel::Query`), and accepts only then ([V1]). The kernel reads the
  premises from the checker's lists, makes the formula of every instance
  itself, grants what rests on the type of a term only for a term that the
  checker wrote, validates the proof of every lemma, and conjoins all of it
  in a diagram of its own ([V2], [V3]). One kernel serves the queries of one
  body. `CheckedProgram` keeps the goal of every certificate and the solver
  of every body, and `CheckedProgram::revalidate` validates all of them again
  with a fresh kernel. `vn2 check FILE --certificates` writes all of them as
  a text, which is described below ([V5]). Every refuted obligation constructs
  an integer valuation and history witness verified against the query ([M1],
  [M2], [M6]), with nonlinear operator remarks ([M3]) and generic loop
  iteration notes ([M4]).

**The work of the search is measured by counts** (`counts`): queries,
candidates, theory checks and their rows, premises added, the nodes that
the diagrams came to hold, tableaus,
exchanges of the simplex method with the entries they write, splits, and
the theory checks that went on to the Omega test with the splinters it
tried. `vn2 check --counts` prints them, and `vn2 fuzz` prints their sum
over a campaign. A count is the same on every machine and
under every load, and by [J6] the same in every run: the checker keeps
names and terms in ordered tables, and a hash table is used only where
nothing reads its order (the tables of the diagram, the tables that give
a term or a row its number, and sets that are only asked whether they hold
a thing). The counts of 24 November 2026, for the
ten surface programs of the three slices: 553 queries, 568 candidates, 536
theory checks of 5,012 rows, 1,015 premises added, 23,301 nodes, and no
exchange. For the
data kernel of slice 2 (`v2/tests/kernels/slice2_data.rails`): 212 queries,
607 candidates, 490 theory checks of 16,239 rows, 95,568 nodes, 1,299
exchanges that write 35,514 entries, and 632 splits (before a model gave a
content one number: 915 candidates and 581 theory checks of 35,051 rows).
Over the 6,851 mutants of 25 generated programs: 1,323,287 queries,
1,664,289 candidates, 1,480,640 theory checks of 25,703,861 rows,
274,463,989 nodes, 264,489 exchanges that write 3,515,700 entries, and
84,201 splits. Six of these theory checks go on to the Omega test, with 24
splinters between them; before the test was asked ahead of the splits that
take turns, one did, and the exchanges wrote 7,881,928 entries. Over the
13,073 mutants of 40 programs of slice 2: 2,836,869 queries, 2,215,849
theory checks of 27,946,898 rows, 3,814,652 premises added, 453,442,725
nodes, and 8,743,177 exchanges that write 248,677,216 entries (before:
2,428,111 theory checks of 45,332,785 rows, 7,173,936 premises added, and
357,502,067 entries). The answers are the same, mutant for mutant.

`v2/tests/kernel.rs` tests the kernel's matcher: every instance of [A1],
[A2] and [A7] to [A9] that it grants is evaluated with the values that the
real operations give, on operands at the ends of every type and beyond them;
the kernel grants every instance that the search makes for terms of every
form; and it refuses eighteen names that name no instance, and the range of a
term that the checker did not write. Every instance of [A3] to [A6] is
evaluated with values of the oracle as well (section 12.4).

`v2/tests/checker.rs` tests every checking, fact-logic, certificate and
counterexample clause of slice 1 with accepting and rejecting programs, verifies
that the kernel refuses a certificate without its lemmas, its instances or its
facts, with a wrong step, with a name that is no instance, with a premise that
the checker did not state, and as the answer to another goal, checks
all four `.rails` programs in `v2/tests/slice1_surface/`, the template with
80 sets of numbers (over 1,000 kernel-validated certificates) and ten
generated programs, and verifies that every stuck mutant of four generated
programs, and every stuck mutant and every `DropInvariant` mutant of the
template, is rejected by `resolve` or `check::check`. Two tests hold the
search itself: a program that is checked a second time, on another thread,
gives the same certificate text and the same counts (30 programs with 2,136
certificates: the surface programs, the data kernel, four generated
programs, and the expansion of each); and the data kernel, its expansion,
and a program whose exit condition rests on remainders and a product
(`v2/tests/kernels/remainders_and_products.core`) are checked within a
stated number of theory checks and of entries written. The last is a mutant
that a campaign found: it is valid, one of its candidates has rows that
the splits do not decide, and its answer was the limit of [J6] until the
Omega test refuted that candidate. A precondition on the difference of two
parameters, which bounds neither, holds the Omega test in the checker: the
splits do not end on it, the answer was the limit of [J6], and it is now a
proof with sixteen splinters that validates from the certificate text.
Five programs of the generator of slice 2 on which the checker gave no
answer, or one after a minute (review finding RC22), are in
`v2/tests/kernels/` too: four are checked within a stated number of theory
checks, of premises and of nodes of diagrams, and the fifth, in which a
candidate without a model kept the splits, within a stated number of
entries. A body of sixteen tests has no answer with sixty steps, though
its questions take fewer candidates, tableaus, exchanges and splits than
that: the nodes of its diagram are steps. The
same test holds the limit that remains: a wedge between two lines with
coefficients of a million has no integer point and about a million
splinters, and its answer is the limit of [J6], after 283,119 splinters
and 0.7 seconds with the two million steps of a query.

The tests of `v2/src/lia.rs` compare the theory check with a search of
every point on 3,000 sets of rows in a box. Those of `v2/src/lia/omega.rs`
do the same for the Omega test alone, on 3,000 sets of rows in a box, on
1,500 in which each variable is a sum of two terms and none has a bound,
and on 1,500 pairs of thin bands, many of which have rational solutions and
no integer one; the kernel validates every proof, and every model is
evaluated.

### The certificate text ([V5])

`vn2 check FILE... --certificates` prints the certificates of the files as
one text, and `vn2 validate TEXT...` reads such texts and validates every
certificate in them. A text holds each query as well as what the search
found for it ([V2]). What reads it therefore needs neither the program nor
the checker: `certificate::read` makes the tables, the goals and the premises
from the text alone, in a diagram of its own, and `Body::validate` gives them
to a kernel. The reader uses the integers, the diagram and the data of
`terms`, and nothing of the search. That the queries are the ones the program
gives rise to is outside the text, as it is outside the kernel ([V4]).

A text is lines. An empty line says nothing, and neither does a line that
begins with `#`. A line is words with spaces between them. Each of `{`, `}`,
`[` and `]` is a word by itself. A string is in double quotes, with the
escapes `\"`, `\\`, `\n`, `\r`, `\t` and `\u{…}` (hexadecimal). The first
line is `villanelle certificates 1`. Bodies follow, one for each body of the
program that had a question. A body is the line `body`, its tables in the
order of this list, its questions, and the line `end`:

| Line | States |
| --- | --- |
| `history hK "site" "alternative"` | History atom `K`: the site took the alternative. Numbered from 0, in order |
| `term uK written FORM`, `term uK added FORM` | Term `K`, numbered from 0, in order. `written`: the checker wrote the term. `added`: the search added it, as a term that an instance speaks of |
| `row aK {FORM} <= B` | Row `K`, numbered from 0, in order: the linear form is at most the integer `B` |
| `arity S N` | Struct `S` has `N` fields |
| `node nK V nL nH` | Formula `K`: formula `H` if `V` holds, and formula `L` if not. `V` is a history atom `hK` or a row `aK`. `n0` is false and `n1` is true. A formula is stated before it is named |
| `question "control" LINE "clause"` | A question: what the clause asked at that line of the control |
| `goal nK` | The goal of the question, negated. It comes first |
| `structure nK`, `fact nK` | A premise: a formula of `Ω`, a fact of `Ψ` |
| `instance NAME` | An instance of the theory ([J3]), by its name |
| `lemma LITERALS` | A theory lemma: the literals do not hold together. A literal is a row `aK`, or `!aK` for its negation. The proof follows, a step a line |

The tables of a body are as they stood at the end of the body, and all its
questions share them. A linear form is `{c k*uI …}`: the constant, which is
left out when it is zero, and each term with its integer coefficient. The
form of a row and of a split has no constant.

The forms of a term ([S6]) are these. A term stands for one integer: a value
of another sort is counted by one ([J1]).

| Form | Term |
| --- | --- |
| `var "name" TYPE RANGE` | A logical name. `TYPE` is an integer type or `none`. `RANGE` is `ranged` when [A1] gives the name the range of its type, and `free` when it does not |
| `usize-max` | `usize.max` ([A2]) |
| `div-const {t} k` | `t ÷ k` for a literal `k ≥ 1` ([A7]) |
| `div {s} {t}`, `rem {s} {t}` | `div(s, t)` and `rem(s, t)` ([A8]) |
| `mul {s} {t} a A b B` | `mul(s, t)`, with the declared interval `[a, A]` of `s` and `[b, B]` of `t` ([A9]). A bound that is not known is `none` |
| `pure-alt F [ARGUMENTS]` | `alt_F(t̄)`, the alternative that the pure operation `F` takes ([I10]) |
| `pure-pay F A I [ARGUMENTS]` | `pay_{F, A, I}(t̄)`, field `I` of the payload of its alternative `A` |
| `len {t}` | `len(t)` ([A3]) |
| `str "text"` | A string literal |
| `empty-map "key" "value"` | `∅`, with the types of its keys and of its values. A literal is a term of its type |
| `vec "element" [ITEMS]` | A vector literal, with the type of its elements |
| `struct S [ARGUMENTS]` | The constructor term `S {t̄}` ([A4]) |
| `field {t} S I TYPE KIND RANGE` | `t.xᵢ`, field `I` of struct `S`. `KIND` is `bool` or `other`; `TYPE` and `RANGE` are as for `var` |
| `ctor V C N [ARGUMENTS]` | Constructor `C` of the `N` constructors of variant `V`, applied ([A5]) |
| `tag {t} V N` | The number of the constructor of `t`, a value of variant `V` |
| `index {t} {i} TYPE KIND RANGE` | `t[i]` ([A6]) |
| `update {t} {i} {e}` | `t[i ↦ e]` ([A6]) |
| `trim {t}` | `trim(t)` ([S5]) |

An instance is named, and the kernel makes its formula ([V2]):

| Name | The instance |
| --- | --- |
| `term uK` | What the theory says of term `K` by itself. For a `ranged` name, field or element that the checker wrote: the range of its type, or `0 ≤ u ≤ 1` for `bool` ([A1]); a field or an element of a constructor term, a literal or an update term has none. For `usize-max`: `2³² - 1 ≤ u ≤ 2⁶⁴ - 1` ([A2]). For `len`: `0 ≤ u ≤ usize.max`. For a vector literal and `∅`: the length ([A3]). For a `ctor` that the checker wrote: `tag(u) = C`. For a `tag` that the checker wrote, or whose value is such a `ctor`: `0 ≤ u ≤ N - 1` ([A5]). For an `update`: `len(u) = len(t)`, and `0 ≤ i < len(t)` implies `u[i] = e` ([A6]). For `div-const`, `div` and `rem`: the bounds of [A7] and [A8]. For a `mul` that the checker wrote: those planes of [A9] whose two bounds are known |
| `pair uI uJ` | What it says of two terms together. For two applications of one symbol: equal arguments imply equal results ([S5]); for two applications of one constructor, the converse too ([A4], [A5]). For two different string literals and for two different constructors of one variant: the terms are not equal ([A3], [A5]). For a field term and a constructor term of its struct: if the value of the field term is the constructor term, the field is the argument ([A4]) |
| `frame uU uE uO` | For the update term `U` = `t[i ↦ e]`, its element `E` = `U[j]` and the element `O` = `t[j]`: `j ≠ i` implies `E = O` ([A6]) |
| `extension S uL [FIELDS] uR [FIELDS]` | For two values of struct `S`: equal fields imply equal values ([A4]). A side is a constructor term, with no field listed, or another term with the field term of each of its fields, in order, each written by the checker |

The formula of an instance is over the rows of the table. Each comparison in
it is brought to the canonical form of a row (step 2 of the reference
procedure: the coefficients divided by their common factor and the bound
rounded down, with the first coefficient positive; a comparison whose first
coefficient is negative is the negation of the row of its complement). An
instance is refused when the table lacks a row or a term that it needs.

A proof ([V3]) refutes the literals of its lemma. Its steps and its end are
these lines:

| Line | Step |
| --- | --- |
| `literal I` | The row of literal `I` of the lemma, counted from 0: the row `e ≤ b` of `aK`, or for `!aK` its complement `-e ≤ -b - 1` |
| `combine M*pR …` | The sum of rows of the path, each with a positive integer multiplier |
| `round pR D` | From row `R`, whose coefficients the integer `D ≥ 1` divides: the coefficients divided by `D`, and the bound divided by `D` and rounded down |
| `close pR` | The end of a branch: row `R` is `0 ≤ b` with `b < 0` |
| `split {FORM} <= B` | The end of a branch in two. The proof of the first follows, with the row `FORM ≤ B` more, and then the proof of the second, with the row `FORM ≥ B + 1` |

`pR` is a position on the path from the root of the proof, counted from 0.
Every step adds its row to the path, and so does a split, for each of its two
branches. A branch sees the rows of the branches above it and its own. The
reader takes a proof in which at most 256 splits nest, which is as deep as
the search goes.

For a question the kernel validates the proof of every lemma, makes the
formula of every instance, and requires that these have no case in common:
the goal, the premises, the instances, and for each lemma the statement that
its literals do not all hold. This text states that no `x` of type `u8` is
greater than 300, and was written by hand:

```text
villanelle certificates 1
body
term u0 written usize-max
term u1 written var "x" u8 ranged
row a0 {1*u1} <= -1
row a1 {1*u1} <= 255
row a2 {1*u1} <= 300
node n2 a2 n1 n0
question "by hand" 1 "N2"
goal n2
instance term u1
lemma a1 !a2
 literal 0
 literal 1
 combine 1*p0 1*p1
 close p2
end
```

`v2/tests/certificate.rs` tests the text. The text of every surface program
of slices 1 to 3 and of twelve generated programs is read back: the tables
are those of the check, every goal and premise is the same formula, every
certificate is the same, and the kernel validates all of them from the text.
The text above validates, and is refused with the bound 200, without its
lemma, and with `x` as a term that the search added. A text of the checker
is refused after each of eight changes: a question without its facts, with
another goal, with a row whose bound was raised, with a term marked as
added, with an instance that is none, with a proof that closes on a row
that is no contradiction, with a proof that has no end, and with the
literals of a lemma negated. The reader refuses thirty-four texts that are
not well formed. A proof in which 256 splits nest is read and validated, and
one with 257 is refused. Names and literals with quotes, line breaks and
brackets in them are read as they were written.

The reader and the kernel are one crate, by one hand. A second checker that
another hand writes from this description is not there.

## 11. Call expansion (Theorem 4) and the phase 4 typed LLVM IR backend

- **Call expansion (`expand`, `vn2 expand FILE`, Theorem 4 of [core.md](core.md)
  section 8).** `expand::expand` replaces every decision on a defined control in
  place by the callee's body with fresh names and sites, binding the callee's
  parameters to the call arguments, preserving the callee's precondition (`⊢ φ`)
  and exit conditions (`⇐ φₐ`) as `[P1]` obligations, lifting any `■` (`Exit`)
  inside a loop of the callee out of the loop through a fresh `□` (`Leave`)
  alternative, binding the caller's arm variables at each exit of the callee,
  and substituting the disjunction of the callee's exit histories for each atom
  `d.a` in the rest of the caller's body. Every expanded program re-parses,
  resolves, passes `check::check` with kernel-validated certificates, and yields
  the same observations in the oracle, the erased interpreter and native code.
- **Typed LLVM IR and C ABI emission (`codegen`, `vn2 emit-llvm FILE`, `vn2
  emit-c FILE`, [core.md](core.md) section 9, `[R1]` to `[R3]`).**
  - **[R1]** Every variable slot is a native scalar `alloca` (`i1`, `i8`, `i16`,
    `i32`, `i64`, with `usize` lowered to `i32` or `i64` according to
    `--usize 32|64`), promoted to SSA registers by LLVM's `mem2reg`. There are
    no dynamic value tags, no moved marks and no runtime frame tables.
  - **[R2]** `⊢` obligations, loop invariants, preconditions, exit conditions
    `⇐` and effect allowances emit zero instructions. Arithmetic compiles to
    direct machine operations (`add`, `sub`, `mul`, `udiv`/`sdiv`,
    `urem`/`srem`), short-circuit `∧`/`∨` to conditional branches, and functions
    to `alwaysinline fastcc` helpers. `⊥` (`Impossible`) and decision switch arms
    guarded by `site.alt ▷ ⊥` emit `unreachable`, so LLVM's optimizer deletes
    impossible branches (in `spend.rails`, `checked_sub.underflow → ⊥` is folded
    into `unreachable` with zero history bits allocated for `checked_sub`).
  - **[R3]** Only `(site, alternative)` atoms mentioned in non-erased selectors
    allocate an `i1` history bit. Entering a loop clears only the bits of sites
    belonging to that loop body.
  - **Typed C ABI.** Each `extern` control is declared as `i32 @vn2_ext_<name>`
    and each defined control exports `i32 @vn2_call_<name>`, returning the
    0-based alternative index in `i32` and writing payload fields through typed
    output pointers. `codegen::emit_c_header` emits the matching C header with
    `#define VN2_<CONTROL>_<ALT>` constants and prototypes.
- **Differential native verification and paired Rust benchmark
  (`v2/tests/backend.rs`).** `codegen::run_native_batch` compiles programs with
  `clang -x ir` at both `-O0` and `-O2` (original and Theorem-4-expanded) and
  verifies agreement on outcomes and event traces against `oracle::run` and
  `erased::run` across all `.rails` programs, the template with eight sets of
  numbers and six generated programs (32-bit and 64-bit `usize`); the
  expansion of each passes the checker and ends in the oracle as the program
  does. `vn2 fuzz --native` does the same for the program of any seed
  (section 8). In paired hot-loop measurements on Apple M2
  (`clang -x ir -O3` vs `rustc -C opt-level=3`, 5,000,000 iterations of composed
  Euclidean `gcd`, `spend_step` with `over → ⊥` erased, and modular accumulation,
  measured separately from launch and output with `clock_gettime`), compiled v2
  runs in **12.99 ms** against optimized Rust in **13.11 ms** (**0.991×** of
  optimized Rust), with identical checksum (`432,500,000`). The kernel is
  written inside the test and is scalar code, which allocates nothing by
  construction; allocations were not measured, and the test asserts nothing
  about the ratio. This is not the measurement of the phase 4 exit, which is
  every kernel under `experiments/` for time, allocations and peak memory
  ([review](review.md), RB6).

## 12. Slice 2 Phase 2: Data, Resources, Captured Outcomes, Faults, and Boundaries

Slice 2 Phase 2 extends the core syntax (`syntax.rs`, `text.rs`), resolver
(`typed.rs`, `resolve.rs`), instrumented oracle (`oracle.rs`), erased semantics
(`erased.rs`), differential harness (`differential.rs`, `script.rs`, `host.rs`),
and Rails surface reader, elaborator, and formatter (`surface.rs`):

- **Types and usage kinds (`[T1]`–`[T6]`, `[W5a]`, `[W6]`–`[W8]`).** Adds
  `string`, `[pub] [copy] struct`, `[pub] [copy] variant`, `[τ]` (`vector<τ>`),
  `κ ⇀ υ` (`map<κ, υ>`), `extern resource R [on fault release]`, `outcome⟨O⟩`,
  and `&τ` / `&~τ` parameter and operand modes. `resolve.rs` checks type-cycle
  rejection (`[T1]`), `copy` kind propagation (`[T1]`/`[G4b]`), function
  must-parameter prohibition (`[W5a]`), borrow nesting (`[W6]`/`[T6]`),
  `old(y)` on `&~` parameters (`[W7]`), and non-borrow assignment (`[W8]`).
- **Instrumented semantics (`oracle.rs`).** Implements `Slot::{Available,
  Moved}`, move-on-consume (`[E-Var]`, `X2 E-Var`), partial-move rejection
  (`X2 E-Field`, `X2 E-Index`), bounds checking (`X7 E-Index`),
  non-lending-before-lending operand order (`[E-Operands]`) with `&~`
  writebacks, temporary obligation check (`X5 E-Temp`), struct unpacking
  (`[E-Unpack]`), place assignment (`[E-Assign]`, `X2`/`X5`), captured outcomes
  (`[E-Capture]`, `[E-Outcome]`), resource open/close lifecycle
  (`[E-Resource]`), scope obligation check (`X5 E-Scope`), faults and unwinding
  (`[E-Fault]` / `X8 E-Fault`, `[E-Unwind]` / `X8 E-Unwind`, `[E-Root]`),
  lexical boundaries (`[E-Boundary]`, `[E-Contingency]` with `recover ↑ ℓ`,
  `escalate`, `terminate`), named boundaries (`[E-Supervise]`, `X2
  E-Supervise`), and all eight built-in operations (`push`, `pop`, `take`,
  `get`, `insert`, `remove`, `entry_at`, `emit`).
- **Erased semantics (`erased.rs`, `[R4]`, `[R5]`).** Computes static
  availability formulas `avail_at[body][pc][var] = D(var) ∧ ¬M(var)` as
  history-bit selectors during planning (`plan()`) with zero runtime moved
  flags, and releases `on fault release` resources during fault unwinding using
  those selectors alone. Since 23 November 2026 (review finding RO5) the
  formulas of a body take what the bodies inside it do to its names: after a
  boundary a name is as the work left it at its end, and after a loop as the
  `□` that ended the loop left it; on a history on which the boundary or
  the loop did not run, as it was before (RB12: the atom of the boundary's
  alternative, or none of the bits of the loop's `□`, says so). For the
  second the interpreter keeps one
  more bit of the history for each `□` of a loop that leaves some name
  otherwise than the loop found it; [O6](b) makes the `□` of one alternative
  agree, so in a checked program such a bit says no more than the atom of
  the alternative, and the interpreter is spared deciding which of the three
  answers of [O6](b) holds. A contingency finds the names around its
  boundary as the statement of the work that faulted left them ([F5]): the
  layout keeps a bit for each statement of the work that may fault and
  leaves some such name otherwise than the boundary found it, the fault sets
  it, and the formulas of the contingency are written over these bits. So
  the formulas of a statement cover the names of every body around it, and
  a fault or a terminator ends each scope by the formulas of the statement
  at which it occurred ([R3] and [R4] of the core, which say so since that
  day). `erased::layout` is this layout and the backend takes it from there
  (RB1): the interpreter runs the formulas that compiled code evaluates. A
  fault at a statement where the layout expects none ends the run as
  undefined. Differential tests verify exact outcome and trace
  agreement (including `conn.release(...)` events and `faulted "..."` ends)
  between `oracle` and `erased`.
- **Rails surface & formatter (`surface.rs`).** Adds layout (`[Y12]`),
  grammar (`[G4a]`, `[G4b]`, `[G7a]`, `[G12]`, `[G8]`/`[G9]` plain and ASCII
  forms), elaboration (`[U6]` variant & captured-outcome decisions, `[U10]`
  `∀ x ∈ p`, `[U11]` move marks `▾` and `~` borrows, `[U12]` method form with
  module-control rejection, `[U14]` `■ ▾x`), and canonical Rails formatting
  (`[G10]`).
- **Conformance suite (`v2/tests/slice2.rs`, `tests/slice2/*.core`,
  `tests/slice2_surface/*.rails`).** 37 core files (13 before section 12.1) and 4 canonical Rails files
  (including `show_file_resource.rails` from section 2 of `surface.md`) with
  accepting, rejecting, stuck-state, core round-trip, formatter idempotence,
  and oracle-vs-erased differential checks.

### 12.1 Fault boundaries, as requalified on 23 November 2026

The rules of fault boundaries were wrong in three ways (review findings RO1,
RO3, RO4). They now follow sections 6.9 and 7.7 of the core, which say since
that day how each end of a contingency runs.

- **What `resolve` refuses.** The requirements of form of [F5] and [F6]. In
  a contingency there is no `■`, no boundary, no `supervise`, and `↑` and `□`
  only of a loop of the contingency itself. The contingency of a lexical
  boundary mentions the names it retains, the message and its own: a name or
  a site of the body around it is not found (`C1`, `W2`). `terminate`
  without a status ends a body of a named boundary and occurs nowhere else.
  `terminate n` occurs in the contingency of a boundary of a control that is
  inside no other boundary, with a literal from 0 to 255, and a control that
  holds one is invoked by nothing. `recover ↑ ℓ` names a loop around its
  boundary, and the body of the boundary does not mention a parameter of
  that loop. `□` in the body of a boundary leaves the loop around the
  boundary; its operands are built where the statement stands, where the
  names of that body are in scope.
- **Unwinding** is one function, `unwind`. The scopes of the current
  activation end innermost first. The scope of a lexical boundary starts its
  contingency; the body of a named boundary starts its own when only its
  scope is left; an activation with no scope left is popped, and the caller
  permits `faults` or has a boundary around the waiting statement. The
  erased interpreter has the same order, and moves the frame around a
  boundary past the boundary statement when a fault leaves the contingency,
  so that what the boundary had taken is not released a second time.
- **The ends of a contingency.** `recover ↑ ℓ` reads the parameters of the
  loop as operands, ends the scopes up to the loop by [E-Scope] and enters
  it again; no copy of the parameters is kept. `escalate` finds the message
  of the innermost contingency, from inside a loop as well. `terminate n`
  ends every scope of the entry activation by [E-Scope] and gives the end
  `terminated n`; `terminate` ends the scopes of a body of a named boundary
  and lets the supervising control go on.
- **The backend** follows: it kept a copy of the parameters of a restarted
  loop, taken when the loop was first entered, and restored it at `recover`.
  The parameters now stay in their slots. The driver prints `terminated n`.
- **Conformance.** `lexical_boundaries.core` (12 runs that end, each also
  compiled and compared at `-O0` and `-O2` in
  `slice_two_core_programs_agree_natively`), `lexical_boundaries_stuck.core`
  (12 stuck runs: X1, X2, X5, X7 and X8 in the ways a boundary can reach
  them), 22 files `reject_*.core` for the requirements of form, and seven
  more runs of named boundaries in `faults_and_boundaries.core`. The suite
  of slice 2 has 37 files and 64 runs.

### 12.2 Hosts, built-in operations and exit conditions, as requalified on 23 November 2026

Five further findings of the review are closed (RO2, RO6, RO8, RO9, RO10).
Three of them are about borrows and have their tests with slice 3.

- **The condition of an exit** ([E-Exit], RO2). An activation keeps, for
  each parameter that is or holds a borrow, the borrow as it was passed, and
  the condition of an alternative reads the value at completion through it.
  The oracle read the parameter's slot, which is empty when the body passed
  the borrow on, and then took the value at entry: a true condition was
  stuck and a false one passed. `tests/slice3/exit_conditions.core`.
- **Borrows from a host** ([E-Extern], [E-Host], RO6): section 5.
  `tests/slice3/host_borrows.core` has 11 runs that end and 10 violations,
  and `the_seeded_host_answers_borrowed_payloads_with_places_within_its_arguments`
  (`tests/slice3.rs`) runs its controls under 60 seeds in both semantics.
  The native driver of the backend answered a borrowed payload with a
  value in a cell of its own, which is no place within an argument, until
  24 November (section 17.1).
- **Pure operations** ([I10], RO8): a resource inside a struct or a variant
  of the payload makes an extern control impure, so two calls may give two
  resources. `tests/slice2/pure_operations.core`, with the violation of a
  pure control that answers in two ways.
- **Built-in operations** (RO9, RO10). Their contracts are those of the
  corpus prelude, which the core now names. The collection of `push`, `pop`,
  `insert` and `remove` is `&~p` or a name of type `&~`, which passes the
  borrow itself and is moved by it; a value or `&p` is refused by `C1`. The
  map of `get` and `entry_at`, the key of `get` and `remove` and the text of
  `emit` are operands for a `&` parameter: `&p` or a name of that type;
  `&~p` is refused, and since 24 November a value too (RO14: bind it to a
  name first, as the surface does). Four files
  `tests/slice2/reject_c1_*.core` hold the refusals, and
  `tests/slice3/builtin_operands.core` the runs, with example 6.3 of the
  reference model, whose `insert` gives back the value it replaced.

### 12.3 The rules of the data, as requalified on 24 November 2026

Every rule that the data of slice 2 applies has a file of its own in
`tests/slice2`, as the rules of slice 1 have: the runs that apply the
rule, and a run for each way of being stuck by it. A comment over each
control says which sentence of the rule it holds.

| File | Rule | Stuck states it reaches |
| --- | --- | --- |
| `e_var.core` | [E-Var]: a read leaves the slot, a consumed name of kind `copy` stays, any other moves | `X2 E-Var` for a read, a move, a borrow, a formula, a base of a field, a payload name of another alternative, a second round of a loop, a second payload field and a loop parameter |
| `e_field_index.core` | [E-Field], [E-Index], and a term of a formula that indexes out of range | `X2 E-Field`, `X2 E-Index`, `X7 E-Index` (read, borrowed, assigned, in a base), `X7 E-Arith`, `X2 E-Var` |
| `e_build.core` | [E-Build]: the constructors, `∅`, `clone` | `X2 E-Var` (a field or an element consumed twice), `X7 E-Index` |
| `e_temp.core` | [E-Temp] | `X5 E-Temp` with a resource and with a captured outcome |
| `e_bind_unpack.core` | [E-Bind], [E-Unpack] | `X3 E-Bind` by an unpack, by a payload name and after a move; `X2 E-Var`; `X5 E-Scope` |
| `e_assign.core` | [E-Assign] | `X2 E-Assign`, `X2 E-Var` (a component of a moved or unbound root), `X5 E-Assign` (a name, a field, an element, an owner, a captured outcome), `X7 E-Index`, `X7 E-Arith` |
| `e_operands.core` | [E-Operands] | `X2 E-Var` |
| `e_outcome.core` | [E-Capture], [E-Outcome] | `X2 E-Var`, `X5 E-Scope`, `X7 E-Call` |
| `e_resource_scope.core` | [E-Resource], [E-Scope] | `X5 E-Scope` in a name, a parameter, a struct, a vector, a variant, a map, and at `↑` and `□` |
| `e_unwind_values.core` | [E-Unwind] through a value ([T3]) | `X8 E-Unwind` in a name, a struct, a vector, a variant, a map and a captured outcome |
| `checked_release_order.core` | [E-Unwind]: the order of release | none; the checker accepts it and it runs in compiled code |
| `op_vectors.core`, `op_maps.core`, `op_text.core` | The built-in operations, every alternative of each, and `trim` | `X2 E-Var`, `X9 E-Effect` |

38 more files `reject_*.core` hold a refusal of the reader each: the kinds
([T1], [T6]), the forms of types ([W4] to [W8]), the typing of
constructors, fields, indexes, unpacks, assignments and built-in operands
([C1], [C2], [C4]) and the move mark on a read ([O3]). The test
`slice_two_core_conforms_and_matches_erased` asks that 20 rules are
applied, 18 stuck labels reached and 15 clauses of refusal met; the suite
of slice 2 has 100 files and 358 runs, 236 of them compared with the
erased semantics. One of the files and 58 of the runs are those of section
12.4, with the label `X7 E-Oblige`. The oracle counts an application of
[E-Temp] now.

What the files found:

- **The order of release** (RO12). `Machine::unwind_scope_with_clause`
  visited the slots of a scope in the reverse of the order in which the
  run had bound them. It visits them by the ids of their names now, which
  `resolve` gives in the order in which the text of a body first binds
  them; [E-Unwind] of the core states that order.
- **A component of a moved root** is `X2 E-Var`, and [E-Assign] of the
  core says that the root is looked up.
- **An outcome type that names a control** is refused in a declaration
  (RO13, open).

The checker is held against the same files control by control.
`check::check_each` gives the verdict on every defined control of a
program, each checked against the signatures of the others, and
`script::Report::stuck_in` the controls in which a run was stuck.
`the_rule_files_of_the_data_are_rejected_exactly_where_a_run_is_stuck`
(`tests/checker_slice2.rs`) asks that the two agree: of the 124 controls
of the fourteen files the checker refuses the 62 in which a run is stuck
and accepts 59. The other three are in a table of the test with the
reason: an empty vector of resources holds no obligation and its type has
kind `must` ([O5]); an empty vector of locks is destroyed under a fault
and its type is not fault-releasable ([F2]); and an effect is stuck in the
control that has it, where the control that does not allow it is its
caller ([F3]).

A counterexample gives no number for a name of a data type (RC25): the
model of the search has one for every term, and it is no value of the
name. `Solver::counterexample` leaves such a name out and gives its
length where the model has one.

### 12.4 The axioms of the data, held against real values on 24 November 2026

Soundness needs that every instance of the theory is true of real values
(section 6 of the [fact logic](facts.md)). For [A1], [A2] and [A7] to [A9]
`tests/kernel.rs` has held that since the kernel makes the instances. For
[A3] to [A6], and for [S5] on a field, an element, a length, a write and
`trim`, three tests of the same file hold it now.

- `the_instances_of_the_data_axioms_hold_for_real_values` writes terms as
  the checker writes them, in 200 worlds drawn at random: names of sixteen
  types (integers, `bool`, `string`, two structs, a variant, six vector
  types, two map types) that hold values of the oracle, and over them
  fields, elements, lengths, constructor terms, literals, writes of an
  element, the names that a decision gives the fields of a variant value,
  and names bound to the value of a term. A term has the value that the
  oracle's operation gives. An element out of range is the oracle's value
  for the type ([E-Formula]), and a write out of range leaves the vector
  as it was. Every term then gets a number: its value for an integer, zero
  or one for a truth value, and for any other value a number that no other
  value has, of its type or of another. Every instance that the search
  makes is granted by the kernel and true for these numbers. The test
  counts the instances of each part of the theory, and where an instance
  has a condition it counts those whose condition holds.
- `a_wrong_value_makes_the_instance_of_its_axiom_false` gives one term a
  number that is not that of its real value, sixteen times: a literal of
  two elements with the length three, `∅` with an entry, a length below
  zero and one above `usize.max`, two string literals that are one value,
  a field that is not the argument, constructor terms with different
  arguments that are one value and with equal arguments that are two, two
  values with equal fields that differ, a constructor term of another
  constructor, terms of two constructors that are one value, a value of
  no constructor, a write that changes the length, a written element that
  is not what was written, and a write that changes another element. Each
  time the instance of the axiom is false. Four more numbers are wrong
  where the condition of the instance does not hold, and the instance
  stays true.
- `a_literal_at_two_types_is_two_terms`: `[]` at six types, `∅` at two,
  and `[1, 0]` beside `[true, false]`. Before this test the crate had one
  term for each of the three, and a value of one type had the number of a
  value of another.

`tests/slice2/facts_data.core` has the same axioms as statements of a
program, and the oracle says what is true: an obligation `⊢ φ` that a run
finds false is stuck ([E-Oblige]). Each axiom is there as a statement that
every run finds true, with a statement beside it that some run finds
false. `the_axioms_of_the_data_are_proved_and_what_they_do_not_say_is_not`
(`tests/checker_slice2.rs`) holds the checker against the 58 runs, control
by control, as section 12.3 describes: of the 49 controls it refuses the
21 in which a run is stuck and proves 23. The other five are true of
every run and not proved. Two are what the logic leaves out ([A3]): the
elements of a vector literal, and the length of a string literal. Three
are review finding RC26: two values of a struct without fields are equal,
two values of a variant with one constructor are equal, and a value of a
variant with three constructors is one of the three. The checker knows
the constructor of a variant value only where a decision has taken the
value apart.

With a literal as a term of its type the campaigns answer as before,
program for program and mutant for mutant. The search of the 13,073
mutants of slice 2 makes the same 2,215,849 theory checks, of 27,945,739
rows where there were 27,946,898, and adds 3,815,083 premises where it
added 3,814,652; the campaigns of slice 1, which has no literal of data,
count the same in every number.

## 13. Slice 2 Phase 3: Ownership, Faults, Boundaries, and Data Fact Logic

Slice 2 Phase 3 extends the checker (`check.rs`), fact logic (`facts.rs`), and
independent certificate kernel (`kernel.rs`) to verify all data, resource,
ownership, fault, and boundary constructs of slice 2:

- **Ownership (`[O0]`–`[O6]`, `[P8]`).** Tracks movedness `M(x)` alongside
  definedness `D(x)` on ROBDD histories (availability `D(x) ∧ ¬M(x)`). Checks
  non-lending-before-lending operand order (`[O0]`), disjoint binding (`[O1]`),
  availability at reads, moves, and borrows (`[O2]`), move-on-consume and
  rejection of non-copy partial moves (`[O3]`) and discarded `must` temporaries
  (`O3a`), assignment rules including preventing overwrite of available `must`
  values and mutating places of non-`must` type (`[O4]`), scope-exit
  completion obligations at `■`, `□`, `↑`, `terminate`, `recover ↑`, and
  lexical boundary fallthrough (`[O5]`), outer-name loop invariance at `↑`
  and across `□ a` leaves (`[O6]`), and `[O3]`/`[O3a]` inside functions
  (`[P8]`).
- **Faults and boundaries (`[F1]`–`[F6]`).** Enforces fault permission
  (`faults` signature or enclosing boundary, `[F1]`), emptiness of live
  non-fault-releasable values at any faulting statement (`[F2]`), effects of
  calls, `emit` (`console.write`), and `supervise` (`[F3]`), `assume ⊥`
  obligations (`[F4]`), lexical boundary capture moves, `B₁` fallthrough
  completion, contingency `in_contingency` restrictions (`[F5]`), and named
  boundary `B₁`/`B₂` checking including retained-parameter availability across
  possible faults (`[F6]`).
- **Data fact logic and kernel (`[A3]`–`[A6]`, `[I7]`, `[I9]`, `[I11]`, `[I12]`,
  `[M7]`).** Extends `AtomTerm` with `Len`, `StrLit`, `EmptyMap`, `VecLit`,
  `StructCtor`, `Field`, `VariantCtor`, `VariantTag`, `Index`, `Update`, and
  `Trim`; instantiates measure bounds and literals (`[A3]`), struct field
  projection, injectivity, and extensionality (`[A4]`), variant constructor
  distinctness, injectivity, and decision facts (`[A5]`, `[I11]`), vector update
  length preservation, read-after-write, and `[J3]`-finite frame axioms
  (`[A6]`, `[I9]`), `&~` post-exit parameters and `old(y)` (`[P4]`), vector
  index bounds `0 ≤ i < len(v)` (`[P5]`), captured-outcome contract propagation
  (`[I12]`), built-in collection contracts (`push`, `pop`, `take`, `insert`,
  `remove`, `get`, `entry_at`), kernel clause validation for `A3`–`A6` in
  `kernel::validate`, and `[M7]` counterexample extensionality notes.
- **Conformance (`v2/tests/checker_slice2.rs`, `tests/slice2_surface/*.rails`).**
  Tests accepting and rejecting cases for every Slice 2 Phase 3 clause,
  validates all generated certificates across all four canonical Slice 2
  `.rails` files (over 148 certificates), and confirms every stuck control of
  `tests/slice2/*.core` is rejected by its corresponding Phase 3 clause.

### 13.1 Captures, as requalified on 23 November 2026

Two programs that the checker accepted are stuck in the oracle (review
findings RC2 and RC3), and both are refused now.

- **A captured operation writes at the capture.** For `push`, `pop`,
  `insert` and `remove` the place gets a fresh name at the capture
  statement, as it does at a decision. The record of the capture keeps the
  collection before and after, and the decision of the outcome adds what
  the alternative says of the two (`shape_facts`: the conditions of the
  corpus prelude, and that the collection is the same on an alternative
  that leaves it). A decision that is written directly uses the same
  function.
- **The record goes with the value** ([I12]). An assignment to a name drops
  the record of its capture on those histories, a bind or an assignment of
  a captured outcome carries the record to the new name, and a loop that
  assigns a name of the body around it drops the record at its entry.
- **Tests that run the program too.** `stuck_and_rejected` and
  `done_and_accepted` (`tests/checker_slice2.rs`) take a program with its
  directive, require the oracle to find it stuck, or to run it to its end,
  and the checker to refuse it by the clause given, or to accept it with
  certificates that validate again. The tests of these two findings use
  them; the earlier tests of the file ask the checker alone.

### 13.2 Fault boundaries of the checker, as requalified on 23 November 2026

Four findings of the review are closed (RC4, RC5, RC6, RC20). Each test
runs its programs in the oracle too.

- **A contingency begins where the work faulted** ([F5], RC4). `B₂` was
  checked with the ownership of the names around the boundary as it was at
  the entry of the boundary. A work that fills an outer name before it
  faults was accepted and is stuck (`X5`); one that consumes it was
  refused. The checker now keeps, for the `B₁` under check, the state of
  ownership at each statement that may fault (`FaultState`, recorded by
  `check_may_fault`), and runs the checks of a terminator of `B₂` once for
  each state, with the names around the boundary as they were in it and on
  the histories of both statements (`for_each_fault_state`): [O5] at
  `terminate n`; at `recover ↑ ℓ`, [O2] for the parameters of the loop,
  which it reads as operands and moves, then [O5] and [O6]. A statement of
  `B₂` that may fault (`escalate`, `fault`, a call) hands each of those
  states on to the boundary around it, and [F2] and [F6] at such a
  statement leave out the names around the boundary, of which they were
  required where `B₁` faulted. The values of those names in `B₂` are the
  ones of before, forgotten where `B₁` writes them; `B₂` cannot name them.
- **What a boundary has in its care** ([E-Boundary], RC5). While `B₁` is
  checked the checker keeps what the boundary took, and every check of the
  scopes that a terminator ends ([O5]) refuses a value of kind `must`
  among it when the scope of `B₁` is one of them. The end of `B₁` is such
  a terminator.
- **The contingency of a named boundary** ([F6], RC6). A call there that
  may fault is refused by [F1], since nothing encloses it.
- **Effects through `supervise`** ([F6], RC20). `resolve` adds to the
  effects of a named boundary those of every boundary its `B₁` supervises,
  to a fixed point, so that they count toward whatever supervises it.

Tests: seven of `tests/checker_slice2.rs`, 22 programs.

Two smaller findings went with them.

- **The move mark of the text form** (RC7). `▾e` says that `e` is
  consumed, and the position of an expression decides that ([E-Var]). The
  oracle moved `v` at `len(▾v)` and the checker read it. `resolve` now
  refuses the mark on an expression that is read, by [O3]: under an
  operator, as an argument of a function, as the base of a field or an
  index, as the place of `len` or `clone`, in a borrow. On the value of a
  bind, an operand given by value, a payload or a field of a constructor it
  is accepted and says what the position says already.
- **The declared interval of a component** (RC8, [A9]). The checker gave a
  field or an element the interval of its type unless its base was a
  constructor written in place, so one level of nesting hid the
  constructor: `wrap {pair {a + 1, 0}}.inner.left` had the interval of a
  `u32`, which `a + 1` in a formula need not have, and the planes of a
  product by it proved what is false. A component now has that interval
  only as a component of a place.
- **The histories of a contingency** (RC21, [F5], [F6], [P6]). `B₂` was
  checked on every history of its boundary. It is checked now on the
  histories of the statements of `B₁` that may fault: the disjunction of
  the reach that `check_may_fault` records for each, so that `⊥` is
  accepted in the contingency of work that cannot fault and a fact of the
  faulting histories is known in `B₂`. The `B₂` of a named boundary has a
  diagram of its own, and is entered on every history or on none, by
  whether a statement of `B₁` that no lexical boundary encloses may fault
  on a history that can happen (`work_can_fault`).
- **A captured outcome whose capture is not visible** (RC23, [I12]). The
  record of a capture is kept for the histories that saw it. On the others,
  where the outcome arrived as a parameter of a control or of a loop or as
  the payload of a loop, a decision on it now adds the conditions of the
  captured operation over fresh names: one for each parameter, of the type
  of the parameter, and a second one for `old(p)` where the parameter is
  `&~`. The operation is the control that the outcome type names
  (`outcome_control`).

## 14. Slice 2 Phase 4: Call Expansion and Typed LLVM IR Backend for Data, Resources, and Boundaries

Slice 2 Phase 4 completes Theorem 4 call expansion (`expand.rs`), the typed
LLVM IR and C ABI backend (`codegen.rs`), and the Slice 2 differential and
paired native-performance suite (`v2/tests/backend_slice2.rs`):

- **Theorem 4 call expansion for slice 2 (`expand.rs`).** Extends in-place call
  expansion across `Declaration::Boundary` (`body` and `contingency`), lexical
  `Command::Boundary`, `Unpack`, `AssignPlace`, `Supervise`, `Fault`,
  `Terminate`, `Escalate`, and `Recover`. Evaluates operands in `[E-Operands]`
  order, substitutes `&τ` shared borrow parameters (either direct place
  substitution or an owned temporary binding for rvalues) and `&~τ` exclusive
  borrow parameters (direct caller-place substitution plus `old(y)` /
  `len(old(y))` snapshots for `⇐` postconditions) without introducing core
  local borrows (`[W8]`), tracks fault/termination reachability for selector
  pruning, and leaves `Command::Capture` unexpanded (as core has no outcome
  expression constructor).
- **Typed native layouts and portable C ABI (`codegen.rs`, `[R1]`–`[R5]`).**
  Lowers structs to flat `%vn2.struct.<id>` aggregates, unit variants/outcomes
  directly to `i32`, payload variants/outcomes to tagged
  `{ i32, [N x i64] }` layouts, strings and vectors to `{ ptr, usize, usize }`
  (with string literals using `cap = 0` so `.rodata` is never freed), maps to
  sorted flat `{ ptr, usize, usize }` arrays with binary-search key lookup
  matching `BTreeMap` order, and resources/borrows to opaque `ptr` values with
  zero dynamic value wrappers. Internal `fastcc` functions pass aggregates by
  value while C ABI boundaries (`@vn2_call_*`, `@vn2_ext_*`, `emit_c_header`)
  pass aggregates by pointer for portability across Apple `arm64` and Linux
  `x86_64`.
- **Static cleanup, resource release, and structured arm-chain lowering
  (`[R2]`–`[R5]`).** Takes the layout of the erased semantics
  (`erased::layout`, including post-end
  snapshots for lexical boundary fallthrough) so `[R4]` destruction and `[R5]`
  `on fault release` unwinding (`@vn2_release_<res>`) are driven purely by
  static history-bit selectors with zero runtime moved flags. Since 23
  November 2026 (review findings RB1, RB3, RB11) every scope that a
  terminator or a fault ends is ended by the formulas of that statement
  (`end_scopes` and `emit_unwind` in `emit_body_unit`); a `□` and a
  statement of the work of a boundary set a bit where a formula asks which
  one ended the loop or faulted; what a boundary has in its care ends with
  the scope of its work however the work ends; and the message of a fault
  has one owner: the contingency holds it in a slot of its own
  (`%lex_fault_<body>`, `%unit_fault` for a named boundary), `escalate`
  passes that slot on, every other end of the contingency destroys it, and
  the name of the message reads the slot where no statement consumes the
  name and owns a copy otherwise. Unchecked vector
  indexing and `⊥ → unreachable` follow `[R2]`. A general structured arm-chain
  lowering pass (`plan_structured_flow`) chains mutually exclusive `Decide` and
  two-sided `Test` arm spans directly into their arm statements, eliminating
  redundant history-bit checks and speculative arm branches in hot loops.
- **The allocation count of the native harness.** `emit_native_harness_llvm`
  ends by `count_allocations`: every call of `malloc`, `realloc` and `free`
  in the text of the module goes through `@vn2_h_malloc`, `@vn2_h_realloc`
  and `@vn2_h_free`, which keep the number of live allocations in
  `@vn2_h_live` and the number made in `@vn2_h_made`. Where a run has
  ended, `main` frees what the harness kept: the value behind each
  reference it gave the entry control, and the places its hosts lent, which
  are globals (`@h_lent_<n>`) written when the answer is given. A host
  frees what it was given by value. `main` then writes `LIVE n` if the
  number is not zero and sets it to zero for the next run, and
  `run_native_batch` gives that run the end `undefined`; at its end `main`
  writes `MADE n`, which `run_native_counted` returns with the runs.
  Freeing here is the destruction of memory only: no resource is released
  by it. `run_native_ir` compiles and runs a text, so that a test can
  change what was compiled:
  `a_run_of_compiled_code_that_leaves_an_allocation_live_is_seen` takes the
  release of a string out and requires the count to see it.
- **Checked files of the suite in compiled code.** `script::native_runs`
  gives the runs of the directives of a core text file as a compiled program
  takes them, and
  `checked_core_programs_of_slice_two_run_natively_as_the_oracle_does`
  compiles every file of `v2/tests/slice2/` that the checker accepts whole
  and compares each run with the oracle at `-O0` and `-O2`. Most files of
  the suite hold a control that is there to be stuck, so the checker
  refuses them; the four it accepts are `erased_nested_ownership.core`,
  `checked_faults_and_boundaries.core`, which is written for this (the ends
  of a contingency with messages that own memory, care lists, a boundary in
  the work of another, a named boundary), `checked_skipped_bodies.core`
  (RB12: a boundary or a loop that does not run, and what the names around
  it still own), and `checked_nested_boundaries.core` (the shapes that the
  generator writes since 24 November: boundaries in the work of boundaries,
  and contingencies that restart a loop further out than the body their
  boundary stands in). Where a batch of runs fails, the test runs each run alone
  and names those that differ.
- **Verification (`v2/tests/backend_slice2.rs`).** Verifies Theorem 4 expansion
  plus `check::check` and `kernel::validate` across all 4 Slice 2 `.rails`
  files and a dedicated `&τ`/`&~τ`/`old(y)`/resource/fault/boundary test;
  checks LLVM IR and C header erasure; runs differential native tests at `-O0`
  and `-O2` across 64-bit and 32-bit `usize` on all 4 Slice 2 `.rails` files
  (original and expanded) and all 15 non-stuck controls of `tests/slice2/*.core`
  against `oracle::run` and `erased::run`.
- **Paired native performance (`paired_native_performance_matches_optimized_rust_on_slice_two_data_kernel`).**
  - **Workload:** Build a `[point]` vector (`copy struct point {x: u64, y: u64}`)
    by pushing 2,000 elements, run 200 unchecked indexed passes dispatching on
    `copy variant op: add │ sub │ mix │ scale` (through a Theorem-4-inlined
    `choose_op` control) with in-place element updates, pop all 2,000 elements
    into a checksum mod `1_000_000_007`, and drop via `[R4]` (repeated 10×
    inside a single timed hot region separate from launch/output, 5 paired
    samples, minimum hot time taken). Both binaries produce identical verified
    checksum `2426593890`.
  - **Environment:** Apple M2 (`Darwin arm64`), `Apple clang 21.0.0 -x ir -O3`
    vs. `rustc 1.97.1 -C opt-level=3`.
  - **Measured result:** Before structured arm-chain lowering, v2 ran in
    `27.056 ms` (`2.418×` Rust) because flat history-bit dispatch kept extra
    conditional branches inside the inner loop. After structured arm-chain
    lowering, v2 runs in `10.863 ms` (`10,863,000 ns`) vs. Rust `10.600 ms`
    (`10,599,584 ns`), ratio **`1.025×`** (gap `+0.26 ms` / `+2.5%`; Slice 1
    scalar `hot_bench` remains `0.997×`). This is one synthetic kernel
    written inside the test, not the measurement of the phase 4 exit. A map
    is a sorted array: inserting 20,000 keys in descending order takes 55 ms
    against 0.52 ms for Rust's `BTreeMap` ([review](review.md), RB6).
  - **Next experiment:** Emit natural alignment hints (`align 8` for `i64`/`ptr`
    loads and stores) and evaluate pre-sized vector growth in Phase 7 to close
    the remaining `2.5%` gap.

## 15. Slice 3 Phase 2: Second-Class Borrows, Views, and Borrow Tag Semantics

Slice 3 Phase 2 implements the executable core oracle, zero-tag erased
semantics, well-formedness and typing rules, Rails surface reader/elaborator/
formatter, and conformance suite for second-class borrows and views
([`references.md`](references.md)):

- **Core syntax, typed AST, and well-formedness (`syntax.rs`, `text.rs`,
  `typed.rs`, `resolve.rs`).** Adds `view struct` declarations, payload origins
  `∈`, local borrows (`&p`, `&~p`), borrowed variant decisions (`[E-Outcome]`,
  `Operation::Variant { borrow }`), recursive `Expr::lends()` across view
  constructors (`[E-Operands]`), and normative borrowed-payload contracts for
  `get` (`&v ∈ 0`) and `entry_at` (`&k ∈ 0, &v ∈ 0, next : usize`). Enforces
  `[W5a]` (no borrow or view inside an owning container), `[W6]` (no reference
  to a reference or to a view, no borrow or view inside a regular `struct` or
  `variant`, and at least one borrow/view field in a `view struct`), `[W8]`
  (no borrows/views in function parameters or outputs), `[W9]` (valid payload
  origins on every borrow/view outcome payload, exclusive origin matching for
  `&~` and `&~`-containing views, and no origin on owned payloads), `[T1]`
  (view kinds: `copy` if all fields are `&`/copy, `drop` if any field is `&~`),
  `[T4]` (immutable `&` places; mutable `&~` and view-projected `&~` places),
  `[T6]` (no move out of a borrowed place), `[F5]` (no `&~` across a fault
  boundary), and `[F6]` (no borrow/view outcome payload escaping a boundary),
  plus borrow-preserving `□` (`LeaveKind`).
- **Instrumented borrow tag oracle and erased semantics (`oracle.rs`,
  `erased.rs`, `host.rs`).** Replaces call-end writebacks with live
  `RuntimePlace` references (`Value::Ref { mode, place, tag }`) across struct
  fields, vector elements, variant payload fields, and map keys/values, and
  adds `TagTable` implementing `[B1]`–`[B5]` (`X4 B1` stuck states on tag
  invalidation, element-granular place overlap, child reborrow chains,
  collection shape write invalidation, and scope-end tag kills `[B4]`).
  Enforces `[E-Formula]` read-only dereferencing without tag mutation,
  `[E-Outcome]` variant field reborrows, and `[E-Host]` borrow/origin/overlap
  checks on host extern calls. `erased.rs` runs zero-tag `[R1]` live
  `RuntimePlace` references and matches `oracle::run` differentially.
- **Rails surface, elaboration, and formatter (`surface.rs`).** Supports
  `[pub] view struct`, `∈`/`in`/`from` payload origins (keeping `from` usable
  as a field name, e.g. `tail {items: &~[u32], from: usize}`), brace literals
  in call arguments, `[U11]` + Q16 (`~r` required for `&~τ` and automatic
  temporary binding for non-place rvalues passed to `&τ`) across all typed
  slots (bindings, calls, loop initial values, `↑`, `■`, view constructors),
  `[U6]` borrowed variant decisions (`Δ p`, `Δ ~p`, `Δ ▾p`), `[U9]`
  borrow-preserving `□`, `[U10]` `∀ x ∈ p` with origin propagation, `[G3]`
  `■ auto` origin inference, and `[G10]` canonical formatting (printing
  exclusive borrows as `~p`).
- **Conformance (`v2/tests/slice3.rs`, `tests/slice3/*.core`,
  `tests/slice3_surface/*.rails`).** Exercises 22 core runs (valid borrows,
  views, variant borrows, `get`, loops, and 9 `X4 B1` tag-invalidation stuck
  cases including the [`references.md`](references.md) §10 trace), 10 Rails
  surface runs with differential erased checking and `[G10]` format
  idempotence, `[G3]` `■ auto` origin inference, 25 core well-formedness
  refusals, ASCII `in`/`from` and `[U11]`/Q16 surface refusals, and `[E-Host]`
  host borrow violation checks.

### 15.1 The borrow rules, as requalified on 24 November 2026

The suite of slice 3 has a file for each rule of the borrows, as slices 1
and 2 have: `b1_access.core`, `b2_invalidation.core`, `b3_creation.core`,
`b4_moves_and_scopes.core`, `b5_shapes.core`, `e_borrow_operands.core`
([E-Borrow], [E-Operands], [E-Fn], [W8] and the borrows that a decision on
a variant gives) and `e_views.core`, each with the runs that apply the rule
and a run for each way of being stuck by it, and eight refusals
`reject_c1_*.core`. With the five files before them: 20 files, 130 runs, 67
compared with the erased semantics. `slice_three_core_conforms_and_matches_erased`
(`v2/tests/slice3.rs`) asks for 13 rules (`SLICE3_RULES`), three stuck
labels (`SLICE3_STUCK`) and the refusal (`SLICE3_REFUSALS`).

A run that is stuck by `X4 B1` says what ended the borrow. The tag table
(`TagTable` in `oracle.rs`) keeps, for a dead tag, the `Death`: the
`Access` that killed it (`Read`, `Assign`, `Move`, `LendShared`,
`LendExclusive`, `Shape`) or the end of the scope of what it refers to, and
a descendant has the death of the tag that took it along. The detail of the
stuck state reads, for example, "the borrow is dead: a change of shape of
its collection ended it ([B2], [B5])". `script::Report.stuck_details` gives
the details by control, and the table `DEATHS` of the test names the cause
of each of the 39 dead borrows of the rule files, so that a run about [B5]
is stuck by a change of shape and not by the borrow that the operation's
operand makes. The count `B2` is an access that killed a tag.

What the oracle did otherwise, and does now: a formula read through a dead
borrow (RO15); a function's borrow argument made a borrow (RO16); a call
and an exit read every borrowed argument for the formulas of the signature,
mentioned or not (RO17: `Control::signature_reads`, `typed::mentions`,
`Machine::entry_values`); `r ← e` through a moved borrow name was reported
as `X2 E-Assign` and is `X2 E-Var`. The reader takes `&p`, `&~p` or a name
or field of a view of the borrow type where a borrow type is expected
(`Typer::borrow_operand` in `resolve.rs`), and a place for a borrow
parameter of a function (`Typer::function_argument`); a formula reads its
terms in place as before (`Typer::read_in_place`). The generator of slice 2
binds a value that an operand lends to a name of its own before the
statement (`Ctx.hidden`, `bind_hidden` in `generate/valid/data.rs`), as the
surface does by [U11]. Such a bind runs before every operand of the
statement, so its value moves no name that an operand before it mentions
(`Ctx.read`); the first campaign without that rule had one program rejected
by [O2], with `len(v2)` read after the bind had moved `v2`. The programs of
slice 1 are unchanged, text for text over 600 seeds.

A host writes behind an argument lent exclusively (RO11, [E-Extern]).
`host::Answer` has `writes`, a list of an argument's index and the value
the host leaves behind it; in a directive the answer is followed by
`~x <- v`, with `x` the name of the parameter (`script.rs` resolves it at
the parameter's type). `Machine::host_writes` (`oracle.rs`) checks each
write ([E-Host]: the argument is lent exclusively, the value is of the type
it refers to, and a value of kind `must` is not changed), makes the write
an access through the argument's tag (`Access::Host`, whose death reads "a
write of the host behind it ended it"), and stores the value before the
borrows of the payload are made; the event holds the values of the call.
The condition of the alternative reads the argument after the write and
`old` of it from the values of the call. The table of the answers of a
pure control (`Machine.answers`) has the values at completion beside the
answer, so a host that writes otherwise on equal arguments is a
violation. `erased.rs` writes the same values at its
three calls of a host. `e_extern_writes.core` holds it: 21 files, 143 runs,
73 compared, and 40 dead borrows with their causes. Until 24 November
the native driver wrote nothing behind an argument, and those runs were
left out of compiled code; section 17.1 says how it writes them.

## 16. Slice 3 Phase 3: Static ROBDD Loan Checking and Borrow/View Fact Logic

Slice 3 Phase 3 adds static borrow/view ownership refinements, borrow and view
fact propagation/invalidation, and Pass 2 static ROBDD loan checking to
`v2/src/check.rs`:

- **Borrow ownership refinements (`[O0]`, `[O3]`).** Rejects moving non-`copy`
  values out through shared or exclusive borrows in `check_expr_pure_ownership`
  and `check_consume_expr` without marking the borrow itself moved (`[O3]`),
  orders `view struct` constructor fields non-lending before lending matching
  `[E-Operands]`, and evaluates `Operation::Variant { borrow: Some(_), .. }`
  using `check_consume_expr`.
- **Borrow and view fact logic (`[I7]`, `[I9]`).** Tracks multi-hop
  `local_borrows` with functional updates when owners change (`[I7]`), tracks
  `var_loan_roots` across `Bind`, `Unpack`, `Decide` (controls, builtins, and
  borrowed variants), `Loop`, and `Leave` (`Leave::roots`),
  invalidates dependent roots on non-local borrow/view writes and exclusive view
  arguments (`apply_call_exclusive_updates`, `invalidate_exclusive_view_arg`)
  (`I9`), and transitively closes `modified_outer` across loops and lexical
  boundaries (`collect_operand_modified`, `close_modified_with_borrows`).
- **Static ROBDD loan checker (`LoanChecker`, `[L1]`–`[L5]`, `[L2a]`, `[RM7]`).**
  Runs Pass 2 after Pass 1 (`check_control` and `check_boundary`), tracking
  `LoanRoot::{Owned, Behind, ParamOrigin}` with `[RM7]` structural place overlap
  (`LoanPlace::overlaps`), path-sensitive ROBDD holder liveness including
  cross-iteration loop `repeat_g` and lexical boundary fallthrough/contingency
  flow (`compute_body_liveness`), fixed-point loop back-edge loan seeding
  (`seed_loop_again_loans`), operand temporary lifetimes in `eval_loan_operands`
  (covering `Expr::Var`, `Expr::Field`, `Expr::Borrow`, and view constructors),
  reassignment loan attachment (`Command::Assign`), `[L3]` conflict queries
  validated through `require_entailment` and `kernel::validate`, `[L4]` exit
  origin checking, and scope-end loan checks (`check_scope_end_loans`).
- **Conformance (`v2/tests/checker_slice3.rs`, `tests/slice3_surface/*.rails`).**
  Verifies all 34 synchronous worked examples from [`references.md`](references.md)
  (§§4–10), `[I7]`/`[I9]`/`[O3]` checks, both `tests/slice3_surface/*.rails`
  programs under `vn2 check --certificates`, and all 9 stuck controls plus
  `[RM7]` `disjoint_elements` from `tests/slice3/*.core`.

### 16.1 The checker against the rule files of the borrows, 24 November 2026

`the_rule_files_of_the_borrows_are_rejected_exactly_where_a_run_is_stuck`
(`v2/tests/checker_slice3.rs`) gives each control of the eight rule files
of slice 3 to `check::check_each` and asks that the checker refuse exactly
the controls in which a run of the oracle is stuck, and by the clause that
excludes the stuck state (`excludes`: `X4 B1` by a loan clause, `X2
E-Var` by [O2], `X7 E-Index` by [P5]); a refusal for another reason where a
run is stuck is a failure, since it hides whether the clause holds. Of 84
controls, 39 are refused and 35 accepted; `ASKS_MORE` lists four that the
checker refuses where no run is stuck (two by [RM7], which does not compare
indices, one by [L2], for which a use of a view uses each of its borrows,
and one because a write through a field of a view leaves the root with no
fact, [I7] and [I9]); `STUCK_BY_ANOTHER` lists three pairs in which a run
is stuck in a control that keeps its contract (it reads a borrow it was
given, or one a callee returned) and the checker refuses the caller or the
callee that broke the clause ([L3], [L4]).

The loan check runs after the check of the facts, so a control that is
stuck by a dead borrow and also adds numbers the logic cannot bound was
refused by [P5] first. The rule files were written for the oracle: ten of
their controls with only runs that end added or compared numbers that the
logic does not know (an element of a vector literal, [A3]; a value found
in a map; a payload of a host; a condition the control does not
establish), and bound them now by a precondition, a condition of the
host, a guard or an element written before it is read, or keep the
arithmetic out; four that are stuck by a dead borrow keep it out, so that
the loan clause is the one that refuses them. `add_from` of
`e_borrow_operands.core` is `copy_from`, and copies.

Found and closed: RC27, an assignment through a name of exclusive borrow
type that had moved was accepted (`check_assign` asks [O2] of the name);
RO18, the operands of a decision for an `&~` parameter took a bare place as
`&~p` (`Resolver::arguments`), and the move mark on such a name is read now
([C1]). RC1 is closed in the same part (section 9 of the review): a loop
renames at its entry every place its body lends exclusively
(`collect_modified_vars`).

### 16.2 The clause tests of the loans, 24 November 2026

`v2/tests/slice3/l_loans.core` takes the loans of section 7.5 of the core
a clause at a time: for each way a rule makes a loan ([L1]: a bound name,
a payload derived with `∈`, a decision through a borrow, the payload of
`□`, a copy, a borrow through a borrow name), keeps it live ([L2]: a later
mention, a history, the command of the statement, a later operand, a
formula; [L2a]: a loop parameter that receives a borrow through `↑`, the
end of an iteration), meets an access ([L3]: a read, an exclusive borrow, a
move, a change of shape, fields, passing a borrow name), escapes ([L4]) or
is held by a view ([L5]), a control in which a run is stuck and one beside
it that runs to its end. `each_loan_rule_refuses_where_a_run_is_stuck_and_accepts_beside_it`
(`v2/tests/checker_slice3.rs`, table `LOANS`) asks that the checker refuse
the control that broke the rule, by the clause named, and accept the one
beside it and every callee. In four rows the run is stuck in another
control that keeps its contract: a callee that reads a borrow which the
operands of its call ended, or a caller that reads what its callee
returned. The oracle suite holds the cause of each of the 27 dead borrows.
A name of borrow type cannot be declared mutable ([W8]), so the holder of
[L2a] that outlives an iteration is a loop parameter or the payload of a
leave in practice.

Found and closed: RC28 (the arguments of a function in an operand were
checked as if the statement lent nothing) and RC29 (a borrow in the operand
of `len` counted as used by the command); both are in `eval_loan_expr`. The
checker uses each field of a view in its own mode where [L5] said the view
is one borrow; [L5] says what the checker does now (change entry of the
core).

### 16.3 Generated programs with borrows, 24 November 2026

The generator of slice 3 (section 8, "Borrows in generated programs") found
RC30: at `recover ↑ ℓ`, `compute_body_liveness` took a name bound in a body
within the restarted loop, such as the work of a boundary around the one
that recovers, as live after the restart, and a valid program whose payload
borrow is held there was refused by [L3]. The name is bound anew by the
next iteration ([L2a]), as the head of the loop already said; the condition
is `var_in_body_tree` now.
`a_name_bound_within_the_restarted_loop_is_not_live_after_recover_l2a`
(`v2/tests/checker_slice3.rs`) holds it with a program that runs to its end
and is accepted, and one that carries the borrow on through a parameter of
the loop, which is stuck and refused. The checker accepts all of 900
generated programs with borrows (36,396 runs, none stuck).

### 16.4 Mutants of the borrows, 24 November 2026

The four kinds of mutation of the borrows (section 8, "Mutations") and the
twelve before them, on the first 40 generated programs of slice 3
(`vn2 fuzz --slice 3 --seed 1 --count 40 --mutants --seconds 10`):
11,088 mutants; `resolve` refuses 1,408, the checker rejects 1,732 (1,261
of them with a stuck run) and accepts 7,948 with none. No mutant with a
stuck run was accepted, and the checker gave an answer in ten seconds on
every one. The twelve kinds before give, kind for kind, the lines they gave
before. Of the four kinds: `FlipBorrow` 83 mutants (47 refused, one
rejected and stuck, 35 accepted), `ConflictingBorrow` 16 (8 refused, 7
rejected, 5 of them stuck, one accepted), `AccessLent` 16 (5 rejected, 3 of
them stuck, 11 accepted), `ExtendBorrow` 393 (11 rejected and stuck, 382
accepted). They meet few conflicts in generated programs: the generator ends a borrow where
it stops mentioning the names that hold it, and most of its borrows are of
names that nothing writes or moves afterwards (of the 83 borrows bound to
names in these 40 programs, 19 are mentioned after the statement that binds
them). The program of `mutations_of_borrows_are_stuck_and_rejected` has the
conflicts that the generated programs lack: in it each kind is stuck in the
controls where it meets one (X4 B1, and X2 E-Var where a statement before
moved the borrow name), and in no other; the test fails with a conflicting
borrow made in the same mode, with payload names that hold no place, and
with a checker that allows a read beside an exclusive loan.

### 16.5 Two exclusive operands in one call, 25 November 2026

[I9] applies each write to the record produced by the preceding write in
the same invocation. The indices of the lent places and the values used
by `old` come from entry to the call. The updates occur when the call
runs, including when its outcome is captured ([I12]).

Two tests in `v2/tests/checker_slice3.rs` exercise RC33 in the checker and
oracle. Run them with `cargo test --test checker_slice3 rc33`.

- `exclusive_call_operands_update_the_same_record_rc33` passes two fields
  of a record as direct borrows, inside a constructed view, and by local
  borrow names. In each form the checker refuses an assertion of the old
  value of either changed field by [P1]. The oracle gets stuck at the
  assertion. Both accept the assertion that the third field kept its value.
- `a_capture_keeps_both_exclusive_postconditions_rc33` decides the
  captured outcome of a call. Its contract relates each changed field to
  the other parameter’s entry value. The checker proves both resulting
  values and the unchanged third field. The assertion that the first field
  kept its old value is refused. The oracle confirms both verdicts.

Before the repair the checker accepted the stale first field in the
direct call and refused the true assertion after the capture.

## 17. Slice 3 Phase 4: Theorem 4 Expansion and Typed LLVM IR / C ABI Backend for Borrows and Views

Slice 3 Phase 4 completes Theorem 4 call expansion (`expand.rs`), erased borrow
consumption (`erased.rs`), and direct typed LLVM IR and C ABI code generation
(`codegen.rs`, `[R1]`–`[R5]`) for borrows (`&τ`, `&~τ`) and `view struct` values:

- **Erased consumption fix (`v2/src/erased.rs`).** Updates
  `collect_consumed_vars` on `Expr::Var(VarRef::Local(id), expr_ty)` so
  reading or mutating through an exclusive borrow `&~r` does not mark `r` moved,
  while moving `&~r` itself (`Type::Ref(BorrowMode::Exclusive, _)`) or any
  non-`copy` owned value still consumes it.
- **Theorem 4 call expansion (`v2/src/expand.rs`).** Adds `expr_lends_syntax`,
  updates `inline_callee` to rename and bind all parameters (`&τ`, `&~τ`, and
  `view struct`) as `_exp{call_id}_{name}` locals in `[E-Operands]` order
  (non-lending before lending) with `old(...)` snapshots reading through renamed
  `&~` locals, updates `subst_and_rename_expr`, `rename_place`, and
  `rename_command`, and preserves `[E-Operands]` evaluation order for
  `Command::Exit` payload bindings in `lift_exits_in_body`.
- **Typed LLVM IR and C ABI backend (`v2/src/codegen.rs`, `[R1]`–`[R5]`).**
  - Lowers `&τ` and `&~τ` with zero runtime borrow tags (`ptr`, with
    `ptr noalias` on `&~` control parameters in `emit_body_unit`), emits
    `unreachable` for `⊥` and zero bounds-check traps (`[R2]`), and removes
    dead `require_clone` in `BuiltinOp::Get` so `@vn2_map_get_` stores `ptr`
    directly with no `@vn2_clone_` call.
  - Dereferences borrow-typed fields in `emit_place_ptr` (`PlaceStep::Field`),
    `emit_expr_ptr_if_place` (`Expr::Field`, including `extractvalue` for
    by-value `view struct` parameters in pure functions), `emit_read_operand`
    (`Type::Ref` guard), `emit_expr`, and `emit_printers`, while preserving
    `[E-Operands]` order in `emit_exprs_ordered` (lending `view struct`
    constructors, `Loop`, `Again`, `Leave`, `Exit`) and Pass 2
    `emit_operation_call`.
  - Orders `struct` declarations topologically in `emit_c_header`, formats
    pointer fields cleanly (`const struct vn2_vec *items;` /
    `struct vn2_vec *items;`), guards shared `vn2_string` / `vn2_vec` / `vn2_map`
    typedefs under `#ifndef VN2_RUNTIME_TYPES_DEFINED` so generated headers
    compose cleanly in a single C translation unit, forwards `&bool` origin
    pointers without dangling stack temporaries in `emit_control_c_wrapper`, and
    extends `emit_harness_value_into` (`heap_refs` + `Type::Ref`) and
    `emit_native_harness_llvm` for borrowed payloads and trace printing.
- **Conformance and paired benchmark (`v2/tests/backend_slice3.rs`).** Verifies
  Theorem 4 expansion + kernel-validated certificates + directive parity on both
  `tests/slice3_surface/*.rails` programs and a multi-control Slice 3 suite
  (`widest`, `pick_mut`, `halves`, `longest`, chained views, `clear`, and loop
  exit lifting); verifies zero-tag / zero-`oob` / zero-clone `@vn2_map_get_` IR
  plus composable dual-header `clang -fsyntax-only`; checks `-O0`/`-O2` 32/64-bit
  differential parity across orig/expanded `.rails`, `.core`, and `extern`
  borrowed `&string`/`&bool` payloads; and benchmarks `borrow_view_bench` (`4096`
  `u64` elements × `200` passes × `10` reps, checksum `4790574320`, Apple M2
  `arm64`, `Apple clang 21.0.0 -O3` vs. `rustc 1.97.1 -O3`): **24.440 ms** (v2)
  vs. **23.932 ms** (Rust) = **1.021×** (0.508 ms / 2.1% remaining gap from
  loop induction and `urem`/modulo lowering across `scale_tail` and
  `sum_window`; next experiment: inspect generated arm64 assembly and align
  unsigned `mod` constant strength-reduction). This is one synthetic kernel
  written inside the test, not the measurement of the phase 4 exit
  ([review](review.md), RB6).

### 17.1 Hosts that lend and write, in compiled code, 24 November 2026

RO6 and RO11 of the review are closed for compiled code, and RB13 is found
and closed with them. The native driver answered a borrow in a payload with
a value in a cell of its own, which is no place within an argument, and
wrote nothing behind an argument: `emit_native_harness_llvm` refused a run
whose host writes and `script::native_runs` left such runs out. The one
test of a borrowed payload gave values and compared compiled code with the
erased semantics alone. What changed, in `codegen.rs`:

- `emit_host_place` is the address of the place that a host names within an
  argument of its stub (`%p0`, `%p1`, …), along the steps of
  `oracle::lent_within`: a step from a place that holds a borrow goes
  through it (the fields of a view, then what its borrow refers to), and
  struct fields, variant fields, vector elements and map values and keys
  (by `@vn2_map_find_<mid>` on a key the stub writes and releases) follow.
- `emit_harness_value_into` takes `Refs`: `Slots` for the arguments of the
  entry (a slot of `main`), `Within(control)` for a host's payload (a place
  within an argument, and nothing else: the cell is gone, and a value where
  a borrow belongs stops the driver, as [E-Host] stops the run), and
  `Nothing` for a key and for a write. `Lent` and the globals `@h_lent_N`
  are gone.
- The stub of a host prints the event first, with the arguments as they
  were at the call; then it writes what the host leaves behind each
  argument lent exclusively (nothing behind a value of kind `must`), making
  the new value before it releases the old one, so that the two never share
  an address; then it makes the payload, and prints it.
- RB13: an argument `&bool` of an extern control was passed as a byte in a
  temporary that held a copy. The place itself is passed now, as for every
  other type behind a borrow: a `bool` is a byte that holds 0 or 1.

`tests/slice3/checked_host_places.core` (16 runs; the checker accepts every
control) has a host that writes behind a `bool` and one that lends it, a
value of a map by its key, a borrow through the borrow of a view, shared
and exclusive, two exclusive borrows of one payload, a view of two borrows,
a write that releases a vector and one after which the payload is made in
the new vector, two writes in one answer, and four hosts with `uses io`, so
their calls are events. `hosts_that_lend_from_and_write_behind_arguments_run_natively_ro6_ro11`
(`tests/backend_slice3.rs`) compiles the runs of the controls that the
checker accepts in that file, `host_borrows.core` and
`e_extern_writes.core`, 28 runs, at both widths of `usize` and at `-O0`
and `-O2`, and compares the end, the trace and the allocations with the
oracle and the erased semantics. Each of five mutants of the driver fails
it: the temporary of RB13, no release of the old value, a null pointer for
the place, the event printed after the write, and the payload made before
it. ASan and `leaks` by hand on the emitted code: 73 runs, no error and no
leak. The checker refuses `writes`, `splits` and `spans` of
`host_borrows.core` by [P5] (an index or a sum over what the call left
unknown) where no run is stuck, so those three run in compiled code in the
forms of the first file. No test reaches a step into a variant field or to
a map key in compiled code: a directive has no step for either (the seeded
host draws variant fields), and the generator of slice 3 is to.

## 18. Slice 4 Phase 2: Second Review of Task Rules, Instrumented/Erased Task Scheduler, and Rails Task Surface

Before coding Slice 4, the task-rule repairs named at Phase 1 acceptance
(`[TK3]`–`[TK6]`, `[E-Await]`, `[E-AwaitHost]`, `[E-Stop]`, `[N5]`, `[F5]`,
`[F6]` of [`core.md`](core.md); `[J3]`, `[I10]` of [`facts.md`](facts.md);
`[G3]` of [`surface.md`](surface.md)) received their second review and three
further specification repairs were folded in (`core.md` section 12):

1. **`[TK6]` `old(y)` freshness.** `d : Δ await next(x)` instantiates each
   alternative condition `φₐ` with a fresh logical name for each parameter and
   a separate fresh logical name for `old(y)` of each `&~` parameter `y`, so
   postconditions like `y = old(y) + 1` do not collapse to `u = u + 1` and
   falsely prove `⊥`.
2. **`[W11]` `await next(x)` in decisions only.** `await next(x)` is permitted
   only in a decision (`Δ`), never in `capture`, because `capture` records no
   `d.empty` atom to track `[TK2]` consumption of `x`.
3. **`[E-AwaitHost]` ordering and turn handoff + `[I10]` supervised `run`.**
   `[E-AwaitHost]` checks its precondition (`[E-Extern]`) and effect allowance
   (`[E-Effect]`) before taking the immediate `cancelled` shortcut and passes
   the turn (`ready`) when it does; `[I10]` in [`facts.md`](facts.md) excludes
   any `run` inside a named boundary supervised by a control from purity.

Slice 4 Phase 2 then implements tasks across core syntax, resolution, the
instrumented oracle, the erased interpreter, differential scheduling, and the
Rails surface:

- **Core syntax, parser, and well-formedness (`typed.rs`, `syntax.rs`,
  `text.rs`, `resolve.rs`).** Adds `async control`, `extern async control`,
  `tasks⟨f⟩` (`Kind::Must`, fault-releasable, non-obligation), `tasks⟨f⟩()`,
  `count(x)`, `spawn f(ō) into x`, `cancel x`, `await f(ō)`, `await next(x)`,
  `run f(ō)`, and `capture [await | run] f(ō)` (keeping `next`, `tasks`,
  `into`, and `count` contextual), enforcing `[W10]`–`[W12]`, `[TK1]`, and
  transitive `[I10]` purity (`Program::control_is_pure`).
- **Instrumented cooperative scheduler (`oracle.rs`, `host.rs`, `script.rs`).**
  Implements `TaskSet`, `TaskState`, `Task`, `TaskRun`, cross-task borrow
  resolution (`find_slot_ref`/`slot_mut`), `[E-Run]`, `[E-Turn]`, `[E-Await]`,
  `[E-AwaitHost]` (with precondition/effect checks before the `cancelled`
  shortcut and `on fault release` unwinding on cancellation/withdrawal),
  `[E-Spawn]`, `[E-Next]` (marking `x` moved on `empty`), `[E-Cancel]` (with
  root cancellation propagating through spawned members and nested `run`),
  `[E-Done]`, `[E-MemberFault]`, `[E-Stop]` (stopping activations and sibling
  task sets without running contingencies or asking fault permission, sticking
  in `X8 E-Stop` on non-fault-releasable open resources), `X5 E-Scope` on
  undrained non-empty task sets, and `[E-Effect]` across parent task
  allowances. Extends `Host` with non-breaking default scheduling methods
  (`pick_turn`, `pick_waiting`, `should_cancel_root`), `Scheduled<H>`, and
  `turns [...]` / `cancel_at N` options in `//! run`.
- **Erased task scheduler and Theorem 3 replay (`erased.rs`,
  `differential.rs`).** Implements `[R6]` in `erased.rs` with zero borrow tags,
  zero contract checks, and static history-bit availability formulas
  (`d.empty` marking `x` moved so `[R4]`/`[R5]`/`[R6]` unwind and stop live
  task sets with zero runtime moved flags), preserving exact step-count parity.
  `differential::Recording` records every turn choice, waiting-host completion,
  and root-cancellation decision and replays them identically via
  `Scheduled<Script>` into `erased::run`.
- **Rails surface, elaboration, and canonical formatter (`surface.rs`).**
  Implements `[G7b]` and `[U19]` (`async control`, `extern async control`,
  `tasks<f>`, `tasks()`, `x.count()`, `spawn f(ā) into x`, `cancel x`,
  `Δ await f(ā)`, `Δ await next x`, `Δ run f(ā)`, single-alternative
  `await f(ā)`/`run f(ā)`, `capture await/run`, `forward await/run`,
  `■ Δ await/run/await next`, `[G3]` `■ auto` inference across `await`/`run`,
  and idempotent `[G10]` canonical formatting).
- **Conformance suite (`tests/slice4/*.core`, `tests/slice4_surface/*.rails`,
  `tests/slice4.rs`).** Exercises every Slice 4 dynamic rule (`E-Run` through
  `E-Stop`), turn-schedule interleavings, cross-task shared and exclusive
  borrows plus `X4 B1`, `X5 E-Scope`, `X7 E-Extern` before cancel shortcut,
  `X8 E-Stop`, `X8 E-Unwind`, `X9 E-Effect`, `on fault release` cleanup on
  cancel and member-fault stop, all `[W10]`–`[W12]`/`[TK1]`/`[U19]` refusals,
  `[I10]` supervised-`run` impurity, `[G3]` `■ auto`, `[G10]` canonical
  formatting, and oracle-vs-erased differential parity.

That was the account of the draft (22 November). What the suite held then
was two files, and its test asserted no stuck state; the review counted the
oracle of slice 4 as not met.

### 18.1 The clause tests of the task rules, 24 November 2026

`v2/tests/slice4/` has a file for each rule of the tasks, each with the runs
that apply it and a run for each way of being stuck by it: `e_run.core`,
`e_turn.core`, `e_await.core`, `e_await_host.core`, `e_spawn_next.core`
([E-Spawn], [E-Next], [E-Done], `count`), `e_cancel.core`,
`e_member_fault.core`, `e_stop.core` and `e_exhaust.core`, beside the two
files of the draft. On 24 November these 11 files had 93 runs, 70 compared
with the erased semantics. `slice_four_core_conforms_and_matches_erased`
(`v2/tests/slice4.rs`) asks that each of the 11 rules be applied and that
each stuck run be stuck in the control and the state that `STUCK` lists (22
rows: X2 `E-Var` for a set used after `empty`, X4 `B1`, X5 `E-Scope`, X7
`E-Call`, `E-Extern` and `E-Spawn`, X8 `E-Stop` and `E-Unwind`, X9
`E-Effect`, X10 `E-Decide` for `await next` without `empty`), and every
stuck control of the suite is in the table. The test of the refusals has 23
programs ([W10], [W11], [W12], [TK1]).

What the rules of 24 November changed (core section 12), and what the files
found:

- **[E-Run] of an extern control (RT1).** The draft asked the host at once,
  as a plain call. A run of an `extern async control` is now a run whose
  root task has no activation and waits for the operation (`TaskState::
  WaitingHost` with an empty stack): the host completes it when no task is
  ready, or withdraws it when it cancels the root, and
  `Machine::finish_extern_root` ends the run and completes the caller's
  decision, in the oracle and in the erased semantics. A root cancellation
  that ends such a run gives the caller the turn (`step_scheduler`).
- **[E-MemberFault] (RT2).** The oracle withdrew the operation that the
  owner itself awaits already; `runs_owner_waits` holds it (the script has
  no answer for the operation, and the lease it was given is released once).
- **[E-Exhaust] (RT3).** `End::Exhausted` in both semantics, written
  `exhausted`; `Config::capacity` (directive `capacity N`) is the largest
  length and count, `usize_max` otherwise; `push`, an `insert` of a new key
  and `spawn` check it. No scope ends and nothing is released.
- **RO5 with tasks** (the review's probe
  `r6_repo_suite_other_schedule.core`). The erased semantics ended the
  scopes of a stopped task by the formulas of the statement at which it
  stood, which count the arguments of that statement as moved; a task that
  is ready stands before a statement it has not begun, so a lease that the
  next statement would give away was not released. `erased::Layout` has
  `before_at` now, the formulas before the arguments of each statement
  move, and `stop_activation` uses them for the top activation of a task
  that is ready. The same held where the fault of a member arrives at an
  owner that is ready (`trigger_unwind`, `before`). Both are runs of the
  suite that differed (`runs_stops_keeper` with the probe's schedule,
  `runs_owner_ready`).
- **Theorem 4 (RT4).** `expand.rs` expanded only plain decisions already;
  the test of the expansion of the suite
  (`slice_four_expansion_keeps_turns_and_runs_rt4`: every file, expanded, is
  well formed, and each run that ends gives its end and trace) found that it
  put the body of a synchronous control that runs an async one into the
  async control that called it, which [W10] refuses. It does not now, and
  the theorem leaves that case out.
- The directive `waiting [i, …]` chooses the operation the host completes
  when no task is ready.

Each change was broken and its test failed: a stop of a ready task by the
formulas of its next statement, and the arrival at a ready owner likewise
(one run each), the release of the owner's own withdrawn operation (two
runs), the capacity of `push` (one run, oracle against erased), and the
guard that keeps `run` out of an async control in the expansion (four
files). Before the change of [E-Run], `runs_finish` with `cancel_at 1`
ended in `host-failed`.

Limits of the instrumented profile: the host sets the flag of the root of
the innermost run only, where [E-Cancel] lets it set that of any root.
At this checkpoint the native harness omitted explicit turns, waiting order,
cancellation and capacity. Sections 18.4 to 18.22 record the subsequent
native comparisons, including replay of both scheduling choices.

### 18.2 The first task-checker checkpoint, 25 November 2026

`check.rs` checks the statements of the tasks by [TK1], [TK2] and [TK4] to
[TK7] of the core (section 7.8). The first checkpoint left task-set loans open.
Section 18.3 records their checks.

- **Counts.** `count(x)` is a measure ([A3]). The crate writes it with the
  symbol of `len` over the term of the set (`count_of`), so the kernel
  grants `0 ≤ count(x) ≤ usize.max` as it does for a length.
  - `x := tasks⟨f⟩()` binds a fresh term whose count is 0
    (`bind_empty_set`).
  - `spawn … into x`, and each alternative of the producer in `await
    next(x)`, rename the set with one member more or one fewer
    (`rename_set`, [I9]).
  - A loop renames a set that its body spawns into or awaits
    (`collect_modified_vars`).
  - On `empty` the set has no members, and it moves ([TK2]).
  - The payload of an alternative satisfies that alternative's condition,
    over fresh names for the member's arguments. `fresh_arguments` makes
    these names; [I12] uses it too.
- **Spawn, cancel and count.** `check_spawn` asks that the set be available
  and checks the operands as those of a call: the producer's precondition
  ([P3]) and its effects ([TK7]). A spawn does not fault. `cancel` reads the
  set, and `count(x)` asks for it ([O2]).
- **`await f` and `run f`.** These are checked as calls
  (`check_invocation`): facts, faults, effects, and what they write through
  `&~` parameters.
- **What every await asks.** An `await` asks [TK4] in `check_stop`: after
  the operands move, no name that is not fault-releasable is available, and
  what a boundary around the await has in its care is fault-releasable. It
  also asks [TK5] in `member_fault_histories`: where a set whose producer
  permits `faults` is available, the await may fault, and [F1] and [F2]
  apply.
- **What a stopped task can hold.** `check_held_operands` and
  `check_held_payloads` ask for fault-releasable types in four places:
  - the operands given by value to `await f` and to `spawn f`;
  - the operands given by value to a `run` of a cancellable extern control;
  - the payloads of a producer, at a spawn;
  - the payloads of an extern control, at an await.
- **Boundaries.** A lexical boundary asks that no set be available ([TK5]).
- **Loans.** The loan pass reads the operands of a spawn as those of a
  call. At this checkpoint the checker refused a spawn whose producer took
  a borrow or a view. Section 18.3 records the replacement.

The tests are in `v2/tests/checker_slice4.rs`.
`the_rule_files_of_the_tasks_are_rejected_exactly_where_a_run_is_stuck`
holds the checker against the 11 rule files of section 18.1, control by
control. The first checkpoint had these verdicts for its 160 controls:

- 18 are refused where a run is stuck, each by a clause that excludes the
  run's stuck state;
- 132 are accepted;
- two are refused by the stand-in (`ASKS_MORE`);
- eight form four pairs (`STUCK_BY_ANOTHER`) in which a run is stuck in a
  control that keeps its contract, because the other control broke a rule
  and is the one refused:
  - two members that hold a lock are stopped by the fault of a sibling;
  - a member uses an effect that its parent does not allow ([E-Effect]);
  - a parent writes a place while a member holds a borrow of it. The
    stand-in refused the spawn in this example.

The clause tests run each program in the oracle as well:

- [TK4]: four programs stuck and refused, one accepted, and one refused
  although every run ends (an awaited extern payload, RC32);
- [TK5]: a set at a boundary;
- [TK6]: counts, the condition of a payload, and a loop that renames the
  set;
- [L3]: the operands of a spawn, read as a call's;
- [TK7]: `run`.

At this checkpoint each of 18 mutations failed at least one test. The
mutations exercised these parts of the checker.

- the facts of a count;
- the renaming in a loop, at a spawn and at `await next`;
- the names at an await, the operands held and the payloads held;
- the faults of members, and the boundary;
- the count of `empty`, and the move of the set on `empty`;
- the read of the set by `count`;
- the effects, the precondition and the loans of a spawn;
- the stand-in;
- the operands of a run of a cancellable extern control;
- the set asked for by `await next`;
- the condition of a payload.

Sixteen controls of the rule files, one of them extern, got bounds, so that
a control whose runs all end can be proved:

- preconditions on `add`, `runs_add`, `waiter`, `sub_add` and its five
  callers, `bump`, `excl_pool` and `run_excl_pool`;
- the condition `⇐ v = n` on `echo`;
- bounds on the payloads of `host_work` and `worker`;
- an invariant on the loop of `two_workers`, written by cases on
  `count(pool)`: the core has no conversion between integer types, so the
  sum and the count cannot meet in one formula.

No run changed.

### 18.3 The loans of a task set, 25 November 2026

[TK3] makes a set a holder of every loan passed to one of its members.
The facts pass records the availability of sets after each statement.
The loan pass includes those histories when it checks a read, a write
or the end of the lender's scope. A fault can stop members without a
drain. A borrow or view received from a member holds the loans of the set
on its alternative, including after the owner takes the empty alternative.
The loop pass carries loans of outer sets into the next iteration. A
spawn made on an earlier inner iteration and an outer back edge can
have different inner decisions.

On the 160 controls of section 18.2 the verdicts are now 18 refused where
a run gets stuck, 134 accepted, and the same four pairs. The parent
`race_write` is refused by [L3] where it writes the borrowed vector.
The `shared_pool` example could overflow its unsigned accumulator on
inputs outside the original run. The fixture checks the sum before adding
and faults explicitly on overflow. The suite exercises the original sum
of 42, an exact sum of `u32.max` and an overflowing sum. The 11 core files
now have 95 runs, 72 compared with the erased semantics.

The command `cargo test --test checker_slice4` exercises the rule files
and the paired owner/member examples in the oracle and the checker.
Six deliberate mutations each broke a test. They removed the set holder at
spawn, liveness by availability, the loop-carried set loan, inheritance by
a payload, the exclusive update at spawn, or cumulative field updates.
A separate nested-loop test failed when the inner spawn and outer back edge
were treated as decisions of the same inner iteration.

### 18.4 Native run of a defined root, 25 November 2026

Under [E-Turn] a defined root has the only turn when its run starts.
If it can neither await nor spawn, no other task can run before it returns
or faults. A synchronous control it calls can start a nested run. Its
caller resumes when the inner root ends. The backend uses the defined
control's calling convention for this case, including its outcome slots
and fault unwinding. At this first checkpoint both emitters refused a module if a body
needed a task set, an await or a run of an extern control. Section 18.5
adds defined awaits. The diagnostic names the enclosing control
or boundary.

From `v2/`, run `cargo test --test backend_slice4`. The checker accepts
`tests/slice4/checked_run.core` as a whole. Its six directives give explicit
outcomes and traces. The test compares those oracle and erased runs with
compiled code at both widths of `usize`, at `-O0` and `-O2`. On the fault
path the root releases its lease before the caller releases its own.
On the nested path the three emits occur in order. Four vector inputs
account for the four allocations in each six-run batch. Each run ends with
zero live allocations. Before the change both tests stopped at the
unimplemented task-operation arm. No run here needs a schedule choice.
The scheduler and comparisons on generated task programs remain open (RB9).

### 18.5 A defined await gives up the turn, 25 November 2026

For a decision or capture on `await f`, the caller evaluates the operands
and binds them in a native activation. Its slots also hold the destinations
for the alternative payload and any fault. The ready task has a continuation
that enters `f` with this activation. The caller's stack keeps the activation
and borrowed places alive until the task returns. Entering a root at `run`,
and returning to its caller, give up no turn.

Modules that await a defined control declare the C host function
`uint64_t vn2_pick_turn(uint64_t ready_count)`. The host returns an index
among the ready tasks. A defined await in this checkpoint calls the host
with 1 before resuming the sole ready task. Section 18.6 adds choices among
members of a task set.

From `v2/`, run `cargo test --test backend_slice4`. The six directives in
`tests/slice4/checked_await.core` give 24 compiled comparisons with the
oracle and the erased interpreter across both widths and optimization levels.
The owned vectors account for both allocations per batch. The C-host test
also compares the complete sequence of turn offers and samples with each
interpreter independently. The two nested awaits offer one ready task each.
On four successive calls the host returns 0, 1, 2 and 2. The alternative that
skips both awaits makes one host call and receives 0. Omitting the host
selection or moving it after the continuation changes the transcript.

### 18.6 Native spawn and delivery of nonsuspending members, 25 November 2026

The single-set implementation used two queues. Section 18.12 shares the ready
queue across sets. A top-level `spawn` binds the arguments in an activation
in the owner's stack frame and appends it to the ready queue. At `await next`,
the C host receives the number of ready tasks. The owner is first when it can
receive a completed member or observe an empty set. The ready children follow
in spawn order. The index is taken modulo the offered count, as in the oracle.
A selected child runs to its exit and appends its activation, including the
tag and payload, to the done queue. The host chooses again. Selecting the owner
delivers the oldest completion. A done member contributes to `count` until
delivery. Selecting the owner on an empty set consumes the set.

This checkpoint covers one set with spawn sites in the owner's top-level
body. Each site runs at most once per invocation. Section 18.11 covers
spawns inside loops.
Decisions on `await next` can repeat in a loop. Section 18.6 covers producers
that finish in one turn. Section 18.7 extends this to defined awaits. A
producer at that checkpoint took and returned owned or copy values and let no fault escape. Sections 18.13 and 18.14 add borrowed inputs and results.
Section 18.8 covers defined awaits in the owner. Host waits, cancellation,
faulting calls and fault boundaries in an owner still give diagnostics. A synchronous call that starts a nested run uses a
separate invocation. The scripted native host consumes one `turns` choice
at each offer and chooses the first ready task after the choices run out.

In `tests/slice4/checked_spawn.core`, changing the first choice reverses two
pairs of emits. A second owner moves a vector to one child and receives it
under different completion orders. A third selects the middle of three ready
children, then appends another after a delivery. The commands to reproduce
the comparisons are `vn2 test tests/slice4/checked_spawn.core` and
`cargo test --test backend_slice4`. The latter tests both widths of `usize`
at `-O0` and `-O2`, including allocation accounting.

### 18.7 A member awaits with ready siblings, 25 November 2026

A spawned member can await a defined control that finishes its work in the
same turn. At each executed await the member binds its operands and result
destinations in its frame, saves the point where execution will resume, and
returns to the scheduler. It keeps its original position among the ready
members. The host can select a sibling, or the owner if a completed member
is waiting for delivery. When the host selects the suspended member again,
it enters the awaited callee. Its alternative and payload return to the
decision or capture in the member, which continues on the same turn.

The owner keeps the member's locals, history bits and native temporary
slots in its activation, including any place lent to the awaited callee.
They survive another member's turn and a return from `await next` to the
owner. Only first entry initializes the slots. A loop can use the same
resume point on successive iterations. A call of the producer as a root
uses the ordinary defined-await entry.

Run `cargo test --test backend_slice4` from `v2/`. The six directives in
`tests/slice4/checked_member_await.core` compare event order, returned
vectors and local writes across the two interpreters and compiled code.
A C host separately links the emitted module and records the number of ready
tasks at every turn of `rounds(2, 1)`. Its eight offers are 2, 2, 2, 2,
1, 1, 1, 1. Its three emits are q, p, p. Both interpreters produce the
same offers, emits and final result. A member awaiting an extern control
or a callee with its own set still receives a diagnostic. Section 18.10
covers a defined callee that awaits again.

### 18.8 A set owner awaits with ready children, 25 November 2026

At a defined await the owner binds the operands and gives up its turn. The
host sees the owner first, followed by ready members in spawn order. A member
can yield, or finish and leave its result queued. When the host selects the
owner, it enters the awaited callee. Results stay queued and counted until
the owner receives them through `await next`. A defined await before the set
is created, while it is empty, or after it is consumed offers one ready task.

This checkpoint covers a defined callee that finishes on that turn without
a fault or termination. Section 18.9 extends it to nested awaits.
Run `cargo test --test backend_slice4` from `v2/`. In `runs_parent` from
`tests/slice4/e_await.core`, both interpreters and a separately linked C host
observe ready counts of 2, 1, 1, 1. The default schedule emits parent then
child. Choosing index 1 on the first offer emits child then parent.
`tests/slice4/checked_owner_await.core` also exercises two suspended children,
a captured vector result, delivery in completion order and a borrow of an
owner local across an await.

### 18.9 Nested defined awaits in the set owner, 26 November 2026

Each defined await binds its operands and gives the host a turn choice before
the callee starts. Each awaited activation inherits its owner’s ready children.
At the next await, the host can select one of those children. Result
slots and borrowed locals stay live during the child's turn. A separate `run`
starts a fresh root. The outer children become eligible again when execution
returns to the outer run and reaches another await.

The internal async entry takes a pointer to the owner’s scheduler. Each set
records its producer's resume function. A public C entry and a fresh run
start without inherited children. At this checkpoint, targets on the owner's await chain had to be defined,
have no set of their own and neither fault nor terminate. Section 18.10
extends nested suspension to a spawned member. Section 18.15 covers sets
created on the owner's await chain.

From `v2/`, run `vn2 test tests/slice4/checked_nested_owner_await.core`
and `cargo test --test backend_slice4`. The fixture gives the child the
first, second or third turn choice. A separately linked C host requests
indices 0, 1, 0, 1 in `example`. The second request sees only the root of
the nested run. The fourth sees the outer child, which runs before the
leaf. Both interpreters and the C host see the leaf write 5 through the
borrow of the local in `middle`.

### 18.10 Nested defined awaits in a spawned member, 26 November 2026

When a member awaits a defined control, it binds the operands and result
destinations before it yields. If the callee reaches another defined
await, the same member gives up the turn again. The host can select a
sibling while the caller and callee are both suspended. When the callee
returns, its caller continues on that turn.

The scheduler keeps one queue entry for the member. Each active awaited
callee whose body can suspend has its own resume index and local slots.
The caller allocates this frame on entry to the await and frees it when
the callee returns. Bound arguments and result destinations stay in the
caller. A borrow into a suspended activation therefore still names the
same place when the host selects the member again. A callee that finishes
in one turn uses the existing bound arguments without a heap frame.

From `v2/`, run `vn2 test tests/slice4/checked_nested_member_await.core`
and `cargo test --test backend_slice4`. Five runs exercise both delivery
orders, two members suspended in the same callees, an ordinary root call
and a recursive member that resumes three callers at the same await site.
The counted native batch makes 19 allocations, eight vectors and eleven
callee frames, and releases each. A separately linked C host selects the
sibling on turn 4. The owner receives its result on turn 5. On turn 6 the
leaf writes through the borrow of the local in `middle`.

### 18.11 Repeated spawn sites, 26 November 2026

A loop can spawn several outstanding members of one set at the same site.
Each visit binds its arguments in a distinct member frame. A member keeps
its frame while ready, suspended or waiting for delivery. At `await next`
the owner moves the selected payload out before it can spawn again.

Top-level sites keep their stack frames. Loop sites draw from the heap.
A set keeps at most one delivered heap frame for the next loop spawn,
which resets its resume index and binds new arguments. Delivering another
heap frame frees the previous spare. Receiving `empty` frees the last spare.
A spawn traps if increasing the count would exceed the target's
`usize.max`. Native reporting of the `exhausted` end and scripted capacity
limits remain open.

From `v2/`, run `vn2 test tests/slice4/checked_repeated_spawn.core` and
`cargo test --test backend_slice4 repeated_spawn`. The six directives
cover zero iterations, mixed stack and heap frames, several completions queued
before delivery, and a suspended member overtaken by its sibling.
In `alternating(4)` four visits to one site use one member allocation.
Across all six runs the counted batch makes 29 allocations and releases
each. A separate test lowers the emitted count limit to four and three.
The fourth spawn fits at four and reaches the trap at three. Both
interpreters run the same program at both limits.

### 18.12 Scheduling across sets in one owner, 26 November 2026

All ready members of the owner enter one queue in spawn order. A yielding
member retains its position. Each member carries its originating set, which
supplies the producer entry and receives the completed frame. Each set keeps
its own completion queue, undelivered count and spare frame.

At a defined await the host can select the owner or any ready member. At
`await next(s)`, the owner becomes eligible when `s` is empty or has a
completion. A different set's members can run and finish while the owner
waits. Delivery takes the oldest completion of `s`. Consuming an empty set
leaves the members of other sets eligible, including through a nested
defined await. A fresh `run` still starts with its own root.

From `v2/`, run `vn2 test tests/slice4/checked_multiple_sets.core` and
`cargo test --test backend_slice4 multiple_sets`. In `interleaved` two
packets return vectors and a stamp returns the host's sampled turn. When
both packets finish before the stamp, the C host sees the owner first
become eligible after the stamp finishes on turn 4. When the stamp
finishes first, the host can still select either packet at the await that
consumes the empty stamp set. In `iterations(3)` the owner consumes and
recreates a second set of the same producer three times before receiving
the outer value of 99.

### 18.13 Borrowed spawn inputs, 26 November 2026

A spawned member stores the address of each borrowed place in its frame.
A view argument carries the addresses of its borrowed fields. A member can
forward those borrows to a defined callee at an await. The checker holds the
loans in the set until the owner consumes it on the empty arm ([TK3]).

From `v2/`, run `vn2 test tests/slice4/checked_borrowed_spawn.core` and
`cargo test --test backend_slice4 borrowed_spawn_inputs`. In `pair`, each
member borrows two different fields of the owner's record. Its callee reads
the destination's old value and writes the source value through the exclusive
borrow. The owner observes both writes after draining the set. The second
schedule delivers the second member first. The other two runs pass borrows
in a view to a nonsuspending member and forward the same shared borrow to
two outstanding loop members. The four runs allocate two loop frames per
batch and leave no allocations live at any exit.

The paired checker test
`a_task_set_holds_shared_and_exclusive_loans_until_drained_tk3` exercises
the owner writing a shared lender or reading an exclusive lender. Each
conflict is rejected and gets stuck in the oracle. Moving that access
after the drain is accepted and the oracle reaches the owner's exit.

### 18.14 Borrowed task results, 26 November 2026

At `await next`, the selected arm loads the result from the completed
member's frame into the owner's payload slot. For a shared or exclusive
borrow, the value it loads is the address the member returned. A view
carries the addresses of its fields in the same way. The owner can keep
the payload through another spawn that reuses the member frame and through
the empty arm that frees it. Under [TK3] the payload inherits the loans
held by its set and continues to hold them while it is live.

From `v2/`, run `vn2 test tests/slice4/checked_borrowed_result.core` and
`cargo test --test backend_slice4 borrowed_results_keep`. In `order`, two
suspended members return different fields of the same owner record. Two
schedules deliver the values in opposite orders. In `recycle`, two loop
spawns use one heap frame. After draining the set the owner reads 79
through the first reference and 31 through the second. In `edit`, one set
delivers a shared reference. Another delivers either an exclusive reference
or a view containing shared and exclusive fields. Writing through each
alternative after draining both sets changes the selected owner field.

The checker test `await_next_payload_holds_the_loan_after_the_set_is_consumed_tk3`
pairs a write to a shared lender and a read of an exclusive lender with
the same accesses to a different local. While the payload is still used,
each conflict is rejected and the oracle gets stuck. Each access to the
different local is accepted and the oracle reaches the owner's exit.

### 18.15 Task sets in an awaited callee, 26 November 2026

A defined callee on the root task's await chain can create and drain its
own sets. The first activation that owns a set supplies storage for the run's
ready queue. Awaited activations use that queue, including through a callee
that owns no set. Each set keeps its completion queue. At an inner
`await next`, an outer member can run, but its completion goes back to its
own set. A fresh `run` starts its own queue.

From `v2/`, run `vn2 test tests/slice4/checked_awaited_set.core` and
`cargo test --test backend_slice4 awaited_set_owners`. In `outer(false)`
the host sees three choices at the await inside `inner`: the root, the
outer packet and the inner packet. At the following `await next` only
the two packets are eligible. Selecting the outer packet leaves one ready
task, the inner packet. Selecting the inner packet first gives the root
a turn while the outer packet is still ready. In both schedules the two
callers receive their own vectors. `outer(true)` enters the same inner
control through a fresh run. In `collect(2)` three recursive activations
drain distinct sets of the same producer and return `[0, 1, 2]`.

### 18.16 A spawned member waits for its children, 26 November 2026

A nonfaulting spawned member can own sets. At `await next(s)` it saves
where to resume and gives up its turn. If `s` is empty or has a completion,
the member stays eligible. Otherwise the set records the member waiting
for it. The scheduler counts eligible members and skips blocked ones when
applying the host's index in spawn order. The first completion in `s` clears
its waiter and makes the member eligible in its original position. Delivery
takes place on the parent's selected turn, in completion order.

A child spawned once by a member can use space in that member's frame when
the child owns no sets. A repeated spawn takes separate storage. So does
a member's child if the child owns sets. That keeps recursive frame layouts finite.
Each set can reuse one delivered heap frame and frees it on the empty arm.

From `v2/`, run `vn2 test tests/slice4/checked_member_set.core` and
`cargo test --test backend_slice4 member_owned_sets`. The parent in
`owner` waits for the two packets in `wanted`. A peer and a side packet can
finish while it waits. One schedule delivers `[22]` then `[44]`. Another
finishes both wanted packets before the parent runs again, delivers them
in the opposite order, and wakes the parent once. In each run the side set
delivers `[70]`. The linked C host checks every ready count and sampled
turn. In `twins`, two recursive producers return paths of different lengths
in either completion order. In `borrow_after_empty` the member yields on an
empty set and returns a reference to its owner's local.

### 18.17 Task sets in a callee awaited by a member, 26 November 2026

A defined await extends the same task. The callee keeps its own resume point,
locals and sets. When it waits for a child, the scheduler parks the spawned
member to which that activation belongs. A completion in the requested set
wakes that member. On its selected turn it resumes at the innermost pending
await. When the callee returns, the caller continues on that turn.

From `v2/`, run `vn2 test tests/slice4/checked_nested_member_set.core` and
`cargo test --test backend_slice4 nested_member_sets`. In `pair`, two workers
wait in separate invocations of `collect`, whose only suspension points are
`await next`. At the fifth offer both workers are blocked and their two
children are ready. Choosing the second child delivers `[22]` before `[11]`.
Choosing the first reverses the order. The linked C host checks every offer
and the turn on which each worker continues after its captured await.

In `recursive(3)` three invocations of `descend` each keep a child and a set
across a recursive await. The deepest activation drains an empty set. Two
schedules return `[1, 2, 3]`, including one in which each child finishes
before the deeper call returns.

### 18.18 A defined root waits for the host, 26 November 2026

A root alone in its run can await a noncancellable, nonfaulting extern async
control. The operands and the caller's output slots are bound before the
request starts. While the root waits, its run has one pending operation. The
host selects that operation, completes it, and chooses the ready root for its
next turn ([E-AwaitHost], [E-Turn]). A later await can use the first result.
If a synchronous caller starts a fresh run, tasks in the outer run stay
suspended while that root waits.

For `await fetch(...)`, the generated C header declares
`struct vn2_wait_fetch`. Its fields hold the host's opaque `host_state`
(initially null), the typed inputs (`in_key`, for example) and result-slot
pointers in alternative and field order. The request lives through completion
and belongs to the caller. The host can keep its operation handle in
`host_state`. By-value operands transfer to the host once. Borrowed operands
remain valid for the operation and returned loans name their declared origins.

1. `vn2_start_fetch(request)` starts the operation on the bound inputs.
2. With no ready task, `vn2_pick_waiting(states, count)` receives the host
   state values of the pending operations. It may wait until a completion is
   available. In this subset the sole operation has index zero for every
   choice modulo `count`.
3. `vn2_complete_fetch(request)` receives the same request, fills the
   selected alternative's result slots, releases any host-owned operation
   state, and returns the alternative tag. A C boolean payload uses one byte.
4. `vn2_pick_turn(1)` offers the ready root. Execution continues in the
   selected arm or with the captured outcome.

Run `vn2 test tests/slice4/checked_host_wait.core` and
`cargo test --test backend_slice4 root_host_wait` from `v2/`. The fixture
exercises both outcomes, a unit result, an owned vector, a returned exclusive
loan, and an inner run with an outer member ready. A linked C host checks
each waiting and ready offer, request identity and bound operands. It supplies
the byte 2 for true in both a capture and a decision. The scripted native
host uses the only pending operation and consumes its answer at completion.

### 18.19 A direct run of a host operation, 26 November 2026

In `run fetch(...)`, the host operation itself is the root of the fresh run
([E-Run]). The caller binds inputs and result slots and starts the same
typed request described in section 18.18. The host selects the sole pending
operation and completes it. That ends the run. The caller immediately receives
the chosen alternative and its fields, in a decision or a capture. A module
using only direct host runs needs `vn2_pick_waiting` and can link without
`vn2_pick_turn`.

Tasks ready in an enclosing run keep their place while the inner run executes.
In `checked_host_run.core`, two successive calls to `fetch` finish before the
host is offered either outer member. The caller receives 37. The first scripted
turn still determines whether the caller receives member 11 or member 22 first.

Run `vn2 test tests/slice4/checked_host_run.core` and
`cargo test --test backend_slice4 direct_host_runs` from `v2/`. The fixture
also transfers an owned vector and returns a resource whose type has no
fault release. The caller consumes that resource once. A linked C host checks
the order of waiting, completion and ready offers, and writes byte 2 for true
to the boolean result slot. The native subset here covers noncancellable,
nonfaulting host operations.

### 18.20 A task-set owner awaits the host, 27 November 2026

When the root awaits a noncancellable, nonfaulting host operation, the host
starts the bound request immediately ([E-AwaitHost]). Until it completes,
the ready choices contain only eligible members of that run ([E-Turn]).
A member can yield, spawn a child, wait for it and wake on its completion.
The scheduler checks the ready count after every turn. Once that count is
zero, `vn2_pick_waiting` sees the sole pending operation in this example. The host completes
it, then `vn2_pick_turn(1)` offers the root its turn. Finished members stay
in their sets until their owner takes their results.

Run `vn2 test tests/slice4/checked_owner_host_wait.core` and
`cargo test --test backend_slice4 owner_host_wait` from `v2/`. In
`collect`, the C host checks that `fetch` starts before the first ready
offer. Selecting the first eligible member each time gives ready counts of
2, 2, 1 and 1 before the host selects the completion. The root receives 37
and finds two results in its set. Another scripted order delivers member 22
before member 11.

In `inherited`, the await is in `relay`, which has no set of its own.
It uses the scheduler of the owner that awaited it. A member spawns a child
that calls `ping(55)`. The child wakes its parent, which drains the set and
finishes. Both interpreters and compiled code record `ping` before the host
completion of `fetch(8, false)`.

### 18.21 A spawned member waits for the host, 27 November 2026

A member that awaits a noncancellable, nonfaulting extern starts the bound
request and gives up its turn ([E-AwaitHost]). Its activation retains the
request, operands and result slots. Once the run has no ready task, the
host sees the pending root first, if any, then waiting members in spawn
order ([E-Turn]). The host selects an index modulo the number of operations
offered. Completion fills the selected activation's slots and makes its
task ready. The member can await again before it exits. An owner blocked
on that set can take the member's result only after the exit ([E-Next]).

Run `vn2 test tests/slice4/checked_member_host_wait.core` and
`cargo test --test backend_slice4 member_host_wait` from `v2/`.
In `owner`, the member resumes between two requests and its owner eventually
receives 37. In `nested`, a callee in the member transfers an owned vector
to the host and returns its replacement. In `overlap`, the root and member
wait on different controls. The scripted host chooses the first pending
control matching the next answer, just as the interpreter does.

In `pair`, two members wait for the same control. A linked C host starts
member 22 first, receives the handles for 11 and 22 in spawn order, and
chooses index 3 modulo 2. It completes 22, offers the resumed member and
then its owner a turn, and finally completes 11. A single candidate fits
on the stack. For overlapping waits, the scheduler allocates temporary
arrays for the host handles and corresponding members and releases them
before calling the selected completion.

### 18.22 Replaying choices among pending host operations, 27 November 2026

A native run keeps separate positions in its `turns` and `waiting` lists.
When the scheduler offers pending operations, the scripted host consumes
one waiting index, even for a single operation. The scheduler reduces the
index modulo the number offered. When the list runs out, the scripted
host selects the first pending operation whose control matches the next
answer, or the first operation if there is no match. An explicit selection
takes precedence even if the next answer then fails. Both lists start
afresh at each run in a batch.

From `v2/`, run `vn2 test tests/slice4/e_turn.core
tests/slice4/checked_waiting_choices.core` and
`cargo test --test backend_slice4 waiting_choices`. The seventh turn
directive completes two reads in the specified order. In the new fixture,
a lone operation consumes the first item of `waiting [0, 5]`. The next
offer holds the root's stamp and the reads from members 11 and 22. Index 5
selects member 22. The next scripted answer selects member 11, ahead of
the pending stamp. A linked C host checks the identity and order of the
handles on all four offers and returns the same trace and payload. A
separate test selects the stamp when the answer belongs to a read and
checks the three events recorded before the host failure.

## 19. What is open

- **Requalification.** No slice meets its exit. The [review](review.md)
  lists the defects and, in its section 3, what each slice owes: a generator
  that is not one program (done for slice 1), a kernel that validates axiom
  instances and a certificate text that
  a reader validates (done), a decision procedure that is complete without bounds (done), the
  fault-boundary rules of the oracle, the unsound cases of the
  checker in slices 2 and 3, the double free in compiled code, a reader that
  reads the corpus, and a formatter that keeps comments. The work follows
  section 10 of the review, slice 1 first.
- **Later work.** Slice 4 still needs native cancellation, faulting host operations, member faults, capacity and generated
  task programs in the native comparison.
- **This document.** Sections 3, 4 and 7 describe slice 1 only, and the list
  of choices below was not extended for slices 2 to 4 (review, RO9, RD3).
  Each is brought up to date when its slice is requalified.
- **Operators that the surface does not have yet.** The wrapping and
  saturating operators and the numeric conversions are named in the core and
  the fact logic and have no spelling. They belong to phase 5.

Choices the oracle makes where the core leaves one:

1. **A quotient by zero in a formula is 0 and a remainder by zero is the
   dividend.** [E-Formula] asks only that the value depend on the operands
   alone.
2. **The greatest `usize` is a parameter of the run**, `2⁶⁴ - 1` unless the
   run says `2³² - 1`. The fact logic proves for every width between ([A2]),
   so a checked program must not be stuck under either.
3. **A literal of type `usize` must fit 32 bits**, since it has to be a value
   on every target.
4. **Effects are checked in slice 1** ([E-Effect]), because an extern control
   with an effect is what makes a trace. The checker's rule for them ([F3])
   belongs to slice 2.
5. **A run is bounded by fuel**, and a run that exhausts it ends in `fuel`.
   Running forever is not stuck ([core](core.md), section 6.10).

Writing the oracle asked four questions of the core, which section 12 of the
[core](core.md) records with the answers: the order of `∧` and `∨`, a
function call inside a formula, an assignment to a name without a slot, and
the type of an integer literal.
