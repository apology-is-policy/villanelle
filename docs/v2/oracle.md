# Villanelle v2 oracle, checker and typed backend

Status: **under requalification**, 23 November 2026. Phases 2, 3 and 4 of
the [redesign plan](../redesign-plan.md). The crate holds code for slices 1 to
3 through oracle, erased interpreter, checker, call expansion and typed LLVM
IR backend, and for slice 4 in the oracle. The oracle of slice 1 and its
conformance suite (sections 1 to 7) are qualified. Everything described from
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
| `bdd`, `facts`, `kernel` | The ROBDD engine; the `Th_Z` fact logic with its search and its counterexamples ([M1] to [M6]); and the certificate kernel, which is given the query by the checker, makes the formula of every instance from its name with its own matcher for the axiom list, checks the proof of every lemma (a tree of the steps of [V3], with Split) and recomputes the Boolean step in a diagram of its own ([V1] to [V4]) (section 10) |
| `certificate` | The text of certificates ([V5]): the writer, and a reader that makes the tables, the goals and the premises from a text alone and gives them to the kernel (section 10) |
| `counts` | The work of the search as counts for each thread, which `vn2 check --counts` prints; nothing reads them to decide anything (section 10) |
| `terms`, `lia`, `rational` | The terms, rows, proofs, names of instances and certificates that the search and the kernel both read; the theory check for the rows of a candidate, which answers with a model, a proof or the counted limit of [J6], and whose last part, the Omega test (`lia/omega.rs`), decides rows without bounds (section 7 of the [fact logic](facts.md) has a note on the method); and the rationals of its simplex method |
| `check` | The phase 3 checker: coverage ([K1] to [K8]), conditional facts and SSA renaming ([N1] to [N5]), acknowledgement ([C2]), availability ([O1], [O2], [O4], [O6]), obligations ([P1] to [P8]), effects ([F3]) and impossible-arm warnings ([U16]) (section 10) |
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
answer.

## 6. Directives

A line that begins with `//!` states a run beside the program, and what it
must yield.

```text
//! run add(250, 5) => done sum {255}
//! run add(250, 6) => stuck X7 E-Arith
//! run pump(2) with [read -> value {7}; read -> closed] => done total {7}
//!     trace [read(2) -> value {7}; read(2) -> closed {}]
//! run address(4294967295) usize 32 => stuck X7 E-Arith
//! reject W1
```

`run` names an entry control and its arguments. The options follow: `with
arithmetic`, `with [...]` for a scripted host, `usize 32`, `fuel N`. After
`=>` comes the expected end: `done` with the alternative and its payload,
`faulted` with the message, `terminated` with the status of `terminate n`,
`stuck` with the state and the clause, `violation`, `host-failed`, `fuel`, or
`not-an-execution` (the arguments are not values of the parameter types, or
the precondition of the entry is false; section 8 of the core does not count
such a run as an execution). `trace [...]` states the events. `reject` names
the clause by which `resolve` must refuse the program.

Every `run` that ends in `done`, `faulted`, `terminated` or `fuel` is also carried out under the erased
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
  of its contract or of its body ([P1] to [P8], X6, X7). `mutate::classify`
  runs a mutant in the oracle; across 16 sets of numbers of the template,
  the stuck mutants reach all 15 stuck states of slice 1. They are the
  target rejection set for the phase 3 checker.
  `every_stuck_mutant_of_a_generated_program_is_rejected`
  (`v2/tests/checker.rs`) takes every mutant of four generated programs,
  draws the runs of each for its own preconditions, and requires that
  `resolve` or the checker rejects each mutant with a stuck run: 72 of them,
  of every kind but `DropInvariant`, which leaves no run stuck.
- **Fuzzing (`fuzz`, `vn2 fuzz`).** `vn2 fuzz --seed N --count N` takes the
  program of each seed through the reader, the oracle and the erased
  semantics on entries that satisfy its precondition, and asks the checker.
  `--native` compiles each accepted program at `-O0` and `-O2`, for both
  widths of `usize`, and requires that every run ends as the oracle's did
  and with the same trace. `--mutants` tries every mutant too, where a
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
  4,066, none of which has a stuck run among those tried. The time
  limit of the checker is of the clock. On a machine under load, a campaign
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
  the rationals, a first search for a model along the splits, rounded sums,
  splits, and behind them the Omega test, with a proof as a tree of the
  steps of [V3] that is pruned to what its ends rely on. The splits have
  half of the steps that are left; where they do not end, the Omega test
  starts from the rows as they were given. It changes variables in an
  equality without a unit coefficient, and for a variable that no side
  bounds with units it tries the sums of the bounds as they are, then the
  sums of the bounds tightened by the distance that the coefficients fix,
  and then one equality, a splinter, for each value within that distance.
  Its search has the shape of its proof: a split for each bound, with the
  splinters on one side and the tightened bound on the other. The refinement
  starts from the goal and the structure. A candidate that has a model is
  completed to one of every term. Every premise and every instance that
  this model fails is conjoined before the next candidate is taken: a model
  that fails one fails several, and each would cost a candidate.
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
candidates, theory checks and their rows, premises added, tableaus,
exchanges of the simplex method with the entries they write, splits, and
the theory checks that went on to the Omega test with the splinters it
tried. `vn2 check --counts` prints them, and `vn2 fuzz` prints their sum
over a campaign. A count is the same on every machine and
under every load, and by [J6] the same in every run: the checker keeps
names and terms in ordered tables, and a hash table is used only where
nothing reads its order (the tables of the diagram, the tables that give
a term or a row its number, and sets that are only asked whether they hold
a thing). The counts of 23 November 2026, for the
ten surface programs of the three slices: 552 queries, 602 candidates, 551
theory checks of 6,742 rows, 1,486 premises added, and no exchange. For the
data kernel of slice 2 (`v2/tests/kernels/slice2_data.rails`): 212 queries,
915 candidates, 581 theory checks of 35,051 rows, 3,240 exchanges that
write 120,731 entries, and 2,375 splits.
Over the 5,403 mutants of 25 generated programs: 1,116,283 queries,
1,408,543 candidates, 1,252,564 theory checks of 21,804,605 rows, 239,878
exchanges that write 7,436,643 entries, and 80,203 splits. One of these
theory checks goes on to the Omega test, which refutes its rows without a
splinter; it accounts for 4.5 million of the entries. No theory check of
the surface programs, of the data kernel or of the 300 generated programs
does.

`v2/tests/kernel.rs` tests the kernel's matcher: every instance of [A1],
[A2] and [A7] to [A9] that it grants is evaluated with the values that the
real operations give, on operands at the ends of every type and beyond them;
the kernel grants every instance that the search makes for terms of every
form; and it refuses eighteen names that name no instance, and the range of a
term that the checker did not write.

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
proof with sixteen splinters that validates from the certificate text. The
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
| `empty-map` | `∅` |
| `vec [ITEMS]` | A vector literal |
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
  those selectors alone. Differential tests verify exact outcome and trace
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
  (`[R2]`–`[R5]`).** Reuses `erased::compute_availability` (including post-end
  snapshots for lexical boundary fallthrough) so `[R4]` destruction and `[R5]`
  `on fault release` unwinding (`@vn2_release_<res>`) are driven purely by
  static history-bit selectors with zero runtime moved flags. Unchecked vector
  indexing and `⊥ → unreachable` follow `[R2]`. A general structured arm-chain
  lowering pass (`plan_structured_flow`) chains mutually exclusive `Decide` and
  two-sided `Test` arm spans directly into their arm statements, eliminating
  redundant history-bit checks and speculative arm branches in hot loops.
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
  borrowed variants), `Loop`, and `Leave` (`LeaveRecord::payload_roots`),
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
- **Later work.** For slice 4, the checker ([TK1] to [TK7], `count(x)`
  facts) and the backend are not written.
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
