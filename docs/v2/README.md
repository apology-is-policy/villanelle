# Villanelle v2 design

Phase 1 of the [redesign plan](../redesign-plan.md): the design on paper. The
author accepted it on 20 November 2026, and the documents here are the working
specification of v2 ([Acceptance](#acceptance)). An implementation is in
progress in the crate `v2/`. What it is verified to do, and what it is not, is
in the [review](review.md) of 23 November 2026.

v1, the language and compiler at 0.306, is described by the
[language reference](../language-reference.md) and stays as it is.

| Document | Deliverable | State |
| --- | --- | --- |
| [Core calculus](core.md) | The core language, its instrumented semantics, the checker's judgments, and the claims to test and mechanize | Draft 2, accepted. The synchronous language has two reviews folded in. Tasks and named boundaries were read by the combined review, which found four programs that the task rules accepted and the semantics left stuck, and no checking rule for named boundaries; the implementation of slice 4 folded three further repairs into `[W11]`, `[E-AwaitHost]`, `[TK6]` and `[I10]` (`core.md` section 12). The independent second review of the task rules ([task-review.md](task-review.md), 23 November 2026) found them right and four further defects, which the rules answer since 24 November 2026; RT1 and RT3 by the author's choices. Records the decisions on Q1 to Q5, Q18, RT1 and RT3. |
| [Fact logic](facts.md) | The interpreted fragment behind `⊨`, the decision procedure, certificates, counterexamples, worked examples | Draft 1, accepted; two reviews folded in. Records the decisions on Q6 to Q10. The corpus added the length of a vector literal. |
| [Reference model](references.md) | Second-class borrows and views: the model, 36 worked examples in Rails and core form with verdicts, the tag semantics on an example | Draft 1, accepted; one review folded in, which found the 36 verdicts to agree with their clauses. Records the decisions on Q16 and Q17. |
| [Surface](surface.md) | The Rails grammar, layout, and the elaboration into the core, including the acknowledgement rule and outcome groups | Draft 1, accepted, with the task forms of the core's draft 2 and the forms the corpus needed (traits, named boundaries, `copy` types); one review folded in. Records the decisions on Q11 to Q15 and Q19. |
| [Corpus on paper](corpus.md) | The settings application, the eight collection modules and three new programs, rewritten by hand, with counts and findings | Draft 1, accepted; checked by hand and read by one review, which found no error in the programs. Library 476 to 231 lines, application 635 to 304, no filler arm; thirteen gaps repaired in the other documents, thirteen limits left open. |
| [Oracle](oracle.md) | Phases 2, 3 and 4: the instrumented semantics, the Rails surface reader, elaborator and formatter, the certificate-producing checker, call expansion (Theorem 4) and the typed LLVM IR and C ABI backend (the crate `v2/`), with the conformance suite | **Under requalification.** Code exists for slices 1 to 3 through oracle, checker and backend, and for slice 4 in the oracle and, since 25 November 2026, in the checker including task-set loans (review, RC31). The native backend supports defined roots, defined awaits with one ready task, and scheduling members across sets owned by the root, spawned members and their respective awaited callees. Members can wait for a child or yield at a defined await. Members can borrow places in the owner across an await and return references or views that name those places (review, RB9). No slice meets its exit: the oracle of slice 1 is qualified, and the rest is draft. Slice 1 is being requalified first. |
| [Review](review.md) | What the implementation of 21 and 22 November is verified to do, the findings against it with reproductions, what each slice still owes, and the course | Open, 23 November 2026. Its section 9 has the state of each finding. |
| [Second review of the task rules](task-review.md) | An independent reading of the task rules of the core and the fact logic against the semantics, with probes of the oracle of slice 4 | 23 November 2026. Four findings, RT1 to RT4, open for slice 4; the repairs of 22 November hold up. |
| [Reading and repair test](reading-test.md) | v1 and v2 versions of the same programs, given to people and to agents | First run with agents done: 24 runs, 23 fully correct, so no difference between the versions is shown on reading. The repair needs 8 edits in v2 against 14. People have not taken it. |

## Acceptance

The author accepted phase 1 on 20 November 2026, and with it the choices that
each document lists and the recommendation of every question, Q1 to Q19 (Q1 to
Q5 on 19 November). The documents are normative for the phases that follow.
They are corrected, with a note of what changed, when the oracle, the checker
or a review finds an error. A change to an accepted decision goes to the
author.

Three things were open at acceptance, and the author accepted with them named:

- **The task rules.** The repairs that the combined review led to
  ([TK3] to [TK6], [E-Await], [E-AwaitHost], [E-Stop], [N5], [F5] and [F6] of
  the core, [J3] and [I10] of the fact logic, [G3] of the surface) have not
  had their second review. On 22 November 2026 the implementation of slice 4
  folded three further repairs into `[W11]`, `[E-AwaitHost]`, `[TK6]`
  (`core.md` section 12) and `[I10]` (`facts.md`). They read as correct and
  stay, but they were made by the implementation and no review was written
  ([review](review.md), RD2). The independent review was made on 23
  November 2026 ([task-review.md](task-review.md)): the repairs hold up,
  and it made four findings of its own, RT1 to RT4. The rules answer them
  since 24 November 2026 (`core.md` section 12; RT1 and RT3 by choices of
  the author, section 11). The oracle and the erased semantics hold all
  four since 24 November 2026, and the checker holds RT1 and RT3 since 25
  November 2026 ([review](review.md), section 9).
- **Workarounds.** The plan's exit asks that the corpus show no construct that
  v2 cannot express without a workaround. Three of the thirteen open limits of
  the [corpus](corpus.md) (section 6.2) are workarounds until phase 5:
  consuming a vector element by element (O1), receiving a single result
  through a decision (O2) and disposing of an empty vector (O5).
- **The reading test.** It showed no difference between the versions in either
  direction, with agents only. People have not taken it.

## Conventions

- Program text is written in Rails, the adopted surface syntax, and placed in
  `text` fences so that the manual checks do not try to compile it. The
  reference for how Rails looks is
  [`experiments/syntax_lab/rails/`](../../experiments/syntax_lab/rails/).
- Core programs use the same glyphs without sugar, plus `▷` between a selector
  and the command it guards.
- Normative clauses carry identifiers in brackets. The phase 2 conformance suite
  takes an accepting and a rejecting test from each.
- A choice that goes beyond the accepted decisions is listed at the end of the
  document that makes it, as a question for the author with a recommendation.

## Order of work

1. Core calculus, draft 1, and its reviews (done).
2. Fact logic, since the worked examples of every other document depend on what
   can be proved (draft 1 done).
3. Surface and elaboration, then the reference model as examples in that
   syntax (draft 1 of both done).
4. Core calculus draft 2: tasks (done).
5. The corpus on paper, which tests all of the above and yields the counts the
   plan asks for (lines, labels, filler arms, annotations) (draft 1 done).
6. One independent review of all five documents together, for consistency and
   soundness (done; the repairs it led to have not been reviewed again).
7. The reading and repair test (first run with agents done; people are the
   author's part and open).
8. The author's acceptance of phase 1 (20 November 2026).
Items 9 to 16 were written on 21 and 22 November. The [review](review.md) of
23 November found that none of them meets its exit, so each is marked
"draft" here; item 17 is the work in progress.

9. Phase 2 in slices: the oracle, erased semantics, generator, differential
   harness, mutation tests and Rails surface reader with elaboration for
   scalars and decisions (the oracle and its conformance suite done; since
   23 November the generator writes programs from their histories, and the
   harness and the mutations run on them: review, RG1).
10. Phase 3 for slice 1: the checker on the typed core with ROBDD histories,
    the `Th_Z` fact logic, the independent certificate kernel, counterexample
    models, the canonical Rails formatter and compiler warnings (draft: the
    formatter loses comments; since 23 November the kernel makes every
    axiom instance itself, a certificate text is validated without the
    checker, and the procedure gives a proof, a model or a counted limit
    and is complete without bounds: review, RC9 to RC13, RC16).
11. Phase 4 for slice 1: Theorem 4 call expansion and the typed LLVM IR and C
    ABI backend under the erased semantics ([R1] to [R3]), verified against the
    oracle and the erased interpreter at `-O0` and `-O2` (original and expanded)
    and measured against optimized Rust on one synthetic scalar kernel
    (draft; no kernel under `experiments/` is measured).
12. Phases 2, 3 and 4 for slice 2: structs, variants, vectors, maps, strings,
    usage kinds `copy < drop < must`, moves `▾`, `extern resource`
    (`on fault release`), captured outcomes, faults, lexical and named
    boundaries, erased history-bit fault release (`[R4]`, `[R5]`), Rails
    surface and canonical formatter, Phase 3 ROBDD ownership (`[O0]`–`[O6]`),
    faults and boundaries (`[F1]`–`[F6]`), data axioms (`[A3]`–`[A6]`, `[I9]`,
    `[I11]`, `[I12]`, `[M7]`) with kernel certificate validation, and Phase 4
    Theorem 4 call expansion + typed LLVM IR and C ABI backend (`[R1]`–`[R5]`)
    run natively at `-O0`/`-O2` across 32/64-bit `usize` (draft: the fault
    boundaries of the oracle are requalified since 23 November 2026, sections
    6.9 and 7.7 of the core say how each end of a contingency runs, and so
    are pure operations and the operands and contracts of the built-in
    operations; the findings by which the checker accepted stuck programs
    of this slice (RC2 to RC8) and compiled code freed a value twice (RB1)
    are closed, every compiled run is counted for allocations left live,
    the oracle has a test for each clause of the rules of the data since
    24 November 2026, with the checker held against it control by control,
    and the review lists the open findings and what the slice still owes).
13. Phase 2 for slice 3: second-class borrows `&τ`/`&~τ`, `view struct`,
    payload origins `∈`, well-formedness (`[W5a]`, `[W6]`, `[W8]`, `[W9]`,
    `[T1]`, `[T4]`, `[T6]`, `[F5]`, `[F6]`), instrumented borrow tag semantics
    (`[B1]`–`[B5]`, `X4`) and zero-tag erased live references (`[R1]`),
    borrowed variant decisions (`[E-Outcome]`), `[E-Host]` borrow/origin
    checks, normative `get`/`entry_at` borrowed payloads, and Rails surface
    support (`[U6]`, `[U9]`–`[U11]`, Q16, `[G3]` `■ auto` origins, `[G10]`
    formatter) (draft: two conformance files, without a test for each
    clause).
14. Phase 3 for slice 3: static ROBDD loan checking (`[L1]`–`[L5]`, `[L2a]`,
    `[RM7]`), borrow ownership refinements (`[O0]`, `[O3]`), borrow/view fact
    propagation and invalidation (`[I7]`, `[I9]`), `checker_slice3.rs` covering
    all 34 synchronous worked examples in [`references.md`](references.md) and
    all Slice 3 `.core` stuck controls, plus kernel-validated verification of
    both `tests/slice3_surface/*.rails` programs (draft: a write through a
    borrow inside a loop is accepted and stuck).
15. Phase 4 for slice 3: Theorem 4 call expansion across borrows and views
    (`expand.rs`), dereference-vs-move fix (`erased.rs`), zero-tag erased
    borrow lowering (`ptr` / `ptr noalias` on `&~`), `view struct` field pointer
    dereferencing, composable topologically-ordered C ABI headers, and
    non-dangling borrowed host payloads (`codegen.rs`), plus `-O0`/`-O2`
    32/64-bit differential parity on the test programs
    (`tests/backend_slice3.rs`) (draft).
16. Three further repairs of the task rules (`core.md` section 12, `facts.md`
    `[I10]`) and Phase 2 for slice 4: `async control`, `extern async control`,
    `tasks⟨f⟩`, `tasks⟨f⟩()`, `count(x)`, `spawn … into`, `await`, `await next`,
    `cancel`, `run`, well-formedness (`[W10]`–`[W12]`, `[TK1]`, `[I10]`),
    instrumented and erased cooperative task schedulers (`[E-Run]`–`[E-Stop]`,
    `[R6]`), schedule-replaying differential parity, Rails surface (`[G7b]`,
    `[U19]`, `[G3]`, `[G10]`), and conformance suites (`tests/slice4/*.core`,
    `tests/slice4_surface/*.rails`, `tests/slice4.rs`) (draft: two
    conformance files, and the erased semantics releases wrongly under
    faults).
17. Requalification, in the order of the [review](review.md), section 10:
    a real generator for slice 1 and fuzzing with it; the kernel and the
    decision procedure brought to the fact logic; slices 2, 3 and 4 in order
    with a test for each clause; the reader extended until the corpus runs;
    an independent second review of the task rules (in progress; the
    review of the task rules is [task-review.md](task-review.md)).
