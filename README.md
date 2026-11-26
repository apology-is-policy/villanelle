# Villanelle

Villanelle is a systems language organized around **explicit named outcomes**, **decisions**, and **path selection**:

- Operations complete through named outcome alternatives (`■`) with typed payloads and optional logical conditions (`⇐ φ`) rather than single return values or implicit exceptions.
- Callers invoke multi-outcome operations with `Δ`, acknowledge every alternative in the contract, and select execution histories with Boolean path conditions (`╞═` in v2 Rails, `[mask]:` in v1 and plain form).
- Ownership (`copy < drop < must`), must-complete resource lifecycles, fault boundaries, second-class borrows, structured task sets, and arithmetic proof obligations (`⊢ φ`, `⊥`) are checked statically over reduced ordered binary decision diagrams (ROBDDs) without hidden control flow or runtime tags.

This repository holds two tracks:

1. **Villanelle v2 (`v2/`, [`docs/v2/`](docs/v2/README.md)) — active redesign**: The clean-slate v2 specification and an implementation in progress, following the [redesign plan](docs/redesign-plan.md). The specification introduces the **Rails** surface syntax, a small guarded-command core calculus, a linear integer and data fact logic ($\text{Th}_{\mathbb{Z}}$) with proof certificates and counterexamples, second-class borrows and views, and task sets. The implementation has code for much of it and is being requalified; [`docs/v2/review.md`](docs/v2/review.md) states what is verified.
2. **Villanelle v1 (root crate, `0.306.0`, tag `v1-final`, [`docs/language-reference.md`](docs/language-reference.md)) — frozen baseline**: The complete v1 compiler (`./bin/vnc`), reference and native LLVM 22.1.8 / Rust backends, collections library (`0.1.0`), persistent CLI and loopback HTTP settings service ([`applications/settings/`](applications/settings/README.md)), and VS Code extension ([`editors/vscode/`](editors/vscode/README.md)).

---

## v2 Redesign Status and Progressive Roadmap

The v2 redesign ([`docs/redesign-plan.md`](docs/redesign-plan.md)) progresses through paper specification (Phase 1), four vertical slices implemented across the executable oracle (Phase 2), certificate-producing checker (Phase 3), and typed LLVM IR backend (Phase 4), followed by expressiveness, formal mechanization, runtime performance, and tooling (Phases 5–8).

**State on 25 November 2026.** Phase 1 is accepted. Code exists for slices 1 to 3 through oracle, checker and backend, and for slice 4 in the oracle, the checker and the native subset for a single ready task. A [review](docs/v2/review.md) of that code found that no slice met the plan's exit, and the code is being requalified slice by slice. Slice 1 is requalified. For slice 2 the fault boundaries of the oracle are corrected, the findings of the review in the checker are closed, a generator writes the constructs of the slice, and its programs agree in the oracle, the erased semantics, the checker and compiled code; the slice is not complete, and the oracle of the slice has a test for each clause of its rules, and the review lists what the slice still owes (the axioms of the data held against real values, a rate for the mutants, long campaigns, measured kernels). For slice 3 the oracle has a test for each clause of its rules, the checker handles writes through loop borrows (RC1) and ordinary calls that receive two exclusive fields of one record (RC33), the checker is held against the oracle on the rule files of the borrows and the loans, and a generator writes the constructs of the slice, whose programs the checker accepts and the erased semantics agrees with, and the checker rejects every mutant of them, of sixteen kinds, that a run finds stuck; a rate for the mutants, long campaigns and measured kernels are owed. For slice 4 the task rules answer the four findings of their second review (RT1 to RT4), the oracle has a test for each clause of its rules, and the checker is held against the oracle on those rule files, control by control, including the loans of a task set. Native code runs defined roots and gives up the turn at a defined await when only one task is ready. Multiple ready tasks and a generator of task programs are owed. The Rails reader reads 1 of the 17 corpus files. The tables below say what exists, not what is verified.

### Phase Overview

| Phase | Scope | Status | Primary Artifacts |
| --- | --- | --- | --- |
| **Phase 0** | Freeze v1 at `0.306.0` (`v1-final`) | **Complete** | Tag `v1-final`, [`docs/language-reference.md`](docs/language-reference.md) |
| **Phase 1** | Core calculus, $\text{Th}_{\mathbb{Z}}$ fact logic, second-class borrow model, Rails surface syntax, paper corpus, reading & repair test | **Complete** (accepted 20 Nov 2026) | [`docs/v2/README.md`](docs/v2/README.md), [`core.md`](docs/v2/core.md), [`facts.md`](docs/v2/facts.md), [`references.md`](docs/v2/references.md), [`surface.md`](docs/v2/surface.md), [`corpus.md`](docs/v2/corpus.md), [`reading-test.md`](docs/v2/reading-test.md) |
| **Phase 2** | Executable core oracle, erased semantics, differential fuzzer, mutation harness, Rails reader & elaborator | **Active**: requalifying slice 1. Code exists for slices 1–4; the exit is not met ([review](docs/v2/review.md)) | [`v2/`](v2/), [`docs/v2/oracle.md`](docs/v2/oracle.md), [`docs/v2/review.md`](docs/v2/review.md) |
| **Phase 3** | ROBDD + $\text{Th}_{\mathbb{Z}}$ checker, certificate kernel, counterexamples, canonical Rails formatter, warnings | Code for slices 1–4, unqualified: unsound in slices 2 and 3, and the slice 4 checker has oracle-backed clause tests for the task rules. Since 23 November the kernel makes every axiom instance itself and validates certificates from their text ([review](docs/v2/review.md)) | [`v2/src/bdd.rs`](v2/src/bdd.rs), [`facts.rs`](v2/src/facts.rs), [`kernel.rs`](v2/src/kernel.rs), [`check.rs`](v2/src/check.rs), [`surface.rs`](v2/src/surface.rs) |
| **Phase 4** | Theorem 4 call expansion and direct typed LLVM IR & C ABI backend under erased semantics | Defined roots and awaits run with one ready task. The root and spawned members can each create sets and await callees that create their own sets. The host sees ready members in spawn order across those sets. A lone root can await a noncancellable, nonfaulting host operation and resume with its result. A direct `run` of that operation returns to its caller on completion. Members can borrow owner fields across a defined await and return references to those fields. The host chooses which ready task runs next, including at a nested defined await in the owner or a member (RB9). For slices 1–3, generated programs of slices 1 and 2 agree with the oracle in compiled code since 23 November 2026, and those of slice 3 since 24 November, findings of the review are open, and no kernel under `experiments/` is measured ([review](docs/v2/review.md)) | [`v2/src/expand.rs`](v2/src/expand.rs), [`v2/src/codegen.rs`](v2/src/codegen.rs), [`v2/tests/backend.rs`](v2/tests/backend.rs), [`v2/tests/backend_slice2.rs`](v2/tests/backend_slice2.rs), [`v2/tests/backend_slice3.rs`](v2/tests/backend_slice3.rs), [`v2/tests/backend_slice4.rs`](v2/tests/backend_slice4.rs) |
| **Phase 5** | Expressiveness (callable parameters, recursion, `box⟨τ⟩`, value-position decisions) & v1 → v2 migrator | Planned | [`docs/redesign-plan.md`](docs/redesign-plan.md) |
| **Phase 6** | Lean 4 mechanization of safety, resource linearity, erasure, and expansion (Theorems 1–4) | Planned | [`docs/v2/core.md`](docs/v2/core.md) §8 |
| **Phase 7** | Native coroutine / task-set runtime & collection performance vs. optimized Rust | Planned | [`docs/redesign-plan.md`](docs/redesign-plan.md) |
| **Phase 8** | LSP server, VS Code Rails support, and v2 reference manual | Planned | [`docs/redesign-plan.md`](docs/redesign-plan.md) |

### Vertical Slices Across Phases 2, 3, and 4 (`v2/`)

Each vertical slice is taken end-to-end through the Phase 2 oracle and erased interpreter, the Phase 3 certificate-producing checker and formatter, and the Phase 4 call expander and typed LLVM IR backend. The cells say what code and tests exist. "Draft" means written and not qualified; what each slice still owes is in section 3 of the [review](docs/v2/review.md):

| Slice | Language Constructs | Clauses | Phase 2: Oracle, Erased & Surface | Phase 3: Checker, Kernel & Formatter | Phase 4: Expansion & Typed Backend |
| --- | --- | --- | --- | --- | --- |
| **1. Scalars and decisions** | `bool`, `u8`..`u64`, `i8`..`i64`, `usize`, pure `function`, `?` tests, `Δ` decisions, `↻` loops, `■` exits, `□` leaves, `↑` again, `⊥` impossible, `⊢` / `⇐` formulas, `outcome` groups, `■ auto`, `forward`, `■ Δ` adapters | `W1`–`W5`, `W7`, `W9`, `H1`–`H4`, `K1`–`K8`, `N1`–`N5`, `P1`–`P8`, `C1`–`C3`, `F3`, `R1`–`R3`, `S1`–`S6`, `I1`–`I6`, `I8`, `I10`, `I13`, `A1`, `A2`, `A7`–`A9`, `J1`–`J6`, `V1`–`V5`, `M1`–`M6`, `Y1`–`Y10`, `G1`–`G10`, `U1`–`U9`, `U13`–`U18`; `X1`–`X3`, `X6`, `X7`, `X9`, `X10` | **Oracle qualified; harness draft** — 41 `.core` & 4 `.rails` conformance suites with a test for each clause, seeded host, 120k arithmetic axiom property tests; a generator of valid programs (300 seeds: no stuck run, no difference from the erased semantics, every construct reached); seven kinds of mutants of generated programs, of which every one with a stuck run is rejected | **Draft** — ROBDD + $\text{Th}_{\mathbb{Z}}$ solver (simplex over the rationals with rounded sums and splits; a counted limit where it cannot decide), certificate kernel (told the query by the checker; makes every axiom instance itself; `vn2 validate` reads the certificate text), counterexample models, `vn2 format` (`[G10]`; loses comments), warnings (`[U5]`, `[U16]`–`[U18]`); held up under the review's attack | **Draft** — `vn2 expand` (Theorem 4), `vn2 emit-llvm` & `vn2 emit-c` (`[R1]`–`[R3]`), native runs at `-O0`/`-O2` agree with the oracle on the test programs and on 300 generated programs; one synthetic kernel measured, not the plan's exit |
| **2. Data, resources, and faults** | `struct` (`copy` / `drop`), `variant`, `[τ]`, `κ ⇀ υ`, `string`, `len`, `clone`, indexing `p[e]`, unpacking `S {x̄} := e`, usage kinds `copy < drop < must`, moves `▾`, `extern resource` (`on fault release`), captured `outcome⟨K⟩`, `fault`, lexical and named `boundary` / `contingency` / `supervise` | `T1`–`T6`, `O0`–`O6`, `F1`–`F6`, `R4`, `R5`, `I7`, `I9`, `I11`, `I12`, `A3`–`A6`, `M7`, `Y12`, `G4b`, `G7a`, `G12`, `U10`–`U12`; `X2`, `X3`, `X5`, `X8`, `X9` | **Draft** — fault-boundary rules wrong in three places; 13 `.core` & 4 `.rails` conformance suites (`show_file_resource.rails`, records/variants, collections/`∀`, boundaries/faults), erased history-bit fault release (`[R4]`, `[R5]`), Rails formatter (`[G10]`) & surface clauses (`[Y12]`, `[G4a]`, `[G4b]`, `[G7a]`, `[G12]`, `[U6]`, `[U10]`–`[U12]`, `[U14]`) | **Draft, unsound** (captures, boundary contingencies) — ROBDD movedness `M(x)` & ownership (`[O0]`–`[O6]`), fault & boundary checking (`[F1]`–`[F6]`), `&~` `old(y)` (`[P4]`), index bounds (`[P5]`), data axioms (`[A3]`–`[A6]`, `[I9]`, `[I11]`, `[I12]`), kernel validation (`kernel::validate`), `[M7]` counterexamples, all 4 `.rails` suites accepted | **Draft** (a value moved in a nested body is freed twice) — Theorem 4 expansion for data/borrows/resources/boundaries, typed LLVM IR & pointer-passing C ABI (`[R1]`–`[R5]`), static history-bit drop & `on fault release` unwinding, structured arm-chain lowering, `-O0`/`-O2` native runs across 32/64-bit `usize` agree on the test programs; one synthetic kernel measured |
| **3. Borrows and views** | `&τ`, `&~τ`, payload origins `∈`, `view struct`, borrow tags, place overlap, loop loan liveness | `W5a`, `W6`, `W8`, `W9`, `B1`–`B5`, `L1`–`L5`, `L2a`, `I7`, `I9`, `G4a`; `X4` | **Draft** — 2 `.core` & 2 `.rails` conformance suites, without a test for each clause (`borrows_and_tags.core`, `views_and_variants.core`, `borrows_and_variants.rails`, `views_and_loops.rails`), `view struct` & `∈` well-formedness (`[W5a]`/`[W6]`/`[W8]`/`[W9]`/`[T1]`/`[T4]`/`[T6]`/`[F5]`/`[F6]`), borrow tag oracle (`[B1]`–`[B5]`, `X4`) & zero-tag erased references (`[R1]`), `[E-Host]` borrow checks, Rails `[U6]`/`[U9]`–`[U11]`/Q16/`[G3]`/`[G10]` | **Draft, unsound** (a write through a borrow inside a loop) — ROBDD static loan checker (`[L1]`–`[L5]`, `[L2a]`, `[RM7]`), `[O3]`/`[O0]` borrow ownership, `[I7]`/`[I9]` borrow/view facts; all 34 synchronous `references.md` examples get their verdicts, and the loan rules held up under the review's attack | **Draft** — Theorem 4 borrow/view expansion, zero-tag erased `ptr`/`noalias`, composable C ABI headers, `-O0`/`-O2` 32/64-bit runs agree on the test programs; one synthetic kernel measured |
| **4. Tasks** | `async control`, `tasks⟨f⟩`, `spawn … into`, `await`, `await next`, `cancel`, `run`, `count`, cancellation & member fault delivery | `W10`–`W12`, `TK1`–`TK7`, `E-Run`–`E-Stop`, `R6`, `G7b`, `U19` | **Oracle requalified** — the task rules reviewed independently and repaired (RT1 to RT4), 11 `.core` files with a test for each clause and 1 `.rails` suite (`v2/tests/slice4/`), `[W10]`–`[W12]`/`[TK1]`/`[I10]` resolution, instrumented & erased cooperative schedulers (`[E-Run]`–`[E-Stop]`, `[R6]`), schedule-replaying comparison with the erased semantics, Rails `[G7b]`/`[U19]`/`[G3]`/`[G10]` | **Draft** — `[TK1]`–`[TK7]`: `count(x)` as a measure that `spawn` and `await next` change, sets that move on `empty`, what a task holds where it can be stopped, the faults of members at awaits, and `await`/`run` as calls; held against the oracle on the 11 rule files, control by control (18 refused where a run is stuck, 134 accepted, four caller/callee pairs). Sets hold loans until drained and transfer them to borrowed payloads (review, RC31) | **Draft** — defined roots and defined awaits agree with both interpreters on 12 runs at both widths and optimization levels. A C host observes the turn at await. Seven more runs exercise a single task set with top-level spawns, selectable ready children and owned results. Six runs cover member suspension, loop re-entry and ordinary root invocation. Four more cover owner awaits, including children finishing before the owner resumes and delivery in completion order. Six runs cover nested defined awaits in the owner and isolation of a nested run. Five runs cover nested member awaits, including overlapping invocations and recursion. A C host observes the owner receiving a sibling’s result while the first member is suspended in its callee. Six runs cover repeated spawns, delivery of distinct vectors in completion order, and reuse of a delivered frame. Six runs cover scheduling across sets and delivery from the requested set, including two sets with the same producer. Four runs cover borrowed spawn inputs, including writes to disjoint owner fields across suspension. Five runs cover borrowed results, including a reference used after its member frame is reused and an exclusive view delivered from a second set. Seven runs cover sets created in an awaited callee, recursive owners and isolation of a fresh run. Seven runs cover sets owned by spawned members, including parents waiting for different sets and recursive spawns. Five runs cover sets in callees awaited by members, including two workers waiting in the same control and a recursive await with a live child at each level. Nine runs cover a single pending host operation in a defined root, including sequential waits and an inner run with an outer member ready. Eleven runs cover direct host operations, including two outer tasks whose first turn choice survives both completions. Host awaits with competing tasks, cancellation and faults remain open (RB9) |

### Paper Corpus Highlights (Phase 1)

Rewriting the 8 v1 collection modules and the 4-module settings service into v2 Rails ([`docs/v2/corpus.md`](docs/v2/corpus.md)) reduced code size by more than half and eliminated all 15 v1 filler arms:

| Corpus Group | v1 Lines | v2 Lines | v1 Labels | v2 Labels | v1 Routes | v2 Routes | v1 Filler Arms | v2 Filler Arms | v2 Proof Lines (`⊢`/`⇐`) | v2 Proven `⊥` |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| **Collections library (8 modules)** | 476 | **231** | 66 | **7** | 72 | **7** | 13 | **0** | 8 | 3 |
| **Settings service (4 modules)** | 635 | **304** | 86 | **18** | 92 | **0** | 2 | **0** | 0 | 2 |
| **New stress programs (3 programs)** | — | **208** | — | **22** | — | **9** | — | **0** | 16 | 0 |

---

## v2 at a Glance: Rails and `vn2`

### Example 1: Arithmetic Proof Obligations and `⊥` Erasure

In [`v2/tests/slice1_surface/spend.rails`](v2/tests/slice1_surface/spend.rails), the test `? used > total → ■ over` establishes `¬(used > total)` on the continuing rail. When `checked_sub` is decided, its `underflow` alternative has contract condition `⇐ a < b`, which contradicts the continuing history. The programmer marks `underflow → ⊥`; the checker proves the arm unreachable and emits a certificate that the kernel validates, and the LLVM backend lowers the arm to `unreachable`:

```text
extern control checked_sub(a: u32, b: u32)
    ■ difference {value: u32} ⇐ a ≥ b ∧ value = a - b
    ■ underflow ⇐ a < b

control spend(total: u32, used: u32) ■ left {value: u32} │ over
│ ? used > total → ■ over
│ Δ checked_sub(total, used): difference {value} │ underflow → ⊥
│ ■ left {value}
╵
```

### Example 2: Decisions, Path Selection, and Guaranteed Cleanup

In [`v2/tests/slice1_surface/show_file.rails`](v2/tests/slice1_surface/show_file.rails), statements on the solid rail `│` run on every history still active, while junctions `╞═` select histories by Boolean combinations of outcomes:

```text
control show_file(filename: u32) ■ auto
│ Δ open(filename)
│ ├ opened {file}
│ ├ not_found → ■ missing
│ └ denied    → ■ failed
│ Δ read(file): data {contents} │ failed
│
│ ┄ Always attempt close, even if reading failed.
│ Δ close(file): closed │ failed
│
╞═ data
│ ┆ Δ decode_utf8(contents): text {text} → decoded │ invalid
│
╞═ decoded ∧ closed
│ ┆ emit(text)
│ ┆ ■ done
╞═ read.failed ∨ close.failed ∨ invalid
│ ┆ ■ failed
╵
```

### Running the v2 Toolchain (`vn2`)

`v2/` is a self-contained crate with zero external dependencies.

```sh
cd v2
cargo test                                                               # all suites; the backend tests need clang and rustc
cargo run --bin vn2 -- test tests/slice1/*.core tests/slice1_surface/*.rails tests/slice2/*.core tests/slice2_surface/*.rails tests/slice3/*.core tests/slice3_surface/*.rails tests/slice4/*.core tests/slice4_surface/*.rails
cargo run --bin vn2 -- check tests/slice1_surface/*.rails tests/slice2_surface/*.rails tests/slice3_surface/*.rails # typecheck, prove & validate certificates
cargo run --bin vn2 -- check tests/slice1_surface/*.rails --certificates > certificates.txt # write the certificate text
cargo run --bin vn2 -- validate certificates.txt # validate it from the text alone
cargo run --bin vn2 -- format tests/slice1_surface/show_file.rails tests/slice2_surface/show_file_resource.rails tests/slice3_surface/*.rails tests/slice4_surface/*.rails --check
cargo run --bin vn2 -- expand tests/slice3_surface/borrows_and_variants.rails  # Theorem 4 in-place call expansion
cargo run --bin vn2 -- emit-llvm tests/slice3_surface/views_and_loops.rails      # Phase 4 typed LLVM IR ([R1]-[R5])
cargo run --bin vn2 -- emit-c tests/slice3_surface/borrows_and_variants.rails    # C ABI header for borrows, views & data
cargo run --bin vn2 -- run tests/slice1_surface/spend.rails spend 10 4 --arithmetic
cargo run --bin vn2 -- print tests/slice1_surface/show_file.rails        # elaborate Rails and print canonical core form
```

### v2 Code Map (`v2/src/`)

| Module | Responsibility |
| --- | --- |
| [`v2/src/int.rs`](v2/src/int.rs) | Arbitrary-precision mathematical integers for `[E-Formula]`, `[E-Arith]`, and the certificate kernel |
| [`v2/src/syntax.rs`](v2/src/syntax.rs), [`v2/src/text.rs`](v2/src/text.rs) | Core calculus AST, glyph printer, and core reader (`selector ▷ command`) |
| [`v2/src/surface.rs`](v2/src/surface.rs) | Rails and plain-form surface parser (`[Y1]`–`[Y10]`, `[G1]`–`[G9]`), canonical formatter (`[G10]`), elaborator (`[U1]`–`[U15]`), and surface warnings (`[U5]`, `[U17]`, `[U18]`) |
| [`v2/src/typed.rs`](v2/src/typed.rs), [`v2/src/resolve.rs`](v2/src/resolve.rs) | Well-formedness (`[W1]`–`[W9]`, `[T1]`–`[T6]`, `[F5]`, `[F6]`) and bidirectional type resolution (`[C1]`–`[C3]`) |
| [`v2/src/bdd.rs`](v2/src/bdd.rs), [`v2/src/facts.rs`](v2/src/facts.rs), [`v2/src/kernel.rs`](v2/src/kernel.rs) | ROBDD manager, $\text{Th}_{\mathbb{Z}}$ decision procedure (`[S1]`–`[S6]`, `[I1]`–`[I13]`, `[A1]`–`[A9]`, `[J1]`–`[J6]`), certificate kernel (checks lemma steps and the Boolean step; not yet axiom instances, so not yet `[V1]`–`[V5]`), and counterexample builder (`[M1]`–`[M7]`) |
| [`v2/src/check.rs`](v2/src/check.rs) | Phase 3 checker (`[K1]`–`[K8]`, `[N1]`–`[N5]`, `[C2]`, `[O0]`–`[O6]`, `[L1]`–`[L5]`, `[L2a]`, `[P1]`–`[P8]`, `[F1]`–`[F6]`) and impossible-arm warnings (`[U16]`) |
| [`v2/src/expand.rs`](v2/src/expand.rs) | Theorem 4 in-place call expansion of defined controls |
| [`v2/src/codegen.rs`](v2/src/codegen.rs) | Phase 4 typed LLVM IR and C ABI backend under `[R1]`–`[R5]`, structured arm-chain lowering, and native `clang -x ir` differential runner |
| [`v2/src/oracle.rs`](v2/src/oracle.rs), [`v2/src/erased.rs`](v2/src/erased.rs), [`v2/src/differential.rs`](v2/src/differential.rs) | Instrumented operational semantics (§6, borrow tags `[B1]`–`[B5]`), zero-tag erased machine-word semantics (§9), and Theorem 3 differential harness |
| [`v2/src/host.rs`](v2/src/host.rs), [`v2/src/script.rs`](v2/src/script.rs), [`v2/src/rng.rs`](v2/src/rng.rs) | Scripted, checked-arithmetic, and seeded extern hosts (`[E-Extern]`, `[E-Host]`) and `//!` test directive runner |
| [`v2/src/generate.rs`](v2/src/generate.rs), [`v2/src/mutate.rs`](v2/src/mutate.rs) | Core program generators (`valid` writes programs that are valid by construction from their histories and intervals, `template` is one fixed regression program, `free` is random) and single-step stuck-state mutation classifier; [`v2/src/fuzz.rs`](v2/src/fuzz.rs) (`vn2 fuzz`) holds reader, semantics and checker against each other on them |

---

## Villanelle v1 Baseline (`0.306.0`, Frozen at `v1-final`)

The root crate implements Villanelle v1 (`0.306.0`), frozen at tag `v1-final` before the v2 redesign. Its complete specification is in [`docs/language-reference.md`](docs/language-reference.md) and its companion chapters under [`docs/reference/`](docs/reference/grammar.md), with the full 0.46–0.306 checkpoint history recorded in [`docs/language-revision.md`](docs/language-revision.md).

### v1 Highlights

- **Language and verification**: Explicit outcome contracts (`exits`), `delta` routing, path selection labels `[mask]:`, second-class references and origin groups (`from`, `['a]`), traits and generic controls, must-complete resources with protocol state machines, lexical and named fault boundaries (`fault boundary`, `contingency`, `supervise`), and scoped async task execution (`async control`, `defer`, `spawn`, `await`, `cancel`).
- **Backends**: Reference interpreter, generated Rust backend (`--backend rust`), and direct native LLVM 22.1.8 / LLD backend (`--backend llvm`, including direct LLVM Switch-Resume coroutine lowering for async controls).
- **Collections library (`0.1.0`)**: Eight pure Villanelle modules in [`library/`](library/README.md) (`membership`, `search`, `reduction`, `partition`, `sequence_batches`, `traversal`, `ordering`, `ordered_search`).
- **Settings service**: Persistent CLI and concurrent loopback HTTP settings service in [`applications/settings/`](applications/settings/README.md) with typed Rust host adapters.
- **Editor tooling**: Language server (`vnc lsp`), formatter (`vnc format`), contract and outcome-absorption snapshots, path explanations (`vnc explain`), and the VS Code extension in [`editors/vscode/`](editors/vscode/README.md).

### Build and Run v1

For the direct LLVM native backend, set `LLVM_SYS_221_PREFIX` to a static LLVM/LLD 22.1.8 installation. For a Rust-only bootstrap without LLVM, add `--no-default-features`.

```sh
cargo build --locked --release --bin vnc
./target/release/vnc check playground/hello.vn
./target/release/vnc exec playground/hello.vn
./target/release/vnc build playground/hello.vn --release
./playground/build/hello
```

Common `./bin/vnc` commands:

```sh
./bin/vnc check playground/hello.vn
./bin/vnc exec playground/forwarding.vn
./bin/vnc exec playground/collections.vn
./bin/vnc exec playground/port.vn --entry parse_port -- 443
./bin/vnc format applications/settings/server.vn --check
./bin/vnc expand examples/refresh.vn examples/manifest.json refresh
./bin/vnc certify-expansion playground/forwarding.vn playground/manifest.json main > expansion.json
./bin/vnc verify-expansion playground/forwarding.vn playground/manifest.json expansion.json
./bin/vnc protocol playground/read_file.vn playground/manifest.json show_file playground/protocol/read_failed.json
```

Verify the v1 compiler and test suites:

```sh
cargo test --locked
cargo clippy --locked --all-targets -- -D warnings
TELLUR_TEST_BACKEND=rust cargo test --locked --features llvm --test settings_application
TELLUR_TEST_BACKEND=llvm cargo test --locked --features llvm --test settings_application
```

### v1 Code Map

| Location | Responsibility |
| --- | --- |
| `src/syntax.rs`, `src/manifest.rs` | v1 parser, formatter, and trusted type/primitive contracts |
| `src/bdd.rs`, `src/check.rs`, `src/inference.rs` | Symbolic path analysis, typing, coverage, and ownership/borrow checking |
| `src/generics.rs`, `src/generic_controls.rs`, `src/traits.rs` | Concrete layouts, generic definition checking, trait conformance, and static dispatch |
| `src/ir.rs`, `src/verify.rs` | Checked representation, provenance, inspection, and structural verification |
| `src/expand.rs`, `src/runtime.rs` | Region expansion, expansion certificates, and reference execution |
| `src/native.rs`, `src/native/llvm.rs`, `src/native/runtime.rs` | Native Rust & LLVM 22.1.8 lowering, coroutine lowering, and host runtime |
| `src/lsp.rs`, `editors/vscode/` | Language server, diagnostics, hover, and VS Code extension |
| `library/` | Villanelle v1 collections library (`0.1.0`) |
| `applications/settings/` | Persistent CLI and loopback HTTP settings application |
| `playground/`, `examples/`, `tests/` | Interactive examples, conformance cases, and differential test suites |

The project is licensed under [Apache 2.0](LICENSE).
