//! Villanelle v2.
//!
//! The specification is in `docs/v2/`. This crate is built beside v1 and
//! shares no code with it. It grows by slices; each slice passes through the
//! oracle, the checker and the backend before the next begins.
//!
//! | Module | Holds |
//! | --- | --- |
//! | `int` | Mathematical integers |
//! | `syntax`, `text` | The core text form: its tree, printer and reader |
//! | `surface` | The Rails surface syntax: layout, grammar and elaboration into the core |
//! | `typed`, `resolve` | The typed core, and the way to it from the tree |
//! | `bdd`, `facts`, `kernel` | The ROBDD engine, the fact logic `Th_Z` with its search, and the certificate kernel, which is told the query by the checker and trusts nothing of the search |
//! | `certificate` | The text of certificates ([V5]): a writer, and a reader that gives what a text states to the kernel |
//! | `terms`, `lia`, `rational` | Terms, rows and proofs; the theory check on integers; the rationals of its simplex method |
//! | `counts` | The work of the search as counts, so that it is measured without a clock |
//! | `check` | The Phase 3 checker: coverage, acknowledgement, availability, obligations and effects |
//! | `expand` | Theorem 4 call expansion: in-place expansion of decisions on defined controls |
//! | `codegen` | The Phase 4 typed LLVM IR and C ABI backend under the erased semantics ([R1] to [R3]) |
//! | `oracle`, `host` | The instrumented semantics and the hosts of a run |
//! | `erased` | The erased semantics, which release code implements |
//! | `differential` | The comparison of the two semantics, run by run |
//! | `script` | Test directives written beside a program |
//! | `rng` | A seeded source of pseudo-random numbers |
//! | `generate` | Random core programs and construct coverage |
//! | `fuzz` | Generated programs and their mutants against reader, semantics and checker |
//! | `mutate` | Single-step mutations of valid programs, classified by the oracle |

pub mod bdd;
pub mod certificate;
pub mod check;
pub mod codegen;
pub mod counts;
pub mod differential;
pub mod erased;
pub mod expand;
pub mod facts;
pub mod fuzz;
pub mod generate;
pub mod host;
pub mod int;
pub mod kernel;
pub mod lia;
pub mod mutate;
pub mod oracle;
pub mod rational;
pub mod resolve;
pub mod rng;
pub mod script;
pub mod surface;
pub mod syntax;
pub mod terms;
pub mod text;
pub mod typed;

/// Reads and resolves a program in the core text form.
pub fn load(source: &str) -> Result<typed::Program, String> {
    let tree = text::parse(source).map_err(|error| error.to_string())?;
    resolve::resolve(&tree).map_err(|error| error.to_string())
}

/// Reads, elaborates and resolves a program in the Rails surface syntax.
pub fn load_surface(source: &str) -> Result<typed::Program, String> {
    let tree = surface::elaborate(source).map_err(|error| error.to_string())?;
    resolve::resolve(&tree).map_err(|error| error.to_string())
}
