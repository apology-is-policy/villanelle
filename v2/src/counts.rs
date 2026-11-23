//! Counts of the work that the search does, so that it can be measured
//! without a clock.
//!
//! A count is the same on every machine and under every load, which a time
//! is not. The counts are kept for each thread, and nothing reads them to
//! decide anything: they change no answer.

use std::cell::Cell;

/// What the search did on this thread since the thread began.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Counts {
    /// Questions asked of the decision procedure.
    pub queries: u64,
    /// Candidates: assignments that satisfy the formula so far.
    pub candidates: u64,
    /// Candidates that a lemma of an earlier question refuted.
    pub lemmas_reused: u64,
    /// Candidates given to the theory check, and the rows they had together.
    pub theory_checks: u64,
    pub rows: u64,
    /// Theory checks that ended with a proof, and with a model.
    pub refuted: u64,
    pub models: u64,
    /// Premises and instances that a model failed, and that were added.
    pub premises: u64,
    /// Tableaus built, exchanges made in them, and entries written by the
    /// exchanges.
    pub tableaus: u64,
    pub exchanges: u64,
    pub entries: u64,
    /// Splits of a variable at a value that is not an integer.
    pub splits: u64,
}

thread_local! {
    static HERE: Cell<Counts> = const { Cell::new(Counts {
        queries: 0,
        candidates: 0,
        lemmas_reused: 0,
        theory_checks: 0,
        rows: 0,
        refuted: 0,
        models: 0,
        premises: 0,
        tableaus: 0,
        exchanges: 0,
        entries: 0,
        splits: 0,
    }) };
}

/// The counts of this thread.
pub fn now() -> Counts {
    HERE.with(Cell::get)
}

/// Changes the counts of this thread.
pub fn count(change: impl FnOnce(&mut Counts)) {
    HERE.with(|here| {
        let mut counts = here.get();
        change(&mut counts);
        here.set(counts);
    });
}

impl Counts {
    /// What was done between `earlier` and these counts.
    pub fn since(&self, earlier: &Counts) -> Counts {
        Counts {
            queries: self.queries - earlier.queries,
            candidates: self.candidates - earlier.candidates,
            lemmas_reused: self.lemmas_reused - earlier.lemmas_reused,
            theory_checks: self.theory_checks - earlier.theory_checks,
            rows: self.rows - earlier.rows,
            refuted: self.refuted - earlier.refuted,
            models: self.models - earlier.models,
            premises: self.premises - earlier.premises,
            tableaus: self.tableaus - earlier.tableaus,
            exchanges: self.exchanges - earlier.exchanges,
            entries: self.entries - earlier.entries,
            splits: self.splits - earlier.splits,
        }
    }
}

impl std::fmt::Display for Counts {
    fn fmt(&self, out: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            out,
            "{} queries, {} candidates ({} by an earlier lemma), {} theory checks of {} rows \
             ({} refuted, {} with a model), {} premises added, {} tableaus, {} exchanges \
             writing {} entries, {} splits",
            self.queries,
            self.candidates,
            self.lemmas_reused,
            self.theory_checks,
            self.rows,
            self.refuted,
            self.models,
            self.premises,
            self.tableaus,
            self.exchanges,
            self.entries,
            self.splits,
        )
    }
}
