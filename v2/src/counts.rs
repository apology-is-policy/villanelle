//! Counts of the work that the search does, so that it can be measured
//! without a clock.
//!
//! A count is the same on every machine and under every load, which a time
//! is not. The counts are kept for each thread, and nothing reads them to
//! decide anything: they change no answer.
//!
//! The module also holds the one clock of the search: a time by which the
//! check of a thread ends, which a harness sets that waits for an answer
//! only so long ([`set_deadline`]). A check that nobody waits for would go
//! on, and one whose diagrams grow takes memory while it does. No answer
//! depends on the clock: a check either ends before its time or gives none.

use std::cell::Cell;
use std::time::Instant;

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
    /// Theory checks that went on to the Omega test, and the splinters it
    /// tried.
    pub omega_tests: u64,
    pub splinters: u64,
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
        omega_tests: 0,
        splinters: 0,
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
    let ticks = TICKS.with(|ticks| {
        let next = ticks.get().wrapping_add(1);
        ticks.set(next);
        next
    });
    if ticks.is_multiple_of(4096) {
        keep_time();
    }
}

thread_local! {
    static DEADLINE: Cell<Option<Instant>> = const { Cell::new(None) };
    static TICKS: Cell<u32> = const { Cell::new(0) };
}

/// What a check whose time is up unwinds with.
pub struct OutOfTime;

/// Gives the search of this thread a time by which it ends, or with `None`
/// takes the time away.
pub fn set_deadline(deadline: Option<Instant>) {
    DEADLINE.with(|here| here.set(deadline));
}

/// Ends the check of this thread, by unwinding with [`OutOfTime`], if it has
/// a time and the time is up. The search asks now and then.
pub fn keep_time() {
    if let Some(deadline) = DEADLINE.with(Cell::get)
        && Instant::now() >= deadline
    {
        std::panic::resume_unwind(Box::new(OutOfTime));
    }
}

impl Counts {
    /// These counts and `other` together.
    pub fn plus(&self, other: &Counts) -> Counts {
        Counts {
            queries: self.queries + other.queries,
            candidates: self.candidates + other.candidates,
            lemmas_reused: self.lemmas_reused + other.lemmas_reused,
            theory_checks: self.theory_checks + other.theory_checks,
            rows: self.rows + other.rows,
            refuted: self.refuted + other.refuted,
            models: self.models + other.models,
            premises: self.premises + other.premises,
            tableaus: self.tableaus + other.tableaus,
            exchanges: self.exchanges + other.exchanges,
            entries: self.entries + other.entries,
            splits: self.splits + other.splits,
            omega_tests: self.omega_tests + other.omega_tests,
            splinters: self.splinters + other.splinters,
        }
    }

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
            omega_tests: self.omega_tests - earlier.omega_tests,
            splinters: self.splinters - earlier.splinters,
        }
    }
}

impl std::fmt::Display for Counts {
    fn fmt(&self, out: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            out,
            "{} queries, {} candidates ({} by an earlier lemma), {} theory checks of {} rows \
             ({} refuted, {} with a model), {} premises added, {} tableaus, {} exchanges \
             writing {} entries, {} splits, {} Omega tests with {} splinters",
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
            self.omega_tests,
            self.splinters,
        )
    }
}
