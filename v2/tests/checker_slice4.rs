//! Phase 3 checker conformance tests for slice 4: the rules of the tasks
//! ([TK1] to [TK7] of the core, section 7.8), held against the oracle on the
//! rule files of `v2/tests/slice4/`, control by control.

use std::path::PathBuf;
use villanelle_v2::check::{self, CheckedProgram};
use villanelle_v2::load;

fn check_core(source: &str) -> Result<CheckedProgram, check::Error> {
    let program = load(source).unwrap_or_else(|e| panic!("resolve failed: {e}\n{source}"));
    check::check(&program)
}

fn accept_core(label: &str, source: &str) -> CheckedProgram {
    let report = match check_core(source) {
        Ok(r) => r,
        Err(e) => panic!("[{label}] expected acceptance, got: {e}\n{source}"),
    };
    report
        .revalidate()
        .unwrap_or_else(|e| panic!("[{label}] the kernel rejected {e}"));
    report
}

fn reject_core(clause: &str, source: &str) -> check::Error {
    match check_core(source) {
        Ok(_) => panic!("[{clause}] expected rejection by [{clause}], but accepted:\n{source}"),
        Err(e) => {
            assert_eq!(
                e.clause, clause,
                "[{clause}] expected [{clause}], got [{}]: {e}\n{source}",
                e.clause
            );
            e
        }
    }
}

/// The program is stuck in the oracle, as its directive says, and the
/// checker refuses it by `clause`.
fn stuck_and_rejected(clause: &str, source: &str) {
    let report = villanelle_v2::script::check(source);
    assert!(
        report.failures.is_empty() && report.runs > 0 && !report.stuck.is_empty(),
        "[{clause}] the oracle does not find the program stuck: {:?}\n{source}",
        report.failures
    );
    reject_core(clause, source);
}

/// The program runs to its end in the oracle, as its directive says, and the
/// checker accepts it.
fn done_and_accepted(clause: &str, source: &str) {
    let report = villanelle_v2::script::check(source);
    assert!(
        report.failures.is_empty() && report.runs > 0 && report.stuck.is_empty(),
        "[{clause}] the oracle does not run the program to its end: {:?}\n{source}",
        report.failures
    );
    accept_core(clause, source);
}

/// The program runs to its end in the oracle, as its directive says, and the
/// checker refuses it by `clause`: a rule that asks more than the runs need.
fn done_and_rejected(clause: &str, source: &str) {
    let report = villanelle_v2::script::check(source);
    assert!(
        report.failures.is_empty() && report.runs > 0 && report.stuck.is_empty(),
        "[{clause}] the oracle does not run the program to its end: {:?}\n{source}",
        report.failures
    );
    reject_core(clause, source);
}

/// The rule files of the tasks (`v2/tests/slice4/`), each with the runs that
/// apply its rule and the runs that are stuck by it.
const RULE_FILES: [&str; 11] = [
    "e_await",
    "e_await_host",
    "e_cancel",
    "e_exhaust",
    "e_member_fault",
    "e_run",
    "e_spawn_next",
    "e_stop",
    "e_turn",
    "tasks_and_turns",
    "tasks_faults_and_cancel",
];

/// The controls of the rule files that the checker refuses although no run
/// of them is stuck, with the clause and the reason.
const ASKS_MORE: [(&str, &str, &str, &str); 2] = [
    (
        "tasks_and_turns",
        "shared_pool",
        "TK3",
        "a stand-in: the loans of a task set are not checked yet, so a spawn that may lend is refused",
    ),
    (
        "tasks_and_turns",
        "excl_pool",
        "TK3",
        "a stand-in: the loans of a task set are not checked yet, so a spawn that may lend is refused",
    ),
];

/// The runs that are stuck in a control that the checker accepts, because
/// another control broke the clause and the checker refuses that one: the
/// file, the control in which the run is stuck, the control that broke the
/// clause, the clause by which the checker refuses it, and how.
const STUCK_BY_ANOTHER: [(&str, &str, &str, &str, &str); 4] = [
    (
        "e_stop",
        "stops_locker",
        "locks",
        "TK4",
        "`locks` holds a lock, which is not fault-releasable, at `await tick`, where the fault of its sibling stops it",
    ),
    (
        "tasks_faults_and_cancel",
        "lock_pool",
        "lock_or_fault",
        "TK4",
        "`lock_or_fault` holds a lock at `await wait_io`, where the fault of its sibling stops it",
    ),
    (
        "tasks_and_turns",
        "bad_effect_member",
        "bad_effect_parent",
        "F3",
        "the stack of a member continues into the control that spawned it ([E-Effect]), and `bad_effect_parent` does not allow `io.secret`",
    ),
    (
        "tasks_and_turns",
        "read_at",
        "race_write",
        "TK3",
        "`race_write` writes `xs` while a member holds a borrow of it; the stand-in refuses the spawn that lends",
    ),
];

/// Whether a clause of the checker is the one that excludes a stuck state of
/// the oracle.
fn excludes(clause: &str, state: &str) -> bool {
    match state {
        "X2 E-Var" => clause == "O2",
        "X4 B1" => clause.starts_with('L'),
        "X5 E-Scope" => clause == "O5",
        "X7 E-Call" | "X7 E-Extern" | "X7 E-Spawn" => clause == "P3",
        "X8 E-Stop" | "X8 E-Unwind" => matches!(clause, "F1" | "F2" | "TK4" | "TK5"),
        "X9 E-Effect" => clause == "F3",
        "X10 E-Decide" => clause == "C2",
        _ => false,
    }
}

/// Holds the checker against the oracle on the rule files, control by
/// control: a control in which a run is stuck must be rejected by a clause
/// that excludes the stuck state, and any other must be accepted, apart from
/// those of `asks_more`, which the checker refuses by the clause named, and
/// the pairs of `stuck_by_another`. Gives the numbers of the controls
/// rejected and accepted.
fn held_against_the_oracle(
    files: &[&str],
    asks_more: &[(&str, &str, &str, &str)],
    stuck_by_another: &[(&str, &str, &str, &str, &str)],
) -> (usize, usize) {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/slice4");
    let mut failures = Vec::new();
    let mut rejected = 0;
    let mut accepted = 0;
    let mut asked_more = 0;
    let mut paired = 0;
    for name in files {
        let source = std::fs::read_to_string(dir.join(format!("{name}.core"))).unwrap();
        let report = villanelle_v2::script::check(&source);
        assert!(
            report.failures.is_empty(),
            "{name}: {}",
            report.failures.join("\n")
        );
        let program = load(&source).unwrap_or_else(|e| panic!("{name}: {e}"));
        let verdicts = check::check_each(&program).unwrap_or_else(|e| panic!("{name}: {e}"));
        for (control, verdict) in verdicts {
            let stuck = report.stuck_in.get(&control);
            if let Some((_, _, _, clause, _)) = stuck_by_another
                .iter()
                .find(|(file, _, culprit, _, _)| file == name && *culprit == control)
            {
                match (stuck, verdict) {
                    (None, Some(error)) if error.clause == *clause => paired += 1,
                    (_, verdict) => failures.push(format!(
                        "{name}: `{control}` is to be refused by [{clause}] with no run stuck in it: {verdict:?}, {stuck:?}"
                    )),
                }
                continue;
            }
            if stuck_by_another
                .iter()
                .any(|(file, in_control, _, _, _)| file == name && *in_control == control)
            {
                match (stuck, verdict) {
                    (Some(_), None) => paired += 1,
                    (_, verdict) => failures.push(format!(
                        "{name}: `{control}` is to be stuck and accepted: {verdict:?}, {stuck:?}"
                    )),
                }
                continue;
            }
            if let Some((_, _, clause, _)) = asks_more
                .iter()
                .find(|(file, asked, _, _)| file == name && *asked == control)
            {
                assert!(stuck.is_none(), "{name}: {control}");
                match verdict {
                    Some(error) if error.clause == *clause => asked_more += 1,
                    Some(error) => {
                        failures.push(format!("{name}: [{clause}] is expected, and {error}"))
                    }
                    None => failures.push(format!("{name}: `{control}` is accepted")),
                }
                continue;
            }
            match (stuck, verdict) {
                (Some(states), None) => failures.push(format!(
                    "{name}: `{control}` is accepted, and a run of it is stuck ({})",
                    states.iter().cloned().collect::<Vec<_>>().join(", ")
                )),
                (None, Some(error)) => {
                    failures.push(format!("{name}: `{control}`: no run is stuck, and {error}"))
                }
                (Some(states), Some(error)) => {
                    if states.iter().any(|state| excludes(error.clause, state)) {
                        rejected += 1;
                    } else {
                        failures.push(format!(
                            "{name}: `{control}` is stuck ({}), and refused by another clause: {error}",
                            states.iter().cloned().collect::<Vec<_>>().join(", ")
                        ));
                    }
                }
                (None, None) => accepted += 1,
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    assert_eq!(asked_more, asks_more.len());
    assert_eq!(paired, 2 * stuck_by_another.len());
    (rejected, accepted)
}

#[test]
fn the_rule_files_of_the_tasks_are_rejected_exactly_where_a_run_is_stuck() {
    let counts = held_against_the_oracle(&RULE_FILES, &ASKS_MORE, &STUCK_BY_ANOTHER);
    assert_eq!(counts, (18, 132));
}

// [TK4]: what a task holds where it can be stopped. A member given a lock by
// value is stopped before its first turn when the owner faults
// (`SPAWN_LOCK`; with a lease, `SPAWN_LEASE`, the lease is released); a lock
// given by value to an awaited control is held there while a member's fault
// stops it (`AWAIT_LOCK`); a member that is done with a lock as its payload
// is stopped when its sibling faults (`PAYLOAD_LOCK`); a lock in the care of
// a boundary around an `await` (`CARE_LOCK`). The rule files have the same
// programs with leases, accepted: `owner_awaits_waiter`, `stops_done` and
// `stops_guarded`.

const SPAWN_LOCK: &str = r#"
extern resource lock
extern control open_lock(id : u32) ■ { ok {k : lock} } uses io.res
extern control close_lock(k : lock) ■ { ok {} } uses io.res

async control holder(k : lock) ■ { ok {} } uses io.res
    1 ⊤ ▷ c : Δ close_lock(k) ▸ ok {}
    2 ⊤ ▷ ■ ok {}

async control spawns_holder() ■ { ok {} } faults uses io.res
    1 ⊤ ▷ ~pool : tasks⟨holder⟩ := tasks⟨holder⟩()
    2 ⊤ ▷ o : Δ open_lock(1) ▸ ok {k}
    3 o.ok ▷ spawn holder(k) into pool
    4 ⊤ ▷ fault "owner"

control runs_spawns_holder() ■ { ok {} } faults uses io.res
    1 ⊤ ▷ d : Δ run spawns_holder() ▸ ok {}
    2 d.ok ▷ ■ ok {}

//! run runs_spawns_holder() with [open_lock -> ok {lock#1}] => stuck X8 E-Stop
"#;

const SPAWN_LEASE: &str = r#"
extern resource lock on fault release
extern control open_lock(id : u32) ■ { ok {k : lock} } uses io.res
extern control close_lock(k : lock) ■ { ok {} } uses io.res

async control holder(k : lock) ■ { ok {} } uses io.res
    1 ⊤ ▷ c : Δ close_lock(k) ▸ ok {}
    2 ⊤ ▷ ■ ok {}

async control spawns_holder() ■ { ok {} } faults uses io.res
    1 ⊤ ▷ ~pool : tasks⟨holder⟩ := tasks⟨holder⟩()
    2 ⊤ ▷ o : Δ open_lock(1) ▸ ok {k}
    3 o.ok ▷ spawn holder(k) into pool
    4 ⊤ ▷ fault "owner"

control runs_spawns_holder() ■ { ok {} } faults uses io.res
    1 ⊤ ▷ d : Δ run spawns_holder() ▸ ok {}
    2 d.ok ▷ ■ ok {}

//! run runs_spawns_holder() with [open_lock -> ok {lock#1}] => faulted "owner" trace [open_lock(1) -> ok {lock#1}; lock.release(lock#1) -> released]
"#;

const AWAIT_LOCK: &str = r#"
extern resource lock
extern control open_lock(id : u32) ■ { ok {k : lock} } uses io.res
extern control close_lock(k : lock) ■ { ok {} } uses io.res

async control early() ■ { ok {} } faults
    1 ⊤ ▷ fault "early"

async control holds(k : lock) ■ { ok {} } uses io.res
    1 ⊤ ▷ c : Δ close_lock(k) ▸ ok {}
    2 ⊤ ▷ ■ ok {}

async control awaits_holds() ■ { ok {} } faults uses io.res
    1 ⊤ ▷ ~pool : tasks⟨early⟩ := tasks⟨early⟩()
    2 ⊤ ▷ spawn early() into pool
    3 ⊤ ▷ o : Δ open_lock(1) ▸ ok {k}
    4 o.ok ▷ a : Δ await holds(k) ▸ ok {}
    5 ⊤ ▷ lp : ↻ drain() {
          1 ⊤ ▷ n : Δ await next(pool) ▸ ok {} │ empty {}
          2 n.ok ▷ ↑ drain()
          3 n.empty ▷ □ drained {}
        } ▸ drained {}
    6 ⊤ ▷ ■ ok {}

control runs_awaits_holds() ■ { ok {} } faults uses io.res
    1 ⊤ ▷ d : Δ run awaits_holds() ▸ ok {}
    2 d.ok ▷ ■ ok {}

//! run runs_awaits_holds() with [open_lock -> ok {lock#1}] turns [1] => stuck X8 E-Stop
"#;

const PAYLOAD_LOCK: &str = r#"
extern resource lock
extern control open_lock(id : u32) ■ { ok {k : lock} } uses io.res
extern control close_lock(k : lock) ■ { ok {} } uses io.res

async control quick(id : u32) ■ { held {k : lock} } faults uses io.res
    1 ⊤ ▷ t : ? id = 0
    2 t.true ▷ fault "early"
    3 t.false ▷ o : Δ open_lock(id) ▸ ok {k}
    4 o.ok ▷ ■ held {k}

async control stops_done() ■ { ok {} } faults uses io.res
    1 ⊤ ▷ ~pool : tasks⟨quick⟩ := tasks⟨quick⟩()
    2 ⊤ ▷ spawn quick(1) into pool
    3 ⊤ ▷ spawn quick(0) into pool
    4 ⊤ ▷ lp : ↻ drain() {
          1 ⊤ ▷ n : Δ await next(pool) ▸ held {k} │ empty {}
          2 n.held ▷ c : Δ close_lock(k) ▸ ok {}
          3 n.held ▷ ↑ drain()
          4 n.empty ▷ □ drained {}
        } ▸ drained {}
    5 ⊤ ▷ ■ ok {}

control runs_stops_done() ■ { ok {} } faults uses io.res
    1 ⊤ ▷ d : Δ run stops_done() ▸ ok {}
    2 d.ok ▷ ■ ok {}

//! run runs_stops_done() with [open_lock -> ok {lock#1}] turns [0, 1] => stuck X8 E-Stop
"#;

const CARE_LOCK: &str = r#"
extern resource lock
extern control open_lock(id : u32) ■ { ok {k : lock} } uses io.res
extern async control tick(id : u32) ■ { done {} │ cancelled {} } uses io.net
contingent extern control drop_lock(k : lock) ■ { ok {} } uses io.res

async control guarded(id : u32) ■ { ok {} } faults uses io.res, io.net
    1 ⊤ ▷ t : ? id = 0
    2 t.true ▷ fault "early"
    3 t.false ▷ o : Δ open_lock(id) ▸ ok {k}
    4 o.ok ▷ b : boundary {
          1 ⊤ ▷ w : Δ await tick(id) ▸ done {} │ cancelled {}
          2 ⊤ ▷ fault "inner"
      } contingency [k] (m : string) {
          1 ⊤ ▷ c : Δ drop_lock(▾k) ▸ ok {}
          2 ⊤ ▷ escalate
      }
    5 ⊤ ▷ ■ ok {}

async control stops_guarded() ■ { ok {} } faults uses io.res, io.net
    1 ⊤ ▷ ~pool : tasks⟨guarded⟩ := tasks⟨guarded⟩()
    2 ⊤ ▷ spawn guarded(4) into pool
    3 ⊤ ▷ spawn guarded(0) into pool
    4 ⊤ ▷ lp : ↻ drain() {
          1 ⊤ ▷ n : Δ await next(pool) ▸ ok {} │ empty {}
          2 n.ok ▷ ↑ drain()
          3 n.empty ▷ □ drained {}
        } ▸ drained {}
    5 ⊤ ▷ ■ ok {}

control runs_stops_guarded() ■ { ok {} } faults uses io.res, io.net
    1 ⊤ ▷ d : Δ run stops_guarded() ▸ ok {}
    2 d.ok ▷ ■ ok {}

//! run runs_stops_guarded() with [open_lock -> ok {lock#4}] => stuck X8 E-Stop
"#;

const EXTERN_PAYLOAD: &str = r#"
extern resource lock
extern control close_lock(k : lock) ■ { ok {} } uses io.res
extern async control fetch(id : u32) ■ { got {k : lock} } uses io.net

async control awaits_fetch() ■ { ok {} } uses io.res, io.net
    1 ⊤ ▷ f : Δ await fetch(1) ▸ got {k}
    2 f.got ▷ c : Δ close_lock(k) ▸ ok {}
    3 f.got ▷ ■ ok {}

control runs_awaits_fetch() ■ { ok {} } uses io.res, io.net
    1 ⊤ ▷ d : Δ run awaits_fetch() ▸ ok {}
    2 d.ok ▷ ■ ok {}

control runs_fetch() ■ { got {k : lock} } uses io.net
    1 ⊤ ▷ d : Δ run fetch(2) ▸ got {k}
    2 d.got ▷ ■ got {k}

//! run runs_awaits_fetch() with [fetch -> got {lock#1}; close_lock -> ok] => done ok trace [fetch(1) -> got {lock#1}; close_lock(lock#1) -> ok]
//! run runs_fetch() with [fetch -> got {lock#2}] => done got {lock#2} trace [fetch(2) -> got {lock#2}]
"#;

const SET_AT_BOUNDARY: &str = r#"
extern async control tick(id : u32) ■ { done {} │ cancelled {} } uses io.net

async control early() ■ { ok {} } faults
    1 ⊤ ▷ fault "early"

async control set_at_boundary() ■ { ok {} │ caught {} } faults uses io.net
    1 ⊤ ▷ ~pool : tasks⟨early⟩ := tasks⟨early⟩()
    2 ⊤ ▷ spawn early() into pool
    3 ⊤ ▷ b : boundary {
          1 ⊤ ▷ w : Δ await tick(0) ▸ done {} │ cancelled {}
      } contingency (m : string) {
          1 ⊤ ▷ fault "caught"
      }
    4 b.done ▷ lp : ↻ drain() {
          1 ⊤ ▷ n : Δ await next(pool) ▸ ok {} │ empty {}
          2 n.ok ▷ ↑ drain()
          3 n.empty ▷ □ drained {}
        } ▸ drained {}
    5 b.done ▷ ■ ok {}

control runs_set_at_boundary() ■ { ok {} │ caught {} } faults uses io.net
    1 ⊤ ▷ d : Δ run set_at_boundary() ▸ ok {} │ caught {}
    2 d.ok ▷ ■ ok {}
    3 d.caught ▷ ■ caught {}

//! run runs_set_at_boundary() => faulted "caught"
"#;

const COUNTS: &str = r#"
async control nine(v : u32) ⊢ v ≤ 9 ■ { ok {w : u32} ⇐ w ≤ 9 }
    1 ⊤ ▷ ■ ok {v}

async control counts() ■ { ok {w : u32} }
    1 ⊤ ▷ ~pool : tasks⟨nine⟩ := tasks⟨nine⟩()
    2 ⊤ ▷ ⊢ count(pool) = 0
    3 ⊤ ▷ spawn nine(9) into pool
    4 ⊤ ▷ spawn nine(4) into pool
    5 ⊤ ▷ ⊢ count(pool) = 2
    6 ⊤ ▷ n : Δ await next(pool) ▸ ok {w} │ empty {}
    7 n.empty ▷ ⊥
    8 n.ok ▷ ⊢ count(pool) = 1 ∧ w ≤ 9
    9 n.ok ▷ cancel pool
    10 n.ok ▷ ⊢ count(pool) = 1
    11 n.ok ▷ lp : ↻ drain() {
          1 ⊤ ▷ x : Δ await next(pool) ▸ ok {u} │ empty {}
          2 x.ok ▷ ↑ drain()
          3 x.empty ▷ □ drained {}
        } ▸ drained {}
    12 n.ok ▷ ■ ok {w}

control runs_counts() ■ { ok {w : u32} }
    1 ⊤ ▷ d : Δ run counts() ▸ ok {w}
    2 d.ok ▷ ■ ok {w}

//! run runs_counts() => done ok {9}
//! run runs_counts() turns [1] => done ok {4}
"#;

const COUNT_WRONG: &str = r#"
async control nine(v : u32) ⊢ v ≤ 9 ■ { ok {w : u32} ⇐ w ≤ 9 }
    1 ⊤ ▷ ■ ok {v}

async control counts() ■ { ok {} }
    1 ⊤ ▷ ~pool : tasks⟨nine⟩ := tasks⟨nine⟩()
    2 ⊤ ▷ spawn nine(9) into pool
    3 ⊤ ▷ spawn nine(4) into pool
    4 ⊤ ▷ ⊢ count(pool) = 1
    5 ⊤ ▷ lp : ↻ drain() {
          1 ⊤ ▷ x : Δ await next(pool) ▸ ok {u} │ empty {}
          2 x.ok ▷ ↑ drain()
          3 x.empty ▷ □ drained {}
        } ▸ drained {}
    6 ⊤ ▷ ■ ok {}

control runs_counts() ■ { ok {} }
    1 ⊤ ▷ d : Δ run counts() ▸ ok {}
    2 d.ok ▷ ■ ok {}

//! run runs_counts() => stuck X7 E-Oblige
"#;

const PAYLOAD_WRONG: &str = r#"
async control nine(v : u32) ⊢ v ≤ 9 ■ { ok {w : u32} ⇐ w ≤ 9 }
    1 ⊤ ▷ ■ ok {v}

async control counts() ■ { ok {} }
    1 ⊤ ▷ ~pool : tasks⟨nine⟩ := tasks⟨nine⟩()
    2 ⊤ ▷ spawn nine(9) into pool
    3 ⊤ ▷ lp : ↻ drain() {
          1 ⊤ ▷ x : Δ await next(pool) ▸ ok {u} │ empty {}
          2 x.ok ▷ ⊢ u ≤ 8
          3 x.ok ▷ ↑ drain()
          4 x.empty ▷ □ drained {}
        } ▸ drained {}
    4 ⊤ ▷ ■ ok {}

control runs_counts() ■ { ok {} }
    1 ⊤ ▷ d : Δ run counts() ▸ ok {}
    2 d.ok ▷ ■ ok {}

//! run runs_counts() => stuck X7 E-Oblige
"#;

const LOOP_RENAMES: &str = r#"
async control nine(v : u32) ⊢ v ≤ 9 ■ { ok {w : u32} ⇐ w ≤ 9 }
    1 ⊤ ▷ ■ ok {v}

async control counts() ■ { ok {} }
    1 ⊤ ▷ ~pool : tasks⟨nine⟩ := tasks⟨nine⟩()
    2 ⊤ ▷ spawn nine(9) into pool
    3 ⊤ ▷ spawn nine(4) into pool
    4 ⊤ ▷ lp : ↻ drain() {
          1 ⊤ ▷ ⊢ count(pool) = 2
          2 ⊤ ▷ x : Δ await next(pool) ▸ ok {u} │ empty {}
          3 x.ok ▷ ↑ drain()
          4 x.empty ▷ □ drained {}
        } ▸ drained {}
    5 ⊤ ▷ ■ ok {}

control runs_counts() ■ { ok {} }
    1 ⊤ ▷ d : Δ run counts() ▸ ok {}
    2 d.ok ▷ ■ ok {}

//! run runs_counts() => stuck X7 E-Oblige
"#;

const SPAWN_IN_LOOP: &str = r#"
async control nine(v : u32) ⊢ v ≤ 9 ■ { ok {w : u32} ⇐ w ≤ 9 }
    1 ⊤ ▷ ■ ok {v}

async control counts() ■ { ok {} }
    1 ⊤ ▷ ~pool : tasks⟨nine⟩ := tasks⟨nine⟩()
    2 ⊤ ▷ lp : ↻ fill(i : u32 := 0) {
          1 ⊤ ▷ ⊢ count(pool) = 0
          2 ⊤ ▷ t : ? i < 2
          3 t.true ▷ spawn nine(i) into pool
          4 t.true ▷ ↑ fill(i + 1)
          5 t.false ▷ □ filled {}
        } ▸ filled {}
    3 ⊤ ▷ lq : ↻ drain() {
          1 ⊤ ▷ x : Δ await next(pool) ▸ ok {u} │ empty {}
          2 x.ok ▷ ↑ drain()
          3 x.empty ▷ □ drained {}
        } ▸ drained {}
    4 ⊤ ▷ ■ ok {}

control runs_counts() ■ { ok {} }
    1 ⊤ ▷ d : Δ run counts() ▸ ok {}
    2 d.ok ▷ ■ ok {}

//! run runs_counts() => stuck X7 E-Oblige
"#;

const SPAWN_READS_LENT: &str = r#"
async control member(n : u32) ■ { ok {} }
    1 ⊤ ▷ ■ ok {}

async control reads_lent() ■ { ok {v : u32} }
    1 ⊤ ▷ ~v : u32 := 1
    2 ⊤ ▷ r : &~u32 := &~v
    3 ⊤ ▷ ~pool : tasks⟨member⟩ := tasks⟨member⟩()
    4 ⊤ ▷ spawn member(v) into pool
    5 ⊤ ▷ r ← 2
    6 ⊤ ▷ lp : ↻ drain() {
          1 ⊤ ▷ n : Δ await next(pool) ▸ ok {} │ empty {}
          2 n.ok ▷ ↑ drain()
          3 n.empty ▷ □ drained {}
        } ▸ drained {}
    7 ⊤ ▷ ■ ok {v}

control runs_reads_lent() ■ { ok {v : u32} }
    1 ⊤ ▷ d : Δ run reads_lent() ▸ ok {v}
    2 d.ok ▷ ■ ok {v}

//! run runs_reads_lent() => stuck X4 B1
"#;

const SPAWN_READS_OTHER: &str = r#"
async control member(n : u32) ■ { ok {} }
    1 ⊤ ▷ ■ ok {}

async control reads_lent() ■ { ok {v : u32} }
    1 ⊤ ▷ ~v : u32 := 1
    2 ⊤ ▷ r : &~u32 := &~v
    3 ⊤ ▷ ~pool : tasks⟨member⟩ := tasks⟨member⟩()
    4 ⊤ ▷ spawn member(3) into pool
    5 ⊤ ▷ r ← 2
    6 ⊤ ▷ lp : ↻ drain() {
          1 ⊤ ▷ n : Δ await next(pool) ▸ ok {} │ empty {}
          2 n.ok ▷ ↑ drain()
          3 n.empty ▷ □ drained {}
        } ▸ drained {}
    7 ⊤ ▷ ■ ok {v}

control runs_reads_lent() ■ { ok {v : u32} }
    1 ⊤ ▷ d : Δ run reads_lent() ▸ ok {v}
    2 d.ok ▷ ■ ok {v}

//! run runs_reads_lent() => done ok {2}
"#;

const RUN_EFFECT: &str = r#"
extern async control tick(id : u32) ■ { done {} │ cancelled {} } uses io.net

control runs_tick() ■ { ok {} }
    1 ⊤ ▷ d : Δ run tick(0) ▸ done {} │ cancelled {}
    2 ⊤ ▷ ■ ok {}

//! run runs_tick() with [tick -> done] => stuck X9 E-Effect
"#;

const RUN_EFFECT_ALLOWED: &str = r#"
extern async control tick(id : u32) ■ { done {} │ cancelled {} } uses io.net

control runs_tick() ■ { ok {} } uses io.net
    1 ⊤ ▷ d : Δ run tick(0) ▸ done {} │ cancelled {}
    2 ⊤ ▷ ■ ok {}

//! run runs_tick() with [tick -> done] => done ok trace [tick(0) -> done]
"#;

#[test]
fn what_a_task_holds_where_it_can_be_stopped_is_fault_releasable_tk4() {
    stuck_and_rejected("TK4", SPAWN_LOCK);
    done_and_accepted("TK4", SPAWN_LEASE);
    stuck_and_rejected("TK4", AWAIT_LOCK);
    stuck_and_rejected("TK4", PAYLOAD_LOCK);
    stuck_and_rejected("TK4", CARE_LOCK);
}

/// [TK4] asks a fault-releasable type of the payload of an `extern async
/// control` that a task awaits, and the checker refuses `awaits_fetch`
/// although no run of it is stuck: a completion of the host leaves one task
/// ready, which takes the next turn, so the instrumented host reaches no
/// state in which that task is stopped before it runs. A run of the same
/// operation gives the payload to a control that is not async, which is
/// never stopped, and is accepted.
#[test]
fn the_payload_of_an_awaited_extern_control_is_fault_releasable_tk4() {
    let report = villanelle_v2::script::check(EXTERN_PAYLOAD);
    assert!(report.failures.is_empty() && report.stuck.is_empty() && report.runs == 2);
    let program = load(EXTERN_PAYLOAD).unwrap();
    let verdicts = check::check_each(&program).unwrap();
    let clauses: Vec<(String, Option<&str>)> = verdicts
        .iter()
        .map(|(control, verdict)| (control.clone(), verdict.as_ref().map(|e| e.clause)))
        .collect();
    assert_eq!(
        clauses,
        [
            ("awaits_fetch".to_string(), Some("TK4")),
            ("runs_awaits_fetch".to_string(), None),
            ("runs_fetch".to_string(), None),
        ]
    );
}

/// [TK5]: no task set is available at a lexical boundary statement, so the
/// fault of a member reaches the boundary around its set and none inside it.
/// The oracle delivers it to the owner where it waits, in the work of the
/// boundary, and the contingency runs: nothing is stuck, and the checker
/// refuses the program.
#[test]
fn no_task_set_is_available_at_a_boundary_tk5() {
    done_and_rejected("TK5", SET_AT_BOUNDARY);
}

/// [TK6]: `count(x)` is 0 for a new set, one more after a spawn and one less
/// after an alternative of the producer, and the set has no members on
/// `empty`; the payload satisfies the condition of its alternative
/// (`COUNTS`). A false statement about the count or the payload is refused
/// where a run finds it false, and so is a fact from before a loop in which
/// `await next` or `spawn` renames the set ([I9]).
#[test]
fn count_is_a_measure_that_spawn_and_await_next_change_tk6() {
    done_and_accepted("TK6", COUNTS);
    stuck_and_rejected("P1", COUNT_WRONG);
    stuck_and_rejected("P1", PAYLOAD_WRONG);
    stuck_and_rejected("P1", LOOP_RENAMES);
    stuck_and_rejected("P1", SPAWN_IN_LOOP);
}

/// The operands of a spawn are read as those of a call ([O0], [L3]): a spawn
/// that reads a place lent exclusively to a borrow that is used afterwards
/// is refused.
#[test]
fn the_operands_of_a_spawn_are_read_as_those_of_a_call_l3() {
    stuck_and_rejected("L3", SPAWN_READS_LENT);
    done_and_accepted("L3", SPAWN_READS_OTHER);
}

/// [TK7]: `run f` counts the effects of `f` toward the control that contains
/// it ([F3]); the rule files hold `spawn` (`bad_effect_parent`) and `await`
/// (`awaits_secret`).
#[test]
fn a_run_counts_the_effects_of_what_it_runs_tk7() {
    stuck_and_rejected("F3", RUN_EFFECT);
    done_and_accepted("F3", RUN_EFFECT_ALLOWED);
}
