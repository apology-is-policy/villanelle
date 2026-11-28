//! Native defined roots, awaits, and scheduling of task-set members.
use std::{collections::VecDeque, fs, process::Command};
use villanelle_v2::codegen::{
    NativeRunSpec, emit_c_header, emit_llvm, emit_native_harness_llvm, run_native_counted,
    run_native_ir,
};
use villanelle_v2::differential::{Verdict, compare};
use villanelle_v2::host::{Answer, Host, Scheduled, Script};
use villanelle_v2::int::Int;
use villanelle_v2::oracle::{self, Config, Value};
use villanelle_v2::typed::{Control, Program};
use villanelle_v2::{check, erased, load, script};

const SET_CANCEL: &str = include_str!("slice4/checked_set_cancel.core");
const MEMBER_CANCEL: &str = include_str!("slice4/checked_member_cancel.core");
const OWNER_CANCEL: &str = include_str!("slice4/checked_owner_cancel.core");
const CANCEL_RUN: &str = include_str!("slice4/checked_cancel_run.core");
const ROOT_CANCEL: &str = include_str!("slice4/checked_root_cancel.core");
const WAITING_CHOICES: &str = include_str!("slice4/checked_waiting_choices.core");
const MEMBER_HOST_WAIT: &str = include_str!("slice4/checked_member_host_wait.core");
const OWNER_HOST_WAIT: &str = include_str!("slice4/checked_owner_host_wait.core");
const HOST_RUN: &str = include_str!("slice4/checked_host_run.core");
const HOST_WAIT: &str = include_str!("slice4/checked_host_wait.core");
const NESTED_MEMBER_SET: &str = include_str!("slice4/checked_nested_member_set.core");
const MEMBER_SET: &str = include_str!("slice4/checked_member_set.core");
const AWAITED_SET: &str = include_str!("slice4/checked_awaited_set.core");
const MULTIPLE_SETS: &str = include_str!("slice4/checked_multiple_sets.core");
const REPEATED_SPAWN: &str = include_str!("slice4/checked_repeated_spawn.core");
const ROOTS: &str = include_str!("slice4/checked_run.core");
const AWAITS: &str = include_str!("slice4/checked_await.core");
const NESTED_MEMBER: &str = include_str!("slice4/checked_nested_member_await.core");
const NESTED_OWNER: &str = include_str!("slice4/checked_nested_owner_await.core");
const MEMBER_AWAIT: &str = include_str!("slice4/checked_member_await.core");

fn scheduled_host(spec: &NativeRunSpec) -> Scheduled<Script> {
    let mut host = Scheduled::new(Script {
        answers: spec.answers.iter().cloned().collect(),
    });
    host.turns = spec.turns.iter().copied().collect();
    host.waiting = spec.waiting.iter().copied().collect();
    host.cancel_at_turn = spec.cancel_at_turn;
    host
}

fn compare_native_runs(source: &str, rules: &[&str], counts: &[u64], allocations: u64) {
    let (program, runs) = script::native_runs(source).unwrap();
    check::check(&program).unwrap().revalidate().unwrap();
    let report = script::check(source);
    assert!(report.failures.is_empty(), "{:?}", report.failures);
    assert_eq!(
        (report.runs, report.compared, runs.len()),
        (counts.len(), counts.len(), counts.len())
    );
    for bits in [32, 64] {
        let mut expected = Vec::new();
        for (spec, &count) in runs.iter().zip(counts) {
            let mut host = scheduled_host(spec);
            let comparison = compare(
                &program,
                &spec.entry,
                spec.arguments.clone(),
                &mut host,
                &Config::with_usize_bits(bits),
            );
            assert_eq!(comparison.verdict, Verdict::Same, "{}", spec.entry);
            for &rule in rules {
                assert_eq!(
                    comparison.oracle.rules.get(rule).copied().unwrap_or(0),
                    count,
                    "{} [{rule}]",
                    spec.entry
                );
            }
            let erased = comparison.erased.unwrap();
            expected.push((erased.end.to_string(), erased.trace));
        }
        for optimization in [0, 2] {
            let batch = run_native_counted(&program, &runs, bits, optimization).unwrap();
            let observations: Vec<_> = batch
                .runs
                .into_iter()
                .map(|(end, trace)| (end.to_string(), trace))
                .collect();
            assert_eq!(observations, expected, "usize={bits} -O{optimization}");
            assert_eq!(
                batch.allocations, allocations,
                "usize={bits} -O{optimization}"
            );
        }
    }
}

#[test]
fn defined_roots_return_or_unwind_in_the_callers_decision() {
    // Four nonempty input vectors. Their payloads move to the eventual owner.
    compare_native_runs(ROOTS, &["E-Run"], &[1, 1, 1, 2, 1, 1], 4);
}

#[test]
fn direct_host_runs_return_the_selected_payload_to_the_caller() {
    // Two vectors in swap. Each host request itself is in the caller's frame.
    compare_native_runs(HOST_RUN, &["E-Run"], &[2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2], 2);
    let (source, _) = HOST_RUN.split_once("async control tag(").unwrap();
    let program = load(source).unwrap();
    for bits in [32, 64] {
        let header = emit_c_header(&program, bits);
        assert!(header.contains("uint64_t vn2_pick_waiting("));
        assert!(!header.contains("vn2_pick_turn"));
        assert!(
            !emit_llvm(&program, bits)
                .unwrap()
                .contains("@vn2_pick_turn")
        );
    }
}

#[test]
fn member_cancel_resumes_the_bound_activation_on_a_ready_turn() {
    // Fourteen owned vectors, three two-request host offers and a nested activation.
    compare_native_runs(
        MEMBER_CANCEL,
        &["E-Spawn"],
        &[2, 2, 2, 2, 1, 1, 1, 1, 2],
        18,
    );
}

#[test]
fn set_cancel_matches_current_members_and_their_descendants() {
    // Waiting handles need one dynamic list in each split run, plus a second
    // list when one child finishes before the root request completes.
    // A spawned owner also offers its own wait alongside its three children.
    compare_native_runs(SET_CANCEL, &["E-Cancel"], &[2; 6], 5);
}

#[test]
fn set_cancel_replays_the_checked_rule_file() {
    compare_native_runs(
        include_str!("slice4/e_cancel.core"),
        &["E-Cancel"],
        &[1, 1, 1, 0, 0],
        1,
    );
}

#[test]
fn set_cancel_runs_the_rails_lease_example() {
    let rails = include_str!("slice4_surface/tasks_and_cancel.rails");
    let (decls, _) = rails.split_once("async control voice(").unwrap();
    let (_, tail) = rails.split_once("async control leased_worker(").unwrap();
    let (example, _) = tail.split_once("async control failing_member(").unwrap();
    let source = format!("{decls}async control leased_worker({example}");
    let directive = source
        .lines()
        .find(|line| line.starts_with("//! run"))
        .unwrap();
    let core = villanelle_v2::surface::elaborate(&source).unwrap().print();
    compare_native_runs(&format!("{core}\n{directive}"), &["E-Cancel"], &[1], 1);
}

#[test]
fn set_cancel_c_host_checks_selective_withdrawal_in_the_owners_turn() {
    let (split, _) = SET_CANCEL
        .split_once("extern async control probe(")
        .unwrap();
    compare_cancellation_host(split, "set_cancel", include_str!("host_set_cancel.c"));
}

#[test]
fn member_cancel_c_host_checks_bound_handles_and_ready_choices() {
    compare_cancellation_host(
        MEMBER_CANCEL,
        "member_cancel",
        include_str!("host_member_cancel.c"),
    );
}

fn compare_cancellation_host(source: &str, name: &str, driver: &str) {
    let (_, runs) = script::native_runs(source).unwrap();
    compare_c_host(source, name, driver, |program, config| {
        let mut expected = Vec::new();
        for spec in &runs {
            let result = compare(
                program,
                &spec.entry,
                spec.arguments.clone(),
                &mut scheduled_host(spec),
                config,
            );
            assert_eq!(result.verdict, Verdict::Same);
            assert!(matches!(result.oracle.end, oracle::End::Done { .. }));
            expected.extend(result.oracle.trace.iter().map(ToString::to_string));
            expected.push(result.oracle.end.to_string());
        }
        expected
    });
}

#[test]
fn owner_cancel_with_ready_and_waiting_members_matches_both_interpreters() {
    // One vector per invocation and a two-request waiting list in the two
    // schedules where the host chooses between hold and ping.
    compare_native_runs(OWNER_CANCEL, &["E-Spawn"], &[1; 9], 11);
}

#[test]
fn owner_cancel_replays_the_checked_host_await_rule_examples() {
    // The rest of the rule file intentionally violates a precondition and an effect allowance.
    let (checked, _) = include_str!("slice4/e_await_host.core")
        .split_once("// The precondition and the allowance")
        .unwrap();
    compare_native_runs(checked, &["E-Run"], &[1; 6], 0);
}

#[test]
fn owner_cancel_c_host_checks_withdrawal_before_the_ready_choice() {
    const DRIVER: &str = r#"
#include "module.h"
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static struct vn2_wait_hold *hold;
static struct vn2_wait_ping *ping;
static int hold_token, ping_token;
static void *selected;
static unsigned scenario, ready_picks;
static const char *expected;

static void observe(const char *event) {
    size_t n = strlen(event);
    if (strncmp(expected, event, n) || expected[n] != ' ') {
        fprintf(stderr, "scenario %u: saw %s, expected %s\n", scenario, event, expected);
        exit(1);
    }
    expected += n + 1;
}
uint8_t vn2_should_cancel_root(uint64_t turn) {
    const unsigned at[] = {1, 1, 1, 2, 3, 3, 0, 2, 0};
    char event[32];
    snprintf(event, sizeof event, "poll%" PRIu64, turn);
    observe(event);
    return at[scenario] && turn >= at[scenario];
}
uint64_t vn2_pick_turn(uint64_t count) {
    if (count != 1 && count != 2) abort();
    observe(count == 2 ? "ready2" : "ready1");
    ++ready_picks;
    return ((scenario == 0 || scenario == 7) && ready_picks == 2) || (scenario == 2 && ready_picks == 1);
}
uint64_t vn2_pick_waiting(void *const *states, uint64_t n) {
    if (selected || !n || n != (uint64_t)((hold != NULL) + (ping != NULL))) abort();
    if (hold && states[0] != &hold_token) abort();
    if (ping && states[n-1] != &ping_token) abort();
    observe(n == 2 ? "both" : (hold ? "only_hold" : "only_ping"));
    uint64_t i = n == 2 && scenario == 4;
    selected = states[i];
    return i;
}
int32_t vn2_ext_acquire(void **out) {
    observe("acquire");
    *out = (void *)(uintptr_t)3;
    puts("acquire() -> ok {lease#3}");
    return VN2_ACQUIRE_OK;
}
int32_t vn2_ext_mark(uint32_t n) {
    observe("mark");
    printf("mark(%u) -> ok {}\n", (unsigned)n);
    return VN2_MARK_OK;
}
static void check_args(struct vn2_wait_hold *r) {
    if ((uintptr_t)r->in_l != 3 || r->in_xs->len != 2 || *r->in_cell != 7) abort();
    const uint32_t *xs = r->in_xs->data;
    if (xs[0] != 4 || xs[1] != 8) abort();
}
void vn2_start_hold(struct vn2_wait_hold *r) {
    observe("start");
    if (hold || r->host_state) abort();
    check_args(r);
    hold = r;
    r->host_state = &hold_token;
}
void vn2_withdraw_hold(struct vn2_wait_hold *r) {
    observe("withdraw");
    if (selected || r != hold || r->host_state != &hold_token) abort();
    check_args(r);
    hold = NULL;
}
void vn2_release_lease(void *l) {
    observe("release");
    if (hold || (uintptr_t)l != 3) abort();
    puts("lease.release(lease#3) -> released {}");
}
int32_t vn2_complete_hold(struct vn2_wait_hold *r) {
    observe("complete");
    if (r != hold || selected != &hold_token || r->host_state != selected) abort();
    check_args(r);
    hold = selected = NULL;
    free(r->in_xs->data);
    if (scenario == 6) {
        *r->in_cell = 13;
        puts("hold(lease#3, [4, 8], 7) -> cancelled {}");
        return VN2_HOLD_CANCELLED;
    }
    *r->in_cell = 9;
    *r->out_0_done_0 = 37;
    puts("hold(lease#3, [4, 8], 7) -> done {37}");
    return VN2_HOLD_DONE;
}
void vn2_start_ping(struct vn2_wait_ping *r) {
    observe("start_ping");
    if (ping || r->host_state) abort();
    ping = r;
    r->host_state = &ping_token;
}
int32_t vn2_complete_ping(struct vn2_wait_ping *r) {
    observe("complete_ping");
    if (r != ping || selected != &ping_token || r->host_state != selected) abort();
    ping = selected = NULL;
    puts("ping() -> ok {}");
    return VN2_PING_OK;
}
int main(void) {
    const char *cases[] = {
        "poll1 ready2 acquire release ready2 mark ready1 mark ready1 ready1 poll6 ready1 ",
        "acquire start poll1 withdraw release ready2 mark ready1 mark ready1 ready1 poll5 ready1 ",
        "acquire start poll1 withdraw release ready2 mark ready1 mark ready1 ready1 poll5 ready1 ",
        "acquire start poll1 ready1 mark start_ping poll2 withdraw release ready1 mark "
        "only_ping complete_ping ready1 ready1 ready1 poll7 ready1 ",
        "acquire start poll1 ready1 mark start_ping poll2 both complete_ping poll3 withdraw "
        "release ready2 mark ready1 ready1 ready1 poll7 ready1 ",
        "acquire start poll1 ready1 mark start_ping poll2 both complete poll3 ready1 mark "
        "only_ping complete_ping ready1 ready1 ready1 poll8 ready1 ",
        "acquire start poll1 ready1 mark poll2 only_hold complete poll3 ready1 mark "
        "poll4 ready1 poll5 ready1 poll6 ready1 ",
        "poll1 ready2 acquire start poll2 withdraw release ready2 mark ready1 mark ready1 ready1 ",
        "poll1 ready2 acquire start poll2 ready1 mark poll3 only_hold complete poll4 ready1 mark "
        "poll5 ready1 poll6 ready1 "
    };
    for (scenario = 0; scenario < sizeof cases / sizeof *cases; ++scenario) {
        expected = cases[scenario];
        ready_picks = 0;
        uint32_t *xs = malloc(2 * sizeof *xs);
        if (!xs) abort();
        xs[0] = 4;
        xs[1] = 8;
        vn2_vec input = {xs, 2, 2};
        uint32_t cell;
        if (scenario >= 7) {
            if (vn2_call_inherited(&input, &cell) != VN2_INHERITED_OK) return 1;
        } else if (vn2_call_example(&input, scenario == 0, scenario >= 3 && scenario <= 5,
                                    &cell) != VN2_EXAMPLE_OK) return 1;
        if (*expected || hold || ping || selected) return 1;
        printf("done ok {%u}\n", (unsigned)cell);
    }
    return 0;
}
"#;
    let (_, runs) = script::native_runs(OWNER_CANCEL).unwrap();
    compare_c_host(OWNER_CANCEL, "owner_cancel", DRIVER, |program, config| {
        let mut expected = Vec::new();
        for spec in &runs {
            let result = compare(
                program,
                &spec.entry,
                spec.arguments.clone(),
                &mut scheduled_host(spec),
                config,
            );
            assert_eq!(result.verdict, Verdict::Same);
            assert!(matches!(result.oracle.end, oracle::End::Done { .. }));
            expected.extend(result.oracle.trace.iter().map(ToString::to_string));
            expected.push(result.oracle.end.to_string());
        }
        expected
    });
}

#[test]
fn cancel_run_compiles_without_a_ready_task_callback() {
    let (source, _) = CANCEL_RUN.split_once("async control pause()").unwrap();
    compare_native_runs(source, &["E-Run"], &[1, 1, 1, 2, 2], 7);
    let program = load(source).unwrap();
    for bits in [32, 64] {
        assert!(!emit_c_header(&program, bits).contains("vn2_pick_turn"));
        assert!(
            !emit_llvm(&program, bits)
                .unwrap()
                .contains("@vn2_pick_turn")
        );
    }
}

#[test]
fn cancel_run_preserves_its_caller_and_coexists_with_await() {
    compare_native_runs(CANCEL_RUN, &["E-Run"], &[1, 1, 1, 2, 2, 2, 2, 2, 0], 14);
}

#[test]
fn cancel_run_c_host_checks_the_callers_turn_after_release_and_completion() {
    const DRIVER: &str = r#"
#include "module.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static struct vn2_wait_finish *pending;
static const char *expected;
static unsigned scenario, polls;
static void observe(const char *event) {
    size_t len = strlen(event);
    if (strncmp(expected, event, len) || expected[len] != ' ') {
        fprintf(stderr, "scenario %u: saw %s, expected %s\n", scenario, event, expected);
        exit(1);
    }
    expected += len + 1;
}
uint8_t vn2_should_cancel_root(uint64_t turn) {
    observe("poll");
    if (turn != ++polls) abort();
    return scenario < 2 && turn == 1;
}
uint64_t vn2_pick_turn(uint64_t n) {
    if (n != 1 && n != 2) abort();
    observe(n == 2 ? "ready2" : "ready1");
    return 0;
}
int32_t vn2_ext_acquire(uint32_t id, void **out) {
    observe("acquire");
    *out = (void *)(uintptr_t)id;
    printf("acquire(%u) -> ok {lease#%u}\n", (unsigned)id, (unsigned)id);
    return VN2_ACQUIRE_OK;
}
int32_t vn2_ext_mark(uint32_t value) {
    observe("mark");
    printf("mark(%u) -> ok {}\n", (unsigned)value);
    return VN2_MARK_OK;
}
static void check_bound(struct vn2_wait_finish *r) {
    uintptr_t id = (uintptr_t)r->in_l;
    const uint32_t *xs = r->in_xs->data;
    if ((id != 3 && id != 4) || r->in_xs->len != 2 || xs[0] != id + 1 ||
        xs[1] != id + 5 || *r->in_cell != 7) abort();
}
void vn2_start_finish(struct vn2_wait_finish *r) {
    observe("start");
    if (pending || r->host_state) abort();
    check_bound(r);
    r->host_state = pending = r;
}
uint64_t vn2_pick_waiting(void *const *states, uint64_t n) {
    observe("waiting");
    if (n != 1 || !pending || states[0] != pending) abort();
    return 0;
}
void vn2_withdraw_finish(struct vn2_wait_finish *r) {
    observe("withdraw");
    if (!pending || pending != r || r->host_state != r) abort();
    check_bound(r);
    pending = NULL;
}
void vn2_release_lease(void *handle) {
    observe("release");
    if (pending) abort();
    printf("lease.release(lease#%u) -> released {}\n", (unsigned)(uintptr_t)handle);
}
int32_t vn2_complete_finish(struct vn2_wait_finish *r) {
    observe("complete");
    if (!pending || pending != r || r->host_state != r) abort();
    check_bound(r);
    pending = NULL;
    unsigned id = (unsigned)(uintptr_t)r->in_l;
    const uint32_t *xs = r->in_xs->data;
    printf("finish(lease#%u, [%u, %u], %u) -> ", id, (unsigned)xs[0], (unsigned)xs[1],
           (unsigned)*r->in_cell);
    free(r->in_xs->data);
    if (scenario == 2 && id == 3) {
        *r->in_cell = 13;
        puts("cancelled {}");
        return VN2_FINISH_CANCELLED;
    }
    *r->in_cell = 9;
    *r->out_1_value_0 = 10 * id + 7;
    printf("value {%u}\n", (unsigned)*r->out_1_value_0);
    return VN2_FINISH_VALUE;
}
static vn2_vec data(uint32_t first) {
    uint32_t *xs = malloc(2 * sizeof *xs);
    if (!xs) abort();
    xs[0] = first;
    xs[1] = first + 4;
    return (vn2_vec){xs, 2, 2};
}
int main(void) {
    const char *cases[] = {
        "poll ready2 acquire release mark acquire release mark ready1 mark ready1 ready1 ",
        "acquire start poll withdraw release mark acquire start poll waiting complete mark "
        "poll ready1 mark poll ready1 poll ready1 ",
        "acquire start poll waiting complete mark acquire start poll waiting complete mark "
        "poll ready1 mark poll ready1 poll ready1 ",
        "acquire start poll waiting complete poll ready1 "
    };
    for (scenario = 0; scenario < 4; ++scenario) {
        expected = cases[scenario];
        polls = 0;
        vn2_vec a = data(4);
        uint32_t first, second;
        if (scenario == 3) {
            if (vn2_call_wait_once(&a, &first) != VN2_WAIT_ONCE_OK) return 1;
            printf("done ok {%u}\n", (unsigned)first);
        } else {
            vn2_vec b = data(5);
            if (vn2_call_outer(&a, &b, scenario == 0, &first, &second) != VN2_OUTER_OK) return 1;
            printf("done ok {%u, %u}\n", (unsigned)first, (unsigned)second);
        }
        if (pending || *expected) return 1;
    }
    return 0;
}
"#;
    let (_, runs) = script::native_runs(CANCEL_RUN).unwrap();
    let inherited = runs
        .iter()
        .find(|s| s.entry == "outer" && s.cancel_at_turn == Some(1))
        .unwrap();
    let completed = runs
        .iter()
        .find(|s| s.entry == "outer" && s.cancel_at_turn.is_none())
        .unwrap();
    let awaited = runs.iter().find(|s| s.entry == "wait_once").unwrap();
    let mut withdrawn = completed.clone();
    // Withdraw the first finish. A one-shot request lets the second finish complete.
    assert_eq!(withdrawn.answers.remove(1).0, "finish");
    compare_c_host(CANCEL_RUN, "cancel_run", DRIVER, |program, config| {
        let mut expected = Vec::new();
        for (spec, first_turn) in [
            (inherited, true),
            (&withdrawn, true),
            (completed, false),
            (awaited, false),
        ] {
            let mut host = scheduled_host(spec);
            host.cancel_at_turn = None;
            host.cancel_decisions.push_back(first_turn);
            let result = compare(
                program,
                &spec.entry,
                spec.arguments.clone(),
                &mut host,
                config,
            );
            assert_eq!(result.verdict, Verdict::Same);
            assert!(matches!(result.oracle.end, oracle::End::Done { .. }));
            expected.extend(result.oracle.trace.iter().map(ToString::to_string));
            expected.push(result.oracle.end.to_string());
        }
        expected
    });
}

fn single_root_cancel_source() -> &'static str {
    ROOT_CANCEL
        .split_once("extern async control ping()")
        .unwrap()
        .0
}

#[test]
fn root_cancel_counts_member_turns_before_a_nested_run() {
    compare_native_runs(
        ROOT_CANCEL,
        &["E-AwaitHost"],
        &[1, 2, 1, 1, 1, 1, 2, 3, 2],
        9,
    );
}

#[test]
fn root_cancel_before_issue_and_during_wait_release_the_arguments() {
    // Withdrawal counts E-AwaitHost once at issue and again at withdrawal.
    compare_native_runs(
        single_root_cancel_source(),
        &["E-AwaitHost"],
        &[1, 2, 1, 1, 1, 1],
        6,
    );
}

#[test]
fn root_cancel_c_host_observes_start_withdrawal_release_and_resumption() {
    const DRIVER: &str = r#"
#include "module.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static unsigned scenario, at, reentered;
static char calls[48];
static size_t count;
static struct vn2_wait_hold *pending;
static void record(char event) {
    if (count + 1 >= sizeof calls) abort();
    calls[count++] = event;
    calls[count] = 0;
}
uint8_t vn2_should_cancel_root(uint64_t turn) {
    if (!turn || turn > 9) abort();
    record((char)('0' + turn));
    return !reentered && turn == at;
}
uint64_t vn2_pick_turn(uint64_t n) {
    if (n != 1) abort();
    record('R');
    return 0;
}
int32_t vn2_ext_open_lease(uint32_t id, void **out) {
    if (id != 3 || pending) abort();
    record('O');
    // A fresh call from C starts at turn one, even inside a cancelled root.
    reentered = 1;
    if (vn2_call_checkpoint() != VN2_CHECKPOINT_OK) abort();
    reentered = 0;
    *out = (void *)(uintptr_t)id;
    puts("open_lease(3) -> ok {lease#3}");
    return VN2_OPEN_LEASE_OK;
}
static void check_inputs(struct vn2_wait_hold *r) {
    const uint32_t *data = r->in_xs->data;
    if ((uintptr_t)r->in_l != 3 || r->in_xs->len != 2 || data[0] != 4 ||
        data[1] != 8 || *r->in_cell != 7) abort();
}
void vn2_start_hold(struct vn2_wait_hold *r) {
    if (pending || r->host_state) abort();
    check_inputs(r);
    r->host_state = pending = r;
    record('S');
}
void vn2_withdraw_hold(struct vn2_wait_hold *r) {
    if (!pending || r != pending || r->host_state != pending) abort();
    check_inputs(r);
    pending = NULL;
    record('X');
}
void vn2_release_lease(void *handle) {
    if ((uintptr_t)handle != 3 || pending) abort();
    record('L');
    puts("lease.release(lease#3) -> released {}");
}
uint64_t vn2_pick_waiting(void *const *states, uint64_t n) {
    if (n != 1 || !pending || states[0] != pending) abort();
    record('W');
    return 0;
}
int32_t vn2_complete_hold(struct vn2_wait_hold *r) {
    if (!pending || r != pending || r->host_state != pending) abort();
    check_inputs(r);
    pending = NULL;
    record('C');
    free(r->in_xs->data);
    if (scenario == 3) {
        puts("hold(lease#3, [4, 8], 7) -> cancelled {}");
        return VN2_HOLD_CANCELLED;
    }
    puts("hold(lease#3, [4, 8], 7) -> done {37}");
    *r->out_0_done_0 = 37;
    *r->in_cell = 9;
    return VN2_HOLD_DONE;
}
int main(void) {
    const unsigned turns[] = {1, 2, 3, 0, 1, 1};
    const char *expected[] = {
        "1RO1RLR", "1RO1RS2XLR", "1RO1RS2WC3R", "1RO1RS2WC3R",
        "1RRO1RLR", "1R2R3RO1RS4WC5R"
    };
    for (scenario = 0; scenario < 6; ++scenario) {
        count = 0;
        at = turns[scenario];
        uint32_t *values = malloc(2 * sizeof *values);
        if (!values) abort();
        values[0] = 4;
        values[1] = 8;
        vn2_vec input = {values, 2, 2};
        uint32_t v = 0, cell = 0, stopped = 0;
        int32_t tag;
        if (scenario == 4) tag = vn2_call_inherit(&input, &v, &cell, &stopped);
        else if (scenario == 5) tag = vn2_call_after_inner(&input, &v, &cell, &stopped);
        else tag = vn2_call_example(&input, &v, &cell, &stopped);
        if (pending || strcmp(calls, expected[scenario])) {
            fprintf(stderr, "scenario %u: expected %s, got %s\n", scenario, expected[scenario], calls);
            return 1;
        }
        if (tag == VN2_EXAMPLE_OK) printf("done ok {%u, %u}\n", (unsigned)v, (unsigned)cell);
        else if (tag == VN2_EXAMPLE_STOPPED) printf("done stopped {%u}\n", (unsigned)stopped);
        else return 1;
    }
    return 0;
}
"#;
    struct OneShot {
        script: Script,
        at: Option<u64>,
    }
    impl Host for OneShot {
        fn should_cancel_root(&mut self, turn: u64) -> bool {
            self.at == Some(turn)
        }
        fn call(
            &mut self,
            control: &Control,
            args: &[Value],
            config: &Config,
        ) -> Result<Answer, String> {
            self.script.call(control, args, config)
        }
    }
    let (_, runs) = script::native_runs(single_root_cancel_source()).unwrap();
    compare_c_host(
        single_root_cancel_source(),
        "root_cancel",
        DRIVER,
        |program, config| {
            let mut expected = Vec::new();
            for (spec, at) in runs
                .iter()
                .zip([Some(1), Some(2), Some(3), None, Some(1), Some(1)])
            {
                let mut host = OneShot {
                    script: scheduled_host(spec).inner,
                    at,
                };
                let result = compare(
                    program,
                    &spec.entry,
                    spec.arguments.clone(),
                    &mut host,
                    config,
                );
                assert_eq!(result.verdict, Verdict::Same);
                assert!(matches!(result.oracle.end, oracle::End::Done { .. }));
                expected.extend(result.oracle.trace.iter().map(ToString::to_string));
                expected.push(result.oracle.end.to_string());
            }
            expected
        },
    );
}

#[test]
fn waiting_choices_replay_all_turn_fixture_directives() {
    compare_native_runs(
        include_str!("slice4/e_turn.core"),
        &["E-AwaitHost"],
        &[2, 2, 0, 0, 1, 2, 2],
        4,
    );
}

#[test]
fn waiting_choices_handle_three_candidates_and_reset_between_runs() {
    compare_native_runs(WAITING_CHOICES, &["E-AwaitHost"], &[4; 4], 8);
}

#[test]
fn waiting_choices_reject_an_answer_for_a_different_operation() {
    let (program, runs) = script::native_runs(WAITING_CHOICES).unwrap();
    let mut spec = runs[0].clone();
    // Select stamp(9) while the next answer belongs to read_value.
    spec.waiting = vec![0, 0];
    for bits in [32, 64] {
        let config = Config::with_usize_bits(bits);
        let original = oracle::run(
            &program,
            &spec.entry,
            vec![],
            &mut scheduled_host(&spec),
            &config,
        );
        let erased = erased::run(
            &program,
            &spec.entry,
            vec![],
            &mut scheduled_host(&spec),
            &config,
        );
        assert!(matches!(original.end, oracle::End::HostFailed(_)));
        assert!(matches!(erased.end, erased::End::HostFailed(_)));
        assert_eq!(erased.trace, original.trace);
        assert_eq!(
            original
                .trace
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>(),
            [
                "stamp(0) -> ok {9}",
                "enter(22) -> ok {}",
                "enter(11) -> ok {}"
            ]
        );
        for opt in [0, 2] {
            let batch =
                run_native_counted(&program, std::slice::from_ref(&spec), bits, opt).unwrap();
            let [(erased::End::HostFailed(_), trace)] = batch.runs.as_slice() else {
                panic!("expected one failed host, got {:?}", batch.runs);
            };
            assert_eq!(trace, &original.trace);
        }
    }
}

#[test]
fn waiting_choices_use_the_same_pending_handles_in_a_linked_host() {
    const DRIVER: &str = r#"
#include "module.h"
#include <stdio.h>
#include <stdlib.h>
static const uint32_t offers[][3] = {{0}, {9, 11, 22}, {9, 11}, {9}};
static const unsigned counts[] = {1, 3, 2, 1};
static const unsigned picks[] = {0, 5, 1, 0};
static unsigned offer, turn;
static void *selected;
void vn2_start_stamp(struct vn2_wait_stamp *r) {
    if (r->host_state) abort();
    r->host_state = &r->in_key;
}
void vn2_start_read_value(struct vn2_wait_read_value *r) {
    if (r->host_state) abort();
    r->host_state = &r->in_key;
}
uint64_t vn2_pick_turn(uint64_t n) {
    if (!n) abort();
    return turn++ == 1;
}
uint64_t vn2_pick_waiting(void *const *states, uint64_t n) {
    if (offer >= 4 || n != counts[offer] || selected) abort();
    for (unsigned i = 0; i < n; ++i) {
        if (!states[i] || *(uint32_t *)states[i] != offers[offer][i]) abort();
    }
    unsigned choice = picks[offer++];
    selected = states[choice % n];
    return choice;
}
int32_t vn2_complete_stamp(struct vn2_wait_stamp *r) {
    if (selected != &r->in_key || r->host_state != selected) abort();
    selected = NULL;
    *r->out_0_ok_0 = r->in_key ? 90 : 9;
    printf("stamp(%u) -> ok {%u}\n", (unsigned)r->in_key, (unsigned)*r->out_0_ok_0);
    return VN2_STAMP_OK;
}
int32_t vn2_complete_read_value(struct vn2_wait_read_value *r) {
    if (selected != &r->in_key || r->host_state != selected) abort();
    selected = NULL;
    *r->out_0_ok_0 = r->in_key * 10;
    printf("read_value(%u) -> ok {%u}\n", (unsigned)r->in_key, (unsigned)*r->out_0_ok_0);
    return VN2_READ_VALUE_OK;
}
int32_t vn2_ext_enter(uint32_t key) {
    printf("enter(%u) -> ok {}\n", (unsigned)key);
    return VN2_ENTER_OK;
}
int main(void) {
    uint32_t mark, a, x, b, y;
    if (vn2_call_example(&mark, &a, &x, &b, &y) != VN2_EXAMPLE_OK || offer != 4 || selected)
        return 1;
    printf("done ok {%u, %u, %u, %u, %u}\n", (unsigned)mark, (unsigned)a, (unsigned)x,
           (unsigned)b, (unsigned)y);
    return 0;
}
"#;
    let (_, runs) = script::native_runs(WAITING_CHOICES).unwrap();
    let spec = &runs[0];
    compare_c_host(
        WAITING_CHOICES,
        "waiting_choices",
        DRIVER,
        |program, config| {
            let result = compare(
                program,
                &spec.entry,
                spec.arguments.clone(),
                &mut scheduled_host(spec),
                config,
            );
            assert_eq!(result.verdict, Verdict::Same);
            assert_eq!(
                result.oracle.end.to_string(),
                "done ok {90, 22, 220, 11, 110}"
            );
            let mut observed: Vec<_> = result
                .oracle
                .trace
                .iter()
                .map(ToString::to_string)
                .collect();
            observed.push(result.oracle.end.to_string());
            observed
        },
    );
}

#[test]
fn member_host_wait_delivers_to_the_parked_activation() {
    // Two vectors and one nested activation. Four simultaneous-wait offers
    // need a temporary pair of arrays. A single request needs no allocation.
    compare_native_runs(
        MEMBER_HOST_WAIT,
        &["E-AwaitHost"],
        &[2, 1, 1, 2, 2, 2, 1, 2, 3],
        7,
    );
}

#[test]
fn owner_host_wait_keeps_member_completions_until_delivery() {
    // These scalar members and their leaf children fit in the owning frames.
    compare_native_runs(OWNER_HOST_WAIT, &["E-AwaitHost"], &[1; 6], 0);
}

#[test]
fn root_host_wait_binds_each_completion_and_releases_owned_arguments() {
    // Only the input and output vectors of exchange_data need heap storage.
    compare_native_runs(HOST_WAIT, &["E-AwaitHost"], &[2, 1, 1, 2, 2, 1, 1, 1, 2], 2);
}

#[test]
fn defined_await_resumes_with_bound_operands_and_output_slots() {
    // Only the two nonempty input vectors need heap storage.
    compare_native_runs(AWAITS, &["E-Await", "E-Turn"], &[1, 1, 2, 0, 0, 2], 2);
}

#[test]
fn spawned_members_run_on_the_chosen_turn_and_keep_their_payloads() {
    let source = include_str!("slice4/checked_spawn.core");
    // Each collect run owns two allocated vectors. Scheduler activations
    // for these single-execution spawn sites stay in the owner's frame.
    compare_native_runs(source, &["E-Spawn"], &[2, 2, 2, 2, 2, 4, 4], 6);
    let program = load(source).unwrap();
    assert!(emit_c_header(&program, 64).contains("uint64_t vn2_pick_turn(uint64_t ready_count);"));
}

#[test]
fn borrowed_spawn_inputs_keep_the_owner_places_across_turns() {
    // Only the two simultaneous loop members need heap frames.
    compare_native_runs(
        include_str!("slice4/checked_borrowed_spawn.core"),
        &["E-Spawn"],
        &[2, 2, 1, 2],
        2,
    );
}

#[test]
fn borrowed_results_keep_their_origins_after_delivery_and_frame_reuse() {
    // The second loop spawn in recycle takes the first delivered frame.
    compare_native_runs(
        include_str!("slice4/checked_borrowed_result.core"),
        &["E-Spawn"],
        &[2, 2, 2, 2, 2],
        1,
    );
}

#[test]
fn repeated_spawns_preserve_each_member_until_its_payload_is_delivered() {
    // The alternating run visits its spawn four times and needs one heap frame.
    compare_native_runs(REPEATED_SPAWN, &["E-Spawn"], &[0, 1, 4, 4, 2, 4], 29);
}

#[test]
fn repeated_spawn_stops_before_count_would_exceed_the_target_limit() {
    // Use small limits at the emitted spawn sites to reach the target-width
    // guard without building billions of members. Identify its trap by exit code.
    let (program, runs) = script::native_runs(REPEATED_SPAWN).unwrap();
    let four = &runs[2..3];
    for (bits, max) in [(32, u64::from(u32::MAX)), (64, u64::MAX)] {
        for (cap, end) in [(4, "done ok {[[90], [3], [2], []], 4}"), (3, "exhausted")] {
            let mut config = Config::with_usize_bits(bits);
            config.capacity = Some(Int::from_u64(cap));
            let spec = &four[0];
            let mut host = Script {
                answers: Default::default(),
            };
            let comparison = compare(
                &program,
                &spec.entry,
                spec.arguments.clone(),
                &mut host,
                &config,
            );
            assert_eq!(comparison.verdict, Verdict::Same);
            assert_eq!(comparison.oracle.end.to_string(), end);
        }
        let ir = emit_native_harness_llvm(&program, four, bits).unwrap();
        let limit = format!(", i64 {max})");
        let scaled = |cap| {
            ir.lines()
                .map(|line| {
                    if line.contains("call fastcc void @vn2_spawn(") {
                        assert!(line.ends_with(&limit), "{line}");
                        line.replace(&limit, &format!(", i64 {cap})"))
                    } else {
                        line.to_string()
                    }
                })
                .collect::<Vec<_>>()
                .join("\n")
        };
        for optimization in [0, 2] {
            let at_limit = run_native_ir(&program, four, &scaled(4), optimization).unwrap();
            assert_eq!(
                at_limit.runs[0].0.to_string(),
                "done ok {[[90], [3], [2], []], 4}"
            );
            let beyond = scaled(3).replace("call void @llvm.trap()", "call void @exit(i32 70)");
            assert_eq!(
                run_native_ir(&program, four, &beyond, optimization).unwrap_err(),
                "native binary exited with Some(70) after 0 of 1 runs"
            );
        }
    }
}

#[test]
fn nested_member_sets_deliver_to_the_correct_await_activation() {
    // Thirteen suspending callee activations, four input vectors and two paths.
    compare_native_runs(NESTED_MEMBER_SET, &["E-Spawn"], &[4, 4, 1, 4, 4], 19);
}

#[test]
fn member_owned_sets_deliver_to_each_parent_in_completion_order() {
    // Eight packet vectors, six tree vectors, and eight recursive child frames.
    compare_native_runs(MEMBER_SET, &["E-Spawn"], &[5, 5, 0, 3, 5, 5, 1], 22);
}

#[test]
fn awaited_set_owners_deliver_their_own_results() {
    // Ten packet vectors in the outer runs, one in inner, one in collect.
    compare_native_runs(AWAITED_SET, &["E-Spawn"], &[2, 2, 2, 2, 2, 1, 3], 12);
}

#[test]
fn multiple_sets_deliver_only_the_requested_producers_results() {
    // Eight packet vectors, three loop frames, and the collected number vector.
    compare_native_runs(MULTIPLE_SETS, &["E-Spawn"], &[3, 3, 3, 3, 1, 4], 12);
}

#[test]
fn a_defined_await_keeps_a_member_ready_with_its_bound_operands() {
    // Each pair owns two input vectors. The same worker run alone owns one.
    compare_native_runs(MEMBER_AWAIT, &["E-Await"], &[3, 3, 3, 2, 3, 1], 7);
}

#[test]
fn a_defined_owner_await_preserves_completions_until_next() {
    // Two child vectors on each collect, plus two nonempty owner inputs.
    compare_native_runs(
        include_str!("slice4/checked_owner_await.core"),
        &["E-Await"],
        &[3, 3, 3, 3],
        8,
    );
}

#[test]
fn nested_owner_awaits_schedule_the_same_children_at_each_depth() {
    compare_native_runs(NESTED_OWNER, &["E-Await"], &[3, 3, 3, 3, 4, 2], 5);
}

#[test]
fn nested_member_awaits_keep_each_invocations_payload_and_resume_point() {
    // Eight vectors and eleven suspending callee activations across the five runs.
    compare_native_runs(NESTED_MEMBER, &["E-Await"], &[3, 3, 6, 3, 3], 19);
}

#[test]
fn native_compilation_reports_operations_that_need_a_scheduler() {
    // The former refusal of a captured cancellable await now runs natively.
    compare_native_runs(
        r#"
extern async control tick() ■ { ok {} │ cancelled {} } uses io
async control waits() ■ { ok {} } uses io
    ⊤ ▷ r := capture await tick()
    ⊤ ▷ d : Δ outcome(r) ▸ ok {} │ cancelled {}
    ⊤ ▷ ■ ok {}
//! run waits() with [tick -> ok] => done ok trace [tick() -> ok]
"#,
        &["E-AwaitHost"],
        &[1],
        0,
    );
    // The former refusal of a direct cancellable run also executes.
    compare_native_runs(
        r#"
extern async control tick() ■ { ok {} │ cancelled {} } uses io
control bridge2() ■ { ok {} } uses io
    ⊤ ▷ r : Δ run tick() ▸ ok {} │ cancelled {}
    ⊤ ▷ ■ ok {}
//! run bridge2() with [tick -> ok] => done ok trace [tick() -> ok]
"#,
        &["E-Run"],
        &[1],
        0,
    );
    compare_native_runs(
        r#"
async control member() ■ { ok {} }
    ⊤ ▷ ■ ok {}
async control pool() ■ { ok {} }
    ⊤ ▷ ~x : tasks⟨member⟩ := tasks⟨member⟩()
    ⊤ ▷ cancel x
    ⊤ ▷ r : Δ await next(x) ▸ ok {} │ empty {}
    r.ok ▷ ⊥
    r.empty ▷ ■ ok {}
//! run pool() => done ok
"#,
        &["E-Cancel"],
        &[1],
        0,
    );
    // Put supported entries first. Both emitters compile the whole module.
    for (decls, reason) in [
        (
            r#"
extern async control tick() ■ { ok {} } faults uses io
control bridge2() ■ { ok {} } faults uses io
    ⊤ ▷ r := capture run tick()
    ⊤ ▷ d : Δ outcome(r) ▸ ok {}
    d.ok ▷ ■ ok {}
//! run bridge2() with [tick -> ok] => done ok trace [tick() -> ok]
"#,
            "faulting host run of `tick`",
        ),
        (
            r#"
extern async control tick() ■ { ok {} } faults uses io
async control waits() ■ { ok {} } faults uses io
    ⊤ ▷ r : Δ await tick() ▸ ok {}
    r.ok ▷ ■ ok {}
//! run waits() with [tick -> ok] => done ok trace [tick() -> ok]
"#,
            "faulting host await of `tick`",
        ),
    ] {
        let source = format!("{ROOTS}\n{decls}");
        let (program, specs) = script::native_runs(&source).unwrap();
        check::check(&program).unwrap().revalidate().unwrap();
        let report = script::check(&source);
        assert!(report.failures.is_empty(), "{:?}", report.failures);
        assert_eq!((report.runs, report.compared), (7, 7));
        let error = emit_llvm(&program, 64).unwrap_err();
        assert!(error.contains(reason), "{error}");
        // Even a batch asking only for a supported entry sees the refusal.
        assert_eq!(
            run_native_counted(&program, &specs[..1], 64, 0).unwrap_err(),
            error
        );
    }
}

#[test]
fn root_host_wait_offers_the_pending_request_before_resuming_the_root() {
    let (source, _) = HOST_WAIT.split_once("async control unit()").unwrap();
    compare_fetch_host(
        source,
        "root_host_wait",
        &[0, 1],
        &[
            "waiting 4 true",
            "complete 4 true",
            "ready 1",
            "waiting 8 false",
            "complete 8 false",
            "ready 1",
        ],
    );
}

#[test]
fn direct_host_runs_finish_before_the_outer_tasks_are_offered() {
    let (source, _) = HOST_RUN.split_once("extern async control tick()").unwrap();
    compare_fetch_host(
        source,
        "direct_host_run",
        &[0, 0],
        &[
            "waiting 4 true",
            "complete 4 true",
            "waiting 8 false",
            "complete 8 false",
            "ready 2",
            "ready 2",
            "ready 1",
            "ready 1",
            "ready 1",
        ],
    );
}

#[test]
fn member_host_wait_resumes_the_member_before_its_owner() {
    let (source, _) = MEMBER_HOST_WAIT
        .split_once("extern async control exchange(")
        .unwrap();
    compare_fetch_host(
        source,
        "member_host_wait",
        &[1, 2],
        &[
            "ready 1",
            "waiting 4 true",
            "complete 4 true",
            "ready 1",
            "waiting 8 false",
            "complete 8 false",
            "ready 1",
            "ready 1",
            "ready 1",
        ],
    );
}

#[test]
fn member_host_wait_offers_pending_operations_in_spawn_order() {
    #[derive(Default)]
    struct PairHost(Vec<String>);
    impl Host for PairHost {
        fn pick_turn(&mut self, ready: usize) -> usize {
            self.0.push(format!("ready {ready}"));
            ready - 1
        }
        fn pick_waiting(&mut self, waiting: &[(&Control, &[Value])]) -> usize {
            let mut line = "waiting".to_owned();
            for (control, args) in waiting {
                assert_eq!(control.name, "fetch");
                let [Value::Int(key), Value::Bool(true)] = args else {
                    panic!("unexpected pending request {args:?}")
                };
                line.push_str(&format!(" {key}"));
            }
            self.0.push(line);
            3
        }
        fn call(
            &mut self,
            control: &Control,
            args: &[Value],
            _: &Config,
        ) -> Result<Answer, String> {
            assert_eq!(control.name, "fetch");
            let [Value::Int(key), Value::Bool(true)] = args else {
                panic!("unexpected completion {args:?}")
            };
            self.0.push(format!("complete {key}"));
            let (alternative, payload) = if key == &Int::from_u64(22) {
                (
                    "found",
                    vec![Value::Int(Int::from_u64(44)), Value::Bool(false)],
                )
            } else {
                ("missing", vec![])
            };
            Ok(Answer {
                alternative: alternative.into(),
                payload,
                writes: vec![],
            })
        }
    }
    const DRIVER: &str = r#"
#include "module.h"
#include <stdio.h>
#include <stdlib.h>
static unsigned starts;
static struct vn2_wait_fetch *selected;
void vn2_start_fetch(struct vn2_wait_fetch *r) {
    if (r->host_state || !r->in_cached || r->in_key != (starts++ ? 11 : 22)) abort();
    r->host_state = r;
}
uint64_t vn2_pick_turn(uint64_t n) {
    printf("ready %u\n", (unsigned)n);
    return n - 1;
}
uint64_t vn2_pick_waiting(void *const *states, uint64_t n) {
    if (!n || n > 2 || selected) abort();
    printf("waiting");
    for (unsigned i = 0; i < n; ++i) {
        struct vn2_wait_fetch *r = states[i];
        printf(" %u", (unsigned)r->in_key);
    }
    puts("");
    selected = states[3 % n];
    return 3;
}
int32_t vn2_complete_fetch(struct vn2_wait_fetch *r) {
    if (selected != r || r->host_state != r) abort();
    selected = NULL;
    printf("complete %u\n", (unsigned)r->in_key);
    if (r->in_key == 11) return VN2_FETCH_MISSING;
    *r->out_0_found_0 = 44;
    *r->out_0_found_1 = 0;
    return VN2_FETCH_FOUND;
}
int main(void) {
    struct vn2_wait_fetch a, b;
    if (vn2_call_run_pair(&a.in_key, &b.in_key) != VN2_RUN_PAIR_OK || starts != 2) return 1;
    printf("done ok {%u, %u}\n", (unsigned)a.in_key, (unsigned)b.in_key);
    return 0;
}
"#;
    let (source, _) = MEMBER_HOST_WAIT
        .split_once("extern async control exchange(")
        .unwrap();
    compare_c_host(source, "member_host_pair", DRIVER, |program, config| {
        let mut host = PairHost::default();
        let original = oracle::run(program, "run_pair", vec![], &mut host, config);
        let mut erased_host = PairHost::default();
        let erased = erased::run(program, "run_pair", vec![], &mut erased_host, config);
        assert_eq!(erased.trace, original.trace);
        assert_eq!(erased.end.to_string(), original.end.to_string());
        assert_eq!(erased_host.0, host.0);
        assert_eq!(
            host.0,
            [
                "ready 2",
                "ready 1",
                "waiting 11 22",
                "complete 22",
                "ready 1",
                "ready 1",
                "waiting 11",
                "complete 11",
                "ready 1",
                "ready 1",
                "ready 1",
            ]
        );
        assert_eq!(original.end.to_string(), "done ok {1, 0}");
        host.0.push(original.end.to_string());
        host.0
    });
}

#[test]
fn owner_host_wait_offers_only_members_until_the_host_can_complete() {
    let (source, _) = OWNER_HOST_WAIT.split_once("extern control ping(").unwrap();
    compare_fetch_host(
        source,
        "owner_host_wait",
        &[0],
        &[
            "ready 2",
            "ready 2",
            "ready 1",
            "ready 1",
            "waiting 4 false",
            "complete 4 false",
            "ready 1",
            "ready 1",
            "ready 1",
            "ready 1",
        ],
    );
}

fn compare_fetch_host(source: &str, name: &str, start_turns: &[u32], expected: &[&str]) {
    #[derive(Default)]
    struct FetchHost(Vec<String>);

    impl Host for FetchHost {
        fn pick_waiting(&mut self, waiting: &[(&Control, &[Value])]) -> usize {
            let [(control, [Value::Int(key), Value::Bool(cached)])] = waiting else {
                panic!("expected one fetch");
            };
            assert_eq!(control.name, "fetch");
            self.0.push(format!("waiting {key} {cached}"));
            7 // Every index selects the sole pending operation.
        }

        fn call(
            &mut self,
            control: &Control,
            args: &[Value],
            _: &Config,
        ) -> Result<Answer, String> {
            assert_eq!(control.name, "fetch");
            let [Value::Int(key), Value::Bool(cached)] = args else {
                panic!("expected fetch arguments")
            };
            self.0.push(format!("complete {key} {cached}"));
            Ok(Answer {
                alternative: "found".into(),
                payload: vec![
                    Value::Int(Int::from_u64(if *cached { 8 } else { 37 })),
                    Value::Bool(true),
                ],
                writes: vec![],
            })
        }

        fn pick_turn(&mut self, ready: usize) -> usize {
            self.0.push(format!("ready {ready}"));
            0
        }
    }

    const DRIVER: &str = r#"
#include "module.h"
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>

static struct vn2_wait_fetch *pending;
static const unsigned start_turns[] = {START_TURNS};
static unsigned token, selected, starts, turns;

void vn2_start_fetch(struct vn2_wait_fetch *r) {
    if (pending || r->host_state || starts >= sizeof(start_turns) / sizeof(start_turns[0])) abort();
    if (turns != start_turns[starts++]) abort();
    pending = r;
    r->host_state = &token;
}
uint64_t vn2_pick_waiting(void *const *states, uint64_t count) {
    if (!pending || selected || count != 1 || states[0] != &token) abort();
    selected = 1;
    printf("waiting %" PRIu64 " %s\n", (uint64_t)pending->in_key, pending->in_cached ? "true" : "false");
    return 7;
}
int32_t vn2_complete_fetch(struct vn2_wait_fetch *r) {
    if (!selected || r != pending || r->host_state != &token) abort();
    printf("complete %" PRIu64 " %s\n", (uint64_t)r->in_key, r->in_cached ? "true" : "false");
    *r->out_0_found_0 = r->in_cached ? 8 : 37;
    *r->out_0_found_1 = 2;  /* Nonzero C byte, including for a captured outcome. */
    pending = NULL;
    selected = 0;
    return VN2_FETCH_FOUND;
}
uint64_t vn2_pick_turn(uint64_t count) {
    ++turns;
    printf("ready %" PRIu64 "\n", count);
    return 0;
}
int main(void) {
    struct vn2_wait_fetch result;
    if (vn2_call_example(&result.in_key) != VN2_EXAMPLE_OK) return 1;
    if (starts != sizeof(start_turns) / sizeof(start_turns[0])) return 1;
    printf("done ok {%" PRIu64 "}\n", (uint64_t)result.in_key);
    return 0;
}
"#;
    let starts = start_turns
        .iter()
        .map(u32::to_string)
        .collect::<Vec<_>>()
        .join(", ");
    let driver = DRIVER.replace("START_TURNS", &starts);
    compare_c_host(source, name, &driver, |program, config| {
        let mut host = FetchHost::default();
        let original = oracle::run(program, "example", vec![], &mut host, config);
        let mut erased_host = FetchHost::default();
        let erased = erased::run(program, "example", vec![], &mut erased_host, config);
        assert_eq!(erased.trace, original.trace);
        assert_eq!(erased.end.to_string(), original.end.to_string());
        assert_eq!(erased_host.0, host.0);
        assert_eq!(host.0, expected);
        assert_eq!(original.end.to_string(), "done ok {37}");
        host.0.push(original.end.to_string());
        host.0
    });
}

/// The next sample reveals how many times the host has selected a ready task.
#[derive(Default)]
struct TurnHost {
    turns: u64,
    choices: VecDeque<usize>,
    calls: Vec<String>,
}

impl Host for TurnHost {
    fn pick_turn(&mut self, ready: usize) -> usize {
        self.calls.push(format!("ready {ready}"));
        self.turns += 1;
        self.choices.pop_front().unwrap_or(0)
    }

    fn call(&mut self, control: &Control, args: &[Value], _: &Config) -> Result<Answer, String> {
        assert_eq!(control.name, "sample");
        let [Value::Int(mark)] = args else {
            panic!("bad sample arguments {args:?}")
        };
        self.calls.push(format!("sample {mark} at {}", self.turns));
        Ok(Answer {
            alternative: "ok".into(),
            payload: vec![Value::Int(Int::from_u64(self.turns))],
            writes: Vec::new(),
        })
    }
}

const C_HOST: &str = r#"
#include "module.h"
#include <inttypes.h>
#include <stdio.h>

static uint32_t turns;

uint64_t vn2_pick_turn(uint64_t ready_count) {
    printf("ready %" PRIu64 "\n", ready_count);
    ++turns;
    return 0;
}

int32_t vn2_ext_sample(uint32_t mark, uint32_t *value) {
    printf("sample %" PRIu32 " at %" PRIu32 "\n", mark, turns);
    *value = turns;
    return VN2_SAMPLE_OK;
}

int main(void) {
    for (uint8_t wait = 0; wait <= 1; ++wait) {
        uint32_t x, y, z, last;
        turns = 0;
        if (vn2_call_runs_timed(wait, &x, &y, &z, &last) != VN2_RUNS_TIMED_OUT)
            return 1;
        printf("done out {%" PRIu32 ", %" PRIu32 ", %" PRIu32 ", %" PRIu32 "}\n", x, y, z, last);
    }
    return 0;
}
"#;

#[test]
fn the_host_picks_the_turn_before_the_awaited_body_starts() {
    compare_c_host(AWAITS, "await_turn", C_HOST, |program, config| {
        let mut expected = Vec::new();
        for wait in [false, true] {
            let args = vec![Value::Bool(wait)];
            let mut host = TurnHost::default();
            let original = oracle::run(program, "runs_timed", args.clone(), &mut host, config);
            let mut erased_host = TurnHost::default();
            let erased = erased::run(program, "runs_timed", args, &mut erased_host, config);
            assert_eq!(erased.end.to_string(), original.end.to_string());
            assert_eq!(erased.trace, original.trace);
            assert_eq!(erased_host.calls, host.calls);
            assert_eq!(host.turns, if wait { 2 } else { 0 });
            expected.extend(host.calls);
            expected.push(original.end.to_string());
        }
        expected
    });
}

#[test]
fn the_host_sees_a_suspended_member_in_spawn_order_until_it_finishes() {
    const DRIVER: &str = r#"
#include "module.h"
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>

static unsigned turn, emitted;
static char events[3];

uint64_t vn2_pick_turn(uint64_t ready_count) {
    const uint64_t choices[] = {0, 1, 1};
    printf("ready %" PRIu64 "\n", ready_count);
    unsigned i = turn++;
    return i < 3 ? choices[i] : 0;
}
void vn2_builtin_emit(const struct vn2_string *value) {
    if (emitted == sizeof(events) || value->len != 1) exit(2);
    events[emitted++] = value->data[0];
}
int main(void) {
    if (vn2_call_rounds(2, 1) != VN2_ROUNDS_OK) return 1;
    for (unsigned i = 0; i < emitted; ++i)
        printf("emit(\"%c\") -> done {}\n", events[i]);
    puts("done ok {}");
    return 0;
}
"#;
    compare_c_host(MEMBER_AWAIT, "member_turn", DRIVER, |program, config| {
        let args = vec![Value::Int(Int::from_u64(2)), Value::Int(Int::from_u64(1))];
        let host = || TurnHost {
            choices: [0, 1, 1].into(),
            ..Default::default()
        };
        let mut original_host = host();
        let original = oracle::run(program, "rounds", args.clone(), &mut original_host, config);
        let mut erased_host = host();
        let erased = erased::run(program, "rounds", args, &mut erased_host, config);
        assert_eq!(erased.end.to_string(), original.end.to_string());
        assert_eq!(erased.trace, original.trace);
        assert_eq!(erased_host.calls, original_host.calls);
        let mut expected = original_host.calls;
        assert_eq!(
            expected,
            [
                "ready 2", "ready 2", "ready 2", "ready 2", "ready 1", "ready 1", "ready 1",
                "ready 1"
            ]
        );
        expected.extend(original.trace.iter().map(ToString::to_string));
        expected.push(original.end.to_string());
        expected
    });
}

#[test]
fn the_host_chooses_between_an_awaiting_owner_and_its_child() {
    const DRIVER: &str = r#"
#include "module.h"
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static uint64_t first;
uint64_t vn2_pick_turn(uint64_t count) {
    printf("ready %" PRIu64 "\n", count);
    uint64_t choice = first;
    first = 0;
    return choice;
}
static char events[2][7];
static unsigned emitted;
void vn2_builtin_emit(const struct vn2_string *s) {
    if (emitted == 2 || s->len >= sizeof(events[0])) exit(2);
    memcpy(events[emitted], s->data, s->len);
    events[emitted++][s->len] = 0;
}
int main(void) {
    for (unsigned choice = 0; choice < 2; ++choice) {
        first = choice;
        emitted = 0;
        if (vn2_call_runs_parent() != VN2_RUNS_PARENT_OK || emitted != 2) return 1;
        for (unsigned i = 0; i < emitted; ++i)
            printf("emit(\"%s\") -> done {}\n", events[i]);
        puts("done ok {}");
    }
    return 0;
}
"#;
    compare_c_host(
        include_str!("slice4/e_await.core"),
        "owner_turn",
        DRIVER,
        |program, config| {
            let mut expected = Vec::new();
            for choice in [0, 1] {
                let host = || TurnHost {
                    choices: [choice].into(),
                    ..Default::default()
                };
                let mut original_host = host();
                let original =
                    oracle::run(program, "runs_parent", vec![], &mut original_host, config);
                let mut erased_host = host();
                let erased = erased::run(program, "runs_parent", vec![], &mut erased_host, config);
                assert_eq!(erased.end.to_string(), original.end.to_string());
                assert_eq!(erased.trace, original.trace);
                assert_eq!(erased_host.calls, original_host.calls);
                assert_eq!(
                    original_host.calls,
                    ["ready 2", "ready 1", "ready 1", "ready 1"]
                );
                expected.extend(original_host.calls);
                expected.extend(original.trace.iter().map(ToString::to_string));
                expected.push(original.end.to_string());
            }
            expected
        },
    );
}

#[test]
fn a_nested_run_freezes_the_outer_set_until_the_next_owner_await() {
    compare_sampled_example(
        NESTED_OWNER,
        "nested_owner",
        [0, 1, 0, 1],
        &[
            "ready 2",
            "sample 1 at 1",
            "ready 1",
            "sample 7 at 2",
            "ready 2",
            "sample 2 at 3",
            "ready 2",
            "sample 9 at 4",
            "ready 1",
            "sample 3 at 5",
            "ready 1",
            "ready 1",
        ],
    );
}

#[test]
fn the_owner_receives_a_sibling_while_a_nested_member_is_suspended() {
    compare_sampled_example(
        NESTED_MEMBER,
        "nested_member",
        [0, 0, 0, 1],
        &[
            "ready 2",
            "ready 2",
            "sample 1 at 2",
            "ready 2",
            "sample 2 at 3",
            "ready 2",
            "sample 9 at 4",
            "ready 2",
            "sample 7 at 5",
            "ready 1",
            "sample 3 at 6",
            "ready 1",
            "ready 1",
        ],
    );
}

#[test]
fn nested_member_sets_wake_only_the_worker_whose_child_finished() {
    for (name, child, first, second) in [
        ("nested_set_first", 0, "sample 1 at 5", "sample 2 at 9"),
        ("nested_set_second", 1, "sample 2 at 5", "sample 1 at 9"),
    ] {
        compare_sampled_example(
            NESTED_MEMBER_SET,
            name,
            [0, 0, 0, 0, child],
            &[
                "ready 2",
                "ready 2",
                "ready 2",
                "ready 2",
                "ready 2",
                first,
                "ready 2",
                "ready 2",
                "sample 9 at 7",
                "ready 2",
                "ready 1",
                second,
                "ready 1",
                "ready 1",
                "sample 9 at 11",
                "ready 1",
                "ready 1",
            ],
        );
    }
}

#[test]
fn member_owned_sets_offer_only_ready_parents_in_spawn_order() {
    // The peer and side packet finish while the parent waits for its wanted set.
    compare_sampled_example(
        MEMBER_SET,
        "member_set_wait",
        [0, 0, 0, 0],
        &[
            "ready 2",
            "ready 4",
            "sample 1 at 2",
            "ready 4",
            "sample 9 at 3",
            "ready 4",
            "ready 3",
            "sample 7 at 5",
            "ready 2",
            "sample 2 at 6",
            "ready 2",
            "sample 3 at 7",
            "ready 1",
            "sample 4 at 8",
            "ready 1",
            "ready 1",
            "ready 1",
            "ready 1",
            "ready 1",
            "ready 1",
        ],
    );
    // Two completions in the same set wake the parent once, in its old position.
    compare_sampled_example(
        MEMBER_SET,
        "member_set_wake",
        [0, 3, 3, 0],
        &[
            "ready 2",
            "ready 4",
            "sample 4 at 2",
            "ready 4",
            "sample 2 at 3",
            "ready 3",
            "sample 3 at 4",
            "ready 3",
            "ready 3",
            "ready 2",
            "sample 1 at 7",
            "ready 2",
            "sample 9 at 8",
            "ready 2",
            "ready 1",
            "sample 7 at 10",
            "ready 1",
            "ready 1",
            "ready 1",
            "ready 1",
        ],
    );
}

#[test]
fn awaited_set_owners_offer_inner_and_outer_members_in_spawn_order() {
    // At the inner next, the outer packet can finish without waking the owner.
    compare_sampled_example(
        AWAITED_SET,
        "awaited_set_outer_first",
        [0, 0, 0, 0],
        &[
            "ready 2",
            "ready 2",
            "ready 3",
            "sample 4 at 3",
            "ready 2",
            "sample 1 at 4",
            "ready 1",
            "sample 2 at 5",
            "ready 1",
            "sample 3 at 6",
            "ready 1",
            "ready 1",
            "ready 1",
        ],
    );
    // Selecting the inner packet wakes the owner while the outer packet is ready.
    compare_sampled_example(
        AWAITED_SET,
        "awaited_set_inner_first",
        [0, 0, 0, 1],
        &[
            "ready 2",
            "ready 2",
            "ready 3",
            "sample 4 at 3",
            "ready 2",
            "sample 2 at 4",
            "ready 2",
            "sample 3 at 5",
            "ready 2",
            "ready 1",
            "sample 1 at 7",
            "ready 1",
            "ready 1",
        ],
    );
}

#[test]
fn multiple_sets_offer_all_ready_members_in_spawn_order() {
    // Two packets finish before the stamp. Neither wakes the waiting owner.
    compare_sampled_example(
        MULTIPLE_SETS,
        "sets_waiting",
        [2, 0, 0, 0],
        &[
            "ready 3",
            "sample 3 at 1",
            "ready 2",
            "ready 2",
            "sample 1 at 3",
            "ready 1",
            "sample 2 at 4",
            "ready 1",
            "sample 7 at 5",
            "ready 1",
            "ready 1",
            "ready 1",
            "sample 8 at 8",
            "ready 1",
            "ready 1",
            "ready 1",
        ],
    );
    // Both packets are still ready when the owner consumes the empty stamp set.
    compare_sampled_example(
        MULTIPLE_SETS,
        "sets_drained",
        [1, 0, 0, 2],
        &[
            "ready 3",
            "sample 2 at 1",
            "ready 3",
            "sample 7 at 2",
            "ready 3",
            "ready 3",
            "sample 3 at 4",
            "ready 2",
            "ready 2",
            "sample 8 at 6",
            "ready 2",
            "ready 1",
            "ready 1",
            "sample 1 at 9",
            "ready 1",
            "ready 1",
        ],
    );
}

fn compare_sampled_example<const N: usize>(
    source: &str,
    name: &str,
    choices: [usize; N],
    calls: &[&str],
) {
    const DRIVER: &str = r#"
#include "module.h"
#include <inttypes.h>
#include <stdio.h>

static uint32_t turns;
uint64_t vn2_pick_turn(uint64_t count) {
    const uint64_t choices[] = {CHOICES};
    printf("ready %" PRIu64 "\n", count);
    uint32_t i = turns++;
    return i < sizeof(choices) / sizeof(choices[0]) ? choices[i] : 0;
}
int32_t vn2_ext_sample(uint32_t mark, uint32_t *value) {
    printf("sample %" PRIu32 " at %" PRIu32 "\n", mark, turns);
    *value = turns;
    return VN2_SAMPLE_OK;
}
int main(void) {
    uint32_t mark;
    if (vn2_call_example(&mark) != VN2_EXAMPLE_OK) return 1;
    printf("done ok {%" PRIu32 "}\n", mark);
    return 0;
}
"#;
    let values = choices.map(|choice| choice.to_string()).join(", ");
    compare_c_host(
        source,
        name,
        &DRIVER.replace("CHOICES", &values),
        |program, config| {
            let host = || TurnHost {
                choices: choices.into(),
                ..Default::default()
            };
            let mut original_host = host();
            let original = oracle::run(program, "example", vec![], &mut original_host, config);
            let mut erased_host = host();
            let erased = erased::run(program, "example", vec![], &mut erased_host, config);
            assert_eq!(erased.end.to_string(), original.end.to_string());
            assert_eq!(erased.trace, original.trace);
            assert_eq!(erased_host.calls, original_host.calls);
            assert_eq!(original_host.calls, calls);
            let mut expected = original_host.calls;
            expected.push(original.end.to_string());
            expected
        },
    );
}

fn compare_c_host(
    source: &str,
    name: &str,
    driver: &str,
    observations: impl Fn(&Program, &Config) -> Vec<String>,
) {
    let program = load(source).unwrap();
    let dir = std::env::temp_dir().join(format!("vn2_{name}_{}", std::process::id()));
    fs::create_dir(&dir).unwrap();
    fs::write(dir.join("host.c"), driver).unwrap();
    for bits in [32, 64] {
        let expected = observations(&program, &Config::with_usize_bits(bits));
        fs::write(dir.join("module.ll"), emit_llvm(&program, bits).unwrap()).unwrap();
        let header = emit_c_header(&program, bits);
        assert!(header.contains("uint64_t vn2_pick_turn(uint64_t ready_count);"));
        fs::write(dir.join("module.h"), header).unwrap();
        for optimization in ["-O0", "-O2"] {
            let build = Command::new("clang")
                .current_dir(&dir)
                .args([
                    "-Wall",
                    "-Wextra",
                    "-Werror",
                    "-Wno-override-module",
                    optimization,
                    "module.ll",
                    "host.c",
                    "-o",
                    "driver",
                ])
                .output()
                .unwrap();
            assert!(
                build.status.success(),
                "{}",
                String::from_utf8_lossy(&build.stderr)
            );
            let run = Command::new(dir.join("driver")).output().unwrap();
            assert!(
                run.status.success(),
                "{:?}: {}",
                run.status,
                String::from_utf8_lossy(&run.stderr)
            );
            assert_eq!(
                String::from_utf8(run.stdout)
                    .unwrap()
                    .lines()
                    .collect::<Vec<_>>(),
                expected,
                "usize={bits} {optimization}"
            );
        }
    }
    fs::remove_dir_all(dir).unwrap();
}

#[test]
fn task_set_diagnostics_cover_unsupported_awaits_sets_and_faults() {
    let base = r#"
async control idle() ■ { ok {} }
    ⊤ ▷ ■ ok {}

async control child(value : usize) ■ { ok {} }
    ⊤ ▷ ■ ok {}

async control owner() ■ { ok {} }
    ⊤ ▷ ~pool : tasks⟨child⟩ := tasks⟨child⟩()
    ⊤ ▷ v : usize := 3
    ⊤ ▷ spawn child(v) into pool
    ⊤ ▷ lp : ↻ drain() {
          ⊤ ▷ n : Δ await next(pool) ▸ ok {} │ empty {}
          n.ok ▷ ↑ drain()
          n.empty ▷ □ drained {}
        } ▸ drained {}
    ⊤ ▷ ■ ok {}

//! run owner() turns [1] => done ok
"#;
    let next_owner = "⊤ ▷ lp : ↻ drain()";
    let suspend = "⊤ ▷ w : Δ await idle() ▸ ok {}";
    let new_set = "⊤ ▷ ~other : tasks⟨child⟩ := tasks⟨child⟩()\n    ⊤ ▷ q : Δ await next(other) ▸ ok {} │ empty {}\n    q.ok ▷ ⊥";
    // Both previously refused paths drain an empty set in the awaited callee.
    let idle_set = base.replace(
        "async control idle() ■ { ok {} }",
        &format!("async control idle() ■ {{ ok {{}} }}\n    {new_set}"),
    );
    let direct = idle_set.replace(
        "child(value : usize) ■ { ok {} }",
        &format!("child(value : usize) ■ {{ ok {{}} }}\n    {suspend}"),
    );
    let indirect = direct.replace(
        "async control child",
        &format!("async control middle() ■ {{ ok {{}} }}\n    {suspend}\n    ⊤ ▷ ■ ok {{}}\n\nasync control child"),
    ).replace(
        &format!("child(value : usize) ■ {{ ok {{}} }}\n    {suspend}"),
        "child(value : usize) ■ { ok {} }\n    ⊤ ▷ w : Δ await middle() ▸ ok {}",
    );
    compare_native_runs(&direct, &["E-Await"], &[1], 1);
    compare_native_runs(&indirect, &["E-Await"], &[2], 2);
    let with_read = base
        .replace(
            "async control idle",
            "extern async control read() ■ { ok {} } uses io\n\nasync control idle",
        )
        .replace("owner() ■ { ok {} }", "owner() ■ { ok {} } uses io")
        .replace(
            "turns [1] => done ok",
            "with [read -> ok] turns [1] => done ok trace [read() -> ok]",
        );
    let await_read = "⊤ ▷ w : Δ await read() ▸ ok {}";
    let owner_wait = with_read.replace(next_owner, &format!("{await_read}\n    {next_owner}"));
    let callee_wait = with_read
        .replace(
            "async control idle() ■ { ok {} }",
            &format!("async control idle() ■ {{ ok {{}} }} uses io\n    {await_read}"),
        )
        .replace(next_owner, &format!("{suspend}\n    {next_owner}"));
    compare_native_runs(&owner_wait, &["E-AwaitHost"], &[1], 0);
    compare_native_runs(&callee_wait, &["E-AwaitHost"], &[1], 0);
    let member_wait = with_read.replace(
        "child(value : usize) ■ { ok {} }",
        &format!("child(value : usize) ■ {{ ok {{}} }} uses io\n    {await_read}"),
    );
    let shared_wait = callee_wait
        .replace(
            "child(value : usize) ■ { ok {} }",
            &format!("child(value : usize) ■ {{ ok {{}} }} uses io\n    {suspend}"),
        )
        .replace("with [read -> ok]", "with [read -> ok; read -> ok]")
        .replace("trace [read() -> ok]", "trace [read() -> ok; read() -> ok]");
    compare_native_runs(&member_wait, &["E-AwaitHost"], &[1], 0);
    compare_native_runs(&shared_wait, &["E-AwaitHost"], &[2], 2);
    let cancellable_callee = callee_wait
        .replace("read() ■ { ok {} }", "read() ■ { ok {} │ cancelled {} }")
        .replace(
            "await read() ▸ ok {}",
            "await read() ▸ ok {} │ cancelled {}",
        );
    compare_native_runs(&cancellable_callee, &["E-AwaitHost"], &[1], 0);
    let cancellable_member = member_wait
        .replace("read() ■ { ok {} }", "read() ■ { ok {} │ cancelled {} }")
        .replace(
            "await read() ▸ ok {}",
            "await read() ▸ ok {} │ cancelled {}",
        );
    compare_native_runs(&cancellable_member, &["E-AwaitHost"], &[1], 0);
    let cancelling_set = new_set.replace("⊤ ▷ q :", "⊤ ▷ cancel other\n    ⊤ ▷ q :");
    let awaited_cancel = idle_set
        .replace(new_set, &cancelling_set)
        .replace(next_owner, &format!("{suspend}\n    {next_owner}"));
    let nested_cancel = indirect.replace(new_set, &cancelling_set);
    let borrower = format!(
        "async control borrower(value : &usize) ■ {{ ok {{loan : &usize ∈ value}} }}
    {cancelling_set}
    ⊤ ▷ ■ ok {{value}}"
    );
    let borrow_in_owner = "⊤ ▷ ~other : tasks⟨borrower⟩ := tasks⟨borrower⟩()
    ⊤ ▷ spawn borrower(&v) into other
    ⊤ ▷ a : Δ await next(other) ▸ ok {loan} │ empty {}
    a.empty ▷ ⊥
    ⊤ ▷ b : Δ await next(other) ▸ ok {extra} │ empty {}
    b.ok ▷ ⊥";
    let borrowing_cancel = base
        .replace(
            "async control owner",
            &format!("{borrower}\n\nasync control owner"),
        )
        .replace(next_owner, &format!("{borrow_in_owner}\n    {next_owner}"));
    compare_native_runs(&awaited_cancel, &["E-Cancel"], &[1], 0);
    compare_native_runs(&nested_cancel, &["E-Cancel"], &[1], 2);
    compare_native_runs(&borrowing_cancel, &["E-Cancel"], &[1], 0);
    for (source, reason) in [
        (
            base.replace(
                "async control idle() ■ { ok {} }",
                "async control idle() ■ { ok {} } faults",
            )
            .replace(
                "async control owner() ■ { ok {} }",
                &format!("async control owner() ■ {{ ok {{}} }} faults\n    {suspend}"),
            ),
            "a faulting or terminating call in a task-set owner",
        ),
        (
            owner_wait
                .replace(
                    "read() ■ { ok {} } uses io",
                    "read() ■ { ok {} } faults uses io",
                )
                .replace(
                    "owner() ■ { ok {} } uses io",
                    "owner() ■ { ok {} } faults uses io",
                ),
            "faulting host await of `read` in task-set owner",
        ),
        (
            member_wait
                .replace(
                    "read() ■ { ok {} } uses io",
                    "read() ■ { ok {} } faults uses io",
                )
                .replace(
                    "child(value : usize) ■ { ok {} } uses io",
                    "child(value : usize) ■ { ok {} } faults uses io",
                )
                .replace(
                    "owner() ■ { ok {} } uses io",
                    "owner() ■ { ok {} } faults uses io",
                ),
            "faulting host await of `read` in task-set member",
        ),
        (
            base.replace(
                "child(value : usize) ■ { ok {} }",
                "child(value : usize) ■ { ok {} } faults",
            )
            .replace("owner() ■ { ok {} }", "owner() ■ { ok {} } faults"),
            "nonfaulting",
        ),
    ] {
        let (program, specs) = script::native_runs(&source).unwrap();
        check::check(&program).unwrap().revalidate().unwrap();
        let report = script::check(&source);
        assert!(report.failures.is_empty(), "{:?}", report.failures);
        assert_eq!((report.runs, report.compared), (1, 1));
        let error = emit_llvm(&program, 64).unwrap_err();
        assert!(error.contains(reason), "{error}");
        assert_eq!(
            run_native_counted(&program, &specs, 64, 0).unwrap_err(),
            error
        );
    }
}
