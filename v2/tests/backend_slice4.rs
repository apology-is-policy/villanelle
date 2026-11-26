//! Native defined roots, awaits, and scheduling of task-set members.
use std::{collections::VecDeque, fs, process::Command};
use villanelle_v2::codegen::{
    emit_c_header, emit_llvm, emit_native_harness_llvm, run_native_counted, run_native_ir,
};
use villanelle_v2::differential::{Verdict, compare};
use villanelle_v2::host::{Answer, Host, Scheduled, Script};
use villanelle_v2::int::Int;
use villanelle_v2::oracle::{self, Config, Value};
use villanelle_v2::typed::{Control, Program};
use villanelle_v2::{check, erased, load, script};

const MULTIPLE_SETS: &str = include_str!("slice4/checked_multiple_sets.core");
const REPEATED_SPAWN: &str = include_str!("slice4/checked_repeated_spawn.core");
const ROOTS: &str = include_str!("slice4/checked_run.core");
const AWAITS: &str = include_str!("slice4/checked_await.core");
const NESTED_MEMBER: &str = include_str!("slice4/checked_nested_member_await.core");
const NESTED_OWNER: &str = include_str!("slice4/checked_nested_owner_await.core");
const MEMBER_AWAIT: &str = include_str!("slice4/checked_member_await.core");

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
            let mut host = Scheduled::new(Script {
                answers: spec.answers.iter().cloned().collect(),
            });
            host.turns = spec.turns.iter().copied().collect();
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
    // Put supported entries first. Both emitters compile the whole module.
    for (decls, reason) in [
        (
            r#"
extern async control tick() ■ { ok {} } uses io
control bridge2() ■ { ok {} } uses io
    ⊤ ▷ r : Δ run tick() ▸ ok {}
    r.ok ▷ ■ ok {}
//! run bridge2() with [tick -> ok] => done ok trace [tick() -> ok]
"#,
            "run of extern async control `tick`",
        ),
        (
            r#"
extern async control tick() ■ { ok {} } uses io
async control waits() ■ { ok {} } uses io
    ⊤ ▷ r := capture await tick()
    ⊤ ▷ d : Δ outcome(r) ▸ ok {}
    d.ok ▷ ■ ok {}
//! run waits() with [tick -> ok] => done ok trace [tick() -> ok]
"#,
            "await of `tick`",
        ),
        (
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
            "task set",
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

fn compare_sampled_example(source: &str, name: &str, choices: [usize; 4], calls: &[&str]) {
    const DRIVER: &str = r#"
#include "module.h"
#include <inttypes.h>
#include <stdio.h>

static uint32_t turns;
uint64_t vn2_pick_turn(uint64_t count) {
    const uint64_t choices[] = {CHOICES};
    printf("ready %" PRIu64 "\n", count);
    uint32_t i = turns++;
    return i < 4 ? choices[i] : 0;
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
            assert!(run.status.success(), "{:?}", run.status);
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
fn task_set_diagnostics_cover_unsupported_awaits_sets_and_loans() {
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
    let spawn = "⊤ ▷ spawn child(v) into pool";
    let next_owner = "⊤ ▷ lp : ↻ drain()";
    let suspend = "⊤ ▷ w : Δ await idle() ▸ ok {}";
    let new_set = "⊤ ▷ ~other : tasks⟨child⟩ := tasks⟨child⟩()\n    ⊤ ▷ q : Δ await next(other) ▸ ok {} │ empty {}\n    q.ok ▷ ⊥";
    for (source, reason) in [
        (base.replace("async control idle", &format!("async control leaf() ■ {{ ok {{}} }}\n    {new_set}\n    ⊤ ▷ ■ ok {{}}\n\nasync control idle"))
            .replace("async control idle() ■ { ok {} }", "async control idle() ■ { ok {} }\n    ⊤ ▷ w : Δ await leaf() ▸ ok {}")
            .replace(next_owner, &format!("{suspend}\n    {next_owner}")), "task-set owner `owner` awaiting `leaf`, which creates a set"),
        (base.replace("async control idle() ■ { ok {} }", &format!("async control idle() ■ {{ ok {{}} }}\n    {new_set}"))
            .replace(next_owner, &format!("{suspend}\n    {next_owner}")), "task-set owner `owner` awaiting `idle`, which creates a set"),
        (base.replace("async control idle() ■ { ok {} }", "async control idle() ■ { ok {} } faults")
            .replace("async control owner() ■ { ok {} }", &format!("async control owner() ■ {{ ok {{}} }} faults\n    {suspend}")), "a faulting or terminating call in a task-set owner"),
        (base.replace("async control idle", "extern async control read() ■ { ok {} } uses io\n\nasync control idle")
            .replace("owner() ■ { ok {} }", "owner() ■ { ok {} } uses io")
            .replace(next_owner, &format!("⊤ ▷ w : Δ await read() ▸ ok {{}}\n    {next_owner}"))
            .replace("turns [1] => done ok", "with [read -> ok] turns [1] => done ok trace [read() -> ok]"), "await of extern `read` in task-set owner"),
        (base.replace("async control idle() ■ { ok {} }", "extern async control read() ■ { ok {} } uses io\n\nasync control idle() ■ { ok {} } uses io\n    ⊤ ▷ w : Δ await read() ▸ ok {}")
            .replace("owner() ■ { ok {} }", "owner() ■ { ok {} } uses io")
            .replace(next_owner, &format!("{suspend}\n    {next_owner}"))
            .replace("turns [1] => done ok", "with [read -> ok] turns [1] => done ok trace [read() -> ok]"), "await of extern `read` in task-set owner"),
        (base.replace("async control idle() ■ { ok {} }", &format!("async control idle() ■ {{ ok {{}} }}\n    {new_set}"))
            .replace("async control child", "async control middle() ■ { ok {} }\n    ⊤ ▷ w : Δ await idle() ▸ ok {}\n    ⊤ ▷ ■ ok {}\n\nasync control child")
            .replace("child(value : usize) ■ { ok {} }", "child(value : usize) ■ { ok {} }\n    ⊤ ▷ w : Δ await middle() ▸ ok {}"), "task-set member `child` awaiting `idle`, which creates a set"),
        (base.replace("async control child", "extern async control read() ■ { ok {} } uses io\n\nasync control child")
            .replace("child(value : usize) ■ { ok {} }", "child(value : usize) ■ { ok {} } uses io\n    ⊤ ▷ w : Δ await read() ▸ ok {}")
            .replace("owner() ■ { ok {} }", "owner() ■ { ok {} } uses io")
            .replace("turns [1] => done ok", "with [read -> ok] turns [1] => done ok trace [read() -> ok]"), "await of extern `read` in task-set member"),
        (base.replace("async control idle() ■ { ok {} }", "async control unit() ■ { ok {} }\n    ⊤ ▷ ■ ok {}\n\nasync control idle() ■ { ok {} }\n    ⊤ ▷ ~set : tasks⟨unit⟩ := tasks⟨unit⟩()\n    ⊤ ▷ n : Δ await next(set) ▸ ok {} │ empty {}\n    n.ok ▷ ⊥")
            .replace("child(value : usize) ■ { ok {} }", &format!("child(value : usize) ■ {{ ok {{}} }}\n    {suspend}")), "task-set member `child` awaiting `idle`, which creates a set"),
        (base.replace("async control owner", "async control borrower(value : &usize) ■ { ok {} }\n    ⊤ ▷ ■ ok {}\n\nasync control owner")
            .replace(next_owner, &format!("⊤ ▷ ~other : tasks⟨borrower⟩ := tasks⟨borrower⟩()\n    ⊤ ▷ spawn borrower(&v) into other\n    ⊤ ▷ a : Δ await next(other) ▸ ok {{}} │ empty {{}}\n    a.empty ▷ ⊥\n    ⊤ ▷ b : Δ await next(other) ▸ ok {{}} │ empty {{}}\n    b.ok ▷ ⊥\n    {next_owner}")), "owned or copy inputs and results and no task set of its own for `borrower`"),
        (base.replace(spawn, &format!("⊤ ▷ l : ↻ once() {{\n        {spawn}\n        ⊤ ▷ □ added {{}}\n    }} ▸ added {{}}")).replace("value : usize", "value : &usize").replace("child(v)", "child(&v)"), "owned or copy inputs"),
        (base.replace("value : usize", "value : &usize").replace("child(v)", "child(&v)"), "owned or copy inputs"),
        (base.replace("child(value : usize) ■ { ok {} }", "child(value : usize) ■ { ok {} } faults").replace("owner() ■ { ok {} }", "owner() ■ { ok {} } faults"), "nonfaulting"),
    ] {
        let (program, specs) = script::native_runs(&source).unwrap();
        check::check(&program).unwrap().revalidate().unwrap();
        let report = script::check(&source);
        assert!(report.failures.is_empty(), "{:?}", report.failures);
        assert_eq!((report.runs, report.compared), (1, 1));
        let error = emit_llvm(&program, 64).unwrap_err();
        assert!(error.contains(reason), "{error}");
        assert_eq!(run_native_counted(&program, &specs, 64, 0).unwrap_err(), error);
    }
}
