//! Native defined roots, awaits, and scheduling of task-set members.
use std::{fs, process::Command};
use villanelle_v2::codegen::{emit_c_header, emit_llvm, run_native_counted};
use villanelle_v2::differential::{Verdict, compare};
use villanelle_v2::host::{Answer, Host, Scheduled, Script};
use villanelle_v2::int::Int;
use villanelle_v2::oracle::{self, Config, Value};
use villanelle_v2::typed::Control;
use villanelle_v2::{check, erased, load, script};

const ROOTS: &str = include_str!("slice4/checked_run.core");
const AWAITS: &str = include_str!("slice4/checked_await.core");

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
    calls: Vec<String>,
}

impl Host for TurnHost {
    fn pick_turn(&mut self, ready: usize) -> usize {
        self.calls.push(format!("ready {ready}"));
        self.turns += 1;
        0
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
    let program = load(AWAITS).unwrap();
    let dir = std::env::temp_dir().join(format!("vn2_await_turn_{}", std::process::id()));
    fs::create_dir(&dir).unwrap();
    fs::write(dir.join("host.c"), C_HOST).unwrap();
    for bits in [32, 64] {
        let config = Config::with_usize_bits(bits);
        let mut expected = Vec::new();
        for wait in [false, true] {
            let args = vec![Value::Bool(wait)];
            let mut host = TurnHost::default();
            let original = oracle::run(&program, "runs_timed", args.clone(), &mut host, &config);
            let mut erased_host = TurnHost::default();
            let erased = erased::run(&program, "runs_timed", args, &mut erased_host, &config);
            assert_eq!(erased.end.to_string(), original.end.to_string());
            assert_eq!(erased.trace, original.trace);
            assert_eq!(erased_host.calls, host.calls);
            assert_eq!(host.turns, if wait { 2 } else { 0 });
            expected.extend(host.calls);
            expected.push(original.end.to_string());
        }
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
fn task_set_diagnostics_cover_suspension_loans_and_repeated_spawn_sites() {
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
        (base.replace(next_owner, &format!("{suspend}\n    {next_owner}")), "await of another control in a task-set owner"),
        (base.replace("child(value : usize) ■ { ok {} }", &format!("child(value : usize) ■ {{ ok {{}} }}\n    {suspend}")), "nonsuspending task-set producer"),
        (base.replace(next_owner, &format!("{new_set}\n    {next_owner}")), "multiple task sets"),
        (base.replace(spawn, &format!("⊤ ▷ l : ↻ once() {{\n        {spawn}\n        ⊤ ▷ □ added {{}}\n    }} ▸ added {{}}")), "spawn outside the owner's top-level body"),
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
