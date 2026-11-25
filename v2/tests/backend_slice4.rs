//! Native [E-Run] for a defined root that has the only turn.
use villanelle_v2::codegen::{emit_llvm, run_native_counted};
use villanelle_v2::differential::{Verdict, compare};
use villanelle_v2::host::Script;
use villanelle_v2::{check, oracle::Config, script};

const ROOTS: &str = include_str!("slice4/checked_run.core");

#[test]
fn defined_roots_return_or_unwind_in_the_callers_decision() {
    let (program, runs) = script::native_runs(ROOTS).unwrap();
    check::check(&program).unwrap().revalidate().unwrap();
    let report = script::check(ROOTS);
    assert!(report.failures.is_empty(), "{:?}", report.failures);
    assert_eq!((report.runs, report.compared, runs.len()), (6, 6, 6));
    for bits in [32, 64] {
        let mut expected = Vec::new();
        for spec in &runs {
            let mut host = Script {
                answers: spec.answers.iter().cloned().collect(),
            };
            let comparison = compare(
                &program,
                &spec.entry,
                spec.arguments.clone(),
                &mut host,
                &Config::with_usize_bits(bits),
            );
            assert_eq!(comparison.verdict, Verdict::Same, "{}", spec.entry);
            let roots = if spec.entry == "runs_nested" { 2 } else { 1 };
            assert_eq!(comparison.oracle.rules.get("E-Run"), Some(&roots));
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
            // The harness allocates the four nonempty vector inputs. Their
            // payloads move, and no root needs a heap frame in this subset.
            assert_eq!(batch.allocations, 4, "usize={bits} -O{optimization}");
        }
    }
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
async control waits() ■ { ok {v : usize} } uses console.write
    ⊤ ▷ r : Δ await say(1) ▸ ok {v}
    r.ok ▷ ■ ok {v}
//! run waits() => done ok {1} trace [emit("inner") -> done]
"#,
            "await of `say`",
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
