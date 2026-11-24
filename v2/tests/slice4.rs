//! Slice 4 Phase 2 conformance tests: cooperative tasks, task sets, turns,
//! cancellation, member faults, stopping, core well-formedness (`[W10]`–`[W12]`,
//! `[TK1]`), transitive purity (`[I10]`), Rails surface elaboration & canonical
//! formatting (`[G7b]`, `[U19]`, `[G3]`, `[G10]`), and oracle-vs-erased
//! differential parity (`[R6]`).

use std::collections::{BTreeSet, VecDeque};
use std::path::PathBuf;
use villanelle_v2::host::{Answer, Scheduled, Script};
use villanelle_v2::int::Int;
use villanelle_v2::oracle::{self, Config, End, Value};
use villanelle_v2::{resolve, script, surface, text};

fn core_files() -> Vec<(String, String)> {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/slice4");
    let mut files = Vec::new();
    for entry in std::fs::read_dir(&root).expect("tests/slice4") {
        let path = entry.expect("dir entry").path();
        if path.extension().and_then(|s| s.to_str()) == Some("core") {
            let name = path.file_name().unwrap().to_string_lossy().into_owned();
            let text = std::fs::read_to_string(&path).expect("read core file");
            files.push((name, text));
        }
    }
    files.sort_by(|a, b| a.0.cmp(&b.0));
    files
}

fn surface_files() -> Vec<(String, String)> {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/slice4_surface");
    let mut files = Vec::new();
    for entry in std::fs::read_dir(&root).expect("tests/slice4_surface") {
        let path = entry.expect("dir entry").path();
        if path.extension().and_then(|s| s.to_str()) == Some("rails") {
            let name = path.file_name().unwrap().to_string_lossy().into_owned();
            let text = std::fs::read_to_string(&path).expect("read rails file");
            files.push((name, text));
        }
    }
    files.sort_by(|a, b| a.0.cmp(&b.0));
    files
}

#[test]
fn slice_four_core_conforms_and_matches_erased() {
    let files = core_files();
    assert!(!files.is_empty(), "expected slice 4 core test files");
    let mut runs = 0usize;
    let mut compared = 0usize;
    let mut rules = BTreeSet::new();
    for (name, source) in &files {
        let report = script::check(source);
        if !report.failures.is_empty() {
            panic!("{} failed:\n{}", name, report.failures.join("\n"));
        }
        assert!(report.runs > 0, "{name} has no run directives");
        runs += report.runs;
        compared += report.compared;
        rules.extend(report.rules.keys().cloned());
    }
    assert!(runs >= 12 && compared >= 8 && compared < runs);
    for required in [
        "E-Run",
        "E-Turn",
        "E-Await",
        "E-AwaitHost",
        "E-Spawn",
        "E-Next",
        "E-Cancel",
        "E-Done",
        "E-MemberFault",
        "E-Stop",
    ] {
        assert!(
            rules.contains(required),
            "Slice 4 core suite did not exercise rule {required}; saw {rules:?}"
        );
    }
}

#[test]
fn slice_four_core_printer_and_reader_agree() {
    for (name, source) in core_files() {
        let parsed = text::parse(&source).unwrap_or_else(|e| panic!("{name}: {e}"));
        let printed = parsed.print();
        let reparsed =
            text::parse(&printed).unwrap_or_else(|e| panic!("{name} reparse: {e}\n{printed}"));
        assert_eq!(
            printed,
            reparsed.print(),
            "core printer/reader round-trip failed for {name}"
        );
    }
}

#[test]
fn slice_four_surface_files_run_format_and_match_erased() {
    let files = surface_files();
    assert!(!files.is_empty(), "expected slice 4 surface test files");
    let mut runs = 0usize;
    let mut compared = 0usize;
    for (name, source) in &files {
        let report = script::check_surface(source);
        if !report.failures.is_empty() {
            panic!("{} failed:\n{}", name, report.failures.join("\n"));
        }
        assert!(report.runs > 0, "{name} has no run directives");
        runs += report.runs;
        compared += report.compared;

        let formatted =
            surface::format(source).unwrap_or_else(|e| panic!("{name}: format error: {e}"));
        assert_eq!(
            formatted, *source,
            "{name} is not in canonical Rails form ([G10])"
        );
        let twice = surface::format(&formatted)
            .unwrap_or_else(|e| panic!("{name}: second format error: {e}"));
        assert_eq!(twice, formatted, "{name}: formatter is not idempotent");
    }
    assert!(runs >= 5 && compared == runs);

    // Verify `[G3]` `■ auto` inferred contracts for `chorus`, `fetch_twice`, and `forward_fetch`.
    let src = files
        .iter()
        .find(|(n, _)| n == "tasks_and_cancel.rails")
        .map(|(_, s)| s.as_str())
        .expect("tasks_and_cancel.rails");
    let elab = surface::elaborate(src).expect("elaborate tasks_and_cancel.rails");
    let typed = resolve::resolve(&elab).expect("resolve tasks_and_cancel.rails");
    let chorus = &typed.controls[typed.control("chorus").expect("chorus")];
    assert_eq!(chorus.contract.len(), 1);
    assert_eq!(chorus.contract[0].name, "finished");
    let fwd = &typed.controls[typed.control("forward_fetch").expect("forward_fetch")];
    let fwd_names: Vec<&str> = fwd.contract.iter().map(|a| a.name.as_str()).collect();
    assert_eq!(fwd_names, vec!["cancelled", "ok"]);
}

#[test]
fn slice_four_core_well_formedness_refusals() {
    let rejecting: &[(&str, &str)] = &[
        // [W10]: `await` in a synchronous control
        (
            "W10",
            r#"
async control leaf() ■ { ok {} }
    1 ⊤ ▷ ■ ok {}
control sync_bad() ■ { ok {} }
    1 ⊤ ▷ d : Δ await leaf() ▸ ok {}
    2 d.ok ▷ ■ ok {}
"#,
        ),
        // [W10]: `run` in an `async control`
        (
            "W10",
            r#"
async control leaf() ■ { ok {} }
    1 ⊤ ▷ ■ ok {}
async control async_bad() ■ { ok {} }
    1 ⊤ ▷ d : Δ run leaf() ▸ ok {}
    2 d.ok ▷ ■ ok {}
"#,
        ),
        // [W10]: calling an `async control` synchronously without `await` or `run`
        (
            "W10",
            r#"
async control leaf() ■ { ok {} }
    1 ⊤ ▷ ■ ok {}
control sync_bad() ■ { ok {} }
    1 ⊤ ▷ d : Δ leaf() ▸ ok {}
    2 d.ok ▷ ■ ok {}
"#,
        ),
        // [W10]: `await` on a non-async control
        (
            "W10",
            r#"
control plain() ■ { ok {} }
    1 ⊤ ▷ ■ ok {}
async control bad() ■ { ok {} }
    1 ⊤ ▷ d : Δ await plain() ▸ ok {}
    2 d.ok ▷ ■ ok {}
"#,
        ),
        // [W10]: `spawn` in a synchronous control
        (
            "W10",
            r#"
async control leaf() ■ { ok {} }
    1 ⊤ ▷ ■ ok {}
control bad() ■ { ok {} }
    1 ⊤ ▷ ~p : tasks⟨leaf⟩ := tasks⟨leaf⟩()
    2 ⊤ ▷ ■ ok {}
"#,
        ),
        // [W10]: `contingent async control` is forbidden
        (
            "W10",
            r#"
contingent async control bad() ■ { ok {} }
    1 ⊤ ▷ ■ ok {}
"#,
        ),
        // [W10]: `spawn` of an `extern async control` (not defined)
        (
            "W10",
            r#"
extern async control io_op() ■ { ok {} } uses io.net
async control bad() ■ { ok {} } uses io.net
    1 ⊤ ▷ ~p : tasks⟨io_op⟩ := tasks⟨io_op⟩()
    2 ⊤ ▷ ■ ok {}
"#,
        ),
        // [W11]: immutable task set binding
        (
            "W11",
            r#"
async control leaf() ■ { ok {} }
    1 ⊤ ▷ ■ ok {}
async control bad() ■ { ok {} }
    1 ⊤ ▷ p : tasks⟨leaf⟩ := tasks⟨leaf⟩()
    2 ⊤ ▷ ■ ok {}
"#,
        ),
        // [W11]: `tasks⟨f⟩` as a parameter type
        (
            "W11",
            r#"
async control leaf() ■ { ok {} }
    1 ⊤ ▷ ■ ok {}
async control bad(p : tasks⟨leaf⟩) ■ { ok {} }
    1 ⊤ ▷ ■ ok {}
"#,
        ),
        // [W11]: `tasks⟨f⟩` as a struct field
        (
            "W11",
            r#"
async control leaf() ■ { ok {} }
    1 ⊤ ▷ ■ ok {}
struct bag { p : tasks⟨leaf⟩ }
control noop() ■ { ok {} }
    1 ⊤ ▷ ■ ok {}
"#,
        ),
        // [W11]: `capture await next(x)` is forbidden (second-review repair)
        (
            "W11",
            r#"
async control leaf() ■ { ok {} }
    1 ⊤ ▷ ■ ok {}
async control bad() ■ { ok {} }
    1 ⊤ ▷ ~p : tasks⟨leaf⟩ := tasks⟨leaf⟩()
    2 ⊤ ▷ c := capture await next(p)
    3 ⊤ ▷ ■ ok {}
"#,
        ),
        // [W12]: `cancelled` with payload is forbidden everywhere
        (
            "W12",
            r#"
extern async control bad() ■ { ok {} │ cancelled {code : u32} } uses io.net
control noop() ■ { ok {} }
    1 ⊤ ▷ ■ ok {}
"#,
        ),
        // [W12]: `cancelled` with condition on `extern async control` is forbidden
        (
            "W12",
            r#"
extern async control bad(x : u32) ■ { ok {} │ cancelled {} ⇐ x > 0 } uses io.net
control noop() ■ { ok {} }
    1 ⊤ ▷ ■ ok {}
"#,
        ),
        // [W12]: producer of `tasks⟨f⟩` cannot have an `empty` alternative
        (
            "W12",
            r#"
async control prod() ■ { ok {} │ empty {} }
    1 ⊤ ▷ ■ ok {}
async control bad() ■ { ok {} }
    1 ⊤ ▷ ~p : tasks⟨prod⟩ := tasks⟨prod⟩()
    2 ⊤ ▷ ■ ok {}
"#,
        ),
        // [TK1]: `spawn` producer mismatch
        (
            "TK1",
            r#"
async control f() ■ { ok {} }
    1 ⊤ ▷ ■ ok {}
async control g() ■ { ok {} }
    1 ⊤ ▷ ■ ok {}
async control bad() ■ { ok {} }
    1 ⊤ ▷ ~p : tasks⟨f⟩ := tasks⟨f⟩()
    2 ⊤ ▷ spawn g() into p
    3 ⊤ ▷ ■ ok {}
"#,
        ),
        // [TK1]: `count` on a non-task-set variable
        (
            "TK1",
            r#"
async control bad(x : u32) ■ { ok {v : usize} }
    1 ⊤ ▷ ■ ok {count(x)}
"#,
        ),
    ];

    for (idx, (expected_clause, src)) in rejecting.iter().enumerate() {
        let parsed = text::parse(src).unwrap_or_else(|e| panic!("case {idx} parse failed: {e}"));
        let err = resolve::resolve(&parsed)
            .expect_err(&format!("case {idx} should fail [{expected_clause}]"));
        assert_eq!(
            err.clause, *expected_clause,
            "case {idx}: expected [{expected_clause}], got [{}]: {}",
            err.clause, err.message
        );
    }
}

#[test]
fn slice_four_surface_refusals_and_purity_i10() {
    // [U19]: `tasks()` without `: tasks<f>` annotation
    let missing_annot = r#"
async control leaf() ■ ok
│ ■ ok
╵

async control bad() ■ ok
│ ~p := tasks()
│ ■ ok
╵
"#;
    let err = surface::elaborate(missing_annot).expect_err("tasks() without annotation must fail");
    assert_eq!(err.clause, "U19");

    // [W11]: `capture await next x` in surface
    let cap_next = r#"
async control leaf() ■ ok
│ ■ ok
╵

async control bad() ■ ok
│ ~p: tasks<leaf> := tasks()
│ c := capture await next p
│ ■ ok
╵
"#;
    let err = surface::elaborate(cap_next).expect_err("capture await next must fail");
    assert_eq!(err.clause, "W11");

    // [I10] (second-review repair): a control that supervises a named boundary
    // whose body runs an `async control` is NOT pure!
    let supervised_run_src = r#"
async control leaf() ■ { ok {} }
    1 ⊤ ▷ ■ ok {}

boundary b() {
    1 ⊤ ▷ d : Δ run leaf() ▸ ok {}
    2 d.ok ▷ terminate
} contingency (m : string) {
    1 ⊤ ▷ terminate
}

control supervises_run() ■ { ok {} }
    1 ⊤ ▷ supervise b()
    2 ⊤ ▷ ■ ok {}

control pure_ctrl(x : u32) ■ { ok {v : u32} }
    1 ⊤ ▷ ■ ok {x + 1}
"#;
    let parsed = text::parse(supervised_run_src).expect("parse I10 test");
    let typed = resolve::resolve(&parsed).expect("resolve I10 test");
    let leaf_id = typed.control("leaf").unwrap();
    let sup_id = typed.control("supervises_run").unwrap();
    let pure_id = typed.control("pure_ctrl").unwrap();
    assert!(!typed.control_is_pure(leaf_id), "async control is not pure");
    assert!(
        !typed.control_is_pure(sup_id),
        "control supervising a boundary with `run` is not pure ([I10])"
    );
    assert!(typed.control_is_pure(pure_id), "pure_ctrl is pure");
}

#[test]
fn slice_four_await_host_checks_precondition_before_cancel_shortcut() {
    // Second-review repair on [E-AwaitHost]: precondition and effect checks
    // run BEFORE the `cancelled` shortcut.
    let src = r#"
extern async control positive_io(x : u32) ⊢ x > 0 ■ { done {} │ cancelled {} } uses io.net

async control worker(x : u32) ■ { done {} │ cancelled {} } uses io.net
    1 ⊤ ▷ w : Δ await positive_io(x) ▸ done {} │ cancelled {}
    2 w.done ▷ ■ done {}
    3 w.cancelled ▷ ■ cancelled {}

control entry(x : u32) ■ { done {} │ cancelled {} } uses io.net
    1 ⊤ ▷ d : Δ run worker(x) ▸ done {} │ cancelled {}
    2 d.done ▷ ■ done {}
    3 d.cancelled ▷ ■ cancelled {}
"#;
    let parsed = text::parse(src).expect("parse");
    let typed = resolve::resolve(&parsed).expect("resolve");
    let mut host = Scheduled::new(Script {
        answers: VecDeque::from([(
            "positive_io".to_string(),
            Answer {
                alternative: "done".to_string(),
                payload: Vec::new(),
                writes: Vec::new(),
            },
        )]),
    });
    host.cancel_at_turn = Some(1);
    let run = oracle::run(
        &typed,
        "entry",
        vec![Value::Int(Int::from_u64(0))],
        &mut host,
        &Config::default(),
    );
    match run.end {
        End::Stuck(s) => {
            assert_eq!(s.state, 7);
            assert_eq!(s.clause, "E-Extern");
        }
        other => panic!("expected X7 E-Extern before cancel shortcut, got {other}"),
    }
}
