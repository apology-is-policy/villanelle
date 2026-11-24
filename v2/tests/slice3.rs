//! Slice 3 Phase 2 conformance tests: second-class borrows, views, borrow tags
//! `[B1]`–`[B5]`, `[E-Outcome]` variant borrows, `[E-Host]` borrow checks,
//! core well-formedness (`[W5a]`, `[W6]`, `[W8]`, `[W9]`, `[T1]`, `[T4]`, `[T6]`,
//! `[F5]`, `[F6]`), Rails elaboration (`[G3]`, `[G8]`, `[G10]`, `[U6]`, `[U9]`,
//! `[U10]`, `[U11]`, Q16), and oracle-vs-erased differential agreement.

use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;
use villanelle_v2::host::{Answer, Host};
use villanelle_v2::int::Int;
use villanelle_v2::oracle::{self, Config, End, RuntimePlace, Value};
use villanelle_v2::typed::{BorrowMode, Control, Kind};
use villanelle_v2::{resolve, script, surface, text};

fn core_files() -> Vec<(String, String)> {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/slice3");
    let mut files = Vec::new();
    for entry in std::fs::read_dir(&root).expect("tests/slice3") {
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
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/slice3_surface");
    let mut files = Vec::new();
    for entry in std::fs::read_dir(&root).expect("tests/slice3_surface") {
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

/// The rules of section 6 that the borrows of slice 3 apply.
const SLICE3_RULES: [&str; 13] = [
    "B1",
    "B2",
    "B3",
    "B4",
    "B5",
    "E-Borrow",
    "E-Operands",
    "E-Outcome",
    "E-Extern",
    "E-Var",
    "E-Field",
    "E-Index",
    "E-Assign",
];

/// The ways of being stuck that the suite of slice 3 reaches.
const SLICE3_STUCK: [&str; 3] = ["X4 B1", "X2 E-Var", "X7 E-Index"];

/// The clauses by which `resolve` refuses a core file of the suite.
const SLICE3_REFUSALS: [&str; 1] = ["C1"];

/// The rule files of the borrows: a dead borrow in each says what ended it,
/// and the cause is the clause that the run is about ([B2] to [B5]).
const RULE_FILES: [&str; 8] = [
    "b1_access.core",
    "b2_invalidation.core",
    "b3_creation.core",
    "b4_moves_and_scopes.core",
    "b5_shapes.core",
    "e_borrow_operands.core",
    "e_extern_writes.core",
    "e_views.core",
];

const READ: &str = "a read of its place";
const ASSIGNMENT: &str = "an assignment to its place";
const MOVE: &str = "a move of what it refers to";
const SHARED: &str = "a shared borrow of its place";
const EXCLUSIVE: &str = "an exclusive borrow of its place";
const SHAPE: &str = "a change of shape of its collection";
const SCOPE: &str = "the scope of what it refers to ended";
const HOST: &str = "a write of the host behind it";

/// For each run of the rule files that is stuck by a dead borrow: the file,
/// the control in which it is stuck, and what ended the borrow.
const DEATHS: [(&str, &str, &str); 40] = [
    ("b1_access.core", "read_through_dead", ASSIGNMENT),
    ("b1_access.core", "write_through_dead", READ),
    ("b1_access.core", "lend_through_dead", ASSIGNMENT),
    ("b1_access.core", "component_through_dead", ASSIGNMENT),
    ("b1_access.core", "formula_through_dead", ASSIGNMENT),
    ("b1_access.core", "formula_through_gone", EXCLUSIVE),
    ("b1_access.core", "shows", ASSIGNMENT),
    ("b1_access.core", "condition_through_dead", ASSIGNMENT),
    ("b2_invalidation.core", "read_kills_exclusive", READ),
    ("b2_invalidation.core", "write_kills_shared", ASSIGNMENT),
    ("b2_invalidation.core", "parent_kills_child", ASSIGNMENT),
    ("b2_invalidation.core", "descendants_die", ASSIGNMENT),
    ("b2_invalidation.core", "whole_kills_part", ASSIGNMENT),
    ("b2_invalidation.core", "part_kills_whole", ASSIGNMENT),
    ("b2_invalidation.core", "element_kills_element", ASSIGNMENT),
    ("b2_invalidation.core", "whole_read_kills_part", READ),
    ("b3_creation.core", "shared_kills_exclusive", SHARED),
    ("b3_creation.core", "exclusive_kills_shared", EXCLUSIVE),
    ("b3_creation.core", "exclusive_kills_exclusive", EXCLUSIVE),
    ("b3_creation.core", "write_kills_shared_child", ASSIGNMENT),
    (
        "b3_creation.core",
        "whole_kills_component_child",
        ASSIGNMENT,
    ),
    ("b4_moves_and_scopes.core", "move_kills_borrow", MOVE),
    ("b4_moves_and_scopes.core", "move_kills_component", MOVE),
    (
        "b4_moves_and_scopes.core",
        "assign_kills_borrow",
        ASSIGNMENT,
    ),
    ("b4_moves_and_scopes.core", "copies_share_a_tag", ASSIGNMENT),
    ("b4_moves_and_scopes.core", "leaves_a_local", SCOPE),
    ("b4_moves_and_scopes.core", "goes_round_with_a_local", SCOPE),
    ("b4_moves_and_scopes.core", "returns_a_local", SCOPE),
    ("b4_moves_and_scopes.core", "reads_a_dead_payload", SCOPE),
    ("b5_shapes.core", "push_kills_element", SHAPE),
    ("b5_shapes.core", "pop_kills_element", SHAPE),
    ("b5_shapes.core", "insert_kills_entry", SHAPE),
    ("b5_shapes.core", "remove_kills_entry", SHAPE),
    ("e_borrow_operands.core", "copy_from", SHARED),
    (
        "e_borrow_operands.core",
        "function_read_ends_exclusive",
        READ,
    ),
    ("e_borrow_operands.core", "read_ends_fields", READ),
    ("e_extern_writes.core", "write_ends_a_borrow", HOST),
    ("e_views.core", "field_through_dead", ASSIGNMENT),
    (
        "borrows_and_tags.core",
        "stuck_push_kills_elem_borrow",
        EXCLUSIVE,
    ),
    ("views_and_variants.core", "stuck_dangling_view", SCOPE),
];

#[test]
fn slice_three_core_conforms_and_matches_erased() {
    let files = core_files();
    let mut failures = Vec::new();
    let mut rules: BTreeMap<&str, u64> = BTreeMap::new();
    let mut stuck = BTreeSet::new();
    let mut refusals = BTreeSet::new();
    let mut details: BTreeMap<(String, String), BTreeSet<String>> = BTreeMap::new();
    let mut runs = 0usize;
    let mut compared = 0usize;
    for (name, source) in &files {
        let report = script::check(source);
        if report.runs == 0 && report.rejected.is_none() && report.failures.is_empty() {
            failures.push(format!("{name}: no directives"));
        }
        for failure in &report.failures {
            failures.push(format!("{name}: {failure}"));
        }
        runs += report.runs;
        compared += report.compared;
        for (rule, count) in report.rules {
            *rules.entry(rule).or_insert(0) += count;
        }
        stuck.extend(report.stuck);
        refusals.extend(report.rejected);
        for (control, said) in report.stuck_details {
            details.insert((name.clone(), control), said);
        }
    }
    for rule in SLICE3_RULES {
        if !rules.contains_key(rule) {
            failures.push(format!("no slice 3 run applied [{rule}]"));
        }
    }
    for state in SLICE3_STUCK {
        if !stuck.contains(state) {
            failures.push(format!("no slice 3 run reached stuck state {state}"));
        }
    }
    for clause in SLICE3_REFUSALS {
        if !refusals.contains(clause) {
            failures.push(format!("no slice 3 core file was refused by [{clause}]"));
        }
    }
    // Each dead borrow was ended by the access that its run is about.
    for (file, control, cause) in DEATHS {
        let said = details
            .get(&(file.to_string(), control.to_string()))
            .cloned()
            .unwrap_or_default();
        if !said.iter().any(|detail| detail.contains(cause)) {
            failures.push(format!(
                "{file}: `{control}` is not stuck because {cause}: {said:?}"
            ));
        }
    }
    // And every dead borrow of the rule files is in the table.
    for ((file, control), said) in &details {
        let listed = DEATHS.iter().any(|(f, c, _)| f == file && c == control);
        if RULE_FILES.contains(&file.as_str())
            && said
                .iter()
                .any(|detail| detail.contains("the borrow is dead"))
            && !listed
        {
            failures.push(format!(
                "{file}: `{control}` is stuck by a dead borrow not in DEATHS"
            ));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    assert!(runs >= 143, "{runs} runs");
    // Every run that is not stuck and has a host that answers is compared
    // with the erased semantics ([R4], [R5]).
    assert!(compared >= 73 && compared < runs, "{compared} compared");
}

#[test]
fn slice_three_core_printer_and_reader_agree() {
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
fn slice_three_surface_files_run_format_and_match_erased() {
    let files = surface_files();
    assert!(!files.is_empty(), "expected slice 3 surface test files");
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
    assert!(runs >= 10 && compared == runs);

    // Verify `[G3]` `■ auto` inferred `∈ a, b` on private `shorter` in `borrows_and_variants.rails`.
    let borrows_src = files
        .iter()
        .find(|(n, _)| n == "borrows_and_variants.rails")
        .map(|(_, s)| s.as_str())
        .expect("borrows_and_variants.rails");
    let elab = surface::elaborate(borrows_src).expect("elaborate borrows_and_variants.rails");
    let typed = resolve::resolve(&elab).expect("resolve borrows_and_variants.rails");
    let shorter_id = typed.control("shorter").expect("shorter control");
    let shorter_ok = &typed.controls[shorter_id].contract[0];
    assert_eq!(shorter_ok.fields[0].origins, vec![0, 1]);
}

#[test]
fn slice_three_core_well_formedness_and_kinds() {
    // Verify `[T1]` view struct kinds: `window` is Copy, `tail` is Drop.
    let views_src = r#"
view struct window {items : &[u32], start : usize, stop : usize}
view struct tail {items : &~[u32], from : usize}
control noop() ■ { ok {} }
    1 ⊤ ▷ ■ ok {}
"#;
    let parsed = text::parse(views_src).expect("parse views");
    let typed = resolve::resolve(&parsed).expect("resolve views");
    assert_eq!(typed.structs[0].kind, Kind::Copy);
    assert_eq!(typed.structs[1].kind, Kind::Drop);

    let rejecting: &[(&str, &str)] = &[
        // [W5a]: function taking exclusive borrow
        (
            "W5a",
            r#"
function bad(x : &~u32) : u32 := x
"#,
        ),
        // [W5a]: function taking exclusive view
        (
            "W5a",
            r#"
view struct tail {items : &~[u32], from : usize}
function bad(t : tail) : usize := t.from
"#,
        ),
        // [W5a]: function returning a borrow
        (
            "W5a",
            r#"
function bad(x : &u32) : &u32 := x
"#,
        ),
        // [W5a]: function returning a view
        (
            "W5a",
            r#"
view struct window {items : &[u32], start : usize, stop : usize}
function bad(w : window) : window := w
"#,
        ),
        // [W6]: borrow inside ordinary struct
        (
            "W6",
            r#"
struct bad {r : &u32}
"#,
        ),
        // [W6]: view inside ordinary struct
        (
            "W6",
            r#"
view struct window {items : &[u32], start : usize, stop : usize}
struct bad {w : window}
"#,
        ),
        // [W6]: borrow inside variant
        (
            "W6",
            r#"
variant bad {a {r : &u32}}
"#,
        ),
        // [W6]: borrow inside vector
        (
            "W6",
            r#"
control bad(xs : [&u32]) ■ { ok {} }
    1 ⊤ ▷ ■ ok {}
"#,
        ),
        // [W6]: borrow of a borrow
        (
            "W6",
            r#"
control bad(x : &&u32) ■ { ok {} }
    1 ⊤ ▷ ■ ok {}
"#,
        ),
        // [W6]: borrow of a view
        (
            "W6",
            r#"
view struct window {items : &[u32], start : usize, stop : usize}
control bad(w : &window) ■ { ok {} }
    1 ⊤ ▷ ■ ok {}
"#,
        ),
        // [W6]: view struct with owned drop field
        (
            "W6",
            r#"
view struct bad {label : string, items : &[u32]}
"#,
        ),
        // [W8]: mutable borrow binding
        (
            "W8",
            r#"
control bad() ■ { ok {} }
    1 ⊤ ▷ x : u32 := 1
    2 ⊤ ▷ ~r : &u32 := &x
    3 ⊤ ▷ ■ ok {}
"#,
        ),
        // [W8]: mutable view binding
        (
            "W8",
            r#"
view struct window {items : &[u32], start : usize, stop : usize}
control bad() ■ { ok {} }
    1 ⊤ ▷ xs : [u32] := [1]
    2 ⊤ ▷ ~w : window := window {&xs, 0, 1}
    3 ⊤ ▷ ■ ok {}
"#,
        ),
        // [W8]: assigning to a view binding
        (
            "W8",
            r#"
view struct window {items : &[u32], start : usize, stop : usize}
control bad() ■ { ok {} }
    1 ⊤ ▷ xs : [u32] := [1]
    2 ⊤ ▷ w : window := window {&xs, 0, 1}
    3 ⊤ ▷ w ← window {&xs, 0, 1}
    4 ⊤ ▷ ■ ok {}
"#,
        ),
        // [W9]: borrowed payload field without `∈`
        (
            "W9",
            r#"
control bad(x : &u32) ■ { ok {out : &u32} }
    1 ⊤ ▷ ■ ok {x}
"#,
        ),
        // [W9]: view payload field without `∈`
        (
            "W9",
            r#"
view struct window {items : &[u32], start : usize, stop : usize}
control bad(xs : &[u32]) ■ { ok {w : window} }
    1 ⊤ ▷ ■ ok {window {xs, 0, 0}}
"#,
        ),
        // [T4]: owned payload field with `∈`
        (
            "T4",
            r#"
control bad(x : &u32) ■ { ok {out : u32 ∈ x} }
    1 ⊤ ▷ ■ ok {x}
"#,
        ),
        // [T4]: origin parameter is owned, not borrow/view
        (
            "T4",
            r#"
control bad(x : u32) ■ { ok {out : &u32 ∈ x} }
    1 ⊤ ▷ ■ ok {&x}
"#,
        ),
        // [T4]: exclusive payload originating from shared parameter
        (
            "T4",
            r#"
control bad(x : &u32) ■ { ok {out : &~u32 ∈ x} }
    1 ⊤ ▷ ■ ok {x}
"#,
        ),
        // [T6]: outcome declaration with borrow payload
        (
            "T6",
            r#"
outcome bad { ok {r : &u32} }
"#,
        ),
        // [T6]: outcome declaration with view payload
        (
            "T6",
            r#"
view struct window {items : &[u32], start : usize, stop : usize}
outcome bad { ok {w : window} }
"#,
        ),
        // [T6]: capturing an operation with borrowed payload
        (
            "T6",
            r#"
control id(x : &u32) ■ { ok {r : &u32 ∈ x} }
    1 ⊤ ▷ ■ ok {x}
control bad() ■ { ok {} }
    1 ⊤ ▷ n : u32 := 1
    2 ⊤ ▷ c := capture id(&n)
    3 ⊤ ▷ ■ ok {}
"#,
        ),
        // [F5]: lexical boundary capturing a borrow
        (
            "F5",
            r#"
control bad() ■ { ok {} }
    1 ⊤ ▷ n : u32 := 1
    2 ⊤ ▷ r : &u32 := &n
    3 ⊤ ▷ b : boundary {
        1 ⊤ ▷ fault "boom"
    } contingency [r] (m : string) {
        1 ⊤ ▷ terminate 1
    }
    4 ⊤ ▷ ■ ok {}
"#,
        ),
        // [F6]: named boundary with borrow parameter
        (
            "F6",
            r#"
boundary bad(r : &u32) {
    1 ⊤ ▷ terminate
} contingency(m : string) {
    1 ⊤ ▷ terminate
}
"#,
        ),
        // [F6]: named boundary with view parameter
        (
            "F6",
            r#"
view struct window {items : &[u32], start : usize, stop : usize}
boundary bad(w : window) {
    1 ⊤ ▷ terminate
} contingency(m : string) {
    1 ⊤ ▷ terminate
}
"#,
        ),
    ];

    for (idx, (expected_clause, src)) in rejecting.iter().enumerate() {
        let parsed = text::parse(src)
            .unwrap_or_else(|e| panic!("case {idx} ({expected_clause}) failed to parse: {e}"));
        match resolve::resolve(&parsed) {
            Ok(_) => panic!("case {idx} ({expected_clause}) unexpectedly resolved"),
            Err(err) => assert_eq!(
                err.clause, *expected_clause,
                "case {idx} expected clause {expected_clause}, got {}: {}",
                err.clause, err.message
            ),
        }
    }
}

#[test]
fn slice_three_surface_clauses_and_q16() {
    // [G8] ASCII `in` / `from` for `∈` parses and formats canonically to `∈` ([G10]).
    let ascii_src = r#"
pub view struct window {items: &vector<u32>, start: usize, stop: usize}

pub control widest(a: &string, b: &string) exits ok {out: &string in a, b} {
    if len(a) >= len(b) => exit ok {a}
    exit ok {b}
}

pub control first_ref(xs: &vector<u32>) exits ok {w: window from xs} {
    exit ok {window {xs, 0, len(xs)}}
}
"#;
    let formatted = surface::format(ascii_src).expect("format ASCII slice 3");
    assert!(
        formatted.contains("pub view struct window {items: &[u32], start: usize, stop: usize}")
    );
    assert!(formatted.contains("ok {out: &string ∈ a, b}"));
    assert!(formatted.contains("ok {w: window ∈ xs}"));
    let elab = surface::elaborate(&formatted).expect("elaborate formatted");
    let _typed = resolve::resolve(&elab).expect("resolve formatted");

    // Rejecting surface cases: Q16 bare `&~` name, missing `~` in bind / view / loop / again.
    let rejecting: &[(&str, &str)] = &[
        // Q16 ([U11]): passing bare exclusive borrow `r` where `&~u32` is expected
        (
            "U11",
            r#"
control bump(x: &~u32) ■ done
│ x ← x + 1
│ ■ done
╵

control bad() ■ done
│ ~n: u32 := 1
│ r: &~u32 := ~n
│ bump(r)
│ ■ done
╵
"#,
        ),
        // [U11]: missing `~` on `&~` local bind
        (
            "U11",
            r#"
control bad() ■ done
│ ~n: u32 := 1
│ r: &~u32 := n
│ ■ done
╵
"#,
        ),
        // [U11]: missing `~` inside a view constructor
        (
            "U11",
            r#"
view struct tail {items: &~[u32], from: usize}

control bad() ■ done
│ ~xs: [u32] := [1, 2]
│ t: tail := tail {xs, 1}
│ ■ done
╵
"#,
        ),
        // [U11]: missing `~` on loop parameter initial expression
        (
            "U11",
            r#"
control bad() ■ done
│ ~n: u32 := 1
│ ↻ lp(r: &~u32 := n)
│ ║ □
│ ■ done
╵
"#,
        ),
        // [U11]: missing `~` on `↑` loop step argument
        (
            "U11",
            r#"
control bad() ■ done
│ ~n: u32 := 1
│ ↻ lp(r: &~u32 := ~n)
│ ║ ↑ lp(r)
│ ■ done
╵
"#,
        ),
    ];

    for (idx, (expected_clause, src)) in rejecting.iter().enumerate() {
        match surface::elaborate(src) {
            Ok(_) => panic!("surface case {idx} ({expected_clause}) unexpectedly elaborated"),
            Err(err) => assert_eq!(
                err.clause, *expected_clause,
                "surface case {idx} expected {expected_clause}, got {}: {}",
                err.clause, err.message
            ),
        }
    }
}

#[test]
fn slice_three_host_borrow_violation_e_host() {
    // [E-Host]: an extern control whose host returns a non-borrow for a borrowed
    // payload field or a borrow with a dead/unowned tag ends in `HostViolation`.
    let src = r#"
extern control ext_pick(a : &u32)
    ■ { ok {out : &u32 ∈ a} }

control caller()
    ■ { ok {v : u32} }
    1 ⊤ ▷ n : u32 := 7
    2 ⊤ ▷ d : Δ ext_pick(&n) ▸ ok {r}
    3 ⊤ ▷ ■ ok {r}
"#;
    let parsed = text::parse(src).expect("parse");
    let program = resolve::resolve(&parsed).expect("resolve");

    struct BadNonBorrowHost;
    impl Host for BadNonBorrowHost {
        fn call(
            &mut self,
            _control: &Control,
            _args: &[Value],
            _cfg: &Config,
        ) -> Result<Answer, String> {
            Ok(Answer {
                alternative: "ok".to_string(),
                payload: vec![Value::Int(Int::from_u64(7))],
                writes: Vec::new(),
            })
        }
    }
    let res1 = oracle::run(
        &program,
        "caller",
        Vec::new(),
        &mut BadNonBorrowHost,
        &Config::default(),
    );
    assert!(
        matches!(res1.end, End::HostViolation(_)),
        "expected HostViolation for non-borrow answer, got {}",
        res1.end
    );

    struct BadDanglingTagHost;
    impl Host for BadDanglingTagHost {
        fn call(
            &mut self,
            _control: &Control,
            _args: &[Value],
            _cfg: &Config,
        ) -> Result<Answer, String> {
            Ok(Answer {
                alternative: "ok".to_string(),
                payload: vec![Value::Ref {
                    mode: BorrowMode::Shared,
                    place: RuntimePlace::root(999, 0),
                    tag: 999,
                }],
                writes: Vec::new(),
            })
        }
    }
    let res2 = oracle::run(
        &program,
        "caller",
        Vec::new(),
        &mut BadDanglingTagHost,
        &Config::default(),
    );
    assert!(
        matches!(res2.end, End::HostViolation(_)),
        "expected HostViolation for dead/wrong-origin borrow tag, got {}",
        res2.end
    );
}

#[test]
fn the_seeded_host_answers_borrowed_payloads_with_places_within_its_arguments() {
    // [E-Extern]: a host names a place within an origin, and both semantics
    // make the same borrow of it. The controls are those of
    // `host_borrows.core`, which the scripted host answers there.
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/slice3/host_borrows.core");
    let source = std::fs::read_to_string(root).expect("host_borrows.core");
    let program = villanelle_v2::load(&source).expect("resolved");
    let config = Config::default();
    let mut ended = std::collections::BTreeMap::new();
    for seed in 0..60u64 {
        for (entry, arguments) in [
            ("reads", vec![Value::Int(Int::from_i128(8))]),
            ("writes", Vec::new()),
            ("picks", Vec::new()),
            ("picks_first", Vec::new()),
            ("splits", Vec::new()),
            ("spans", Vec::new()),
        ] {
            let mut host = villanelle_v2::host::Seeded::new(&program, seed);
            let outcome = villanelle_v2::differential::compare(
                &program, entry, arguments, &mut host, &config,
            );
            assert!(
                matches!(outcome.oracle.end, End::Done { .. }),
                "seed {seed}: `{entry}` ended in `{}`",
                outcome.oracle.end
            );
            assert_eq!(
                outcome.verdict,
                villanelle_v2::differential::Verdict::Same,
                "seed {seed}: `{entry}` differed"
            );
            ended
                .entry(entry)
                .or_insert_with(std::collections::BTreeSet::new)
                .insert(format!("{}", outcome.oracle.end));
        }
    }
    // The host chooses among the places: each control that has a choice
    // ends in more than one way over the seeds.
    for entry in ["reads", "writes", "picks", "splits", "spans"] {
        assert!(ended[entry].len() > 1, "`{entry}` ended one way only");
    }
}

/// RO11: the native driver answers a borrowed payload with a cell of its own
/// and writes nothing behind an argument (RO6), so the runs whose host writes
/// are left out of the compiled runs of a file rather than compiled with the
/// write lost. Of the six runs of `e_extern_writes.core` that end, one has a
/// host that writes nothing.
#[test]
fn runs_whose_host_writes_are_left_out_of_compiled_code_ro11() {
    let source = include_str!("slice3/e_extern_writes.core");
    let (_, specs) = script::native_runs(source).expect("the runs of the file");
    let entries: Vec<&str> = specs.iter().map(|spec| spec.entry.as_str()).collect();
    assert_eq!(entries, ["renames"]);
    assert!(
        specs[0]
            .answers
            .iter()
            .all(|(_, answer)| answer.writes.is_empty())
    );
}
