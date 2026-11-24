//! Slice 2 Phase 4 conformance, differential, and paired native-performance
//! tests for Theorem 4 expansion (`expand`) and the typed LLVM IR + C ABI
//! backend (`codegen`).

use std::collections::HashSet;
use std::path::PathBuf;
use std::process::Command as ProcessCommand;
use villanelle_v2::codegen::{
    NativeRunSpec, emit_c_header, emit_llvm, emit_native_harness_llvm, run_native_batch,
    run_native_ir,
};
use villanelle_v2::host::{Answer, Script};
use villanelle_v2::int::Int;
use villanelle_v2::oracle::{Config, End, Value, run};
use villanelle_v2::syntax::{Command as SynCommand, Declaration, Statement as SynStatement};
use villanelle_v2::{check, erased, expand, resolve, script, surface, text};

fn slice2_surface_files() -> Vec<(String, String)> {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/slice2_surface");
    let mut out = Vec::new();
    for entry in std::fs::read_dir(&root).expect("tests/slice2_surface") {
        let path = entry.expect("an entry").path();
        if path.extension().is_some_and(|ext| ext == "rails") {
            let name = path
                .file_name()
                .expect("a file name")
                .to_string_lossy()
                .into_owned();
            out.push((name, std::fs::read_to_string(&path).expect("readable")));
        }
    }
    out.sort();
    out
}

fn assert_no_expandable_defined_calls(tree: &villanelle_v2::syntax::Program) {
    let defined: HashSet<String> = tree
        .declarations
        .iter()
        .filter_map(|d| match d {
            Declaration::Control(c) if !c.external => Some(c.name.clone()),
            _ => None,
        })
        .collect();

    fn check_stmts(stmts: &[SynStatement], defined: &HashSet<String>) {
        for s in stmts {
            match &s.command {
                SynCommand::Decide { operation, .. } => {
                    assert!(
                        !defined.contains(operation),
                        "expanded body still contains expandable call to defined control `{operation}`"
                    );
                }
                SynCommand::Loop { body, .. } => check_stmts(body, defined),
                SynCommand::Boundary {
                    body, contingency, ..
                } => {
                    check_stmts(body, defined);
                    check_stmts(contingency, defined);
                }
                _ => {}
            }
        }
    }

    for decl in &tree.declarations {
        match decl {
            Declaration::Control(c) if !c.external => check_stmts(&c.body, &defined),
            Declaration::Boundary(b) => {
                check_stmts(&b.body, &defined);
                check_stmts(&b.contingency, &defined);
            }
            _ => {}
        }
    }
}

fn verify_native_specs(
    label: &str,
    program: &villanelle_v2::typed::Program,
    specs: &[NativeRunSpec],
    usize_bits: u32,
) {
    let config = Config {
        usize_max: Int::power_of_two(usize_bits).minus(&Int::from_u64(1)),
        fuel: 200_000,
    };

    let mut expected = Vec::with_capacity(specs.len());
    for (idx, spec) in specs.iter().enumerate() {
        let mut o_host = Script {
            answers: spec.answers.iter().cloned().collect(),
        };
        let mut e_host = Script {
            answers: spec.answers.iter().cloned().collect(),
        };
        let oracle_out = run(
            program,
            &spec.entry,
            spec.arguments.clone(),
            &mut o_host,
            &config,
        );
        let erased_out = erased::run(
            program,
            &spec.entry,
            spec.arguments.clone(),
            &mut e_host,
            &config,
        );
        let expected_end = match &oracle_out.end {
            End::Done {
                alternative,
                payload,
            } => erased::End::Done {
                alternative: alternative.clone(),
                payload: payload.clone(),
            },
            End::Faulted(msg) => erased::End::Faulted(msg.clone()),
            End::Terminated(status) => erased::End::Terminated(*status),
            other => panic!(
                "{label} run {idx} ({}, usize={usize_bits}) did not finish cleanly in oracle: {other}",
                spec.entry
            ),
        };
        assert_eq!(
            format!("{}", erased_out.end),
            format!("{expected_end}"),
            "{label} run {idx} ({}, usize={usize_bits}): oracle vs erased outcome mismatch",
            spec.entry
        );
        assert_eq!(
            erased_out.trace, oracle_out.trace,
            "{label} run {idx} ({}, usize={usize_bits}): oracle vs erased trace mismatch",
            spec.entry
        );
        expected.push((expected_end, oracle_out.trace));
    }

    let native_o0 = run_native_batch(program, specs, usize_bits, 0)
        .unwrap_or_else(|e| panic!("{label} (usize={usize_bits}, -O0) failed:\n{e}"));
    let native_o2 = run_native_batch(program, specs, usize_bits, 2)
        .unwrap_or_else(|e| panic!("{label} (usize={usize_bits}, -O2) failed:\n{e}"));

    assert_eq!(native_o0.len(), expected.len(), "{label} -O0 count");
    assert_eq!(native_o2.len(), expected.len(), "{label} -O2 count");

    for (i, ((exp_end, exp_trace), ((o0_end, o0_tr), (o2_end, o2_tr)))) in expected
        .iter()
        .zip(native_o0.iter().zip(native_o2.iter()))
        .enumerate()
    {
        assert_eq!(
            format!("{o0_end}"),
            format!("{exp_end}"),
            "{label} run {i} ({}, usize={usize_bits}): native -O0 outcome mismatch",
            specs[i].entry
        );
        assert_eq!(
            o0_tr, exp_trace,
            "{label} run {i} ({}, usize={usize_bits}): native -O0 trace mismatch",
            specs[i].entry
        );
        assert_eq!(
            format!("{o2_end}"),
            format!("{exp_end}"),
            "{label} run {i} ({}, usize={usize_bits}): native -O2 outcome mismatch",
            specs[i].entry
        );
        assert_eq!(
            o2_tr, exp_trace,
            "{label} run {i} ({}, usize={usize_bits}): native -O2 trace mismatch",
            specs[i].entry
        );
    }
}

fn u32_val(v: u32) -> Value {
    Value::Int(Int::from_u64(u64::from(v)))
}

fn res_val(name: &str, id: u64) -> Value {
    Value::Resource {
        ty: 0,
        name: name.to_string(),
        id,
    }
}

fn ans(alt: &str, payload: Vec<Value>) -> Answer {
    Answer {
        alternative: alt.to_string(),
        payload,
    }
}

#[test]
fn slice_two_theorem_4_expansion_preserves_checking_and_semantics() {
    // 1. All 4 Slice 2 `.rails` files expand, re-parse, check with kernel-validated
    //    certificates, and pass every `//! run` directive identically.
    for (name, source) in slice2_surface_files() {
        let tree = surface::elaborate(&source).unwrap();
        let expanded = expand::expand(&tree).unwrap();
        assert_no_expandable_defined_calls(&expanded);

        let printed = expanded.print();
        let reparsed = text::parse(&printed)
            .unwrap_or_else(|e| panic!("{name}: expanded core failed to re-parse: {e}\n{printed}"));
        let resolved = resolve::resolve(&reparsed)
            .unwrap_or_else(|e| panic!("{name}: expanded core failed to resolve: {e}\n{printed}"));
        let checked = check::check(&resolved)
            .unwrap_or_else(|e| panic!("{name}: expanded core failed check: {e}\n{printed}"));
        checked.revalidate().unwrap();

        let directives_tail: Vec<&str> = source
            .lines()
            .filter(|l| {
                let t = l.trim_start();
                t.starts_with("//!") || t.starts_with("┄!")
            })
            .collect();
        let with_directives = format!("{printed}\n{}\n", directives_tail.join("\n"));
        let report = script::check(&with_directives);
        assert!(
            report.failures.is_empty(),
            "{name}: expanded directives failed: {:?}\n{with_directives}",
            report.failures
        );
    }

    // 2. Dedicated Slice 2 expansion case exercising `&τ` shared borrow (both
    //    place and rvalue temp), `&~τ` exclusive borrow + `old(y)` / `len(old(y))`
    //    postconditions, resources (`on fault release`), faults, and a named boundary.
    let borrow_and_fault_source = r#"
copy struct point {x: u32, y: u32}
struct labeled {tag: string, value: u32}

extern resource conn on fault release
extern control open_conn() ■ opened {c: conn} uses net
extern control close_conn(c: conn) ■ closed uses net

control read_labeled(item: &labeled) ■ ok {v: u32} ⇐ v = item.value
│ ■ ok {item.value}
╵

control read_str(s: &string) ■ ok {n: usize} ⇐ n = len(s)
│ ■ ok {len(s)}
╵

control push_point(pts: &~[point], p: point)
    ■ pushed ⇐ len(pts) = len(old(pts)) + 1
│ pts.push(p)
│ ■ pushed
╵

control with_conn(fail_now: bool) ■ ok faults uses net
│ Δ open_conn(): opened {c}
│ ? fail_now → fault "callee failed"
│ close_conn(▾c)
│ ■ ok
╵

contingent control log_msg(tag: &string, msg: &string) ■ done uses console.write
│ emit(tag)
│ emit(msg)
│ ■ done
╵

boundary guarded_job(tag: string, fail_now: bool) retains tag
│ Δ with_conn(fail_now): ok
│ terminate
╵
contingency (m: string)
│ log_msg(tag, m)
│ terminate
╵

control run_all(fail_now: bool) ■ done {total: u32, count: usize, slen: usize} uses net, console.write
│ ~pts: [point] := [point {1, 2}]
│ push_point(&~pts, point {3, 4})
│ item: labeled := labeled {"lbl", 10}
│ Δ read_labeled(item): ok {v1}
│ Δ read_str(trim("  hello  ")): ok {v2}
│ supervise guarded_job("job", fail_now)
│ p1: point := pts[1]
│ ■ done {(p1.x mod 10000) + (p1.y mod 10000) + v1, len(pts), v2}
╵
"#;
    let orig_tree = surface::elaborate(borrow_and_fault_source).unwrap();
    let orig_prog = resolve::resolve(&orig_tree).unwrap();
    let orig_checked = check::check(&orig_prog).unwrap();
    orig_checked.revalidate().unwrap();

    let exp_tree = expand::expand(&orig_tree).unwrap();
    assert_no_expandable_defined_calls(&exp_tree);
    let exp_printed = exp_tree.print();
    let exp_reparsed = text::parse(&exp_printed)
        .unwrap_or_else(|e| panic!("expanded borrow/fault failed to parse: {e}\n{exp_printed}"));
    let exp_prog = resolve::resolve(&exp_reparsed)
        .unwrap_or_else(|e| panic!("expanded borrow/fault failed to resolve: {e}\n{exp_printed}"));
    let exp_checked = check::check(&exp_prog)
        .unwrap_or_else(|e| panic!("expanded borrow/fault failed check: {e}\n{exp_printed}"));
    exp_checked.revalidate().unwrap();

    let specs = vec![
        NativeRunSpec {
            entry: "run_all".to_string(),
            arguments: vec![Value::Bool(false)],
            arithmetic: false,
            answers: vec![
                (
                    "open_conn".to_string(),
                    ans("opened", vec![res_val("conn", 1)]),
                ),
                ("close_conn".to_string(), ans("closed", vec![])),
            ],
        },
        NativeRunSpec {
            entry: "run_all".to_string(),
            arguments: vec![Value::Bool(true)],
            arithmetic: false,
            answers: vec![(
                "open_conn".to_string(),
                ans("opened", vec![res_val("conn", 2)]),
            )],
        },
    ];
    verify_native_specs("borrow_and_fault_orig", &orig_prog, &specs, 64);
    verify_native_specs("borrow_and_fault_exp", &exp_prog, &specs, 64);
}

#[test]
fn slice_two_phase_4_ir_and_c_abi_erasure() {
    let rec_prog =
        villanelle_v2::load_surface(include_str!("slice2_surface/records_and_variants.rails"))
            .unwrap();
    let col_prog =
        villanelle_v2::load_surface(include_str!("slice2_surface/collections_and_foreach.rails"))
            .unwrap();
    let res_prog =
        villanelle_v2::load_surface(include_str!("slice2_surface/show_file_resource.rails"))
            .unwrap();
    let bnd_prog =
        villanelle_v2::load_surface(include_str!("slice2_surface/boundaries_and_faults.rails"))
            .unwrap();

    let rec_ir = emit_llvm(&rec_prog, 64);
    let rec_hdr = emit_c_header(&rec_prog, 64);
    let col_ir = emit_llvm(&col_prog, 64);
    let col_ir_32 = emit_llvm(&col_prog, 32);
    let res_ir = emit_llvm(&res_prog, 64);
    let res_hdr = emit_c_header(&res_prog, 64);
    let bnd_ir = emit_llvm(&bnd_prog, 64);
    let bnd_hdr = emit_c_header(&bnd_prog, 64);

    // [R1]: Flat static native representations, zero dynamic Value wrapper.
    assert!(rec_ir.contains("%vn2.struct.0 = type { i32, i32 }"));
    assert!(rec_ir.contains("%vn2.variant.1 = type { i32, ["));
    // Unit variant `op` lowers directly to `i32`, never to a struct type.
    assert!(!rec_ir.contains("%vn2.variant.0 = type"));
    assert!(!rec_ir.contains("Value"));
    assert!(col_ir.contains("%vn2.vec = type { ptr, i64, i64 }"));
    assert!(col_ir.contains("%vn2.map = type { ptr, i64, i64 }"));
    assert!(col_ir.contains("%vn2.string = type { ptr, i64, i64 }"));
    assert!(col_ir_32.contains("%vn2.vec = type { ptr, i32, i32 }"));

    // [R2]: `⊥` compiles directly to `unreachable`, and indexing emits no bounds trap.
    assert!(col_ir.contains("unreachable"));
    assert!(!col_ir.contains("oob"));

    // [R4]/[R5]: Static history-bit release (`@vn2_release_conn`) and drop (`@vn2_drop_`),
    // zero runtime moved-flag arrays.
    assert!(bnd_ir.contains("declare void @vn2_release_conn(ptr)"));
    assert!(bnd_ir.contains("call void @vn2_release_conn("));
    assert!(res_ir.contains("declare void @vn2_builtin_emit(ptr)"));
    assert!(!bnd_ir.contains("moved_flag"));
    assert!(!res_ir.contains("moved_flag"));

    // Typed C ABI header declarations for structs, variants, resources, emit, and faults.
    assert!(
        rec_hdr.contains(
            "typedef struct vn2_struct_point { uint32_t x; uint32_t y; } vn2_struct_point;"
        )
    );
    assert!(rec_hdr.contains("typedef struct vn2_variant_shape {"));
    assert!(res_hdr.contains("void vn2_release_file_handle(void *handle);"));
    assert!(res_hdr.contains("void vn2_builtin_emit(const struct vn2_string *text);"));
    assert!(bnd_hdr.contains("#define VN2_FAULT (-1)"));
    assert!(bnd_hdr.contains("void vn2_release_conn(void *handle);"));
    assert!(bnd_hdr.contains("struct vn2_string *out_fault"));
}

#[test]
fn slice_two_surface_programs_agree_across_oracle_erased_expanded_and_native() {
    let cases: Vec<(&str, &str, Vec<NativeRunSpec>)> = vec![
        (
            "records_and_variants.rails",
            include_str!("slice2_surface/records_and_variants.rails"),
            vec![
                NativeRunSpec {
                    entry: "eval_op".to_string(),
                    arguments: vec![
                        Value::Variant {
                            ty: 0,
                            name: "op".to_string(),
                            constructor: 0,
                            constructor_name: "add".to_string(),
                            fields: vec![],
                        },
                        u32_val(6),
                        u32_val(7),
                    ],
                    arithmetic: false,
                    answers: vec![],
                },
                NativeRunSpec {
                    entry: "eval_op".to_string(),
                    arguments: vec![
                        Value::Variant {
                            ty: 0,
                            name: "op".to_string(),
                            constructor: 1,
                            constructor_name: "sub".to_string(),
                            fields: vec![],
                        },
                        u32_val(4),
                        u32_val(9),
                    ],
                    arithmetic: false,
                    answers: vec![],
                },
                NativeRunSpec {
                    entry: "eval_op".to_string(),
                    arguments: vec![
                        Value::Variant {
                            ty: 0,
                            name: "op".to_string(),
                            constructor: 2,
                            constructor_name: "mul".to_string(),
                            fields: vec![],
                        },
                        u32_val(4),
                        u32_val(5),
                    ],
                    arithmetic: false,
                    answers: vec![],
                },
                NativeRunSpec {
                    entry: "describe_shape".to_string(),
                    arguments: vec![
                        Value::Variant {
                            ty: 1,
                            name: "shape".to_string(),
                            constructor: 0,
                            constructor_name: "circle".to_string(),
                            fields: vec![u32_val(4)],
                        },
                        Value::String("  circle  ".to_string()),
                    ],
                    arithmetic: false,
                    answers: vec![],
                },
                NativeRunSpec {
                    entry: "describe_shape".to_string(),
                    arguments: vec![
                        Value::Variant {
                            ty: 1,
                            name: "shape".to_string(),
                            constructor: 1,
                            constructor_name: "rect".to_string(),
                            fields: vec![u32_val(3), u32_val(5)],
                        },
                        Value::String(" box ".to_string()),
                    ],
                    arithmetic: false,
                    answers: vec![],
                },
            ],
        ),
        (
            "collections_and_foreach.rails",
            include_str!("slice2_surface/collections_and_foreach.rails"),
            vec![
                NativeRunSpec {
                    entry: "sum_vector".to_string(),
                    arguments: vec![Value::Vector(vec![
                        u32_val(1),
                        u32_val(2),
                        u32_val(3),
                        u32_val(4),
                    ])],
                    arithmetic: false,
                    answers: vec![],
                },
                NativeRunSpec {
                    entry: "forward_captured".to_string(),
                    arguments: vec![
                        Value::Vector(vec![u32_val(2), u32_val(8), u32_val(5)]),
                        u32_val(6),
                    ],
                    arithmetic: false,
                    answers: vec![],
                },
                NativeRunSpec {
                    entry: "forward_captured".to_string(),
                    arguments: vec![
                        Value::Vector(vec![u32_val(1), u32_val(2), u32_val(3)]),
                        u32_val(10),
                    ],
                    arithmetic: false,
                    answers: vec![],
                },
                NativeRunSpec {
                    entry: "collect_and_map".to_string(),
                    arguments: vec![],
                    arithmetic: false,
                    answers: vec![],
                },
            ],
        ),
        (
            "show_file_resource.rails",
            include_str!("slice2_surface/show_file_resource.rails"),
            vec![
                NativeRunSpec {
                    entry: "show_file".to_string(),
                    arguments: vec![Value::String("notes.txt".to_string())],
                    arithmetic: false,
                    answers: vec![
                        (
                            "open".to_string(),
                            ans("opened", vec![res_val("file_handle", 1)]),
                        ),
                        (
                            "read".to_string(),
                            ans("data", vec![Value::String("hello".to_string())]),
                        ),
                        ("close".to_string(), ans("closed", vec![])),
                        (
                            "decode_utf8".to_string(),
                            ans("text", vec![Value::String("hello".to_string())]),
                        ),
                    ],
                },
                NativeRunSpec {
                    entry: "show_file".to_string(),
                    arguments: vec![Value::String("absent.txt".to_string())],
                    arithmetic: false,
                    answers: vec![("open".to_string(), ans("not_found", vec![]))],
                },
                NativeRunSpec {
                    entry: "show_file".to_string(),
                    arguments: vec![Value::String("secret.txt".to_string())],
                    arithmetic: false,
                    answers: vec![("open".to_string(), ans("denied", vec![]))],
                },
                NativeRunSpec {
                    entry: "show_file".to_string(),
                    arguments: vec![Value::String("broken.txt".to_string())],
                    arithmetic: false,
                    answers: vec![
                        (
                            "open".to_string(),
                            ans("opened", vec![res_val("file_handle", 2)]),
                        ),
                        ("read".to_string(), ans("failed", vec![])),
                        ("close".to_string(), ans("closed", vec![])),
                    ],
                },
                NativeRunSpec {
                    entry: "show_file".to_string(),
                    arguments: vec![Value::String("badutf8.txt".to_string())],
                    arithmetic: false,
                    answers: vec![
                        (
                            "open".to_string(),
                            ans("opened", vec![res_val("file_handle", 3)]),
                        ),
                        (
                            "read".to_string(),
                            ans("data", vec![Value::String("?".to_string())]),
                        ),
                        ("close".to_string(), ans("closed", vec![])),
                        ("decode_utf8".to_string(), ans("invalid", vec![])),
                    ],
                },
            ],
        ),
        (
            "boundaries_and_faults.rails",
            include_str!("slice2_surface/boundaries_and_faults.rails"),
            vec![
                NativeRunSpec {
                    entry: "run_worker".to_string(),
                    arguments: vec![Value::Bool(false)],
                    arithmetic: false,
                    answers: vec![
                        (
                            "open_conn".to_string(),
                            ans("opened", vec![res_val("conn", 1)]),
                        ),
                        ("close_conn".to_string(), ans("closed", vec![])),
                    ],
                },
                NativeRunSpec {
                    entry: "run_worker".to_string(),
                    arguments: vec![Value::Bool(true)],
                    arithmetic: false,
                    answers: vec![(
                        "open_conn".to_string(),
                        ans("opened", vec![res_val("conn", 1)]),
                    )],
                },
                NativeRunSpec {
                    entry: "direct_fault".to_string(),
                    arguments: vec![],
                    arithmetic: false,
                    answers: vec![],
                },
            ],
        ),
    ];

    for (name, source, specs) in &cases {
        let tree = surface::elaborate(source).unwrap();
        let orig_prog = resolve::resolve(&tree).unwrap();
        let exp_tree = expand::expand(&tree).unwrap();
        let exp_prog = resolve::resolve(&exp_tree).unwrap();

        for usize_bits in [64u32, 32u32] {
            verify_native_specs(&format!("{name} (orig)"), &orig_prog, specs, usize_bits);
            verify_native_specs(&format!("{name} (exp)"), &exp_prog, specs, usize_bits);
        }
    }
}

#[test]
fn slice_two_core_programs_agree_natively() {
    // 1. records_and_variants.core
    let rec_core = villanelle_v2::load(include_str!("slice2/records_and_variants.core")).unwrap();
    let rec_specs = vec![
        NativeRunSpec {
            entry: "calc".to_string(),
            arguments: vec![
                Value::Variant {
                    ty: 0,
                    name: "op".to_string(),
                    constructor: 0,
                    constructor_name: "add".to_string(),
                    fields: vec![],
                },
                u32_val(4),
                u32_val(5),
            ],
            arithmetic: false,
            answers: vec![],
        },
        NativeRunSpec {
            entry: "calc".to_string(),
            arguments: vec![
                Value::Variant {
                    ty: 0,
                    name: "op".to_string(),
                    constructor: 1,
                    constructor_name: "sub".to_string(),
                    fields: vec![],
                },
                u32_val(9),
                u32_val(3),
            ],
            arithmetic: false,
            answers: vec![],
        },
        NativeRunSpec {
            entry: "calc".to_string(),
            arguments: vec![
                Value::Variant {
                    ty: 0,
                    name: "op".to_string(),
                    constructor: 2,
                    constructor_name: "mul".to_string(),
                    fields: vec![],
                },
                u32_val(3),
                u32_val(7),
            ],
            arithmetic: false,
            answers: vec![],
        },
        NativeRunSpec {
            entry: "area_and_unpack".to_string(),
            arguments: vec![
                Value::Variant {
                    ty: 1,
                    name: "shape".to_string(),
                    constructor: 0,
                    constructor_name: "circle".to_string(),
                    fields: vec![u32_val(4)],
                },
                Value::String("  hi  ".to_string()),
            ],
            arithmetic: false,
            answers: vec![],
        },
        NativeRunSpec {
            entry: "area_and_unpack".to_string(),
            arguments: vec![
                Value::Variant {
                    ty: 1,
                    name: "shape".to_string(),
                    constructor: 1,
                    constructor_name: "rect".to_string(),
                    fields: vec![u32_val(3), u32_val(5)],
                },
                Value::String("\tok\n".to_string()),
            ],
            arithmetic: false,
            answers: vec![],
        },
        NativeRunSpec {
            entry: "copy_reuse".to_string(),
            arguments: vec![Value::Struct {
                ty: 0,
                name: "point".to_string(),
                fields: vec![u32_val(3), u32_val(4)],
            }],
            arithmetic: false,
            answers: vec![],
        },
    ];
    verify_native_specs("records_and_variants.core", &rec_core, &rec_specs, 64);

    // 2. collections_and_builtins.core
    let col_core =
        villanelle_v2::load(include_str!("slice2/collections_and_builtins.core")).unwrap();
    let col_specs = vec![
        NativeRunSpec {
            entry: "vec_ops".to_string(),
            arguments: vec![],
            arithmetic: false,
            answers: vec![],
        },
        NativeRunSpec {
            entry: "operands_order".to_string(),
            arguments: vec![],
            arithmetic: false,
            answers: vec![],
        },
        NativeRunSpec {
            entry: "map_ops".to_string(),
            arguments: vec![],
            arithmetic: false,
            answers: vec![],
        },
        NativeRunSpec {
            entry: "say_hello".to_string(),
            arguments: vec![Value::String("hello".to_string())],
            arithmetic: false,
            answers: vec![],
        },
    ];
    verify_native_specs("collections_and_builtins.core", &col_core, &col_specs, 64);

    // 3. ownership_and_resources.core
    let own_core =
        villanelle_v2::load(include_str!("slice2/ownership_and_resources.core")).unwrap();
    let own_specs = vec![NativeRunSpec {
        entry: "clean_resource".to_string(),
        arguments: vec![Value::String("a.txt".to_string())],
        arithmetic: false,
        answers: vec![
            (
                "open_file".to_string(),
                ans("opened", vec![res_val("file_handle", 1)]),
            ),
            (
                "read_file".to_string(),
                ans("data", vec![Value::String("ok".to_string())]),
            ),
            ("close_file".to_string(), ans("closed", vec![])),
        ],
    }];
    verify_native_specs("ownership_and_resources.core", &own_core, &own_specs, 64);

    // 4. captured_outcomes.core
    let cap_core = villanelle_v2::load(include_str!("slice2/captured_outcomes.core")).unwrap();
    let cap_specs = vec![
        NativeRunSpec {
            entry: "capture_and_decide".to_string(),
            arguments: vec![u32_val(1)],
            arithmetic: false,
            answers: vec![("fetch".to_string(), ans("ok", vec![u32_val(42)]))],
        },
        NativeRunSpec {
            entry: "capture_and_decide".to_string(),
            arguments: vec![u32_val(2)],
            arithmetic: false,
            answers: vec![("fetch".to_string(), ans("failed", vec![u32_val(404)]))],
        },
    ];
    verify_native_specs("captured_outcomes.core", &cap_core, &cap_specs, 64);

    // 5. faults_and_boundaries.core (all 6 non-stuck controls, including lexical recover/escalate/terminate)
    let flt_core = villanelle_v2::load(include_str!("slice2/faults_and_boundaries.core")).unwrap();
    let flt_specs = vec![
        NativeRunSpec {
            entry: "root_fault_with_release".to_string(),
            arguments: vec![Value::Bool(false)],
            arithmetic: false,
            answers: vec![
                (
                    "open_conn".to_string(),
                    ans("opened", vec![res_val("conn", 1)]),
                ),
                ("close_conn".to_string(), ans("closed", vec![])),
            ],
        },
        NativeRunSpec {
            entry: "root_fault_with_release".to_string(),
            arguments: vec![Value::Bool(true)],
            arithmetic: false,
            answers: vec![(
                "open_conn".to_string(),
                ans("opened", vec![res_val("conn", 1)]),
            )],
        },
        NativeRunSpec {
            entry: "assumed_fault".to_string(),
            arguments: vec![],
            arithmetic: false,
            answers: vec![],
        },
        NativeRunSpec {
            entry: "lexical_recover".to_string(),
            arguments: vec![u32_val(7)],
            arithmetic: false,
            answers: vec![
                (
                    "open_conn".to_string(),
                    ans("opened", vec![res_val("conn", 1)]),
                ),
                ("check_ready".to_string(), ans("not_ready", vec![])),
                (
                    "open_conn".to_string(),
                    ans("opened", vec![res_val("conn", 2)]),
                ),
                ("check_ready".to_string(), ans("ready", vec![u32_val(1)])),
                ("close_conn".to_string(), ans("closed", vec![])),
            ],
        },
        NativeRunSpec {
            entry: "lexical_escalate".to_string(),
            arguments: vec![],
            arithmetic: false,
            answers: vec![],
        },
        NativeRunSpec {
            entry: "lexical_terminate".to_string(),
            arguments: vec![],
            arithmetic: false,
            answers: vec![],
        },
        NativeRunSpec {
            entry: "run_supervised".to_string(),
            arguments: vec![Value::Bool(false)],
            arithmetic: false,
            answers: vec![],
        },
        NativeRunSpec {
            entry: "run_supervised".to_string(),
            arguments: vec![Value::Bool(true)],
            arithmetic: false,
            answers: vec![],
        },
    ];
    verify_native_specs("faults_and_boundaries.core", &flt_core, &flt_specs, 64);

    // 6. lexical_boundaries.core: every run of the file that ends.
    let lex_core = villanelle_v2::load(include_str!("slice2/lexical_boundaries.core")).unwrap();
    let spec = |entry: &str, arguments: Vec<Value>, answers: Vec<(&str, Answer)>| NativeRunSpec {
        entry: entry.to_string(),
        arguments,
        arithmetic: false,
        answers: answers
            .into_iter()
            .map(|(control, answer)| (control.to_string(), answer))
            .collect(),
    };
    // `conn` is the first resource type of the file and `lock` the second.
    let opened = |name: &str, id: u64| {
        let ty = usize::from(name == "lock");
        let name = name.to_string();
        ans("opened", vec![Value::Resource { ty, name, id }])
    };
    let lex_specs = vec![
        spec("falls_off", vec![u32_val(4)], vec![]),
        spec("ends_inside", vec![u32_val(3)], vec![]),
        spec("leaves_inside", vec![u32_val(2)], vec![]),
        spec(
            "cares",
            vec![Value::String("t".to_string())],
            vec![
                ("open_lock", opened("lock", 1)),
                ("open_conn", opened("conn", 1)),
                ("close_lock", ans("closed", vec![])),
            ],
        ),
        spec("from_below", vec![], vec![("open_conn", opened("conn", 1))]),
        spec(
            "retries",
            vec![u32_val(3)],
            vec![
                ("open_conn", opened("conn", 1)),
                ("open_conn", opened("conn", 2)),
                ("open_conn", opened("conn", 3)),
                ("close_conn", ans("closed", vec![])),
            ],
        ),
        spec(
            "recovers_outer",
            vec![Value::String("kept".to_string())],
            vec![],
        ),
        spec("escalates_to_outer", vec![], vec![]),
        spec("loops_in_contingency", vec![u32_val(2)], vec![]),
        spec("ends_execution", vec![u32_val(0)], vec![]),
        spec("ends_execution", vec![u32_val(1)], vec![]),
        spec("supervises", vec![], vec![]),
    ];
    verify_native_specs("lexical_boundaries.core", &lex_core, &lex_specs, 64);
}

/// The core text files of the slice 2 suite that the checker accepts, with
/// the runs of their directives that end.
fn checked_core_files() -> Vec<(String, villanelle_v2::typed::Program, Vec<NativeRunSpec>)> {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/slice2");
    let mut paths: Vec<_> = std::fs::read_dir(&dir)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "core"))
        .collect();
    paths.sort();
    let mut files = Vec::new();
    for path in paths {
        let name = path.file_name().unwrap().to_string_lossy().to_string();
        let source = std::fs::read_to_string(&path).unwrap();
        let Ok((program, specs)) = script::native_runs(&source) else {
            continue;
        };
        if specs.is_empty() || check::check(&program).is_err() {
            continue;
        }
        files.push((name, program, specs));
    }
    files
}

/// How the oracle ends each run, and what it does.
fn oracle_ends(
    program: &villanelle_v2::typed::Program,
    specs: &[NativeRunSpec],
) -> Vec<(String, Vec<villanelle_v2::oracle::Event>)> {
    specs
        .iter()
        .map(|spec| {
            let script = Script {
                answers: spec.answers.iter().cloned().collect(),
            };
            let config = Config::default();
            let arguments = spec.arguments.clone();
            let out = if spec.arithmetic {
                let mut host = villanelle_v2::host::Arithmetic(script);
                run(program, &spec.entry, arguments, &mut host, &config)
            } else {
                let mut host = script;
                run(program, &spec.entry, arguments, &mut host, &config)
            };
            (out.end.to_string(), out.trace)
        })
        .collect()
}

/// What a checked program becomes is compiled: every file of the suite that
/// the checker accepts runs its directives in compiled code, at `-O0` and
/// `-O2`, to the end and the trace of the oracle ([R1] to [R5]).
#[test]
fn checked_core_programs_of_slice_two_run_natively_as_the_oracle_does() {
    let files = checked_core_files();
    let mut runs = 0;
    let mut failures = Vec::new();
    for (name, program, specs) in &files {
        let expected = oracle_ends(program, specs);
        // What run `index` says where it does not end as the oracle's does.
        let differs = |level: u8, index: usize, native: &(erased::End, Vec<_>)| {
            let (end, trace) = &expected[index];
            let entry = &specs[index].entry;
            if native.0.to_string() != *end {
                Some(format!(
                    "{name} -O{level} run {index} of `{entry}`: `{}`, and the oracle `{end}`",
                    native.0
                ))
            } else if native.1 != *trace {
                Some(format!(
                    "{name} -O{level} run {index} of `{entry}`: the trace is not the oracle's"
                ))
            } else {
                None
            }
        };
        for level in [0, 2] {
            let native = match run_native_batch(program, specs, 64, level) {
                Ok(native) if native.len() == expected.len() => native,
                Ok(native) => {
                    failures.push(format!(
                        "{name} -O{level}: {} runs of {}",
                        native.len(),
                        expected.len()
                    ));
                    continue;
                }
                Err(_) => {
                    // The runs of a batch share a process. Each one alone
                    // says which of them ended it.
                    for (index, spec) in specs.iter().enumerate() {
                        let entry = &spec.entry;
                        match run_native_batch(program, std::slice::from_ref(spec), 64, level) {
                            Ok(one) if one.len() == 1 => {
                                failures.extend(differs(level, index, &one[0]))
                            }
                            Ok(_) => failures
                                .push(format!("{name} -O{level} run {index} of `{entry}`: no end")),
                            Err(error) => {
                                let error: String = error.chars().take(200).collect();
                                failures.push(format!(
                                    "{name} -O{level} run {index} of `{entry}`: {error}"
                                ));
                            }
                        }
                    }
                    continue;
                }
            };
            for (index, run) in native.iter().enumerate() {
                failures.extend(differs(level, index, run));
            }
        }
        runs += specs.len();
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    // The files of the suite that the checker accepts whole: most of the
    // others hold a control that is there to be stuck.
    let names: Vec<&str> = files.iter().map(|(name, _, _)| name.as_str()).collect();
    assert_eq!(
        names,
        [
            "checked_faults_and_boundaries.core",
            "checked_nested_boundaries.core",
            "checked_skipped_bodies.core",
            "erased_nested_ownership.core"
        ]
    );
    assert_eq!(runs, 58);
}

/// `ir` with no string freed by the program: the calls that release a
/// string are taken out of every function but `main` and the hosts, which
/// are the harness.
fn without_string_releases(ir: &str) -> String {
    let mut out = String::new();
    let mut harness = false;
    for line in ir.lines() {
        if line.starts_with("define ") {
            harness = line.contains("@main(") || line.contains("@vn2_ext_");
        }
        if harness || !line.contains("call fastcc void @vn2_str_drop(") {
            out.push_str(line);
            out.push('\n');
        }
    }
    out
}

/// [R4] is observed: the harness counts the allocations of a run, and a run
/// of compiled code that leaves one live does not end as the oracle's run
/// does. The programs here are the checked files of the suite with the
/// release of a string taken out of what was compiled.
#[test]
fn a_run_of_compiled_code_that_leaves_an_allocation_live_is_seen() {
    let mut seen = 0;
    let mut runs = 0;
    let mut made = Vec::new();
    for (name, program, specs) in &checked_core_files() {
        let ir = emit_native_harness_llvm(program, specs, 64);
        let leaking = without_string_releases(&ir);
        assert_ne!(ir, leaking, "{name} releases no string");
        for level in [0, 2] {
            let whole = run_native_ir(program, specs, &ir, level).unwrap();
            let leaked = run_native_ir(program, specs, &leaking, level).unwrap();
            assert_eq!(whole.runs.len(), specs.len());
            assert_eq!(leaked.runs.len(), specs.len());
            // Taking a release out makes no allocation more or fewer.
            assert_eq!(whole.allocations, leaked.allocations);
            made.push(whole.allocations);
            for ((end, _), (leaked_end, _)) in whole.runs.iter().zip(&leaked.runs) {
                assert!(
                    !matches!(end, erased::End::Undefined(_)),
                    "{name} -O{level}: `{end}`"
                );
                runs += 1;
                if let erased::End::Undefined(message) = leaked_end {
                    assert!(message.contains("allocations live"), "{message}");
                    seen += 1;
                }
            }
        }
    }
    assert_eq!((runs, seen), (116, 40));
    // The allocations of the four files, at `-O0` and at `-O2`.
    assert_eq!(made, [21, 21, 50, 50, 7, 7, 0, 0]);
}

#[test]
fn paired_native_performance_matches_optimized_rust_on_slice_two_data_kernel() {
    // Slice 2 data kernel:
    //   1. Build a `[point]` vector (`copy struct point {x: u64, y: u64}`) by
    //      pushing `n = 2000` points.
    //   2. Run `passes = 200` unchecked indexed passes over `pts[j]`, dispatching
    //      on `copy variant op: add | sub | mix | scale`, updating `pts[j]` in
    //      place, and accumulating a checksum mod 1_000_000_007.
    //   3. Pop all `2000` points back out (`pts.pop()`) into the checksum and
    //      drop the vector cleanly via `[R4]`.
    let v2_source = include_str!("kernels/slice2_data.rails");

    let tree = surface::elaborate(v2_source).unwrap();
    let expanded = expand::expand(&tree).unwrap();
    let program = resolve::resolve(&expanded).unwrap();
    let checked = check::check(&program).unwrap();
    checked.revalidate().unwrap();

    let mut v2_ir = emit_llvm(&program, 64);
    v2_ir.push_str(
        r#"
%timespec = type { i64, i64 }
declare i32 @clock_gettime(i32, ptr)
declare i32 @printf(ptr, ...)
@fmt_bench = private unnamed_addr constant [11 x i8] c"%llu %lld\0A\00"

define i32 @main() nounwind {
entry:
  %t0 = alloca %timespec
  %t1 = alloca %timespec
  %out = alloca i64
  store i64 0, ptr %out
  ; Warm-up call
  %w = call i32 @vn2_call_data_bench(i64 256, i64 20, ptr %out)
  ; Timed hot call: 2000 points x 200 passes (x 10 reps for stable timing)
  call i32 @clock_gettime(i32 0, ptr %t0)
  %rep = alloca i32
  store i32 0, ptr %rep
  %tot = alloca i64
  store i64 0, ptr %tot
  br label %lp
lp:
  %r = load i32, ptr %rep
  %more = icmp slt i32 %r, 10
  br i1 %more, label %body, label %done
body:
  %tag = call i32 @vn2_call_data_bench(i64 2000, i64 200, ptr %out)
  %cur = load i64, ptr %out
  %prev = load i64, ptr %tot
  %sum = add i64 %prev, %cur
  store i64 %sum, ptr %tot
  %nr = add i32 %r, 1
  store i32 %nr, ptr %rep
  br label %lp
done:
  call i32 @clock_gettime(i32 0, ptr %t1)
  %s0_p = getelementptr %timespec, ptr %t0, i32 0, i32 0
  %ns0_p = getelementptr %timespec, ptr %t0, i32 0, i32 1
  %s1_p = getelementptr %timespec, ptr %t1, i32 0, i32 0
  %ns1_p = getelementptr %timespec, ptr %t1, i32 0, i32 1
  %s0 = load i64, ptr %s0_p
  %ns0 = load i64, ptr %ns0_p
  %s1 = load i64, ptr %s1_p
  %ns1 = load i64, ptr %ns1_p
  %ds = sub i64 %s1, %s0
  %dns = sub i64 %ns1, %ns0
  %ds_ns = mul i64 %ds, 1000000000
  %elapsed = add i64 %ds_ns, %dns
  %cs = load i64, ptr %tot
  call i32 (ptr, ...) @printf(ptr @fmt_bench, i64 %cs, i64 %elapsed)
  ret i32 0
}
"#,
    );

    let rust_source = r#"
use std::hint::black_box;
use std::time::Instant;

#[derive(Clone, Copy)]
struct Point {
    x: u64,
    y: u64,
}

#[derive(Clone, Copy)]
enum Op {
    Add,
    Sub,
    Mix,
    Scale,
}

#[inline(always)]
fn choose_op(k: u64) -> Op {
    if k == 0 {
        Op::Add
    } else if k == 1 {
        Op::Sub
    } else if k == 2 {
        Op::Mix
    } else {
        Op::Scale
    }
}

#[inline(never)]
fn data_bench(n: usize, passes: u64) -> u64 {
    let mut pts: Vec<Point> = Vec::new();
    for _ in 0..n {
        pts.push(Point { x: 17, y: 29 });
    }
    let mut acc = 0u64;
    for p in 0..passes {
        let mut sub_acc = acc;
        for j in 0..n {
            let cur = pts[j];
            let x0 = cur.x % 1_000_000;
            let y0 = cur.y % 1_000_000;
            let (nx, ny) = match choose_op((p + x0 + y0) % 4) {
                Op::Add => ((x0 + y0 + 1) % 1_000_000, (y0 + 3) % 1_000_000),
                Op::Sub => (
                    if x0 >= y0 { x0 - y0 } else { y0 - x0 },
                    (x0 + 5) % 1_000_000,
                ),
                Op::Mix => ((x0 * 3 + y0) % 1_000_000, (y0 * 5 + 7) % 1_000_000),
                Op::Scale => ((x0 * 7 + 11) % 1_000_000, (y0 * 2 + x0) % 1_000_000),
            };
            pts[j] = Point { x: nx, y: ny };
            sub_acc = (sub_acc + nx + ny) % 1_000_000_007;
        }
        acc = sub_acc;
    }
    let mut final_acc = acc;
    for _ in 0..n {
        let pt = match pts.pop() {
            Some(v) => v,
            None => unreachable!(),
        };
        final_acc = (final_acc + (pt.x % 1_000_000) + (pt.y % 1_000_000)) % 1_000_000_007;
    }
    final_acc
}

fn main() {
    let _ = black_box(data_bench(black_box(256), black_box(20)));
    let start = Instant::now();
    let mut tot = 0u64;
    for _ in 0..10 {
        tot = tot.wrapping_add(black_box(data_bench(black_box(2000), black_box(200))));
    }
    let elapsed = start.elapsed().as_nanos() as i64;
    println!("{tot} {elapsed}");
}
"#;

    let tmp_dir = std::env::temp_dir();
    let pid = std::process::id();
    let v2_ll = tmp_dir.join(format!("vn2_s2_perf_{pid}.ll"));
    let v2_bin = tmp_dir.join(format!("vn2_s2_perf_{pid}_v2.bin"));
    let rs_src = tmp_dir.join(format!("vn2_s2_perf_{pid}.rs"));
    let rs_bin = tmp_dir.join(format!("vn2_s2_perf_{pid}_rs.bin"));

    std::fs::write(&v2_ll, &v2_ir).unwrap();
    std::fs::write(&rs_src, rust_source).unwrap();

    let c1 = ProcessCommand::new("clang")
        .args(["-x", "ir"])
        .arg(&v2_ll)
        .args(["-O3", "-Wno-override-module", "-o"])
        .arg(&v2_bin)
        .output()
        .unwrap();
    let _ = std::fs::remove_file(&v2_ll);
    assert!(
        c1.status.success(),
        "clang -O3 failed: {}",
        String::from_utf8_lossy(&c1.stderr)
    );

    let c2 = ProcessCommand::new("rustc")
        .arg(&rs_src)
        .args(["-C", "opt-level=3", "-o"])
        .arg(&rs_bin)
        .output()
        .unwrap();
    let _ = std::fs::remove_file(&rs_src);
    assert!(
        c2.status.success(),
        "rustc -O3 failed: {}",
        String::from_utf8_lossy(&c2.stderr)
    );

    let mut v2_best_ns = i64::MAX;
    let mut rs_best_ns = i64::MAX;
    let mut v2_checksum = 0u64;
    let mut rs_checksum = 0u64;

    // The best time of each side estimates its cost, and noise only adds to
    // a time. On a loaded machine five rounds do not reach the best, so the
    // measurement goes on, up to 40 rounds, until the ratio is within the
    // bound; a kernel that is slower than the bound stays so.
    for round in 0..40 {
        if round >= 5
            && v2_best_ns > 0
            && rs_best_ns > 0
            && v2_best_ns as f64 <= 1.20 * rs_best_ns as f64
        {
            break;
        }
        let out_v2 = ProcessCommand::new(&v2_bin).output().unwrap();
        assert!(out_v2.status.success());
        let s_v2 = String::from_utf8_lossy(&out_v2.stdout);
        let mut parts_v2 = s_v2.split_whitespace();
        v2_checksum = parts_v2.next().unwrap().parse().unwrap();
        let ns_v2: i64 = parts_v2.next().unwrap().parse().unwrap();
        if ns_v2 > 0 {
            v2_best_ns = v2_best_ns.min(ns_v2);
        }

        let out_rs = ProcessCommand::new(&rs_bin).output().unwrap();
        assert!(out_rs.status.success());
        let s_rs = String::from_utf8_lossy(&out_rs.stdout);
        let mut parts_rs = s_rs.split_whitespace();
        rs_checksum = parts_rs.next().unwrap().parse().unwrap();
        let ns_rs: i64 = parts_rs.next().unwrap().parse().unwrap();
        if ns_rs > 0 {
            rs_best_ns = rs_best_ns.min(ns_rs);
        }
    }

    let _ = std::fs::remove_file(&v2_bin);
    let _ = std::fs::remove_file(&rs_bin);

    assert_eq!(v2_checksum, rs_checksum, "v2 and Rust checksums must match");
    assert!(v2_best_ns > 0 && rs_best_ns > 0);
    let ratio = v2_best_ns as f64 / rs_best_ns as f64;
    eprintln!(
        "paired Slice 2 data_bench (10 x 2000 points x 200 passes, checksum={v2_checksum}): v2 LLVM -O3 = {:.3} ms ({v2_best_ns} ns), Rust -O3 = {:.3} ms ({rs_best_ns} ns), ratio v2/Rust = {:.3}x",
        v2_best_ns as f64 / 1_000_000.0,
        rs_best_ns as f64 / 1_000_000.0,
        ratio
    );
    assert!(
        ratio <= 1.20,
        "Slice 2 data_bench ratio {ratio:.3}x exceeded 1.20x target (v2={v2_best_ns} ns, Rust={rs_best_ns} ns)"
    );
}
