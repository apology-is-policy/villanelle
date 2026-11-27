//! A single pending host operation in an await or a direct run ([E-AwaitHost], [E-Run]).
use super::*;

pub(super) fn targets(program: &Program) -> BTreeSet<ControlId> {
    operations(program)
        .filter_map(|op| match op {
            Operation::AwaitControl(id) | Operation::RunControl(id)
                if program.controls[*id].body.is_none() =>
            {
                Some(*id)
            }
            _ => None,
        })
        .collect()
}

pub(super) fn emit_header(
    out: &mut String,
    program: &Program,
    control: &Control,
    bits: u32,
    outputs: &[String],
) {
    let request = format!("struct vn2_wait_{}", control.name);
    let _ = writeln!(out, "{request} {{\n    void *host_state;");
    for param in &control.parameters {
        let ty = c_header_param_ty(program, &param.ty, bits);
        let _ = writeln!(out, "    {ty} in_{};", param.name);
    }
    for field in outputs {
        let _ = writeln!(out, "    {field};");
    }
    let _ = writeln!(out, "}};");
    let _ = writeln!(out, "void vn2_start_{}({request} *request);", control.name);
    let _ = writeln!(
        out,
        "int32_t vn2_complete_{}({request} *request);",
        control.name
    );
}

// The request and all its input and result slots outlive the pending operation.
pub(super) fn emit_request(
    em: &mut IrEmitter<'_, '_>,
    id: ControlId,
    args: &[String],
    tag: &str,
    scheduler: Option<&str>,
) {
    let ty = format!("%vn2.wait.{id}");
    let request = em.alloc_temp(&ty);
    let _ = writeln!(em.code, "  store ptr null, ptr {request}");
    for (i, arg) in args.iter().enumerate() {
        let field = em.fresh_reg();
        let index = i + 1;
        let _ = writeln!(
            em.code,
            "  {field} = getelementptr {ty}, ptr {request}, i32 0, i32 {index}\n  store {arg}, ptr {field}"
        );
    }
    let name = &em.program.controls[id].name;
    let _ = writeln!(em.code, "  call void @vn2_start_{name}(ptr {request})");
    if let Some(scheduler) = scheduler {
        let _ = writeln!(
            em.code,
            "  call fastcc void @vn2_run_ready_members(ptr {scheduler})"
        );
    }
    // host_state is the first field, so its address is the one-element list.
    let _ = writeln!(
        em.code,
        "  call i64 @vn2_pick_waiting(ptr {request}, i64 1)"
    );
    let _ = writeln!(
        em.code,
        "  {tag} = call i32 @vn2_complete_{name}(ptr {request})"
    );
}

pub(super) fn emit_support(
    out: &mut String,
    program: &Program,
    ids: &BTreeSet<ControlId>,
    bits: u32,
    scripted: bool,
) {
    if ids.is_empty() {
        return;
    }
    if scripted {
        // With one pending operation the scripted host always selects index zero.
        out.push_str("define i64 @vn2_pick_waiting(ptr %states, i64 %count) {\n  ret i64 0\n}\n");
    } else {
        out.push_str("declare i64 @vn2_pick_waiting(ptr, i64)\n");
    }
    for &id in ids {
        let control = &program.controls[id];
        let name = &control.name;
        let ty = format!("%vn2.wait.{id}");
        let fields = c_abi_signature_types(program, control, bits);
        let mut layout = vec!["ptr".to_owned()];
        layout.extend_from_slice(&fields);
        let _ = writeln!(out, "{ty} = type {{ {} }}", layout.join(", "));
        if !scripted {
            let _ = writeln!(
                out,
                "declare void @vn2_start_{name}(ptr)\ndeclare i32 @vn2_complete_{name}(ptr)"
            );
            continue;
        }
        // Bind this invocation at start. Consume its scripted answer only on completion.
        let _ = writeln!(
            out,
            "define void @vn2_start_{name}(ptr %request) {{\n  store ptr %request, ptr %request\n  ret void\n}}"
        );
        let _ = writeln!(out, "define i32 @vn2_complete_{name}(ptr %request) {{");
        let mut args = Vec::new();
        for (i, ll) in fields.iter().enumerate() {
            let index = i + 1;
            let _ = writeln!(
                out,
                "  %s{i} = getelementptr {ty}, ptr %request, i32 0, i32 {index}\n  %a{i} = load {ll}, ptr %s{i}"
            );
            args.push(format!("{ll} %a{i}"));
        }
        let _ = writeln!(
            out,
            "  %tag = call i32 @vn2_ext_{name}({})\n  ret i32 %tag\n}}",
            args.join(", ")
        );
    }
}
