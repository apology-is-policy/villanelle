//! Bound host requests and their completion in an await or a direct run ([E-AwaitHost], [E-Run]).
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
    if control.is_cancellable() {
        let _ = writeln!(
            out,
            "void vn2_withdraw_{}({request} *request);",
            control.name
        );
    }
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
    body: &ControlBody,
    id: ControlId,
    args: &[String],
    tag: &str,
    awaits: bool,
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
    if em.program.controls[id].is_cancellable() {
        let kind = if awaits { "await" } else { "run" };
        let _ = writeln!(
            em.code,
            "  {tag} = call fastcc i32 @vn2_{kind}_host_{id}(ptr {request})"
        );
        return;
    }
    let name = &em.program.controls[id].name;
    let _ = writeln!(em.code, "  call void @vn2_start_{name}(ptr {request})");
    if awaits && em.resume_points.is_some() {
        let wait = em.alloc_temp("%vn2.pending");
        let points = em.resume_points.as_mut().unwrap();
        let pc = points.len() + 1;
        let resume = format!("member_host_{pc}");
        points.push(resume.clone());
        let _ = writeln!(
            em.code,
            "  call fastcc void @vn2_park_host(ptr %task_scheduler, ptr %task_member, ptr {wait}, ptr {request}, ptr @vn2_complete_{name})"
        );
        let _ = writeln!(
            em.code,
            "  store i32 {pc}, ptr %member_state\n  ret i32 -3\n{resume}:"
        );
        let slot = em.fresh_reg();
        let _ = writeln!(
            em.code,
            "  {slot} = getelementptr %vn2.pending, ptr {wait}, i32 0, i32 2\n  {tag} = load i32, ptr {slot}"
        );
        return;
    }

    if awaits && em.reg.has_task_sets {
        let scheduler = tasks::owner_scheduler(body);
        let _ = writeln!(
            em.code,
            "  call fastcc void @vn2_wait_for_root(ptr {scheduler}, ptr {request})"
        );
    } else {
        root_cancel::poll(em);
        // host_state is the first field, so its address is the one-element list.
        let _ = writeln!(
            em.code,
            "  call i64 @vn2_pick_waiting(ptr {request}, i64 1)"
        );
    }
    let _ = writeln!(
        em.code,
        "  {tag} = call i32 @vn2_complete_{name}(ptr {request})"
    );
    if awaits {
        root_cancel::poll(em);
        em.code.push_str("  call i64 @vn2_pick_turn(i64 1)\n");
    }
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
    if !scripted {
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
        if control.is_cancellable() {
            if scripted {
                // A script consumes its answer only at completion. It holds no external state.
                let _ = writeln!(
                    out,
                    "define void @vn2_withdraw_{name}(ptr %request) {{ ret void }}"
                );
            } else {
                let _ = writeln!(out, "declare void @vn2_withdraw_{name}(ptr)");
            }
        }
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
            "@vn2_script_host_{id} = private constant i64 {id}\ndefine void @vn2_start_{name}(ptr %request) {{\n  store ptr @vn2_script_host_{id}, ptr %request\n  ret void\n}}"
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

/// Explicit choices precede Script::pick_waiting, which matches the next answer.
pub(super) fn emit_script_picker(out: &mut String, controls: &[i64]) {
    let ids = controls
        .iter()
        .map(|id| format!("i64 {id}"))
        .collect::<Vec<_>>()
        .join(", ");
    let _ = writeln!(
        out,
        "@vn2_script_controls = private constant [{} x i64] [{ids}]",
        controls.len()
    );
    out.push_str(
        "@vn2_wait_choices = internal global %vn2.choices zeroinitializer

define i64 @vn2_pick_waiting(ptr %states, i64 %count) {
entry:
  %choice_ptr = call ptr @vn2_take_choice(ptr @vn2_wait_choices)
  %exhausted = icmp eq ptr %choice_ptr, null
  br i1 %exhausted, label %fallback, label %scripted
scripted:
  %choice = load i64, ptr %choice_ptr
  ret i64 %choice
fallback:
  %pos = load i64, ptr @script_pos
  %end = load i64, ptr @script_end
  %empty = icmp eq i64 %pos, %end
  %one = icmp eq i64 %count, 1
  %default = or i1 %empty, %one
  br i1 %default, label %first, label %lookup
lookup:
  %slot = getelementptr i64, ptr @vn2_script_controls, i64 %pos
  %wanted = load i64, ptr %slot
  br label %scan
scan:
  %i = phi i64 [ 0, %lookup ], [ %next, %advance ]
  %addr = getelementptr ptr, ptr %states, i64 %i
  %state = load ptr, ptr %addr
  %id = load i64, ptr %state
  %match = icmp eq i64 %id, %wanted
  br i1 %match, label %found, label %advance
advance:
  %next = add i64 %i, 1
  %last = icmp eq i64 %next, %count
  br i1 %last, label %first, label %scan
found:
  ret i64 %i
first:
  ret i64 0
}
",
    );
}
