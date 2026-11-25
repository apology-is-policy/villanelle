//! Native task sets whose spawn sites execute at most once per invocation.
//! The owner keeps one activation per site on its stack. A member keeps its locals
//! across defined awaits and its result until the owner receives it.
use super::*;

fn sets(body: &ControlBody) -> impl Iterator<Item = (VarId, ControlId)> + '_ {
    body.vars
        .iter()
        .enumerate()
        .filter_map(|(slot, var)| match var.ty {
            Type::Tasks(id, _) => Some((slot, id)),
            _ => None,
        })
}

pub(super) fn uses_sets(program: &Program) -> bool {
    program
        .controls
        .iter()
        .filter_map(|c| c.body.as_ref())
        .any(|body| sets(body).next().is_some())
}

pub(super) fn emit_support<'a>(
    out: &mut String,
    program: &'a Program,
    reg: &mut RuntimeRegistry<'a>,
    term_tys: &[Option<Type>],
) -> Result<(), String> {
    let mut members = BTreeSet::new();
    for control in &program.controls {
        let Some(body) = &control.body else { continue };
        let mut sets = sets(body);
        let Some((_, member)) = sets.next() else {
            continue;
        };
        let reason = if sets.next().is_some() {
            Some("multiple task sets in one owner")
        } else {
            body.bodies
                .iter()
                .enumerate()
                .flat_map(|(id, body)| body.statements.iter().map(move |s| (id, &s.command)))
                .find_map(|(id, command)| match command {
                    Command::Spawn { .. } if id != 0 => {
                        Some("task-set spawn outside the owner's top-level body")
                    }
                    Command::Cancel { .. } => Some("task set cancellation"),
                    Command::Fault { .. }
                    | Command::Boundary { .. }
                    | Command::Supervise { .. } => {
                        Some("a fault boundary or fault in a task-set owner")
                    }
                    _ => match operation(command) {
                        Some(Operation::Control(cid) | Operation::RunControl(cid))
                            if program.controls[*cid].faults || term_tys[*cid].is_some() =>
                        {
                            Some("a faulting or terminating call in a task-set owner")
                        }
                        _ => None,
                    },
                })
        };
        if let Some(reason) = reason {
            return Err(format!(
                "control `{}`: the native backend does not yet support {reason}",
                control.name
            ));
        }
        check_owner_awaits(program, control, body, term_tys)?;
        members.insert(member);
    }
    if members.is_empty() {
        return Ok(());
    }
    out.push_str(include_str!("task_set.ll"));
    for id in members {
        emit_member(out, program, id, reg, term_tys)?;
    }
    Ok(())
}

fn awaits(body: &ControlBody) -> impl Iterator<Item = ControlId> + '_ {
    body.bodies
        .iter()
        .flat_map(|b| &b.statements)
        .filter_map(|s| match operation(&s.command) {
            Some(Operation::AwaitControl(callee)) => Some(*callee),
            _ => None,
        })
}

fn awaited_body<'a>(
    target: &'a Control,
    role: &str,
    caller: &str,
) -> Result<&'a ControlBody, String> {
    let Some(body) = &target.body else {
        return Err(format!(
            "the native backend does not yet support await of extern `{}` in task-set {role} `{caller}`",
            target.name
        ));
    };
    if sets(body).next().is_some() {
        return Err(format!(
            "the native backend does not yet support task-set {role} `{caller}` awaiting `{}`, which creates a set",
            target.name
        ));
    }
    Ok(body)
}

// Follow only await edges. A nested run has its own ready tasks.
fn check_owner_awaits(
    program: &Program,
    owner: &Control,
    body: &ControlBody,
    term_tys: &[Option<Type>],
) -> Result<(), String> {
    let mut pending: Vec<_> = awaits(body).collect();
    let mut visited = BTreeSet::new();
    while let Some(id) = pending.pop() {
        if !visited.insert(id) {
            continue;
        }
        let target = &program.controls[id];
        let body = awaited_body(target, "owner", &owner.name)?;
        if target.faults || term_tys[id].is_some() {
            return Err(format!(
                "await of `{}` from `{}`: the native backend does not yet support a faulting or terminating call in a task-set owner",
                target.name, owner.name
            ));
        }
        pending.extend(awaits(body));
    }
    Ok(())
}

fn emit_member<'a>(
    out: &mut String,
    program: &'a Program,
    id: ControlId,
    reg: &mut RuntimeRegistry<'a>,
    term_tys: &[Option<Type>],
) -> Result<(), String> {
    let member = &program.controls[id];
    let body = member
        .body
        .as_ref()
        .expect("[W10] requires a defined producer");
    let uses_loans = member
        .parameters
        .iter()
        .chain(member.contract.iter().flat_map(|alt| &alt.fields))
        .any(|p| program.contains_borrow_or_view(&p.ty));
    if member.faults || term_tys[id].is_some() || uses_loans || sets(body).next().is_some() {
        return Err(format!(
            "the native backend needs a nonfaulting task-set producer with owned or copy inputs and results and no task set of its own for `{}`",
            member.name
        ));
    }

    let mut callees = awaits(body).peekable();
    if callees.peek().is_some() {
        // Ordinary synchronous calls can start a nested run, whose tasks have
        // their own ready set. An awaited callee shares this member's turn.
        for callee in callees {
            let target = &program.controls[callee];
            let body = awaited_body(target, "member", &member.name)?;
            if awaits(body).next().is_some() {
                return Err(format!(
                    "the native backend does not yet support task-set member `{}` awaiting `{}`, whose body can suspend again",
                    member.name, target.name
                ));
            }
        }
        return emit_body_unit(
            out,
            program,
            reg,
            term_tys,
            UnitKind::Control { id, member: true },
            &format!("vn2_member_{id}"),
            &control_parameters(member),
            body,
            None,
            None,
            member.parameters.len(),
        );
    }

    let mut args = emit_member_entry(out, program, id, reg.usize_bits, &[], &[]);
    args.push("ptr null".into());
    let _ = writeln!(
        out,
        "  %tag = call fastcc i32 @vn2_ctrl_{id}({})\n  ret i32 %tag\n}}\n",
        args.join(", ")
    );
    Ok(())
}

// The queue link and resume index/result tag precede the bound inputs,
// result destinations, and slots of the resumable body. Every resume gets
// fresh SSA addresses for the same slots in this invocation of the owner.
pub(super) fn emit_member_entry(
    out: &mut String,
    program: &Program,
    id: ControlId,
    bits: u32,
    slots: &[(String, String)],
    resume_points: &[String],
) -> Vec<String> {
    let member = &program.controls[id];
    let ty = format!("%vn2.member.{id}");
    let mut fields = vec!["ptr".to_string(), "i32".to_string()];
    fields.extend(
        member
            .parameters
            .iter()
            .chain(member.contract.iter().flat_map(|alt| &alt.fields))
            .map(|f| llvm_ty(program, &f.ty, bits)),
    );
    let locals_start = fields.len();
    fields.extend(slots.iter().map(|(_, ty)| ty.clone()));
    let _ = writeln!(out, "{ty} = type {{ {} }}", fields.join(", "));
    let _ = writeln!(
        out,
        "define internal fastcc i32 @vn2_member_{id}(ptr %frame) nounwind {{\nentry:"
    );
    let mut args: Vec<_> = member
        .parameters
        .iter()
        .enumerate()
        .map(|(i, _)| format!("{} %p{i}", fields[i + 2]))
        .collect();
    let mut index = 2 + member.parameters.len();
    for (alt, alternative) in member.contract.iter().enumerate() {
        for field in 0..alternative.fields.len() {
            let name = format!("%out_{alt}_{field}");
            let _ = writeln!(
                out,
                "  {name} = getelementptr {ty}, ptr %frame, i32 0, i32 {index}"
            );
            args.push(format!("ptr {name}"));
            index += 1;
        }
    }
    for (i, (name, _)) in slots.iter().enumerate() {
        let index = locals_start + i;
        let _ = writeln!(
            out,
            "  {name} = getelementptr {ty}, ptr %frame, i32 0, i32 {index}"
        );
    }
    if !resume_points.is_empty() {
        let _ = writeln!(
            out,
            "  %member_state = getelementptr {ty}, ptr %frame, i32 0, i32 1\n  %pc = load i32, ptr %member_state\n  switch i32 %pc, label %bad_pc [\n    i32 0, label %start"
        );
        for (i, label) in resume_points.iter().enumerate() {
            let _ = writeln!(out, "    i32 {}, label %{label}", i + 1);
        }
        out.push_str("  ]\nbad_pc:\n  unreachable\nstart:\n");
    }
    for i in 0..member.parameters.len() {
        let index = 2 + i;
        let ll = &fields[index];
        let _ = writeln!(
            out,
            "  %in_{i} = getelementptr {ty}, ptr %frame, i32 0, i32 {index}\n  %p{i} = load {ll}, ptr %in_{i}"
        );
    }
    args
}

fn pool(em: &mut IrEmitter<'_, '_>, set: VarId) -> String {
    let ptr = em.fresh_reg();
    let _ = writeln!(em.code, "  {ptr} = load ptr, ptr %slot_{set}");
    ptr
}

/// Give the host a turn choice and pass the same set to the next activation.
pub(super) fn choose_owner(em: &mut IrEmitter<'_, '_>, body: &ControlBody) -> String {
    if !em.reg.has_task_sets {
        em.code.push_str("  call i64 @vn2_pick_turn(i64 1)\n");
        return "null".into();
    }
    let peers = match sets(body).next() {
        Some((slot, _)) => pool(em, slot),
        None => "%owner_pool".to_string(),
    };
    let _ = writeln!(
        em.code,
        "  call fastcc void @vn2_choose_owner(ptr {peers}, i1 true)"
    );
    peers
}

fn field(em: &mut IrEmitter<'_, '_>, ty: &str, ptr: &str, index: usize) -> String {
    let result = em.fresh_reg();
    let _ = writeln!(
        em.code,
        "  {result} = getelementptr {ty}, ptr {ptr}, i32 0, i32 {index}"
    );
    result
}

pub(super) fn new_set(em: &mut IrEmitter<'_, '_>, member: ControlId) -> String {
    let ptr = em.alloc_temp("%vn2.pool");
    let _ = writeln!(
        em.code,
        "  call fastcc void @vn2_pool_init(ptr {ptr}, ptr @vn2_member_{member})"
    );
    ptr
}

pub(super) fn count(em: &mut IrEmitter<'_, '_>, set: VarId) -> String {
    let ptr = pool(em, set);
    let slot = field(em, "%vn2.pool", &ptr, 3);
    let total = em.fresh_reg();
    let _ = writeln!(em.code, "  {total} = load i64, ptr {slot}");
    if em.reg.usize_bits == 64 {
        return total;
    }
    let narrow = em.fresh_reg();
    let _ = writeln!(em.code, "  {narrow} = trunc i64 {total} to i32");
    narrow
}

pub(super) fn spawn(
    em: &mut IrEmitter<'_, '_>,
    body: &ControlBody,
    set: VarId,
    id: ControlId,
    args: &[Expr],
) {
    let ty = format!("%vn2.member.{id}");
    let frame = em.alloc_temp(&ty);
    let values = em.emit_exprs_ordered(args, &VarAccess::ControlSlots(body));
    for (i, (arg, value)) in args.iter().zip(values).enumerate() {
        let ptr = field(em, &ty, &frame, i + 2);
        let ll = em.llvm_ty(&arg.ty());
        let _ = writeln!(em.code, "  store {ll} {value}, ptr {ptr}");
    }
    let ptr = pool(em, set);
    let _ = writeln!(
        em.code,
        "  call fastcc void @vn2_spawn(ptr {ptr}, ptr {frame})"
    );
}

pub(super) fn next(
    em: &mut IrEmitter<'_, '_>,
    set: VarId,
    id: ControlId,
) -> (String, Vec<Vec<String>>) {
    let ptr = pool(em, set);
    let ty = format!("%vn2.member.{id}");
    let frame = em.fresh_reg();
    let empty = em.fresh_reg();
    let empty_label = em.fresh_label("pool_empty");
    let member_label = em.fresh_label("pool_member");
    let join = em.fresh_label("pool_result");
    let _ = writeln!(em.code, "  {frame} = call fastcc ptr @vn2_next(ptr {ptr})");
    let _ = writeln!(
        em.code,
        "  {empty} = icmp eq ptr {frame}, null\n  br i1 {empty}, label %{empty_label}, label %{member_label}"
    );
    let _ = writeln!(
        em.code,
        "{empty_label}:\n  store ptr null, ptr %slot_{set}\n  br label %{join}\n{member_label}:"
    );
    let tag_slot = field(em, &ty, &frame, 1);
    let member_tag = em.fresh_reg();
    let _ = writeln!(
        em.code,
        "  {member_tag} = load i32, ptr {tag_slot}\n  br label %{join}\n{join}:"
    );
    let member = &em.program.controls[id];
    let tag = em.fresh_reg();
    let _ = writeln!(
        em.code,
        "  {tag} = phi i32 [ {}, %{empty_label} ], [ {member_tag}, %{member_label} ]",
        member.contract.len()
    );
    // Only the selected alternative loads through these addresses. Empty has
    // no fields; an ordinary (non-inbounds) GEP does not dereference its base.
    let mut index = 2 + member.parameters.len();
    let mut slots = Vec::new();
    for alt in &member.contract {
        let mut fields = Vec::new();
        for _ in &alt.fields {
            fields.push(field(em, &ty, &frame, index));
            index += 1;
        }
        slots.push(fields);
    }
    slots.push(Vec::new());
    (tag, slots)
}
