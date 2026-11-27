//! Native task sets. Single-execution spawns can use the owner's activation.
//! Repeated spawns and recursively nested owners use separate member frames.
use super::*;

// Keep the common prefix in sync with %vn2.member_header in task_set.ll.
const FIRST_INPUT: usize = 5;

#[derive(Clone, Copy)]
pub(super) enum Frame {
    Member,
    Nested,
}

fn producers(body: &ControlBody) -> impl Iterator<Item = ControlId> + '_ {
    body.vars.iter().filter_map(|var| match var.ty {
        Type::Tasks(id, _) => Some(id),
        _ => None,
    })
}

pub(super) fn uses_sets(program: &Program) -> bool {
    program
        .controls
        .iter()
        .filter_map(|c| c.body.as_ref())
        .any(|body| producers(body).next().is_some())
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
        let mut owned = producers(body).peekable();
        if owned.peek().is_none() {
            continue;
        }
        let reason = body
            .bodies
            .iter()
            .flat_map(|body| &body.statements)
            .find_map(|s| match &s.command {
                Command::Cancel { .. } => Some("task set cancellation"),
                Command::Fault { .. } | Command::Boundary { .. } | Command::Supervise { .. } => {
                    Some("a fault boundary or fault in a task-set owner")
                }
                _ => match operation(&s.command) {
                    Some(Operation::Control(cid) | Operation::RunControl(cid))
                        if program.controls[*cid].faults || term_tys[*cid].is_some() =>
                    {
                        Some("a faulting or terminating call in a task-set owner")
                    }
                    _ => None,
                },
            });
        if let Some(reason) = reason {
            return Err(format!(
                "control `{}`: the native backend does not yet support {reason}",
                control.name
            ));
        }
        check_owner_awaits(program, control, body, term_tys)?;
        members.extend(owned);
    }
    if members.is_empty() {
        return Ok(());
    }
    reg.needed_libc = true;
    out.push_str(include_str!("task_set.ll"));
    let mut nested = BTreeSet::new();
    for id in members {
        let member = &program.controls[id];
        // A run starts its own scheduler. Only await extends this task's stack.
        let mut pending: Vec<_> = awaits(member.body.as_ref().unwrap()).collect();
        while let Some(callee) = pending.pop() {
            let target = &program.controls[callee];
            let body = target.body.as_ref().ok_or_else(|| {
                format!(
                    "the native backend does not yet support await of extern `{}` in task-set member `{}`",
                    target.name, member.name
                )
            })?;
            if needs_activation(body) && nested.insert(callee) {
                pending.extend(awaits(body));
            }
        }
        emit_member(out, program, id, reg, term_tys)?;
    }
    for id in nested {
        let control = &program.controls[id];
        emit_body_unit(
            out,
            program,
            reg,
            term_tys,
            UnitKind::Control {
                id,
                frame: Some(Frame::Nested),
            },
            &format!("vn2_nested_{id}"),
            &control_parameters(control),
            control.body.as_ref().unwrap(),
            control.faults.then(|| "%out_fault".into()),
            term_tys[id]
                .as_ref()
                .map(|ty| ("%out_term".into(), ty.clone())),
            control.parameters.len(),
        )?;
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

// A member gives up its turn both at a defined await and at await next.
fn needs_activation(body: &ControlBody) -> bool {
    awaits(body).next().is_some() || producers(body).next().is_some()
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
        let Some(body) = &target.body else {
            if target.is_cancellable() || target.faults {
                return Err(format!(
                    "the native backend does not yet support a cancellable or faulting host await of `{}` in task-set owner `{}`",
                    target.name, owner.name
                ));
            }
            continue;
        };
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
    if member.faults || term_tys[id].is_some() {
        return Err(format!(
            "the native backend needs a nonfaulting task-set producer for `{}`",
            member.name
        ));
    }

    if needs_activation(body) {
        return emit_body_unit(
            out,
            program,
            reg,
            term_tys,
            UnitKind::Control {
                id,
                frame: Some(Frame::Member),
            },
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

// The common header precedes the inputs, result destinations and local slots. Every resume gets
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
    let mut fields = vec![
        "ptr".into(),
        "i32".into(),
        "i1".into(),
        "i1".into(),
        "ptr".into(),
    ];
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
        "define internal fastcc i32 @vn2_member_{id}(ptr %task_member, ptr %task_scheduler) nounwind {{\nentry:"
    );
    let mut args: Vec<_> = member
        .parameters
        .iter()
        .enumerate()
        .map(|(i, _)| format!("{} %p{i}", fields[FIRST_INPUT + i]))
        .collect();
    let mut index = FIRST_INPUT + member.parameters.len();
    for (alt, alternative) in member.contract.iter().enumerate() {
        for field in 0..alternative.fields.len() {
            let name = format!("%out_{alt}_{field}");
            let _ = writeln!(
                out,
                "  {name} = getelementptr {ty}, ptr %task_member, i32 0, i32 {index}"
            );
            args.push(format!("ptr {name}"));
            index += 1;
        }
    }
    emit_local_addresses(out, &ty, "%task_member", locals_start, slots);
    if !resume_points.is_empty() {
        let _ = writeln!(
            out,
            "  %member_state = getelementptr {ty}, ptr %task_member, i32 0, i32 1"
        );
        emit_resume_switch(out, resume_points);
    }
    for i in 0..member.parameters.len() {
        let index = FIRST_INPUT + i;
        let ll = &fields[index];
        let _ = writeln!(
            out,
            "  %in_{i} = getelementptr {ty}, ptr %task_member, i32 0, i32 {index}\n  %p{i} = load {ll}, ptr %in_{i}"
        );
    }
    args
}

fn emit_local_addresses(
    out: &mut String,
    ty: &str,
    base: &str,
    start: usize,
    slots: &[(String, String)],
) {
    for (i, (name, _)) in slots.iter().enumerate() {
        let index = start + i;
        let _ = writeln!(
            out,
            "  {name} = getelementptr {ty}, ptr {base}, i32 0, i32 {index}"
        );
    }
}

fn emit_resume_switch(out: &mut String, points: &[String]) {
    out.push_str("  %pc = load i32, ptr %member_state\n  switch i32 %pc, label %bad_pc [\n    i32 0, label %start\n");
    for (i, label) in points.iter().enumerate() {
        let _ = writeln!(out, "    i32 {}, label %{label}", i + 1);
    }
    out.push_str("  ]\nbad_pc:\n  unreachable\nstart:\n");
}

pub(super) fn emit_nested_entry(
    out: &mut String,
    id: ControlId,
    bound: &[(String, String)],
    slots: &[(String, String)],
    points: &[String],
) {
    let ty = format!("%vn2.activation.{id}");
    let mut fields = vec!["i32"];
    fields.extend(slots.iter().map(|(_, ll)| ll.as_str()));
    let _ = writeln!(out, "{ty} = type {{ {} }}", fields.join(", "));
    let _ = writeln!(
        out,
        "define internal fastcc ptr @vn2_activate_{id}() nounwind {{\n  %ptr = call ptr @malloc(i64 ptrtoint (ptr getelementptr ({ty}, ptr null, i32 1) to i64))\n  store i32 0, ptr %ptr\n  ret ptr %ptr\n}}"
    );
    let _ = writeln!(
        out,
        "define internal fastcc i32 @vn2_nested_{id}(ptr %frame, ptr %member_state, ptr %task_member, ptr %task_scheduler) nounwind {{\nentry:"
    );
    load_await_fields(out, id, bound);
    emit_local_addresses(out, &ty, "%member_state", 1, slots);
    emit_resume_switch(out, points);
}

// The bound arguments live in the caller. A callee that can itself suspend
// needs its own PC and locals until it returns, including on a recursive edge.
// All activations of this task park and wake the same scheduler member.
pub(super) fn await_in_member(em: &mut IrEmitter<'_, '_>, id: ControlId, frame: &str, tag: &str) {
    let nested = em.program.controls[id]
        .body
        .as_ref()
        .is_some_and(needs_activation);
    let activation = nested.then(|| {
        let slot = em.alloc_temp("ptr");
        let ptr = em.fresh_reg();
        em.reg.needed_libc = true;
        let _ = writeln!(
            em.code,
            "  {ptr} = call fastcc ptr @vn2_activate_{id}()\n  store ptr {ptr}, ptr {slot}"
        );
        slot
    });

    let points = em.resume_points.as_mut().unwrap();
    let pc = points.len() + 1;
    let label = format!("member_resume_{pc}");
    points.push(label.clone());
    let _ = writeln!(
        em.code,
        "  store i32 {pc}, ptr %member_state\n  ret i32 -3\n{label}:"
    );
    if let Some(slot) = activation {
        let ptr = em.fresh_reg();
        let yielded = em.fresh_reg();
        let pending = em.fresh_label("nested_yield");
        let done = em.fresh_label("nested_done");
        let _ = writeln!(
            em.code,
            "  {ptr} = load ptr, ptr {slot}\n  {tag} = call fastcc i32 @vn2_nested_{id}(ptr {frame}, ptr {ptr}, ptr %task_member, ptr %task_scheduler)"
        );
        let _ = writeln!(
            em.code,
            "  {yielded} = icmp eq i32 {tag}, -3\n  br i1 {yielded}, label %{pending}, label %{done}\n{pending}:\n  ret i32 -3\n{done}:\n  call void @free(ptr {ptr})"
        );
    } else {
        let _ = writeln!(
            em.code,
            "  {tag} = call fastcc i32 @vn2_resume_{id}(ptr {frame}, ptr null)"
        );
    }
}

fn pool(em: &mut IrEmitter<'_, '_>, set: VarId) -> String {
    let ptr = em.fresh_reg();
    let _ = writeln!(em.code, "  {ptr} = load ptr, ptr %slot_{set}");
    ptr
}

pub(super) fn init_owner(em: &mut IrEmitter<'_, '_>, body: &ControlBody) {
    if em.resume_points.is_none() && producers(body).next().is_some() {
        em.slots
            .push(("%root_scheduler".into(), "%vn2.scheduler".into()));
        em.code
            .push_str("  %task_scheduler = call fastcc ptr @vn2_owner_scheduler(ptr %owner_scheduler, ptr %root_scheduler)\n");
    }
}

pub(super) fn owner_scheduler(body: &ControlBody) -> &'static str {
    if producers(body).next().is_some() {
        "%task_scheduler"
    } else {
        "%owner_scheduler"
    }
}

/// A defined await in the same task inherits every ready child of its owner.
pub(super) fn choose_owner(em: &mut IrEmitter<'_, '_>, body: &ControlBody) -> &'static str {
    if !em.reg.has_task_sets {
        em.code.push_str("  call i64 @vn2_pick_turn(i64 1)\n");
        return "null";
    }
    let scheduler = owner_scheduler(body);
    let _ = writeln!(
        em.code,
        "  call fastcc void @vn2_choose_owner(ptr {scheduler}, ptr null)"
    );
    scheduler
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
    let slot = field(em, "%vn2.pool", &ptr, 1);
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
    repeated: bool,
) {
    let ty = format!("%vn2.member.{id}");
    let values = em.emit_exprs_ordered(args, &VarAccess::ControlSlots(body));
    let ptr = pool(em, set);
    // A member frame can contain a leaf child inline. Give a nested owner
    // separate storage so even recursive spawns have finite frame layouts.
    let child = &em.program.controls[id];
    let heap_frame = repeated
        || (em.resume_points.is_some()
            && producers(child.body.as_ref().expect("defined producer"))
                .next()
                .is_some());
    let frame = if heap_frame {
        let frame = em.fresh_reg();
        let _ = writeln!(
            em.code,
            "  {frame} = call fastcc ptr @vn2_take_frame(ptr {ptr}, i64 ptrtoint (ptr getelementptr ({ty}, ptr null, i32 1) to i64))"
        );
        frame
    } else {
        em.alloc_temp(&ty)
    };
    for (i, (arg, value)) in args.iter().zip(values).enumerate() {
        let ptr = field(em, &ty, &frame, FIRST_INPUT + i);
        let ll = em.llvm_ty(&arg.ty());
        let _ = writeln!(em.code, "  store {ll} {value}, ptr {ptr}");
    }
    let max = if em.reg.usize_bits == 32 {
        u64::from(u32::MAX)
    } else {
        u64::MAX
    };
    let _ = writeln!(
        em.code,
        "  call fastcc void @vn2_spawn(ptr %task_scheduler, ptr {ptr}, ptr {frame}, i1 {heap_frame}, i64 {max})"
    );
}

pub(super) fn next(
    em: &mut IrEmitter<'_, '_>,
    set: VarId,
    id: ControlId,
) -> (String, Vec<Vec<String>>) {
    let awaited = pool(em, set);
    let ptr = if let Some(points) = &mut em.resume_points {
        let pc = points.len() + 1;
        let resume = format!("member_next_{pc}");
        points.push(resume.clone());
        let _ = writeln!(em.code, "  store i32 {pc}, ptr %member_state");
        let _ = writeln!(
            em.code,
            "  call fastcc void @vn2_wait_member(ptr %task_scheduler, ptr %task_member, ptr {awaited})\n  ret i32 -3\n{resume}:"
        );
        pool(em, set)
    } else {
        let _ = writeln!(
            em.code,
            "  call fastcc void @vn2_choose_owner(ptr %task_scheduler, ptr {awaited})"
        );
        awaited
    };
    let ty = format!("%vn2.member.{id}");
    let frame = em.fresh_reg();
    let empty = em.fresh_reg();
    let empty_label = em.fresh_label("pool_empty");
    let member_label = em.fresh_label("pool_member");
    let join = em.fresh_label("pool_result");
    let _ = writeln!(
        em.code,
        "  {frame} = call fastcc ptr @vn2_take_result(ptr {ptr})"
    );
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
    // The selected arm loads each value before the frame can be reused. For a
    // borrow this copies the pointer into the owner's slot. Empty has no fields;
    // an ordinary (non-inbounds) GEP does not dereference its base.
    let mut index = FIRST_INPUT + member.parameters.len();
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
