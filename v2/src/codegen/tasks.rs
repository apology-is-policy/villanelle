//! Native task sets whose spawn sites execute at most once per invocation.
//! The owner keeps one activation per site on its stack. A member runs from
//! entry to exit in one turn and keeps its result until the owner receives it.
use super::*;

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

pub(super) fn emit_support(
    out: &mut String,
    program: &Program,
    bits: u32,
    term_tys: &[Option<Type>],
) -> Result<(), String> {
    let mut members = BTreeSet::new();
    for control in &program.controls {
        let Some(body) = &control.body else { continue };
        let mut sets = producers(body);
        let Some(member) = sets.next() else { continue };
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
                        Some(Operation::AwaitControl(_)) => {
                            Some("await of another control in a task-set owner")
                        }
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
        members.insert(member);
    }
    if members.is_empty() {
        return Ok(());
    }
    out.push_str(include_str!("task_set.ll"));
    for id in members {
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
        if member.faults
            || term_tys[id].is_some()
            || uses_loans
            || producers(body).next().is_some()
            || body
                .bodies
                .iter()
                .flat_map(|b| &b.statements)
                .filter_map(|s| operation(&s.command))
                .any(|op| matches!(op, Operation::AwaitControl(_) | Operation::AwaitNext(_, _)))
        {
            return Err(format!(
                "the native backend needs a nonfaulting, nonsuspending task-set producer with owned or copy inputs and results for `{}`",
                member.name
            ));
        }
        emit_member(out, program, id, bits);
    }
    Ok(())
}

// The next link is at offset zero for the queue. The rest belongs to this
// producer: its result tag, bound inputs, and one destination per output.
fn emit_member(out: &mut String, program: &Program, id: ControlId, bits: u32) {
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
    let _ = writeln!(out, "{ty} = type {{ {} }}", fields.join(", "));
    let _ = writeln!(
        out,
        "define internal fastcc void @vn2_member_{id}(ptr %frame) {{"
    );
    let mut args = Vec::new();
    for (i, field) in fields.iter().enumerate().skip(2) {
        let _ = writeln!(
            out,
            "  %slot{i} = getelementptr {ty}, ptr %frame, i32 0, i32 {i}"
        );
        if i - 2 < member.parameters.len() {
            let _ = writeln!(out, "  %arg{i} = load {field}, ptr %slot{i}");
            args.push(format!("{field} %arg{i}"));
        } else {
            args.push(format!("ptr %slot{i}"));
        }
    }
    let _ = writeln!(
        out,
        "  %tag = call fastcc i32 @vn2_ctrl_{id}({})",
        args.join(", ")
    );
    let _ = writeln!(
        out,
        "  %result = getelementptr {ty}, ptr %frame, i32 0, i32 1\n  store i32 %tag, ptr %result\n  ret void\n}}\n"
    );
}

fn pool(em: &mut IrEmitter<'_, '_>, set: VarId) -> String {
    let ptr = em.fresh_reg();
    let _ = writeln!(em.code, "  {ptr} = load ptr, ptr %slot_{set}");
    ptr
}

fn field(em: &mut IrEmitter<'_, '_>, ty: &str, ptr: &str, index: usize) -> String {
    let result = em.fresh_reg();
    let _ = writeln!(
        em.code,
        "  {result} = getelementptr {ty}, ptr {ptr}, i32 0, i32 {index}"
    );
    result
}

pub(super) fn new_set(em: &mut IrEmitter<'_, '_>) -> String {
    let ptr = em.alloc_temp("%vn2.pool");
    let _ = writeln!(em.code, "  call fastcc void @vn2_pool_init(ptr {ptr})");
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
    let _ = writeln!(
        em.code,
        "  {frame} = call fastcc ptr @vn2_next(ptr {ptr}, ptr @vn2_member_{id})"
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
