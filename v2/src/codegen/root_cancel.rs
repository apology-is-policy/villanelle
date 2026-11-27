//! Cancellation of the innermost native run at a scheduling turn ([E-Cancel]).
use super::*;

fn requests(program: &Program) -> impl Iterator<Item = (ControlId, bool)> + '_ {
    operations(program).filter_map(|op| {
        let (id, awaits) = match *op {
            Operation::AwaitControl(id) => (id, true),
            Operation::RunControl(id) => (id, false),
            _ => return None,
        };
        program.controls[id]
            .is_cancellable()
            .then_some((id, awaits))
    })
}

pub(super) fn needed(program: &Program) -> bool {
    requests(program).next().is_some()
}

pub(super) fn emit_support(out: &mut String, reg: &mut RuntimeRegistry<'_>, scripted: bool) {
    if !reg.has_root_cancel {
        if reg.has_task_sets {
            // The shared scheduler has no observable cancellation in this module.
            out.push_str(
                "define internal fastcc i1 @vn2_poll_cancel() alwaysinline { ret i1 false }\n",
            );
        }
        return;
    }
    if scripted {
        out.push_str(
            "@vn2_cancel_at = internal global i64 0
@vn2_cancel_scheduled = internal global i1 false
define internal i8 @vn2_should_cancel_root(i64 %turn) {
  %enabled = load i1, ptr @vn2_cancel_scheduled
  %at = load i64, ptr @vn2_cancel_at
  %due = icmp uge i64 %turn, %at
  %answer = and i1 %enabled, %due
  %result = zext i1 %answer to i8
  ret i8 %result
}
",
        );
    } else {
        out.push_str("declare i8 @vn2_should_cancel_root(i64)\n");
    }

    // Synchronous controls can start runs, including inside host callbacks.
    // Each C entry saves the enclosing execution. Nested language runs inherit
    // the current flag and share the turn count, then restore the caller's flag.
    out.push_str(
        "@vn2_turn_number = internal thread_local global i64 0
@vn2_root_cancelled = internal thread_local global i1 false
define internal fastcc i1 @vn2_poll_cancel() {
  %previous = load i64, ptr @vn2_turn_number
  %turn = add i64 %previous, 1
  store i64 %turn, ptr @vn2_turn_number
  %cancelled = load i1, ptr @vn2_root_cancelled
  br i1 %cancelled, label %already, label %ask
already:
  ret i1 true
ask:
  %answer = call i8 @vn2_should_cancel_root(i64 %turn)
  %flag = icmp ne i8 %answer, 0
  store i1 %flag, ptr @vn2_root_cancelled
  ret i1 %flag
}
",
    );
    for (id, awaits) in requests(reg.program).collect::<BTreeSet<_>>() {
        emit_request(out, reg, id, awaits);
    }
}

pub(super) fn poll(em: &mut IrEmitter<'_, '_>) {
    if em.reg.has_root_cancel {
        em.code.push_str("  call fastcc i1 @vn2_poll_cancel()\n");
    }
}

/// A host operation bound by a root await or a direct run.
/// The request fields already hold the operands and result slots. The runtime
/// retains the by-value operands until completion transfers them to the host.
fn emit_request(out: &mut String, reg: &mut RuntimeRegistry<'_>, id: ControlId, awaits: bool) {
    let kind = if awaits { "await" } else { "run" };
    let program = reg.program;
    let control = &program.controls[id];
    let name = &control.name;
    let cancelled_tag = control
        .contract
        .iter()
        .position(|a| a.name == "cancelled")
        .unwrap();
    let scheduled = awaits && reg.has_task_sets;
    let scheduler_arg = if scheduled { ", ptr %scheduler" } else { "" };
    let wait = if scheduled {
        "@vn2_wait_for_root(ptr %scheduler, ptr %request, i1 true)"
    } else {
        "@vn2_poll_cancel()"
    };
    let _ = writeln!(
        out,
        "define internal fastcc i32 @vn2_{kind}_host_{id}(ptr %request{scheduler_arg}) {{
entry:
  %flag = load i1, ptr @vn2_root_cancelled
  br i1 %flag, label %release, label %start
start:
  call void @vn2_start_{name}(ptr %request)
  %requested = call fastcc i1 {wait}
  br i1 %requested, label %withdraw, label %complete
withdraw:
  call void @vn2_withdraw_{name}(ptr %request)
  br label %release
release:"
    );
    let mut em = IrEmitter::new(program, reg);
    for (i, param) in control.parameters.iter().enumerate() {
        if needs_runtime_cleanup(program, &param.ty) {
            let field = em.fresh_reg();
            let index = i + 1;
            let _ = writeln!(
                em.code,
                "  {field} = getelementptr %vn2.wait.{id}, ptr %request, i32 0, i32 {index}"
            );
            if is_c_scalar_by_val(program, &param.ty) {
                em.emit_release_ptr(&field, &param.ty);
            } else {
                let place = em.fresh_reg();
                let _ = writeln!(em.code, "  {place} = load ptr, ptr {field}");
                em.emit_release_ptr(&place, &param.ty);
            }
        }
    }
    out.push_str(&em.code);
    // A direct run ends in the caller's turn on release or completion.
    // An await must offer its task a ready turn. Withdrawal already polled
    // for cancellation in that turn; an early cancellation or completion did not.
    if awaits {
        out.push_str("  br i1 %flag, label %next_turn, label %resume\n");
    } else {
        let _ = writeln!(out, "  ret i32 {cancelled_tag}");
    }
    out.push_str("complete:\n");
    if !scheduled {
        out.push_str("  call i64 @vn2_pick_waiting(ptr %request, i64 1)\n");
    }
    let _ = writeln!(
        out,
        "  %completed = call i32 @vn2_complete_{name}(ptr %request)"
    );
    if !awaits {
        out.push_str("  ret i32 %completed\n}\n");
        return;
    }
    let choose = if scheduled {
        "call fastcc void @vn2_choose_owner_polled(ptr %scheduler, ptr null)"
    } else {
        "call i64 @vn2_pick_turn(i64 1)"
    };
    let _ = writeln!(
        out,
        "  br label %next_turn
next_turn:
  %result = phi i32 [ {cancelled_tag}, %release ], [ %completed, %complete ]
  call fastcc i1 @vn2_poll_cancel()
  br label %resume
resume:
  %tag = phi i32 [ {cancelled_tag}, %release ], [ %result, %next_turn ]
  {choose}
  ret i32 %tag
}}"
    );
}
