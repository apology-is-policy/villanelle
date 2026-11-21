//! Call expansion: Theorem 4 of `docs/v2/core.md`.
//!
//! > **Theorem 4 (expansion).** Expanding a decision on a defined control in
//! > place (the control's body with fresh names and sites, its parameters bound
//! > to the arguments, and each exit replaced by the caller's continuation for
//! > that alternative) yields a checked program with the same observations.
//!
//! [`expand`] takes a [`syntax::Program`], resolves it to check well-formedness,
//! and expands every decision on a defined control in place across all control
//! bodies and named boundaries. Any `■` (`Exit`) inside a loop of a callee is
//! first lifted out of the loop through a fresh `□` (`Leave`) alternative so
//! that all exits of a callee stand at the top level of its body before
//! inlining. Slice 2 support also handles `&τ`/`&~τ` borrow substitution,
//! `old(y)` snapshots, `struct`/`variant`/collection/resource constructs, and
//! lexical/named boundaries.

use crate::int::Int;
use crate::resolve;
use crate::syntax::{
    Alternative, Arm, Command, Control, Declaration, Expr, LoopParameter, Place, PlaceStep,
    Program, Selector, Statement,
};
use crate::typed::{BorrowMode, IntType, Type};
use std::collections::{HashMap, HashSet};

/// Expands every decision on a defined control in `program` in place.
pub fn expand(program: &Program) -> Result<Program, resolve::Error> {
    // Ensure the input program is well-resolved before expanding.
    let _ = resolve::resolve(program)?;

    let mut controls_by_name: HashMap<String, Control> = HashMap::new();
    for decl in &program.declarations {
        if let Declaration::Control(control) = decl {
            controls_by_name.insert(control.name.clone(), control.clone());
        }
    }

    let mut next_id = 0usize;
    // Expand defined controls iteratively until no defined control body contains
    // a decision on a defined control.
    let max_rounds = controls_by_name.len().max(1) + 1;
    for _ in 0..max_rounds {
        let snapshot = controls_by_name.clone();
        let mut any_expanded = false;
        for control in controls_by_name.values_mut() {
            if control.external {
                continue;
            }
            if has_defined_call(&control.body, &snapshot) {
                control.body = expand_body(
                    &control.body,
                    &snapshot,
                    &program.declarations,
                    &mut next_id,
                );
                any_expanded = true;
            }
        }
        if !any_expanded {
            break;
        }
    }

    // Now also expand any defined control calls inside named boundaries.
    let final_controls = controls_by_name.clone();
    let mut declarations = Vec::new();
    for decl in &program.declarations {
        match decl {
            Declaration::Function(f) => declarations.push(Declaration::Function(f.clone())),
            Declaration::Control(c) => {
                declarations.push(Declaration::Control(controls_by_name[&c.name].clone()));
            }
            Declaration::Boundary(b) => {
                let mut nb = b.clone();
                if has_defined_call(&nb.body, &final_controls) {
                    nb.body = expand_body(
                        &nb.body,
                        &final_controls,
                        &program.declarations,
                        &mut next_id,
                    );
                }
                if has_defined_call(&nb.contingency, &final_controls) {
                    nb.contingency = expand_body(
                        &nb.contingency,
                        &final_controls,
                        &program.declarations,
                        &mut next_id,
                    );
                }
                declarations.push(Declaration::Boundary(nb));
            }
            other => declarations.push(other.clone()),
        }
    }
    Ok(Program { declarations })
}

fn has_exit_in_stmts(statements: &[Statement]) -> bool {
    statements.iter().any(|stmt| match &stmt.command {
        Command::Exit { .. } => true,
        Command::Loop { body, .. } => has_exit_in_stmts(body),
        Command::Boundary {
            body, contingency, ..
        } => has_exit_in_stmts(body) || has_exit_in_stmts(contingency),
        _ => false,
    })
}

fn has_exit_in_boundary(statements: &[Statement]) -> bool {
    statements.iter().any(|stmt| match &stmt.command {
        Command::Boundary {
            body, contingency, ..
        } => has_exit_in_stmts(body) || has_exit_in_stmts(contingency),
        Command::Loop { body, .. } => has_exit_in_boundary(body),
        _ => false,
    })
}

fn is_expandable_callee(controls: &HashMap<String, Control>, operation: &str) -> bool {
    controls
        .get(operation)
        .is_some_and(|c| !c.external && !has_exit_in_boundary(&c.body))
}

fn has_defined_call(statements: &[Statement], controls: &HashMap<String, Control>) -> bool {
    for stmt in statements {
        match &stmt.command {
            Command::Decide { operation, .. } if is_expandable_callee(controls, operation) => {
                return true;
            }
            Command::Loop { body, .. } if has_defined_call(body, controls) => {
                return true;
            }
            Command::Boundary {
                body, contingency, ..
            } if has_defined_call(body, controls) || has_defined_call(contingency, controls) => {
                return true;
            }
            _ => {}
        }
    }
    false
}

fn expand_body(
    statements: &[Statement],
    controls: &HashMap<String, Control>,
    decls: &[Declaration],
    next_id: &mut usize,
) -> Vec<Statement> {
    let mut current: Vec<Statement> = statements
        .iter()
        .map(|stmt| match &stmt.command {
            Command::Loop {
                site,
                name,
                parameters,
                invariant,
                body,
                arms,
            } => Statement {
                selector: stmt.selector.clone(),
                command: Command::Loop {
                    site: site.clone(),
                    name: name.clone(),
                    parameters: parameters.clone(),
                    invariant: invariant.clone(),
                    body: expand_body(body, controls, decls, next_id),
                    arms: arms.clone(),
                },
                line: stmt.line,
            },
            Command::Boundary {
                site,
                body,
                captures,
                message,
                contingency,
            } => Statement {
                selector: stmt.selector.clone(),
                command: Command::Boundary {
                    site: site.clone(),
                    body: expand_body(body, controls, decls, next_id),
                    captures: captures.clone(),
                    message: message.clone(),
                    contingency: expand_body(contingency, controls, decls, next_id),
                },
                line: stmt.line,
            },
            _ => stmt.clone(),
        })
        .collect();

    let mut idx = 0usize;
    while idx < current.len() {
        let is_defined_decide = match &current[idx].command {
            Command::Decide { operation, .. } => is_expandable_callee(controls, operation),
            _ => false,
        };
        if !is_defined_decide {
            idx += 1;
            continue;
        }

        let call_stmt = current.remove(idx);
        let call_guard = call_stmt.selector;
        let call_line = call_stmt.line;
        let Command::Decide {
            site: call_site,
            operation,
            arguments,
            arms: caller_arms,
        } = call_stmt.command
        else {
            unreachable!();
        };

        let callee = &controls[&operation];
        let call_id = *next_id;
        *next_id += 1;

        let (inlined_stmts, alt_selectors, dead_vars) = inline_callee(
            callee,
            &call_guard,
            call_line,
            &arguments,
            &caller_arms,
            decls,
            call_id,
            next_id,
        );

        let mut count = inlined_stmts.len();
        for (offset, s) in inlined_stmts.into_iter().enumerate() {
            current.insert(idx + offset, s);
        }

        // Substitute `Selector::Atom(call_site, alt)` in all subsequent
        // statements of this body (and inside nested loops/boundaries that
        // follow), simplifying booleans and pruning unreachable `¬⊤` blocks.
        let mut alt_map = alt_selectors;
        for later in &mut current[(idx + count)..] {
            substitute_site_in_stmt(later, &call_site, &alt_map);
        }
        prune_dead_statements(&mut current, idx + count, &mut alt_map);

        // Emit `¬⊤ ▷ y_i : ty := default` only for unreachable alternative
        // payload vars that still appear referenced in surviving statements.
        let false_sel = Selector::Not(Box::new(Selector::Top));
        let mut dead_binds = Vec::new();
        for (raw_name, field_ty) in dead_vars {
            let (is_mut, clean_name) = match raw_name.strip_prefix('~') {
                Some(s) => (true, s.to_string()),
                None => (false, raw_name),
            };
            if is_var_used_in_stmts(&current[(idx + count)..], &clean_name)
                && let Some(def_val) = default_expr_for_decls(&field_ty, decls)
            {
                dead_binds.push(Statement {
                    selector: false_sel.clone(),
                    command: Command::Bind {
                        mutable: is_mut,
                        name: clean_name,
                        ty: Some(field_ty),
                        value: def_val,
                    },
                    line: call_line,
                });
            }
        }
        let dead_count = dead_binds.len();
        for (offset, s) in dead_binds.into_iter().enumerate() {
            current.insert(idx + count + offset, s);
        }
        count += dead_count;

        idx += count;
    }

    current
}

fn is_false_selector(sel: &Selector) -> bool {
    matches!(sel, Selector::Not(inner) if matches!(&**inner, Selector::Top))
}

fn simplify_selector(sel: Selector) -> Selector {
    match sel {
        Selector::Top | Selector::Atom(_, _) => sel,
        Selector::Not(inner) => match simplify_selector(*inner) {
            Selector::Top => Selector::Not(Box::new(Selector::Top)),
            Selector::Not(twice) => *twice,
            other => Selector::Not(Box::new(other)),
        },
        Selector::And(l, r) => {
            let sl = simplify_selector(*l);
            let sr = simplify_selector(*r);
            if is_false_selector(&sl) || is_false_selector(&sr) {
                Selector::Not(Box::new(Selector::Top))
            } else if matches!(sl, Selector::Top) {
                sr
            } else if matches!(sr, Selector::Top) {
                sl
            } else {
                Selector::And(Box::new(sl), Box::new(sr))
            }
        }
        Selector::Or(l, r) => {
            let sl = simplify_selector(*l);
            let sr = simplify_selector(*r);
            if matches!(sl, Selector::Top) || matches!(sr, Selector::Top) {
                Selector::Top
            } else if is_false_selector(&sl) {
                sr
            } else if is_false_selector(&sr) {
                sl
            } else {
                Selector::Or(Box::new(sl), Box::new(sr))
            }
        }
    }
}

fn collect_sites_in_command(command: &Command, out: &mut HashSet<String>) {
    match command {
        Command::Test { site, .. } | Command::Decide { site, .. } => {
            out.insert(site.clone());
        }
        Command::Loop { site, body, .. } => {
            out.insert(site.clone());
            for s in body {
                collect_sites_in_command(&s.command, out);
            }
        }
        Command::Boundary {
            site,
            body,
            contingency,
            ..
        } => {
            out.insert(site.clone());
            for s in body {
                collect_sites_in_command(&s.command, out);
            }
            for s in contingency {
                collect_sites_in_command(&s.command, out);
            }
        }
        _ => {}
    }
}

fn replace_sites_with_false(sel: Selector, dropped_sites: &HashSet<String>) -> Selector {
    let rewritten = match sel {
        Selector::Atom(ref site, _) if dropped_sites.contains(site) => {
            Selector::Not(Box::new(Selector::Top))
        }
        Selector::Not(inner) => {
            Selector::Not(Box::new(replace_sites_with_false(*inner, dropped_sites)))
        }
        Selector::And(l, r) => Selector::And(
            Box::new(replace_sites_with_false(*l, dropped_sites)),
            Box::new(replace_sites_with_false(*r, dropped_sites)),
        ),
        Selector::Or(l, r) => Selector::Or(
            Box::new(replace_sites_with_false(*l, dropped_sites)),
            Box::new(replace_sites_with_false(*r, dropped_sites)),
        ),
        other => other,
    };
    simplify_selector(rewritten)
}

fn prune_dead_statements(
    stmts: &mut Vec<Statement>,
    start_idx: usize,
    _alt_map: &mut HashMap<String, Selector>,
) {
    loop {
        let mut dropped_sites = HashSet::new();
        for stmt in &stmts[start_idx..] {
            if is_false_selector(&stmt.selector) {
                collect_sites_in_command(&stmt.command, &mut dropped_sites);
            }
        }
        let prev_len = stmts.len();
        let mut i = start_idx;
        while i < stmts.len() {
            if is_false_selector(&stmts[i].selector) {
                stmts.remove(i);
            } else {
                match &mut stmts[i].command {
                    Command::Loop { body, .. } => prune_dead_statements(body, 0, _alt_map),
                    Command::Boundary {
                        body, contingency, ..
                    } => {
                        prune_dead_statements(body, 0, _alt_map);
                        prune_dead_statements(contingency, 0, _alt_map);
                    }
                    _ => {}
                }
                i += 1;
            }
        }
        if dropped_sites.is_empty() && stmts.len() == prev_len {
            break;
        }
        if dropped_sites.is_empty() {
            break;
        }
        for stmt in &mut stmts[start_idx..] {
            stmt.selector = replace_sites_with_false(stmt.selector.clone(), &dropped_sites);
        }
    }
}

fn expr_to_place(expr: &Expr) -> Option<Place> {
    let inner = match expr {
        Expr::Borrow(_, p) => &**p,
        other => other,
    };
    match inner {
        Expr::Name(root) => Some(Place {
            root: root.clone(),
            steps: Vec::new(),
        }),
        Expr::Field(base, field) => {
            let mut place = expr_to_place(base)?;
            place.steps.push(PlaceStep::Field(field.clone()));
            Some(place)
        }
        Expr::Index(base, idx) => {
            let mut place = expr_to_place(base)?;
            place.steps.push(PlaceStep::Index((**idx).clone()));
            Some(place)
        }
        _ => None,
    }
}

fn place_to_expr(place: &Place) -> Expr {
    let mut cur = Expr::Name(place.root.clone());
    for step in &place.steps {
        cur = match step {
            PlaceStep::Field(f) => Expr::Field(Box::new(cur), f.clone()),
            PlaceStep::Index(idx) => Expr::Index(Box::new(cur), Box::new(idx.clone())),
        };
    }
    cur
}

fn collect_old_uses(expr: &Expr, len_old: &mut HashSet<String>, val_old: &mut HashSet<String>) {
    match expr {
        Expr::Len(inner) => {
            if let Expr::Old(name) = &**inner {
                len_old.insert(name.clone());
            } else {
                collect_old_uses(inner, len_old, val_old);
            }
        }
        Expr::Old(name) => {
            val_old.insert(name.clone());
        }
        Expr::Unary(_, e)
        | Expr::Move(e)
        | Expr::Borrow(_, e)
        | Expr::Field(e, _)
        | Expr::Clone(e) => collect_old_uses(e, len_old, val_old),
        Expr::Binary(_, l, r) | Expr::Index(l, r) => {
            collect_old_uses(l, len_old, val_old);
            collect_old_uses(r, len_old, val_old);
        }
        Expr::Call(_, args)
        | Expr::Struct(_, args)
        | Expr::Variant(_, _, args)
        | Expr::Vector(args) => {
            for a in args {
                collect_old_uses(a, len_old, val_old);
            }
        }
        Expr::Integer(_) | Expr::Boolean(_) | Expr::String(_) | Expr::Name(_) | Expr::EmptyMap => {}
    }
}

fn is_copy_type_syntax(ty: &Type, decls: &[Declaration]) -> bool {
    match ty {
        Type::Bool | Type::Int(_) | Type::Ref(BorrowMode::Shared, _) => true,
        Type::Named(name) => decls.iter().any(|d| match d {
            Declaration::Struct(s) if s.name == *name => s.is_copy,
            Declaration::Variant(v) if v.name == *name => v.is_copy,
            _ => false,
        }),
        _ => false,
    }
}

#[allow(clippy::too_many_arguments, clippy::type_complexity)]
fn inline_callee(
    callee: &Control,
    call_guard: &Selector,
    call_line: u32,
    arguments: &[Expr],
    caller_arms: &[Arm],
    decls: &[Declaration],
    call_id: usize,
    next_id: &mut usize,
) -> (
    Vec<Statement>,
    HashMap<String, Selector>,
    Vec<(String, Type)>,
) {
    // 1. Lift any `Command::Exit` inside loops of `callee` to the top level of
    //    `callee.body`.
    let lifted_body = lift_exits_in_body(&callee.body, &callee.contract, next_id);

    // 2. Build injective renamings for all non-borrow variables, sites and loop
    //    names in `lifted_body` and `callee.parameters`.
    let mut var_names = HashSet::new();
    let mut site_names = HashSet::new();
    let mut loop_names = HashSet::new();
    let mut borrow_param_names = HashSet::new();
    for param in &callee.parameters {
        if matches!(param.ty, Type::Ref(_, _)) {
            borrow_param_names.insert(param.name.clone());
        } else {
            var_names.insert(param.name.clone());
        }
    }
    collect_callee_names(
        &lifted_body,
        &mut var_names,
        &mut site_names,
        &mut loop_names,
    );
    for bp in &borrow_param_names {
        var_names.remove(bp);
    }

    let prefix = format!("_exp{call_id}_");
    let var_map: HashMap<String, String> = var_names
        .into_iter()
        .map(|v| (v.clone(), format!("{prefix}{v}")))
        .collect();
    let site_map: HashMap<String, String> = site_names
        .into_iter()
        .map(|s| (s.clone(), format!("{prefix}{s}")))
        .collect();
    let loop_map: HashMap<String, String> = loop_names
        .into_iter()
        .map(|l| (l.clone(), format!("{prefix}{l}")))
        .collect();

    let mut out = Vec::new();
    let mut expr_substs: HashMap<String, Expr> = HashMap::new();
    let mut mut_places: HashMap<String, Place> = HashMap::new();
    let mut rvalue_shared_binds: Vec<Statement> = Vec::new();
    let mut old_binds: Vec<Statement> = Vec::new();

    // Detect `old(param)` and `len(old(param))` in `callee.contract`.
    let mut len_old_params = HashSet::new();
    let mut val_old_params = HashSet::new();
    for alt in &callee.contract {
        if let Some(cond) = &alt.condition {
            collect_old_uses(cond, &mut len_old_params, &mut val_old_params);
        }
    }

    // 3. Evaluate & bind parameters in `[E-Operands]` order: non-lending first,
    //    then borrow substitutions & `old(...)` snapshots.
    for (param, arg_expr) in callee.parameters.iter().zip(arguments) {
        match &param.ty {
            Type::Ref(BorrowMode::Exclusive, inner_ty) => {
                let place =
                    expr_to_place(arg_expr).expect("exclusive borrow argument must be a place");
                let p_expr = place_to_expr(&place);
                if len_old_params.contains(&param.name) {
                    let old_len_name = format!("{prefix}old_len_{}", param.name);
                    old_binds.push(Statement {
                        selector: call_guard.clone(),
                        command: Command::Bind {
                            mutable: false,
                            name: old_len_name,
                            ty: Some(Type::Int(IntType::Usize)),
                            value: Expr::Len(Box::new(p_expr.clone())),
                        },
                        line: call_line,
                    });
                }
                if val_old_params.contains(&param.name) {
                    let old_val_name = format!("{prefix}old_{}", param.name);
                    let snap_val = if is_copy_type_syntax(inner_ty, decls) {
                        p_expr.clone()
                    } else {
                        Expr::Clone(Box::new(p_expr.clone()))
                    };
                    old_binds.push(Statement {
                        selector: call_guard.clone(),
                        command: Command::Bind {
                            mutable: false,
                            name: old_val_name,
                            ty: Some((**inner_ty).clone()),
                            value: snap_val,
                        },
                        line: call_line,
                    });
                }
                expr_substs.insert(param.name.clone(), p_expr);
                mut_places.insert(param.name.clone(), place);
            }
            Type::Ref(BorrowMode::Shared, inner_ty) => {
                if let Some(place) = expr_to_place(arg_expr) {
                    expr_substs.insert(param.name.clone(), place_to_expr(&place));
                } else {
                    let tmp_name = format!("{prefix}{}", param.name);
                    rvalue_shared_binds.push(Statement {
                        selector: call_guard.clone(),
                        command: Command::Bind {
                            mutable: false,
                            name: tmp_name.clone(),
                            ty: Some((**inner_ty).clone()),
                            value: arg_expr.clone(),
                        },
                        line: call_line,
                    });
                    expr_substs.insert(param.name.clone(), Expr::Name(tmp_name));
                }
            }
            val_ty => {
                out.push(Statement {
                    selector: call_guard.clone(),
                    command: Command::Bind {
                        mutable: false,
                        name: var_map[&param.name].clone(),
                        ty: Some(val_ty.clone()),
                        value: arg_expr.clone(),
                    },
                    line: call_line,
                });
            }
        }
    }
    out.extend(rvalue_shared_binds);
    out.extend(old_binds);

    // 4. If `callee` has a precondition `⊢ φ`, emit it as an obligation on
    //    `call_guard` so `[P3]` is preserved as `[P1]`.
    if let Some(pre) = &callee.precondition {
        let mut renamed_pre = pre.clone();
        subst_and_rename_expr(&mut renamed_pre, &var_map, &expr_substs, None);
        out.push(Statement {
            selector: call_guard.clone(),
            command: Command::Oblige(renamed_pre),
            line: call_line,
        });
    }

    // 5. Walk top-level statements of `lifted_body`, tracking relative
    //    selectors on which `callee` has already terminated.
    let mut terminated: Vec<Selector> = Vec::new();
    let mut alt_reach: HashMap<String, Vec<Selector>> = HashMap::new();
    for alt in &callee.contract {
        alt_reach.insert(alt.name.clone(), Vec::new());
    }

    for stmt in &lifted_body {
        let mut rel_sel = stmt.selector.clone();
        rename_selector(&mut rel_sel, &site_map);
        let active = simplify_selector(build_active_selector(call_guard, &terminated, &rel_sel));

        match &stmt.command {
            Command::Exit {
                alternative,
                payload,
            } => {
                let contract_alt = callee
                    .contract
                    .iter()
                    .find(|a| &a.name == alternative)
                    .expect("a contract alternative");
                let caller_arm = caller_arms
                    .iter()
                    .find(|a| &a.alternative == alternative)
                    .expect("a caller arm");

                let renamed_payload: Vec<Expr> = payload
                    .iter()
                    .map(|e| {
                        let mut c = e.clone();
                        subst_and_rename_expr(&mut c, &var_map, &expr_substs, None);
                        c
                    })
                    .collect();

                // Bind the caller's arm variables `[~]y_i : field.ty := val_i` on `active`.
                for ((y_raw, field_param), val_expr) in caller_arm
                    .names
                    .iter()
                    .zip(&contract_alt.fields)
                    .zip(&renamed_payload)
                {
                    let (y_mut, y_clean) = match y_raw.strip_prefix('~') {
                        Some(s) => (true, s.to_string()),
                        None => (false, y_raw.clone()),
                    };
                    out.push(Statement {
                        selector: active.clone(),
                        command: Command::Bind {
                            mutable: y_mut,
                            name: y_clean,
                            ty: Some(field_param.ty.clone()),
                            value: val_expr.clone(),
                        },
                        line: call_line,
                    });
                }

                // If the contract alternative has `⇐ cond`, check it as an
                // obligation on `active` (`[P4]` -> `[P1]`), resolving `old(y)`.
                if let Some(cond) = &contract_alt.condition {
                    let mut cond_map = var_map.clone();
                    for (field_param, y_raw) in contract_alt.fields.iter().zip(&caller_arm.names) {
                        let clean = y_raw.strip_prefix('~').unwrap_or(y_raw).to_string();
                        cond_map.insert(field_param.name.clone(), clean);
                    }
                    let mut renamed_cond = cond.clone();
                    subst_and_rename_expr(
                        &mut renamed_cond,
                        &cond_map,
                        &expr_substs,
                        Some(&prefix),
                    );
                    out.push(Statement {
                        selector: active.clone(),
                        command: Command::Oblige(renamed_cond),
                        line: call_line,
                    });
                }

                alt_reach
                    .get_mut(alternative)
                    .expect("known alternative")
                    .push(active);
                terminated.push(rel_sel);
            }
            Command::Impossible => {
                out.push(Statement {
                    selector: active,
                    command: Command::Impossible,
                    line: call_line,
                });
                terminated.push(rel_sel);
            }
            Command::Fault { .. }
            | Command::Terminate(_)
            | Command::Escalate
            | Command::Recover { .. } => {
                let renamed_cmd = rename_command(
                    &stmt.command,
                    &var_map,
                    &expr_substs,
                    &mut_places,
                    &site_map,
                    &loop_map,
                );
                out.push(Statement {
                    selector: active,
                    command: renamed_cmd,
                    line: call_line,
                });
                terminated.push(rel_sel);
            }
            other => {
                let renamed_cmd = rename_command(
                    other,
                    &var_map,
                    &expr_substs,
                    &mut_places,
                    &site_map,
                    &loop_map,
                );
                if let Command::Loop { arms, .. } = &renamed_cmd
                    && arms.is_empty()
                {
                    terminated.push(rel_sel);
                }
                out.push(Statement {
                    selector: active,
                    command: renamed_cmd,
                    line: call_line,
                });
            }
        }
    }

    // 6. Collect exit selectors for every alternative and note dead arm variables
    //    that may need default bindings after dead-statement pruning.
    let false_sel = Selector::Not(Box::new(Selector::Top));
    let mut alt_selectors = HashMap::new();
    let mut dead_vars = Vec::new();
    for contract_alt in &callee.contract {
        let reaches = &alt_reach[&contract_alt.name];
        if reaches.is_empty() {
            if let Some(caller_arm) = caller_arms
                .iter()
                .find(|a| a.alternative == contract_alt.name)
            {
                for (y_name, field_param) in caller_arm.names.iter().zip(&contract_alt.fields) {
                    dead_vars.push((y_name.clone(), field_param.ty.clone()));
                }
            }
            alt_selectors.insert(contract_alt.name.clone(), false_sel.clone());
        } else {
            let mut iter = reaches.iter().cloned();
            let first = iter.next().unwrap();
            let disj = iter.fold(first, |acc, s| Selector::Or(Box::new(acc), Box::new(s)));
            alt_selectors.insert(contract_alt.name.clone(), disj);
        }
    }

    (out, alt_selectors, dead_vars)
}

fn default_expr_for_decls(ty: &Type, decls: &[Declaration]) -> Option<Expr> {
    match ty {
        Type::Bool => Some(Expr::Boolean(false)),
        Type::Int(_) => Some(Expr::Integer(Int::from_u64(0))),
        Type::String => Some(Expr::String(String::new())),
        Type::Vector(_) => Some(Expr::Vector(Vec::new())),
        Type::Map(_, _) => Some(Expr::EmptyMap),
        Type::Named(name) => {
            for d in decls {
                match d {
                    Declaration::Struct(s) if s.name == *name => {
                        let fields: Option<Vec<Expr>> = s
                            .fields
                            .iter()
                            .map(|f| default_expr_for_decls(&f.ty, decls))
                            .collect();
                        return fields.map(|fs| Expr::Struct(name.clone(), fs));
                    }
                    Declaration::Variant(v) if v.name == *name => {
                        let ctor = v.constructors.first()?;
                        let fields: Option<Vec<Expr>> = ctor
                            .fields
                            .iter()
                            .map(|f| default_expr_for_decls(&f.ty, decls))
                            .collect();
                        return fields.map(|fs| Expr::Variant(name.clone(), ctor.name.clone(), fs));
                    }
                    _ => {}
                }
            }
            None
        }
        _ => None,
    }
}

fn is_var_used_in_expr(expr: &Expr, name: &str) -> bool {
    match expr {
        Expr::Name(n) | Expr::Old(n) => n == name,
        Expr::Unary(_, e)
        | Expr::Move(e)
        | Expr::Borrow(_, e)
        | Expr::Field(e, _)
        | Expr::Len(e)
        | Expr::Clone(e) => is_var_used_in_expr(e, name),
        Expr::Binary(_, l, r) | Expr::Index(l, r) => {
            is_var_used_in_expr(l, name) || is_var_used_in_expr(r, name)
        }
        Expr::Call(_, args)
        | Expr::Struct(_, args)
        | Expr::Variant(_, _, args)
        | Expr::Vector(args) => args.iter().any(|a| is_var_used_in_expr(a, name)),
        Expr::Integer(_) | Expr::Boolean(_) | Expr::String(_) | Expr::EmptyMap => false,
    }
}

fn is_var_used_in_place(place: &Place, name: &str) -> bool {
    place.root == name
        || place.steps.iter().any(|step| match step {
            PlaceStep::Field(_) => false,
            PlaceStep::Index(e) => is_var_used_in_expr(e, name),
        })
}

fn is_var_used_in_stmts(stmts: &[Statement], name: &str) -> bool {
    stmts.iter().any(|stmt| match &stmt.command {
        Command::Bind { value, .. } | Command::Unpack { value, .. } => {
            is_var_used_in_expr(value, name)
        }
        Command::Assign {
            name: target,
            value,
        } => target == name || is_var_used_in_expr(value, name),
        Command::AssignPlace { target, value } => {
            is_var_used_in_place(target, name) || is_var_used_in_expr(value, name)
        }
        Command::Oblige(e) | Command::Test { condition: e, .. } => is_var_used_in_expr(e, name),
        Command::Capture { arguments, .. }
        | Command::Decide { arguments, .. }
        | Command::Supervise { arguments, .. }
        | Command::Again { arguments, .. } => {
            arguments.iter().any(|a| is_var_used_in_expr(a, name))
        }
        Command::Leave { payload, .. } | Command::Exit { payload, .. } => {
            payload.iter().any(|a| is_var_used_in_expr(a, name))
        }
        Command::Loop {
            parameters,
            invariant,
            body,
            ..
        } => {
            parameters
                .iter()
                .any(|p| is_var_used_in_expr(&p.initial, name))
                || invariant
                    .as_ref()
                    .is_some_and(|i| is_var_used_in_expr(i, name))
                || is_var_used_in_stmts(body, name)
        }
        Command::Boundary {
            body,
            captures,
            contingency,
            ..
        } => {
            captures.iter().any(|c| c == name)
                || is_var_used_in_stmts(body, name)
                || is_var_used_in_stmts(contingency, name)
        }
        Command::Fault { message, .. } => is_var_used_in_expr(message, name),
        Command::Terminate(Some(e)) => is_var_used_in_expr(e, name),
        Command::Terminate(None)
        | Command::Impossible
        | Command::Escalate
        | Command::Recover { .. } => false,
    })
}

/// Lifts any `Command::Exit` inside any `Command::Loop` of `statements` out to
/// the top level of `statements`.
fn lift_exits_in_body(
    statements: &[Statement],
    contract: &[Alternative],
    next_id: &mut usize,
) -> Vec<Statement> {
    let mut out = Vec::new();
    for stmt in statements {
        match &stmt.command {
            Command::Loop {
                site,
                name,
                parameters,
                invariant,
                body,
                arms,
            } => {
                // First lift exits inside any nested loops of `body`.
                let inner_lifted = lift_exits_in_body(body, contract, next_id);
                let mut new_loop_body = Vec::new();
                let mut new_arms = arms.clone();
                let mut post_exits: Vec<(String, String, Vec<String>)> = Vec::new();

                for inner_stmt in inner_lifted {
                    if let Command::Exit {
                        alternative,
                        payload,
                    } = inner_stmt.command
                    {
                        let contract_alt = contract
                            .iter()
                            .find(|a| a.name == alternative)
                            .expect("a contract alternative");
                        let lift_id = *next_id;
                        *next_id += 1;
                        let lift_alt = format!("_lift_exit_{lift_id}");

                        let mut leave_payload = Vec::new();
                        let mut arm_vars = Vec::new();
                        for (field_idx, (expr, field_param)) in
                            payload.into_iter().zip(&contract_alt.fields).enumerate()
                        {
                            let val_name = format!("_lift_val_{lift_id}_{field_idx}");
                            let out_name = format!("_lift_out_{lift_id}_{field_idx}");
                            new_loop_body.push(Statement {
                                selector: inner_stmt.selector.clone(),
                                command: Command::Bind {
                                    mutable: false,
                                    name: val_name.clone(),
                                    ty: Some(field_param.ty.clone()),
                                    value: expr,
                                },
                                line: inner_stmt.line,
                            });
                            leave_payload.push(Expr::Name(val_name));
                            arm_vars.push(out_name);
                        }
                        new_loop_body.push(Statement {
                            selector: inner_stmt.selector,
                            command: Command::Leave {
                                alternative: lift_alt.clone(),
                                payload: leave_payload,
                            },
                            line: inner_stmt.line,
                        });
                        new_arms.push(Arm {
                            alternative: lift_alt.clone(),
                            names: arm_vars.clone(),
                        });
                        post_exits.push((lift_alt, alternative, arm_vars));
                    } else {
                        new_loop_body.push(inner_stmt);
                    }
                }

                out.push(Statement {
                    selector: stmt.selector.clone(),
                    command: Command::Loop {
                        site: site.clone(),
                        name: name.clone(),
                        parameters: parameters.clone(),
                        invariant: invariant.clone(),
                        body: new_loop_body,
                        arms: new_arms,
                    },
                    line: stmt.line,
                });

                for (lift_alt, orig_alt, arm_vars) in post_exits {
                    out.push(Statement {
                        selector: Selector::Atom(site.clone(), lift_alt),
                        command: Command::Exit {
                            alternative: orig_alt,
                            payload: arm_vars.into_iter().map(Expr::Name).collect(),
                        },
                        line: stmt.line,
                    });
                }
            }
            Command::Boundary {
                site,
                body,
                captures,
                message,
                contingency,
            } => {
                out.push(Statement {
                    selector: stmt.selector.clone(),
                    command: Command::Boundary {
                        site: site.clone(),
                        body: lift_exits_in_body(body, contract, next_id),
                        captures: captures.clone(),
                        message: message.clone(),
                        contingency: lift_exits_in_body(contingency, contract, next_id),
                    },
                    line: stmt.line,
                });
            }
            _ => out.push(stmt.clone()),
        }
    }
    out
}

fn build_active_selector(
    call_guard: &Selector,
    terminated: &[Selector],
    rel_sel: &Selector,
) -> Selector {
    let mut acc = call_guard.clone();
    for term in terminated {
        let not_term = match term {
            Selector::Top => Selector::Not(Box::new(Selector::Top)),
            other => Selector::Not(Box::new(other.clone())),
        };
        acc = and_sel(acc, not_term);
    }
    and_sel(acc, rel_sel.clone())
}

fn and_sel(left: Selector, right: Selector) -> Selector {
    match (&left, &right) {
        (Selector::Top, _) => right,
        (_, Selector::Top) => left,
        _ => Selector::And(Box::new(left), Box::new(right)),
    }
}

fn strip_tilde(name: &str) -> String {
    name.strip_prefix('~').unwrap_or(name).to_string()
}

fn collect_callee_names(
    statements: &[Statement],
    vars: &mut HashSet<String>,
    sites: &mut HashSet<String>,
    loops: &mut HashSet<String>,
) {
    for stmt in statements {
        match &stmt.command {
            Command::Bind { name, .. }
            | Command::Capture { name, .. }
            | Command::Assign { name, .. } => {
                vars.insert(strip_tilde(name));
            }
            Command::Unpack { names, .. } => {
                for n in names {
                    vars.insert(strip_tilde(n));
                }
            }
            Command::Test { site, .. } => {
                sites.insert(site.clone());
            }
            Command::Decide { site, arms, .. } => {
                sites.insert(site.clone());
                for arm in arms {
                    for v in &arm.names {
                        vars.insert(strip_tilde(v));
                    }
                }
            }
            Command::Loop {
                site,
                name,
                parameters,
                body,
                arms,
                ..
            } => {
                sites.insert(site.clone());
                loops.insert(name.clone());
                for p in parameters {
                    vars.insert(strip_tilde(&p.name));
                }
                for arm in arms {
                    for v in &arm.names {
                        vars.insert(strip_tilde(v));
                    }
                }
                collect_callee_names(body, vars, sites, loops);
            }
            Command::Boundary {
                site,
                body,
                message,
                contingency,
                ..
            } => {
                sites.insert(site.clone());
                if let Some(m) = message {
                    vars.insert(strip_tilde(m));
                }
                collect_callee_names(body, vars, sites, loops);
                collect_callee_names(contingency, vars, sites, loops);
            }
            _ => {}
        }
    }
}

fn rename_selector(selector: &mut Selector, site_map: &HashMap<String, String>) {
    match selector {
        Selector::Top => {}
        Selector::Atom(site, _) => {
            if let Some(new_site) = site_map.get(site) {
                *site = new_site.clone();
            }
        }
        Selector::Not(inner) => rename_selector(inner, site_map),
        Selector::And(l, r) | Selector::Or(l, r) => {
            rename_selector(l, site_map);
            rename_selector(r, site_map);
        }
    }
}

fn subst_and_rename_expr(
    expr: &mut Expr,
    var_map: &HashMap<String, String>,
    expr_substs: &HashMap<String, Expr>,
    old_prefix: Option<&str>,
) {
    match expr {
        Expr::Integer(_) | Expr::Boolean(_) | Expr::String(_) | Expr::EmptyMap => {}
        Expr::Len(inner) => {
            if let Expr::Old(name) = &**inner
                && let Some(prefix) = old_prefix
                && expr_substs.contains_key(name)
            {
                *expr = Expr::Name(format!("{prefix}old_len_{name}"));
                return;
            }
            subst_and_rename_expr(inner, var_map, expr_substs, old_prefix);
        }
        Expr::Old(name) => {
            if let Some(prefix) = old_prefix
                && expr_substs.contains_key(name)
            {
                *expr = Expr::Name(format!("{prefix}old_{name}"));
                return;
            }
            if let Some(new_name) = var_map.get(name) {
                *name = new_name.clone();
            }
        }
        Expr::Name(name) => {
            if let Some(replacement) = expr_substs.get(name) {
                *expr = replacement.clone();
            } else if let Some(new_name) = var_map.get(name) {
                *name = new_name.clone();
            }
        }
        Expr::Unary(_, inner)
        | Expr::Move(inner)
        | Expr::Borrow(_, inner)
        | Expr::Field(inner, _)
        | Expr::Clone(inner) => subst_and_rename_expr(inner, var_map, expr_substs, old_prefix),
        Expr::Binary(_, l, r) | Expr::Index(l, r) => {
            subst_and_rename_expr(l, var_map, expr_substs, old_prefix);
            subst_and_rename_expr(r, var_map, expr_substs, old_prefix);
        }
        Expr::Call(_, args)
        | Expr::Struct(_, args)
        | Expr::Variant(_, _, args)
        | Expr::Vector(args) => {
            for arg in args {
                subst_and_rename_expr(arg, var_map, expr_substs, old_prefix);
            }
        }
    }
}

fn rename_place(
    place: &Place,
    var_map: &HashMap<String, String>,
    expr_substs: &HashMap<String, Expr>,
    mut_places: &HashMap<String, Place>,
) -> Place {
    let mut new_steps: Vec<PlaceStep> = Vec::new();
    let root = if let Some(base) = mut_places.get(&place.root) {
        for s in &base.steps {
            new_steps.push(s.clone());
        }
        base.root.clone()
    } else {
        var_map
            .get(&place.root)
            .cloned()
            .unwrap_or_else(|| place.root.clone())
    };
    for step in &place.steps {
        match step {
            PlaceStep::Field(f) => new_steps.push(PlaceStep::Field(f.clone())),
            PlaceStep::Index(idx) => {
                let mut e = idx.clone();
                subst_and_rename_expr(&mut e, var_map, expr_substs, None);
                new_steps.push(PlaceStep::Index(e));
            }
        }
    }
    Place {
        root,
        steps: new_steps,
    }
}

fn rename_arm_name(raw: &str, var_map: &HashMap<String, String>) -> String {
    if let Some(stripped) = raw.strip_prefix('~') {
        let mapped = var_map
            .get(stripped)
            .cloned()
            .unwrap_or_else(|| stripped.to_string());
        format!("~{mapped}")
    } else {
        var_map.get(raw).cloned().unwrap_or_else(|| raw.to_string())
    }
}

fn rename_command(
    command: &Command,
    var_map: &HashMap<String, String>,
    expr_substs: &HashMap<String, Expr>,
    mut_places: &HashMap<String, Place>,
    site_map: &HashMap<String, String>,
    loop_map: &HashMap<String, String>,
) -> Command {
    match command {
        Command::Bind {
            mutable,
            name,
            ty,
            value,
        } => {
            let mut v = value.clone();
            subst_and_rename_expr(&mut v, var_map, expr_substs, None);
            Command::Bind {
                mutable: *mutable,
                name: var_map.get(name).cloned().unwrap_or_else(|| name.clone()),
                ty: ty.clone(),
                value: v,
            }
        }
        Command::Unpack {
            struct_name,
            names,
            value,
        } => {
            let mut v = value.clone();
            subst_and_rename_expr(&mut v, var_map, expr_substs, None);
            Command::Unpack {
                struct_name: struct_name.clone(),
                names: names
                    .iter()
                    .map(|n| var_map.get(n).cloned().unwrap_or_else(|| n.clone()))
                    .collect(),
                value: v,
            }
        }
        Command::Capture {
            mutable,
            name,
            ty,
            operation,
            arguments,
        } => Command::Capture {
            mutable: *mutable,
            name: var_map.get(name).cloned().unwrap_or_else(|| name.clone()),
            ty: ty.clone(),
            operation: operation.clone(),
            arguments: arguments
                .iter()
                .map(|a| {
                    let mut c = a.clone();
                    subst_and_rename_expr(&mut c, var_map, expr_substs, None);
                    c
                })
                .collect(),
        },
        Command::Assign { name, value } => {
            let mut v = value.clone();
            subst_and_rename_expr(&mut v, var_map, expr_substs, None);
            if let Some(target_place) = mut_places.get(name) {
                if target_place.steps.is_empty() {
                    Command::Assign {
                        name: target_place.root.clone(),
                        value: v,
                    }
                } else {
                    Command::AssignPlace {
                        target: target_place.clone(),
                        value: v,
                    }
                }
            } else {
                Command::Assign {
                    name: var_map.get(name).cloned().unwrap_or_else(|| name.clone()),
                    value: v,
                }
            }
        }
        Command::AssignPlace { target, value } => {
            let mut v = value.clone();
            subst_and_rename_expr(&mut v, var_map, expr_substs, None);
            Command::AssignPlace {
                target: rename_place(target, var_map, expr_substs, mut_places),
                value: v,
            }
        }
        Command::Oblige(formula) => {
            let mut f = formula.clone();
            subst_and_rename_expr(&mut f, var_map, expr_substs, None);
            Command::Oblige(f)
        }
        Command::Test { site, condition } => {
            let mut c = condition.clone();
            subst_and_rename_expr(&mut c, var_map, expr_substs, None);
            Command::Test {
                site: site_map.get(site).cloned().unwrap_or_else(|| site.clone()),
                condition: c,
            }
        }
        Command::Decide {
            site,
            operation,
            arguments,
            arms,
        } => {
            let new_args = arguments
                .iter()
                .map(|a| {
                    let mut c = a.clone();
                    subst_and_rename_expr(&mut c, var_map, expr_substs, None);
                    c
                })
                .collect();
            let new_arms = arms
                .iter()
                .map(|arm| Arm {
                    alternative: arm.alternative.clone(),
                    names: arm
                        .names
                        .iter()
                        .map(|n| rename_arm_name(n, var_map))
                        .collect(),
                })
                .collect();
            Command::Decide {
                site: site_map.get(site).cloned().unwrap_or_else(|| site.clone()),
                operation: operation.clone(),
                arguments: new_args,
                arms: new_arms,
            }
        }
        Command::Loop {
            site,
            name,
            parameters,
            invariant,
            body,
            arms,
        } => {
            let new_params = parameters
                .iter()
                .map(|p| {
                    let mut init = p.initial.clone();
                    subst_and_rename_expr(&mut init, var_map, expr_substs, None);
                    LoopParameter {
                        mutable: p.mutable,
                        name: var_map
                            .get(&p.name)
                            .cloned()
                            .unwrap_or_else(|| p.name.clone()),
                        ty: p.ty.clone(),
                        initial: init,
                    }
                })
                .collect();
            let new_inv = invariant.as_ref().map(|inv| {
                let mut c = inv.clone();
                subst_and_rename_expr(&mut c, var_map, expr_substs, None);
                c
            });
            let new_body = body
                .iter()
                .map(|s| {
                    let mut sel = s.selector.clone();
                    rename_selector(&mut sel, site_map);
                    Statement {
                        selector: sel,
                        command: rename_command(
                            &s.command,
                            var_map,
                            expr_substs,
                            mut_places,
                            site_map,
                            loop_map,
                        ),
                        line: s.line,
                    }
                })
                .collect();
            let new_arms = arms
                .iter()
                .map(|arm| Arm {
                    alternative: arm.alternative.clone(),
                    names: arm
                        .names
                        .iter()
                        .map(|n| rename_arm_name(n, var_map))
                        .collect(),
                })
                .collect();
            Command::Loop {
                site: site_map.get(site).cloned().unwrap_or_else(|| site.clone()),
                name: loop_map.get(name).cloned().unwrap_or_else(|| name.clone()),
                parameters: new_params,
                invariant: new_inv,
                body: new_body,
                arms: new_arms,
            }
        }
        Command::Boundary {
            site,
            body,
            captures,
            message,
            contingency,
        } => {
            let new_body = body
                .iter()
                .map(|s| {
                    let mut sel = s.selector.clone();
                    rename_selector(&mut sel, site_map);
                    Statement {
                        selector: sel,
                        command: rename_command(
                            &s.command,
                            var_map,
                            expr_substs,
                            mut_places,
                            site_map,
                            loop_map,
                        ),
                        line: s.line,
                    }
                })
                .collect();
            let new_contingency = contingency
                .iter()
                .map(|s| {
                    let mut sel = s.selector.clone();
                    rename_selector(&mut sel, site_map);
                    Statement {
                        selector: sel,
                        command: rename_command(
                            &s.command,
                            var_map,
                            expr_substs,
                            mut_places,
                            site_map,
                            loop_map,
                        ),
                        line: s.line,
                    }
                })
                .collect();
            Command::Boundary {
                site: site_map.get(site).cloned().unwrap_or_else(|| site.clone()),
                body: new_body,
                captures: captures
                    .iter()
                    .map(|c| var_map.get(c).cloned().unwrap_or_else(|| c.clone()))
                    .collect(),
                message: message
                    .as_ref()
                    .map(|m| var_map.get(m).cloned().unwrap_or_else(|| m.clone())),
                contingency: new_contingency,
            }
        }
        Command::Supervise {
            boundary,
            arguments,
        } => Command::Supervise {
            boundary: boundary.clone(),
            arguments: arguments
                .iter()
                .map(|a| {
                    let mut c = a.clone();
                    subst_and_rename_expr(&mut c, var_map, expr_substs, None);
                    c
                })
                .collect(),
        },
        Command::Again { name, arguments } => Command::Again {
            name: loop_map.get(name).cloned().unwrap_or_else(|| name.clone()),
            arguments: arguments
                .iter()
                .map(|a| {
                    let mut c = a.clone();
                    subst_and_rename_expr(&mut c, var_map, expr_substs, None);
                    c
                })
                .collect(),
        },
        Command::Leave {
            alternative,
            payload,
        } => Command::Leave {
            alternative: alternative.clone(),
            payload: payload
                .iter()
                .map(|a| {
                    let mut c = a.clone();
                    subst_and_rename_expr(&mut c, var_map, expr_substs, None);
                    c
                })
                .collect(),
        },
        Command::Exit {
            alternative,
            payload,
        } => Command::Exit {
            alternative: alternative.clone(),
            payload: payload
                .iter()
                .map(|a| {
                    let mut c = a.clone();
                    subst_and_rename_expr(&mut c, var_map, expr_substs, None);
                    c
                })
                .collect(),
        },
        Command::Fault { message, assumed } => {
            let mut m = message.clone();
            subst_and_rename_expr(&mut m, var_map, expr_substs, None);
            Command::Fault {
                message: m,
                assumed: *assumed,
            }
        }
        Command::Terminate(status) => Command::Terminate(status.as_ref().map(|e| {
            let mut c = e.clone();
            subst_and_rename_expr(&mut c, var_map, expr_substs, None);
            c
        })),
        Command::Escalate => Command::Escalate,
        Command::Recover { loop_name } => Command::Recover {
            loop_name: loop_map
                .get(loop_name)
                .cloned()
                .unwrap_or_else(|| loop_name.clone()),
        },
        Command::Impossible => Command::Impossible,
    }
}

fn substitute_site_in_stmt(
    stmt: &mut Statement,
    site: &str,
    alt_selectors: &HashMap<String, Selector>,
) {
    stmt.selector = simplify_selector(substitute_site_in_selector(
        &stmt.selector,
        site,
        alt_selectors,
    ));
    match &mut stmt.command {
        Command::Loop { body, .. } => {
            for child in body {
                substitute_site_in_stmt(child, site, alt_selectors);
            }
        }
        Command::Boundary {
            body, contingency, ..
        } => {
            for child in body {
                substitute_site_in_stmt(child, site, alt_selectors);
            }
            for child in contingency {
                substitute_site_in_stmt(child, site, alt_selectors);
            }
        }
        _ => {}
    }
}

fn substitute_site_in_selector(
    selector: &Selector,
    site: &str,
    alt_selectors: &HashMap<String, Selector>,
) -> Selector {
    match selector {
        Selector::Top => Selector::Top,
        Selector::Atom(s, alt) => {
            if s == site {
                alt_selectors
                    .get(alt)
                    .cloned()
                    .unwrap_or_else(|| Selector::Not(Box::new(Selector::Top)))
            } else {
                Selector::Atom(s.clone(), alt.clone())
            }
        }
        Selector::Not(inner) => Selector::Not(Box::new(substitute_site_in_selector(
            inner,
            site,
            alt_selectors,
        ))),
        Selector::And(l, r) => Selector::And(
            Box::new(substitute_site_in_selector(l, site, alt_selectors)),
            Box::new(substitute_site_in_selector(r, site, alt_selectors)),
        ),
        Selector::Or(l, r) => Selector::Or(
            Box::new(substitute_site_in_selector(l, site, alt_selectors)),
            Box::new(substitute_site_in_selector(r, site, alt_selectors)),
        ),
    }
}
