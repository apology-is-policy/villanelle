//! Single-step mutations of valid core programs, classified by the oracle.
//!
//! Each mutant seeds one defect into a valid [`syntax::Program`]: removing an
//! arm of a decision, removing a disposition (`■`, `□` or `↑`), dropping a
//! statement's guard selector to `⊤`, dropping a loop's invariant, dropping
//! an effect from a control's `uses` clause, making an integer literal one
//! greater or one less, or replacing a comparison by the one beside it.
//!
//! [`classify`] runs a mutant through `resolve` and the oracle across a set of
//! inputs. The mutants that are stuck in the oracle are those that the checker
//! of phase 3 must reject.

use crate::host::{Arithmetic, Seeded};
use crate::int::Int;
use crate::oracle::{self, Config, End, Stuck, Value};
use crate::resolve;
use crate::syntax::{
    Binary, Command, Control, Declaration, Expr, PlaceStep, Program, Selector, Statement,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Kind {
    /// An arm of a decision is removed ([C2], X10).
    RemoveArm,
    /// An exit, `□` or `↑` is removed ([K7], X1).
    RemoveDisposition,
    /// A selector is replaced by `⊤` ([O2] to [O4], [P1] to [P8], X2, X3, X6, X7).
    DropGuard,
    /// The invariant of a loop is dropped ([K4], [P4]).
    DropInvariant,
    /// An effect is removed from a control's `uses` clause ([F3], X9).
    DropEffect,
    /// An integer literal is one greater or one less ([P1] to [P5], X6, X7).
    ShiftLiteral,
    /// A comparison is replaced by the one beside it: `<` and `≤` by each
    /// other, `>` and `≥` by each other, `=` and `≠` by each other ([P1] to
    /// [P8], X6).
    FlipComparison,
}

#[derive(Clone, Debug)]
pub struct Mutant {
    pub kind: Kind,
    pub control: String,
    pub detail: String,
    pub program: Program,
}

#[derive(Clone, Debug)]
pub enum Class {
    /// `resolve` refuses the mutant by this clause.
    Refused(&'static str),
    /// A run of the mutant in the oracle is stuck here.
    Stuck(Stuck),
    /// No tested run of the mutant was stuck.
    Unstuck,
}

fn body_mut<'a>(
    program: &'a mut Program,
    declaration: usize,
    loop_path: &[usize],
) -> &'a mut Vec<Statement> {
    let Declaration::Control(control) = &mut program.declarations[declaration] else {
        panic!("expected a control declaration");
    };
    let mut statements = &mut control.body;
    for index in loop_path {
        let Command::Loop { body, .. } = &mut statements[*index].command else {
            panic!("expected a loop statement");
        };
        statements = body;
    }
    statements
}

fn collect_from_body(
    program: &Program,
    declaration: usize,
    control_name: &str,
    loop_path: &mut Vec<usize>,
    out: &mut Vec<Mutant>,
) {
    let statements = {
        let Declaration::Control(control) = &program.declarations[declaration] else {
            return;
        };
        let mut current = &control.body;
        for index in loop_path.iter() {
            let Command::Loop { body, .. } = &current[*index].command else {
                return;
            };
            current = body;
        }
        current.clone()
    };

    for (index, statement) in statements.iter().enumerate() {
        if !matches!(statement.selector, Selector::Top) {
            let mut mutated = program.clone();
            body_mut(&mut mutated, declaration, loop_path)[index].selector = Selector::Top;
            out.push(Mutant {
                kind: Kind::DropGuard,
                control: control_name.to_string(),
                detail: format!("drop guard at statement {index}"),
                program: mutated,
            });
        }

        match &statement.command {
            Command::Decide { site, arms, .. } => {
                for (arm_index, arm) in arms.iter().enumerate() {
                    let mut mutated = program.clone();
                    let Command::Decide { arms: target, .. } =
                        &mut body_mut(&mut mutated, declaration, loop_path)[index].command
                    else {
                        unreachable!();
                    };
                    target.remove(arm_index);
                    out.push(Mutant {
                        kind: Kind::RemoveArm,
                        control: control_name.to_string(),
                        detail: format!("remove arm `{}` of `{site}`", arm.alternative),
                        program: mutated,
                    });
                }
            }
            Command::Exit { alternative, .. }
            | Command::Leave { alternative, .. }
            | Command::Again {
                name: alternative, ..
            } => {
                let mut mutated = program.clone();
                body_mut(&mut mutated, declaration, loop_path).remove(index);
                out.push(Mutant {
                    kind: Kind::RemoveDisposition,
                    control: control_name.to_string(),
                    detail: format!("remove disposition `{alternative}` at statement {index}"),
                    program: mutated,
                });
            }
            Command::Loop {
                name, invariant, ..
            } => {
                if invariant.is_some() {
                    let mut mutated = program.clone();
                    let Command::Loop {
                        invariant: target, ..
                    } = &mut body_mut(&mut mutated, declaration, loop_path)[index].command
                    else {
                        unreachable!();
                    };
                    *target = None;
                    out.push(Mutant {
                        kind: Kind::DropInvariant,
                        control: control_name.to_string(),
                        detail: format!("drop invariant of `{name}`"),
                        program: mutated,
                    });
                }
                loop_path.push(index);
                collect_from_body(program, declaration, control_name, loop_path, out);
                loop_path.pop();
            }
            _ => {}
        }
    }
}

/// Calls `visit` on `expr` and then on every expression inside it.
fn walk(expr: &mut Expr, visit: &mut dyn FnMut(&mut Expr)) {
    visit(expr);
    match expr {
        Expr::Integer(_)
        | Expr::Boolean(_)
        | Expr::String(_)
        | Expr::Name(_)
        | Expr::Old(_)
        | Expr::EmptyMap
        | Expr::TasksEmpty(_)
        | Expr::Count(_) => {}
        Expr::Move(inner)
        | Expr::Borrow(_, inner)
        | Expr::Field(inner, _)
        | Expr::Len(inner)
        | Expr::Clone(inner)
        | Expr::Unary(_, inner) => walk(inner, visit),
        Expr::Index(left, right) | Expr::Binary(_, left, right) => {
            walk(left, visit);
            walk(right, visit);
        }
        Expr::Struct(_, items)
        | Expr::Variant(_, _, items)
        | Expr::Vector(items)
        | Expr::Call(_, items) => {
            for item in items {
                walk(item, visit);
            }
        }
    }
}

/// Calls `visit` on every expression of the statements, in their order.
fn walk_statements(statements: &mut [Statement], visit: &mut dyn FnMut(&mut Expr)) {
    for statement in statements {
        match &mut statement.command {
            Command::Bind { value, .. }
            | Command::Unpack { value, .. }
            | Command::Assign { value, .. }
            | Command::Oblige(value)
            | Command::Test {
                condition: value, ..
            }
            | Command::Fault { message: value, .. }
            | Command::Terminate(Some(value)) => walk(value, visit),
            Command::AssignPlace { target, value } => {
                for step in &mut target.steps {
                    if let PlaceStep::Index(index) = step {
                        walk(index, visit);
                    }
                }
                walk(value, visit);
            }
            Command::Capture { arguments, .. }
            | Command::Decide { arguments, .. }
            | Command::Supervise { arguments, .. }
            | Command::Spawn { arguments, .. }
            | Command::Again { arguments, .. }
            | Command::Leave {
                payload: arguments, ..
            }
            | Command::Exit {
                payload: arguments, ..
            } => {
                for argument in arguments {
                    walk(argument, visit);
                }
            }
            Command::Loop {
                parameters,
                invariant,
                body,
                ..
            } => {
                for parameter in parameters {
                    walk(&mut parameter.initial, visit);
                }
                if let Some(invariant) = invariant {
                    walk(invariant, visit);
                }
                walk_statements(body, visit);
            }
            Command::Boundary {
                body, contingency, ..
            } => {
                walk_statements(body, visit);
                walk_statements(contingency, visit);
            }
            Command::Cancel { .. }
            | Command::Impossible
            | Command::Terminate(None)
            | Command::Escalate
            | Command::Recover { .. } => {}
        }
    }
}

/// Calls `visit` on every expression of a control: its precondition, the
/// conditions of its contract, and its body.
fn walk_control(control: &mut Control, visit: &mut dyn FnMut(&mut Expr)) {
    if let Some(precondition) = &mut control.precondition {
        walk(precondition, visit);
    }
    for alternative in &mut control.contract {
        if let Some(condition) = &mut alternative.condition {
            walk(condition, visit);
        }
    }
    walk_statements(&mut control.body, visit);
}

/// What one expression can become by a mutation of itself, and not of what
/// is inside it: the kind, the expression, and words for the change.
fn changes(expr: &Expr) -> Vec<(Kind, Expr, String)> {
    match expr {
        Expr::Integer(value) => {
            let one = Int::from_u64(1);
            [value.plus(&one), value.minus(&one)]
                .into_iter()
                .map(|shifted| {
                    let detail = format!("literal `{value}` to `{shifted}`");
                    (Kind::ShiftLiteral, Expr::Integer(shifted), detail)
                })
                .collect()
        }
        Expr::Binary(operator, left, right) => {
            let beside = match operator {
                Binary::Less => Binary::LessEqual,
                Binary::LessEqual => Binary::Less,
                Binary::Greater => Binary::GreaterEqual,
                Binary::GreaterEqual => Binary::Greater,
                Binary::Equal => Binary::NotEqual,
                Binary::NotEqual => Binary::Equal,
                _ => return Vec::new(),
            };
            let detail = format!("`{}` to `{}`", operator.glyph(), beside.glyph());
            vec![(
                Kind::FlipComparison,
                Expr::Binary(beside, left.clone(), right.clone()),
                detail,
            )]
        }
        _ => Vec::new(),
    }
}

/// The mutants of a control that change one expression of it.
fn collect_from_expressions(program: &Program, declaration: usize, out: &mut Vec<Mutant>) {
    let Declaration::Control(control) = &program.declarations[declaration] else {
        return;
    };
    // How many changes each expression has, in the order of the walk.
    let mut counts = Vec::new();
    walk_control(&mut control.clone(), &mut |expr| {
        counts.push(changes(expr).len());
    });
    for (site, count) in counts.iter().enumerate() {
        for choice in 0..*count {
            let mut mutated = program.clone();
            let Declaration::Control(target) = &mut mutated.declarations[declaration] else {
                unreachable!();
            };
            let mut at = 0;
            let mut made = None;
            walk_control(target, &mut |expr| {
                if at == site {
                    let (kind, changed, detail) = changes(expr).swap_remove(choice);
                    *expr = changed;
                    made = Some((kind, detail));
                }
                at += 1;
            });
            let (kind, detail) = made.expect("the expression that was counted");
            out.push(Mutant {
                kind,
                control: control.name.clone(),
                detail: format!("{detail} (expression {site})"),
                program: mutated,
            });
        }
    }
}

/// Produces all single-step mutants of `program`.
pub fn mutate(program: &Program) -> Vec<Mutant> {
    let mut out = Vec::new();
    for (declaration, item) in program.declarations.iter().enumerate() {
        let Declaration::Control(control) = item else {
            continue;
        };
        if control.external {
            continue;
        }
        for (effect_index, effect) in control.uses.iter().enumerate() {
            let mut mutated = program.clone();
            let Declaration::Control(target) = &mut mutated.declarations[declaration] else {
                unreachable!();
            };
            target.uses.remove(effect_index);
            out.push(Mutant {
                kind: Kind::DropEffect,
                control: control.name.clone(),
                detail: format!("drop effect `{effect}`"),
                program: mutated,
            });
        }
        let mut loop_path = Vec::new();
        collect_from_body(
            program,
            declaration,
            &control.name,
            &mut loop_path,
            &mut out,
        );
        collect_from_expressions(program, declaration, &mut out);
    }
    out
}

/// Resolves `mutant` and runs it in the oracle across `runs` (each a control
/// name and its arguments), under a few host seeds, returning the first
/// refusal or stuck state it meets.
pub fn classify(
    mutant: &Mutant,
    runs: &[(String, Vec<Value>)],
    seed: u64,
    config: &Config,
) -> Class {
    let typed = match resolve::resolve(&mutant.program) {
        Ok(typed) => typed,
        Err(error) => return Class::Refused(error.clause),
    };
    for (run_index, (entry, arguments)) in runs.iter().enumerate() {
        for host_offset in 0..3u64 {
            let run_seed = seed
                .wrapping_add((run_index as u64).wrapping_mul(31))
                .wrapping_add(host_offset);
            let mut host = Arithmetic(Seeded::new(&typed, run_seed));
            let outcome = oracle::run(&typed, entry, arguments.clone(), &mut host, config);
            if let End::Stuck(stuck) = outcome.end {
                return Class::Stuck(stuck);
            }
        }
    }
    Class::Unstuck
}
