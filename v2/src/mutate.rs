//! Single-step mutations of valid core programs, classified by the oracle.
//!
//! Each mutant seeds one defect into a valid [`syntax::Program`]: removing an
//! arm of a decision, removing a disposition (`■`, `□` or `↑`), dropping a
//! statement's guard selector to `⊤`, dropping a loop's invariant, dropping
//! an effect from a control's `uses` clause, making an integer literal one
//! greater or one less, or replacing a comparison by the one beside it. For
//! the ownership of slice 2: removing a statement, so that what it consumed
//! stays and what it wrote is not written; letting two statements that
//! follow one another change places; consuming where a clone was made; and
//! removing the permission to fault of a control or the release under a
//! fault of a resource. Taking a name out of the care of a boundary, or out
//! of what a named boundary retains, is no mutation here: where the
//! contingency mentions the name `resolve` refuses the program, and where
//! it does not the program means the same.
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
    /// A statement that is no disposition and holds no body is removed: what
    /// it consumed is still owed, and what it wrote is not written ([O4],
    /// [O5], X5; [P1] to [P5], X7; [K7], X1 for `fault e` and `⊥`).
    RemoveStatement,
    /// `clone(e)` is replaced by `e`, which is consumed ([O2], [O3], X2).
    ConsumeClone,
    /// `faults` is removed from a control ([F1], X8).
    DropFaults,
    /// `on fault release` is removed from a resource ([F2], X8).
    DropFaultRelease,
    /// Two statements that follow one another in a body change places: what
    /// the second consumes or releases is gone when the first runs, and what
    /// may fault runs while something is owed ([O2] to [O5], [F2], X2, X5,
    /// X8).
    SwapStatements,
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

/// The statements of a declaration: the body of a control, or the work or
/// the contingency of a named boundary.
#[derive(Clone, Copy)]
struct Root {
    declaration: usize,
    contingency: bool,
}

/// A step from a body into one that a statement of it holds.
#[derive(Clone, Copy)]
enum Step {
    Loop(usize),
    Work(usize),
    Contingency(usize),
}

fn body_ref<'a>(program: &'a Program, root: Root, path: &[Step]) -> &'a [Statement] {
    let mut statements: &[Statement] = match &program.declarations[root.declaration] {
        Declaration::Control(control) => &control.body,
        Declaration::Boundary(boundary) if root.contingency => &boundary.contingency,
        Declaration::Boundary(boundary) => &boundary.body,
        _ => panic!("expected a declaration with a body"),
    };
    for step in path {
        statements = match (*step, &statements[step.index()].command) {
            (Step::Loop(_), Command::Loop { body, .. }) => body,
            (Step::Work(_), Command::Boundary { body, .. }) => body,
            (Step::Contingency(_), Command::Boundary { contingency, .. }) => contingency,
            _ => panic!("expected a statement that holds a body"),
        };
    }
    statements
}

fn body_mut<'a>(program: &'a mut Program, root: Root, path: &[Step]) -> &'a mut Vec<Statement> {
    let mut statements = match &mut program.declarations[root.declaration] {
        Declaration::Control(control) => &mut control.body,
        Declaration::Boundary(boundary) => {
            if root.contingency {
                &mut boundary.contingency
            } else {
                &mut boundary.body
            }
        }
        _ => panic!("expected a declaration with a body"),
    };
    for step in path {
        statements = match (*step, &mut statements[step.index()].command) {
            (Step::Loop(_), Command::Loop { body, .. }) => body,
            (Step::Work(_), Command::Boundary { body, .. }) => body,
            (Step::Contingency(_), Command::Boundary { contingency, .. }) => contingency,
            _ => panic!("expected a statement that holds a body"),
        };
    }
    statements
}

impl Step {
    fn index(self) -> usize {
        match self {
            Step::Loop(index) | Step::Work(index) | Step::Contingency(index) => index,
        }
    }
}

/// The mutant of `program` with the statement `index` of a body removed.
fn without_statement(program: &Program, root: Root, path: &[Step], index: usize) -> Program {
    let mut mutated = program.clone();
    body_mut(&mut mutated, root, path).remove(index);
    mutated
}

fn collect_from_body(
    program: &Program,
    root: Root,
    control_name: &str,
    path: &mut Vec<Step>,
    out: &mut Vec<Mutant>,
) {
    let statements = body_ref(program, root, path).to_vec();
    let made = |kind: Kind, detail: String, program: Program| Mutant {
        kind,
        control: control_name.to_string(),
        detail,
        program,
    };

    for second in 1..statements.len() {
        let mut mutated = program.clone();
        body_mut(&mut mutated, root, path).swap(second - 1, second);
        out.push(made(
            Kind::SwapStatements,
            format!("swap statements {} and {second}", second - 1),
            mutated,
        ));
    }

    for (index, statement) in statements.iter().enumerate() {
        if !matches!(statement.selector, Selector::Top) {
            let mut mutated = program.clone();
            body_mut(&mut mutated, root, path)[index].selector = Selector::Top;
            out.push(made(
                Kind::DropGuard,
                format!("drop guard at statement {index}"),
                mutated,
            ));
        }

        match &statement.command {
            Command::Decide { site, arms, .. } => {
                for (arm_index, arm) in arms.iter().enumerate() {
                    let mut mutated = program.clone();
                    let Command::Decide { arms: target, .. } =
                        &mut body_mut(&mut mutated, root, path)[index].command
                    else {
                        unreachable!();
                    };
                    target.remove(arm_index);
                    out.push(made(
                        Kind::RemoveArm,
                        format!("remove arm `{}` of `{site}`", arm.alternative),
                        mutated,
                    ));
                }
            }
            Command::Exit { alternative, .. }
            | Command::Leave { alternative, .. }
            | Command::Again {
                name: alternative, ..
            } => {
                out.push(made(
                    Kind::RemoveDisposition,
                    format!("remove disposition `{alternative}` at statement {index}"),
                    without_statement(program, root, path, index),
                ));
            }
            Command::Terminate(_) | Command::Escalate | Command::Recover { .. } => {
                let word = match &statement.command {
                    Command::Terminate(_) => "terminate",
                    Command::Escalate => "escalate",
                    _ => "recover",
                };
                out.push(made(
                    Kind::RemoveDisposition,
                    format!("remove disposition `{word}` at statement {index}"),
                    without_statement(program, root, path, index),
                ));
            }
            Command::Loop {
                name,
                invariant: Some(_),
                ..
            } => {
                let mut mutated = program.clone();
                let Command::Loop {
                    invariant: target, ..
                } = &mut body_mut(&mut mutated, root, path)[index].command
                else {
                    unreachable!();
                };
                *target = None;
                out.push(made(
                    Kind::DropInvariant,
                    format!("drop invariant of `{name}`"),
                    mutated,
                ));
            }
            _ => {}
        }

        match &statement.command {
            // A disposition has its own kind, and a statement that holds a
            // body is mutated inside.
            Command::Exit { .. }
            | Command::Leave { .. }
            | Command::Again { .. }
            | Command::Terminate(_)
            | Command::Escalate
            | Command::Recover { .. } => {}
            Command::Loop { .. } => {
                path.push(Step::Loop(index));
                collect_from_body(program, root, control_name, path, out);
                path.pop();
            }
            Command::Boundary { .. } => {
                for step in [Step::Work(index), Step::Contingency(index)] {
                    path.push(step);
                    collect_from_body(program, root, control_name, path, out);
                    path.pop();
                }
            }
            _ => out.push(made(
                Kind::RemoveStatement,
                format!("remove statement {index}"),
                without_statement(program, root, path, index),
            )),
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

/// Calls `visit` on every expression of the declaration: of a control, or of
/// the work and the contingency of a named boundary.
fn walk_declaration(declaration: &mut Declaration, visit: &mut dyn FnMut(&mut Expr)) {
    match declaration {
        Declaration::Control(control) => walk_control(control, visit),
        Declaration::Boundary(boundary) => {
            walk_statements(&mut boundary.body, visit);
            walk_statements(&mut boundary.contingency, visit);
        }
        _ => {}
    }
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
        Expr::Clone(inner) => vec![(
            Kind::ConsumeClone,
            (**inner).clone(),
            "a clone to what it copies".to_string(),
        )],
        _ => Vec::new(),
    }
}

/// The mutants of a control or of a named boundary that change one
/// expression of it.
fn collect_from_expressions(
    program: &Program,
    declaration: usize,
    name: &str,
    out: &mut Vec<Mutant>,
) {
    // How many changes each expression has, in the order of the walk.
    let mut counts = Vec::new();
    walk_declaration(
        &mut program.declarations[declaration].clone(),
        &mut |expr| {
            counts.push(changes(expr).len());
        },
    );
    for (site, count) in counts.iter().enumerate() {
        for choice in 0..*count {
            let mut mutated = program.clone();
            let target = &mut mutated.declarations[declaration];
            let mut at = 0;
            let mut made = None;
            walk_declaration(target, &mut |expr| {
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
                control: name.to_string(),
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
        match item {
            Declaration::Control(control) if !control.external => {
                for (effect_index, effect) in control.uses.iter().enumerate() {
                    let mut mutated = program.clone();
                    let Declaration::Control(target) = &mut mutated.declarations[declaration]
                    else {
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
                if control.faults {
                    let mut mutated = program.clone();
                    let Declaration::Control(target) = &mut mutated.declarations[declaration]
                    else {
                        unreachable!();
                    };
                    target.faults = false;
                    out.push(Mutant {
                        kind: Kind::DropFaults,
                        control: control.name.clone(),
                        detail: "drop `faults`".to_string(),
                        program: mutated,
                    });
                }
                let root = Root {
                    declaration,
                    contingency: false,
                };
                collect_from_body(program, root, &control.name, &mut Vec::new(), &mut out);
                collect_from_expressions(program, declaration, &control.name, &mut out);
            }
            Declaration::Boundary(boundary) => {
                for contingency in [false, true] {
                    let root = Root {
                        declaration,
                        contingency,
                    };
                    collect_from_body(program, root, &boundary.name, &mut Vec::new(), &mut out);
                }
                collect_from_expressions(program, declaration, &boundary.name, &mut out);
            }
            Declaration::Resource(resource) if resource.on_fault_release => {
                let mut mutated = program.clone();
                let Declaration::Resource(target) = &mut mutated.declarations[declaration] else {
                    unreachable!();
                };
                target.on_fault_release = false;
                out.push(Mutant {
                    kind: Kind::DropFaultRelease,
                    control: resource.name.clone(),
                    detail: "drop `on fault release`".to_string(),
                    program: mutated,
                });
            }
            _ => {}
        }
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
