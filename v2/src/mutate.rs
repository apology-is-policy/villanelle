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
//! For the borrows of slice 3, each aimed at a borrow that a run uses after
//! it ended: a borrow made in the other mode, with the type of the name it
//! is bound to; a borrow of the same place in the other mode, or an access
//! of its root, before a statement that mentions the name that holds it;
//! and a borrow of a name of borrow type after a later statement, so that
//! the name lives longer. Which names are of borrow type is read from the
//! program as `resolve` types it. A write through a shared borrow name is
//! no mutation here: `resolve` refuses it ([C1]).
//!
//! [`classify`] runs a mutant through `resolve` and the oracle across a set of
//! inputs. The mutants that are stuck in the oracle are those that the checker
//! of phase 3 must reject.

use std::collections::BTreeMap;

use crate::host::{Arithmetic, Seeded};
use crate::int::Int;
use crate::oracle::{self, Config, End, Stuck, Value};
use crate::resolve;
use crate::syntax::{
    Binary, Command, Control, Declaration, Expr, PlaceStep, Program, Selector, Statement,
};
use crate::typed::{self, BorrowMode, Type};

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
    /// A borrow `&p` that a name or a loop parameter is bound to is made
    /// `&~p`, or `&~p` is made `&p`, and the declared type of the name with
    /// it: an exclusive borrow ends the borrows of the place, and a read of
    /// the place ends it ([B1] to [B3], X4; [C1], [W8]).
    FlipBorrow,
    /// Before a statement that mentions a name bound to `&p` or `&~p`, a
    /// borrow of `p` in the other mode is bound to a fresh name: it ends
    /// the borrow that the name holds ([B2], [B3], X4).
    ConflictingBorrow,
    /// Before a statement that mentions a name bound to a borrow of `p`, the
    /// root of `p` is bound to a fresh name: a value that is copied is read,
    /// which ends an exclusive borrow of it, and one that is not is moved,
    /// which ends every borrow of it ([B2], [B4], X4).
    AccessLent,
    /// A name of borrow type is borrowed again after a later statement of
    /// its body, so that the borrow it holds lives over what the statements
    /// between do ([B1], [L2], X4; [O2], X2 where one of them moved it).
    ExtendBorrow,
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

/// The type of each name of the variables, where the name has one type.
fn types_of<'a>(vars: impl Iterator<Item = &'a typed::Var>) -> BTreeMap<String, Type> {
    let mut seen: BTreeMap<String, Option<Type>> = BTreeMap::new();
    for var in vars {
        seen.entry(var.name.clone())
            .and_modify(|ty| {
                if ty.as_ref() != Some(&var.ty) {
                    *ty = None;
                }
            })
            .or_insert_with(|| Some(var.ty.clone()));
    }
    seen.into_iter()
        .filter_map(|(name, ty)| Some((name, ty?)))
        .collect()
}

/// The types of the names of each control and named boundary, by the name
/// of the declaration; a name bound at two types in one is left out.
fn name_types(typed: &typed::Program) -> BTreeMap<String, BTreeMap<String, Type>> {
    let mut out = BTreeMap::new();
    for control in &typed.controls {
        if let Some(body) = &control.body {
            out.insert(control.name.clone(), types_of(body.vars.iter()));
        }
    }
    for boundary in &typed.boundaries {
        let vars = boundary.body.vars.iter().chain(&boundary.contingency.vars);
        out.insert(boundary.name.clone(), types_of(vars));
    }
    out
}

/// A name of borrow type that a body holds after a statement of it, or from
/// its start: the selector of the histories on which it is bound, and the
/// borrow it holds where the text says of which place: `x := &p`, or a
/// payload name of a control whose contract derives it from a parameter
/// (`∈ y`) for which the argument is `&p` or `&~p`; then the place of the
/// borrow is within `p`.
struct Holder {
    name: String,
    selector: Selector,
    borrow: Option<(BorrowMode, Expr)>,
}

/// The place that the payload name at `position` of `alternative` borrows
/// within, where the contract of `operation` derives it from one parameter
/// and the argument for that parameter is a borrow.
fn payload_borrow(
    program: &Program,
    operation: &str,
    arguments: &[Expr],
    alternative: &str,
    position: usize,
) -> Option<(BorrowMode, Expr)> {
    let control = program
        .declarations
        .iter()
        .find_map(|declaration| match declaration {
            Declaration::Control(control) if control.name == operation => Some(control),
            _ => None,
        })?;
    let field = control
        .contract
        .iter()
        .find(|candidate| candidate.name == alternative)?
        .fields
        .get(position)?;
    let (Type::Ref(mode, _), [origin]) = (&field.ty, field.origins.as_slice()) else {
        return None;
    };
    let index = control
        .parameters
        .iter()
        .position(|parameter| &parameter.name == origin)?;
    match arguments.get(index)? {
        Expr::Borrow(_, place) => Some((*mode, (**place).clone())),
        _ => None,
    }
}

/// The names of borrow type that `statement` binds.
fn holders_of(
    program: &Program,
    statement: &Statement,
    types: &BTreeMap<String, Type>,
) -> Vec<Holder> {
    let borrowed = |name: &String| matches!(types.get(name), Some(Type::Ref(..)));
    let of_arms = |site: &str, arms: &[crate::syntax::Arm], call: Option<(&str, &[Expr])>| {
        let mut holders = Vec::new();
        for arm in arms {
            for (position, name) in arm.names.iter().enumerate() {
                if !borrowed(name) {
                    continue;
                }
                holders.push(Holder {
                    name: name.clone(),
                    selector: Selector::Atom(site.to_string(), arm.alternative.clone()),
                    borrow: call.and_then(|(operation, arguments)| {
                        payload_borrow(program, operation, arguments, &arm.alternative, position)
                    }),
                });
            }
        }
        holders
    };
    match &statement.command {
        Command::Bind { name, value, .. } if borrowed(name) => vec![Holder {
            name: name.clone(),
            selector: statement.selector.clone(),
            borrow: match value {
                Expr::Borrow(mode, place) => Some((*mode, (**place).clone())),
                _ => None,
            },
        }],
        Command::Unpack { names, .. } => names
            .iter()
            .filter(|name| borrowed(name))
            .map(|name| Holder {
                name: name.clone(),
                selector: statement.selector.clone(),
                borrow: None,
            })
            .collect(),
        Command::Decide {
            site,
            operation,
            arguments,
            arms,
            ..
        } => of_arms(site, arms, Some((operation, arguments))),
        Command::Loop { site, arms, .. } => of_arms(site, arms, None),
        _ => Vec::new(),
    }
}

/// Whether one of the statements mentions `name`.
fn mentions(statements: &[Statement], name: &str) -> bool {
    let mut found = false;
    walk_statements(&mut statements.to_vec(), &mut |expr| {
        if let Expr::Name(seen) | Expr::Old(seen) = expr {
            found |= seen == name;
        }
    });
    found
        || statements.iter().any(|statement| match &statement.command {
            Command::Assign { name: target, .. } => target == name,
            Command::AssignPlace { target, .. } => target.root == name,
            Command::Cancel { set } | Command::Spawn { set, .. } => set == name,
            Command::Loop { body, .. } => mentions(body, name),
            Command::Boundary {
                body,
                captures,
                contingency,
                ..
            } => {
                captures.iter().any(|capture| capture == name)
                    || mentions(body, name)
                    || mentions(contingency, name)
            }
            _ => false,
        })
}

/// Whether a statement ends the histories that its selector takes.
fn is_disposition(command: &Command) -> bool {
    matches!(
        command,
        Command::Exit { .. }
            | Command::Leave { .. }
            | Command::Again { .. }
            | Command::Terminate(_)
            | Command::Escalate
            | Command::Recover { .. }
            | Command::Impossible
            | Command::Fault { .. }
    )
}

/// The name at the root of a place.
fn root_name(place: &Expr) -> Option<&str> {
    match place {
        Expr::Name(name) => Some(name),
        Expr::Field(inner, _) | Expr::Index(inner, _) => root_name(inner),
        _ => None,
    }
}

fn other(mode: BorrowMode) -> BorrowMode {
    match mode {
        BorrowMode::Shared => BorrowMode::Exclusive,
        BorrowMode::Exclusive => BorrowMode::Shared,
    }
}

fn sign(mode: BorrowMode) -> &'static str {
    match mode {
        BorrowMode::Shared => "&",
        BorrowMode::Exclusive => "&~",
    }
}

/// The type of a name bound to a borrow made in the other mode.
fn flipped(ty: &Option<Type>) -> Option<Type> {
    match ty {
        Some(Type::Ref(mode, inner)) => Some(Type::Ref(other(*mode), inner.clone())),
        other => other.clone(),
    }
}

/// What the mutants of the borrows of one declaration share: the program,
/// the statements of the declaration, its name, the types of its names and
/// a name that the program does not use.
struct Lending<'a> {
    program: &'a Program,
    root: Root,
    control: &'a str,
    types: &'a BTreeMap<String, Type>,
    fresh: &'a str,
}

/// The mutants of the borrows of a body and of the bodies within it.
/// `entry` holds the names of borrow type bound at the start of the body
/// (the parameters of a loop).
fn collect_borrows(
    lending: &Lending,
    path: &mut Vec<Step>,
    entry: Vec<Holder>,
    out: &mut Vec<Mutant>,
) {
    let Lending {
        program,
        root,
        control: control_name,
        types,
        fresh,
    } = *lending;
    let statements = body_ref(program, root, path).to_vec();
    let at = |index: usize| {
        statements
            .get(index)
            .or(statements.last())
            .map_or(0, |s| s.line)
    };
    let insert = |index: usize, selector: &Selector, value: Expr| {
        let mut mutated = program.clone();
        body_mut(&mut mutated, root, path).insert(
            index,
            Statement {
                selector: selector.clone(),
                command: Command::Bind {
                    mutable: false,
                    name: fresh.to_string(),
                    ty: None,
                    value,
                },
                line: at(index),
            },
        );
        mutated
    };
    let mut push = |kind: Kind, detail: String, program: Program| {
        out.push(Mutant {
            kind,
            control: control_name.to_string(),
            detail,
            program,
        })
    };

    // Each holder with the index of the first statement after its binding.
    let mut holders: Vec<(usize, Holder)> = entry.into_iter().map(|h| (0, h)).collect();
    for (index, statement) in statements.iter().enumerate() {
        holders.extend(
            holders_of(program, statement, types)
                .into_iter()
                .map(|holder| (index + 1, holder)),
        );
    }

    for (from, holder) in &holders {
        let name = &holder.name;
        if let Some((mode, place)) = &holder.borrow {
            for index in *from..statements.len() {
                if !mentions(&statements[index..=index], name) {
                    continue;
                }
                let made = Expr::Borrow(other(*mode), Box::new(place.clone()));
                push(
                    Kind::ConflictingBorrow,
                    format!(
                        "`{}{place}` before statement {index}, which mentions `{name}`",
                        sign(other(*mode)),
                    ),
                    insert(index, &holder.selector, made),
                );
                if let Some(lent) = root_name(place) {
                    push(
                        Kind::AccessLent,
                        format!("`{lent}` before statement {index}, which mentions `{name}`"),
                        insert(index, &holder.selector, Expr::Name(lent.to_string())),
                    );
                }
            }
        }
        // After statement `index - 1`; not after the last one where it ends
        // every history, and not just after the binding.
        for index in (from + 1).max(1)..=statements.len() {
            if index == statements.len() && is_disposition(&statements[index - 1].command) {
                continue;
            }
            let read = Expr::Borrow(BorrowMode::Shared, Box::new(Expr::Name(name.clone())));
            push(
                Kind::ExtendBorrow,
                format!("`&{name}` after statement {}", index - 1),
                insert(index, &holder.selector, read),
            );
        }
    }

    for (index, statement) in statements.iter().enumerate() {
        match &statement.command {
            Command::Bind {
                value: Expr::Borrow(mode, place),
                ty,
                ..
            } => {
                let mut mutated = program.clone();
                let Command::Bind {
                    value, ty: target, ..
                } = &mut body_mut(&mut mutated, root, path)[index].command
                else {
                    unreachable!();
                };
                *value = Expr::Borrow(other(*mode), place.clone());
                *target = flipped(ty);
                push(
                    Kind::FlipBorrow,
                    format!(
                        "`{}` to `{}` at statement {index}",
                        sign(*mode),
                        sign(other(*mode))
                    ),
                    mutated,
                );
            }
            Command::Loop { parameters, .. } => {
                for (number, parameter) in parameters.iter().enumerate() {
                    let Expr::Borrow(mode, place) = &parameter.initial else {
                        continue;
                    };
                    let mut mutated = program.clone();
                    let Command::Loop {
                        parameters: target, ..
                    } = &mut body_mut(&mut mutated, root, path)[index].command
                    else {
                        unreachable!();
                    };
                    target[number].initial = Expr::Borrow(other(*mode), place.clone());
                    if let Some(ty) = flipped(&Some(parameter.ty.clone())) {
                        target[number].ty = ty;
                    }
                    push(
                        Kind::FlipBorrow,
                        format!(
                            "`{}` to `{}` for `{}` at statement {index}",
                            sign(*mode),
                            sign(other(*mode)),
                            parameter.name
                        ),
                        mutated,
                    );
                }
            }
            _ => {}
        }
    }

    for (index, statement) in statements.iter().enumerate() {
        match &statement.command {
            Command::Loop { parameters, .. } => {
                let entry = parameters
                    .iter()
                    .filter(|parameter| matches!(parameter.ty, Type::Ref(..)))
                    .map(|parameter| Holder {
                        name: parameter.name.clone(),
                        selector: Selector::Top,
                        borrow: match &parameter.initial {
                            Expr::Borrow(mode, place) => Some((*mode, (**place).clone())),
                            _ => None,
                        },
                    })
                    .collect();
                path.push(Step::Loop(index));
                collect_borrows(lending, path, entry, out);
                path.pop();
            }
            Command::Boundary { .. } => {
                for step in [Step::Work(index), Step::Contingency(index)] {
                    path.push(step);
                    collect_borrows(lending, path, Vec::new(), out);
                    path.pop();
                }
            }
            _ => {}
        }
    }
}

/// A name that no part of the program's text holds.
fn fresh_name(program: &Program) -> String {
    let text = program.print();
    (0..)
        .map(|number| format!("z{number}"))
        .find(|name| !text.contains(name.as_str()))
        .expect("a fresh name")
}

/// Produces all single-step mutants of `program`.
pub fn mutate(program: &Program) -> Vec<Mutant> {
    let mut out = Vec::new();
    let types = resolve::resolve(program)
        .map(|typed| name_types(&typed))
        .unwrap_or_default();
    let fresh = fresh_name(program);
    let borrows = |declaration: &str, root: Root, out: &mut Vec<Mutant>| {
        if let Some(names) = types.get(declaration) {
            let lending = Lending {
                program,
                root,
                control: declaration,
                types: names,
                fresh: &fresh,
            };
            collect_borrows(&lending, &mut Vec::new(), Vec::new(), out);
        }
    };
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
                borrows(&control.name, root, &mut out);
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
                for contingency in [false, true] {
                    let root = Root {
                        declaration,
                        contingency,
                    };
                    borrows(&boundary.name, root, &mut out);
                }
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
