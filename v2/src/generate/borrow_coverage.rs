//! The constructs of the borrows of slice 3 that a program reaches.
//!
//! Which names hold borrows is a matter of types, so the observer keeps,
//! for the control being observed, the names whose type is a borrow: its
//! borrowed parameters, the names bound with a borrow type, and the payload
//! names of a decision whose contract field is a borrow.

use super::Coverage;
use crate::syntax::{Command, Control, Declaration, Expr, Program, Statement};
use crate::typed::{BorrowMode, Type};
use std::collections::BTreeSet;

/// The constructs that slice 3 adds: borrows of places and through borrow
/// names, copied, moved, written through and passed on, borrowed parameters,
/// and payloads that borrow from the arguments.
pub const BORROW_CONSTRUCTS: [&str; 20] = [
    "borrow-shared-name",
    "borrow-exclusive-name",
    "borrow-field",
    "borrow-element",
    "reborrow",
    "borrow-copy",
    "borrow-move",
    "write-through",
    "write-through-place",
    "read-through",
    "borrow-argument",
    "reborrow-argument",
    "borrow-builtin",
    "borrow-parameter",
    "exclusive-borrow-parameter",
    "payload-borrow",
    "payload-exclusive-borrow",
    "payload-borrow-name",
    "borrow-in-loop",
    "write-through-in-loop",
];

const BUILT_IN: [&str; 8] = [
    "push", "pop", "take", "get", "insert", "remove", "entry_at", "emit",
];

/// The names that hold borrows in the control being observed, and the
/// loops around the statement being observed, each with the borrow names
/// bound outside it.
struct Names<'p> {
    program: &'p Program,
    borrows: BTreeSet<String>,
    outside: Vec<BTreeSet<String>>,
}

fn root(expr: &Expr) -> Option<&str> {
    match expr {
        Expr::Name(name) => Some(name),
        Expr::Field(base, _) | Expr::Index(base, _) => root(base),
        _ => None,
    }
}

impl Coverage {
    /// Observes the constructs of [`BORROW_CONSTRUCTS`] in `program`.
    pub(super) fn observe_borrows(&mut self, program: &Program) {
        for declaration in &program.declarations {
            let Declaration::Control(control) = declaration else {
                continue;
            };
            if control.external {
                for field in control.contract.iter().flat_map(|alt| &alt.fields) {
                    match field.ty {
                        Type::Ref(BorrowMode::Shared, _) => self.hit("payload-borrow"),
                        Type::Ref(BorrowMode::Exclusive, _) => self.hit("payload-exclusive-borrow"),
                        _ => {}
                    }
                }
                continue;
            }
            let mut names = Names {
                program,
                borrows: BTreeSet::new(),
                outside: Vec::new(),
            };
            for parameter in &control.parameters {
                match parameter.ty {
                    Type::Ref(BorrowMode::Shared, _) => self.hit("borrow-parameter"),
                    Type::Ref(BorrowMode::Exclusive, _) => self.hit("exclusive-borrow-parameter"),
                    _ => continue,
                }
                names.borrows.insert(parameter.name.clone());
            }
            self.borrow_statements(&control.body, &mut names);
        }
    }

    fn borrow_statements(&mut self, statements: &[Statement], names: &mut Names<'_>) {
        for statement in statements {
            match &statement.command {
                Command::Bind {
                    name, ty, value, ..
                } => {
                    let borrowed = matches!(ty, Some(Type::Ref(_, _)));
                    match (ty, value) {
                        (Some(Type::Ref(mode, _)), Expr::Borrow(_, place)) => {
                            self.hit(match mode {
                                BorrowMode::Shared => "borrow-shared-name",
                                BorrowMode::Exclusive => "borrow-exclusive-name",
                            });
                            self.borrow_place(place, names);
                        }
                        (Some(Type::Ref(BorrowMode::Shared, _)), Expr::Name(_)) => {
                            self.hit("borrow-copy")
                        }
                        (
                            Some(Type::Ref(BorrowMode::Exclusive, _)),
                            Expr::Name(_) | Expr::Move(_),
                        ) => self.hit("borrow-move"),
                        _ => self.borrow_expr(value, names),
                    }
                    if borrowed {
                        names.borrows.insert(name.clone());
                    }
                }
                Command::Assign { name, value } => {
                    if names.borrows.contains(name) {
                        self.hit("write-through");
                        self.write_in_loop(name, names);
                    }
                    self.borrow_expr(value, names);
                }
                Command::AssignPlace { target, value } => {
                    if names.borrows.contains(&target.root) {
                        self.hit("write-through-place");
                        self.write_in_loop(&target.root, names);
                    }
                    self.borrow_expr(value, names);
                }
                Command::Decide {
                    operation,
                    arguments,
                    arms,
                    ..
                } => {
                    self.borrow_arguments(operation, arguments, names);
                    let contract =
                        names.program.declarations.iter().find_map(
                            |declaration| match declaration {
                                Declaration::Control(Control { name, contract, .. })
                                    if name == operation =>
                                {
                                    Some(contract)
                                }
                                _ => None,
                            },
                        );
                    for arm in arms {
                        let Some(alternative) = contract
                            .and_then(|alts| alts.iter().find(|alt| alt.name == arm.alternative))
                        else {
                            continue;
                        };
                        for (bound, field) in arm.names.iter().zip(&alternative.fields) {
                            if matches!(field.ty, Type::Ref(_, _)) {
                                self.hit("payload-borrow-name");
                                names.borrows.insert(bound.clone());
                            }
                        }
                    }
                }
                Command::Capture {
                    operation,
                    arguments,
                    ..
                } => self.borrow_arguments(operation, arguments, names),
                Command::Loop {
                    parameters, body, ..
                } => {
                    for parameter in parameters {
                        self.borrow_expr(&parameter.initial, names);
                    }
                    names.outside.push(names.borrows.clone());
                    self.borrow_statements(body, names);
                    names.outside.pop();
                }
                Command::Boundary {
                    body, contingency, ..
                } => {
                    self.borrow_statements(body, names);
                    self.borrow_statements(contingency, names);
                }
                Command::Oblige(expr)
                | Command::Test {
                    condition: expr, ..
                } => self.borrow_expr(expr, names),
                Command::Unpack { value, .. } => self.borrow_expr(value, names),
                Command::Supervise { arguments, .. }
                | Command::Spawn { arguments, .. }
                | Command::Again { arguments, .. }
                | Command::Leave {
                    payload: arguments, ..
                }
                | Command::Exit {
                    payload: arguments, ..
                } => {
                    for argument in arguments {
                        self.borrow_expr(argument, names);
                    }
                }
                _ => {}
            }
        }
    }

    fn write_in_loop(&mut self, name: &str, names: &Names<'_>) {
        if names
            .outside
            .last()
            .is_some_and(|outside| outside.contains(name))
        {
            self.hit("write-through-in-loop");
        }
    }

    fn borrow_place(&mut self, place: &Expr, names: &Names<'_>) {
        match place {
            Expr::Field(_, _) => self.hit("borrow-field"),
            Expr::Index(_, _) => self.hit("borrow-element"),
            _ => {}
        }
        if root(place).is_some_and(|root| names.borrows.contains(root)) {
            self.hit("reborrow");
        }
        if let Expr::Index(_, index) = place {
            self.borrow_expr(index, names);
        }
    }

    fn borrow_arguments(&mut self, operation: &str, arguments: &[Expr], names: &Names<'_>) {
        for argument in arguments {
            match argument {
                Expr::Name(name) if names.borrows.contains(name) => self.hit("borrow-argument"),
                Expr::Move(inner) if matches!(&**inner, Expr::Name(name) if names.borrows.contains(name)) => {
                    self.hit("borrow-argument")
                }
                Expr::Borrow(_, place) => {
                    if root(place).is_some_and(|root| names.borrows.contains(root)) {
                        self.hit(if BUILT_IN.contains(&operation) {
                            "borrow-builtin"
                        } else {
                            "reborrow-argument"
                        });
                    }
                    if let Expr::Index(_, index) = &**place {
                        self.borrow_expr(index, names);
                    }
                }
                other => self.borrow_expr(other, names),
            }
        }
    }

    /// A borrow name read in an expression is a read through it ([B1]).
    fn borrow_expr(&mut self, expr: &Expr, names: &Names<'_>) {
        match expr {
            Expr::Name(name) => {
                if names.borrows.contains(name) {
                    self.hit("read-through");
                    if names
                        .outside
                        .last()
                        .is_some_and(|outside| outside.contains(name))
                    {
                        self.hit("borrow-in-loop");
                    }
                }
            }
            Expr::Integer(_)
            | Expr::Boolean(_)
            | Expr::String(_)
            | Expr::EmptyMap
            | Expr::TasksEmpty(_)
            | Expr::Old(_)
            | Expr::Count(_) => {}
            Expr::Move(inner)
            | Expr::Field(inner, _)
            | Expr::Len(inner)
            | Expr::Clone(inner)
            | Expr::Unary(_, inner) => self.borrow_expr(inner, names),
            Expr::Borrow(_, place) => self.borrow_place(place, names),
            Expr::Index(left, right) | Expr::Binary(_, left, right) => {
                self.borrow_expr(left, names);
                self.borrow_expr(right, names);
            }
            Expr::Struct(_, items)
            | Expr::Variant(_, _, items)
            | Expr::Vector(items)
            | Expr::Call(_, items) => {
                for item in items {
                    self.borrow_expr(item, names);
                }
            }
        }
    }
}
