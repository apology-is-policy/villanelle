//! Random core programs of slice 1 that are valid by construction.
//!
//! A program is valid when it resolves, when no execution of it from an
//! entry that satisfies its precondition is stuck in the oracle under a host
//! that respects its contracts, and when the checker accepts it.
//!
//! The generator writes a body statement by statement and keeps, beside it,
//! every history that is still running ([K1] to [K3] of `docs/v2/core.md`).
//! A history is the set of its atoms with what is known on it: the names
//! that are bound and an interval for each integer. A statement with
//! selector `g` runs on the histories that satisfy `g`, a test or a decision
//! splits each of them, a terminator ends them, and the body is complete when
//! none is left ([K7]). A history whose intervals become empty cannot
//! happen, and gets `⊥` or nothing.
//!
//! Every obligation of a statement ([P1] to [P6]) is discharged on the
//! intervals of the histories that run it: an arithmetic result lies in its
//! type, a divisor is not zero, a precondition, an invariant and the
//! condition of an alternative hold. The intervals come from facts that the
//! checker has too (binds, tests, conditions of alternatives, preconditions,
//! invariants, the ranges of types), and the partial operators are bounded as
//! the fact logic bounds them ([`super::interval`]). So the generator never
//! concludes more than the fact logic entails.
//!
//! What it does not do: it knows nothing relational beyond an interval (the
//! one exception is a recalled definition, `⊢ x = e` straight after
//! `x := e`), and it covers slice 1 only.

use super::interval::{
    NEG, POS, Range, above, add, below, divide_by_literal, divide_by_term, multiply, negate,
    product_by_planes, remainder_by_literal, remainder_by_term, scale, subtract,
};
use super::{bin, int, name, stmt};
use crate::int::Int;
use crate::rng::Rng;
use crate::syntax::{
    Alternative, Arm, Binary, CallMode, Command, Control, Declaration, Expr, Function,
    LoopParameter, Parameter, Program, Selector, Statement, Unary,
};
use crate::typed::{IntType, Type};
use std::collections::{BTreeMap, BTreeSet};

const ALTERNATIVES: [&str; 12] = [
    "done", "ok", "low", "high", "none", "some", "left", "right", "stop", "more", "hit", "miss",
];
const EFFECTS: [&str; 3] = ["io", "net", "log"];
const COMPARISONS: [Binary; 6] = [
    Binary::Equal,
    Binary::NotEqual,
    Binary::Less,
    Binary::LessEqual,
    Binary::Greater,
    Binary::GreaterEqual,
];

/// Beyond this many running histories a body stops splitting all of them.
const MAX_HISTORIES: usize = 24;
/// The control body and at most two loops inside each other.
const MAX_BODIES: usize = 3;
const MAX_LOOPS: usize = 3;

/// The values of a type on the widest target.
fn value_range(ty: IntType) -> Range {
    let greatest = Int::power_of_two(64).minus(&Int::from_u64(1));
    let (least, most) = ty.bounds(&greatest);
    Range::new(
        least.to_i128().unwrap_or(NEG),
        most.to_i128().unwrap_or(POS),
    )
}

/// Where the result of a checked operator must lie to be a value on every
/// target ([A2]): a `usize` within 32 bits.
fn fit_range(ty: IntType) -> Range {
    let (least, most) = ty.literal_bounds();
    Range::new(
        least.to_i128().unwrap_or(NEG),
        most.to_i128().unwrap_or(POS),
    )
}

/// The declared interval of a value term ([A9]): the bounds of its type that
/// are literals, so a `usize` has no upper end.
fn declared_range(ty: IntType) -> Range {
    let range = value_range(ty);
    if ty == IntType::Usize {
        Range::new(range.lo, POS)
    } else {
        range
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Tri {
    True,
    False,
    Unknown,
}

impl Tri {
    fn of(value: bool) -> Tri {
        if value { Tri::True } else { Tri::False }
    }

    fn not(self) -> Tri {
        match self {
            Tri::True => Tri::False,
            Tri::False => Tri::True,
            Tri::Unknown => Tri::Unknown,
        }
    }

    fn and(self, other: Tri) -> Tri {
        match (self, other) {
            (Tri::False, _) | (_, Tri::False) => Tri::False,
            (Tri::True, Tri::True) => Tri::True,
            _ => Tri::Unknown,
        }
    }

    fn or(self, other: Tri) -> Tri {
        self.not().and(other.not()).not()
    }

    fn hull(self, other: Tri) -> Tri {
        if self == other { self } else { Tri::Unknown }
    }
}

/// What is known of an integer term: the interval that the facts give, its
/// declared interval ([A9]), and its value when it is a constant expression
/// ([I3]).
#[derive(Clone, Copy, Debug)]
struct Val {
    flow: Range,
    declared: Range,
    constant: Option<i128>,
}

impl Val {
    fn constant(value: i128) -> Val {
        Val {
            flow: Range::point(value),
            declared: Range::point(value),
            constant: Some(value),
        }
    }

    fn unknown() -> Val {
        Val {
            flow: Range::ALL,
            declared: Range::ALL,
            constant: None,
        }
    }

    /// A value term of `ty` known to lie in `flow`.
    fn value(ty: IntType, flow: Range) -> Val {
        Val {
            flow: flow.meet(value_range(ty)),
            declared: declared_range(ty),
            constant: None,
        }
    }
}

#[derive(Clone, Debug)]
enum Know {
    Int(Val),
    Bool(Tri),
}

impl Know {
    fn top(ty: &Type) -> Know {
        match ty {
            Type::Int(int_ty) => Know::Int(Val::value(*int_ty, Range::ALL)),
            _ => Know::Bool(Tri::Unknown),
        }
    }

    fn hull(&self, other: &Know) -> Know {
        match (self, other) {
            (Know::Int(a), Know::Int(b)) => Know::Int(Val {
                flow: a.flow.hull(b.flow),
                declared: a.declared.hull(b.declared),
                constant: if a.constant == b.constant {
                    a.constant
                } else {
                    None
                },
            }),
            (Know::Bool(a), Know::Bool(b)) => Know::Bool(a.hull(*b)),
            (seen, _) => seen.clone(),
        }
    }
}

/// A name on one history.
#[derive(Clone, Debug)]
struct Slot {
    ty: Type,
    mutable: bool,
    know: Know,
    /// For a `bool` bound once to an expression over names that never
    /// change: that expression ([I13]).
    definition: Option<Expr>,
}

type Env = BTreeMap<String, Slot>;

struct FnSig {
    name: String,
    params: Vec<(String, Type)>,
    /// For each parameter, the interval its precondition gives it.
    pre: Vec<Range>,
    result: Type,
    body: Expr,
}

/// One end of the interval that a condition gives a payload field.
#[derive(Clone, Copy, Debug)]
enum End {
    Open,
    Literal(i128),
    /// A parameter of the same type, plus a literal.
    Parameter(usize, i128),
}

#[derive(Clone, Debug)]
struct FieldSig {
    name: String,
    ty: Type,
    lo: End,
    hi: End,
}

#[derive(Clone, Debug)]
struct AltSig {
    name: String,
    fields: Vec<FieldSig>,
    /// What the condition says about each parameter.
    params: Vec<Option<Range>>,
}

/// The signature of a control as its callers see it.
#[derive(Clone, Debug)]
struct Sig {
    name: String,
    params: Vec<(String, Type)>,
    pre: Vec<Range>,
    /// `(i, j)`: the precondition also says `pᵢ ≤ pⱼ`, with `i < j`.
    order: Option<(usize, usize)>,
    alts: Vec<AltSig>,
    uses: Vec<String>,
}

fn opposite(operator: Binary) -> Binary {
    match operator {
        Binary::Less => Binary::GreaterEqual,
        Binary::LessEqual => Binary::Greater,
        Binary::Greater => Binary::LessEqual,
        Binary::GreaterEqual => Binary::Less,
        Binary::Equal => Binary::NotEqual,
        Binary::NotEqual => Binary::Equal,
        other => other,
    }
}

fn compare(operator: Binary, a: Range, b: Range) -> Tri {
    let less = |a: Range, b: Range| {
        if a.hi < b.lo {
            Tri::True
        } else if a.lo >= b.hi {
            Tri::False
        } else {
            Tri::Unknown
        }
    };
    let less_equal = |a: Range, b: Range| {
        if a.hi <= b.lo {
            Tri::True
        } else if a.lo > b.hi {
            Tri::False
        } else {
            Tri::Unknown
        }
    };
    let equal = if a.as_point().is_some() && a.as_point() == b.as_point() {
        Tri::True
    } else if a.meet(b).is_empty() {
        Tri::False
    } else {
        Tri::Unknown
    };
    match operator {
        Binary::Less => less(a, b),
        Binary::LessEqual => less_equal(a, b),
        Binary::Greater => less(b, a),
        Binary::GreaterEqual => less_equal(b, a),
        Binary::Equal => equal,
        Binary::NotEqual => equal.not(),
        _ => Tri::Unknown,
    }
}

/// `a` without the value `point`, when that value is one of its ends.
fn without(a: Range, point: Option<i128>) -> Range {
    match point {
        Some(value) if a.lo == value && a.hi == value => Range { lo: 1, hi: 0 },
        Some(value) if a.lo == value => Range {
            lo: value + 1,
            hi: a.hi,
        },
        Some(value) if a.hi == value => Range {
            lo: a.lo,
            hi: value - 1,
        },
        _ => a,
    }
}

fn literal_of(expr: &Expr) -> Option<i128> {
    match expr {
        Expr::Integer(value) => value.to_i128(),
        Expr::Unary(Unary::Negate, inner) => match &**inner {
            Expr::Integer(value) => value.to_i128().map(|value| -value),
            _ => None,
        },
        _ => None,
    }
}

/// The interval reasoning: what an expression is worth on a history, whether
/// its obligations hold there, and what a condition adds.
struct Lib<'a> {
    functions: &'a [FnSig],
}

impl Lib<'_> {
    fn function(&self, name: &str) -> Option<&FnSig> {
        self.functions.iter().find(|function| function.name == name)
    }

    /// The integer type that a name or a call in `expr` gives it. An
    /// expression of literals alone has none, and is `u32` unless its place
    /// expects another type ([C1]).
    fn anchor(&self, expr: &Expr, env: &Env) -> Option<IntType> {
        match expr {
            Expr::Name(name) => match &env.get(name)?.ty {
                Type::Int(ty) => Some(*ty),
                _ => None,
            },
            Expr::Call(function, _) => match &self.function(function)?.result {
                Type::Int(ty) => Some(*ty),
                _ => None,
            },
            Expr::Unary(Unary::Negate, inner) => self.anchor(inner, env),
            Expr::Binary(operator, left, right) if operator.level() >= 4 => {
                self.anchor(left, env).or_else(|| self.anchor(right, env))
            }
            _ => None,
        }
    }

    /// The value of an integer expression on `env`. With `fit`, the
    /// expression is evaluated ([E-Arith], [E-Fn]) and the answer is `None`
    /// unless every obligation of [P5] and [P3] follows from the intervals.
    /// Without, it is a term of a formula ([E-Formula]) and has no
    /// obligations.
    fn int(&self, expr: &Expr, env: &Env, fit: Option<IntType>) -> Option<Val> {
        let fits = |val: Val| match fit {
            Some(ty) if !val.flow.within(fit_range(ty)) => None,
            _ => Some(val),
        };
        match expr {
            Expr::Integer(_) | Expr::Unary(Unary::Negate, _) if literal_of(expr).is_some() => {
                fits(Val::constant(literal_of(expr)?))
            }
            Expr::Unary(Unary::Negate, inner) => {
                let operand = self.int(inner, env, fit)?;
                fits(Val {
                    flow: negate(operand.flow),
                    declared: negate(operand.declared),
                    constant: operand.constant.and_then(i128::checked_neg),
                })
            }
            Expr::Name(name) => match &env.get(name)?.know {
                Know::Int(val) => Some(*val),
                Know::Bool(_) => None,
            },
            Expr::Binary(operator, left, right) => {
                let a = self.int(left, env, fit)?;
                let b = self.int(right, env, fit)?;
                let val = match operator {
                    Binary::Add => Val {
                        flow: add(a.flow, b.flow),
                        declared: add(a.declared, b.declared),
                        constant: a
                            .constant
                            .zip(b.constant)
                            .and_then(|(x, y)| x.checked_add(y)),
                    },
                    Binary::Subtract => Val {
                        flow: subtract(a.flow, b.flow),
                        declared: subtract(a.declared, b.declared),
                        constant: a
                            .constant
                            .zip(b.constant)
                            .and_then(|(x, y)| x.checked_sub(y)),
                    },
                    Binary::Multiply => match (a.constant, b.constant) {
                        (Some(x), Some(y)) => {
                            x.checked_mul(y).map_or(Val::unknown(), Val::constant)
                        }
                        (Some(factor), None) => Val {
                            flow: scale(b.flow, factor),
                            declared: scale(b.declared, factor),
                            constant: None,
                        },
                        (None, Some(factor)) => Val {
                            flow: scale(a.flow, factor),
                            declared: scale(a.declared, factor),
                            constant: None,
                        },
                        (None, None) => Val {
                            flow: product_by_planes(a.flow, a.declared, b.flow, b.declared),
                            declared: if a.declared.bounded() && b.declared.bounded() {
                                multiply(a.declared, b.declared)
                            } else {
                                Range::ALL
                            },
                            constant: None,
                        },
                    },
                    Binary::Divide | Binary::Remainder => {
                        let quotient = *operator == Binary::Divide;
                        match (b.constant, a.constant) {
                            (Some(0), _) => {
                                if fit.is_some() {
                                    return None;
                                }
                                Val::unknown()
                            }
                            (Some(divisor), Some(dividend)) => Val::constant(if quotient {
                                dividend / divisor
                            } else {
                                dividend % divisor
                            }),
                            (Some(divisor), None) => {
                                let by = if quotient {
                                    divide_by_literal
                                } else {
                                    remainder_by_literal
                                };
                                Val {
                                    flow: by(a.flow, divisor),
                                    declared: by(a.declared, divisor),
                                    constant: None,
                                }
                            }
                            (None, _) => {
                                let flow = if quotient {
                                    divide_by_term(a.flow, b.flow)
                                } else {
                                    remainder_by_term(a.flow, b.flow)
                                };
                                match flow {
                                    Some(flow) => Val {
                                        flow,
                                        declared: Range::ALL,
                                        constant: None,
                                    },
                                    None => {
                                        if fit.is_some() {
                                            return None;
                                        }
                                        Val::unknown()
                                    }
                                }
                            }
                        }
                    }
                    _ => return None,
                };
                fits(val)
            }
            Expr::Call(function, arguments) => {
                let sig = self.function(function)?;
                let inner = self.bind_arguments(sig, arguments, env, fit.is_some())?;
                // [I8]: the call is the body on the argument terms. Its own
                // obligations were proved where the function is declared.
                self.int(&sig.body, &inner, None)
            }
            _ => None,
        }
    }

    fn bind_arguments(
        &self,
        sig: &FnSig,
        arguments: &[Expr],
        env: &Env,
        evaluated: bool,
    ) -> Option<Env> {
        let mut inner = Env::new();
        for (index, (parameter, ty)) in sig.params.iter().enumerate() {
            let argument = arguments.get(index)?;
            let know = match ty {
                Type::Int(int_ty) => {
                    let val = self.int(argument, env, evaluated.then_some(*int_ty))?;
                    if evaluated && !val.flow.within(sig.pre[index]) {
                        return None;
                    }
                    Know::Int(val)
                }
                _ => Know::Bool(self.boolean(argument, env, evaluated)?),
            };
            inner.insert(
                parameter.clone(),
                Slot {
                    ty: ty.clone(),
                    mutable: false,
                    know,
                    definition: None,
                },
            );
        }
        Some(inner)
    }

    /// The truth of a Boolean expression on `env`; `None` as for [`Lib::int`].
    fn boolean(&self, expr: &Expr, env: &Env, evaluated: bool) -> Option<Tri> {
        match expr {
            Expr::Boolean(value) => Some(Tri::of(*value)),
            Expr::Name(name) => match &env.get(name)?.know {
                Know::Bool(tri) => Some(*tri),
                Know::Int(_) => None,
            },
            Expr::Unary(Unary::Not, inner) => Some(self.boolean(inner, env, evaluated)?.not()),
            Expr::Binary(Binary::And, left, right) => {
                // [E-Bool], [P7]: the right operand is evaluated, and its
                // obligations are proved, where the left one is true.
                let first = self.boolean(left, env, evaluated)?;
                let mut then = env.clone();
                let second = if self.refine(left, true, &mut then) {
                    self.boolean(right, &then, evaluated)?
                } else {
                    Tri::False
                };
                Some(first.and(second))
            }
            Expr::Binary(Binary::Or, left, right) => {
                let first = self.boolean(left, env, evaluated)?;
                let mut otherwise = env.clone();
                let second = if self.refine(left, false, &mut otherwise) {
                    self.boolean(right, &otherwise, evaluated)?
                } else {
                    Tri::True
                };
                Some(first.or(second))
            }
            Expr::Binary(operator, left, right) if operator.level() == 3 => {
                let ty = self
                    .anchor(left, env)
                    .or_else(|| self.anchor(right, env))
                    .unwrap_or(IntType::U32);
                let fit = evaluated.then_some(ty);
                let a = self.int(left, env, fit)?;
                let b = self.int(right, env, fit)?;
                Some(compare(*operator, a.flow, b.flow))
            }
            Expr::Call(function, arguments) => {
                let sig = self.function(function)?;
                let inner = self.bind_arguments(sig, arguments, env, evaluated)?;
                self.boolean(&sig.body, &inner, false)
            }
            _ => None,
        }
    }

    /// Adds to `env` what follows from `expr` having the value `polarity`.
    /// False when it cannot have it.
    fn refine(&self, expr: &Expr, polarity: bool, env: &mut Env) -> bool {
        match expr {
            Expr::Boolean(value) => *value == polarity,
            Expr::Name(name) => {
                let Some(slot) = env.get_mut(name) else {
                    return true;
                };
                let Know::Bool(seen) = slot.know else {
                    return true;
                };
                if seen == Tri::of(!polarity) {
                    return false;
                }
                slot.know = Know::Bool(Tri::of(polarity));
                match slot.definition.clone() {
                    Some(definition) => self.refine(&definition, polarity, env),
                    None => true,
                }
            }
            Expr::Unary(Unary::Not, inner) => self.refine(inner, !polarity, env),
            Expr::Binary(Binary::And, left, right) => {
                if polarity {
                    self.refine(left, true, env) && self.refine(right, true, env)
                } else {
                    self.refine_one_of(left, right, false, env)
                }
            }
            Expr::Binary(Binary::Or, left, right) => {
                if polarity {
                    self.refine_one_of(left, right, true, env)
                } else {
                    self.refine(left, false, env) && self.refine(right, false, env)
                }
            }
            Expr::Binary(operator, left, right) if operator.level() == 3 => {
                self.refine_comparison(*operator, left, right, polarity, env)
            }
            other => self.boolean(other, env, false) != Some(Tri::of(!polarity)),
        }
    }

    /// At least one of the two has the value `wanted`.
    fn refine_one_of(&self, left: &Expr, right: &Expr, wanted: bool, env: &mut Env) -> bool {
        let excluded = Some(Tri::of(!wanted));
        let first = self.boolean(left, env, false) == excluded;
        let second = self.boolean(right, env, false) == excluded;
        match (first, second) {
            (true, true) => false,
            (true, false) => self.refine(right, wanted, env),
            (false, true) => self.refine(left, wanted, env),
            (false, false) => true,
        }
    }

    fn refine_comparison(
        &self,
        operator: Binary,
        left: &Expr,
        right: &Expr,
        polarity: bool,
        env: &mut Env,
    ) -> bool {
        let operator = if polarity {
            operator
        } else {
            opposite(operator)
        };
        let (Some(a), Some(b)) = (self.int(left, env, None), self.int(right, env, None)) else {
            return true;
        };
        let (a, b) = (a.flow, b.flow);
        let up_to = |hi: i128| Range { lo: NEG, hi };
        let from = |lo: i128| Range { lo, hi: POS };
        let (new_a, new_b) = match operator {
            Binary::Less => (a.meet(up_to(below(b.hi))), b.meet(from(above(a.lo)))),
            Binary::LessEqual => (a.meet(up_to(b.hi)), b.meet(from(a.lo))),
            Binary::Greater => (a.meet(from(above(b.lo))), b.meet(up_to(below(a.hi)))),
            Binary::GreaterEqual => (a.meet(from(b.lo)), b.meet(up_to(a.hi))),
            Binary::Equal => (a.meet(b), a.meet(b)),
            Binary::NotEqual => (without(a, b.as_point()), without(b, a.as_point())),
            _ => (a, b),
        };
        if new_a.is_empty() || new_b.is_empty() {
            return false;
        }
        Self::narrow(left, new_a, env);
        Self::narrow(right, new_b, env);
        true
    }

    /// `expr` lies in `range`: narrow the name it is, or the name it is a
    /// literal away from.
    fn narrow(expr: &Expr, range: Range, env: &mut Env) {
        match expr {
            Expr::Name(name) => {
                if let Some(Slot {
                    know: Know::Int(val),
                    ..
                }) = env.get_mut(name)
                {
                    let narrowed = val.flow.meet(range);
                    if !narrowed.is_empty() {
                        val.flow = narrowed;
                    }
                }
            }
            Expr::Binary(Binary::Add, left, right) => match (literal_of(left), literal_of(right)) {
                (None, Some(literal)) => {
                    Self::narrow(left, subtract(range, Range::point(literal)), env);
                }
                (Some(literal), None) => {
                    Self::narrow(right, subtract(range, Range::point(literal)), env);
                }
                _ => {}
            },
            Expr::Binary(Binary::Subtract, left, right) => {
                if let (None, Some(literal)) = (literal_of(left), literal_of(right)) {
                    Self::narrow(left, add(range, Range::point(literal)), env);
                }
            }
            _ => {}
        }
    }
}

/// One history of a body that is still running.
#[derive(Clone, Debug)]
struct Path {
    /// `(site, alternative)`, as indices into the sites of the body.
    atoms: Vec<(usize, usize)>,
    env: Env,
}

struct SiteInfo {
    name: String,
    alternatives: Vec<String>,
}

#[derive(Clone)]
struct ParamInfo {
    name: String,
    ty: Type,
    invariant: Option<Range>,
}

#[derive(Clone)]
struct LeaveRecord {
    payload: Vec<Know>,
    assigned: BTreeMap<String, Know>,
}

#[derive(Clone)]
struct LoopInfo {
    name: String,
    params: Vec<ParamInfo>,
    /// The first parameter counts, up to `bound` or down to zero, and every
    /// `↑` moves it. That is what ends the loop.
    counter: String,
    bound: i128,
    up: bool,
    /// The alternatives that a `□` may use, with the types of their payloads.
    planned: Vec<(String, Vec<Type>)>,
    leaves: Vec<Vec<LeaveRecord>>,
    /// The outer names that the body may assign.
    assignable: BTreeSet<String>,
}

struct Scope {
    sites: Vec<SiteInfo>,
    live: Vec<Path>,
    statements: Vec<Statement>,
    looping: Option<LoopInfo>,
    /// Atoms of the bodies around that hold on every history that runs this
    /// loop ([H4]).
    outer_atoms: Vec<(String, String)>,
}

#[derive(Clone, Default)]
struct ExitRecord {
    used: bool,
    fields: Vec<Option<Range>>,
    params: Vec<Option<Range>>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Step {
    Bind,
    Assign,
    Oblige,
    Test,
    Decide,
    Loop,
    Terminate,
}

struct Generator<'r> {
    rng: &'r mut Rng,
    functions: Vec<FnSig>,
    callables: Vec<Sig>,
    palette: Vec<IntType>,
    // The control being written.
    scopes: Vec<Scope>,
    fresh: usize,
    loops: usize,
    contract: Vec<(String, Vec<(String, Type)>)>,
    parameters: Vec<String>,
    exits: Vec<ExitRecord>,
    effects: BTreeSet<String>,
}

fn conjunction(parts: Vec<Expr>) -> Option<Expr> {
    parts
        .into_iter()
        .reduce(|left, right| bin(Binary::And, left, right))
}

fn and_selector(left: &Selector, right: Selector) -> Selector {
    match left {
        Selector::Top => right,
        _ => Selector::And(Box::new(left.clone()), Box::new(right)),
    }
}

fn holds(scope: &Scope, selector: &Selector, path: &Path) -> bool {
    match selector {
        Selector::Top => true,
        Selector::Atom(site, alternative) => {
            match scope.sites.iter().position(|seen| &seen.name == site) {
                Some(index) => scope.sites[index]
                    .alternatives
                    .iter()
                    .position(|seen| seen == alternative)
                    .is_some_and(|which| path.atoms.contains(&(index, which))),
                None => scope
                    .outer_atoms
                    .iter()
                    .any(|(seen, which)| seen == site && which == alternative),
            }
        }
        Selector::Not(inner) => !holds(scope, inner, path),
        Selector::And(left, right) => holds(scope, left, path) && holds(scope, right, path),
        Selector::Or(left, right) => holds(scope, left, path) || holds(scope, right, path),
    }
}

/// What holds on every one of `paths`.
fn merge(paths: &[&Path]) -> Env {
    let Some((first, rest)) = paths.split_first() else {
        return Env::new();
    };
    let mut env = first.env.clone();
    for other in rest {
        env.retain(|name, slot| match other.env.get(name) {
            Some(theirs) if theirs.ty == slot.ty && theirs.mutable == slot.mutable => {
                slot.know = slot.know.hull(&theirs.know);
                let same = match (&slot.definition, &theirs.definition) {
                    (Some(ours), Some(theirs)) => ours.to_string() == theirs.to_string(),
                    _ => false,
                };
                if !same {
                    slot.definition = None;
                }
                true
            }
            _ => false,
        });
    }
    env
}

fn parameter(name: &str, ty: &Type) -> Parameter {
    Parameter {
        name: name.to_string(),
        ty: ty.clone(),
        origins: Vec::new(),
    }
}

impl Generator<'_> {
    fn lib(&self) -> Lib<'_> {
        Lib {
            functions: &self.functions,
        }
    }

    fn scope(&self) -> &Scope {
        &self.scopes[self.scopes.len() - 1]
    }

    fn scope_mut(&mut self) -> &mut Scope {
        let last = self.scopes.len() - 1;
        &mut self.scopes[last]
    }

    fn fresh(&mut self, prefix: &str) -> String {
        self.fresh += 1;
        format!("{prefix}{}", self.fresh)
    }

    fn push(&mut self, selector: &Selector, command: Command) {
        self.scope_mut()
            .statements
            .push(stmt(selector.clone(), command));
    }

    /// A type for a name, a parameter or a field. Most integers of one
    /// program have one of a few types, so that expressions find names to
    /// combine: both operands of an operator have one type ([C1]).
    fn random_type(&mut self) -> Type {
        if self.rng.chance(1, 6) {
            Type::Bool
        } else if self.rng.chance(4, 5) {
            Type::Int(*self.rng.pick(&self.palette))
        } else {
            Type::Int(*self.rng.pick(&IntType::ALL))
        }
    }

    // Literals and intervals.

    fn literal(&mut self, ty: IntType) -> i128 {
        let fit = fit_range(ty);
        match self.rng.below(24) {
            0 => fit.lo,
            1 => fit.hi,
            2 => fit.hi - 1,
            _ if ty.is_signed() => self.rng.range(-9, 9),
            _ => self.rng.range(0, 9),
        }
    }

    /// A value of `range`, which has both ends, with its ends preferred.
    fn literal_in(&mut self, range: Range) -> i128 {
        let span = range.hi - range.lo;
        match self.rng.below(6) {
            0 => range.lo,
            1 => range.hi,
            2 => (range.lo + 1).min(range.hi),
            3 => (range.hi - 1).max(range.lo),
            _ => range.lo + self.rng.range(0, span.min(12)),
        }
    }

    /// An interval of values of `ty` for a precondition, an invariant or a
    /// condition. Its lower end is a literal of the type on every target.
    fn subrange(&mut self, ty: IntType) -> Range {
        let value = value_range(ty);
        let fit = fit_range(ty);
        match self.rng.below(6) {
            0 => Range::new(0, self.rng.range(0, 9)),
            1 => {
                let lo = self.rng.range(fit.lo.max(-20), 20);
                Range::new(lo, (lo + self.rng.range(0, 30)).min(fit.hi))
            }
            2 => Range::new(fit.hi - self.rng.range(0, 9), fit.hi),
            3 => Range::new(fit.lo, fit.lo + self.rng.range(0, 9)),
            4 => Range::new(value.lo, self.rng.range(0, 100)),
            _ => Range::new(self.rng.range(fit.lo.max(-5), 50), value.hi),
        }
    }

    /// The conjuncts that say `subject` lies in `range`, where that is more
    /// than its type says.
    fn bounds(&mut self, subject: &Expr, range: Range, ty: IntType) -> Vec<Expr> {
        let value = value_range(ty);
        let mut out = Vec::new();
        if range.lo > value.lo {
            let literal = int(range.lo);
            out.push(match self.rng.below(4) {
                0 => bin(Binary::LessEqual, literal, subject.clone()),
                1 => Expr::Unary(
                    Unary::Not,
                    Box::new(bin(Binary::Less, subject.clone(), literal)),
                ),
                _ => bin(Binary::GreaterEqual, subject.clone(), literal),
            });
        }
        if range.hi < value.hi {
            let literal = int(range.hi);
            out.push(match self.rng.below(4) {
                0 => bin(Binary::GreaterEqual, literal, subject.clone()),
                1 => bin(Binary::Less, subject.clone(), int(range.hi + 1)),
                _ => bin(Binary::LessEqual, subject.clone(), literal),
            });
        }
        if out.len() == 2 && self.rng.chance(1, 2) {
            out.swap(0, 1);
        }
        out
    }

    // Expressions.

    fn names_of(env: &Env, ty: &Type) -> Vec<String> {
        env.iter()
            .filter(|(_, slot)| &slot.ty == ty)
            .map(|(name, _)| name.clone())
            .collect()
    }

    fn atom(&mut self, env: &Env, ty: IntType) -> Expr {
        let names = Self::names_of(env, &Type::Int(ty));
        if !names.is_empty() && self.rng.chance(3, 4) {
            name(self.rng.pick(&names))
        } else {
            int(self.literal(ty))
        }
    }

    /// An integer expression of `ty` whose obligations hold on `env`.
    fn gen_int(&mut self, env: &Env, ty: IntType, depth: u8) -> (Expr, Val) {
        for _ in 0..6 {
            let proposal = self.propose_int(env, ty, depth);
            if let Some(val) = self.lib().int(&proposal, env, Some(ty)) {
                return (proposal, val);
            }
        }
        for _ in 0..4 {
            let proposal = self.atom(env, ty);
            if let Some(val) = self.lib().int(&proposal, env, Some(ty)) {
                return (proposal, val);
            }
        }
        (int(0), Val::constant(0))
    }

    /// An operand for an operator: an expression, brought into a small
    /// interval by `mod` or `÷` when it is wide.
    fn operand(&mut self, env: &Env, ty: IntType, depth: u8) -> Expr {
        let (expr, val) = self.gen_int(env, ty, depth - 1);
        let wide = val.flow.width().is_none_or(|width| width > 64);
        if wide && self.rng.chance(2, 3) {
            self.tame(expr, ty)
        } else {
            expr
        }
    }

    fn tame(&mut self, expr: Expr, ty: IntType) -> Expr {
        let fit = fit_range(ty);
        if self.rng.chance(3, 4) {
            bin(Binary::Remainder, expr, int(self.rng.range(2, 9)))
        } else {
            let divisor = *self.rng.pick(&[2, 3, 16, 100, 1000]);
            bin(Binary::Divide, expr, int(divisor.min(fit.hi)))
        }
    }

    fn propose_int(&mut self, env: &Env, ty: IntType, depth: u8) -> Expr {
        if depth == 0 || self.rng.chance(1, 4) {
            return self.atom(env, ty);
        }
        let signed = ty.is_signed();
        match self.rng.below(12) {
            0 | 1 => {
                let left = self.operand(env, ty, depth);
                let right = self.operand(env, ty, depth);
                bin(Binary::Add, left, right)
            }
            2 | 3 => {
                let left = self.operand(env, ty, depth);
                let right = self.operand(env, ty, depth);
                bin(Binary::Subtract, left, right)
            }
            4 => {
                // [A9]: a product of two terms is bounded through the
                // declared intervals of its operands, so both are remainders.
                let left = self.gen_int(env, ty, depth - 1).0;
                let right = self.gen_int(env, ty, depth - 1).0;
                bin(
                    Binary::Multiply,
                    bin(Binary::Remainder, left, int(self.rng.range(2, 9))),
                    bin(Binary::Remainder, right, int(self.rng.range(2, 9))),
                )
            }
            5 => {
                let factor = if signed {
                    self.rng.range(-3, 5)
                } else {
                    self.rng.range(0, 5)
                };
                let other = self.operand(env, ty, depth);
                if self.rng.chance(1, 2) {
                    bin(Binary::Multiply, int(factor), other)
                } else {
                    bin(Binary::Multiply, other, int(factor))
                }
            }
            6 | 7 => {
                let operator = if self.rng.chance(1, 2) {
                    Binary::Divide
                } else {
                    Binary::Remainder
                };
                let mut divisor = self.rng.range(1, 9);
                if signed && self.rng.chance(1, 4) {
                    divisor = -divisor;
                }
                let left = self.gen_int(env, ty, depth - 1).0;
                bin(operator, left, int(divisor))
            }
            8 => {
                // [A8]: a divisor that is a term has to be known nonzero.
                let operator = if self.rng.chance(1, 2) {
                    Binary::Divide
                } else {
                    Binary::Remainder
                };
                let left = self.gen_int(env, ty, depth - 1).0;
                let right = self.gen_int(env, ty, depth - 1).0;
                bin(operator, left, right)
            }
            9 => self
                .call(env, &Type::Int(ty), depth)
                .unwrap_or_else(|| self.atom(env, ty)),
            10 if signed => {
                let inner = self.operand(env, ty, depth);
                Expr::Unary(Unary::Negate, Box::new(inner))
            }
            _ => self.operand(env, ty, depth),
        }
    }

    /// A call of a function with result `result`, with arguments that
    /// satisfy its precondition.
    fn call(&mut self, env: &Env, result: &Type, depth: u8) -> Option<Expr> {
        let candidates: Vec<usize> = (0..self.functions.len())
            .filter(|&index| &self.functions[index].result == result)
            .collect();
        if candidates.is_empty() {
            return None;
        }
        let index = *self.rng.pick(&candidates);
        let params = self.functions[index].params.clone();
        let pre = self.functions[index].pre.clone();
        let mut arguments = Vec::new();
        for (position, (_, ty)) in params.iter().enumerate() {
            arguments.push(match ty {
                Type::Int(int_ty) => self.gen_int_in(env, *int_ty, pre[position])?.0,
                _ => self.gen_bool(env, depth.saturating_sub(1)).0,
            });
        }
        Some(Expr::Call(self.functions[index].name.clone(), arguments))
    }

    /// An integer expression of `ty` that is known to lie in `target`.
    fn gen_int_in(&mut self, env: &Env, ty: IntType, target: Range) -> Option<(Expr, Val)> {
        let target = target.meet(fit_range(ty));
        if target.is_empty() {
            return None;
        }
        for _ in 0..3 {
            let (expr, val) = self.gen_int(env, ty, 2);
            if val.flow.within(target) {
                return Some((expr, val));
            }
        }
        let names = Self::names_of(env, &Type::Int(ty));
        let flow_of = |name: &String| match &env[name].know {
            Know::Int(val) => val.flow,
            Know::Bool(_) => Range::ALL,
        };
        let inside: Vec<&String> = names
            .iter()
            .filter(|name| flow_of(name).within(target))
            .collect();
        if !inside.is_empty() && self.rng.chance(1, 2) {
            let chosen = (*self.rng.pick(&inside)).clone();
            let val = self.lib().int(&name(&chosen), env, Some(ty))?;
            return Some((name(&chosen), val));
        }
        let width = target.width()?;
        if width >= 2 && !names.is_empty() && self.rng.chance(2, 3) {
            let chosen = self.rng.pick(&names).clone();
            if flow_of(&chosen).lo >= 0 {
                let modulus = width.min(2 + self.rng.range(0, 14));
                let mut expr = bin(Binary::Remainder, name(&chosen), int(modulus));
                if target.lo > 0 {
                    expr = bin(Binary::Add, expr, int(target.lo));
                } else if target.lo < 0 {
                    expr = bin(Binary::Subtract, expr, int(-target.lo));
                }
                if let Some(val) = self.lib().int(&expr, env, Some(ty))
                    && val.flow.within(target)
                {
                    return Some((expr, val));
                }
            }
        }
        let literal = self.literal_in(target);
        Some((int(literal), Val::constant(literal)))
    }

    /// A Boolean expression whose obligations hold on `env`.
    fn gen_bool(&mut self, env: &Env, depth: u8) -> (Expr, Tri) {
        for _ in 0..6 {
            let proposal = self.propose_bool(env, depth);
            if let Some(tri) = self.lib().boolean(&proposal, env, true) {
                return (proposal, tri);
            }
        }
        let value = self.rng.chance(1, 2);
        (Expr::Boolean(value), Tri::of(value))
    }

    fn propose_bool(&mut self, env: &Env, depth: u8) -> Expr {
        let bools = Self::names_of(env, &Type::Bool);
        let choice = self.rng.below(if depth == 0 { 7 } else { 12 });
        match choice {
            0 if !bools.is_empty() => name(self.rng.pick(&bools)),
            1 if self.rng.chance(1, 4) => Expr::Boolean(self.rng.chance(1, 2)),
            0..=6 => self.comparison(env, depth),
            7 => {
                let inner = self.propose_bool(env, depth - 1);
                Expr::Unary(Unary::Not, Box::new(inner))
            }
            8 | 9 => {
                // The right operand may rely on the left one ([E-Bool]).
                let conjunction = choice == 8;
                let left = self.gen_bool(env, depth - 1).0;
                let mut after = env.clone();
                let right = if self.lib().refine(&left, conjunction, &mut after) {
                    self.gen_bool(&after, depth - 1).0
                } else {
                    self.gen_bool(env, depth - 1).0
                };
                let operator = if conjunction { Binary::And } else { Binary::Or };
                bin(operator, left, right)
            }
            _ => self
                .call(env, &Type::Bool, depth)
                .unwrap_or_else(|| self.comparison(env, depth)),
        }
    }

    fn comparison(&mut self, env: &Env, depth: u8) -> Expr {
        let typed: Vec<IntType> = env
            .values()
            .filter_map(|slot| match &slot.ty {
                Type::Int(ty) => Some(*ty),
                _ => None,
            })
            .collect();
        let ty = if !typed.is_empty() && self.rng.chance(5, 6) {
            *self.rng.pick(&typed)
        } else {
            *self.rng.pick(&IntType::ALL)
        };
        let depth = depth.min(2);
        let (mut left, left_val) = self.gen_int(env, ty, depth);
        let near = left_val.flow.meet(fit_range(ty));
        let mut right = if self.rng.chance(1, 2) && !near.is_empty() {
            // A literal at or beside what the left side can be.
            let fit = fit_range(ty);
            let literal = self.literal_in(near) + self.rng.range(-1, 1);
            int(literal.clamp(fit.lo, fit.hi))
        } else {
            self.gen_int(env, ty, depth).0
        };
        let anchored =
            self.lib().anchor(&left, env).is_some() || self.lib().anchor(&right, env).is_some();
        if !anchored && ty != IntType::U32 {
            // Literals alone are `u32` ([C1]).
            let empty = Env::new();
            left = self.gen_int(&empty, IntType::U32, 1).0;
            right = self.gen_int(&empty, IntType::U32, 1).0;
        }
        if self.rng.chance(1, 4) {
            std::mem::swap(&mut left, &mut right);
        }
        bin(*self.rng.pick(&COMPARISONS), left, right)
    }

    fn gen_expr(&mut self, env: &Env, ty: &Type, depth: u8) -> (Expr, Know) {
        match ty {
            Type::Int(int_ty) => {
                let (expr, val) = self.gen_int(env, *int_ty, depth);
                (expr, Know::Int(val))
            }
            _ => {
                let (expr, tri) = self.gen_bool(env, depth.min(2));
                (expr, Know::Bool(tri))
            }
        }
    }

    /// A formula that the intervals of `env` make true.
    fn fact(&mut self, env: &Env) -> Expr {
        for _ in 0..8 {
            let proposal = self.propose_fact(env, 2);
            if self.lib().boolean(&proposal, env, false) == Some(Tri::True) {
                return proposal;
            }
        }
        Expr::Boolean(true)
    }

    fn propose_fact(&mut self, env: &Env, depth: u8) -> Expr {
        let ints: Vec<(String, IntType, Range)> = env
            .iter()
            .filter_map(|(name, slot)| match (&slot.ty, &slot.know) {
                (Type::Int(ty), Know::Int(val)) => Some((name.clone(), *ty, val.flow)),
                _ => None,
            })
            .collect();
        match self.rng.below(if depth == 0 { 6 } else { 9 }) {
            0..=2 if !ints.is_empty() => {
                // An interval of a name, at its ends or beyond them.
                let (subject, ty, flow) = self.rng.pick(&ints).clone();
                let slack = if self.rng.chance(1, 3) {
                    self.rng.range(0, 3)
                } else {
                    0
                };
                let wider = Range::new(
                    if flow.has_lo() { flow.lo - slack } else { NEG },
                    if flow.has_hi() { flow.hi + slack } else { POS },
                );
                // The type says nothing here, so every end is written.
                let mut parts = Vec::new();
                let subject = name(&subject);
                if wider.has_lo() && self.rng.chance(2, 3) {
                    parts.push(bin(Binary::GreaterEqual, subject.clone(), int(wider.lo)));
                }
                if wider.has_hi() && (parts.is_empty() || self.rng.chance(2, 3)) {
                    parts.push(bin(Binary::LessEqual, subject.clone(), int(wider.hi)));
                }
                let _ = ty;
                conjunction(parts).unwrap_or(Expr::Boolean(true))
            }
            0..=4 => {
                let ty = if ints.is_empty() {
                    IntType::U32
                } else {
                    self.rng.pick(&ints).1
                };
                let (left, a) = self.gen_int(env, ty, 2);
                let (right, b) = self.gen_int(env, ty, 2);
                let anchored = self.lib().anchor(&left, env).is_some()
                    || self.lib().anchor(&right, env).is_some();
                if !anchored && ty != IntType::U32 {
                    return Expr::Boolean(true);
                }
                if a.flow.hi <= b.flow.lo {
                    bin(Binary::LessEqual, left, right)
                } else if b.flow.hi <= a.flow.lo {
                    bin(Binary::GreaterEqual, left, right)
                } else {
                    bin(
                        Binary::Or,
                        bin(Binary::LessEqual, left.clone(), right.clone()),
                        bin(Binary::Greater, left, right),
                    )
                }
            }
            5 => {
                let (expr, tri) = self.gen_bool(env, 1);
                match tri {
                    Tri::True => expr,
                    Tri::False => Expr::Unary(Unary::Not, Box::new(expr)),
                    Tri::Unknown => bin(
                        Binary::Or,
                        expr.clone(),
                        Expr::Unary(Unary::Not, Box::new(expr)),
                    ),
                }
            }
            6 | 7 => {
                let left = self.propose_fact(env, depth - 1);
                let right = self.propose_fact(env, depth - 1);
                bin(Binary::And, left, right)
            }
            _ => {
                let held = self.propose_fact(env, depth - 1);
                let other = self.gen_bool(env, 1).0;
                if self.rng.chance(1, 2) {
                    bin(Binary::Or, held, other)
                } else {
                    bin(Binary::Or, other, held)
                }
            }
        }
    }

    // Histories.

    fn running(&self, selector: &Selector) -> Vec<usize> {
        let scope = self.scope();
        (0..scope.live.len())
            .filter(|&index| holds(scope, selector, &scope.live[index]))
            .collect()
    }

    fn running_env(&self, running: &[usize]) -> Env {
        let scope = self.scope();
        let paths: Vec<&Path> = running.iter().map(|&index| &scope.live[index]).collect();
        merge(&paths)
    }

    /// The histories `running` are replaced by `children`.
    fn replace(&mut self, running: &[usize], children: Vec<Path>) {
        let scope = self.scope_mut();
        let mut kept = Vec::new();
        for (index, path) in std::mem::take(&mut scope.live).into_iter().enumerate() {
            if !running.contains(&index) {
                kept.push(path);
            }
        }
        kept.extend(children);
        scope.live = kept;
    }

    fn selector_of_some(&mut self) -> Selector {
        let count = self.scope().live.len();
        let which = self.rng.index(count);
        let atoms = self.scope().live[which].atoms.clone();
        if atoms.is_empty() {
            return Selector::Top;
        }
        let take = if atoms.len() > 1 && self.rng.chance(1, 3) {
            2
        } else {
            1
        };
        let first = self.rng.index(atoms.len());
        let mut out: Option<Selector> = None;
        for offset in 0..take {
            let (site, alternative) = atoms[(first + offset) % atoms.len()];
            let info = &self.scope().sites[site];
            let site_name = info.name.clone();
            let alternatives = info.alternatives.clone();
            // With two alternatives, `¬d.b` is `d.a` on every history that
            // reached `d`, and true on those that did not.
            let atom = if alternatives.len() == 2 && self.rng.chance(1, 6) {
                Selector::Not(Box::new(Selector::Atom(
                    site_name,
                    alternatives[1 - alternative].clone(),
                )))
            } else {
                Selector::Atom(site_name, alternatives[alternative].clone())
            };
            out = Some(match out {
                Some(seen) => Selector::And(Box::new(seen), Box::new(atom)),
                None => atom,
            });
        }
        out.unwrap_or(Selector::Top)
    }

    fn pick_selector(&mut self) -> (Selector, Vec<usize>) {
        let count = self.scope().live.len();
        if count == 0 {
            return (Selector::Top, Vec::new());
        }
        let mut selector = if self.scope().sites.is_empty() || self.rng.chance(1, 3) {
            Selector::Top
        } else {
            let first = self.selector_of_some();
            if self.rng.chance(1, 5) {
                let second = self.selector_of_some();
                match (&first, &second) {
                    (Selector::Top, _) | (_, Selector::Top) => Selector::Top,
                    _ => Selector::Or(Box::new(first), Box::new(second)),
                }
            } else {
                first
            }
        };
        if !self.scope().outer_atoms.is_empty() && self.rng.chance(1, 8) {
            let which = self.rng.index(self.scope().outer_atoms.len());
            let (site, alternative) = self.scope().outer_atoms[which].clone();
            selector = and_selector(&selector, Selector::Atom(site, alternative));
        }
        let running = self.running(&selector);
        (selector, running)
    }

    // Statements.

    fn fill(&mut self, budget: usize) {
        let mut last: Option<Selector> = None;
        for _ in 0..budget {
            if self.scope().live.is_empty() {
                break;
            }
            let (selector, running) = match &last {
                Some(selector) if self.rng.chance(1, 2) => {
                    (selector.clone(), self.running(selector))
                }
                _ => self.pick_selector(),
            };
            if running.is_empty() {
                last = None;
                continue;
            }
            last = Some(selector.clone());
            self.step(&selector, &running);
        }
        // [K7]: no history is left running.
        let mut rounds = 0;
        while !self.scope().live.is_empty() {
            rounds += 1;
            let few = self.scope().live.len() == 1;
            let (selector, running) = if few || rounds > 12 || self.rng.chance(1, 3) {
                (Selector::Top, self.running(&Selector::Top))
            } else {
                self.pick_selector()
            };
            if !running.is_empty() {
                self.terminate(&selector, &running);
            }
        }
    }

    fn step(&mut self, selector: &Selector, running: &[usize]) {
        let live = self.scope().live.len();
        let room = live < MAX_HISTORIES || running.len() <= 2;
        let mut choices = vec![(5u64, Step::Bind), (3, Step::Assign), (2, Step::Oblige)];
        if room {
            choices.push((4, Step::Test));
            if !self.callables.is_empty() {
                choices.push((4, Step::Decide));
            }
            if self.scopes.len() < MAX_BODIES && self.loops < MAX_LOOPS {
                choices.push((2, Step::Loop));
            }
        }
        if running.len() < live {
            choices.push((2, Step::Terminate));
        }
        let total: u64 = choices.iter().map(|(weight, _)| weight).sum();
        let mut drawn = self.rng.below(total);
        let mut chosen = Step::Bind;
        for (weight, step) in choices {
            if drawn < weight {
                chosen = step;
                break;
            }
            drawn -= weight;
        }
        let done = match chosen {
            Step::Bind => false,
            Step::Assign => self.assign(selector, running),
            Step::Oblige => {
                let env = self.running_env(running);
                let formula = self.fact(&env);
                self.push(selector, Command::Oblige(formula));
                true
            }
            Step::Test => {
                let env = self.running_env(running);
                let condition = self.gen_bool(&env, 2).0;
                self.branch(selector, running, condition);
                true
            }
            Step::Decide => self.decide(selector, running),
            Step::Loop => {
                self.make_loop(selector, running);
                true
            }
            Step::Terminate => {
                self.terminate(selector, running);
                true
            }
        };
        if !done {
            self.bind(selector, running);
        }
    }

    fn bind(&mut self, selector: &Selector, running: &[usize]) {
        let env = self.running_env(running);
        let ty = self.random_type();
        let bound = self.fresh("v");
        let mutable = self.rng.chance(1, 3);
        let (value, know) = self.gen_expr(&env, &ty, 3);
        let mut definition = None;
        let (know, typed) = match (&ty, know) {
            (Type::Int(int_ty), Know::Int(val)) => {
                // A bound name is a value term: it has the range of its type.
                let mut held = Val::value(*int_ty, val.flow);
                if !mutable {
                    held.constant = val.constant;
                }
                let anchored = *int_ty == IntType::U32 || self.lib().anchor(&value, &env).is_some();
                (Know::Int(held), !anchored || self.rng.chance(1, 2))
            }
            (_, know) => {
                if !mutable && Self::unchanging(&value, &env) {
                    definition = Some(value.clone());
                }
                (know, self.rng.chance(1, 2))
            }
        };
        self.push(
            selector,
            Command::Bind {
                mutable,
                name: bound.clone(),
                ty: typed.then(|| ty.clone()),
                value: value.clone(),
            },
        );
        let slot = Slot {
            ty: ty.clone(),
            mutable,
            know,
            definition,
        };
        for &index in running {
            self.scope_mut().live[index]
                .env
                .insert(bound.clone(), slot.clone());
        }
        // [N4]: the bind is a fact, and the one thing here that an interval
        // does not say.
        if matches!(ty, Type::Int(_)) && self.rng.chance(1, 6) {
            self.push(
                selector,
                Command::Oblige(bin(Binary::Equal, name(&bound), value)),
            );
        }
    }

    /// Whether every name in `expr` is one that is never assigned.
    fn unchanging(expr: &Expr, env: &Env) -> bool {
        match expr {
            Expr::Name(name) => env.get(name).is_some_and(|slot| !slot.mutable),
            Expr::Unary(_, inner) => Self::unchanging(inner, env),
            Expr::Binary(_, left, right) => {
                Self::unchanging(left, env) && Self::unchanging(right, env)
            }
            Expr::Call(_, arguments) => arguments
                .iter()
                .all(|argument| Self::unchanging(argument, env)),
            _ => true,
        }
    }

    fn assign(&mut self, selector: &Selector, running: &[usize]) -> bool {
        let env = self.running_env(running);
        let candidates: Vec<String> = env
            .iter()
            .filter(|(_, slot)| slot.mutable)
            .map(|(name, _)| name.clone())
            .collect();
        if candidates.is_empty() {
            return false;
        }
        let target = self.rng.pick(&candidates).clone();
        let ty = env[&target].ty.clone();
        let (value, know) = self.gen_expr(&env, &ty, 3);
        let know = match (&ty, know) {
            (Type::Int(int_ty), Know::Int(val)) => Know::Int(Val::value(*int_ty, val.flow)),
            (_, know) => know,
        };
        self.push(
            selector,
            Command::Assign {
                name: target.clone(),
                value,
            },
        );
        for &index in running {
            if let Some(slot) = self.scope_mut().live[index].env.get_mut(&target) {
                slot.know = know.clone();
                slot.definition = None;
            }
        }
        true
    }

    /// A test on `condition`: each running history splits in two, and an
    /// arm that no history can take is `⊥` or left out.
    fn branch(&mut self, selector: &Selector, running: &[usize], condition: Expr) {
        let site = self.fresh("t");
        let site_index = self.scope().sites.len();
        let mut children = Vec::new();
        let mut reached = [false, false];
        for &index in running {
            let path = self.scope().live[index].clone();
            for (which, polarity) in [(0, true), (1, false)] {
                let mut env = path.env.clone();
                if self.lib().refine(&condition, polarity, &mut env) {
                    let mut atoms = path.atoms.clone();
                    atoms.push((site_index, which));
                    children.push(Path { atoms, env });
                    reached[which] = true;
                }
            }
        }
        let alternatives = vec!["true".to_string(), "false".to_string()];
        self.scope_mut().sites.push(SiteInfo {
            name: site.clone(),
            alternatives: alternatives.clone(),
        });
        self.push(
            selector,
            Command::Test {
                site: site.clone(),
                condition,
            },
        );
        self.replace(running, children);
        for (which, alternative) in alternatives.into_iter().enumerate() {
            if !reached[which] && self.rng.chance(3, 5) {
                let arm = and_selector(selector, Selector::Atom(site.clone(), alternative));
                self.push(&arm, Command::Impossible);
            }
        }
    }

    /// The histories on which a completed operation continues: one for each
    /// running history and each alternative that its condition allows there.
    fn complete(
        &mut self,
        selector: &Selector,
        running: &[usize],
        site: &str,
        callee: &Sig,
        arguments: &[Expr],
        arms: &[Arm],
    ) {
        let site_index = self.scope().sites.len();
        let mut children = Vec::new();
        let mut reached = vec![false; callee.alts.len()];
        for &index in running {
            let path = self.scope().live[index].clone();
            'alternative: for (which, alternative) in callee.alts.iter().enumerate() {
                let mut env = path.env.clone();
                // [N4]: `d.a ⇒ φₐ`, over the arguments and the payload names.
                for (position, bound) in alternative.params.iter().enumerate() {
                    let Some(bound) = bound else { continue };
                    let Some(val) = self.lib().int(&arguments[position], &env, None) else {
                        continue;
                    };
                    let narrowed = val.flow.meet(*bound);
                    if narrowed.is_empty() {
                        continue 'alternative;
                    }
                    Lib::narrow(&arguments[position], narrowed, &mut env);
                }
                for (field, bound) in alternative.fields.iter().zip(&arms[which].names) {
                    let know = match &field.ty {
                        Type::Int(int_ty) => {
                            let mut range = value_range(*int_ty);
                            let lib = self.lib();
                            let argument = |position: usize| {
                                lib.int(&arguments[position], &env, None)
                                    .map_or(Range::ALL, |val| val.flow)
                            };
                            match field.lo {
                                End::Open => {}
                                End::Literal(literal) => range.lo = range.lo.max(literal),
                                End::Parameter(position, offset) => {
                                    let from = add(argument(position), Range::point(offset));
                                    range.lo = range.lo.max(from.lo);
                                }
                            }
                            match field.hi {
                                End::Open => {}
                                End::Literal(literal) => range.hi = range.hi.min(literal),
                                End::Parameter(position, offset) => {
                                    let to = add(argument(position), Range::point(offset));
                                    range.hi = range.hi.min(to.hi);
                                }
                            }
                            if range.is_empty() {
                                continue 'alternative;
                            }
                            Know::Int(Val::value(*int_ty, range))
                        }
                        other => Know::top(other),
                    };
                    env.insert(
                        bound.clone(),
                        Slot {
                            ty: field.ty.clone(),
                            mutable: false,
                            know,
                            definition: None,
                        },
                    );
                }
                let mut atoms = path.atoms.clone();
                atoms.push((site_index, which));
                children.push(Path { atoms, env });
                reached[which] = true;
            }
        }
        self.scope_mut().sites.push(SiteInfo {
            name: site.to_string(),
            alternatives: callee.alts.iter().map(|alt| alt.name.clone()).collect(),
        });
        self.replace(running, children);
        for (which, alternative) in callee.alts.iter().enumerate() {
            if !reached[which] && self.rng.chance(3, 5) {
                let arm = and_selector(
                    selector,
                    Selector::Atom(site.to_string(), alternative.name.clone()),
                );
                self.push(&arm, Command::Impossible);
            }
        }
    }

    fn decide(&mut self, selector: &Selector, running: &[usize]) -> bool {
        let env = self.running_env(running);
        let callee = self.rng.pick(&self.callables).clone();
        let mut arguments: Vec<Expr> = Vec::new();
        for (position, (_, ty)) in callee.params.iter().enumerate() {
            let argument = match ty {
                Type::Int(int_ty) => {
                    let mut target = callee.pre[position];
                    match callee.order {
                        Some((small, large)) if position == small => {
                            target = target.meet(Range {
                                lo: NEG,
                                hi: callee.pre[large].hi,
                            });
                        }
                        Some((small, large)) if position == large => {
                            let Some(first) = self.lib().int(&arguments[small], &env, None) else {
                                return false;
                            };
                            target = target.meet(Range {
                                lo: first.flow.hi,
                                hi: POS,
                            });
                        }
                        _ => {}
                    }
                    match self.gen_int_in(&env, *int_ty, target) {
                        Some((expr, _)) => expr,
                        None => return false,
                    }
                }
                _ => self.gen_bool(&env, 1).0,
            };
            arguments.push(argument);
        }
        let site = self.fresh("d");
        let arms: Vec<Arm> = callee
            .alts
            .iter()
            .map(|alternative| Arm {
                alternative: alternative.name.clone(),
                names: alternative.fields.iter().map(|_| self.fresh("v")).collect(),
            })
            .collect();
        self.effects.extend(callee.uses.iter().cloned());
        self.push(
            selector,
            Command::Decide {
                site: site.clone(),
                mode: CallMode::Sync,
                operation: callee.name.clone(),
                arguments: arguments.clone(),
                arms: arms.clone(),
            },
        );
        self.complete(selector, running, &site, &callee, &arguments, &arms);
        true
    }

    fn make_loop(&mut self, selector: &Selector, running: &[usize]) {
        let env = self.running_env(running);
        self.loops += 1;
        let site = self.fresh("s");
        let loop_name = self.fresh("l");
        let counter = self.fresh("i");
        let counter_ty = *self.rng.pick(&IntType::ALL);
        let bound = self.rng.range(1, 4);
        let up = self.rng.chance(3, 4);
        let counter_invariant = self.rng.chance(1, 2).then(|| Range::new(0, bound));
        let mut parameters = vec![LoopParameter {
            mutable: false,
            name: counter.clone(),
            ty: Type::Int(counter_ty),
            initial: int(if up { 0 } else { bound }),
        }];
        let mut params = vec![ParamInfo {
            name: counter.clone(),
            ty: Type::Int(counter_ty),
            invariant: counter_invariant,
        }];
        for _ in 0..self.rng.below(3) {
            let ty = self.random_type();
            let mutable = self.rng.chance(1, 4);
            let (initial, invariant) = match &ty {
                Type::Int(int_ty) => {
                    let invariant = self.rng.chance(1, 2).then(|| self.subrange(*int_ty));
                    let initial = match invariant {
                        Some(range) => match self.gen_int_in(&env, *int_ty, range) {
                            Some((expr, _)) => expr,
                            None => continue,
                        },
                        None => self.gen_int(&env, *int_ty, 2).0,
                    };
                    (initial, invariant)
                }
                _ => (self.gen_bool(&env, 1).0, None),
            };
            let parameter = self.fresh("x");
            parameters.push(LoopParameter {
                mutable,
                name: parameter.clone(),
                ty: ty.clone(),
                initial,
            });
            params.push(ParamInfo {
                name: parameter,
                ty,
                invariant,
            });
        }
        let mut invariant_parts = Vec::new();
        for info in &params {
            if let (Type::Int(int_ty), Some(range)) = (&info.ty, info.invariant) {
                invariant_parts.extend(self.bounds(&name(&info.name), range, *int_ty));
            }
        }
        let invariant = conjunction(invariant_parts);

        // The body sees the names around it. Those it may assign are known
        // inside by their type alone ([N5]); the others do not change.
        let mut inner = env.clone();
        let mut assignable = BTreeSet::new();
        for (outer, slot) in inner.iter_mut() {
            if slot.mutable {
                if self.rng.chance(1, 2) {
                    slot.know = Know::top(&slot.ty);
                    slot.definition = None;
                    assignable.insert(outer.clone());
                } else {
                    slot.mutable = false;
                }
            }
        }
        for (info, parameter) in params.iter().zip(&parameters) {
            let know = match &info.ty {
                Type::Int(int_ty) => {
                    Know::Int(Val::value(*int_ty, info.invariant.unwrap_or(Range::ALL)))
                }
                other => Know::top(other),
            };
            inner.insert(
                info.name.clone(),
                Slot {
                    ty: info.ty.clone(),
                    mutable: parameter.mutable,
                    know,
                    definition: None,
                },
            );
        }
        let mut planned: Vec<(String, Vec<Type>)> = Vec::new();
        for _ in 0..=self.rng.below(2) {
            let alternative = (*self.rng.pick(&ALTERNATIVES)).to_string();
            if planned.iter().any(|(seen, _)| seen == &alternative) {
                continue;
            }
            let types = (0..self.rng.below(3)).map(|_| self.random_type()).collect();
            planned.push((alternative, types));
        }
        let mut outer_atoms = self.scope().outer_atoms.clone();
        if let Some(&first) = running.first() {
            let scope = self.scope();
            for &(site_index, which) in &scope.live[first].atoms {
                if running
                    .iter()
                    .all(|&index| scope.live[index].atoms.contains(&(site_index, which)))
                {
                    let info = &scope.sites[site_index];
                    outer_atoms.push((info.name.clone(), info.alternatives[which].clone()));
                }
            }
        }
        let leaves = vec![Vec::new(); planned.len()];
        self.scopes.push(Scope {
            sites: Vec::new(),
            live: vec![Path {
                atoms: Vec::new(),
                env: inner,
            }],
            statements: Vec::new(),
            looping: Some(LoopInfo {
                name: loop_name.clone(),
                params,
                counter: counter.clone(),
                bound,
                up,
                planned,
                leaves,
                assignable,
            }),
            outer_atoms,
        });

        // The test that lets the counter move. Without an invariant only an
        // ordering bounds it; with one, an equation does too.
        let subject = name(&counter);
        let bounded = counter_invariant.is_some();
        let unsigned = !counter_ty.is_signed();
        let condition = if up {
            match self.rng.below(5) {
                0 => bin(Binary::GreaterEqual, subject, int(bound)),
                1 => bin(Binary::Greater, int(bound), subject),
                2 if bounded => bin(Binary::Equal, subject, int(bound)),
                3 if bounded => bin(Binary::NotEqual, subject, int(bound)),
                _ => bin(Binary::Less, subject, int(bound)),
            }
        } else {
            match self.rng.below(5) {
                0 => bin(Binary::GreaterEqual, subject, int(1)),
                1 => bin(Binary::Less, int(0), subject),
                2 if bounded || unsigned => bin(Binary::Equal, subject, int(0)),
                3 if bounded || unsigned => bin(Binary::NotEqual, subject, int(0)),
                _ => bin(Binary::Greater, subject, int(0)),
            }
        };
        self.branch(&Selector::Top, &[0], condition);
        let budget = 2 + self.rng.index(6);
        self.fill(budget);

        let body = self.scopes.pop().expect("the scope of the loop body");
        let info = body.looping.expect("the loop of the body");
        let mut arms = Vec::new();
        let mut used = Vec::new();
        for (which, (alternative, types)) in info.planned.iter().enumerate() {
            if info.leaves[which].is_empty() {
                continue;
            }
            let names: Vec<String> = types.iter().map(|_| self.fresh("v")).collect();
            arms.push(Arm {
                alternative: alternative.clone(),
                names: names.clone(),
            });
            used.push((which, names));
        }
        let site_index = self.scope().sites.len();
        let mut children = Vec::new();
        for &index in running {
            let path = self.scope().live[index].clone();
            for (position, (which, names)) in used.iter().enumerate() {
                let records = &info.leaves[*which];
                let mut env = path.env.clone();
                for (field, bound) in names.iter().enumerate() {
                    let ty = &info.planned[*which].1[field];
                    let mut know = records[0].payload[field].clone();
                    for record in &records[1..] {
                        know = know.hull(&record.payload[field]);
                    }
                    // A payload name is a value term of its type.
                    let know = match (ty, know) {
                        (Type::Int(int_ty), Know::Int(val)) => {
                            Know::Int(Val::value(*int_ty, val.flow))
                        }
                        (_, know) => know,
                    };
                    env.insert(
                        bound.clone(),
                        Slot {
                            ty: ty.clone(),
                            mutable: false,
                            know,
                            definition: None,
                        },
                    );
                }
                // [K8]: an outer name that the loop changed is, after the
                // loop, what it was where the iteration left.
                for outer in &info.assignable {
                    let Some(slot) = env.get_mut(outer) else {
                        continue;
                    };
                    let mut know: Option<Know> = None;
                    for record in records {
                        if let Some(seen) = record.assigned.get(outer) {
                            know = Some(match know {
                                Some(joined) => joined.hull(seen),
                                None => seen.clone(),
                            });
                        }
                    }
                    slot.know = match (&slot.ty, know) {
                        (Type::Int(int_ty), Some(Know::Int(val))) => {
                            Know::Int(Val::value(*int_ty, val.flow))
                        }
                        (_, Some(know)) => know,
                        (ty, None) => Know::top(ty),
                    };
                    slot.definition = None;
                }
                let mut atoms = path.atoms.clone();
                atoms.push((site_index, position));
                children.push(Path { atoms, env });
            }
        }
        self.scope_mut().sites.push(SiteInfo {
            name: site.clone(),
            alternatives: arms.iter().map(|arm| arm.alternative.clone()).collect(),
        });
        self.push(
            selector,
            Command::Loop {
                site,
                name: loop_name,
                parameters,
                invariant,
                body: body.statements,
                arms,
            },
        );
        self.replace(running, children);
    }

    fn terminate(&mut self, selector: &Selector, running: &[usize]) {
        if self.scope().looping.is_none() {
            self.exit(selector, running);
            return;
        }
        let innermost = self.scopes.len() - 1;
        let outer: Vec<usize> = (0..innermost)
            .filter(|&index| self.scopes[index].looping.is_some())
            .collect();
        let done = match self.rng.below(10) {
            0..=4 => self.again(selector, running, innermost),
            5 if !outer.is_empty() => {
                let target = *self.rng.pick(&outer);
                self.again(selector, running, target)
            }
            6 => {
                self.exit(selector, running);
                true
            }
            _ => false,
        };
        if !done {
            self.leave(selector, running);
        }
    }

    fn exit(&mut self, selector: &Selector, running: &[usize]) {
        let env = self.running_env(running);
        let which = self.rng.index(self.contract.len());
        let (alternative, fields) = self.contract[which].clone();
        let mut payload = Vec::new();
        for (position, (_, ty)) in fields.iter().enumerate() {
            let (expr, know) = self.gen_expr(&env, ty, 2);
            if let Know::Int(val) = know {
                let seen = &mut self.exits[which].fields[position];
                *seen = Some(seen.map_or(val.flow, |range| range.hull(val.flow)));
            }
            payload.push(expr);
        }
        // [P4]: a condition speaks of the parameters as they were at entry,
        // and a parameter never changes.
        for (position, parameter) in self.parameters.clone().iter().enumerate() {
            if let Some(Slot {
                know: Know::Int(val),
                ..
            }) = env.get(parameter)
            {
                let seen = &mut self.exits[which].params[position];
                *seen = Some(seen.map_or(val.flow, |range| range.hull(val.flow)));
            }
        }
        self.exits[which].used = true;
        self.push(
            selector,
            Command::Exit {
                alternative,
                payload,
            },
        );
        self.replace(running, Vec::new());
    }

    fn leave(&mut self, selector: &Selector, running: &[usize]) {
        let env = self.running_env(running);
        let info = self.scope().looping.clone().expect("a loop to leave");
        let which = self.rng.index(info.planned.len());
        let (alternative, types) = info.planned[which].clone();
        let mut payload = Vec::new();
        let mut knows = Vec::new();
        for ty in &types {
            let (mut expr, know) = self.gen_expr(&env, ty, 2);
            // [W9]: a payload field of a loop has the type of its operand,
            // and literals alone are `u32` ([C1]). A name says the type.
            if let Type::Int(int_ty) = ty
                && *int_ty != IntType::U32
                && self.lib().anchor(&expr, &env).is_none()
            {
                let held = self.fresh("v");
                self.push(
                    selector,
                    Command::Bind {
                        mutable: false,
                        name: held.clone(),
                        ty: Some(ty.clone()),
                        value: expr,
                    },
                );
                expr = name(&held);
            }
            payload.push(expr);
            knows.push(know);
        }
        let assigned = info
            .assignable
            .iter()
            .filter_map(|outer| Some((outer.clone(), env.get(outer)?.know.clone())))
            .collect();
        if let Some(looping) = &mut self.scope_mut().looping {
            looping.leaves[which].push(LeaveRecord {
                payload: knows,
                assigned,
            });
        }
        self.push(
            selector,
            Command::Leave {
                alternative,
                payload,
            },
        );
        self.replace(running, Vec::new());
    }

    /// `↑ ℓ` for the loop whose body is the scope `target`. It needs room
    /// for the counter to move, which a test gave or did not.
    fn again(&mut self, selector: &Selector, running: &[usize], target: usize) -> bool {
        let env = self.running_env(running);
        let info = self.scopes[target].looping.clone().expect("a loop");
        let Some(Slot {
            know: Know::Int(counter),
            ty: Type::Int(counter_ty),
            ..
        }) = env.get(&info.counter)
        else {
            return false;
        };
        let room = if info.up {
            info.bound - counter.flow.hi
        } else {
            counter.flow.lo
        };
        if room < 1 || !counter.flow.bounded() {
            return false;
        }
        let pace = 1 + self.rng.range(0, (room - 1).min(1));
        let operator = if info.up {
            Binary::Add
        } else {
            Binary::Subtract
        };
        let moved = bin(operator, name(&info.counter), int(pace));
        if self.lib().int(&moved, &env, Some(*counter_ty)).is_none() {
            return false;
        }
        let mut arguments = vec![moved];
        for parameter in &info.params[1..] {
            arguments.push(match (&parameter.ty, parameter.invariant) {
                (Type::Int(int_ty), Some(range)) => match self.gen_int_in(&env, *int_ty, range) {
                    Some((expr, _)) => expr,
                    None => return false,
                },
                (ty, _) => self.gen_expr(&env, ty, 2).0,
            });
        }
        self.push(
            selector,
            Command::Again {
                name: info.name,
                arguments,
            },
        );
        self.replace(running, Vec::new());
        true
    }

    // Declarations.

    fn precondition(
        &mut self,
        params: &[(String, Type)],
        pre: &[Range],
        order: Option<(usize, usize)>,
    ) -> Option<Expr> {
        let mut parts = Vec::new();
        for ((parameter, ty), range) in params.iter().zip(pre) {
            if let Type::Int(int_ty) = ty {
                parts.extend(self.bounds(&name(parameter), *range, *int_ty));
            }
        }
        if let Some((small, large)) = order {
            parts.push(bin(
                Binary::LessEqual,
                name(&params[small].0),
                name(&params[large].0),
            ));
        }
        conjunction(parts)
    }

    fn parameters_and_precondition(
        &mut self,
        prefix: &str,
        count: usize,
        bounded: u64,
    ) -> (Vec<(String, Type)>, Vec<Range>) {
        let mut params = Vec::new();
        let mut pre = Vec::new();
        for index in 0..count {
            let ty = self.random_type();
            pre.push(match &ty {
                Type::Int(int_ty) if self.rng.chance(bounded, 4) => {
                    self.subrange(*int_ty).meet(value_range(*int_ty))
                }
                Type::Int(int_ty) => value_range(*int_ty),
                _ => Range::ALL,
            });
            params.push((format!("{prefix}{index}"), ty));
        }
        (params, pre)
    }

    fn function(&mut self, index: usize) -> Function {
        let count = 1 + self.rng.index(3);
        let (params, pre) = self.parameters_and_precondition("a", count, 2);
        let mut env = Env::new();
        for ((parameter, ty), range) in params.iter().zip(&pre) {
            let know = match ty {
                Type::Int(int_ty) => Know::Int(Val::value(*int_ty, *range)),
                other => Know::top(other),
            };
            env.insert(
                parameter.clone(),
                Slot {
                    ty: ty.clone(),
                    mutable: false,
                    know,
                    definition: None,
                },
            );
        }
        // The result has the type of a parameter more often than not, so
        // that the body can be made of them.
        let result = if self.rng.chance(2, 3) {
            self.rng.pick(&params).1.clone()
        } else {
            self.random_type()
        };
        let body = self.gen_expr(&env, &result, 3).0;
        let precondition = self.precondition(&params, &pre, None);
        let function = Function {
            name: format!("f{index}"),
            parameters: params.iter().map(|(n, ty)| parameter(n, ty)).collect(),
            precondition,
            result: result.clone(),
            body: body.clone(),
            line: 1,
        };
        self.functions.push(FnSig {
            name: function.name.clone(),
            params,
            pre,
            result,
            body,
        });
        function
    }

    fn alternative_names(&mut self, count: usize) -> Vec<String> {
        let mut names: Vec<String> = Vec::new();
        while names.len() < count {
            let candidate = (*self.rng.pick(&ALTERNATIVES)).to_string();
            if !names.contains(&candidate) {
                names.push(candidate);
            }
        }
        names
    }

    /// The condition `⇐ φ` that `alternative` states, as text.
    fn condition(&mut self, params: &[(String, Type)], alternative: &AltSig) -> Option<Expr> {
        let mut parts = Vec::new();
        for ((parameter, ty), bound) in params.iter().zip(&alternative.params) {
            if let (Type::Int(int_ty), Some(range)) = (ty, bound) {
                parts.extend(self.bounds(&name(parameter), *range, *int_ty));
            }
        }
        for field in &alternative.fields {
            let subject = name(&field.name);
            let end = |end: End| match end {
                End::Open => None,
                End::Literal(literal) => Some(int(literal)),
                End::Parameter(position, 0) => Some(name(&params[position].0)),
                End::Parameter(position, offset) if offset > 0 => {
                    Some(bin(Binary::Add, name(&params[position].0), int(offset)))
                }
                End::Parameter(position, offset) => Some(bin(
                    Binary::Subtract,
                    name(&params[position].0),
                    int(-offset),
                )),
            };
            if let Some(lo) = end(field.lo) {
                parts.push(if self.rng.chance(1, 3) {
                    bin(Binary::LessEqual, lo, subject.clone())
                } else {
                    bin(Binary::GreaterEqual, subject.clone(), lo)
                });
            }
            if let Some(hi) = end(field.hi) {
                parts.push(if self.rng.chance(1, 3) {
                    bin(Binary::GreaterEqual, hi, subject.clone())
                } else {
                    bin(Binary::LessEqual, subject.clone(), hi)
                });
            }
        }
        conjunction(parts)
    }

    fn signature(&mut self, sig: &Sig) -> (Vec<Parameter>, Option<Expr>, Vec<Alternative>) {
        let parameters = sig.params.iter().map(|(n, ty)| parameter(n, ty)).collect();
        let precondition = self.precondition(&sig.params, &sig.pre, sig.order);
        let contract = sig
            .alts
            .iter()
            .map(|alternative| Alternative {
                name: alternative.name.clone(),
                fields: alternative
                    .fields
                    .iter()
                    .map(|field| parameter(&field.name, &field.ty))
                    .collect(),
                condition: self.condition(&sig.params, alternative),
            })
            .collect();
        (parameters, precondition, contract)
    }

    /// Two parameters of one type whose intervals allow `pᵢ ≤ pⱼ`.
    fn order(&mut self, params: &[(String, Type)], pre: &[Range]) -> Option<(usize, usize)> {
        if !self.rng.chance(1, 4) {
            return None;
        }
        for small in 0..params.len() {
            for large in small + 1..params.len() {
                let same =
                    matches!(&params[small].1, Type::Int(_)) && params[small].1 == params[large].1;
                if same && pre[small].lo <= pre[large].hi && pre[small].lo <= pre[large].lo {
                    return Some((small, large));
                }
            }
        }
        None
    }

    fn external(&mut self, index: usize) -> Control {
        let count = self.rng.index(4);
        let (params, pre) = self.parameters_and_precondition("p", count, 1);
        let names = {
            let count = 1 + self.rng.index(3);
            self.alternative_names(count)
        };
        let mut alts: Vec<AltSig> = Vec::new();
        for alternative in names {
            let mut fields = Vec::new();
            for position in 0..self.rng.index(3) {
                let ty = self.random_type();
                let (mut lo, mut hi) = (End::Open, End::Open);
                if let Type::Int(int_ty) = &ty {
                    let same: Vec<usize> = (0..params.len())
                        .filter(|&parameter| params[parameter].1 == ty)
                        .collect();
                    match self.rng.below(8) {
                        0 | 1 => {
                            let range = self.subrange(*int_ty);
                            let value = value_range(*int_ty);
                            if range.lo > value.lo {
                                lo = End::Literal(range.lo);
                            }
                            if range.hi < value.hi {
                                hi = End::Literal(range.hi);
                            }
                        }
                        // Each of these is satisfied by the argument itself.
                        2 if !same.is_empty() => {
                            let parameter = *self.rng.pick(&same);
                            lo = End::Parameter(parameter, 0);
                            hi = End::Parameter(parameter, self.rng.range(0, 5));
                        }
                        3 if !same.is_empty() => {
                            let parameter = *self.rng.pick(&same);
                            lo = End::Parameter(parameter, -self.rng.range(0, 5));
                            hi = End::Parameter(parameter, 0);
                        }
                        4 if !same.is_empty() => {
                            lo = End::Parameter(*self.rng.pick(&same), 0);
                        }
                        5 if !same.is_empty() => {
                            hi = End::Parameter(*self.rng.pick(&same), 0);
                        }
                        _ => {}
                    }
                }
                fields.push(FieldSig {
                    name: format!("r{position}"),
                    ty,
                    lo,
                    hi,
                });
            }
            alts.push(AltSig {
                name: alternative,
                fields,
                params: vec![None; params.len()],
            });
        }
        // Two alternatives may divide the values of a parameter between
        // them. Every argument then has an answer.
        let ints: Vec<usize> = (0..params.len())
            .filter(|&parameter| matches!(params[parameter].1, Type::Int(_)))
            .collect();
        if alts.len() >= 2 && !ints.is_empty() && self.rng.chance(1, 2) {
            let parameter = *self.rng.pick(&ints);
            let Type::Int(int_ty) = params[parameter].1 else {
                unreachable!("an integer parameter");
            };
            let inside = pre[parameter].meet(fit_range(int_ty));
            if inside.width().is_some_and(|width| width >= 2) {
                let threshold = self.literal_in(Range::new(inside.lo, inside.hi - 1));
                alts[0].params[parameter] = Some(Range {
                    lo: NEG,
                    hi: threshold,
                });
                alts[1].params[parameter] = Some(Range {
                    lo: threshold + 1,
                    hi: POS,
                });
            }
        }
        let uses = if self.rng.chance(1, 2) {
            vec![(*self.rng.pick(&EFFECTS)).to_string()]
        } else {
            Vec::new()
        };
        let sig = Sig {
            name: format!("e{index}"),
            params,
            pre,
            order: None,
            alts,
            uses,
        };
        let (parameters, precondition, contract) = self.signature(&sig);
        let control = Control {
            name: sig.name.clone(),
            public: false,
            external: true,
            is_async: false,
            contingent: false,
            faults: false,
            parameters,
            precondition,
            contract,
            uses: sig.uses.clone(),
            body: Vec::new(),
            line: 1,
        };
        self.callables.push(sig);
        control
    }

    fn control(&mut self, index: usize) -> Control {
        self.fresh = 0;
        self.loops = 0;
        self.effects.clear();
        let count = self.rng.index(5);
        let (params, pre) = self.parameters_and_precondition("p", count, 2);
        let order = self.order(&params, &pre);
        let names = {
            let count = 1 + self.rng.index(3);
            self.alternative_names(count)
        };
        self.contract = names
            .into_iter()
            .map(|alternative| {
                let fields = (0..self.rng.index(3))
                    .map(|position| (format!("r{position}"), self.random_type()))
                    .collect();
                (alternative, fields)
            })
            .collect();
        self.exits = self
            .contract
            .iter()
            .map(|(_, fields)| ExitRecord {
                used: false,
                fields: vec![None; fields.len()],
                params: vec![None; params.len()],
            })
            .collect();
        self.parameters = params.iter().map(|(n, _)| n.clone()).collect();
        let mut env = Env::new();
        for ((parameter, ty), range) in params.iter().zip(&pre) {
            let know = match ty {
                Type::Int(int_ty) => Know::Int(Val::value(*int_ty, *range)),
                other => Know::top(other),
            };
            env.insert(
                parameter.clone(),
                Slot {
                    ty: ty.clone(),
                    mutable: false,
                    know,
                    definition: None,
                },
            );
        }
        self.scopes.push(Scope {
            sites: Vec::new(),
            live: vec![Path {
                atoms: Vec::new(),
                env,
            }],
            statements: Vec::new(),
            looping: None,
            outer_atoms: Vec::new(),
        });
        let budget = 3 + self.rng.index(10);
        self.fill(budget);
        let body = self.scopes.pop().expect("the scope of the control");

        // The conditions of the contract: what held at every exit with the
        // alternative, stated in full, in part or not at all.
        let mut alts = Vec::new();
        for (which, (alternative, fields)) in self.contract.clone().into_iter().enumerate() {
            let record = self.exits[which].clone();
            let mut field_sigs = Vec::new();
            for (position, (field, ty)) in fields.into_iter().enumerate() {
                let (mut lo, mut hi) = (End::Open, End::Open);
                if let (Type::Int(int_ty), Some(range)) = (&ty, record.fields[position]) {
                    let value = value_range(*int_ty);
                    if range.has_lo() && range.lo > value.lo && self.rng.chance(3, 4) {
                        lo = End::Literal(range.lo - self.slack());
                    }
                    if range.has_hi() && range.hi < value.hi && self.rng.chance(3, 4) {
                        hi = End::Literal(range.hi + self.slack());
                    }
                }
                field_sigs.push(FieldSig {
                    name: field,
                    ty,
                    lo,
                    hi,
                });
            }
            let mut param_bounds = vec![None; params.len()];
            for (position, (_, ty)) in params.iter().enumerate() {
                if let (Type::Int(_), Some(range)) = (ty, record.params[position]) {
                    let stated = Range {
                        lo: if range.lo > pre[position].lo && self.rng.chance(3, 4) {
                            range.lo
                        } else {
                            NEG
                        },
                        hi: if range.hi < pre[position].hi && self.rng.chance(3, 4) {
                            range.hi
                        } else {
                            POS
                        },
                    };
                    if stated != Range::ALL {
                        param_bounds[position] = Some(stated);
                    }
                }
            }
            alts.push(AltSig {
                name: alternative,
                fields: field_sigs,
                params: param_bounds,
            });
        }
        let mut uses: Vec<String> = self.effects.iter().cloned().collect();
        if self.rng.chance(1, 8) {
            let extra = (*self.rng.pick(&EFFECTS)).to_string();
            if !uses.contains(&extra) {
                uses.push(extra);
            }
        }
        let sig = Sig {
            name: format!("c{index}"),
            params,
            pre,
            order,
            alts,
            uses,
        };
        let (parameters, precondition, contract) = self.signature(&sig);
        let control = Control {
            name: sig.name.clone(),
            public: self.rng.chance(1, 3),
            external: false,
            is_async: false,
            contingent: false,
            faults: false,
            parameters,
            precondition,
            contract,
            uses: sig.uses.clone(),
            body: body.statements,
            line: 1,
        };
        self.callables.push(sig);
        control
    }

    /// How far a stated bound lies beyond what was found, most often not at
    /// all.
    fn slack(&mut self) -> i128 {
        if self.rng.chance(1, 4) {
            self.rng.range(1, 3)
        } else {
            0
        }
    }
}

/// Generates a core program of slice 1 that is valid by construction: it
/// resolves, the checker accepts it, and no execution from an entry that
/// satisfies its precondition is stuck in the oracle, on a 32-bit or a 64-bit
/// target, under a host that respects the contracts.
pub fn valid(rng: &mut Rng) -> Program {
    let palette = (0..3).map(|_| *rng.pick(&IntType::ALL)).collect();
    let mut generator = Generator {
        rng,
        functions: Vec::new(),
        callables: Vec::new(),
        palette,
        scopes: Vec::new(),
        fresh: 0,
        loops: 0,
        contract: Vec::new(),
        parameters: Vec::new(),
        exits: Vec::new(),
        effects: BTreeSet::new(),
    };
    let mut declarations = Vec::new();
    for index in 0..generator.rng.index(3) {
        declarations.push(Declaration::Function(generator.function(index)));
    }
    for index in 0..1 + generator.rng.index(3) {
        declarations.push(Declaration::Control(generator.external(index)));
    }
    for index in 0..1 + generator.rng.index(3) {
        declarations.push(Declaration::Control(generator.control(index)));
    }
    Program { declarations }
}
