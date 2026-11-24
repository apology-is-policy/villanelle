//! Hosts for the oracle.
//!
//! An extern control is a relation of the host: given the arguments it
//! yields an alternative and a payload ([E-Extern]). The oracle checks every
//! answer against the contract ([E-Host]), so a host here may be wrong; a
//! wrong answer ends the run in `violation`, not in a stuck state.

use crate::int::Int;
use crate::oracle::{Config, RuntimeStep, Value, signature_holds};
use crate::rng::{Rng, mix};
use crate::typed::{self, BorrowMode, Comparison, Control, Expr, IntType, Program, Type, VarRef};
use std::collections::{BTreeMap, VecDeque};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Answer {
    pub alternative: String,
    pub payload: Vec<Value>,
    /// The values that the host leaves behind arguments it was lent
    /// exclusively, by the position of the argument ([E-Extern]). An
    /// argument that is not named keeps what it holds.
    pub writes: Vec<(usize, Value)>,
}

pub trait Host {
    /// The answer to one call, or the reason this host has none.
    fn call(
        &mut self,
        control: &Control,
        arguments: &[Value],
        config: &Config,
    ) -> Result<Answer, String>;

    /// Choose which ready task (index in `0..ready_count`) takes the next turn ([E-Turn]).
    fn pick_turn(&mut self, ready_count: usize) -> usize {
        let _ = ready_count;
        0
    }

    /// Choose which waiting extern async operation completes next when no task is ready
    /// ([E-Turn], [E-AwaitHost]).
    fn pick_waiting(&mut self, waiting: &[(&Control, &[Value])]) -> usize {
        let _ = waiting;
        0
    }

    /// Whether the host cancels the root task of the innermost run before the next turn
    /// ([E-Cancel]). Called only when the root is not yet cancelled.
    fn should_cancel_root(&mut self, turn: u64) -> bool {
        let _ = turn;
        false
    }
}

/// A host that answers from a list, in order. Each entry names the control
/// it answers.
#[derive(Clone, Debug, Default)]
pub struct Script {
    pub answers: VecDeque<(String, Answer)>,
}

impl Host for Script {
    fn call(
        &mut self,
        control: &Control,
        _arguments: &[Value],
        _config: &Config,
    ) -> Result<Answer, String> {
        match self.answers.pop_front() {
            None => Err(format!(
                "the script has no answer left for `{}`",
                control.name
            )),
            Some((name, _)) if name != control.name => Err(format!(
                "the script answers `{name}` next, and `{}` was called",
                control.name
            )),
            Some((_, answer)) => Ok(answer),
        }
    }

    fn pick_waiting(&mut self, waiting: &[(&Control, &[Value])]) -> usize {
        if let Some((next_name, _)) = self.answers.front()
            && let Some(idx) = waiting.iter().position(|(c, _)| c.name == *next_name)
        {
            return idx;
        }
        0
    }
}

/// A host wrapper that supplies explicit turn choices, waiting-operation choices,
/// and optional root cancellation at a given turn ([E-Turn], [E-Cancel]).
#[derive(Clone, Debug)]
pub struct Scheduled<H: Host> {
    pub inner: H,
    pub turns: VecDeque<usize>,
    pub waiting: VecDeque<usize>,
    pub cancel_at_turn: Option<u64>,
    pub cancel_decisions: VecDeque<bool>,
}

impl<H: Host> Scheduled<H> {
    pub fn new(inner: H) -> Self {
        Self {
            inner,
            turns: VecDeque::new(),
            waiting: VecDeque::new(),
            cancel_at_turn: None,
            cancel_decisions: VecDeque::new(),
        }
    }
}

impl<H: Host> Host for Scheduled<H> {
    fn call(
        &mut self,
        control: &Control,
        arguments: &[Value],
        config: &Config,
    ) -> Result<Answer, String> {
        self.inner.call(control, arguments, config)
    }

    fn pick_turn(&mut self, ready_count: usize) -> usize {
        if let Some(choice) = self.turns.pop_front() {
            choice % ready_count.max(1)
        } else {
            self.inner.pick_turn(ready_count)
        }
    }

    fn pick_waiting(&mut self, waiting: &[(&Control, &[Value])]) -> usize {
        if let Some(choice) = self.waiting.pop_front() {
            choice % waiting.len().max(1)
        } else {
            self.inner.pick_waiting(waiting)
        }
    }

    fn should_cancel_root(&mut self, turn: u64) -> bool {
        if let Some(flag) = self.cancel_decisions.pop_front() {
            return flag;
        }
        if let Some(at) = self.cancel_at_turn {
            turn >= at
        } else {
            self.inner.should_cancel_root(turn)
        }
    }
}

/// A host that computes the checked arithmetic of the prelude and passes
/// every other call on.
pub struct Arithmetic<H: Host>(pub H);

fn checked(
    control: &Control,
    arguments: &[Value],
    config: &Config,
) -> Option<Result<Answer, String>> {
    let operations = [
        "checked_add",
        "checked_sub",
        "checked_mul",
        "checked_div",
        "checked_rem",
    ];
    let operation = operations
        .iter()
        .find(|name| control.name.starts_with(**name))?;
    let shape = || {
        Err(format!(
            "`{}` does not have the shape of checked arithmetic",
            control.name
        ))
    };
    let [Value::Int(left), Value::Int(right)] = arguments else {
        return Some(shape());
    };
    let [fits, fails] = control.contract.as_slice() else {
        return Some(shape());
    };
    let ([field], true) = (fits.fields.as_slice(), fails.fields.is_empty()) else {
        return Some(shape());
    };
    let result: Int = match *operation {
        "checked_add" => left.plus(right),
        "checked_sub" => left.minus(right),
        "checked_mul" => left.times(right),
        _ => {
            let Some((quotient, remainder)) = left.divide(right) else {
                return Some(Err(format!(
                    "`{}` was asked to divide by zero; its contract must require a divisor that is not zero",
                    control.name
                )));
            };
            if *operation == "checked_div" {
                quotient
            } else {
                remainder
            }
        }
    };
    let result = Value::Int(result);
    Some(Ok(
        if matches!(field.ty, Type::Int(_)) && config.fits(&result, &field.ty) {
            Answer {
                alternative: fits.name.clone(),
                payload: vec![result],
                writes: Vec::new(),
            }
        } else {
            Answer {
                alternative: fails.name.clone(),
                payload: Vec::new(),
                writes: Vec::new(),
            }
        },
    ))
}

impl<H: Host> Host for Arithmetic<H> {
    fn call(
        &mut self,
        control: &Control,
        arguments: &[Value],
        config: &Config,
    ) -> Result<Answer, String> {
        match checked(control, arguments, config) {
            Some(answer) => answer,
            None => self.0.call(control, arguments, config),
        }
    }

    fn pick_turn(&mut self, ready_count: usize) -> usize {
        self.0.pick_turn(ready_count)
    }

    fn pick_waiting(&mut self, waiting: &[(&Control, &[Value])]) -> usize {
        self.0.pick_waiting(waiting)
    }

    fn should_cancel_root(&mut self, turn: u64) -> bool {
        self.0.should_cancel_root(turn)
    }
}

/// Draws a scalar value of `ty` that fits under `config`.
pub fn draw_value(rng: &mut Rng, ty: &Type, arguments: &[Value], config: &Config) -> Value {
    match ty.deref_type() {
        Type::Bool => Value::Bool(rng.chance(1, 2)),
        Type::Int(int_ty) => Value::Int(draw_int(rng, *int_ty, arguments, config)),
        Type::String => {
            let samples = ["", "a", "b", "ok", "hello", "key"];
            Value::String((*rng.pick(&samples)).to_string())
        }
        Type::Vector(_) => Value::Vector(Vec::new()),
        Type::Map(_, _) => Value::Map(BTreeMap::new()),
        Type::Resource(rid, name) => Value::Resource {
            ty: *rid,
            name: name.clone(),
            id: rng.below(1_000_000) + 1,
        },
        _ => Value::Int(Int::zero()),
    }
}

/// Draws a value of any slice 1 or slice 2 type `ty` using `program`
/// definitions. `None` where the type holds an outcome type and no value of
/// it was found ([`draw_outcome`]).
pub fn draw_value_in_program(
    program: &Program,
    rng: &mut Rng,
    ty: &Type,
    arguments: &[Value],
    config: &Config,
    next_res: &mut u64,
) -> Option<Value> {
    Some(match ty.deref_type() {
        Type::Bool => Value::Bool(rng.chance(1, 2)),
        Type::Int(int_ty) => Value::Int(draw_int(rng, *int_ty, arguments, config)),
        Type::String => {
            let samples = ["", "a", "b", "ok", "hello", "key"];
            Value::String((*rng.pick(&samples)).to_string())
        }
        Type::Struct(sid, name) => {
            let fields = program.structs[*sid]
                .fields
                .iter()
                .map(|f| draw_value_in_program(program, rng, &f.ty, arguments, config, next_res))
                .collect::<Option<Vec<Value>>>()?;
            Value::Struct {
                ty: *sid,
                name: name.clone(),
                fields,
            }
        }
        Type::Variant(vid, name) => {
            let vdef = &program.variants[*vid];
            let cidx = rng.index(vdef.constructors.len());
            let ctor = &vdef.constructors[cidx];
            let fields = ctor
                .fields
                .iter()
                .map(|f| draw_value_in_program(program, rng, &f.ty, arguments, config, next_res))
                .collect::<Option<Vec<Value>>>()?;
            Value::Variant {
                ty: *vid,
                name: name.clone(),
                constructor: cidx,
                constructor_name: ctor.name.clone(),
                fields,
            }
        }
        Type::Vector(elem_ty) => {
            let len = rng.below(4) as usize;
            let items = (0..len)
                .map(|_| draw_value_in_program(program, rng, elem_ty, arguments, config, next_res))
                .collect::<Option<Vec<Value>>>()?;
            Value::Vector(items)
        }
        Type::Map(k_ty, v_ty) => {
            let len = rng.below(3) as usize;
            let mut entries = BTreeMap::new();
            for _ in 0..len {
                let k = draw_value_in_program(program, rng, k_ty, arguments, config, next_res)?;
                let v = draw_value_in_program(program, rng, v_ty, arguments, config, next_res)?;
                entries.insert(k, v);
            }
            Value::Map(entries)
        }
        Type::Resource(rid, name) => {
            *next_res += 1;
            Value::Resource {
                ty: *rid,
                name: name.clone(),
                id: *next_res,
            }
        }
        Type::Outcome(oid, _) => draw_outcome(program, rng, *oid, config, next_res)?,
        _ => Value::Int(Int::zero()),
    })
}

/// What each condition of the contract of `control` says of each field of
/// its alternative in plain bounds, for `arguments`. A value drawn within
/// them most often satisfies the condition.
fn field_bounds(control: &Control, arguments: &[Value]) -> Vec<Vec<(Option<i128>, Option<i128>)>> {
    control
        .contract
        .iter()
        .map(|alternative| match &alternative.condition {
            Some(condition) => plain_bounds(
                condition,
                arguments,
                alternative.fields.len(),
                &|name| match name {
                    VarRef::Field(index) => Some(*index),
                    _ => None,
                },
            ),
            None => Vec::new(),
        })
        .collect()
}

/// A payload for `alternative`, each integer field within its plain bounds
/// where it has some. Whether the condition holds of it is for the caller.
fn draw_payload(
    program: &Program,
    rng: &mut Rng,
    alternative: &typed::Alternative,
    bounds: &[(Option<i128>, Option<i128>)],
    arguments: &[Value],
    config: &Config,
    next_res: &mut u64,
) -> Option<Vec<Value>> {
    alternative
        .fields
        .iter()
        .enumerate()
        .map(|(index, field)| {
            let bounded = match (&field.ty, bounds.get(index)) {
                (Type::Int(int_ty), Some((low, high))) if low.is_some() || high.is_some() => {
                    draw_int_between(rng, *int_ty, *low, *high, config)
                }
                _ => None,
            };
            match bounded {
                Some(number) => Some(Value::Int(number)),
                None => draw_value_in_program(program, rng, &field.ty, arguments, config, next_res),
            }
        })
        .collect()
}

/// A value of the outcome type `oid` as the operation of that name could
/// have given it ([I12]): for some arguments that satisfy the precondition
/// of the operation, an alternative and a payload of which its condition
/// holds. A checked program may assume that much of a value of the type
/// that it did not capture itself, so a host and an entry give no other.
/// A declared outcome type has no conditions. `None` where the attempts
/// found no such value.
pub fn draw_outcome(
    program: &Program,
    rng: &mut Rng,
    oid: usize,
    config: &Config,
    next_res: &mut u64,
) -> Option<Value> {
    let odef = &program.outcomes[oid];
    let made = |alternative: usize, payload: Vec<Value>| Value::Outcome {
        ty: oid,
        alternative,
        alternative_name: odef.alternatives[alternative].name.clone(),
        payload,
    };
    let Some(control) = program
        .controls
        .iter()
        .find(|control| control.name == odef.name)
    else {
        let alternative = rng.index(odef.alternatives.len());
        let payload = odef.alternatives[alternative]
            .fields
            .iter()
            .map(|f| draw_value_in_program(program, rng, &f.ty, &[], config, next_res))
            .collect::<Option<Vec<Value>>>()?;
        return Some(made(alternative, payload));
    };
    let hints = hints_of(control.precondition.as_ref(), &[]);
    let of_parameters = match &control.precondition {
        Some(pre) => plain_bounds(pre, &[], control.parameters.len(), &|name| match name {
            VarRef::Parameter(index) => Some(*index),
            _ => None,
        }),
        None => vec![(None, None); control.parameters.len()],
    };
    let count = control.contract.len();
    for _ in 0..24 {
        // The arguments are imagined: what they hold is no value of the
        // execution, and a resource among them has no number of its own.
        let mut imagined = *next_res;
        let arguments: Option<Vec<Value>> = control
            .parameters
            .iter()
            .zip(&of_parameters)
            .map(|(parameter, (low, high))| match parameter.ty.deref_type() {
                Type::Int(ty) => Some(Value::Int(
                    draw_int_between(rng, *ty, *low, *high, config)
                        .unwrap_or_else(|| draw_int_near(rng, *ty, &hints, config)),
                )),
                other => draw_value_in_program(program, rng, other, &[], config, &mut imagined),
            })
            .collect();
        let Some(arguments) = arguments else {
            continue;
        };
        if let Some(pre) = &control.precondition
            && !signature_holds(program, config, pre, &arguments, &[])
        {
            continue;
        }
        let bounds = field_bounds(control, &arguments);
        let start = rng.index(count);
        for attempt in 0..count * 8 {
            let which = (start + attempt) % count;
            let alternative = &control.contract[which];
            // A borrow in a payload names a place of an argument, and here
            // there is none.
            if alternative
                .fields
                .iter()
                .any(|field| program.contains_borrow_or_view(&field.ty))
            {
                continue;
            }
            let mut resources = *next_res;
            let Some(payload) = draw_payload(
                program,
                rng,
                alternative,
                &bounds[which],
                &arguments,
                config,
                &mut resources,
            ) else {
                continue;
            };
            let valid = match &alternative.condition {
                None => true,
                Some(condition) => {
                    signature_holds(program, config, condition, &arguments, &payload)
                }
            };
            if valid {
                *next_res = resources;
                return Some(made(which, payload));
            }
        }
    }
    None
}

fn draw_int(rng: &mut Rng, ty: IntType, arguments: &[Value], config: &Config) -> Int {
    let (least, greatest) = ty.bounds(&config.usize_max);
    let low = least.to_i128().unwrap_or(i128::from(i64::MIN));
    let high = greatest.to_i128().unwrap_or(i128::from(u64::MAX));
    let chosen = match rng.below(6) {
        0 => rng.range(0.max(low), 7.min(high)),
        1 => rng.range((-7).max(low), 7.min(high)),
        2 => {
            let ints: Vec<i128> = arguments
                .iter()
                .filter_map(|value| match value {
                    Value::Int(number) => number.to_i128(),
                    _ => None,
                })
                .collect();
            if ints.is_empty() {
                rng.range((-3).max(low), 3.min(high))
            } else {
                let base = *rng.pick(&ints);
                base.saturating_add(rng.range(-2, 2)).clamp(low, high)
            }
        }
        3 => rng.range((-50).max(low), 50.min(high)),
        4 => *rng.pick(&[
            low,
            (low + 1).min(high),
            0.clamp(low, high),
            1.clamp(low, high),
            (high - 1).max(low),
            high,
        ]),
        _ => rng.range(low, high),
    };
    Int::from_i128(chosen)
}

/// The integer literals that occur in `formula`. A value that satisfies a
/// precondition or the condition of an alternative is most often at one of
/// them or beside it.
pub fn integer_literals(formula: &Expr, out: &mut Vec<i128>) {
    match formula {
        Expr::Integer(value, _) => out.extend(value.to_i128()),
        Expr::Negate(inner, _) => {
            if let Expr::Integer(value, _) = &**inner {
                out.extend(value.to_i128().map(|value| -value));
            } else {
                integer_literals(inner, out);
            }
        }
        Expr::Move(inner, _)
        | Expr::Field(inner, _, _, _)
        | Expr::Len(inner)
        | Expr::Clone(inner, _)
        | Expr::Trim(inner)
        | Expr::Not(inner) => integer_literals(inner, out),
        Expr::Index(left, right, _)
        | Expr::Arithmetic(_, left, right, _)
        | Expr::Compare(_, left, right)
        | Expr::And(left, right)
        | Expr::Or(left, right) => {
            integer_literals(left, out);
            integer_literals(right, out);
        }
        Expr::Struct(_, items, _)
        | Expr::Variant(_, _, items, _)
        | Expr::Vector(items, _)
        | Expr::Call(_, items, _) => {
            for item in items {
                integer_literals(item, out);
            }
        }
        _ => {}
    }
}

/// The values near which a formula over `arguments` changes its truth: its
/// literals, the integer arguments, and each argument a literal away.
pub fn hints_of(formula: Option<&Expr>, arguments: &[Value]) -> Vec<i128> {
    let mut literals = Vec::new();
    if let Some(formula) = formula {
        integer_literals(formula, &mut literals);
    }
    let given: Vec<i128> = arguments
        .iter()
        .filter_map(|value| match value {
            Value::Int(number) => number.to_i128(),
            _ => None,
        })
        .collect();
    let mut out = literals.clone();
    out.extend(&given);
    for argument in &given {
        for literal in &literals {
            out.extend(argument.checked_add(*literal));
            out.extend(argument.checked_sub(*literal));
        }
    }
    out
}

/// The value of a term made of literals, of the integer `arguments` and of
/// sums and differences of those.
fn plain_term(term: &Expr, arguments: &[Value]) -> Option<i128> {
    match term {
        Expr::Integer(value, _) => value.to_i128(),
        Expr::Negate(inner, _) => plain_term(inner, arguments)?.checked_neg(),
        Expr::Var(VarRef::Parameter(index), _) => match arguments.get(*index)? {
            Value::Int(number) => number.to_i128(),
            _ => None,
        },
        Expr::Arithmetic(typed::Arithmetic::Add, left, right, _) => {
            plain_term(left, arguments)?.checked_add(plain_term(right, arguments)?)
        }
        Expr::Arithmetic(typed::Arithmetic::Subtract, left, right, _) => {
            plain_term(left, arguments)?.checked_sub(plain_term(right, arguments)?)
        }
        _ => None,
    }
}

/// The bounds that the conjuncts of `formula` put on each of `count`
/// subjects, where a conjunct compares a subject with a plain term. `subject`
/// says which subject a name is. The bounds are a guide for drawing values:
/// whether the formula holds is decided by evaluating it.
pub fn plain_bounds(
    formula: &Expr,
    arguments: &[Value],
    count: usize,
    subject: &dyn Fn(&VarRef) -> Option<usize>,
) -> Vec<(Option<i128>, Option<i128>)> {
    fn visit(
        formula: &Expr,
        positive: bool,
        arguments: &[Value],
        subject: &dyn Fn(&VarRef) -> Option<usize>,
        out: &mut [(Option<i128>, Option<i128>)],
    ) {
        match formula {
            Expr::And(left, right) if positive => {
                visit(left, true, arguments, subject, out);
                visit(right, true, arguments, subject, out);
            }
            Expr::Or(left, right) if !positive => {
                visit(left, false, arguments, subject, out);
                visit(right, false, arguments, subject, out);
            }
            Expr::Not(inner) => visit(inner, !positive, arguments, subject, out),
            Expr::Compare(comparison, left, right) => {
                let which = |term: &Expr| match term {
                    Expr::Var(name, _) => subject(name),
                    _ => None,
                };
                // `subject ⋈ value`, with the comparison turned when the
                // subject stands on the right.
                let (index, value, comparison) = match (which(left), which(right)) {
                    (Some(index), None) => match plain_term(right, arguments) {
                        Some(value) => (index, value, *comparison),
                        None => return,
                    },
                    (None, Some(index)) => match plain_term(left, arguments) {
                        Some(value) => (
                            index,
                            value,
                            match comparison {
                                Comparison::Less => Comparison::Greater,
                                Comparison::LessEqual => Comparison::GreaterEqual,
                                Comparison::Greater => Comparison::Less,
                                Comparison::GreaterEqual => Comparison::LessEqual,
                                other => *other,
                            },
                        ),
                        None => return,
                    },
                    _ => return,
                };
                let comparison = if positive {
                    comparison
                } else {
                    match comparison {
                        Comparison::Less => Comparison::GreaterEqual,
                        Comparison::LessEqual => Comparison::Greater,
                        Comparison::Greater => Comparison::LessEqual,
                        Comparison::GreaterEqual => Comparison::Less,
                        Comparison::Equal => Comparison::NotEqual,
                        Comparison::NotEqual => Comparison::Equal,
                    }
                };
                let (low, high) = &mut out[index];
                let raise = |low: &mut Option<i128>, to: i128| {
                    *low = Some(low.map_or(to, |seen| seen.max(to)));
                };
                let lower = |high: &mut Option<i128>, to: i128| {
                    *high = Some(high.map_or(to, |seen| seen.min(to)));
                };
                match comparison {
                    Comparison::GreaterEqual => raise(low, value),
                    Comparison::Greater => raise(low, value.saturating_add(1)),
                    Comparison::LessEqual => lower(high, value),
                    Comparison::Less => lower(high, value.saturating_sub(1)),
                    Comparison::Equal => {
                        raise(low, value);
                        lower(high, value);
                    }
                    Comparison::NotEqual => {}
                }
            }
            _ => {}
        }
    }
    let mut out = vec![(None, None); count];
    visit(formula, true, arguments, subject, &mut out);
    out
}

/// Draws an integer of `ty` from `low` to `high`, where an end that is
/// absent is the end of the type, with the ends and their neighbours
/// preferred. `None` when no value of the type lies there.
pub fn draw_int_between(
    rng: &mut Rng,
    ty: IntType,
    low: Option<i128>,
    high: Option<i128>,
    config: &Config,
) -> Option<Int> {
    let (least, greatest) = ty.bounds(&config.usize_max);
    let least = least.to_i128().unwrap_or(i128::from(i64::MIN));
    let greatest = greatest.to_i128().unwrap_or(i128::from(u64::MAX));
    let low = low.map_or(least, |low| low.max(least));
    let high = high.map_or(greatest, |high| high.min(greatest));
    if low > high {
        return None;
    }
    let chosen = match rng.below(8) {
        0 => low,
        1 => high,
        2 => (low + 1).min(high),
        3 => (high - 1).max(low),
        4 | 5 => rng.range(low, high.min(low.saturating_add(16))),
        6 => rng.range(low.max(high.saturating_sub(16)), high),
        _ => rng.range(low, high),
    };
    Some(Int::from_i128(chosen))
}

/// Draws an integer of `ty` at, beside or between the `hints`, and otherwise
/// as [`draw_value`] does.
pub fn draw_int_near(rng: &mut Rng, ty: IntType, hints: &[i128], config: &Config) -> Int {
    if hints.is_empty() || rng.chance(1, 4) {
        return draw_int(rng, ty, &[], config);
    }
    let (least, greatest) = ty.bounds(&config.usize_max);
    let low = least.to_i128().unwrap_or(i128::from(i64::MIN));
    let high = greatest.to_i128().unwrap_or(i128::from(u64::MAX));
    let base = *rng.pick(hints);
    let chosen = match rng.below(5) {
        0 | 1 => base,
        2 => base.saturating_add(1),
        3 => base.saturating_sub(1),
        _ => {
            let other = *rng.pick(hints);
            rng.range(base.min(other), base.max(other))
        }
    };
    Int::from_i128(chosen.clamp(low, high))
}

fn push_value(words: &mut Vec<u64>, value: &Value) {
    match value {
        Value::Bool(flag) => {
            words.push(0);
            words.push(u64::from(*flag));
        }
        Value::Int(number) => {
            words.push(if number.is_negative() { 2 } else { 1 });
            let raw = number.to_i128().unwrap_or(0) as u128;
            words.push(raw as u64);
            words.push((raw >> 64) as u64);
        }
        Value::String(s) => {
            words.push(3);
            words.push(s.len() as u64);
            for b in s.as_bytes() {
                words.push(u64::from(*b));
            }
        }
        Value::Struct { ty, fields, .. } => {
            words.push(4);
            words.push(*ty as u64);
            words.push(fields.len() as u64);
            for f in fields {
                push_value(words, f);
            }
        }
        Value::Variant {
            ty,
            constructor,
            fields,
            ..
        } => {
            words.push(5);
            words.push(*ty as u64);
            words.push(*constructor as u64);
            words.push(fields.len() as u64);
            for f in fields {
                push_value(words, f);
            }
        }
        Value::Vector(items) => {
            words.push(6);
            words.push(items.len() as u64);
            for item in items {
                push_value(words, item);
            }
        }
        Value::Map(entries) => {
            words.push(7);
            words.push(entries.len() as u64);
            for (k, v) in entries {
                push_value(words, k);
                push_value(words, v);
            }
        }
        Value::Resource { ty, id, .. } => {
            words.push(8);
            words.push(*ty as u64);
            words.push(*id);
        }
        Value::Outcome {
            ty,
            alternative,
            payload,
            ..
        } => {
            words.push(9);
            words.push(*ty as u64);
            words.push(*alternative as u64);
            for p in payload {
                push_value(words, p);
            }
        }
        Value::Ref { mode, tag, .. } => {
            words.push(10);
            words.push(u64::from(*mode == crate::typed::BorrowMode::Exclusive));
            words.push(*tag);
        }
        Value::TaskSet(id) => {
            words.push(11);
            words.push(*id);
        }
    }
}

/// A host that draws answers from a seeded generator and honors every
/// contract ([E-Host]).
pub struct Seeded<'a> {
    program: &'a Program,
    seed: u64,
    rng: Rng,
    next_res: u64,
    /// Whether it leaves values of its own behind the arguments lent
    /// exclusively, now and then.
    writes: bool,
}

impl<'a> Seeded<'a> {
    /// A host that leaves every argument as it found it.
    pub fn new(program: &'a Program, seed: u64) -> Seeded<'a> {
        Seeded {
            program,
            seed,
            rng: Rng::new(seed),
            next_res: 0,
            writes: false,
        }
    }

    /// A host that now and then leaves a value of its own behind an
    /// argument lent exclusively, where the condition of the alternative
    /// does not speak of it and the value holds no obligation ([E-Host]).
    pub fn writing(program: &'a Program, seed: u64) -> Seeded<'a> {
        Seeded {
            writes: true,
            ..Seeded::new(program, seed)
        }
    }
}

/// A place that a host may name: the argument, the steps to the place, and
/// the value there.
type Named = (usize, Vec<RuntimeStep>, Value);

/// What a borrow of a payload asks of the arguments: a place of the type
/// `ty` within the argument `argument`, to be borrowed with `mode`.
struct Wanted<'a> {
    program: &'a Program,
    argument: usize,
    mode: BorrowMode,
    ty: &'a Type,
}

impl Wanted<'_> {
    /// The places within `value`, which has the type `ty`, that hold a
    /// value of the wanted type.
    fn within(&self, ty: &Type, value: &Value, steps: &mut Vec<RuntimeStep>, out: &mut Vec<Named>) {
        if ty == self.ty {
            out.push((self.argument, steps.clone(), value.clone()));
        }
        match (ty, value) {
            (Type::Struct(id, _), Value::Struct { fields, .. }) => {
                let definitions = &self.program.structs[*id].fields;
                for (index, (definition, field)) in definitions.iter().zip(fields).enumerate() {
                    steps.push(RuntimeStep::Field(index));
                    self.within(definition.ty.deref_type(), field, steps, out);
                    steps.pop();
                }
            }
            (
                Type::Variant(id, _),
                Value::Variant {
                    constructor,
                    fields,
                    ..
                },
            ) => {
                let definitions = &self.program.variants[*id].constructors[*constructor].fields;
                for (index, (definition, field)) in definitions.iter().zip(fields).enumerate() {
                    steps.push(RuntimeStep::VariantField(*constructor, index));
                    self.within(&definition.ty, field, steps, out);
                    steps.pop();
                }
            }
            (Type::Vector(element), Value::Vector(items)) => {
                for (index, item) in items.iter().enumerate() {
                    steps.push(RuntimeStep::Index(index));
                    self.within(element, item, steps, out);
                    steps.pop();
                }
            }
            (Type::Map(key_ty, element), Value::Map(entries)) => {
                for (key, item) in entries {
                    // A key is lent shared only: a map keeps its keys in
                    // order.
                    if self.mode == BorrowMode::Shared && **key_ty == *self.ty {
                        steps.push(RuntimeStep::MapKey(key.clone()));
                        out.push((self.argument, steps.clone(), key.clone()));
                        steps.pop();
                    }
                    steps.push(RuntimeStep::MapValue(key.clone()));
                    self.within(element, item, steps, out);
                    steps.pop();
                }
            }
            _ => {}
        }
    }

    /// The places that the borrow may refer to within the argument, whose
    /// parameter has the type `ty`: within what the parameter lends, or
    /// what the borrows of a view lend. An exclusive borrow comes only from
    /// what was lent exclusively.
    fn lent(&self, ty: &Type, value: &Value, steps: &mut Vec<RuntimeStep>, out: &mut Vec<Named>) {
        match (ty, value) {
            (Type::Ref(lender, referent), _) => {
                if self.mode == BorrowMode::Shared || *lender == BorrowMode::Exclusive {
                    self.within(referent, value, steps, out);
                }
            }
            (Type::Struct(id, _), Value::Struct { fields, .. })
                if self.program.structs[*id].is_view =>
            {
                let definitions = &self.program.structs[*id].fields;
                for (index, (definition, field)) in definitions.iter().zip(fields).enumerate() {
                    steps.push(RuntimeStep::Field(index));
                    self.lent(&definition.ty, field, steps, out);
                    steps.pop();
                }
            }
            _ => {}
        }
    }
}

/// One call of the seeded host while it answers the borrows of a payload:
/// the places it has named so far, with their modes.
struct Lending<'a> {
    control: &'a Control,
    arguments: &'a [Value],
    config: &'a Config,
    taken: Vec<(BorrowMode, usize, Vec<RuntimeStep>)>,
}

impl Seeded<'_> {
    /// A payload value of the type `ty`, which is or holds a borrow: each
    /// borrow names a place within one of the `origins` ([E-Extern]) that
    /// overlaps no place already named in this payload unless both are
    /// shared ([E-Host]). Returns what the host answers and the same with
    /// each borrow replaced by the value it refers to, for the condition of
    /// the alternative; `None` when the arguments hold no such place.
    fn lend(
        &self,
        rng: &mut Rng,
        lending: &mut Lending<'_>,
        ty: &Type,
        origins: &[usize],
        next_res: &mut u64,
    ) -> Option<(Value, Value)> {
        match ty {
            Type::Ref(mode, wanted) => {
                let mut places = Vec::new();
                for &origin in origins {
                    let wanted = Wanted {
                        program: self.program,
                        argument: origin,
                        mode: *mode,
                        ty: wanted,
                    };
                    wanted.lent(
                        &lending.control.parameters[origin].ty,
                        &lending.arguments[origin],
                        &mut Vec::new(),
                        &mut places,
                    );
                }
                places.retain(|(argument, steps, _)| {
                    !lending
                        .taken
                        .iter()
                        .any(|(other_mode, other, other_steps)| {
                            let shorter = steps.len().min(other_steps.len());
                            other == argument
                                && (*mode == BorrowMode::Exclusive
                                    || *other_mode == BorrowMode::Exclusive)
                                && steps[..shorter] == other_steps[..shorter]
                        })
                });
                if places.is_empty() {
                    return None;
                }
                let (argument, steps, referent) = places.swap_remove(rng.index(places.len()));
                lending.taken.push((*mode, argument, steps.clone()));
                Some((Value::within(*mode, argument, steps), referent))
            }
            Type::Struct(id, name) if self.program.structs[*id].is_view => {
                let mut answered = Vec::new();
                let mut referred = Vec::new();
                for field in &self.program.structs[*id].fields {
                    let (value, referent) = if self.program.contains_borrow_or_view(&field.ty) {
                        self.lend(rng, lending, &field.ty, origins, next_res)?
                    } else {
                        let value = draw_value_in_program(
                            self.program,
                            rng,
                            &field.ty,
                            lending.arguments,
                            lending.config,
                            next_res,
                        )?;
                        (value.clone(), value)
                    };
                    answered.push(value);
                    referred.push(referent);
                }
                let made = |fields| Value::Struct {
                    ty: *id,
                    name: name.clone(),
                    fields,
                };
                Some((made(answered), made(referred)))
            }
            _ => None,
        }
    }
}

impl Host for Seeded<'_> {
    fn call(
        &mut self,
        control: &Control,
        arguments: &[Value],
        config: &Config,
    ) -> Result<Answer, String> {
        let mut rng = if control.is_pure(self.program) {
            let mut words = Vec::with_capacity(4 + control.name.len() + arguments.len() * 3);
            words.push(self.seed);
            words.push(control.name.len() as u64);
            for byte in control.name.as_bytes() {
                words.push(u64::from(*byte));
            }
            for argument in arguments {
                push_value(&mut words, argument);
            }
            Rng::new(mix(&words))
        } else {
            self.rng.fork()
        };
        let count = control.contract.len();
        let start = rng.index(count);
        // A value drawn within the plain bounds of a condition most often
        // satisfies it; whether it does is decided below, by the condition
        // itself.
        let bounds = field_bounds(control, arguments);
        for attempt in 0..192 {
            let which = (start + attempt) % count;
            let alternative = &control.contract[which];
            let mut res_counter = self.next_res;
            let Some(mut payload) = draw_payload(
                self.program,
                &mut rng,
                alternative,
                &bounds[which],
                arguments,
                config,
                &mut res_counter,
            ) else {
                continue;
            };
            // What the host leaves behind an argument lent exclusively is
            // written there before the borrows of the payload are made
            // ([E-Extern]), so they name places in what it leaves.
            let mut writes = Vec::new();
            let mut written = arguments.to_vec();
            if self.writes {
                for (position, parameter) in control.parameters.iter().enumerate() {
                    let Type::Ref(BorrowMode::Exclusive, referent) = &parameter.ty else {
                        continue;
                    };
                    let spoken = alternative.condition.as_ref().is_some_and(|condition| {
                        typed::mentions(condition, VarRef::Parameter(position))
                    });
                    if spoken
                        || self.program.kind(referent) == typed::Kind::Must
                        || self.program.contains_borrow_or_view(referent)
                        || !rng.chance(1, 3)
                    {
                        continue;
                    }
                    let Some(value) = draw_value_in_program(
                        self.program,
                        &mut rng,
                        referent,
                        arguments,
                        config,
                        &mut res_counter,
                    ) else {
                        continue;
                    };
                    written[position] = value.clone();
                    writes.push((position, value));
                }
            }
            // A borrow of the payload names a place within an origin; the
            // condition reads the value there.
            let mut referred = payload.clone();
            let mut lending = Lending {
                control,
                arguments: &written,
                config,
                taken: Vec::new(),
            };
            let mut lent = true;
            for (index, field) in alternative.fields.iter().enumerate() {
                if !self.program.contains_borrow_or_view(&field.ty) {
                    continue;
                }
                match self.lend(
                    &mut rng,
                    &mut lending,
                    &field.ty,
                    &field.origins,
                    &mut res_counter,
                ) {
                    Some((value, referent)) => {
                        payload[index] = value;
                        referred[index] = referent;
                    }
                    None => {
                        lent = false;
                        break;
                    }
                }
            }
            if !lent {
                continue;
            }
            let valid = match &alternative.condition {
                None => true,
                Some(condition) => {
                    signature_holds(self.program, config, condition, arguments, &referred)
                }
            };
            if valid {
                self.next_res = res_counter;
                return Ok(Answer {
                    alternative: alternative.name.clone(),
                    payload,
                    writes,
                });
            }
        }
        Err(format!(
            "no answer found that satisfies the contract of `{}`",
            control.name
        ))
    }

    fn pick_turn(&mut self, ready_count: usize) -> usize {
        self.rng.index(ready_count)
    }

    fn pick_waiting(&mut self, waiting: &[(&Control, &[Value])]) -> usize {
        self.rng.index(waiting.len())
    }
}
