//! The phase 3 checker (`docs/v2/core.md`, section 7; `docs/v2/facts.md`).
//!
//! For each function, named boundary, and defined control of a
//! [`typed::Program`], [`check`] verifies:
//!
//! - **[K1] to [K8]** Live histories, structure `Ω`, loop post-iteration facts
//!   and coverage (`Θ ⊨ ¬Lₙ₊₁`, [K7]).
//! - **[N1] to [N5]** Conditional facts `Ψ`, SSA renaming on mutation and loop
//!   entry, and exact entailment. The checker gives the certificate of every
//!   yes to the kernel, with the goal it asked about, and accepts only what
//!   the kernel validates ([`crate::kernel::Kernel::validate`], [V1]).
//! - **[C2]** Decision acknowledgement (every alternative of the operation's
//!   contract is listed).
//! - **[O0] to [O6]** Ownership and availability (`D(x)` and `M(x)` on
//!   histories: operand order [O0], no double bind [O1], available at use [O2],
//!   move-on-consume and no partial/borrowed moves [O3], no discarded `must`
//!   temporaries [O3a], overwrite/component assignment rules [O4], scope-exit
//!   obligations [O5], outer names across loops [O6]).
//! - **[L1] to [L5], [L2a]** Second-class borrow and view loan checking (loan
//!   creation and inheritance across `&`/`&~`, `view struct`, `∈` contracts,
//!   and borrowed variant decisions [L1]; history-conditioned backward liveness
//!   [L2] and loop cross-iteration liveness [L2a]; place-overlap access
//!   conflicts and scope-end invalidations [L3]; outcome origin escape
//!   checking [L4]; view borrow aggregation [L5]).
//! - **[P1] to [P8]** Proof obligations: `⊢ φ` ([P1]), loop invariants at
//!   entry and `↑` ([P2]), preconditions of functions and controls ([P3]),
//!   contract exit conditions `⇐ φ` with `old(y)` ([P4]), arithmetic bounds,
//!   non-zero divisors, and vector index bounds ([P5]), unreachable `⊥` ([P6]),
//!   left-to-right and short-circuit order ([P7]), and function bodies ([P8]).
//! - **[F1] to [F6]** Fault permissions ([F1]), fault-releasable values at
//!   faulting statements ([F2]), effects within `uses` ([F3]), `assume ⊥`
//!   ([F4]), lexical boundaries ([F5]), and named boundaries ([F6]).

use crate::bdd::{self, Bdd, Formula};
use crate::certificate::{self, Asked};
use crate::facts::{AtomTerm, Certificate, Counterexample, Decision, LinearTerm, Solver, TermId};
use crate::int::Int;
use crate::kernel::Kernel;
use crate::typed::{
    Alternative, Arithmetic, BodyId, BorrowMode, BoundaryDef, BuiltinOp, Command, Comparison,
    Control, ControlBody, ControlId, Expr, Function, FunctionId, IntType, Kind, Operation, Place,
    PlaceStep, Program, Selector, SiteId, StructId, Type, VarId, VarRef,
};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

#[derive(Clone, Debug)]
pub struct Error {
    pub control: String,
    pub line: u32,
    pub clause: &'static str,
    pub message: String,
    pub counterexample: Option<Box<Counterexample>>,
}

impl fmt::Display for Error {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "{}:{}: {} [{}]",
            self.control, self.line, self.message, self.clause
        )?;
        if let Some(cex) = &self.counterexample {
            write!(formatter, " — {cex}")?;
        }
        Ok(())
    }
}

/// An entailment that the kernel has validated ([V1]).
#[derive(Clone, Debug)]
pub struct Proved {
    pub control: String,
    pub line: u32,
    /// The clause that asked.
    pub clause: &'static str,
    /// The position in [`CheckedProgram::bodies`] of the body whose lists
    /// the certificate names.
    pub body: usize,
    /// The negated goal, as the checker gave it to the search and to the
    /// kernel.
    pub goal: Formula,
    pub certificate: Certificate,
}

/// What the check of a program gathers: the entailments proved, each
/// validated by the kernel when it was proved, and the solver of every body
/// as it was at the end, which holds the lists that the certificates name.
#[derive(Default)]
pub struct Proofs {
    proved: Vec<Proved>,
    bodies: Vec<Solver>,
    /// The kernel for the body that is being checked.
    kernel: Kernel,
}

impl Proofs {
    /// Has the kernel validate a certificate against the goal that the
    /// checker asked about, and records it.
    fn accept(
        &mut self,
        solver: &Solver,
        goal: Formula,
        control: &str,
        line: u32,
        clause: &'static str,
        certificate: Certificate,
    ) -> Result<(), String> {
        self.kernel.validate(&solver.query(goal), &certificate)?;
        self.proved.push(Proved {
            control: control.to_string(),
            line,
            clause,
            body: self.bodies.len(),
            goal,
            certificate,
        });
        Ok(())
    }

    /// Ends the check of a body. Its solver is kept for the certificates
    /// that name its lists, and the next body gets a kernel of its own.
    fn close_body(&mut self, solver: Solver) {
        self.bodies.push(solver);
        self.kernel = Kernel::new();
    }
}

#[derive(Clone, Debug)]
pub struct CheckedProgram {
    pub certificates: Vec<Proved>,
    /// The solver of each body that was checked, as it was at the end.
    pub bodies: Vec<Solver>,
    pub warnings: Vec<crate::surface::Warning>,
}

impl CheckedProgram {
    /// Validates every certificate again, with a kernel that has seen
    /// nothing of the check.
    pub fn revalidate(&self) -> Result<(), String> {
        let mut kernels: Vec<Kernel> = self.bodies.iter().map(|_| Kernel::new()).collect();
        for proved in &self.certificates {
            let query = self.bodies[proved.body].query(proved.goal);
            kernels[proved.body]
                .validate(&query, &proved.certificate)
                .map_err(|error| {
                    format!(
                        "{}:{} [{}]: {error}",
                        proved.control, proved.line, proved.clause
                    )
                })?;
        }
        Ok(())
    }

    /// Writes the certificates of every body in the text of [V5]
    /// ([`crate::certificate`]), without the line that begins a text.
    pub fn write_certificates(&self, out: &mut String) -> Result<(), String> {
        for (position, solver) in self.bodies.iter().enumerate() {
            let asked: Vec<Asked> = self
                .certificates
                .iter()
                .filter(|proved| proved.body == position)
                .map(|proved| Asked {
                    control: &proved.control,
                    line: proved.line,
                    clause: proved.clause,
                    goal: proved.goal,
                    certificate: &proved.certificate,
                })
                .collect();
            if !asked.is_empty() {
                let tables = solver.query(crate::bdd::TRUE);
                certificate::write_body(out, &tables, &solver.history_names, &asked)?;
            }
        }
        Ok(())
    }

    /// The text of the certificates of the program.
    pub fn certificate_text(&self) -> Result<String, String> {
        let mut out = format!("{}\n", certificate::HEADER);
        self.write_certificates(&mut out)?;
        Ok(out)
    }
}

/// Checks every function, named boundary, and defined control of `program`.
pub fn check(program: &Program) -> Result<CheckedProgram, Error> {
    let mut certificates = Proofs::default();
    let mut warnings = Vec::new();
    for (id, function) in program.functions.iter().enumerate() {
        check_function(program, id, function, &mut certificates)?;
    }
    let mut boundary_may_fault: Vec<bool> =
        program.boundaries.iter().map(|b| b.may_fault).collect();
    for (bid, boundary) in program.boundaries.iter().enumerate() {
        let may_fault = check_boundary(
            program,
            boundary,
            &boundary_may_fault,
            &mut certificates,
            &mut warnings,
        )?;
        boundary_may_fault[bid] = may_fault;
    }
    for control in &program.controls {
        if control.body.is_some() {
            check_control(
                program,
                control,
                &boundary_may_fault,
                &mut certificates,
                &mut warnings,
            )?;
        }
    }
    Ok(CheckedProgram {
        certificates: certificates.proved,
        bodies: certificates.bodies,
        warnings,
    })
}

#[derive(Clone)]
struct Env {
    locals: BTreeMap<VarId, LinearTerm>,
    parameters: Vec<LinearTerm>,
    old_parameters: Vec<LinearTerm>,
    fields: Vec<LinearTerm>,
    constants: BTreeMap<VarId, Int>,
}

impl Env {
    fn lookup(&self, var: VarRef) -> LinearTerm {
        match var {
            VarRef::Local(id) => self
                .locals
                .get(&id)
                .cloned()
                .unwrap_or_else(|| LinearTerm::from_i128(0)),
            VarRef::Parameter(idx) => self
                .parameters
                .get(idx)
                .cloned()
                .unwrap_or_else(|| LinearTerm::from_i128(0)),
            VarRef::Field(idx) => self
                .fields
                .get(idx)
                .cloned()
                .unwrap_or_else(|| LinearTerm::from_i128(0)),
        }
    }

    fn lookup_old(&self, idx: usize) -> LinearTerm {
        self.old_parameters
            .get(idx)
            .cloned()
            .unwrap_or_else(|| LinearTerm::from_i128(0))
    }
}

fn subst_place(place: &Place, args: &[Expr]) -> Place {
    Place {
        root: place.root,
        root_ty: place.root_ty.clone(),
        steps: place
            .steps
            .iter()
            .map(|step| match step {
                PlaceStep::Field(sid, fidx, ty) => PlaceStep::Field(*sid, *fidx, ty.clone()),
                PlaceStep::Index(idx, ty) => {
                    PlaceStep::Index(subst_parameters(idx, args), ty.clone())
                }
            })
            .collect(),
        ty: place.ty.clone(),
    }
}

fn unfold_place(program: &Program, place: &Place) -> Place {
    Place {
        root: place.root,
        root_ty: place.root_ty.clone(),
        steps: place
            .steps
            .iter()
            .map(|step| match step {
                PlaceStep::Field(sid, fidx, ty) => PlaceStep::Field(*sid, *fidx, ty.clone()),
                PlaceStep::Index(idx, ty) => {
                    PlaceStep::Index(unfold_functions(program, idx), ty.clone())
                }
            })
            .collect(),
        ty: place.ty.clone(),
    }
}

/// Unfolds non-recursive function calls in `expr` ([I8]).
fn unfold_functions(program: &Program, expr: &Expr) -> Expr {
    match expr {
        Expr::Boolean(_)
        | Expr::Integer(_, _)
        | Expr::String(_)
        | Expr::Var(_, _)
        | Expr::Old(_, _)
        | Expr::EmptyMap(_)
        | Expr::TasksEmpty(_, _)
        | Expr::Count(_) => expr.clone(),
        Expr::Move(inner, ty) => Expr::Move(Box::new(unfold_functions(program, inner)), ty.clone()),
        Expr::Borrow(mode, place, ty) => {
            Expr::Borrow(*mode, unfold_place(program, place), ty.clone())
        }
        Expr::Field(base, sid, fidx, ty) => Expr::Field(
            Box::new(unfold_functions(program, base)),
            *sid,
            *fidx,
            ty.clone(),
        ),
        Expr::Index(base, idx, ty) => Expr::Index(
            Box::new(unfold_functions(program, base)),
            Box::new(unfold_functions(program, idx)),
            ty.clone(),
        ),
        Expr::Struct(sid, args, ty) => Expr::Struct(
            *sid,
            args.iter().map(|a| unfold_functions(program, a)).collect(),
            ty.clone(),
        ),
        Expr::Variant(vid, cidx, args, ty) => Expr::Variant(
            *vid,
            *cidx,
            args.iter().map(|a| unfold_functions(program, a)).collect(),
            ty.clone(),
        ),
        Expr::Vector(args, ty) => Expr::Vector(
            args.iter().map(|a| unfold_functions(program, a)).collect(),
            ty.clone(),
        ),
        Expr::Len(inner) => Expr::Len(Box::new(unfold_functions(program, inner))),
        Expr::Clone(inner, ty) => {
            Expr::Clone(Box::new(unfold_functions(program, inner)), ty.clone())
        }
        Expr::Trim(inner) => Expr::Trim(Box::new(unfold_functions(program, inner))),
        Expr::Negate(inner, ty) => Expr::Negate(Box::new(unfold_functions(program, inner)), *ty),
        Expr::Not(inner) => Expr::Not(Box::new(unfold_functions(program, inner))),
        Expr::Arithmetic(op, l, r, ty) => Expr::Arithmetic(
            *op,
            Box::new(unfold_functions(program, l)),
            Box::new(unfold_functions(program, r)),
            *ty,
        ),
        Expr::Compare(cmp, l, r) => Expr::Compare(
            *cmp,
            Box::new(unfold_functions(program, l)),
            Box::new(unfold_functions(program, r)),
        ),
        Expr::And(l, r) => Expr::And(
            Box::new(unfold_functions(program, l)),
            Box::new(unfold_functions(program, r)),
        ),
        Expr::Or(l, r) => Expr::Or(
            Box::new(unfold_functions(program, l)),
            Box::new(unfold_functions(program, r)),
        ),
        Expr::Call(fn_id, args, _) => {
            let unfolded_args: Vec<Expr> =
                args.iter().map(|a| unfold_functions(program, a)).collect();
            let body = subst_parameters(&program.functions[*fn_id].body, &unfolded_args);
            unfold_functions(program, &body)
        }
    }
}

fn subst_parameters(expr: &Expr, args: &[Expr]) -> Expr {
    match expr {
        Expr::Boolean(_)
        | Expr::Integer(_, _)
        | Expr::String(_)
        | Expr::Old(_, _)
        | Expr::EmptyMap(_)
        | Expr::TasksEmpty(_, _)
        | Expr::Count(_) => expr.clone(),
        Expr::Var(VarRef::Parameter(idx), _) => args[*idx].clone(),
        Expr::Var(_, _) => expr.clone(),
        Expr::Move(inner, ty) => Expr::Move(Box::new(subst_parameters(inner, args)), ty.clone()),
        Expr::Borrow(mode, place, ty) => Expr::Borrow(*mode, subst_place(place, args), ty.clone()),
        Expr::Field(base, sid, fidx, ty) => Expr::Field(
            Box::new(subst_parameters(base, args)),
            *sid,
            *fidx,
            ty.clone(),
        ),
        Expr::Index(base, idx, ty) => Expr::Index(
            Box::new(subst_parameters(base, args)),
            Box::new(subst_parameters(idx, args)),
            ty.clone(),
        ),
        Expr::Struct(sid, items, ty) => Expr::Struct(
            *sid,
            items.iter().map(|a| subst_parameters(a, args)).collect(),
            ty.clone(),
        ),
        Expr::Variant(vid, cidx, items, ty) => Expr::Variant(
            *vid,
            *cidx,
            items.iter().map(|a| subst_parameters(a, args)).collect(),
            ty.clone(),
        ),
        Expr::Vector(items, ty) => Expr::Vector(
            items.iter().map(|a| subst_parameters(a, args)).collect(),
            ty.clone(),
        ),
        Expr::Len(inner) => Expr::Len(Box::new(subst_parameters(inner, args))),
        Expr::Clone(inner, ty) => Expr::Clone(Box::new(subst_parameters(inner, args)), ty.clone()),
        Expr::Trim(inner) => Expr::Trim(Box::new(subst_parameters(inner, args))),
        Expr::Negate(inner, ty) => Expr::Negate(Box::new(subst_parameters(inner, args)), *ty),
        Expr::Not(inner) => Expr::Not(Box::new(subst_parameters(inner, args))),
        Expr::Arithmetic(op, l, r, ty) => Expr::Arithmetic(
            *op,
            Box::new(subst_parameters(l, args)),
            Box::new(subst_parameters(r, args)),
            *ty,
        ),
        Expr::Compare(cmp, l, r) => Expr::Compare(
            *cmp,
            Box::new(subst_parameters(l, args)),
            Box::new(subst_parameters(r, args)),
        ),
        Expr::And(l, r) => Expr::And(
            Box::new(subst_parameters(l, args)),
            Box::new(subst_parameters(r, args)),
        ),
        Expr::Or(l, r) => Expr::Or(
            Box::new(subst_parameters(l, args)),
            Box::new(subst_parameters(r, args)),
        ),
        Expr::Call(id, call_args, ty) => Expr::Call(
            *id,
            call_args
                .iter()
                .map(|a| subst_parameters(a, args))
                .collect(),
            ty.clone(),
        ),
    }
}

/// Evaluates a constant integer expression ([I3]).
fn eval_const(program: &Program, expr: &Expr, constants: &BTreeMap<VarId, Int>) -> Option<Int> {
    let unfolded = unfold_functions(program, expr);
    eval_const_unfolded(&unfolded, constants)
}

fn eval_const_unfolded(expr: &Expr, constants: &BTreeMap<VarId, Int>) -> Option<Int> {
    match expr {
        Expr::Integer(n, _) => Some(n.clone()),
        Expr::Var(VarRef::Local(id), _) => constants.get(id).cloned(),
        Expr::Negate(inner, _) => Some(eval_const_unfolded(inner, constants)?.negate()),
        Expr::Arithmetic(op, l, r, _) => {
            let a = eval_const_unfolded(l, constants)?;
            let b = eval_const_unfolded(r, constants)?;
            match op {
                Arithmetic::Add => Some(a.plus(&b)),
                Arithmetic::Subtract => Some(a.minus(&b)),
                Arithmetic::Multiply => Some(a.times(&b)),
                Arithmetic::Divide => Some(a.divide(&b)?.0),
                Arithmetic::Remainder => Some(a.divide(&b)?.1),
            }
        }
        _ => None,
    }
}

fn int_bounds_for_type(ty: &Type) -> (Option<Int>, Option<Int>) {
    match ty.deref_type() {
        Type::Int(IntType::Usize) => (Some(Int::zero()), None),
        Type::Int(int_ty) => {
            let (lo, hi) = int_ty.literal_bounds();
            (Some(lo), Some(hi))
        }
        _ => (None, None),
    }
}

/// Computes the declared interval `[low, high]` of an unfolded integer
/// expression for `[A9]`.
fn interval_unfolded(expr: &Expr, constants: &BTreeMap<VarId, Int>) -> (Option<Int>, Option<Int>) {
    if let Some(c) = eval_const_unfolded(expr, constants) {
        return (Some(c.clone()), Some(c));
    }
    match expr {
        Expr::Integer(n, _) => (Some(n.clone()), Some(n.clone())),
        Expr::Var(_, ty) | Expr::Old(_, ty) => int_bounds_for_type(ty),
        Expr::Move(inner, _) | Expr::Clone(inner, _) => interval_unfolded(inner, constants),
        Expr::Borrow(_, place, _) => int_bounds_for_type(&place.ty),
        Expr::Len(_) => (Some(Int::zero()), None),
        Expr::Field(base, _, _, ty) => {
            if matches!(&**base, Expr::Struct(_, _, _)) {
                (None, None)
            } else {
                int_bounds_for_type(ty)
            }
        }
        Expr::Index(base, _, ty) => {
            if matches!(&**base, Expr::Vector(_, _)) {
                (None, None)
            } else {
                int_bounds_for_type(ty)
            }
        }
        Expr::Negate(inner, _) => {
            let (lo, hi) = interval_unfolded(inner, constants);
            (hi.map(|h| h.negate()), lo.map(|l| l.negate()))
        }
        Expr::Arithmetic(Arithmetic::Add, l, r, _) => {
            let (l1, h1) = interval_unfolded(l, constants);
            let (l2, h2) = interval_unfolded(r, constants);
            (
                l1.zip(l2).map(|(a, b)| a.plus(&b)),
                h1.zip(h2).map(|(a, b)| a.plus(&b)),
            )
        }
        Expr::Arithmetic(Arithmetic::Subtract, l, r, _) => {
            let (l1, h1) = interval_unfolded(l, constants);
            let (l2, h2) = interval_unfolded(r, constants);
            (
                l1.zip(h2).map(|(a, b)| a.minus(&b)),
                h1.zip(l2).map(|(a, b)| a.minus(&b)),
            )
        }
        Expr::Arithmetic(Arithmetic::Multiply, l, r, _) => {
            // A multiple by a literal keeps the ends that its operand has.
            let multiple = |factor: Int, operand: &Expr| {
                let (low, high) = interval_unfolded(operand, constants);
                let low = low.map(|end| end.times(&factor));
                let high = high.map(|end| end.times(&factor));
                if factor.is_zero() {
                    (Some(Int::zero()), Some(Int::zero()))
                } else if factor.is_negative() {
                    (high, low)
                } else {
                    (low, high)
                }
            };
            if let Some(factor) = eval_const_unfolded(l, constants) {
                return multiple(factor, r);
            }
            if let Some(factor) = eval_const_unfolded(r, constants) {
                return multiple(factor, l);
            }
            let (l1, h1) = interval_unfolded(l, constants);
            let (l2, h2) = interval_unfolded(r, constants);
            if let (Some(a), Some(big_a), Some(b), Some(big_b)) = (l1, h1, l2, h2) {
                let p1 = a.times(&b);
                let p2 = a.times(&big_b);
                let p3 = big_a.times(&b);
                let p4 = big_a.times(&big_b);
                let min = p1.clone().min(p2.clone()).min(p3.clone()).min(p4.clone());
                let max = p1.max(p2).max(p3).max(p4);
                (Some(min), Some(max))
            } else {
                (None, None)
            }
        }
        Expr::Arithmetic(Arithmetic::Divide, l, r, _) => {
            if let Some(k) = eval_const_unfolded(r, constants)
                && !k.is_zero()
            {
                let (l1, h1) = interval_unfolded(l, constants);
                if !k.is_negative() {
                    (
                        l1.map(|a| a.divide(&k).unwrap().0),
                        h1.map(|b| b.divide(&k).unwrap().0),
                    )
                } else {
                    (
                        h1.map(|b| b.divide(&k).unwrap().0),
                        l1.map(|a| a.divide(&k).unwrap().0),
                    )
                }
            } else {
                (None, None)
            }
        }
        Expr::Arithmetic(Arithmetic::Remainder, l, r, _) => {
            if let Some(k) = eval_const_unfolded(r, constants)
                && !k.is_zero()
            {
                let (l1, h1) = interval_unfolded(l, constants);
                let abs_k = if k.is_negative() { k.negate() } else { k };
                let max_rem = abs_k.minus(&Int::from_u64(1));
                let lo = if l1.as_ref().is_some_and(|a| !a.is_negative()) {
                    Int::zero()
                } else {
                    max_rem.negate()
                };
                let hi = if h1.as_ref().is_some_and(|b| *b <= Int::zero()) {
                    Int::zero()
                } else {
                    max_rem
                };
                (Some(lo), Some(hi))
            } else {
                (None, None)
            }
        }
        _ => (None, None),
    }
}

fn int_and_bool_info(ty: &Type) -> (Option<IntType>, bool) {
    match ty.deref_type() {
        Type::Int(it) => (Some(*it), false),
        Type::Bool => (None, true),
        _ => (None, false),
    }
}

fn translate_field_term(
    solver: &mut Solver,
    base: LinearTerm,
    sid: StructId,
    fidx: usize,
    fty: &Type,
) -> LinearTerm {
    if let Some(bid) = base.as_var()
        && let AtomTerm::StructCtor(c_sid, fields) = &solver.terms[bid]
        && *c_sid == sid
        && fidx < fields.len()
    {
        return fields[fidx].clone();
    }
    let (int_ty, is_bool) = int_and_bool_info(fty);
    let is_value_term = solver.is_value_term_linear(&base);
    let id = solver.intern_term(AtomTerm::Field {
        base,
        struct_id: sid,
        field_idx: fidx,
        int_ty,
        is_bool,
        is_value_term,
    });
    solver.register_sort(id, fty.deref_type());
    solver.instantiate_all();
    LinearTerm::var(id)
}

fn translate_index_term(
    solver: &mut Solver,
    base: LinearTerm,
    index: LinearTerm,
    ety: &Type,
) -> LinearTerm {
    let (int_ty, is_bool) = int_and_bool_info(ety);
    let is_value_term = solver.is_value_term_linear(&base);
    let id = solver.intern_term(AtomTerm::Index {
        base,
        index,
        int_ty,
        is_bool,
        is_value_term,
    });
    solver.register_sort(id, ety.deref_type());
    solver.instantiate_all();
    LinearTerm::var(id)
}

fn translate_place(program: &Program, solver: &mut Solver, place: &Place, env: &Env) -> LinearTerm {
    let mut cur = env.lookup(VarRef::Local(place.root));
    for step in &place.steps {
        match step {
            PlaceStep::Field(sid, fidx, fty) => {
                cur = translate_field_term(solver, cur, *sid, *fidx, fty);
            }
            PlaceStep::Index(idx_expr, ety) => {
                let idx_term = translate_term(program, solver, idx_expr, env);
                cur = translate_index_term(solver, cur, idx_term, ety);
            }
        }
    }
    cur
}

/// Computes `upd(root_term, steps, new_val)` per `[I9]`.
fn functional_update(
    program: &Program,
    solver: &mut Solver,
    cur_term: LinearTerm,
    cur_ty: &Type,
    steps: &[PlaceStep],
    new_val: LinearTerm,
    env: &Env,
) -> LinearTerm {
    let Some((first, rest)) = steps.split_first() else {
        return new_val;
    };
    match first {
        PlaceStep::Field(sid, fidx, fty) => {
            let sdef = &program.structs[*sid];
            let sub_old = translate_field_term(solver, cur_term.clone(), *sid, *fidx, fty);
            let updated_field =
                functional_update(program, solver, sub_old, fty, rest, new_val, env);
            let mut fields = Vec::with_capacity(sdef.fields.len());
            for (idx, field_param) in sdef.fields.iter().enumerate() {
                if idx == *fidx {
                    fields.push(updated_field.clone());
                } else {
                    fields.push(translate_field_term(
                        solver,
                        cur_term.clone(),
                        *sid,
                        idx,
                        &field_param.ty,
                    ));
                }
            }
            let cid = solver.intern_term(AtomTerm::StructCtor(*sid, fields));
            solver.register_sort(cid, cur_ty.deref_type());
            solver.instantiate_all();
            LinearTerm::var(cid)
        }
        PlaceStep::Index(idx_expr, ety) => {
            let idx_term = translate_term(program, solver, idx_expr, env);
            let sub_old = translate_index_term(solver, cur_term.clone(), idx_term.clone(), ety);
            let updated_elem = functional_update(program, solver, sub_old, ety, rest, new_val, env);
            let uid = solver.intern_term(AtomTerm::Update {
                base: cur_term,
                index: idx_term,
                value: updated_elem,
            });
            solver.register_sort(uid, cur_ty.deref_type());
            solver.instantiate_all();
            LinearTerm::var(uid)
        }
    }
}

fn ensure_struct_fields(program: &Program, solver: &mut Solver, sid: StructId, term: &LinearTerm) {
    if let Some(tid) = term.as_var()
        && matches!(solver.terms[tid], AtomTerm::StructCtor(_, _))
    {
        return;
    }
    for (fidx, field) in program.structs[sid].fields.iter().enumerate() {
        let _ = translate_field_term(solver, term.clone(), sid, fidx, &field.ty);
    }
}

/// Translates `expr` into a [`LinearTerm`] in `solver` ([I1] to [I13]).
fn translate_term(program: &Program, solver: &mut Solver, expr: &Expr, env: &Env) -> LinearTerm {
    let unfolded = unfold_functions(program, expr);
    if let Some(c) = eval_const_unfolded(&unfolded, &env.constants) {
        return LinearTerm::constant(c);
    }
    match &unfolded {
        Expr::Boolean(b) => LinearTerm::from_i128(i128::from(*b)),
        Expr::Integer(n, _) => LinearTerm::constant(n.clone()),
        Expr::String(s) => {
            let id = solver.intern_term(AtomTerm::StrLit(s.clone()));
            solver.register_sort(id, &Type::String);
            solver.instantiate_all();
            LinearTerm::var(id)
        }
        Expr::Var(vr, _) => env.lookup(*vr),
        Expr::Old(idx, _) => env.lookup_old(*idx),
        Expr::Move(inner, _) | Expr::Clone(inner, _) => translate_term(program, solver, inner, env),
        Expr::Borrow(_, place, _) => translate_place(program, solver, place, env),
        Expr::Field(base, sid, fidx, fty) => {
            let bt = translate_term(program, solver, base, env);
            translate_field_term(solver, bt, *sid, *fidx, fty)
        }
        Expr::Index(base, idx, ety) => {
            let bt = translate_term(program, solver, base, env);
            let it = translate_term(program, solver, idx, env);
            translate_index_term(solver, bt, it, ety)
        }
        Expr::Struct(sid, items, ty) => {
            let fields: Vec<LinearTerm> = items
                .iter()
                .map(|item| translate_term(program, solver, item, env))
                .collect();
            let id = solver.intern_term(AtomTerm::StructCtor(*sid, fields));
            solver.register_sort(id, ty);
            solver.instantiate_all();
            LinearTerm::var(id)
        }
        Expr::Variant(vid, cidx, items, ty) => {
            let fields: Vec<LinearTerm> = items
                .iter()
                .map(|item| translate_term(program, solver, item, env))
                .collect();
            let num_ctors = program.variants[*vid].constructors.len();
            let id = solver.intern_term(AtomTerm::VariantCtor {
                variant_id: *vid,
                ctor_idx: *cidx,
                fields,
                num_ctors,
            });
            solver.register_sort(id, ty);
            solver.instantiate_all();
            LinearTerm::var(id)
        }
        Expr::Vector(items, ty) => {
            let elems: Vec<LinearTerm> = items
                .iter()
                .map(|item| translate_term(program, solver, item, env))
                .collect();
            let id = solver.intern_term(AtomTerm::VecLit(elems));
            solver.register_sort(id, ty);
            solver.instantiate_all();
            LinearTerm::var(id)
        }
        Expr::EmptyMap(ty) => {
            let id = solver.intern_term(AtomTerm::EmptyMap);
            solver.register_sort(id, ty);
            solver.instantiate_all();
            LinearTerm::var(id)
        }
        Expr::TasksEmpty(_, _) | Expr::Count(_) => LinearTerm::from_i128(0),
        Expr::Len(inner) => {
            let bt = translate_term(program, solver, inner, env);
            let id = solver.intern_term(AtomTerm::Len(bt));
            solver.instantiate_all();
            LinearTerm::var(id)
        }
        Expr::Trim(inner) => {
            let bt = translate_term(program, solver, inner, env);
            let id = solver.intern_term(AtomTerm::Trim(bt));
            solver.register_sort(id, &Type::String);
            solver.instantiate_all();
            LinearTerm::var(id)
        }
        Expr::Negate(inner, _) => translate_term(program, solver, inner, env).negate(),
        Expr::Arithmetic(Arithmetic::Add, l, r, _) => {
            let tl = translate_term(program, solver, l, env);
            let tr = translate_term(program, solver, r, env);
            tl.add(&tr)
        }
        Expr::Arithmetic(Arithmetic::Subtract, l, r, _) => {
            let tl = translate_term(program, solver, l, env);
            let tr = translate_term(program, solver, r, env);
            tl.sub(&tr)
        }
        Expr::Arithmetic(Arithmetic::Multiply, l, r, _) => {
            if let Some(k) = eval_const_unfolded(l, &env.constants) {
                return translate_term(program, solver, r, env).scale(&k);
            }
            if let Some(k) = eval_const_unfolded(r, &env.constants) {
                return translate_term(program, solver, l, env).scale(&k);
            }
            let tl = translate_term(program, solver, l, env);
            let tr = translate_term(program, solver, r, env);
            let bl = interval_unfolded(l, &env.constants);
            let br = interval_unfolded(r, &env.constants);
            let ((left, left_bounds), (right, right_bounds)) = if tl <= tr {
                ((tl, bl), (tr, br))
            } else {
                ((tr, br), (tl, bl))
            };
            let id = solver.intern_term(AtomTerm::Mul {
                left,
                right,
                left_bounds,
                right_bounds,
            });
            solver.instantiate_all();
            LinearTerm::var(id)
        }
        Expr::Arithmetic(Arithmetic::Divide, l, r, _) => {
            let tl = translate_term(program, solver, l, env);
            if let Some(k) = eval_const_unfolded(r, &env.constants)
                && !k.is_zero()
            {
                let abs_k = if k.is_negative() {
                    k.negate()
                } else {
                    k.clone()
                };
                if abs_k == Int::from_u64(1) {
                    return if k.is_negative() { tl.negate() } else { tl };
                }
                let id = solver.intern_term(AtomTerm::DivConst(tl, abs_k));
                solver.instantiate_all();
                let q = LinearTerm::var(id);
                return if k.is_negative() { q.negate() } else { q };
            }
            let tr = translate_term(program, solver, r, env);
            let id = solver.intern_term(AtomTerm::Div(tl, tr));
            solver.instantiate_all();
            LinearTerm::var(id)
        }
        Expr::Arithmetic(Arithmetic::Remainder, l, r, _) => {
            let tl = translate_term(program, solver, l, env);
            if let Some(k) = eval_const_unfolded(r, &env.constants)
                && !k.is_zero()
            {
                let abs_k = if k.is_negative() { k.negate() } else { k };
                if abs_k == Int::from_u64(1) {
                    return LinearTerm::from_i128(0);
                }
                let id = solver.intern_term(AtomTerm::DivConst(tl.clone(), abs_k.clone()));
                solver.instantiate_all();
                let q = LinearTerm::var(id);
                return tl.sub(&q.scale(&abs_k));
            }
            let tr = translate_term(program, solver, r, env);
            let id = solver.intern_term(AtomTerm::Rem(tl, tr));
            solver.instantiate_all();
            LinearTerm::var(id)
        }
        // [I13]: A Boolean formula used where a value term is needed.
        Expr::Not(_) | Expr::Compare(_, _, _) | Expr::And(_, _) | Expr::Or(_, _) => {
            let phi = translate_formula(program, solver, &unfolded, env);
            let b_id = solver.fresh_var("_bool".to_string(), None, false);
            let b_term = LinearTerm::var(b_id);
            let ge_0 = solver.le(&LinearTerm::from_i128(0), &b_term);
            let le_1 = solver.le(&b_term, &LinearTerm::from_i128(1));
            let range = solver.bdd.and(ge_0, le_1);
            solver.add_fact(bdd::TRUE, range);
            solver.add_def_bool(bdd::TRUE, b_id, phi);
            b_term
        }
        Expr::Call(_, _, _) => unreachable!("unfolded above"),
    }
}

/// Translates a Boolean expression or formula into a BDD [`Formula`] ([S4],
/// [I6], [I8]).
fn translate_formula(program: &Program, solver: &mut Solver, expr: &Expr, env: &Env) -> Formula {
    let unfolded = unfold_functions(program, expr);
    match &unfolded {
        Expr::Boolean(true) => bdd::TRUE,
        Expr::Boolean(false) => bdd::FALSE,
        Expr::Var(_, _)
        | Expr::Old(_, _)
        | Expr::Move(_, _)
        | Expr::Clone(_, _)
        | Expr::Borrow(_, _, _)
        | Expr::Field(_, _, _, _)
        | Expr::Index(_, _, _) => {
            let term = translate_term(program, solver, &unfolded, env);
            solver.le(&LinearTerm::from_i128(1), &term)
        }
        Expr::Not(inner) => {
            let f = translate_formula(program, solver, inner, env);
            solver.bdd.not(f)
        }
        Expr::And(l, r) => {
            let fl = translate_formula(program, solver, l, env);
            let fr = translate_formula(program, solver, r, env);
            solver.bdd.and(fl, fr)
        }
        Expr::Or(l, r) => {
            let fl = translate_formula(program, solver, l, env);
            let fr = translate_formula(program, solver, r, env);
            solver.bdd.or(fl, fr)
        }
        Expr::Compare(cmp, l, r) => {
            if *l.ty().deref_type() == Type::Bool {
                let fl = translate_formula(program, solver, l, env);
                let fr = translate_formula(program, solver, r, env);
                let iff = solver.bdd.iff(fl, fr);
                match cmp {
                    Comparison::Equal => iff,
                    Comparison::NotEqual => solver.bdd.not(iff),
                    _ => bdd::FALSE,
                }
            } else {
                let tl = translate_term(program, solver, l, env);
                let tr = translate_term(program, solver, r, env);
                if let Type::Struct(sid, _) = l.ty().deref_type()
                    && matches!(cmp, Comparison::Equal | Comparison::NotEqual)
                {
                    ensure_struct_fields(program, solver, *sid, &tl);
                    ensure_struct_fields(program, solver, *sid, &tr);
                }
                match cmp {
                    Comparison::Equal => solver.eq(&tl, &tr),
                    Comparison::NotEqual => solver.ne(&tl, &tr),
                    Comparison::Less => solver.lt(&tl, &tr),
                    Comparison::LessEqual => solver.le(&tl, &tr),
                    Comparison::Greater => solver.lt(&tr, &tl),
                    Comparison::GreaterEqual => solver.le(&tr, &tl),
                }
            }
        }
        _ => bdd::FALSE,
    }
}

/// What is reported when the count of steps of [J6] runs out. It is not a
/// verdict on the program.
fn limit_message(steps: u64, about: &str) -> String {
    format!("the compiler's limit of {steps} steps was reached before this was decided: {about}")
}

/// What is reported when the decision procedure contradicts itself ([M1]).
fn fault_message(fault: &str, about: &str) -> String {
    format!("a defect of the compiler: {fault}; it arose while deciding: {about}")
}

/// Proves that `negated_goal` is unsatisfiable under `solver`, validates the
/// resulting [`Certificate`] in the kernel ([`Proofs::accept`], [V1]), and
/// records it.
#[allow(clippy::too_many_arguments)]
fn require_entailment(
    solver: &mut Solver,
    negated_goal: Formula,
    control: &str,
    line: u32,
    clause: &'static str,
    message: impl Into<String>,
    visible_vars: &[(String, TermId, bool)],
    in_loop: bool,
    certificates: &mut Proofs,
) -> Result<(), Error> {
    match solver.decide(negated_goal, visible_vars, in_loop) {
        Decision::Proved(cert) => certificates
            .accept(solver, negated_goal, control, line, clause, cert)
            .map_err(|kernel_err| Error {
                control: control.to_string(),
                line,
                clause: "V1",
                message: format!("certificate rejected by the kernel: {kernel_err}"),
                counterexample: None,
            }),
        Decision::Refuted(cex) => Err(Error {
            control: control.to_string(),
            line,
            clause,
            message: message.into(),
            counterexample: Some(cex),
        }),
        Decision::Limit { steps } => Err(Error {
            control: control.to_string(),
            line,
            clause: "J6",
            message: limit_message(steps, &message.into()),
            counterexample: None,
        }),
        Decision::Fault(fault) => Err(Error {
            control: control.to_string(),
            line,
            clause: "M1",
            message: fault_message(&fault, &message.into()),
            counterexample: None,
        }),
    }
}

/// Checks `Θ; guard ⊨ goal` ([N2]).
#[allow(clippy::too_many_arguments)]
fn require_formula(
    solver: &mut Solver,
    guard: Formula,
    goal: Formula,
    control: &str,
    line: u32,
    clause: &'static str,
    message: impl Into<String>,
    visible_vars: &[(String, TermId, bool)],
    in_loop: bool,
    certificates: &mut Proofs,
) -> Result<(), Error> {
    let not_goal = solver.bdd.not(goal);
    let negated = solver.bdd.and(guard, not_goal);
    require_entailment(
        solver,
        negated,
        control,
        line,
        clause,
        message,
        visible_vars,
        in_loop,
        certificates,
    )
}

fn type_range_formula(solver: &mut Solver, term: &LinearTerm, ty: IntType) -> Formula {
    if ty == IntType::Usize {
        let low = solver.le(&LinearTerm::from_i128(0), term);
        let umax = LinearTerm::var(solver.usize_max_term);
        let high = solver.le(term, &umax);
        solver.bdd.and(low, high)
    } else {
        let (lo, hi) = ty.literal_bounds();
        let low = solver.le(&LinearTerm::constant(lo), term);
        let high = solver.le(term, &LinearTerm::constant(hi));
        solver.bdd.and(low, high)
    }
}

#[allow(clippy::too_many_arguments)]
fn check_index_bounds(
    solver: &mut Solver,
    base_term: &LinearTerm,
    idx_term: &LinearTerm,
    guard: Formula,
    control: &str,
    line: u32,
    visible_vars: &[(String, TermId, bool)],
    in_loop: bool,
    certificates: &mut Proofs,
) -> Result<(), Error> {
    let len_id = solver.intern_term(AtomTerm::Len(base_term.clone()));
    solver.instantiate_all();
    let len_term = LinearTerm::var(len_id);
    let ge_zero = solver.le(&LinearTerm::from_i128(0), idx_term);
    let lt_len = solver.lt(idx_term, &len_term);
    let in_bounds = solver.bdd.and(ge_zero, lt_len);
    require_formula(
        solver,
        guard,
        in_bounds,
        control,
        line,
        "P5",
        "vector index may be out of bounds",
        visible_vars,
        in_loop,
        certificates,
    )?;
    solver.add_fact(guard, in_bounds);
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn check_place_obligations(
    program: &Program,
    solver: &mut Solver,
    place: &Place,
    guard: Formula,
    env: &Env,
    control: &str,
    line: u32,
    visible_vars: &[(String, TermId, bool)],
    in_loop: bool,
    certificates: &mut Proofs,
) -> Result<(), Error> {
    let mut cur = env.lookup(VarRef::Local(place.root));
    for step in &place.steps {
        match step {
            PlaceStep::Field(sid, fidx, fty) => {
                cur = translate_field_term(solver, cur, *sid, *fidx, fty);
            }
            PlaceStep::Index(idx_expr, ety) => {
                check_expr_obligations(
                    program,
                    solver,
                    idx_expr,
                    guard,
                    env,
                    control,
                    line,
                    visible_vars,
                    in_loop,
                    certificates,
                )?;
                let idx_term = translate_term(program, solver, idx_expr, env);
                check_index_bounds(
                    solver,
                    &cur,
                    &idx_term,
                    guard,
                    control,
                    line,
                    visible_vars,
                    in_loop,
                    certificates,
                )?;
                cur = translate_index_term(solver, cur, idx_term, ety);
            }
        }
    }
    Ok(())
}

/// Checks `[P5]` (arithmetic range, non-zero divisor, vector index bounds) and
/// `[P3]` (function preconditions) for `expr` under history guard `guard`, in
/// the evaluation order of `[P7]` and `[E-Bool]`.
#[allow(clippy::too_many_arguments)]
fn check_expr_obligations(
    program: &Program,
    solver: &mut Solver,
    expr: &Expr,
    guard: Formula,
    env: &Env,
    control: &str,
    line: u32,
    visible_vars: &[(String, TermId, bool)],
    in_loop: bool,
    certificates: &mut Proofs,
) -> Result<(), Error> {
    match expr {
        Expr::Boolean(_)
        | Expr::Integer(_, _)
        | Expr::String(_)
        | Expr::Var(_, _)
        | Expr::Old(_, _)
        | Expr::EmptyMap(_)
        | Expr::TasksEmpty(_, _)
        | Expr::Count(_) => Ok(()),
        Expr::Move(inner, _)
        | Expr::Field(inner, _, _, _)
        | Expr::Len(inner)
        | Expr::Clone(inner, _)
        | Expr::Trim(inner)
        | Expr::Not(inner) => check_expr_obligations(
            program,
            solver,
            inner,
            guard,
            env,
            control,
            line,
            visible_vars,
            in_loop,
            certificates,
        ),
        Expr::Borrow(_, place, _) => check_place_obligations(
            program,
            solver,
            place,
            guard,
            env,
            control,
            line,
            visible_vars,
            in_loop,
            certificates,
        ),
        Expr::Index(base, idx, _) => {
            check_expr_obligations(
                program,
                solver,
                base,
                guard,
                env,
                control,
                line,
                visible_vars,
                in_loop,
                certificates,
            )?;
            check_expr_obligations(
                program,
                solver,
                idx,
                guard,
                env,
                control,
                line,
                visible_vars,
                in_loop,
                certificates,
            )?;
            let base_term = translate_term(program, solver, base, env);
            let idx_term = translate_term(program, solver, idx, env);
            check_index_bounds(
                solver,
                &base_term,
                &idx_term,
                guard,
                control,
                line,
                visible_vars,
                in_loop,
                certificates,
            )
        }
        Expr::Struct(sid, items, _) => {
            if program.structs[*sid].is_view {
                for item in items.iter().filter(|e| !e.lends()) {
                    check_expr_obligations(
                        program,
                        solver,
                        item,
                        guard,
                        env,
                        control,
                        line,
                        visible_vars,
                        in_loop,
                        certificates,
                    )?;
                }
                for item in items.iter().filter(|e| e.lends()) {
                    check_expr_obligations(
                        program,
                        solver,
                        item,
                        guard,
                        env,
                        control,
                        line,
                        visible_vars,
                        in_loop,
                        certificates,
                    )?;
                }
            } else {
                for item in items {
                    check_expr_obligations(
                        program,
                        solver,
                        item,
                        guard,
                        env,
                        control,
                        line,
                        visible_vars,
                        in_loop,
                        certificates,
                    )?;
                }
            }
            Ok(())
        }
        Expr::Variant(_, _, items, _) | Expr::Vector(items, _) => {
            for item in items {
                check_expr_obligations(
                    program,
                    solver,
                    item,
                    guard,
                    env,
                    control,
                    line,
                    visible_vars,
                    in_loop,
                    certificates,
                )?;
            }
            Ok(())
        }
        Expr::Negate(inner, ty) => {
            check_expr_obligations(
                program,
                solver,
                inner,
                guard,
                env,
                control,
                line,
                visible_vars,
                in_loop,
                certificates,
            )?;
            let term = translate_term(program, solver, expr, env);
            let fits = type_range_formula(solver, &term, *ty);
            require_formula(
                solver,
                guard,
                fits,
                control,
                line,
                "P5",
                format!("negation may overflow `{}`", ty.name()),
                visible_vars,
                in_loop,
                certificates,
            )?;
            solver.add_fact(guard, fits);
            Ok(())
        }
        Expr::Arithmetic(op, left, right, ty) => {
            check_expr_obligations(
                program,
                solver,
                left,
                guard,
                env,
                control,
                line,
                visible_vars,
                in_loop,
                certificates,
            )?;
            check_expr_obligations(
                program,
                solver,
                right,
                guard,
                env,
                control,
                line,
                visible_vars,
                in_loop,
                certificates,
            )?;
            if matches!(op, Arithmetic::Divide | Arithmetic::Remainder) {
                let r_term = translate_term(program, solver, right, env);
                let non_zero = solver.ne(&r_term, &LinearTerm::from_i128(0));
                require_formula(
                    solver,
                    guard,
                    non_zero,
                    control,
                    line,
                    "P5",
                    "divisor may be zero",
                    visible_vars,
                    in_loop,
                    certificates,
                )?;
                solver.add_fact(guard, non_zero);
            }
            let term = translate_term(program, solver, expr, env);
            let fits = type_range_formula(solver, &term, *ty);
            require_formula(
                solver,
                guard,
                fits,
                control,
                line,
                "P5",
                format!("arithmetic result may overflow `{}`", ty.name()),
                visible_vars,
                in_loop,
                certificates,
            )?;
            solver.add_fact(guard, fits);
            Ok(())
        }
        Expr::Compare(_, left, right) => {
            check_expr_obligations(
                program,
                solver,
                left,
                guard,
                env,
                control,
                line,
                visible_vars,
                in_loop,
                certificates,
            )?;
            check_expr_obligations(
                program,
                solver,
                right,
                guard,
                env,
                control,
                line,
                visible_vars,
                in_loop,
                certificates,
            )
        }
        // [P7], [E-Bool]: The right operand of `∧` is evaluated where the left
        // operand is true, and that of `∨` where the left operand is false.
        Expr::And(left, right) => {
            check_expr_obligations(
                program,
                solver,
                left,
                guard,
                env,
                control,
                line,
                visible_vars,
                in_loop,
                certificates,
            )?;
            let left_holds = translate_formula(program, solver, left, env);
            let right_guard = solver.bdd.and(guard, left_holds);
            check_expr_obligations(
                program,
                solver,
                right,
                right_guard,
                env,
                control,
                line,
                visible_vars,
                in_loop,
                certificates,
            )
        }
        Expr::Or(left, right) => {
            check_expr_obligations(
                program,
                solver,
                left,
                guard,
                env,
                control,
                line,
                visible_vars,
                in_loop,
                certificates,
            )?;
            let left_holds = translate_formula(program, solver, left, env);
            let not_left = solver.bdd.not(left_holds);
            let right_guard = solver.bdd.and(guard, not_left);
            check_expr_obligations(
                program,
                solver,
                right,
                right_guard,
                env,
                control,
                line,
                visible_vars,
                in_loop,
                certificates,
            )
        }
        Expr::Call(fn_id, arguments, _) => {
            for arg in arguments {
                check_expr_obligations(
                    program,
                    solver,
                    arg,
                    guard,
                    env,
                    control,
                    line,
                    visible_vars,
                    in_loop,
                    certificates,
                )?;
            }
            let callee = &program.functions[*fn_id];
            if let Some(pre) = &callee.precondition {
                let arg_terms: Vec<LinearTerm> = arguments
                    .iter()
                    .map(|a| translate_term(program, solver, a, env))
                    .collect();
                let call_env = Env {
                    locals: BTreeMap::new(),
                    parameters: arg_terms.clone(),
                    old_parameters: arg_terms,
                    fields: Vec::new(),
                    constants: BTreeMap::new(),
                };
                let pre_formula = translate_formula(program, solver, pre, &call_env);
                require_formula(
                    solver,
                    guard,
                    pre_formula,
                    control,
                    line,
                    "P3",
                    format!("precondition of function `{}` may not hold", callee.name),
                    visible_vars,
                    in_loop,
                    certificates,
                )?;
                solver.add_fact(guard, pre_formula);
            }
            Ok(())
        }
    }
}

fn check_expr_pure_ownership(
    program: &Program,
    param_types: &[Type],
    expr: &Expr,
    consumed: bool,
    control: &str,
    line: u32,
) -> Result<(), Error> {
    match expr {
        Expr::Boolean(_)
        | Expr::Integer(_, _)
        | Expr::String(_)
        | Expr::Old(_, _)
        | Expr::EmptyMap(_)
        | Expr::TasksEmpty(_, _)
        | Expr::Count(_) => Ok(()),
        Expr::Var(VarRef::Parameter(idx), expr_ty) => {
            if consumed
                && param_types
                    .get(*idx)
                    .is_some_and(|pt| matches!(pt, Type::Ref(_, _)))
                && !matches!(expr_ty, Type::Ref(_, _))
                && program.kind(expr_ty) != Kind::Copy
            {
                return Err(Error {
                    control: control.to_string(),
                    line,
                    clause: "O3",
                    message: format!("cannot move `{expr_ty}` value out through a borrow"),
                    counterexample: None,
                });
            }
            Ok(())
        }
        Expr::Var(_, _) => Ok(()),
        Expr::Borrow(_, place, _) => {
            for step in &place.steps {
                if let PlaceStep::Index(idx, _) = step {
                    check_expr_pure_ownership(program, param_types, idx, false, control, line)?;
                }
            }
            Ok(())
        }
        Expr::Move(inner, _) => {
            check_expr_pure_ownership(program, param_types, inner, true, control, line)
        }
        Expr::Field(base, _, _, fty) => {
            check_expr_pure_ownership(program, param_types, base, false, control, line)?;
            if consumed && program.kind(fty) != Kind::Copy {
                return Err(Error {
                    control: control.to_string(),
                    line,
                    clause: "O3",
                    message: "cannot move out of a struct field of non-copy type".to_string(),
                    counterexample: None,
                });
            }
            Ok(())
        }
        Expr::Index(base, idx, ety) => {
            check_expr_pure_ownership(program, param_types, base, false, control, line)?;
            check_expr_pure_ownership(program, param_types, idx, false, control, line)?;
            if consumed && program.kind(ety) != Kind::Copy {
                return Err(Error {
                    control: control.to_string(),
                    line,
                    clause: "O3",
                    message: "cannot move out of a vector element of non-copy type".to_string(),
                    counterexample: None,
                });
            }
            Ok(())
        }
        Expr::Struct(sid, items, ty) => {
            if !consumed && program.kind(ty) == Kind::Must {
                return Err(Error {
                    control: control.to_string(),
                    line,
                    clause: "O3a",
                    message: "temporary value of kind `must` cannot be discarded".to_string(),
                    counterexample: None,
                });
            }
            if program.structs[*sid].is_view {
                for item in items.iter().filter(|e| !e.lends()) {
                    check_expr_pure_ownership(program, param_types, item, true, control, line)?;
                }
                for item in items.iter().filter(|e| e.lends()) {
                    check_expr_pure_ownership(program, param_types, item, true, control, line)?;
                }
            } else {
                for item in items {
                    check_expr_pure_ownership(program, param_types, item, true, control, line)?;
                }
            }
            Ok(())
        }
        Expr::Variant(_, _, items, ty) | Expr::Vector(items, ty) => {
            if !consumed && program.kind(ty) == Kind::Must {
                return Err(Error {
                    control: control.to_string(),
                    line,
                    clause: "O3a",
                    message: "temporary value of kind `must` cannot be discarded".to_string(),
                    counterexample: None,
                });
            }
            for item in items {
                check_expr_pure_ownership(program, param_types, item, true, control, line)?;
            }
            Ok(())
        }
        Expr::Len(inner)
        | Expr::Clone(inner, _)
        | Expr::Trim(inner)
        | Expr::Negate(inner, _)
        | Expr::Not(inner) => {
            check_expr_pure_ownership(program, param_types, inner, false, control, line)
        }
        Expr::Arithmetic(_, l, r, _)
        | Expr::Compare(_, l, r)
        | Expr::And(l, r)
        | Expr::Or(l, r) => {
            check_expr_pure_ownership(program, param_types, l, false, control, line)?;
            check_expr_pure_ownership(program, param_types, r, false, control, line)
        }
        Expr::Call(fn_id, args, _) => {
            let callee_params = &program.functions[*fn_id].parameters;
            for (i, arg) in args.iter().enumerate() {
                if !arg.lends() {
                    let is_ref = callee_params
                        .get(i)
                        .is_some_and(|p| matches!(p.ty, Type::Ref(_, _)));
                    check_expr_pure_ownership(program, param_types, arg, !is_ref, control, line)?;
                }
            }
            for (i, arg) in args.iter().enumerate() {
                if arg.lends() {
                    let is_ref = callee_params
                        .get(i)
                        .is_some_and(|p| matches!(p.ty, Type::Ref(_, _)));
                    check_expr_pure_ownership(program, param_types, arg, !is_ref, control, line)?;
                }
            }
            Ok(())
        }
    }
}

fn alloc_type_term_in(solver: &mut Solver, name: String, ty: &Type) -> TermId {
    let base_ty = ty.deref_type();
    let id = match base_ty {
        Type::Int(int_ty) => solver.fresh_var(name, Some(*int_ty), true),
        Type::Bool => {
            let id = solver.fresh_var(name, None, true);
            let t = LinearTerm::var(id);
            let lo = solver.le(&LinearTerm::from_i128(0), &t);
            let hi = solver.le(&t, &LinearTerm::from_i128(1));
            let both = solver.bdd.and(lo, hi);
            solver.add_structure(both);
            id
        }
        _ => solver.fresh_var(name, None, true),
    };
    solver.register_sort(id, base_ty);
    solver.instantiate_all();
    id
}

fn register_program_structs(program: &Program, solver: &mut Solver) {
    for (sid, s) in program.structs.iter().enumerate() {
        solver.register_struct_arity(sid, s.fields.len());
    }
}

/// Checks a [`Function`] declaration ([P8]).
fn check_function(
    program: &Program,
    _id: FunctionId,
    function: &Function,
    certificates: &mut Proofs,
) -> Result<(), Error> {
    let mut solver = Solver::new(Vec::new());
    register_program_structs(program, &mut solver);
    let mut param_terms = Vec::new();
    let mut visible_vars = Vec::new();

    for param in &function.parameters {
        let term_id = alloc_type_term_in(&mut solver, param.name.clone(), &param.ty);
        param_terms.push(LinearTerm::var(term_id));
        visible_vars.push((
            param.name.clone(),
            term_id,
            *param.ty.deref_type() == Type::Bool,
        ));
    }

    let env = Env {
        locals: BTreeMap::new(),
        parameters: param_terms.clone(),
        old_parameters: param_terms,
        fields: Vec::new(),
        constants: BTreeMap::new(),
    };

    if let Some(pre) = &function.precondition {
        let pre_formula = translate_formula(program, &mut solver, pre, &env);
        solver.add_fact(bdd::TRUE, pre_formula);
    }

    let fn_param_tys: Vec<Type> = function.parameters.iter().map(|p| p.ty.clone()).collect();
    check_expr_pure_ownership(
        program,
        &fn_param_tys,
        &function.body,
        true,
        &function.name,
        1,
    )?;
    let result = check_expr_obligations(
        program,
        &mut solver,
        &function.body,
        bdd::TRUE,
        &env,
        &function.name,
        1,
        &visible_vars,
        false,
        certificates,
    );
    certificates.close_body(solver);
    result
}

fn collect_read_vars(expr: &Expr, out: &mut Vec<VarId>) {
    match expr {
        Expr::Boolean(_)
        | Expr::Integer(_, _)
        | Expr::String(_)
        | Expr::Old(_, _)
        | Expr::EmptyMap(_)
        | Expr::TasksEmpty(_, _) => {}
        Expr::Count(var) => out.push(*var),
        Expr::Var(VarRef::Local(id), _) => {
            if !out.contains(id) {
                out.push(*id);
            }
        }
        Expr::Var(_, _) => {}
        Expr::Borrow(_, place, _) => {
            if !out.contains(&place.root) {
                out.push(place.root);
            }
            for step in &place.steps {
                if let crate::typed::PlaceStep::Index(idx, _) = step {
                    collect_read_vars(idx, out);
                }
            }
        }
        Expr::Move(inner, _)
        | Expr::Field(inner, _, _, _)
        | Expr::Len(inner)
        | Expr::Clone(inner, _)
        | Expr::Trim(inner)
        | Expr::Negate(inner, _)
        | Expr::Not(inner) => collect_read_vars(inner, out),
        Expr::Index(l, r, _)
        | Expr::Arithmetic(_, l, r, _)
        | Expr::Compare(_, l, r)
        | Expr::And(l, r)
        | Expr::Or(l, r) => {
            collect_read_vars(l, out);
            collect_read_vars(r, out);
        }
        Expr::Struct(_, args, _)
        | Expr::Variant(_, _, args, _)
        | Expr::Vector(args, _)
        | Expr::Call(_, args, _) => {
            for arg in args {
                collect_read_vars(arg, out);
            }
        }
    }
}

fn collect_operand_modified(program: &Program, arg: &Expr, out: &mut BTreeSet<VarId>) {
    match arg {
        Expr::Borrow(BorrowMode::Exclusive, place, _) => {
            out.insert(place.root);
        }
        Expr::Var(VarRef::Local(id), ty) if program.has_exclusive_borrow(ty) => {
            out.insert(*id);
        }
        Expr::Struct(sid, fields, _) if program.structs[*sid].is_view => {
            for field in fields {
                collect_operand_modified(program, field, out);
            }
        }
        Expr::Move(inner, _) => collect_operand_modified(program, inner, out),
        _ => {}
    }
}

fn collect_modified_vars(
    program: &Program,
    body: &ControlBody,
    body_id: BodyId,
    out: &mut BTreeSet<VarId>,
) {
    for stmt in &body.bodies[body_id].statements {
        match &stmt.command {
            Command::Assign { var, .. } => {
                out.insert(*var);
            }
            Command::AssignPlace { target, .. } => {
                out.insert(target.root);
            }
            Command::Decide {
                op_kind, arguments, ..
            } => {
                if let Operation::Builtin {
                    target: Some(place),
                    ..
                } = op_kind
                {
                    out.insert(place.root);
                }
                for arg in arguments {
                    collect_operand_modified(program, arg, out);
                }
            }
            Command::Capture {
                operation,
                arguments,
                ..
            } => {
                if let Operation::Builtin {
                    target: Some(place),
                    ..
                } = operation
                {
                    out.insert(place.root);
                }
                for arg in arguments {
                    collect_operand_modified(program, arg, out);
                }
            }
            Command::Loop { body: inner, .. } => {
                collect_modified_vars(program, body, *inner, out);
            }
            Command::Boundary {
                body: b1,
                contingency: b2,
                ..
            } => {
                collect_modified_vars(program, body, *b1, out);
                collect_modified_vars(program, body, *b2, out);
            }
            _ => {}
        }
    }
}

/// Identifies single-binder immutable locals bound to constant expressions ([I3]).
fn find_constant_locals(
    program: &Program,
    body: &ControlBody,
    param_count: usize,
) -> BTreeMap<VarId, Int> {
    let mut bind_counts: BTreeMap<VarId, usize> = BTreeMap::new();
    let mut bind_exprs: BTreeMap<VarId, Expr> = BTreeMap::new();
    for (idx, _) in body.vars.iter().enumerate() {
        bind_counts.insert(idx, 0);
    }
    for param_idx in 0..param_count.min(body.vars.len()) {
        // Parameters of the control/boundary are not constant expressions ([I3]).
        *bind_counts.entry(param_idx).or_insert(0) += 2;
    }
    for b in &body.bodies {
        if let Some(head) = &b.head {
            for &lp in &head.parameters {
                *bind_counts.entry(lp).or_insert(0) += 2;
            }
        }
        for stmt in &b.statements {
            match &stmt.command {
                Command::Spawn { .. } | Command::Cancel { .. } => {}
                Command::Bind { var, value } => {
                    *bind_counts.entry(*var).or_insert(0) += 1;
                    if !matches!(value, Expr::Borrow(BorrowMode::Exclusive, _, _)) {
                        bind_exprs.insert(*var, value.clone());
                    }
                }
                Command::Unpack { vars, .. } => {
                    for &v in vars {
                        *bind_counts.entry(v).or_insert(0) += 2;
                    }
                }
                Command::Capture { var, .. } => {
                    *bind_counts.entry(*var).or_insert(0) += 2;
                }
                Command::Boundary {
                    contingency_vars,
                    message_var,
                    ..
                } => {
                    for &v in contingency_vars {
                        *bind_counts.entry(v).or_insert(0) += 2;
                    }
                    if let Some(mv) = message_var {
                        *bind_counts.entry(*mv).or_insert(0) += 2;
                    }
                }
                Command::Decide { arms, .. } => {
                    for arm in arms {
                        for &v in &arm.vars {
                            *bind_counts.entry(v).or_insert(0) += 2;
                        }
                    }
                }
                Command::Loop { arms, .. } => {
                    for arm in arms {
                        for &v in arm {
                            *bind_counts.entry(v).or_insert(0) += 2;
                        }
                    }
                }
                _ => {}
            }
        }
    }

    let mut constants = BTreeMap::new();
    let mut changed = true;
    while changed {
        changed = false;
        for (&var, &count) in &bind_counts {
            if count == 1
                && !body.vars[var].mutable
                && !constants.contains_key(&var)
                && let Some(expr) = bind_exprs.get(&var)
                && let Some(val) = eval_const(program, expr, &constants)
            {
                let fits = match body.vars[var].ty {
                    Type::Int(int_ty) => {
                        let (lo, hi) = int_ty.literal_bounds();
                        val >= lo && val <= hi
                    }
                    _ => false,
                };
                if fits {
                    constants.insert(var, val);
                    changed = true;
                }
            }
        }
    }
    constants
}

#[derive(Clone)]
struct CapturedInfo {
    operation: Operation,
    old_args: Vec<LinearTerm>,
    post_args: Vec<LinearTerm>,
}

#[derive(Clone)]
enum FrozenStep {
    Field(StructId, usize, Type),
    Index(LinearTerm, Type),
}

#[derive(Clone)]
struct FrozenPlace {
    root: VarId,
    root_ty: Type,
    steps: Vec<FrozenStep>,
}

type VisibleVars = Vec<(String, TermId, bool)>;

type LeaveRecord = (
    usize,
    Formula,
    Vec<LinearTerm>,
    Vec<Vec<(Formula, TermId)>>,
    Vec<Formula>,
    Vec<Formula>,
    Vec<Vec<(Formula, VarId)>>,
);

struct BodyChecker<'a> {
    program: &'a Program,
    owner_name: String,
    allowed_uses: Vec<String>,
    contract: Vec<Alternative>,
    param_types: Vec<Type>,
    body: &'a ControlBody,
    boundary_may_fault: &'a [bool],
    solver: Solver,
    /// BDD variable index for each `(SiteId, alternative_position)`.
    site_atoms: Vec<Vec<usize>>,
    /// `D(x)` for each `VarId` ([7.4]).
    defined: Vec<Formula>,
    /// `M(x)` for each `VarId` ([7.4]).
    moved: Vec<Formula>,
    /// Disjoint `(history_guard, logical_term_id)` versions of each `VarId` ([I1], [N5]).
    versions: Vec<Vec<(Formula, TermId)>>,
    /// Entry logical terms for the control/boundary parameters ([P4]).
    entry_parameters: Vec<LinearTerm>,
    /// Constant local map ([I3]).
    constants: BTreeMap<VarId, Int>,
    /// Captured operation metadata for outcome variables ([I12]).
    captured: BTreeMap<VarId, Vec<(Formula, CapturedInfo)>>,
    /// Frozen place(s) abbreviated by a local borrow variable ([I7], [I9]).
    local_borrows: BTreeMap<VarId, Vec<(Formula, FrozenPlace)>>,
    /// Underlying loan root variables held by each borrow/view variable ([I9]).
    var_loan_roots: Vec<Vec<(Formula, VarId)>>,
    /// Recorded `Rᵢ` for each `(BodyId, stmt_idx)` for Pass 2 loan checking.
    stmt_r: BTreeMap<(BodyId, usize), Formula>,
    /// Recorded visible variables at `(BodyId, stmt_idx)` for Pass 2 counterexamples.
    stmt_visible: BTreeMap<(BodyId, usize), VisibleVars>,
    /// Recorded fallthrough `live` at end of lexical boundary `B₁` for Pass 2.
    boundary_fallthrough_live: BTreeMap<BodyId, Formula>,
    /// Entry availability snapshot `D(v) ∧ ¬M(v)` per loop body ([O6]).
    loop_entry_avail: BTreeMap<BodyId, Vec<Formula>>,
    /// Stack of enclosing active body scopes (outermost first).
    active_scopes: Vec<BodyId>,
    /// Whether this scope permits faults (`faults` signature or inside `B₁`).
    permits_faults: bool,
    /// Whether currently checking a `contingency` body `B₂` ([F5], [F6]).
    in_contingency: bool,
    /// Retained variables in a named boundary `B₁` ([F6]).
    retained_vars: Vec<VarId>,
    /// Set to `true` when checking a named boundary's `B₂` and a feasible
    /// `escalate` or `fault` occurs ([F6]).
    boundary_can_fault: bool,
    certificates: &'a mut Proofs,
    warnings: &'a mut Vec<crate::surface::Warning>,
    /// The line of the statement being checked.
    at_line: u32,
    /// The first question that got no verdict: a limit ([J6]), a fault of
    /// the procedure ([M1]) or a certificate that the kernel refused
    /// ([V1]). It is reported in place of whatever the body's check
    /// concludes, since that may rest on the missing answer.
    trouble: Option<Error>,
}

impl<'a> BodyChecker<'a> {
    fn note_trouble(&mut self, clause: &'static str, message: String) {
        if self.trouble.is_none() {
            self.trouble = Some(Error {
                control: self.owner_name.clone(),
                line: self.at_line,
                clause,
                message,
                counterexample: None,
            });
        }
    }

    /// The result of checking the body, unless a question got no verdict.
    fn settle<T>(&mut self, result: Result<T, Error>) -> Result<T, Error> {
        match self.trouble.take() {
            Some(trouble) => Err(trouble),
            None => result,
        }
    }

    /// Whether `negated` has no model under what the body states. A yes is
    /// validated by the kernel and recorded, as every entailment is ([V1]).
    /// Without a verdict the answer is no, and the trouble is noted.
    fn has_no_model(
        &mut self,
        negated: Formula,
        visible_vars: &[(String, TermId, bool)],
        in_loop: bool,
        clause: &'static str,
        about: &str,
    ) -> bool {
        match self.solver.decide(negated, visible_vars, in_loop) {
            Decision::Proved(cert) => match self.certificates.accept(
                &self.solver,
                negated,
                &self.owner_name,
                self.at_line,
                clause,
                cert,
            ) {
                Ok(()) => true,
                Err(kernel_err) => {
                    self.note_trouble(
                        "V1",
                        format!("certificate rejected by the kernel: {kernel_err}"),
                    );
                    false
                }
            },
            Decision::Refuted(_) => false,
            Decision::Limit { steps } => {
                self.note_trouble("J6", limit_message(steps, about));
                false
            }
            Decision::Fault(fault) => {
                self.note_trouble("M1", fault_message(&fault, about));
                false
            }
        }
    }

    fn atom(&mut self, site: SiteId, alt_pos: usize) -> Formula {
        let var = self.site_atoms[site][alt_pos];
        self.solver.bdd.variable(var)
    }

    fn selector(&mut self, sel: &Selector) -> Formula {
        match sel {
            Selector::Top => bdd::TRUE,
            Selector::Atom(site, alt_pos) => self.atom(*site, *alt_pos),
            Selector::Not(inner) => {
                let f = self.selector(inner);
                self.solver.bdd.not(f)
            }
            Selector::And(l, r) => {
                let fl = self.selector(l);
                let fr = self.selector(r);
                self.solver.bdd.and(fl, fr)
            }
            Selector::Or(l, r) => {
                let fl = self.selector(l);
                let fr = self.selector(r);
                self.solver.bdd.or(fl, fr)
            }
        }
    }

    fn alloc_var_term(&mut self, var: VarId) -> TermId {
        let info = &self.body.vars[var];
        alloc_type_term_in(&mut self.solver, info.name.clone(), &info.ty)
    }

    fn alloc_type_term(&mut self, name: &str, ty: &Type) -> TermId {
        alloc_type_term_in(&mut self.solver, name.to_string(), ty)
    }

    fn set_version(&mut self, var: VarId, guard: Formula, term_id: TermId) {
        let mut updated = Vec::new();
        for (old_guard, old_term) in self.versions[var].drain(..) {
            let remaining = self.solver.bdd.minus(old_guard, guard);
            if remaining != bdd::FALSE {
                updated.push((remaining, old_term));
            }
        }
        if guard != bdd::FALSE {
            updated.push((guard, term_id));
        }
        self.versions[var] = updated;
    }

    fn avail(&mut self, var: VarId) -> Formula {
        let not_moved = self.solver.bdd.not(self.moved[var]);
        self.solver.bdd.and(self.defined[var], not_moved)
    }

    fn is_feasible(
        &mut self,
        guard: Formula,
        visible_vars: &[(String, TermId, bool)],
        in_loop: bool,
    ) -> bool {
        if guard == bdd::FALSE {
            return false;
        }
        !self.has_no_model(
            guard,
            visible_vars,
            in_loop,
            "N1",
            "whether a history is feasible",
        )
    }

    /// Builds an [`Env`] that maps each currently defined variable to its
    /// logical term (introducing a multiplexer variable when a variable has
    /// more than one version across histories, [I1]).
    fn current_env(&mut self) -> (Env, Vec<(String, TermId, bool)>) {
        let mut locals = BTreeMap::new();
        let mut visible = Vec::new();
        for var in 0..self.body.vars.len() {
            if self.versions[var].is_empty() {
                continue;
            }
            let term_id = if self.versions[var].len() == 1 {
                self.versions[var][0].1
            } else {
                let mux = self.alloc_var_term(var);
                let entries = self.versions[var].clone();
                let mut union_guard = bdd::FALSE;
                for (h, tid) in entries {
                    union_guard = self.solver.bdd.or(union_guard, h);
                    self.solver.add_def_linear(h, mux, LinearTerm::var(tid));
                }
                self.versions[var] = vec![(union_guard, mux)];
                mux
            };
            locals.insert(var, LinearTerm::var(term_id));
            visible.push((
                self.body.vars[var].name.clone(),
                term_id,
                *self.body.vars[var].ty.deref_type() == Type::Bool,
            ));
        }
        (
            Env {
                locals,
                parameters: self.entry_parameters.clone(),
                old_parameters: self.entry_parameters.clone(),
                fields: Vec::new(),
                constants: self.constants.clone(),
            },
            visible,
        )
    }

    fn check_available(
        &mut self,
        var: VarId,
        r_i: Formula,
        line: u32,
        visible_vars: &[(String, TermId, bool)],
        in_loop: bool,
    ) -> Result<(), Error> {
        let avail_var = self.avail(var);
        let msg = if self.moved[var] != bdd::FALSE {
            format!(
                "`{}` may not be available (unbound or already moved) on this history",
                self.body.vars[var].name
            )
        } else {
            format!(
                "`{}` may not be bound on this history",
                self.body.vars[var].name
            )
        };
        require_formula(
            &mut self.solver,
            r_i,
            avail_var,
            &self.owner_name,
            line,
            "O2",
            msg,
            visible_vars,
            in_loop,
            self.certificates,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn check_consume_expr(
        &mut self,
        expr: &Expr,
        r_i: Formula,
        line: u32,
        visible_vars: &[(String, TermId, bool)],
        in_loop: bool,
    ) -> Result<(), Error> {
        match expr {
            Expr::Var(VarRef::Local(id), expr_ty) => {
                self.check_available(*id, r_i, line, visible_vars, in_loop)?;
                let var_ty = &self.body.vars[*id].ty;
                if matches!(var_ty, Type::Ref(_, _)) && !matches!(expr_ty, Type::Ref(_, _)) {
                    // Dereferencing a borrow in a consumed slot never moves the
                    // borrow itself; only `copy` values may leave behind a borrow ([O3]).
                    if self.program.kind(expr_ty) != Kind::Copy
                        && self.is_feasible(r_i, visible_vars, in_loop)
                    {
                        return Err(Error {
                            control: self.owner_name.clone(),
                            line,
                            clause: "O3",
                            message: format!(
                                "cannot move `{expr_ty}` value out through borrow `{}`",
                                self.body.vars[*id].name
                            ),
                            counterexample: None,
                        });
                    }
                } else if self.program.kind(var_ty) != Kind::Copy {
                    self.moved[*id] = self.solver.bdd.or(self.moved[*id], r_i);
                }
                Ok(())
            }
            Expr::Move(inner, _) => {
                self.check_consume_expr(inner, r_i, line, visible_vars, in_loop)
            }
            Expr::Field(base, _, _, fty) => {
                self.check_read_expr(base, r_i, line, visible_vars, in_loop)?;
                if self.program.kind(fty) != Kind::Copy
                    && self.is_feasible(r_i, visible_vars, in_loop)
                {
                    return Err(Error {
                        control: self.owner_name.clone(),
                        line,
                        clause: "O3",
                        message: "cannot move out of a struct field of non-copy type".to_string(),
                        counterexample: None,
                    });
                }
                Ok(())
            }
            Expr::Index(base, idx, ety) => {
                self.check_read_expr(base, r_i, line, visible_vars, in_loop)?;
                self.check_read_expr(idx, r_i, line, visible_vars, in_loop)?;
                if self.program.kind(ety) != Kind::Copy
                    && self.is_feasible(r_i, visible_vars, in_loop)
                {
                    return Err(Error {
                        control: self.owner_name.clone(),
                        line,
                        clause: "O3",
                        message: "cannot move out of a vector element of non-copy type".to_string(),
                        counterexample: None,
                    });
                }
                Ok(())
            }
            Expr::Struct(sid, items, _) => {
                if self.program.structs[*sid].is_view {
                    for item in items.iter().filter(|e| !e.lends()) {
                        self.check_consume_expr(item, r_i, line, visible_vars, in_loop)?;
                    }
                    for item in items.iter().filter(|e| e.lends()) {
                        self.check_consume_expr(item, r_i, line, visible_vars, in_loop)?;
                    }
                } else {
                    for item in items {
                        self.check_consume_expr(item, r_i, line, visible_vars, in_loop)?;
                    }
                }
                Ok(())
            }
            Expr::Variant(_, _, items, _) | Expr::Vector(items, _) => {
                for item in items {
                    self.check_consume_expr(item, r_i, line, visible_vars, in_loop)?;
                }
                Ok(())
            }
            Expr::Borrow(_, place, _) => {
                self.check_available(place.root, r_i, line, visible_vars, in_loop)?;
                for step in &place.steps {
                    if let PlaceStep::Index(idx, _) = step {
                        self.check_read_expr(idx, r_i, line, visible_vars, in_loop)?;
                    }
                }
                Ok(())
            }
            other => self.check_read_expr(other, r_i, line, visible_vars, in_loop),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn check_read_expr(
        &mut self,
        expr: &Expr,
        r_i: Formula,
        line: u32,
        visible_vars: &[(String, TermId, bool)],
        in_loop: bool,
    ) -> Result<(), Error> {
        match expr {
            Expr::Boolean(_)
            | Expr::Integer(_, _)
            | Expr::String(_)
            | Expr::Old(_, _)
            | Expr::EmptyMap(_)
            | Expr::TasksEmpty(_, _)
            | Expr::Count(_) => Ok(()),
            Expr::Var(VarRef::Local(id), _) => {
                self.check_available(*id, r_i, line, visible_vars, in_loop)
            }
            Expr::Var(_, _) => Ok(()),
            Expr::Borrow(_, place, _) => {
                self.check_available(place.root, r_i, line, visible_vars, in_loop)?;
                for step in &place.steps {
                    if let PlaceStep::Index(idx, _) = step {
                        self.check_read_expr(idx, r_i, line, visible_vars, in_loop)?;
                    }
                }
                Ok(())
            }
            Expr::Struct(sid, items, ty) => {
                if self.program.kind(ty) == Kind::Must
                    && self.is_feasible(r_i, visible_vars, in_loop)
                {
                    return Err(Error {
                        control: self.owner_name.clone(),
                        line,
                        clause: "O3a",
                        message: "temporary value of kind `must` cannot be discarded".to_string(),
                        counterexample: None,
                    });
                }
                if self.program.structs[*sid].is_view {
                    for item in items.iter().filter(|e| !e.lends()) {
                        self.check_consume_expr(item, r_i, line, visible_vars, in_loop)?;
                    }
                    for item in items.iter().filter(|e| e.lends()) {
                        self.check_consume_expr(item, r_i, line, visible_vars, in_loop)?;
                    }
                } else {
                    for item in items {
                        self.check_consume_expr(item, r_i, line, visible_vars, in_loop)?;
                    }
                }
                Ok(())
            }
            Expr::Variant(_, _, items, ty) | Expr::Vector(items, ty) => {
                if self.program.kind(ty) == Kind::Must
                    && self.is_feasible(r_i, visible_vars, in_loop)
                {
                    return Err(Error {
                        control: self.owner_name.clone(),
                        line,
                        clause: "O3a",
                        message: "temporary value of kind `must` cannot be discarded".to_string(),
                        counterexample: None,
                    });
                }
                for item in items {
                    self.check_consume_expr(item, r_i, line, visible_vars, in_loop)?;
                }
                Ok(())
            }
            Expr::Move(inner, _)
            | Expr::Field(inner, _, _, _)
            | Expr::Len(inner)
            | Expr::Clone(inner, _)
            | Expr::Trim(inner)
            | Expr::Negate(inner, _)
            | Expr::Not(inner) => self.check_read_expr(inner, r_i, line, visible_vars, in_loop),
            Expr::Index(l, r, _)
            | Expr::Arithmetic(_, l, r, _)
            | Expr::Compare(_, l, r)
            | Expr::And(l, r)
            | Expr::Or(l, r) => {
                self.check_read_expr(l, r_i, line, visible_vars, in_loop)?;
                self.check_read_expr(r, r_i, line, visible_vars, in_loop)
            }
            Expr::Call(_, args, _) => {
                for arg in args {
                    self.check_read_expr(arg, r_i, line, visible_vars, in_loop)?;
                }
                Ok(())
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn check_reads(
        &mut self,
        expr: &Expr,
        r_i: Formula,
        line: u32,
        visible_vars: &[(String, TermId, bool)],
        in_loop: bool,
    ) -> Result<(), Error> {
        let mut vars = Vec::new();
        collect_read_vars(expr, &mut vars);
        for var in vars {
            self.check_available(var, r_i, line, visible_vars, in_loop)?;
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn check_operands_o0(
        &mut self,
        arguments: &[Expr],
        _param_types: Option<&[Type]>,
        r_i: Formula,
        env: &Env,
        line: u32,
        visible_vars: &[(String, TermId, bool)],
        in_loop: bool,
    ) -> Result<(), Error> {
        // [O0] Pass 1: non-lending operands (`!arg.lends()`, matching [E-Operands]) left to right.
        for arg in arguments {
            if !arg.lends() {
                check_expr_obligations(
                    self.program,
                    &mut self.solver,
                    arg,
                    r_i,
                    env,
                    &self.owner_name,
                    line,
                    visible_vars,
                    in_loop,
                    self.certificates,
                )?;
                self.check_consume_expr(arg, r_i, line, visible_vars, in_loop)?;
            }
        }
        // [O0] Pass 2: lending operands left to right.
        for arg in arguments {
            if arg.lends() {
                check_expr_obligations(
                    self.program,
                    &mut self.solver,
                    arg,
                    r_i,
                    env,
                    &self.owner_name,
                    line,
                    visible_vars,
                    in_loop,
                    self.certificates,
                )?;
                self.check_consume_expr(arg, r_i, line, visible_vars, in_loop)?;
            }
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn check_scope_obligations(
        &mut self,
        scope_bodies: &[BodyId],
        r_i: Formula,
        line: u32,
        visible_vars: &[(String, TermId, bool)],
        in_loop: bool,
    ) -> Result<(), Error> {
        if r_i == bdd::FALSE {
            return Ok(());
        }
        for var in 0..self.body.vars.len() {
            if !scope_bodies.contains(&self.body.vars[var].body) {
                continue;
            }
            if self.program.kind(&self.body.vars[var].ty) != Kind::Must {
                continue;
            }
            let avail_var = self.avail(var);
            let live_must = self.solver.bdd.and(r_i, avail_var);
            require_entailment(
                &mut self.solver,
                live_must,
                &self.owner_name,
                line,
                "O5",
                format!(
                    "`{}` holds an unconsumed obligation when its scope ends",
                    self.body.vars[var].name
                ),
                visible_vars,
                in_loop,
                self.certificates,
            )?;
        }
        Ok(())
    }

    fn check_may_fault(
        &mut self,
        r_i: Formula,
        line: u32,
        visible_vars: &[(String, TermId, bool)],
        in_loop: bool,
    ) -> Result<(), Error> {
        // [F1]: Control or enclosing boundary permits faults.
        if !self.permits_faults {
            require_entailment(
                &mut self.solver,
                r_i,
                &self.owner_name,
                line,
                "F1",
                format!(
                    "`{}` may fault here without declaring `faults`",
                    self.owner_name
                ),
                visible_vars,
                in_loop,
                self.certificates,
            )?;
        }
        // [F6]: In a named boundary's `B₁`, every retained parameter stays available at a fault.
        for &ret_var in &self.retained_vars.clone() {
            let avail_ret = self.avail(ret_var);
            require_formula(
                &mut self.solver,
                r_i,
                avail_ret,
                &self.owner_name,
                line,
                "F6",
                format!(
                    "retained parameter `{}` may already be moved where a fault can occur",
                    self.body.vars[ret_var].name
                ),
                visible_vars,
                in_loop,
                self.certificates,
            )?;
        }
        // [F2]: Every non-fault-releasable name in scope must already be consumed.
        for var in 0..self.body.vars.len() {
            if !self.active_scopes.contains(&self.body.vars[var].body) {
                continue;
            }
            if self.retained_vars.contains(&var) {
                continue;
            }
            if self.program.is_fault_releasable(&self.body.vars[var].ty) {
                continue;
            }
            let avail_var = self.avail(var);
            let live_non_rel = self.solver.bdd.and(r_i, avail_var);
            require_entailment(
                &mut self.solver,
                live_non_rel,
                &self.owner_name,
                line,
                "F2",
                format!(
                    "`{}` holds a non-fault-releasable value where a fault can occur",
                    self.body.vars[var].name
                ),
                visible_vars,
                in_loop,
                self.certificates,
            )?;
        }
        Ok(())
    }

    fn check_effects(
        &mut self,
        effects: &[String],
        op_name: &str,
        r_i: Formula,
        line: u32,
        visible_vars: &[(String, TermId, bool)],
        in_loop: bool,
    ) -> Result<(), Error> {
        let mut checked_feasible = None;
        for effect in effects {
            if !self.allowed_uses.contains(effect) {
                let feasible = *checked_feasible
                    .get_or_insert_with(|| self.is_feasible(r_i, visible_vars, in_loop));
                if feasible {
                    return Err(Error {
                        control: self.owner_name.clone(),
                        line,
                        clause: "F3",
                        message: format!(
                            "`{op_name}` uses effect `{effect}`, which `{}` does not allow",
                            self.owner_name
                        ),
                        counterexample: None,
                    });
                }
            }
        }
        Ok(())
    }

    fn bind_value_term(&mut self, var: VarId, r_i: Formula, val_term: LinearTerm) -> TermId {
        let term_id = self.alloc_var_term(var);
        if *self.body.vars[var].ty.deref_type() == Type::Bool {
            let b = self.solver.le(&LinearTerm::from_i128(1), &val_term);
            self.solver.add_def_bool(r_i, term_id, b);
        } else {
            self.solver.add_def_linear(r_i, term_id, val_term);
        }
        self.set_version(var, r_i, term_id);
        term_id
    }

    fn bind_value(&mut self, var: VarId, r_i: Formula, expr: &Expr, env: &Env) -> TermId {
        let term_id = self.alloc_var_term(var);
        if *self.body.vars[var].ty.deref_type() == Type::Bool {
            let phi = translate_formula(self.program, &mut self.solver, expr, env);
            self.solver.add_def_bool(r_i, term_id, phi);
        } else {
            let val_term = translate_term(self.program, &mut self.solver, expr, env);
            self.solver.add_def_linear(r_i, term_id, val_term);
        }
        self.set_version(var, r_i, term_id);
        term_id
    }

    fn var_in_body_tree(&self, var: VarId, root_body: BodyId) -> bool {
        let mut cur = Some(self.body.vars[var].body);
        while let Some(b) = cur {
            if b == root_body {
                return true;
            }
            cur = self.body.bodies[b].parent;
        }
        false
    }

    fn bind_local_borrow(&mut self, var: VarId, r_i: Formula, place: &Place, env: &Env) {
        if r_i == bdd::FALSE {
            return;
        }
        let tail = freeze_place(self.program, &mut self.solver, place, env);
        if let Some(parent_entries) = self.local_borrows.get(&place.root).cloned() {
            let mut covered = bdd::FALSE;
            let dest = self.local_borrows.entry(var).or_default();
            for (bg, parent_fp) in &parent_entries {
                let g = self.solver.bdd.and(r_i, *bg);
                if g != bdd::FALSE {
                    covered = self.solver.bdd.or(covered, g);
                    let mut combined_steps = parent_fp.steps.clone();
                    combined_steps.extend(tail.steps.clone());
                    dest.push((
                        g,
                        FrozenPlace {
                            root: parent_fp.root,
                            root_ty: parent_fp.root_ty.clone(),
                            steps: combined_steps,
                        },
                    ));
                }
            }
            let rest = self.solver.bdd.minus(r_i, covered);
            if rest != bdd::FALSE {
                dest.push((rest, tail));
            }
        } else {
            self.local_borrows.entry(var).or_default().push((r_i, tail));
        }
    }

    fn push_var_loan_root(&mut self, var: VarId, guard: Formula, root_v: VarId) {
        if guard == bdd::FALSE {
            return;
        }
        let entries = &mut self.var_loan_roots[var];
        for (eg, rv) in entries.iter_mut() {
            if *rv == root_v {
                *eg = self.solver.bdd.or(*eg, guard);
                return;
            }
        }
        entries.push((guard, root_v));
    }

    fn expr_loan_roots(&mut self, expr: &Expr, r_i: Formula) -> Vec<(Formula, VarId)> {
        let mut out = Vec::new();
        if r_i == bdd::FALSE {
            return out;
        }
        match expr {
            Expr::Borrow(_, place, _) => {
                out.push((r_i, place.root));
                for (lg, rv) in self.var_loan_roots[place.root].clone() {
                    let g = self.solver.bdd.and(r_i, lg);
                    if g != bdd::FALSE {
                        out.push((g, rv));
                    }
                }
            }
            Expr::Var(VarRef::Local(id), ty) if self.program.contains_borrow_or_view(ty) => {
                out.push((r_i, *id));
                for (lg, rv) in self.var_loan_roots[*id].clone() {
                    let g = self.solver.bdd.and(r_i, lg);
                    if g != bdd::FALSE {
                        out.push((g, rv));
                    }
                }
            }
            Expr::Field(base, _, _, ty) if self.program.contains_borrow_or_view(ty) => {
                return self.expr_loan_roots(base, r_i);
            }
            Expr::Struct(sid, fields, _) if self.program.structs[*sid].is_view => {
                for field in fields {
                    out.extend(self.expr_loan_roots(field, r_i));
                }
            }
            Expr::Move(inner, _) => return self.expr_loan_roots(inner, r_i),
            _ => {}
        }
        out
    }

    fn record_expr_loan_roots(&mut self, dest_var: VarId, expr: &Expr, guard: Formula) {
        if !self
            .program
            .contains_borrow_or_view(&self.body.vars[dest_var].ty)
        {
            return;
        }
        let roots = self.expr_loan_roots(expr, guard);
        for (lg, rv) in roots {
            self.push_var_loan_root(dest_var, lg, rv);
        }
    }

    fn invalidate_loan_roots(&mut self, var: VarId, guard: Formula) {
        if guard == bdd::FALSE
            || !self
                .program
                .contains_borrow_or_view(&self.body.vars[var].ty)
        {
            return;
        }
        let local_fps: Vec<VarId> = self
            .local_borrows
            .get(&var)
            .map(|entries| entries.iter().map(|(_, fp)| fp.root).collect())
            .unwrap_or_default();
        let roots = self.var_loan_roots[var].clone();
        for (lg, root_v) in roots {
            if root_v == var || local_fps.contains(&root_v) {
                continue;
            }
            let g = self.solver.bdd.and(guard, lg);
            if g != bdd::FALSE
                && self.defined[root_v] != bdd::FALSE
                && self.active_scopes.contains(&self.body.vars[root_v].body)
            {
                let fresh_tid = self.alloc_var_term(root_v);
                self.set_version(root_v, g, fresh_tid);
            }
        }
    }

    fn refresh_dependent_local_borrows(&mut self, written_root: VarId, guard: Formula) {
        if guard == bdd::FALSE {
            return;
        }
        let mut raw_deps: Vec<(VarId, Formula, FrozenPlace)> = Vec::new();
        for (&lb_var, entries) in &self.local_borrows {
            if self.defined[lb_var] == bdd::FALSE
                || !self.active_scopes.contains(&self.body.vars[lb_var].body)
            {
                continue;
            }
            for (bg, fp) in entries {
                if fp.root == written_root {
                    raw_deps.push((lb_var, *bg, fp.clone()));
                }
            }
        }
        let mut dependents: Vec<(VarId, Formula, FrozenPlace)> = Vec::new();
        for (lb_var, bg, fp) in raw_deps {
            let g = self.solver.bdd.and(guard, bg);
            if g != bdd::FALSE {
                dependents.push((lb_var, g, fp));
            }
        }
        if dependents.is_empty() {
            return;
        }
        let (env, _) = self.current_env();
        let root_term = env
            .locals
            .get(&written_root)
            .cloned()
            .unwrap_or_else(|| LinearTerm::from_i128(0));
        for (lb_var, g, fp) in dependents {
            let mut sub_term = root_term.clone();
            for step in &fp.steps {
                match step {
                    FrozenStep::Field(sid, fidx, fty) => {
                        sub_term =
                            translate_field_term(&mut self.solver, sub_term, *sid, *fidx, fty);
                    }
                    FrozenStep::Index(idx_t, ety) => {
                        sub_term =
                            translate_index_term(&mut self.solver, sub_term, idx_t.clone(), ety);
                    }
                }
            }
            let _ = self.bind_value_term(lb_var, g, sub_term);
        }
    }

    fn invalidate_exclusive_view_arg(&mut self, arg: &Expr, guard: Formula, env: &Env) {
        if guard == bdd::FALSE {
            return;
        }
        match arg {
            Expr::Borrow(BorrowMode::Exclusive, place, _) => {
                let z_tid = self.alloc_type_term("_mut", &place.ty);
                self.apply_place_write(place, guard, LinearTerm::var(z_tid), env);
            }
            Expr::Var(VarRef::Local(vid), ty) if self.program.has_exclusive_borrow(ty) => {
                if matches!(ty, Type::Ref(BorrowMode::Exclusive, _)) {
                    let inner_ty = ty.deref_type();
                    let z_tid = self.alloc_type_term("_mut", inner_ty);
                    let place = Place {
                        root: *vid,
                        root_ty: ty.clone(),
                        steps: Vec::new(),
                        ty: inner_ty.clone(),
                    };
                    self.apply_place_write(&place, guard, LinearTerm::var(z_tid), env);
                } else {
                    let fresh_tid = self.alloc_var_term(*vid);
                    self.set_version(*vid, guard, fresh_tid);
                    self.invalidate_loan_roots(*vid, guard);
                }
            }
            Expr::Struct(sid, fields, _) if self.program.structs[*sid].is_view => {
                for field in fields {
                    if self.program.has_exclusive_borrow(&field.ty()) {
                        self.invalidate_exclusive_view_arg(field, guard, env);
                    }
                }
            }
            Expr::Move(inner, _) => self.invalidate_exclusive_view_arg(inner, guard, env),
            _ => {}
        }
    }

    fn close_modified_with_borrows(&self, vars: &mut BTreeSet<VarId>) {
        let mut stack: Vec<VarId> = vars.iter().copied().collect();
        while let Some(v) = stack.pop() {
            if let Some(entries) = self.local_borrows.get(&v) {
                for (_, fp) in entries {
                    if vars.insert(fp.root) {
                        stack.push(fp.root);
                    }
                }
            }
            for (_, rv) in &self.var_loan_roots[v] {
                if vars.insert(*rv) {
                    stack.push(*rv);
                }
            }
        }
    }

    fn collect_loop_again_root_vars(&mut self, loop_body: BodyId, r_i: Formula) {
        let Some(head) = self.body.bodies[loop_body].head.clone() else {
            return;
        };
        let mut collected: Vec<Vec<VarId>> = vec![Vec::new(); head.parameters.len()];
        self.scan_again_roots_in_body(loop_body, loop_body, &mut collected);
        for (&lp_var, raw_roots) in head.parameters.iter().zip(collected) {
            if !self
                .program
                .contains_borrow_or_view(&self.body.vars[lp_var].ty)
            {
                continue;
            }
            let mut root_set: BTreeSet<VarId> = raw_roots.into_iter().collect();
            self.close_modified_with_borrows(&mut root_set);
            for rv in root_set {
                if !self.var_in_body_tree(rv, loop_body) {
                    self.push_var_loan_root(lp_var, r_i, rv);
                }
            }
        }
    }

    fn scan_again_roots_in_body(
        &self,
        cur_body: BodyId,
        target_loop: BodyId,
        out: &mut [Vec<VarId>],
    ) {
        fn collect_expr_vars(expr: &Expr, out: &mut Vec<VarId>) {
            match expr {
                Expr::Borrow(_, place, _) => out.push(place.root),
                Expr::Var(VarRef::Local(id), _) => out.push(*id),
                Expr::Field(base, _, _, _) | Expr::Move(base, _) => collect_expr_vars(base, out),
                Expr::Struct(_, fields, _) => {
                    for f in fields {
                        collect_expr_vars(f, out);
                    }
                }
                _ => {}
            }
        }
        for stmt in &self.body.bodies[cur_body].statements {
            match &stmt.command {
                Command::Again { body, arguments } if *body == target_loop => {
                    for (slot, arg) in out.iter_mut().zip(arguments) {
                        collect_expr_vars(arg, slot);
                    }
                }
                Command::Loop { body: inner, .. } => {
                    self.scan_again_roots_in_body(*inner, target_loop, out);
                }
                Command::Boundary {
                    body: b1,
                    contingency: b2,
                    ..
                } => {
                    self.scan_again_roots_in_body(*b1, target_loop, out);
                    self.scan_again_roots_in_body(*b2, target_loop, out);
                }
                _ => {}
            }
        }
    }

    fn apply_place_write(&mut self, place: &Place, guard: Formula, new_val: LinearTerm, env: &Env) {
        if guard == bdd::FALSE {
            return;
        }
        let local_root_term = env
            .locals
            .get(&place.root)
            .cloned()
            .unwrap_or_else(|| LinearTerm::from_i128(0));
        let local_root_ty = self.body.vars[place.root].ty.deref_type().clone();
        let updated_local = functional_update(
            self.program,
            &mut self.solver,
            local_root_term,
            &local_root_ty,
            &place.steps,
            new_val.clone(),
            env,
        );
        if let Some(entries) = self.local_borrows.get(&place.root).cloned() {
            let mut covered = bdd::FALSE;
            for (bg, frozen) in &entries {
                let g = self.solver.bdd.and(guard, *bg);
                if g == bdd::FALSE {
                    continue;
                }
                covered = self.solver.bdd.or(covered, g);
                let cur_root_term = env
                    .locals
                    .get(&frozen.root)
                    .cloned()
                    .unwrap_or_else(|| LinearTerm::from_i128(0));
                let updated_sub = if place.steps.is_empty() {
                    new_val.clone()
                } else {
                    let mut sub_term = cur_root_term.clone();
                    let mut sub_ty = frozen.root_ty.deref_type().clone();
                    for fstep in &frozen.steps {
                        match fstep {
                            FrozenStep::Field(sid, fidx, fty) => {
                                sub_term = translate_field_term(
                                    &mut self.solver,
                                    sub_term,
                                    *sid,
                                    *fidx,
                                    fty,
                                );
                                sub_ty = fty.clone();
                            }
                            FrozenStep::Index(idx_t, ety) => {
                                sub_term = translate_index_term(
                                    &mut self.solver,
                                    sub_term,
                                    idx_t.clone(),
                                    ety,
                                );
                                sub_ty = ety.clone();
                            }
                        }
                    }
                    functional_update(
                        self.program,
                        &mut self.solver,
                        sub_term,
                        &sub_ty,
                        &place.steps,
                        new_val.clone(),
                        env,
                    )
                };
                let new_root = functional_update_frozen(
                    self.program,
                    &mut self.solver,
                    cur_root_term,
                    frozen.root_ty.deref_type(),
                    &frozen.steps,
                    updated_sub,
                );
                let _ = self.bind_value_term(frozen.root, g, new_root);
                self.invalidate_loan_roots(frozen.root, g);
                self.refresh_dependent_local_borrows(frozen.root, g);
            }
            let uncovered = self.solver.bdd.minus(guard, covered);
            if uncovered != bdd::FALSE {
                self.invalidate_loan_roots(place.root, uncovered);
            }
            let _ = self.bind_value_term(place.root, guard, updated_local);
            return;
        }
        let _ = self.bind_value_term(place.root, guard, updated_local);
        self.invalidate_loan_roots(place.root, guard);
        self.refresh_dependent_local_borrows(place.root, guard);
    }

    #[allow(clippy::too_many_arguments)]
    fn apply_builtin_facts(
        &mut self,
        op: BuiltinOp,
        target: Option<&Place>,
        arg_terms: &[LinearTerm],
        alt_pos: usize,
        atom: Formula,
        field_terms: &[LinearTerm],
        env: &Env,
    ) {
        match op {
            BuiltinOp::Push => {
                if alt_pos == 0
                    && let Some(place) = target
                {
                    let v_old = translate_place(self.program, &mut self.solver, place, env);
                    let len_old_id = self.solver.intern_term(AtomTerm::Len(v_old));
                    let v_new_tid = self.alloc_type_term("_vec", &place.ty);
                    let v_new = LinearTerm::var(v_new_tid);
                    let len_new_id = self.solver.intern_term(AtomTerm::Len(v_new.clone()));
                    self.solver.instantiate_all();
                    let plus_one = LinearTerm::var(len_old_id).add(&LinearTerm::from_i128(1));
                    let eq_len = self.solver.eq(&LinearTerm::var(len_new_id), &plus_one);
                    self.solver.add_fact(atom, eq_len);
                    self.apply_place_write(place, atom, v_new, env);
                }
            }
            BuiltinOp::Pop => {
                if let Some(place) = target {
                    let v_old = translate_place(self.program, &mut self.solver, place, env);
                    let len_old_id = self.solver.intern_term(AtomTerm::Len(v_old));
                    self.solver.instantiate_all();
                    let len_old = LinearTerm::var(len_old_id);
                    if alt_pos == 0 {
                        let non_empty = self.solver.le(&LinearTerm::from_i128(1), &len_old);
                        self.solver.add_fact(atom, non_empty);
                        let v_new_tid = self.alloc_type_term("_vec", &place.ty);
                        let v_new = LinearTerm::var(v_new_tid);
                        let len_new_id = self.solver.intern_term(AtomTerm::Len(v_new.clone()));
                        self.solver.instantiate_all();
                        let minus_one = len_old.sub(&LinearTerm::from_i128(1));
                        let eq_len = self.solver.eq(&LinearTerm::var(len_new_id), &minus_one);
                        self.solver.add_fact(atom, eq_len);
                        self.apply_place_write(place, atom, v_new, env);
                    } else {
                        let is_empty = self.solver.eq(&len_old, &LinearTerm::from_i128(0));
                        self.solver.add_fact(atom, is_empty);
                    }
                }
            }
            BuiltinOp::Take => {
                if let Some(v_old) = arg_terms.first() {
                    let len_old_id = self.solver.intern_term(AtomTerm::Len(v_old.clone()));
                    self.solver.instantiate_all();
                    let len_old = LinearTerm::var(len_old_id);
                    if alt_pos == 0 {
                        let non_empty = self.solver.le(&LinearTerm::from_i128(1), &len_old);
                        self.solver.add_fact(atom, non_empty);
                        if let Some(tail) = field_terms.get(1) {
                            let len_tail_id = self.solver.intern_term(AtomTerm::Len(tail.clone()));
                            self.solver.instantiate_all();
                            let minus_one = len_old.sub(&LinearTerm::from_i128(1));
                            let eq_len = self.solver.eq(&LinearTerm::var(len_tail_id), &minus_one);
                            self.solver.add_fact(atom, eq_len);
                        }
                    } else {
                        let is_empty = self.solver.eq(&len_old, &LinearTerm::from_i128(0));
                        self.solver.add_fact(atom, is_empty);
                    }
                }
            }
            BuiltinOp::Insert => {
                if let Some(place) = target {
                    let m_old = translate_place(self.program, &mut self.solver, place, env);
                    let len_old_id = self.solver.intern_term(AtomTerm::Len(m_old));
                    self.solver.instantiate_all();
                    let len_old = LinearTerm::var(len_old_id);
                    let m_new_tid = self.alloc_type_term("_map", &place.ty);
                    let m_new = LinearTerm::var(m_new_tid);
                    let len_new_id = self.solver.intern_term(AtomTerm::Len(m_new.clone()));
                    self.solver.instantiate_all();
                    if alt_pos == 0 {
                        let plus_one = len_old.add(&LinearTerm::from_i128(1));
                        let eq_len = self.solver.eq(&LinearTerm::var(len_new_id), &plus_one);
                        self.solver.add_fact(atom, eq_len);
                    } else {
                        let non_empty = self.solver.le(&LinearTerm::from_i128(1), &len_old);
                        let eq_len = self.solver.eq(&LinearTerm::var(len_new_id), &len_old);
                        let both = self.solver.bdd.and(non_empty, eq_len);
                        self.solver.add_fact(atom, both);
                    }
                    self.apply_place_write(place, atom, m_new, env);
                }
            }
            BuiltinOp::Remove => {
                if let Some(place) = target
                    && alt_pos == 0
                {
                    let m_old = translate_place(self.program, &mut self.solver, place, env);
                    let len_old_id = self.solver.intern_term(AtomTerm::Len(m_old));
                    self.solver.instantiate_all();
                    let len_old = LinearTerm::var(len_old_id);
                    let non_empty = self.solver.le(&LinearTerm::from_i128(1), &len_old);
                    let m_new_tid = self.alloc_type_term("_map", &place.ty);
                    let m_new = LinearTerm::var(m_new_tid);
                    let len_new_id = self.solver.intern_term(AtomTerm::Len(m_new.clone()));
                    self.solver.instantiate_all();
                    let minus_one = len_old.sub(&LinearTerm::from_i128(1));
                    let eq_len = self.solver.eq(&LinearTerm::var(len_new_id), &minus_one);
                    let both = self.solver.bdd.and(non_empty, eq_len);
                    self.solver.add_fact(atom, both);
                    self.apply_place_write(place, atom, m_new, env);
                }
            }
            BuiltinOp::Get => {
                if alt_pos == 0
                    && let Some(m_old) = arg_terms.first()
                {
                    let len_old_id = self.solver.intern_term(AtomTerm::Len(m_old.clone()));
                    self.solver.instantiate_all();
                    let non_empty = self
                        .solver
                        .le(&LinearTerm::from_i128(1), &LinearTerm::var(len_old_id));
                    self.solver.add_fact(atom, non_empty);
                }
            }
            BuiltinOp::EntryAt => {
                if let (Some(m_old), Some(pos)) = (arg_terms.first(), arg_terms.get(1)) {
                    let len_old_id = self.solver.intern_term(AtomTerm::Len(m_old.clone()));
                    self.solver.instantiate_all();
                    let len_old = LinearTerm::var(len_old_id);
                    if alt_pos == 0 {
                        let in_range = self.solver.lt(pos, &len_old);
                        self.solver.add_fact(atom, in_range);
                        if let Some(next_term) = field_terms.get(2) {
                            let plus_one = pos.add(&LinearTerm::from_i128(1));
                            let eq_next = self.solver.eq(next_term, &plus_one);
                            self.solver.add_fact(atom, eq_next);
                        }
                    } else {
                        let at_end = self.solver.le(&len_old, pos);
                        self.solver.add_fact(atom, at_end);
                    }
                }
            }
            BuiltinOp::Emit => {}
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn warn_unreachable_arms(
        &mut self,
        op_name: &str,
        line: u32,
        statements: &[crate::typed::Statement],
        contract: &[Alternative],
        arms: &[crate::typed::Arm],
        arm_atoms: &[Formula],
        is_pure: bool,
        always_check: bool,
        r_i: Formula,
        visible_vars: &[(String, TermId, bool)],
        in_loop: bool,
    ) {
        let mut checked_r_i_feasible: Option<bool> = None;
        for (pos, arm) in arms.iter().enumerate() {
            let atom = arm_atoms[pos];
            let contract_alt = &contract[arm.alternative];
            if !always_check && contract_alt.condition.is_none() && !is_pure {
                continue;
            }
            let has_impossible = statements.iter().any(|s| {
                if matches!(s.command, Command::Impossible) {
                    let sel = self.selector(&s.selector);
                    self.solver.bdd.implies(atom, sel) == bdd::TRUE
                } else {
                    false
                }
            });
            if has_impossible {
                continue;
            }
            let r_i_feasible = *checked_r_i_feasible
                .get_or_insert_with(|| self.is_feasible(r_i, visible_vars, in_loop));
            if !r_i_feasible {
                break;
            }
            self.at_line = line;
            if self.has_no_model(
                atom,
                visible_vars,
                in_loop,
                "U16",
                "whether an alternative can happen",
            ) {
                self.warnings.push(crate::surface::Warning {
                    control: self.owner_name.clone(),
                    line,
                    clause: "U16",
                    message: format!(
                        "the alternative `{}` of `{op_name}` cannot happen here; mark its arm `→ ⊥`",
                        contract_alt.name
                    ),
                });
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn check_loop_repeat_scope(
        &mut self,
        target_body: BodyId,
        r_i: Formula,
        line: u32,
        label: &str,
        visible_vars: &[(String, TermId, bool)],
        in_loop: bool,
    ) -> Result<(), Error> {
        let Some(pos) = self.active_scopes.iter().position(|&b| b == target_body) else {
            return Ok(());
        };
        let ended: Vec<BodyId> = self.active_scopes[pos..].to_vec();
        self.check_scope_obligations(&ended, r_i, line, visible_vars, in_loop)?;
        let outer_bodies: Vec<BodyId> = self.active_scopes[..pos].to_vec();
        if let Some(entry_avail) = self.loop_entry_avail.get(&target_body).cloned() {
            for (var, &entry_a) in entry_avail.iter().enumerate().take(self.body.vars.len()) {
                if !outer_bodies.contains(&self.body.vars[var].body) {
                    continue;
                }
                let cur_a = self.avail(var);
                let eq_entry = self.solver.bdd.iff(cur_a, entry_a);
                require_formula(
                    &mut self.solver,
                    r_i,
                    eq_entry,
                    &self.owner_name,
                    line,
                    "O6",
                    format!(
                        "outer `{}` does not match its loop-entry availability at `{label}`",
                        self.body.vars[var].name
                    ),
                    visible_vars,
                    in_loop,
                    self.certificates,
                )?;
            }
        }
        Ok(())
    }

    fn apply_call_exclusive_updates(
        &mut self,
        cid: ControlId,
        arguments: &[Expr],
        r_i: Formula,
        post_args: &mut [LinearTerm],
        env: &Env,
    ) {
        let param_tys: Vec<Type> = self.program.controls[cid]
            .parameters
            .iter()
            .map(|p| p.ty.clone())
            .collect();
        for (pidx, (arg, pty)) in arguments.iter().zip(&param_tys).enumerate() {
            if matches!(pty, Type::Ref(BorrowMode::Exclusive, _)) {
                let inner_ty = pty.deref_type();
                let z_tid = self.alloc_type_term("_mut", inner_ty);
                let z_term = LinearTerm::var(z_tid);
                post_args[pidx] = z_term.clone();
                match arg {
                    Expr::Borrow(BorrowMode::Exclusive, place, _) => {
                        self.apply_place_write(place, r_i, z_term, env);
                    }
                    Expr::Var(VarRef::Local(vid), _) => {
                        let place = Place {
                            root: *vid,
                            root_ty: pty.clone(),
                            steps: Vec::new(),
                            ty: inner_ty.clone(),
                        };
                        self.apply_place_write(&place, r_i, z_term, env);
                    }
                    _ => {}
                }
            } else if self.program.has_exclusive_borrow(pty) {
                self.invalidate_exclusive_view_arg(arg, r_i, env);
            }
        }
    }

    fn check_body(
        &mut self,
        body_id: BodyId,
        live: Formula,
        in_loop: bool,
        loop_leaves: &mut BTreeMap<BodyId, Vec<LeaveRecord>>,
    ) -> Result<(), Error> {
        self.check_body_inner(body_id, live, in_loop, loop_leaves, false)
            .map(|_| ())
    }

    fn check_body_inner(
        &mut self,
        body_id: BodyId,
        mut live: Formula,
        in_loop: bool,
        loop_leaves: &mut BTreeMap<BodyId, Vec<LeaveRecord>>,
        allow_fallthrough: bool,
    ) -> Result<Formula, Error> {
        let statements = self.body.bodies[body_id].statements.clone();
        let last_line = statements.last().map_or(1, |s| s.line);

        for (stmt_idx, statement) in statements.iter().enumerate() {
            let line = statement.line;
            self.at_line = line;
            let g_i = self.selector(&statement.selector);
            // [K2]: Rᵢ = Lᵢ ∧ gᵢ
            let r_i = self.solver.bdd.and(live, g_i);
            let (env, visible_vars) = self.current_env();
            self.stmt_r.insert((body_id, stmt_idx), r_i);
            self.stmt_visible
                .insert((body_id, stmt_idx), visible_vars.clone());

            match &statement.command {
                Command::Spawn { .. } | Command::Cancel { .. } => {
                    return Err(Error {
                        control: self.owner_name.clone(),
                        line,
                        clause: "TK1",
                        message: "static checking for Slice 4 tasks is scheduled for Phase 3"
                            .to_string(),
                        counterexample: None,
                    });
                }
                Command::Bind { var, value } => {
                    check_expr_obligations(
                        self.program,
                        &mut self.solver,
                        value,
                        r_i,
                        &env,
                        &self.owner_name,
                        line,
                        &visible_vars,
                        in_loop,
                        self.certificates,
                    )?;
                    self.check_consume_expr(value, r_i, line, &visible_vars, in_loop)?;
                    // [O1]: Θ ⊨ ¬(Rᵢ ∧ D(x))
                    let d_var = self.defined[*var];
                    let double_bind = self.solver.bdd.and(r_i, d_var);
                    require_entailment(
                        &mut self.solver,
                        double_bind,
                        &self.owner_name,
                        line,
                        "O1",
                        format!(
                            "`{}` may already be bound on this history",
                            self.body.vars[*var].name
                        ),
                        &visible_vars,
                        in_loop,
                        self.certificates,
                    )?;
                    self.bind_value(*var, r_i, value, &env);
                    self.defined[*var] = self.solver.bdd.or(self.defined[*var], r_i);
                    let not_ri = self.solver.bdd.not(r_i);
                    self.moved[*var] = self.solver.bdd.and(self.moved[*var], not_ri);
                    if let Expr::Borrow(_, place, _) = value {
                        self.bind_local_borrow(*var, r_i, place, &env);
                    } else if let Expr::Var(VarRef::Local(src), ty) = value
                        && matches!(ty, Type::Ref(_, _))
                        && let Some(entries) = self.local_borrows.get(src).cloned()
                    {
                        let dest = self.local_borrows.entry(*var).or_default();
                        for (bg, fp) in entries {
                            let g = self.solver.bdd.and(r_i, bg);
                            if g != bdd::FALSE {
                                dest.push((g, fp));
                            }
                        }
                    }
                    self.record_expr_loan_roots(*var, value, r_i);
                }
                Command::Unpack {
                    struct_id,
                    vars,
                    value,
                } => {
                    check_expr_obligations(
                        self.program,
                        &mut self.solver,
                        value,
                        r_i,
                        &env,
                        &self.owner_name,
                        line,
                        &visible_vars,
                        in_loop,
                        self.certificates,
                    )?;
                    self.check_consume_expr(value, r_i, line, &visible_vars, in_loop)?;
                    let val_term = translate_term(self.program, &mut self.solver, value, &env);
                    let mut field_terms = Vec::with_capacity(vars.len());
                    for (fidx, &var_id) in vars.iter().enumerate() {
                        let d_var = self.defined[var_id];
                        let double_bind = self.solver.bdd.and(r_i, d_var);
                        require_entailment(
                            &mut self.solver,
                            double_bind,
                            &self.owner_name,
                            line,
                            "O1",
                            format!(
                                "`{}` may already be bound on this history",
                                self.body.vars[var_id].name
                            ),
                            &visible_vars,
                            in_loop,
                            self.certificates,
                        )?;
                        let fty = self.program.structs[*struct_id].fields[fidx].ty.clone();
                        let ft = translate_field_term(
                            &mut self.solver,
                            val_term.clone(),
                            *struct_id,
                            fidx,
                            &fty,
                        );
                        let tid = self.bind_value_term(var_id, r_i, ft);
                        self.defined[var_id] = self.solver.bdd.or(self.defined[var_id], r_i);
                        let not_ri = self.solver.bdd.not(r_i);
                        self.moved[var_id] = self.solver.bdd.and(self.moved[var_id], not_ri);
                        self.record_expr_loan_roots(var_id, value, r_i);
                        field_terms.push(LinearTerm::var(tid));
                    }
                    let cid = self
                        .solver
                        .intern_term(AtomTerm::StructCtor(*struct_id, field_terms));
                    self.solver.instantiate_all();
                    let eq = self.solver.eq(&val_term, &LinearTerm::var(cid));
                    self.solver.add_fact(r_i, eq);
                }
                Command::Assign { var, value } => {
                    check_expr_obligations(
                        self.program,
                        &mut self.solver,
                        value,
                        r_i,
                        &env,
                        &self.owner_name,
                        line,
                        &visible_vars,
                        in_loop,
                        self.certificates,
                    )?;
                    self.check_consume_expr(value, r_i, line, &visible_vars, in_loop)?;
                    // [O4]: Θ ⊨ Rᵢ → D(x)
                    let d_var = self.defined[*var];
                    require_formula(
                        &mut self.solver,
                        r_i,
                        d_var,
                        &self.owner_name,
                        line,
                        "O4",
                        format!(
                            "`{}` has no slot on this history",
                            self.body.vars[*var].name
                        ),
                        &visible_vars,
                        in_loop,
                        self.certificates,
                    )?;
                    if self.program.kind(self.body.vars[*var].ty.deref_type()) == Kind::Must {
                        let m_var = self.moved[*var];
                        require_formula(
                            &mut self.solver,
                            r_i,
                            m_var,
                            &self.owner_name,
                            line,
                            "O4",
                            format!(
                                "`{}` holds an unconsumed `must` value and cannot be overwritten",
                                self.body.vars[*var].name
                            ),
                            &visible_vars,
                            in_loop,
                            self.certificates,
                        )?;
                    }
                    if matches!(self.body.vars[*var].ty, Type::Ref(BorrowMode::Exclusive, _)) {
                        let new_val = translate_term(self.program, &mut self.solver, value, &env);
                        let place = Place {
                            root: *var,
                            root_ty: self.body.vars[*var].ty.clone(),
                            steps: Vec::new(),
                            ty: self.body.vars[*var].ty.deref_type().clone(),
                        };
                        self.apply_place_write(&place, r_i, new_val, &env);
                    } else {
                        self.bind_value(*var, r_i, value, &env);
                        self.refresh_dependent_local_borrows(*var, r_i);
                    }
                    let not_ri = self.solver.bdd.not(r_i);
                    self.moved[*var] = self.solver.bdd.and(self.moved[*var], not_ri);
                }
                Command::AssignPlace { target, value } => {
                    check_expr_obligations(
                        self.program,
                        &mut self.solver,
                        value,
                        r_i,
                        &env,
                        &self.owner_name,
                        line,
                        &visible_vars,
                        in_loop,
                        self.certificates,
                    )?;
                    self.check_consume_expr(value, r_i, line, &visible_vars, in_loop)?;
                    self.check_available(target.root, r_i, line, &visible_vars, in_loop)?;
                    for step in &target.steps {
                        if let PlaceStep::Index(idx_expr, _) = step {
                            self.check_read_expr(idx_expr, r_i, line, &visible_vars, in_loop)?;
                        }
                    }
                    check_place_obligations(
                        self.program,
                        &mut self.solver,
                        target,
                        r_i,
                        &env,
                        &self.owner_name,
                        line,
                        &visible_vars,
                        in_loop,
                        self.certificates,
                    )?;
                    if self.program.kind(&target.ty) == Kind::Must
                        && self.is_feasible(r_i, &visible_vars, in_loop)
                    {
                        return Err(Error {
                            control: self.owner_name.clone(),
                            line,
                            clause: "O4",
                            message: "cannot assign to a place of kind `must`".to_string(),
                            counterexample: None,
                        });
                    }
                    let new_val = translate_term(self.program, &mut self.solver, value, &env);
                    self.apply_place_write(target, r_i, new_val, &env);
                }
                Command::Oblige(formula) => {
                    self.check_reads(formula, r_i, line, &visible_vars, in_loop)?;
                    let phi = translate_formula(self.program, &mut self.solver, formula, &env);
                    // [P1]: Θ; Rᵢ ⊨ φ
                    require_formula(
                        &mut self.solver,
                        r_i,
                        phi,
                        &self.owner_name,
                        line,
                        "P1",
                        "proof obligation may not hold",
                        &visible_vars,
                        in_loop,
                        self.certificates,
                    )?;
                    self.solver.add_fact(r_i, phi);
                }
                Command::Test { site, condition } => {
                    check_expr_obligations(
                        self.program,
                        &mut self.solver,
                        condition,
                        r_i,
                        &env,
                        &self.owner_name,
                        line,
                        &visible_vars,
                        in_loop,
                        self.certificates,
                    )?;
                    self.check_read_expr(condition, r_i, line, &visible_vars, in_loop)?;
                    let d_true = self.atom(*site, 0);
                    let d_false = self.atom(*site, 1);
                    // [K4]: d.true → Rᵢ, d.false → Rᵢ, ¬(d.true ∧ d.false)
                    let t_imp_r = self.solver.bdd.implies(d_true, r_i);
                    let f_imp_r = self.solver.bdd.implies(d_false, r_i);
                    let both = self.solver.bdd.and(d_true, d_false);
                    let not_both = self.solver.bdd.not(both);
                    // [K5]: Rᵢ → d.true ∨ d.false
                    let either = self.solver.bdd.or(d_true, d_false);
                    let r_imp_either = self.solver.bdd.implies(r_i, either);
                    self.solver.add_structure(t_imp_r);
                    self.solver.add_structure(f_imp_r);
                    self.solver.add_structure(not_both);
                    self.solver.add_structure(r_imp_either);

                    // [N4]: d.true ⇒ e, d.false ⇒ ¬e
                    let phi = translate_formula(self.program, &mut self.solver, condition, &env);
                    let not_phi = self.solver.bdd.not(phi);
                    self.solver.add_fact(d_true, phi);
                    self.solver.add_fact(d_false, not_phi);
                }
                Command::Capture {
                    var,
                    outcome_id: _,
                    operation,
                    arguments,
                } => {
                    let old_args: Vec<LinearTerm> = arguments
                        .iter()
                        .map(|a| translate_term(self.program, &mut self.solver, a, &env))
                        .collect();
                    let cap_param_tys: Option<Vec<Type>> = match operation {
                        Operation::Control(cid) => Some(
                            self.program.controls[*cid]
                                .parameters
                                .iter()
                                .map(|p| p.ty.clone())
                                .collect(),
                        ),
                        _ => None,
                    };
                    self.check_operands_o0(
                        arguments,
                        cap_param_tys.as_deref(),
                        r_i,
                        &env,
                        line,
                        &visible_vars,
                        in_loop,
                    )?;

                    let mut post_args = old_args.clone();
                    match operation {
                        Operation::Control(cid) => {
                            let callee = &self.program.controls[*cid];
                            if self.in_contingency
                                && !callee.contingent
                                && self.is_feasible(r_i, &visible_vars, in_loop)
                            {
                                return Err(Error {
                                    control: self.owner_name.clone(),
                                    line,
                                    clause: "F5",
                                    message: format!(
                                        "contingency may not call non-contingent `{}`",
                                        callee.name
                                    ),
                                    counterexample: None,
                                });
                            }
                            if callee.faults {
                                self.check_may_fault(r_i, line, &visible_vars, in_loop)?;
                            }
                            let uses = callee.uses.clone();
                            let callee_name = callee.name.clone();
                            self.check_effects(
                                &uses,
                                &callee_name,
                                r_i,
                                line,
                                &visible_vars,
                                in_loop,
                            )?;

                            if let Some(pre) = &self.program.controls[*cid].precondition.clone() {
                                let call_env = Env {
                                    locals: BTreeMap::new(),
                                    parameters: old_args.clone(),
                                    old_parameters: old_args.clone(),
                                    fields: Vec::new(),
                                    constants: BTreeMap::new(),
                                };
                                let pre_formula = translate_formula(
                                    self.program,
                                    &mut self.solver,
                                    pre,
                                    &call_env,
                                );
                                require_formula(
                                    &mut self.solver,
                                    r_i,
                                    pre_formula,
                                    &self.owner_name,
                                    line,
                                    "P3",
                                    format!(
                                        "precondition of `{}` may not hold",
                                        self.program.controls[*cid].name
                                    ),
                                    &visible_vars,
                                    in_loop,
                                    self.certificates,
                                )?;
                                self.solver.add_fact(r_i, pre_formula);
                            }

                            self.apply_call_exclusive_updates(
                                *cid,
                                arguments,
                                r_i,
                                &mut post_args,
                                &env,
                            );
                        }
                        Operation::Builtin {
                            op: BuiltinOp::Emit,
                            ..
                        } => {
                            let uses = vec!["console.write".to_string()];
                            self.check_effects(&uses, "emit", r_i, line, &visible_vars, in_loop)?;
                        }
                        _ => {}
                    }

                    // [O1] on `var`.
                    let d_var = self.defined[*var];
                    let double_bind = self.solver.bdd.and(r_i, d_var);
                    require_entailment(
                        &mut self.solver,
                        double_bind,
                        &self.owner_name,
                        line,
                        "O1",
                        format!(
                            "`{}` may already be bound on this history",
                            self.body.vars[*var].name
                        ),
                        &visible_vars,
                        in_loop,
                        self.certificates,
                    )?;
                    let tid = self.alloc_var_term(*var);
                    self.set_version(*var, r_i, tid);
                    self.defined[*var] = self.solver.bdd.or(self.defined[*var], r_i);
                    let not_ri = self.solver.bdd.not(r_i);
                    self.moved[*var] = self.solver.bdd.and(self.moved[*var], not_ri);
                    self.captured.entry(*var).or_default().push((
                        r_i,
                        CapturedInfo {
                            operation: operation.clone(),
                            old_args,
                            post_args,
                        },
                    ));
                }
                Command::Decide {
                    site,
                    operation: _,
                    op_kind,
                    arguments,
                    arms,
                } => {
                    let contract = op_kind.contract(self.program);
                    let op_name = op_kind.name(self.program).to_string();
                    // [C2]: Every alternative of the operation's contract is listed.
                    if arms.len() != contract.len() {
                        return Err(Error {
                            control: self.owner_name.clone(),
                            line,
                            clause: "C2",
                            message: format!(
                                "decision on `{op_name}` lists {} of {} alternatives",
                                arms.len(),
                                contract.len()
                            ),
                            counterexample: None,
                        });
                    }

                    let old_arg_terms: Vec<LinearTerm> = arguments
                        .iter()
                        .map(|a| translate_term(self.program, &mut self.solver, a, &env))
                        .collect();
                    let mut post_arg_terms = old_arg_terms.clone();

                    // Check [O0], [F5], [F1]/[F2]/[F6], [F3], [P3] depending on operation kind.
                    match op_kind {
                        Operation::AwaitControl(_)
                        | Operation::AwaitNext(_, _)
                        | Operation::RunControl(_) => {
                            return Err(Error {
                                control: self.owner_name.clone(),
                                line,
                                clause: "TK1",
                                message:
                                    "static checking for Slice 4 tasks is scheduled for Phase 3"
                                        .to_string(),
                                counterexample: None,
                            });
                        }
                        Operation::Control(cid) => {
                            let callee = &self.program.controls[*cid];
                            if self.in_contingency
                                && !callee.contingent
                                && self.is_feasible(r_i, &visible_vars, in_loop)
                            {
                                return Err(Error {
                                    control: self.owner_name.clone(),
                                    line,
                                    clause: "F5",
                                    message: format!(
                                        "contingency may not call non-contingent `{}`",
                                        callee.name
                                    ),
                                    counterexample: None,
                                });
                            }
                            let decide_param_tys: Vec<Type> =
                                callee.parameters.iter().map(|p| p.ty.clone()).collect();
                            self.check_operands_o0(
                                arguments,
                                Some(&decide_param_tys),
                                r_i,
                                &env,
                                line,
                                &visible_vars,
                                in_loop,
                            )?;
                            if self.program.controls[*cid].faults {
                                self.check_may_fault(r_i, line, &visible_vars, in_loop)?;
                            }
                            let uses = self.program.controls[*cid].uses.clone();
                            self.check_effects(&uses, &op_name, r_i, line, &visible_vars, in_loop)?;

                            if let Some(pre) = &self.program.controls[*cid].precondition.clone() {
                                let call_env = Env {
                                    locals: BTreeMap::new(),
                                    parameters: old_arg_terms.clone(),
                                    old_parameters: old_arg_terms.clone(),
                                    fields: Vec::new(),
                                    constants: BTreeMap::new(),
                                };
                                let pre_formula = translate_formula(
                                    self.program,
                                    &mut self.solver,
                                    pre,
                                    &call_env,
                                );
                                require_formula(
                                    &mut self.solver,
                                    r_i,
                                    pre_formula,
                                    &self.owner_name,
                                    line,
                                    "P3",
                                    format!("precondition of `{op_name}` may not hold"),
                                    &visible_vars,
                                    in_loop,
                                    self.certificates,
                                )?;
                                self.solver.add_fact(r_i, pre_formula);
                            }

                            self.apply_call_exclusive_updates(
                                *cid,
                                arguments,
                                r_i,
                                &mut post_arg_terms,
                                &env,
                            );
                        }
                        Operation::Builtin { op, .. } => {
                            self.check_operands_o0(
                                arguments,
                                None,
                                r_i,
                                &env,
                                line,
                                &visible_vars,
                                in_loop,
                            )?;
                            if *op == BuiltinOp::Emit {
                                let uses = vec!["console.write".to_string()];
                                self.check_effects(
                                    &uses,
                                    "emit",
                                    r_i,
                                    line,
                                    &visible_vars,
                                    in_loop,
                                )?;
                            }
                        }
                        Operation::Outcome(_) => {
                            self.check_operands_o0(
                                arguments,
                                None,
                                r_i,
                                &env,
                                line,
                                &visible_vars,
                                in_loop,
                            )?;
                        }
                        Operation::Variant { .. } => {
                            if let Some(arg) = arguments.first() {
                                check_expr_obligations(
                                    self.program,
                                    &mut self.solver,
                                    arg,
                                    r_i,
                                    &env,
                                    &self.owner_name,
                                    line,
                                    &visible_vars,
                                    in_loop,
                                    self.certificates,
                                )?;
                                self.check_consume_expr(arg, r_i, line, &visible_vars, in_loop)?;
                            }
                        }
                    }

                    let mut any_arm = bdd::FALSE;
                    let mut arm_atoms = Vec::new();
                    for pos in 0..arms.len() {
                        let atom = self.atom(*site, pos);
                        arm_atoms.push(atom);
                        any_arm = self.solver.bdd.or(any_arm, atom);
                        // [K4]: d.a → Rᵢ
                        let imp = self.solver.bdd.implies(atom, r_i);
                        self.solver.add_structure(imp);
                    }
                    // [K4]: ¬(d.a ∧ d.b)
                    for i in 0..arm_atoms.len() {
                        for j in (i + 1)..arm_atoms.len() {
                            let both = self.solver.bdd.and(arm_atoms[i], arm_atoms[j]);
                            let not_both = self.solver.bdd.not(both);
                            self.solver.add_structure(not_both);
                        }
                    }

                    let (is_pure, pure_cid) = match op_kind {
                        Operation::Control(cid) if self.program.controls[*cid].is_pure() => {
                            (true, Some(*cid))
                        }
                        _ => (false, None),
                    };
                    let pure_alt_term = pure_cid.map(|cid| {
                        let id = self
                            .solver
                            .intern_term(AtomTerm::PureAlt(cid, old_arg_terms.clone()));
                        self.solver.instantiate_all();
                        LinearTerm::var(id)
                    });

                    // Snapshot captured entries if deciding an outcome variable.
                    let outcome_captures = match op_kind {
                        Operation::Outcome(_) => match arguments.first() {
                            Some(Expr::Var(VarRef::Local(v), _)) => self.captured.get(v).cloned(),
                            Some(Expr::Move(inner, _)) => match &**inner {
                                Expr::Var(VarRef::Local(v), _) => self.captured.get(v).cloned(),
                                _ => None,
                            },
                            _ => None,
                        },
                        _ => None,
                    };

                    for (pos, arm) in arms.iter().enumerate() {
                        let atom = arm_atoms[pos];
                        let contract_alt = &contract[arm.alternative];
                        let mut field_terms = Vec::new();

                        for (field_idx, &var_id) in arm.vars.iter().enumerate() {
                            // [O1]: Θ ⊨ ¬(d.a ∧ D(x))
                            let d_var = self.defined[var_id];
                            let double_bind = self.solver.bdd.and(atom, d_var);
                            require_entailment(
                                &mut self.solver,
                                double_bind,
                                &self.owner_name,
                                line,
                                "O1",
                                format!(
                                    "`{}` may already be bound on this history",
                                    self.body.vars[var_id].name
                                ),
                                &visible_vars,
                                in_loop,
                                self.certificates,
                            )?;
                            let tid = self.alloc_var_term(var_id);
                            let v_term = LinearTerm::var(tid);
                            self.set_version(var_id, atom, tid);
                            self.defined[var_id] = self.solver.bdd.or(self.defined[var_id], atom);
                            let not_atom = self.solver.bdd.not(atom);
                            self.moved[var_id] = self.solver.bdd.and(self.moved[var_id], not_atom);
                            if let Some(field) = contract_alt.fields.get(field_idx)
                                && self.program.contains_borrow_or_view(&field.ty)
                            {
                                for &oidx in &field.origins {
                                    if let Some(arg) = arguments.get(oidx) {
                                        self.record_expr_loan_roots(var_id, arg, atom);
                                    }
                                }
                            }

                            if let Some(cid) = pure_cid {
                                let pay_id = self.solver.intern_term(AtomTerm::PurePay(
                                    cid,
                                    arm.alternative,
                                    field_idx,
                                    old_arg_terms.clone(),
                                ));
                                self.solver.instantiate_all();
                                let eq = self.solver.eq(&v_term, &LinearTerm::var(pay_id));
                                self.solver.add_fact(atom, eq);
                            }
                            field_terms.push(v_term);
                        }

                        if let Some(alt_term) = &pure_alt_term {
                            let eq = self
                                .solver
                                .eq(alt_term, &LinearTerm::from_i128(arm.alternative as i128));
                            self.solver.add_fact(atom, eq);
                        }

                        match op_kind {
                            Operation::AwaitControl(_)
                            | Operation::AwaitNext(_, _)
                            | Operation::RunControl(_) => {}
                            Operation::Control(_) => {
                                if let Some(cond) = &contract_alt.condition {
                                    let cond_env = Env {
                                        locals: BTreeMap::new(),
                                        parameters: post_arg_terms.clone(),
                                        old_parameters: old_arg_terms.clone(),
                                        fields: field_terms,
                                        constants: BTreeMap::new(),
                                    };
                                    let cond_formula = translate_formula(
                                        self.program,
                                        &mut self.solver,
                                        cond,
                                        &cond_env,
                                    );
                                    self.solver.add_fact(atom, cond_formula);
                                }
                            }
                            Operation::Builtin { op, target, .. } => {
                                self.apply_builtin_facts(
                                    *op,
                                    target.as_ref(),
                                    &old_arg_terms,
                                    arm.alternative,
                                    atom,
                                    &field_terms,
                                    &env,
                                );
                            }
                            Operation::Variant { id: vid, .. } => {
                                // [I11]: `d.c ⇒ x = V.c {ȳ}`
                                if let Some(scrutinee) = old_arg_terms.first() {
                                    let num_ctors = self.program.variants[*vid].constructors.len();
                                    let ctor_id = self.solver.intern_term(AtomTerm::VariantCtor {
                                        variant_id: *vid,
                                        ctor_idx: arm.alternative,
                                        fields: field_terms,
                                        num_ctors,
                                    });
                                    self.solver.instantiate_all();
                                    let eq = self.solver.eq(scrutinee, &LinearTerm::var(ctor_id));
                                    self.solver.add_fact(atom, eq);
                                }
                            }
                            Operation::Outcome(_) => {
                                // [I12]: Conditions of the captured operation over capture arguments.
                                if let Some(entries) = &outcome_captures {
                                    for (cap_guard, info) in entries {
                                        let g = self.solver.bdd.and(*cap_guard, atom);
                                        if g == bdd::FALSE {
                                            continue;
                                        }
                                        match &info.operation {
                                            Operation::Control(cid) => {
                                                if let Some(cond) = &self.program.controls[*cid]
                                                    .contract[arm.alternative]
                                                    .condition
                                                {
                                                    let cond_env = Env {
                                                        locals: BTreeMap::new(),
                                                        parameters: info.post_args.clone(),
                                                        old_parameters: info.old_args.clone(),
                                                        fields: field_terms.clone(),
                                                        constants: BTreeMap::new(),
                                                    };
                                                    let cf = translate_formula(
                                                        self.program,
                                                        &mut self.solver,
                                                        cond,
                                                        &cond_env,
                                                    );
                                                    self.solver.add_fact(g, cf);
                                                }
                                            }
                                            Operation::Builtin { op, .. } => {
                                                self.apply_builtin_facts(
                                                    *op,
                                                    None,
                                                    &info.old_args,
                                                    arm.alternative,
                                                    g,
                                                    &field_terms,
                                                    &env,
                                                );
                                            }
                                            _ => {}
                                        }
                                    }
                                } else if let Some(cond) = &contract_alt.condition {
                                    let max_p = max_param_index(cond);
                                    let mut fresh_params = Vec::with_capacity(max_p);
                                    for p in 0..max_p {
                                        let tid = self.solver.fresh_var(
                                            format!("_out_arg{p}"),
                                            None,
                                            false,
                                        );
                                        fresh_params.push(LinearTerm::var(tid));
                                    }
                                    let cond_env = Env {
                                        locals: BTreeMap::new(),
                                        parameters: fresh_params.clone(),
                                        old_parameters: fresh_params,
                                        fields: field_terms,
                                        constants: BTreeMap::new(),
                                    };
                                    let cf = translate_formula(
                                        self.program,
                                        &mut self.solver,
                                        cond,
                                        &cond_env,
                                    );
                                    self.solver.add_fact(atom, cf);
                                }
                            }
                        }
                    }

                    let always_check_u16 = matches!(op_kind, Operation::Outcome(_))
                        || matches!(
                            op_kind,
                            Operation::Builtin {
                                op: BuiltinOp::Pop
                                    | BuiltinOp::Take
                                    | BuiltinOp::Insert
                                    | BuiltinOp::Remove
                                    | BuiltinOp::Get
                                    | BuiltinOp::EntryAt,
                                ..
                            }
                        );
                    self.warn_unreachable_arms(
                        &op_name,
                        line,
                        &statements,
                        &contract,
                        arms,
                        &arm_atoms,
                        is_pure,
                        always_check_u16,
                        r_i,
                        &visible_vars,
                        in_loop,
                    );

                    // [K3]: Lᵢ₊₁ = Lᵢ ∧ (gᵢ → d.a₁ ∨ … ∨ d.aₙ)
                    let g_imp_any = self.solver.bdd.implies(g_i, any_arm);
                    live = self.solver.bdd.and(live, g_imp_any);
                }
                Command::Loop {
                    site,
                    body: loop_body,
                    initial,
                    arms,
                } => {
                    self.check_operands_o0(initial, None, r_i, &env, line, &visible_vars, in_loop)?;

                    let head = self.body.bodies[*loop_body]
                        .head
                        .as_ref()
                        .expect("a loop head")
                        .clone();

                    // [P2]: Loop invariant holds for the initial arguments at entry.
                    if let Some(inv) = &head.invariant {
                        let mut init_env = env.clone();
                        for (&param_var, init_expr) in head.parameters.iter().zip(initial) {
                            let init_term =
                                translate_term(self.program, &mut self.solver, init_expr, &env);
                            init_env.locals.insert(param_var, init_term);
                        }
                        let inv_entry =
                            translate_formula(self.program, &mut self.solver, inv, &init_env);
                        require_formula(
                            &mut self.solver,
                            r_i,
                            inv_entry,
                            &self.owner_name,
                            line,
                            "P2",
                            format!("invariant of loop `{}` may not hold at entry", head.name),
                            &visible_vars,
                            in_loop,
                            self.certificates,
                        )?;
                    }

                    // Save outer state before checking the generic iteration ([K6], [N5], [O6]).
                    let saved_defined = self.defined.clone();
                    let saved_moved = self.moved.clone();
                    let saved_versions = self.versions.clone();
                    let mut entry_avail = Vec::with_capacity(self.body.vars.len());
                    for v in 0..self.body.vars.len() {
                        entry_avail.push(self.avail(v));
                    }
                    self.loop_entry_avail.insert(*loop_body, entry_avail);

                    for (&param_var, init_expr) in head.parameters.iter().zip(initial) {
                        self.record_expr_loan_roots(param_var, init_expr, r_i);
                    }
                    self.collect_loop_again_root_vars(*loop_body, r_i);

                    // [N5], [I9]: Give fresh logical names to loop parameters
                    // and to outer names that the loop body can change.
                    let mut modified_outer = BTreeSet::new();
                    collect_modified_vars(self.program, self.body, *loop_body, &mut modified_outer);
                    self.close_modified_with_borrows(&mut modified_outer);
                    for &var in &modified_outer {
                        if self.body.vars[var].body != *loop_body && self.defined[var] != bdd::FALSE
                        {
                            let fresh_tid = self.alloc_var_term(var);
                            let active_on_loop = self.solver.bdd.and(self.defined[var], r_i);
                            self.set_version(var, active_on_loop, fresh_tid);
                        }
                    }

                    for &param_var in &head.parameters {
                        let tid = self.alloc_var_term(param_var);
                        self.defined[param_var] = r_i;
                        let not_ri = self.solver.bdd.not(r_i);
                        self.moved[param_var] = self.solver.bdd.and(self.moved[param_var], not_ri);
                        self.versions[param_var] = vec![(r_i, tid)];
                    }

                    // [N4]: Inside the loop body, the invariant is assumed on R_d.
                    if let Some(inv) = &head.invariant {
                        let (iter_env, _) = self.current_env();
                        let inv_iter =
                            translate_formula(self.program, &mut self.solver, inv, &iter_env);
                        self.solver.add_fact(r_i, inv_iter);
                    }

                    loop_leaves.insert(*loop_body, Vec::new());
                    self.active_scopes.push(*loop_body);
                    // [K6]: Check the loop body for one generic iteration with L₁ = R_d.
                    self.check_body_inner(*loop_body, r_i, true, loop_leaves, false)?;
                    self.active_scopes.pop();
                    self.loop_entry_avail.remove(loop_body);
                    let leaves = loop_leaves.remove(loop_body).unwrap_or_default();

                    // Restore outer definedness and link post-loop facts ([K8], [O6]).
                    self.defined = saved_defined;
                    self.moved = saved_moved;
                    self.versions = saved_versions;

                    let mut any_arm = bdd::FALSE;
                    let mut arm_atoms = Vec::new();
                    for alt_idx in 0..arms.len() {
                        let atom = self.atom(*site, alt_idx);
                        arm_atoms.push(atom);
                        any_arm = self.solver.bdd.or(any_arm, atom);
                        // [K4]: d.a → Rᵢ
                        let imp = self.solver.bdd.implies(atom, r_i);
                        self.solver.add_structure(imp);

                        // [K8]: d.a ↔ R_{j₁} ∨ … ∨ R_{jₖ}
                        let mut leave_disj = bdd::FALSE;
                        for (leave_alt, r_j, _, _, _, _, _) in &leaves {
                            if *leave_alt == alt_idx {
                                leave_disj = self.solver.bdd.or(leave_disj, *r_j);
                            }
                        }
                        let iff = self.solver.bdd.iff(atom, leave_disj);
                        self.solver.add_structure(iff);
                    }
                    for i in 0..arm_atoms.len() {
                        for j in (i + 1)..arm_atoms.len() {
                            let both = self.solver.bdd.and(arm_atoms[i], arm_atoms[j]);
                            let not_both = self.solver.bdd.not(both);
                            self.solver.add_structure(not_both);
                        }
                    }

                    // Update modified outer variables on the histories where the loop left ([K8]).
                    for (_, r_j, _, leave_versions, _, _, _) in &leaves {
                        for &var in &modified_outer {
                            if self.body.vars[var].body != *loop_body {
                                let mux = self.alloc_var_term(var);
                                for &(h, tid) in &leave_versions[var] {
                                    let on_leave = self.solver.bdd.and(*r_j, h);
                                    if on_leave != bdd::FALSE {
                                        self.solver.add_def_linear(
                                            on_leave,
                                            mux,
                                            LinearTerm::var(tid),
                                        );
                                    }
                                }
                                self.set_version(var, *r_j, mux);
                            }
                        }
                    }

                    // [O6](b): `□ a` leaves must agree on every outer variable's availability.
                    for (alt_idx, &atom) in arm_atoms.iter().enumerate() {
                        for var in 0..self.body.vars.len() {
                            if !self.active_scopes.contains(&self.body.vars[var].body) {
                                continue;
                            }
                            let mut same_as_entry_bad = bdd::FALSE;
                            let mut moved_bad = bdd::FALSE;
                            let mut avail_bad = bdd::FALSE;
                            let entry_a = self.avail(var);
                            let mut has_leaf = false;
                            for (leave_alt, r_j, _, _, l_def, l_mov, _) in &leaves {
                                if *leave_alt != alt_idx {
                                    continue;
                                }
                                has_leaf = true;
                                let not_lmov = self.solver.bdd.not(l_mov[var]);
                                let l_avail = self.solver.bdd.and(l_def[var], not_lmov);
                                let eq_entry = self.solver.bdd.iff(l_avail, entry_a);
                                let not_eq_entry = self.solver.bdd.not(eq_entry);
                                let b_entry = self.solver.bdd.and(*r_j, not_eq_entry);
                                same_as_entry_bad = self.solver.bdd.or(same_as_entry_bad, b_entry);

                                let b_mov = self.solver.bdd.and(*r_j, l_avail);
                                moved_bad = self.solver.bdd.or(moved_bad, b_mov);

                                let not_lav = self.solver.bdd.not(l_avail);
                                let b_av = self.solver.bdd.and(*r_j, not_lav);
                                avail_bad = self.solver.bdd.or(avail_bad, b_av);
                            }
                            if !has_leaf || same_as_entry_bad == bdd::FALSE {
                                continue;
                            }
                            let about = "the ownership of a name after a loop";
                            if self.has_no_model(
                                same_as_entry_bad,
                                &visible_vars,
                                in_loop,
                                "O6",
                                about,
                            ) {
                                continue;
                            }
                            if self.has_no_model(moved_bad, &visible_vars, in_loop, "O6", about) {
                                self.moved[var] = self.solver.bdd.or(self.moved[var], atom);
                                continue;
                            }
                            if self.has_no_model(avail_bad, &visible_vars, in_loop, "O6", about) {
                                self.defined[var] = self.solver.bdd.or(self.defined[var], atom);
                                let not_atom = self.solver.bdd.not(atom);
                                self.moved[var] = self.solver.bdd.and(self.moved[var], not_atom);
                                continue;
                            }
                            require_entailment(
                                &mut self.solver,
                                same_as_entry_bad,
                                &self.owner_name,
                                line,
                                "O6",
                                format!(
                                    "loop leaves disagree on ownership of outer `{}`",
                                    self.body.vars[var].name
                                ),
                                &visible_vars,
                                in_loop,
                                self.certificates,
                            )?;
                        }
                    }

                    // Bind loop arm payload variables ([O1], [K8]).
                    for (alt_idx, arm_vars) in arms.iter().enumerate() {
                        let atom = arm_atoms[alt_idx];
                        for (field_pos, &var_id) in arm_vars.iter().enumerate() {
                            let d_var = self.defined[var_id];
                            let double_bind = self.solver.bdd.and(atom, d_var);
                            require_entailment(
                                &mut self.solver,
                                double_bind,
                                &self.owner_name,
                                line,
                                "O1",
                                format!(
                                    "`{}` may already be bound on this history",
                                    self.body.vars[var_id].name
                                ),
                                &visible_vars,
                                in_loop,
                                self.certificates,
                            )?;
                            let out_tid = self.alloc_var_term(var_id);
                            let out_is_borrow_or_view = self
                                .program
                                .contains_borrow_or_view(&self.body.vars[var_id].ty);
                            for (leave_alt, r_j, payload_terms, _, _, _, payload_roots) in &leaves {
                                if *leave_alt == alt_idx {
                                    if let Some(val_term) = payload_terms.get(field_pos) {
                                        if *self.body.vars[var_id].ty.deref_type() == Type::Bool {
                                            let b =
                                                self.solver.le(&LinearTerm::from_i128(1), val_term);
                                            self.solver.add_def_bool(*r_j, out_tid, b);
                                        } else {
                                            self.solver.add_def_linear(
                                                *r_j,
                                                out_tid,
                                                val_term.clone(),
                                            );
                                        }
                                    }
                                    if out_is_borrow_or_view
                                        && let Some(proots) = payload_roots.get(field_pos)
                                    {
                                        for &(lg, rv) in proots {
                                            if !self.var_in_body_tree(rv, *loop_body) {
                                                let rj_lg = self.solver.bdd.and(*r_j, lg);
                                                let g = self.solver.bdd.and(atom, rj_lg);
                                                self.push_var_loan_root(var_id, g, rv);
                                            }
                                        }
                                    }
                                }
                            }
                            self.set_version(var_id, atom, out_tid);
                            self.defined[var_id] = self.solver.bdd.or(self.defined[var_id], atom);
                            let not_atom = self.solver.bdd.not(atom);
                            self.moved[var_id] = self.solver.bdd.and(self.moved[var_id], not_atom);
                        }
                    }

                    // [K3]: Lᵢ₊₁ = Lᵢ ∧ (gᵢ → d.a₁ ∨ … ∨ d.aₙ)
                    let g_imp_any = self.solver.bdd.implies(g_i, any_arm);
                    live = self.solver.bdd.and(live, g_imp_any);
                }
                Command::Boundary {
                    site,
                    body: b1_body,
                    captures,
                    contingency_vars,
                    message_var,
                    contingency: b2_body,
                } => {
                    // [F5]: Captured names must own their values, be available, and move.
                    let mut cap_terms = Vec::with_capacity(captures.len());
                    for &cap_var in captures {
                        self.check_available(cap_var, r_i, line, &visible_vars, in_loop)?;
                        let cap_term = env
                            .locals
                            .get(&cap_var)
                            .cloned()
                            .unwrap_or_else(|| LinearTerm::from_i128(0));
                        cap_terms.push(cap_term);
                        if self.program.kind(&self.body.vars[cap_var].ty) != Kind::Copy {
                            self.moved[cap_var] = self.solver.bdd.or(self.moved[cap_var], r_i);
                        }
                    }

                    let outer_defined = self.defined.clone();
                    let outer_moved = self.moved.clone();
                    let outer_versions = self.versions.clone();
                    let outer_permits_faults = self.permits_faults;
                    let outer_in_contingency = self.in_contingency;

                    // Check `B₁` with fault permission enabled ([F5]).
                    self.active_scopes.push(*b1_body);
                    self.permits_faults = true;
                    self.in_contingency = false;
                    let b1_exit_live =
                        self.check_body_inner(*b1_body, r_i, in_loop, loop_leaves, true)?;
                    self.boundary_fallthrough_live
                        .insert(*b1_body, b1_exit_live);
                    let (_, b1_visible) = self.current_env();
                    self.check_scope_obligations(
                        &[*b1_body],
                        b1_exit_live,
                        line,
                        &b1_visible,
                        in_loop,
                    )?;
                    self.active_scopes.pop();
                    let b1_end_defined = self.defined.clone();
                    let b1_end_moved = self.moved.clone();
                    let b1_end_versions = self.versions.clone();

                    // Check `B₂` (`contingency`) with outer state reset and captures + message bound.
                    self.defined = outer_defined.clone();
                    self.moved = outer_moved.clone();
                    self.versions = outer_versions.clone();
                    let mut b1_modified = BTreeSet::new();
                    collect_modified_vars(self.program, self.body, *b1_body, &mut b1_modified);
                    self.close_modified_with_borrows(&mut b1_modified);
                    for &var in &b1_modified {
                        if self.active_scopes.contains(&self.body.vars[var].body)
                            && self.defined[var] != bdd::FALSE
                        {
                            let fresh_tid = self.alloc_var_term(var);
                            let on_b2 = self.solver.bdd.and(self.defined[var], r_i);
                            self.set_version(var, on_b2, fresh_tid);
                        }
                    }
                    for (cvar, cap_term) in contingency_vars.iter().zip(&cap_terms) {
                        let _ = self.bind_value_term(*cvar, r_i, cap_term.clone());
                        self.defined[*cvar] = self.solver.bdd.or(self.defined[*cvar], r_i);
                        let not_ri = self.solver.bdd.not(r_i);
                        self.moved[*cvar] = self.solver.bdd.and(self.moved[*cvar], not_ri);
                    }
                    if let Some(mvar) = message_var {
                        let mtid = self.alloc_var_term(*mvar);
                        self.set_version(*mvar, r_i, mtid);
                        self.defined[*mvar] = self.solver.bdd.or(self.defined[*mvar], r_i);
                        let not_ri = self.solver.bdd.not(r_i);
                        self.moved[*mvar] = self.solver.bdd.and(self.moved[*mvar], not_ri);
                    }
                    self.active_scopes.push(*b2_body);
                    self.permits_faults = outer_permits_faults;
                    self.in_contingency = true;
                    self.check_body_inner(*b2_body, r_i, in_loop, loop_leaves, false)?;
                    self.active_scopes.pop();

                    // Restore flags and merge `B₁` fallthrough state with bypassed `!g_i` histories.
                    self.permits_faults = outer_permits_faults;
                    self.in_contingency = outer_in_contingency;
                    let bypassed = self.solver.bdd.minus(live, g_i);
                    for v in 0..self.body.vars.len() {
                        let left_d = self.solver.bdd.and(outer_defined[v], bypassed);
                        let right_d = self.solver.bdd.and(b1_end_defined[v], b1_exit_live);
                        self.defined[v] = self.solver.bdd.or(left_d, right_d);

                        let left_m = self.solver.bdd.and(outer_moved[v], bypassed);
                        let right_m = self.solver.bdd.and(b1_end_moved[v], b1_exit_live);
                        self.moved[v] = self.solver.bdd.or(left_m, right_m);

                        let mut merged = Vec::new();
                        for (g, tid) in &outer_versions[v] {
                            let mg = self.solver.bdd.and(*g, bypassed);
                            if mg != bdd::FALSE {
                                merged.push((mg, *tid));
                            }
                        }
                        for (g, tid) in &b1_end_versions[v] {
                            let mg = self.solver.bdd.and(*g, b1_exit_live);
                            if mg != bdd::FALSE {
                                merged.push((mg, *tid));
                            }
                        }
                        self.versions[v] = merged;
                    }
                    let d_done = self.atom(*site, 0);
                    let iff = self.solver.bdd.iff(d_done, b1_exit_live);
                    self.solver.add_structure(iff);
                    let g_imp_done = self.solver.bdd.implies(g_i, d_done);
                    live = self.solver.bdd.and(live, g_imp_done);
                }
                Command::Supervise {
                    boundary: bid,
                    arguments,
                } => {
                    let bdef = &self.program.boundaries[*bid];
                    let bname = bdef.name.clone();
                    if self.in_contingency && self.is_feasible(r_i, &visible_vars, in_loop) {
                        return Err(Error {
                            control: self.owner_name.clone(),
                            line,
                            clause: "F5",
                            message: format!("contingency may not supervise boundary `{bname}`"),
                            counterexample: None,
                        });
                    }
                    let b_param_tys: Vec<Type> =
                        bdef.parameters.iter().map(|p| p.ty.clone()).collect();
                    self.check_operands_o0(
                        arguments,
                        Some(&b_param_tys),
                        r_i,
                        &env,
                        line,
                        &visible_vars,
                        in_loop,
                    )?;
                    let uses = bdef.uses.clone();
                    self.check_effects(&uses, &bname, r_i, line, &visible_vars, in_loop)?;
                    if self.boundary_may_fault[*bid] {
                        self.check_may_fault(r_i, line, &visible_vars, in_loop)?;
                    }
                }
                Command::Again {
                    body: target_body,
                    arguments,
                } => {
                    self.check_operands_o0(
                        arguments,
                        None,
                        r_i,
                        &env,
                        line,
                        &visible_vars,
                        in_loop,
                    )?;
                    let head = self.body.bodies[*target_body]
                        .head
                        .as_ref()
                        .expect("a loop head")
                        .clone();
                    // [P2]: Loop invariant holds for the new arguments at `↑`.
                    if let Some(inv) = &head.invariant {
                        let mut next_env = env.clone();
                        for (&param_var, arg_expr) in head.parameters.iter().zip(arguments) {
                            let arg_term =
                                translate_term(self.program, &mut self.solver, arg_expr, &env);
                            next_env.locals.insert(param_var, arg_term);
                        }
                        let inv_again =
                            translate_formula(self.program, &mut self.solver, inv, &next_env);
                        require_formula(
                            &mut self.solver,
                            r_i,
                            inv_again,
                            &self.owner_name,
                            line,
                            "P2",
                            format!("invariant of loop `{}` may not hold at `↑`", head.name),
                            &visible_vars,
                            in_loop,
                            self.certificates,
                        )?;
                    }
                    self.check_loop_repeat_scope(
                        *target_body,
                        r_i,
                        line,
                        "↑",
                        &visible_vars,
                        in_loop,
                    )?;
                    // [K3]: Lᵢ₊₁ = Lᵢ ∧ ¬gᵢ
                    live = self.solver.bdd.minus(live, g_i);
                }
                Command::Leave {
                    alternative,
                    payload,
                } => {
                    self.check_operands_o0(payload, None, r_i, &env, line, &visible_vars, in_loop)?;
                    let payload_terms: Vec<LinearTerm> = payload
                        .iter()
                        .map(|e| translate_term(self.program, &mut self.solver, e, &env))
                        .collect();
                    let payload_roots: Vec<Vec<(Formula, VarId)>> = payload
                        .iter()
                        .map(|e| self.expr_loan_roots(e, bdd::TRUE))
                        .collect();
                    let target_loop_pos = self
                        .active_scopes
                        .iter()
                        .rposition(|&b| self.body.bodies[b].head.is_some());
                    if let Some(pos) = target_loop_pos {
                        let target_loop = self.active_scopes[pos];
                        let ended: Vec<BodyId> = self.active_scopes[pos..].to_vec();
                        self.check_scope_obligations(&ended, r_i, line, &visible_vars, in_loop)?;
                        if let Some(list) = loop_leaves.get_mut(&target_loop) {
                            list.push((
                                *alternative,
                                r_i,
                                payload_terms,
                                self.versions.clone(),
                                self.defined.clone(),
                                self.moved.clone(),
                                payload_roots,
                            ));
                        }
                    }
                    // [K3]: Lᵢ₊₁ = Lᵢ ∧ ¬gᵢ
                    live = self.solver.bdd.minus(live, g_i);
                }
                Command::Exit {
                    alternative,
                    payload,
                } => {
                    self.check_operands_o0(payload, None, r_i, &env, line, &visible_vars, in_loop)?;
                    let entry = &self.contract[*alternative];
                    // [P4]: Contract condition `⇐ φₐ` at `■`.
                    if let Some(cond) = &entry.condition {
                        let payload_terms: Vec<LinearTerm> = payload
                            .iter()
                            .map(|e| translate_term(self.program, &mut self.solver, e, &env))
                            .collect();
                        let exit_parameters: Vec<LinearTerm> = self
                            .param_types
                            .iter()
                            .enumerate()
                            .map(|(pidx, pty)| {
                                if self.program.has_exclusive_borrow(pty) {
                                    env.locals
                                        .get(&pidx)
                                        .cloned()
                                        .unwrap_or_else(|| self.entry_parameters[pidx].clone())
                                } else {
                                    self.entry_parameters[pidx].clone()
                                }
                            })
                            .collect();
                        let exit_env = Env {
                            locals: BTreeMap::new(),
                            parameters: exit_parameters,
                            old_parameters: self.entry_parameters.clone(),
                            fields: payload_terms,
                            constants: BTreeMap::new(),
                        };
                        let cond_formula =
                            translate_formula(self.program, &mut self.solver, cond, &exit_env);
                        require_formula(
                            &mut self.solver,
                            r_i,
                            cond_formula,
                            &self.owner_name,
                            line,
                            "P4",
                            format!(
                                "condition of exit alternative `{}` may not hold",
                                entry.name
                            ),
                            &visible_vars,
                            in_loop,
                            self.certificates,
                        )?;
                    }
                    let all_scopes = self.active_scopes.clone();
                    self.check_scope_obligations(&all_scopes, r_i, line, &visible_vars, in_loop)?;
                    // [K3]: Lᵢ₊₁ = Lᵢ ∧ ¬gᵢ
                    live = self.solver.bdd.minus(live, g_i);
                }
                Command::Fault {
                    message,
                    assumed: _,
                } => {
                    check_expr_obligations(
                        self.program,
                        &mut self.solver,
                        message,
                        r_i,
                        &env,
                        &self.owner_name,
                        line,
                        &visible_vars,
                        in_loop,
                        self.certificates,
                    )?;
                    self.check_consume_expr(message, r_i, line, &visible_vars, in_loop)?;
                    self.check_may_fault(r_i, line, &visible_vars, in_loop)?;
                    if self.in_contingency && self.is_feasible(r_i, &visible_vars, in_loop) {
                        self.boundary_can_fault = true;
                    }
                    // [K3]: Lᵢ₊₁ = Lᵢ ∧ ¬gᵢ
                    live = self.solver.bdd.minus(live, g_i);
                }
                Command::Escalate => {
                    self.check_may_fault(r_i, line, &visible_vars, in_loop)?;
                    if self.in_contingency && self.is_feasible(r_i, &visible_vars, in_loop) {
                        self.boundary_can_fault = true;
                    }
                    // [K3]: Lᵢ₊₁ = Lᵢ ∧ ¬gᵢ
                    live = self.solver.bdd.minus(live, g_i);
                }
                Command::Terminate(_) => {
                    let all_scopes = self.active_scopes.clone();
                    self.check_scope_obligations(&all_scopes, r_i, line, &visible_vars, in_loop)?;
                    // [K3]: Lᵢ₊₁ = Lᵢ ∧ ¬gᵢ
                    live = self.solver.bdd.minus(live, g_i);
                }
                Command::Recover { body: target_body } => {
                    if let Some(inv) = self.body.bodies[*target_body]
                        .head
                        .as_ref()
                        .expect("a loop head")
                        .invariant
                        .clone()
                    {
                        let inv_rec = translate_formula(self.program, &mut self.solver, &inv, &env);
                        require_formula(
                            &mut self.solver,
                            r_i,
                            inv_rec,
                            &self.owner_name,
                            line,
                            "P2",
                            "loop invariant may not hold at `recover ↑`",
                            &visible_vars,
                            in_loop,
                            self.certificates,
                        )?;
                    }
                    self.check_loop_repeat_scope(
                        *target_body,
                        r_i,
                        line,
                        "recover ↑",
                        &visible_vars,
                        in_loop,
                    )?;
                    // [K3]: Lᵢ₊₁ = Lᵢ ∧ ¬gᵢ
                    live = self.solver.bdd.minus(live, g_i);
                }
                Command::Impossible => {
                    // [P6]: Θ ⊨ ¬Rᵢ
                    require_entailment(
                        &mut self.solver,
                        r_i,
                        &self.owner_name,
                        line,
                        "P6",
                        "`⊥` may be reachable on this history",
                        &visible_vars,
                        in_loop,
                        self.certificates,
                    )?;
                    // [K3]: Lᵢ₊₁ = Lᵢ ∧ ¬gᵢ
                    live = self.solver.bdd.minus(live, g_i);
                }
            }
        }

        if !allow_fallthrough {
            // [K7] Coverage: Θ ⊨ ¬Lₙ₊₁
            let (_, visible_vars) = self.current_env();
            require_entailment(
                &mut self.solver,
                live,
                &self.owner_name,
                last_line,
                "K7",
                "a feasible history reaches the end of the body without a disposition",
                &visible_vars,
                in_loop,
                self.certificates,
            )?;
        }
        Ok(live)
    }
}

fn freeze_place(program: &Program, solver: &mut Solver, place: &Place, env: &Env) -> FrozenPlace {
    let steps = place
        .steps
        .iter()
        .map(|s| match s {
            PlaceStep::Field(sid, fidx, ty) => FrozenStep::Field(*sid, *fidx, ty.clone()),
            PlaceStep::Index(idx_expr, ty) => {
                let it = translate_term(program, solver, idx_expr, env);
                FrozenStep::Index(it, ty.clone())
            }
        })
        .collect();
    FrozenPlace {
        root: place.root,
        root_ty: place.root_ty.clone(),
        steps,
    }
}

fn functional_update_frozen(
    program: &Program,
    solver: &mut Solver,
    cur_term: LinearTerm,
    cur_ty: &Type,
    steps: &[FrozenStep],
    new_val: LinearTerm,
) -> LinearTerm {
    let Some((first, rest)) = steps.split_first() else {
        return new_val;
    };
    match first {
        FrozenStep::Field(sid, fidx, fty) => {
            let sdef = &program.structs[*sid];
            let sub_old = translate_field_term(solver, cur_term.clone(), *sid, *fidx, fty);
            let updated_field =
                functional_update_frozen(program, solver, sub_old, fty, rest, new_val);
            let mut fields = Vec::with_capacity(sdef.fields.len());
            for (idx, field_param) in sdef.fields.iter().enumerate() {
                if idx == *fidx {
                    fields.push(updated_field.clone());
                } else {
                    fields.push(translate_field_term(
                        solver,
                        cur_term.clone(),
                        *sid,
                        idx,
                        &field_param.ty,
                    ));
                }
            }
            let cid = solver.intern_term(AtomTerm::StructCtor(*sid, fields));
            solver.register_sort(cid, cur_ty.deref_type());
            solver.instantiate_all();
            LinearTerm::var(cid)
        }
        FrozenStep::Index(idx_term, ety) => {
            let sub_old = translate_index_term(solver, cur_term.clone(), idx_term.clone(), ety);
            let updated_elem =
                functional_update_frozen(program, solver, sub_old, ety, rest, new_val);
            let uid = solver.intern_term(AtomTerm::Update {
                base: cur_term,
                index: idx_term.clone(),
                value: updated_elem,
            });
            solver.register_sort(uid, cur_ty.deref_type());
            solver.instantiate_all();
            LinearTerm::var(uid)
        }
    }
}

fn max_param_index(expr: &Expr) -> usize {
    match expr {
        Expr::Boolean(_)
        | Expr::Integer(_, _)
        | Expr::String(_)
        | Expr::EmptyMap(_)
        | Expr::TasksEmpty(_, _)
        | Expr::Count(_)
        | Expr::Var(VarRef::Local(_), _)
        | Expr::Var(VarRef::Field(_), _) => 0,
        Expr::Var(VarRef::Parameter(idx), _) | Expr::Old(idx, _) => *idx + 1,
        Expr::Borrow(_, place, _) => place
            .steps
            .iter()
            .filter_map(|s| match s {
                PlaceStep::Index(e, _) => Some(max_param_index(e)),
                PlaceStep::Field(_, _, _) => None,
            })
            .max()
            .unwrap_or(0),
        Expr::Move(inner, _)
        | Expr::Field(inner, _, _, _)
        | Expr::Len(inner)
        | Expr::Clone(inner, _)
        | Expr::Trim(inner)
        | Expr::Negate(inner, _)
        | Expr::Not(inner) => max_param_index(inner),
        Expr::Index(l, r, _)
        | Expr::Arithmetic(_, l, r, _)
        | Expr::Compare(_, l, r)
        | Expr::And(l, r)
        | Expr::Or(l, r) => max_param_index(l).max(max_param_index(r)),
        Expr::Struct(_, items, _)
        | Expr::Variant(_, _, items, _)
        | Expr::Vector(items, _)
        | Expr::Call(_, items, _) => items.iter().map(max_param_index).max().unwrap_or(0),
    }
}

fn solver_for_control_body(program: &Program, body: &ControlBody) -> (Solver, Vec<Vec<usize>>) {
    let mut history_names = Vec::new();
    let mut site_atoms = Vec::new();
    for site in &body.sites {
        let mut indices = Vec::new();
        for alt in &site.alternatives {
            indices.push(history_names.len());
            history_names.push((site.name.clone(), alt.clone()));
        }
        site_atoms.push(indices);
    }
    let mut solver = Solver::new(history_names);
    register_program_structs(program, &mut solver);
    (solver, site_atoms)
}

fn check_boundary(
    program: &Program,
    boundary: &BoundaryDef,
    boundary_may_fault: &[bool],
    certificates: &mut Proofs,
    warnings: &mut Vec<crate::surface::Warning>,
) -> Result<bool, Error> {
    // 1. Check `B₁` (`boundary.body`) with `permits_faults = true` and `retains` checked ([F6]).
    let (solver1, site_atoms1) = solver_for_control_body(program, &boundary.body);
    let var_count1 = boundary.body.vars.len();
    let constants1 = find_constant_locals(program, &boundary.body, boundary.parameters.len());
    let mut checker1 = BodyChecker {
        program,
        owner_name: boundary.name.clone(),
        allowed_uses: boundary.uses.clone(),
        contract: Vec::new(),
        param_types: boundary.parameters.iter().map(|p| p.ty.clone()).collect(),
        body: &boundary.body,
        boundary_may_fault,
        solver: solver1,
        site_atoms: site_atoms1,
        defined: vec![bdd::FALSE; var_count1],
        moved: vec![bdd::FALSE; var_count1],
        versions: vec![Vec::new(); var_count1],
        entry_parameters: Vec::new(),
        constants: constants1,
        captured: BTreeMap::new(),
        local_borrows: BTreeMap::new(),
        var_loan_roots: vec![Vec::new(); var_count1],
        stmt_r: BTreeMap::new(),
        stmt_visible: BTreeMap::new(),
        boundary_fallthrough_live: BTreeMap::new(),
        loop_entry_avail: BTreeMap::new(),
        active_scopes: vec![0],
        permits_faults: true,
        in_contingency: false,
        retained_vars: boundary.retains.clone(),
        boundary_can_fault: false,
        certificates,
        warnings,
        at_line: 1,
        trouble: None,
    };
    for param_idx in 0..boundary.parameters.len() {
        let tid = checker1.alloc_var_term(param_idx);
        checker1.defined[param_idx] = bdd::TRUE;
        checker1.versions[param_idx] = vec![(bdd::TRUE, tid)];
        checker1.entry_parameters.push(LinearTerm::var(tid));
    }
    let mut loop_leaves1 = BTreeMap::new();
    let result = checker1
        .check_body(0, bdd::TRUE, false, &mut loop_leaves1)
        .and_then(|()| checker1.check_loans());
    checker1.settle(result)?;
    let solver1 = checker1.solver;
    certificates.close_body(solver1);

    // 2. Check `B₂` (`boundary.contingency`) with `retains` + `message` bound ([F6]).
    let cont_param_count = boundary.retains.len() + 1;
    let (solver2, site_atoms2) = solver_for_control_body(program, &boundary.contingency);
    let var_count2 = boundary.contingency.vars.len();
    let constants2 = find_constant_locals(program, &boundary.contingency, cont_param_count);
    let mut checker2 = BodyChecker {
        program,
        owner_name: format!("{} contingency", boundary.name),
        allowed_uses: boundary.uses.clone(),
        contract: Vec::new(),
        param_types: boundary
            .retains
            .iter()
            .map(|&r| boundary.parameters[r].ty.clone())
            .chain(std::iter::once(Type::String))
            .collect(),
        body: &boundary.contingency,
        boundary_may_fault,
        solver: solver2,
        site_atoms: site_atoms2,
        defined: vec![bdd::FALSE; var_count2],
        moved: vec![bdd::FALSE; var_count2],
        versions: vec![Vec::new(); var_count2],
        entry_parameters: Vec::new(),
        constants: constants2,
        captured: BTreeMap::new(),
        local_borrows: BTreeMap::new(),
        var_loan_roots: vec![Vec::new(); var_count2],
        stmt_r: BTreeMap::new(),
        stmt_visible: BTreeMap::new(),
        boundary_fallthrough_live: BTreeMap::new(),
        loop_entry_avail: BTreeMap::new(),
        active_scopes: vec![0],
        permits_faults: true,
        in_contingency: true,
        retained_vars: Vec::new(),
        boundary_can_fault: false,
        certificates,
        warnings,
        at_line: 1,
        trouble: None,
    };
    for param_idx in 0..cont_param_count.min(var_count2) {
        let tid = checker2.alloc_var_term(param_idx);
        checker2.defined[param_idx] = bdd::TRUE;
        checker2.versions[param_idx] = vec![(bdd::TRUE, tid)];
        checker2.entry_parameters.push(LinearTerm::var(tid));
    }
    let mut loop_leaves2 = BTreeMap::new();
    let result = checker2
        .check_body(0, bdd::TRUE, false, &mut loop_leaves2)
        .and_then(|()| checker2.check_loans());
    checker2.settle(result)?;
    let can_fault = checker2.boundary_can_fault;
    let solver2 = checker2.solver;
    certificates.close_body(solver2);
    Ok(can_fault)
}

fn check_control(
    program: &Program,
    control: &Control,
    boundary_may_fault: &[bool],
    certificates: &mut Proofs,
    warnings: &mut Vec<crate::surface::Warning>,
) -> Result<(), Error> {
    let body = control.body.as_ref().expect("a defined control");
    let (solver, site_atoms) = solver_for_control_body(program, body);
    let var_count = body.vars.len();
    let constants = find_constant_locals(program, body, control.parameters.len());

    let mut checker = BodyChecker {
        program,
        owner_name: control.name.clone(),
        allowed_uses: control.uses.clone(),
        contract: control.contract.clone(),
        param_types: control.parameters.iter().map(|p| p.ty.clone()).collect(),
        body,
        boundary_may_fault,
        solver,
        site_atoms,
        defined: vec![bdd::FALSE; var_count],
        moved: vec![bdd::FALSE; var_count],
        versions: vec![Vec::new(); var_count],
        entry_parameters: Vec::new(),
        constants,
        captured: BTreeMap::new(),
        local_borrows: BTreeMap::new(),
        var_loan_roots: vec![Vec::new(); var_count],
        stmt_r: BTreeMap::new(),
        stmt_visible: BTreeMap::new(),
        boundary_fallthrough_live: BTreeMap::new(),
        loop_entry_avail: BTreeMap::new(),
        active_scopes: vec![0],
        permits_faults: control.faults,
        in_contingency: false,
        retained_vars: Vec::new(),
        boundary_can_fault: false,
        certificates,
        warnings,
        at_line: 1,
        trouble: None,
    };

    for param_idx in 0..control.parameters.len() {
        let tid = checker.alloc_var_term(param_idx);
        checker.defined[param_idx] = bdd::TRUE;
        checker.versions[param_idx] = vec![(bdd::TRUE, tid)];
        checker.entry_parameters.push(LinearTerm::var(tid));
    }

    if let Some(pre) = &control.precondition {
        let (env, _) = checker.current_env();
        let pre_formula = translate_formula(program, &mut checker.solver, pre, &env);
        checker.solver.add_fact(bdd::TRUE, pre_formula);
    }

    let mut loop_leaves = BTreeMap::new();
    let result = checker
        .check_body(0, bdd::TRUE, false, &mut loop_leaves)
        .and_then(|()| checker.check_loans());
    checker.settle(result)?;
    let solver = checker.solver;
    certificates.close_body(solver);
    Ok(())
}

// ============================================================================
// Pass 2: Static ROBDD Loan Checking ([L1]-[L5], [L2a])
// ============================================================================

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum LoanRoot {
    Owned(VarId),
    Behind(VarId, Vec<(StructId, usize)>),
    ParamOrigin(usize),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum LoanStep {
    Field(StructId, usize),
    Elem,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct LoanPlace {
    root: LoanRoot,
    steps: Vec<LoanStep>,
}

impl LoanPlace {
    fn overlaps(&self, other: &LoanPlace) -> bool {
        self.root == other.root && self.steps.iter().zip(&other.steps).all(|(a, b)| a == b)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Holder {
    Var(VarId),
    Temp(usize),
}

#[derive(Clone, Debug)]
struct Loan {
    place: LoanPlace,
    mode: BorrowMode,
    created_on: Formula,
    holders: Vec<(Holder, Formula)>,
}

type LeaveLoanRecord = (BodyId, usize, Formula, Vec<Vec<(usize, Formula)>>);

struct EvalCtx<'c> {
    r_i: Formula,
    after_live: &'c BTreeMap<VarId, Formula>,
    later_in_stmt: &'c BTreeSet<VarId>,
    in_loop: bool,
    visible: &'c [(String, TermId, bool)],
}

impl<'c> EvalCtx<'c> {
    fn with_later<'n>(&self, later: &'n BTreeSet<VarId>) -> EvalCtx<'n>
    where
        'c: 'n,
    {
        EvalCtx {
            r_i: self.r_i,
            after_live: self.after_live,
            later_in_stmt: later,
            in_loop: self.in_loop,
            visible: self.visible,
        }
    }
}

fn view_borrow_field_paths(
    program: &Program,
    ty: &Type,
) -> Vec<(Vec<(StructId, usize)>, BorrowMode)> {
    fn collect(
        program: &Program,
        ty: &Type,
        prefix: &mut Vec<(StructId, usize)>,
        out: &mut Vec<(Vec<(StructId, usize)>, BorrowMode)>,
    ) {
        match ty {
            Type::Ref(mode, _) => out.push((prefix.clone(), *mode)),
            Type::Struct(sid, _) if program.structs[*sid].is_view => {
                for (fidx, fdef) in program.structs[*sid].fields.iter().enumerate() {
                    prefix.push((*sid, fidx));
                    collect(program, &fdef.ty, prefix, out);
                    prefix.pop();
                }
            }
            _ => {}
        }
    }
    let mut prefix = Vec::new();
    let mut out = Vec::new();
    collect(program, ty, &mut prefix, &mut out);
    out
}

fn place_to_loan_place(program: &Program, body: &ControlBody, place: &Place) -> LoanPlace {
    let root_ty = &body.vars[place.root].ty;
    let convert_steps = |steps: &[PlaceStep]| -> Vec<LoanStep> {
        steps
            .iter()
            .map(|s| match s {
                PlaceStep::Field(sid, fidx, _) => LoanStep::Field(*sid, *fidx),
                PlaceStep::Index(_, _) => LoanStep::Elem,
            })
            .collect()
    };
    if matches!(root_ty, Type::Ref(_, _)) {
        return LoanPlace {
            root: LoanRoot::Behind(place.root, Vec::new()),
            steps: convert_steps(&place.steps),
        };
    }
    if program.is_view(root_ty) {
        let mut prefix = Vec::new();
        for (idx, step) in place.steps.iter().enumerate() {
            if let PlaceStep::Field(sid, fidx, fty) = step {
                prefix.push((*sid, *fidx));
                if matches!(fty, Type::Ref(_, _)) {
                    return LoanPlace {
                        root: LoanRoot::Behind(place.root, prefix),
                        steps: convert_steps(&place.steps[idx + 1..]),
                    };
                }
            } else {
                break;
            }
        }
    }
    LoanPlace {
        root: LoanRoot::Owned(place.root),
        steps: convert_steps(&place.steps),
    }
}

enum RawStep<'e> {
    Field(StructId, usize, Type),
    Index(&'e Expr),
}

struct DecomposedPlace<'e> {
    root: VarId,
    loan_place: LoanPlace,
    raw_field_steps: Vec<LoanStep>,
    view_prefix: Vec<(StructId, usize)>,
    index_exprs: Vec<&'e Expr>,
}

fn decompose_place_expr<'e>(
    program: &Program,
    body: &ControlBody,
    expr: &'e Expr,
) -> Option<DecomposedPlace<'e>> {
    let mut raw_rev: Vec<RawStep<'e>> = Vec::new();
    let mut cur = expr;
    let root = loop {
        match cur {
            Expr::Move(inner, _) => cur = inner,
            Expr::Field(base, sid, fidx, _) => {
                let decl_ty = program.structs[*sid].fields[*fidx].ty.clone();
                raw_rev.push(RawStep::Field(*sid, *fidx, decl_ty));
                cur = base;
            }
            Expr::Index(base, idx, _) => {
                raw_rev.push(RawStep::Index(idx));
                cur = base;
            }
            Expr::Var(VarRef::Local(id), _) => break *id,
            _ => return None,
        }
    };
    raw_rev.reverse();
    let index_exprs: Vec<&'e Expr> = raw_rev
        .iter()
        .filter_map(|s| match s {
            RawStep::Index(e) => Some(*e),
            RawStep::Field(_, _, _) => None,
        })
        .collect();
    let raw_field_steps: Vec<LoanStep> = raw_rev
        .iter()
        .map(|s| match s {
            RawStep::Field(sid, fidx, _) => LoanStep::Field(*sid, *fidx),
            RawStep::Index(_) => LoanStep::Elem,
        })
        .collect();
    let root_ty = &body.vars[root].ty;
    if matches!(root_ty, Type::Ref(_, _)) {
        return Some(DecomposedPlace {
            root,
            loan_place: LoanPlace {
                root: LoanRoot::Behind(root, Vec::new()),
                steps: raw_field_steps.clone(),
            },
            raw_field_steps,
            view_prefix: Vec::new(),
            index_exprs,
        });
    }
    let mut prefix = Vec::new();
    if program.is_view(root_ty) {
        for (idx, step) in raw_rev.iter().enumerate() {
            if let RawStep::Field(sid, fidx, decl_ty) = step {
                prefix.push((*sid, *fidx));
                if matches!(decl_ty, Type::Ref(_, _)) {
                    return Some(DecomposedPlace {
                        root,
                        loan_place: LoanPlace {
                            root: LoanRoot::Behind(root, prefix.clone()),
                            steps: raw_field_steps[idx + 1..].to_vec(),
                        },
                        raw_field_steps,
                        view_prefix: prefix,
                        index_exprs,
                    });
                }
            } else {
                break;
            }
        }
    }
    Some(DecomposedPlace {
        root,
        loan_place: LoanPlace {
            root: LoanRoot::Owned(root),
            steps: raw_field_steps.clone(),
        },
        raw_field_steps,
        view_prefix: prefix,
        index_exprs,
    })
}

fn collect_expr_mentions(expr: &Expr, out: &mut BTreeSet<VarId>) {
    match expr {
        Expr::Boolean(_)
        | Expr::Integer(_, _)
        | Expr::String(_)
        | Expr::Old(_, _)
        | Expr::EmptyMap(_)
        | Expr::TasksEmpty(_, _) => {}
        Expr::Count(id) => {
            out.insert(*id);
        }
        Expr::Var(VarRef::Local(id), _) => {
            out.insert(*id);
        }
        Expr::Var(_, _) => {}
        Expr::Borrow(_, place, _) => {
            out.insert(place.root);
            for step in &place.steps {
                if let PlaceStep::Index(idx, _) = step {
                    collect_expr_mentions(idx, out);
                }
            }
        }
        Expr::Move(inner, _)
        | Expr::Field(inner, _, _, _)
        | Expr::Len(inner)
        | Expr::Clone(inner, _)
        | Expr::Trim(inner)
        | Expr::Negate(inner, _)
        | Expr::Not(inner) => collect_expr_mentions(inner, out),
        Expr::Index(l, r, _)
        | Expr::Arithmetic(_, l, r, _)
        | Expr::Compare(_, l, r)
        | Expr::And(l, r)
        | Expr::Or(l, r) => {
            collect_expr_mentions(l, out);
            collect_expr_mentions(r, out);
        }
        Expr::Struct(_, items, _)
        | Expr::Variant(_, _, items, _)
        | Expr::Vector(items, _)
        | Expr::Call(_, items, _) => {
            for item in items {
                collect_expr_mentions(item, out);
            }
        }
    }
}

fn stmt_direct_mentions(
    program: &Program,
    body: &ControlBody,
    stmt: &crate::typed::Statement,
) -> BTreeSet<VarId> {
    let mut out = BTreeSet::new();
    match &stmt.command {
        Command::Bind { value, .. } | Command::Unpack { value, .. } => {
            collect_expr_mentions(value, &mut out);
        }
        Command::Assign { var, value } => {
            if matches!(body.vars[*var].ty, Type::Ref(_, _)) {
                out.insert(*var);
            }
            collect_expr_mentions(value, &mut out);
        }
        Command::AssignPlace { target, value } => {
            if program.contains_borrow_or_view(&body.vars[target.root].ty) {
                out.insert(target.root);
            }
            for step in &target.steps {
                if let PlaceStep::Index(idx, _) = step {
                    collect_expr_mentions(idx, &mut out);
                }
            }
            collect_expr_mentions(value, &mut out);
        }
        Command::Oblige(f) => collect_expr_mentions(f, &mut out),
        Command::Test { condition, .. } => collect_expr_mentions(condition, &mut out),
        Command::Capture { arguments, .. }
        | Command::Decide { arguments, .. }
        | Command::Supervise { arguments, .. }
        | Command::Again { arguments, .. } => {
            for a in arguments {
                collect_expr_mentions(a, &mut out);
            }
        }
        Command::Loop {
            body: loop_body,
            initial,
            ..
        } => {
            for a in initial {
                collect_expr_mentions(a, &mut out);
            }
            if let Some(head) = &body.bodies[*loop_body].head
                && let Some(inv) = &head.invariant
            {
                collect_expr_mentions(inv, &mut out);
            }
        }
        Command::Boundary { captures, .. } => {
            out.extend(captures.iter().copied());
        }
        Command::Leave { payload, .. } | Command::Exit { payload, .. } => {
            for p in payload {
                collect_expr_mentions(p, &mut out);
            }
        }
        Command::Fault { message, .. } => collect_expr_mentions(message, &mut out),
        Command::Spawn { arguments, set, .. } => {
            out.insert(*set);
            for a in arguments {
                collect_expr_mentions(a, &mut out);
            }
        }
        Command::Cancel { set } => {
            out.insert(*set);
        }
        Command::Terminate(_)
        | Command::Escalate
        | Command::Recover { .. }
        | Command::Impossible => {}
    }
    out
}

fn or_guard_map(map: &mut BTreeMap<VarId, Formula>, var: VarId, guard: Formula, bdd: &mut Bdd) {
    if guard == bdd::FALSE {
        return;
    }
    match map.get_mut(&var) {
        Some(existing) => *existing = bdd.or(*existing, guard),
        None => {
            map.insert(var, guard);
        }
    }
}

struct LoanChecker<'a, 'b> {
    bc: &'a mut BodyChecker<'b>,
    loans: Vec<Loan>,
    next_temp: usize,
    mentions_in_body: BTreeMap<BodyId, BTreeMap<VarId, Formula>>,
    feasible_mentions: BTreeMap<BodyId, BTreeSet<VarId>>,
    live_after_stmt: BTreeMap<(BodyId, usize), BTreeMap<VarId, Formula>>,
    boundary_after_live: BTreeMap<BodyId, BTreeMap<VarId, Formula>>,
}

impl<'a, 'b> LoanChecker<'a, 'b> {
    fn new(bc: &'a mut BodyChecker<'b>) -> Self {
        let mut loans = Vec::new();
        for (pidx, pty) in bc.param_types.iter().enumerate() {
            if bc.program.contains_borrow_or_view(pty) {
                let mode = if bc.program.has_exclusive_borrow(pty) {
                    BorrowMode::Exclusive
                } else {
                    BorrowMode::Shared
                };
                loans.push(Loan {
                    place: LoanPlace {
                        root: LoanRoot::ParamOrigin(pidx),
                        steps: Vec::new(),
                    },
                    mode,
                    created_on: bdd::TRUE,
                    holders: vec![(Holder::Var(pidx), bdd::TRUE)],
                });
            }
        }
        LoanChecker {
            bc,
            loans,
            next_temp: 0,
            mentions_in_body: BTreeMap::new(),
            feasible_mentions: BTreeMap::new(),
            live_after_stmt: BTreeMap::new(),
            boundary_after_live: BTreeMap::new(),
        }
    }

    fn fresh_temp(&mut self) -> Holder {
        let id = self.next_temp;
        self.next_temp += 1;
        Holder::Temp(id)
    }

    fn describe_place(&self, place: &LoanPlace) -> String {
        let mut s = match &place.root {
            LoanRoot::Owned(v) => self.bc.body.vars[*v].name.clone(),
            LoanRoot::Behind(v, prefix) => {
                let mut base = format!("*{}", self.bc.body.vars[*v].name);
                for &(sid, fidx) in prefix {
                    base.push('.');
                    base.push_str(&self.bc.program.structs[sid].fields[fidx].name);
                }
                base
            }
            LoanRoot::ParamOrigin(pidx) => {
                format!("origin({})", self.bc.body.vars[*pidx].name)
            }
        };
        for step in &place.steps {
            match step {
                LoanStep::Field(sid, fidx) => {
                    s.push('.');
                    s.push_str(&self.bc.program.structs[*sid].fields[*fidx].name);
                }
                LoanStep::Elem => s.push_str("[…]"),
            }
        }
        s
    }

    fn collect_body_mentions(
        &mut self,
        body_id: BodyId,
        in_loop: bool,
    ) -> BTreeMap<VarId, Formula> {
        let mut map = BTreeMap::new();
        let stmts = self.bc.body.bodies[body_id].statements.clone();
        for (stmt_idx, stmt) in stmts.iter().enumerate() {
            let r_i = self
                .bc
                .stmt_r
                .get(&(body_id, stmt_idx))
                .copied()
                .unwrap_or(bdd::FALSE);
            for v in stmt_direct_mentions(self.bc.program, self.bc.body, stmt) {
                or_guard_map(&mut map, v, r_i, &mut self.bc.solver.bdd);
            }
            match &stmt.command {
                Command::Loop { body: inner, .. } => {
                    let inner_m = self.collect_body_mentions(*inner, true);
                    for (v, g) in inner_m {
                        or_guard_map(&mut map, v, g, &mut self.bc.solver.bdd);
                    }
                }
                Command::Boundary {
                    body: b1,
                    contingency: b2,
                    ..
                } => {
                    let m1 = self.collect_body_mentions(*b1, in_loop);
                    for (v, g) in m1 {
                        or_guard_map(&mut map, v, g, &mut self.bc.solver.bdd);
                    }
                    let m2 = self.collect_body_mentions(*b2, in_loop);
                    for (v, g) in m2 {
                        or_guard_map(&mut map, v, g, &mut self.bc.solver.bdd);
                    }
                }
                _ => {}
            }
        }
        let mut feasible = BTreeSet::new();
        for (&v, &g) in &map {
            if self
                .bc
                .program
                .contains_borrow_or_view(&self.bc.body.vars[v].ty)
                && self.bc.is_feasible(g, &[], in_loop)
            {
                feasible.insert(v);
            }
        }
        self.mentions_in_body.insert(body_id, map.clone());
        self.feasible_mentions.insert(body_id, feasible);
        map
    }

    fn collect_repeat_and_leave_guards(
        &mut self,
        cur_body: BodyId,
        targets: &[BodyId],
        in_inner_loop: bool,
    ) -> (Formula, Formula) {
        let mut rep = bdd::FALSE;
        let mut lv = bdd::FALSE;
        let stmts = &self.bc.body.bodies[cur_body].statements;
        for (stmt_idx, stmt) in stmts.iter().enumerate() {
            let r_i = self
                .bc
                .stmt_r
                .get(&(cur_body, stmt_idx))
                .copied()
                .unwrap_or(bdd::FALSE);
            match &stmt.command {
                Command::Again { body: target, .. } | Command::Recover { body: target }
                    if targets.contains(target) =>
                {
                    rep = self.bc.solver.bdd.or(rep, r_i);
                }
                Command::Leave { .. } if !in_inner_loop => {
                    lv = self.bc.solver.bdd.or(lv, r_i);
                }
                Command::Loop { body: inner, .. } => {
                    let (ir, _) = self.collect_repeat_and_leave_guards(*inner, targets, true);
                    rep = self.bc.solver.bdd.or(rep, ir);
                }
                Command::Boundary {
                    body: b1,
                    contingency: b2,
                    ..
                } => {
                    let (r1, l1) =
                        self.collect_repeat_and_leave_guards(*b1, targets, in_inner_loop);
                    rep = self.bc.solver.bdd.or(rep, r1);
                    lv = self.bc.solver.bdd.or(lv, l1);
                    let (r2, _) = self.collect_repeat_and_leave_guards(*b2, targets, in_inner_loop);
                    rep = self.bc.solver.bdd.or(rep, r2);
                }
                _ => {}
            }
        }
        (rep, lv)
    }

    fn collect_recover_guard(&mut self, cur_body: BodyId) -> (Formula, BTreeSet<BodyId>) {
        let mut rec_g = bdd::FALSE;
        let mut targets = BTreeSet::new();
        for (stmt_idx, stmt) in self.bc.body.bodies[cur_body].statements.iter().enumerate() {
            let r_i = self
                .bc
                .stmt_r
                .get(&(cur_body, stmt_idx))
                .copied()
                .unwrap_or(bdd::FALSE);
            match &stmt.command {
                Command::Recover { body: target } => {
                    rec_g = self.bc.solver.bdd.or(rec_g, r_i);
                    targets.insert(*target);
                }
                Command::Loop { body: inner, .. } => {
                    let (ig, it) = self.collect_recover_guard(*inner);
                    rec_g = self.bc.solver.bdd.or(rec_g, ig);
                    targets.extend(it);
                }
                Command::Boundary {
                    body: b1,
                    contingency: b2,
                    ..
                } => {
                    let (g1, t1) = self.collect_recover_guard(*b1);
                    let (g2, t2) = self.collect_recover_guard(*b2);
                    rec_g = self.bc.solver.bdd.or(rec_g, g1);
                    rec_g = self.bc.solver.bdd.or(rec_g, g2);
                    targets.extend(t1);
                    targets.extend(t2);
                }
                _ => {}
            }
        }
        (rec_g, targets)
    }

    fn compute_body_liveness(
        &mut self,
        body_id: BodyId,
        after_body_live: &BTreeMap<VarId, Formula>,
        ancestors: &[BodyId],
        loop_ancestors: &[BodyId],
    ) {
        let mut running = if let Some(head) = &self.bc.body.bodies[body_id].head.clone() {
            let mut loop_targets = loop_ancestors.to_vec();
            loop_targets.push(body_id);
            let (repeat_g, leave_g) =
                self.collect_repeat_and_leave_guards(body_id, &loop_targets, false);
            let mut seeded = BTreeMap::new();
            for (&v, &g) in after_body_live {
                let mut inner_g = self.bc.solver.bdd.and(g, leave_g);
                if g != bdd::FALSE && self.bc.is_feasible(g, &[], true) {
                    inner_g = self.bc.solver.bdd.or(inner_g, repeat_g);
                }
                if inner_g != bdd::FALSE {
                    seeded.insert(v, inner_g);
                }
            }
            let feasible = self
                .feasible_mentions
                .get(&body_id)
                .cloned()
                .unwrap_or_default();
            for v in feasible {
                let var_body = self.bc.body.vars[v].body;
                if head.parameters.contains(&v) || ancestors.contains(&var_body) {
                    or_guard_map(&mut seeded, v, repeat_g, &mut self.bc.solver.bdd);
                }
            }
            seeded
        } else {
            after_body_live.clone()
        };

        let stmts = self.bc.body.bodies[body_id].statements.clone();
        for (stmt_idx, stmt) in stmts.iter().enumerate().rev() {
            self.live_after_stmt
                .insert((body_id, stmt_idx), running.clone());
            let r_i = self
                .bc
                .stmt_r
                .get(&(body_id, stmt_idx))
                .copied()
                .unwrap_or(bdd::FALSE);
            match &stmt.command {
                Command::Loop {
                    body: inner,
                    initial,
                    ..
                } => {
                    let mut next_anc = ancestors.to_vec();
                    next_anc.push(body_id);
                    let mut next_loop_anc = loop_ancestors.to_vec();
                    if self.bc.body.bodies[body_id].head.is_some() {
                        next_loop_anc.push(body_id);
                    }
                    self.compute_body_liveness(*inner, &running, &next_anc, &next_loop_anc);
                    let inner_m = self
                        .mentions_in_body
                        .get(inner)
                        .cloned()
                        .unwrap_or_default();
                    for (v, g) in inner_m {
                        if self.bc.body.vars[v].body != *inner {
                            or_guard_map(&mut running, v, g, &mut self.bc.solver.bdd);
                        }
                    }
                    let mut head_vars = BTreeSet::new();
                    for a in initial {
                        collect_expr_mentions(a, &mut head_vars);
                    }
                    if let Some(head) = &self.bc.body.bodies[*inner].head
                        && let Some(inv) = &head.invariant
                    {
                        collect_expr_mentions(inv, &mut head_vars);
                    }
                    for v in head_vars {
                        or_guard_map(&mut running, v, r_i, &mut self.bc.solver.bdd);
                    }
                }
                Command::Boundary {
                    body: b1,
                    captures,
                    contingency: b2,
                    ..
                } => {
                    let b1_exit = self
                        .bc
                        .boundary_fallthrough_live
                        .get(b1)
                        .copied()
                        .unwrap_or(bdd::FALSE);
                    let (b1_rep, b1_lv) =
                        self.collect_repeat_and_leave_guards(*b1, loop_ancestors, false);
                    let b1_rl = self.bc.solver.bdd.or(b1_rep, b1_lv);
                    let b1_cont = self.bc.solver.bdd.or(b1_exit, b1_rl);
                    let mut b1_after = BTreeMap::new();
                    for (&v, &g) in &running {
                        let fg = self.bc.solver.bdd.and(g, b1_cont);
                        or_guard_map(&mut b1_after, v, fg, &mut self.bc.solver.bdd);
                    }
                    let b2_feasible = self.feasible_mentions.get(b2).cloned().unwrap_or_default();
                    for v in b2_feasible {
                        if !self.bc.var_in_body_tree(v, *b2) {
                            or_guard_map(&mut b1_after, v, r_i, &mut self.bc.solver.bdd);
                        }
                    }
                    self.boundary_after_live.insert(*b1, b1_after.clone());

                    let mut next_anc = ancestors.to_vec();
                    next_anc.push(body_id);
                    let mut next_loop_anc = loop_ancestors.to_vec();
                    if self.bc.body.bodies[body_id].head.is_some() {
                        next_loop_anc.push(body_id);
                    }
                    self.compute_body_liveness(*b1, &b1_after, &next_anc, &next_loop_anc);

                    let mut b2_after = BTreeMap::new();
                    let (rec_g, rec_targets) = self.collect_recover_guard(*b2);
                    if rec_g != bdd::FALSE {
                        for &target in &rec_targets {
                            let feas = self
                                .feasible_mentions
                                .get(&target)
                                .cloned()
                                .unwrap_or_default();
                            for v in feas {
                                if self.bc.body.vars[v].body != target
                                    && !self.bc.var_in_body_tree(v, *b2)
                                {
                                    or_guard_map(&mut b2_after, v, rec_g, &mut self.bc.solver.bdd);
                                }
                            }
                            for (&v, &g) in &running {
                                let fg = self.bc.solver.bdd.and(g, rec_g);
                                or_guard_map(&mut b2_after, v, fg, &mut self.bc.solver.bdd);
                            }
                        }
                    }
                    self.compute_body_liveness(*b2, &b2_after, &next_anc, &next_loop_anc);

                    for sub in [*b1, *b2] {
                        let subm = self.mentions_in_body.get(&sub).cloned().unwrap_or_default();
                        for (v, g) in subm {
                            if self.bc.body.vars[v].body != sub {
                                or_guard_map(&mut running, v, g, &mut self.bc.solver.bdd);
                            }
                        }
                    }
                    for &c in captures {
                        or_guard_map(&mut running, c, r_i, &mut self.bc.solver.bdd);
                    }
                }
                _ => {
                    for v in stmt_direct_mentions(self.bc.program, self.bc.body, stmt) {
                        or_guard_map(&mut running, v, r_i, &mut self.bc.solver.bdd);
                    }
                }
            }
        }
    }

    fn loans_for_holder(&mut self, holder: Holder, r_i: Formula) -> Vec<(usize, Formula)> {
        let mut out = Vec::new();
        for lid in 0..self.loans.len() {
            let holders = self.loans[lid].holders.clone();
            for (h, hg) in holders {
                if h == holder {
                    let g = self.bc.solver.bdd.and(r_i, hg);
                    if g != bdd::FALSE {
                        out.push((lid, g));
                    }
                }
            }
        }
        out
    }

    fn attach_holder_loans(&mut self, holder: Holder, src: &[(usize, Formula)], guard: Formula) {
        if guard == bdd::FALSE {
            return;
        }
        for &(lid, shg) in src {
            let g = self.bc.solver.bdd.and(guard, shg);
            if g == bdd::FALSE {
                continue;
            }
            let holders = &mut self.loans[lid].holders;
            if let Some((_, existing)) = holders.iter_mut().find(|(h, _)| *h == holder) {
                *existing = self.bc.solver.bdd.or(*existing, g);
            } else {
                holders.push((holder, g));
            }
        }
    }

    fn check_access(
        &mut self,
        access_place: &LoanPlace,
        is_write: bool,
        through: Option<Holder>,
        ctx: &EvalCtx<'_>,
        active_temps: &[Holder],
        line: u32,
    ) -> Result<(), Error> {
        let loan_count = self.loans.len();
        for lid in 0..loan_count {
            let (l_place, l_mode, l_created, l_holders) = {
                let l = &self.loans[lid];
                (l.place.clone(), l.mode, l.created_on, l.holders.clone())
            };
            if !l_place.overlaps(access_place) {
                continue;
            }
            if !is_write && l_mode == BorrowMode::Shared {
                continue;
            }
            let mut through_guard = bdd::FALSE;
            let mut holder_live = bdd::FALSE;
            for (h, hg) in &l_holders {
                if Some(*h) == through {
                    through_guard = self.bc.solver.bdd.or(through_guard, *hg);
                }
                let used = match h {
                    Holder::Temp(_) => {
                        if active_temps.contains(h) {
                            ctx.r_i
                        } else {
                            bdd::FALSE
                        }
                    }
                    Holder::Var(vid) => {
                        let after = ctx.after_live.get(vid).copied().unwrap_or(bdd::FALSE);
                        if ctx.later_in_stmt.contains(vid) {
                            self.bc.solver.bdd.or(after, ctx.r_i)
                        } else {
                            after
                        }
                    }
                };
                let h_live = self.bc.solver.bdd.and(*hg, used);
                holder_live = self.bc.solver.bdd.or(holder_live, h_live);
            }
            let not_through = self.bc.solver.bdd.not(through_guard);
            let r_not_through = self.bc.solver.bdd.and(ctx.r_i, not_through);
            let created_and_live = self.bc.solver.bdd.and(l_created, holder_live);
            let conflict = self.bc.solver.bdd.and(r_not_through, created_and_live);
            if conflict != bdd::FALSE {
                let desc = self.describe_place(&l_place);
                let action = if is_write { "write" } else { "read" };
                let access_desc = self.describe_place(access_place);
                let msg = format!(
                    "cannot {action} `{access_desc}` while `{desc}` is lent and its borrow is still used"
                );
                require_entailment(
                    &mut self.bc.solver,
                    conflict,
                    &self.bc.owner_name,
                    line,
                    "L3",
                    msg,
                    ctx.visible,
                    ctx.in_loop,
                    self.bc.certificates,
                )?;
            }
        }
        Ok(())
    }

    fn eval_loan_expr(
        &mut self,
        expr: &Expr,
        consumed: bool,
        ctx: &EvalCtx<'_>,
        active_temps: &mut Vec<Holder>,
        line: u32,
    ) -> Result<Vec<(usize, Formula)>, Error> {
        match expr {
            Expr::Boolean(_)
            | Expr::Integer(_, _)
            | Expr::String(_)
            | Expr::Old(_, _)
            | Expr::EmptyMap(_)
            | Expr::TasksEmpty(_, _)
            | Expr::Count(_) => Ok(Vec::new()),
            Expr::Var(VarRef::Local(id), expr_ty) => {
                let var_ty = self.bc.body.vars[*id].ty.clone();
                if matches!(var_ty, Type::Ref(_, _)) {
                    let is_ref_val = matches!(expr_ty, Type::Ref(_, _));
                    let is_write =
                        is_ref_val && matches!(var_ty, Type::Ref(BorrowMode::Exclusive, _));
                    let lp = LoanPlace {
                        root: LoanRoot::Behind(*id, Vec::new()),
                        steps: Vec::new(),
                    };
                    self.check_access(
                        &lp,
                        is_write,
                        Some(Holder::Var(*id)),
                        ctx,
                        active_temps,
                        line,
                    )?;
                    Ok(if is_ref_val {
                        self.loans_for_holder(Holder::Var(*id), ctx.r_i)
                    } else {
                        Vec::new()
                    })
                } else if self.bc.program.is_view(&var_ty) {
                    let is_write = consumed && self.bc.program.kind(&var_ty) != Kind::Copy;
                    self.check_access(
                        &LoanPlace {
                            root: LoanRoot::Owned(*id),
                            steps: Vec::new(),
                        },
                        is_write,
                        None,
                        ctx,
                        active_temps,
                        line,
                    )?;
                    for (prefix, mode) in view_borrow_field_paths(self.bc.program, &var_ty) {
                        self.check_access(
                            &LoanPlace {
                                root: LoanRoot::Behind(*id, prefix),
                                steps: Vec::new(),
                            },
                            mode == BorrowMode::Exclusive,
                            Some(Holder::Var(*id)),
                            ctx,
                            active_temps,
                            line,
                        )?;
                    }
                    Ok(self.loans_for_holder(Holder::Var(*id), ctx.r_i))
                } else {
                    let is_write = consumed && self.bc.program.kind(&var_ty) != Kind::Copy;
                    self.check_access(
                        &LoanPlace {
                            root: LoanRoot::Owned(*id),
                            steps: Vec::new(),
                        },
                        is_write,
                        None,
                        ctx,
                        active_temps,
                        line,
                    )?;
                    Ok(Vec::new())
                }
            }
            Expr::Var(_, _) => Ok(Vec::new()),
            Expr::Move(inner, _) => self.eval_loan_expr(inner, true, ctx, active_temps, line),
            Expr::Borrow(mode, place, _) => {
                let idx_exprs: Vec<&Expr> = place
                    .steps
                    .iter()
                    .filter_map(|s| match s {
                        PlaceStep::Index(e, _) => Some(e),
                        PlaceStep::Field(_, _, _) => None,
                    })
                    .collect();
                let root_borrow_or_view = self
                    .bc
                    .program
                    .contains_borrow_or_view(&self.bc.body.vars[place.root].ty);
                for (k, ie) in idx_exprs.iter().enumerate() {
                    let mut ilater = ctx.later_in_stmt.clone();
                    if root_borrow_or_view {
                        ilater.insert(place.root);
                    }
                    for rem in &idx_exprs[k + 1..] {
                        collect_expr_mentions(rem, &mut ilater);
                    }
                    let ictx = ctx.with_later(&ilater);
                    self.eval_loan_expr(ie, false, &ictx, active_temps, line)?;
                }
                let lp = place_to_loan_place(self.bc.program, self.bc.body, place);
                let through = match &lp.root {
                    LoanRoot::Behind(v, _) => Some(Holder::Var(*v)),
                    _ => None,
                };
                self.check_access(
                    &lp,
                    *mode == BorrowMode::Exclusive,
                    through,
                    ctx,
                    active_temps,
                    line,
                )?;
                let temp = self.fresh_temp();
                active_temps.push(temp);
                let lid = self.loans.len();
                self.loans.push(Loan {
                    place: lp.clone(),
                    mode: *mode,
                    created_on: ctx.r_i,
                    holders: vec![(temp, ctx.r_i)],
                });
                let mut ret = vec![(lid, ctx.r_i)];
                if matches!(lp.root, LoanRoot::Behind(_, _)) {
                    let inherited = self.loans_for_holder(Holder::Var(place.root), ctx.r_i);
                    self.attach_holder_loans(temp, &inherited, ctx.r_i);
                    ret.extend(inherited);
                }
                Ok(ret)
            }
            Expr::Field(base, _, _, expr_ty) | Expr::Index(base, _, expr_ty) => {
                if let Some(decomp) = decompose_place_expr(self.bc.program, self.bc.body, expr) {
                    let root_borrow_or_view = self
                        .bc
                        .program
                        .contains_borrow_or_view(&self.bc.body.vars[decomp.root].ty);
                    for (k, ie) in decomp.index_exprs.iter().enumerate() {
                        let mut ilater = ctx.later_in_stmt.clone();
                        if root_borrow_or_view {
                            ilater.insert(decomp.root);
                        }
                        for rem in &decomp.index_exprs[k + 1..] {
                            collect_expr_mentions(rem, &mut ilater);
                        }
                        let ictx = ctx.with_later(&ilater);
                        self.eval_loan_expr(ie, false, &ictx, active_temps, line)?;
                    }
                    if let Type::Ref(fmode, _) = expr_ty {
                        self.check_access(
                            &LoanPlace {
                                root: LoanRoot::Owned(decomp.root),
                                steps: decomp.raw_field_steps.clone(),
                            },
                            false,
                            None,
                            ctx,
                            active_temps,
                            line,
                        )?;
                        self.check_access(
                            &LoanPlace {
                                root: LoanRoot::Behind(decomp.root, decomp.view_prefix),
                                steps: Vec::new(),
                            },
                            *fmode == BorrowMode::Exclusive,
                            Some(Holder::Var(decomp.root)),
                            ctx,
                            active_temps,
                            line,
                        )?;
                        return Ok(self.loans_for_holder(Holder::Var(decomp.root), ctx.r_i));
                    } else if self.bc.program.is_view(expr_ty) {
                        let is_write = consumed && self.bc.program.kind(expr_ty) != Kind::Copy;
                        self.check_access(
                            &LoanPlace {
                                root: LoanRoot::Owned(decomp.root),
                                steps: decomp.raw_field_steps,
                            },
                            is_write,
                            None,
                            ctx,
                            active_temps,
                            line,
                        )?;
                        for (sub_prefix, sub_mode) in
                            view_borrow_field_paths(self.bc.program, expr_ty)
                        {
                            let mut full = decomp.view_prefix.clone();
                            full.extend(sub_prefix);
                            self.check_access(
                                &LoanPlace {
                                    root: LoanRoot::Behind(decomp.root, full),
                                    steps: Vec::new(),
                                },
                                sub_mode == BorrowMode::Exclusive,
                                Some(Holder::Var(decomp.root)),
                                ctx,
                                active_temps,
                                line,
                            )?;
                        }
                        return Ok(self.loans_for_holder(Holder::Var(decomp.root), ctx.r_i));
                    }
                    let through = match &decomp.loan_place.root {
                        LoanRoot::Behind(v, _) => Some(Holder::Var(*v)),
                        _ => None,
                    };
                    self.check_access(&decomp.loan_place, false, through, ctx, active_temps, line)?;
                    return Ok(Vec::new());
                }
                if let Expr::Index(b, idx, _) = expr {
                    let mut blater = ctx.later_in_stmt.clone();
                    collect_expr_mentions(idx, &mut blater);
                    let bctx = ctx.with_later(&blater);
                    let ret = self.eval_loan_expr(b, false, &bctx, active_temps, line)?;
                    self.eval_loan_expr(idx, false, ctx, active_temps, line)?;
                    return Ok(if self.bc.program.contains_borrow_or_view(expr_ty) {
                        ret
                    } else {
                        Vec::new()
                    });
                }
                let ret = self.eval_loan_expr(base, false, ctx, active_temps, line)?;
                Ok(if self.bc.program.contains_borrow_or_view(expr_ty) {
                    ret
                } else {
                    Vec::new()
                })
            }
            Expr::Struct(sid, items, _) => {
                if self.bc.program.structs[*sid].is_view {
                    let per_arg = self.eval_loan_operands(items, ctx, active_temps, line)?;
                    let mut out = Vec::new();
                    for item in per_arg {
                        out.extend(item);
                    }
                    Ok(out)
                } else {
                    for (k, item) in items.iter().enumerate() {
                        let mut ilater = ctx.later_in_stmt.clone();
                        for rem in &items[k + 1..] {
                            collect_expr_mentions(rem, &mut ilater);
                        }
                        let ictx = ctx.with_later(&ilater);
                        self.eval_loan_expr(item, true, &ictx, active_temps, line)?;
                    }
                    Ok(Vec::new())
                }
            }
            Expr::Variant(_, _, items, _) | Expr::Vector(items, _) => {
                for (k, item) in items.iter().enumerate() {
                    let mut ilater = ctx.later_in_stmt.clone();
                    for rem in &items[k + 1..] {
                        collect_expr_mentions(rem, &mut ilater);
                    }
                    let ictx = ctx.with_later(&ilater);
                    self.eval_loan_expr(item, true, &ictx, active_temps, line)?;
                }
                Ok(Vec::new())
            }
            Expr::Len(inner)
            | Expr::Clone(inner, _)
            | Expr::Trim(inner)
            | Expr::Negate(inner, _)
            | Expr::Not(inner) => {
                self.eval_loan_expr(inner, false, ctx, active_temps, line)?;
                Ok(Vec::new())
            }
            Expr::Arithmetic(_, l, r, _)
            | Expr::Compare(_, l, r)
            | Expr::And(l, r)
            | Expr::Or(l, r) => {
                let mut llater = ctx.later_in_stmt.clone();
                collect_expr_mentions(r, &mut llater);
                let lctx = ctx.with_later(&llater);
                self.eval_loan_expr(l, false, &lctx, active_temps, line)?;
                self.eval_loan_expr(r, false, ctx, active_temps, line)?;
                Ok(Vec::new())
            }
            Expr::Call(_, args, _) => {
                let mut call_temps = Vec::new();
                let _ = self.eval_loan_operands(args, ctx, &mut call_temps, line)?;
                Ok(Vec::new())
            }
        }
    }

    fn eval_loan_operands(
        &mut self,
        exprs: &[Expr],
        ctx: &EvalCtx<'_>,
        active_temps: &mut Vec<Holder>,
        line: u32,
    ) -> Result<Vec<Vec<(usize, Formula)>>, Error> {
        let mut results: Vec<Option<Vec<(usize, Formula)>>> = vec![None; exprs.len()];
        let pass1: Vec<usize> = (0..exprs.len()).filter(|&i| !exprs[i].lends()).collect();
        let pass2: Vec<usize> = (0..exprs.len()).filter(|&i| exprs[i].lends()).collect();

        for (pos, &i) in pass1.iter().enumerate() {
            let mut later = ctx.later_in_stmt.clone();
            for &j in &pass1[pos + 1..] {
                collect_expr_mentions(&exprs[j], &mut later);
            }
            for &j in &pass2 {
                collect_expr_mentions(&exprs[j], &mut later);
            }
            let ictx = ctx.with_later(&later);
            let loans = self.eval_loan_expr(&exprs[i], true, &ictx, active_temps, line)?;
            if !loans.is_empty() {
                let temp = self.fresh_temp();
                active_temps.push(temp);
                self.attach_holder_loans(temp, &loans, ctx.r_i);
            }
            results[i] = Some(loans);
        }
        for (pos, &i) in pass2.iter().enumerate() {
            let mut later = ctx.later_in_stmt.clone();
            for &j in &pass2[pos + 1..] {
                collect_expr_mentions(&exprs[j], &mut later);
            }
            let ictx = ctx.with_later(&later);
            let loans = self.eval_loan_expr(&exprs[i], true, &ictx, active_temps, line)?;
            if !loans.is_empty() {
                let temp = self.fresh_temp();
                active_temps.push(temp);
                self.attach_holder_loans(temp, &loans, ctx.r_i);
            }
            results[i] = Some(loans);
        }
        Ok(results
            .into_iter()
            .map(|r| r.expect("operand evaluated"))
            .collect())
    }

    fn seed_loop_again_loans(&mut self, loop_body: BodyId, r_loop: Formula) {
        let Some(head) = self.bc.body.bodies[loop_body].head.clone() else {
            return;
        };
        let mut ancestors = BTreeSet::new();
        let mut cur = self.bc.body.bodies[loop_body].parent;
        while let Some(p) = cur {
            ancestors.insert(p);
            cur = self.bc.body.bodies[p].parent;
        }
        let is_outside = |root: &LoanRoot| -> bool {
            match root {
                LoanRoot::ParamOrigin(_) => true,
                LoanRoot::Owned(v) | LoanRoot::Behind(v, _) => {
                    ancestors.contains(&self.bc.body.vars[*v].body)
                }
            }
        };

        let mut env_map: BTreeMap<VarId, Vec<(LoanPlace, BorrowMode)>> = BTreeMap::new();
        for loan in &self.loans {
            for &(holder, hg) in &loan.holders {
                if let Holder::Var(v) = holder
                    && (ancestors.contains(&self.bc.body.vars[v].body)
                        || head.parameters.contains(&v))
                    && self.bc.solver.bdd.and(r_loop, hg) != bdd::FALSE
                {
                    env_map
                        .entry(v)
                        .or_default()
                        .push((loan.place.clone(), loan.mode));
                }
            }
        }
        for list in env_map.values_mut() {
            dedup_loan_pairs(list);
        }

        let program = self.bc.program;
        let body = self.bc.body;
        let mut eval_struct_loans =
            |expr: &Expr, env: &BTreeMap<VarId, Vec<(LoanPlace, BorrowMode)>>| {
                expr_structural_external_loans(program, body, expr, env, &is_outside)
            };

        let mut changed = true;
        while changed {
            changed = false;
            changed |= self.propagate_loop_body_loans(
                loop_body,
                loop_body,
                &head.parameters,
                &mut env_map,
                &mut eval_struct_loans,
            );
        }

        for &lp_var in &head.parameters {
            if !self
                .bc
                .program
                .contains_borrow_or_view(&self.bc.body.vars[lp_var].ty)
            {
                continue;
            }
            let Some(pairs) = env_map.get(&lp_var) else {
                continue;
            };
            for (place, mode) in pairs {
                let already_covered = self.loans.iter().any(|l| {
                    l.place == *place
                        && l.mode == *mode
                        && self.bc.solver.bdd.implies(r_loop, l.created_on) == bdd::TRUE
                        && l.holders.iter().any(|&(h, hg)| {
                            h == Holder::Var(lp_var)
                                && self.bc.solver.bdd.implies(r_loop, hg) == bdd::TRUE
                        })
                });
                if !already_covered {
                    self.loans.push(Loan {
                        place: place.clone(),
                        mode: *mode,
                        created_on: r_loop,
                        holders: vec![(Holder::Var(lp_var), r_loop)],
                    });
                }
            }
        }
    }

    fn propagate_loop_body_loans<F>(
        &self,
        cur_body: BodyId,
        target_loop: BodyId,
        target_params: &[VarId],
        env_map: &mut BTreeMap<VarId, Vec<(LoanPlace, BorrowMode)>>,
        eval_struct: &mut F,
    ) -> bool
    where
        F: FnMut(
            &Expr,
            &BTreeMap<VarId, Vec<(LoanPlace, BorrowMode)>>,
        ) -> Vec<(LoanPlace, BorrowMode)>,
    {
        let mut changed = false;
        for stmt in &self.bc.body.bodies[cur_body].statements {
            match &stmt.command {
                Command::Spawn { .. } | Command::Cancel { .. } => {}
                Command::Bind { var, value } => {
                    if self
                        .bc
                        .program
                        .contains_borrow_or_view(&self.bc.body.vars[*var].ty)
                    {
                        let items = eval_struct(value, env_map);
                        changed |= extend_loan_pairs(env_map.entry(*var).or_default(), items);
                    }
                }
                Command::Unpack { vars, value, .. } => {
                    let items = eval_struct(value, env_map);
                    for &v in vars {
                        if self
                            .bc
                            .program
                            .contains_borrow_or_view(&self.bc.body.vars[v].ty)
                        {
                            changed |=
                                extend_loan_pairs(env_map.entry(v).or_default(), items.clone());
                        }
                    }
                }
                Command::Decide {
                    op_kind,
                    arguments,
                    arms,
                    ..
                } => {
                    let contract = op_kind.contract(self.bc.program);
                    let arg_items: Vec<Vec<(LoanPlace, BorrowMode)>> =
                        arguments.iter().map(|a| eval_struct(a, env_map)).collect();
                    for arm in arms {
                        let alt = &contract[arm.alternative];
                        for (fidx, &v) in arm.vars.iter().enumerate() {
                            if let Some(field) = alt.fields.get(fidx)
                                && self.bc.program.contains_borrow_or_view(&field.ty)
                            {
                                for &oidx in &field.origins {
                                    if let Some(items) = arg_items.get(oidx) {
                                        changed |= extend_loan_pairs(
                                            env_map.entry(v).or_default(),
                                            items.clone(),
                                        );
                                    }
                                }
                            }
                        }
                    }
                }
                Command::Loop {
                    body: inner,
                    initial,
                    arms,
                    ..
                } => {
                    if let Some(inner_head) = &self.bc.body.bodies[*inner].head {
                        for (&lp, init_e) in inner_head.parameters.iter().zip(initial) {
                            let items = eval_struct(init_e, env_map);
                            changed |= extend_loan_pairs(env_map.entry(lp).or_default(), items);
                        }
                    }
                    changed |= self.propagate_loop_body_loans(
                        *inner,
                        target_loop,
                        target_params,
                        env_map,
                        eval_struct,
                    );
                    changed |= self.propagate_inner_leaves(*inner, arms, env_map, eval_struct);
                }
                Command::Boundary {
                    body: b1,
                    contingency: b2,
                    ..
                } => {
                    changed |= self.propagate_loop_body_loans(
                        *b1,
                        target_loop,
                        target_params,
                        env_map,
                        eval_struct,
                    );
                    changed |= self.propagate_loop_body_loans(
                        *b2,
                        target_loop,
                        target_params,
                        env_map,
                        eval_struct,
                    );
                }
                Command::Again { body, arguments } if *body == target_loop => {
                    for (&lp, arg) in target_params.iter().zip(arguments) {
                        if self
                            .bc
                            .program
                            .contains_borrow_or_view(&self.bc.body.vars[lp].ty)
                        {
                            let items = eval_struct(arg, env_map);
                            changed |= extend_loan_pairs(env_map.entry(lp).or_default(), items);
                        }
                    }
                }
                _ => {}
            }
        }
        changed
    }

    fn propagate_inner_leaves<F>(
        &self,
        cur_body: BodyId,
        arms: &[Vec<VarId>],
        env_map: &mut BTreeMap<VarId, Vec<(LoanPlace, BorrowMode)>>,
        eval_struct: &mut F,
    ) -> bool
    where
        F: FnMut(
            &Expr,
            &BTreeMap<VarId, Vec<(LoanPlace, BorrowMode)>>,
        ) -> Vec<(LoanPlace, BorrowMode)>,
    {
        let mut changed = false;
        for stmt in &self.bc.body.bodies[cur_body].statements {
            match &stmt.command {
                Command::Leave {
                    alternative,
                    payload,
                } => {
                    if let Some(arm_vars) = arms.get(*alternative) {
                        for (&v, p) in arm_vars.iter().zip(payload) {
                            if self
                                .bc
                                .program
                                .contains_borrow_or_view(&self.bc.body.vars[v].ty)
                            {
                                let items = eval_struct(p, env_map);
                                changed |= extend_loan_pairs(env_map.entry(v).or_default(), items);
                            }
                        }
                    }
                }
                Command::Boundary {
                    body: b1,
                    contingency: b2,
                    ..
                } => {
                    changed |= self.propagate_inner_leaves(*b1, arms, env_map, eval_struct);
                    changed |= self.propagate_inner_leaves(*b2, arms, env_map, eval_struct);
                }
                _ => {}
            }
        }
        changed
    }

    fn scopes_down_to(&self, target_body: BodyId, mut cur_body: BodyId) -> Vec<BodyId> {
        let mut ended = Vec::new();
        loop {
            ended.push(cur_body);
            if cur_body == target_body {
                break;
            }
            match self.bc.body.bodies[cur_body].parent {
                Some(p) => cur_body = p,
                None => break,
            }
        }
        ended
    }

    fn enclosing_loop(&self, mut cur_body: BodyId) -> Option<BodyId> {
        loop {
            if self.bc.body.bodies[cur_body].head.is_some() {
                return Some(cur_body);
            }
            cur_body = self.bc.body.bodies[cur_body].parent?;
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn check_scope_end_loans(
        &mut self,
        ended_scopes: &[BodyId],
        r_i: Formula,
        after_live: &BTreeMap<VarId, Formula>,
        active_temps: &[Holder],
        line: u32,
        in_loop: bool,
        visible: &[(String, TermId, bool)],
    ) -> Result<(), Error> {
        let empty = BTreeSet::new();
        let ctx = EvalCtx {
            r_i,
            after_live,
            later_in_stmt: &empty,
            in_loop,
            visible,
        };
        for var in 0..self.bc.body.vars.len() {
            if !ended_scopes.contains(&self.bc.body.vars[var].body) {
                continue;
            }
            if matches!(self.bc.body.vars[var].ty, Type::Ref(_, _)) {
                continue;
            }
            self.check_access(
                &LoanPlace {
                    root: LoanRoot::Owned(var),
                    steps: Vec::new(),
                },
                true,
                None,
                &ctx,
                active_temps,
                line,
            )?;
        }
        Ok(())
    }

    fn check_body_loans(
        &mut self,
        body_id: BodyId,
        in_loop: bool,
    ) -> Result<Vec<LeaveLoanRecord>, Error> {
        let mut leaves = Vec::new();
        let stmts = self.bc.body.bodies[body_id].statements.clone();
        for (stmt_idx, stmt) in stmts.iter().enumerate() {
            let line = stmt.line;
            let r_i = self
                .bc
                .stmt_r
                .get(&(body_id, stmt_idx))
                .copied()
                .unwrap_or(bdd::FALSE);
            let visible = self
                .bc
                .stmt_visible
                .get(&(body_id, stmt_idx))
                .cloned()
                .unwrap_or_default();
            let after_live = self
                .live_after_stmt
                .get(&(body_id, stmt_idx))
                .cloned()
                .unwrap_or_default();
            let empty = BTreeSet::new();
            let ctx = EvalCtx {
                r_i,
                after_live: &after_live,
                later_in_stmt: &empty,
                in_loop,
                visible: &visible,
            };

            match &stmt.command {
                Command::Spawn { .. } | Command::Cancel { .. } => {}
                Command::Bind { var, value } => {
                    let mut temps = Vec::new();
                    let ret = self.eval_loan_expr(value, true, &ctx, &mut temps, line)?;
                    if self
                        .bc
                        .program
                        .contains_borrow_or_view(&self.bc.body.vars[*var].ty)
                    {
                        self.attach_holder_loans(Holder::Var(*var), &ret, r_i);
                    }
                }
                Command::Unpack { vars, value, .. } => {
                    let mut temps = Vec::new();
                    let ret = self.eval_loan_expr(value, true, &ctx, &mut temps, line)?;
                    for &v in vars {
                        if self
                            .bc
                            .program
                            .contains_borrow_or_view(&self.bc.body.vars[v].ty)
                        {
                            self.attach_holder_loans(Holder::Var(v), &ret, r_i);
                        }
                    }
                }
                Command::Assign { var, value } => {
                    let mut temps = Vec::new();
                    let is_ref = matches!(self.bc.body.vars[*var].ty, Type::Ref(_, _));
                    let mut later = BTreeSet::new();
                    if is_ref {
                        later.insert(*var);
                    }
                    let vctx = ctx.with_later(&later);
                    let ret = self.eval_loan_expr(value, true, &vctx, &mut temps, line)?;
                    let (lp, through) = if is_ref {
                        (
                            LoanPlace {
                                root: LoanRoot::Behind(*var, Vec::new()),
                                steps: Vec::new(),
                            },
                            Some(Holder::Var(*var)),
                        )
                    } else {
                        (
                            LoanPlace {
                                root: LoanRoot::Owned(*var),
                                steps: Vec::new(),
                            },
                            None,
                        )
                    };
                    self.check_access(&lp, true, through, &ctx, &temps, line)?;
                    if self
                        .bc
                        .program
                        .contains_borrow_or_view(&self.bc.body.vars[*var].ty)
                    {
                        self.attach_holder_loans(Holder::Var(*var), &ret, r_i);
                    }
                }
                Command::AssignPlace { target, value } => {
                    let mut temps = Vec::new();
                    let target_has_ref_or_view =
                        self.bc.program.contains_borrow_or_view(&target.root_ty);
                    let idx_exprs: Vec<&Expr> = target
                        .steps
                        .iter()
                        .filter_map(|s| match s {
                            PlaceStep::Index(e, _) => Some(e),
                            PlaceStep::Field(_, _, _) => None,
                        })
                        .collect();
                    let mut value_later = BTreeSet::new();
                    if target_has_ref_or_view {
                        value_later.insert(target.root);
                    }
                    for ie in &idx_exprs {
                        collect_expr_mentions(ie, &mut value_later);
                    }
                    let vctx = ctx.with_later(&value_later);
                    self.eval_loan_expr(value, true, &vctx, &mut temps, line)?;
                    for (k, ie) in idx_exprs.iter().enumerate() {
                        let mut ilater = BTreeSet::new();
                        if target_has_ref_or_view {
                            ilater.insert(target.root);
                        }
                        for rem in &idx_exprs[k + 1..] {
                            collect_expr_mentions(rem, &mut ilater);
                        }
                        let ictx = ctx.with_later(&ilater);
                        self.eval_loan_expr(ie, false, &ictx, &mut temps, line)?;
                    }
                    let lp = place_to_loan_place(self.bc.program, self.bc.body, target);
                    let through = match &lp.root {
                        LoanRoot::Behind(v, _) => Some(Holder::Var(*v)),
                        _ => None,
                    };
                    self.check_access(&lp, true, through, &ctx, &temps, line)?;
                }
                Command::Oblige(_) | Command::Escalate | Command::Impossible => {}
                Command::Test { condition, .. } => {
                    let mut temps = Vec::new();
                    self.eval_loan_expr(condition, false, &ctx, &mut temps, line)?;
                }
                Command::Capture { arguments, .. } => {
                    let mut temps = Vec::new();
                    let _ = self.eval_loan_operands(arguments, &ctx, &mut temps, line)?;
                }
                Command::Decide {
                    site,
                    op_kind,
                    arguments,
                    arms,
                    ..
                } => {
                    let mut temps = Vec::new();
                    let arg_loans = self.eval_loan_operands(arguments, &ctx, &mut temps, line)?;
                    let contract = op_kind.contract(self.bc.program);
                    for (pos, arm) in arms.iter().enumerate() {
                        let atom = self.bc.atom(*site, pos);
                        let g = self.bc.solver.bdd.and(r_i, atom);
                        let alt = &contract[arm.alternative];
                        for (fidx, &var_id) in arm.vars.iter().enumerate() {
                            if let Some(field) = alt.fields.get(fidx)
                                && self.bc.program.contains_borrow_or_view(&field.ty)
                            {
                                for &oidx in &field.origins {
                                    if let Some(src) = arg_loans.get(oidx) {
                                        self.attach_holder_loans(Holder::Var(var_id), src, g);
                                    }
                                }
                            }
                        }
                    }
                }
                Command::Loop {
                    site,
                    body: inner,
                    initial,
                    arms,
                } => {
                    let mut temps = Vec::new();
                    let init_loans = self.eval_loan_operands(initial, &ctx, &mut temps, line)?;
                    let head = self.bc.body.bodies[*inner]
                        .head
                        .clone()
                        .expect("a loop head");
                    for (&lp_var, iloans) in head.parameters.iter().zip(&init_loans) {
                        if self
                            .bc
                            .program
                            .contains_borrow_or_view(&self.bc.body.vars[lp_var].ty)
                        {
                            self.attach_holder_loans(Holder::Var(lp_var), iloans, r_i);
                        }
                    }
                    self.seed_loop_again_loans(*inner, r_i);
                    let inner_leaves = self.check_body_loans(*inner, true)?;
                    for (target_loop, leave_alt, leave_r, pay_loans) in inner_leaves {
                        if target_loop != *inner {
                            leaves.push((target_loop, leave_alt, leave_r, pay_loans));
                            continue;
                        }
                        let atom = self.bc.atom(*site, leave_alt);
                        let g = self.bc.solver.bdd.and(atom, leave_r);
                        if let Some(arm_vars) = arms.get(leave_alt) {
                            for (&var_id, ploans) in arm_vars.iter().zip(&pay_loans) {
                                if self
                                    .bc
                                    .program
                                    .contains_borrow_or_view(&self.bc.body.vars[var_id].ty)
                                {
                                    self.attach_holder_loans(Holder::Var(var_id), ploans, g);
                                }
                            }
                        }
                    }
                }
                Command::Boundary {
                    body: b1,
                    captures,
                    contingency: b2,
                    ..
                } => {
                    for &cap_var in captures {
                        let is_write =
                            self.bc.program.kind(&self.bc.body.vars[cap_var].ty) != Kind::Copy;
                        self.check_access(
                            &LoanPlace {
                                root: LoanRoot::Owned(cap_var),
                                steps: Vec::new(),
                            },
                            is_write,
                            None,
                            &ctx,
                            &[],
                            line,
                        )?;
                    }
                    let b1_leaves = self.check_body_loans(*b1, in_loop)?;
                    leaves.extend(b1_leaves);
                    let b1_exit = self
                        .bc
                        .boundary_fallthrough_live
                        .get(b1)
                        .copied()
                        .unwrap_or(bdd::FALSE);
                    if b1_exit != bdd::FALSE {
                        let b1_end_after = self
                            .boundary_after_live
                            .get(b1)
                            .cloned()
                            .unwrap_or_default();
                        self.check_scope_end_loans(
                            &[*b1],
                            b1_exit,
                            &b1_end_after,
                            &[],
                            line,
                            in_loop,
                            &visible,
                        )?;
                    }
                    let b2_leaves = self.check_body_loans(*b2, in_loop)?;
                    leaves.extend(b2_leaves);
                }
                Command::Supervise { arguments, .. } => {
                    let mut temps = Vec::new();
                    let _ = self.eval_loan_operands(arguments, &ctx, &mut temps, line)?;
                }
                Command::Again {
                    body: target,
                    arguments,
                } => {
                    let mut temps = Vec::new();
                    let _ = self.eval_loan_operands(arguments, &ctx, &mut temps, line)?;
                    let ended = self.scopes_down_to(*target, body_id);
                    self.check_scope_end_loans(
                        &ended,
                        r_i,
                        &after_live,
                        &temps,
                        line,
                        in_loop,
                        &visible,
                    )?;
                }
                Command::Leave {
                    alternative,
                    payload,
                } => {
                    let mut temps = Vec::new();
                    let pay_loans = self.eval_loan_operands(payload, &ctx, &mut temps, line)?;
                    if let Some(target_loop) = self.enclosing_loop(body_id) {
                        let ended = self.scopes_down_to(target_loop, body_id);
                        self.check_scope_end_loans(
                            &ended,
                            r_i,
                            &after_live,
                            &temps,
                            line,
                            in_loop,
                            &visible,
                        )?;
                        leaves.push((target_loop, *alternative, r_i, pay_loans));
                    }
                }
                Command::Exit {
                    alternative,
                    payload,
                } => {
                    let mut temps = Vec::new();
                    let pay_loans = self.eval_loan_operands(payload, &ctx, &mut temps, line)?;
                    let alt = &self.bc.contract[*alternative];
                    for (fidx, field) in alt.fields.iter().enumerate() {
                        if self.bc.program.contains_borrow_or_view(&field.ty)
                            && let Some(ploans) = pay_loans.get(fidx)
                        {
                            for &(lid, hg) in ploans {
                                let loan = &self.loans[lid];
                                let allowed = match &loan.place.root {
                                    LoanRoot::ParamOrigin(pidx) => field.origins.contains(pidx),
                                    LoanRoot::Behind(v, _) if *v < self.bc.param_types.len() => {
                                        field.origins.contains(v)
                                    }
                                    LoanRoot::Behind(_, _) => true,
                                    LoanRoot::Owned(_) => false,
                                };
                                if !allowed {
                                    let created_and_held =
                                        self.bc.solver.bdd.and(loan.created_on, hg);
                                    let bad = self.bc.solver.bdd.and(r_i, created_and_held);
                                    if bad != bdd::FALSE {
                                        let desc = self.describe_place(&loan.place);
                                        let msg = format!(
                                            "borrowed payload `{}` in exit `{}` holds a loan on `{desc}`, which does not match its allowed origins",
                                            field.name, alt.name
                                        );
                                        require_entailment(
                                            &mut self.bc.solver,
                                            bad,
                                            &self.bc.owner_name,
                                            line,
                                            "L4",
                                            msg,
                                            &visible,
                                            in_loop,
                                            self.bc.certificates,
                                        )?;
                                    }
                                }
                            }
                        }
                    }
                    let ended = self.scopes_down_to(0, body_id);
                    self.check_scope_end_loans(
                        &ended,
                        r_i,
                        &after_live,
                        &temps,
                        line,
                        in_loop,
                        &visible,
                    )?;
                }
                Command::Fault { message, .. } => {
                    let mut temps = Vec::new();
                    self.eval_loan_expr(message, true, &ctx, &mut temps, line)?;
                }
                Command::Terminate(_) => {
                    let temps = Vec::new();
                    let ended = self.scopes_down_to(0, body_id);
                    self.check_scope_end_loans(
                        &ended,
                        r_i,
                        &after_live,
                        &temps,
                        line,
                        in_loop,
                        &visible,
                    )?;
                }
                Command::Recover { body: target } => {
                    let ended = self.scopes_down_to(*target, body_id);
                    self.check_scope_end_loans(
                        &ended,
                        r_i,
                        &after_live,
                        &[],
                        line,
                        in_loop,
                        &visible,
                    )?;
                }
            }
        }
        Ok(leaves)
    }
}

fn dedup_loan_pairs(list: &mut Vec<(LoanPlace, BorrowMode)>) {
    let mut out = Vec::with_capacity(list.len());
    for item in list.drain(..) {
        if !out.contains(&item) {
            out.push(item);
        }
    }
    *list = out;
}

fn extend_loan_pairs(
    dest: &mut Vec<(LoanPlace, BorrowMode)>,
    items: Vec<(LoanPlace, BorrowMode)>,
) -> bool {
    let mut changed = false;
    for item in items {
        if !dest.contains(&item) {
            dest.push(item);
            changed = true;
        }
    }
    changed
}

fn expr_structural_external_loans(
    program: &Program,
    body: &ControlBody,
    expr: &Expr,
    env: &BTreeMap<VarId, Vec<(LoanPlace, BorrowMode)>>,
    is_outside: &dyn Fn(&LoanRoot) -> bool,
) -> Vec<(LoanPlace, BorrowMode)> {
    let mut out = Vec::new();
    match expr {
        Expr::Borrow(mode, place, _) => {
            let lp = place_to_loan_place(program, body, place);
            if is_outside(&lp.root) {
                out.push((lp.clone(), *mode));
            }
            if matches!(lp.root, LoanRoot::Behind(_, _))
                && let Some(inherited) = env.get(&place.root)
            {
                out.extend(inherited.iter().cloned());
            }
        }
        Expr::Var(VarRef::Local(id), ty) if program.contains_borrow_or_view(ty) => {
            if let Some(items) = env.get(id) {
                out.extend(items.iter().cloned());
            }
        }
        Expr::Field(base, _, _, ty) if program.contains_borrow_or_view(ty) => {
            out.extend(expr_structural_external_loans(
                program, body, base, env, is_outside,
            ));
        }
        Expr::Struct(sid, fields, _) if program.structs[*sid].is_view => {
            for field in fields {
                out.extend(expr_structural_external_loans(
                    program, body, field, env, is_outside,
                ));
            }
        }
        Expr::Move(inner, _) => {
            out.extend(expr_structural_external_loans(
                program, body, inner, env, is_outside,
            ));
        }
        _ => {}
    }
    dedup_loan_pairs(&mut out);
    out
}

impl<'a> BodyChecker<'a> {
    fn check_loans(&mut self) -> Result<(), Error> {
        let mut checker = LoanChecker::new(self);
        checker.collect_body_mentions(0, false);
        let empty = BTreeMap::new();
        checker.compute_body_liveness(0, &empty, &[], &[]);
        let _ = checker.check_body_loans(0, false)?;
        Ok(())
    }
}
