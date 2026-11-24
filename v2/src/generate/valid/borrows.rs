//! The borrows of slice 3 in the generator of valid programs.
//!
//! A borrow is a loan on a place ([L1] of `docs/v2/core.md`), and the names
//! that carry it hold the loan: the name a borrow is bound to, the copies of
//! a shared one, the name an exclusive one moves to, a borrow made through
//! it, and the payload names that an operation derives from a borrowed
//! argument. For every name on every history the generator keeps the loans
//! it holds ([`Loan`]). A loan is live while one of its holders is available
//! ([L2]): a holder that the generator stops mentioning ends its loans
//! there. It is marked gone, as a moved name is, and nothing mentions it
//! again ([`Generator::retire`]).
//!
//! While a statement is written, the names that live loans are on are lent
//! ([`Generator::lend_view`]): a name lent exclusively is not available to
//! the statement at all, and one lent shared is read and not written, moved
//! or lent exclusively ([L3]). A borrow name that a borrow made through it
//! lends is lent in the same way, since an access through it is an access to
//! what is behind it. So the steps of slices 1 and 2 respect the loans
//! without knowing of them, and the steps here make borrows, copy and move
//! them, and write through them. A borrow of a place is made only where it
//! overlaps no place that a live loan holds, unless both are shared; that
//! test goes by the place, so two fields of one struct may be lent
//! exclusively at once.
//!
//! A loop body does not end a holder that it did not bind: one generic
//! iteration stands for all of them, and a mention of the holder anywhere in
//! the body follows an access in the iteration before ([L2a]). What it lends
//! stays lent throughout the body.
//!
//! What is known of the value behind a borrow name is what was known of the
//! place it was made of ([I7]): while the borrow is live, nothing else
//! changes that place. A write through it changes what it knows, and what
//! its exclusive loans are on is known by its type alone afterwards.

use super::data::{Ctx, Kind, held, know_at};
use super::{
    AltSig, BTreeSet, BorrowMode, Command, End, Env, Expr, FieldSig, Generator, Know, POS, Range,
    Selector, Sig, Slot, Type, int, name,
};
use crate::syntax::{Place, PlaceStep};

/// A loan that a name holds ([L1]): the place it is on and the mode of the
/// borrow that made it. The place starts at `root`; where `root` is a borrow
/// name, the place is behind it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Loan {
    pub(super) root: String,
    pub(super) path: Vec<Step>,
    pub(super) mode: BorrowMode,
}

/// A step of the place of a loan: a field by its position, or an index,
/// which overlaps every other index of its collection ([L3]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Step {
    Field(usize),
    Index,
}

/// Whether two places from one root overlap: one is a prefix of the other.
fn overlap(a: &[Step], b: &[Step]) -> bool {
    a.iter().zip(b).all(|(x, y)| x == y)
}

/// What is known of a value reached through a borrow name: as `know`, with
/// no integer a constant. The checker takes a name bound once to a constant
/// expression as that constant ([I3]), and a borrow name is no such name, so
/// it neither multiplies nor divides as a literal does.
fn variable(know: Know) -> Know {
    match know {
        Know::Int(mut val) => {
            val.constant = None;
            Know::Int(val)
        }
        Know::Struct(fields) => Know::Struct(fields.into_iter().map(variable).collect()),
        Know::Variant(constructors) => Know::Variant(
            constructors
                .into_iter()
                .map(|fields| fields.map(|fields| fields.into_iter().map(variable).collect()))
                .collect(),
        ),
        other => other,
    }
}

/// Whether an operation lends from its arguments: some payload field of it
/// is a borrow.
pub(super) fn lends(sig: &Sig) -> bool {
    sig.alts
        .iter()
        .flat_map(|alternative| &alternative.fields)
        .any(|field| matches!(field.ty, Type::Ref(_, _)))
}

/// A place that a borrow may be made of or a write may go to: the
/// expression that names it, its root and the steps from it, as the loan
/// and as the target of an assignment write them, its type, and what is
/// known of the value there.
#[derive(Clone)]
struct Spot {
    expr: Expr,
    root: String,
    path: Vec<Step>,
    steps: Vec<PlaceStep>,
    ty: Type,
    know: Know,
}

impl Generator<'_> {
    /// The loans that the available names of the histories `running` hold.
    fn live_loans(&self, running: &[usize]) -> Vec<Loan> {
        let scope = self.scope();
        let mut out: Vec<Loan> = Vec::new();
        for &index in running {
            for slot in scope.live[index].env.values() {
                if slot.gone {
                    continue;
                }
                for loan in &slot.loans {
                    if !out.contains(loan) {
                        out.push(loan.clone());
                    }
                }
            }
        }
        out
    }

    /// Marks in `env`, the names as a statement on the histories `running`
    /// sees them, how the live loans lend each name. One lent exclusively is
    /// gone for the statement; one lent shared is read only ([L3]).
    pub(super) fn lend_view(&self, running: &[usize], env: &mut Env) {
        for loan in self.live_loans(running) {
            if let Some(slot) = env.get_mut(&loan.root) {
                slot.lent = slot.lent.max(Some(loan.mode));
                if loan.mode == BorrowMode::Exclusive {
                    slot.gone = true;
                }
            }
        }
    }

    /// Ends the loans of one holder on the histories `running`: nothing
    /// mentions it from here on ([L2]). A holder that a loop body around did
    /// not bind is left as it is ([L2a]).
    pub(super) fn retire(&mut self, running: &[usize]) {
        let floor = self.floor();
        let env = self.merged_env(running);
        let holders: Vec<String> = env
            .iter()
            .filter(|(_, slot)| !slot.gone && !slot.loans.is_empty() && slot.home >= floor)
            .map(|(holder, _)| holder.clone())
            .collect();
        if holders.is_empty() {
            return;
        }
        let chosen = self.rng.pick(&holders).clone();
        let here = self.here();
        for &index in running {
            if let Some(slot) = self.scopes[here].live[index].env.get_mut(&chosen) {
                slot.gone = true;
            }
        }
    }

    /// After a write through the name `root` on the histories `running`:
    /// what its exclusive loans are on may have changed, and is known by
    /// its type alone ([I9]). Nothing happens where `root` holds no loan.
    pub(super) fn written_through(&mut self, running: &[usize], root: &str) {
        let here = self.here();
        for &index in running {
            let env = &self.scopes[here].live[index].env;
            let Some(slot) = env.get(root) else {
                continue;
            };
            let roots: Vec<String> = slot
                .loans
                .iter()
                .filter(|loan| loan.mode == BorrowMode::Exclusive)
                .map(|loan| loan.root.clone())
                .collect();
            let tops: Vec<(String, Know)> = roots
                .into_iter()
                .filter_map(|changed| {
                    let top = self.types.top(&env.get(&changed)?.ty);
                    Some((changed, top))
                })
                .collect();
            for (changed, top) in tops {
                if let Some(slot) = self.scopes[here].live[index].env.get_mut(&changed) {
                    slot.know = top;
                    slot.definition = None;
                }
            }
        }
    }

    /// The places within the value of `start`, through fields and at an
    /// index known to be in range, two steps deep at most, that hold no
    /// obligation.
    fn spots_within(&self, start: Spot, depth: u8, out: &mut Vec<Spot>) {
        if depth > 0 {
            match (&start.ty, &start.know) {
                (Type::Named(named), _) => {
                    if let Some(info) = self.types.structure(named) {
                        for (position, (field, ty)) in info.fields.iter().enumerate() {
                            let know = match &start.know {
                                Know::Struct(fields) => fields[position].clone(),
                                _ => self.types.top(ty),
                            };
                            let mut inner = start.clone();
                            inner.expr = Expr::Field(Box::new(start.expr.clone()), field.clone());
                            inner.path.push(Step::Field(position));
                            inner.steps.push(PlaceStep::Field(field.clone()));
                            inner.ty = ty.clone();
                            inner.know = know;
                            self.spots_within(inner, depth - 1, out);
                        }
                    }
                }
                (Type::Vector(item), Know::Sized(length)) if length.lo >= 1 => {
                    let last = (length.lo - 1).min(3);
                    for position in [0, last] {
                        let mut inner = start.clone();
                        inner.expr =
                            Expr::Index(Box::new(start.expr.clone()), Box::new(int(position)));
                        inner.path.push(Step::Index);
                        inner.steps.push(PlaceStep::Index(int(position)));
                        inner.ty = (**item).clone();
                        inner.know = self.types.top(item);
                        self.spots_within(inner, depth - 1, out);
                        if last == 0 {
                            break;
                        }
                    }
                }
                _ => {}
            }
        }
        if self.types.kind(&start.ty) != Kind::Must {
            out.push(start);
        }
    }

    /// The places of the histories `running` that a borrow in `mode` may be
    /// made of: within an available name that owns its value, or behind a
    /// borrow name; none overlaps a place that a live loan holds unless both
    /// are shared ([L3]). An exclusive one needs a name bound with `~`
    /// ([C1]) or an exclusive borrow name that is not kept read-only. The
    /// counter of a loop and a name that a named boundary retains are left
    /// alone.
    fn lendable(&self, running: &[usize], mode: BorrowMode) -> Vec<Spot> {
        let env = self.merged_env(running);
        let loans = self.live_loans(running);
        let counters = self.counters();
        let mut out = Vec::new();
        for (root, slot) in &env {
            if slot.gone || counters.contains(root) || self.retained.contains(root) {
                continue;
            }
            let (ty, writable) = match &slot.ty {
                Type::Ref(held, inner) => (
                    (**inner).clone(),
                    *held == BorrowMode::Exclusive && slot.lent.is_none(),
                ),
                Type::Bool | Type::Int(_) => (slot.ty.clone(), slot.mutable),
                other if self.types.kind(other) == Kind::Must => continue,
                other => (other.clone(), slot.mutable),
            };
            if mode == BorrowMode::Exclusive && !writable {
                continue;
            }
            let mut found = Vec::new();
            self.spots_within(
                Spot {
                    expr: name(root),
                    root: root.clone(),
                    path: Vec::new(),
                    steps: Vec::new(),
                    ty,
                    know: slot.know.clone(),
                },
                2,
                &mut found,
            );
            out.extend(found.into_iter().filter(|spot| {
                loans.iter().all(|loan| {
                    loan.root != spot.root
                        || !overlap(&loan.path, &spot.path)
                        || mode == BorrowMode::Shared && loan.mode == BorrowMode::Shared
                })
            }));
        }
        out
    }

    /// One statement on borrows. False when none could be written.
    pub(super) fn borrow_step(
        &mut self,
        selector: &Selector,
        running: &[usize],
        room: bool,
    ) -> bool {
        match self.rng.below(9) {
            0..=3 => self.bind_borrow(selector, running),
            4 => self.copy_borrow(selector, running),
            // A map that a host is to lend from needs entries.
            5 if room => self.map_op(selector, running),
            _ => self.write_through(selector, running),
        }
    }

    /// `r : &τ := &p` or `r : &~τ := &~p` ([E-Borrow]): a borrow of a place
    /// of a name, or of a place behind a borrow name, which `r` holds with
    /// every loan of that name ([L1]).
    fn bind_borrow(&mut self, selector: &Selector, running: &[usize]) -> bool {
        let mode = if self.rng.chance(1, 3) {
            BorrowMode::Exclusive
        } else {
            BorrowMode::Shared
        };
        let spots = self.lendable(running, mode);
        if spots.is_empty() {
            return false;
        }
        let spot = self.rng.pick(&spots).clone();
        let env = self.merged_env(running);
        let mut loans = match env.get(&spot.root) {
            Some(slot) if matches!(slot.ty, Type::Ref(_, _)) => slot.loans.clone(),
            _ => Vec::new(),
        };
        loans.push(Loan {
            root: spot.root.clone(),
            path: spot.path.clone(),
            mode,
        });
        let bound = self.fresh("r");
        let ty = Type::Ref(mode, Box::new(spot.ty.clone()));
        self.push(
            selector,
            Command::Bind {
                mutable: false,
                name: bound.clone(),
                ty: Some(ty.clone()),
                value: Expr::Borrow(mode, Box::new(spot.expr)),
            },
        );
        let mut slot = self.slot(&ty, false, variable(spot.know));
        slot.loans = loans;
        self.bind_name(running, &bound, &slot);
        true
    }

    /// `t : &τ := s` copies a shared borrow name, and `q : &~τ := r` moves
    /// an exclusive one ([E-Var], [O3]); the new name holds every loan of
    /// the old one.
    fn copy_borrow(&mut self, selector: &Selector, running: &[usize]) -> bool {
        let mut ctx = self.ctx(running);
        let names: Vec<String> = ctx
            .env
            .iter()
            .filter(|(held, slot)| match &slot.ty {
                Type::Ref(BorrowMode::Shared, _) => !slot.gone,
                Type::Ref(BorrowMode::Exclusive, _) => self.consumable(held, slot),
                _ => false,
            })
            .map(|(held, _)| held.clone())
            .collect();
        if names.is_empty() {
            return false;
        }
        let chosen = self.rng.pick(&names).clone();
        let old = ctx.env[&chosen].clone();
        let value = if matches!(old.ty, Type::Ref(BorrowMode::Exclusive, _)) {
            ctx.moved.push(chosen.clone());
            if self.rng.chance(1, 2) {
                Expr::Move(Box::new(name(&chosen)))
            } else {
                name(&chosen)
            }
        } else {
            name(&chosen)
        };
        let bound = self.fresh("r");
        self.push(
            selector,
            Command::Bind {
                mutable: false,
                name: bound.clone(),
                ty: Some(old.ty.clone()),
                value,
            },
        );
        self.apply(running, &ctx);
        let mut slot = self.slot(&old.ty, false, old.know.clone());
        slot.loans = old.loans.clone();
        self.bind_name(running, &bound, &slot);
        true
    }

    /// `r ← e`, `r.f ← e` or `r[i] ← e` through an exclusive borrow name
    /// that nothing lends ([E-Assign], [B1]).
    fn write_through(&mut self, selector: &Selector, running: &[usize]) -> bool {
        let mut ctx = self.ctx(running);
        let writers: Vec<String> = ctx
            .env
            .iter()
            .filter(|(_, slot)| {
                matches!(slot.ty, Type::Ref(BorrowMode::Exclusive, _))
                    && !slot.gone
                    && slot.lent.is_none()
            })
            .map(|(writer, _)| writer.clone())
            .collect();
        if writers.is_empty() {
            return false;
        }
        let chosen = self.rng.pick(&writers).clone();
        let slot = ctx.env[&chosen].clone();
        let Type::Ref(_, inner) = &slot.ty else {
            return false;
        };
        let mut targets = Vec::new();
        self.spots_within(
            Spot {
                expr: name(&chosen),
                root: chosen.clone(),
                path: Vec::new(),
                steps: Vec::new(),
                ty: (**inner).clone(),
                know: slot.know.clone(),
            },
            2,
            &mut targets,
        );
        if targets.is_empty() {
            return false;
        }
        let target = self.rng.pick(&targets).clone();
        ctx.lent.insert(chosen.clone());
        let Some((value, know)) = self.value(&mut ctx, &target.ty, 2) else {
            return false;
        };
        let command = if target.steps.is_empty() {
            Command::Assign {
                name: chosen.clone(),
                value,
            }
        } else {
            Command::AssignPlace {
                target: Place {
                    root: chosen.clone(),
                    steps: target.steps.clone(),
                },
                value,
            }
        };
        self.push(selector, command);
        self.apply(running, &ctx);
        self.written_through(running, &chosen);
        // What is behind the name is the value written; an element is
        // known by its type alone in any case.
        if !target.path.contains(&Step::Index) {
            let fields: Vec<usize> = target
                .path
                .iter()
                .map(|step| match step {
                    Step::Field(position) => *position,
                    Step::Index => unreachable!("no index on the way"),
                })
                .collect();
            let know = variable(held(&target.ty, know));
            let here = self.here();
            for &index in running {
                let env = &mut self.scopes[here].live[index].env;
                if let Some(seen) = know_at(env, &chosen, &fields) {
                    *seen = know.clone();
                }
            }
        }
        true
    }

    /// An operand for a parameter `&τ` or `&~τ` made of a borrow name
    /// ([C1], [L1]): a shared borrow name itself, which is copied; an
    /// exclusive one itself, which moves into the operation; or a borrow
    /// made through either, `&r` or `&~r`. What an exclusive operand lends
    /// may change.
    pub(super) fn borrow_operand(
        &mut self,
        ctx: &mut Ctx,
        mode: BorrowMode,
        inner: &Type,
        pre: Range,
    ) -> Option<Expr> {
        let long = |slot: &Slot| match &slot.know {
            Know::Sized(length) => length.lo >= pre.lo,
            _ => pre.lo <= 0,
        };
        let names: Vec<String> = ctx
            .env
            .iter()
            .filter(|(held, slot)| {
                let Type::Ref(lender, referent) = &slot.ty else {
                    return false;
                };
                **referent == *inner
                    && !slot.gone
                    && long(slot)
                    && match mode {
                        BorrowMode::Shared => !ctx.exclusive.contains(*held),
                        BorrowMode::Exclusive => {
                            *lender == BorrowMode::Exclusive
                                && slot.lent.is_none()
                                && !ctx.lent.contains(*held)
                        }
                    }
            })
            .map(|(held, _)| held.clone())
            .collect();
        if names.is_empty() {
            return None;
        }
        let chosen = self.rng.pick(&names).clone();
        let slot = ctx.env[&chosen].clone();
        ctx.lent.insert(chosen.clone());
        let shared_name = matches!(slot.ty, Type::Ref(BorrowMode::Shared, _));
        Some(match mode {
            BorrowMode::Shared if shared_name && self.rng.chance(1, 2) => name(&chosen),
            BorrowMode::Shared => Expr::Borrow(BorrowMode::Shared, Box::new(name(&chosen))),
            BorrowMode::Exclusive => {
                ctx.exclusive.insert(chosen.clone());
                for loan in &slot.loans {
                    if loan.mode == BorrowMode::Exclusive && !ctx.changed.contains(&loan.root) {
                        ctx.changed.push(loan.root.clone());
                    }
                }
                if self.consumable(&chosen, &slot) && self.rng.chance(1, 2) {
                    ctx.moved.push(chosen.clone());
                    if let Some(seen) = ctx.env.get_mut(&chosen) {
                        seen.gone = true;
                    }
                    name(&chosen)
                } else {
                    ctx.changed.push(chosen.clone());
                    Expr::Borrow(BorrowMode::Exclusive, Box::new(name(&chosen)))
                }
            }
        })
    }

    /// The loans that a payload name derived from the arguments at
    /// `origins` holds: those of each argument ([L1]). An argument `&p` or
    /// `&~p` is a loan on all of `p`, and on what is behind it too where it
    /// is a borrow name; a borrow name passed as it is gives its own.
    pub(super) fn derived_loans(env: &Env, arguments: &[Expr], origins: &[usize]) -> Vec<Loan> {
        let mut out: Vec<Loan> = Vec::new();
        for &origin in origins {
            let lent = match &arguments[origin] {
                Expr::Borrow(mode, place) => {
                    let mut root = &**place;
                    while let Expr::Field(base, _) | Expr::Index(base, _) = root {
                        root = base.as_ref();
                    }
                    let Expr::Name(root) = root else {
                        continue;
                    };
                    let mut lent = match env.get(root) {
                        Some(slot) if matches!(slot.ty, Type::Ref(_, _)) => slot.loans.clone(),
                        _ => Vec::new(),
                    };
                    lent.push(Loan {
                        root: root.clone(),
                        path: Vec::new(),
                        mode: *mode,
                    });
                    lent
                }
                Expr::Name(held) => env
                    .get(held)
                    .map(|slot| slot.loans.clone())
                    .unwrap_or_default(),
                Expr::Move(inner) => match &**inner {
                    Expr::Name(held) => env
                        .get(held)
                        .map(|slot| slot.loans.clone())
                        .unwrap_or_default(),
                    _ => Vec::new(),
                },
                _ => Vec::new(),
            };
            for loan in lent {
                if !out.contains(&loan) {
                    out.push(loan);
                }
            }
        }
        out
    }

    /// The operations whose outcome a name may hold: those whose payloads
    /// hold no borrow.
    pub(super) fn capturable(&self) -> Vec<String> {
        self.callables
            .iter()
            .filter(|sig| !lends(sig))
            .map(|sig| sig.name.clone())
            .collect()
    }

    /// The types of the places within a value of the type `ty` that a host
    /// may lend, each with whether every value of `ty` has such a place and
    /// whether it may be lent exclusively: the value itself and its struct
    /// fields always, the fields of a variant, the elements of a vector and
    /// the values of a map where there are any, and the keys of a map
    /// shared only ([E-Extern]).
    fn lent_types(
        &self,
        ty: &Type,
        always: bool,
        exclusive: bool,
        out: &mut Vec<(Type, bool, bool)>,
    ) {
        if self.types.kind(ty) != Kind::Must {
            out.push((ty.clone(), always, exclusive));
        }
        match ty {
            Type::Named(named) => {
                if let Some(info) = self.types.structure(named) {
                    for (_, field) in &info.fields {
                        self.lent_types(field, always, exclusive, out);
                    }
                } else if let Some(info) = self.types.variant(named) {
                    for (_, fields) in &info.constructors {
                        for (_, field) in fields {
                            self.lent_types(field, false, exclusive, out);
                        }
                    }
                }
            }
            Type::Vector(item) => self.lent_types(item, false, exclusive, out),
            Type::Map(key, value) => {
                self.lent_types(key, false, false, out);
                self.lent_types(value, false, exclusive, out);
            }
            _ => {}
        }
    }

    /// Now and then an extern control borrows one collection more, shared
    /// or exclusively, so that its alternatives may lend the keys and the
    /// values of a map or the elements of a vector ([E-Extern]): a map with
    /// the type of its keys and values, or a vector whose length the
    /// precondition bounds below, so that its arguments have elements. Data
    /// of every type is drawn for parameters, and a collection would seldom
    /// be borrowed by an extern control otherwise.
    pub(super) fn lend_a_collection(
        &mut self,
        params: &mut Vec<(String, Type)>,
        pre: &mut Vec<Range>,
    ) {
        if !self.rng.chance(1, 4) {
            return;
        }
        let (collection, length) = if self.rng.chance(1, 2) {
            let key = if self.rng.chance(1, 2) {
                Type::String
            } else {
                Type::Int(*self.rng.pick(&self.palette))
            };
            let map = Type::Map(Box::new(key), Box::new(self.element_type()));
            (map, Range::ALL)
        } else {
            let vector = Type::Vector(Box::new(self.element_type()));
            (vector, Range::new(self.rng.range(1, 3), POS))
        };
        let mode = if self.rng.chance(1, 2) {
            BorrowMode::Exclusive
        } else {
            BorrowMode::Shared
        };
        params.push((
            format!("p{}", params.len()),
            Type::Ref(mode, Box::new(collection)),
        ));
        pre.push(length);
    }

    /// An extern control lends from its borrowed parameters: now and then a
    /// payload field is a borrow of a place within one of them, `&τ ∈ p`,
    /// or `&~τ ∈ p` where `p` is lent exclusively ([E-Extern], [W9]). The
    /// host names a place of the type `τ` within the argument. The first
    /// `forced` alternatives, those that an argument may leave as the only
    /// ones its conditions allow, lend only what every argument has, so that
    /// some alternative can always be answered; an alternative lends from a
    /// parameter once at most, so that two exclusive borrows never have to
    /// be found apart.
    pub(super) fn lend_payloads(
        &mut self,
        params: &[(String, Type)],
        alts: &mut [AltSig],
        forced: usize,
    ) {
        let lenders: Vec<usize> = (0..params.len())
            .filter(|&position| matches!(params[position].1, Type::Ref(_, _)))
            .collect();
        if lenders.is_empty() {
            return;
        }
        for (which, alternative) in alts.iter_mut().enumerate() {
            let mut used = BTreeSet::new();
            for _ in 0..2 {
                if !self.rng.chance(1, 2) {
                    continue;
                }
                let origin = *self.rng.pick(&lenders);
                if !used.insert(origin) {
                    continue;
                }
                let Type::Ref(lender, referent) = &params[origin].1 else {
                    continue;
                };
                let mut found = Vec::new();
                self.lent_types(referent, true, *lender == BorrowMode::Exclusive, &mut found);
                found.retain(|(_, always, _)| *always || which >= forced);
                // A place that only some values have (a field of a variant,
                // an element, a key or a value of a map) is asked for in half
                // of the alternatives that may ask for one.
                if which >= forced
                    && found.iter().any(|(_, always, _)| !always)
                    && self.rng.chance(1, 2)
                {
                    found.retain(|(_, always, _)| !always);
                }
                if found.is_empty() {
                    continue;
                }
                let (wanted, _, exclusive) = self.rng.pick(&found).clone();
                let mode = if exclusive && self.rng.chance(1, 2) {
                    BorrowMode::Exclusive
                } else {
                    BorrowMode::Shared
                };
                let position = alternative.fields.len();
                alternative.fields.push(FieldSig {
                    name: format!("r{position}"),
                    ty: Type::Ref(mode, Box::new(wanted)),
                    lo: End::Open,
                    hi: End::Open,
                    origins: vec![origin],
                });
            }
        }
    }
}
