//! Faults and fault boundaries in the generator of valid programs: `fault`,
//! decisions and captures on operations that say `faults`, the lexical
//! boundary with its contingency, and the named boundary with `supervise`.
//!
//! A statement that may fault ([F1]) is written only where a fault is
//! permitted: the control says `faults`, or the statement stands in the work
//! of a boundary. Before it, the histories that run it give up what may not
//! be held there ([`Generator::expose`]): every obligation that is not
//! fault-releasable ([F2]), and what the end of the contingency asks of the
//! bodies around the boundary ([F5]), which is decided before the work is
//! written ([`Plan`]): `recover ↑ ℓ` ends the bodies up to `ℓ` and
//! `terminate n` all bodies of the control, so no obligation of those is
//! held where the work may fault ([O5]).
//!
//! The work of a lexical boundary is a body like that of a loop, without a
//! loop: it sees the names around it, it may consume them, and the histories
//! that fall off its end go on after the boundary. A contingency is written
//! as a body that nothing encloses: it sees what the boundary took into its
//! care and the message.

use super::data::{Ctx, Due, Kind};
use super::{
    BTreeSet, Binary, Command, Env, Expr, Generator, Know, MAX_BODIES, POS, Path, Range, Scope,
    Selector, Sig, SiteInfo, Slot, Type, Val, and_selector, bin, int, merge, name, parameter, stmt,
};
use crate::syntax::{BoundaryDecl, Statement};

const MESSAGES: [&str; 5] = ["stop", "bad input", "not yet", "", "limit"];

/// How the histories of a contingency end ([E-Contingency]).
#[derive(Clone, PartialEq)]
pub(super) enum Plan {
    /// No statement of the work may fault, and the contingency is `⊥`.
    Quiet,
    /// `escalate`, or a new `fault`.
    Escalate,
    /// `recover ↑ ℓ`: the body of `ℓ` as an index into the bodies being
    /// written, and the name of `ℓ`.
    Recover(usize, String),
    /// `terminate n`, in an entry control.
    Status,
    /// `terminate`, in the contingency of a named boundary; with the flag,
    /// `escalate` or a new `fault` as well.
    Stop(bool),
}

/// How the histories of the work of a lexical boundary may end.
#[derive(Clone, Copy, PartialEq)]
pub(super) enum Ends {
    /// With any terminator, or by falling off the end.
    Any,
    /// By a fault or by falling off the end: no terminator leaves the work.
    Inside,
    /// By a fault. The boundary then has obligations in its care ([O5]).
    Fault,
}

/// The work of a lexical boundary, as the body that is being written.
#[derive(Clone)]
pub(super) struct Work {
    pub(super) plan: Plan,
    pub(super) ends: Ends,
    /// Whether a statement that may fault was written in it.
    faulted: bool,
}

/// What the bodies being written are the bodies of.
#[derive(Clone, PartialEq)]
pub(super) enum Unit {
    /// A control: it ends with `■`.
    Control,
    /// The work of a named boundary: it ends with `terminate` ([F6]).
    Named,
    /// A contingency.
    Contingency(Plan),
}

/// Where a fault goes from a statement.
#[derive(Clone)]
pub(super) enum Route {
    /// Out of the control, or to the contingency of the named boundary
    /// whose work is being written.
    Out,
    /// To the contingency of the lexical boundary whose work is the body at
    /// the index.
    Work(usize, Plan),
}

/// A named boundary that a control may supervise.
#[derive(Clone)]
pub(super) struct BoundarySig {
    name: String,
    params: Vec<(String, Type)>,
    /// Whether a history of its contingency ends with `escalate` or with a
    /// new `fault`: `supervise` may fault then ([F6]).
    escapes: bool,
    uses: Vec<String>,
}

fn plain(env: Env) -> Scope {
    Scope {
        sites: Vec::new(),
        live: vec![Path {
            atoms: Vec::new(),
            env,
        }],
        statements: Vec::new(),
        looping: None,
        work: None,
        outer_atoms: Vec::new(),
    }
}

fn owned(ty: &Type, know: Know) -> Slot {
    Slot {
        ty: ty.clone(),
        mutable: false,
        know,
        definition: None,
        gone: false,
        home: 0,
    }
}

impl Generator<'_> {
    /// The operations that a statement here may name: in a contingency
    /// those declared `contingent` ([F5]), and one that says `faults` only
    /// where a fault is permitted ([F1]).
    pub(super) fn callees(&self) -> Vec<Sig> {
        let permitted = self.route().is_some();
        self.callables
            .iter()
            .filter(|sig| match self.unit {
                Unit::Contingency(_) => sig.contingent && !sig.faults,
                _ => !sig.faults || permitted,
            })
            .cloned()
            .collect()
    }

    /// Where a fault goes from a statement here, or `None` where none is
    /// permitted.
    pub(super) fn route(&self) -> Option<Route> {
        if matches!(self.unit, Unit::Contingency(_)) {
            return None;
        }
        for index in (0..self.scopes.len()).rev() {
            if let Some(work) = &self.scopes[index].work {
                return (work.plan != Plan::Quiet).then(|| Route::Work(index, work.plan.clone()));
            }
        }
        self.faults.then_some(Route::Out)
    }

    /// The outermost body that a terminator here may end.
    pub(super) fn reach(&self) -> usize {
        (0..self.scopes.len())
            .rev()
            .find(|&index| {
                self.scopes[index]
                    .work
                    .as_ref()
                    .is_some_and(|work| work.ends != Ends::Any)
            })
            .map_or(0, |index| index + 1)
    }

    /// Whether an obligation that the name holds may not be held where a
    /// statement may fault whose fault goes along `route`.
    pub(super) fn must_go(&self, route: &Route, name: &str, slot: &Slot) -> bool {
        // [F6]: a retained name stays whole.
        if self.retained.contains(name) {
            return false;
        }
        let stays = self.releasable(&slot.ty);
        match route {
            Route::Out | Route::Work(_, Plan::Escalate) => !stays,
            // `recover ↑ ℓ` ends the bodies from `ℓ` to the boundary.
            Route::Work(work, Plan::Recover(target, _)) => {
                !stays || (*target..*work).contains(&slot.home)
            }
            // `terminate n` ends every body around the boundary.
            Route::Work(work, Plan::Status) => !stays || slot.home < *work,
            Route::Work(..) => false,
        }
    }

    /// Whether the statement may consume the name: one that goes on, a name
    /// of the loop body it is in ([O6]); one that ends in a fault, any name
    /// of the bodies that the fault and the contingency end.
    fn may_take(&self, route: &Route, ends: bool, slot: &Slot) -> bool {
        if !ends {
            return slot.home >= self.floor();
        }
        match route {
            Route::Work(_, Plan::Recover(target, _)) => slot.home >= *target,
            _ => true,
        }
    }

    /// Makes the histories `running` of `selector` fit for a statement that
    /// may fault, whose expressions left the names as `ctx` has them: what
    /// they still hold and may not hold there is discharged before the
    /// statement. False, with nothing written, where a name cannot be
    /// consumed here. With `ends`, the statement ends its histories.
    pub(super) fn expose(
        &mut self,
        selector: &Selector,
        running: &[usize],
        ctx: &Ctx,
        ends: bool,
    ) -> bool {
        let Some(route) = self.route() else {
            return false;
        };
        for &index in running {
            for (name, slot) in &self.scope().live[index].env {
                if slot.gone || ctx.moved.contains(name) || self.types.kind(&slot.ty) != Kind::Must
                {
                    continue;
                }
                if self.must_go(&route, name, slot) && !self.may_take(&route, ends, slot) {
                    return false;
                }
            }
        }
        self.apply(running, ctx);
        self.discharge(selector, &Due::Fault(route.clone()));
        match route {
            Route::Out => self.faulted = true,
            Route::Work(index, plan) => {
                if let Some(work) = &mut self.scopes[index].work {
                    work.faulted = true;
                }
                if plan == Plan::Escalate {
                    self.faulted = true;
                }
            }
        }
        true
    }

    /// The message of a fault: a literal most often, or a string that the
    /// statement consumes.
    fn message(&mut self, ctx: &mut Ctx) -> Expr {
        if self.rng.chance(1, 4) {
            self.ending = true;
            let value = self.value(ctx, &Type::String, 1);
            self.ending = false;
            if let Some((expr, _)) = value {
                return expr;
            }
        }
        Expr::String((*self.rng.pick(&MESSAGES)).to_string())
    }

    /// `fault e` ([E-Fault]). False where it cannot be written.
    pub(super) fn fault(&mut self, selector: &Selector, running: &[usize]) -> bool {
        if self.route().is_none() {
            return false;
        }
        let mut ctx = self.ctx(running);
        let message = self.message(&mut ctx);
        if !self.expose(selector, running, &ctx, true) {
            return false;
        }
        self.push(
            selector,
            Command::Fault {
                message,
                assumed: false,
            },
        );
        let ended = self.running(selector);
        self.replace(&ended, Vec::new());
        true
    }

    /// The terminator that ends what is being written: `■` in a control,
    /// `terminate` in the work of a named boundary, and in a contingency
    /// what its plan says.
    pub(super) fn finish(&mut self, selector: &Selector, running: &[usize]) {
        match self.unit.clone() {
            Unit::Control => self.exit(selector, running),
            Unit::Named => {
                let ctx = self.ctx(running);
                self.end(selector, running, &ctx, 0, Command::Terminate(None));
            }
            Unit::Contingency(plan) => self.conclude(selector, running, &plan),
        }
    }

    /// The end of a history of a contingency ([E-Contingency]). `recover`
    /// and `terminate` end its scope as any terminator does ([O5]);
    /// `escalate` and a new `fault` leave what a fault releases ([F2]).
    fn conclude(&mut self, selector: &Selector, running: &[usize], plan: &Plan) {
        let mut ctx = self.ctx(running);
        let (command, due) = match plan {
            Plan::Recover(_, loop_name) => (
                Command::Recover {
                    loop_name: loop_name.clone(),
                },
                Due::From(0),
            ),
            Plan::Status => (
                Command::Terminate(Some(int(self.rng.range(0, 255)))),
                Due::From(0),
            ),
            Plan::Stop(escapes) if !escapes || self.rng.chance(1, 2) => {
                (Command::Terminate(None), Due::From(0))
            }
            _ => {
                self.escaped = true;
                let command = if self.rng.chance(1, 3) {
                    Command::Fault {
                        message: self.message(&mut ctx),
                        assumed: false,
                    }
                } else {
                    Command::Escalate
                };
                (command, Due::Escape)
            }
        };
        self.apply(running, &ctx);
        self.discharge(selector, &due);
        self.push(selector, command);
        let ended = self.running(selector);
        self.replace(&ended, Vec::new());
    }

    /// Writes a contingency whose histories end as `plan` says, with the
    /// names `env`. Nothing of the bodies around it is visible ([F5]).
    fn contingency(&mut self, plan: Plan, env: Env) -> Vec<Statement> {
        let scopes = std::mem::take(&mut self.scopes);
        let unit = std::mem::replace(&mut self.unit, Unit::Contingency(plan));
        let retained = std::mem::take(&mut self.retained);
        self.scopes.push(plain(env));
        let budget = self.rng.index(4);
        self.fill(budget);
        let body = self.scopes.pop().expect("the body of the contingency");
        self.scopes = scopes;
        self.unit = unit;
        self.retained = retained;
        body.statements
    }

    /// Whether a boundary may be written here: not in a contingency
    /// ([F5](a)), and in the work of no other.
    pub(super) fn boundary_fits(&self) -> bool {
        !matches!(self.unit, Unit::Contingency(_))
            && self.scopes.len() < MAX_BODIES
            && self.scopes.iter().all(|scope| scope.work.is_none())
    }

    /// Whether a contingency here may restart the loop whose body this is,
    /// and then the name of the loop and the expression that moves its
    /// counter. The loop goes round with the parameters as they are at the
    /// boundary: each is available there and within the invariant, and none
    /// holds what a fault does not release. The counter moves before the
    /// boundary, or a fault that comes again would come for ever.
    fn recovery(&self, env: &Env) -> Option<(String, Expr)> {
        let info = self.scope().looping.as_ref()?;
        let Some(Slot {
            know: Know::Int(counter),
            ty: Type::Int(counter_ty),
            mutable: true,
            gone: false,
            ..
        }) = env.get(&info.counter)
        else {
            return None;
        };
        let room = if info.up {
            info.bound - counter.flow.hi
        } else {
            counter.flow.lo
        };
        if room < 1 || !counter.flow.bounded() {
            return None;
        }
        let operator = if info.up {
            Binary::Add
        } else {
            Binary::Subtract
        };
        let moved = bin(operator, name(&info.counter), int(1));
        let after = self.lib().int(&moved, env, Some(*counter_ty))?;
        for parameter in &info.params {
            let slot = env.get(&parameter.name)?;
            if slot.gone || self.types.kind(&slot.ty) == Kind::Must && !self.releasable(&slot.ty) {
                return None;
            }
            let Some(invariant) = parameter.invariant else {
                continue;
            };
            let flow = if parameter.name == info.counter {
                after.flow
            } else {
                match &slot.know {
                    Know::Int(val) => val.flow,
                    _ => continue,
                }
            };
            if flow.lo < invariant.lo || flow.hi > invariant.hi {
                return None;
            }
        }
        Some((info.name.clone(), moved))
    }

    /// `d : boundary {B₁} contingency [x̄] (m : string) {B₂}` ([E-Boundary]).
    pub(super) fn make_boundary(&mut self, selector: &Selector) -> bool {
        // A contingency can restart the loop on the histories on which its
        // counter has room, and the first test of the body says which those
        // are: most often the boundary stands under that test.
        let mut narrowed = selector.clone();
        if self.scope().looping.is_some() && self.rng.chance(2, 3) {
            let env = self.running_env(&self.running(selector));
            let first = self.scope().sites.first();
            let atoms: Vec<Selector> = first.map_or_else(Vec::new, |site| {
                site.alternatives
                    .iter()
                    .map(|alternative| Selector::Atom(site.name.clone(), alternative.clone()))
                    .collect()
            });
            if self.recovery(&env).is_none() {
                for atom in atoms {
                    let under = and_selector(selector, atom);
                    let picked = self.running(&under);
                    if !picked.is_empty() && self.recovery(&self.running_env(&picked)).is_some() {
                        narrowed = under;
                        break;
                    }
                }
            }
        }
        let selector = &narrowed;
        // As before a loop: every obligation is held by all the histories
        // or by none of them, so that the work can end it or leave it.
        self.level(selector);
        let running = self.running(selector);
        if running.is_empty() {
            return false;
        }
        let here = self.scopes.len() - 1;
        let env = self.running_env(&running);

        let recovery = self.recovery(&env);
        let mut plans = vec![Plan::Quiet];
        if self.faults {
            plans.extend([Plan::Escalate, Plan::Escalate]);
        }
        if self.entry {
            plans.extend([Plan::Status, Plan::Status]);
        }
        if let Some((loop_name, _)) = &recovery {
            let plan = Plan::Recover(here, loop_name.clone());
            plans.extend(vec![plan; 6]);
        }
        let plan = self.rng.pick(&plans).clone();
        let route = Route::Work(here + 1, plan.clone());
        let parameters: BTreeSet<String> = match (&plan, &self.scope().looping) {
            (Plan::Recover(..), Some(info)) => {
                info.params.iter().map(|info| info.name.clone()).collect()
            }
            _ => BTreeSet::new(),
        };
        let held = parameters
            .iter()
            .any(|name| self.types.kind(&env[name].ty) == Kind::Must);

        // What the boundary takes into its care. An obligation is ended
        // with the work unless the work ends in a fault ([E-Boundary]), so
        // one goes into the care of a boundary whose work always faults.
        let mut doomed = plan != Plan::Quiet && self.rng.chance(1, 4);
        let mut care: Vec<String> = Vec::new();
        for (name, slot) in &env {
            // Each name of the list owns its value ([F5]).
            if care.len() == 3
                || parameters.contains(name)
                || matches!(slot.ty, Type::Ref(_, _))
                || !self.consumable(name, slot)
            {
                continue;
            }
            let taken = match self.types.kind(&slot.ty) {
                Kind::Copy => self.rng.chance(1, 6),
                Kind::Drop => self.rng.chance(1, 3),
                Kind::Must => doomed && self.rng.chance(1, 2),
            };
            if taken {
                care.push(name.clone());
            }
        }
        // A work that always faults can fault at once.
        let open = running.iter().all(|&index| {
            self.scope().live[index].env.iter().all(|(name, slot)| {
                slot.gone
                    || care.contains(name)
                    || self.types.kind(&slot.ty) != Kind::Must
                    || !self.must_go(&route, name, slot)
                    || self.may_take(&route, true, slot)
            })
        });
        if doomed && !open {
            doomed = false;
            care.retain(|name| self.types.kind(&env[name].ty) != Kind::Must);
        }
        let ends = if doomed {
            Ends::Fault
        } else if held || self.rng.chance(1, 4) {
            // The work mentions no parameter of the loop that the
            // contingency restarts ([F5](c)), so where one holds an
            // obligation no terminator of the work can end the loop.
            Ends::Inside
        } else {
            Ends::Any
        };

        let mut ctx = self.ctx(&running);
        let mut cared = Env::new();
        for name in &care {
            let slot = &env[name];
            let know = match &slot.know {
                Know::Outcome(_) => Know::Opaque,
                know => know.clone(),
            };
            cared.insert(name.clone(), owned(&slot.ty, know));
            if self.types.kind(&slot.ty) != Kind::Copy {
                ctx.moved.push(name.clone());
            }
        }
        self.apply(&running, &ctx);
        if let (Plan::Recover(..), Some((_, moved))) = (&plan, &recovery) {
            let counter = self
                .scope()
                .looping
                .as_ref()
                .map(|info| info.counter.clone());
            let counter = counter.expect("the loop that the contingency restarts");
            self.push(
                selector,
                Command::Assign {
                    name: counter.clone(),
                    value: moved.clone(),
                },
            );
            for &index in &running {
                let env = &self.scopes[here].live[index].env;
                let Some(Type::Int(counter_ty)) = env.get(&counter).map(|slot| slot.ty.clone())
                else {
                    continue;
                };
                let Some(val) = self.lib().int(moved, env, Some(counter_ty)) else {
                    continue;
                };
                if let Some(slot) = self.scopes[here].live[index].env.get_mut(&counter) {
                    slot.know = Know::Int(Val::value(counter_ty, val.flow));
                    slot.definition = None;
                }
            }
        }

        // The work sees the names around it.
        let start = self.running_env(&running);
        let mut inner = start.clone();
        for parameter in &parameters {
            inner.remove(parameter);
        }
        if !parameters.is_empty() {
            for slot in inner.values_mut() {
                slot.definition = None;
            }
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
        let mut work = plain(inner);
        work.work = Some(Work {
            plan: plan.clone(),
            ends,
            faulted: false,
        });
        work.outer_atoms = outer_atoms;
        self.scopes.push(work);
        let budget = 1 + self.rng.index(5);
        self.fill(budget);
        let body = self.scopes.pop().expect("the work of the boundary");
        let faulted = body.work.as_ref().is_some_and(|work| work.faulted);

        // The histories that fell off the end go on after the boundary. A
        // name that the work may have assigned is what it is there; one that
        // it consumed is gone.
        let site = self.fresh("b");
        let site_index = self.scope().sites.len();
        let mut children = Vec::new();
        if !body.live.is_empty() {
            let fell = merge(&body.live.iter().collect::<Vec<&Path>>());
            for &index in &running {
                let mut path = self.scope().live[index].clone();
                for (name, slot) in path.env.iter_mut() {
                    let (Some(before), Some(after)) = (start.get(name), fell.get(name)) else {
                        continue;
                    };
                    if slot.mutable {
                        slot.know = after.know.clone();
                        slot.definition = None;
                    }
                    if after.gone != before.gone {
                        slot.gone = after.gone;
                    }
                }
                path.atoms.push((site_index, 0));
                children.push(path);
            }
        }
        self.scope_mut().sites.push(SiteInfo {
            name: site.clone(),
            alternatives: vec!["done".to_string()],
        });

        let message = self.rng.chance(4, 5).then(|| self.fresh("m"));
        let contingency = if faulted || plan != Plan::Quiet && self.rng.chance(1, 3) {
            if let Some(message) = &message {
                cared.insert(
                    message.clone(),
                    owned(&Type::String, Know::Sized(Range::new(0, POS))),
                );
            }
            self.contingency(plan, cared)
        } else {
            vec![stmt(Selector::Top, Command::Impossible)]
        };
        self.push(
            selector,
            Command::Boundary {
                site: site.clone(),
                body: body.statements,
                captures: care,
                message,
                contingency,
            },
        );
        let reached = !children.is_empty();
        self.replace(&running, children);
        if !reached && self.rng.chance(3, 5) {
            let arm = and_selector(selector, Selector::Atom(site, "done".to_string()));
            self.push(&arm, Command::Impossible);
        }
        true
    }

    /// The end of the work of a lexical boundary: its histories end as
    /// `ends` says, and those that are left fall off the end, which ends
    /// the scope of the work ([O5]).
    pub(super) fn close_work(&mut self, ends: Ends) {
        let mut rounds = 0;
        while !self.scope().live.is_empty() {
            rounds += 1;
            if ends == Ends::Fault {
                let all = self.running(&Selector::Top);
                let written = self.fault(&Selector::Top, &all);
                assert!(written, "the work of the boundary can fault");
                continue;
            }
            if rounds > 4 || self.rng.chance(1, 3) {
                break;
            }
            let (selector, running) = self.pick_selector();
            if running.is_empty() {
                continue;
            }
            if ends == Ends::Inside {
                self.fault(&selector, &running);
            } else {
                self.terminate(&selector, &running);
            }
        }
        if !self.scope().live.is_empty() {
            let here = self.scopes.len() - 1;
            self.settle(&Selector::Top, here);
            // After the boundary a name of the bodies around is held on
            // every history that fell off or on none.
            self.level(&Selector::Top);
        }
    }

    /// `supervise b(ō)` ([E-Supervise]).
    pub(super) fn supervise(&mut self, selector: &Selector, running: &[usize]) -> bool {
        if matches!(self.unit, Unit::Contingency(_)) || self.boundaries.is_empty() {
            return false;
        }
        let callee = self.rng.pick(&self.boundaries).clone();
        if callee.escapes && self.route().is_none() {
            return false;
        }
        let mut ctx = self.ctx(running);
        self.ending = callee.escapes;
        let mut arguments = Vec::new();
        for (_, ty) in &callee.params {
            let seen = ctx.env.clone();
            let argument = match ty {
                Type::Int(int_ty) => Some(self.gen_int(&seen, *int_ty, 2).0),
                Type::Bool => Some(self.gen_bool(&seen, 1).0),
                other => self.value(&mut ctx, other, 2).map(|(expr, _)| expr),
            };
            let Some(argument) = argument else {
                self.ending = false;
                return false;
            };
            arguments.push(argument);
        }
        self.ending = false;
        if callee.escapes {
            if !self.expose(selector, running, &ctx, false) {
                return false;
            }
        } else {
            self.apply(running, &ctx);
        }
        self.effects.extend(callee.uses.iter().cloned());
        self.push(
            selector,
            Command::Supervise {
                boundary: callee.name.clone(),
                arguments,
            },
        );
        true
    }

    /// `boundary b(x̄ : τ̄) retains ȳ {B₁} contingency (m : string) {B₂}`
    /// ([F6]).
    pub(super) fn boundary(&mut self, index: usize) -> BoundaryDecl {
        self.fresh = 0;
        self.loops = 0;
        self.effects.clear();
        let count = self.rng.index(4);
        let params: Vec<(String, Type)> = (0..count)
            .map(|position| (format!("p{position}"), self.payload_type()))
            .collect();
        let mut retains = Vec::new();
        for (parameter, _) in &params {
            if self.rng.chance(1, 2) {
                retains.push(parameter.clone());
            }
        }
        self.unit = Unit::Named;
        self.faults = true;
        self.entry = false;
        self.faulted = false;
        self.retained = retains.iter().cloned().collect();
        let mut env = Env::new();
        for (parameter, ty) in &params {
            env.insert(parameter.clone(), owned(ty, self.types.top(ty)));
        }
        self.scopes.push(plain(env.clone()));
        let budget = 2 + self.rng.index(7);
        self.fill(budget);
        let body = self.scopes.pop().expect("the work of the named boundary");

        let message = self.fresh("m");
        self.escaped = false;
        let contingency = if self.faulted || self.rng.chance(1, 3) {
            let mut seen = Env::new();
            for parameter in &retains {
                seen.insert(parameter.clone(), env[parameter].clone());
            }
            seen.insert(
                message.clone(),
                owned(&Type::String, Know::Sized(Range::new(0, POS))),
            );
            let escapes = self.rng.chance(1, 3);
            self.contingency(Plan::Stop(escapes), seen)
        } else {
            vec![stmt(Selector::Top, Command::Impossible)]
        };
        self.unit = Unit::Control;
        self.faults = false;
        self.retained.clear();
        let name = format!("w{index}");
        self.boundaries.push(BoundarySig {
            name: name.clone(),
            params: params.clone(),
            escapes: self.escaped,
            uses: self.effects.iter().cloned().collect(),
        });
        BoundaryDecl {
            name,
            parameters: params.iter().map(|(n, ty)| parameter(n, ty)).collect(),
            retains,
            body: body.statements,
            message,
            contingency,
            line: 1,
        }
    }
}
