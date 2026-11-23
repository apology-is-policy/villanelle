//! The data of slice 2 in the generator of valid programs: structs,
//! variants, vectors, maps and strings, and the built-in operations on them.
//!
//! Beside what [`super`] keeps for an integer, the generator keeps for every
//! name on every history whether its value has moved ([O3]) and what the
//! fact logic knows of it: a struct field by field ([A4]), a variant by its
//! constructors ([A5]), a collection by the interval of its length ([A3] and
//! the conditions of the built-in operations). It writes a statement only
//! where its rules hold on those: a name is read where it is available
//! ([O2]) and consumed where it may move ([O3], [O6]), an index is less
//! than the length ([P5]), a collection that an operation changes is a
//! mutable place ([C1]).
//!
//! One statement evaluates its operands in an order ([E-Operands], [O0]),
//! and [`Ctx`] is the state of the names while one is written: a name that
//! an operand has consumed is gone for the operands after it, and a name
//! that an operand lends is not consumed by another.
//!
//! A value of kind `must` is an obligation ([T1]): a resource, a struct or
//! a variant that holds one, a captured outcome. It comes from the payload
//! of a decision, from a parameter or from a capture, and a history ends
//! only where none is left ([O5]). So before every terminator the generator
//! discharges what the histories of its selector still hold in the scopes
//! that the terminator ends ([`Generator::settle`]): a resource by the
//! contingent operation that closes it, a struct by taking it apart, a
//! variant or a captured outcome by a decision on it. Where only some of
//! the histories hold a name, the statement stands under a selector that
//! picks those.

use super::faults::Route;
use super::{
    AltSig, Arm, BTreeSet, BorrowMode, CallMode, Command, Control, Declaration, Env, Expr,
    Generator, IntType, Know, POS, ParamInfo, Path, Range, Selector, Sig, SiteInfo, Slot, Tri,
    Type, Val, add, and_selector, bin, int, name, subtract,
};
use crate::syntax::{
    Binary, Parameter, Place, PlaceStep, ResourceDecl, StructDecl, VariantConstructor, VariantDecl,
};

const STRINGS: [&str; 6] = ["", "a", "b", "ok", "hello", "key"];

/// The usage kinds of [T1], least first.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum Kind {
    Copy,
    Drop,
    Must,
}

#[derive(Clone, Debug)]
pub(super) struct StructInfo {
    pub(super) name: String,
    pub(super) copy: bool,
    pub(super) fields: Vec<(String, Type)>,
}

#[derive(Clone, Debug)]
pub(super) struct VariantInfo {
    pub(super) name: String,
    pub(super) copy: bool,
    pub(super) constructors: Vec<(String, Vec<(String, Type)>)>,
}

#[derive(Clone, Debug)]
pub(super) struct ResourceInfo {
    pub(super) name: String,
    /// The contingent operation that takes a value of the resource and
    /// ends it.
    pub(super) closer: String,
    /// Whether it is declared `on fault release` ([T3]).
    pub(super) releasable: bool,
}

/// The types that the program declares.
#[derive(Clone, Debug, Default)]
pub(super) struct Types {
    pub(super) resources: Vec<ResourceInfo>,
    pub(super) structs: Vec<StructInfo>,
    pub(super) variants: Vec<VariantInfo>,
}

impl Types {
    pub(super) fn resource(&self, name: &str) -> Option<&ResourceInfo> {
        self.resources.iter().find(|info| info.name == name)
    }

    pub(super) fn structure(&self, name: &str) -> Option<&StructInfo> {
        self.structs.iter().find(|info| info.name == name)
    }

    pub(super) fn variant(&self, name: &str) -> Option<&VariantInfo> {
        self.variants.iter().find(|info| info.name == name)
    }

    /// The usage kind of a type ([T1]).
    pub(super) fn kind(&self, ty: &Type) -> Kind {
        match ty {
            Type::Bool | Type::Int(_) | Type::Ref(BorrowMode::Shared, _) => Kind::Copy,
            Type::String | Type::Ref(BorrowMode::Exclusive, _) => Kind::Drop,
            Type::Vector(item) => Kind::Drop.max(self.kind(item)),
            Type::Map(key, value) => Kind::Drop.max(self.kind(key)).max(self.kind(value)),
            Type::Named(name) => {
                let (copy, fields): (bool, Vec<&Type>) = if let Some(info) = self.structure(name) {
                    (info.copy, info.fields.iter().map(|(_, ty)| ty).collect())
                } else if let Some(info) = self.variant(name) {
                    let fields = info
                        .constructors
                        .iter()
                        .flat_map(|(_, fields)| fields.iter().map(|(_, ty)| ty))
                        .collect();
                    (info.copy, fields)
                } else {
                    return Kind::Must;
                };
                let inner = fields
                    .into_iter()
                    .map(|ty| self.kind(ty))
                    .max()
                    .unwrap_or(Kind::Copy);
                if copy { inner } else { inner.max(Kind::Drop) }
            }
            _ => Kind::Must,
        }
    }

    /// What the type alone says of a value.
    pub(super) fn top(&self, ty: &Type) -> Know {
        match ty {
            Type::Int(int_ty) => Know::Int(Val::value(*int_ty, Range::ALL)),
            Type::Bool => Know::Bool(Tri::Unknown),
            Type::String | Type::Vector(_) | Type::Map(_, _) => Know::Sized(Range::new(0, POS)),
            Type::Ref(_, inner) => self.top(inner),
            Type::Named(name) => {
                if let Some(info) = self.structure(name) {
                    Know::Struct(info.fields.iter().map(|(_, ty)| self.top(ty)).collect())
                } else if let Some(info) = self.variant(name) {
                    Know::Variant(
                        info.constructors
                            .iter()
                            .map(|(_, fields)| {
                                Some(fields.iter().map(|(_, ty)| self.top(ty)).collect())
                            })
                            .collect(),
                    )
                } else {
                    Know::Opaque
                }
            }
            _ => Know::Opaque,
        }
    }
}

/// What is known at the fields `steps` of the name `root`.
pub(super) fn know_at<'e>(env: &'e mut Env, root: &str, steps: &[usize]) -> Option<&'e mut Know> {
    let mut know = &mut env.get_mut(root)?.know;
    for &step in steps {
        let Know::Struct(fields) = know else {
            return None;
        };
        know = fields.get_mut(step)?;
    }
    Some(know)
}

/// What is known of a value once a name or a field holds it: an integer is
/// then a value term of its type ([A1]), and no constant expression ([I3]).
fn held(ty: &Type, know: Know) -> Know {
    match (ty, know) {
        (Type::Int(int_ty), Know::Int(val)) => Know::Int(Val::value(*int_ty, val.flow)),
        (_, know) => know,
    }
}

/// The names while one statement is written.
#[derive(Clone)]
pub(super) struct Ctx {
    pub(super) env: Env,
    /// The names that an operand lends, and those that one lends
    /// exclusively.
    lent: BTreeSet<String>,
    exclusive: BTreeSet<String>,
    /// The names that the statement consumes.
    pub(super) moved: Vec<String>,
    /// The names that an operation may have changed, of which only the type
    /// is known afterwards ([I9]).
    changed: Vec<String>,
}

/// A place: a name or a field of it.
#[derive(Clone, Debug)]
struct Spot {
    expr: Expr,
    root: String,
    /// The fields from the root, by position and by name.
    steps: Vec<usize>,
    fields: Vec<String>,
    ty: Type,
    /// Whether the root was bound with `~` ([C1]).
    mutable: bool,
}

impl Spot {
    fn length(&self, env: &Env) -> Range {
        let mut know = match env.get(&self.root) {
            Some(slot) => &slot.know,
            None => return Range::new(0, POS),
        };
        for &step in &self.steps {
            match know {
                Know::Struct(fields) => know = &fields[step],
                _ => return Range::new(0, POS),
            }
        }
        match know {
            Know::Sized(length) => *length,
            _ => Range::new(0, POS),
        }
    }

    fn set(&self, env: &mut Env, know: Know) {
        if let Some(seen) = know_at(env, &self.root, &self.steps) {
            *seen = know;
        }
    }

    fn place(&self, last: Option<Expr>) -> Place {
        let mut steps: Vec<PlaceStep> = self.fields.iter().cloned().map(PlaceStep::Field).collect();
        steps.extend(last.map(PlaceStep::Index));
        Place {
            root: self.root.clone(),
            steps,
        }
    }
}

struct Walk<'a> {
    types: &'a Types,
    wanted: &'a dyn Fn(&Type) -> bool,
    out: Vec<Spot>,
}

impl Walk<'_> {
    fn walk(&mut self, spot: Spot, depth: u8) {
        if depth > 0
            && let Type::Named(name) = &spot.ty
            && let Some(info) = self.types.structure(name)
        {
            for (index, (field, ty)) in info.fields.iter().enumerate() {
                let mut inner = spot.clone();
                inner.expr = Expr::Field(Box::new(spot.expr.clone()), field.clone());
                inner.steps.push(index);
                inner.fields.push(field.clone());
                inner.ty = ty.clone();
                self.walk(inner, depth - 1);
            }
        }
        if (self.wanted)(&spot.ty) && self.types.kind(&spot.ty) != Kind::Must {
            self.out.push(spot);
        }
    }
}

fn parameter(name: &str, ty: &Type) -> Parameter {
    Parameter {
        name: name.to_string(),
        ty: ty.clone(),
        origins: Vec::new(),
    }
}

/// Which obligations a statement asks to be discharged before it.
#[derive(Clone)]
pub(super) enum Due {
    /// Those of the bodies from the index inward ([O5]).
    From(usize),
    /// Those that some of the histories hold and others do not.
    Uneven,
    /// Those that may not be held where a fault can occur ([F2], and what
    /// the end of the contingency asks of the bodies around the boundary).
    Fault(Route),
    /// In a contingency, before `escalate` or a new `fault`: those that are
    /// not fault-releasable.
    Escape,
}

fn arm(alternative: &str, names: &[&String]) -> Arm {
    Arm {
        alternative: alternative.to_string(),
        names: names.iter().map(|name| (*name).clone()).collect(),
    }
}

impl Generator<'_> {
    pub(super) fn ctx(&self, running: &[usize]) -> Ctx {
        Ctx {
            env: self.running_env(running),
            lent: BTreeSet::new(),
            exclusive: BTreeSet::new(),
            moved: Vec::new(),
            changed: Vec::new(),
        }
    }

    /// What the statement did to the names, on the histories that ran it.
    pub(super) fn apply(&mut self, running: &[usize], ctx: &Ctx) {
        if ctx.moved.is_empty() && ctx.changed.is_empty() {
            return;
        }
        let tops: Vec<(&String, Know)> = ctx
            .changed
            .iter()
            .filter_map(|name| Some((name, self.types.top(&ctx.env.get(name)?.ty))))
            .collect();
        let last = self.scopes.len() - 1;
        for &index in running {
            let env = &mut self.scopes[last].live[index].env;
            for moved in &ctx.moved {
                if let Some(slot) = env.get_mut(moved) {
                    slot.gone = true;
                }
            }
            for (name, top) in &tops {
                if let Some(slot) = env.get_mut(*name) {
                    slot.know = top.clone();
                    slot.definition = None;
                }
            }
        }
    }

    fn here(&self) -> usize {
        self.scopes.len() - 1
    }

    /// The innermost body that is a loop. A name of a body around it is, at
    /// every `↑`, as available as it was when the loop began ([O6]), so the
    /// body moves no such name.
    pub(super) fn floor(&self) -> usize {
        (0..self.scopes.len())
            .rev()
            .find(|&index| self.scopes[index].looping.is_some())
            .unwrap_or(0)
    }

    /// Whether the value of the name may be consumed here. A name that a
    /// named boundary retains stays whole while a statement of its work may
    /// still fault ([F6]).
    pub(super) fn consumable(&self, name: &str, slot: &Slot) -> bool {
        !slot.gone
            && (self.types.kind(&slot.ty) == Kind::Copy
                || slot.home >= self.floor() && !self.retained.contains(name))
    }

    /// Whether the type is fault-releasable ([T3]).
    pub(super) fn releasable(&self, ty: &Type) -> bool {
        match ty {
            Type::Vector(item) => self.releasable(item),
            Type::Map(key, value) => self.releasable(key) && self.releasable(value),
            Type::Named(named) => {
                if let Some(info) = self.types.resource(named) {
                    info.releasable
                } else if let Some(info) = self.types.structure(named) {
                    info.fields.iter().all(|(_, ty)| self.releasable(ty))
                } else if let Some(info) = self.types.variant(named) {
                    info.constructors
                        .iter()
                        .flat_map(|(_, fields)| fields)
                        .all(|(_, ty)| self.releasable(ty))
                } else {
                    false
                }
            }
            Type::OutcomeNamed(captured) => self
                .callables
                .iter()
                .find(|sig| &sig.name == captured)
                .is_some_and(|sig| {
                    sig.alts
                        .iter()
                        .flat_map(|alternative| &alternative.fields)
                        .all(|field| self.releasable(&field.ty))
                }),
            _ => true,
        }
    }

    fn bind_name(&mut self, running: &[usize], bound: &str, slot: &Slot) {
        let last = self.here();
        for &index in running {
            self.scopes[last].live[index]
                .env
                .insert(bound.to_string(), slot.clone());
        }
    }

    fn slot(&self, ty: &Type, mutable: bool, know: Know) -> Slot {
        Slot {
            ty: ty.clone(),
            mutable,
            know,
            definition: None,
            gone: false,
            home: self.here(),
        }
    }

    // Types.

    /// A type for a name, a parameter or a field: one of slice 1, or data.
    pub(super) fn value_type(&mut self) -> Type {
        if self.data && self.rng.chance(1, 3) {
            self.data_type()
        } else {
            self.random_type()
        }
    }

    fn struct_type(&mut self) -> Option<Type> {
        if self.types.structs.is_empty() {
            return None;
        }
        let index = self.rng.index(self.types.structs.len());
        Some(Type::Named(self.types.structs[index].name.clone()))
    }

    fn resource_type(&mut self) -> Option<Type> {
        if self.types.resources.is_empty() {
            return None;
        }
        let index = self.rng.index(self.types.resources.len());
        Some(Type::Named(self.types.resources[index].name.clone()))
    }

    /// A type for a parameter or for a payload field: a resource now and
    /// then, which is how one comes to a body and leaves it.
    pub(super) fn payload_type(&mut self) -> Type {
        if self.data && !self.types.resources.is_empty() && self.rng.chance(1, 8) {
            self.resource_type().expect("a resource")
        } else {
            self.value_type()
        }
    }

    /// Now and then, the type of an obligation that the statement could
    /// give away: a loop takes it as a parameter.
    pub(super) fn held_type(&mut self, ctx: &Ctx) -> Option<Type> {
        if !self.data || !self.rng.chance(1, 4) {
            return None;
        }
        let held: Vec<Type> = ctx
            .env
            .iter()
            .filter(|(name, slot)| {
                self.types.kind(&slot.ty) == Kind::Must
                    && self.consumable(name, slot)
                    && !ctx.lent.contains(*name)
            })
            .map(|(_, slot)| slot.ty.clone())
            .collect();
        if held.is_empty() {
            None
        } else {
            Some(self.rng.pick(&held).clone())
        }
    }

    /// Now and then, the type of a parameter of the loop that holds an
    /// obligation: an iteration leaves with it.
    pub(super) fn parameter_type(&mut self, params: &[ParamInfo]) -> Option<Type> {
        if !self.data || !self.rng.chance(1, 3) {
            return None;
        }
        let held: Vec<Type> = params
            .iter()
            .filter(|info| self.types.kind(&info.ty) == Kind::Must)
            .map(|info| info.ty.clone())
            .collect();
        if held.is_empty() {
            None
        } else {
            Some(self.rng.pick(&held).clone())
        }
    }

    fn variant_type(&mut self) -> Option<Type> {
        if self.types.variants.is_empty() {
            return None;
        }
        let index = self.rng.index(self.types.variants.len());
        Some(Type::Named(self.types.variants[index].name.clone()))
    }

    /// The type of an element or of a field: a scalar most often, and
    /// none that holds an obligation.
    fn element_type(&mut self) -> Type {
        match self.rng.below(6) {
            0 => Type::String,
            1 => self
                .struct_type()
                .filter(|ty| self.types.kind(ty) != Kind::Must)
                .unwrap_or(Type::String),
            _ => self.random_type(),
        }
    }

    fn data_type(&mut self) -> Type {
        match self.rng.below(11) {
            10 => self.resource_type().unwrap_or(Type::String),
            0 | 1 => Type::String,
            2..=4 => self.struct_type().unwrap_or(Type::String),
            5 | 6 => self.variant_type().unwrap_or(Type::String),
            7 => {
                let key = if self.rng.chance(1, 2) {
                    Type::String
                } else {
                    Type::Int(*self.rng.pick(&self.palette))
                };
                Type::Map(Box::new(key), Box::new(self.element_type()))
            }
            _ => Type::Vector(Box::new(self.element_type())),
        }
    }

    /// The resources, the structs and the variants of the program, and for
    /// each resource the operation that closes it.
    pub(super) fn declare_types(&mut self) -> Vec<Declaration> {
        let mut out = Vec::new();
        for index in 0..self.rng.index(3) {
            let name = format!("rs{index}");
            let releasable = self.rng.chance(1, 2);
            out.push(Declaration::Resource(ResourceDecl {
                name: name.clone(),
                on_fault_release: releasable,
                line: 1,
            }));
            let sig = Sig {
                name: format!("k{index}"),
                params: vec![("p0".to_string(), Type::Named(name.clone()))],
                pre: vec![Range::ALL],
                order: None,
                alts: vec![AltSig {
                    name: "done".to_string(),
                    fields: Vec::new(),
                    params: vec![None],
                }],
                uses: Vec::new(),
                faults: false,
                contingent: true,
            };
            let (parameters, precondition, contract) = self.signature(&sig);
            out.push(Declaration::Control(Control {
                name: sig.name.clone(),
                public: false,
                external: true,
                is_async: false,
                contingent: true,
                faults: false,
                parameters,
                precondition,
                contract,
                uses: Vec::new(),
                body: Vec::new(),
                line: 1,
            }));
            self.types.resources.push(ResourceInfo {
                name,
                closer: sig.name.clone(),
                releasable,
            });
            self.callables.push(sig);
        }
        for index in 0..1 + self.rng.index(3) {
            let mut fields = Vec::new();
            for position in 0..1 + self.rng.index(3) {
                let ty = match self.rng.below(9) {
                    0 => Type::String,
                    1 => self.struct_type().unwrap_or(Type::Bool),
                    2 => Type::Vector(Box::new(self.random_type())),
                    8 => self.resource_type().unwrap_or(Type::Bool),
                    _ => self.random_type(),
                };
                fields.push((format!("m{position}"), ty));
            }
            let all_copy = fields
                .iter()
                .all(|(_, ty)| self.types.kind(ty) == Kind::Copy);
            let copy = all_copy && self.rng.chance(1, 2);
            let name = format!("st{index}");
            out.push(Declaration::Struct(StructDecl {
                name: name.clone(),
                public: false,
                is_copy: copy,
                is_view: false,
                fields: fields.iter().map(|(n, ty)| parameter(n, ty)).collect(),
                line: 1,
            }));
            self.types.structs.push(StructInfo { name, copy, fields });
        }
        for index in 0..self.rng.index(3) {
            let count = 2 + self.rng.index(2);
            let mut constructors = Vec::new();
            for constructor in self.alternative_names(count) {
                let mut fields = Vec::new();
                for position in 0..self.rng.index(3) {
                    let ty = if self.rng.chance(1, 9) {
                        self.resource_type()
                    } else {
                        None
                    };
                    let ty = match ty {
                        Some(resource) => resource,
                        None => self.element_type(),
                    };
                    fields.push((format!("m{position}"), ty));
                }
                constructors.push((constructor, fields));
            }
            let all_copy = constructors
                .iter()
                .flat_map(|(_, fields)| fields)
                .all(|(_, ty)| self.types.kind(ty) == Kind::Copy);
            let copy = all_copy && self.rng.chance(1, 2);
            let name = format!("vt{index}");
            out.push(Declaration::Variant(VariantDecl {
                name: name.clone(),
                public: false,
                is_copy: copy,
                constructors: constructors
                    .iter()
                    .map(|(constructor, fields)| VariantConstructor {
                        name: constructor.clone(),
                        fields: fields.iter().map(|(n, ty)| parameter(n, ty)).collect(),
                    })
                    .collect(),
                line: 1,
            }));
            self.types.variants.push(VariantInfo {
                name,
                copy,
                constructors,
            });
        }
        out
    }

    /// An extern control borrows some of its data: `&τ` to read it, and
    /// `&~τ` now and then.
    pub(super) fn lend_parameters(&mut self, params: &mut [(String, Type)]) {
        for (_, ty) in params.iter_mut() {
            if ty.is_scalar() {
                continue;
            }
            match self.rng.below(8) {
                0..=3 => *ty = Type::Ref(BorrowMode::Shared, Box::new(ty.clone())),
                4 => *ty = Type::Ref(BorrowMode::Exclusive, Box::new(ty.clone())),
                _ => {}
            }
        }
    }

    // Places and values.

    /// The places of `env` whose type `wanted` accepts and that hold no
    /// obligation: an available name, or a field of one, two fields deep at
    /// most.
    fn places(&self, env: &Env, wanted: &dyn Fn(&Type) -> bool) -> Vec<Spot> {
        let mut walk = Walk {
            types: &self.types,
            wanted,
            out: Vec::new(),
        };
        for (root, slot) in env {
            if slot.gone || self.ending && self.types.kind(&slot.ty) == Kind::Must {
                continue;
            }
            walk.walk(
                Spot {
                    expr: name(root),
                    root: root.clone(),
                    steps: Vec::new(),
                    fields: Vec::new(),
                    ty: slot.ty.clone(),
                    mutable: slot.mutable,
                },
                2,
            );
        }
        walk.out
    }

    /// An integer of `ty` that is read out of data: a field, an element at
    /// an index that is known to be in range, a length.
    pub(super) fn int_place(&mut self, env: &Env, ty: IntType) -> Option<Expr> {
        let wanted = Type::Int(ty);
        let mut found: Vec<Expr> = Vec::new();
        for spot in self.places(env, &|_| true) {
            match &spot.ty {
                seen if *seen == wanted && !spot.steps.is_empty() => found.push(spot.expr.clone()),
                Type::Vector(item) => {
                    if ty == IntType::Usize {
                        found.push(Expr::Len(Box::new(spot.expr.clone())));
                    }
                    let length = spot.length(env);
                    if **item == wanted && length.lo >= 1 {
                        let last = (length.lo - 1).min(3);
                        for index in [0, last] {
                            found.push(Expr::Index(
                                Box::new(spot.expr.clone()),
                                Box::new(int(index)),
                            ));
                        }
                    }
                }
                Type::String | Type::Map(_, _) if ty == IntType::Usize => {
                    found.push(Expr::Len(Box::new(spot.expr.clone())));
                }
                _ => {}
            }
        }
        if found.is_empty() {
            None
        } else {
            Some(self.rng.pick(&found).clone())
        }
    }

    /// Consumes the name `chosen`: it moves unless its type is `copy`.
    fn take_name(&mut self, ctx: &mut Ctx, chosen: &str) -> (Expr, Know) {
        let slot = &ctx.env[chosen];
        let know = slot.know.clone();
        if self.types.kind(&slot.ty) == Kind::Copy {
            return (name(chosen), know);
        }
        if let Some(slot) = ctx.env.get_mut(chosen) {
            slot.gone = true;
        }
        ctx.moved.push(chosen.to_string());
        let expr = if self.rng.chance(1, 2) {
            Expr::Move(Box::new(name(chosen)))
        } else {
            name(chosen)
        };
        (expr, know)
    }

    /// The names of the type `ty` whose value may be consumed.
    fn owned(&self, ctx: &Ctx, ty: &Type) -> Vec<String> {
        ctx.env
            .iter()
            .filter(|(name, slot)| {
                &slot.ty == ty && self.consumable(name, slot) && !ctx.lent.contains(*name)
            })
            .map(|(name, _)| name.clone())
            .collect()
    }

    /// An expression of the type `ty` that is consumed where it stands, and
    /// what is known of its value: a name, which moves; a clone of a place;
    /// or a constructor, whose fields are consumed in turn.
    pub(super) fn value(&mut self, ctx: &mut Ctx, ty: &Type, depth: u8) -> Option<(Expr, Know)> {
        if ty.is_scalar() {
            return Some(self.gen_expr(&ctx.env, ty, depth));
        }
        // An obligation is given by the name that holds it, or it is made
        // of names that hold its parts.
        let must = self.types.kind(ty) == Kind::Must;
        let names = self.owned(ctx, ty);
        if !names.is_empty() && (must || self.rng.chance(1, 2)) {
            let chosen = self.rng.pick(&names).clone();
            return Some(self.take_name(ctx, &chosen));
        }
        if !must && self.rng.chance(1, 5) {
            let spots = self.places(&ctx.env, &|seen| seen == ty);
            if !spots.is_empty() {
                let spot = self.rng.pick(&spots).clone();
                let know = self
                    .lib()
                    .place(&spot.expr, &ctx.env, false)
                    .map_or_else(|| self.types.top(ty), |(_, know)| know);
                return Some((Expr::Clone(Box::new(spot.expr)), know));
            }
        }
        self.build(ctx, ty, depth)
    }

    /// A constructor of the type `ty`.
    fn build(&mut self, ctx: &mut Ctx, ty: &Type, depth: u8) -> Option<(Expr, Know)> {
        let below = depth.saturating_sub(1);
        match ty {
            Type::String => {
                let text = (*self.rng.pick(&STRINGS)).to_string();
                Some((Expr::String(text), Know::Sized(Range::new(0, POS))))
            }
            Type::Vector(item) => {
                let count = self.rng.index(if depth == 0 { 2 } else { 4 });
                self.vector(ctx, item, count, below)
            }
            Type::Map(_, _) => Some((Expr::EmptyMap, Know::Sized(Range::point(0)))),
            Type::Named(named) => {
                if let Some(info) = self.types.structure(named).cloned() {
                    let mut fields = Vec::new();
                    let mut knows = Vec::new();
                    for (_, field_ty) in &info.fields {
                        let (expr, know) = self.value(ctx, field_ty, below)?;
                        fields.push(expr);
                        knows.push(held(field_ty, know));
                    }
                    Some((Expr::Struct(info.name, fields), Know::Struct(knows)))
                } else if let Some(info) = self.types.variant(named).cloned() {
                    let which = self.rng.index(info.constructors.len());
                    let (constructor, declared) = &info.constructors[which];
                    let mut fields = Vec::new();
                    let mut knows = Vec::new();
                    for (_, field_ty) in declared {
                        let (expr, know) = self.value(ctx, field_ty, below)?;
                        fields.push(expr);
                        knows.push(held(field_ty, know));
                    }
                    let mut known = vec![None; info.constructors.len()];
                    known[which] = Some(knows);
                    Some((
                        Expr::Variant(info.name.clone(), constructor.clone(), fields),
                        Know::Variant(known),
                    ))
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn vector(
        &mut self,
        ctx: &mut Ctx,
        item: &Type,
        count: usize,
        depth: u8,
    ) -> Option<(Expr, Know)> {
        let mut items = Vec::new();
        for _ in 0..count {
            items.push(self.value(ctx, item, depth)?.0);
        }
        Some((
            Expr::Vector(items),
            Know::Sized(Range::point(count as i128)),
        ))
    }

    /// A value of the type `ty` that satisfies what a precondition says of
    /// it: for a vector, a length in `pre`.
    fn sized_value(&mut self, ctx: &mut Ctx, ty: &Type, pre: Range) -> Option<Expr> {
        let Type::Vector(item) = ty else {
            return Some(self.value(ctx, ty, 2)?.0);
        };
        if pre.lo <= 0 {
            return Some(self.value(ctx, ty, 2)?.0);
        }
        let long: Vec<String> = self
            .owned(ctx, ty)
            .into_iter()
            .filter(
                |name| matches!(&ctx.env[name].know, Know::Sized(length) if length.lo >= pre.lo),
            )
            .collect();
        if !long.is_empty() && self.rng.chance(2, 3) {
            let chosen = self.rng.pick(&long).clone();
            return Some(self.take_name(ctx, &chosen).0);
        }
        let count = pre.lo as usize + self.rng.index(2);
        Some(self.vector(ctx, item, count, 1)?.0)
    }

    /// An operand for a parameter of the type `ty`: a value, `&p` or `&~p`
    /// ([W8]). `pre` is what the precondition says of it.
    pub(super) fn operand_for(&mut self, ctx: &mut Ctx, ty: &Type, pre: Range) -> Option<Expr> {
        let long = |slot: &Slot| match &slot.know {
            Know::Sized(length) => length.lo >= pre.lo,
            _ => pre.lo <= 0,
        };
        match ty {
            Type::Ref(BorrowMode::Exclusive, inner) => {
                if self.ending && self.types.kind(inner) == Kind::Must {
                    return None;
                }
                let names: Vec<String> = ctx
                    .env
                    .iter()
                    .filter(|(name, slot)| {
                        slot.mutable
                            && !slot.gone
                            && slot.ty == **inner
                            && !ctx.lent.contains(*name)
                            && long(slot)
                    })
                    .map(|(name, _)| name.clone())
                    .collect();
                if names.is_empty() {
                    return None;
                }
                let chosen = self.rng.pick(&names).clone();
                ctx.lent.insert(chosen.clone());
                ctx.exclusive.insert(chosen.clone());
                ctx.changed.push(chosen.clone());
                Some(Expr::Borrow(BorrowMode::Exclusive, Box::new(name(&chosen))))
            }
            Type::Ref(BorrowMode::Shared, inner) => {
                // An obligation is lent by the name that holds it, and is
                // no temporary ([O3a]).
                let must = self.types.kind(inner) == Kind::Must;
                if self.ending && must {
                    return None;
                }
                let names: Vec<String> = ctx
                    .env
                    .iter()
                    .filter(|(name, slot)| {
                        !slot.gone
                            && slot.ty == **inner
                            && !ctx.exclusive.contains(*name)
                            && long(slot)
                    })
                    .map(|(name, _)| name.clone())
                    .collect();
                if !names.is_empty() && (must || self.rng.chance(3, 4)) {
                    let chosen = self.rng.pick(&names).clone();
                    ctx.lent.insert(chosen.clone());
                    return Some(Expr::Borrow(BorrowMode::Shared, Box::new(name(&chosen))));
                }
                if must {
                    return None;
                }
                // A value that is read where it is.
                self.sized_value(ctx, inner, pre)
            }
            other => self.sized_value(ctx, other, pre),
        }
    }

    // Statements.

    /// One statement on data. False when none could be written.
    pub(super) fn data_step(&mut self, selector: &Selector, running: &[usize], room: bool) -> bool {
        match self.rng.below(16) {
            0 | 1 => self.unpack(selector, running),
            2..=4 => self.assign_data(selector, running),
            5 | 6 if room => self.decide_variant(selector, running),
            7 | 8 => self.push_op(selector, running),
            9 if room => self.shrink_op(selector, running),
            10 if room => self.map_op(selector, running),
            11 if room => self.guarded_index(selector, running),
            12 => self.emit_op(selector, running),
            13 | 14 => self.capture_op(selector, running),
            15 if room => self.decide_outcome(selector, running),
            _ => {
                let ty = self.data_type();
                self.bind_data(selector, running, ty)
            }
        }
    }

    pub(super) fn bind_data(&mut self, selector: &Selector, running: &[usize], ty: Type) -> bool {
        let mut ctx = self.ctx(running);
        let Some((value, know)) = self.value(&mut ctx, &ty, 2) else {
            return false;
        };
        let bound = self.fresh("v");
        let mutable = self.rng.chance(1, 2);
        // A name or a constructor of a declared type says the type; a
        // literal of a collection does not.
        let says = matches!(
            value,
            Expr::Name(_) | Expr::Move(_) | Expr::Struct(_, _) | Expr::Variant(_, _, _)
        );
        let typed = !says || self.rng.chance(1, 2);
        self.push(
            selector,
            Command::Bind {
                mutable,
                name: bound.clone(),
                ty: typed.then(|| ty.clone()),
                value,
            },
        );
        self.apply(running, &ctx);
        let slot = self.slot(&ty, mutable, know);
        self.bind_name(running, &bound, &slot);
        true
    }

    /// `S {x̄} := e` ([E-Unpack]): a struct is taken apart.
    fn unpack(&mut self, selector: &Selector, running: &[usize]) -> bool {
        let mut ctx = self.ctx(running);
        let candidates: Vec<String> = ctx
            .env
            .iter()
            .filter(|(name, slot)| {
                matches!(&slot.ty, Type::Named(ty) if self.types.structure(ty).is_some())
                    && self.consumable(name, slot)
            })
            .map(|(name, _)| name.clone())
            .collect();
        if !candidates.is_empty() && self.rng.chance(3, 4) {
            let chosen = self.rng.pick(&candidates).clone();
            self.unpack_name(selector, running, &chosen);
            return true;
        }
        let Some(ty) = self.struct_type() else {
            return false;
        };
        let Some((value, know)) = self.build(&mut ctx, &ty, 2) else {
            return false;
        };
        self.unpack_value(selector, running, &ctx, value, know, &ty)
    }

    /// Takes apart the struct that the name `chosen` holds.
    fn unpack_name(&mut self, selector: &Selector, running: &[usize], chosen: &str) {
        let mut ctx = self.ctx(running);
        let ty = ctx.env[chosen].ty.clone();
        let (value, know) = self.take_name(&mut ctx, chosen);
        self.unpack_value(selector, running, &ctx, value, know, &ty);
    }

    fn unpack_value(
        &mut self,
        selector: &Selector,
        running: &[usize],
        ctx: &Ctx,
        value: Expr,
        know: Know,
        ty: &Type,
    ) -> bool {
        let Type::Named(struct_name) = ty else {
            return false;
        };
        let Some(info) = self.types.structure(struct_name).cloned() else {
            return false;
        };
        let names: Vec<String> = info.fields.iter().map(|_| self.fresh("v")).collect();
        self.push(
            selector,
            Command::Unpack {
                struct_name: info.name.clone(),
                names: names.clone(),
                value,
            },
        );
        self.apply(running, ctx);
        let knows = match know {
            Know::Struct(fields) => fields,
            _ => info
                .fields
                .iter()
                .map(|(_, ty)| self.types.top(ty))
                .collect(),
        };
        for ((bound, (_, field_ty)), know) in names.iter().zip(&info.fields).zip(knows) {
            let slot = self.slot(field_ty, false, held(field_ty, know));
            self.bind_name(running, bound, &slot);
        }
        true
    }

    /// `x ← e`, `p.x ← e` or `p[i] ← e` on data ([E-Assign], [O4]).
    fn assign_data(&mut self, selector: &Selector, running: &[usize]) -> bool {
        let mut ctx = self.ctx(running);
        let floor = self.floor();
        // A whole name: one that was moved may be assigned where it could
        // have been moved, so that a loop leaves it as it found it ([O6]).
        // A name that holds an obligation is assigned only where its value
        // has moved on every history ([O4]).
        let whole: Vec<String> = ctx
            .env
            .iter()
            .filter(|(name, slot)| {
                slot.mutable
                    && !slot.ty.is_scalar()
                    && if self.types.kind(&slot.ty) == Kind::Must {
                        slot.home >= floor && self.gone_on_all(running, name)
                    } else {
                        !slot.gone || slot.home >= floor
                    }
            })
            .map(|(name, _)| name.clone())
            .collect();
        // A field of a name, or an element of a vector that has one.
        let parts: Vec<Spot> = self
            .places(&ctx.env, &|_| true)
            .into_iter()
            .filter(|spot| {
                spot.mutable
                    && self.types.kind(&spot.ty) != Kind::Must
                    && (!spot.steps.is_empty()
                        || matches!(spot.ty, Type::Vector(_)) && spot.length(&ctx.env).lo >= 1)
            })
            .collect();
        if whole.is_empty() && parts.is_empty() {
            return false;
        }
        if parts.is_empty() || !whole.is_empty() && self.rng.chance(1, 3) {
            let target = self.rng.pick(&whole).clone();
            let ty = ctx.env[&target].ty.clone();
            let Some((value, know)) = self.value(&mut ctx, &ty, 2) else {
                return false;
            };
            self.push(
                selector,
                Command::Assign {
                    name: target.clone(),
                    value,
                },
            );
            self.apply(running, &ctx);
            let last = self.here();
            for &index in running {
                if let Some(slot) = self.scopes[last].live[index].env.get_mut(&target) {
                    slot.know = know.clone();
                    slot.gone = false;
                    slot.definition = None;
                }
            }
            return true;
        }
        let spot = self.rng.pick(&parts).clone();
        // The owner is written, so the value does not consume it.
        ctx.lent.insert(spot.root.clone());
        let element = match &spot.ty {
            Type::Vector(item) if spot.steps.is_empty() || self.rng.chance(1, 2) => {
                let length = spot.length(&ctx.env);
                if length.lo >= 1 {
                    Some(((**item).clone(), self.rng.range(0, (length.lo - 1).min(3))))
                } else {
                    None
                }
            }
            _ => None,
        };
        if matches!(spot.ty, Type::Vector(_)) && spot.steps.is_empty() && element.is_none() {
            return false;
        }
        let written = element.as_ref().map_or(&spot.ty, |(item, _)| item).clone();
        if self.types.kind(&written) == Kind::Must {
            return false;
        }
        let Some((value, know)) = self.value(&mut ctx, &written, 2) else {
            return false;
        };
        let target = spot.place(element.as_ref().map(|(_, index)| int(*index)));
        self.push(selector, Command::AssignPlace { target, value });
        self.apply(running, &ctx);
        if element.is_none() {
            let know = held(&written, know);
            let last = self.here();
            for &index in running {
                spot.set(&mut self.scopes[last].live[index].env, know.clone());
            }
        }
        true
    }

    /// The histories on which a decision goes on: for each running history
    /// and each alternative, the names as they are there, or `None` where
    /// the alternative cannot occur.
    fn split(
        &mut self,
        selector: &Selector,
        running: &[usize],
        site: &str,
        alternatives: &[&str],
        outcomes: Vec<Vec<Option<Env>>>,
    ) {
        let site_index = self.scope().sites.len();
        let mut children = Vec::new();
        let mut reached = vec![false; alternatives.len()];
        for (&index, per) in running.iter().zip(outcomes) {
            let atoms = self.scope().live[index].atoms.clone();
            for (which, env) in per.into_iter().enumerate() {
                let Some(env) = env else { continue };
                let mut atoms = atoms.clone();
                atoms.push((site_index, which));
                children.push(Path { atoms, env });
                reached[which] = true;
            }
        }
        self.scope_mut().sites.push(SiteInfo {
            name: site.to_string(),
            alternatives: alternatives
                .iter()
                .map(|name| (*name).to_string())
                .collect(),
        });
        self.replace(running, children);
        for (which, alternative) in alternatives.iter().enumerate() {
            if !reached[which] && self.rng.chance(3, 5) {
                let arm = and_selector(
                    selector,
                    Selector::Atom(site.to_string(), (*alternative).to_string()),
                );
                self.push(&arm, Command::Impossible);
            }
        }
    }

    /// Writes a decision on a built-in operation and gives its site.
    fn operation(
        &mut self,
        selector: &Selector,
        operation: &str,
        arguments: Vec<Expr>,
        arms: Vec<Arm>,
    ) -> String {
        let site = self.fresh("d");
        self.push(
            selector,
            Command::Decide {
                site: site.clone(),
                mode: CallMode::Sync,
                operation: operation.to_string(),
                arguments,
                arms,
            },
        );
        site
    }

    /// `d : Δ V(x) ▸ …` ([E-Outcome], [I11]): a variant is taken apart.
    fn decide_variant(&mut self, selector: &Selector, running: &[usize]) -> bool {
        let ctx = self.ctx(running);
        let candidates: Vec<String> = ctx
            .env
            .iter()
            .filter(|(name, slot)| {
                matches!(&slot.ty, Type::Named(ty) if self.types.variant(ty).is_some())
                    && self.consumable(name, slot)
            })
            .map(|(name, _)| name.clone())
            .collect();
        if candidates.is_empty() {
            return false;
        }
        let chosen = self.rng.pick(&candidates).clone();
        self.decide_variant_name(selector, running, &chosen);
        true
    }

    /// Takes apart the variant that the name `chosen` holds.
    fn decide_variant_name(&mut self, selector: &Selector, running: &[usize], chosen: &str) {
        let mut ctx = self.ctx(running);
        let Type::Named(variant) = ctx.env[chosen].ty.clone() else {
            return;
        };
        let Some(info) = self.types.variant(&variant).cloned() else {
            return;
        };
        let operand = self.take_name(&mut ctx, chosen).0;
        let arms: Vec<Arm> = info
            .constructors
            .iter()
            .map(|(constructor, fields)| Arm {
                alternative: constructor.clone(),
                names: fields.iter().map(|_| self.fresh("v")).collect(),
            })
            .collect();
        let site = self.operation(selector, &info.name, vec![operand], arms.clone());
        // What each history knows of the value, before it moves.
        let seen: Vec<Know> = running
            .iter()
            .map(|&index| self.scope().live[index].env[chosen].know.clone())
            .collect();
        self.apply(running, &ctx);
        let mut outcomes = Vec::new();
        for (&index, know) in running.iter().zip(seen) {
            let mut per = Vec::new();
            for (which, (_, fields)) in info.constructors.iter().enumerate() {
                let knows = match &know {
                    Know::Variant(all) => all[which].clone(),
                    _ => Some(fields.iter().map(|(_, ty)| self.types.top(ty)).collect()),
                };
                per.push(knows.map(|knows| {
                    let mut env = self.scope().live[index].env.clone();
                    for ((bound, (_, ty)), know) in arms[which].names.iter().zip(fields).zip(knows)
                    {
                        env.insert(bound.clone(), self.slot(ty, false, held(ty, know)));
                    }
                    env
                }));
            }
            outcomes.push(per);
        }
        let alternatives: Vec<&str> = info
            .constructors
            .iter()
            .map(|(constructor, _)| constructor.as_str())
            .collect();
        self.split(selector, running, &site, &alternatives, outcomes);
    }

    fn vectors(&self, env: &Env) -> Vec<Spot> {
        self.places(env, &|ty| matches!(ty, Type::Vector(_)))
            .into_iter()
            .filter(|spot| spot.mutable)
            .collect()
    }

    /// `Δ push(&~v, e)`: the vector is one longer.
    fn push_op(&mut self, selector: &Selector, running: &[usize]) -> bool {
        let mut ctx = self.ctx(running);
        let spots = self.vectors(&ctx.env);
        if spots.is_empty() {
            return false;
        }
        let spot = self.rng.pick(&spots).clone();
        let Type::Vector(item) = &spot.ty else {
            return false;
        };
        ctx.lent.insert(spot.root.clone());
        let Some((value, _)) = self.value(&mut ctx, item, 2) else {
            return false;
        };
        let lent = Expr::Borrow(BorrowMode::Exclusive, Box::new(spot.expr.clone()));
        let site = self.operation(selector, "push", vec![lent, value], vec![arm("done", &[])]);
        self.apply(running, &ctx);
        let outcomes = running
            .iter()
            .map(|&index| {
                let mut env = self.scope().live[index].env.clone();
                let longer = add(spot.length(&env), Range::point(1));
                spot.set(&mut env, Know::Sized(longer));
                vec![Some(env)]
            })
            .collect();
        self.split(selector, running, &site, &["done"], outcomes);
        true
    }

    /// `Δ pop(&~v)` or `Δ take(v)`: an element leaves the vector, or it is
    /// empty.
    fn shrink_op(&mut self, selector: &Selector, running: &[usize]) -> bool {
        let mut ctx = self.ctx(running);
        let shorter =
            |length: Range| subtract(Range::new(length.lo.max(1), length.hi), Range::point(1));
        if self.rng.chance(2, 3) {
            let spots = self.vectors(&ctx.env);
            if spots.is_empty() {
                return false;
            }
            let spot = self.rng.pick(&spots).clone();
            let Type::Vector(item) = &spot.ty else {
                return false;
            };
            let last = self.fresh("v");
            let lent = Expr::Borrow(BorrowMode::Exclusive, Box::new(spot.expr.clone()));
            let arms = vec![arm("item", &[&last]), arm("empty", &[])];
            let site = self.operation(selector, "pop", vec![lent], arms);
            let outcomes = running
                .iter()
                .map(|&index| {
                    let env = &self.scope().live[index].env;
                    let length = spot.length(env);
                    let item_env = (length.hi >= 1).then(|| {
                        let mut env = env.clone();
                        spot.set(&mut env, Know::Sized(shorter(length)));
                        env.insert(last.clone(), self.slot(item, false, self.types.top(item)));
                        env
                    });
                    let empty_env = (length.lo <= 0).then(|| {
                        let mut env = env.clone();
                        spot.set(&mut env, Know::Sized(Range::point(0)));
                        env
                    });
                    vec![item_env, empty_env]
                })
                .collect();
            self.split(selector, running, &site, &["item", "empty"], outcomes);
            return true;
        }
        let candidates: Vec<String> = ctx
            .env
            .iter()
            .filter(|(name, slot)| {
                matches!(slot.ty, Type::Vector(_)) && self.consumable(name, slot)
            })
            .map(|(name, _)| name.clone())
            .collect();
        if candidates.is_empty() {
            return false;
        }
        let chosen = self.rng.pick(&candidates).clone();
        let ty = ctx.env[&chosen].ty.clone();
        let Type::Vector(item) = &ty else {
            return false;
        };
        let lengths: Vec<Range> = running
            .iter()
            .map(|&index| match &self.scope().live[index].env[&chosen].know {
                Know::Sized(length) => *length,
                _ => Range::new(0, POS),
            })
            .collect();
        let operand = self.take_name(&mut ctx, &chosen).0;
        let (head, tail) = (self.fresh("v"), self.fresh("v"));
        let arms = vec![arm("item", &[&head, &tail]), arm("empty", &[])];
        let site = self.operation(selector, "take", vec![operand], arms);
        self.apply(running, &ctx);
        let outcomes = running
            .iter()
            .zip(lengths)
            .map(|(&index, length)| {
                let env = &self.scope().live[index].env;
                let item_env = (length.hi >= 1).then(|| {
                    let mut env = env.clone();
                    env.insert(head.clone(), self.slot(item, false, self.types.top(item)));
                    env.insert(
                        tail.clone(),
                        self.slot(&ty, false, Know::Sized(shorter(length))),
                    );
                    env
                });
                let empty_env = (length.lo <= 0).then(|| env.clone());
                vec![item_env, empty_env]
            })
            .collect();
        self.split(selector, running, &site, &["item", "empty"], outcomes);
        true
    }

    /// An operand for a parameter `&τ` of a built-in operation: `&p`, or a
    /// value that is read where it is.
    fn read_operand(&mut self, ctx: &mut Ctx, ty: &Type) -> Option<Expr> {
        self.operand_for(
            ctx,
            &Type::Ref(BorrowMode::Shared, Box::new(ty.clone())),
            Range::ALL,
        )
    }

    /// Reads a payload borrow of a copy type once, where the alternative
    /// that gave it occurred ([W8]): `x : τ := borrowed`.
    fn copy_out(
        &mut self,
        selector: &Selector,
        site: &str,
        alternative: &str,
        borrowed: &str,
        ty: &Type,
    ) {
        if self.types.kind(ty) != Kind::Copy || !self.rng.chance(2, 3) {
            return;
        }
        let taken_arm = and_selector(
            selector,
            Selector::Atom(site.to_string(), alternative.to_string()),
        );
        let taken = self.running(&taken_arm);
        if taken.is_empty() {
            return;
        }
        let bound = self.fresh("v");
        self.push(
            &taken_arm,
            Command::Bind {
                mutable: false,
                name: bound.clone(),
                ty: Some(ty.clone()),
                value: name(borrowed),
            },
        );
        let slot = self.slot(ty, false, self.types.top(ty));
        self.bind_name(&taken, &bound, &slot);
    }

    /// `get`, `entry_at`, `insert` or `remove` on a map. The conditions of
    /// the prelude say what becomes of its length.
    fn map_op(&mut self, selector: &Selector, running: &[usize]) -> bool {
        let mut ctx = self.ctx(running);
        let spots = self.places(&ctx.env, &|ty| matches!(ty, Type::Map(_, _)));
        if spots.is_empty() {
            // No map yet: this statement binds one.
            let key = if self.rng.chance(1, 2) {
                Type::String
            } else {
                Type::Int(*self.rng.pick(&self.palette))
            };
            let ty = Type::Map(Box::new(key), Box::new(self.element_type()));
            return self.bind_data(selector, running, ty);
        }
        let spot = self.rng.pick(&spots).clone();
        let Type::Map(key_ty, value_ty) = &spot.ty else {
            return false;
        };
        ctx.lent.insert(spot.root.clone());
        let lend = |mode: BorrowMode| Expr::Borrow(mode, Box::new(spot.expr.clone()));
        let envs = |generator: &Self| -> Vec<Env> {
            running
                .iter()
                .map(|&index| generator.scope().live[index].env.clone())
                .collect()
        };
        match self.rng.below(if spot.mutable { 7 } else { 3 }) {
            0 | 1 => {
                let Some(key) = self.read_operand(&mut ctx, key_ty) else {
                    return false;
                };
                let found = self.fresh("v");
                let arms = vec![arm("found", &[&found]), arm("missing", &[])];
                let arguments = vec![lend(BorrowMode::Shared), key];
                let site = self.operation(selector, "get", arguments, arms);
                self.apply(running, &ctx);
                let outcomes = envs(self)
                    .into_iter()
                    .map(|env| vec![Some(env.clone()), Some(env)])
                    .collect();
                self.split(selector, running, &site, &["found", "missing"], outcomes);
                self.copy_out(selector, &site, "found", &found, value_ty);
            }
            2 => {
                let (position, _) = self.gen_int(&ctx.env, IntType::Usize, 1);
                let (key, value, next) = (self.fresh("v"), self.fresh("v"), self.fresh("v"));
                let arms = vec![arm("item", &[&key, &value, &next]), arm("finished", &[])];
                let arguments = vec![lend(BorrowMode::Shared), position];
                let site = self.operation(selector, "entry_at", arguments, arms);
                self.apply(running, &ctx);
                let usize_ty = Type::Int(IntType::Usize);
                let outcomes = envs(self)
                    .into_iter()
                    .map(|env| {
                        let mut item = env.clone();
                        let slot = self.slot(&usize_ty, false, self.types.top(&usize_ty));
                        item.insert(next.clone(), slot);
                        vec![Some(item), Some(env)]
                    })
                    .collect();
                self.split(selector, running, &site, &["item", "finished"], outcomes);
                self.copy_out(selector, &site, "item", &value, value_ty);
            }
            3 | 4 => {
                let Some((key, _)) = self.value(&mut ctx, key_ty, 1) else {
                    return false;
                };
                let Some((value, _)) = self.value(&mut ctx, value_ty, 2) else {
                    return false;
                };
                let previous = self.fresh("v");
                let arms = vec![arm("inserted", &[]), arm("replaced", &[&previous])];
                let arguments = vec![lend(BorrowMode::Exclusive), key, value];
                let site = self.operation(selector, "insert", arguments, arms);
                self.apply(running, &ctx);
                let outcomes = envs(self)
                    .into_iter()
                    .map(|env| {
                        let length = spot.length(&env);
                        let mut inserted = env.clone();
                        spot.set(&mut inserted, Know::Sized(add(length, Range::point(1))));
                        let replaced = (length.hi >= 1).then(|| {
                            let mut env = env;
                            let stays = Range::new(length.lo.max(1), length.hi);
                            spot.set(&mut env, Know::Sized(stays));
                            let slot = self.slot(value_ty, false, self.types.top(value_ty));
                            env.insert(previous.clone(), slot);
                            env
                        });
                        vec![Some(inserted), replaced]
                    })
                    .collect();
                self.split(
                    selector,
                    running,
                    &site,
                    &["inserted", "replaced"],
                    outcomes,
                );
            }
            _ => {
                let Some(key) = self.read_operand(&mut ctx, key_ty) else {
                    return false;
                };
                let previous = self.fresh("v");
                let arms = vec![arm("removed", &[&previous]), arm("missing", &[])];
                let arguments = vec![lend(BorrowMode::Exclusive), key];
                let site = self.operation(selector, "remove", arguments, arms);
                self.apply(running, &ctx);
                // The contract of `remove` says nothing of the length.
                let outcomes = envs(self)
                    .into_iter()
                    .map(|mut env| {
                        spot.set(&mut env, Know::Sized(Range::new(0, POS)));
                        let mut removed = env.clone();
                        let slot = self.slot(value_ty, false, self.types.top(value_ty));
                        removed.insert(previous.clone(), slot);
                        vec![Some(removed), Some(env)]
                    })
                    .collect();
                self.split(selector, running, &site, &["removed", "missing"], outcomes);
            }
        }
        true
    }

    /// `t : ? i < len(v)` and, where it is true, `x := v[i]`: the index is
    /// in range by the test and by nothing else ([P5]).
    fn guarded_index(&mut self, selector: &Selector, running: &[usize]) -> bool {
        let env = self.running_env(running);
        let spots = self.places(
            &env,
            &|ty| matches!(ty, Type::Vector(item) if item.is_scalar()),
        );
        if spots.is_empty() {
            return false;
        }
        let spot = self.rng.pick(&spots).clone();
        let Type::Vector(item) = &spot.ty else {
            return false;
        };
        let (index, _) = self.gen_int(&env, IntType::Usize, 1);
        let length = Expr::Len(Box::new(spot.expr.clone()));
        let condition = if self.rng.chance(1, 2) {
            bin(Binary::Less, index.clone(), length)
        } else {
            bin(Binary::Greater, length, index.clone())
        };
        let before = self.scope().sites.len();
        self.branch(selector, running, condition);
        let site = self.scope().sites[before].name.clone();
        let taken_arm = and_selector(selector, Selector::Atom(site, "true".to_string()));
        let taken = self.running(&taken_arm);
        if taken.is_empty() {
            return true;
        }
        let bound = self.fresh("v");
        self.push(
            &taken_arm,
            Command::Bind {
                mutable: false,
                name: bound.clone(),
                ty: Some((**item).clone()),
                value: Expr::Index(Box::new(spot.expr.clone()), Box::new(index)),
            },
        );
        let slot = self.slot(item, false, self.types.top(item));
        self.bind_name(&taken, &bound, &slot);
        true
    }

    /// `Δ emit(&s)`: the one built-in operation with an effect.
    fn emit_op(&mut self, selector: &Selector, running: &[usize]) -> bool {
        let mut ctx = self.ctx(running);
        let Some(text) = self.read_operand(&mut ctx, &Type::String) else {
            return false;
        };
        self.effects.insert("console.write".to_string());
        let site = self.operation(selector, "emit", vec![text], vec![arm("done", &[])]);
        self.apply(running, &ctx);
        let outcomes = running
            .iter()
            .map(|&index| vec![Some(self.scope().live[index].env.clone())])
            .collect();
        self.split(selector, running, &site, &["done"], outcomes);
        true
    }

    // Obligations.

    fn gone_on_all(&self, running: &[usize], name: &str) -> bool {
        running.iter().all(|&index| {
            self.scope().live[index]
                .env
                .get(name)
                .is_some_and(|slot| slot.gone)
        })
    }

    /// `x := capture f(ō)` ([E-Capture]): the operation runs here, and the
    /// name holds its outcome until a decision takes it ([I12]).
    fn capture_op(&mut self, selector: &Selector, running: &[usize]) -> bool {
        // An `&~` argument has two terms in the record of a capture; the
        // generator keeps one interval for each argument.
        let callables: Vec<Sig> = self
            .callees()
            .into_iter()
            .filter(|sig| {
                sig.params
                    .iter()
                    .all(|(_, ty)| !matches!(ty, Type::Ref(BorrowMode::Exclusive, _)))
            })
            .collect();
        if callables.is_empty() {
            return false;
        }
        let callee = self.rng.pick(&callables).clone();
        let mut ctx = self.ctx(running);
        let Some(arguments) = self.arguments(&mut ctx, &callee) else {
            return false;
        };
        // The operation runs here, so a fault of it occurs here ([F1]).
        let exposed;
        let running = if callee.faults {
            if !self.expose(selector, running, &ctx, false) {
                return false;
            }
            exposed = self.running(selector);
            &exposed[..]
        } else {
            self.apply(running, &ctx);
            running
        };
        let recorded: Vec<Vec<Range>> = running
            .iter()
            .map(|&index| {
                let env = &self.scope().live[index].env;
                callee
                    .params
                    .iter()
                    .zip(&arguments)
                    .map(|((_, ty), argument)| match ty {
                        Type::Int(_) => self
                            .lib()
                            .int(argument, env, None)
                            .map_or(Range::ALL, |val| val.flow),
                        _ => Range::ALL,
                    })
                    .collect()
            })
            .collect();
        let bound = self.fresh("v");
        let mutable = self.rng.chance(1, 4);
        let ty = Type::OutcomeNamed(callee.name.clone());
        let typed = self.rng.chance(1, 3);
        self.effects.extend(callee.uses.iter().cloned());
        self.push(
            selector,
            Command::Capture {
                mutable,
                name: bound.clone(),
                ty: typed.then(|| ty.clone()),
                mode: CallMode::Sync,
                operation: callee.name.clone(),
                arguments,
            },
        );
        let last = self.here();
        for (&index, ranges) in running.iter().zip(recorded) {
            let slot = self.slot(&ty, mutable, Know::Outcome(ranges));
            self.scopes[last].live[index]
                .env
                .insert(bound.clone(), slot);
        }
        true
    }

    /// `d : Δ outcome(x) ▸ …` on a name that holds a captured outcome.
    fn decide_outcome(&mut self, selector: &Selector, running: &[usize]) -> bool {
        let env = self.running_env(running);
        let candidates: Vec<String> = env
            .iter()
            .filter(|(name, slot)| {
                matches!(slot.ty, Type::OutcomeNamed(_)) && self.consumable(name, slot)
            })
            .map(|(name, _)| name.clone())
            .collect();
        if candidates.is_empty() {
            return false;
        }
        let chosen = self.rng.pick(&candidates).clone();
        self.decide_outcome_name(selector, running, &chosen);
        true
    }

    /// The decision on the captured outcome that `chosen` holds
    /// ([E-Outcome]): each alternative is known by the conditions of the
    /// captured operation, over the arguments of the capture where the
    /// capture is visible and over names of which nothing is known where it
    /// is not ([I12]).
    fn decide_outcome_name(&mut self, selector: &Selector, running: &[usize], chosen: &str) {
        let mut ctx = self.ctx(running);
        let Type::OutcomeNamed(captured) = ctx.env[chosen].ty.clone() else {
            return;
        };
        let Some(callee) = self
            .callables
            .iter()
            .find(|sig| sig.name == captured)
            .cloned()
        else {
            return;
        };
        let operand = self.take_name(&mut ctx, chosen).0;
        let arms: Vec<Arm> = callee
            .alts
            .iter()
            .map(|alternative| Arm {
                alternative: alternative.name.clone(),
                names: alternative.fields.iter().map(|_| self.fresh("v")).collect(),
            })
            .collect();
        let site = self.operation(selector, "outcome", vec![operand], arms.clone());
        let seen: Vec<Know> = running
            .iter()
            .map(|&index| self.scope().live[index].env[chosen].know.clone())
            .collect();
        self.apply(running, &ctx);
        let mut outcomes = Vec::new();
        for (&index, know) in running.iter().zip(seen) {
            let recorded = match know {
                Know::Outcome(ranges) if ranges.len() == callee.params.len() => ranges,
                _ => vec![Range::ALL; callee.params.len()],
            };
            let mut per = Vec::new();
            'alternative: for (which, alternative) in callee.alts.iter().enumerate() {
                let mut narrowed = recorded.clone();
                for (position, bound) in alternative.params.iter().enumerate() {
                    if let Some(bound) = bound {
                        narrowed[position] = narrowed[position].meet(*bound);
                        if narrowed[position].is_empty() {
                            per.push(None);
                            continue 'alternative;
                        }
                    }
                }
                let mut env = self.scope().live[index].env.clone();
                for (field, bound) in alternative.fields.iter().zip(&arms[which].names) {
                    let Some(know) = self.payload_know(field, &|position| narrowed[position])
                    else {
                        per.push(None);
                        continue 'alternative;
                    };
                    env.insert(bound.clone(), self.slot(&field.ty, false, know));
                }
                per.push(Some(env));
            }
            outcomes.push(per);
        }
        let alternatives: Vec<&str> = callee
            .alts
            .iter()
            .map(|alternative| alternative.name.as_str())
            .collect();
        self.split(selector, running, &site, &alternatives, outcomes);
    }

    /// `d : Δ k(▾x) ▸ done {}`: the resource that `chosen` holds is closed.
    fn close(&mut self, selector: &Selector, running: &[usize], chosen: &str) {
        let mut ctx = self.ctx(running);
        let Type::Named(resource) = ctx.env[chosen].ty.clone() else {
            return;
        };
        let Some(closer) = self
            .types
            .resource(&resource)
            .map(|info| info.closer.clone())
        else {
            return;
        };
        let operand = self.take_name(&mut ctx, chosen).0;
        let site = self.operation(selector, &closer, vec![operand], vec![arm("done", &[])]);
        self.apply(running, &ctx);
        let outcomes = running
            .iter()
            .map(|&index| vec![Some(self.scope().live[index].env.clone())])
            .collect();
        self.split(selector, running, &site, &["done"], outcomes);
    }

    /// Whether the statement asks that the name be gone.
    fn due(&self, due: &Due, name: &str, slot: &Slot) -> bool {
        if slot.gone || self.types.kind(&slot.ty) != Kind::Must {
            return false;
        }
        match due {
            Due::From(floor) => slot.home >= *floor,
            Due::Uneven => true,
            Due::Fault(route) => self.must_go(route, name, slot),
            Due::Escape => !self.releasable(&slot.ty),
        }
    }

    /// An obligation that a history of `running` holds and that `due` asks
    /// for, and the histories that hold it.
    fn owed(&self, running: &[usize], due: &Due) -> Option<(String, Vec<usize>)> {
        let uneven = matches!(due, Due::Uneven);
        let scope = self.scope();
        let holds = |index: usize, name: &str| {
            scope.live[index]
                .env
                .get(name)
                .is_some_and(|slot| !slot.gone)
        };
        for &index in running {
            for (name, slot) in &scope.live[index].env {
                if !self.due(due, name, slot) {
                    continue;
                }
                let holders: Vec<usize> = running
                    .iter()
                    .copied()
                    .filter(|&other| holds(other, name))
                    .collect();
                if uneven && holders.len() == running.len() {
                    continue;
                }
                return Some((name.clone(), holders));
            }
        }
        None
    }

    /// A selector, within `selector`, whose histories are some of `holders`
    /// and no other: `selector` itself where all of its histories are
    /// holders, else `selector` and the one atom that picks most of them,
    /// else every atom of one of them.
    fn selector_of(
        &self,
        selector: &Selector,
        running: &[usize],
        holders: &[usize],
    ) -> (Selector, Vec<usize>) {
        if holders.len() == running.len() {
            return (selector.clone(), running.to_vec());
        }
        let scope = self.scope();
        let atom = |site: usize, which: usize| {
            let info = &scope.sites[site];
            Selector::Atom(info.name.clone(), info.alternatives[which].clone())
        };
        let mut best: Option<(Selector, Vec<usize>)> = None;
        for &holder in holders {
            for &(site, which) in &scope.live[holder].atoms {
                let under = and_selector(selector, atom(site, which));
                let picked = self.running(&under);
                if picked.iter().all(|index| holders.contains(index))
                    && best
                        .as_ref()
                        .is_none_or(|(_, seen)| picked.len() > seen.len())
                {
                    best = Some((under, picked));
                }
            }
        }
        if let Some(best) = best {
            return best;
        }
        let mut under = selector.clone();
        for &(site, which) in &scope.live[holders[0]].atoms {
            under = and_selector(&under, atom(site, which));
        }
        let picked = self.running(&under);
        (under, picked)
    }

    pub(super) fn discharge(&mut self, selector: &Selector, due: &Due) {
        loop {
            let running = self.running(selector);
            let Some((owed, holders)) = self.owed(&running, due) else {
                return;
            };
            let (under, picked) = self.selector_of(selector, &running, &holders);
            let ty = self.scope().live[picked[0]].env[&owed].ty.clone();
            match &ty {
                Type::OutcomeNamed(_) => self.decide_outcome_name(&under, &picked, &owed),
                Type::Named(named) if self.types.structure(named).is_some() => {
                    self.unpack_name(&under, &picked, &owed);
                }
                Type::Named(named) if self.types.variant(named).is_some() => {
                    self.decide_variant_name(&under, &picked, &owed);
                }
                _ => self.close(&under, &picked, &owed),
            }
        }
    }

    /// What [O5] asks before a terminator that ends the bodies from `floor`
    /// inward: no history of `selector` holds an obligation there. The
    /// statements that discharge them stand before the terminator, and the
    /// histories of `selector` are other ones afterwards.
    pub(super) fn settle(&mut self, selector: &Selector, floor: usize) {
        self.discharge(selector, &Due::From(floor));
    }

    /// Before a loop: every obligation is held by all the histories of
    /// `selector` or by none of them.
    pub(super) fn level(&mut self, selector: &Selector) {
        self.discharge(selector, &Due::Uneven);
    }
}
