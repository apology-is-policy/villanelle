//! The oracle: the instrumented semantics of `docs/v2/core.md`, section 6,
//! implemented directly.
//!
//! It runs a typed core program and is stuck on every violation the checker
//! is meant to exclude. Each rule below carries the name of its clause, and
//! each way of being stuck carries its number from the table of section 6.10.

use crate::host::Host;
use crate::int::Int;
use crate::syntax::escape_string;
use crate::typed::{
    Arithmetic, BodyId, BorrowMode, BoundaryId, BuiltinOp, Command, Comparison, Control,
    ControlBody, ControlId, Expr, Kind, Operation, OutcomeId, Place, PlaceStep, Program,
    ResourceId, Selector, SiteId, StructId, Type, VarId, VarRef, VariantId,
};
use std::collections::{BTreeMap, HashMap, VecDeque};
use std::fmt;

pub type ScopeId = u64;
pub type TagId = u64;
pub type TaskSetId = u64;

/// One concrete step inside a runtime place (`docs/v2/core.md` section 6.1).
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum RuntimeStep {
    Field(usize),
    Index(usize),
    VariantField(usize, usize),
    MapValue(Value),
    MapKey(Value),
}

/// A live runtime location `(scope, var, steps)` referred to by a borrow.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct RuntimePlace {
    pub scope: ScopeId,
    pub var: VarId,
    pub steps: Vec<RuntimeStep>,
}

impl RuntimePlace {
    pub fn root(scope: ScopeId, var: VarId) -> RuntimePlace {
        RuntimePlace {
            scope,
            var,
            steps: Vec::new(),
        }
    }

    pub fn with_step(&self, step: RuntimeStep) -> RuntimePlace {
        let mut out = self.clone();
        out.steps.push(step);
        out
    }

    /// Whether `self` contains `other` (`self` is a prefix of `other`, §6.3).
    pub fn contains(&self, other: &RuntimePlace) -> bool {
        self.scope == other.scope
            && self.var == other.var
            && other.steps.len() >= self.steps.len()
            && other.steps[..self.steps.len()] == self.steps[..]
    }

    /// Whether `self` and `other` overlap (one contains the other, §6.3).
    pub fn overlaps(&self, other: &RuntimePlace) -> bool {
        self.contains(other) || other.contains(self)
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Value {
    Bool(bool),
    Int(Int),
    String(String),
    Struct {
        ty: StructId,
        name: String,
        fields: Vec<Value>,
    },
    Variant {
        ty: VariantId,
        name: String,
        constructor: usize,
        constructor_name: String,
        fields: Vec<Value>,
    },
    Vector(Vec<Value>),
    Map(BTreeMap<Value, Value>),
    Resource {
        ty: ResourceId,
        name: String,
        id: u64,
    },
    Outcome {
        ty: OutcomeId,
        alternative: usize,
        alternative_name: String,
        payload: Vec<Value>,
    },
    Ref {
        mode: BorrowMode,
        place: RuntimePlace,
        tag: TagId,
    },
    TaskSet(TaskSetId),
}

/// The scope of a place that a host names within one of its arguments. No
/// scope of a run has this number.
pub const HOST_SCOPE: ScopeId = ScopeId::MAX;

impl Value {
    /// A borrow as a host answers it ([E-Extern]): the place `steps` within
    /// its argument number `argument`. A host sees values and no slots, so
    /// it names the place and the semantics makes the reborrow ([B3]).
    pub fn within(mode: BorrowMode, argument: usize, steps: Vec<RuntimeStep>) -> Value {
        Value::Ref {
            mode,
            place: RuntimePlace {
                scope: HOST_SCOPE,
                var: argument,
                steps,
            },
            tag: 0,
        }
    }
}

/// The borrow among the arguments of a host call that the place `named` by
/// the host lies within, and that place in the store. The steps of `named`
/// first go through the fields of a view to a borrow that it holds, and
/// then into what that borrow refers to.
pub(crate) fn lent_within(
    arguments: &[Value],
    named: &RuntimePlace,
) -> Result<(BorrowMode, RuntimePlace, TagId), String> {
    let Some(mut current) = arguments.get(named.var) else {
        return Err(format!("argument {} does not exist", named.var));
    };
    let mut steps = named.steps.as_slice();
    loop {
        match current {
            Value::Ref { mode, place, tag } => {
                let mut lent = place.clone();
                lent.steps.extend(steps.iter().cloned());
                return Ok((*mode, lent, *tag));
            }
            Value::Struct { fields, .. } => {
                let Some((RuntimeStep::Field(index), rest)) = steps.split_first() else {
                    return Err(format!("argument {} is not a borrow", named.var));
                };
                let Some(field) = fields.get(*index) else {
                    return Err(format!("argument {} has no field {index}", named.var));
                };
                current = field;
                steps = rest;
            }
            _ => return Err(format!("argument {} is not a borrow", named.var)),
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Bool(value) => write!(formatter, "{value}"),
            Value::Int(value) => write!(formatter, "{value}"),
            Value::String(value) => write!(formatter, "\"{}\"", escape_string(value)),
            Value::Struct { name, fields, .. } => {
                write!(formatter, "{name} {{{}}}", list(fields))
            }
            Value::Variant {
                name,
                constructor_name,
                fields,
                ..
            } => {
                write!(formatter, "{name}.{constructor_name} {{{}}}", list(fields))
            }
            Value::Vector(items) => write!(formatter, "[{}]", list(items)),
            Value::Map(entries) => {
                if entries.is_empty() {
                    formatter.write_str("∅")
                } else {
                    let parts: Vec<String> =
                        entries.iter().map(|(k, v)| format!("{k} ↦ {v}")).collect();
                    write!(formatter, "{{{}}}", parts.join(", "))
                }
            }
            Value::Resource { name, id, .. } => write!(formatter, "{name}#{id}"),
            Value::Outcome {
                alternative_name,
                payload,
                ..
            } => write!(
                formatter,
                "outcome.{alternative_name} {{{}}}",
                list(payload)
            ),
            Value::Ref { mode, place, .. } if place.scope == HOST_SCOPE => {
                let sign = match mode {
                    BorrowMode::Shared => "&",
                    BorrowMode::Exclusive => "&~",
                };
                write!(formatter, "{sign}argument#{}", place.var)?;
                for step in &place.steps {
                    match step {
                        RuntimeStep::Field(index) => write!(formatter, ".{index}")?,
                        RuntimeStep::Index(index) => write!(formatter, "[{index}]")?,
                        RuntimeStep::VariantField(_, index) => write!(formatter, ".{index}")?,
                        RuntimeStep::MapValue(key) => write!(formatter, "[{key}]")?,
                        RuntimeStep::MapKey(key) => write!(formatter, "[key {key}]")?,
                    }
                }
                Ok(())
            }
            Value::Ref { mode, tag, .. } => match mode {
                BorrowMode::Shared => write!(formatter, "&ref#{tag}"),
                BorrowMode::Exclusive => write!(formatter, "&~ref#{tag}"),
            },
            Value::TaskSet(id) => write!(formatter, "tasks#{id}"),
        }
    }
}

pub fn list(values: &[Value]) -> String {
    values
        .iter()
        .map(Value::to_string)
        .collect::<Vec<_>>()
        .join(", ")
}

/// The parameters of a run that the program text does not fix.
#[derive(Clone, Debug)]
pub struct Config {
    /// The greatest `usize`. The fact logic bounds it between `2^32 - 1` and
    /// `2^64 - 1` and proves for every value between ([A2]); a run has one.
    pub usize_max: Int,
    /// The number of steps after which a run is reported as not ending.
    pub fuel: u64,
}

impl Default for Config {
    fn default() -> Config {
        Config {
            usize_max: Int::power_of_two(64).minus(&Int::from_u64(1)),
            fuel: 1_000_000,
        }
    }
}

impl Config {
    pub fn with_usize_bits(bits: u32) -> Config {
        Config {
            usize_max: Int::power_of_two(bits).minus(&Int::from_u64(1)),
            ..Config::default()
        }
    }

    pub fn fits(&self, value: &Value, ty: &Type) -> bool {
        if let (Value::Ref { mode, .. }, Type::Ref(exp_mode, _)) = (value, ty) {
            return mode == exp_mode;
        }
        match (value, ty.deref_type()) {
            (Value::Bool(_), Type::Bool) => true,
            (Value::Int(value), Type::Int(ty)) => {
                let (least, greatest) = ty.bounds(&self.usize_max);
                *value >= least && *value <= greatest
            }
            (Value::String(_), Type::String) => true,
            (Value::Struct { ty: sid, .. }, Type::Struct(exp_sid, _)) => sid == exp_sid,
            (Value::Variant { ty: vid, .. }, Type::Variant(exp_vid, _)) => vid == exp_vid,
            (Value::Vector(items), Type::Vector(elem_ty)) => {
                items.iter().all(|item| self.fits(item, elem_ty))
            }
            (Value::Map(entries), Type::Map(k_ty, v_ty)) => entries
                .iter()
                .all(|(k, v)| self.fits(k, k_ty) && self.fits(v, v_ty)),
            (Value::Resource { ty: rid, .. }, Type::Resource(exp_rid, _)) => rid == exp_rid,
            (Value::Outcome { ty: oid, .. }, Type::Outcome(exp_oid, _)) => oid == exp_oid,
            _ => false,
        }
    }

    pub fn fits_in_program(&self, program: &Program, value: &Value, ty: &Type) -> bool {
        if let (Value::Ref { mode, .. }, Type::Ref(exp_mode, _)) = (value, ty) {
            return mode == exp_mode;
        }
        match (value, ty.deref_type()) {
            (Value::Bool(_), Type::Bool) => true,
            (Value::Int(value), Type::Int(ty)) => {
                let (least, greatest) = ty.bounds(&self.usize_max);
                *value >= least && *value <= greatest
            }
            (Value::String(_), Type::String) => true,
            (
                Value::Struct {
                    ty: sid, fields, ..
                },
                Type::Struct(exp_sid, _),
            ) if sid == exp_sid => {
                let st = &program.structs[*sid];
                fields.len() == st.fields.len()
                    && fields
                        .iter()
                        .zip(&st.fields)
                        .all(|(v, f)| self.fits_in_program(program, v, &f.ty))
            }
            (
                Value::Variant {
                    ty: vid,
                    constructor,
                    fields,
                    ..
                },
                Type::Variant(exp_vid, _),
            ) if vid == exp_vid => {
                let var = &program.variants[*vid];
                let Some(ctor) = var.constructors.get(*constructor) else {
                    return false;
                };
                fields.len() == ctor.fields.len()
                    && fields
                        .iter()
                        .zip(&ctor.fields)
                        .all(|(v, f)| self.fits_in_program(program, v, &f.ty))
            }
            (Value::Vector(items), Type::Vector(elem_ty)) => items
                .iter()
                .all(|item| self.fits_in_program(program, item, elem_ty)),
            (Value::Map(entries), Type::Map(k_ty, v_ty)) => entries.iter().all(|(k, v)| {
                self.fits_in_program(program, k, k_ty) && self.fits_in_program(program, v, v_ty)
            }),
            (Value::Resource { ty: rid, .. }, Type::Resource(exp_rid, _)) => rid == exp_rid,
            (
                Value::Outcome {
                    ty: oid,
                    alternative,
                    payload,
                    ..
                },
                Type::Outcome(exp_oid, _),
            ) if oid == exp_oid => {
                let oc = &program.outcomes[*oid];
                let Some(alt) = oc.alternatives.get(*alternative) else {
                    return false;
                };
                payload.len() == alt.fields.len()
                    && payload
                        .iter()
                        .zip(&alt.fields)
                        .all(|(v, f)| self.fits_in_program(program, v, &f.ty))
            }
            _ => false,
        }
    }
}

/// One step of the host that had an effect ([E-Extern], [E-Unwind]).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Event {
    pub control: String,
    pub arguments: Vec<Value>,
    pub alternative: String,
    pub payload: Vec<Value>,
}

impl fmt::Display for Event {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "{}({}) -> {} {{{}}}",
            self.control,
            list(&self.arguments),
            self.alternative,
            list(&self.payload)
        )
    }
}

/// A stuck configuration: which row of the table of section 6.10, the clause
/// that has no successor, and where.
#[derive(Clone, Debug)]
pub struct Stuck {
    pub state: u8,
    pub clause: &'static str,
    pub control: String,
    pub line: u32,
    pub detail: String,
}

/// How an execution ends ([6.11]), and the ways a run can fail to be one.
#[derive(Clone, Debug)]
pub enum End {
    Done {
        alternative: String,
        payload: Vec<Value>,
    },
    /// A fault unwound out of the entry control ([E-Root]).
    Faulted(String),
    /// The entry control ended the execution with a status
    /// ([E-Contingency], `terminate n`).
    Terminated(u8),
    Stuck(Stuck),
    /// The host broke a contract ([E-Host]). Not a stuck state.
    HostViolation(String),
    /// The host of this run had no answer. A defect of the test, not of the
    /// program.
    HostFailed(String),
    /// The fuel ran out. The instrumented profile's stand-in for divergence.
    OutOfFuel,
    /// The entry or its arguments do not start an execution (section 8).
    NotAnExecution(String),
}

impl fmt::Display for End {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            End::Done {
                alternative,
                payload,
            } => {
                write!(formatter, "done {alternative} {{{}}}", list(payload))
            }
            End::Faulted(message) => {
                write!(formatter, "faulted \"{}\"", escape_string(message))
            }
            End::Terminated(status) => write!(formatter, "terminated {status}"),
            End::Stuck(stuck) => write!(
                formatter,
                "stuck X{} {} at {}:{}: {}",
                stuck.state, stuck.clause, stuck.control, stuck.line, stuck.detail
            ),
            End::HostViolation(detail) => write!(formatter, "violation: {detail}"),
            End::HostFailed(detail) => write!(formatter, "host-failed: {detail}"),
            End::OutOfFuel => formatter.write_str("fuel"),
            End::NotAnExecution(detail) => write!(formatter, "not-an-execution: {detail}"),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Run {
    pub end: End,
    pub trace: Vec<Event>,
    pub steps: u64,
    /// How often each rule of the semantics was applied, by clause.
    pub rules: BTreeMap<&'static str, u64>,
}

struct Fail {
    state: u8,
    clause: &'static str,
    detail: String,
}

fn fail<T>(state: u8, clause: &'static str, detail: impl Into<String>) -> Result<T, Fail> {
    Err(Fail {
        state,
        clause,
        detail: detail.into(),
    })
}

trait Env {
    fn get(&self, var: VarRef) -> Result<Value, Fail>;
    fn get_old(&self, index: usize) -> Result<Value, Fail>;
    fn get_task_count(&self, _var: VarId) -> Result<usize, Fail> {
        fail(10, "E-Formula", "`count` is only available inside a body")
    }
}

/// The parameters of a signature and the payload of one alternative.
struct SignatureEnv<'a> {
    parameters: &'a [Value],
    old_parameters: &'a [Value],
    fields: &'a [Value],
}

impl Env for SignatureEnv<'_> {
    fn get(&self, var: VarRef) -> Result<Value, Fail> {
        let value = match var {
            VarRef::Parameter(index) => self.parameters.get(index),
            VarRef::Field(index) => self.fields.get(index),
            VarRef::Local(_) => None,
        };
        match value {
            Some(value) => Ok(value.clone()),
            None => fail(
                10,
                "E-Formula",
                "a signature refers to a name it does not have",
            ),
        }
    }

    fn get_old(&self, index: usize) -> Result<Value, Fail> {
        match self.old_parameters.get(index) {
            Some(value) => Ok(value.clone()),
            None => fail(
                10,
                "E-Formula",
                "a signature refers to an old parameter it does not have",
            ),
        }
    }
}

/// A slot in a scope (`docs/v2/core.md` section 6.1): available with value `v`,
/// or moved (`◌`).
#[derive(Clone, Debug)]
enum Slot {
    Available(Value),
    Moved,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum TagMode {
    Owner,
    Shared,
    Exclusive,
}

#[derive(Clone, Debug)]
struct Tag {
    mode: TagMode,
    place: RuntimePlace,
    parent: Option<TagId>,
    alive: bool,
}

/// The borrow tag table (`docs/v2/core.md` section 6.3, `[B1]`–`[B5]`).
/// Tag IDs are 1-based indices into `tags` (index 0 is a dummy sentinel).
struct TagTable {
    tags: Vec<Tag>,
}

impl TagTable {
    fn new() -> TagTable {
        TagTable {
            tags: vec![Tag {
                mode: TagMode::Owner,
                place: RuntimePlace::root(0, 0),
                parent: None,
                alive: false,
            }],
        }
    }

    fn new_owner(&mut self, scope: ScopeId, var: VarId) -> TagId {
        let id = self.tags.len() as TagId;
        self.tags.push(Tag {
            mode: TagMode::Owner,
            place: RuntimePlace::root(scope, var),
            parent: None,
            alive: true,
        });
        id
    }

    fn is_alive(&self, id: TagId) -> bool {
        self.tags.get(id as usize).is_some_and(|t| t.alive)
    }

    fn ancestors(&self, mut id: TagId) -> Vec<TagId> {
        let mut out = Vec::new();
        while id != 0 {
            out.push(id);
            match self.tags.get(id as usize).and_then(|t| t.parent) {
                Some(p) => id = p,
                None => break,
            }
        }
        out
    }

    /// Kills `root_id` and every descendant tag derived from it (`[B2]`, `[B4]`).
    fn kill_with_descendants(&mut self, root_id: TagId) {
        let start = root_id as usize;
        if start == 0 || start >= self.tags.len() {
            return;
        }
        self.tags[start].alive = false;
        // Because every child tag has id > parent id, one forward sweep kills all descendants.
        for i in (start + 1)..self.tags.len() {
            if self.tags[i].alive
                && let Some(p) = self.tags[i].parent
                && !self.tags[p as usize].alive
            {
                self.tags[i].alive = false;
            }
        }
    }

    /// `[B1]` + `[B2]`: checks `tag_id` for a read or write access to `place`,
    /// then invalidates conflicting non-ancestor live tags and their descendants.
    fn access(&mut self, tag_id: TagId, place: &RuntimePlace, is_write: bool) -> Result<(), Fail> {
        let Some(tag) = self.tags.get(tag_id as usize).cloned() else {
            return fail(4, "B1", "access through unknown borrow tag");
        };
        if !tag.alive {
            return fail(
                4,
                "B1",
                "borrow tag is no longer alive (use after invalidation or scope end)",
            );
        }
        if !tag.place.contains(place) {
            return fail(
                4,
                "B1",
                "access through a borrow outside its borrowed place",
            );
        }
        if is_write && tag.mode == TagMode::Shared {
            return fail(4, "B1", "write access through a shared borrow");
        }
        let anc = self.ancestors(tag_id);
        let mut to_kill = Vec::new();
        for u in 1..self.tags.len() {
            let u_id = u as TagId;
            let entry = &self.tags[u];
            if !entry.alive || anc.contains(&u_id) {
                continue;
            }
            if !entry.place.overlaps(place) {
                continue;
            }
            if is_write || entry.mode == TagMode::Exclusive {
                to_kill.push(u_id);
            }
        }
        for u_id in to_kill {
            self.kill_with_descendants(u_id);
        }
        Ok(())
    }

    /// `[B3]`: creates a child borrow of `place` derived from `parent_tag`.
    fn create_borrow(
        &mut self,
        parent_tag: TagId,
        place: RuntimePlace,
        mode: BorrowMode,
    ) -> Result<TagId, Fail> {
        let is_write = mode == BorrowMode::Exclusive;
        self.access(parent_tag, &place, is_write)?;
        let id = self.tags.len() as TagId;
        self.tags.push(Tag {
            mode: match mode {
                BorrowMode::Shared => TagMode::Shared,
                BorrowMode::Exclusive => TagMode::Exclusive,
            },
            place,
            parent: Some(parent_tag),
            alive: true,
        });
        Ok(id)
    }
}

#[derive(Clone, Debug)]
enum ScopeKind {
    Normal,
    Loop,
    LexicalBoundary {
        site: SiteId,
        parent_pc: usize,
        captures: Vec<Value>,
        contingency_body: BodyId,
        contingency_vars: Vec<VarId>,
        message_var: Option<VarId>,
    },
    LexicalContingency {
        fault_message: String,
    },
}

/// One run of one body ([6.2]).
struct Scope {
    id: ScopeId,
    body: BodyId,
    pc: usize,
    slots: Vec<(VarId, Slot, TagId)>,
    history: Vec<(SiteId, usize)>,
    kind: ScopeKind,
}

#[derive(Clone, Debug)]
enum ActivationKind {
    Control(ControlId),
    Boundary {
        id: BoundaryId,
        in_contingency: Option<String>,
    },
}

/// One call of a control or named boundary.
struct Activation {
    kind: ActivationKind,
    /// Concrete entry argument snapshots (`old(y)` in contract conditions, [E-Formula]).
    arguments: Vec<Value>,
    /// The arguments that are or hold a borrow, as they were passed: the
    /// instrumented semantics keeps them so that a condition reads the value
    /// at completion through them whatever the body did with the parameter
    /// ([E-Formula], [E-Exit]).
    borrowed: Vec<Option<Value>>,
    scopes: Vec<Scope>,
}

struct TaskSet {
    owner_task: usize,
    owner_scope: ScopeId,
    members: Vec<usize>,
    done_queue: VecDeque<usize>,
}

enum TaskState {
    Ready,
    WaitingHost {
        callee: ControlId,
        arguments: Vec<Value>,
        concrete_args: Vec<Value>,
        consumed_resources: Vec<(ResourceId, u64)>,
    },
    WaitingNext {
        set_id: TaskSetId,
        set_var: VarId,
        prod_id: ControlId,
    },
    WaitingRun,
    Done {
        alternative: usize,
        payload: Vec<Value>,
    },
    Stopped,
}

struct Task {
    stack: Vec<Activation>,
    state: TaskState,
    member_of: Option<TaskSetId>,
    cancelled: bool,
    /// Effect allowances inherited from spawning or running ancestor activations ([E-Effect]).
    parent_allowances: Vec<Vec<String>>,
}

struct TaskRun {
    root_task: usize,
    caller_task: Option<usize>,
    tasks: Vec<usize>,
}

fn find_slot_ref<'a>(
    entry_slots: &'a [(VarId, Slot, TagId)],
    stack: &'a [Activation],
    tasks: &'a [Task],
    place: &RuntimePlace,
) -> Option<&'a Slot> {
    if place.scope == 0 {
        return entry_slots
            .iter()
            .find(|(v, _, _)| *v == place.var)
            .map(|(_, s, _)| s);
    }
    for act in stack.iter().rev() {
        for scope in act.scopes.iter().rev() {
            if scope.id == place.scope {
                return scope
                    .slots
                    .iter()
                    .find(|(v, _, _)| *v == place.var)
                    .map(|(_, s, _)| s);
            }
        }
    }
    for task in tasks {
        for act in task.stack.iter().rev() {
            for scope in act.scopes.iter().rev() {
                if scope.id == place.scope {
                    return scope
                        .slots
                        .iter()
                        .find(|(v, _, _)| *v == place.var)
                        .map(|(_, s, _)| s);
                }
            }
        }
    }
    None
}

fn read_place_from_state(
    entry_slots: &[(VarId, Slot, TagId)],
    stack: &[Activation],
    tasks: &[Task],
    place: &RuntimePlace,
) -> Result<Value, Fail> {
    let Some(slot) = find_slot_ref(entry_slots, stack, tasks, place) else {
        return fail(4, "B1", "borrow refers to a scope that has ended");
    };
    let Slot::Available(mut current) = slot.clone() else {
        return fail(2, "E-Var", "borrowed slot has been moved");
    };
    for step in &place.steps {
        match step {
            RuntimeStep::Field(fidx) => {
                let Value::Struct { mut fields, .. } = current else {
                    return fail(10, "E-Field", "field access on non-struct");
                };
                current = fields.swap_remove(*fidx);
            }
            RuntimeStep::Index(idx) => {
                let Value::Vector(mut items) = current else {
                    return fail(10, "E-Index", "index on non-vector");
                };
                if *idx >= items.len() {
                    return fail(
                        7,
                        "E-Index",
                        format!("index {idx} is out of bounds for length {}", items.len()),
                    );
                }
                current = items.swap_remove(*idx);
            }
            RuntimeStep::VariantField(cidx, fidx) => {
                let Value::Variant {
                    constructor,
                    mut fields,
                    ..
                } = current
                else {
                    return fail(10, "E-Outcome", "variant field access on non-variant");
                };
                if constructor != *cidx || *fidx >= fields.len() {
                    return fail(4, "B1", "variant constructor changed under borrow");
                }
                current = fields.swap_remove(*fidx);
            }
            RuntimeStep::MapValue(key) => {
                let Value::Map(mut entries) = current else {
                    return fail(10, "E-Extern", "map lookup on non-map");
                };
                let Some(val) = entries.remove(key) else {
                    return fail(4, "B1", "map key removed under borrow");
                };
                current = val;
            }
            RuntimeStep::MapKey(key) => {
                let Value::Map(entries) = current else {
                    return fail(10, "E-Extern", "map key access on non-map");
                };
                if !entries.contains_key(key) {
                    return fail(4, "B1", "map key removed under borrow");
                }
                current = key.clone();
            }
        }
    }
    Ok(current)
}

/// Recursively dereferences `Value::Ref` without touching tags (`[E-Formula]`).
fn deref_value_formula(
    entry_slots: &[(VarId, Slot, TagId)],
    stack: &[Activation],
    tasks: &[Task],
    value: &Value,
) -> Result<Value, Fail> {
    match value {
        Value::Ref { place, .. } => {
            let inner = read_place_from_state(entry_slots, stack, tasks, place)?;
            deref_value_formula(entry_slots, stack, tasks, &inner)
        }
        Value::Struct { ty, name, fields } => {
            let mut out = Vec::with_capacity(fields.len());
            for f in fields {
                out.push(deref_value_formula(entry_slots, stack, tasks, f)?);
            }
            Ok(Value::Struct {
                ty: *ty,
                name: name.clone(),
                fields: out,
            })
        }
        Value::Variant {
            ty,
            name,
            constructor,
            constructor_name,
            fields,
        } => {
            let mut out = Vec::with_capacity(fields.len());
            for f in fields {
                out.push(deref_value_formula(entry_slots, stack, tasks, f)?);
            }
            Ok(Value::Variant {
                ty: *ty,
                name: name.clone(),
                constructor: *constructor,
                constructor_name: constructor_name.clone(),
                fields: out,
            })
        }
        other => Ok(other.clone()),
    }
}

struct ActivationEnv<'a> {
    body: &'a ControlBody,
    entry_slots: &'a [(VarId, Slot, TagId)],
    stack: &'a [Activation],
    tasks: &'a [Task],
    task_sets: &'a [TaskSet],
}

impl Env for ActivationEnv<'_> {
    /// [E-Formula]: reads current values through borrows and changes no tag.
    fn get(&self, var: VarRef) -> Result<Value, Fail> {
        let VarRef::Local(id) = var else {
            return fail(10, "E-Var", "a body refers to a name of a signature");
        };
        let activation = self.stack.last().expect("an activation");
        for scope in activation.scopes.iter().rev() {
            if let Some((_, slot, _)) = scope.slots.iter().find(|(slot, _, _)| *slot == id) {
                return match slot {
                    Slot::Available(value) => {
                        deref_value_formula(self.entry_slots, self.stack, self.tasks, value)
                    }
                    Slot::Moved => fail(
                        2,
                        "E-Var",
                        format!(
                            "`{}` has been moved on this history",
                            self.body.vars[id].name
                        ),
                    ),
                };
            }
        }
        fail(
            2,
            "E-Var",
            format!("`{}` has no value on this history", self.body.vars[id].name),
        )
    }

    fn get_old(&self, index: usize) -> Result<Value, Fail> {
        let activation = self.stack.last().expect("an activation");
        match activation.arguments.get(index) {
            Some(v) => Ok(v.clone()),
            None => fail(10, "E-Formula", "no entry argument for `old`"),
        }
    }

    fn get_task_count(&self, var: VarId) -> Result<usize, Fail> {
        let activation = self.stack.last().expect("an activation");
        for scope in activation.scopes.iter().rev() {
            if let Some((_, slot, _)) = scope.slots.iter().find(|(s, _, _)| *s == var) {
                return match slot {
                    Slot::Available(Value::TaskSet(set_id)) => {
                        Ok(self.task_sets[*set_id as usize].members.len())
                    }
                    Slot::Available(_) => fail(10, "E-Formula", "non-task-set in `count`"),
                    Slot::Moved => fail(
                        2,
                        "E-Var",
                        format!(
                            "`{}` has been moved on this history",
                            self.body.vars[var].name
                        ),
                    ),
                };
            }
        }
        fail(
            2,
            "E-Var",
            format!(
                "`{}` has no value on this history",
                self.body.vars[var].name
            ),
        )
    }
}

struct Evaluator<'a> {
    program: &'a Program,
    config: &'a Config,
}

fn integer(value: Value) -> Result<Int, Fail> {
    match value {
        Value::Int(value) => Ok(value),
        _ => fail(
            10,
            "E-Arith",
            "a non-integer stands where an integer is needed",
        ),
    }
}

fn boolean(value: Value) -> Result<bool, Fail> {
    match value {
        Value::Bool(value) => Ok(value),
        _ => fail(10, "E-Test", "a non-bool stands where a bool is needed"),
    }
}

fn compare(comparison: Comparison, left: &Value, right: &Value) -> Result<bool, Fail> {
    Ok(match (left, right) {
        (Value::Int(a), Value::Int(b)) => match comparison {
            Comparison::Equal => a == b,
            Comparison::NotEqual => a != b,
            Comparison::Less => a < b,
            Comparison::LessEqual => a <= b,
            Comparison::Greater => a > b,
            Comparison::GreaterEqual => a >= b,
        },
        (a, b) => match comparison {
            Comparison::Equal => a == b,
            Comparison::NotEqual => a != b,
            _ => return fail(10, "E-Arith", "values of this type are not ordered"),
        },
    })
}

fn sign(operator: Arithmetic) -> &'static str {
    match operator {
        Arithmetic::Add => "+",
        Arithmetic::Subtract => "-",
        Arithmetic::Multiply => "*",
        Arithmetic::Divide => "÷",
        Arithmetic::Remainder => "mod",
    }
}

fn value_len(value: &Value) -> Result<Int, Fail> {
    match value {
        Value::Vector(items) => Ok(Int::from_u64(items.len() as u64)),
        Value::String(s) => Ok(Int::from_u64(s.len() as u64)),
        Value::Map(entries) => Ok(Int::from_u64(entries.len() as u64)),
        _ => fail(10, "E-Arith", "`len` applied to a value without a length"),
    }
}

impl Evaluator<'_> {
    /// `e ⇓ v` in a pure read context (such as inside a function body).
    fn value(&self, expr: &Expr, env: &dyn Env) -> Result<Value, Fail> {
        Ok(match expr {
            Expr::Boolean(value) => Value::Bool(*value),
            Expr::Integer(value, _) => Value::Int(value.clone()),
            Expr::String(value) => Value::String(value.clone()),
            Expr::Var(var, _) => env.get(*var)?,
            Expr::Old(idx, _) => env.get_old(*idx)?,
            Expr::Move(inner, _) => self.value(inner, env)?,
            Expr::Borrow(_, place, _) => {
                let mut current = env.get(VarRef::Local(place.root))?;
                for step in &place.steps {
                    match step {
                        PlaceStep::Field(_, fidx, _) => {
                            let Value::Struct { mut fields, .. } = current else {
                                return fail(10, "E-Field", "field access on non-struct");
                            };
                            current = fields.swap_remove(*fidx);
                        }
                        PlaceStep::Index(idx_expr, _) => {
                            let Value::Vector(mut items) = current else {
                                return fail(10, "E-Index", "index on non-vector");
                            };
                            let idx = integer(self.value(idx_expr, env)?)?;
                            let Some(i) = idx
                                .to_i128()
                                .filter(|&i| i >= 0 && (i as usize) < items.len())
                            else {
                                return fail(
                                    7,
                                    "E-Index",
                                    format!(
                                        "index {idx} is out of bounds for length {}",
                                        items.len()
                                    ),
                                );
                            };
                            current = items.swap_remove(i as usize);
                        }
                    }
                }
                current
            }
            Expr::Field(base, _, fidx, _) => {
                let base_val = self.value(base, env)?;
                let Value::Struct { mut fields, .. } = base_val else {
                    return fail(10, "E-Field", "field access on non-struct");
                };
                fields.swap_remove(*fidx)
            }
            Expr::Index(base, idx_expr, _) => {
                let base_val = self.value(base, env)?;
                let Value::Vector(mut items) = base_val else {
                    return fail(10, "E-Index", "index on non-vector");
                };
                let idx = integer(self.value(idx_expr, env)?)?;
                let Some(i) = idx
                    .to_i128()
                    .filter(|&i| i >= 0 && (i as usize) < items.len())
                else {
                    return fail(
                        7,
                        "E-Index",
                        format!("index {idx} is out of bounds for length {}", items.len()),
                    );
                };
                items.swap_remove(i as usize)
            }
            Expr::Struct(sid, fields, _) => {
                let mut vals = Vec::with_capacity(fields.len());
                for f in fields {
                    vals.push(self.value(f, env)?);
                }
                Value::Struct {
                    ty: *sid,
                    name: self.program.structs[*sid].name.clone(),
                    fields: vals,
                }
            }
            Expr::Variant(vid, cidx, fields, _) => {
                let mut vals = Vec::with_capacity(fields.len());
                for f in fields {
                    vals.push(self.value(f, env)?);
                }
                let vdef = &self.program.variants[*vid];
                Value::Variant {
                    ty: *vid,
                    name: vdef.name.clone(),
                    constructor: *cidx,
                    constructor_name: vdef.constructors[*cidx].name.clone(),
                    fields: vals,
                }
            }
            Expr::Vector(items, _) => {
                let mut vals = Vec::with_capacity(items.len());
                for item in items {
                    vals.push(self.value(item, env)?);
                }
                Value::Vector(vals)
            }
            Expr::EmptyMap(_) => Value::Map(BTreeMap::new()),
            Expr::Len(place) => Value::Int(value_len(&self.value(place, env)?)?),
            Expr::Clone(place, _) => self.value(place, env)?,
            Expr::Trim(arg) => {
                let Value::String(s) = self.value(arg, env)? else {
                    return fail(10, "E-Fn", "`trim` expects a string");
                };
                Value::String(s.trim().to_string())
            }
            Expr::Not(operand) => Value::Bool(!boolean(self.value(operand, env)?)?),
            Expr::Negate(operand, ty) => {
                let operand = integer(self.value(operand, env)?)?;
                let result = operand.negate();
                if !self
                    .config
                    .fits(&Value::Int(result.clone()), &Type::Int(*ty))
                {
                    return fail(
                        7,
                        "E-Arith",
                        format!("-{operand} = {result} is not a value of {}", ty.name()),
                    );
                }
                Value::Int(result)
            }
            Expr::Arithmetic(operator, left, right, ty) => {
                let left = integer(self.value(left, env)?)?;
                let right = integer(self.value(right, env)?)?;
                let result = match operator {
                    Arithmetic::Add => left.plus(&right),
                    Arithmetic::Subtract => left.minus(&right),
                    Arithmetic::Multiply => left.times(&right),
                    Arithmetic::Divide | Arithmetic::Remainder => {
                        let Some((quotient, remainder)) = left.divide(&right) else {
                            return fail(
                                7,
                                "E-Arith",
                                format!("{left} {} 0: the divisor is zero", sign(*operator)),
                            );
                        };
                        if *operator == Arithmetic::Divide {
                            quotient
                        } else {
                            remainder
                        }
                    }
                };
                if !self
                    .config
                    .fits(&Value::Int(result.clone()), &Type::Int(*ty))
                {
                    return fail(
                        7,
                        "E-Arith",
                        format!(
                            "{left} {} {right} = {result} is not a value of {}",
                            sign(*operator),
                            ty.name()
                        ),
                    );
                }
                Value::Int(result)
            }
            Expr::Compare(comparison, left, right) => {
                let left = self.value(left, env)?;
                let right = self.value(right, env)?;
                Value::Bool(compare(*comparison, &left, &right)?)
            }
            Expr::And(left, right) => {
                Value::Bool(boolean(self.value(left, env)?)? && boolean(self.value(right, env)?)?)
            }
            Expr::Or(left, right) => {
                Value::Bool(boolean(self.value(left, env)?)? || boolean(self.value(right, env)?)?)
            }
            Expr::Call(id, arguments, _) => {
                let function = &self.program.functions[*id];
                let mut values = Vec::new();
                for argument in arguments {
                    values.push(self.value(argument, env)?);
                }
                let inner = SignatureEnv {
                    parameters: &values,
                    old_parameters: &values,
                    fields: &[],
                };
                if let Some(precondition) = &function.precondition
                    && !self.holds(precondition, &inner)?
                {
                    return fail(
                        7,
                        "E-Fn",
                        format!(
                            "the precondition of `{}` is false for ({})",
                            function.name,
                            list(&values)
                        ),
                    );
                }
                self.value(&function.body, &inner)?
            }
            Expr::TasksEmpty(_, _) => {
                return fail(10, "E-Fn", "`tasks⟨f⟩()` cannot be evaluated in a function");
            }
            Expr::Count(var) => Value::Int(Int::from_u64(env.get_task_count(*var)? as u64)),
        })
    }

    /// The value of a term of a formula ([E-Formula]): over the mathematical
    /// integers, total, and with no obligation of its own.
    fn term(&self, expr: &Expr, env: &dyn Env) -> Result<Value, Fail> {
        Ok(match expr {
            Expr::Boolean(value) => Value::Bool(*value),
            Expr::Integer(value, _) => Value::Int(value.clone()),
            Expr::String(value) => Value::String(value.clone()),
            Expr::Var(var, _) => env.get(*var)?,
            Expr::Old(idx, _) => env.get_old(*idx)?,
            Expr::Move(inner, _) => self.term(inner, env)?,
            Expr::Borrow(_, place, _) => {
                let mut current = env.get(VarRef::Local(place.root))?;
                for step in &place.steps {
                    match step {
                        PlaceStep::Field(_, fidx, _) => {
                            if let Value::Struct { mut fields, .. } = current {
                                current = fields.swap_remove(*fidx);
                            }
                        }
                        PlaceStep::Index(idx_expr, elem_ty) => {
                            if let Value::Vector(mut items) = current {
                                let idx = integer(self.term(idx_expr, env)?)?;
                                current = match idx
                                    .to_i128()
                                    .filter(|&i| i >= 0 && (i as usize) < items.len())
                                {
                                    Some(i) => items.swap_remove(i as usize),
                                    None => self.default_formula_value(elem_ty),
                                };
                            }
                        }
                    }
                }
                current
            }
            Expr::Field(base, _, fidx, _) => {
                let Value::Struct { mut fields, .. } = self.term(base, env)? else {
                    return fail(10, "E-Formula", "field access on non-struct in formula");
                };
                fields.swap_remove(*fidx)
            }
            Expr::Index(base, idx_expr, elem_ty) => {
                let Value::Vector(mut items) = self.term(base, env)? else {
                    return fail(10, "E-Formula", "index on non-vector in formula");
                };
                let idx = integer(self.term(idx_expr, env)?)?;
                // [E-Formula]: an out-of-range index in a formula denotes a
                // deterministic value of the element type.
                match idx
                    .to_i128()
                    .filter(|&i| i >= 0 && (i as usize) < items.len())
                {
                    Some(i) => items.swap_remove(i as usize),
                    None => self.default_formula_value(elem_ty),
                }
            }
            Expr::Struct(sid, fields, _) => {
                let mut vals = Vec::with_capacity(fields.len());
                for f in fields {
                    vals.push(self.term(f, env)?);
                }
                Value::Struct {
                    ty: *sid,
                    name: self.program.structs[*sid].name.clone(),
                    fields: vals,
                }
            }
            Expr::Variant(vid, cidx, fields, _) => {
                let mut vals = Vec::with_capacity(fields.len());
                for f in fields {
                    vals.push(self.term(f, env)?);
                }
                let vdef = &self.program.variants[*vid];
                Value::Variant {
                    ty: *vid,
                    name: vdef.name.clone(),
                    constructor: *cidx,
                    constructor_name: vdef.constructors[*cidx].name.clone(),
                    fields: vals,
                }
            }
            Expr::Vector(items, _) => {
                let mut vals = Vec::with_capacity(items.len());
                for item in items {
                    vals.push(self.term(item, env)?);
                }
                Value::Vector(vals)
            }
            Expr::EmptyMap(_) => Value::Map(BTreeMap::new()),
            Expr::Len(place) => Value::Int(value_len(&self.term(place, env)?)?),
            Expr::Clone(place, _) => self.term(place, env)?,
            Expr::Trim(arg) => {
                let Value::String(s) = self.term(arg, env)? else {
                    return fail(10, "E-Formula", "`trim` expects a string");
                };
                Value::String(s.trim().to_string())
            }
            Expr::Not(operand) => Value::Bool(!boolean(self.term(operand, env)?)?),
            Expr::Negate(operand, _) => Value::Int(integer(self.term(operand, env)?)?.negate()),
            Expr::Arithmetic(operator, left, right, _) => {
                let left = integer(self.term(left, env)?)?;
                let right = integer(self.term(right, env)?)?;
                Value::Int(match operator {
                    Arithmetic::Add => left.plus(&right),
                    Arithmetic::Subtract => left.minus(&right),
                    Arithmetic::Multiply => left.times(&right),
                    Arithmetic::Divide => left.divide(&right).map_or(Int::zero(), |pair| pair.0),
                    Arithmetic::Remainder => {
                        left.divide(&right).map_or(left.clone(), |pair| pair.1)
                    }
                })
            }
            Expr::Compare(comparison, left, right) => {
                let left = self.term(left, env)?;
                let right = self.term(right, env)?;
                Value::Bool(compare(*comparison, &left, &right)?)
            }
            Expr::And(left, right) => {
                let left = boolean(self.term(left, env)?)?;
                let right = boolean(self.term(right, env)?)?;
                Value::Bool(left && right)
            }
            Expr::Or(left, right) => {
                let left = boolean(self.term(left, env)?)?;
                let right = boolean(self.term(right, env)?)?;
                Value::Bool(left || right)
            }
            Expr::Call(id, arguments, _) => {
                let mut values = Vec::new();
                for argument in arguments {
                    values.push(self.term(argument, env)?);
                }
                let inner = SignatureEnv {
                    parameters: &values,
                    old_parameters: &values,
                    fields: &[],
                };
                self.term(&self.program.functions[*id].body, &inner)?
            }
            Expr::TasksEmpty(_, _) => Value::TaskSet(0),
            Expr::Count(var) => Value::Int(Int::from_u64(env.get_task_count(*var)? as u64)),
        })
    }

    fn default_formula_value(&self, ty: &Type) -> Value {
        match ty.deref_type() {
            Type::Bool => Value::Bool(false),
            Type::Int(_) => Value::Int(Int::zero()),
            Type::String => Value::String(String::new()),
            Type::Struct(sid, name) => {
                let fields = self.program.structs[*sid]
                    .fields
                    .iter()
                    .map(|f| self.default_formula_value(&f.ty))
                    .collect();
                Value::Struct {
                    ty: *sid,
                    name: name.clone(),
                    fields,
                }
            }
            Type::Variant(vid, name) => {
                let ctor = &self.program.variants[*vid].constructors[0];
                let fields = ctor
                    .fields
                    .iter()
                    .map(|f| self.default_formula_value(&f.ty))
                    .collect();
                Value::Variant {
                    ty: *vid,
                    name: name.clone(),
                    constructor: 0,
                    constructor_name: ctor.name.clone(),
                    fields,
                }
            }
            Type::Vector(_) => Value::Vector(Vec::new()),
            Type::Map(_, _) => Value::Map(BTreeMap::new()),
            Type::Resource(rid, name) => Value::Resource {
                ty: *rid,
                name: name.clone(),
                id: 0,
            },
            Type::Outcome(oid, _) => {
                let alt = &self.program.outcomes[*oid].alternatives[0];
                let payload = alt
                    .fields
                    .iter()
                    .map(|f| self.default_formula_value(&f.ty))
                    .collect();
                Value::Outcome {
                    ty: *oid,
                    alternative: 0,
                    alternative_name: alt.name.clone(),
                    payload,
                }
            }
            _ => Value::Int(Int::zero()),
        }
    }

    fn holds(&self, formula: &Expr, env: &dyn Env) -> Result<bool, Fail> {
        boolean(self.term(formula, env)?)
    }
}

struct Machine<'a> {
    program: &'a Program,
    config: &'a Config,
    host: &'a mut dyn Host,
    /// Synthetic owner slots (`ScopeId = 0`) for entry arguments passed by borrow or view.
    entry_slots: Vec<(VarId, Slot, TagId)>,
    /// Borrow tag table (`[B1]`–`[B5]`).
    tags: TagTable,
    next_scope_id: ScopeId,
    stack: Vec<Activation>,
    tasks: Vec<Task>,
    task_sets: Vec<TaskSet>,
    runs: Vec<TaskRun>,
    current_task: usize,
    has_turn: bool,
    turns_taken: u64,
    trace: Vec<Event>,
    steps: u64,
    rules: BTreeMap<&'static str, u64>,
    /// What each pure extern control answered, by its arguments ([E-Host]).
    answers: HashMap<(ControlId, Vec<Value>), (usize, Vec<Value>)>,
    /// Resource table: `(ResourceId, handle_id)` -> `true` while open, `false` once closed ([E-Resource]).
    resources: BTreeMap<(ResourceId, u64), bool>,
    /// Where the statement being run is, for the report of a stuck state.
    location: (String, u32),
}

/// What a step of the host leads to.
enum Answered {
    Completed(usize, Vec<Value>),
    Ended(End),
}

fn collect_resources(value: &Value, out: &mut Vec<(ResourceId, u64)>) {
    match value {
        Value::Resource { ty, id, .. } => out.push((*ty, *id)),
        Value::Struct { fields, .. }
        | Value::Variant { fields, .. }
        | Value::Vector(fields)
        | Value::Outcome {
            payload: fields, ..
        } => {
            for f in fields {
                collect_resources(f, out);
            }
        }
        Value::Map(entries) => {
            for (k, v) in entries {
                collect_resources(k, out);
                collect_resources(v, out);
            }
        }
        Value::Bool(_)
        | Value::Int(_)
        | Value::String(_)
        | Value::Ref { .. }
        | Value::TaskSet(_) => {}
    }
}

impl<'a> Machine<'a> {
    fn count(&mut self, clause: &'static str) {
        *self.rules.entry(clause).or_insert(0) += 1;
    }

    fn evaluator(&self) -> Evaluator<'a> {
        Evaluator {
            program: self.program,
            config: self.config,
        }
    }

    fn body(&self) -> &'a ControlBody {
        let act = self.stack.last().expect("an activation");
        match &act.kind {
            ActivationKind::Control(cid) => self.program.controls[*cid]
                .body
                .as_ref()
                .expect("a defined control"),
            ActivationKind::Boundary { id, in_contingency } => {
                if in_contingency.is_some() {
                    &self.program.boundaries[*id].contingency
                } else {
                    &self.program.boundaries[*id].body
                }
            }
        }
    }

    fn current_name(&self) -> String {
        let act = self.stack.last().expect("an activation");
        match &act.kind {
            ActivationKind::Control(cid) => self.program.controls[*cid].name.clone(),
            ActivationKind::Boundary { id, .. } => self.program.boundaries[*id].name.clone(),
        }
    }

    fn scope(&mut self) -> &mut Scope {
        self.stack
            .last_mut()
            .expect("an activation")
            .scopes
            .last_mut()
            .expect("a scope")
    }

    /// Whether `value` contains an open resource, captured outcome, or non-empty task set ([6.8]).
    fn contains_obligation(&self, value: &Value) -> bool {
        match value {
            Value::Resource { ty, id, .. } => {
                self.resources.get(&(*ty, *id)).copied().unwrap_or(false)
            }
            Value::Outcome { .. } => true,
            Value::TaskSet(set_id) => !self.task_sets[*set_id as usize].members.is_empty(),
            Value::Struct { fields, .. }
            | Value::Variant { fields, .. }
            | Value::Vector(fields) => fields.iter().any(|f| self.contains_obligation(f)),
            Value::Map(entries) => entries
                .iter()
                .any(|(k, v)| self.contains_obligation(k) || self.contains_obligation(v)),
            Value::Bool(_) | Value::Int(_) | Value::String(_) | Value::Ref { .. } => false,
        }
    }

    fn alloc_scope_id(&mut self) -> ScopeId {
        let id = self.next_scope_id;
        self.next_scope_id += 1;
        id
    }

    fn access_tag(
        &mut self,
        tag_id: TagId,
        place: &RuntimePlace,
        is_write: bool,
    ) -> Result<(), Fail> {
        self.tags.access(tag_id, place, is_write)?;
        self.count("B1");
        Ok(())
    }

    fn create_borrow_tag(
        &mut self,
        parent_tag: TagId,
        place: RuntimePlace,
        mode: BorrowMode,
    ) -> Result<TagId, Fail> {
        let tag = self.tags.create_borrow(parent_tag, place, mode)?;
        self.count("B3");
        Ok(tag)
    }

    fn read_place(&self, place: &RuntimePlace) -> Result<Value, Fail> {
        read_place_from_state(&self.entry_slots, &self.stack, &self.tasks, place)
    }

    /// [E-Extern]: a borrow in the payload of a host is a reborrow, by [B3],
    /// of a place within one of the arguments. The host named the place
    /// (`Value::within`); this makes the borrow, with a tag under the tag of
    /// the argument. An answer that names no such place is not a payload of
    /// the alternative, and the reason is returned ([E-Host]).
    fn lend(&mut self, arguments: &[Value], value: &mut Value, ty: &Type) -> Result<(), String> {
        match value {
            Value::Ref { mode, place, tag } if place.scope == HOST_SCOPE => {
                let Type::Ref(_, referent_ty) = ty else {
                    return Err("a borrow stands where the contract has a value".to_string());
                };
                let (lender, lent, parent) = lent_within(arguments, place)?;
                if *mode == BorrowMode::Exclusive && lender != BorrowMode::Exclusive {
                    return Err(format!(
                        "an exclusive borrow within argument {}, which was lent shared",
                        place.var
                    ));
                }
                let referent = self
                    .read_place(&lent)
                    .map_err(|_| format!("a place that is not within argument {}", place.var))?;
                if !self
                    .config
                    .fits_in_program(self.program, &referent, referent_ty)
                {
                    return Err(format!(
                        "a place within argument {} that holds no value of type {referent_ty}",
                        place.var
                    ));
                }
                let made = self
                    .tags
                    .create_borrow(parent, lent.clone(), *mode)
                    .map_err(|failure| failure.detail)?;
                self.count("B3");
                *place = lent;
                *tag = made;
                Ok(())
            }
            Value::Struct { ty: id, fields, .. } if self.program.structs[*id].is_view => {
                let program = self.program;
                for (field, definition) in fields.iter_mut().zip(&program.structs[*id].fields) {
                    self.lend(arguments, field, &definition.ty)?;
                }
                Ok(())
            }
            _ => Ok(()),
        }
    }

    fn deref_formula(&self, value: &Value) -> Result<Value, Fail> {
        deref_value_formula(&self.entry_slots, &self.stack, &self.tasks, value)
    }

    /// Recursively materializes any `Value::Ref` by performing a `[B1]` read
    /// access through its tag (used for pure function calls, host calls,
    /// traces, and final entry `Done` payloads).
    fn deref_checked(&mut self, value: &Value) -> Result<Value, Fail> {
        match value {
            Value::Ref { place, tag, .. } => {
                self.access_tag(*tag, place, false)?;
                let inner = self.read_place(place)?;
                self.deref_checked(&inner)
            }
            Value::Struct { ty, name, fields } => {
                let mut out = Vec::with_capacity(fields.len());
                for f in fields {
                    out.push(self.deref_checked(f)?);
                }
                Ok(Value::Struct {
                    ty: *ty,
                    name: name.clone(),
                    fields: out,
                })
            }
            Value::Variant {
                ty,
                name,
                constructor,
                constructor_name,
                fields,
            } => {
                let mut out = Vec::with_capacity(fields.len());
                for f in fields {
                    out.push(self.deref_checked(f)?);
                }
                Ok(Value::Variant {
                    ty: *ty,
                    name: name.clone(),
                    constructor: *constructor,
                    constructor_name: constructor_name.clone(),
                    fields: out,
                })
            }
            other => Ok(other.clone()),
        }
    }

    fn find_local_slot(&self, var: VarId) -> Result<(ScopeId, Slot, TagId), Fail> {
        let var_name = &self.body().vars[var].name;
        let activation = self.stack.last().expect("an activation");
        for scope in activation.scopes.iter().rev() {
            if let Some((_, slot, owner_tag)) = scope.slots.iter().find(|(s, _, _)| *s == var) {
                return Ok((scope.id, slot.clone(), *owner_tag));
            }
        }
        fail(
            2,
            "E-Var",
            format!("`{var_name}` has no value on this history"),
        )
    }

    fn slot_mut(&mut self, scope_id: ScopeId, var: VarId) -> Option<&mut Slot> {
        if scope_id == 0 {
            return self
                .entry_slots
                .iter_mut()
                .find(|(v, _, _)| *v == var)
                .map(|(_, s, _)| s);
        }
        for act in self.stack.iter_mut().rev() {
            for scope in act.scopes.iter_mut().rev() {
                if scope.id == scope_id {
                    return scope
                        .slots
                        .iter_mut()
                        .find(|(v, _, _)| *v == var)
                        .map(|(_, s, _)| s);
                }
            }
        }
        for task in &mut self.tasks {
            for act in task.stack.iter_mut().rev() {
                for scope in act.scopes.iter_mut().rev() {
                    if scope.id == scope_id {
                        return scope
                            .slots
                            .iter_mut()
                            .find(|(v, _, _)| *v == var)
                            .map(|(_, s, _)| s);
                    }
                }
            }
        }
        None
    }

    /// Resolves a syntactic `Place` into `(RuntimePlace, TagId)` through any
    /// borrow root or borrow-typed view field.
    fn resolve_place(&mut self, place: &Place) -> Result<(RuntimePlace, TagId), Fail> {
        let var_name = self.body().vars[place.root].name.clone();
        let (scope_id, slot, owner_tag) = self.find_local_slot(place.root)?;
        let Slot::Available(root_val) = slot else {
            return fail(
                2,
                "E-Var",
                format!("`{var_name}` has been moved on this history"),
            );
        };
        let (mut cur_place, mut cur_tag) = match root_val {
            Value::Ref { place, tag, .. } => (place, tag),
            _ => (RuntimePlace::root(scope_id, place.root), owner_tag),
        };
        for step in &place.steps {
            match step {
                PlaceStep::Field(_, fidx, _) => {
                    if !self.tags.is_alive(cur_tag) {
                        return fail(
                            4,
                            "B1",
                            "borrow tag is no longer alive (use after invalidation or scope end)",
                        );
                    }
                    let current_val = self.read_place(&cur_place)?;
                    let Value::Struct { fields, .. } = current_val else {
                        return fail(10, "E-Field", "field access on non-struct");
                    };
                    if let Value::Ref {
                        place: fplace,
                        tag: ftag,
                        ..
                    } = &fields[*fidx]
                    {
                        cur_place = fplace.clone();
                        cur_tag = *ftag;
                    } else {
                        cur_place.steps.push(RuntimeStep::Field(*fidx));
                    }
                }
                PlaceStep::Index(idx_expr, _) => {
                    let idx_val = integer(self.eval_expr(idx_expr, false)?)?;
                    if !self.tags.is_alive(cur_tag) {
                        return fail(
                            4,
                            "B1",
                            "borrow tag is no longer alive (use after invalidation or scope end)",
                        );
                    }
                    let current_val = self.read_place(&cur_place)?;
                    let Value::Vector(items) = current_val else {
                        return fail(10, "E-Index", "index on non-vector");
                    };
                    let Some(i) = idx_val
                        .to_i128()
                        .filter(|&i| i >= 0 && (i as usize) < items.len())
                    else {
                        return fail(
                            7,
                            "E-Index",
                            format!(
                                "index {idx_val} is out of bounds for length {}",
                                items.len()
                            ),
                        );
                    };
                    cur_place.steps.push(RuntimeStep::Index(i as usize));
                }
            }
        }
        Ok((cur_place, cur_tag))
    }

    /// If `expr` is a place chain (`Var` followed by `Field`/`Index`), resolves
    /// it to `(RuntimePlace, TagId)` so reads access only the leaf component (`[B5]`).
    fn resolve_expr_place(&mut self, expr: &Expr) -> Result<Option<(RuntimePlace, TagId)>, Fail> {
        match expr {
            Expr::Var(VarRef::Local(id), _) => {
                let var_name = self.body().vars[*id].name.clone();
                let (scope_id, slot, owner_tag) = self.find_local_slot(*id)?;
                let Slot::Available(root_val) = slot else {
                    return fail(
                        2,
                        "E-Var",
                        format!("`{var_name}` has been moved on this history"),
                    );
                };
                match root_val {
                    Value::Ref { place, tag, .. } => Ok(Some((place, tag))),
                    _ => Ok(Some((RuntimePlace::root(scope_id, *id), owner_tag))),
                }
            }
            Expr::Field(base, _, fidx, expr_ty) => {
                let Some((mut cur_place, mut cur_tag)) = self.resolve_expr_place(base)? else {
                    return Ok(None);
                };
                if !self.tags.is_alive(cur_tag) {
                    return fail(
                        4,
                        "B1",
                        "borrow tag is no longer alive (use after invalidation or scope end)",
                    );
                }
                let current_val = self.read_place(&cur_place)?;
                let Value::Struct { fields, .. } = current_val else {
                    return fail(10, "E-Field", "field access on non-struct");
                };
                if !matches!(expr_ty, Type::Ref(_, _))
                    && let Value::Ref {
                        place: fplace,
                        tag: ftag,
                        ..
                    } = &fields[*fidx]
                {
                    cur_place = fplace.clone();
                    cur_tag = *ftag;
                } else {
                    cur_place.steps.push(RuntimeStep::Field(*fidx));
                }
                Ok(Some((cur_place, cur_tag)))
            }
            Expr::Index(base, idx_expr, _) => {
                let Some((mut cur_place, cur_tag)) = self.resolve_expr_place(base)? else {
                    return Ok(None);
                };
                let idx_val = integer(self.eval_expr(idx_expr, false)?)?;
                if !self.tags.is_alive(cur_tag) {
                    return fail(
                        4,
                        "B1",
                        "borrow tag is no longer alive (use after invalidation or scope end)",
                    );
                }
                let current_val = self.read_place(&cur_place)?;
                let Value::Vector(items) = current_val else {
                    return fail(10, "E-Index", "index on non-vector");
                };
                let Some(i) = idx_val
                    .to_i128()
                    .filter(|&i| i >= 0 && (i as usize) < items.len())
                else {
                    return fail(
                        7,
                        "E-Index",
                        format!(
                            "index {idx_val} is out of bounds for length {}",
                            items.len()
                        ),
                    );
                };
                cur_place.steps.push(RuntimeStep::Index(i as usize));
                Ok(Some((cur_place, cur_tag)))
            }
            _ => Ok(None),
        }
    }

    /// Writes `new_val` at `place` through `tag` (`[B1]`, `[B2]`, `[E-Assign]`).
    fn write_runtime_place(
        &mut self,
        place: &RuntimePlace,
        tag: TagId,
        new_val: Value,
        check_replaced_obligation: bool,
    ) -> Result<(), Fail> {
        self.access_tag(tag, place, true)?;
        let Some(slot_clone) =
            find_slot_ref(&self.entry_slots, &self.stack, &self.tasks, place).cloned()
        else {
            return fail(4, "B1", "assignment target scope has ended");
        };
        if place.steps.is_empty() {
            if check_replaced_obligation
                && let Slot::Available(old_val) = &slot_clone
                && self.contains_obligation(old_val)
            {
                return fail(
                    5,
                    "E-Assign",
                    "overwriting slot destroys an uncompleted obligation",
                );
            }
            let slot = self.slot_mut(place.scope, place.var).expect("slot exists");
            *slot = Slot::Available(new_val);
            return Ok(());
        }
        let Slot::Available(mut root_val) = slot_clone else {
            return fail(2, "E-Assign", "assignment target slot has been moved");
        };
        let replaced = update_nested(&mut root_val, &place.steps, new_val)?;
        if check_replaced_obligation && self.contains_obligation(&replaced) {
            return fail(
                5,
                "E-Assign",
                "overwriting component destroys an uncompleted obligation",
            );
        }
        let slot = self.slot_mut(place.scope, place.var).expect("slot exists");
        *slot = Slot::Available(root_val);
        Ok(())
    }

    /// Evaluates an expression `expr` in the current activation, checking
    /// borrow tags (`[B1]`–`[B4]`), moving slots when `consumed` is true and
    /// the variable's type does not have kind `copy` (`[E-Var]`, `[O3]`), and
    /// checking temporary obligations when `consumed` is false (`[E-Temp]`).
    fn eval_expr(&mut self, expr: &Expr, consumed: bool) -> Result<Value, Fail> {
        let is_temp = matches!(
            expr,
            Expr::Struct(_, _, _)
                | Expr::Variant(_, _, _, _)
                | Expr::Vector(_, _)
                | Expr::EmptyMap(_)
                | Expr::Clone(_, _)
                | Expr::Call(_, _, _)
        );
        let value = match expr {
            Expr::Boolean(v) => Value::Bool(*v),
            Expr::Integer(v, _) => Value::Int(v.clone()),
            Expr::String(v) => Value::String(v.clone()),
            Expr::Var(VarRef::Local(id), expr_ty) => {
                let var_name = self.body().vars[*id].name.clone();
                let var_ty = self.body().vars[*id].ty.clone();
                let (scope_id, slot, owner_tag) = self.find_local_slot(*id)?;
                let Slot::Available(val) = slot else {
                    return fail(
                        2,
                        "E-Var",
                        format!("`{var_name}` has been moved on this history"),
                    );
                };
                if matches!(var_ty, Type::Ref(_, _)) {
                    if matches!(expr_ty, Type::Ref(_, _)) {
                        // [W8]: passing the borrow itself (copying `&τ` or moving `&~τ`).
                        // Copying a shared borrow copies its tag; moving an exclusive
                        // borrow moves its tag. Neither is an access to the referent.
                        if consumed && self.program.kind(&var_ty) != Kind::Copy {
                            let own_place = RuntimePlace::root(scope_id, *id);
                            self.access_tag(owner_tag, &own_place, true)?;
                            *self.slot_mut(scope_id, *id).expect("slot") = Slot::Moved;
                        }
                        self.count("E-Var");
                        val
                    } else {
                        // [W8]: dereferencing a borrow name to read its referent value.
                        if consumed && self.program.kind(expr_ty) != Kind::Copy {
                            return fail(
                                2,
                                "E-Var",
                                format!("cannot move non-copy value out of borrow `{var_name}`"),
                            );
                        }
                        let Value::Ref { place, tag, .. } = val else {
                            return fail(10, "E-Var", "borrow slot does not hold a reference");
                        };
                        self.access_tag(tag, &place, false)?;
                        let derefed = self.read_place(&place)?;
                        self.count("E-Var");
                        derefed
                    }
                } else {
                    let is_copy = self.program.kind(&var_ty) == Kind::Copy;
                    let own_place = RuntimePlace::root(scope_id, *id);
                    if consumed && !is_copy {
                        // [B4]: moving a value out of a slot is a write access through owner tag.
                        self.access_tag(owner_tag, &own_place, true)?;
                        *self.slot_mut(scope_id, *id).expect("slot") = Slot::Moved;
                        self.count("B4");
                    } else {
                        self.access_tag(owner_tag, &own_place, false)?;
                    }
                    self.count("E-Var");
                    val
                }
            }
            Expr::Var(_, _) | Expr::Old(_, _) => {
                return fail(10, "E-Var", "a body refers to a name of a signature");
            }
            Expr::Move(inner, _) => self.eval_expr(inner, true)?,
            Expr::Borrow(mode, place, _) => {
                let (rplace, parent_tag) = self.resolve_place(place)?;
                let tag = self.create_borrow_tag(parent_tag, rplace.clone(), *mode)?;
                self.count("E-Borrow");
                Value::Ref {
                    mode: *mode,
                    place: rplace,
                    tag,
                }
            }
            Expr::Field(base, _, fidx, fty) => {
                if consumed && self.program.kind(fty) != Kind::Copy {
                    return fail(
                        2,
                        "E-Field",
                        "cannot partially move a non-copy field out of a struct",
                    );
                }
                if let Some((rplace, tag)) = self.resolve_expr_place(expr)? {
                    if matches!(fty, Type::Ref(_, _)) {
                        // Copying a `&τ` borrow field out of a view without touching referent.
                        if !self.tags.is_alive(tag) {
                            return fail(4, "B1", "borrow tag is no longer alive");
                        }
                        let val = self.read_place(&rplace)?;
                        self.count("E-Field");
                        val
                    } else {
                        self.access_tag(tag, &rplace, false)?;
                        let val = self.read_place(&rplace)?;
                        self.count("E-Field");
                        val
                    }
                } else {
                    let base_val = self.eval_expr(base, false)?;
                    let Value::Struct { mut fields, .. } = base_val else {
                        return fail(10, "E-Field", "field access on non-struct");
                    };
                    let raw = fields.swap_remove(*fidx);
                    let val = if !matches!(fty, Type::Ref(_, _))
                        && let Value::Ref { place, tag, .. } = &raw
                    {
                        self.access_tag(*tag, place, false)?;
                        self.read_place(place)?
                    } else {
                        raw
                    };
                    self.count("E-Field");
                    val
                }
            }
            Expr::Index(base, idx_expr, ety) => {
                if consumed && self.program.kind(ety) != Kind::Copy {
                    return fail(
                        2,
                        "E-Index",
                        "cannot partially move a non-copy element out of a vector",
                    );
                }
                if let Some((rplace, tag)) = self.resolve_expr_place(expr)? {
                    self.access_tag(tag, &rplace, false)?;
                    let val = self.read_place(&rplace)?;
                    self.count("E-Index");
                    val
                } else {
                    let base_val = self.eval_expr(base, false)?;
                    let idx_val = integer(self.eval_expr(idx_expr, false)?)?;
                    let Value::Vector(mut items) = base_val else {
                        return fail(10, "E-Index", "index on non-vector");
                    };
                    let Some(i) = idx_val
                        .to_i128()
                        .filter(|&i| i >= 0 && (i as usize) < items.len())
                    else {
                        return fail(
                            7,
                            "E-Index",
                            format!(
                                "index {idx_val} is out of bounds for length {}",
                                items.len()
                            ),
                        );
                    };
                    self.count("E-Index");
                    items.swap_remove(i as usize)
                }
            }
            Expr::Struct(sid, fields, _) => {
                let vals = if self.program.structs[*sid].is_view {
                    // [E-Operands]: a view constructor evaluates non-lending fields first.
                    self.eval_operands(fields)?
                } else {
                    let mut out = Vec::with_capacity(fields.len());
                    for f in fields {
                        out.push(self.eval_expr(f, true)?);
                    }
                    out
                };
                self.count("E-Build");
                Value::Struct {
                    ty: *sid,
                    name: self.program.structs[*sid].name.clone(),
                    fields: vals,
                }
            }
            Expr::Variant(vid, cidx, fields, _) => {
                let mut vals = Vec::with_capacity(fields.len());
                for f in fields {
                    vals.push(self.eval_expr(f, true)?);
                }
                self.count("E-Build");
                let vdef = &self.program.variants[*vid];
                Value::Variant {
                    ty: *vid,
                    name: vdef.name.clone(),
                    constructor: *cidx,
                    constructor_name: vdef.constructors[*cidx].name.clone(),
                    fields: vals,
                }
            }
            Expr::Vector(items, _) => {
                let mut vals = Vec::with_capacity(items.len());
                for item in items {
                    vals.push(self.eval_expr(item, true)?);
                }
                self.count("E-Build");
                Value::Vector(vals)
            }
            Expr::EmptyMap(_) => {
                self.count("E-Build");
                Value::Map(BTreeMap::new())
            }
            Expr::Len(place) => {
                let v = self.eval_expr(place, false)?;
                let v = self.deref_checked(&v)?;
                Value::Int(value_len(&v)?)
            }
            Expr::Clone(place, _) => {
                let v = self.eval_expr(place, false)?;
                let v = self.deref_checked(&v)?;
                self.count("E-Build");
                v
            }
            Expr::Trim(arg) => {
                let v = self.eval_expr(arg, false)?;
                let Value::String(s) = self.deref_checked(&v)? else {
                    return fail(10, "E-Fn", "`trim` expects a string");
                };
                Value::String(s.trim().to_string())
            }
            Expr::Not(operand) => Value::Bool(!boolean(self.eval_expr(operand, false)?)?),
            Expr::Negate(operand, ty) => {
                let operand = integer(self.eval_expr(operand, false)?)?;
                let result = operand.negate();
                if !self
                    .config
                    .fits(&Value::Int(result.clone()), &Type::Int(*ty))
                {
                    return fail(
                        7,
                        "E-Arith",
                        format!("-{operand} = {result} is not a value of {}", ty.name()),
                    );
                }
                Value::Int(result)
            }
            Expr::Arithmetic(operator, left, right, ty) => {
                let left = integer(self.eval_expr(left, false)?)?;
                let right = integer(self.eval_expr(right, false)?)?;
                let result = match operator {
                    Arithmetic::Add => left.plus(&right),
                    Arithmetic::Subtract => left.minus(&right),
                    Arithmetic::Multiply => left.times(&right),
                    Arithmetic::Divide | Arithmetic::Remainder => {
                        let Some((quotient, remainder)) = left.divide(&right) else {
                            return fail(
                                7,
                                "E-Arith",
                                format!("{left} {} 0: the divisor is zero", sign(*operator)),
                            );
                        };
                        if *operator == Arithmetic::Divide {
                            quotient
                        } else {
                            remainder
                        }
                    }
                };
                if !self
                    .config
                    .fits(&Value::Int(result.clone()), &Type::Int(*ty))
                {
                    return fail(
                        7,
                        "E-Arith",
                        format!(
                            "{left} {} {right} = {result} is not a value of {}",
                            sign(*operator),
                            ty.name()
                        ),
                    );
                }
                Value::Int(result)
            }
            Expr::Compare(comparison, left, right) => {
                let left = self.eval_expr(left, false)?;
                let right = self.eval_expr(right, false)?;
                Value::Bool(compare(*comparison, &left, &right)?)
            }
            Expr::And(left, right) => Value::Bool(
                boolean(self.eval_expr(left, false)?)? && boolean(self.eval_expr(right, false)?)?,
            ),
            Expr::Or(left, right) => Value::Bool(
                boolean(self.eval_expr(left, false)?)? || boolean(self.eval_expr(right, false)?)?,
            ),
            Expr::Call(id, arguments, _) => {
                let function = &self.program.functions[*id];
                let mut values = Vec::with_capacity(arguments.len());
                for argument in arguments {
                    let v = self.eval_expr(argument, false)?;
                    // [E-Fn]: read borrowed/view arguments where they are, checking [B1].
                    values.push(self.deref_checked(&v)?);
                }
                let inner = SignatureEnv {
                    parameters: &values,
                    old_parameters: &values,
                    fields: &[],
                };
                if let Some(precondition) = &function.precondition
                    && !self.evaluator().holds(precondition, &inner)?
                {
                    return fail(
                        7,
                        "E-Fn",
                        format!(
                            "the precondition of `{}` is false for ({})",
                            function.name,
                            list(&values)
                        ),
                    );
                }
                self.evaluator().value(&function.body, &inner)?
            }
            Expr::TasksEmpty(_, _) => {
                let owner_scope = self.scope().id;
                let set_id = self.task_sets.len() as TaskSetId;
                self.task_sets.push(TaskSet {
                    owner_task: self.current_task,
                    owner_scope,
                    members: Vec::new(),
                    done_queue: VecDeque::new(),
                });
                Value::TaskSet(set_id)
            }
            Expr::Count(var) => {
                let (scope_id, slot, owner_tag) = self.find_local_slot(*var)?;
                let Slot::Available(Value::TaskSet(set_id)) = slot else {
                    let var_name = &self.body().vars[*var].name;
                    return fail(
                        2,
                        "E-Var",
                        format!("`{var_name}` has been moved on this history"),
                    );
                };
                self.access_tag(owner_tag, &RuntimePlace::root(scope_id, *var), false)?;
                let count = self.task_sets[set_id as usize].members.len() as u64;
                Value::Int(Int::from_u64(count))
            }
        };
        // [E-Temp]: A temporary value that was read and not consumed is
        // destroyed when its reader is done; if it contains an obligation, stuck.
        if !consumed && is_temp && self.contains_obligation(&value) {
            return fail(
                5,
                "E-Temp",
                "a temporary value containing an obligation was not consumed",
            );
        }
        Ok(value)
    }

    /// Evaluates operands according to `[E-Operands]`: operands that do not
    /// lend are evaluated first, left to right, and operands that lend (`&p`,
    /// `&~p`, or view constructors with a lending field) afterwards, left to right.
    fn eval_operands(&mut self, exprs: &[Expr]) -> Result<Vec<Value>, Fail> {
        let mut results: Vec<Option<Value>> = vec![None; exprs.len()];
        for (i, expr) in exprs.iter().enumerate() {
            if !expr.lends() {
                results[i] = Some(self.eval_expr(expr, true)?);
            }
        }
        for (i, expr) in exprs.iter().enumerate() {
            if expr.lends() {
                results[i] = Some(self.eval_expr(expr, true)?);
            }
        }
        if exprs.len() > 1 && exprs.iter().any(Expr::lends) {
            self.count("E-Operands");
        }
        Ok(results.into_iter().map(|v| v.expect("evaluated")).collect())
    }

    fn formula(&self, formula: &Expr) -> Result<bool, Fail> {
        let env = ActivationEnv {
            body: self.body(),
            entry_slots: &self.entry_slots,
            stack: &self.stack,
            tasks: &self.tasks,
            task_sets: &self.task_sets,
        };
        self.evaluator().holds(formula, &env)
    }

    /// [E-Bind]: a name gets its slot and owner tag once in a run of its body.
    fn bind(&mut self, var: VarId, value: Value) -> Result<(), Fail> {
        let name = self.body().vars[var].name.clone();
        let scope_id = {
            let scope = self.scope();
            if scope.slots.iter().any(|(slot, _, _)| *slot == var) {
                return fail(
                    3,
                    "E-Bind",
                    format!("`{name}` is bound twice in one run of its body"),
                );
            }
            scope.id
        };
        let owner_tag = self.tags.new_owner(scope_id, var);
        self.scope()
            .slots
            .push((var, Slot::Available(value), owner_tag));
        Ok(())
    }

    /// [E-Scope], [B4]: ends a scope normally; stuck with X5 if any available
    /// slot contains an uncompleted obligation, and kills all owner tags of the scope.
    fn end_scope(&mut self, scope: &Scope) -> Result<(), Fail> {
        for (var_id, slot, owner_tag) in scope.slots.iter().rev() {
            if let Slot::Available(val) = slot
                && self.contains_obligation(val)
            {
                let var_name = &self.body().vars[*var_id].name;
                return fail(
                    5,
                    "E-Scope",
                    format!(
                        "`{var_name}` holds an uncompleted obligation `{val}` when its scope ends"
                    ),
                );
            }
            self.tags.kill_with_descendants(*owner_tag);
        }
        if let ScopeKind::LexicalBoundary { captures, .. } = &scope.kind {
            for val in captures {
                if self.contains_obligation(val) {
                    return fail(
                        5,
                        "E-Scope",
                        format!(
                            "boundary capture `{val}` holds an uncompleted obligation when the boundary ends"
                        ),
                    );
                }
            }
        }
        self.count("B4");
        self.count("E-Scope");
        Ok(())
    }

    /// [E-Unwind] / [E-Stop]: releases fault-releasable obligations in `value`
    /// and gets stuck with X8 on any open resource not declared `on fault release`.
    fn unwind_value_with_clause(
        &mut self,
        value: &Value,
        clause: &'static str,
    ) -> Result<(), Fail> {
        match value {
            Value::Resource { ty, name, id } => {
                if self.resources.get(&(*ty, *id)).copied().unwrap_or(false) {
                    if !self.program.resources[*ty].on_fault_release {
                        return fail(
                            8,
                            clause,
                            format!(
                                "open resource `{name}#{id}` is not declared `on fault release`"
                            ),
                        );
                    }
                    self.resources.insert((*ty, *id), false);
                    self.trace.push(Event {
                        control: format!("{name}.release"),
                        arguments: vec![value.clone()],
                        alternative: "released".to_string(),
                        payload: Vec::new(),
                    });
                }
                Ok(())
            }
            Value::TaskSet(set_id) => self.stop_task_set(*set_id),
            Value::Outcome { payload, .. } => {
                for item in payload {
                    self.unwind_value_with_clause(item, clause)?;
                }
                Ok(())
            }
            Value::Struct { fields, .. }
            | Value::Variant { fields, .. }
            | Value::Vector(fields) => {
                for item in fields {
                    self.unwind_value_with_clause(item, clause)?;
                }
                Ok(())
            }
            Value::Map(entries) => {
                for (k, v) in entries {
                    self.unwind_value_with_clause(k, clause)?;
                    self.unwind_value_with_clause(v, clause)?;
                }
                Ok(())
            }
            Value::Bool(_) | Value::Int(_) | Value::String(_) | Value::Ref { .. } => Ok(()),
        }
    }

    fn unwind_scope_with_clause(
        &mut self,
        scope: &Scope,
        clause: &'static str,
        release_boundary_captures: bool,
    ) -> Result<(), Fail> {
        for (_, slot, owner_tag) in scope.slots.iter().rev() {
            if let Slot::Available(val) = slot {
                self.unwind_value_with_clause(val, clause)?;
            }
            self.tags.kill_with_descendants(*owner_tag);
        }
        if release_boundary_captures
            && let ScopeKind::LexicalBoundary { captures, .. } = &scope.kind
        {
            for val in captures {
                self.unwind_value_with_clause(val, clause)?;
            }
        }
        self.count(clause);
        Ok(())
    }

    fn unwind_scope(&mut self, scope: &Scope) -> Result<(), Fail> {
        self.unwind_scope_with_clause(scope, "E-Unwind", false)
    }

    /// [E-Stop]: stops one activation, ending all of its scopes innermost first
    /// (including boundary captures) without running contingencies or checking `faults`.
    fn stop_activation(&mut self, mut act: Activation) -> Result<(), Fail> {
        while let Some(scope) = act.scopes.pop() {
            self.unwind_scope_with_clause(&scope, "E-Stop", true)?;
        }
        Ok(())
    }

    /// [E-Stop]: stops a task, withdrawing any waiting host operation, releasing
    /// any `Done` payload, and stopping all of its activations last-first.
    fn stop_task(&mut self, tid: usize) -> Result<(), Fail> {
        let prev_state = std::mem::replace(&mut self.tasks[tid].state, TaskState::Stopped);
        match prev_state {
            TaskState::WaitingHost {
                callee,
                concrete_args,
                ..
            } => {
                // Withdrawn host operation has no completion and no event; release by-value args.
                let param_is_ref: Vec<bool> = self.program.controls[callee]
                    .parameters
                    .iter()
                    .map(|p| matches!(p.ty, Type::Ref(_, _)))
                    .collect();
                for (arg, is_ref) in concrete_args.iter().zip(param_is_ref) {
                    if !is_ref {
                        self.unwind_value_with_clause(arg, "E-Stop")?;
                    }
                }
            }
            TaskState::Done { payload, .. } => {
                for val in &payload {
                    self.unwind_value_with_clause(val, "E-Stop")?;
                }
            }
            TaskState::Stopped => return Ok(()),
            TaskState::Ready | TaskState::WaitingNext { .. } | TaskState::WaitingRun => {}
        }
        let mut stack = std::mem::take(&mut self.tasks[tid].stack);
        while let Some(act) = stack.pop() {
            self.stop_activation(act)?;
        }
        self.count("E-Stop");
        Ok(())
    }

    /// [E-Stop]: stops every member of task set `set_id`.
    fn stop_task_set(&mut self, set_id: TaskSetId) -> Result<(), Fail> {
        let members = std::mem::take(&mut self.task_sets[set_id as usize].members);
        self.task_sets[set_id as usize].done_queue.clear();
        for mid in members {
            self.stop_task(mid)?;
        }
        Ok(())
    }

    /// Whether `tid` is effectively cancelled ([E-Cancel]): its own flag is set,
    /// its owner task is cancelled, or the caller of its nested run is cancelled.
    fn is_task_cancelled(&self, mut tid: usize) -> bool {
        loop {
            if self.tasks[tid].cancelled {
                return true;
            }
            if let Some(set_id) = self.tasks[tid].member_of {
                tid = self.task_sets[set_id as usize].owner_task;
                continue;
            }
            if let Some(run) = self.runs.iter().find(|r| r.root_task == tid)
                && let Some(caller) = run.caller_task
            {
                tid = caller;
                continue;
            }
            return false;
        }
    }

    /// Snapshot of effect allowances currently active on the call stack and
    /// spawning/running ancestor chain ([E-Effect]).
    fn collect_allowances(&self) -> Vec<Vec<String>> {
        let mut out = self.tasks[self.current_task].parent_allowances.clone();
        for act in &self.stack {
            if let ActivationKind::Control(cid) = act.kind {
                out.push(self.program.controls[cid].uses.clone());
            }
        }
        out
    }

    fn park_current(&mut self, state: TaskState) {
        let tid = self.current_task;
        self.tasks[tid].stack = std::mem::take(&mut self.stack);
        self.tasks[tid].state = state;
        self.has_turn = false;
    }

    fn activate_task(&mut self, tid: usize) {
        self.stack = std::mem::take(&mut self.tasks[tid].stack);
        self.tasks[tid].state = TaskState::Ready;
        self.current_task = tid;
        self.has_turn = true;
    }

    /// Withdraws any `WaitingHost` cancellable operation in the innermost run
    /// whose task is now effectively cancelled ([E-Cancel], [E-AwaitHost]).
    fn withdraw_cancelled_host_waits(&mut self) -> Result<(), Fail> {
        let run_tasks = self.runs.last().expect("a run").tasks.clone();
        for tid in run_tasks {
            let is_waiting_cancellable = matches!(
                self.tasks[tid].state,
                TaskState::WaitingHost { callee, .. } if self.program.controls[callee].is_cancellable()
            );
            if !is_waiting_cancellable || !self.is_task_cancelled(tid) {
                continue;
            }
            let prev = std::mem::replace(&mut self.tasks[tid].state, TaskState::Ready);
            let TaskState::WaitingHost {
                callee,
                concrete_args,
                ..
            } = prev
            else {
                unreachable!();
            };
            let param_is_ref: Vec<bool> = self.program.controls[callee]
                .parameters
                .iter()
                .map(|p| matches!(p.ty, Type::Ref(_, _)))
                .collect();
            for (arg, is_ref) in concrete_args.iter().zip(param_is_ref) {
                if !is_ref {
                    self.unwind_value_with_clause(arg, "E-Unwind")?;
                }
            }
            let cancel_idx = self.program.controls[callee]
                .contract
                .iter()
                .position(|a| a.name == "cancelled")
                .expect("cancellable control has `cancelled`");
            // Temporarily swap `tid`'s stack in to complete its waiting decision/capture.
            let saved_stack = std::mem::take(&mut self.stack);
            let saved_tid = self.current_task;
            self.stack = std::mem::take(&mut self.tasks[tid].stack);
            self.current_task = tid;
            let res = self.complete(cancel_idx, Vec::new());
            self.tasks[tid].stack = std::mem::take(&mut self.stack);
            self.stack = saved_stack;
            self.current_task = saved_tid;
            res?;
            self.count("E-AwaitHost");
        }
        Ok(())
    }

    /// Whether the current activation runs the contingency of a named
    /// boundary ([E-Supervise]).
    fn in_named_contingency(&self) -> bool {
        matches!(
            self.stack.last().expect("an activation").kind,
            ActivationKind::Boundary {
                in_contingency: Some(_),
                ..
            }
        )
    }

    /// Whether the current position in the top activation is permitted to fault
    /// ([E-Fault], [E-Unwind]).
    fn current_permits_faults(&self) -> bool {
        let act = self.stack.last().expect("an activation");
        if act
            .scopes
            .iter()
            .any(|s| matches!(s.kind, ScopeKind::LexicalBoundary { .. }))
        {
            return true;
        }
        match &act.kind {
            ActivationKind::Control(cid) => self.program.controls[*cid].faults,
            ActivationKind::Boundary {
                in_contingency: None,
                ..
            } => true,
            ActivationKind::Boundary {
                in_contingency: Some(_),
                ..
            } => false,
        }
    }

    /// [E-Unwind], [E-Contingency], [E-Supervise], [E-Root]: the mode is
    /// `fault(message)`. The scopes end innermost first, until a boundary
    /// takes the fault or the last activation is popped.
    fn unwind(&mut self, message: String) -> Result<Option<End>, Fail> {
        loop {
            // The scopes of the current activation, innermost first. A
            // lexical boundary takes the fault before anything around it,
            // and the body of a named boundary when only its own scope is
            // left.
            loop {
                let activation = self.stack.last().expect("an activation");
                if let ActivationKind::Boundary {
                    id,
                    in_contingency: None,
                } = activation.kind
                    && activation.scopes.len() == 1
                {
                    return self.enter_named_contingency(id, message);
                }
                let Some(scope) = self.stack.last_mut().expect("an activation").scopes.pop() else {
                    break;
                };
                self.unwind_scope(&scope)?;
                if let ScopeKind::LexicalBoundary {
                    captures,
                    contingency_body,
                    contingency_vars,
                    message_var,
                    ..
                } = scope.kind
                {
                    // [E-Contingency]: `B₂` runs with `x̄` and the message, in
                    // the place of `B₁`.
                    let scope_id = self.alloc_scope_id();
                    let mut slots = Vec::with_capacity(contingency_vars.len() + 1);
                    for (var, val) in contingency_vars.into_iter().zip(captures) {
                        let tag = self.tags.new_owner(scope_id, var);
                        slots.push((var, Slot::Available(val), tag));
                    }
                    if let Some(mvar) = message_var {
                        let tag = self.tags.new_owner(scope_id, mvar);
                        slots.push((mvar, Slot::Available(Value::String(message.clone())), tag));
                    }
                    self.stack
                        .last_mut()
                        .expect("an activation")
                        .scopes
                        .push(Scope {
                            id: scope_id,
                            body: contingency_body,
                            pc: 0,
                            slots,
                            history: Vec::new(),
                            kind: ScopeKind::LexicalContingency {
                                fault_message: message,
                            },
                        });
                    self.count("E-Contingency");
                    return Ok(None);
                }
            }

            // The activation has no scopes left: it is popped, and the
            // unwinding continues where it was called from.
            let _popped = self.stack.pop().expect("an activation");
            let mut arrival = "a fault";
            if self.stack.is_empty() {
                let cur = self.current_task;
                if let Some(set_id) = self.tasks[cur].member_of {
                    // [E-MemberFault]: remove member and deliver fault to the owner activation `A`.
                    self.tasks[cur].state = TaskState::Stopped;
                    self.task_sets[set_id as usize]
                        .members
                        .retain(|&m| m != cur);
                    self.task_sets[set_id as usize]
                        .done_queue
                        .retain(|&m| m != cur);
                    let owner_task = self.task_sets[set_id as usize].owner_task;
                    let owner_scope = self.task_sets[set_id as usize].owner_scope;
                    self.count("E-MemberFault");

                    // If the owner task was waiting on a host operation, withdraw it ([E-Stop]).
                    if let TaskState::WaitingHost {
                        callee,
                        concrete_args,
                        ..
                    } = std::mem::replace(&mut self.tasks[owner_task].state, TaskState::Ready)
                    {
                        let param_is_ref: Vec<bool> = self.program.controls[callee]
                            .parameters
                            .iter()
                            .map(|p| matches!(p.ty, Type::Ref(_, _)))
                            .collect();
                        for (arg, is_ref) in concrete_args.iter().zip(param_is_ref) {
                            if !is_ref {
                                self.unwind_value_with_clause(arg, "E-Stop")?;
                            }
                        }
                    }

                    self.activate_task(owner_task);
                    let owner_act_idx = self
                        .stack
                        .iter()
                        .position(|act| act.scopes.iter().any(|s| s.id == owner_scope))
                        .expect("owner scope still in owner task stack");
                    // Stop every activation above `A` ([E-Stop]).
                    while self.stack.len() > owner_act_idx + 1 {
                        let above = self.stack.pop().expect("activation above owner");
                        self.stop_activation(above)?;
                    }
                    arrival = "a member fault";
                } else if self.runs.len() > 1 {
                    // Root of a nested `run`: the fault reaches the caller waiting at `run` ([E-Run]).
                    let finished_run = self.runs.pop().expect("nested run");
                    self.tasks[cur].state = TaskState::Stopped;
                    let caller = finished_run.caller_task.expect("nested run has caller");
                    self.activate_task(caller);
                    arrival = "a fault from `run`";
                } else {
                    self.count("E-Root");
                    return Ok(Some(End::Faulted(message)));
                }
            }
            self.locate();
            // [E-Unwind]: the activation the fault reaches permits `faults`,
            // or a boundary encloses the waiting statement.
            if !self.current_permits_faults() {
                let name = self.current_name();
                return fail(
                    8,
                    "E-Unwind",
                    format!(
                        "{arrival} reached `{name}`, which does not permit `faults` and has no enclosing boundary"
                    ),
                );
            }
        }
    }

    /// [E-Supervise]: unwinds `B₁` of named boundary `id` except for its
    /// retained parameters `ȳ`, and starts `B₂` (`contingency`).
    fn enter_named_contingency(
        &mut self,
        id: BoundaryId,
        message: String,
    ) -> Result<Option<End>, Fail> {
        let retains = self.program.boundaries[id].retains.clone();
        // The scopes inside `B₁` have ended ([E-Unwind]); its own is left.
        let mut root_scope = self
            .stack
            .last_mut()
            .expect("an activation")
            .scopes
            .pop()
            .expect("root scope of named boundary");
        let mut retained_values = Vec::with_capacity(retains.len());
        for &param_var in &retains {
            let param_name = self.program.boundaries[id].parameters[param_var]
                .name
                .clone();
            let slot = root_scope
                .slots
                .iter_mut()
                .find(|(s, _, _)| *s == param_var);
            match slot {
                Some((_, s @ Slot::Available(_), _)) => {
                    let Slot::Available(val) = std::mem::replace(s, Slot::Moved) else {
                        unreachable!();
                    };
                    retained_values.push(val);
                }
                _ => {
                    return fail(
                        2,
                        "E-Supervise",
                        format!(
                            "retained parameter `{param_name}` is not available when boundary `{}` faults",
                            self.program.boundaries[id].name
                        ),
                    );
                }
            }
        }
        // Unwind all remaining non-retained slots of `B₁`.
        self.unwind_scope(&root_scope)?;

        let scope_id = self.alloc_scope_id();
        let mut b2_slots = Vec::with_capacity(retained_values.len() + 1);
        for (idx, val) in retained_values.into_iter().enumerate() {
            let tag = self.tags.new_owner(scope_id, idx);
            b2_slots.push((idx, Slot::Available(val), tag));
        }
        let msg_var = retains.len();
        let msg_tag = self.tags.new_owner(scope_id, msg_var);
        b2_slots.push((
            msg_var,
            Slot::Available(Value::String(message.clone())),
            msg_tag,
        ));
        let act = self.stack.last_mut().expect("an activation");
        act.kind = ActivationKind::Boundary {
            id,
            in_contingency: Some(message),
        };
        act.scopes.push(Scope {
            id: scope_id,
            body: 0,
            pc: 0,
            slots: b2_slots,
            history: Vec::new(),
            kind: ScopeKind::Normal,
        });
        self.count("E-Supervise");
        Ok(None)
    }

    fn selects(&self, selector: &Selector) -> bool {
        match selector {
            Selector::Top => true,
            Selector::Atom(site, alternative) => {
                let activation = self.stack.last().expect("an activation");
                activation
                    .scopes
                    .iter()
                    .any(|scope| scope.history.contains(&(*site, *alternative)))
            }
            Selector::Not(inner) => !self.selects(inner),
            Selector::And(left, right) => self.selects(left) && self.selects(right),
            Selector::Or(left, right) => self.selects(left) || self.selects(right),
        }
    }

    fn locate(&mut self) {
        let activation = self.stack.last().expect("an activation");
        let scope = activation.scopes.last().expect("a scope");
        let statements = &self.body().bodies[scope.body].statements;
        let line = match statements.get(scope.pc).or(statements.last()) {
            Some(statement) => statement.line,
            None => 0,
        };
        self.location = (self.current_name(), line);
    }

    /// [E-Loop], [E-Again]: a fresh scope for the body of a loop, with its
    /// parameters bound and the invariant true for them.
    fn enter(
        &mut self,
        body: BodyId,
        values: Vec<Value>,
        clause: &'static str,
    ) -> Result<(), Fail> {
        let params = self.body().bodies[body]
            .head
            .as_ref()
            .expect("a loop body")
            .parameters
            .clone();
        let scope_id = self.alloc_scope_id();
        let mut slots = Vec::with_capacity(params.len());
        for (&var, val) in params.iter().zip(values) {
            let tag = self.tags.new_owner(scope_id, var);
            slots.push((var, Slot::Available(val), tag));
        }
        let activation = self.stack.last_mut().expect("an activation");
        activation.scopes.push(Scope {
            id: scope_id,
            body,
            pc: 0,
            slots,
            history: Vec::new(),
            kind: ScopeKind::Loop,
        });
        let head = self.body().bodies[body].head.as_ref().expect("a loop body");
        if let Some(invariant) = &head.invariant
            && !self.formula(invariant)?
        {
            return fail(
                7,
                clause,
                format!("the invariant of the loop `{}` is false", head.name),
            );
        }
        Ok(())
    }

    /// [E-Decide], [E-Capture]: the waiting decision or capture completes with
    /// an alternative of the operation's contract and its payload.
    fn complete(&mut self, alternative: usize, payload: Vec<Value>) -> Result<(), Fail> {
        let body = self.body();
        let scope = self.scope();
        let statement = &body.bodies[scope.body].statements[scope.pc];
        match &statement.command {
            Command::Decide {
                site,
                op_kind,
                arms,
                ..
            } => {
                let site = *site;
                let arms = arms.clone();
                let contract = op_kind.contract(self.program);
                let op_name = op_kind.name(self.program).to_string();
                let Some(position) = arms.iter().position(|arm| arm.alternative == alternative)
                else {
                    return fail(
                        10,
                        "E-Decide",
                        format!(
                            "`{op_name}` completed with `{}`, which the decision does not list",
                            contract[alternative].name
                        ),
                    );
                };
                let scope = self.scope();
                scope.history.push((site, position));
                scope.pc += 1;
                for (var, value) in arms[position].vars.iter().zip(payload) {
                    self.bind(*var, value)?;
                }
                self.count("E-Decide");
                Ok(())
            }
            Command::Capture {
                var, outcome_id, ..
            } => {
                let var = *var;
                let outcome_id = *outcome_id;
                let alt_name = self.program.outcomes[outcome_id].alternatives[alternative]
                    .name
                    .clone();
                let out_val = Value::Outcome {
                    ty: outcome_id,
                    alternative,
                    alternative_name: alt_name,
                    payload,
                };
                self.bind(var, out_val)?;
                self.scope().pc += 1;
                self.count("E-Capture");
                Ok(())
            }
            _ => fail(
                10,
                "E-Decide",
                "an operation completes where no decision or capture waits",
            ),
        }
    }

    fn check_effects(&self, uses: &[String], callee_name: &str) -> Result<(), Fail> {
        for effect in uses {
            for activation in &self.stack {
                if let ActivationKind::Control(cid) = activation.kind {
                    let caller = &self.program.controls[cid];
                    if !caller.uses.contains(effect) {
                        return fail(
                            9,
                            "E-Effect",
                            format!(
                                "`{callee_name}` has the effect `{effect}`, which `{}` does not allow",
                                caller.name
                            ),
                        );
                    }
                }
            }
            for allowed in &self.tasks[self.current_task].parent_allowances {
                if !allowed.contains(effect) {
                    return fail(
                        9,
                        "E-Effect",
                        format!(
                            "`{callee_name}` has the effect `{effect}`, which an enclosing task activation does not allow"
                        ),
                    );
                }
            }
        }
        Ok(())
    }

    /// [E-Extern], [E-Effect], [E-Host], [E-Resource]: one step of the host.
    fn external(&mut self, id: ControlId, arguments: Vec<Value>) -> Result<Answered, Fail> {
        let mut concrete_args = Vec::with_capacity(arguments.len());
        for arg in &arguments {
            concrete_args.push(self.deref_checked(arg)?);
        }
        let callee: &Control = &self.program.controls[id];
        if let Some(precondition) = &callee.precondition {
            let env = SignatureEnv {
                parameters: &concrete_args,
                old_parameters: &concrete_args,
                fields: &[],
            };
            if !self.evaluator().holds(precondition, &env)? {
                return fail(
                    7,
                    "E-Extern",
                    format!(
                        "the precondition of `{}` is false for ({})",
                        callee.name,
                        list(&concrete_args)
                    ),
                );
            }
        }
        self.check_effects(&callee.uses, &callee.name)?;

        // [E-Resource]: track resources passed by value vs by borrow.
        let mut consumed_resources = Vec::new();
        for (arg, param) in concrete_args.iter().zip(&callee.parameters) {
            let mut arg_res = Vec::new();
            collect_resources(arg, &mut arg_res);
            for &(rid, handle_id) in &arg_res {
                if !self
                    .resources
                    .get(&(rid, handle_id))
                    .copied()
                    .unwrap_or(false)
                {
                    return fail(
                        5,
                        "E-Resource",
                        format!(
                            "resource `{}#{handle_id}` passed to `{}` is not open",
                            self.program.resources[rid].name, callee.name
                        ),
                    );
                }
            }
            if !matches!(param.ty, Type::Ref(_, _)) {
                consumed_resources.extend(arg_res);
            }
        }

        let mut answer = match self.host.call(callee, &concrete_args, self.config) {
            Ok(answer) => answer,
            Err(detail) => return Ok(Answered::Ended(End::HostFailed(detail))),
        };
        let violation = |detail: String| Ok(Answered::Ended(End::HostViolation(detail)));
        let Some(index) = callee
            .contract
            .iter()
            .position(|entry| entry.name == answer.alternative)
        else {
            return violation(format!(
                "`{}` answered `{}`, which its contract does not list",
                callee.name, answer.alternative
            ));
        };
        let alternative = &callee.contract[index];
        for (value, field) in answer.payload.iter_mut().zip(&alternative.fields) {
            if let Err(detail) = self.lend(&arguments, value, &field.ty) {
                return violation(format!(
                    "`{}` answered `{}` with {detail} in `{}`",
                    callee.name, answer.alternative, field.name
                ));
            }
        }
        let typed = answer.payload.len() == alternative.fields.len()
            && answer
                .payload
                .iter()
                .zip(&alternative.fields)
                .all(|(value, field)| self.config.fits_in_program(self.program, value, &field.ty));
        if !typed {
            return violation(format!(
                "`{}` answered `{} {{{}}}`, which is not a payload of that alternative",
                callee.name,
                answer.alternative,
                list(&answer.payload)
            ));
        }

        // [E-Host]: validate any returned borrow/view payload against declared origins `∈ ȳ`.
        fn collect_refs(v: &Value, out: &mut Vec<(BorrowMode, RuntimePlace, TagId)>) {
            match v {
                Value::Ref { mode, place, tag } => out.push((*mode, place.clone(), *tag)),
                Value::Struct { fields, .. } => {
                    for f in fields {
                        collect_refs(f, out);
                    }
                }
                _ => {}
            }
        }
        let mut all_payload_refs: Vec<(BorrowMode, RuntimePlace, TagId)> = Vec::new();
        for (val, field) in answer.payload.iter().zip(&alternative.fields) {
            if self.program.contains_borrow_or_view(&field.ty) {
                let mut frefs = Vec::new();
                collect_refs(val, &mut frefs);
                if frefs.is_empty() && matches!(field.ty, Type::Ref(_, _)) {
                    return violation(format!(
                        "`{}` answered a non-borrow value for borrowed payload `{}`",
                        callee.name, field.name
                    ));
                }
                let mut allowed_sources = Vec::new();
                for &oidx in &field.origins {
                    collect_refs(&arguments[oidx], &mut allowed_sources);
                }
                for (rmode, rplace, rtag) in &frefs {
                    if !self.tags.is_alive(*rtag) {
                        return violation(format!(
                            "`{}` returned a dead borrow in `{}`",
                            callee.name, field.name
                        ));
                    }
                    let anc = self.tags.ancestors(*rtag);
                    let valid_origin = allowed_sources
                        .iter()
                        .any(|(_, aplace, atag)| anc.contains(atag) && aplace.contains(rplace));
                    if !valid_origin {
                        return violation(format!(
                            "`{}` returned a borrow in `{}` not derived from its declared origins",
                            callee.name, field.name
                        ));
                    }
                    all_payload_refs.push((*rmode, rplace.clone(), *rtag));
                }
            }
        }
        for i in 0..all_payload_refs.len() {
            for j in (i + 1)..all_payload_refs.len() {
                let (m1, p1, _) = &all_payload_refs[i];
                let (m2, p2, _) = &all_payload_refs[j];
                if (*m1 == BorrowMode::Exclusive || *m2 == BorrowMode::Exclusive) && p1.overlaps(p2)
                {
                    return violation(format!(
                        "`{}` returned overlapping exclusive borrows in its payload",
                        callee.name
                    ));
                }
            }
        }

        // [E-Resource]: resources taken by value are closed unless returned in
        // the payload; new resources in the payload are recorded as open.
        for &(rid, handle_id) in &consumed_resources {
            self.resources.insert((rid, handle_id), false);
        }
        let mut returned_resources = Vec::new();
        for val in &answer.payload {
            collect_resources(val, &mut returned_resources);
        }
        for &(rid, handle_id) in &returned_resources {
            if consumed_resources.contains(&(rid, handle_id)) {
                self.resources.insert((rid, handle_id), true);
            } else if let std::collections::btree_map::Entry::Vacant(e) =
                self.resources.entry((rid, handle_id))
            {
                e.insert(true);
            } else {
                return violation(format!(
                    "`{}` returned an already-used resource handle `{}#{handle_id}`",
                    callee.name, self.program.resources[rid].name
                ));
            }
        }
        if !consumed_resources.is_empty() || !returned_resources.is_empty() {
            self.count("E-Resource");
        }

        let mut concrete_payload = Vec::with_capacity(answer.payload.len());
        for val in &answer.payload {
            concrete_payload.push(self.deref_formula(val)?);
        }
        if let Some(condition) = &alternative.condition {
            let env = SignatureEnv {
                parameters: &concrete_args,
                old_parameters: &concrete_args,
                fields: &concrete_payload,
            };
            if !self.evaluator().holds(condition, &env)? {
                return violation(format!(
                    "`{}` answered `{} {{{}}}` for ({}), and the condition of the alternative is false",
                    callee.name,
                    answer.alternative,
                    list(&concrete_payload),
                    list(&concrete_args)
                ));
            }
        }
        if callee.is_pure(self.program) {
            let key = (id, concrete_args.clone());
            let given = (index, concrete_payload.clone());
            match self.answers.get(&key) {
                Some(earlier) if *earlier != given => {
                    return violation(format!(
                        "`{}` has no effect and answered ({}) in two ways",
                        callee.name,
                        list(&concrete_args)
                    ));
                }
                Some(_) => {}
                None => {
                    self.answers.insert(key, given);
                }
            }
        } else {
            self.trace.push(Event {
                control: callee.name.clone(),
                arguments: concrete_args,
                alternative: answer.alternative.clone(),
                payload: concrete_payload,
            });
        }
        self.count("E-Extern");
        Ok(Answered::Completed(index, answer.payload))
    }

    fn execute_builtin(
        &mut self,
        op: BuiltinOp,
        _target: Option<&Place>,
        arguments: &[Expr],
    ) -> Result<(usize, Vec<Value>), Fail> {
        let mut vals = self.eval_operands(arguments)?;
        match op {
            BuiltinOp::Push => {
                // [B5]: push is a write access to the whole vector.
                let elem = vals.remove(1);
                let Value::Ref { place, tag, .. } = vals.remove(0) else {
                    return fail(10, "E-Extern", "`push` requires an exclusive borrow");
                };
                self.access_tag(tag, &place, true)?;
                let Value::Vector(mut items) = self.read_place(&place)? else {
                    return fail(10, "E-Extern", "`push` on non-vector");
                };
                items.push(elem);
                self.write_runtime_place(&place, tag, Value::Vector(items), false)?;
                self.count("B5");
                Ok((0, Vec::new()))
            }
            BuiltinOp::Pop => {
                // [B5]: pop is a write access to the whole vector.
                let Value::Ref { place, tag, .. } = vals.remove(0) else {
                    return fail(10, "E-Extern", "`pop` requires an exclusive borrow");
                };
                self.access_tag(tag, &place, true)?;
                let Value::Vector(mut items) = self.read_place(&place)? else {
                    return fail(10, "E-Extern", "`pop` on non-vector");
                };
                self.count("B5");
                if let Some(last) = items.pop() {
                    self.write_runtime_place(&place, tag, Value::Vector(items), false)?;
                    Ok((0, vec![last]))
                } else {
                    Ok((1, Vec::new()))
                }
            }
            BuiltinOp::Take => {
                let Value::Vector(mut items) = vals.remove(0) else {
                    return fail(10, "E-Extern", "`take` on non-vector");
                };
                if items.is_empty() {
                    Ok((1, Vec::new()))
                } else {
                    let head = items.remove(0);
                    Ok((0, vec![head, Value::Vector(items)]))
                }
            }
            BuiltinOp::Get => {
                // `get(map: &k ⇀ v, key: &k) ■ found {value: &v ∈ map} │ missing`
                let raw_key = vals.remove(1);
                let key = self.deref_checked(&raw_key)?;
                let Value::Ref { place, tag, .. } = vals.remove(0) else {
                    return fail(10, "E-Extern", "`get` requires a map borrow");
                };
                self.access_tag(tag, &place, false)?;
                let Value::Map(entries) = self.read_place(&place)? else {
                    return fail(10, "E-Extern", "`get` on non-map");
                };
                if entries.contains_key(&key) {
                    let val_place = place.with_step(RuntimeStep::MapValue(key));
                    let val_tag =
                        self.create_borrow_tag(tag, val_place.clone(), BorrowMode::Shared)?;
                    Ok((
                        0,
                        vec![Value::Ref {
                            mode: BorrowMode::Shared,
                            place: val_place,
                            tag: val_tag,
                        }],
                    ))
                } else {
                    Ok((1, Vec::new()))
                }
            }
            BuiltinOp::Insert => {
                // [B5]: insert is a write access to the whole map.
                let value = vals.remove(2);
                let key = vals.remove(1);
                let Value::Ref { place, tag, .. } = vals.remove(0) else {
                    return fail(10, "E-Extern", "`insert` requires an exclusive borrow");
                };
                self.access_tag(tag, &place, true)?;
                let Value::Map(mut entries) = self.read_place(&place)? else {
                    return fail(10, "E-Extern", "`insert` on non-map");
                };
                let prev = entries.insert(key, value);
                self.write_runtime_place(&place, tag, Value::Map(entries), false)?;
                self.count("B5");
                match prev {
                    None => Ok((0, Vec::new())),
                    Some(old) => Ok((1, vec![old])),
                }
            }
            BuiltinOp::Remove => {
                // [B5]: remove is a write access to the whole map.
                let raw_key = vals.remove(1);
                let key = self.deref_checked(&raw_key)?;
                let Value::Ref { place, tag, .. } = vals.remove(0) else {
                    return fail(10, "E-Extern", "`remove` requires an exclusive borrow");
                };
                self.access_tag(tag, &place, true)?;
                let Value::Map(mut entries) = self.read_place(&place)? else {
                    return fail(10, "E-Extern", "`remove` on non-map");
                };
                let prev = entries.remove(&key);
                self.write_runtime_place(&place, tag, Value::Map(entries), false)?;
                self.count("B5");
                match prev {
                    Some(old) => Ok((0, vec![old])),
                    None => Ok((1, Vec::new())),
                }
            }
            BuiltinOp::EntryAt => {
                // `entry_at(map: &k ⇀ v, position: usize) ■ item {key: &k ∈ map, value: &v ∈ map, next: usize} │ finished`
                let pos = integer(vals.remove(1))?;
                let Value::Ref { place, tag, .. } = vals.remove(0) else {
                    return fail(10, "E-Extern", "`entry_at` requires a map borrow");
                };
                self.access_tag(tag, &place, false)?;
                let Value::Map(entries) = self.read_place(&place)? else {
                    return fail(10, "E-Extern", "`entry_at` on non-map");
                };
                let Some(idx) = pos
                    .to_i128()
                    .filter(|&i| i >= 0 && (i as usize) < entries.len())
                else {
                    return Ok((1, Vec::new()));
                };
                let (k, _) = entries.iter().nth(idx as usize).unwrap();
                let key_val = k.clone();
                let key_place = place.with_step(RuntimeStep::MapKey(key_val.clone()));
                let val_place = place.with_step(RuntimeStep::MapValue(key_val));
                let key_tag = self.create_borrow_tag(tag, key_place.clone(), BorrowMode::Shared)?;
                let val_tag = self.create_borrow_tag(tag, val_place.clone(), BorrowMode::Shared)?;
                let next = pos.plus(&Int::from_u64(1));
                Ok((
                    0,
                    vec![
                        Value::Ref {
                            mode: BorrowMode::Shared,
                            place: key_place,
                            tag: key_tag,
                        },
                        Value::Ref {
                            mode: BorrowMode::Shared,
                            place: val_place,
                            tag: val_tag,
                        },
                        Value::Int(next),
                    ],
                ))
            }
            BuiltinOp::Emit => {
                self.check_effects(&["console.write".to_string()], "emit")?;
                let raw_text = vals.remove(0);
                let text = self.deref_checked(&raw_text)?;
                self.trace.push(Event {
                    control: "emit".to_string(),
                    arguments: vec![text],
                    alternative: "done".to_string(),
                    payload: Vec::new(),
                });
                self.count("E-Extern");
                Ok((0, Vec::new()))
            }
        }
    }

    fn execute_operation(
        &mut self,
        op_kind: &Operation,
        arguments: &[Expr],
    ) -> Result<Option<Answered>, Fail> {
        match op_kind {
            Operation::Control(callee_id) => {
                let arg_values = self.eval_operands(arguments)?;
                let callee = &self.program.controls[*callee_id];
                if callee.body.is_none() {
                    return Ok(Some(self.external(*callee_id, arg_values)?));
                }
                // [E-Call]
                let mut entry_snapshots = Vec::with_capacity(arg_values.len());
                for v in &arg_values {
                    entry_snapshots.push(self.deref_formula(v)?);
                }
                if let Some(precondition) = &callee.precondition {
                    let env = SignatureEnv {
                        parameters: &entry_snapshots,
                        old_parameters: &entry_snapshots,
                        fields: &[],
                    };
                    if !self.evaluator().holds(precondition, &env)? {
                        return fail(
                            7,
                            "E-Call",
                            format!(
                                "the precondition of `{}` is false for ({})",
                                callee.name,
                                list(&entry_snapshots)
                            ),
                        );
                    }
                }
                self.push_control(*callee_id, arg_values, entry_snapshots);
                self.count("E-Call");
                Ok(None)
            }
            Operation::AwaitControl(callee_id) => {
                let arg_values = self.eval_operands(arguments)?;
                let callee = &self.program.controls[*callee_id];
                if callee.body.is_none() {
                    // [E-AwaitHost]: check precondition, effects, and resources before waiting or cancelling.
                    let mut concrete_args = Vec::with_capacity(arg_values.len());
                    for arg in &arg_values {
                        concrete_args.push(self.deref_checked(arg)?);
                    }
                    let callee = &self.program.controls[*callee_id];
                    if let Some(precondition) = &callee.precondition {
                        let env = SignatureEnv {
                            parameters: &concrete_args,
                            old_parameters: &concrete_args,
                            fields: &[],
                        };
                        if !self.evaluator().holds(precondition, &env)? {
                            return fail(
                                7,
                                "E-Extern",
                                format!(
                                    "the precondition of `{}` is false for ({})",
                                    callee.name,
                                    list(&concrete_args)
                                ),
                            );
                        }
                    }
                    self.check_effects(&callee.uses, &callee.name)?;
                    let mut consumed_resources = Vec::new();
                    for (arg, param) in concrete_args.iter().zip(&callee.parameters) {
                        let mut arg_res = Vec::new();
                        collect_resources(arg, &mut arg_res);
                        for &(rid, handle_id) in &arg_res {
                            if !self
                                .resources
                                .get(&(rid, handle_id))
                                .copied()
                                .unwrap_or(false)
                            {
                                return fail(
                                    5,
                                    "E-Resource",
                                    format!(
                                        "resource `{}#{handle_id}` passed to `{}` is not open",
                                        self.program.resources[rid].name, callee.name
                                    ),
                                );
                            }
                        }
                        if !matches!(param.ty, Type::Ref(_, _)) {
                            consumed_resources.extend(arg_res);
                        }
                    }
                    let is_cancellable = callee.is_cancellable();
                    if self.is_task_cancelled(self.current_task) && is_cancellable {
                        let param_is_ref: Vec<bool> = callee
                            .parameters
                            .iter()
                            .map(|p| matches!(p.ty, Type::Ref(_, _)))
                            .collect();
                        for (arg, is_ref) in concrete_args.iter().zip(param_is_ref) {
                            if !is_ref {
                                self.unwind_value_with_clause(arg, "E-Unwind")?;
                            }
                        }
                        let cancel_idx = self.program.controls[*callee_id]
                            .contract
                            .iter()
                            .position(|a| a.name == "cancelled")
                            .expect("cancellable control has `cancelled`");
                        self.complete(cancel_idx, Vec::new())?;
                        self.park_current(TaskState::Ready);
                        self.count("E-AwaitHost");
                        return Ok(None);
                    }
                    self.park_current(TaskState::WaitingHost {
                        callee: *callee_id,
                        arguments: arg_values,
                        concrete_args,
                        consumed_resources,
                    });
                    self.count("E-AwaitHost");
                    return Ok(None);
                }
                // [E-Await]: defined async control — bind parameters in the same task and give up turn.
                let mut entry_snapshots = Vec::with_capacity(arg_values.len());
                for v in &arg_values {
                    entry_snapshots.push(self.deref_formula(v)?);
                }
                if let Some(precondition) = &callee.precondition {
                    let env = SignatureEnv {
                        parameters: &entry_snapshots,
                        old_parameters: &entry_snapshots,
                        fields: &[],
                    };
                    if !self.evaluator().holds(precondition, &env)? {
                        return fail(
                            7,
                            "E-Call",
                            format!(
                                "the precondition of `{}` is false for ({})",
                                callee.name,
                                list(&entry_snapshots)
                            ),
                        );
                    }
                }
                self.push_control(*callee_id, arg_values, entry_snapshots);
                self.park_current(TaskState::Ready);
                self.count("E-Await");
                Ok(None)
            }
            Operation::AwaitNext(set_var, prod_id) => {
                let (scope_id, slot, owner_tag) = self.find_local_slot(*set_var)?;
                let Slot::Available(Value::TaskSet(set_id)) = slot else {
                    let var_name = &self.body().vars[*set_var].name;
                    return fail(
                        2,
                        "E-Var",
                        format!("`{var_name}` has been moved on this history"),
                    );
                };
                self.access_tag(owner_tag, &RuntimePlace::root(scope_id, *set_var), true)?;
                self.park_current(TaskState::WaitingNext {
                    set_id,
                    set_var: *set_var,
                    prod_id: *prod_id,
                });
                self.count("E-Next");
                Ok(None)
            }
            Operation::RunControl(callee_id) => {
                let arg_values = self.eval_operands(arguments)?;
                let callee = &self.program.controls[*callee_id];
                if callee.body.is_none() {
                    // Running an `extern async control` directly via `run f(ō)` ([E-Run], [E-Cancel]).
                    let mut concrete_args = Vec::with_capacity(arg_values.len());
                    for arg in &arg_values {
                        concrete_args.push(self.deref_checked(arg)?);
                    }
                    let callee = &self.program.controls[*callee_id];
                    if let Some(precondition) = &callee.precondition {
                        let env = SignatureEnv {
                            parameters: &concrete_args,
                            old_parameters: &concrete_args,
                            fields: &[],
                        };
                        if !self.evaluator().holds(precondition, &env)? {
                            return fail(
                                7,
                                "E-Extern",
                                format!(
                                    "the precondition of `{}` is false for ({})",
                                    callee.name,
                                    list(&concrete_args)
                                ),
                            );
                        }
                    }
                    self.check_effects(&callee.uses, &callee.name)?;
                    let is_cancellable = callee.is_cancellable();
                    if self.is_task_cancelled(self.current_task) && is_cancellable {
                        let param_is_ref: Vec<bool> = callee
                            .parameters
                            .iter()
                            .map(|p| matches!(p.ty, Type::Ref(_, _)))
                            .collect();
                        for (arg, is_ref) in concrete_args.iter().zip(param_is_ref) {
                            if !is_ref {
                                self.unwind_value_with_clause(arg, "E-Unwind")?;
                            }
                        }
                        let cancel_idx = self.program.controls[*callee_id]
                            .contract
                            .iter()
                            .position(|a| a.name == "cancelled")
                            .expect("cancellable control has `cancelled`");
                        self.count("E-Run");
                        return Ok(Some(Answered::Completed(cancel_idx, Vec::new())));
                    }
                    self.count("E-Run");
                    return Ok(Some(self.external(*callee_id, arg_values)?));
                }
                // Defined `async control` started as a nested run ([E-Run]).
                let mut entry_snapshots = Vec::with_capacity(arg_values.len());
                for v in &arg_values {
                    entry_snapshots.push(self.deref_formula(v)?);
                }
                if let Some(precondition) = &callee.precondition {
                    let env = SignatureEnv {
                        parameters: &entry_snapshots,
                        old_parameters: &entry_snapshots,
                        fields: &[],
                    };
                    if !self.evaluator().holds(precondition, &env)? {
                        return fail(
                            7,
                            "E-Call",
                            format!(
                                "the precondition of `{}` is false for ({})",
                                callee.name,
                                list(&entry_snapshots)
                            ),
                        );
                    }
                }
                let caller = self.current_task;
                let allowances = self.collect_allowances();
                self.park_current(TaskState::WaitingRun);
                let root_id = self.tasks.len();
                let root_act =
                    self.make_control_activation(*callee_id, arg_values, entry_snapshots);
                self.tasks.push(Task {
                    stack: Vec::new(),
                    state: TaskState::Ready,
                    member_of: None,
                    cancelled: false,
                    parent_allowances: allowances,
                });
                self.runs.push(TaskRun {
                    root_task: root_id,
                    caller_task: Some(caller),
                    tasks: vec![root_id],
                });
                self.stack = vec![root_act];
                self.current_task = root_id;
                self.has_turn = true;
                self.count("E-Run");
                Ok(None)
            }
            Operation::Builtin { op, target, .. } => {
                let (alt, payload) = self.execute_builtin(*op, target.as_ref(), arguments)?;
                Ok(Some(Answered::Completed(alt, payload)))
            }
            Operation::Outcome(_) => {
                let val = self.eval_expr(&arguments[0], true)?;
                let Value::Outcome {
                    alternative,
                    payload,
                    ..
                } = val
                else {
                    return fail(10, "E-Outcome", "`outcome` on non-outcome value");
                };
                self.count("E-Outcome");
                Ok(Some(Answered::Completed(alternative, payload)))
            }
            Operation::Variant { borrow, .. } => match borrow {
                None => {
                    let val = self.eval_expr(&arguments[0], true)?;
                    let Value::Variant {
                        constructor,
                        fields,
                        ..
                    } = val
                    else {
                        return fail(10, "E-Outcome", "variant decision on non-variant value");
                    };
                    self.count("E-Outcome");
                    Ok(Some(Answered::Completed(constructor, fields)))
                }
                Some(mode) => {
                    // [E-Outcome]: deciding a borrowed variant reborrows each field through it.
                    let val = self.eval_expr(&arguments[0], true)?;
                    let Value::Ref { place, tag, .. } = val else {
                        return fail(
                            10,
                            "E-Outcome",
                            "borrowed variant decision requires a borrow value",
                        );
                    };
                    self.access_tag(tag, &place, false)?;
                    let Value::Variant {
                        constructor,
                        fields,
                        ..
                    } = self.read_place(&place)?
                    else {
                        return fail(10, "E-Outcome", "variant decision on non-variant value");
                    };
                    let mut field_refs = Vec::with_capacity(fields.len());
                    for fidx in 0..fields.len() {
                        let fplace = place.with_step(RuntimeStep::VariantField(constructor, fidx));
                        let ftag = self.create_borrow_tag(tag, fplace.clone(), *mode)?;
                        field_refs.push(Value::Ref {
                            mode: *mode,
                            place: fplace,
                            tag: ftag,
                        });
                    }
                    self.count("E-Outcome");
                    Ok(Some(Answered::Completed(constructor, field_refs)))
                }
            },
        }
    }

    /// One step. `Ok(None)` when the configuration has a successor.
    fn step(&mut self) -> Result<Option<End>, Fail> {
        self.locate();
        let body = self.body();
        let (body_id, pc) = {
            let scope = self.scope();
            (scope.body, scope.pc)
        };
        let statements = &body.bodies[body_id].statements;
        let Some(statement) = statements.get(pc) else {
            // [E-Boundary]: `B₁` of a lexical boundary may fall off its end,
            // which completes site `d` with its single alternative.
            if matches!(self.scope().kind, ScopeKind::LexicalBoundary { .. }) {
                let top_scope = self
                    .stack
                    .last_mut()
                    .expect("an activation")
                    .scopes
                    .pop()
                    .unwrap();
                self.end_scope(&top_scope)?;
                let ScopeKind::LexicalBoundary {
                    site, parent_pc, ..
                } = top_scope.kind
                else {
                    unreachable!();
                };
                let parent = self.scope();
                parent.history.push((site, 0));
                parent.pc = parent_pc + 1;
                return Ok(None);
            }
            // [E-End]: a body never falls off its end.
            return fail(
                1,
                "E-End",
                "the body reaches its end and the history is not disposed",
            );
        };
        if !self.selects(&statement.selector) {
            self.count("E-Skip");
            self.scope().pc += 1;
            return Ok(None);
        }
        let command = statement.command.clone();
        match &command {
            Command::Bind { var, value } => {
                let value = self.eval_expr(value, true)?;
                self.bind(*var, value)?;
                self.scope().pc += 1;
                self.count("E-Bind");
            }
            Command::Unpack { vars, value, .. } => {
                let val = self.eval_expr(value, true)?;
                let Value::Struct { fields, .. } = val else {
                    return fail(10, "E-Unpack", "unpacking a non-struct value");
                };
                for (var, fval) in vars.iter().zip(fields) {
                    self.bind(*var, fval)?;
                }
                self.scope().pc += 1;
                self.count("E-Unpack");
            }
            Command::Capture {
                operation,
                arguments,
                ..
            } => {
                if let Some(answered) = self.execute_operation(operation, arguments)? {
                    match answered {
                        Answered::Ended(end) => return Ok(Some(end)),
                        Answered::Completed(alternative, payload) => {
                            self.complete(alternative, payload)?;
                        }
                    }
                }
            }
            Command::Assign { var, value } => {
                let value = self.eval_expr(value, true)?;
                let var_name = self.body().vars[*var].name.clone();
                let var_ty = self.body().vars[*var].ty.clone();
                let (scope_id, slot, owner_tag) = self.find_local_slot(*var).map_err(|_| Fail {
                    state: 2,
                    clause: "E-Assign",
                    detail: format!("`{var_name}` has no slot on this history"),
                })?;
                if matches!(var_ty, Type::Ref(_, _)) {
                    let Slot::Available(Value::Ref { place, tag, .. }) = slot else {
                        return fail(
                            2,
                            "E-Assign",
                            format!("`{var_name}` has been moved on this history"),
                        );
                    };
                    self.write_runtime_place(&place, tag, value, true)?;
                } else {
                    let own_place = RuntimePlace::root(scope_id, *var);
                    self.write_runtime_place(&own_place, owner_tag, value, true)?;
                }
                self.scope().pc += 1;
                self.count("E-Assign");
            }
            Command::AssignPlace { target, value } => {
                let value = self.eval_expr(value, true)?;
                let (rplace, tag) = self.resolve_place(target)?;
                self.write_runtime_place(&rplace, tag, value, true)?;
                self.scope().pc += 1;
                self.count("E-Assign");
            }
            Command::Oblige(formula) => {
                if !self.formula(formula)? {
                    return fail(7, "E-Oblige", "the obligation is false");
                }
                self.scope().pc += 1;
                self.count("E-Oblige");
            }
            Command::Test { site, condition } => {
                let value = self.eval_expr(condition, false)?;
                let alternative = if boolean(value)? { 0 } else { 1 };
                let scope = self.scope();
                scope.history.push((*site, alternative));
                scope.pc += 1;
                self.count("E-Test");
            }
            Command::Decide {
                op_kind, arguments, ..
            } => {
                if let Some(answered) = self.execute_operation(op_kind, arguments)? {
                    match answered {
                        Answered::Ended(end) => return Ok(Some(end)),
                        Answered::Completed(alternative, payload) => {
                            self.complete(alternative, payload)?;
                        }
                    }
                }
            }
            Command::Loop {
                body: inner,
                initial,
                ..
            } => {
                let values = self.eval_operands(initial)?;
                if let Err(stuck) = self.enter(*inner, values, "E-Loop") {
                    if let Some(popped) = self.stack.last_mut().expect("an activation").scopes.pop()
                    {
                        for (_, _, tag) in &popped.slots {
                            self.tags.kill_with_descendants(*tag);
                        }
                    }
                    return Err(stuck);
                }
                self.count("E-Loop");
            }
            Command::Boundary {
                site,
                body: b1,
                captures,
                contingency_vars,
                message_var,
                contingency: b2,
            } => {
                let mut cap_values = Vec::with_capacity(captures.len());
                for &cvar in captures {
                    let cty = self.body().vars[cvar].ty.clone();
                    let val = self.eval_expr(&Expr::Var(VarRef::Local(cvar), cty), true)?;
                    cap_values.push(val);
                }
                let parent_pc = self.scope().pc;
                let scope_id = self.alloc_scope_id();
                self.stack
                    .last_mut()
                    .expect("an activation")
                    .scopes
                    .push(Scope {
                        id: scope_id,
                        body: *b1,
                        pc: 0,
                        slots: Vec::new(),
                        history: Vec::new(),
                        kind: ScopeKind::LexicalBoundary {
                            site: *site,
                            parent_pc,
                            captures: cap_values,
                            contingency_body: *b2,
                            contingency_vars: contingency_vars.clone(),
                            message_var: *message_var,
                        },
                    });
                self.count("E-Boundary");
            }
            Command::Supervise {
                boundary,
                arguments,
            } => {
                let values = self.eval_operands(arguments)?;
                let scope_id = self.alloc_scope_id();
                let mut slots = Vec::with_capacity(values.len());
                for (i, v) in values.into_iter().enumerate() {
                    let tag = self.tags.new_owner(scope_id, i);
                    slots.push((i, Slot::Available(v), tag));
                }
                self.stack.push(Activation {
                    kind: ActivationKind::Boundary {
                        id: *boundary,
                        in_contingency: None,
                    },
                    arguments: Vec::new(),
                    borrowed: Vec::new(),
                    scopes: vec![Scope {
                        id: scope_id,
                        body: 0,
                        pc: 0,
                        slots,
                        history: Vec::new(),
                        kind: ScopeKind::Normal,
                    }],
                });
                self.count("E-Supervise");
            }
            Command::Spawn {
                control,
                arguments,
                set,
            } => {
                let arg_values = self.eval_operands(arguments)?;
                let (scope_id, slot, owner_tag) = self.find_local_slot(*set)?;
                let Slot::Available(Value::TaskSet(set_id)) = slot else {
                    let var_name = &self.body().vars[*set].name;
                    return fail(
                        2,
                        "E-Var",
                        format!("`{var_name}` has been moved on this history"),
                    );
                };
                self.access_tag(owner_tag, &RuntimePlace::root(scope_id, *set), true)?;
                let mut entry_snapshots = Vec::with_capacity(arg_values.len());
                for v in &arg_values {
                    entry_snapshots.push(self.deref_formula(v)?);
                }
                let callee = &self.program.controls[*control];
                if let Some(precondition) = &callee.precondition {
                    let env = SignatureEnv {
                        parameters: &entry_snapshots,
                        old_parameters: &entry_snapshots,
                        fields: &[],
                    };
                    if !self.evaluator().holds(precondition, &env)? {
                        return fail(
                            7,
                            "E-Spawn",
                            format!(
                                "the precondition of `{}` is false for ({})",
                                callee.name,
                                list(&entry_snapshots)
                            ),
                        );
                    }
                }
                let allowances = self.collect_allowances();
                let member_act =
                    self.make_control_activation(*control, arg_values, entry_snapshots);
                let tid = self.tasks.len();
                self.tasks.push(Task {
                    stack: vec![member_act],
                    state: TaskState::Ready,
                    member_of: Some(set_id),
                    cancelled: false,
                    parent_allowances: allowances,
                });
                self.task_sets[set_id as usize].members.push(tid);
                self.runs.last_mut().expect("a run").tasks.push(tid);
                self.scope().pc += 1;
                self.count("E-Spawn");
            }
            Command::Cancel { set } => {
                let (scope_id, slot, owner_tag) = self.find_local_slot(*set)?;
                let Slot::Available(Value::TaskSet(set_id)) = slot else {
                    let var_name = &self.body().vars[*set].name;
                    return fail(
                        2,
                        "E-Var",
                        format!("`{var_name}` has been moved on this history"),
                    );
                };
                self.access_tag(owner_tag, &RuntimePlace::root(scope_id, *set), false)?;
                let members = self.task_sets[set_id as usize].members.clone();
                for mid in members {
                    self.tasks[mid].cancelled = true;
                }
                self.withdraw_cancelled_host_waits()?;
                self.scope().pc += 1;
                self.count("E-Cancel");
            }
            Command::Again {
                body: target,
                arguments,
            } => {
                let values = self.eval_operands(arguments)?;
                while let Some(scope) = self.stack.last_mut().expect("an activation").scopes.pop() {
                    let done = scope.body == *target;
                    self.end_scope(&scope)?;
                    if done {
                        break;
                    }
                }
                self.enter(*target, values, "E-Again")?;
                self.count("E-Again");
            }
            Command::Leave {
                alternative,
                payload,
            } => {
                let values = self.eval_operands(payload)?;
                loop {
                    let scope = self
                        .stack
                        .last_mut()
                        .expect("an activation")
                        .scopes
                        .pop()
                        .expect("a loop scope");
                    let is_loop = matches!(scope.kind, ScopeKind::Loop);
                    self.end_scope(&scope)?;
                    if is_loop {
                        break;
                    }
                }
                let body = self.body();
                let scope = self.scope();
                let Command::Loop { site, arms, .. } =
                    &body.bodies[scope.body].statements[scope.pc].command
                else {
                    return fail(
                        10,
                        "E-Leave",
                        "a loop is left where no loop statement waits",
                    );
                };
                let site = *site;
                let arm_vars = arms[*alternative].clone();
                scope.history.push((site, *alternative));
                scope.pc += 1;
                for (var, value) in arm_vars.iter().zip(values) {
                    self.bind(*var, value)?;
                }
                self.count("E-Leave");
            }
            Command::Exit {
                alternative,
                payload,
            } => {
                let values = self.eval_operands(payload)?;
                let act = self.stack.last().expect("an activation");
                let ActivationKind::Control(control_id) = act.kind else {
                    return fail(10, "E-Exit", "`■` inside a named boundary");
                };
                let control = &self.program.controls[control_id];
                let entry = &control.contract[*alternative];
                if let Some(condition) = &entry.condition {
                    // A parameter that is or holds a borrow stands for the
                    // value at completion, read through the borrow as it was
                    // passed: the body may have passed the parameter on.
                    let mut final_params = act.arguments.clone();
                    for (index, borrow) in act.borrowed.iter().enumerate() {
                        if let Some(borrow) = borrow {
                            final_params[index] = self.deref_formula(borrow)?;
                        }
                    }
                    let mut concrete_fields = Vec::with_capacity(values.len());
                    for v in &values {
                        concrete_fields.push(self.deref_formula(v)?);
                    }
                    let env = SignatureEnv {
                        parameters: &final_params,
                        old_parameters: &act.arguments,
                        fields: &concrete_fields,
                    };
                    if !self.evaluator().holds(condition, &env)? {
                        return fail(
                            7,
                            "E-Exit",
                            format!(
                                "the condition of `{}` is false for the payload {{{}}}",
                                entry.name,
                                list(&concrete_fields)
                            ),
                        );
                    }
                }
                // [E-Scope], [B4] for every scope of the activation, innermost first.
                let mut scopes =
                    std::mem::take(&mut self.stack.last_mut().expect("an activation").scopes);
                while let Some(scope) = scopes.pop() {
                    self.end_scope(&scope)?;
                }
                let _popped = self.stack.pop().expect("an activation");
                self.count("E-Exit");
                if self.stack.is_empty() {
                    let cur = self.current_task;
                    if let Some(set_id) = self.tasks[cur].member_of {
                        // [E-Done]: member finishes and keeps payload until `[E-Next]`.
                        self.tasks[cur].state = TaskState::Done {
                            alternative: *alternative,
                            payload: values,
                        };
                        self.task_sets[set_id as usize].done_queue.push_back(cur);
                        self.has_turn = false;
                        self.count("E-Done");
                        return Ok(None);
                    }
                    if self.runs.len() > 1 {
                        // Nested `run` root finishes: deliver outcome to caller waiting at `run` ([E-Run]).
                        let finished_run = self.runs.pop().expect("nested run");
                        self.tasks[cur].state = TaskState::Stopped;
                        let caller = finished_run.caller_task.expect("nested run has caller");
                        self.activate_task(caller);
                        self.locate();
                        self.complete(*alternative, values)?;
                        self.count("E-Done");
                        return Ok(None);
                    }
                    // Materialize final observable payload after scope-end tag kills
                    // so returning a dangling borrow of a local triggers X4 B1.
                    let mut observable = Vec::with_capacity(values.len());
                    for v in &values {
                        observable.push(self.deref_checked(v)?);
                    }
                    let alt_name = self.program.controls[control_id].contract[*alternative]
                        .name
                        .clone();
                    return Ok(Some(End::Done {
                        alternative: alt_name,
                        payload: observable,
                    }));
                }
                self.locate();
                self.complete(*alternative, values)?;
            }
            Command::Fault { message, .. } => {
                let Value::String(msg) = self.eval_expr(message, false)? else {
                    return fail(10, "E-Fault", "fault message is not a string");
                };
                self.count("E-Fault");
                // [E-Supervise]: a new `fault` is one of the ends of the
                // contingency of a named boundary, and leaves it. Anywhere
                // else the control permits `faults` or a boundary of the
                // activation encloses the statement; the boundary of a
                // contingency no longer does ([F5]).
                if !self.in_named_contingency() && !self.current_permits_faults() {
                    return fail(
                        8,
                        "E-Fault",
                        format!(
                            "`{}` does not permit `faults` and no boundary encloses this statement",
                            self.current_name()
                        ),
                    );
                }
                return self.unwind(msg);
            }
            Command::Impossible => return fail(6, "E-Impossible", "`⊥` runs"),
            Command::Terminate(None) => {
                // [E-Supervise]: the body of a named boundary ends, and the
                // supervising control goes on with its next statement.
                if !matches!(
                    self.stack.last().expect("an activation").kind,
                    ActivationKind::Boundary { .. }
                ) || self.stack.len() < 2
                {
                    return fail(
                        10,
                        "E-Supervise",
                        "`terminate` outside a body of a named boundary",
                    );
                }
                let mut scopes =
                    std::mem::take(&mut self.stack.last_mut().expect("an activation").scopes);
                while let Some(scope) = scopes.pop() {
                    self.end_scope(&scope)?;
                }
                self.stack.pop();
                self.scope().pc += 1;
                self.count("E-Supervise");
            }
            Command::Terminate(Some(status)) => {
                // [E-Contingency]: in the entry control only. Every scope of
                // the activation ends by [E-Scope], and the execution is
                // final with the status.
                let entry = self.stack.len() == 1
                    && self.runs.len() == 1
                    && self.tasks[self.current_task].member_of.is_none()
                    && matches!(
                        self.stack.last().expect("an activation").kind,
                        ActivationKind::Control(_)
                    );
                if !entry {
                    return fail(
                        10,
                        "E-Contingency",
                        "`terminate n` outside the entry control",
                    );
                }
                let mut scopes =
                    std::mem::take(&mut self.stack.last_mut().expect("an activation").scopes);
                while let Some(scope) = scopes.pop() {
                    self.end_scope(&scope)?;
                }
                self.stack.pop();
                self.count("E-Contingency");
                return Ok(Some(End::Terminated(*status)));
            }
            Command::Escalate => {
                // [E-Contingency], [E-Supervise]: the original fault goes on
                // outward from the contingency.
                let lexical = self
                    .stack
                    .last()
                    .expect("an activation")
                    .scopes
                    .iter()
                    .rev()
                    .find_map(|scope| match &scope.kind {
                        ScopeKind::LexicalContingency { fault_message } => {
                            Some(fault_message.clone())
                        }
                        _ => None,
                    });
                let message = match lexical {
                    Some(message) => {
                        if !self.current_permits_faults() {
                            return fail(
                                8,
                                "E-Unwind",
                                format!(
                                    "`{}` does not permit `faults` and no boundary encloses the one that escalates",
                                    self.current_name()
                                ),
                            );
                        }
                        message
                    }
                    None => {
                        let ActivationKind::Boundary {
                            in_contingency: Some(message),
                            ..
                        } = self.stack.last().expect("an activation").kind.clone()
                        else {
                            return fail(10, "E-Contingency", "`escalate` outside contingency");
                        };
                        message
                    }
                };
                return self.unwind(message);
            }
            Command::Recover { body: target } => {
                // [E-Contingency]: the loop starts again with its own
                // parameters, read as operands are ([E-Var]): [F5] keeps
                // them as they were when the boundary was entered.
                let operands: Vec<Expr> = body.bodies[*target]
                    .head
                    .as_ref()
                    .expect("a loop body")
                    .parameters
                    .iter()
                    .map(|var| Expr::Var(VarRef::Local(*var), body.vars[*var].ty.clone()))
                    .collect();
                let values = self.eval_operands(&operands)?;
                let activation = self.stack.last_mut().expect("an activation");
                if !activation.scopes.iter().any(|scope| scope.body == *target) {
                    return fail(10, "E-Contingency", "`recover` names no loop that runs");
                }
                while let Some(scope) = self.stack.last_mut().expect("an activation").scopes.pop() {
                    let done = scope.body == *target;
                    self.end_scope(&scope)?;
                    if done {
                        break;
                    }
                }
                self.enter(*target, values, "E-Again")?;
                self.count("E-Contingency");
            }
        }
        Ok(None)
    }

    fn make_control_activation(
        &mut self,
        control: ControlId,
        arguments: Vec<Value>,
        entry_snapshots: Vec<Value>,
    ) -> Activation {
        let scope_id = self.alloc_scope_id();
        let parameters = &self.program.controls[control].parameters;
        let borrowed = arguments
            .iter()
            .zip(parameters)
            .map(|(value, parameter)| {
                self.program
                    .contains_borrow_or_view(&parameter.ty)
                    .then(|| value.clone())
            })
            .collect();
        let mut slots = Vec::with_capacity(arguments.len());
        for (i, v) in arguments.into_iter().enumerate() {
            let tag = self.tags.new_owner(scope_id, i);
            slots.push((i, Slot::Available(v), tag));
        }
        let scope = Scope {
            id: scope_id,
            body: 0,
            pc: 0,
            slots,
            history: Vec::new(),
            kind: ScopeKind::Normal,
        };
        Activation {
            kind: ActivationKind::Control(control),
            arguments: entry_snapshots,
            borrowed,
            scopes: vec![scope],
        }
    }

    fn push_control(
        &mut self,
        control: ControlId,
        arguments: Vec<Value>,
        entry_snapshots: Vec<Value>,
    ) {
        let act = self.make_control_activation(control, arguments, entry_snapshots);
        self.stack.push(act);
    }

    /// Completes one `WaitingHost` task chosen by the host ([E-Turn], [E-AwaitHost]).
    fn complete_waiting_host(&mut self, tid: usize) -> Result<Option<End>, Fail> {
        let prev = std::mem::replace(&mut self.tasks[tid].state, TaskState::Ready);
        let TaskState::WaitingHost {
            callee,
            arguments,
            concrete_args,
            consumed_resources,
        } = prev
        else {
            unreachable!();
        };
        // Swap `tid`'s stack in so `deref_formula`, `complete`, and `locate` see `tid`.
        self.stack = std::mem::take(&mut self.tasks[tid].stack);
        self.current_task = tid;
        self.locate();

        let callee_ctrl = &self.program.controls[callee];
        let mut answer = match self.host.call(callee_ctrl, &concrete_args, self.config) {
            Ok(answer) => answer,
            Err(detail) => {
                self.tasks[tid].stack = std::mem::take(&mut self.stack);
                return Ok(Some(End::HostFailed(detail)));
            }
        };
        let finish_violation = |machine: &mut Machine<'_>, detail: String| {
            machine.tasks[tid].stack = std::mem::take(&mut machine.stack);
            Ok(Some(End::HostViolation(detail)))
        };
        let Some(index) = callee_ctrl
            .contract
            .iter()
            .position(|entry| entry.name == answer.alternative)
        else {
            let detail = format!(
                "`{}` answered `{}`, which its contract does not list",
                callee_ctrl.name, answer.alternative
            );
            return finish_violation(self, detail);
        };
        let alternative = &callee_ctrl.contract[index];
        for (value, field) in answer.payload.iter_mut().zip(&alternative.fields) {
            if let Err(detail) = self.lend(&arguments, value, &field.ty) {
                let detail = format!(
                    "`{}` answered `{}` with {detail} in `{}`",
                    callee_ctrl.name, answer.alternative, field.name
                );
                return finish_violation(self, detail);
            }
        }
        let typed = answer.payload.len() == alternative.fields.len()
            && answer
                .payload
                .iter()
                .zip(&alternative.fields)
                .all(|(value, field)| self.config.fits_in_program(self.program, value, &field.ty));
        if !typed {
            let detail = format!(
                "`{}` answered `{} {{{}}}`, which is not a payload of that alternative",
                callee_ctrl.name,
                answer.alternative,
                list(&answer.payload)
            );
            return finish_violation(self, detail);
        }

        // [E-Host]: validate returned borrows/views against declared origins.
        fn collect_refs(v: &Value, out: &mut Vec<(BorrowMode, RuntimePlace, TagId)>) {
            match v {
                Value::Ref { mode, place, tag } => out.push((*mode, place.clone(), *tag)),
                Value::Struct { fields, .. } => {
                    for f in fields {
                        collect_refs(f, out);
                    }
                }
                _ => {}
            }
        }
        let mut all_payload_refs = Vec::new();
        for (val, field) in answer.payload.iter().zip(&alternative.fields) {
            if self.program.contains_borrow_or_view(&field.ty) {
                let mut frefs = Vec::new();
                collect_refs(val, &mut frefs);
                if frefs.is_empty() && matches!(field.ty, Type::Ref(_, _)) {
                    let detail = format!(
                        "`{}` answered a non-borrow value for borrowed payload `{}`",
                        callee_ctrl.name, field.name
                    );
                    return finish_violation(self, detail);
                }
                let mut allowed_sources = Vec::new();
                for &oidx in &field.origins {
                    collect_refs(&arguments[oidx], &mut allowed_sources);
                }
                for (rmode, rplace, rtag) in &frefs {
                    if !self.tags.is_alive(*rtag) {
                        let detail = format!(
                            "`{}` returned a dead borrow in `{}`",
                            callee_ctrl.name, field.name
                        );
                        return finish_violation(self, detail);
                    }
                    let anc = self.tags.ancestors(*rtag);
                    let valid_origin = allowed_sources
                        .iter()
                        .any(|(_, aplace, atag)| anc.contains(atag) && aplace.contains(rplace));
                    if !valid_origin {
                        let detail = format!(
                            "`{}` returned a borrow in `{}` not derived from its declared origins",
                            callee_ctrl.name, field.name
                        );
                        return finish_violation(self, detail);
                    }
                    all_payload_refs.push((*rmode, rplace.clone(), *rtag));
                }
            }
        }
        for i in 0..all_payload_refs.len() {
            for j in (i + 1)..all_payload_refs.len() {
                let (m1, p1, _) = &all_payload_refs[i];
                let (m2, p2, _) = &all_payload_refs[j];
                if (*m1 == BorrowMode::Exclusive || *m2 == BorrowMode::Exclusive) && p1.overlaps(p2)
                {
                    let detail = format!(
                        "`{}` returned overlapping exclusive borrows in its payload",
                        callee_ctrl.name
                    );
                    return finish_violation(self, detail);
                }
            }
        }

        // [E-Resource]: update resource table.
        for &(rid, handle_id) in &consumed_resources {
            self.resources.insert((rid, handle_id), false);
        }
        let mut returned_resources = Vec::new();
        for val in &answer.payload {
            collect_resources(val, &mut returned_resources);
        }
        for &(rid, handle_id) in &returned_resources {
            if consumed_resources.contains(&(rid, handle_id)) {
                self.resources.insert((rid, handle_id), true);
            } else if let std::collections::btree_map::Entry::Vacant(e) =
                self.resources.entry((rid, handle_id))
            {
                e.insert(true);
            } else {
                let detail = format!(
                    "`{}` returned an already-used resource handle `{}#{handle_id}`",
                    callee_ctrl.name, self.program.resources[rid].name
                );
                return finish_violation(self, detail);
            }
        }
        if !consumed_resources.is_empty() || !returned_resources.is_empty() {
            self.count("E-Resource");
        }

        let mut concrete_payload = Vec::with_capacity(answer.payload.len());
        for val in &answer.payload {
            concrete_payload.push(self.deref_formula(val)?);
        }
        if let Some(condition) = &alternative.condition {
            let env = SignatureEnv {
                parameters: &concrete_args,
                old_parameters: &concrete_args,
                fields: &concrete_payload,
            };
            if !self.evaluator().holds(condition, &env)? {
                let detail = format!(
                    "`{}` answered `{} {{{}}}` for ({}), and the condition of the alternative is false",
                    callee_ctrl.name,
                    answer.alternative,
                    list(&concrete_payload),
                    list(&concrete_args)
                );
                return finish_violation(self, detail);
            }
        }
        if !callee_ctrl.is_pure(self.program) {
            self.trace.push(Event {
                control: callee_ctrl.name.clone(),
                arguments: concrete_args,
                alternative: answer.alternative,
                payload: concrete_payload,
            });
        }
        self.count("E-Extern");
        self.complete(index, answer.payload)?;
        self.tasks[tid].stack = std::mem::take(&mut self.stack);
        self.tasks[tid].state = TaskState::Ready;
        Ok(None)
    }

    /// Top-level step with cooperative task scheduling ([E-Turn]).
    fn step_scheduler(&mut self) -> Result<Option<End>, Fail> {
        if self.has_turn {
            return self.step();
        }
        let top_run_root = self.runs.last().expect("a run").root_task;
        self.turns_taken += 1;
        if !self.is_task_cancelled(top_run_root) && self.host.should_cancel_root(self.turns_taken) {
            self.tasks[top_run_root].cancelled = true;
            self.withdraw_cancelled_host_waits()?;
        }

        let run_tasks = self.runs.last().expect("a run").tasks.clone();
        let mut ready = Vec::new();
        for &tid in &run_tasks {
            match self.tasks[tid].state {
                TaskState::Ready => ready.push(tid),
                TaskState::WaitingNext { set_id, .. } => {
                    let set = &self.task_sets[set_id as usize];
                    if set.members.is_empty() || !set.done_queue.is_empty() {
                        ready.push(tid);
                    }
                }
                _ => {}
            }
        }
        if !ready.is_empty() {
            let choice = self.host.pick_turn(ready.len()) % ready.len();
            let tid = ready[choice];
            self.count("E-Turn");
            if let TaskState::WaitingNext {
                set_id,
                set_var,
                prod_id,
            } = self.tasks[tid].state
            {
                self.activate_task(tid);
                self.locate();
                if self.task_sets[set_id as usize].members.is_empty() {
                    // Mark `x`'s slot moved (`◌`) and complete with `empty` ([E-Next]).
                    let (scope_id, _, _) = self.find_local_slot(set_var)?;
                    if let Some(slot_ref) = self.slot_mut(scope_id, set_var) {
                        *slot_ref = Slot::Moved;
                    }
                    let empty_idx = self.program.controls[prod_id].contract.len();
                    self.complete(empty_idx, Vec::new())?;
                } else {
                    let done_tid = self.task_sets[set_id as usize]
                        .done_queue
                        .pop_front()
                        .expect("done member");
                    self.task_sets[set_id as usize]
                        .members
                        .retain(|&m| m != done_tid);
                    let prev =
                        std::mem::replace(&mut self.tasks[done_tid].state, TaskState::Stopped);
                    let TaskState::Done {
                        alternative,
                        payload,
                    } = prev
                    else {
                        unreachable!();
                    };
                    self.complete(alternative, payload)?;
                }
                return Ok(None);
            }
            self.activate_task(tid);
            return Ok(None);
        }

        // No task is ready: let the host complete a waiting extern async operation ([E-Turn]).
        let mut waiting_tids = Vec::new();
        for &tid in &run_tasks {
            if matches!(self.tasks[tid].state, TaskState::WaitingHost { .. }) {
                waiting_tids.push(tid);
            }
        }
        if waiting_tids.is_empty() {
            return Ok(Some(End::HostFailed(
                "no ready or waiting task in run".to_string(),
            )));
        }
        let descriptors: Vec<(&Control, &[Value])> = waiting_tids
            .iter()
            .map(|&tid| match &self.tasks[tid].state {
                TaskState::WaitingHost {
                    callee,
                    concrete_args,
                    ..
                } => (&self.program.controls[*callee], concrete_args.as_slice()),
                _ => unreachable!(),
            })
            .collect();
        let widx = self.host.pick_waiting(&descriptors) % waiting_tids.len();
        let chosen = waiting_tids[widx];
        self.count("E-Turn");
        self.complete_waiting_host(chosen)
    }

    /// Wraps top-level entry arguments that have borrow or view types in
    /// synthetic `ScopeId = 0` owner slots + live `Value::Ref` borrows.
    fn wrap_entry_arg(&mut self, value: Value, ty: &Type) -> Result<Value, Fail> {
        match ty {
            Type::Ref(mode, _) => {
                let slot_idx = self.entry_slots.len();
                let owner_tag = self.tags.new_owner(0, slot_idx);
                self.entry_slots
                    .push((slot_idx, Slot::Available(value), owner_tag));
                let place = RuntimePlace::root(0, slot_idx);
                let tag = self.create_borrow_tag(owner_tag, place.clone(), *mode)?;
                Ok(Value::Ref {
                    mode: *mode,
                    place,
                    tag,
                })
            }
            Type::Struct(sid, _) if self.program.structs[*sid].is_view => {
                let Value::Struct { ty, name, fields } = value else {
                    return Ok(value);
                };
                let fdefs: Vec<Type> = self.program.structs[*sid]
                    .fields
                    .iter()
                    .map(|f| f.ty.clone())
                    .collect();
                let mut wrapped = Vec::with_capacity(fields.len());
                for (fval, fty) in fields.into_iter().zip(&fdefs) {
                    wrapped.push(self.wrap_entry_arg(fval, fty)?);
                }
                Ok(Value::Struct {
                    ty,
                    name,
                    fields: wrapped,
                })
            }
            _ => Ok(value),
        }
    }
}

fn update_nested(
    current: &mut Value,
    steps: &[RuntimeStep],
    new_val: Value,
) -> Result<Value, Fail> {
    let (first, rest) = steps.split_first().expect("non-empty steps");
    match first {
        RuntimeStep::Field(fidx) => {
            let Value::Struct { fields, .. } = current else {
                return fail(10, "E-Assign", "field assignment on non-struct");
            };
            if rest.is_empty() {
                Ok(std::mem::replace(&mut fields[*fidx], new_val))
            } else {
                update_nested(&mut fields[*fidx], rest, new_val)
            }
        }
        RuntimeStep::Index(idx) => {
            let Value::Vector(items) = current else {
                return fail(10, "E-Assign", "index assignment on non-vector");
            };
            let len = items.len();
            let Some(elem) = items.get_mut(*idx) else {
                return fail(
                    7,
                    "E-Index",
                    format!("index {idx} is out of bounds for length {len}"),
                );
            };
            if rest.is_empty() {
                Ok(std::mem::replace(elem, new_val))
            } else {
                update_nested(elem, rest, new_val)
            }
        }
        RuntimeStep::VariantField(cidx, fidx) => {
            let Value::Variant {
                constructor,
                fields,
                ..
            } = current
            else {
                return fail(10, "E-Assign", "variant field assignment on non-variant");
            };
            if *constructor != *cidx || *fidx >= fields.len() {
                return fail(4, "B1", "variant constructor changed under borrow");
            }
            if rest.is_empty() {
                Ok(std::mem::replace(&mut fields[*fidx], new_val))
            } else {
                update_nested(&mut fields[*fidx], rest, new_val)
            }
        }
        RuntimeStep::MapValue(key) => {
            let Value::Map(entries) = current else {
                return fail(10, "E-Assign", "map value assignment on non-map");
            };
            let Some(val) = entries.get_mut(key) else {
                return fail(4, "B1", "map key removed under borrow");
            };
            if rest.is_empty() {
                Ok(std::mem::replace(val, new_val))
            } else {
                update_nested(val, rest, new_val)
            }
        }
        RuntimeStep::MapKey(_) => fail(4, "B1", "cannot assign through a map key borrow"),
    }
}

/// Whether `formula`, over the parameters of a signature and the fields of one
/// alternative, holds for `arguments` and `payload` ([E-Formula]).
pub fn signature_holds(
    program: &Program,
    config: &Config,
    formula: &Expr,
    arguments: &[Value],
    payload: &[Value],
) -> bool {
    let env = SignatureEnv {
        parameters: arguments,
        old_parameters: arguments,
        fields: payload,
    };
    let evaluator = Evaluator { program, config };
    evaluator.holds(formula, &env).unwrap_or(false)
}

/// Runs the control `entry` on `arguments` until the execution ends, is
/// stuck, or the fuel runs out.
pub fn run(
    program: &Program,
    entry: &str,
    arguments: Vec<Value>,
    host: &mut dyn Host,
    config: &Config,
) -> Run {
    let mut machine = Machine {
        program,
        config,
        host,
        entry_slots: Vec::new(),
        tags: TagTable::new(),
        next_scope_id: 1,
        stack: Vec::new(),
        tasks: vec![Task {
            stack: Vec::new(),
            state: TaskState::Ready,
            member_of: None,
            cancelled: false,
            parent_allowances: Vec::new(),
        }],
        task_sets: Vec::new(),
        runs: vec![TaskRun {
            root_task: 0,
            caller_task: None,
            tasks: vec![0],
        }],
        current_task: 0,
        has_turn: true,
        turns_taken: 0,
        trace: Vec::new(),
        steps: 0,
        rules: BTreeMap::new(),
        answers: HashMap::new(),
        resources: BTreeMap::new(),
        location: (String::new(), 0),
    };
    let refuse = |detail: String| Run {
        end: End::NotAnExecution(detail),
        trace: Vec::new(),
        steps: 0,
        rules: BTreeMap::new(),
    };
    let Some(id) = program.control(entry) else {
        return refuse(format!("`{entry}` is not a control"));
    };
    let control = &program.controls[id];
    if control.body.is_none() {
        return refuse(format!("`{entry}` is an extern control"));
    }
    let typed = arguments.len() == control.parameters.len()
        && arguments
            .iter()
            .zip(&control.parameters)
            .all(|(value, parameter)| config.fits_in_program(program, value, &parameter.ty));
    if !typed {
        return refuse(format!(
            "({}) are not arguments of `{entry}`",
            list(&arguments)
        ));
    }
    if let Some(precondition) = &control.precondition {
        let env = SignatureEnv {
            parameters: &arguments,
            old_parameters: &arguments,
            fields: &[],
        };
        match machine.evaluator().holds(precondition, &env) {
            Ok(true) => {}
            _ => return refuse(format!("the precondition of `{entry}` is false")),
        }
    }
    // Any resource passed as an initial argument to `entry` starts open.
    for arg in &arguments {
        let mut res = Vec::new();
        collect_resources(arg, &mut res);
        for (rid, handle_id) in res {
            machine.resources.insert((rid, handle_id), true);
        }
    }
    let entry_snapshots = arguments.clone();
    let mut wrapped_args = Vec::with_capacity(arguments.len());
    for (arg, param) in arguments.into_iter().zip(&control.parameters) {
        match machine.wrap_entry_arg(arg, &param.ty) {
            Ok(v) => wrapped_args.push(v),
            Err(stuck) => {
                return Run {
                    end: End::Stuck(Stuck {
                        state: stuck.state,
                        clause: stuck.clause,
                        control: entry.to_string(),
                        line: 0,
                        detail: stuck.detail,
                    }),
                    trace: machine.trace,
                    steps: machine.steps,
                    rules: machine.rules,
                };
            }
        }
    }
    machine.push_control(id, wrapped_args, entry_snapshots);
    let end = loop {
        if machine.steps >= config.fuel {
            break End::OutOfFuel;
        }
        machine.steps += 1;
        match machine.step_scheduler() {
            Ok(None) => {}
            Ok(Some(end)) => break end,
            Err(stuck) => {
                break End::Stuck(Stuck {
                    state: stuck.state,
                    clause: stuck.clause,
                    control: machine.location.0.clone(),
                    line: machine.location.1,
                    detail: stuck.detail,
                });
            }
        }
    };
    Run {
        end,
        trace: machine.trace,
        steps: machine.steps,
        rules: machine.rules,
    }
}
