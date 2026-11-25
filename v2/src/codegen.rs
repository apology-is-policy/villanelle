//! Phase 4: The typed LLVM IR and C ABI backend (`docs/redesign-plan.md` Phase 4;
//! `docs/v2/core.md` section 9, `[R1]`–`[R5]`).
//!
//! Compiles a checked [`typed::Program`] directly to textual LLVM IR (and C ABI
//! declarations for `extern` host adapters, `on fault release` hooks, and
//! public controls) under the erased semantics:
//!
//! - **[R1]** Every variable slot holds its flat native representation (`i1`,
//!   integers, `ptr` resources/borrows, `%vn2.string`, `%vn2.vec`, `%vn2.map`,
//!   `%vn2.struct.*`, `%vn2.variant.*`, `%vn2.outcome.*`). There are no dynamic
//!   value wrappers, no moved marks, and no borrow tags.
//! - **[R2]** `⊢` (`Oblige`), loop invariants, preconditions, outcome
//!   conditions `⇐`, and effect allowances emit zero code. Arithmetic and
//!   indexing (`v[i]`) are unchecked machine operations. `⊥` (`Impossible`) and
//!   decision arms guarded by `⊥` emit `unreachable`.
//! - **[R3]** Only `(site, alternative)` atoms mentioned in some reachable
//!   selector or runtime destruction/fault-release condition allocate an `i1`
//!   history bit.
//! - **[R4], [R5]** At assignments, loop transitions (`↑`, `□`, `recover`),
//!   exits (`■`), lexical boundaries, and fault unwinding, live owned slots are
//!   destroyed (`Drop`) and `on fault release` resources are released strictly
//!   from the static formulas of `erased::layout` (`D(x) ∧ ¬M(x)`) over
//!   history bits, with zero runtime moved flags. The formulas of a statement
//!   cover the names of the bodies around it, so every scope that ends at a
//!   statement is ended by the formulas of that statement.

mod tasks;

use crate::erased;
use crate::host::Answer;
use crate::int::Int;
use crate::oracle::{Event, HOST_SCOPE, RuntimePlace, RuntimeStep, Value};
use crate::script;
use crate::typed::{
    Arithmetic, BodyId, BorrowMode, BoundaryId, BuiltinOp, Command, Comparison, Control,
    ControlBody, ControlId, Expr, Function, FunctionId, IntType, Kind, Operation, Place, PlaceStep,
    Program, Selector, SiteId, Type, VarId, VarRef,
};
use std::collections::{BTreeSet, HashMap, HashSet};
use std::fmt::Write as _;
use std::process::Command as ProcessCommand;
use std::sync::atomic::{AtomicU64, Ordering};

/// A single native test run specification for [`run_native_batch`].
#[derive(Clone, Debug)]
pub struct NativeRunSpec {
    pub entry: String,
    pub arguments: Vec<Value>,
    pub arithmetic: bool,
    /// Ready-task indices offered by the host, then zero after the script ends.
    pub turns: Vec<usize>,
    pub answers: Vec<(String, Answer)>,
}

// ---------------------------------------------------------------------------
// Static history-bit plan ([R2], [R3], [R4], [R5])
// ---------------------------------------------------------------------------

struct HistoryPlan {
    bit: Vec<Vec<Option<usize>>>,
    bits: usize,
    own: Vec<Vec<usize>>,
    avail_at: Vec<Vec<Vec<Option<Selector>>>>,
    /// [O6](b): the bit that a `□` sets, by its body and position, where a
    /// formula asks which `□` ended the loop.
    leave_bit: HashMap<(BodyId, usize), usize>,
    /// [F5]: the bit that a statement of the work of a boundary sets when a
    /// fault occurs at it, by its body and position, where a formula asks
    /// at which statement the work faulted.
    fault_bit: HashMap<(BodyId, usize), usize>,
    /// The names that read the message of a fault without owning it: the
    /// message of a contingency that no statement consumes. No scope ends
    /// them.
    borrowed: Vec<bool>,
    stmt_sel: Vec<Vec<Selector>>,
    stmt_next: Vec<Vec<String>>,
    skip_target: Vec<Vec<String>>,
    branch_targets: Vec<Vec<Option<Vec<String>>>>,
}

fn mentions_site(sel: &Selector, site: SiteId) -> bool {
    match sel {
        Selector::Top => false,
        Selector::Atom(s, _) => *s == site,
        Selector::Not(inner) => mentions_site(inner, site),
        Selector::And(l, r) | Selector::Or(l, r) => {
            mentions_site(l, site) || mentions_site(r, site)
        }
    }
}

fn extract_site_arm(
    sel: &Selector,
    site: SiteId,
    allow_not_arm0: bool,
) -> Option<(usize, Selector)> {
    match sel {
        Selector::Atom(s, arm) if *s == site => Some((*arm, Selector::Top)),
        Selector::Not(inner) if allow_not_arm0 => match &**inner {
            Selector::Atom(s, 0) if *s == site => Some((1, Selector::Top)),
            _ => None,
        },
        Selector::And(l, r) => {
            if let Some((arm, lrem)) = extract_site_arm(l, site, allow_not_arm0)
                && !mentions_site(r, site)
            {
                let rem = if matches!(lrem, Selector::Top) {
                    (**r).clone()
                } else {
                    Selector::And(Box::new(lrem), r.clone())
                };
                return Some((arm, rem));
            }
            if let Some((arm, rrem)) = extract_site_arm(r, site, allow_not_arm0)
                && !mentions_site(l, site)
            {
                let rem = if matches!(rrem, Selector::Top) {
                    (**l).clone()
                } else {
                    Selector::And(l.clone(), Box::new(rrem))
                };
                return Some((arm, rem));
            }
            None
        }
        _ => None,
    }
}

#[allow(clippy::too_many_arguments)]
fn plan_structured_flow(
    b_id: BodyId,
    stmts: &[crate::typed::Statement],
    indices: &[usize],
    after_lbl: &str,
    stmt_sel: &mut [Selector],
    stmt_next: &mut [String],
    skip_target: &mut [String],
    branch_targets: &mut [Option<Vec<String>>],
) {
    let mut pos = 0;
    while pos < indices.len() {
        let s_idx = indices[pos];
        let default_next = if pos + 1 < indices.len() {
            format!("b{b_id}_s{}", indices[pos + 1])
        } else {
            after_lbl.to_string()
        };

        let branch_info = match &stmts[s_idx].command {
            Command::Decide { site, arms, .. } => Some((*site, arms.len(), false)),
            Command::Test { site, .. } => Some((*site, 2, true)),
            _ => None,
        };

        if let Some((site, num_arms, is_test)) = branch_info {
            let allow_not_arm0 = is_test && matches!(stmt_sel[s_idx], Selector::Top);
            let mut end = pos + 1;
            let mut matches_in_span: Vec<(usize, usize, Selector)> = Vec::new();
            while end < indices.len() {
                let k = indices[end];
                if matches!(stmts[k].command, Command::Oblige(_)) {
                    end += 1;
                    continue;
                }
                if let Some((arm_idx, rem)) = extract_site_arm(&stmt_sel[k], site, allow_not_arm0)
                    && arm_idx < num_arms
                {
                    matches_in_span.push((k, arm_idx, rem));
                    end += 1;
                } else {
                    break;
                }
            }

            let mut arm_buckets: Vec<Vec<usize>> = vec![Vec::new(); num_arms];
            for &(k, arm_idx, _) in &matches_in_span {
                arm_buckets[arm_idx].push(k);
            }

            // For `Command::Test`, only collapse into a direct structured branch
            // when both arms have statements (preserving single-arm guard
            // semantics and tests). For `Command::Decide`, collapse whenever any
            // arm has statements in the immediately following span.
            let should_collapse = if is_test {
                !arm_buckets[0].is_empty() && !arm_buckets[1].is_empty()
            } else {
                !matches_in_span.is_empty()
            };

            if should_collapse {
                let span_after = if end < indices.len() {
                    format!("b{b_id}_s{}", indices[end])
                } else {
                    after_lbl.to_string()
                };
                for (k, _, rem) in matches_in_span {
                    stmt_sel[k] = rem;
                }
                let mut targets = Vec::with_capacity(num_arms);
                for bucket in &arm_buckets {
                    if let Some(&first_k) = bucket.first() {
                        targets.push(format!("b{b_id}_s{first_k}"));
                        plan_structured_flow(
                            b_id,
                            stmts,
                            bucket,
                            &span_after,
                            stmt_sel,
                            stmt_next,
                            skip_target,
                            branch_targets,
                        );
                    } else {
                        targets.push(span_after.clone());
                    }
                }
                stmt_next[s_idx] = span_after.clone();
                skip_target[s_idx] = span_after;
                branch_targets[s_idx] = Some(targets);
                pos = end;
                continue;
            }
        }

        stmt_next[s_idx] = default_next.clone();
        skip_target[s_idx] = default_next;
        pos += 1;
    }
}

fn mention(selector: &Selector, plan: &mut HistoryPlan) {
    match selector {
        Selector::Top => {}
        Selector::Atom(site, alternative) => {
            // The atoms of the `□` statements of a loop and of the
            // statements of a boundary that fault follow the alternatives
            // of their site.
            if plan.bit[*site].len() <= *alternative {
                plan.bit[*site].resize(*alternative + 1, None);
            }
            if plan.bit[*site][*alternative].is_none() {
                plan.bit[*site][*alternative] = Some(plan.bits);
                plan.bits += 1;
            }
        }
        Selector::Not(inner) => mention(inner, plan),
        Selector::And(left, right) | Selector::Or(left, right) => {
            mention(left, plan);
            mention(right, plan);
        }
    }
}

fn is_direct_impossible_arm(stmt: &crate::typed::Statement) -> bool {
    matches!(stmt.command, Command::Impossible) && matches!(stmt.selector, Selector::Atom(_, _))
}

fn simplify_selector(sel: Selector) -> Selector {
    fn is_false(s: &Selector) -> bool {
        matches!(s, Selector::Not(inner) if matches!(&**inner, Selector::Top))
    }
    match sel {
        Selector::Top | Selector::Atom(_, _) => sel,
        Selector::Not(inner) => match simplify_selector(*inner) {
            Selector::Top => Selector::Not(Box::new(Selector::Top)),
            Selector::Not(twice) => *twice,
            other => Selector::Not(Box::new(other)),
        },
        Selector::And(l, r) => {
            let sl = simplify_selector(*l);
            let sr = simplify_selector(*r);
            if is_false(&sl) || is_false(&sr) {
                Selector::Not(Box::new(Selector::Top))
            } else if matches!(sl, Selector::Top) {
                sr
            } else if matches!(sr, Selector::Top) {
                sl
            } else {
                Selector::And(Box::new(sl), Box::new(sr))
            }
        }
        Selector::Or(l, r) => {
            let sl = simplify_selector(*l);
            let sr = simplify_selector(*r);
            if matches!(sl, Selector::Top) || matches!(sr, Selector::Top) {
                Selector::Top
            } else if is_false(&sl) {
                sr
            } else if is_false(&sr) {
                sl
            } else {
                Selector::Or(Box::new(sl), Box::new(sr))
            }
        }
    }
}

fn simplify_opt_selector(sel: Option<&Selector>) -> Option<Selector> {
    let raw = sel?;
    let simp = simplify_selector(raw.clone());
    if matches!(&simp, Selector::Not(inner) if matches!(&**inner, Selector::Top)) {
        None
    } else {
        Some(simp)
    }
}

fn needs_drop(program: &Program, ty: &Type) -> bool {
    match ty {
        Type::Bool | Type::Int(_) | Type::Ref(_, _) | Type::Resource(_, _) => false,
        Type::String | Type::Vector(_) | Type::Map(_, _) => true,
        Type::Struct(sid, _) => program.structs[*sid]
            .fields
            .iter()
            .any(|f| needs_drop(program, &f.ty)),
        Type::Variant(vid, _) => program.variants[*vid]
            .constructors
            .iter()
            .any(|c| c.fields.iter().any(|f| needs_drop(program, &f.ty))),
        Type::Outcome(oid, _) => program.outcomes[*oid]
            .alternatives
            .iter()
            .any(|a| a.fields.iter().any(|f| needs_drop(program, &f.ty))),
        Type::Named(_) | Type::OutcomeNamed(_) | Type::TasksNamed(_) | Type::Tasks(_, _) => false,
    }
}

fn needs_runtime_cleanup(program: &Program, ty: &Type) -> bool {
    needs_drop(program, ty) || program.holds_obligation(ty)
}

fn build_plan(program: &Program, body: &ControlBody, param_count: usize) -> HistoryPlan {
    let erased::Layout {
        avail_at,
        leaves,
        faults,
        ..
    } = erased::layout(program, body, param_count);
    let mut stmt_sel = Vec::with_capacity(body.bodies.len());
    let mut stmt_next = Vec::with_capacity(body.bodies.len());
    let mut skip_target = Vec::with_capacity(body.bodies.len());
    let mut branch_targets = Vec::with_capacity(body.bodies.len());

    for (b_id, inner) in body.bodies.iter().enumerate() {
        let n = inner.statements.len();
        let mut sels: Vec<Selector> = inner
            .statements
            .iter()
            .map(|s| s.selector.clone())
            .collect();
        let end_lbl = format!("b{b_id}_end");
        let mut nexts = vec![end_lbl.clone(); n];
        let mut skips = vec![end_lbl.clone(); n];
        let mut branches = vec![None; n];
        let all_indices: Vec<usize> = (0..n).collect();
        plan_structured_flow(
            b_id,
            &inner.statements,
            &all_indices,
            &end_lbl,
            &mut sels,
            &mut nexts,
            &mut skips,
            &mut branches,
        );
        stmt_sel.push(sels);
        stmt_next.push(nexts);
        skip_target.push(skips);
        branch_targets.push(branches);
    }

    let mut plan = HistoryPlan {
        bit: body
            .sites
            .iter()
            .map(|site| vec![None; site.alternatives.len()])
            .collect(),
        bits: 0,
        own: vec![Vec::new(); body.bodies.len()],
        avail_at,
        leave_bit: HashMap::new(),
        fault_bit: HashMap::new(),
        borrowed: vec![false; body.vars.len()],
        stmt_sel,
        stmt_next,
        skip_target,
        branch_targets,
    };
    for (b_id, inner) in body.bodies.iter().enumerate() {
        for (s_idx, statement) in inner.statements.iter().enumerate() {
            // [R2], [R3]: `⊢` obligations are not evaluated, and `site.alt ▷ ⊥`
            // branches directly to `unreachable` in the decision's switch, so
            // neither needs a runtime history bit.
            if matches!(statement.command, Command::Oblige(_))
                || is_direct_impossible_arm(statement)
            {
                continue;
            }
            let eff_sel = plan.stmt_sel[b_id][s_idx].clone();
            mention(&eff_sel, &mut plan);
        }
    }
    let cleanup_vars: Vec<bool> = body
        .vars
        .iter()
        .map(|v| needs_runtime_cleanup(program, &v.ty))
        .collect();
    if cleanup_vars.iter().any(|&c| c) {
        let mut avail_sels = Vec::new();
        for body_snaps in &plan.avail_at {
            for snap in body_snaps {
                for (var_id, sel) in snap.iter().enumerate() {
                    if cleanup_vars[var_id]
                        && let Some(s) = simplify_opt_selector(sel.as_ref())
                    {
                        avail_sels.push(s);
                    }
                }
            }
        }
        for s in &avail_sels {
            mention(s, &mut plan);
        }
    }
    // A `□` or a statement that faults sets a bit only where a formula
    // that some scope end evaluates names it.
    for (leave_body, pc, site, index) in leaves {
        if let Some(Some(bit)) = plan.bit[site].get(index) {
            plan.leave_bit.insert((leave_body, pc), *bit);
        }
    }
    for (fault_body, pc, site, index) in faults {
        if let Some(Some(bit)) = plan.bit[site].get(index) {
            plan.fault_bit.insert((fault_body, pc), *bit);
        }
    }
    for (site, bits) in body.sites.iter().zip(&plan.bit) {
        plan.own[site.body].extend(bits.iter().flatten());
    }
    plan
}

// ---------------------------------------------------------------------------
// Types, layouts, and C ABI
// ---------------------------------------------------------------------------

fn int_bits(ty: IntType, usize_bits: u32) -> u32 {
    match ty {
        IntType::U8 | IntType::I8 => 8,
        IntType::U16 | IntType::I16 => 16,
        IntType::U32 | IntType::I32 => 32,
        IntType::U64 | IntType::I64 => 64,
        IntType::Usize => usize_bits,
    }
}

fn llvm_int_ty(ty: IntType, usize_bits: u32) -> &'static str {
    match int_bits(ty, usize_bits) {
        8 => "i8",
        16 => "i16",
        32 => "i32",
        _ => "i64",
    }
}

fn is_unit_variant(program: &Program, vid: usize) -> bool {
    program.variants[vid]
        .constructors
        .iter()
        .all(|c| c.fields.is_empty())
}

fn is_unit_outcome(program: &Program, oid: usize) -> bool {
    program.outcomes[oid]
        .alternatives
        .iter()
        .all(|a| a.fields.is_empty())
}

fn llvm_ty(program: &Program, ty: &Type, usize_bits: u32) -> String {
    match ty {
        Type::Bool => "i1".to_string(),
        Type::Int(int_ty) => llvm_int_ty(*int_ty, usize_bits).to_string(),
        Type::String => "%vn2.string".to_string(),
        Type::Vector(_) => "%vn2.vec".to_string(),
        Type::Map(_, _) => "%vn2.map".to_string(),
        Type::Struct(sid, _) => format!("%vn2.struct.{sid}"),
        Type::Variant(vid, _) => {
            if is_unit_variant(program, *vid) {
                "i32".to_string()
            } else {
                format!("%vn2.variant.{vid}")
            }
        }
        Type::Outcome(oid, _) => {
            if is_unit_outcome(program, *oid) {
                "i32".to_string()
            } else {
                format!("%vn2.outcome.{oid}")
            }
        }
        Type::Resource(_, _)
        | Type::Ref(_, _)
        | Type::Named(_)
        | Type::OutcomeNamed(_)
        | Type::TasksNamed(_)
        | Type::Tasks(_, _) => "ptr".to_string(),
    }
}

fn is_c_scalar_by_val(program: &Program, ty: &Type) -> bool {
    matches!(
        ty,
        Type::Bool | Type::Int(_) | Type::Resource(_, _) | Type::Ref(_, _)
    ) || matches!(ty, Type::Variant(vid, _) if is_unit_variant(program, *vid))
        || matches!(ty, Type::Outcome(oid, _) if is_unit_outcome(program, *oid))
}

fn c_abi_llvm_ty(program: &Program, ty: &Type, usize_bits: u32) -> String {
    if *ty == Type::Bool {
        "i8".to_string()
    } else if is_c_scalar_by_val(program, ty) {
        llvm_ty(program, ty, usize_bits)
    } else {
        "ptr".to_string()
    }
}

fn c_header_scalar_ty(ty: &Type, usize_bits: u32) -> &'static str {
    match ty {
        Type::Bool | Type::Int(IntType::U8) => "uint8_t",
        Type::Int(IntType::U16) => "uint16_t",
        Type::Int(IntType::U32) => "uint32_t",
        Type::Int(IntType::U64) => "uint64_t",
        Type::Int(IntType::I8) => "int8_t",
        Type::Int(IntType::I16) => "int16_t",
        Type::Int(IntType::I32) => "int32_t",
        Type::Int(IntType::I64) => "int64_t",
        Type::Int(IntType::Usize) => {
            if usize_bits <= 32 {
                "uint32_t"
            } else {
                "uint64_t"
            }
        }
        Type::Resource(_, _) | Type::Ref(_, _) => "void *",
        Type::Variant(_, _) | Type::Outcome(_, _) => "int32_t",
        _ => "void *",
    }
}

fn c_header_value_ty(program: &Program, ty: &Type, usize_bits: u32) -> String {
    match ty {
        Type::Bool
        | Type::Int(_)
        | Type::Resource(_, _)
        | Type::Variant(_, _)
        | Type::Outcome(_, _) => {
            if let Type::Variant(vid, _) = ty
                && !is_unit_variant(program, *vid)
            {
                return format!("struct vn2_variant_{}", program.variants[*vid].name);
            }
            if let Type::Outcome(oid, _) = ty
                && !is_unit_outcome(program, *oid)
            {
                return format!("struct vn2_outcome_{}", program.outcomes[*oid].name);
            }
            c_header_scalar_ty(ty, usize_bits).to_string()
        }
        Type::String => "struct vn2_string".to_string(),
        Type::Vector(_) => "struct vn2_vec".to_string(),
        Type::Map(_, _) => "struct vn2_map".to_string(),
        Type::Struct(sid, _) => format!("struct vn2_struct_{}", program.structs[*sid].name),
        Type::Ref(BorrowMode::Shared, inner) => {
            if **inner == Type::Bool {
                "const uint8_t *".to_string()
            } else {
                format!("const {} *", c_header_value_ty(program, inner, usize_bits))
            }
        }
        Type::Ref(BorrowMode::Exclusive, inner) => {
            if **inner == Type::Bool {
                "uint8_t *".to_string()
            } else {
                format!("{} *", c_header_value_ty(program, inner, usize_bits))
            }
        }
        Type::Named(_) | Type::OutcomeNamed(_) | Type::TasksNamed(_) | Type::Tasks(_, _) => {
            "void *".to_string()
        }
    }
}

fn c_header_param_ty(program: &Program, ty: &Type, usize_bits: u32) -> String {
    match ty {
        Type::Ref(_, _) => c_header_value_ty(program, ty, usize_bits),
        other if is_c_scalar_by_val(program, other) => c_header_scalar_ty(other, usize_bits).into(),
        other => format!("const {} *", c_header_value_ty(program, other, usize_bits)),
    }
}

fn c_header_out_ty(program: &Program, ty: &Type, usize_bits: u32) -> String {
    if matches!(ty, Type::Ref(_, _)) {
        format!("{}*", c_header_value_ty(program, ty, usize_bits))
    } else {
        format!("{} *", c_header_value_ty(program, ty, usize_bits))
    }
}

fn align_up(offset: usize, align: usize) -> usize {
    let a = align.max(1);
    (offset + a - 1) & !(a - 1)
}

fn type_size_align(program: &Program, ty: &Type, usize_bits: u32) -> (usize, usize) {
    let u_bytes = if usize_bits <= 32 { 4 } else { 8 };
    match ty {
        Type::Bool => (1, 1),
        Type::Int(it) => {
            let b = (int_bits(*it, usize_bits) as usize) / 8;
            (b, b)
        }
        Type::Resource(_, _)
        | Type::Ref(_, _)
        | Type::Named(_)
        | Type::OutcomeNamed(_)
        | Type::TasksNamed(_)
        | Type::Tasks(_, _) => (8, 8),
        Type::String | Type::Vector(_) | Type::Map(_, _) => {
            let off1 = align_up(8, u_bytes);
            let off2 = off1 + u_bytes;
            let end = off2 + u_bytes;
            (align_up(end, 8), 8)
        }
        Type::Struct(sid, _) => {
            let fields = &program.structs[*sid].fields;
            if fields.is_empty() {
                (1, 1)
            } else {
                struct_size_align(program, fields.iter().map(|f| &f.ty), usize_bits)
            }
        }
        Type::Variant(vid, _) => {
            if is_unit_variant(program, *vid) {
                (4, 4)
            } else {
                let words = variant_payload_words(program, *vid, usize_bits);
                (8 + words * 8, 8)
            }
        }
        Type::Outcome(oid, _) => {
            if is_unit_outcome(program, *oid) {
                (4, 4)
            } else {
                let words = outcome_payload_words(program, *oid, usize_bits);
                (8 + words * 8, 8)
            }
        }
    }
}

fn struct_size_align<'a>(
    program: &Program,
    fields: impl Iterator<Item = &'a Type>,
    usize_bits: u32,
) -> (usize, usize) {
    let mut size = 0usize;
    let mut max_align = 1usize;
    for ty in fields {
        let (fs, fa) = type_size_align(program, ty, usize_bits);
        size = align_up(size, fa) + fs;
        max_align = max_align.max(fa);
    }
    (align_up(size.max(1), max_align), max_align)
}

fn variant_payload_words(program: &Program, vid: usize, usize_bits: u32) -> usize {
    let max_bytes = program.variants[vid]
        .constructors
        .iter()
        .filter(|c| !c.fields.is_empty())
        .map(|c| struct_size_align(program, c.fields.iter().map(|f| &f.ty), usize_bits).0)
        .max()
        .unwrap_or(0);
    max_bytes.div_ceil(8).max(1)
}

fn outcome_payload_words(program: &Program, oid: usize, usize_bits: u32) -> usize {
    let max_bytes = program.outcomes[oid]
        .alternatives
        .iter()
        .filter(|a| !a.fields.is_empty())
        .map(|a| struct_size_align(program, a.fields.iter().map(|f| &f.ty), usize_bits).0)
        .max()
        .unwrap_or(0);
    max_bytes.div_ceil(8).max(1)
}

/// Operations in decisions and captures, including loop and contingency bodies.
fn operations(program: &Program) -> impl Iterator<Item = &Operation> {
    program
        .controls
        .iter()
        .filter_map(|c| c.body.as_ref())
        .chain(
            program
                .boundaries
                .iter()
                .flat_map(|b| [&b.body, &b.contingency]),
        )
        .flat_map(|body| &body.bodies)
        .flat_map(|body| &body.statements)
        .filter_map(|statement| operation(&statement.command))
}

fn operation(command: &Command) -> Option<&Operation> {
    match command {
        Command::Decide { op_kind, .. }
        | Command::Capture {
            operation: op_kind, ..
        } => Some(op_kind),
        _ => None,
    }
}

fn has_emit_builtin(program: &Program) -> bool {
    operations(program).any(|op| {
        matches!(
            op,
            Operation::Builtin {
                op: BuiltinOp::Emit,
                ..
            }
        )
    })
}

fn defined_await_targets(program: &Program) -> impl Iterator<Item = ControlId> + '_ {
    operations(program).filter_map(|op| match op {
        Operation::AwaitControl(id) if program.controls[*id].body.is_some() => Some(*id),
        _ => None,
    })
}

/// The type of the status of `terminate n` (if any) for each control in
/// `program`. A control that holds one is an entry control ([F5]), so the
/// closure over callers below finds nothing more.
fn compute_control_terminate_tys(program: &Program) -> Vec<Option<Type>> {
    fn scan_body(body: &ControlBody) -> Option<Type> {
        for b in &body.bodies {
            for s in &b.statements {
                if let Command::Terminate(Some(_)) = &s.command {
                    return Some(Type::Int(IntType::U8));
                }
            }
        }
        None
    }
    let mut tys: Vec<Option<Type>> = program
        .controls
        .iter()
        .map(|c| c.body.as_ref().and_then(scan_body))
        .collect();
    let mut changed = true;
    while changed {
        changed = false;
        for (cid, ctrl) in program.controls.iter().enumerate() {
            if tys[cid].is_some() {
                continue;
            }
            let Some(body) = &ctrl.body else {
                continue;
            };
            for b in &body.bodies {
                for s in &b.statements {
                    if let Command::Decide {
                        op_kind:
                            Operation::Control(callee)
                            | Operation::RunControl(callee)
                            | Operation::AwaitControl(callee),
                        ..
                    }
                    | Command::Capture {
                        operation:
                            Operation::Control(callee)
                            | Operation::RunControl(callee)
                            | Operation::AwaitControl(callee),
                        ..
                    } = &s.command
                        && let Some(t) = &tys[*callee]
                    {
                        tys[cid] = Some(t.clone());
                        changed = true;
                        break;
                    }
                }
                if tys[cid].is_some() {
                    break;
                }
            }
        }
    }
    tys
}

/// Emits the typed C header for `program`, declaring outcome tag constants,
/// `vn2.string`/`vec`/`map`/aggregate structs, `extern` host adapters, fault
/// release hooks, and public defined control entry points.
pub fn emit_c_header(program: &Program, usize_bits: u32) -> String {
    let usize_c = if usize_bits <= 32 {
        "uint32_t"
    } else {
        "uint64_t"
    };
    let mut out = String::new();
    let _ = writeln!(
        out,
        "/* Generated by Villanelle v2 (Phase 4 typed C ABI). */"
    );
    let _ = writeln!(out, "#pragma once");
    let _ = writeln!(out, "#include <stddef.h>");
    let _ = writeln!(out, "#include <stdint.h>");
    let _ = writeln!(out);

    let uses_slice2_data = !program.structs.is_empty()
        || !program.variants.is_empty()
        || !program.resources.is_empty()
        || !program.outcomes.is_empty()
        || !program.boundaries.is_empty()
        || program.controls.iter().any(|c| {
            c.faults
                || c.parameters.iter().any(|p| !p.ty.is_scalar())
                || c.contract
                    .iter()
                    .any(|a| a.fields.iter().any(|f| !f.ty.is_scalar()))
        });

    if defined_await_targets(program).next().is_some() || tasks::uses_sets(program) {
        let _ = writeln!(out, "uint64_t vn2_pick_turn(uint64_t ready_count);");
    }
    if uses_slice2_data {
        let _ = writeln!(out, "#ifndef VN2_RUNTIME_TYPES_DEFINED");
        let _ = writeln!(out, "#define VN2_RUNTIME_TYPES_DEFINED");
        let _ = writeln!(out, "#define VN2_FAULT (-1)");
        let _ = writeln!(out, "#define VN2_TERMINATED (-2)");
        let _ = writeln!(
            out,
            "typedef struct vn2_string {{ const char *data; {usize_c} len; {usize_c} cap; }} vn2_string;"
        );
        let _ = writeln!(
            out,
            "typedef struct vn2_vec {{ void *data; {usize_c} len; {usize_c} cap; }} vn2_vec;"
        );
        let _ = writeln!(
            out,
            "typedef struct vn2_map {{ void *data; {usize_c} len; {usize_c} cap; }} vn2_map;"
        );
        let _ = writeln!(out, "#endif");
        let mut visited = vec![false; program.structs.len()];
        let mut struct_order = Vec::with_capacity(program.structs.len());
        fn visit_struct(
            program: &Program,
            sid: usize,
            visited: &mut [bool],
            order: &mut Vec<usize>,
        ) {
            if visited[sid] {
                return;
            }
            visited[sid] = true;
            for f in &program.structs[sid].fields {
                if let Type::Struct(dep, _) = f.ty.deref_type() {
                    visit_struct(program, *dep, visited, order);
                }
            }
            order.push(sid);
        }
        for sid in 0..program.structs.len() {
            visit_struct(program, sid, &mut visited, &mut struct_order);
        }
        for sid in struct_order {
            let s = &program.structs[sid];
            let _ = write!(out, "typedef struct vn2_struct_{} {{ ", s.name);
            if s.fields.is_empty() {
                let _ = write!(out, "uint8_t _empty; ");
            } else {
                for f in &s.fields {
                    let fty = c_header_value_ty(program, &f.ty, usize_bits);
                    if matches!(f.ty, Type::Ref(_, _)) {
                        let _ = write!(out, "{fty}{}; ", f.name);
                    } else {
                        let _ = write!(out, "{fty} {}; ", f.name);
                    }
                }
            }
            let _ = writeln!(out, "}} vn2_struct_{};", s.name);
        }
        for (vid, v) in program.variants.iter().enumerate() {
            if !is_unit_variant(program, vid) {
                let words = variant_payload_words(program, vid, usize_bits);
                let _ = writeln!(
                    out,
                    "typedef struct vn2_variant_{} {{ int32_t tag; uint64_t payload[{words}]; }} vn2_variant_{};",
                    v.name, v.name
                );
            }
        }
        for (oid, o) in program.outcomes.iter().enumerate() {
            if !is_unit_outcome(program, oid) {
                let words = outcome_payload_words(program, oid, usize_bits);
                let _ = writeln!(
                    out,
                    "typedef struct vn2_outcome_{} {{ int32_t tag; uint64_t payload[{words}]; }} vn2_outcome_{};",
                    o.name, o.name
                );
            }
        }
        for r in &program.resources {
            if r.on_fault_release {
                let _ = writeln!(out, "void vn2_release_{}(void *handle);", r.name);
            }
        }
        if has_emit_builtin(program) {
            let _ = writeln!(out, "void vn2_builtin_emit(const struct vn2_string *text);");
        }
        let _ = writeln!(out);
    }

    let term_tys = compute_control_terminate_tys(program);
    for (cid, control) in program.controls.iter().enumerate() {
        let upper_ctrl = control.name.to_ascii_uppercase();
        for (alt_idx, alt) in control.contract.iter().enumerate() {
            let upper_alt = alt.name.to_ascii_uppercase();
            let _ = writeln!(out, "#define VN2_{upper_ctrl}_{upper_alt} {alt_idx}");
        }
        let mut params = Vec::new();
        for param in &control.parameters {
            params.push(format!(
                "{} {}",
                c_header_param_ty(program, &param.ty, usize_bits),
                param.name
            ));
        }
        for (alt_idx, alt) in control.contract.iter().enumerate() {
            for (field_idx, field) in alt.fields.iter().enumerate() {
                params.push(format!(
                    "{}out_{}_{}_{}",
                    c_header_out_ty(program, &field.ty, usize_bits),
                    alt_idx,
                    alt.name,
                    field_idx
                ));
            }
        }
        if control.faults {
            params.push("struct vn2_string *out_fault".to_string());
        }
        if let Some(tty) = &term_tys[cid] {
            params.push(format!(
                "{}out_terminated",
                c_header_out_ty(program, tty, usize_bits)
            ));
        }
        let param_list = if params.is_empty() {
            "void".to_string()
        } else {
            params.join(", ")
        };
        let prefix = if control.body.is_none() {
            "vn2_ext"
        } else {
            "vn2_call"
        };
        let _ = writeln!(out, "int32_t {prefix}_{}({param_list});", control.name);
        let _ = writeln!(out);
    }
    out
}

// ---------------------------------------------------------------------------
// Type / runtime helper registry
// ---------------------------------------------------------------------------

struct RuntimeRegistry<'a> {
    program: &'a Program,
    usize_bits: u32,
    usize_ty: &'static str,
    next_str_id: usize,
    str_literals: Vec<(String, Vec<u8>)>,
    str_literal_map: HashMap<Vec<u8>, String>,
    registered_types: Vec<Type>,
    type_ids: HashMap<Type, usize>,
    registered_maps: Vec<(Type, Type)>,
    map_ids: HashMap<(Type, Type), usize>,
    needed_libc: bool,
    needed_str: bool,
    needed_vec_grow: bool,
    needed_eq: BTreeSet<usize>,
    needed_cmp: BTreeSet<usize>,
    needed_clone: BTreeSet<usize>,
    needed_drop: BTreeSet<usize>,
    needed_release: BTreeSet<usize>,
}

impl<'a> RuntimeRegistry<'a> {
    fn new(program: &'a Program, usize_bits: u32) -> Self {
        Self {
            program,
            usize_bits,
            usize_ty: if usize_bits <= 32 { "i32" } else { "i64" },
            next_str_id: 0,
            str_literals: Vec::new(),
            str_literal_map: HashMap::new(),
            registered_types: Vec::new(),
            type_ids: HashMap::new(),
            registered_maps: Vec::new(),
            map_ids: HashMap::new(),
            needed_libc: false,
            needed_str: false,
            needed_vec_grow: false,
            needed_eq: BTreeSet::new(),
            needed_cmp: BTreeSet::new(),
            needed_clone: BTreeSet::new(),
            needed_drop: BTreeSet::new(),
            needed_release: BTreeSet::new(),
        }
    }

    fn intern_bytes(&mut self, bytes: &[u8]) -> String {
        if let Some(name) = self.str_literal_map.get(bytes) {
            return name.clone();
        }
        let name = format!("@.str.{}", self.next_str_id);
        self.next_str_id += 1;
        self.str_literals.push((name.clone(), bytes.to_vec()));
        self.str_literal_map.insert(bytes.to_vec(), name.clone());
        name
    }

    fn intern_type(&mut self, ty: &Type) -> usize {
        let clean = ty.deref_type().clone();
        if let Some(&id) = self.type_ids.get(&clean) {
            return id;
        }
        let id = self.registered_types.len();
        self.registered_types.push(clean.clone());
        self.type_ids.insert(clean.clone(), id);
        match &clean {
            Type::Vector(elem) => {
                self.intern_type(elem);
            }
            Type::Map(k, v) => {
                self.intern_type(k);
                self.intern_type(v);
                self.intern_map(k, v);
            }
            Type::Struct(sid, _) => {
                for f in &self.program.structs[*sid].fields {
                    self.intern_type(&f.ty);
                }
            }
            Type::Variant(vid, _) => {
                for c in &self.program.variants[*vid].constructors {
                    for f in &c.fields {
                        self.intern_type(&f.ty);
                    }
                }
            }
            Type::Outcome(oid, _) => {
                for a in &self.program.outcomes[*oid].alternatives {
                    for f in &a.fields {
                        self.intern_type(&f.ty);
                    }
                }
            }
            _ => {}
        }
        id
    }

    fn intern_map(&mut self, k: &Type, v: &Type) -> usize {
        let key = (k.clone(), v.clone());
        if let Some(&id) = self.map_ids.get(&key) {
            return id;
        }
        let kt = self.intern_type(k);
        self.require_cmp(kt);
        let id = self.registered_maps.len();
        self.registered_maps.push(key.clone());
        self.map_ids.insert(key, id);
        id
    }

    fn require_eq(&mut self, tid: usize) {
        if !self.needed_eq.insert(tid) {
            return;
        }
        let ty = self.registered_types[tid].clone();
        match ty {
            Type::String => {
                self.needed_str = true;
                self.needed_libc = true;
            }
            Type::Vector(e) => {
                let et = self.intern_type(&e);
                self.require_eq(et);
            }
            Type::Map(k, v) => {
                let kt = self.intern_type(&k);
                let vt = self.intern_type(&v);
                self.require_eq(kt);
                self.require_eq(vt);
            }
            Type::Struct(sid, _) => {
                for f in &self.program.structs[sid].fields {
                    let ft = self.intern_type(&f.ty);
                    self.require_eq(ft);
                }
            }
            Type::Variant(vid, _) => {
                for c in &self.program.variants[vid].constructors {
                    for f in &c.fields {
                        let ft = self.intern_type(&f.ty);
                        self.require_eq(ft);
                    }
                }
            }
            Type::Outcome(oid, _) => {
                for a in &self.program.outcomes[oid].alternatives {
                    for f in &a.fields {
                        let ft = self.intern_type(&f.ty);
                        self.require_eq(ft);
                    }
                }
            }
            _ => {}
        }
    }

    fn require_cmp(&mut self, tid: usize) {
        if !self.needed_cmp.insert(tid) {
            return;
        }
        let ty = self.registered_types[tid].clone();
        match ty {
            Type::String => {
                self.needed_str = true;
                self.needed_libc = true;
            }
            Type::Vector(e) => {
                let et = self.intern_type(&e);
                self.require_cmp(et);
            }
            Type::Map(k, v) => {
                let kt = self.intern_type(&k);
                let vt = self.intern_type(&v);
                self.require_cmp(kt);
                self.require_cmp(vt);
            }
            Type::Struct(sid, _) => {
                for f in &self.program.structs[sid].fields {
                    let ft = self.intern_type(&f.ty);
                    self.require_cmp(ft);
                }
            }
            Type::Variant(vid, _) => {
                for c in &self.program.variants[vid].constructors {
                    for f in &c.fields {
                        let ft = self.intern_type(&f.ty);
                        self.require_cmp(ft);
                    }
                }
            }
            Type::Outcome(oid, _) => {
                for a in &self.program.outcomes[oid].alternatives {
                    for f in &a.fields {
                        let ft = self.intern_type(&f.ty);
                        self.require_cmp(ft);
                    }
                }
            }
            _ => {}
        }
    }

    fn require_clone(&mut self, tid: usize) {
        if !self.needed_clone.insert(tid) {
            return;
        }
        let ty = self.registered_types[tid].clone();
        match ty {
            Type::String => {
                self.needed_str = true;
                self.needed_libc = true;
            }
            Type::Vector(e) => {
                self.needed_libc = true;
                let et = self.intern_type(&e);
                self.require_clone(et);
            }
            Type::Map(k, v) => {
                self.needed_libc = true;
                let kt = self.intern_type(&k);
                let vt = self.intern_type(&v);
                self.require_clone(kt);
                self.require_clone(vt);
            }
            Type::Struct(sid, _) => {
                for f in &self.program.structs[sid].fields {
                    let ft = self.intern_type(&f.ty);
                    self.require_clone(ft);
                }
            }
            Type::Variant(vid, _) => {
                for c in &self.program.variants[vid].constructors {
                    for f in &c.fields {
                        let ft = self.intern_type(&f.ty);
                        self.require_clone(ft);
                    }
                }
            }
            Type::Outcome(oid, _) => {
                for a in &self.program.outcomes[oid].alternatives {
                    for f in &a.fields {
                        let ft = self.intern_type(&f.ty);
                        self.require_clone(ft);
                    }
                }
            }
            _ => {}
        }
    }

    fn require_drop(&mut self, tid: usize) {
        if !self.needed_drop.insert(tid) {
            return;
        }
        let ty = self.registered_types[tid].clone();
        if !needs_drop(self.program, &ty) {
            return;
        }
        match ty {
            Type::String => {
                self.needed_str = true;
                self.needed_libc = true;
            }
            Type::Vector(e) => {
                self.needed_libc = true;
                if needs_drop(self.program, &e) {
                    let et = self.intern_type(&e);
                    self.require_drop(et);
                }
            }
            Type::Map(k, v) => {
                self.needed_libc = true;
                if needs_drop(self.program, &k) {
                    let kt = self.intern_type(&k);
                    self.require_drop(kt);
                }
                if needs_drop(self.program, &v) {
                    let vt = self.intern_type(&v);
                    self.require_drop(vt);
                }
            }
            Type::Struct(sid, _) => {
                for f in &self.program.structs[sid].fields {
                    if needs_drop(self.program, &f.ty) {
                        let ft = self.intern_type(&f.ty);
                        self.require_drop(ft);
                    }
                }
            }
            Type::Variant(vid, _) => {
                for c in &self.program.variants[vid].constructors {
                    for f in &c.fields {
                        if needs_drop(self.program, &f.ty) {
                            let ft = self.intern_type(&f.ty);
                            self.require_drop(ft);
                        }
                    }
                }
            }
            Type::Outcome(oid, _) => {
                for a in &self.program.outcomes[oid].alternatives {
                    for f in &a.fields {
                        if needs_drop(self.program, &f.ty) {
                            let ft = self.intern_type(&f.ty);
                            self.require_drop(ft);
                        }
                    }
                }
            }
            _ => {}
        }
    }

    fn require_release(&mut self, tid: usize) {
        if !self.needed_release.insert(tid) {
            return;
        }
        let ty = self.registered_types[tid].clone();
        if !needs_runtime_cleanup(self.program, &ty) {
            return;
        }
        match ty {
            Type::String => {
                self.needed_str = true;
                self.needed_libc = true;
            }
            Type::Vector(e) => {
                self.needed_libc = true;
                if needs_runtime_cleanup(self.program, &e) {
                    let et = self.intern_type(&e);
                    self.require_release(et);
                }
            }
            Type::Map(k, v) => {
                self.needed_libc = true;
                if needs_runtime_cleanup(self.program, &k) {
                    let kt = self.intern_type(&k);
                    self.require_release(kt);
                }
                if needs_runtime_cleanup(self.program, &v) {
                    let vt = self.intern_type(&v);
                    self.require_release(vt);
                }
            }
            Type::Struct(sid, _) => {
                for f in &self.program.structs[sid].fields {
                    if needs_runtime_cleanup(self.program, &f.ty) {
                        let ft = self.intern_type(&f.ty);
                        self.require_release(ft);
                    }
                }
            }
            Type::Variant(vid, _) => {
                for c in &self.program.variants[vid].constructors {
                    for f in &c.fields {
                        if needs_runtime_cleanup(self.program, &f.ty) {
                            let ft = self.intern_type(&f.ty);
                            self.require_release(ft);
                        }
                    }
                }
            }
            Type::Outcome(oid, _) => {
                for a in &self.program.outcomes[oid].alternatives {
                    for f in &a.fields {
                        if needs_runtime_cleanup(self.program, &f.ty) {
                            let ft = self.intern_type(&f.ty);
                            self.require_release(ft);
                        }
                    }
                }
            }
            _ => {}
        }
    }
}

fn format_llvm_cbytes(bytes: &[u8]) -> String {
    let mut out = String::new();
    for &b in bytes {
        if (0x20..0x7f).contains(&b) && b != b'\\' && b != b'"' {
            out.push(b as char);
        } else {
            let _ = write!(out, "\\{:02X}", b);
        }
    }
    out.push_str("\\00");
    out
}

fn emit_type_decls(out: &mut String, reg: &RuntimeRegistry<'_>, include_slice2: bool) {
    let program = reg.program;
    let u = reg.usize_ty;
    let emit_agg = include_slice2
        || !program.structs.is_empty()
        || !program.variants.is_empty()
        || !program.outcomes.is_empty()
        || !program.boundaries.is_empty()
        || reg.needed_libc
        || reg.needed_str
        || reg.needed_vec_grow
        || !reg.registered_maps.is_empty()
        || !reg.registered_types.is_empty();
    if emit_agg {
        let _ = writeln!(out, "%vn2.string = type {{ ptr, {u}, {u} }}");
        let _ = writeln!(out, "%vn2.vec = type {{ ptr, {u}, {u} }}");
        let _ = writeln!(out, "%vn2.map = type {{ ptr, {u}, {u} }}");
    }
    for (sid, s) in program.structs.iter().enumerate() {
        if s.fields.is_empty() {
            let _ = writeln!(out, "%vn2.struct.{sid} = type {{ i8 }}");
        } else {
            let ftys: Vec<String> = s
                .fields
                .iter()
                .map(|f| llvm_ty(program, &f.ty, reg.usize_bits))
                .collect();
            let _ = writeln!(out, "%vn2.struct.{sid} = type {{ {} }}", ftys.join(", "));
        }
    }
    for (vid, v) in program.variants.iter().enumerate() {
        if !is_unit_variant(program, vid) {
            let words = variant_payload_words(program, vid, reg.usize_bits);
            let _ = writeln!(out, "%vn2.variant.{vid} = type {{ i32, [{words} x i64] }}");
            for (k, c) in v.constructors.iter().enumerate() {
                if !c.fields.is_empty() {
                    let ftys: Vec<String> = c
                        .fields
                        .iter()
                        .map(|f| llvm_ty(program, &f.ty, reg.usize_bits))
                        .collect();
                    let _ = writeln!(
                        out,
                        "%vn2.variant.{vid}.c{k} = type {{ {} }}",
                        ftys.join(", ")
                    );
                }
            }
        }
    }
    for (oid, o) in program.outcomes.iter().enumerate() {
        if !is_unit_outcome(program, oid) {
            let words = outcome_payload_words(program, oid, reg.usize_bits);
            let _ = writeln!(out, "%vn2.outcome.{oid} = type {{ i32, [{words} x i64] }}");
            for (k, a) in o.alternatives.iter().enumerate() {
                if !a.fields.is_empty() {
                    let ftys: Vec<String> = a
                        .fields
                        .iter()
                        .map(|f| llvm_ty(program, &f.ty, reg.usize_bits))
                        .collect();
                    let _ = writeln!(
                        out,
                        "%vn2.outcome.{oid}.a{k} = type {{ {} }}",
                        ftys.join(", ")
                    );
                }
            }
        }
    }
    for (mid, (k, v)) in reg.registered_maps.iter().enumerate() {
        let k_ll = llvm_ty(program, k, reg.usize_bits);
        let v_ll = llvm_ty(program, v, reg.usize_bits);
        let _ = writeln!(out, "%vn2.map_entry.{mid} = type {{ {k_ll}, {v_ll} }}");
    }
    if emit_agg || !reg.str_literals.is_empty() {
        let _ = writeln!(out);
    }
    for (name, bytes) in &reg.str_literals {
        let len = bytes.len() + 1;
        let escaped = format_llvm_cbytes(bytes);
        let _ = writeln!(
            out,
            "{name} = private unnamed_addr constant [{len} x i8] c\"{escaped}\""
        );
    }
    if !reg.str_literals.is_empty() {
        let _ = writeln!(out);
    }
    if reg.needed_libc || reg.needed_str || reg.needed_vec_grow || !reg.registered_maps.is_empty() {
        let _ = writeln!(out, "declare ptr @malloc(i64)");
        let _ = writeln!(out, "declare ptr @realloc(ptr, i64)");
        let _ = writeln!(out, "declare void @free(ptr)");
        let _ = writeln!(out, "declare ptr @memcpy(ptr, ptr, i64)");
        let _ = writeln!(out, "declare ptr @memmove(ptr, ptr, i64)");
        let _ = writeln!(out, "declare i32 @memcmp(ptr, ptr, i64)");
        let _ = writeln!(out);
    }
}

fn emit_runtime_helpers(out: &mut String, reg: &RuntimeRegistry<'_>) {
    let program = reg.program;
    let u = reg.usize_ty;
    let ub = reg.usize_bits;

    let zext_u_to_64 = |val: &str, tmp: &mut String, out_buf: &mut String| -> String {
        if u == "i64" {
            val.to_string()
        } else {
            let _ = writeln!(out_buf, "  {tmp} = zext i32 {val} to i64");
            tmp.clone()
        }
    };
    let trunc_64_to_u = |val: &str, tmp: &mut String, out_buf: &mut String| -> String {
        if u == "i64" {
            val.to_string()
        } else {
            let _ = writeln!(out_buf, "  {tmp} = trunc i64 {val} to i32");
            tmp.clone()
        }
    };

    if reg.needed_str {
        // @vn2_str_drop(ptr %s)
        let _ = writeln!(
            out,
            "define internal fastcc void @vn2_str_drop(ptr %s) nounwind {{"
        );
        let _ = writeln!(out, "entry:");
        let _ = writeln!(
            out,
            "  %p_p = getelementptr %vn2.string, ptr %s, i32 0, i32 0"
        );
        let _ = writeln!(
            out,
            "  %c_p = getelementptr %vn2.string, ptr %s, i32 0, i32 2"
        );
        let _ = writeln!(out, "  %cap = load {u}, ptr %c_p");
        let _ = writeln!(out, "  %owned = icmp ne {u} %cap, 0");
        let _ = writeln!(out, "  br i1 %owned, label %do_free, label %done");
        let _ = writeln!(out, "do_free:");
        let _ = writeln!(out, "  %p = load ptr, ptr %p_p");
        let _ = writeln!(out, "  call void @free(ptr %p)");
        let _ = writeln!(out, "  br label %done");
        let _ = writeln!(out, "done:");
        let _ = writeln!(out, "  ret void");
        let _ = writeln!(out, "}}\n");

        // @vn2_str_clone(ptr %s) -> %vn2.string
        let _ = writeln!(
            out,
            "define internal fastcc %vn2.string @vn2_str_clone(ptr %s) nounwind {{"
        );
        let _ = writeln!(out, "entry:");
        let _ = writeln!(out, "  %v = load %vn2.string, ptr %s");
        let _ = writeln!(out, "  %cap = extractvalue %vn2.string %v, 2");
        let _ = writeln!(out, "  %is_heap = icmp ne {u} %cap, 0");
        let _ = writeln!(out, "  br i1 %is_heap, label %heap_copy, label %ret_static");
        let _ = writeln!(out, "ret_static:");
        let _ = writeln!(out, "  ret %vn2.string %v");
        let _ = writeln!(out, "heap_copy:");
        let _ = writeln!(out, "  %p = extractvalue %vn2.string %v, 0");
        let _ = writeln!(out, "  %len = extractvalue %vn2.string %v, 1");
        let _ = writeln!(out, "  %is_empty = icmp eq {u} %len, 0");
        let _ = writeln!(out, "  br i1 %is_empty, label %ret_empty, label %alloc");
        let _ = writeln!(out, "ret_empty:");
        let _ = writeln!(out, "  ret %vn2.string zeroinitializer");
        let _ = writeln!(out, "alloc:");
        let _ = writeln!(out, "  %new_cap = add {u} %len, 1");
        let mut l64 = "%l64".to_string();
        let mut nc64 = "%nc64".to_string();
        let len64 = zext_u_to_64("%len", &mut l64, out);
        let ncap64 = zext_u_to_64("%new_cap", &mut nc64, out);
        let _ = writeln!(out, "  %buf = call ptr @malloc(i64 {ncap64})");
        let _ = writeln!(out, "  call ptr @memcpy(ptr %buf, ptr %p, i64 {len64})");
        let _ = writeln!(out, "  %nul = getelementptr i8, ptr %buf, {u} %len");
        let _ = writeln!(out, "  store i8 0, ptr %nul");
        let _ = writeln!(out, "  %s0 = insertvalue %vn2.string undef, ptr %buf, 0");
        let _ = writeln!(out, "  %s1 = insertvalue %vn2.string %s0, {u} %len, 1");
        let _ = writeln!(out, "  %s2 = insertvalue %vn2.string %s1, {u} %new_cap, 2",);
        let _ = writeln!(out, "  ret %vn2.string %s2");
        let _ = writeln!(out, "}}\n");

        // @vn2_str_eq(ptr %a, ptr %b) -> i1
        let _ = writeln!(
            out,
            "define internal fastcc i1 @vn2_str_eq(ptr %a, ptr %b) nounwind {{"
        );
        let _ = writeln!(out, "entry:");
        let _ = writeln!(out, "  %va = load %vn2.string, ptr %a");
        let _ = writeln!(out, "  %vb = load %vn2.string, ptr %b");
        let _ = writeln!(out, "  %la = extractvalue %vn2.string %va, 1");
        let _ = writeln!(out, "  %lb = extractvalue %vn2.string %vb, 1");
        let _ = writeln!(out, "  %same_len = icmp eq {u} %la, %lb");
        let _ = writeln!(out, "  br i1 %same_len, label %chk_zero, label %diff");
        let _ = writeln!(out, "chk_zero:");
        let _ = writeln!(out, "  %is_z = icmp eq {u} %la, 0");
        let _ = writeln!(out, "  br i1 %is_z, label %same, label %cmp_bytes");
        let _ = writeln!(out, "cmp_bytes:");
        let _ = writeln!(out, "  %pa = extractvalue %vn2.string %va, 0");
        let _ = writeln!(out, "  %pb = extractvalue %vn2.string %vb, 0");
        let mut la64 = "%la64".to_string();
        let l_arg = zext_u_to_64("%la", &mut la64, out);
        let _ = writeln!(
            out,
            "  %rc = call i32 @memcmp(ptr %pa, ptr %pb, i64 {l_arg})"
        );
        let _ = writeln!(out, "  %eq = icmp eq i32 %rc, 0");
        let _ = writeln!(out, "  ret i1 %eq");
        let _ = writeln!(out, "same:");
        let _ = writeln!(out, "  ret i1 true");
        let _ = writeln!(out, "diff:");
        let _ = writeln!(out, "  ret i1 false");
        let _ = writeln!(out, "}}\n");

        // @vn2_str_cmp(ptr %a, ptr %b) -> i32
        let _ = writeln!(
            out,
            "define internal fastcc i32 @vn2_str_cmp(ptr %a, ptr %b) nounwind {{"
        );
        let _ = writeln!(out, "entry:");
        let _ = writeln!(out, "  %va = load %vn2.string, ptr %a");
        let _ = writeln!(out, "  %vb = load %vn2.string, ptr %b");
        let _ = writeln!(out, "  %la = extractvalue %vn2.string %va, 1");
        let _ = writeln!(out, "  %lb = extractvalue %vn2.string %vb, 1");
        let _ = writeln!(out, "  %a_lt = icmp ult {u} %la, %lb");
        let _ = writeln!(out, "  %minl = select i1 %a_lt, {u} %la, {u} %lb");
        let _ = writeln!(out, "  %has = icmp ne {u} %minl, 0");
        let _ = writeln!(out, "  br i1 %has, label %do_memcmp, label %cmp_len");
        let _ = writeln!(out, "do_memcmp:");
        let _ = writeln!(out, "  %pa = extractvalue %vn2.string %va, 0");
        let _ = writeln!(out, "  %pb = extractvalue %vn2.string %vb, 0");
        let mut m64 = "%m64".to_string();
        let m_arg = zext_u_to_64("%minl", &mut m64, out);
        let _ = writeln!(
            out,
            "  %mc = call i32 @memcmp(ptr %pa, ptr %pb, i64 {m_arg})"
        );
        let _ = writeln!(out, "  %nz = icmp ne i32 %mc, 0");
        let _ = writeln!(out, "  br i1 %nz, label %ret_mc, label %cmp_len");
        let _ = writeln!(out, "ret_mc:");
        let _ = writeln!(out, "  ret i32 %mc");
        let _ = writeln!(out, "cmp_len:");
        let _ = writeln!(out, "  %eq = icmp eq {u} %la, %lb");
        let _ = writeln!(out, "  br i1 %eq, label %ret_zero, label %not_eq");
        let _ = writeln!(out, "ret_zero:");
        let _ = writeln!(out, "  ret i32 0");
        let _ = writeln!(out, "not_eq:");
        let _ = writeln!(out, "  %res = select i1 %a_lt, i32 -1, i32 1");
        let _ = writeln!(out, "  ret i32 %res");
        let _ = writeln!(out, "}}\n");

        // @vn2_str_trim(ptr %s) -> %vn2.string
        let _ = writeln!(
            out,
            "define internal fastcc %vn2.string @vn2_str_trim(ptr %s) nounwind {{"
        );
        let _ = writeln!(out, "entry:");
        let _ = writeln!(out, "  %v = load %vn2.string, ptr %s");
        let _ = writeln!(out, "  %p = extractvalue %vn2.string %v, 0");
        let _ = writeln!(out, "  %len = extractvalue %vn2.string %v, 1");
        let _ = writeln!(out, "  %start = alloca {u}");
        let _ = writeln!(out, "  %end = alloca {u}");
        let _ = writeln!(out, "  store {u} 0, ptr %start");
        let _ = writeln!(out, "  store {u} %len, ptr %end");
        let _ = writeln!(out, "  br label %lead_loop");
        let _ = writeln!(out, "lead_loop:");
        let _ = writeln!(out, "  %si = load {u}, ptr %start");
        let _ = writeln!(out, "  %ei = load {u}, ptr %end");
        let _ = writeln!(out, "  %cond1 = icmp ult {u} %si, %ei");
        let _ = writeln!(out, "  br i1 %cond1, label %lead_chk, label %trail_loop");
        let _ = writeln!(out, "lead_chk:");
        let _ = writeln!(out, "  %ch1p = getelementptr i8, ptr %p, {u} %si");
        let _ = writeln!(out, "  %c1 = load i8, ptr %ch1p");
        let _ = writeln!(out, "  %ws1a = icmp eq i8 %c1, 32");
        let _ = writeln!(out, "  %ws1b = icmp eq i8 %c1, 9");
        let _ = writeln!(out, "  %ws1c = icmp eq i8 %c1, 10");
        let _ = writeln!(out, "  %ws1d = icmp eq i8 %c1, 13");
        let _ = writeln!(out, "  %w1_0 = or i1 %ws1a, %ws1b");
        let _ = writeln!(out, "  %w1_1 = or i1 %ws1c, %ws1d");
        let _ = writeln!(out, "  %w1 = or i1 %w1_0, %w1_1");
        let _ = writeln!(out, "  br i1 %w1, label %lead_inc, label %trail_loop");
        let _ = writeln!(out, "lead_inc:");
        let _ = writeln!(out, "  %si_next = add {u} %si, 1");
        let _ = writeln!(out, "  store {u} %si_next, ptr %start");
        let _ = writeln!(out, "  br label %lead_loop");
        let _ = writeln!(out, "trail_loop:");
        let _ = writeln!(out, "  %s2 = load {u}, ptr %start");
        let _ = writeln!(out, "  %e2 = load {u}, ptr %end");
        let _ = writeln!(out, "  %cond2 = icmp ult {u} %s2, %e2");
        let _ = writeln!(out, "  br i1 %cond2, label %trail_chk, label %finish");
        let _ = writeln!(out, "trail_chk:");
        let _ = writeln!(out, "  %em1 = sub {u} %e2, 1");
        let _ = writeln!(out, "  %ch2p = getelementptr i8, ptr %p, {u} %em1");
        let _ = writeln!(out, "  %c2 = load i8, ptr %ch2p");
        let _ = writeln!(out, "  %ws2a = icmp eq i8 %c2, 32");
        let _ = writeln!(out, "  %ws2b = icmp eq i8 %c2, 9");
        let _ = writeln!(out, "  %ws2c = icmp eq i8 %c2, 10");
        let _ = writeln!(out, "  %ws2d = icmp eq i8 %c2, 13");
        let _ = writeln!(out, "  %w2_0 = or i1 %ws2a, %ws2b");
        let _ = writeln!(out, "  %w2_1 = or i1 %ws2c, %ws2d");
        let _ = writeln!(out, "  %w2 = or i1 %w2_0, %w2_1");
        let _ = writeln!(out, "  br i1 %w2, label %trail_dec, label %finish");
        let _ = writeln!(out, "trail_dec:");
        let _ = writeln!(out, "  store {u} %em1, ptr %end");
        let _ = writeln!(out, "  br label %trail_loop");
        let _ = writeln!(out, "finish:");
        let _ = writeln!(out, "  %fs = load {u}, ptr %start");
        let _ = writeln!(out, "  %fe = load {u}, ptr %end");
        let _ = writeln!(out, "  %nlen = sub {u} %fe, %fs");
        let _ = writeln!(out, "  %is_z = icmp eq {u} %nlen, 0");
        let _ = writeln!(out, "  br i1 %is_z, label %ret_z, label %do_alloc");
        let _ = writeln!(out, "ret_z:");
        let _ = writeln!(out, "  ret %vn2.string zeroinitializer");
        let _ = writeln!(out, "do_alloc:");
        let _ = writeln!(out, "  %cap = add {u} %nlen, 1");
        let mut nl64 = "%nl64".to_string();
        let mut cp64 = "%cp64".to_string();
        let nlen64 = zext_u_to_64("%nlen", &mut nl64, out);
        let ncap64 = zext_u_to_64("%cap", &mut cp64, out);
        let _ = writeln!(out, "  %dst = call ptr @malloc(i64 {ncap64})");
        let _ = writeln!(out, "  %src = getelementptr i8, ptr %p, {u} %fs");
        let _ = writeln!(out, "  call ptr @memcpy(ptr %dst, ptr %src, i64 {nlen64})");
        let _ = writeln!(out, "  %zpos = getelementptr i8, ptr %dst, {u} %nlen");
        let _ = writeln!(out, "  store i8 0, ptr %zpos");
        let _ = writeln!(out, "  %r0 = insertvalue %vn2.string undef, ptr %dst, 0");
        let _ = writeln!(out, "  %r1 = insertvalue %vn2.string %r0, {u} %nlen, 1");
        let _ = writeln!(out, "  %r2 = insertvalue %vn2.string %r1, {u} %cap, 2");
        let _ = writeln!(out, "  ret %vn2.string %r2");
        let _ = writeln!(out, "}}\n");
    }

    if reg.needed_vec_grow {
        let _ = writeln!(
            out,
            "define internal fastcc void @vn2_vec_grow(ptr %v, i64 %stride) nounwind {{"
        );
        let _ = writeln!(out, "entry:");
        let _ = writeln!(out, "  %dp = getelementptr %vn2.vec, ptr %v, i32 0, i32 0");
        let _ = writeln!(out, "  %cp = getelementptr %vn2.vec, ptr %v, i32 0, i32 2");
        let _ = writeln!(out, "  %data = load ptr, ptr %dp");
        let _ = writeln!(out, "  %cap = load {u}, ptr %cp");
        let _ = writeln!(out, "  %is_z = icmp eq {u} %cap, 0");
        let _ = writeln!(out, "  %dbl = mul {u} %cap, 2");
        let _ = writeln!(out, "  %ncap = select i1 %is_z, {u} 4, {u} %dbl");
        let mut ncap_tmp = "%ncap64".to_string();
        let ncap64 = zext_u_to_64("%ncap", &mut ncap_tmp, out);
        let _ = writeln!(out, "  %bytes = mul i64 {ncap64}, %stride");
        let _ = writeln!(out, "  %nd = call ptr @realloc(ptr %data, i64 %bytes)");
        let _ = writeln!(out, "  store ptr %nd, ptr %dp");
        let _ = writeln!(out, "  store {u} %ncap, ptr %cp");
        let _ = writeln!(out, "  ret void");
        let _ = writeln!(out, "}}\n");
    }

    // Iterate registered type helpers cleanly. Notice we collect snapshots in
    // fixed order since all transitive requirements were registered beforehand.
    let eq_ids: Vec<usize> = reg.needed_eq.iter().copied().collect();
    for tid in eq_ids {
        emit_type_eq(out, reg, tid);
    }
    let cmp_ids: Vec<usize> = reg.needed_cmp.iter().copied().collect();
    for tid in cmp_ids {
        emit_type_cmp(out, reg, tid);
    }
    let clone_ids: Vec<usize> = reg.needed_clone.iter().copied().collect();
    for tid in clone_ids {
        emit_type_clone(out, reg, tid);
    }
    let drop_ids: Vec<usize> = reg.needed_drop.iter().copied().collect();
    for tid in drop_ids {
        emit_type_cleanup(out, reg, tid, false);
    }
    let rel_ids: Vec<usize> = reg.needed_release.iter().copied().collect();
    for tid in rel_ids {
        emit_type_cleanup(out, reg, tid, true);
    }
    for mid in 0..reg.registered_maps.len() {
        emit_map_ops(out, reg, mid, &trunc_64_to_u, &zext_u_to_64);
        let _ = (program, ub);
    }
}

fn emit_type_eq(out: &mut String, reg: &RuntimeRegistry<'_>, tid: usize) {
    let program = reg.program;
    let ty = &reg.registered_types[tid];
    let u = reg.usize_ty;
    let ll = llvm_ty(program, ty, reg.usize_bits);
    let _ = writeln!(
        out,
        "define internal fastcc i1 @vn2_eq_{tid}(ptr %a, ptr %b) nounwind {{"
    );
    let _ = writeln!(out, "entry:");
    match ty {
        Type::Bool | Type::Int(_) | Type::Resource(_, _) => {
            let _ = writeln!(out, "  %va = load {ll}, ptr %a");
            let _ = writeln!(out, "  %vb = load {ll}, ptr %b");
            let _ = writeln!(out, "  %r = icmp eq {ll} %va, %vb");
            let _ = writeln!(out, "  ret i1 %r");
        }
        Type::String => {
            let _ = writeln!(out, "  %r = call fastcc i1 @vn2_str_eq(ptr %a, ptr %b)");
            let _ = writeln!(out, "  ret i1 %r");
        }
        Type::Struct(sid, _) => {
            let fields = &program.structs[*sid].fields;
            for (fi, f) in fields.iter().enumerate() {
                let ftid = reg.type_ids[f.ty.deref_type()];
                let _ = writeln!(
                    out,
                    "  %fa_{fi} = getelementptr {ll}, ptr %a, i32 0, i32 {fi}"
                );
                let _ = writeln!(
                    out,
                    "  %fb_{fi} = getelementptr {ll}, ptr %b, i32 0, i32 {fi}"
                );
                let _ = writeln!(
                    out,
                    "  %ok_{fi} = call fastcc i1 @vn2_eq_{ftid}(ptr %fa_{fi}, ptr %fb_{fi})"
                );
                let _ = writeln!(out, "  br i1 %ok_{fi}, label %next_{fi}, label %ret_false");
                let _ = writeln!(out, "next_{fi}:");
            }
            let _ = writeln!(out, "  ret i1 true");
            let _ = writeln!(out, "ret_false:");
            let _ = writeln!(out, "  ret i1 false");
        }
        Type::Variant(vid, _) => {
            if is_unit_variant(program, *vid) {
                let _ = writeln!(out, "  %ta = load i32, ptr %a");
                let _ = writeln!(out, "  %tb = load i32, ptr %b");
                let _ = writeln!(out, "  %r = icmp eq i32 %ta, %tb");
                let _ = writeln!(out, "  ret i1 %r");
            } else {
                emit_tagged_eq(
                    out,
                    reg,
                    tid,
                    &ll,
                    |k| format!("%vn2.variant.{vid}.c{k}"),
                    program.variants[*vid]
                        .constructors
                        .iter()
                        .map(|c| &c.fields),
                );
            }
        }
        Type::Outcome(oid, _) => {
            if is_unit_outcome(program, *oid) {
                let _ = writeln!(out, "  %ta = load i32, ptr %a");
                let _ = writeln!(out, "  %tb = load i32, ptr %b");
                let _ = writeln!(out, "  %r = icmp eq i32 %ta, %tb");
                let _ = writeln!(out, "  ret i1 %r");
            } else {
                emit_tagged_eq(
                    out,
                    reg,
                    tid,
                    &ll,
                    |k| format!("%vn2.outcome.{oid}.a{k}"),
                    program.outcomes[*oid]
                        .alternatives
                        .iter()
                        .map(|a| &a.fields),
                );
            }
        }
        Type::Vector(elem) => {
            let etid = reg.type_ids[elem.deref_type()];
            let e_ll = llvm_ty(program, elem, reg.usize_bits);
            let _ = writeln!(out, "  %va = load %vn2.vec, ptr %a");
            let _ = writeln!(out, "  %vb = load %vn2.vec, ptr %b");
            let _ = writeln!(out, "  %la = extractvalue %vn2.vec %va, 1");
            let _ = writeln!(out, "  %lb = extractvalue %vn2.vec %vb, 1");
            let _ = writeln!(out, "  %sl = icmp eq {u} %la, %lb");
            let _ = writeln!(out, "  br i1 %sl, label %chk, label %ret_f");
            let _ = writeln!(out, "chk:");
            let _ = writeln!(out, "  %da = extractvalue %vn2.vec %va, 0");
            let _ = writeln!(out, "  %db = extractvalue %vn2.vec %vb, 0");
            let _ = writeln!(out, "  %i_s = alloca {u}");
            let _ = writeln!(out, "  store {u} 0, ptr %i_s");
            let _ = writeln!(out, "  br label %lp");
            let _ = writeln!(out, "lp:");
            let _ = writeln!(out, "  %i = load {u}, ptr %i_s");
            let _ = writeln!(out, "  %more = icmp ult {u} %i, %la");
            let _ = writeln!(out, "  br i1 %more, label %elem, label %ret_t");
            let _ = writeln!(out, "elem:");
            let _ = writeln!(out, "  %ea = getelementptr {e_ll}, ptr %da, {u} %i");
            let _ = writeln!(out, "  %eb = getelementptr {e_ll}, ptr %db, {u} %i");
            let _ = writeln!(
                out,
                "  %eq = call fastcc i1 @vn2_eq_{etid}(ptr %ea, ptr %eb)"
            );
            let _ = writeln!(out, "  br i1 %eq, label %step, label %ret_f");
            let _ = writeln!(out, "step:");
            let _ = writeln!(out, "  %ni = add {u} %i, 1");
            let _ = writeln!(out, "  store {u} %ni, ptr %i_s");
            let _ = writeln!(out, "  br label %lp");
            let _ = writeln!(out, "ret_t:");
            let _ = writeln!(out, "  ret i1 true");
            let _ = writeln!(out, "ret_f:");
            let _ = writeln!(out, "  ret i1 false");
        }
        Type::Map(k, v) => {
            let ktid = reg.type_ids[k.deref_type()];
            let vtid = reg.type_ids[v.deref_type()];
            let mid = reg.map_ids[&((**k).clone(), (**v).clone())];
            let entry_ty = format!("%vn2.map_entry.{mid}");
            let _ = writeln!(out, "  %ma = load %vn2.map, ptr %a");
            let _ = writeln!(out, "  %mb = load %vn2.map, ptr %b");
            let _ = writeln!(out, "  %la = extractvalue %vn2.map %ma, 1");
            let _ = writeln!(out, "  %lb = extractvalue %vn2.map %mb, 1");
            let _ = writeln!(out, "  %sl = icmp eq {u} %la, %lb");
            let _ = writeln!(out, "  br i1 %sl, label %chk, label %ret_f");
            let _ = writeln!(out, "chk:");
            let _ = writeln!(out, "  %da = extractvalue %vn2.map %ma, 0");
            let _ = writeln!(out, "  %db = extractvalue %vn2.map %mb, 0");
            let _ = writeln!(out, "  %i_s = alloca {u}");
            let _ = writeln!(out, "  store {u} 0, ptr %i_s");
            let _ = writeln!(out, "  br label %lp");
            let _ = writeln!(out, "lp:");
            let _ = writeln!(out, "  %i = load {u}, ptr %i_s");
            let _ = writeln!(out, "  %more = icmp ult {u} %i, %la");
            let _ = writeln!(out, "  br i1 %more, label %elem, label %ret_t");
            let _ = writeln!(out, "elem:");
            let _ = writeln!(out, "  %ea = getelementptr {entry_ty}, ptr %da, {u} %i");
            let _ = writeln!(out, "  %eb = getelementptr {entry_ty}, ptr %db, {u} %i");
            let _ = writeln!(
                out,
                "  %ka = getelementptr {entry_ty}, ptr %ea, i32 0, i32 0"
            );
            let _ = writeln!(
                out,
                "  %kb = getelementptr {entry_ty}, ptr %eb, i32 0, i32 0"
            );
            let _ = writeln!(
                out,
                "  %keq = call fastcc i1 @vn2_eq_{ktid}(ptr %ka, ptr %kb)"
            );
            let _ = writeln!(out, "  br i1 %keq, label %chk_v, label %ret_f");
            let _ = writeln!(out, "chk_v:");
            let _ = writeln!(
                out,
                "  %va = getelementptr {entry_ty}, ptr %ea, i32 0, i32 1"
            );
            let _ = writeln!(
                out,
                "  %vb = getelementptr {entry_ty}, ptr %eb, i32 0, i32 1"
            );
            let _ = writeln!(
                out,
                "  %veq = call fastcc i1 @vn2_eq_{vtid}(ptr %va, ptr %vb)"
            );
            let _ = writeln!(out, "  br i1 %veq, label %step, label %ret_f");
            let _ = writeln!(out, "step:");
            let _ = writeln!(out, "  %ni = add {u} %i, 1");
            let _ = writeln!(out, "  store {u} %ni, ptr %i_s");
            let _ = writeln!(out, "  br label %lp");
            let _ = writeln!(out, "ret_t:");
            let _ = writeln!(out, "  ret i1 true");
            let _ = writeln!(out, "ret_f:");
            let _ = writeln!(out, "  ret i1 false");
        }
        _ => {
            let _ = writeln!(out, "  ret i1 false");
        }
    }
    let _ = writeln!(out, "}}\n");
}

fn emit_tagged_eq<'a>(
    out: &mut String,
    reg: &RuntimeRegistry<'_>,
    _tid: usize,
    ll: &str,
    sub_ty: impl Fn(usize) -> String,
    ctors: impl Iterator<Item = &'a Vec<crate::typed::Parameter>>,
) {
    let ctors_vec: Vec<&Vec<crate::typed::Parameter>> = ctors.collect();
    let _ = writeln!(out, "  %ta_p = getelementptr {ll}, ptr %a, i32 0, i32 0");
    let _ = writeln!(out, "  %tb_p = getelementptr {ll}, ptr %b, i32 0, i32 0");
    let _ = writeln!(out, "  %ta = load i32, ptr %ta_p");
    let _ = writeln!(out, "  %tb = load i32, ptr %tb_p");
    let _ = writeln!(out, "  %same_t = icmp eq i32 %ta, %tb");
    let _ = writeln!(out, "  br i1 %same_t, label %chk_pay, label %ret_false");
    let _ = writeln!(out, "chk_pay:");
    let mut cases = String::new();
    for (k, fields) in ctors_vec.iter().enumerate() {
        if fields.is_empty() {
            let _ = write!(cases, " i32 {k}, label %ret_true");
        } else {
            let _ = write!(cases, " i32 {k}, label %arm_{k}");
        }
    }
    let _ = writeln!(out, "  switch i32 %ta, label %ret_true [ {cases} ]");
    let _ = writeln!(out, "ret_true:");
    let _ = writeln!(out, "  ret i1 true");
    let _ = writeln!(out, "ret_false:");
    let _ = writeln!(out, "  ret i1 false");
    for (k, fields) in ctors_vec.iter().enumerate() {
        if fields.is_empty() {
            continue;
        }
        let s_ll = sub_ty(k);
        let _ = writeln!(out, "arm_{k}:");
        // A name of the function is written once: each arm has its own.
        let _ = writeln!(out, "  %pa_{k} = getelementptr {ll}, ptr %a, i32 0, i32 1");
        let _ = writeln!(out, "  %pb_{k} = getelementptr {ll}, ptr %b, i32 0, i32 1");
        for (fi, f) in fields.iter().enumerate() {
            let ftid = reg.type_ids[f.ty.deref_type()];
            let _ = writeln!(
                out,
                "  %fa_{k}_{fi} = getelementptr {s_ll}, ptr %pa_{k}, i32 0, i32 {fi}"
            );
            let _ = writeln!(
                out,
                "  %fb_{k}_{fi} = getelementptr {s_ll}, ptr %pb_{k}, i32 0, i32 {fi}"
            );
            let _ = writeln!(
                out,
                "  %ok_{k}_{fi} = call fastcc i1 @vn2_eq_{ftid}(ptr %fa_{k}_{fi}, ptr %fb_{k}_{fi})"
            );
            let _ = writeln!(
                out,
                "  br i1 %ok_{k}_{fi}, label %next_{k}_{fi}, label %ret_false"
            );
            let _ = writeln!(out, "next_{k}_{fi}:");
        }
        let _ = writeln!(out, "  ret i1 true");
    }
}

fn emit_type_cmp(out: &mut String, reg: &RuntimeRegistry<'_>, tid: usize) {
    let program = reg.program;
    let ty = &reg.registered_types[tid];
    let ll = llvm_ty(program, ty, reg.usize_bits);
    let _ = writeln!(
        out,
        "define internal fastcc i32 @vn2_cmp_{tid}(ptr %a, ptr %b) nounwind {{"
    );
    let _ = writeln!(out, "entry:");
    match ty {
        Type::Bool => {
            let _ = writeln!(out, "  %va = load i1, ptr %a");
            let _ = writeln!(out, "  %vb = load i1, ptr %b");
            let _ = writeln!(out, "  %ia = zext i1 %va to i32");
            let _ = writeln!(out, "  %ib = zext i1 %vb to i32");
            let _ = writeln!(out, "  %r = sub i32 %ia, %ib");
            let _ = writeln!(out, "  ret i32 %r");
        }
        Type::Int(it) => {
            let lt = if it.is_signed() { "slt" } else { "ult" };
            let gt = if it.is_signed() { "sgt" } else { "ugt" };
            let _ = writeln!(out, "  %va = load {ll}, ptr %a");
            let _ = writeln!(out, "  %vb = load {ll}, ptr %b");
            let _ = writeln!(out, "  %is_lt = icmp {lt} {ll} %va, %vb");
            let _ = writeln!(out, "  %is_gt = icmp {gt} {ll} %va, %vb");
            let _ = writeln!(out, "  %r0 = select i1 %is_gt, i32 1, i32 0");
            let _ = writeln!(out, "  %r1 = select i1 %is_lt, i32 -1, i32 %r0");
            let _ = writeln!(out, "  ret i32 %r1");
        }
        Type::Resource(_, _) => {
            let _ = writeln!(out, "  %va = load ptr, ptr %a");
            let _ = writeln!(out, "  %vb = load ptr, ptr %b");
            let _ = writeln!(out, "  %ia = ptrtoint ptr %va to i64");
            let _ = writeln!(out, "  %ib = ptrtoint ptr %vb to i64");
            let _ = writeln!(out, "  %is_lt = icmp ult i64 %ia, %ib");
            let _ = writeln!(out, "  %is_gt = icmp ugt i64 %ia, %ib");
            let _ = writeln!(out, "  %r0 = select i1 %is_gt, i32 1, i32 0");
            let _ = writeln!(out, "  %r1 = select i1 %is_lt, i32 -1, i32 %r0");
            let _ = writeln!(out, "  ret i32 %r1");
        }
        Type::String => {
            let _ = writeln!(out, "  %r = call fastcc i32 @vn2_str_cmp(ptr %a, ptr %b)");
            let _ = writeln!(out, "  ret i32 %r");
        }
        Type::Struct(sid, _) => {
            for (fi, f) in program.structs[*sid].fields.iter().enumerate() {
                let ftid = reg.type_ids[f.ty.deref_type()];
                let _ = writeln!(
                    out,
                    "  %fa_{fi} = getelementptr {ll}, ptr %a, i32 0, i32 {fi}"
                );
                let _ = writeln!(
                    out,
                    "  %fb_{fi} = getelementptr {ll}, ptr %b, i32 0, i32 {fi}"
                );
                let _ = writeln!(
                    out,
                    "  %c_{fi} = call fastcc i32 @vn2_cmp_{ftid}(ptr %fa_{fi}, ptr %fb_{fi})"
                );
                let _ = writeln!(out, "  %nz_{fi} = icmp ne i32 %c_{fi}, 0");
                let _ = writeln!(out, "  br i1 %nz_{fi}, label %ret_{fi}, label %next_{fi}");
                let _ = writeln!(out, "ret_{fi}:");
                let _ = writeln!(out, "  ret i32 %c_{fi}");
                let _ = writeln!(out, "next_{fi}:");
            }
            let _ = writeln!(out, "  ret i32 0");
        }
        Type::Variant(vid, _) => {
            if is_unit_variant(program, *vid) {
                let _ = writeln!(out, "  %ta = load i32, ptr %a");
                let _ = writeln!(out, "  %tb = load i32, ptr %b");
                let _ = writeln!(out, "  %lt = icmp ult i32 %ta, %tb");
                let _ = writeln!(out, "  %gt = icmp ugt i32 %ta, %tb");
                let _ = writeln!(out, "  %r0 = select i1 %gt, i32 1, i32 0");
                let _ = writeln!(out, "  %r1 = select i1 %lt, i32 -1, i32 %r0");
                let _ = writeln!(out, "  ret i32 %r1");
            } else {
                let _ = writeln!(out, "  %ta_p = getelementptr {ll}, ptr %a, i32 0, i32 0");
                let _ = writeln!(out, "  %tb_p = getelementptr {ll}, ptr %b, i32 0, i32 0");
                let _ = writeln!(out, "  %ta = load i32, ptr %ta_p");
                let _ = writeln!(out, "  %tb = load i32, ptr %tb_p");
                let _ = writeln!(out, "  %same = icmp eq i32 %ta, %tb");
                let _ = writeln!(out, "  br i1 %same, label %chk_pay, label %diff_t");
                let _ = writeln!(out, "diff_t:");
                let _ = writeln!(out, "  %lt = icmp ult i32 %ta, %tb");
                let _ = writeln!(out, "  %rt = select i1 %lt, i32 -1, i32 1");
                let _ = writeln!(out, "  ret i32 %rt");
                let _ = writeln!(out, "chk_pay:");
                let mut cases = String::new();
                for (k, c) in program.variants[*vid].constructors.iter().enumerate() {
                    if c.fields.is_empty() {
                        let _ = write!(cases, " i32 {k}, label %ret_z");
                    } else {
                        let _ = write!(cases, " i32 {k}, label %arm_{k}");
                    }
                }
                let _ = writeln!(out, "  switch i32 %ta, label %ret_z [ {cases} ]");
                let _ = writeln!(out, "ret_z:");
                let _ = writeln!(out, "  ret i32 0");
                for (k, c) in program.variants[*vid].constructors.iter().enumerate() {
                    if c.fields.is_empty() {
                        continue;
                    }
                    let s_ll = format!("%vn2.variant.{vid}.c{k}");
                    let _ = writeln!(out, "arm_{k}:");
                    let _ = writeln!(out, "  %pa_{k} = getelementptr {ll}, ptr %a, i32 0, i32 1");
                    let _ = writeln!(out, "  %pb_{k} = getelementptr {ll}, ptr %b, i32 0, i32 1");
                    for (fi, f) in c.fields.iter().enumerate() {
                        let ftid = reg.type_ids[f.ty.deref_type()];
                        let _ = writeln!(
                            out,
                            "  %fa_{k}_{fi} = getelementptr {s_ll}, ptr %pa_{k}, i32 0, i32 {fi}"
                        );
                        let _ = writeln!(
                            out,
                            "  %fb_{k}_{fi} = getelementptr {s_ll}, ptr %pb_{k}, i32 0, i32 {fi}"
                        );
                        let _ = writeln!(
                            out,
                            "  %c_{k}_{fi} = call fastcc i32 @vn2_cmp_{ftid}(ptr %fa_{k}_{fi}, ptr %fb_{k}_{fi})"
                        );
                        let _ = writeln!(out, "  %nz_{k}_{fi} = icmp ne i32 %c_{k}_{fi}, 0");
                        let _ = writeln!(
                            out,
                            "  br i1 %nz_{k}_{fi}, label %ret_{k}_{fi}, label %next_{k}_{fi}"
                        );
                        let _ = writeln!(out, "ret_{k}_{fi}:");
                        let _ = writeln!(out, "  ret i32 %c_{k}_{fi}");
                        let _ = writeln!(out, "next_{k}_{fi}:");
                    }
                    let _ = writeln!(out, "  ret i32 0");
                }
            }
        }
        _ => {
            let _ = writeln!(out, "  ret i32 0");
        }
    }
    let _ = writeln!(out, "}}\n");
}

fn emit_type_clone(out: &mut String, reg: &RuntimeRegistry<'_>, tid: usize) {
    let program = reg.program;
    let ty = &reg.registered_types[tid];
    let u = reg.usize_ty;
    let ll = llvm_ty(program, ty, reg.usize_bits);
    let _ = writeln!(
        out,
        "define internal fastcc {ll} @vn2_clone_{tid}(ptr %p) nounwind {{"
    );
    let _ = writeln!(out, "entry:");
    match ty {
        Type::String => {
            let _ = writeln!(out, "  %r = call fastcc %vn2.string @vn2_str_clone(ptr %p)");
            let _ = writeln!(out, "  ret %vn2.string %r");
        }
        Type::Vector(elem) => {
            let etid = reg.type_ids[elem.deref_type()];
            let e_ll = llvm_ty(program, elem, reg.usize_bits);
            let _ = writeln!(out, "  %v = load %vn2.vec, ptr %p");
            let _ = writeln!(out, "  %data = extractvalue %vn2.vec %v, 0");
            let _ = writeln!(out, "  %len = extractvalue %vn2.vec %v, 1");
            let _ = writeln!(out, "  %is_z = icmp eq {u} %len, 0");
            let _ = writeln!(out, "  br i1 %is_z, label %ret_z, label %do_alloc");
            let _ = writeln!(out, "ret_z:");
            let _ = writeln!(out, "  ret %vn2.vec zeroinitializer");
            let _ = writeln!(out, "do_alloc:");
            let _ = writeln!(out, "  %sp = getelementptr {e_ll}, ptr null, i32 1");
            let _ = writeln!(out, "  %stride = ptrtoint ptr %sp to i64");
            let len64 = if u == "i64" {
                "%len".to_string()
            } else {
                let _ = writeln!(out, "  %len64 = zext i32 %len to i64");
                "%len64".to_string()
            };
            let _ = writeln!(out, "  %bytes = mul i64 {len64}, %stride");
            let _ = writeln!(out, "  %nbuf = call ptr @malloc(i64 %bytes)");
            if needs_drop(program, elem) {
                let _ = writeln!(out, "  %i_slot = alloca {u}");
                let _ = writeln!(out, "  store {u} 0, ptr %i_slot");
                let _ = writeln!(out, "  br label %cl_loop");
                let _ = writeln!(out, "cl_loop:");
                let _ = writeln!(out, "  %i = load {u}, ptr %i_slot");
                let _ = writeln!(out, "  %cont = icmp ult {u} %i, %len");
                let _ = writeln!(out, "  br i1 %cont, label %cl_body, label %cl_done");
                let _ = writeln!(out, "cl_body:");
                let _ = writeln!(out, "  %src_p = getelementptr {e_ll}, ptr %data, {u} %i");
                let _ = writeln!(out, "  %dst_p = getelementptr {e_ll}, ptr %nbuf, {u} %i");
                let _ = writeln!(
                    out,
                    "  %cv = call fastcc {e_ll} @vn2_clone_{etid}(ptr %src_p)"
                );
                let _ = writeln!(out, "  store {e_ll} %cv, ptr %dst_p");
                let _ = writeln!(out, "  %ni = add {u} %i, 1");
                let _ = writeln!(out, "  store {u} %ni, ptr %i_slot");
                let _ = writeln!(out, "  br label %cl_loop");
                let _ = writeln!(out, "cl_done:");
            } else {
                let _ = writeln!(out, "  call ptr @memcpy(ptr %nbuf, ptr %data, i64 %bytes)");
            }
            let _ = writeln!(out, "  %v0 = insertvalue %vn2.vec undef, ptr %nbuf, 0");
            let _ = writeln!(out, "  %v1 = insertvalue %vn2.vec %v0, {u} %len, 1");
            let _ = writeln!(out, "  %v2 = insertvalue %vn2.vec %v1, {u} %len, 2");
            let _ = writeln!(out, "  ret %vn2.vec %v2");
        }
        Type::Map(k, v) => {
            let ktid = reg.type_ids[k.deref_type()];
            let vtid = reg.type_ids[v.deref_type()];
            let k_ll = llvm_ty(program, k, reg.usize_bits);
            let v_ll = llvm_ty(program, v, reg.usize_bits);
            let mid = reg.map_ids[&((**k).clone(), (**v).clone())];
            let entry_ty = format!("%vn2.map_entry.{mid}");
            let _ = writeln!(out, "  %m = load %vn2.map, ptr %p");
            let _ = writeln!(out, "  %data = extractvalue %vn2.map %m, 0");
            let _ = writeln!(out, "  %len = extractvalue %vn2.map %m, 1");
            let _ = writeln!(out, "  %is_z = icmp eq {u} %len, 0");
            let _ = writeln!(out, "  br i1 %is_z, label %ret_z, label %do_alloc");
            let _ = writeln!(out, "ret_z:");
            let _ = writeln!(out, "  ret %vn2.map zeroinitializer");
            let _ = writeln!(out, "do_alloc:");
            let _ = writeln!(out, "  %sp = getelementptr {entry_ty}, ptr null, i32 1");
            let _ = writeln!(out, "  %stride = ptrtoint ptr %sp to i64");
            let len64 = if u == "i64" {
                "%len".to_string()
            } else {
                let _ = writeln!(out, "  %len64 = zext i32 %len to i64");
                "%len64".to_string()
            };
            let _ = writeln!(out, "  %bytes = mul i64 {len64}, %stride");
            let _ = writeln!(out, "  %nbuf = call ptr @malloc(i64 %bytes)");
            if needs_drop(program, k) || needs_drop(program, v) {
                let _ = writeln!(out, "  %i_slot = alloca {u}");
                let _ = writeln!(out, "  store {u} 0, ptr %i_slot");
                let _ = writeln!(out, "  br label %cl_loop");
                let _ = writeln!(out, "cl_loop:");
                let _ = writeln!(out, "  %i = load {u}, ptr %i_slot");
                let _ = writeln!(out, "  %cont = icmp ult {u} %i, %len");
                let _ = writeln!(out, "  br i1 %cont, label %cl_body, label %cl_done");
                let _ = writeln!(out, "cl_body:");
                let _ = writeln!(out, "  %se = getelementptr {entry_ty}, ptr %data, {u} %i");
                let _ = writeln!(out, "  %de = getelementptr {entry_ty}, ptr %nbuf, {u} %i");
                let _ = writeln!(
                    out,
                    "  %sk = getelementptr {entry_ty}, ptr %se, i32 0, i32 0"
                );
                let _ = writeln!(
                    out,
                    "  %sv = getelementptr {entry_ty}, ptr %se, i32 0, i32 1"
                );
                let _ = writeln!(
                    out,
                    "  %dk = getelementptr {entry_ty}, ptr %de, i32 0, i32 0"
                );
                let _ = writeln!(
                    out,
                    "  %dv = getelementptr {entry_ty}, ptr %de, i32 0, i32 1"
                );
                let _ = writeln!(out, "  %ck = call fastcc {k_ll} @vn2_clone_{ktid}(ptr %sk)");
                let _ = writeln!(out, "  %cv = call fastcc {v_ll} @vn2_clone_{vtid}(ptr %sv)");
                let _ = writeln!(out, "  store {k_ll} %ck, ptr %dk");
                let _ = writeln!(out, "  store {v_ll} %cv, ptr %dv");
                let _ = writeln!(out, "  %ni = add {u} %i, 1");
                let _ = writeln!(out, "  store {u} %ni, ptr %i_slot");
                let _ = writeln!(out, "  br label %cl_loop");
                let _ = writeln!(out, "cl_done:");
            } else {
                let _ = writeln!(out, "  call ptr @memcpy(ptr %nbuf, ptr %data, i64 %bytes)");
            }
            let _ = writeln!(out, "  %m0 = insertvalue %vn2.map undef, ptr %nbuf, 0");
            let _ = writeln!(out, "  %m1 = insertvalue %vn2.map %m0, {u} %len, 1");
            let _ = writeln!(out, "  %m2 = insertvalue %vn2.map %m1, {u} %len, 2");
            let _ = writeln!(out, "  ret %vn2.map %m2");
        }
        Type::Struct(sid, _) if needs_drop(program, ty) => {
            let fields = &program.structs[*sid].fields;
            let _ = writeln!(out, "  %dst = alloca {ll}");
            for (fi, f) in fields.iter().enumerate() {
                let ftid = reg.type_ids[f.ty.deref_type()];
                let f_ll = llvm_ty(program, &f.ty, reg.usize_bits);
                let _ = writeln!(
                    out,
                    "  %sf_{fi} = getelementptr {ll}, ptr %p, i32 0, i32 {fi}"
                );
                let _ = writeln!(
                    out,
                    "  %df_{fi} = getelementptr {ll}, ptr %dst, i32 0, i32 {fi}"
                );
                let _ = writeln!(
                    out,
                    "  %cv_{fi} = call fastcc {f_ll} @vn2_clone_{ftid}(ptr %sf_{fi})"
                );
                let _ = writeln!(out, "  store {f_ll} %cv_{fi}, ptr %df_{fi}");
            }
            let _ = writeln!(out, "  %res = load {ll}, ptr %dst");
            let _ = writeln!(out, "  ret {ll} %res");
        }
        Type::Variant(vid, _) if needs_drop(program, ty) => {
            let _ = writeln!(out, "  %dst = alloca {ll}");
            let _ = writeln!(out, "  store {ll} zeroinitializer, ptr %dst");
            let _ = writeln!(out, "  %tp = getelementptr {ll}, ptr %p, i32 0, i32 0");
            let _ = writeln!(out, "  %tag = load i32, ptr %tp");
            let _ = writeln!(out, "  %dp_t = getelementptr {ll}, ptr %dst, i32 0, i32 0");
            let _ = writeln!(out, "  store i32 %tag, ptr %dp_t");
            let mut cases = String::new();
            for (k, c) in program.variants[*vid].constructors.iter().enumerate() {
                if !c.fields.is_empty() {
                    let _ = write!(cases, " i32 {k}, label %arm_{k}");
                }
            }
            let _ = writeln!(out, "  switch i32 %tag, label %done [ {cases} ]");
            for (k, c) in program.variants[*vid].constructors.iter().enumerate() {
                if c.fields.is_empty() {
                    continue;
                }
                let s_ll = format!("%vn2.variant.{vid}.c{k}");
                let _ = writeln!(out, "arm_{k}:");
                let _ = writeln!(out, "  %sp_{k} = getelementptr {ll}, ptr %p, i32 0, i32 1");
                let _ = writeln!(
                    out,
                    "  %dp_{k} = getelementptr {ll}, ptr %dst, i32 0, i32 1"
                );
                for (fi, f) in c.fields.iter().enumerate() {
                    let ftid = reg.type_ids[f.ty.deref_type()];
                    let f_ll = llvm_ty(program, &f.ty, reg.usize_bits);
                    let _ = writeln!(
                        out,
                        "  %sf_{k}_{fi} = getelementptr {s_ll}, ptr %sp_{k}, i32 0, i32 {fi}"
                    );
                    let _ = writeln!(
                        out,
                        "  %df_{k}_{fi} = getelementptr {s_ll}, ptr %dp_{k}, i32 0, i32 {fi}"
                    );
                    let _ = writeln!(
                        out,
                        "  %cv_{k}_{fi} = call fastcc {f_ll} @vn2_clone_{ftid}(ptr %sf_{k}_{fi})"
                    );
                    let _ = writeln!(out, "  store {f_ll} %cv_{k}_{fi}, ptr %df_{k}_{fi}");
                }
                let _ = writeln!(out, "  br label %done");
            }
            let _ = writeln!(out, "done:");
            let _ = writeln!(out, "  %res = load {ll}, ptr %dst");
            let _ = writeln!(out, "  ret {ll} %res");
        }
        _ => {
            let _ = writeln!(out, "  %v = load {ll}, ptr %p");
            let _ = writeln!(out, "  ret {ll} %v");
        }
    }
    let _ = writeln!(out, "}}\n");
}

fn emit_type_cleanup(out: &mut String, reg: &RuntimeRegistry<'_>, tid: usize, is_release: bool) {
    let program = reg.program;
    let ty = &reg.registered_types[tid];
    let u = reg.usize_ty;
    let ll = llvm_ty(program, ty, reg.usize_bits);
    let fname = if is_release { "release" } else { "drop" };
    let _ = writeln!(
        out,
        "define internal fastcc void @vn2_{fname}_{tid}(ptr %p) nounwind {{"
    );
    let _ = writeln!(out, "entry:");
    let predicate = if is_release {
        needs_runtime_cleanup
    } else {
        needs_drop
    };
    if !predicate(program, ty) {
        let _ = writeln!(out, "  ret void");
        let _ = writeln!(out, "}}\n");
        return;
    }
    match ty {
        Type::Resource(rid, rname) => {
            if is_release && program.resources[*rid].on_fault_release {
                let _ = writeln!(out, "  %h = load ptr, ptr %p");
                let _ = writeln!(out, "  call void @vn2_release_{rname}(ptr %h)");
            }
            let _ = writeln!(out, "  ret void");
        }
        Type::String => {
            let _ = writeln!(out, "  call fastcc void @vn2_str_drop(ptr %p)");
            let _ = writeln!(out, "  ret void");
        }
        Type::Vector(elem) => {
            let e_ll = llvm_ty(program, elem, reg.usize_bits);
            let _ = writeln!(out, "  %v = load %vn2.vec, ptr %p");
            let _ = writeln!(out, "  %data = extractvalue %vn2.vec %v, 0");
            let _ = writeln!(out, "  %len = extractvalue %vn2.vec %v, 1");
            let _ = writeln!(out, "  %cap = extractvalue %vn2.vec %v, 2");
            if predicate(program, elem) {
                let etid = reg.type_ids[elem.deref_type()];
                let _ = writeln!(out, "  %i_slot = alloca {u}");
                let _ = writeln!(out, "  store {u} 0, ptr %i_slot");
                let _ = writeln!(out, "  br label %d_loop");
                let _ = writeln!(out, "d_loop:");
                let _ = writeln!(out, "  %i = load {u}, ptr %i_slot");
                let _ = writeln!(out, "  %cont = icmp ult {u} %i, %len");
                let _ = writeln!(out, "  br i1 %cont, label %d_body, label %d_free");
                let _ = writeln!(out, "d_body:");
                let _ = writeln!(out, "  %ep = getelementptr {e_ll}, ptr %data, {u} %i");
                let _ = writeln!(out, "  call fastcc void @vn2_{fname}_{etid}(ptr %ep)");
                let _ = writeln!(out, "  %ni = add {u} %i, 1");
                let _ = writeln!(out, "  store {u} %ni, ptr %i_slot");
                let _ = writeln!(out, "  br label %d_loop");
                let _ = writeln!(out, "d_free:");
            }
            let _ = writeln!(out, "  %has_cap = icmp ne {u} %cap, 0");
            let _ = writeln!(out, "  br i1 %has_cap, label %do_free, label %done");
            let _ = writeln!(out, "do_free:");
            let _ = writeln!(out, "  call void @free(ptr %data)");
            let _ = writeln!(out, "  br label %done");
            let _ = writeln!(out, "done:");
            let _ = writeln!(out, "  ret void");
        }
        Type::Map(k, v) => {
            let mid = reg.map_ids[&((**k).clone(), (**v).clone())];
            let entry_ty = format!("%vn2.map_entry.{mid}");
            let _ = writeln!(out, "  %m = load %vn2.map, ptr %p");
            let _ = writeln!(out, "  %data = extractvalue %vn2.map %m, 0");
            let _ = writeln!(out, "  %len = extractvalue %vn2.map %m, 1");
            let _ = writeln!(out, "  %cap = extractvalue %vn2.map %m, 2");
            if predicate(program, k) || predicate(program, v) {
                let _ = writeln!(out, "  %i_slot = alloca {u}");
                let _ = writeln!(out, "  store {u} 0, ptr %i_slot");
                let _ = writeln!(out, "  br label %d_loop");
                let _ = writeln!(out, "d_loop:");
                let _ = writeln!(out, "  %i = load {u}, ptr %i_slot");
                let _ = writeln!(out, "  %cont = icmp ult {u} %i, %len");
                let _ = writeln!(out, "  br i1 %cont, label %d_body, label %d_free");
                let _ = writeln!(out, "d_body:");
                let _ = writeln!(out, "  %ep = getelementptr {entry_ty}, ptr %data, {u} %i");
                if predicate(program, k) {
                    let ktid = reg.type_ids[k.deref_type()];
                    let _ = writeln!(
                        out,
                        "  %kp = getelementptr {entry_ty}, ptr %ep, i32 0, i32 0"
                    );
                    let _ = writeln!(out, "  call fastcc void @vn2_{fname}_{ktid}(ptr %kp)");
                }
                if predicate(program, v) {
                    let vtid = reg.type_ids[v.deref_type()];
                    let _ = writeln!(
                        out,
                        "  %vp = getelementptr {entry_ty}, ptr %ep, i32 0, i32 1"
                    );
                    let _ = writeln!(out, "  call fastcc void @vn2_{fname}_{vtid}(ptr %vp)");
                }
                let _ = writeln!(out, "  %ni = add {u} %i, 1");
                let _ = writeln!(out, "  store {u} %ni, ptr %i_slot");
                let _ = writeln!(out, "  br label %d_loop");
                let _ = writeln!(out, "d_free:");
            }
            let _ = writeln!(out, "  %has_cap = icmp ne {u} %cap, 0");
            let _ = writeln!(out, "  br i1 %has_cap, label %do_free, label %done");
            let _ = writeln!(out, "do_free:");
            let _ = writeln!(out, "  call void @free(ptr %data)");
            let _ = writeln!(out, "  br label %done");
            let _ = writeln!(out, "done:");
            let _ = writeln!(out, "  ret void");
        }
        Type::Struct(sid, _) => {
            for (fi, f) in program.structs[*sid].fields.iter().enumerate() {
                if predicate(program, &f.ty) {
                    let ftid = reg.type_ids[f.ty.deref_type()];
                    let _ = writeln!(
                        out,
                        "  %fp_{fi} = getelementptr {ll}, ptr %p, i32 0, i32 {fi}"
                    );
                    let _ = writeln!(out, "  call fastcc void @vn2_{fname}_{ftid}(ptr %fp_{fi})");
                }
            }
            let _ = writeln!(out, "  ret void");
        }
        // A variant or an outcome with no component anywhere is a number.
        Type::Variant(vid, _) if is_unit_variant(program, *vid) => {
            let _ = writeln!(out, "  ret void");
        }
        Type::Outcome(oid, _) if is_unit_outcome(program, *oid) => {
            let _ = writeln!(out, "  ret void");
        }
        Type::Variant(vid, _) => {
            emit_tagged_cleanup(
                out,
                reg,
                &ll,
                fname,
                predicate,
                |k| format!("%vn2.variant.{vid}.c{k}"),
                program.variants[*vid]
                    .constructors
                    .iter()
                    .map(|c| &c.fields),
            );
        }
        Type::Outcome(oid, _) => {
            emit_tagged_cleanup(
                out,
                reg,
                &ll,
                fname,
                predicate,
                |k| format!("%vn2.outcome.{oid}.a{k}"),
                program.outcomes[*oid]
                    .alternatives
                    .iter()
                    .map(|a| &a.fields),
            );
        }
        _ => {
            let _ = writeln!(out, "  ret void");
        }
    }
    let _ = writeln!(out, "}}\n");
}

fn emit_tagged_cleanup<'a>(
    out: &mut String,
    reg: &RuntimeRegistry<'_>,
    ll: &str,
    fname: &str,
    predicate: fn(&Program, &Type) -> bool,
    sub_ty: impl Fn(usize) -> String,
    ctors: impl Iterator<Item = &'a Vec<crate::typed::Parameter>>,
) {
    let ctors_vec: Vec<&Vec<crate::typed::Parameter>> = ctors.collect();
    let _ = writeln!(out, "  %tp = getelementptr {ll}, ptr %p, i32 0, i32 0");
    let _ = writeln!(out, "  %tag = load i32, ptr %tp");
    let mut cases = String::new();
    for (k, fields) in ctors_vec.iter().enumerate() {
        if fields.iter().any(|f| predicate(reg.program, &f.ty)) {
            let _ = write!(cases, " i32 {k}, label %arm_{k}");
        }
    }
    let _ = writeln!(out, "  switch i32 %tag, label %done [ {cases} ]");
    for (k, fields) in ctors_vec.iter().enumerate() {
        if !fields.iter().any(|f| predicate(reg.program, &f.ty)) {
            continue;
        }
        let s_ll = sub_ty(k);
        let _ = writeln!(out, "arm_{k}:");
        let _ = writeln!(out, "  %pay_{k} = getelementptr {ll}, ptr %p, i32 0, i32 1");
        for (fi, f) in fields.iter().enumerate() {
            if predicate(reg.program, &f.ty) {
                let ftid = reg.type_ids[f.ty.deref_type()];
                let _ = writeln!(
                    out,
                    "  %f_{k}_{fi} = getelementptr {s_ll}, ptr %pay_{k}, i32 0, i32 {fi}"
                );
                let _ = writeln!(
                    out,
                    "  call fastcc void @vn2_{fname}_{ftid}(ptr %f_{k}_{fi})"
                );
            }
        }
        let _ = writeln!(out, "  br label %done");
    }
    let _ = writeln!(out, "done:");
    let _ = writeln!(out, "  ret void");
}

fn emit_map_ops(
    out: &mut String,
    reg: &RuntimeRegistry<'_>,
    mid: usize,
    _trunc_64_to_u: &dyn Fn(&str, &mut String, &mut String) -> String,
    zext_u_to_64: &dyn Fn(&str, &mut String, &mut String) -> String,
) {
    let program = reg.program;
    let (ref k, ref v) = reg.registered_maps[mid];
    let ktid = reg.type_ids[k.deref_type()];
    let _vtid = reg.type_ids[v.deref_type()];
    let k_ll = llvm_ty(program, k, reg.usize_bits);
    let v_ll = llvm_ty(program, v, reg.usize_bits);
    let entry_ty = format!("%vn2.map_entry.{mid}");
    let u = reg.usize_ty;

    // @vn2_map_find_<mid>(ptr %m, ptr %key, ptr %out_found) -> <u_ty> (index where key is or belongs)
    let _ = writeln!(
        out,
        "define internal fastcc {u} @vn2_map_find_{mid}(ptr %m, ptr %k, ptr %found) nounwind {{"
    );
    let _ = writeln!(out, "entry:");
    let _ = writeln!(out, "  %dp = getelementptr %vn2.map, ptr %m, i32 0, i32 0");
    let _ = writeln!(out, "  %lp = getelementptr %vn2.map, ptr %m, i32 0, i32 1");
    let _ = writeln!(out, "  %data = load ptr, ptr %dp");
    let _ = writeln!(out, "  %len = load {u}, ptr %lp");
    let _ = writeln!(out, "  %lo = alloca {u}");
    let _ = writeln!(out, "  %hi = alloca {u}");
    let _ = writeln!(out, "  store {u} 0, ptr %lo");
    let _ = writeln!(out, "  store {u} %len, ptr %hi");
    let _ = writeln!(out, "  store i1 false, ptr %found");
    let _ = writeln!(out, "  br label %bs_loop");
    let _ = writeln!(out, "bs_loop:");
    let _ = writeln!(out, "  %lv = load {u}, ptr %lo");
    let _ = writeln!(out, "  %hv = load {u}, ptr %hi");
    let _ = writeln!(out, "  %cont = icmp ult {u} %lv, %hv");
    let _ = writeln!(out, "  br i1 %cont, label %bs_mid, label %bs_miss");
    let _ = writeln!(out, "bs_mid:");
    let _ = writeln!(out, "  %diff = sub {u} %hv, %lv");
    let _ = writeln!(out, "  %half = lshr {u} %diff, 1");
    let _ = writeln!(out, "  %mid = add {u} %lv, %half");
    let _ = writeln!(out, "  %ep = getelementptr {entry_ty}, ptr %data, {u} %mid");
    let _ = writeln!(
        out,
        "  %kp = getelementptr {entry_ty}, ptr %ep, i32 0, i32 0"
    );
    let _ = writeln!(
        out,
        "  %c = call fastcc i32 @vn2_cmp_{ktid}(ptr %kp, ptr %k)"
    );
    let _ = writeln!(out, "  %is_eq = icmp eq i32 %c, 0");
    let _ = writeln!(out, "  br i1 %is_eq, label %bs_hit, label %bs_step");
    let _ = writeln!(out, "bs_hit:");
    let _ = writeln!(out, "  store i1 true, ptr %found");
    let _ = writeln!(out, "  ret {u} %mid");
    let _ = writeln!(out, "bs_step:");
    let _ = writeln!(out, "  %is_lt = icmp slt i32 %c, 0");
    let _ = writeln!(out, "  br i1 %is_lt, label %go_right, label %go_left");
    let _ = writeln!(out, "go_right:");
    let _ = writeln!(out, "  %mp1 = add {u} %mid, 1");
    let _ = writeln!(out, "  store {u} %mp1, ptr %lo");
    let _ = writeln!(out, "  br label %bs_loop");
    let _ = writeln!(out, "go_left:");
    let _ = writeln!(out, "  store {u} %mid, ptr %hi");
    let _ = writeln!(out, "  br label %bs_loop");
    let _ = writeln!(out, "bs_miss:");
    let _ = writeln!(out, "  ret {u} %lv");
    let _ = writeln!(out, "}}\n");

    // @vn2_map_get_<mid>(ptr %m, ptr %k, ptr %v_out) -> i32 (0 = found, 1 = missing)
    let _ = writeln!(
        out,
        "define internal fastcc i32 @vn2_map_get_{mid}(ptr %m, ptr %k, ptr %v_out) nounwind {{"
    );
    let _ = writeln!(out, "entry:");
    let _ = writeln!(out, "  %found = alloca i1");
    let _ = writeln!(
        out,
        "  %idx = call fastcc {u} @vn2_map_find_{mid}(ptr %m, ptr %k, ptr %found)"
    );
    let _ = writeln!(out, "  %ok = load i1, ptr %found");
    let _ = writeln!(out, "  br i1 %ok, label %hit, label %miss");
    let _ = writeln!(out, "hit:");
    let _ = writeln!(out, "  %dp = getelementptr %vn2.map, ptr %m, i32 0, i32 0");
    let _ = writeln!(out, "  %data = load ptr, ptr %dp");
    let _ = writeln!(out, "  %ep = getelementptr {entry_ty}, ptr %data, {u} %idx");
    let _ = writeln!(
        out,
        "  %vp = getelementptr {entry_ty}, ptr %ep, i32 0, i32 1"
    );
    let _ = writeln!(out, "  store ptr %vp, ptr %v_out");
    let _ = writeln!(out, "  ret i32 0");
    let _ = writeln!(out, "miss:");
    let _ = writeln!(out, "  ret i32 1");
    let _ = writeln!(out, "}}\n");

    // @vn2_map_insert_<mid>(ptr %m, ptr %k, ptr %v, ptr %prev_out) -> i32 (0 = inserted, 1 = replaced)
    let _ = writeln!(
        out,
        "define internal fastcc i32 @vn2_map_insert_{mid}(ptr %m, ptr %k, ptr %v, ptr %prev_out) nounwind {{"
    );
    let _ = writeln!(out, "entry:");
    let _ = writeln!(out, "  %found = alloca i1");
    let _ = writeln!(
        out,
        "  %idx = call fastcc {u} @vn2_map_find_{mid}(ptr %m, ptr %k, ptr %found)"
    );
    let _ = writeln!(out, "  %ok = load i1, ptr %found");
    let _ = writeln!(out, "  br i1 %ok, label %replace, label %insert_new");
    let _ = writeln!(out, "replace:");
    let _ = writeln!(out, "  %dp0 = getelementptr %vn2.map, ptr %m, i32 0, i32 0");
    let _ = writeln!(out, "  %d0 = load ptr, ptr %dp0");
    let _ = writeln!(out, "  %ep0 = getelementptr {entry_ty}, ptr %d0, {u} %idx");
    let _ = writeln!(
        out,
        "  %vp0 = getelementptr {entry_ty}, ptr %ep0, i32 0, i32 1"
    );
    let _ = writeln!(out, "  %old_v = load {v_ll}, ptr %vp0");
    let _ = writeln!(out, "  store {v_ll} %old_v, ptr %prev_out");
    let _ = writeln!(out, "  %new_v = load {v_ll}, ptr %v");
    let _ = writeln!(out, "  store {v_ll} %new_v, ptr %vp0");
    if needs_drop(program, k) && reg.needed_drop.contains(&ktid) {
        let _ = writeln!(out, "  call fastcc void @vn2_drop_{ktid}(ptr %k)");
    }
    let _ = writeln!(out, "  ret i32 1");
    let _ = writeln!(out, "insert_new:");
    let _ = writeln!(out, "  %lp = getelementptr %vn2.map, ptr %m, i32 0, i32 1");
    let _ = writeln!(out, "  %cp = getelementptr %vn2.map, ptr %m, i32 0, i32 2");
    let _ = writeln!(out, "  %len = load {u}, ptr %lp");
    let _ = writeln!(out, "  %cap = load {u}, ptr %cp");
    let _ = writeln!(out, "  %full = icmp eq {u} %len, %cap");
    let _ = writeln!(out, "  br i1 %full, label %grow, label %shift");
    let _ = writeln!(out, "grow:");
    let _ = writeln!(out, "  %dp1 = getelementptr %vn2.map, ptr %m, i32 0, i32 0");
    let _ = writeln!(out, "  %d1 = load ptr, ptr %dp1");
    let _ = writeln!(out, "  %is_z = icmp eq {u} %cap, 0");
    let _ = writeln!(out, "  %dbl = mul {u} %cap, 2");
    let _ = writeln!(out, "  %ncap = select i1 %is_z, {u} 4, {u} %dbl");
    let _ = writeln!(out, "  %esp0 = getelementptr {entry_ty}, ptr null, i32 1");
    let _ = writeln!(out, "  %estr0 = ptrtoint ptr %esp0 to i64");
    let mut ncp_tmp = "%ncp64".to_string();
    let ncp64 = zext_u_to_64("%ncap", &mut ncp_tmp, out);
    let _ = writeln!(out, "  %gbytes = mul i64 {ncp64}, %estr0");
    let _ = writeln!(out, "  %nd = call ptr @realloc(ptr %d1, i64 %gbytes)");
    let _ = writeln!(out, "  store ptr %nd, ptr %dp1");
    let _ = writeln!(out, "  store {u} %ncap, ptr %cp");
    let _ = writeln!(out, "  br label %shift");
    let _ = writeln!(out, "shift:");
    let _ = writeln!(out, "  %dp2 = getelementptr %vn2.map, ptr %m, i32 0, i32 0");
    let _ = writeln!(out, "  %d2 = load ptr, ptr %dp2");
    let _ = writeln!(out, "  %tail = sub {u} %len, %idx");
    let _ = writeln!(out, "  %has_tail = icmp ne {u} %tail, 0");
    let _ = writeln!(out, "  br i1 %has_tail, label %do_move, label %put_entry");
    let _ = writeln!(out, "do_move:");
    let _ = writeln!(out, "  %esp1 = getelementptr {entry_ty}, ptr null, i32 1");
    let _ = writeln!(out, "  %estr1 = ptrtoint ptr %esp1 to i64");
    let mut t_tmp = "%tail64".to_string();
    let tail64 = zext_u_to_64("%tail", &mut t_tmp, out);
    let _ = writeln!(out, "  %mbytes = mul i64 {tail64}, %estr1");
    let _ = writeln!(
        out,
        "  %src_m = getelementptr {entry_ty}, ptr %d2, {u} %idx"
    );
    let _ = writeln!(out, "  %ip1 = add {u} %idx, 1");
    let _ = writeln!(
        out,
        "  %dst_m = getelementptr {entry_ty}, ptr %d2, {u} %ip1"
    );
    let _ = writeln!(
        out,
        "  call ptr @memmove(ptr %dst_m, ptr %src_m, i64 %mbytes)"
    );
    let _ = writeln!(out, "  br label %put_entry");
    let _ = writeln!(out, "put_entry:");
    let _ = writeln!(out, "  %slot = getelementptr {entry_ty}, ptr %d2, {u} %idx");
    let _ = writeln!(
        out,
        "  %sk = getelementptr {entry_ty}, ptr %slot, i32 0, i32 0"
    );
    let _ = writeln!(
        out,
        "  %sv = getelementptr {entry_ty}, ptr %slot, i32 0, i32 1"
    );
    let _ = writeln!(out, "  %kv = load {k_ll}, ptr %k");
    let _ = writeln!(out, "  %vv = load {v_ll}, ptr %v");
    let _ = writeln!(out, "  store {k_ll} %kv, ptr %sk");
    let _ = writeln!(out, "  store {v_ll} %vv, ptr %sv");
    let _ = writeln!(out, "  %nlen = add {u} %len, 1");
    let _ = writeln!(out, "  store {u} %nlen, ptr %lp");
    let _ = writeln!(out, "  ret i32 0");
    let _ = writeln!(out, "}}\n");

    // @vn2_map_remove_<mid>(ptr %m, ptr %k, ptr %prev_out) -> i32 (0 = removed, 1 = missing)
    let _ = writeln!(
        out,
        "define internal fastcc i32 @vn2_map_remove_{mid}(ptr %m, ptr %k, ptr %prev_out) nounwind {{"
    );
    let _ = writeln!(out, "entry:");
    let _ = writeln!(out, "  %found = alloca i1");
    let _ = writeln!(
        out,
        "  %idx = call fastcc {u} @vn2_map_find_{mid}(ptr %m, ptr %k, ptr %found)"
    );
    let _ = writeln!(out, "  %ok = load i1, ptr %found");
    let _ = writeln!(out, "  br i1 %ok, label %do_rem, label %miss");
    let _ = writeln!(out, "do_rem:");
    let _ = writeln!(out, "  %dp = getelementptr %vn2.map, ptr %m, i32 0, i32 0");
    let _ = writeln!(out, "  %lp = getelementptr %vn2.map, ptr %m, i32 0, i32 1");
    let _ = writeln!(out, "  %data = load ptr, ptr %dp");
    let _ = writeln!(out, "  %len = load {u}, ptr %lp");
    let _ = writeln!(out, "  %ep = getelementptr {entry_ty}, ptr %data, {u} %idx");
    let _ = writeln!(
        out,
        "  %kp = getelementptr {entry_ty}, ptr %ep, i32 0, i32 0"
    );
    let _ = writeln!(
        out,
        "  %vp = getelementptr {entry_ty}, ptr %ep, i32 0, i32 1"
    );
    let _ = writeln!(out, "  %old_v = load {v_ll}, ptr %vp");
    let _ = writeln!(out, "  store {v_ll} %old_v, ptr %prev_out");
    if needs_drop(program, k) && reg.needed_drop.contains(&ktid) {
        let _ = writeln!(out, "  call fastcc void @vn2_drop_{ktid}(ptr %kp)");
    }
    let _ = writeln!(out, "  %nlen = sub {u} %len, 1");
    let _ = writeln!(out, "  %tail = sub {u} %nlen, %idx");
    let _ = writeln!(out, "  %has_tail = icmp ne {u} %tail, 0");
    let _ = writeln!(out, "  br i1 %has_tail, label %do_shift, label %finish");
    let _ = writeln!(out, "do_shift:");
    let _ = writeln!(out, "  %esp = getelementptr {entry_ty}, ptr null, i32 1");
    let _ = writeln!(out, "  %estr = ptrtoint ptr %esp to i64");
    let mut tr_tmp = "%tr64".to_string();
    let tail64 = zext_u_to_64("%tail", &mut tr_tmp, out);
    let _ = writeln!(out, "  %bytes = mul i64 {tail64}, %estr");
    let _ = writeln!(out, "  %ip1 = add {u} %idx, 1");
    let _ = writeln!(
        out,
        "  %src = getelementptr {entry_ty}, ptr %data, {u} %ip1"
    );
    let _ = writeln!(out, "  call ptr @memmove(ptr %ep, ptr %src, i64 %bytes)");
    let _ = writeln!(out, "  br label %finish");
    let _ = writeln!(out, "finish:");
    let _ = writeln!(out, "  store {u} %nlen, ptr %lp");
    let _ = writeln!(out, "  ret i32 0");
    let _ = writeln!(out, "miss:");
    let _ = writeln!(out, "  ret i32 1");
    let _ = writeln!(out, "}}\n");
}

// ---------------------------------------------------------------------------
// Body classification & unwind planning
// ---------------------------------------------------------------------------

#[derive(Clone)]
enum BodyRole {
    Root,
    Loop {
        parent_body: BodyId,
        stmt_idx: usize,
        site: SiteId,
        arms: Vec<Vec<VarId>>,
    },
    LexicalB1 {
        parent_body: BodyId,
        stmt_idx: usize,
        site: SiteId,
        b2: BodyId,
        contingency_vars: Vec<VarId>,
        message_var: Option<VarId>,
    },
    LexicalB2 {
        parent_body: BodyId,
        stmt_idx: usize,
    },
}

enum UnwindTarget {
    LexicalCatch {
        b2: BodyId,
        message_var: Option<VarId>,
        frames_to_unwind: Vec<(BodyId, usize)>,
    },
    RootFault {
        frames_to_unwind: Vec<(BodyId, usize)>,
    },
    NamedBoundaryB1Fault {
        frames_to_unwind: Vec<(BodyId, usize)>,
    },
}

#[derive(Clone, Copy)]
enum UnitKind {
    Control { id: ControlId },
    NamedBoundaryB1 { id: BoundaryId },
    NamedBoundaryB2,
}

// ---------------------------------------------------------------------------
// IR emitter
// ---------------------------------------------------------------------------

struct IrEmitter<'a, 'r> {
    program: &'a Program,
    reg: &'r mut RuntimeRegistry<'a>,
    allocas: Vec<String>,
    code: String,
    next_reg: usize,
    next_label: usize,
}

enum VarAccess<'b> {
    DirectParams(&'b Function),
    ControlSlots(&'b ControlBody),
}

enum ReadOperand {
    PlacePtr(String),
    OwnedTemp { ptr: String, ty: Type },
}

impl<'a, 'r> IrEmitter<'a, 'r> {
    fn new(program: &'a Program, reg: &'r mut RuntimeRegistry<'a>) -> Self {
        Self {
            program,
            reg,
            allocas: Vec::new(),
            code: String::new(),
            next_reg: 0,
            next_label: 0,
        }
    }

    fn fresh_reg(&mut self) -> String {
        let r = format!("%r{}", self.next_reg);
        self.next_reg += 1;
        r
    }

    fn fresh_label(&mut self, prefix: &str) -> String {
        let l = format!("{prefix}_{}", self.next_label);
        self.next_label += 1;
        l
    }

    fn alloc_temp(&mut self, ty: &str) -> String {
        let ptr = format!("%tmp{}", self.next_reg);
        self.next_reg += 1;
        self.allocas.push(format!("  {ptr} = alloca {ty}"));
        ptr
    }

    fn llvm_ty(&self, ty: &Type) -> String {
        llvm_ty(self.program, ty, self.reg.usize_bits)
    }

    fn usize_ty(&self) -> &'static str {
        self.reg.usize_ty
    }

    fn emit_zext_usize_to_i64(&mut self, val: &str) -> String {
        if self.reg.usize_bits > 32 {
            val.to_string()
        } else {
            let r = self.fresh_reg();
            let _ = writeln!(self.code, "  {r} = zext i32 {val} to i64");
            r
        }
    }

    fn emit_drop_ptr(&mut self, ptr: &str, ty: &Type) {
        if needs_drop(self.program, ty) {
            let tid = self.reg.intern_type(ty);
            self.reg.require_drop(tid);
            let _ = writeln!(self.code, "  call fastcc void @vn2_drop_{tid}(ptr {ptr})");
        }
    }

    fn emit_release_ptr(&mut self, ptr: &str, ty: &Type) {
        if needs_runtime_cleanup(self.program, ty) {
            let tid = self.reg.intern_type(ty);
            self.reg.require_release(tid);
            let _ = writeln!(
                self.code,
                "  call fastcc void @vn2_release_{tid}(ptr {ptr})"
            );
        }
    }

    /// A copy of the string at `ptr`, which owns its text.
    fn emit_string_copy(&mut self, ptr: &str) -> String {
        let tid = self.reg.intern_type(&Type::String);
        self.reg.require_clone(tid);
        let copy = self.fresh_reg();
        let _ = writeln!(
            self.code,
            "  {copy} = call fastcc %vn2.string @vn2_clone_{tid}(ptr {ptr})"
        );
        copy
    }

    fn finish_read_operand(&mut self, op: ReadOperand) {
        if let ReadOperand::OwnedTemp { ptr, ty } = op {
            self.emit_drop_ptr(&ptr, &ty);
        }
    }

    fn read_operand_ptr<'b>(&mut self, op: &'b ReadOperand) -> &'b str {
        match op {
            ReadOperand::PlacePtr(p) | ReadOperand::OwnedTemp { ptr: p, .. } => p,
        }
    }

    fn emit_place_ptr(&mut self, place: &Place, access: &VarAccess<'_>) -> String {
        let mut cur_ptr = match access {
            VarAccess::ControlSlots(body) => {
                if matches!(body.vars[place.root].ty, Type::Ref(_, _)) {
                    let r = self.fresh_reg();
                    let _ = writeln!(self.code, "  {r} = load ptr, ptr %slot_{}", place.root);
                    r
                } else {
                    format!("%slot_{}", place.root)
                }
            }
            VarAccess::DirectParams(_) => unreachable!("Place only exists inside ControlBody"),
        };
        let mut cur_ty = place.root_ty.deref_type().clone();
        for step in &place.steps {
            match step {
                PlaceStep::Field(sid, fidx, fty) => {
                    let s_ll = self.llvm_ty(&Type::Struct(*sid, String::new()));
                    let gep = self.fresh_reg();
                    let _ = writeln!(
                        self.code,
                        "  {gep} = getelementptr {s_ll}, ptr {cur_ptr}, i32 0, i32 {fidx}"
                    );
                    if matches!(fty, Type::Ref(_, _)) {
                        let deref = self.fresh_reg();
                        let _ = writeln!(self.code, "  {deref} = load ptr, ptr {gep}");
                        cur_ptr = deref;
                    } else {
                        cur_ptr = gep;
                    }
                    cur_ty = fty.deref_type().clone();
                }
                PlaceStep::Index(idx_expr, elem_ty) => {
                    let idx_val = self.emit_expr(idx_expr, access);
                    let u = self.usize_ty();
                    let e_ll = self.llvm_ty(elem_ty);
                    let dp = self.fresh_reg();
                    let _ = writeln!(
                        self.code,
                        "  {dp} = getelementptr %vn2.vec, ptr {cur_ptr}, i32 0, i32 0"
                    );
                    let data = self.fresh_reg();
                    let _ = writeln!(self.code, "  {data} = load ptr, ptr {dp}");
                    let gep = self.fresh_reg();
                    let _ = writeln!(
                        self.code,
                        "  {gep} = getelementptr {e_ll}, ptr {data}, {u} {idx_val}"
                    );
                    cur_ptr = gep;
                    cur_ty = elem_ty.clone();
                }
            }
        }
        let _ = cur_ty;
        cur_ptr
    }

    fn emit_expr_ptr_if_place(&mut self, expr: &Expr, access: &VarAccess<'_>) -> Option<String> {
        match expr {
            Expr::Var(VarRef::Local(id), _) => {
                let VarAccess::ControlSlots(body) = access else {
                    return None;
                };
                if matches!(body.vars[*id].ty, Type::Ref(_, _)) {
                    let r = self.fresh_reg();
                    let _ = writeln!(self.code, "  {r} = load ptr, ptr %slot_{id}");
                    Some(r)
                } else {
                    Some(format!("%slot_{id}"))
                }
            }
            Expr::Var(VarRef::Parameter(idx), _) => {
                let VarAccess::DirectParams(func) = access else {
                    return None;
                };
                if matches!(func.parameters[*idx].ty, Type::Ref(_, _)) {
                    Some(format!("%p{idx}"))
                } else {
                    None
                }
            }
            Expr::Move(inner, _) => self.emit_expr_ptr_if_place(inner, access),
            Expr::Borrow(_, place, _) => Some(self.emit_place_ptr(place, access)),
            Expr::Field(base, sid, fidx, _) => {
                let decl_fty = self.program.structs[*sid].fields[*fidx].ty.clone();
                let s_ll = self.llvm_ty(&Type::Struct(*sid, String::new()));
                if matches!(decl_fty, Type::Ref(_, _)) {
                    if let Some(base_ptr) = self.emit_expr_ptr_if_place(base, access) {
                        let gep = self.fresh_reg();
                        let _ = writeln!(
                            self.code,
                            "  {gep} = getelementptr {s_ll}, ptr {base_ptr}, i32 0, i32 {fidx}"
                        );
                        let deref = self.fresh_reg();
                        let _ = writeln!(self.code, "  {deref} = load ptr, ptr {gep}");
                        Some(deref)
                    } else {
                        let b_val = self.emit_expr(base, access);
                        let deref = self.fresh_reg();
                        let _ =
                            writeln!(self.code, "  {deref} = extractvalue {s_ll} {b_val}, {fidx}");
                        Some(deref)
                    }
                } else {
                    let base_ptr = self.emit_expr_ptr_if_place(base, access)?;
                    let gep = self.fresh_reg();
                    let _ = writeln!(
                        self.code,
                        "  {gep} = getelementptr {s_ll}, ptr {base_ptr}, i32 0, i32 {fidx}"
                    );
                    Some(gep)
                }
            }
            Expr::Index(base, idx_expr, elem_ty) => {
                let base_ptr = self.emit_expr_ptr_if_place(base, access)?;
                let idx_val = self.emit_expr(idx_expr, access);
                let u = self.usize_ty();
                let e_ll = self.llvm_ty(elem_ty);
                let dp = self.fresh_reg();
                let _ = writeln!(
                    self.code,
                    "  {dp} = getelementptr %vn2.vec, ptr {base_ptr}, i32 0, i32 0"
                );
                let data = self.fresh_reg();
                let _ = writeln!(self.code, "  {data} = load ptr, ptr {dp}");
                let gep = self.fresh_reg();
                let _ = writeln!(
                    self.code,
                    "  {gep} = getelementptr {e_ll}, ptr {data}, {u} {idx_val}"
                );
                Some(gep)
            }
            _ => None,
        }
    }

    fn emit_read_operand(&mut self, expr: &Expr, access: &VarAccess<'_>) -> ReadOperand {
        if let Some(p) = self.emit_expr_ptr_if_place(expr, access) {
            return ReadOperand::PlacePtr(p);
        }
        if matches!(expr.ty(), Type::Ref(_, _)) {
            return ReadOperand::PlacePtr(self.emit_expr(expr, access));
        }
        let val = self.emit_expr(expr, access);
        let ty = expr.ty().deref_type().clone();
        let ll = self.llvm_ty(&ty);
        let tmp = self.alloc_temp(&ll);
        let _ = writeln!(self.code, "  store {ll} {val}, ptr {tmp}");
        ReadOperand::OwnedTemp { ptr: tmp, ty }
    }

    fn emit_exprs_ordered(&mut self, exprs: &[Expr], access: &VarAccess<'_>) -> Vec<String> {
        let mut results: Vec<Option<String>> = vec![None; exprs.len()];
        for (i, expr) in exprs.iter().enumerate() {
            if !expr.lends() {
                results[i] = Some(self.emit_expr(expr, access));
            }
        }
        for (i, expr) in exprs.iter().enumerate() {
            if expr.lends() {
                results[i] = Some(self.emit_expr(expr, access));
            }
        }
        results.into_iter().map(|r| r.unwrap()).collect()
    }

    fn emit_expr(&mut self, expr: &Expr, access: &VarAccess<'_>) -> String {
        match expr {
            Expr::Boolean(b) => {
                if *b {
                    "true".to_string()
                } else {
                    "false".to_string()
                }
            }
            Expr::TasksEmpty(_, _) => tasks::new_set(self),
            Expr::Count(set) => tasks::count(self, *set),
            Expr::Integer(val, int_ty) => {
                let bits = int_bits(*int_ty, self.reg.usize_bits);
                let raw = val.to_i128().unwrap_or(0) as u128;
                let masked = if bits >= 64 {
                    raw as u64
                } else {
                    (raw as u64) & ((1u64 << bits) - 1)
                };
                format!("{masked}")
            }
            Expr::String(s) => {
                let bytes = s.as_bytes();
                let g = self.reg.intern_bytes(bytes);
                let len = bytes.len();
                let u = self.usize_ty();
                let t = self.alloc_temp("%vn2.string");
                let p0 = self.fresh_reg();
                let p1 = self.fresh_reg();
                let p2 = self.fresh_reg();
                let _ = writeln!(
                    self.code,
                    "  {p0} = getelementptr %vn2.string, ptr {t}, i32 0, i32 0"
                );
                let _ = writeln!(
                    self.code,
                    "  {p1} = getelementptr %vn2.string, ptr {t}, i32 0, i32 1"
                );
                let _ = writeln!(
                    self.code,
                    "  {p2} = getelementptr %vn2.string, ptr {t}, i32 0, i32 2"
                );
                let _ = writeln!(self.code, "  store ptr {g}, ptr {p0}");
                let _ = writeln!(self.code, "  store {u} {len}, ptr {p1}");
                let _ = writeln!(self.code, "  store {u} 0, ptr {p2}");
                let res = self.fresh_reg();
                let _ = writeln!(self.code, "  {res} = load %vn2.string, ptr {t}");
                res
            }
            Expr::EmptyMap(_) => "zeroinitializer".to_string(),
            Expr::Var(var_ref, var_ty) => match (var_ref, access) {
                (VarRef::Parameter(idx), VarAccess::DirectParams(func)) => {
                    if matches!(func.parameters[*idx].ty, Type::Ref(_, _))
                        && !matches!(var_ty, Type::Ref(_, _))
                    {
                        let ll = self.llvm_ty(var_ty);
                        let reg = self.fresh_reg();
                        let _ = writeln!(self.code, "  {reg} = load {ll}, ptr %p{idx}");
                        reg
                    } else {
                        format!("%p{idx}")
                    }
                }
                (VarRef::Local(id), VarAccess::ControlSlots(body)) => {
                    if matches!(body.vars[*id].ty, Type::Ref(_, _)) {
                        let ptr_r = self.fresh_reg();
                        let _ = writeln!(self.code, "  {ptr_r} = load ptr, ptr %slot_{id}");
                        if matches!(var_ty, Type::Ref(_, _)) {
                            ptr_r
                        } else {
                            let ll = self.llvm_ty(var_ty);
                            let val_r = self.fresh_reg();
                            let _ = writeln!(self.code, "  {val_r} = load {ll}, ptr {ptr_r}");
                            val_r
                        }
                    } else {
                        let ll = self.llvm_ty(var_ty);
                        let reg = self.fresh_reg();
                        let _ = writeln!(self.code, "  {reg} = load {ll}, ptr %slot_{id}");
                        reg
                    }
                }
                _ => unreachable!("resolved body/function variable access mismatch"),
            },
            Expr::Move(inner, _) => self.emit_expr(inner, access),
            Expr::Borrow(_, place, _) => self.emit_place_ptr(place, access),
            Expr::Field(base, sid, fidx, fty) => {
                let decl_fty = self.program.structs[*sid].fields[*fidx].ty.clone();
                let s_ll = self.llvm_ty(&Type::Struct(*sid, String::new()));
                let raw_val = if let Some(p) = self.emit_expr_ptr_if_place(base, access) {
                    let gep = self.fresh_reg();
                    let _ = writeln!(
                        self.code,
                        "  {gep} = getelementptr {s_ll}, ptr {p}, i32 0, i32 {fidx}"
                    );
                    let f_ll = self.llvm_ty(&decl_fty);
                    let r = self.fresh_reg();
                    let _ = writeln!(self.code, "  {r} = load {f_ll}, ptr {gep}");
                    r
                } else {
                    let b_val = self.emit_expr(base, access);
                    let r = self.fresh_reg();
                    let _ = writeln!(self.code, "  {r} = extractvalue {s_ll} {b_val}, {fidx}");
                    r
                };
                if matches!(decl_fty, Type::Ref(_, _)) && !matches!(fty, Type::Ref(_, _)) {
                    let v_ll = self.llvm_ty(fty);
                    let deref = self.fresh_reg();
                    let _ = writeln!(self.code, "  {deref} = load {v_ll}, ptr {raw_val}");
                    deref
                } else {
                    raw_val
                }
            }
            Expr::Index(base, idx_expr, elem_ty) => {
                let op = self.emit_read_operand(base, access);
                let idx_val = self.emit_expr(idx_expr, access);
                let bp = self.read_operand_ptr(&op).to_string();
                let u = self.usize_ty();
                let e_ll = self.llvm_ty(elem_ty);
                let dp = self.fresh_reg();
                let _ = writeln!(
                    self.code,
                    "  {dp} = getelementptr %vn2.vec, ptr {bp}, i32 0, i32 0"
                );
                let data = self.fresh_reg();
                let _ = writeln!(self.code, "  {data} = load ptr, ptr {dp}");
                let gep = self.fresh_reg();
                let _ = writeln!(
                    self.code,
                    "  {gep} = getelementptr {e_ll}, ptr {data}, {u} {idx_val}"
                );
                let r = self.fresh_reg();
                let _ = writeln!(self.code, "  {r} = load {e_ll}, ptr {gep}");
                self.finish_read_operand(op);
                r
            }
            Expr::Struct(sid, fields, _) => {
                let s_ll = self.llvm_ty(&Type::Struct(*sid, String::new()));
                if fields.is_empty() {
                    return "zeroinitializer".to_string();
                }
                let raw_vals = if self.program.structs[*sid].is_view {
                    self.emit_exprs_ordered(fields, access)
                } else {
                    fields.iter().map(|f| self.emit_expr(f, access)).collect()
                };
                let f_vals: Vec<(String, Type)> = raw_vals
                    .into_iter()
                    .zip(fields)
                    .map(|(val, f)| (val, f.ty()))
                    .collect();
                let tmp = self.alloc_temp(&s_ll);
                for (fi, (val, fty)) in f_vals.into_iter().enumerate() {
                    let f_ll = self.llvm_ty(&fty);
                    let gep = self.fresh_reg();
                    let _ = writeln!(
                        self.code,
                        "  {gep} = getelementptr {s_ll}, ptr {tmp}, i32 0, i32 {fi}"
                    );
                    let _ = writeln!(self.code, "  store {f_ll} {val}, ptr {gep}");
                }
                let r = self.fresh_reg();
                let _ = writeln!(self.code, "  {r} = load {s_ll}, ptr {tmp}");
                r
            }
            Expr::Variant(vid, cidx, fields, _) => {
                if is_unit_variant(self.program, *vid) {
                    return format!("{cidx}");
                }
                let v_ll = self.llvm_ty(&Type::Variant(*vid, String::new()));
                let mut f_vals = Vec::with_capacity(fields.len());
                for f in fields {
                    f_vals.push((self.emit_expr(f, access), f.ty()));
                }
                let tmp = self.alloc_temp(&v_ll);
                let _ = writeln!(self.code, "  store {v_ll} zeroinitializer, ptr {tmp}");
                let tp = self.fresh_reg();
                let _ = writeln!(
                    self.code,
                    "  {tp} = getelementptr {v_ll}, ptr {tmp}, i32 0, i32 0"
                );
                let _ = writeln!(self.code, "  store i32 {cidx}, ptr {tp}");
                if !f_vals.is_empty() {
                    let sub_ll = format!("%vn2.variant.{vid}.c{cidx}");
                    let pp = self.fresh_reg();
                    let _ = writeln!(
                        self.code,
                        "  {pp} = getelementptr {v_ll}, ptr {tmp}, i32 0, i32 1"
                    );
                    for (fi, (val, fty)) in f_vals.into_iter().enumerate() {
                        let f_ll = self.llvm_ty(&fty);
                        let gp = self.fresh_reg();
                        let _ = writeln!(
                            self.code,
                            "  {gp} = getelementptr {sub_ll}, ptr {pp}, i32 0, i32 {fi}"
                        );
                        let _ = writeln!(self.code, "  store {f_ll} {val}, ptr {gp}");
                    }
                }
                let r = self.fresh_reg();
                let _ = writeln!(self.code, "  {r} = load {v_ll}, ptr {tmp}");
                r
            }
            Expr::Vector(items, vec_ty) => {
                if items.is_empty() {
                    return "zeroinitializer".to_string();
                }
                self.reg.needed_libc = true;
                let Type::Vector(elem_ty) = vec_ty.deref_type() else {
                    unreachable!();
                };
                let e_ll = self.llvm_ty(elem_ty);
                let u = self.usize_ty();
                let mut vals = Vec::with_capacity(items.len());
                for item in items {
                    vals.push(self.emit_expr(item, access));
                }
                let n = vals.len();
                let sp = self.fresh_reg();
                let stride = self.fresh_reg();
                let bytes = self.fresh_reg();
                let buf = self.fresh_reg();
                let _ = writeln!(self.code, "  {sp} = getelementptr {e_ll}, ptr null, i32 1");
                let _ = writeln!(self.code, "  {stride} = ptrtoint ptr {sp} to i64");
                let _ = writeln!(self.code, "  {bytes} = mul i64 {n}, {stride}");
                let _ = writeln!(self.code, "  {buf} = call ptr @malloc(i64 {bytes})");
                for (i, v) in vals.into_iter().enumerate() {
                    let ep = self.fresh_reg();
                    let _ = writeln!(
                        self.code,
                        "  {ep} = getelementptr {e_ll}, ptr {buf}, i64 {i}"
                    );
                    let _ = writeln!(self.code, "  store {e_ll} {v}, ptr {ep}");
                }
                let tmp = self.alloc_temp("%vn2.vec");
                let p0 = self.fresh_reg();
                let p1 = self.fresh_reg();
                let p2 = self.fresh_reg();
                let _ = writeln!(
                    self.code,
                    "  {p0} = getelementptr %vn2.vec, ptr {tmp}, i32 0, i32 0"
                );
                let _ = writeln!(
                    self.code,
                    "  {p1} = getelementptr %vn2.vec, ptr {tmp}, i32 0, i32 1"
                );
                let _ = writeln!(
                    self.code,
                    "  {p2} = getelementptr %vn2.vec, ptr {tmp}, i32 0, i32 2"
                );
                let _ = writeln!(self.code, "  store ptr {buf}, ptr {p0}");
                let _ = writeln!(self.code, "  store {u} {n}, ptr {p1}");
                let _ = writeln!(self.code, "  store {u} {n}, ptr {p2}");
                let r = self.fresh_reg();
                let _ = writeln!(self.code, "  {r} = load %vn2.vec, ptr {tmp}");
                r
            }
            Expr::Len(arg) => {
                let op = self.emit_read_operand(arg, access);
                let ptr = self.read_operand_ptr(&op).to_string();
                let ll = self.llvm_ty(arg.ty().deref_type());
                let u = self.usize_ty();
                let lp = self.fresh_reg();
                let _ = writeln!(
                    self.code,
                    "  {lp} = getelementptr {ll}, ptr {ptr}, i32 0, i32 1"
                );
                let len = self.fresh_reg();
                let _ = writeln!(self.code, "  {len} = load {u}, ptr {lp}");
                self.finish_read_operand(op);
                len
            }
            Expr::Clone(arg, out_ty) => {
                let tid = self.reg.intern_type(out_ty);
                self.reg.require_clone(tid);
                let op = self.emit_read_operand(arg, access);
                let ptr = self.read_operand_ptr(&op).to_string();
                let ll = self.llvm_ty(out_ty);
                let r = self.fresh_reg();
                let _ = writeln!(
                    self.code,
                    "  {r} = call fastcc {ll} @vn2_clone_{tid}(ptr {ptr})"
                );
                self.finish_read_operand(op);
                r
            }
            Expr::Trim(arg) => {
                self.reg.needed_str = true;
                self.reg.needed_libc = true;
                let op = self.emit_read_operand(arg, access);
                let ptr = self.read_operand_ptr(&op).to_string();
                let r = self.fresh_reg();
                let _ = writeln!(
                    self.code,
                    "  {r} = call fastcc %vn2.string @vn2_str_trim(ptr {ptr})"
                );
                self.finish_read_operand(op);
                r
            }
            Expr::Not(inner) => {
                let v = self.emit_expr(inner, access);
                let reg = self.fresh_reg();
                let _ = writeln!(self.code, "  {reg} = xor i1 {v}, true");
                reg
            }
            Expr::Negate(inner, int_ty) => {
                let v = self.emit_expr(inner, access);
                let ll_ty = llvm_int_ty(*int_ty, self.reg.usize_bits);
                let reg = self.fresh_reg();
                let _ = writeln!(self.code, "  {reg} = sub {ll_ty} 0, {v}");
                reg
            }
            Expr::Arithmetic(op, left, right, int_ty) => {
                let l = self.emit_expr(left, access);
                let r = self.emit_expr(right, access);
                let ll_ty = llvm_int_ty(*int_ty, self.reg.usize_bits);
                let instr = match op {
                    Arithmetic::Add => "add",
                    Arithmetic::Subtract => "sub",
                    Arithmetic::Multiply => "mul",
                    Arithmetic::Divide => {
                        if int_ty.is_signed() {
                            "sdiv"
                        } else {
                            "udiv"
                        }
                    }
                    Arithmetic::Remainder => {
                        if int_ty.is_signed() {
                            "srem"
                        } else {
                            "urem"
                        }
                    }
                };
                let reg = self.fresh_reg();
                let _ = writeln!(self.code, "  {reg} = {instr} {ll_ty} {l}, {r}");
                reg
            }
            Expr::Compare(cmp, left, right) => {
                let op_ty = left.ty();
                let deref = op_ty.deref_type().clone();
                if deref.is_scalar() {
                    let l = self.emit_expr(left, access);
                    let r = self.emit_expr(right, access);
                    let ll_ty = self.llvm_ty(&deref);
                    let signed = matches!(deref, Type::Int(int_ty) if int_ty.is_signed());
                    let pred = match (cmp, signed) {
                        (Comparison::Equal, _) => "eq",
                        (Comparison::NotEqual, _) => "ne",
                        (Comparison::Less, true) => "slt",
                        (Comparison::Less, false) => "ult",
                        (Comparison::LessEqual, true) => "sle",
                        (Comparison::LessEqual, false) => "ule",
                        (Comparison::Greater, true) => "sgt",
                        (Comparison::Greater, false) => "ugt",
                        (Comparison::GreaterEqual, true) => "sge",
                        (Comparison::GreaterEqual, false) => "uge",
                    };
                    let reg = self.fresh_reg();
                    let _ = writeln!(self.code, "  {reg} = icmp {pred} {ll_ty} {l}, {r}");
                    reg
                } else {
                    let tid = self.reg.intern_type(&deref);
                    self.reg.require_eq(tid);
                    let lo = self.emit_read_operand(left, access);
                    let ro = self.emit_read_operand(right, access);
                    let lp = self.read_operand_ptr(&lo).to_string();
                    let rp = self.read_operand_ptr(&ro).to_string();
                    let eq = self.fresh_reg();
                    let _ = writeln!(
                        self.code,
                        "  {eq} = call fastcc i1 @vn2_eq_{tid}(ptr {lp}, ptr {rp})"
                    );
                    self.finish_read_operand(ro);
                    self.finish_read_operand(lo);
                    if *cmp == Comparison::NotEqual {
                        let ne = self.fresh_reg();
                        let _ = writeln!(self.code, "  {ne} = xor i1 {eq}, true");
                        ne
                    } else {
                        eq
                    }
                }
            }
            // [E-Bool]: short-circuit evaluation.
            Expr::And(left, right) => {
                let tmp = self.alloc_temp("i1");
                let _ = writeln!(self.code, "  store i1 false, ptr {tmp}");
                let l = self.emit_expr(left, access);
                let rhs_lbl = self.fresh_label("and_rhs");
                let end_lbl = self.fresh_label("and_end");
                let _ = writeln!(self.code, "  br i1 {l}, label %{rhs_lbl}, label %{end_lbl}");
                let _ = writeln!(self.code, "{rhs_lbl}:");
                let r = self.emit_expr(right, access);
                let _ = writeln!(self.code, "  store i1 {r}, ptr {tmp}");
                let _ = writeln!(self.code, "  br label %{end_lbl}");
                let _ = writeln!(self.code, "{end_lbl}:");
                let reg = self.fresh_reg();
                let _ = writeln!(self.code, "  {reg} = load i1, ptr {tmp}");
                reg
            }
            Expr::Or(left, right) => {
                let tmp = self.alloc_temp("i1");
                let _ = writeln!(self.code, "  store i1 true, ptr {tmp}");
                let l = self.emit_expr(left, access);
                let rhs_lbl = self.fresh_label("or_rhs");
                let end_lbl = self.fresh_label("or_end");
                let _ = writeln!(self.code, "  br i1 {l}, label %{end_lbl}, label %{rhs_lbl}");
                let _ = writeln!(self.code, "{rhs_lbl}:");
                let r = self.emit_expr(right, access);
                let _ = writeln!(self.code, "  store i1 {r}, ptr {tmp}");
                let _ = writeln!(self.code, "  br label %{end_lbl}");
                let _ = writeln!(self.code, "{end_lbl}:");
                let reg = self.fresh_reg();
                let _ = writeln!(self.code, "  {reg} = load i1, ptr {tmp}");
                reg
            }
            Expr::Call(fn_id, args, ret_ty) => {
                let callee = &self.program.functions[*fn_id];
                let mut arg_pieces = Vec::new();
                let mut temp_ops = Vec::new();
                for (arg, param) in args.iter().zip(&callee.parameters) {
                    if matches!(param.ty, Type::Ref(_, _)) {
                        let op = self.emit_read_operand(arg, access);
                        let ptr = self.read_operand_ptr(&op).to_string();
                        arg_pieces.push(format!("ptr {ptr}"));
                        temp_ops.push(op);
                    } else {
                        let v = self.emit_expr(arg, access);
                        let p_ll = self.llvm_ty(&param.ty);
                        arg_pieces.push(format!("{p_ll} {v}"));
                    }
                }
                let ret_ll = self.llvm_ty(ret_ty);
                let reg = self.fresh_reg();
                let _ = writeln!(
                    self.code,
                    "  {reg} = call fastcc {ret_ll} @vn2_fn_{fn_id}({})",
                    arg_pieces.join(", ")
                );
                for op in temp_ops.into_iter().rev() {
                    self.finish_read_operand(op);
                }
                reg
            }
            Expr::Old(_, _) => "zeroinitializer".to_string(),
        }
    }

    fn emit_selector(&mut self, selector: &Selector, plan: &HistoryPlan) -> String {
        match selector {
            Selector::Top => "true".to_string(),
            Selector::Atom(site, alt_pos) => {
                let bit = plan.bit[*site][*alt_pos].expect("mentioned atom has a bit");
                let reg = self.fresh_reg();
                let _ = writeln!(self.code, "  {reg} = load i1, ptr %bit_{bit}");
                reg
            }
            Selector::Not(inner) => {
                let v = self.emit_selector(inner, plan);
                let reg = self.fresh_reg();
                let _ = writeln!(self.code, "  {reg} = xor i1 {v}, true");
                reg
            }
            Selector::And(l, r) => {
                let lv = self.emit_selector(l, plan);
                let rv = self.emit_selector(r, plan);
                let reg = self.fresh_reg();
                let _ = writeln!(self.code, "  {reg} = and i1 {lv}, {rv}");
                reg
            }
            Selector::Or(l, r) => {
                let lv = self.emit_selector(l, plan);
                let rv = self.emit_selector(r, plan);
                let reg = self.fresh_reg();
                let _ = writeln!(self.code, "  {reg} = or i1 {lv}, {rv}");
                reg
            }
        }
    }

    /// Emits `[R4]` destruction or `[R5]` fault release for variables belonging
    /// to `target_body`, checked against static `avail_at[lookup_body][lookup_pc]`.
    #[allow(clippy::too_many_arguments)]
    fn emit_scope_cleanup(
        &mut self,
        body: &ControlBody,
        plan: &HistoryPlan,
        target_body: BodyId,
        lookup_body: BodyId,
        lookup_pc: usize,
        exclude: &[VarId],
        is_fault: bool,
    ) {
        let Some(snap) = plan.avail_at[lookup_body].get(lookup_pc) else {
            return;
        };
        for var_id in (0..body.vars.len()).rev() {
            let var = &body.vars[var_id];
            if var.body != target_body || exclude.contains(&var_id) || plan.borrowed[var_id] {
                continue;
            }
            let applicable = if is_fault {
                needs_runtime_cleanup(self.program, &var.ty)
            } else {
                needs_drop(self.program, &var.ty)
            };
            if !applicable {
                continue;
            }
            let Some(sel) = simplify_opt_selector(snap[var_id].as_ref()) else {
                continue;
            };
            let var_ty = var.ty.clone();
            if matches!(sel, Selector::Top) {
                if is_fault {
                    self.emit_release_ptr(&format!("%slot_{var_id}"), &var_ty);
                } else {
                    self.emit_drop_ptr(&format!("%slot_{var_id}"), &var_ty);
                }
            } else {
                let cond = self.emit_selector(&sel, plan);
                let do_lbl = self.fresh_label("cln_do");
                let after_lbl = self.fresh_label("cln_after");
                let _ = writeln!(
                    self.code,
                    "  br i1 {cond}, label %{do_lbl}, label %{after_lbl}"
                );
                let _ = writeln!(self.code, "{do_lbl}:");
                if is_fault {
                    self.emit_release_ptr(&format!("%slot_{var_id}"), &var_ty);
                } else {
                    self.emit_drop_ptr(&format!("%slot_{var_id}"), &var_ty);
                }
                let _ = writeln!(self.code, "  br label %{after_lbl}");
                let _ = writeln!(self.code, "{after_lbl}:");
            }
        }
    }
}

fn classify_body_roles(body: &ControlBody) -> Vec<BodyRole> {
    let mut roles = vec![BodyRole::Root; body.bodies.len()];
    for (pb_id, pb) in body.bodies.iter().enumerate() {
        for (s_idx, stmt) in pb.statements.iter().enumerate() {
            match &stmt.command {
                Command::Loop {
                    site,
                    body: inner,
                    arms,
                    ..
                } => {
                    roles[*inner] = BodyRole::Loop {
                        parent_body: pb_id,
                        stmt_idx: s_idx,
                        site: *site,
                        arms: arms.clone(),
                    };
                }
                Command::Boundary {
                    site,
                    body: b1,
                    contingency_vars,
                    message_var,
                    contingency: b2,
                    ..
                } => {
                    roles[*b1] = BodyRole::LexicalB1 {
                        parent_body: pb_id,
                        stmt_idx: s_idx,
                        site: *site,
                        b2: *b2,
                        contingency_vars: contingency_vars.clone(),
                        message_var: *message_var,
                    };
                    roles[*b2] = BodyRole::LexicalB2 {
                        parent_body: pb_id,
                        stmt_idx: s_idx,
                    };
                }
                _ => {}
            }
        }
    }
    roles
}

fn ancestor_chain_to_root(
    roles: &[BodyRole],
    start: BodyId,
    start_pc: usize,
) -> Vec<(BodyId, usize)> {
    let mut chain = vec![(start, start_pc)];
    let mut cur = start;
    while cur != 0 {
        match &roles[cur] {
            BodyRole::Root => break,
            BodyRole::Loop {
                parent_body,
                stmt_idx,
                ..
            }
            | BodyRole::LexicalB1 {
                parent_body,
                stmt_idx,
                ..
            }
            | BodyRole::LexicalB2 {
                parent_body,
                stmt_idx,
                ..
            } => {
                chain.push((*parent_body, *stmt_idx));
                cur = *parent_body;
            }
        }
    }
    chain
}

fn compute_unwind_target(
    body: &ControlBody,
    roles: &[BodyRole],
    fail_body: BodyId,
    fail_pc: usize,
) -> UnwindTarget {
    let mut frames_to_unwind = Vec::new();
    let mut cur = fail_body;
    let mut cur_pc = fail_pc;
    loop {
        frames_to_unwind.push((cur, cur_pc));
        match &roles[cur] {
            BodyRole::LexicalB1 {
                b2, message_var, ..
            } => {
                return UnwindTarget::LexicalCatch {
                    b2: *b2,
                    message_var: *message_var,
                    frames_to_unwind,
                };
            }
            BodyRole::Root => break,
            BodyRole::Loop {
                parent_body,
                stmt_idx,
                ..
            }
            | BodyRole::LexicalB2 {
                parent_body,
                stmt_idx,
                ..
            } => {
                cur = *parent_body;
                cur_pc = *stmt_idx;
            }
        }
    }
    let _ = body;
    // If Root was reached without catching:
    UnwindTarget::RootFault { frames_to_unwind }
}

fn adjust_unwind_for_named_b1(unit: UnitKind, target: UnwindTarget) -> UnwindTarget {
    match (unit, target) {
        (UnitKind::NamedBoundaryB1 { .. }, UnwindTarget::RootFault { frames_to_unwind }) => {
            UnwindTarget::NamedBoundaryB1Fault { frames_to_unwind }
        }
        (_, other) => other,
    }
}

/// The message that a fault carries on from the contingency it leaves.
#[derive(Clone, Copy, PartialEq)]
enum Carried {
    /// A new fault: its message is its own.
    Nothing,
    /// `escalate` in the contingency of a lexical boundary: the message that
    /// the contingency was entered with.
    Lexical(BodyId),
    /// `escalate` in the contingency of a named boundary.
    Unit,
}

/// Whether `body` is `home` or lies inside it.
fn is_within(roles: &[BodyRole], mut body: BodyId, home: BodyId) -> bool {
    loop {
        if body == home {
            return true;
        }
        body = match &roles[body] {
            BodyRole::Root => return false,
            BodyRole::Loop { parent_body, .. }
            | BodyRole::LexicalB1 { parent_body, .. }
            | BodyRole::LexicalB2 { parent_body, .. } => *parent_body,
        };
    }
}

/// Whether some statement consumes the name `var` of the body `home`: its
/// formula is other than `⊤` at some statement that has the name in scope.
fn is_consumed(plan: &HistoryPlan, roles: &[BodyRole], home: BodyId, var: VarId) -> bool {
    plan.avail_at.iter().enumerate().any(|(inner, snaps)| {
        is_within(roles, inner, home)
            && snaps
                .iter()
                .any(|snap| !matches!(snap[var], Some(Selector::Top)))
    })
}

/// Emits `[R2]`/`[R1]`/`[R3]`/`[R4]`/`[R5]` LLVM IR for any `ControlBody`
/// (defined control, named boundary B1, or named boundary B2).
#[allow(clippy::too_many_arguments)]
fn emit_body_unit<'a>(
    out: &mut String,
    program: &'a Program,
    reg: &mut RuntimeRegistry<'a>,
    term_tys: &[Option<Type>],
    unit: UnitKind,
    fn_name: &str,
    params_sig: &[(String, Type)],
    body: &ControlBody,
    unit_out_fault: Option<String>,
    unit_out_term: Option<(String, Type)>,
    pre_bound_var_count: usize,
) -> Result<(), String> {
    let mut plan = build_plan(program, body, pre_bound_var_count);
    let roles = classify_body_roles(body);
    // The message of a fault has one owner. A contingency holds it for
    // `escalate` in a slot of its own (`%lex_fault_<body>`, `%unit_fault`);
    // the name that the contingency gives it reads that slot where no
    // statement consumes the name, and owns a copy otherwise.
    for role in &roles {
        if let BodyRole::LexicalB1 {
            b2,
            message_var: Some(message),
            ..
        } = role
        {
            plan.borrowed[*message] = !is_consumed(&plan, &roles, *b2, *message);
        }
    }
    let unit_message: Option<VarId> = match unit {
        UnitKind::NamedBoundaryB2 => Some(params_sig.len() - 1),
        UnitKind::Control { .. } | UnitKind::NamedBoundaryB1 { .. } => None,
    };
    if let Some(message) = unit_message {
        plan.borrowed[message] = !is_consumed(&plan, &roles, 0, message);
    }
    let plan = plan;
    let mut emitter = IrEmitter::new(program, reg);

    let is_control = matches!(unit, UnitKind::Control { .. });
    let mut sig_parts: Vec<String> = params_sig
        .iter()
        .map(|(n, ty)| {
            if is_control && matches!(ty, Type::Ref(BorrowMode::Exclusive, _)) {
                format!("ptr noalias {n}")
            } else {
                format!("{} {n}", emitter.llvm_ty(ty))
            }
        })
        .collect();
    if let UnitKind::Control { id, .. } = unit {
        for (alt_idx, alt) in program.controls[id].contract.iter().enumerate() {
            for (field_idx, _) in alt.fields.iter().enumerate() {
                sig_parts.push(format!("ptr %out_{alt_idx}_{field_idx}"));
            }
        }
    }
    if let Some(ref fptr) = unit_out_fault {
        sig_parts.push(format!("ptr {fptr}"));
    }
    if let Some((ref tptr, _)) = unit_out_term {
        sig_parts.push(format!("ptr {tptr}"));
    }

    let _ = writeln!(
        out,
        "define internal fastcc i32 @{fn_name}({}) nounwind {{",
        sig_parts.join(", ")
    );

    // [R1]: Allocate flat native slots for all variables of `body.vars`.
    for (var_id, var) in body.vars.iter().enumerate() {
        let ll_ty = emitter.llvm_ty(&var.ty);
        emitter
            .allocas
            .push(format!("  %slot_{var_id} = alloca {ll_ty}"));
    }
    // [R3]: Allocate `i1` history bits ONLY for atoms mentioned in reachable selectors / cleanup.
    for bit_id in 0..plan.bits {
        emitter.allocas.push(format!("  %bit_{bit_id} = alloca i1"));
    }
    // Allocate lexical boundary fault message buffers and loop recover param snapshots.
    for (bid, role) in roles.iter().enumerate() {
        if matches!(role, BodyRole::LexicalB2 { .. }) {
            emitter
                .allocas
                .push(format!("  %lex_fault_{bid} = alloca %vn2.string"));
        }
    }

    // Store entry parameters and zero remaining slots.
    for (idx, (pname, pty)) in params_sig.iter().enumerate() {
        let ll = emitter.llvm_ty(pty);
        let _ = writeln!(emitter.code, "  store {ll} {pname}, ptr %slot_{idx}");
    }
    for var_id in params_sig.len()..body.vars.len() {
        let ll = emitter.llvm_ty(&body.vars[var_id].ty);
        let zero = if body.vars[var_id].ty == Type::Bool {
            "false"
        } else {
            "zeroinitializer"
        };
        let _ = writeln!(emitter.code, "  store {ll} {zero}, ptr %slot_{var_id}");
    }
    for bit_id in 0..plan.bits {
        let _ = writeln!(emitter.code, "  store i1 false, ptr %bit_{bit_id}");
    }
    if let Some(message) = unit_message {
        emitter
            .allocas
            .push("  %unit_fault = alloca %vn2.string".to_string());
        let _ = writeln!(emitter.code, "  store %vn2.string %m_in, ptr %unit_fault");
        if !plan.borrowed[message] {
            let copy = emitter.emit_string_copy("%unit_fault");
            let _ = writeln!(
                emitter.code,
                "  store %vn2.string {copy}, ptr %slot_{message}"
            );
        }
    }
    let _ = writeln!(emitter.code, "  br label %b0_entry");

    // [E-Unwind], [R5]: a fault at the statement `fail_pc` of `fail_body`
    // ends every scope up to the boundary that takes it, each by the
    // formulas of that statement.
    let emit_unwind = |em: &mut IrEmitter<'_, '_>,
                       fail_body: BodyId,
                       fail_pc: usize,
                       msg_reg: &str,
                       carried: Carried| {
        let raw_target = compute_unwind_target(body, &roles, fail_body, fail_pc);
        let target = adjust_unwind_for_named_b1(unit, raw_target);
        let end = |em: &mut IrEmitter<'_, '_>, frames: &[(BodyId, usize)], kept: &[VarId]| {
            for &(fb, _) in frames {
                let excl: &[VarId] = if fb == 0 { kept } else { &[] };
                em.emit_scope_cleanup(body, &plan, fb, fail_body, fail_pc, excl, true);
                // The message of a contingency that the fault leaves ends
                // with its scope, unless the fault carries it on.
                if matches!(roles[fb], BodyRole::LexicalB2 { .. })
                    && carried != Carried::Lexical(fb)
                {
                    em.emit_drop_ptr(&format!("%lex_fault_{fb}"), &Type::String);
                }
            }
        };
        match target {
            UnwindTarget::LexicalCatch {
                b2,
                message_var,
                frames_to_unwind,
                ..
            } => {
                end(em, &frames_to_unwind, &[]);
                // [F5]: the contingency reads the names around the
                // boundary as this statement left them.
                if let Some(bit_id) = plan.fault_bit.get(&(fail_body, fail_pc)) {
                    let _ = writeln!(em.code, "  store i1 true, ptr %bit_{bit_id}");
                }
                let _ = writeln!(
                    em.code,
                    "  store %vn2.string {msg_reg}, ptr %lex_fault_{b2}"
                );
                if let Some(mvar) = message_var {
                    if plan.borrowed[mvar] {
                        let _ =
                            writeln!(em.code, "  store %vn2.string {msg_reg}, ptr %slot_{mvar}");
                    } else {
                        let copy = em.emit_string_copy(&format!("%lex_fault_{b2}"));
                        let _ = writeln!(em.code, "  store %vn2.string {copy}, ptr %slot_{mvar}");
                    }
                }
                let _ = writeln!(em.code, "  br label %b{b2}_entry");
            }
            UnwindTarget::NamedBoundaryB1Fault { frames_to_unwind } => {
                let UnitKind::NamedBoundaryB1 { id: bid } = unit else {
                    unreachable!();
                };
                let bdef = &program.boundaries[bid];
                let retains = &bdef.retains;
                end(em, &frames_to_unwind, retains);
                let mut call_args = Vec::new();
                for &ridx in retains {
                    let r_ll = em.llvm_ty(&bdef.parameters[ridx].ty);
                    let rv = em.fresh_reg();
                    let _ = writeln!(em.code, "  {rv} = load {r_ll}, ptr %slot_{ridx}");
                    call_args.push(format!("{r_ll} {rv}"));
                }
                call_args.push(format!("%vn2.string {msg_reg}"));
                if bdef.may_fault {
                    call_args.push(format!("ptr {}", unit_out_fault.as_deref().unwrap()));
                }
                let ret_r = em.fresh_reg();
                let _ = writeln!(
                    em.code,
                    "  {ret_r} = call fastcc i32 @vn2_boundary_b2_{bid}({})",
                    call_args.join(", ")
                );
                let _ = writeln!(em.code, "  ret i32 {ret_r}");
            }
            UnwindTarget::RootFault { frames_to_unwind } => {
                end(em, &frames_to_unwind, &[]);
                if unit_message.is_some() && carried != Carried::Unit {
                    em.emit_drop_ptr("%unit_fault", &Type::String);
                }
                if let Some(ref fptr) = unit_out_fault {
                    let _ = writeln!(em.code, "  store %vn2.string {msg_reg}, ptr {fptr}");
                    let _ = writeln!(em.code, "  ret i32 -1");
                } else {
                    let _ = writeln!(em.code, "  unreachable");
                }
            }
        }
    };
    let emit_fault = |em: &mut IrEmitter<'_, '_>, fail_body: BodyId, fail_pc: usize, msg: &str| {
        emit_unwind(em, fail_body, fail_pc, msg, Carried::Nothing);
    };

    // [E-Scope], [R4]: a terminator at the statement `pc` of `from` ends the
    // scopes from its own outward, through that of `through` or all of them,
    // each by the formulas of that statement. The names `kept` of the last
    // one stay.
    let end_scopes = |em: &mut IrEmitter<'_, '_>,
                      from: BodyId,
                      pc: usize,
                      through: Option<BodyId>,
                      kept: &[VarId]| {
        for (fb, _) in ancestor_chain_to_root(&roles, from, pc) {
            let last = through == Some(fb);
            let excl: &[VarId] = if last { kept } else { &[] };
            em.emit_scope_cleanup(body, &plan, fb, from, pc, excl, false);
            match &roles[fb] {
                // What a boundary has in its care ends with the scope of
                // its work ([E-Boundary]).
                BodyRole::LexicalB1 {
                    contingency_vars, ..
                } => {
                    for &cv in contingency_vars {
                        let cty = body.vars[cv].ty.clone();
                        em.emit_drop_ptr(&format!("%slot_{cv}"), &cty);
                    }
                }
                // The message of the fault ends with the contingency.
                BodyRole::LexicalB2 { .. } => {
                    em.emit_drop_ptr(&format!("%lex_fault_{fb}"), &Type::String);
                }
                BodyRole::Root | BodyRole::Loop { .. } => {}
            }
            if last {
                break;
            }
        }
    };

    // Emit each body `0..body.bodies.len()`.
    for (b_id, b) in body.bodies.iter().enumerate() {
        let _ = writeln!(emitter.code, "b{b_id}_entry:");
        if b_id > 0 {
            // [R3]: Entering a loop / boundary body clears its own history bits.
            for &bit_id in &plan.own[b_id] {
                let _ = writeln!(emitter.code, "  store i1 false, ptr %bit_{bit_id}");
            }
        }
        if b.statements.is_empty() {
            let _ = writeln!(emitter.code, "  br label %b{b_id}_end");
        } else {
            let _ = writeln!(emitter.code, "  br label %b{b_id}_s0");
        }

        for (s_idx, stmt) in b.statements.iter().enumerate() {
            let next_lbl = plan.stmt_next[b_id][s_idx].clone();
            let skip_lbl = plan.skip_target[b_id][s_idx].clone();
            let eff_sel = &plan.stmt_sel[b_id][s_idx];

            let _ = writeln!(emitter.code, "b{b_id}_s{s_idx}:");

            // [R2]: `Command::Oblige` has no runtime behavior, and `site.alt ▷ ⊥`
            // is dispatched directly to `unreachable` in the decision switch.
            if matches!(stmt.command, Command::Oblige(_))
                || (is_direct_impossible_arm(stmt)
                    && matches!(eff_sel, Selector::Atom(s, a) if plan.bit[*s][*a].is_none()))
            {
                let _ = writeln!(emitter.code, "  br label %{next_lbl}");
                continue;
            }

            if !matches!(eff_sel, Selector::Top) {
                let sel_reg = emitter.emit_selector(eff_sel, &plan);
                let run_lbl = format!("b{b_id}_run{s_idx}");
                let _ = writeln!(
                    emitter.code,
                    "  br i1 {sel_reg}, label %{run_lbl}, label %{skip_lbl}"
                );
                let _ = writeln!(emitter.code, "{run_lbl}:");
            }

            match &stmt.command {
                Command::Spawn {
                    control,
                    arguments,
                    set,
                } => {
                    tasks::spawn(&mut emitter, body, *set, *control, arguments);
                    let _ = writeln!(emitter.code, "  br label %{next_lbl}");
                }
                Command::Cancel { .. } => {
                    unreachable!("task set cancellation rejected before emission")
                }
                Command::Bind { var, value } => {
                    let val = emitter.emit_expr(value, &VarAccess::ControlSlots(body));
                    let ll_ty = emitter.llvm_ty(&body.vars[*var].ty);
                    let _ = writeln!(emitter.code, "  store {ll_ty} {val}, ptr %slot_{var}");
                    let _ = writeln!(emitter.code, "  br label %{next_lbl}");
                }
                Command::Unpack { vars, value, .. } => {
                    let s_val = emitter.emit_expr(value, &VarAccess::ControlSlots(body));
                    let s_ll = emitter.llvm_ty(&value.ty());
                    for (fi, &var_id) in vars.iter().enumerate() {
                        let f_ll = emitter.llvm_ty(&body.vars[var_id].ty);
                        let fv = emitter.fresh_reg();
                        let _ =
                            writeln!(emitter.code, "  {fv} = extractvalue {s_ll} {s_val}, {fi}");
                        let _ = writeln!(emitter.code, "  store {f_ll} {fv}, ptr %slot_{var_id}");
                    }
                    let _ = writeln!(emitter.code, "  br label %{next_lbl}");
                }
                Command::Assign { var, value } => {
                    let val = emitter.emit_expr(value, &VarAccess::ControlSlots(body));
                    let vty = body.vars[*var].ty.clone();
                    if let Type::Ref(_, inner) = &vty {
                        let dst_ptr = emitter.fresh_reg();
                        let _ = writeln!(emitter.code, "  {dst_ptr} = load ptr, ptr %slot_{var}");
                        emitter.emit_drop_ptr(&dst_ptr, inner);
                        let ill = emitter.llvm_ty(inner);
                        let _ = writeln!(emitter.code, "  store {ill} {val}, ptr {dst_ptr}");
                    } else {
                        if needs_drop(program, &vty)
                            && let Some(sel) =
                                simplify_opt_selector(plan.avail_at[b_id][s_idx][*var].as_ref())
                        {
                            if matches!(sel, Selector::Top) {
                                emitter.emit_drop_ptr(&format!("%slot_{var}"), &vty);
                            } else {
                                let cond = emitter.emit_selector(&sel, &plan);
                                let d_lbl = emitter.fresh_label("asgn_d");
                                let a_lbl = emitter.fresh_label("asgn_a");
                                let _ = writeln!(
                                    emitter.code,
                                    "  br i1 {cond}, label %{d_lbl}, label %{a_lbl}"
                                );
                                let _ = writeln!(emitter.code, "{d_lbl}:");
                                emitter.emit_drop_ptr(&format!("%slot_{var}"), &vty);
                                let _ = writeln!(emitter.code, "  br label %{a_lbl}");
                                let _ = writeln!(emitter.code, "{a_lbl}:");
                            }
                        }
                        let ll = emitter.llvm_ty(&vty);
                        let _ = writeln!(emitter.code, "  store {ll} {val}, ptr %slot_{var}");
                    }
                    let _ = writeln!(emitter.code, "  br label %{next_lbl}");
                }
                Command::AssignPlace { target, value } => {
                    let val = emitter.emit_expr(value, &VarAccess::ControlSlots(body));
                    let dst_ptr = emitter.emit_place_ptr(target, &VarAccess::ControlSlots(body));
                    emitter.emit_drop_ptr(&dst_ptr, &target.ty);
                    let t_ll = emitter.llvm_ty(&target.ty);
                    let _ = writeln!(emitter.code, "  store {t_ll} {val}, ptr {dst_ptr}");
                    let _ = writeln!(emitter.code, "  br label %{next_lbl}");
                }
                Command::Oblige(_) => unreachable!("handled above"),
                Command::Test { site, condition } => {
                    let cond = emitter.emit_expr(condition, &VarAccess::ControlSlots(body));
                    if let Some(b_true) = plan.bit[*site][0] {
                        let _ = writeln!(emitter.code, "  store i1 {cond}, ptr %bit_{b_true}");
                    }
                    if let Some(b_false) = plan.bit[*site][1] {
                        let not_reg = emitter.fresh_reg();
                        let _ = writeln!(emitter.code, "  {not_reg} = xor i1 {cond}, true");
                        let _ = writeln!(emitter.code, "  store i1 {not_reg}, ptr %bit_{b_false}");
                    }
                    if let Some(targets) = &plan.branch_targets[b_id][s_idx] {
                        let _ = writeln!(
                            emitter.code,
                            "  br i1 {cond}, label %{}, label %{}",
                            targets[0], targets[1]
                        );
                    } else {
                        let _ = writeln!(emitter.code, "  br label %{next_lbl}");
                    }
                }
                Command::Capture {
                    var,
                    outcome_id,
                    operation,
                    arguments,
                } => {
                    emit_operation_call(
                        &mut emitter,
                        program,
                        term_tys,
                        body,
                        b_id,
                        s_idx,
                        operation,
                        arguments,
                        |em, tag_reg, out_slots, temp_drops| {
                            for td in temp_drops {
                                em.finish_read_operand(td);
                            }
                            let oid = *outcome_id;
                            if is_unit_outcome(program, oid) {
                                let _ = writeln!(em.code, "  store i32 {tag_reg}, ptr %slot_{var}");
                            } else {
                                let oc_ll = format!("%vn2.outcome.{oid}");
                                let _ = writeln!(
                                    em.code,
                                    "  store {oc_ll} zeroinitializer, ptr %slot_{var}"
                                );
                                let tp = em.fresh_reg();
                                let _ = writeln!(
                                    em.code,
                                    "  {tp} = getelementptr {oc_ll}, ptr %slot_{var}, i32 0, i32 0"
                                );
                                let _ = writeln!(em.code, "  store i32 {tag_reg}, ptr {tp}");
                                let alts = &program.outcomes[oid].alternatives;
                                let mut cases = String::new();
                                let done_lbl = em.fresh_label("cap_done");
                                for (k, a) in alts.iter().enumerate() {
                                    if a.fields.is_empty() {
                                        let _ = write!(cases, " i32 {k}, label %{done_lbl}");
                                    } else {
                                        let _ = write!(cases, " i32 {k}, label %{done_lbl}_a{k}");
                                    }
                                }
                                let _ = writeln!(
                                    em.code,
                                    "  switch i32 {tag_reg}, label %{done_lbl} [ {cases} ]"
                                );
                                for (k, a) in alts.iter().enumerate() {
                                    if a.fields.is_empty() {
                                        continue;
                                    }
                                    let _ = writeln!(em.code, "{done_lbl}_a{k}:");
                                    let sub_ll = format!("%vn2.outcome.{oid}.a{k}");
                                    let pp = em.fresh_reg();
                                    let _ = writeln!(
                                        em.code,
                                        "  {pp} = getelementptr {oc_ll}, ptr %slot_{var}, i32 0, i32 1"
                                    );
                                    for (fi, f) in a.fields.iter().enumerate() {
                                        let f_ll = em.llvm_ty(&f.ty);
                                        let gp = em.fresh_reg();
                                        let _ = writeln!(
                                            em.code,
                                            "  {gp} = getelementptr {sub_ll}, ptr {pp}, i32 0, i32 {fi}"
                                        );
                                        let loaded = em.fresh_reg();
                                        let src_p = &out_slots[k][fi];
                                        let _ = writeln!(
                                            em.code,
                                            "  {loaded} = load {f_ll}, ptr {src_p}"
                                        );
                                        let _ =
                                            writeln!(em.code, "  store {f_ll} {loaded}, ptr {gp}");
                                    }
                                    let _ = writeln!(em.code, "  br label %{done_lbl}");
                                }
                                let _ = writeln!(em.code, "{done_lbl}:");
                            }
                            let _ = writeln!(em.code, "  br label %{next_lbl}");
                        },
                        &emit_fault,
                        unit_out_term.as_ref().map(|(t, _)| t.as_str()),
                    )?;
                }
                Command::Decide {
                    site,
                    operation: _,
                    op_kind,
                    arguments,
                    arms,
                } => {
                    emit_operation_call(
                        &mut emitter,
                        program,
                        term_tys,
                        body,
                        b_id,
                        s_idx,
                        op_kind,
                        arguments,
                        |em, tag_reg, out_slots, temp_drops| {
                            for td in temp_drops {
                                em.finish_read_operand(td);
                            }
                            let unreach_lbl = em.fresh_label(&format!("b{b_id}_s{s_idx}_unreach"));
                            let mut arm_labels = Vec::new();
                            let mut switch_cases = Vec::new();
                            let contract = op_kind.contract(program);
                            let is_extern = matches!(op_kind, Operation::Control(cid) if program.controls[*cid].body.is_none());

                            for (pos, arm) in arms.iter().enumerate() {
                                let directly_impossible =
                                    b.statements[(s_idx + 1)..].iter().any(|later| {
                                        matches!(later.command, Command::Impossible)
                                            && later.selector == Selector::Atom(*site, pos)
                                    });
                                if directly_impossible && plan.bit[*site][pos].is_none() {
                                    switch_cases.push(format!(
                                        "i32 {}, label %{unreach_lbl}",
                                        arm.alternative
                                    ));
                                    arm_labels.push(None);
                                } else {
                                    let arm_lbl =
                                        em.fresh_label(&format!("b{b_id}_s{s_idx}_arm{pos}"));
                                    switch_cases
                                        .push(format!("i32 {}, label %{arm_lbl}", arm.alternative));
                                    arm_labels.push(Some(arm_lbl));
                                }
                            }

                            let _ = writeln!(
                                em.code,
                                "  switch i32 {tag_reg}, label %{unreach_lbl} [ {} ]",
                                switch_cases.join(" ")
                            );
                            let _ = writeln!(em.code, "{unreach_lbl}:");
                            let _ = writeln!(em.code, "  unreachable");

                            for (pos, arm) in arms.iter().enumerate() {
                                let Some(arm_lbl) = &arm_labels[pos] else {
                                    continue;
                                };
                                let _ = writeln!(em.code, "{arm_lbl}:");
                                if let Some(bit_id) = plan.bit[*site][pos] {
                                    let _ = writeln!(em.code, "  store i1 true, ptr %bit_{bit_id}");
                                }
                                let contract_alt = &contract[arm.alternative];
                                for (field_idx, &var_id) in arm.vars.iter().enumerate() {
                                    let field_ty = &contract_alt.fields[field_idx].ty;
                                    let ptr = &out_slots[arm.alternative][field_idx];
                                    if is_extern && *field_ty == Type::Bool {
                                        let raw = em.fresh_reg();
                                        let _ = writeln!(em.code, "  {raw} = load i8, ptr {ptr}");
                                        let b_reg = em.fresh_reg();
                                        let _ =
                                            writeln!(em.code, "  {b_reg} = icmp ne i8 {raw}, 0");
                                        let _ = writeln!(
                                            em.code,
                                            "  store i1 {b_reg}, ptr %slot_{var_id}"
                                        );
                                    } else {
                                        let ll_ty = em.llvm_ty(field_ty);
                                        let val_reg = em.fresh_reg();
                                        let _ = writeln!(
                                            em.code,
                                            "  {val_reg} = load {ll_ty}, ptr {ptr}"
                                        );
                                        let _ = writeln!(
                                            em.code,
                                            "  store {ll_ty} {val_reg}, ptr %slot_{var_id}"
                                        );
                                    }
                                }
                                let arm_next = plan.branch_targets[b_id][s_idx]
                                    .as_ref()
                                    .map(|ts| ts[pos].as_str())
                                    .unwrap_or(next_lbl.as_str());
                                let _ = writeln!(em.code, "  br label %{arm_next}");
                            }
                        },
                        &emit_fault,
                        unit_out_term.as_ref().map(|(t, _)| t.as_str()),
                    )?;
                }
                Command::Loop {
                    body: inner,
                    initial,
                    ..
                } => {
                    let head = body.bodies[*inner].head.as_ref().expect("a loop head");
                    let init_vals =
                        emitter.emit_exprs_ordered(initial, &VarAccess::ControlSlots(body));
                    for (&param_var, val) in head.parameters.iter().zip(init_vals) {
                        let pty = body.vars[param_var].ty.clone();
                        let ll_ty = emitter.llvm_ty(&pty);
                        let _ =
                            writeln!(emitter.code, "  store {ll_ty} {val}, ptr %slot_{param_var}");
                    }
                    let _ = writeln!(emitter.code, "  br label %b{inner}_entry");
                }
                Command::Boundary {
                    body: inner_b1,
                    captures,
                    contingency_vars,
                    ..
                } => {
                    for (&cap_var, &c_var) in captures.iter().zip(contingency_vars) {
                        let ll = emitter.llvm_ty(&body.vars[cap_var].ty);
                        let cv = emitter.fresh_reg();
                        let _ = writeln!(emitter.code, "  {cv} = load {ll}, ptr %slot_{cap_var}");
                        let _ = writeln!(emitter.code, "  store {ll} {cv}, ptr %slot_{c_var}");
                    }
                    let _ = writeln!(emitter.code, "  br label %b{inner_b1}_entry");
                }
                Command::Supervise {
                    boundary: bid,
                    arguments,
                } => {
                    let bdef = &program.boundaries[*bid];
                    let mut call_args = Vec::new();
                    let mut temp_drops = Vec::new();
                    for (arg, param) in arguments.iter().zip(&bdef.parameters) {
                        if matches!(param.ty, Type::Ref(_, _)) {
                            let op = emitter.emit_read_operand(arg, &VarAccess::ControlSlots(body));
                            let ptr = emitter.read_operand_ptr(&op).to_string();
                            call_args.push(format!("ptr {ptr}"));
                            temp_drops.push(op);
                        } else {
                            let v = emitter.emit_expr(arg, &VarAccess::ControlSlots(body));
                            let ll = emitter.llvm_ty(&param.ty);
                            call_args.push(format!("{ll} {v}"));
                        }
                    }
                    let fslot = if bdef.may_fault {
                        let p = emitter.alloc_temp("%vn2.string");
                        call_args.push(format!("ptr {p}"));
                        Some(p)
                    } else {
                        None
                    };
                    let tag_reg = emitter.fresh_reg();
                    let _ = writeln!(
                        emitter.code,
                        "  {tag_reg} = call fastcc i32 @vn2_boundary_{bid}({})",
                        call_args.join(", ")
                    );
                    for td in temp_drops.into_iter().rev() {
                        emitter.finish_read_operand(td);
                    }
                    if let Some(fp) = fslot {
                        let is_f = emitter.fresh_reg();
                        let ok_lbl = emitter.fresh_label("sup_ok");
                        let f_lbl = emitter.fresh_label("sup_fault");
                        let _ = writeln!(emitter.code, "  {is_f} = icmp eq i32 {tag_reg}, -1");
                        let _ = writeln!(
                            emitter.code,
                            "  br i1 {is_f}, label %{f_lbl}, label %{ok_lbl}"
                        );
                        let _ = writeln!(emitter.code, "{f_lbl}:");
                        let fmsg = emitter.fresh_reg();
                        let _ = writeln!(emitter.code, "  {fmsg} = load %vn2.string, ptr {fp}");
                        emit_fault(&mut emitter, b_id, s_idx, &fmsg);
                        let _ = writeln!(emitter.code, "{ok_lbl}:");
                    }
                    let _ = writeln!(emitter.code, "  br label %{next_lbl}");
                }
                Command::Again {
                    body: target,
                    arguments,
                } => {
                    let head = body.bodies[*target].head.as_ref().expect("a loop head");
                    let arg_vals =
                        emitter.emit_exprs_ordered(arguments, &VarAccess::ControlSlots(body));
                    end_scopes(&mut emitter, b_id, s_idx, Some(*target), &[]);
                    for (&param_var, val) in head.parameters.iter().zip(arg_vals) {
                        let ll_ty = emitter.llvm_ty(&body.vars[param_var].ty);
                        let _ =
                            writeln!(emitter.code, "  store {ll_ty} {val}, ptr %slot_{param_var}");
                    }
                    let _ = writeln!(emitter.code, "  br label %b{target}_entry");
                }
                Command::Leave {
                    alternative,
                    payload,
                } => {
                    let pay_vals =
                        emitter.emit_exprs_ordered(payload, &VarAccess::ControlSlots(body));
                    // The scopes end from this one through that of the loop.
                    let loop_body = ancestor_chain_to_root(&roles, b_id, s_idx)
                        .into_iter()
                        .map(|(fb, _)| fb)
                        .find(|fb| matches!(roles[*fb], BodyRole::Loop { .. }))
                        .expect("loop parent for leave");
                    end_scopes(&mut emitter, b_id, s_idx, Some(loop_body), &[]);
                    let BodyRole::Loop {
                        parent_body,
                        stmt_idx: loop_stmt_idx,
                        site: loop_site,
                        arms: loop_arms,
                    } = roles[loop_body].clone()
                    else {
                        unreachable!("a loop body");
                    };
                    // [O6](b): which `□` ended the loop, where a formula asks.
                    if let Some(bit_id) = plan.leave_bit.get(&(b_id, s_idx)) {
                        let _ = writeln!(emitter.code, "  store i1 true, ptr %bit_{bit_id}");
                    }
                    if let Some(bit_id) = plan.bit[loop_site][*alternative] {
                        let _ = writeln!(emitter.code, "  store i1 true, ptr %bit_{bit_id}");
                    }
                    for (&var_id, val) in loop_arms[*alternative].iter().zip(pay_vals) {
                        let ll_ty = emitter.llvm_ty(&body.vars[var_id].ty);
                        let _ = writeln!(emitter.code, "  store {ll_ty} {val}, ptr %slot_{var_id}");
                    }
                    let resume_lbl = &plan.stmt_next[parent_body][loop_stmt_idx];
                    let _ = writeln!(emitter.code, "  br label %{resume_lbl}");
                }
                Command::Exit {
                    alternative,
                    payload,
                } => {
                    let UnitKind::Control { id: cid, .. } = unit else {
                        unreachable!("boundary cannot exit as control");
                    };
                    let pay_vals =
                        emitter.emit_exprs_ordered(payload, &VarAccess::ControlSlots(body));
                    end_scopes(&mut emitter, b_id, s_idx, None, &[]);
                    let contract_alt = &program.controls[cid].contract[*alternative];
                    for (field_idx, (field, val)) in
                        contract_alt.fields.iter().zip(pay_vals).enumerate()
                    {
                        let ll_ty = emitter.llvm_ty(&field.ty);
                        let _ = writeln!(
                            emitter.code,
                            "  store {ll_ty} {val}, ptr %out_{alternative}_{field_idx}"
                        );
                    }
                    let _ = writeln!(emitter.code, "  ret i32 {alternative}");
                }
                Command::Fault { message, .. } => {
                    let msg_val = emitter.emit_expr(message, &VarAccess::ControlSlots(body));
                    emit_fault(&mut emitter, b_id, s_idx, &msg_val);
                }
                Command::Escalate => {
                    // The original fault goes on with its message, which
                    // the contingency has held since it was entered.
                    let mut cur = b_id;
                    while !matches!(roles[cur], BodyRole::LexicalB2 { .. } | BodyRole::Root) {
                        cur = match &roles[cur] {
                            BodyRole::Loop { parent_body, .. }
                            | BodyRole::LexicalB1 { parent_body, .. } => *parent_body,
                            _ => 0,
                        };
                    }
                    let (held, carried) = if matches!(roles[cur], BodyRole::LexicalB2 { .. }) {
                        (format!("%lex_fault_{cur}"), Carried::Lexical(cur))
                    } else {
                        assert!(unit_message.is_some(), "`escalate` outside a contingency");
                        ("%unit_fault".to_string(), Carried::Unit)
                    };
                    let msg_val = emitter.fresh_reg();
                    let _ = writeln!(emitter.code, "  {msg_val} = load %vn2.string, ptr {held}");
                    emit_unwind(&mut emitter, b_id, s_idx, &msg_val, carried);
                }
                Command::Terminate(opt_expr) => {
                    end_scopes(&mut emitter, b_id, s_idx, None, &[]);
                    if let Some(status) = opt_expr {
                        // [E-Contingency]: the execution ends with a status.
                        let val = status.to_string();
                        if let Some((ref tptr, ref tty)) = unit_out_term {
                            let t_ll = emitter.llvm_ty(tty);
                            let _ = writeln!(emitter.code, "  store {t_ll} {val}, ptr {tptr}");
                        }
                        let _ = writeln!(emitter.code, "  ret i32 -2");
                    } else {
                        // [E-Supervise]: a body of a named boundary ends.
                        if unit_message.is_some() {
                            emitter.emit_drop_ptr("%unit_fault", &Type::String);
                        }
                        let _ = writeln!(emitter.code, "  ret i32 0");
                    }
                }
                Command::Recover { body: target_loop } => {
                    // [E-Contingency]: the loop starts again with its own
                    // parameters, which stay in their slots. Everything
                    // else of the scopes up to the loop ends.
                    let parameters: Vec<VarId> = body.bodies[*target_loop]
                        .head
                        .as_ref()
                        .map(|head| head.parameters.clone())
                        .unwrap_or_default();
                    end_scopes(&mut emitter, b_id, s_idx, Some(*target_loop), &parameters);
                    let _ = writeln!(emitter.code, "  br label %b{target_loop}_entry");
                }
                Command::Impossible => {
                    // [R2]: `⊥` has no behavior and emits `unreachable`.
                    let _ = writeln!(emitter.code, "  unreachable");
                }
            }
        }

        // End of body `b{b_id}_end:`:
        // For a lexical boundary body (`LexicalB1`), falling off the end completes cleanly!
        let _ = writeln!(emitter.code, "b{b_id}_end:");
        if let BodyRole::LexicalB1 {
            parent_body,
            stmt_idx,
            site,
            contingency_vars,
            ..
        } = &roles[b_id]
        {
            // Drop B1's remaining Drop locals at end of B1 using the post-end snapshot.
            emitter.emit_scope_cleanup(body, &plan, b_id, b_id, b.statements.len(), &[], false);
            // Drop captured values prepared for B2 since no fault occurred.
            for &cv in contingency_vars {
                let cty = body.vars[cv].ty.clone();
                emitter.emit_drop_ptr(&format!("%slot_{cv}"), &cty);
            }
            if let Some(bit_id) = plan.bit[*site][0] {
                let _ = writeln!(emitter.code, "  store i1 true, ptr %bit_{bit_id}");
            }
            let resume_lbl = &plan.stmt_next[*parent_body][*stmt_idx];
            let _ = writeln!(emitter.code, "  br label %{resume_lbl}");
        } else {
            // [K7], [R2]: Reaching the end of any control/loop/contingency body is impossible.
            let _ = writeln!(emitter.code, "  unreachable");
        }
    }

    let _ = writeln!(out, "entry:");
    for alloca in &emitter.allocas {
        let _ = writeln!(out, "{alloca}");
    }
    out.push_str(&emitter.code);
    let _ = writeln!(out, "}}\n");
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn emit_operation_call(
    em: &mut IrEmitter<'_, '_>,
    program: &Program,
    term_tys: &[Option<Type>],
    body: &ControlBody,
    b_id: BodyId,
    s_idx: usize,
    op_kind: &Operation,
    arguments: &[Expr],
    on_done: impl FnOnce(&mut IrEmitter<'_, '_>, &str, &[Vec<String>], Vec<ReadOperand>),
    emit_unwind: &impl Fn(&mut IrEmitter<'_, '_>, BodyId, usize, &str),
    caller_out_term: Option<&str>,
) -> Result<(), String> {
    if let Operation::AwaitNext(set, id) = op_kind {
        let (tag, slots) = tasks::next(em, *set, *id);
        on_done(em, &tag, &slots, Vec::new());
        return Ok(());
    }
    let contract = op_kind.contract(program);
    let mut out_slots: Vec<Vec<String>> = Vec::new();
    let is_extern_ctrl =
        matches!(op_kind, Operation::Control(cid) if program.controls[*cid].body.is_none());

    for alt in &contract {
        let mut alt_slots = Vec::new();
        for f in &alt.fields {
            let slot_ty = if is_extern_ctrl && f.ty == Type::Bool {
                "i8".to_string()
            } else {
                em.llvm_ty(&f.ty)
            };
            alt_slots.push(em.alloc_temp(&slot_ty));
        }
        out_slots.push(alt_slots);
    }

    match op_kind {
        Operation::AwaitNext(_, _) => unreachable!("handled before allocating output slots"),
        Operation::AwaitControl(cid) if program.controls[*cid].body.is_none() => {
            return Err(format!(
                "the native backend does not yet support await of `{}`",
                program.controls[*cid].name
            ));
        }
        Operation::RunControl(cid) if program.controls[*cid].body.is_none() => {
            return Err(format!(
                "the native backend does not yet support run of extern async control `{}`",
                program.controls[*cid].name
            ));
        }
        Operation::Control(cid) | Operation::RunControl(cid) | Operation::AwaitControl(cid) => {
            let callee = &program.controls[*cid];
            let is_extern = callee.body.is_none();
            let mut results: Vec<Option<String>> = vec![None; arguments.len()];
            let mut temp_drops = Vec::new();
            let is_lending = |i: usize, e: &Expr| -> bool {
                e.lends()
                    || callee
                        .parameters
                        .get(i)
                        .is_some_and(|p| matches!(p.ty, Type::Ref(_, _)))
            };
            // [E-Operands]: non-lending operands first, then lending operands.
            for (i, arg) in arguments.iter().enumerate() {
                if !is_lending(i, arg) {
                    results[i] = Some(em.emit_expr(arg, &VarAccess::ControlSlots(body)));
                }
            }
            for (i, arg) in arguments.iter().enumerate() {
                if is_lending(i, arg) {
                    if callee
                        .parameters
                        .get(i)
                        .is_some_and(|p| matches!(p.ty, Type::Ref(_, _)))
                    {
                        let op = em.emit_read_operand(arg, &VarAccess::ControlSlots(body));
                        let ptr = em.read_operand_ptr(&op).to_string();
                        results[i] = Some(ptr);
                        temp_drops.push(op);
                    } else {
                        results[i] = Some(em.emit_expr(arg, &VarAccess::ControlSlots(body)));
                    }
                }
            }

            let mut call_args = Vec::new();
            for (i, param) in callee.parameters.iter().enumerate() {
                let raw = results[i].take().unwrap();
                if matches!(param.ty, Type::Ref(_, _)) {
                    // A borrow is the place itself, a `bool` among the
                    // rest: a byte that holds 0 or 1. A host writes behind
                    // it, and what it lends from it is that place ([E-Extern]).
                    call_args.push(format!("ptr {raw}"));
                } else if is_extern && param.ty == Type::Bool {
                    let ext = em.fresh_reg();
                    let _ = writeln!(em.code, "  {ext} = zext i1 {raw} to i8");
                    call_args.push(format!("i8 {ext}"));
                } else {
                    let ll = em.llvm_ty(&param.ty);
                    if is_extern && !is_c_scalar_by_val(program, &param.ty) {
                        let tmp = em.alloc_temp(&ll);
                        let _ = writeln!(em.code, "  store {ll} {raw}, ptr {tmp}");
                        call_args.push(format!("ptr {tmp}"));
                    } else {
                        call_args.push(format!("{ll} {raw}"));
                    }
                }
            }
            for alt_slots in &out_slots {
                for slot in alt_slots {
                    call_args.push(format!("ptr {slot}"));
                }
            }
            let fslot = if callee.faults {
                let p = em.alloc_temp("%vn2.string");
                call_args.push(format!("ptr {p}"));
                Some(p)
            } else {
                None
            };
            let tslot = if !is_extern && term_tys[*cid].is_some() {
                if let Some(ct) = caller_out_term {
                    call_args.push(format!("ptr {ct}"));
                    Some(ct.to_string())
                } else {
                    let t_ll = em.llvm_ty(term_tys[*cid].as_ref().unwrap());
                    let p = em.alloc_temp(&t_ll);
                    call_args.push(format!("ptr {p}"));
                    Some(p)
                }
            } else {
                None
            };

            let tag_reg = em.fresh_reg();
            if matches!(op_kind, Operation::AwaitControl(_)) {
                // [E-Await] Bind the inputs and the caller's result slots before
                // the turn ends. The frame lives until the continuation returns.
                let ty = format!("%vn2.await.{cid}");
                let frame = em.alloc_temp(&ty);
                for (index, arg) in call_args.iter().enumerate() {
                    let slot = em.fresh_reg();
                    let _ = writeln!(
                        em.code,
                        "  {slot} = getelementptr {ty}, ptr {frame}, i32 0, i32 {index}"
                    );
                    let _ = writeln!(em.code, "  store {arg}, ptr {slot}");
                }
                let _ = writeln!(
                    em.code,
                    "  {tag_reg} = call fastcc i32 @vn2_take_only_ready(ptr @vn2_resume_{cid}, ptr {frame})"
                );
            } else if is_extern {
                let _ = writeln!(
                    em.code,
                    "  {tag_reg} = call i32 @vn2_ext_{}({})",
                    callee.name,
                    call_args.join(", ")
                );
            } else {
                let _ = writeln!(
                    em.code,
                    "  {tag_reg} = call fastcc i32 @vn2_ctrl_{cid}({})",
                    call_args.join(", ")
                );
            }

            if fslot.is_some() || tslot.is_some() {
                for td in temp_drops.iter().rev() {
                    if let ReadOperand::OwnedTemp { ptr, ty } = td {
                        em.emit_drop_ptr(ptr, ty);
                    }
                }
                temp_drops.clear();
            }

            if let Some(fp) = fslot {
                let is_f = em.fresh_reg();
                let f_lbl = em.fresh_label("op_fault");
                let ok_lbl = em.fresh_label("op_no_fault");
                let _ = writeln!(em.code, "  {is_f} = icmp eq i32 {tag_reg}, -1");
                let _ = writeln!(em.code, "  br i1 {is_f}, label %{f_lbl}, label %{ok_lbl}");
                let _ = writeln!(em.code, "{f_lbl}:");
                let fmsg = em.fresh_reg();
                let _ = writeln!(em.code, "  {fmsg} = load %vn2.string, ptr {fp}");
                emit_unwind(em, b_id, s_idx, &fmsg);
                let _ = writeln!(em.code, "{ok_lbl}:");
            }
            if tslot.is_some() {
                let is_t = em.fresh_reg();
                let t_lbl = em.fresh_label("op_term");
                let ok_lbl = em.fresh_label("op_no_term");
                let _ = writeln!(em.code, "  {is_t} = icmp eq i32 {tag_reg}, -2");
                let _ = writeln!(em.code, "  br i1 {is_t}, label %{t_lbl}, label %{ok_lbl}");
                let _ = writeln!(em.code, "{t_lbl}:");
                let _ = writeln!(em.code, "  ret i32 -2");
                let _ = writeln!(em.code, "{ok_lbl}:");
            }
            on_done(em, &tag_reg, &out_slots, temp_drops);
        }
        Operation::Builtin { op, .. } => {
            emit_builtin_call(em, program, body, *op, arguments, &out_slots, on_done);
        }
        Operation::Outcome(oid) => {
            let oc_val = em.emit_expr(&arguments[0], &VarAccess::ControlSlots(body));
            if is_unit_outcome(program, *oid) {
                on_done(em, &oc_val, &out_slots, Vec::new());
            } else {
                let oc_ll = format!("%vn2.outcome.{oid}");
                let tmp = em.alloc_temp(&oc_ll);
                let _ = writeln!(em.code, "  store {oc_ll} {oc_val}, ptr {tmp}");
                let tp = em.fresh_reg();
                let _ = writeln!(
                    em.code,
                    "  {tp} = getelementptr {oc_ll}, ptr {tmp}, i32 0, i32 0"
                );
                let tag_reg = em.fresh_reg();
                let _ = writeln!(em.code, "  {tag_reg} = load i32, ptr {tp}");
                let done_lbl = em.fresh_label("oc_done");
                let mut cases = String::new();
                for (k, alt) in program.outcomes[*oid].alternatives.iter().enumerate() {
                    if alt.fields.is_empty() {
                        let _ = write!(cases, " i32 {k}, label %{done_lbl}");
                    } else {
                        let _ = write!(cases, " i32 {k}, label %{done_lbl}_a{k}");
                    }
                }
                let _ = writeln!(
                    em.code,
                    "  switch i32 {tag_reg}, label %{done_lbl} [ {cases} ]"
                );
                for (k, alt) in program.outcomes[*oid].alternatives.iter().enumerate() {
                    if alt.fields.is_empty() {
                        continue;
                    }
                    let _ = writeln!(em.code, "{done_lbl}_a{k}:");
                    let sub_ll = format!("%vn2.outcome.{oid}.a{k}");
                    let pp = em.fresh_reg();
                    let _ = writeln!(
                        em.code,
                        "  {pp} = getelementptr {oc_ll}, ptr {tmp}, i32 0, i32 1"
                    );
                    for (fi, f) in alt.fields.iter().enumerate() {
                        let f_ll = em.llvm_ty(&f.ty);
                        let gp = em.fresh_reg();
                        let _ = writeln!(
                            em.code,
                            "  {gp} = getelementptr {sub_ll}, ptr {pp}, i32 0, i32 {fi}"
                        );
                        let fv = em.fresh_reg();
                        let _ = writeln!(em.code, "  {fv} = load {f_ll}, ptr {gp}");
                        let dst_s = &out_slots[k][fi];
                        let _ = writeln!(em.code, "  store {f_ll} {fv}, ptr {dst_s}");
                    }
                    let _ = writeln!(em.code, "  br label %{done_lbl}");
                }
                let _ = writeln!(em.code, "{done_lbl}:");
                on_done(em, &tag_reg, &out_slots, Vec::new());
            }
        }
        Operation::Variant { id: vid, borrow } => {
            if is_unit_variant(program, *vid) {
                let tag_reg = if borrow.is_some() {
                    let op = em.emit_read_operand(&arguments[0], &VarAccess::ControlSlots(body));
                    let p = em.read_operand_ptr(&op).to_string();
                    let r = em.fresh_reg();
                    let _ = writeln!(em.code, "  {r} = load i32, ptr {p}");
                    r
                } else {
                    em.emit_expr(&arguments[0], &VarAccess::ControlSlots(body))
                };
                on_done(em, &tag_reg, &out_slots, Vec::new());
            } else {
                let v_ll = format!("%vn2.variant.{vid}");
                let (v_ptr, temp_drops) = if borrow.is_none() {
                    let val = em.emit_expr(&arguments[0], &VarAccess::ControlSlots(body));
                    let tmp = em.alloc_temp(&v_ll);
                    let _ = writeln!(em.code, "  store {v_ll} {val}, ptr {tmp}");
                    (tmp, Vec::new())
                } else {
                    let op = em.emit_read_operand(&arguments[0], &VarAccess::ControlSlots(body));
                    let p = em.read_operand_ptr(&op).to_string();
                    (p, vec![op])
                };
                let tp = em.fresh_reg();
                let _ = writeln!(
                    em.code,
                    "  {tp} = getelementptr {v_ll}, ptr {v_ptr}, i32 0, i32 0"
                );
                let tag_reg = em.fresh_reg();
                let _ = writeln!(em.code, "  {tag_reg} = load i32, ptr {tp}");
                let done_lbl = em.fresh_label("var_done");
                let mut cases = String::new();
                for (k, ctor) in program.variants[*vid].constructors.iter().enumerate() {
                    if ctor.fields.is_empty() {
                        let _ = write!(cases, " i32 {k}, label %{done_lbl}");
                    } else {
                        let _ = write!(cases, " i32 {k}, label %{done_lbl}_c{k}");
                    }
                }
                let _ = writeln!(
                    em.code,
                    "  switch i32 {tag_reg}, label %{done_lbl} [ {cases} ]"
                );
                for (k, ctor) in program.variants[*vid].constructors.iter().enumerate() {
                    if ctor.fields.is_empty() {
                        continue;
                    }
                    let _ = writeln!(em.code, "{done_lbl}_c{k}:");
                    let sub_ll = format!("%vn2.variant.{vid}.c{k}");
                    let pp = em.fresh_reg();
                    let _ = writeln!(
                        em.code,
                        "  {pp} = getelementptr {v_ll}, ptr {v_ptr}, i32 0, i32 1"
                    );
                    for (fi, f) in ctor.fields.iter().enumerate() {
                        let gp = em.fresh_reg();
                        let _ = writeln!(
                            em.code,
                            "  {gp} = getelementptr {sub_ll}, ptr {pp}, i32 0, i32 {fi}"
                        );
                        let dst_s = &out_slots[k][fi];
                        if borrow.is_some() {
                            let _ = writeln!(em.code, "  store ptr {gp}, ptr {dst_s}");
                        } else {
                            let f_ll = em.llvm_ty(&f.ty);
                            let fv = em.fresh_reg();
                            let _ = writeln!(em.code, "  {fv} = load {f_ll}, ptr {gp}");
                            let _ = writeln!(em.code, "  store {f_ll} {fv}, ptr {dst_s}");
                        }
                    }
                    let _ = writeln!(em.code, "  br label %{done_lbl}");
                }
                let _ = writeln!(em.code, "{done_lbl}:");
                on_done(em, &tag_reg, &out_slots, temp_drops);
            }
        }
    }
    Ok(())
}

fn emit_builtin_call(
    em: &mut IrEmitter<'_, '_>,
    _program: &Program,
    body: &ControlBody,
    op: BuiltinOp,
    arguments: &[Expr],
    out_slots: &[Vec<String>],
    on_done: impl FnOnce(&mut IrEmitter<'_, '_>, &str, &[Vec<String>], Vec<ReadOperand>),
) {
    let u = em.usize_ty();
    match op {
        BuiltinOp::Push => {
            em.reg.needed_vec_grow = true;
            em.reg.needed_libc = true;
            let val = em.emit_expr(&arguments[1], &VarAccess::ControlSlots(body));
            let elem_ty = arguments[1].ty();
            let e_ll = em.llvm_ty(&elem_ty);
            let v_op = em.emit_read_operand(&arguments[0], &VarAccess::ControlSlots(body));
            let v_ptr = em.read_operand_ptr(&v_op).to_string();
            let lp = em.fresh_reg();
            let cp = em.fresh_reg();
            let _ = writeln!(
                em.code,
                "  {lp} = getelementptr %vn2.vec, ptr {v_ptr}, i32 0, i32 1"
            );
            let _ = writeln!(
                em.code,
                "  {cp} = getelementptr %vn2.vec, ptr {v_ptr}, i32 0, i32 2"
            );
            let len = em.fresh_reg();
            let cap = em.fresh_reg();
            let _ = writeln!(em.code, "  {len} = load {u}, ptr {lp}");
            let _ = writeln!(em.code, "  {cap} = load {u}, ptr {cp}");
            let full = em.fresh_reg();
            let _ = writeln!(em.code, "  {full} = icmp eq {u} {len}, {cap}");
            let grow_lbl = em.fresh_label("push_grow");
            let put_lbl = em.fresh_label("push_put");
            let _ = writeln!(
                em.code,
                "  br i1 {full}, label %{grow_lbl}, label %{put_lbl}"
            );
            let _ = writeln!(em.code, "{grow_lbl}:");
            let sp = em.fresh_reg();
            let stride = em.fresh_reg();
            let _ = writeln!(em.code, "  {sp} = getelementptr {e_ll}, ptr null, i32 1");
            let _ = writeln!(em.code, "  {stride} = ptrtoint ptr {sp} to i64");
            let _ = writeln!(
                em.code,
                "  call fastcc void @vn2_vec_grow(ptr {v_ptr}, i64 {stride})"
            );
            let _ = writeln!(em.code, "  br label %{put_lbl}");
            let _ = writeln!(em.code, "{put_lbl}:");
            let dp = em.fresh_reg();
            let _ = writeln!(
                em.code,
                "  {dp} = getelementptr %vn2.vec, ptr {v_ptr}, i32 0, i32 0"
            );
            let data = em.fresh_reg();
            let _ = writeln!(em.code, "  {data} = load ptr, ptr {dp}");
            let dst = em.fresh_reg();
            let _ = writeln!(
                em.code,
                "  {dst} = getelementptr {e_ll}, ptr {data}, {u} {len}"
            );
            let _ = writeln!(em.code, "  store {e_ll} {val}, ptr {dst}");
            let nlen = em.fresh_reg();
            let _ = writeln!(em.code, "  {nlen} = add {u} {len}, 1");
            let _ = writeln!(em.code, "  store {u} {nlen}, ptr {lp}");
            on_done(em, "0", out_slots, vec![v_op]);
        }
        BuiltinOp::Pop => {
            let v_op = em.emit_read_operand(&arguments[0], &VarAccess::ControlSlots(body));
            let v_ptr = em.read_operand_ptr(&v_op).to_string();
            let Type::Vector(elem_ty) = arguments[0].ty().deref_type().clone() else {
                unreachable!();
            };
            let e_ll = em.llvm_ty(&elem_ty);
            let lp = em.fresh_reg();
            let _ = writeln!(
                em.code,
                "  {lp} = getelementptr %vn2.vec, ptr {v_ptr}, i32 0, i32 1"
            );
            let len = em.fresh_reg();
            let _ = writeln!(em.code, "  {len} = load {u}, ptr {lp}");
            let is_z = em.fresh_reg();
            let _ = writeln!(em.code, "  {is_z} = icmp eq {u} {len}, 0");
            let emp_lbl = em.fresh_label("pop_empty");
            let item_lbl = em.fresh_label("pop_item");
            let done_lbl = em.fresh_label("pop_done");
            let tag_slot = em.alloc_temp("i32");
            let _ = writeln!(
                em.code,
                "  br i1 {is_z}, label %{emp_lbl}, label %{item_lbl}"
            );
            let _ = writeln!(em.code, "{emp_lbl}:");
            let _ = writeln!(em.code, "  store i32 1, ptr {tag_slot}");
            let _ = writeln!(em.code, "  br label %{done_lbl}");
            let _ = writeln!(em.code, "{item_lbl}:");
            let nlen = em.fresh_reg();
            let _ = writeln!(em.code, "  {nlen} = sub {u} {len}, 1");
            let _ = writeln!(em.code, "  store {u} {nlen}, ptr {lp}");
            let dp = em.fresh_reg();
            let _ = writeln!(
                em.code,
                "  {dp} = getelementptr %vn2.vec, ptr {v_ptr}, i32 0, i32 0"
            );
            let data = em.fresh_reg();
            let _ = writeln!(em.code, "  {data} = load ptr, ptr {dp}");
            let ep = em.fresh_reg();
            let _ = writeln!(
                em.code,
                "  {ep} = getelementptr {e_ll}, ptr {data}, {u} {nlen}"
            );
            let ev = em.fresh_reg();
            let _ = writeln!(em.code, "  {ev} = load {e_ll}, ptr {ep}");
            let out_p = &out_slots[0][0];
            let _ = writeln!(em.code, "  store {e_ll} {ev}, ptr {out_p}");
            let _ = writeln!(em.code, "  store i32 0, ptr {tag_slot}");
            let _ = writeln!(em.code, "  br label %{done_lbl}");
            let _ = writeln!(em.code, "{done_lbl}:");
            let tag_reg = em.fresh_reg();
            let _ = writeln!(em.code, "  {tag_reg} = load i32, ptr {tag_slot}");
            on_done(em, &tag_reg, out_slots, vec![v_op]);
        }
        BuiltinOp::Take => {
            em.reg.needed_libc = true;
            let vec_val = em.emit_expr(&arguments[0], &VarAccess::ControlSlots(body));
            let Type::Vector(elem_ty) = arguments[0].ty().deref_type().clone() else {
                unreachable!();
            };
            let e_ll = em.llvm_ty(&elem_ty);
            let data = em.fresh_reg();
            let len = em.fresh_reg();
            let cap = em.fresh_reg();
            let _ = writeln!(em.code, "  {data} = extractvalue %vn2.vec {vec_val}, 0");
            let _ = writeln!(em.code, "  {len} = extractvalue %vn2.vec {vec_val}, 1");
            let _ = writeln!(em.code, "  {cap} = extractvalue %vn2.vec {vec_val}, 2");
            let is_z = em.fresh_reg();
            let _ = writeln!(em.code, "  {is_z} = icmp eq {u} {len}, 0");
            let emp_lbl = em.fresh_label("take_empty");
            let item_lbl = em.fresh_label("take_item");
            let done_lbl = em.fresh_label("take_done");
            let tag_slot = em.alloc_temp("i32");
            let _ = writeln!(
                em.code,
                "  br i1 {is_z}, label %{emp_lbl}, label %{item_lbl}"
            );
            let _ = writeln!(em.code, "{emp_lbl}:");
            let has_c = em.fresh_reg();
            let _ = writeln!(em.code, "  {has_c} = icmp ne {u} {cap}, 0");
            let f_lbl = em.fresh_label("take_free");
            let _ = writeln!(
                em.code,
                "  br i1 {has_c}, label %{f_lbl}, label %{emp_lbl}_end"
            );
            let _ = writeln!(em.code, "{f_lbl}:");
            let _ = writeln!(em.code, "  call void @free(ptr {data})");
            let _ = writeln!(em.code, "  br label %{emp_lbl}_end");
            let _ = writeln!(em.code, "{emp_lbl}_end:");
            let _ = writeln!(em.code, "  store i32 1, ptr {tag_slot}");
            let _ = writeln!(em.code, "  br label %{done_lbl}");

            let _ = writeln!(em.code, "{item_lbl}:");
            let head = em.fresh_reg();
            let _ = writeln!(em.code, "  {head} = load {e_ll}, ptr {data}");
            let head_out = &out_slots[0][0];
            let tail_out = &out_slots[0][1];
            let _ = writeln!(em.code, "  store {e_ll} {head}, ptr {head_out}");
            let rem = em.fresh_reg();
            let _ = writeln!(em.code, "  {rem} = sub {u} {len}, 1");
            let rem_z = em.fresh_reg();
            let _ = writeln!(em.code, "  {rem_z} = icmp eq {u} {rem}, 0");
            let ztail_lbl = em.fresh_label("take_ztail");
            let shift_lbl = em.fresh_label("take_shift");
            let _ = writeln!(
                em.code,
                "  br i1 {rem_z}, label %{ztail_lbl}, label %{shift_lbl}"
            );
            let _ = writeln!(em.code, "{ztail_lbl}:");
            let hc2 = em.fresh_reg();
            let _ = writeln!(em.code, "  {hc2} = icmp ne {u} {cap}, 0");
            let f2_lbl = em.fresh_label("take_f2");
            let _ = writeln!(
                em.code,
                "  br i1 {hc2}, label %{f2_lbl}, label %{ztail_lbl}_end"
            );
            let _ = writeln!(em.code, "{f2_lbl}:");
            let _ = writeln!(em.code, "  call void @free(ptr {data})");
            let _ = writeln!(em.code, "  br label %{ztail_lbl}_end");
            let _ = writeln!(em.code, "{ztail_lbl}_end:");
            let _ = writeln!(em.code, "  store %vn2.vec zeroinitializer, ptr {tail_out}");
            let _ = writeln!(em.code, "  store i32 0, ptr {tag_slot}");
            let _ = writeln!(em.code, "  br label %{done_lbl}");

            let _ = writeln!(em.code, "{shift_lbl}:");
            let sp = em.fresh_reg();
            let stride = em.fresh_reg();
            let _ = writeln!(em.code, "  {sp} = getelementptr {e_ll}, ptr null, i32 1");
            let _ = writeln!(em.code, "  {stride} = ptrtoint ptr {sp} to i64");
            let rem64 = em.emit_zext_usize_to_i64(&rem);
            let bytes = em.fresh_reg();
            let _ = writeln!(em.code, "  {bytes} = mul i64 {rem64}, {stride}");
            let src1 = em.fresh_reg();
            let _ = writeln!(
                em.code,
                "  {src1} = getelementptr {e_ll}, ptr {data}, i64 1"
            );
            let _ = writeln!(
                em.code,
                "  call ptr @memmove(ptr {data}, ptr {src1}, i64 {bytes})"
            );
            let t0 = em.fresh_reg();
            let t1 = em.fresh_reg();
            let t2 = em.fresh_reg();
            let _ = writeln!(
                em.code,
                "  {t0} = insertvalue %vn2.vec undef, ptr {data}, 0"
            );
            let _ = writeln!(em.code, "  {t1} = insertvalue %vn2.vec {t0}, {u} {rem}, 1");
            let _ = writeln!(em.code, "  {t2} = insertvalue %vn2.vec {t1}, {u} {cap}, 2");
            let _ = writeln!(em.code, "  store %vn2.vec {t2}, ptr {tail_out}");
            let _ = writeln!(em.code, "  store i32 0, ptr {tag_slot}");
            let _ = writeln!(em.code, "  br label %{done_lbl}");

            let _ = writeln!(em.code, "{done_lbl}:");
            let tag_reg = em.fresh_reg();
            let _ = writeln!(em.code, "  {tag_reg} = load i32, ptr {tag_slot}");
            on_done(em, &tag_reg, out_slots, Vec::new());
        }
        BuiltinOp::Get => {
            em.reg.needed_libc = true;
            let k_op = em.emit_read_operand(&arguments[1], &VarAccess::ControlSlots(body));
            let m_op = em.emit_read_operand(&arguments[0], &VarAccess::ControlSlots(body));
            let k_ptr = em.read_operand_ptr(&k_op).to_string();
            let m_ptr = em.read_operand_ptr(&m_op).to_string();
            let Type::Map(k_ty, v_ty) = arguments[0].ty().deref_type().clone() else {
                unreachable!();
            };
            let mid = em.reg.intern_map(&k_ty, &v_ty);
            let out_p = &out_slots[0][0];
            let tag_reg = em.fresh_reg();
            let _ = writeln!(
                em.code,
                "  {tag_reg} = call fastcc i32 @vn2_map_get_{mid}(ptr {m_ptr}, ptr {k_ptr}, ptr {out_p})"
            );
            on_done(em, &tag_reg, out_slots, vec![m_op, k_op]);
        }
        BuiltinOp::Insert => {
            em.reg.needed_libc = true;
            let k_val = em.emit_expr(&arguments[1], &VarAccess::ControlSlots(body));
            let v_val = em.emit_expr(&arguments[2], &VarAccess::ControlSlots(body));
            let m_op = em.emit_read_operand(&arguments[0], &VarAccess::ControlSlots(body));
            let m_ptr = em.read_operand_ptr(&m_op).to_string();
            let Type::Map(k_ty, v_ty) = arguments[0].ty().deref_type().clone() else {
                unreachable!();
            };
            let k_ll = em.llvm_ty(&k_ty);
            let v_ll = em.llvm_ty(&v_ty);
            let k_tmp = em.alloc_temp(&k_ll);
            let v_tmp = em.alloc_temp(&v_ll);
            let _ = writeln!(em.code, "  store {k_ll} {k_val}, ptr {k_tmp}");
            let _ = writeln!(em.code, "  store {v_ll} {v_val}, ptr {v_tmp}");
            let mid = em.reg.intern_map(&k_ty, &v_ty);
            if needs_drop(em.program, &k_ty) {
                let ktid = em.reg.intern_type(&k_ty);
                em.reg.require_drop(ktid);
            }
            let out_p = &out_slots[1][0];
            let tag_reg = em.fresh_reg();
            let _ = writeln!(
                em.code,
                "  {tag_reg} = call fastcc i32 @vn2_map_insert_{mid}(ptr {m_ptr}, ptr {k_tmp}, ptr {v_tmp}, ptr {out_p})"
            );
            on_done(em, &tag_reg, out_slots, vec![m_op]);
        }
        BuiltinOp::Remove => {
            em.reg.needed_libc = true;
            let k_op = em.emit_read_operand(&arguments[1], &VarAccess::ControlSlots(body));
            let m_op = em.emit_read_operand(&arguments[0], &VarAccess::ControlSlots(body));
            let k_ptr = em.read_operand_ptr(&k_op).to_string();
            let m_ptr = em.read_operand_ptr(&m_op).to_string();
            let Type::Map(k_ty, v_ty) = arguments[0].ty().deref_type().clone() else {
                unreachable!();
            };
            let mid = em.reg.intern_map(&k_ty, &v_ty);
            if needs_drop(em.program, &k_ty) {
                let ktid = em.reg.intern_type(&k_ty);
                em.reg.require_drop(ktid);
            }
            let out_p = &out_slots[0][0];
            let tag_reg = em.fresh_reg();
            let _ = writeln!(
                em.code,
                "  {tag_reg} = call fastcc i32 @vn2_map_remove_{mid}(ptr {m_ptr}, ptr {k_ptr}, ptr {out_p})"
            );
            on_done(em, &tag_reg, out_slots, vec![m_op, k_op]);
        }
        BuiltinOp::EntryAt => {
            em.reg.needed_libc = true;
            let pos = em.emit_expr(&arguments[1], &VarAccess::ControlSlots(body));
            let m_op = em.emit_read_operand(&arguments[0], &VarAccess::ControlSlots(body));
            let m_ptr = em.read_operand_ptr(&m_op).to_string();
            let Type::Map(k_ty, v_ty) = arguments[0].ty().deref_type().clone() else {
                unreachable!();
            };
            let k_ll = em.llvm_ty(&k_ty);
            let v_ll = em.llvm_ty(&v_ty);
            let mid = em.reg.intern_map(&k_ty, &v_ty);
            let entry_ty = format!("%vn2.map_entry.{mid}");
            let lp = em.fresh_reg();
            let dp = em.fresh_reg();
            let _ = writeln!(
                em.code,
                "  {lp} = getelementptr %vn2.map, ptr {m_ptr}, i32 0, i32 1"
            );
            let _ = writeln!(
                em.code,
                "  {dp} = getelementptr %vn2.map, ptr {m_ptr}, i32 0, i32 0"
            );
            let len = em.fresh_reg();
            let data = em.fresh_reg();
            let _ = writeln!(em.code, "  {len} = load {u}, ptr {lp}");
            let _ = writeln!(em.code, "  {data} = load ptr, ptr {dp}");
            let in_b = em.fresh_reg();
            let _ = writeln!(em.code, "  {in_b} = icmp ult {u} {pos}, {len}");
            let hit_lbl = em.fresh_label("eat_hit");
            let end_lbl = em.fresh_label("eat_end");
            let fin_lbl = em.fresh_label("eat_fin");
            let tag_slot = em.alloc_temp("i32");
            let _ = writeln!(
                em.code,
                "  br i1 {in_b}, label %{hit_lbl}, label %{end_lbl}"
            );
            let _ = writeln!(em.code, "{end_lbl}:");
            let _ = writeln!(em.code, "  store i32 1, ptr {tag_slot}");
            let _ = writeln!(em.code, "  br label %{fin_lbl}");
            let _ = writeln!(em.code, "{hit_lbl}:");
            let ep = em.fresh_reg();
            let _ = writeln!(
                em.code,
                "  {ep} = getelementptr {entry_ty}, ptr {data}, {u} {pos}"
            );
            let kp = em.fresh_reg();
            let vp = em.fresh_reg();
            let _ = writeln!(
                em.code,
                "  {kp} = getelementptr {entry_ty}, ptr {ep}, i32 0, i32 0"
            );
            let _ = writeln!(
                em.code,
                "  {vp} = getelementptr {entry_ty}, ptr {ep}, i32 0, i32 1"
            );
            let _ = writeln!(em.code, "  store ptr {kp}, ptr {}", out_slots[0][0]);
            let _ = writeln!(em.code, "  store ptr {vp}, ptr {}", out_slots[0][1]);
            let _ = (&k_ll, &v_ll);
            let next_p = em.fresh_reg();
            let _ = writeln!(em.code, "  {next_p} = add {u} {pos}, 1");
            let _ = writeln!(em.code, "  store {u} {next_p}, ptr {}", out_slots[0][2]);
            let _ = writeln!(em.code, "  store i32 0, ptr {tag_slot}");
            let _ = writeln!(em.code, "  br label %{fin_lbl}");
            let _ = writeln!(em.code, "{fin_lbl}:");
            let tag_reg = em.fresh_reg();
            let _ = writeln!(em.code, "  {tag_reg} = load i32, ptr {tag_slot}");
            on_done(em, &tag_reg, out_slots, vec![m_op]);
        }
        BuiltinOp::Emit => {
            let s_op = em.emit_read_operand(&arguments[0], &VarAccess::ControlSlots(body));
            let s_ptr = em.read_operand_ptr(&s_op).to_string();
            let _ = writeln!(em.code, "  call void @vn2_builtin_emit(ptr {s_ptr})");
            on_done(em, "0", out_slots, vec![s_op]);
        }
    }
}

// ---------------------------------------------------------------------------
// Module-level LLVM IR emission (`emit_llvm`)
// ---------------------------------------------------------------------------

/// Emits the textual LLVM IR module for all functions, boundaries, and controls
/// of `program`.
pub fn emit_llvm(program: &Program, usize_bits: u32) -> Result<String, String> {
    let mut reg = RuntimeRegistry::new(program, usize_bits);
    let term_tys = compute_control_terminate_tys(program);

    let mut decls_out = String::new();
    let mut body_out = String::new();

    // 1. Extern controls, fault-release callbacks, and emit builtin declarations.
    for control in &program.controls {
        if control.body.is_none() {
            let sig = c_abi_signature_types(program, control, usize_bits);
            let _ = writeln!(
                decls_out,
                "declare i32 @vn2_ext_{}({})",
                control.name,
                sig.join(", ")
            );
        }
    }
    for res in &program.resources {
        if res.on_fault_release {
            let _ = writeln!(decls_out, "declare void @vn2_release_{}(ptr)", res.name);
        }
    }
    if has_emit_builtin(program) {
        let _ = writeln!(decls_out, "declare void @vn2_builtin_emit(ptr)");
    }
    if !decls_out.is_empty() {
        let _ = writeln!(decls_out);
    }

    // 2. Named boundaries, pure functions, and defined controls.
    let awaited = defined_await_targets(program).collect::<BTreeSet<_>>();
    emit_await_continuations(&mut body_out, program, &term_tys, usize_bits, &awaited);
    emit_program_bodies(&mut body_out, program, &mut reg, &term_tys, usize_bits)?;

    if !awaited.is_empty() || tasks::uses_sets(program) {
        let _ = writeln!(decls_out, "declare i64 @vn2_pick_turn(i64)");
    }
    let mut type_out = String::new();
    let _ = writeln!(
        type_out,
        "; Villanelle v2 Phase 4 typed LLVM IR (usize_bits = {usize_bits})\n"
    );
    emit_type_decls(&mut type_out, &reg, false);
    let mut helpers_out = String::new();
    emit_runtime_helpers(&mut helpers_out, &reg);

    let mut out = String::new();
    out.push_str(&type_out);
    out.push_str(&decls_out);
    out.push_str(&helpers_out);
    out.push_str(&body_out);
    Ok(out)
}

fn emit_program_bodies<'a>(
    body_out: &mut String,
    program: &'a Program,
    reg: &mut RuntimeRegistry<'a>,
    term_tys: &[Option<Type>],
    usize_bits: u32,
) -> Result<(), String> {
    tasks::emit_support(body_out, program, usize_bits, term_tys)?;
    // Named boundaries (`@vn2_boundary_<id>` + `@vn2_boundary_b2_<id>`).
    for (bid, bdef) in program.boundaries.iter().enumerate() {
        let b1_params: Vec<(String, Type)> = bdef
            .parameters
            .iter()
            .enumerate()
            .map(|(i, p)| (format!("%p{i}"), p.ty.clone()))
            .collect();
        let b1_fault = if bdef.may_fault {
            Some("%out_fault".to_string())
        } else {
            None
        };
        emit_body_unit(
            body_out,
            program,
            reg,
            term_tys,
            UnitKind::NamedBoundaryB1 { id: bid },
            &format!("vn2_boundary_{bid}"),
            &b1_params,
            &bdef.body,
            b1_fault,
            None,
            bdef.parameters.len(),
        )
        .map_err(|e| format!("boundary `{}`: {e}", bdef.name))?;

        let mut b2_params: Vec<(String, Type)> = bdef
            .retains
            .iter()
            .enumerate()
            .map(|(i, &ridx)| (format!("%p{i}"), bdef.parameters[ridx].ty.clone()))
            .collect();
        b2_params.push(("%m_in".to_string(), Type::String));
        let b2_fault = if bdef.may_fault {
            Some("%out_fault".to_string())
        } else {
            None
        };
        emit_body_unit(
            body_out,
            program,
            reg,
            term_tys,
            UnitKind::NamedBoundaryB2,
            &format!("vn2_boundary_b2_{bid}"),
            &b2_params,
            &bdef.contingency,
            b2_fault,
            None,
            b2_params.len(),
        )
        .map_err(|e| format!("contingency of `{}`: {e}", bdef.name))?;
    }

    // Pure functions (`@vn2_fn_<id>`).
    for (id, function) in program.functions.iter().enumerate() {
        emit_function(body_out, program, reg, id, function);
    }

    // Defined controls (`@vn2_ctrl_<id>`) and C-ABI wrappers (`@vn2_call_<name>`).
    for (id, control) in program.controls.iter().enumerate() {
        if let Some(body) = &control.body {
            let params: Vec<(String, Type)> = control
                .parameters
                .iter()
                .enumerate()
                .map(|(i, p)| (format!("%p{i}"), p.ty.clone()))
                .collect();
            let fslot = if control.faults {
                Some("%out_fault".to_string())
            } else {
                None
            };
            let tslot = term_tys[id]
                .as_ref()
                .map(|t| ("%out_term".to_string(), t.clone()));
            emit_body_unit(
                body_out,
                program,
                reg,
                term_tys,
                UnitKind::Control { id },
                &format!("vn2_ctrl_{id}"),
                &params,
                body,
                fslot,
                tslot,
                control.parameters.len(),
            )
            .map_err(|e| format!("control `{}`: {e}", control.name))?;
            emit_control_c_wrapper(
                body_out,
                program,
                id,
                control,
                term_tys[id].as_ref(),
                usize_bits,
            );
        }
    }
    Ok(())
}

/// [E-Turn] In a module without task sets or extern waits, the suspended
/// task is the sole ready task. After the host picks its turn, enter the
/// awaited control with the arguments already bound in its activation.
fn emit_await_continuations(
    out: &mut String,
    program: &Program,
    term_tys: &[Option<Type>],
    usize_bits: u32,
    awaited: &BTreeSet<ControlId>,
) {
    if awaited.is_empty() {
        return;
    }
    out.push_str(
        "define internal fastcc i32 @vn2_take_only_ready(ptr %resume, ptr %frame) nounwind {
  call i64 @vn2_pick_turn(i64 1)
  %tag = call fastcc i32 %resume(ptr %frame)
  ret i32 %tag
}

",
    );
    for &id in awaited {
        let control = &program.controls[id];
        let mut fields: Vec<String> = control
            .parameters
            .iter()
            .map(|p| llvm_ty(program, &p.ty, usize_bits))
            .collect();
        let output_count = control
            .contract
            .iter()
            .map(|alt| alt.fields.len())
            .sum::<usize>()
            + usize::from(control.faults)
            + usize::from(term_tys[id].is_some());
        fields.extend(std::iter::repeat_n("ptr".to_string(), output_count));
        let ty = format!("%vn2.await.{id}");
        let _ = writeln!(out, "{ty} = type {{ {} }}", fields.join(", "));
        let _ = writeln!(
            out,
            "define internal fastcc i32 @vn2_resume_{id}(ptr %frame) nounwind {{"
        );
        let mut arguments = Vec::with_capacity(fields.len());
        for (index, field) in fields.iter().enumerate() {
            let _ = writeln!(
                out,
                "  %slot{index} = getelementptr {ty}, ptr %frame, i32 0, i32 {index}"
            );
            let _ = writeln!(out, "  %arg{index} = load {field}, ptr %slot{index}");
            arguments.push(format!("{field} %arg{index}"));
        }
        let _ = writeln!(
            out,
            "  %tag = call fastcc i32 @vn2_ctrl_{id}({})",
            arguments.join(", ")
        );
        out.push_str("  ret i32 %tag\n}\n\n");
    }
}

fn c_abi_signature_types(program: &Program, control: &Control, usize_bits: u32) -> Vec<String> {
    let mut sig = Vec::new();
    for param in &control.parameters {
        sig.push(c_abi_llvm_ty(program, &param.ty, usize_bits));
    }
    for alt in &control.contract {
        for _ in &alt.fields {
            sig.push("ptr".to_string());
        }
    }
    if control.faults {
        sig.push("ptr".to_string());
    }
    sig
}

fn emit_function<'a>(
    out: &mut String,
    program: &'a Program,
    reg: &mut RuntimeRegistry<'a>,
    id: FunctionId,
    function: &Function,
) {
    let mut params = Vec::new();
    for (idx, param) in function.parameters.iter().enumerate() {
        let ll = llvm_ty(program, &param.ty, reg.usize_bits);
        params.push(format!("{ll} %p{idx}"));
    }
    let ret_ll = llvm_ty(program, &function.result, reg.usize_bits);
    let _ = writeln!(
        out,
        "define internal fastcc {ret_ll} @vn2_fn_{id}({}) alwaysinline nounwind {{",
        params.join(", ")
    );
    let _ = writeln!(out, "entry:");
    let mut emitter = IrEmitter::new(program, reg);
    let res = emitter.emit_expr(&function.body, &VarAccess::DirectParams(function));
    for alloca in &emitter.allocas {
        let _ = writeln!(out, "{alloca}");
    }
    out.push_str(&emitter.code);
    let _ = writeln!(out, "  ret {ret_ll} {res}");
    let _ = writeln!(out, "}}\n");
}

fn emit_control_c_wrapper(
    out: &mut String,
    program: &Program,
    id: ControlId,
    control: &Control,
    term_ty: Option<&Type>,
    usize_bits: u32,
) {
    let mut c_params = Vec::new();
    for (idx, param) in control.parameters.iter().enumerate() {
        c_params.push(format!(
            "{} %p{idx}",
            c_abi_llvm_ty(program, &param.ty, usize_bits)
        ));
    }
    for (alt_idx, alt) in control.contract.iter().enumerate() {
        for (field_idx, _) in alt.fields.iter().enumerate() {
            c_params.push(format!("ptr %c_out_{alt_idx}_{field_idx}"));
        }
    }
    if control.faults {
        c_params.push("ptr %c_out_fault".to_string());
    }
    if term_ty.is_some() {
        c_params.push("ptr %c_out_term".to_string());
    }

    let _ = writeln!(
        out,
        "define i32 @vn2_call_{}({}) nounwind {{",
        control.name,
        c_params.join(", ")
    );
    let _ = writeln!(out, "entry:");

    let mut internal_args = Vec::new();
    let mut bool_outs = Vec::new();
    let mut bool_ref_writebacks = Vec::new();
    let mut origin_params: HashSet<usize> = HashSet::new();
    for alt in &control.contract {
        for field in &alt.fields {
            for &op in &field.origins {
                origin_params.insert(op);
            }
        }
    }

    for (idx, param) in control.parameters.iter().enumerate() {
        match &param.ty {
            Type::Bool => {
                let _ = writeln!(out, "  %b_in_{idx} = icmp ne i8 %p{idx}, 0");
                internal_args.push(format!("i1 %b_in_{idx}"));
            }
            Type::Ref(_, inner) if **inner == Type::Bool && origin_params.contains(&idx) => {
                internal_args.push(format!("ptr %p{idx}"));
            }
            Type::Ref(mode, inner) if **inner == Type::Bool => {
                let _ = writeln!(out, "  %br_raw_{idx} = load i8, ptr %p{idx}");
                let _ = writeln!(out, "  %br_b_{idx} = icmp ne i8 %br_raw_{idx}, 0");
                let _ = writeln!(out, "  %br_tmp_{idx} = alloca i1");
                let _ = writeln!(out, "  store i1 %br_b_{idx}, ptr %br_tmp_{idx}");
                internal_args.push(format!("ptr %br_tmp_{idx}"));
                if *mode == BorrowMode::Exclusive {
                    bool_ref_writebacks.push(idx);
                }
            }
            other if is_c_scalar_by_val(program, other) => {
                internal_args.push(format!("{} %p{idx}", llvm_ty(program, other, usize_bits)));
            }
            other => {
                let ll = llvm_ty(program, other, usize_bits);
                let _ = writeln!(out, "  %agg_{idx} = load {ll}, ptr %p{idx}");
                internal_args.push(format!("{ll} %agg_{idx}"));
            }
        }
    }

    for (alt_idx, alt) in control.contract.iter().enumerate() {
        for (field_idx, field) in alt.fields.iter().enumerate() {
            if field.ty == Type::Bool {
                let tmp = format!("%b_out_{alt_idx}_{field_idx}");
                let _ = writeln!(out, "  {tmp} = alloca i1");
                internal_args.push(format!("ptr {tmp}"));
                bool_outs.push((alt_idx, field_idx, tmp));
            } else {
                internal_args.push(format!("ptr %c_out_{alt_idx}_{field_idx}"));
            }
        }
    }
    if control.faults {
        internal_args.push("ptr %c_out_fault".to_string());
    }
    if term_ty.is_some() {
        internal_args.push("ptr %c_out_term".to_string());
    }

    let _ = writeln!(
        out,
        "  %tag = call fastcc i32 @vn2_ctrl_{id}({})",
        internal_args.join(", ")
    );

    for idx in bool_ref_writebacks {
        let _ = writeln!(out, "  %bw_b_{idx} = load i1, ptr %br_tmp_{idx}");
        let _ = writeln!(out, "  %bw_i_{idx} = zext i1 %bw_b_{idx} to i8");
        let _ = writeln!(out, "  store i8 %bw_i_{idx}, ptr %p{idx}");
    }
    for (alt_idx, field_idx, tmp) in bool_outs {
        let _ = writeln!(out, "  %bv_{alt_idx}_{field_idx} = load i1, ptr {tmp}");
        let _ = writeln!(
            out,
            "  %bi_{alt_idx}_{field_idx} = zext i1 %bv_{alt_idx}_{field_idx} to i8"
        );
        let _ = writeln!(
            out,
            "  store i8 %bi_{alt_idx}_{field_idx}, ptr %c_out_{alt_idx}_{field_idx}"
        );
    }

    let _ = writeln!(out, "  ret i32 %tag");
    let _ = writeln!(out, "}}\n");
}

// ---------------------------------------------------------------------------
// Complete standalone native harness & printer (`emit_native_harness_llvm`)
// ---------------------------------------------------------------------------

fn checked_arith_kind(name: &str) -> Option<&'static str> {
    [
        "checked_add",
        "checked_sub",
        "checked_mul",
        "checked_div",
        "checked_rem",
    ]
    .into_iter()
    .find(|prefix| name.starts_with(*prefix))
}

fn next_tmp(tmp_id: &mut usize) -> usize {
    let id = *tmp_id;
    *tmp_id += 1;
    id
}

/// What a borrow in a value that the harness writes refers to.
#[derive(Clone, Copy)]
enum Refs<'a> {
    /// A slot of `main`, which holds what the borrow refers to: the
    /// arguments of the entry are given as values.
    Slots,
    /// A place within an argument of the host of this extern control: a
    /// borrow in a payload is a reborrow of one ([E-Extern], [E-Host]).
    Within(&'a Control),
    /// None: a key of a map, or what a host leaves behind an argument.
    Nothing,
}

/// Writes `val` to `dst_ptr`, with the borrows in it as `refs` says.
#[allow(clippy::too_many_arguments)]
fn emit_harness_value_into(
    ir: &mut String,
    program: &Program,
    reg: &mut RuntimeRegistry<'_>,
    val: &Value,
    ty: &Type,
    dst_ptr: &str,
    tmp_id: &mut usize,
    refs: Refs<'_>,
) {
    let u = reg.usize_ty;
    if let Type::Ref(_, inner) = ty {
        match (refs, val) {
            (Refs::Within(control), Value::Ref { place, .. }) if place.scope == HOST_SCOPE => {
                let at = emit_host_place(ir, program, reg, control, place, tmp_id);
                let _ = writeln!(ir, "  store ptr {at}, ptr {dst_ptr}");
            }
            (Refs::Slots, _) => {
                let inner_ll = llvm_ty(program, inner, reg.usize_bits);
                let slot = format!("%href_{}", next_tmp(tmp_id));
                let zero = if **inner == Type::Bool {
                    "false"
                } else {
                    "zeroinitializer"
                };
                let _ = writeln!(ir, "  {slot} = alloca {inner_ll}");
                let _ = writeln!(ir, "  store {inner_ll} {zero}, ptr {slot}");
                emit_harness_value_into(ir, program, reg, val, inner, &slot, tmp_id, refs);
                let _ = writeln!(ir, "  store ptr {slot}, ptr {dst_ptr}");
            }
            // The oracle accepts no other answer, and the native driver is
            // given only the runs that the oracle ends.
            (Refs::Within(control), _) => panic!(
                "a host of `{}` answered {val} for a borrow, which names no place within an argument",
                control.name
            ),
            (Refs::Nothing, _) => panic!("{val} stands where no borrow is written"),
        }
        return;
    }
    match (val, ty.deref_type()) {
        (Value::Bool(b), Type::Bool) => {
            let _ = writeln!(
                ir,
                "  store i1 {}, ptr {dst_ptr}",
                if *b { "true" } else { "false" }
            );
        }
        (Value::Int(v), Type::Int(it)) => {
            let bits = int_bits(*it, reg.usize_bits);
            let raw = v.to_i128().unwrap_or(0) as u128;
            let masked = if bits >= 64 {
                raw as u64
            } else {
                (raw as u64) & ((1u64 << bits) - 1)
            };
            let ll = llvm_int_ty(*it, reg.usize_bits);
            let _ = writeln!(ir, "  store {ll} {masked}, ptr {dst_ptr}");
        }
        (Value::Int(v), Type::Bool) => {
            let _ = writeln!(
                ir,
                "  store i1 {}, ptr {dst_ptr}",
                if v.is_zero() { "false" } else { "true" }
            );
        }
        (Value::String(s), Type::String) => {
            let g = reg.intern_bytes(s.as_bytes());
            let n = s.len();
            let id = next_tmp(tmp_id);
            let _ = writeln!(
                ir,
                "  %hp0_{id} = getelementptr %vn2.string, ptr {dst_ptr}, i32 0, i32 0"
            );
            let _ = writeln!(
                ir,
                "  %hp1_{id} = getelementptr %vn2.string, ptr {dst_ptr}, i32 0, i32 1"
            );
            let _ = writeln!(
                ir,
                "  %hp2_{id} = getelementptr %vn2.string, ptr {dst_ptr}, i32 0, i32 2"
            );
            let _ = writeln!(ir, "  store ptr {g}, ptr %hp0_{id}");
            let _ = writeln!(ir, "  store {u} {n}, ptr %hp1_{id}");
            let _ = writeln!(ir, "  store {u} 0, ptr %hp2_{id}");
        }
        (Value::Resource { id, .. }, Type::Resource(_, _)) => {
            let idn = next_tmp(tmp_id);
            let _ = writeln!(ir, "  %hr_{idn} = inttoptr i64 {id} to ptr");
            let _ = writeln!(ir, "  store ptr %hr_{idn}, ptr {dst_ptr}");
        }
        (Value::Struct { fields, .. }, Type::Struct(sid, _)) => {
            let ll = format!("%vn2.struct.{sid}");
            for (fi, (fval, fparam)) in fields.iter().zip(&program.structs[*sid].fields).enumerate()
            {
                let id = next_tmp(tmp_id);
                let _ = writeln!(
                    ir,
                    "  %hsf_{id} = getelementptr {ll}, ptr {dst_ptr}, i32 0, i32 {fi}"
                );
                emit_harness_value_into(
                    ir,
                    program,
                    reg,
                    fval,
                    &fparam.ty,
                    &format!("%hsf_{id}"),
                    tmp_id,
                    refs,
                );
            }
        }
        (
            Value::Variant {
                constructor,
                fields,
                ..
            },
            Type::Variant(vid, _),
        ) => {
            if is_unit_variant(program, *vid) {
                let _ = writeln!(ir, "  store i32 {constructor}, ptr {dst_ptr}");
            } else {
                let ll = format!("%vn2.variant.{vid}");
                let _ = writeln!(ir, "  store {ll} zeroinitializer, ptr {dst_ptr}");
                let tid = next_tmp(tmp_id);
                let _ = writeln!(
                    ir,
                    "  %hv_t_{tid} = getelementptr {ll}, ptr {dst_ptr}, i32 0, i32 0"
                );
                let _ = writeln!(ir, "  store i32 {constructor}, ptr %hv_t_{tid}");
                if !fields.is_empty() {
                    let sub_ll = format!("%vn2.variant.{vid}.c{constructor}");
                    let _ = writeln!(
                        ir,
                        "  %hv_p_{tid} = getelementptr {ll}, ptr {dst_ptr}, i32 0, i32 1"
                    );
                    for (fi, (fval, fparam)) in fields
                        .iter()
                        .zip(&program.variants[*vid].constructors[*constructor].fields)
                        .enumerate()
                    {
                        let fid = next_tmp(tmp_id);
                        let _ = writeln!(
                            ir,
                            "  %hvf_{fid} = getelementptr {sub_ll}, ptr %hv_p_{tid}, i32 0, i32 {fi}"
                        );
                        emit_harness_value_into(
                            ir,
                            program,
                            reg,
                            fval,
                            &fparam.ty,
                            &format!("%hvf_{fid}"),
                            tmp_id,
                            refs,
                        );
                    }
                }
            }
        }
        (Value::Vector(items), Type::Vector(elem_ty)) => {
            if items.is_empty() {
                let _ = writeln!(ir, "  store %vn2.vec zeroinitializer, ptr {dst_ptr}");
            } else {
                reg.needed_libc = true;
                let e_ll = llvm_ty(program, elem_ty, reg.usize_bits);
                let n = items.len();
                let vid = next_tmp(tmp_id);
                let _ = writeln!(ir, "  %hsp_{vid} = getelementptr {e_ll}, ptr null, i32 1");
                let _ = writeln!(ir, "  %hst_{vid} = ptrtoint ptr %hsp_{vid} to i64");
                let _ = writeln!(ir, "  %hby_{vid} = mul i64 {n}, %hst_{vid}");
                let _ = writeln!(ir, "  %hbuf_{vid} = call ptr @malloc(i64 %hby_{vid})");
                for (i, item) in items.iter().enumerate() {
                    let eid = next_tmp(tmp_id);
                    let _ = writeln!(
                        ir,
                        "  %he_{eid} = getelementptr {e_ll}, ptr %hbuf_{vid}, i64 {i}"
                    );
                    emit_harness_value_into(
                        ir,
                        program,
                        reg,
                        item,
                        elem_ty,
                        &format!("%he_{eid}"),
                        tmp_id,
                        refs,
                    );
                }
                let _ = writeln!(
                    ir,
                    "  %hp0_{vid} = getelementptr %vn2.vec, ptr {dst_ptr}, i32 0, i32 0"
                );
                let _ = writeln!(
                    ir,
                    "  %hp1_{vid} = getelementptr %vn2.vec, ptr {dst_ptr}, i32 0, i32 1"
                );
                let _ = writeln!(
                    ir,
                    "  %hp2_{vid} = getelementptr %vn2.vec, ptr {dst_ptr}, i32 0, i32 2"
                );
                let _ = writeln!(ir, "  store ptr %hbuf_{vid}, ptr %hp0_{vid}");
                let _ = writeln!(ir, "  store {u} {n}, ptr %hp1_{vid}");
                let _ = writeln!(ir, "  store {u} {n}, ptr %hp2_{vid}");
            }
        }
        (Value::Map(entries), Type::Map(k_ty, v_ty)) => {
            if entries.is_empty() {
                let _ = writeln!(ir, "  store %vn2.map zeroinitializer, ptr {dst_ptr}");
            } else {
                reg.needed_libc = true;
                let mid = reg.intern_map(k_ty, v_ty);
                let entry_ty = format!("%vn2.map_entry.{mid}");
                let n = entries.len();
                let did = next_tmp(tmp_id);
                let _ = writeln!(
                    ir,
                    "  %msp_{did} = getelementptr {entry_ty}, ptr null, i32 1"
                );
                let _ = writeln!(ir, "  %mst_{did} = ptrtoint ptr %msp_{did} to i64");
                let _ = writeln!(ir, "  %mby_{did} = mul i64 {n}, %mst_{did}");
                let _ = writeln!(ir, "  %mbuf_{did} = call ptr @malloc(i64 %mby_{did})");
                for (i, (k, v)) in entries.iter().enumerate() {
                    let eid = next_tmp(tmp_id);
                    let _ = writeln!(
                        ir,
                        "  %me_{eid} = getelementptr {entry_ty}, ptr %mbuf_{did}, i64 {i}"
                    );
                    let _ = writeln!(
                        ir,
                        "  %mk_{eid} = getelementptr {entry_ty}, ptr %me_{eid}, i32 0, i32 0"
                    );
                    let _ = writeln!(
                        ir,
                        "  %mv_{eid} = getelementptr {entry_ty}, ptr %me_{eid}, i32 0, i32 1"
                    );
                    emit_harness_value_into(
                        ir,
                        program,
                        reg,
                        k,
                        k_ty,
                        &format!("%mk_{eid}"),
                        tmp_id,
                        refs,
                    );
                    emit_harness_value_into(
                        ir,
                        program,
                        reg,
                        v,
                        v_ty,
                        &format!("%mv_{eid}"),
                        tmp_id,
                        refs,
                    );
                }
                let _ = writeln!(
                    ir,
                    "  %mp0_{did} = getelementptr %vn2.map, ptr {dst_ptr}, i32 0, i32 0"
                );
                let _ = writeln!(
                    ir,
                    "  %mp1_{did} = getelementptr %vn2.map, ptr {dst_ptr}, i32 0, i32 1"
                );
                let _ = writeln!(
                    ir,
                    "  %mp2_{did} = getelementptr %vn2.map, ptr {dst_ptr}, i32 0, i32 2"
                );
                let _ = writeln!(ir, "  store ptr %mbuf_{did}, ptr %mp0_{did}");
                let _ = writeln!(ir, "  store {u} {n}, ptr %mp1_{did}");
                let _ = writeln!(ir, "  store {u} {n}, ptr %mp2_{did}");
            }
        }
        // A value of an outcome type that an entry is given or a host
        // answers with: the alternative and its payload, laid out as a
        // capture lays them out.
        (
            Value::Outcome {
                alternative,
                payload,
                ..
            },
            Type::Outcome(oid, _),
        ) => {
            if is_unit_outcome(program, *oid) {
                let _ = writeln!(ir, "  store i32 {alternative}, ptr {dst_ptr}");
            } else {
                let ll = format!("%vn2.outcome.{oid}");
                let _ = writeln!(ir, "  store {ll} zeroinitializer, ptr {dst_ptr}");
                let tid = next_tmp(tmp_id);
                let _ = writeln!(
                    ir,
                    "  %ho_t_{tid} = getelementptr {ll}, ptr {dst_ptr}, i32 0, i32 0"
                );
                let _ = writeln!(ir, "  store i32 {alternative}, ptr %ho_t_{tid}");
                if !payload.is_empty() {
                    let sub_ll = format!("%vn2.outcome.{oid}.a{alternative}");
                    let _ = writeln!(
                        ir,
                        "  %ho_p_{tid} = getelementptr {ll}, ptr {dst_ptr}, i32 0, i32 1"
                    );
                    for (fi, (fval, fparam)) in payload
                        .iter()
                        .zip(&program.outcomes[*oid].alternatives[*alternative].fields)
                        .enumerate()
                    {
                        let fid = next_tmp(tmp_id);
                        let _ = writeln!(
                            ir,
                            "  %hof_{fid} = getelementptr {sub_ll}, ptr %ho_p_{tid}, i32 0, i32 {fi}"
                        );
                        emit_harness_value_into(
                            ir,
                            program,
                            reg,
                            fval,
                            &fparam.ty,
                            &format!("%hof_{fid}"),
                            tmp_id,
                            refs,
                        );
                    }
                }
            }
        }
        _ => {}
    }
}

/// The address of the place that a host names within one of the arguments
/// of `control` ([E-Extern], `Value::within`), in its stub, whose arguments
/// are `%p0`, `%p1`, …. As `oracle::lent_within` takes them, the steps go
/// through the fields of a view to a borrow that it holds, and from there
/// into what the borrow refers to: a step from a place that holds a borrow
/// goes through the borrow. Only an answer that the oracle accepts reaches
/// the native driver, so every step is one that the place has.
fn emit_host_place(
    ir: &mut String,
    program: &Program,
    reg: &mut RuntimeRegistry<'_>,
    control: &Control,
    place: &RuntimePlace,
    tmp_id: &mut usize,
) -> String {
    let u = reg.usize_ty;
    // A borrow is passed as the place itself, and a view by its address.
    let mut at = format!("%p{}", place.var);
    let mut ty = control.parameters[place.var].ty.deref_type().clone();
    for step in &place.steps {
        if let Type::Ref(_, referent) = &ty {
            let id = next_tmp(tmp_id);
            let _ = writeln!(ir, "  %hpr_{id} = load ptr, ptr {at}");
            at = format!("%hpr_{id}");
            ty = (**referent).clone();
        }
        let id = next_tmp(tmp_id);
        ty = match (step, &ty) {
            (RuntimeStep::Field(index), Type::Struct(sid, _)) => {
                let _ = writeln!(
                    ir,
                    "  %hpf_{id} = getelementptr %vn2.struct.{sid}, ptr {at}, i32 0, i32 {index}"
                );
                program.structs[*sid].fields[*index].ty.clone()
            }
            (RuntimeStep::VariantField(constructor, index), Type::Variant(vid, _)) => {
                let _ = writeln!(
                    ir,
                    "  %hpp_{id} = getelementptr %vn2.variant.{vid}, ptr {at}, i32 0, i32 1"
                );
                let _ = writeln!(
                    ir,
                    "  %hpf_{id} = getelementptr %vn2.variant.{vid}.c{constructor}, ptr %hpp_{id}, i32 0, i32 {index}"
                );
                program.variants[*vid].constructors[*constructor].fields[*index]
                    .ty
                    .clone()
            }
            (RuntimeStep::Index(index), Type::Vector(element)) => {
                let e_ll = llvm_ty(program, element, reg.usize_bits);
                let _ = writeln!(
                    ir,
                    "  %hpd_{id} = getelementptr %vn2.vec, ptr {at}, i32 0, i32 0"
                );
                let _ = writeln!(ir, "  %hpb_{id} = load ptr, ptr %hpd_{id}");
                let _ = writeln!(
                    ir,
                    "  %hpf_{id} = getelementptr {e_ll}, ptr %hpb_{id}, {u} {index}"
                );
                (**element).clone()
            }
            (RuntimeStep::MapValue(key) | RuntimeStep::MapKey(key), Type::Map(k_ty, v_ty)) => {
                let mid = reg.intern_map(k_ty, v_ty);
                let k_ll = llvm_ty(program, k_ty, reg.usize_bits);
                let _ = writeln!(ir, "  %hpk_{id} = alloca {k_ll}");
                emit_harness_value_into(
                    ir,
                    program,
                    reg,
                    key,
                    k_ty,
                    &format!("%hpk_{id}"),
                    tmp_id,
                    Refs::Nothing,
                );
                let _ = writeln!(ir, "  %hpq_{id} = alloca i1");
                let _ = writeln!(
                    ir,
                    "  %hpi_{id} = call fastcc {u} @vn2_map_find_{mid}(ptr {at}, ptr %hpk_{id}, ptr %hpq_{id})"
                );
                if needs_drop(program, k_ty) {
                    let ktid = reg.intern_type(k_ty);
                    reg.require_drop(ktid);
                    let _ = writeln!(ir, "  call fastcc void @vn2_drop_{ktid}(ptr %hpk_{id})");
                }
                let _ = writeln!(
                    ir,
                    "  %hpd_{id} = getelementptr %vn2.map, ptr {at}, i32 0, i32 0"
                );
                let _ = writeln!(ir, "  %hpb_{id} = load ptr, ptr %hpd_{id}");
                let _ = writeln!(
                    ir,
                    "  %hpe_{id} = getelementptr %vn2.map_entry.{mid}, ptr %hpb_{id}, {u} %hpi_{id}"
                );
                let (field, ty) = match step {
                    RuntimeStep::MapKey(_) => (0, k_ty),
                    _ => (1, v_ty),
                };
                let _ = writeln!(
                    ir,
                    "  %hpf_{id} = getelementptr %vn2.map_entry.{mid}, ptr %hpe_{id}, i32 0, i32 {field}"
                );
                (**ty).clone()
            }
            (step, ty) => panic!(
                "a host named the step {step:?} within argument {} of `{}`, where the place has the type {ty}",
                place.var, control.name
            ),
        };
        at = format!("%hpf_{id}");
    }
    at
}

fn emit_printers(
    out: &mut String,
    program: &Program,
    reg: &RuntimeRegistry<'_>,
    used_print_types: &BTreeSet<usize>,
) {
    let u = reg.usize_ty;
    let _ = writeln!(out, "declare i32 @printf(ptr, ...)");
    let _ = writeln!(out, "declare i32 @fflush(ptr)");
    let _ = writeln!(out, "declare i32 @putchar(i32)");
    let _ = writeln!(out, "declare void @exit(i32)");
    let _ = writeln!(
        out,
        "@h_fmt_true = private unnamed_addr constant [5 x i8] c\"true\\00\""
    );
    let _ = writeln!(
        out,
        "@h_fmt_false = private unnamed_addr constant [6 x i8] c\"false\\00\""
    );
    let _ = writeln!(
        out,
        "@h_fmt_u64 = private unnamed_addr constant [5 x i8] c\"%llu\\00\""
    );
    let _ = writeln!(
        out,
        "@h_fmt_i64 = private unnamed_addr constant [5 x i8] c\"%lld\\00\""
    );
    let _ = writeln!(
        out,
        "@h_fmt_sep = private unnamed_addr constant [3 x i8] c\", \\00\""
    );
    let _ = writeln!(
        out,
        "@h_fmt_map_sep = private unnamed_addr constant [6 x i8] c\" |-> \\00\""
    );
    let _ = writeln!(
        out,
        "@h_fmt_res = private unnamed_addr constant [8 x i8] c\"%s#%llu\\00\""
    );
    let _ = writeln!(
        out,
        "@h_fmt_rel_line = private unnamed_addr constant [39 x i8] c\"EVENT %s.release(%s#%llu) -> released\\0A\\00\""
    );
    let _ = writeln!(
        out,
        "@h_fmt_s = private unnamed_addr constant [3 x i8] c\"%s\\00\""
    );
    let _ = writeln!(
        out,
        "@h_fmt_host_fail = private unnamed_addr constant [13 x i8] c\"HOST_FAILED\\0A\\00\""
    );
    let _ = writeln!(out);

    // @vn2_print_escaped_str(ptr %s)
    let _ = writeln!(
        out,
        "define internal void @vn2_print_escaped_str(ptr %s) nounwind {{"
    );
    let _ = writeln!(out, "entry:");
    let _ = writeln!(out, "  call i32 @putchar(i32 34)");
    let _ = writeln!(out, "  %v = load %vn2.string, ptr %s");
    let _ = writeln!(out, "  %p = extractvalue %vn2.string %v, 0");
    let _ = writeln!(out, "  %len = extractvalue %vn2.string %v, 1");
    let _ = writeln!(out, "  %i_slot = alloca {u}");
    let _ = writeln!(out, "  store {u} 0, ptr %i_slot");
    let _ = writeln!(out, "  br label %lp");
    let _ = writeln!(out, "lp:");
    let _ = writeln!(out, "  %i = load {u}, ptr %i_slot");
    let _ = writeln!(out, "  %more = icmp ult {u} %i, %len");
    let _ = writeln!(out, "  br i1 %more, label %body, label %done");
    let _ = writeln!(out, "body:");
    let _ = writeln!(out, "  %cp = getelementptr i8, ptr %p, {u} %i");
    let _ = writeln!(out, "  %c8 = load i8, ptr %cp");
    let _ = writeln!(out, "  %c = zext i8 %c8 to i32");
    let _ = writeln!(
        out,
        "  switch i32 %c, label %normal [ i32 34, label %eq i32 92, label %eb i32 10, label %en i32 13, label %er i32 9, label %et ]"
    );
    let _ = writeln!(out, "eq:");
    let _ = writeln!(out, "  call i32 @putchar(i32 92)");
    let _ = writeln!(out, "  call i32 @putchar(i32 34)");
    let _ = writeln!(out, "  br label %inc");
    let _ = writeln!(out, "eb:");
    let _ = writeln!(out, "  call i32 @putchar(i32 92)");
    let _ = writeln!(out, "  call i32 @putchar(i32 92)");
    let _ = writeln!(out, "  br label %inc");
    let _ = writeln!(out, "en:");
    let _ = writeln!(out, "  call i32 @putchar(i32 92)");
    let _ = writeln!(out, "  call i32 @putchar(i32 110)");
    let _ = writeln!(out, "  br label %inc");
    let _ = writeln!(out, "er:");
    let _ = writeln!(out, "  call i32 @putchar(i32 92)");
    let _ = writeln!(out, "  call i32 @putchar(i32 114)");
    let _ = writeln!(out, "  br label %inc");
    let _ = writeln!(out, "et:");
    let _ = writeln!(out, "  call i32 @putchar(i32 92)");
    let _ = writeln!(out, "  call i32 @putchar(i32 116)");
    let _ = writeln!(out, "  br label %inc");
    let _ = writeln!(out, "normal:");
    let _ = writeln!(out, "  call i32 @putchar(i32 %c)");
    let _ = writeln!(out, "  br label %inc");
    let _ = writeln!(out, "inc:");
    let _ = writeln!(out, "  %ni = add {u} %i, 1");
    let _ = writeln!(out, "  store {u} %ni, ptr %i_slot");
    let _ = writeln!(out, "  br label %lp");
    let _ = writeln!(out, "done:");
    let _ = writeln!(out, "  call i32 @putchar(i32 34)");
    let _ = writeln!(out, "  ret void");
    let _ = writeln!(out, "}}\n");

    for &tid in used_print_types {
        let ty = &reg.registered_types[tid];
        let ll = llvm_ty(program, ty, reg.usize_bits);
        let _ = writeln!(
            out,
            "define internal void @vn2_print_val_{tid}(ptr %p) nounwind {{"
        );
        let _ = writeln!(out, "entry:");
        match ty {
            Type::Bool => {
                let _ = writeln!(out, "  %v = load i1, ptr %p");
                let _ = writeln!(
                    out,
                    "  %s = select i1 %v, ptr @h_fmt_true, ptr @h_fmt_false"
                );
                let _ = writeln!(out, "  call i32 (ptr, ...) @printf(ptr @h_fmt_s, ptr %s)");
            }
            Type::Int(it) => {
                let _ = writeln!(out, "  %v = load {ll}, ptr %p");
                let ext = if it.is_signed() { "sext" } else { "zext" };
                let val64 = if ll == "i64" {
                    "%v".to_string()
                } else {
                    let _ = writeln!(out, "  %v64 = {ext} {ll} %v to i64");
                    "%v64".to_string()
                };
                let fmt = if it.is_signed() {
                    "@h_fmt_i64"
                } else {
                    "@h_fmt_u64"
                };
                let _ = writeln!(out, "  call i32 (ptr, ...) @printf(ptr {fmt}, i64 {val64})");
            }
            Type::String => {
                let _ = writeln!(out, "  call void @vn2_print_escaped_str(ptr %p)");
            }
            Type::Resource(_, rname) => {
                let g = &reg.str_literal_map[rname.as_bytes()];
                let _ = writeln!(out, "  %h = load ptr, ptr %p");
                let _ = writeln!(out, "  %id = ptrtoint ptr %h to i64");
                let _ = writeln!(
                    out,
                    "  call i32 (ptr, ...) @printf(ptr @h_fmt_res, ptr {g}, i64 %id)"
                );
            }
            Type::Struct(sid, sname) => {
                let g = &reg.str_literal_map[sname.as_bytes()];
                let _ = writeln!(out, "  call i32 (ptr, ...) @printf(ptr @h_fmt_s, ptr {g})");
                let _ = writeln!(out, "  call i32 @putchar(i32 32)");
                let _ = writeln!(out, "  call i32 @putchar(i32 123)");
                for (fi, f) in program.structs[*sid].fields.iter().enumerate() {
                    if fi > 0 {
                        let _ = writeln!(out, "  call i32 (ptr, ...) @printf(ptr @h_fmt_sep)");
                    }
                    let ftid = reg.type_ids[f.ty.deref_type()];
                    let _ = writeln!(
                        out,
                        "  %fp_{fi} = getelementptr {ll}, ptr %p, i32 0, i32 {fi}"
                    );
                    if matches!(f.ty, Type::Ref(_, _)) {
                        let _ = writeln!(out, "  %fpd_{fi} = load ptr, ptr %fp_{fi}");
                        let _ = writeln!(out, "  call void @vn2_print_val_{ftid}(ptr %fpd_{fi})");
                    } else {
                        let _ = writeln!(out, "  call void @vn2_print_val_{ftid}(ptr %fp_{fi})");
                    }
                }
                let _ = writeln!(out, "  call i32 @putchar(i32 125)");
            }
            Type::Variant(vid, vname) => {
                let vg = &reg.str_literal_map[vname.as_bytes()];
                let unit = is_unit_variant(program, *vid);
                if unit {
                    let _ = writeln!(out, "  %tag = load i32, ptr %p");
                } else {
                    let _ = writeln!(out, "  %tp = getelementptr {ll}, ptr %p, i32 0, i32 0");
                    let _ = writeln!(out, "  %tag = load i32, ptr %tp");
                }
                let mut cases = String::new();
                for k in 0..program.variants[*vid].constructors.len() {
                    let _ = write!(cases, " i32 {k}, label %c_{k}");
                }
                let _ = writeln!(out, "  switch i32 %tag, label %done [ {cases} ]");
                for (k, c) in program.variants[*vid].constructors.iter().enumerate() {
                    let cg = &reg.str_literal_map[c.name.as_bytes()];
                    let _ = writeln!(out, "c_{k}:");
                    let _ = writeln!(out, "  call i32 (ptr, ...) @printf(ptr @h_fmt_s, ptr {vg})");
                    let _ = writeln!(out, "  call i32 @putchar(i32 46)");
                    let _ = writeln!(out, "  call i32 (ptr, ...) @printf(ptr @h_fmt_s, ptr {cg})");
                    if !c.fields.is_empty() {
                        let _ = writeln!(out, "  call i32 @putchar(i32 32)");
                        let _ = writeln!(out, "  call i32 @putchar(i32 123)");
                        let sub_ll = format!("%vn2.variant.{vid}.c{k}");
                        let _ =
                            writeln!(out, "  %pp_{k} = getelementptr {ll}, ptr %p, i32 0, i32 1");
                        for (fi, f) in c.fields.iter().enumerate() {
                            if fi > 0 {
                                let _ =
                                    writeln!(out, "  call i32 (ptr, ...) @printf(ptr @h_fmt_sep)");
                            }
                            let ftid = reg.type_ids[f.ty.deref_type()];
                            let _ = writeln!(
                                out,
                                "  %cf_{k}_{fi} = getelementptr {sub_ll}, ptr %pp_{k}, i32 0, i32 {fi}"
                            );
                            let _ = writeln!(
                                out,
                                "  call void @vn2_print_val_{ftid}(ptr %cf_{k}_{fi})"
                            );
                        }
                        let _ = writeln!(out, "  call i32 @putchar(i32 125)");
                    }
                    let _ = writeln!(out, "  br label %done");
                }
                let _ = writeln!(out, "done:");
            }
            Type::Outcome(oid, _) => {
                let og = &reg.str_literal_map[b"outcome".as_slice()];
                let unit = is_unit_outcome(program, *oid);
                if unit {
                    let _ = writeln!(out, "  %tag = load i32, ptr %p");
                } else {
                    let _ = writeln!(out, "  %tp = getelementptr {ll}, ptr %p, i32 0, i32 0");
                    let _ = writeln!(out, "  %tag = load i32, ptr %tp");
                }
                let mut cases = String::new();
                for k in 0..program.outcomes[*oid].alternatives.len() {
                    let _ = write!(cases, " i32 {k}, label %a_{k}");
                }
                let _ = writeln!(out, "  switch i32 %tag, label %done [ {cases} ]");
                for (k, a) in program.outcomes[*oid].alternatives.iter().enumerate() {
                    let ag = &reg.str_literal_map[a.name.as_bytes()];
                    let _ = writeln!(out, "a_{k}:");
                    let _ = writeln!(out, "  call i32 (ptr, ...) @printf(ptr @h_fmt_s, ptr {og})");
                    let _ = writeln!(out, "  call i32 @putchar(i32 46)");
                    let _ = writeln!(out, "  call i32 (ptr, ...) @printf(ptr @h_fmt_s, ptr {ag})");
                    let _ = writeln!(out, "  call i32 @putchar(i32 32)");
                    let _ = writeln!(out, "  call i32 @putchar(i32 123)");
                    if !a.fields.is_empty() {
                        let sub_ll = format!("%vn2.outcome.{oid}.a{k}");
                        let _ =
                            writeln!(out, "  %pp_{k} = getelementptr {ll}, ptr %p, i32 0, i32 1");
                        for (fi, f) in a.fields.iter().enumerate() {
                            if fi > 0 {
                                let _ =
                                    writeln!(out, "  call i32 (ptr, ...) @printf(ptr @h_fmt_sep)");
                            }
                            let ftid = reg.type_ids[f.ty.deref_type()];
                            let _ = writeln!(
                                out,
                                "  %af_{k}_{fi} = getelementptr {sub_ll}, ptr %pp_{k}, i32 0, i32 {fi}"
                            );
                            let _ = writeln!(
                                out,
                                "  call void @vn2_print_val_{ftid}(ptr %af_{k}_{fi})"
                            );
                        }
                    }
                    let _ = writeln!(out, "  call i32 @putchar(i32 125)");
                    let _ = writeln!(out, "  br label %done");
                }
                let _ = writeln!(out, "done:");
            }
            Type::Vector(elem) => {
                let etid = reg.type_ids[elem.deref_type()];
                let e_ll = llvm_ty(program, elem, reg.usize_bits);
                let _ = writeln!(out, "  call i32 @putchar(i32 91)");
                let _ = writeln!(out, "  %v = load %vn2.vec, ptr %p");
                let _ = writeln!(out, "  %data = extractvalue %vn2.vec %v, 0");
                let _ = writeln!(out, "  %len = extractvalue %vn2.vec %v, 1");
                let _ = writeln!(out, "  %i_s = alloca {u}");
                let _ = writeln!(out, "  store {u} 0, ptr %i_s");
                let _ = writeln!(out, "  br label %lp");
                let _ = writeln!(out, "lp:");
                let _ = writeln!(out, "  %i = load {u}, ptr %i_s");
                let _ = writeln!(out, "  %more = icmp ult {u} %i, %len");
                let _ = writeln!(out, "  br i1 %more, label %elem, label %done");
                let _ = writeln!(out, "elem:");
                let _ = writeln!(out, "  %nz = icmp ne {u} %i, 0");
                let _ = writeln!(out, "  br i1 %nz, label %sep, label %pr");
                let _ = writeln!(out, "sep:");
                let _ = writeln!(out, "  call i32 (ptr, ...) @printf(ptr @h_fmt_sep)");
                let _ = writeln!(out, "  br label %pr");
                let _ = writeln!(out, "pr:");
                let _ = writeln!(out, "  %ep = getelementptr {e_ll}, ptr %data, {u} %i");
                let _ = writeln!(out, "  call void @vn2_print_val_{etid}(ptr %ep)");
                let _ = writeln!(out, "  %ni = add {u} %i, 1");
                let _ = writeln!(out, "  store {u} %ni, ptr %i_s");
                let _ = writeln!(out, "  br label %lp");
                let _ = writeln!(out, "done:");
                let _ = writeln!(out, "  call i32 @putchar(i32 93)");
            }
            Type::Map(k, v) => {
                let ktid = reg.type_ids[k.deref_type()];
                let vtid = reg.type_ids[v.deref_type()];
                let mid = reg.map_ids[&((**k).clone(), (**v).clone())];
                let entry_ty = format!("%vn2.map_entry.{mid}");
                let _ = writeln!(out, "  call i32 @putchar(i32 123)");
                let _ = writeln!(out, "  %m = load %vn2.map, ptr %p");
                let _ = writeln!(out, "  %data = extractvalue %vn2.map %m, 0");
                let _ = writeln!(out, "  %len = extractvalue %vn2.map %m, 1");
                let _ = writeln!(out, "  %i_s = alloca {u}");
                let _ = writeln!(out, "  store {u} 0, ptr %i_s");
                let _ = writeln!(out, "  br label %lp");
                let _ = writeln!(out, "lp:");
                let _ = writeln!(out, "  %i = load {u}, ptr %i_s");
                let _ = writeln!(out, "  %more = icmp ult {u} %i, %len");
                let _ = writeln!(out, "  br i1 %more, label %elem, label %done");
                let _ = writeln!(out, "elem:");
                let _ = writeln!(out, "  %nz = icmp ne {u} %i, 0");
                let _ = writeln!(out, "  br i1 %nz, label %sep, label %pr");
                let _ = writeln!(out, "sep:");
                let _ = writeln!(out, "  call i32 (ptr, ...) @printf(ptr @h_fmt_sep)");
                let _ = writeln!(out, "  br label %pr");
                let _ = writeln!(out, "pr:");
                let _ = writeln!(out, "  %ep = getelementptr {entry_ty}, ptr %data, {u} %i");
                let _ = writeln!(
                    out,
                    "  %kp = getelementptr {entry_ty}, ptr %ep, i32 0, i32 0"
                );
                let _ = writeln!(
                    out,
                    "  %vp = getelementptr {entry_ty}, ptr %ep, i32 0, i32 1"
                );
                let _ = writeln!(out, "  call void @vn2_print_val_{ktid}(ptr %kp)");
                let _ = writeln!(out, "  call i32 (ptr, ...) @printf(ptr @h_fmt_map_sep)");
                let _ = writeln!(out, "  call void @vn2_print_val_{vtid}(ptr %vp)");
                let _ = writeln!(out, "  %ni = add {u} %i, 1");
                let _ = writeln!(out, "  store {u} %ni, ptr %i_s");
                let _ = writeln!(out, "  br label %lp");
                let _ = writeln!(out, "done:");
                let _ = writeln!(out, "  call i32 @putchar(i32 125)");
            }
            _ => {}
        }
        let _ = writeln!(out, "  ret void");
        let _ = writeln!(out, "}}\n");
    }
}

fn register_print_type(reg: &mut RuntimeRegistry<'_>, ty: &Type, used: &mut BTreeSet<usize>) {
    let tid = reg.intern_type(ty);
    if !used.insert(tid) {
        return;
    }
    let program = reg.program;
    match ty.deref_type() {
        Type::Resource(_, name) => {
            reg.intern_bytes(name.as_bytes());
        }
        Type::Struct(sid, name) => {
            reg.intern_bytes(name.as_bytes());
            for f in &program.structs[*sid].fields {
                register_print_type(reg, &f.ty, used);
            }
        }
        Type::Variant(vid, name) => {
            reg.intern_bytes(name.as_bytes());
            for c in &program.variants[*vid].constructors {
                reg.intern_bytes(c.name.as_bytes());
                for f in &c.fields {
                    register_print_type(reg, &f.ty, used);
                }
            }
        }
        Type::Outcome(oid, _) => {
            reg.intern_bytes(b"outcome");
            for a in &program.outcomes[*oid].alternatives {
                reg.intern_bytes(a.name.as_bytes());
                for f in &a.fields {
                    register_print_type(reg, &f.ty, used);
                }
            }
        }
        Type::Vector(elem) => {
            register_print_type(reg, elem, used);
        }
        Type::Map(k, v) => {
            reg.intern_map(k, v);
            register_print_type(reg, k, used);
            register_print_type(reg, v, used);
        }
        _ => {}
    }
}

/// Emits a complete runnable LLVM IR program that executes `specs` natively
/// and prints each run's trace and outcome in Villanelle syntax.
pub fn emit_native_harness_llvm(
    program: &Program,
    specs: &[NativeRunSpec],
    usize_bits: u32,
) -> Result<String, String> {
    let mut reg = RuntimeRegistry::new(program, usize_bits);
    let term_tys = compute_control_terminate_tys(program);
    let mut body_out = String::new();

    // 1. Named boundaries, functions, and defined controls into `body_out`, sharing `reg`.
    let awaited = defined_await_targets(program).collect::<BTreeSet<_>>();
    emit_await_continuations(&mut body_out, program, &term_tys, usize_bits, &awaited);
    emit_program_bodies(&mut body_out, program, &mut reg, &term_tys, usize_bits)?;

    // 2. Register harness print types & string literals into the SAME `reg`.
    let mut used_print = BTreeSet::new();
    for ctrl in &program.controls {
        reg.intern_bytes(ctrl.name.as_bytes());
        for p in &ctrl.parameters {
            register_print_type(&mut reg, &p.ty, &mut used_print);
        }
        for a in &ctrl.contract {
            reg.intern_bytes(a.name.as_bytes());
            for f in &a.fields {
                register_print_type(&mut reg, &f.ty, &mut used_print);
            }
        }
    }
    for tty in term_tys.iter().flatten() {
        register_print_type(&mut reg, tty, &mut used_print);
    }
    for res in &program.resources {
        if res.on_fault_release {
            reg.intern_bytes(res.name.as_bytes());
        }
    }
    register_print_type(&mut reg, &Type::String, &mut used_print);

    // 3. Build harness externs & `@main`.
    let mut flat_ctrl_ids: Vec<i64> = Vec::new();
    let mut per_ctrl_answers: HashMap<ControlId, Vec<(usize, &Answer)>> = HashMap::new();
    let mut run_offsets: Vec<(usize, usize)> = Vec::new();
    for spec in specs {
        let start = flat_ctrl_ids.len();
        for (ctrl_name, ans) in &spec.answers {
            let cid = program.control(ctrl_name).expect("known extern control");
            let idx = flat_ctrl_ids.len();
            flat_ctrl_ids.push(cid as i64);
            per_ctrl_answers.entry(cid).or_default().push((idx, ans));
        }
        run_offsets.push((start, flat_ctrl_ids.len()));
    }

    let mut h_tmp = 0usize;
    let mut ext_code = String::new();
    let picks_turns = !awaited.is_empty() || tasks::uses_sets(program);
    if picks_turns {
        ext_code.push_str(
            "@vn2_turn_ptr = internal global ptr null
@vn2_turn_left = internal global i64 0

define i64 @vn2_pick_turn(i64 %ready_count) {
  %left = load i64, ptr @vn2_turn_left
  %default = icmp eq i64 %left, 0
  br i1 %default, label %first, label %scripted
first:
  ret i64 0
scripted:
  %ptr = load ptr, ptr @vn2_turn_ptr
  %choice = load i64, ptr %ptr
  %next = getelementptr i64, ptr %ptr, i64 1
  %remaining = sub i64 %left, 1
  store ptr %next, ptr @vn2_turn_ptr
  store i64 %remaining, ptr @vn2_turn_left
  ret i64 %choice
}

",
        );
    }
    for res in &program.resources {
        if res.on_fault_release {
            let rg = reg.str_literal_map[res.name.as_bytes()].clone();
            let _ = writeln!(
                ext_code,
                "define void @vn2_release_{}(ptr %h) nounwind {{",
                res.name
            );
            let _ = writeln!(ext_code, "entry:");
            let _ = writeln!(ext_code, "  %id = ptrtoint ptr %h to i64");
            let _ = writeln!(
                ext_code,
                "  call i32 (ptr, ...) @printf(ptr @h_fmt_rel_line, ptr {rg}, ptr {rg}, i64 %id)"
            );
            let _ = writeln!(ext_code, "  ret void");
            let _ = writeln!(ext_code, "}}\n");
        }
    }
    if has_emit_builtin(program) {
        let _ = writeln!(
            ext_code,
            "define void @vn2_builtin_emit(ptr %s) nounwind {{"
        );
        let _ = writeln!(ext_code, "entry:");
        let _ = writeln!(
            ext_code,
            "  call i32 (ptr, ...) @printf(ptr @h_fmt_emit_pre)"
        );
        let _ = writeln!(ext_code, "  call void @vn2_print_escaped_str(ptr %s)");
        let _ = writeln!(
            ext_code,
            "  call i32 (ptr, ...) @printf(ptr @h_fmt_emit_suf)"
        );
        let _ = writeln!(ext_code, "  ret void");
        let _ = writeln!(ext_code, "}}\n");
    }

    for (ctrl_id, control) in program.controls.iter().enumerate() {
        if control.body.is_some() {
            continue;
        }
        let mut params = Vec::new();
        for (idx, param) in control.parameters.iter().enumerate() {
            params.push(format!(
                "{} %p{idx}",
                c_abi_llvm_ty(program, &param.ty, usize_bits)
            ));
        }
        for (alt_idx, alt) in control.contract.iter().enumerate() {
            for (field_idx, _) in alt.fields.iter().enumerate() {
                params.push(format!("ptr %out_{alt_idx}_{field_idx}"));
            }
        }
        if control.faults {
            params.push("ptr %out_fault".to_string());
        }
        let _ = writeln!(
            ext_code,
            "define i32 @vn2_ext_{}({}) nounwind {{",
            control.name,
            params.join(", ")
        );
        let _ = writeln!(ext_code, "entry:");

        if let Some(op_kind) = checked_arith_kind(&control.name)
            && control.parameters.len() == 2
            && control.contract.len() == 2
            && control.contract[0].fields.len() == 1
            && control.contract[1].fields.is_empty()
            && let Type::Int(res_int_ty) = control.contract[0].fields[0].ty
        {
            let _ = writeln!(ext_code, "  %arith_on = load i1, ptr @use_arith");
            let _ = writeln!(
                ext_code,
                "  br i1 %arith_on, label %do_arith, label %from_script"
            );
            let _ = writeln!(ext_code, "do_arith:");
            let p0_ty = &control.parameters[0].ty;
            let p1_ty = &control.parameters[1].ty;
            let p0_ll = c_abi_llvm_ty(program, p0_ty, usize_bits);
            let p1_ll = c_abi_llvm_ty(program, p1_ty, usize_bits);
            let ext0 = if matches!(p0_ty, Type::Int(t) if t.is_signed()) {
                "sext"
            } else {
                "zext"
            };
            let ext1 = if matches!(p1_ty, Type::Int(t) if t.is_signed()) {
                "sext"
            } else {
                "zext"
            };
            let _ = writeln!(ext_code, "  %a128 = {ext0} {p0_ll} %p0 to i128");
            let _ = writeln!(ext_code, "  %b128 = {ext1} {p1_ll} %p1 to i128");
            if op_kind == "checked_div" || op_kind == "checked_rem" {
                let _ = writeln!(ext_code, "  %z = icmp eq i128 %b128, 0");
                let _ = writeln!(ext_code, "  br i1 %z, label %host_fail, label %div_ok");
                let _ = writeln!(ext_code, "div_ok:");
            }
            let arith_instr = match op_kind {
                "checked_add" => "add",
                "checked_sub" => "sub",
                "checked_mul" => "mul",
                "checked_div" => "sdiv",
                "checked_rem" => "srem",
                _ => unreachable!(),
            };
            let _ = writeln!(ext_code, "  %res128 = {arith_instr} i128 %a128, %b128");
            let usize_max = Int::power_of_two(usize_bits).minus(&Int::from_u64(1));
            let (lo, hi) = res_int_ty.bounds(&usize_max);
            let lo_i128 = lo.to_i128().unwrap();
            let hi_i128 = hi.to_i128().unwrap();
            let _ = writeln!(ext_code, "  %ge_lo = icmp sge i128 %res128, {lo_i128}");
            let _ = writeln!(ext_code, "  %le_hi = icmp sle i128 %res128, {hi_i128}");
            let _ = writeln!(ext_code, "  %fits = and i1 %ge_lo, %le_hi");
            let _ = writeln!(
                ext_code,
                "  br i1 %fits, label %arith_fits, label %arith_fails"
            );
            let _ = writeln!(ext_code, "arith_fits:");
            let res_ll = c_abi_llvm_ty(program, &Type::Int(res_int_ty), usize_bits);
            let _ = writeln!(ext_code, "  %trunc_res = trunc i128 %res128 to {res_ll}");
            let _ = writeln!(ext_code, "  store {res_ll} %trunc_res, ptr %out_0_0");
            let _ = writeln!(ext_code, "  ret i32 0");
            let _ = writeln!(ext_code, "arith_fails:");
            let _ = writeln!(ext_code, "  ret i32 1");
            let _ = writeln!(ext_code, "from_script:");
        }

        let _ = writeln!(ext_code, "  %pos = load i64, ptr @script_pos");
        let _ = writeln!(ext_code, "  %end = load i64, ptr @script_end");
        let _ = writeln!(ext_code, "  %has = icmp slt i64 %pos, %end");
        let _ = writeln!(ext_code, "  br i1 %has, label %dispatch, label %host_fail");
        let _ = writeln!(ext_code, "host_fail:");
        let _ = writeln!(
            ext_code,
            "  call i32 (ptr, ...) @printf(ptr @h_fmt_host_fail)"
        );
        let _ = writeln!(ext_code, "  call void @exit(i32 0)");
        let _ = writeln!(ext_code, "  unreachable");
        let _ = writeln!(ext_code, "dispatch:");
        let answers = per_ctrl_answers
            .get(&ctrl_id)
            .map(|v| v.as_slice())
            .unwrap_or(&[]);
        let mut sw = String::new();
        for (idx, _) in answers {
            let _ = write!(sw, " i64 {idx}, label %ans_{idx}");
        }
        let _ = writeln!(ext_code, "  switch i64 %pos, label %host_fail [ {sw} ]");

        let pure = control.is_pure(program);
        let ctrl_g = reg.str_literal_map[control.name.as_bytes()].clone();
        for (idx, ans) in answers {
            let _ = writeln!(ext_code, "ans_{idx}:");
            let _ = writeln!(ext_code, "  %npos_{idx} = add i64 %pos, 1");
            let _ = writeln!(ext_code, "  store i64 %npos_{idx}, ptr @script_pos");
            let alt_idx = control
                .contract
                .iter()
                .position(|a| a.name == ans.alternative)
                .expect("known alternative");
            let alt = &control.contract[alt_idx];
            // The event holds the arguments as they were at the call, so
            // they are written out before the host writes behind any.
            if !pure {
                let _ = writeln!(
                    ext_code,
                    "  call i32 (ptr, ...) @printf(ptr @h_fmt_ev_hdr, ptr {ctrl_g})"
                );
                for (pi, param) in control.parameters.iter().enumerate() {
                    if pi > 0 {
                        let _ = writeln!(ext_code, "  call i32 (ptr, ...) @printf(ptr @h_fmt_sep)");
                    }
                    let ptid = reg.type_ids[param.ty.deref_type()];
                    if matches!(param.ty, Type::Ref(_, _)) {
                        // The place itself, a `bool` among the rest.
                        let _ = writeln!(ext_code, "  call void @vn2_print_val_{ptid}(ptr %p{pi})");
                    } else if param.ty == Type::Bool {
                        let id = h_tmp;
                        h_tmp += 1;
                        let _ = writeln!(ext_code, "  %pb_{id} = icmp ne i8 %p{pi}, 0");
                        let _ = writeln!(ext_code, "  %pbt_{id} = alloca i1");
                        let _ = writeln!(ext_code, "  store i1 %pb_{id}, ptr %pbt_{id}");
                        let _ =
                            writeln!(ext_code, "  call void @vn2_print_val_{ptid}(ptr %pbt_{id})");
                    } else if is_c_scalar_by_val(program, &param.ty) {
                        let ll = llvm_ty(program, &param.ty, usize_bits);
                        let id = h_tmp;
                        h_tmp += 1;
                        let _ = writeln!(ext_code, "  %pt_{id} = alloca {ll}");
                        let _ = writeln!(ext_code, "  store {ll} %p{pi}, ptr %pt_{id}");
                        let _ =
                            writeln!(ext_code, "  call void @vn2_print_val_{ptid}(ptr %pt_{id})");
                    } else {
                        // An aggregate, passed by its address.
                        let _ = writeln!(ext_code, "  call void @vn2_print_val_{ptid}(ptr %p{pi})");
                    }
                }
            }
            // [E-Extern]: what the host leaves behind each argument lent
            // exclusively is written there, the value it replaces released,
            // before the borrows of the payload are made. Nothing is written
            // behind a value of kind `must`: the host leaves it as it was.
            for (position, value) in &ans.writes {
                let Type::Ref(BorrowMode::Exclusive, referent) = &control.parameters[*position].ty
                else {
                    panic!("a host writes only behind an argument lent exclusively");
                };
                if program.kind(referent) == Kind::Must {
                    continue;
                }
                let behind = format!("%p{position}");
                if !needs_drop(program, referent) {
                    emit_harness_value_into(
                        &mut ext_code,
                        program,
                        &mut reg,
                        value,
                        referent,
                        &behind,
                        &mut h_tmp,
                        Refs::Nothing,
                    );
                    continue;
                }
                // The new value is made while the old one is still held,
                // so that the two never share an address: a borrow left
                // pointing into the old one does not find the new one there.
                let ll = llvm_ty(program, referent, usize_bits);
                let id = next_tmp(&mut h_tmp);
                let _ = writeln!(ext_code, "  %hwn_{id} = alloca {ll}");
                emit_harness_value_into(
                    &mut ext_code,
                    program,
                    &mut reg,
                    value,
                    referent,
                    &format!("%hwn_{id}"),
                    &mut h_tmp,
                    Refs::Nothing,
                );
                let rtid = reg.intern_type(referent);
                reg.require_drop(rtid);
                let _ = writeln!(
                    ext_code,
                    "  call fastcc void @vn2_drop_{rtid}(ptr {behind})"
                );
                let _ = writeln!(ext_code, "  %hwv_{id} = load {ll}, ptr %hwn_{id}");
                let _ = writeln!(ext_code, "  store {ll} %hwv_{id}, ptr {behind}");
            }
            for (fi, (val, field)) in ans.payload.iter().zip(&alt.fields).enumerate() {
                if field.ty == Type::Bool {
                    let b = matches!(val, Value::Bool(true));
                    let _ = writeln!(
                        ext_code,
                        "  store i8 {}, ptr %out_{alt_idx}_{fi}",
                        i32::from(b)
                    );
                } else {
                    emit_harness_value_into(
                        &mut ext_code,
                        program,
                        &mut reg,
                        val,
                        &field.ty,
                        &format!("%out_{alt_idx}_{fi}"),
                        &mut h_tmp,
                        Refs::Within(control),
                    );
                }
            }
            if !pure {
                let alt_g = reg.str_literal_map[alt.name.as_bytes()].clone();
                let _ = writeln!(
                    ext_code,
                    "  call i32 (ptr, ...) @printf(ptr @h_fmt_ev_mid, ptr {alt_g})"
                );
                let _ = writeln!(ext_code, "  call i32 @putchar(i32 32)");
                let _ = writeln!(ext_code, "  call i32 @putchar(i32 123)");
                for (fi, field) in alt.fields.iter().enumerate() {
                    if fi > 0 {
                        let _ = writeln!(ext_code, "  call i32 (ptr, ...) @printf(ptr @h_fmt_sep)");
                    }
                    let ftid = reg.type_ids[field.ty.deref_type()];
                    let out_p = format!("%out_{alt_idx}_{fi}");
                    if matches!(field.ty, Type::Ref(_, _)) {
                        let id = next_tmp(&mut h_tmp);
                        let _ = writeln!(ext_code, "  %fvp_{id} = load ptr, ptr {out_p}");
                        if *field.ty.deref_type() == Type::Bool {
                            let _ = writeln!(ext_code, "  %fb8_{id} = load i8, ptr %fvp_{id}");
                            let _ = writeln!(ext_code, "  %fb_{id} = icmp ne i8 %fb8_{id}, 0");
                            let _ = writeln!(ext_code, "  %fbt_{id} = alloca i1");
                            let _ = writeln!(ext_code, "  store i1 %fb_{id}, ptr %fbt_{id}");
                            let _ = writeln!(
                                ext_code,
                                "  call void @vn2_print_val_{ftid}(ptr %fbt_{id})"
                            );
                        } else {
                            let _ = writeln!(
                                ext_code,
                                "  call void @vn2_print_val_{ftid}(ptr %fvp_{id})"
                            );
                        }
                    } else if field.ty == Type::Bool {
                        let id = h_tmp;
                        h_tmp += 1;
                        let _ = writeln!(ext_code, "  %fb8_{id} = load i8, ptr {out_p}");
                        let _ = writeln!(ext_code, "  %fb_{id} = icmp ne i8 %fb8_{id}, 0");
                        let _ = writeln!(ext_code, "  %fbt_{id} = alloca i1");
                        let _ = writeln!(ext_code, "  store i1 %fb_{id}, ptr %fbt_{id}");
                        let _ =
                            writeln!(ext_code, "  call void @vn2_print_val_{ftid}(ptr %fbt_{id})");
                    } else {
                        let _ =
                            writeln!(ext_code, "  call void @vn2_print_val_{ftid}(ptr {out_p})");
                    }
                }
                let _ = writeln!(ext_code, "  call i32 @putchar(i32 125)");
                let _ = writeln!(ext_code, "  call i32 @putchar(i32 10)");
            }
            // A host has consumed what it was given by value.
            for (pi, param) in control.parameters.iter().enumerate() {
                if needs_drop(program, &param.ty) {
                    let ptid = reg.intern_type(&param.ty);
                    reg.require_drop(ptid);
                    let _ = writeln!(ext_code, "  call fastcc void @vn2_drop_{ptid}(ptr %p{pi})");
                }
            }
            let _ = writeln!(ext_code, "  ret i32 {alt_idx}");
        }
        let _ = writeln!(ext_code, "}}\n");
    }

    let mut main_out = String::new();
    let _ = writeln!(main_out, "define i32 @main() nounwind {{");
    let _ = writeln!(main_out, "entry:");
    for (run_idx, spec) in specs.iter().enumerate() {
        if picks_turns {
            let len = spec.turns.len();
            let _ = writeln!(main_out, "  store i64 {len}, ptr @vn2_turn_left");
            if len > 0 {
                let choices = spec
                    .turns
                    .iter()
                    .map(|i| format!("i64 {i}"))
                    .collect::<Vec<_>>()
                    .join(", ");
                let _ = writeln!(
                    ext_code,
                    "@vn2_turns_{run_idx} = private constant [{len} x i64] [{choices}]"
                );
                let _ = writeln!(
                    main_out,
                    "  store ptr @vn2_turns_{run_idx}, ptr @vn2_turn_ptr"
                );
            }
        }
        let (start, end) = run_offsets[run_idx];
        let _ = writeln!(main_out, "  store i64 {start}, ptr @script_pos");
        let _ = writeln!(main_out, "  store i64 {end}, ptr @script_end");
        let _ = writeln!(
            main_out,
            "  store i1 {}, ptr @use_arith",
            if spec.arithmetic { "true" } else { "false" }
        );

        let cid = program.control(&spec.entry).expect("known entry control");
        let control = &program.controls[cid];
        let mut call_args = Vec::new();
        for (pi, (val, param)) in spec.arguments.iter().zip(&control.parameters).enumerate() {
            if matches!(param.ty, Type::Ref(_, _)) {
                let inner_ll = llvm_ty(program, param.ty.deref_type(), usize_bits);
                let islot = format!("%r{run_idx}_rin_{pi}");
                let _ = writeln!(main_out, "  {islot} = alloca {inner_ll}");
                let _ = writeln!(
                    main_out,
                    "  store {inner_ll} {}, ptr {islot}",
                    if *param.ty.deref_type() == Type::Bool {
                        "false"
                    } else {
                        "zeroinitializer"
                    }
                );
                emit_harness_value_into(
                    &mut main_out,
                    program,
                    &mut reg,
                    val,
                    param.ty.deref_type(),
                    &islot,
                    &mut h_tmp,
                    Refs::Slots,
                );
                call_args.push(format!("ptr {islot}"));
            } else {
                let ll = llvm_ty(program, &param.ty, usize_bits);
                let slot = format!("%r{run_idx}_in_{pi}");
                let _ = writeln!(main_out, "  {slot} = alloca {ll}");
                let _ = writeln!(
                    main_out,
                    "  store {ll} {}, ptr {slot}",
                    if param.ty == Type::Bool {
                        "false"
                    } else {
                        "zeroinitializer"
                    }
                );
                emit_harness_value_into(
                    &mut main_out,
                    program,
                    &mut reg,
                    val,
                    &param.ty,
                    &slot,
                    &mut h_tmp,
                    Refs::Slots,
                );
                let lr = format!("%r{run_idx}_iv_{pi}");
                let _ = writeln!(main_out, "  {lr} = load {ll}, ptr {slot}");
                call_args.push(format!("{ll} {lr}"));
            }
        }

        for (alt_idx, alt) in control.contract.iter().enumerate() {
            for (field_idx, field) in alt.fields.iter().enumerate() {
                let ll = llvm_ty(program, &field.ty, usize_bits);
                let slot = format!("%r{run_idx}_out_{alt_idx}_{field_idx}");
                let _ = writeln!(main_out, "  {slot} = alloca {ll}");
                let zero = if field.ty == Type::Bool {
                    "false"
                } else {
                    "zeroinitializer"
                };
                let _ = writeln!(main_out, "  store {ll} {zero}, ptr {slot}");
                call_args.push(format!("ptr {slot}"));
            }
        }
        let fault_slot = if control.faults {
            let fs = format!("%r{run_idx}_fault");
            let _ = writeln!(main_out, "  {fs} = alloca %vn2.string");
            let _ = writeln!(main_out, "  store %vn2.string zeroinitializer, ptr {fs}");
            call_args.push(format!("ptr {fs}"));
            Some(fs)
        } else {
            None
        };
        let term_slot = term_tys[cid].as_ref().map(|tty| {
            let ll = llvm_ty(program, tty, usize_bits);
            let ts = format!("%r{run_idx}_term");
            let _ = writeln!(main_out, "  {ts} = alloca {ll}");
            let _ = writeln!(
                main_out,
                "  store {ll} {}, ptr {ts}",
                if *tty == Type::Bool {
                    "false"
                } else {
                    "zeroinitializer"
                }
            );
            call_args.push(format!("ptr {ts}"));
            (ts, tty.clone())
        });

        let tag = format!("%r{run_idx}_tag");
        let _ = writeln!(
            main_out,
            "  {tag} = call fastcc i32 @vn2_ctrl_{cid}({})",
            call_args.join(", ")
        );

        let end_lbl = format!("r{run_idx}_end");
        let mut sw = String::new();
        for alt_idx in 0..control.contract.len() {
            let _ = write!(sw, " i32 {alt_idx}, label %r{run_idx}_a{alt_idx}");
        }
        if fault_slot.is_some() {
            let _ = write!(sw, " i32 -1, label %r{run_idx}_flt");
        }
        if term_slot.is_some() {
            let _ = write!(sw, " i32 -2, label %r{run_idx}_trm");
        }
        let _ = writeln!(main_out, "  switch i32 {tag}, label %{end_lbl} [ {sw} ]");

        for (alt_idx, alt) in control.contract.iter().enumerate() {
            let _ = writeln!(main_out, "r{run_idx}_a{alt_idx}:");
            let alt_g = reg.str_literal_map[alt.name.as_bytes()].clone();
            let _ = writeln!(
                main_out,
                "  call i32 (ptr, ...) @printf(ptr @h_fmt_done_hdr, i32 {run_idx}, ptr {alt_g})"
            );
            let _ = writeln!(main_out, "  call i32 @putchar(i32 123)");
            for (fi, field) in alt.fields.iter().enumerate() {
                if fi > 0 {
                    let _ = writeln!(main_out, "  call i32 (ptr, ...) @printf(ptr @h_fmt_sep)");
                }
                let ftid = reg.type_ids[field.ty.deref_type()];
                let slot = format!("%r{run_idx}_out_{alt_idx}_{fi}");
                if matches!(field.ty, Type::Ref(_, _)) {
                    let dp = format!("%r{run_idx}_dp_{alt_idx}_{fi}");
                    let _ = writeln!(main_out, "  {dp} = load ptr, ptr {slot}");
                    let _ = writeln!(main_out, "  call void @vn2_print_val_{ftid}(ptr {dp})");
                } else {
                    let _ = writeln!(main_out, "  call void @vn2_print_val_{ftid}(ptr {slot})");
                }
                if needs_drop(program, &field.ty) {
                    reg.require_drop(ftid);
                    let _ = writeln!(main_out, "  call fastcc void @vn2_drop_{ftid}(ptr {slot})");
                }
            }
            let _ = writeln!(main_out, "  call i32 @putchar(i32 125)");
            let _ = writeln!(main_out, "  call i32 @putchar(i32 10)");
            let _ = writeln!(main_out, "  br label %{end_lbl}");
        }
        if let Some(ref fs) = fault_slot {
            let _ = writeln!(main_out, "r{run_idx}_flt:");
            let _ = writeln!(
                main_out,
                "  call i32 (ptr, ...) @printf(ptr @h_fmt_fault_hdr, i32 {run_idx})"
            );
            let _ = writeln!(main_out, "  call void @vn2_print_escaped_str(ptr {fs})");
            let _ = writeln!(main_out, "  call i32 @putchar(i32 10)");
            let stid = reg.intern_type(&Type::String);
            reg.require_drop(stid);
            let _ = writeln!(main_out, "  call fastcc void @vn2_str_drop(ptr {fs})");
            let _ = writeln!(main_out, "  br label %{end_lbl}");
        }
        if let Some((ref ts, ref tty)) = term_slot {
            let _ = writeln!(main_out, "r{run_idx}_trm:");
            let _ = writeln!(
                main_out,
                "  call i32 (ptr, ...) @printf(ptr @h_fmt_term_hdr, i32 {run_idx})"
            );
            let ttid = reg.type_ids[tty.deref_type()];
            let _ = writeln!(main_out, "  call void @vn2_print_val_{ttid}(ptr {ts})");
            let _ = writeln!(main_out, "  call i32 @putchar(i32 10)");
            let _ = writeln!(main_out, "  br label %{end_lbl}");
        }
        let _ = writeln!(main_out, "{end_lbl}:");
        // The harness frees what it kept: the places it lent to the entry
        // control. Then every allocation of the run has been freed ([R4]),
        // and a count that is not zero is written for the reader of the
        // output.
        for (pi, param) in control.parameters.iter().enumerate() {
            if let Type::Ref(_, inner) = &param.ty
                && needs_drop(program, inner)
            {
                let tid = reg.intern_type(inner);
                reg.require_drop(tid);
                let _ = writeln!(
                    main_out,
                    "  call fastcc void @vn2_drop_{tid}(ptr %r{run_idx}_rin_{pi})"
                );
            }
        }
        let _ = writeln!(main_out, "  %r{run_idx}_live = load i64, ptr @vn2_h_live");
        let _ = writeln!(
            main_out,
            "  %r{run_idx}_even = icmp eq i64 %r{run_idx}_live, 0"
        );
        let _ = writeln!(
            main_out,
            "  br i1 %r{run_idx}_even, label %r{run_idx}_next, label %r{run_idx}_uneven"
        );
        let _ = writeln!(main_out, "r{run_idx}_uneven:");
        let _ = writeln!(
            main_out,
            "  call i32 (ptr, ...) @printf(ptr @h_fmt_live, i64 %r{run_idx}_live)"
        );
        let _ = writeln!(main_out, "  store i64 0, ptr @vn2_h_live");
        let _ = writeln!(main_out, "  br label %r{run_idx}_next");
        let _ = writeln!(main_out, "r{run_idx}_next:");
        // What a run wrote is there if a later run ends the process.
        let _ = writeln!(main_out, "  call i32 @fflush(ptr null)");
    }
    let _ = writeln!(main_out, "  %made = load i64, ptr @vn2_h_made");
    let _ = writeln!(
        main_out,
        "  call i32 (ptr, ...) @printf(ptr @h_fmt_made, i64 %made)"
    );
    let _ = writeln!(main_out, "  ret i32 0");
    let _ = writeln!(main_out, "}}\n");

    let mut out = String::new();
    let _ = writeln!(
        out,
        "; Villanelle v2 Phase 4 native harness (usize_bits = {usize_bits})\n"
    );
    // The harness counts allocations, so the allocator is always declared.
    reg.needed_libc = true;
    emit_type_decls(&mut out, &reg, true);

    let mut helpers = String::new();
    emit_runtime_helpers(&mut helpers, &reg);
    let mut printers = String::new();
    emit_printers(&mut printers, program, &reg, &used_print);

    let mut harness_globals = String::new();
    let _ = writeln!(harness_globals, "@script_pos = internal global i64 0");
    let _ = writeln!(harness_globals, "@script_end = internal global i64 0");
    let _ = writeln!(harness_globals, "@use_arith = internal global i1 false");
    let _ = writeln!(
        harness_globals,
        "@h_fmt_ev_hdr = private unnamed_addr constant [10 x i8] c\"EVENT %s(\\00\""
    );
    let _ = writeln!(
        harness_globals,
        "@h_fmt_ev_mid = private unnamed_addr constant [8 x i8] c\") -> %s\\00\""
    );
    let _ = writeln!(
        harness_globals,
        "@h_fmt_done_hdr = private unnamed_addr constant [17 x i8] c\"DONE %d done %s \\00\""
    );
    let _ = writeln!(
        harness_globals,
        "@h_fmt_fault_hdr = private unnamed_addr constant [17 x i8] c\"DONE %d faulted \\00\""
    );
    let _ = writeln!(
        harness_globals,
        "@h_fmt_term_hdr = private unnamed_addr constant [20 x i8] c\"DONE %d terminated \\00\""
    );
    let _ = writeln!(
        harness_globals,
        "@h_fmt_emit_pre = private unnamed_addr constant [12 x i8] c\"EVENT emit(\\00\""
    );
    let _ = writeln!(
        harness_globals,
        "@h_fmt_emit_suf = private unnamed_addr constant [11 x i8] c\") -> done\\0A\\00\""
    );
    let _ = writeln!(harness_globals);

    out.push_str(&printers);
    out.push_str(&harness_globals);
    out.push_str(&helpers);
    out.push_str(&ext_code);
    out.push_str(&body_out);
    out.push_str(&main_out);
    Ok(count_allocations(&out))
}

/// The module `ir` with every allocation counted: the calls of `malloc`,
/// `realloc` and `free` go through functions that keep in `@vn2_h_live` how
/// many allocations are live, and in `@vn2_h_made` how many were made.
/// `main` reads the first where a run has ended and the second at its end.
fn count_allocations(ir: &str) -> String {
    let mut out = ir
        .replace("call ptr @malloc(", "call ptr @vn2_h_malloc(")
        .replace("call ptr @realloc(", "call ptr @vn2_h_realloc(")
        .replace("call void @free(", "call void @vn2_h_free(");
    out.push_str(
        "@vn2_h_live = internal global i64 0
@vn2_h_made = internal global i64 0
@h_fmt_live = private unnamed_addr constant [11 x i8] c\"LIVE %lld\\0A\\00\"
@h_fmt_made = private unnamed_addr constant [11 x i8] c\"MADE %lld\\0A\\00\"

define internal ptr @vn2_h_malloc(i64 %n) nounwind {
entry:
  %p = call ptr @malloc(i64 %n)
  %some = icmp ne ptr %p, null
  %one = zext i1 %some to i64
  %live = load i64, ptr @vn2_h_live
  %next = add i64 %live, %one
  store i64 %next, ptr @vn2_h_live
  %made = load i64, ptr @vn2_h_made
  %more = add i64 %made, %one
  store i64 %more, ptr @vn2_h_made
  ret ptr %p
}

define internal ptr @vn2_h_realloc(ptr %old, i64 %n) nounwind {
entry:
  %p = call ptr @realloc(ptr %old, i64 %n)
  %fresh = icmp eq ptr %old, null
  %some = icmp ne ptr %p, null
  %both = and i1 %fresh, %some
  %one = zext i1 %both to i64
  %live = load i64, ptr @vn2_h_live
  %next = add i64 %live, %one
  store i64 %next, ptr @vn2_h_live
  %made = load i64, ptr @vn2_h_made
  %more = add i64 %made, %one
  store i64 %more, ptr @vn2_h_made
  ret ptr %p
}

define internal void @vn2_h_free(ptr %p) nounwind {
entry:
  %some = icmp ne ptr %p, null
  %one = zext i1 %some to i64
  %live = load i64, ptr @vn2_h_live
  %next = sub i64 %live, %one
  store i64 %next, ptr @vn2_h_live
  call void @free(ptr %p)
  ret void
}
",
    );
    out
}

/// The seconds a compiled batch of runs may take. A run of a checked program
/// ends ([K7] with the fuel of the oracle's run), so a batch that takes
/// longer is a difference, and is reported as one.
const NATIVE_SECONDS: u64 = 60;

/// Runs the binary at `bin_path` with its output in the file `out_path`, and
/// ends it after [`NATIVE_SECONDS`].
fn run_with_limit(
    bin_path: &std::path::Path,
    out_path: &std::path::Path,
) -> Result<std::process::ExitStatus, String> {
    let out_file = std::fs::File::create(out_path)
        .map_err(|e| format!("write {}: {e}", out_path.display()))?;
    let mut child = ProcessCommand::new(bin_path)
        .stdin(std::process::Stdio::null())
        .stdout(out_file)
        .stderr(std::process::Stdio::null())
        .spawn()
        .map_err(|e| format!("failed to run {}: {e}", bin_path.display()))?;
    let started = std::time::Instant::now();
    loop {
        match child.try_wait() {
            Ok(Some(status)) => return Ok(status),
            Ok(None) => {}
            Err(e) => return Err(format!("failed to wait for {}: {e}", bin_path.display())),
        }
        if started.elapsed().as_secs() >= NATIVE_SECONDS {
            let _ = child.kill();
            let _ = child.wait();
            return Err(format!(
                "native binary did not end in {NATIVE_SECONDS} seconds"
            ));
        }
        std::thread::sleep(std::time::Duration::from_millis(2));
    }
}

/// What a compiled batch of runs gave.
#[derive(Debug, Default)]
pub struct NativeBatch {
    /// The end and the trace of each run.
    pub runs: Vec<(erased::End, Vec<Event>)>,
    /// How many allocations the runs made together.
    pub allocations: u64,
}

/// Compiles `program` with `clang -x ir` at optimization level `opt_level`
/// (`0`, `2`, or `3`), executes all `specs` natively in a single process, and
/// returns the `(erased::End, Vec<Event>)` of each run. A run that ends with
/// an allocation it did not free, or that frees more than it allocated, ends
/// `Undefined` ([R4]).
pub fn run_native_batch(
    program: &Program,
    specs: &[NativeRunSpec],
    usize_bits: u32,
    opt_level: u8,
) -> Result<Vec<(erased::End, Vec<Event>)>, String> {
    run_native_counted(program, specs, usize_bits, opt_level).map(|batch| batch.runs)
}

/// As [`run_native_batch`], with the number of allocations the runs made.
pub fn run_native_counted(
    program: &Program,
    specs: &[NativeRunSpec],
    usize_bits: u32,
    opt_level: u8,
) -> Result<NativeBatch, String> {
    if specs.is_empty() {
        return Ok(NativeBatch::default());
    }
    let ir = emit_native_harness_llvm(program, specs, usize_bits)?;
    run_native_ir(program, specs, &ir, opt_level)
}

/// Compiles and runs `ir`, the text that [`emit_native_harness_llvm`] gave
/// for `specs` or a change of it, as [`run_native_counted`] does.
pub fn run_native_ir(
    program: &Program,
    specs: &[NativeRunSpec],
    ir: &str,
    opt_level: u8,
) -> Result<NativeBatch, String> {
    static COUNTER: AtomicU64 = AtomicU64::new(0);
    let id = COUNTER.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let tmp_dir = std::env::temp_dir();
    let ll_path = tmp_dir.join(format!("vn2_native_{pid}_{id}.ll"));
    let bin_path = tmp_dir.join(format!("vn2_native_{pid}_{id}.bin"));

    std::fs::write(&ll_path, ir).map_err(|e| format!("write {}: {e}", ll_path.display()))?;
    // For looking at what was compiled: `VN2_KEEP_IR` names a directory
    // that gets a copy of the text.
    if let Some(keep) = std::env::var_os("VN2_KEEP_IR") {
        let kept =
            std::path::Path::new(&keep).join(format!("vn2_native_{pid}_{id}_O{opt_level}.ll"));
        let _ = std::fs::write(kept, ir);
    }

    let opt_flag = format!("-O{}", opt_level.min(3));
    let compile = ProcessCommand::new("clang")
        .arg("-x")
        .arg("ir")
        .arg(&ll_path)
        .arg(&opt_flag)
        .arg("-Wno-override-module")
        .arg("-o")
        .arg(&bin_path)
        .output();
    let _ = std::fs::remove_file(&ll_path);

    let compile_out = compile.map_err(|e| format!("failed to invoke clang: {e}"))?;
    if !compile_out.status.success() {
        let _ = std::fs::remove_file(&bin_path);
        return Err(format!(
            "clang {} failed:\n{}\n--- LLVM IR ---\n{ir}",
            opt_flag,
            String::from_utf8_lossy(&compile_out.stderr)
        ));
    }

    let out_path = tmp_dir.join(format!("vn2_native_{pid}_{id}.out"));
    let ran = run_with_limit(&bin_path, &out_path);
    let _ = std::fs::remove_file(&bin_path);
    let written = std::fs::read(&out_path);
    let _ = std::fs::remove_file(&out_path);
    let status = ran?;
    let written = written.map_err(|e| format!("read {}: {e}", out_path.display()))?;
    if !status.success() {
        return Err(format!(
            "native binary exited with {:?} after {} of {} runs",
            status.code(),
            written
                .split(|byte| *byte == b'\n')
                .filter(|line| line.starts_with(b"DONE ") || line == b"HOST_FAILED")
                .count(),
            specs.len()
        ));
    }

    native_results(program, specs, &String::from_utf8_lossy(&written))
}

/// The end and the trace of each run in what a compiled harness wrote, and
/// the allocations it counted.
fn native_results(
    program: &Program,
    specs: &[NativeRunSpec],
    stdout: &str,
) -> Result<NativeBatch, String> {
    let mut results: Vec<(erased::End, Vec<Event>)> = Vec::new();
    let mut current_events = Vec::new();
    let mut allocations = 0;

    for line in stdout.lines() {
        if let Some(ev_text) = line.strip_prefix("EVENT ") {
            let ev = script::parse_native_event(program, ev_text)
                .map_err(|e| format!("native event `{ev_text}`: {e}"))?;
            current_events.push(ev);
        } else if let Some(rest) = line.strip_prefix("DONE ") {
            let (idx_str, end_text) = rest
                .split_once(' ')
                .ok_or_else(|| format!("malformed DONE line: {line}"))?;
            let run_idx: usize = idx_str
                .parse()
                .map_err(|_| format!("bad run index in `{line}`"))?;
            let end = script::parse_native_end(program, &specs[run_idx].entry, end_text)
                .map_err(|e| format!("native end `{end_text}`: {e}"))?;
            let events = std::mem::take(&mut current_events);
            results.push((end, events));
        } else if line == "HOST_FAILED" {
            let events = std::mem::take(&mut current_events);
            results.push((
                erased::End::HostFailed("native script exhausted or mismatched".to_string()),
                events,
            ));
        } else if let Some(count) = line.strip_prefix("LIVE ") {
            // The count of the run that has just ended.
            let run = results
                .last_mut()
                .ok_or_else(|| format!("`{line}` before the end of a run"))?;
            run.0 = erased::End::Undefined(format!(
                "the run ended as `{}` with {count} allocations live",
                run.0
            ));
        } else if let Some(count) = line.strip_prefix("MADE ") {
            allocations = count
                .parse()
                .map_err(|_| format!("bad count in `{line}`"))?;
        }
    }

    Ok(NativeBatch {
        runs: results,
        allocations,
    })
}
