//! The fact logic (`docs/v2/facts.md`): linear integer arithmetic, equality,
//! uninterpreted symbols, axiom instantiation (`[A1]` to `[A9]`, `[I10]`),
//! the decision procedure (`[J1]` to `[J6]`), certificates (`[V1]` to `[V5]`)
//! and counterexamples (`[M1]` to `[M6]`).

use crate::bdd::{self, Bdd, Formula};
use crate::int::Int;
use crate::lia;
pub use crate::terms::{
    AtomTerm, End, LinearTerm, Proof, Row, SortTag, Step, TermId, TheoryAtomId, TheoryLemma,
    div_ceil, div_floor, gcd,
};
use crate::typed::{IntType, StructId, Type};
use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt;

/// An axiom instance added to a query ([J3], [V2]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AxiomInstance {
    pub clause: &'static str,
    pub term: TermId,
    pub formula: Formula,
}

/// The certificate of a proved entailment ([V1] to [V5]).
#[derive(Clone, Debug)]
pub struct Certificate {
    pub bdd: Bdd,
    pub first_theory_var: usize,
    pub theory_atoms: Vec<Row>,
    pub query: Formula,
    pub instances: Vec<AxiomInstance>,
    pub lemmas: Vec<TheoryLemma>,
}

impl fmt::Display for Certificate {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(
            formatter,
            "certificate (atoms: {}, instances: {}, lemmas: {})",
            self.theory_atoms.len(),
            self.instances.len(),
            self.lemmas.len()
        )?;
        for (idx, instance) in self.instances.iter().enumerate() {
            writeln!(
                formatter,
                "  instance {idx}: [{}] on term u{}",
                instance.clause, instance.term
            )?;
        }
        for (idx, lemma) in self.lemmas.iter().enumerate() {
            writeln!(
                formatter,
                "  lemma {idx} ({} literals, {} steps, {} splits)",
                lemma.literals.len(),
                lemma.proof.size(),
                lemma.proof.splits()
            )?;
        }
        Ok(())
    }
}

/// A validated counterexample model when an entailment fails ([M1] to [M7]).
#[derive(Clone, Debug)]
pub struct Counterexample {
    /// The history atoms that hold in the counterexample (`(site_name, alt_name)`).
    pub history: Vec<(String, String)>,
    /// Values of program names in the counterexample (`name -> value`).
    pub values: BTreeMap<String, String>,
    /// Remark when the failure depends on an operator the logic does not
    /// interpret completely ([M3]).
    pub assumed_remark: Option<String>,
    /// Note when two collections or strings agree on length and mentioned
    /// elements but are assigned different values by the model ([M7]).
    pub extensionality_note: Option<String>,
    /// Whether the obligation is inside a loop body ([M4]).
    pub in_loop: bool,
    /// Raw Boolean assignment `h` and integer valuation `ν`.
    pub bool_model: BTreeMap<usize, bool>,
    pub int_model: BTreeMap<TermId, Int>,
}

impl fmt::Display for Counterexample {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !self.history.is_empty() {
            let path: Vec<String> = self
                .history
                .iter()
                .map(|(site, alt)| format!("{site}.{alt}"))
                .collect();
            let _ = write!(formatter, "on history [{}]", path.join(", "));
        } else {
            let _ = write!(formatter, "on the entry history");
        }
        if !self.values.is_empty() {
            let bindings: Vec<String> = self
                .values
                .iter()
                .map(|(name, val)| format!("{name} = {val}"))
                .collect();
            let _ = write!(formatter, " with {}", bindings.join(", "));
        }
        if let Some(remark) = &self.assumed_remark {
            let _ = write!(formatter, " ({remark})");
        }
        if let Some(note) = &self.extensionality_note {
            let _ = write!(formatter, " [{note}]");
        }
        if self.in_loop {
            let _ = write!(
                formatter,
                " [values at the start of an iteration; the loop states nothing that excludes them]"
            );
        }
        Ok(())
    }
}

/// The answer to a query. Only the first two are verdicts ([J5], [J6]).
pub enum Decision {
    Proved(Certificate),
    Refuted(Box<Counterexample>),
    /// The count of steps ran out: the limit of the compiler ([J6]). It is
    /// neither a yes nor a counterexample.
    Limit {
        steps: u64,
    },
    /// The procedure contradicted itself: a model that fails what it was
    /// found for ([M1]). A defect of the compiler, reported as one.
    Fault(String),
}

/// The count of steps that one query may take ([J6]): candidates, exchanges
/// of the simplex method and splits together. It is a count, so the answer
/// does not depend on the machine.
pub const STEP_LIMIT: u64 = 2_000_000;

thread_local! {
    static STEP_LIMIT_HERE: std::cell::Cell<u64> = const { std::cell::Cell::new(STEP_LIMIT) };
}

/// Runs `work` with another count of steps for each query. The tests use it
/// to reach the limit of [J6] on a small program.
pub fn with_step_limit<T>(steps: u64, work: impl FnOnce() -> T) -> T {
    let before = STEP_LIMIT_HERE.with(|limit| limit.replace(steps));
    let result = work();
    STEP_LIMIT_HERE.with(|limit| limit.set(before));
    result
}

#[derive(Clone, Debug)]
pub enum DefRhs {
    Linear(LinearTerm),
    BoolFormula(Formula),
}

/// The solver state for one control body.
#[derive(Clone, Debug)]
pub struct Solver {
    pub bdd: Bdd,
    /// History atom BDD variables `0..first_theory_var`, named `(site, alt)`.
    pub history_names: Vec<(String, String)>,
    pub first_theory_var: usize,
    /// Interned atomic integer terms.
    pub terms: Vec<AtomTerm>,
    term_ids: HashMap<AtomTerm, TermId>,
    pub term_sorts: BTreeMap<TermId, SortTag>,
    pub struct_arities: BTreeMap<StructId, usize>,
    pub usize_max_term: TermId,
    /// Canonical positive linear inequality rows, each mapped to BDD variable
    /// `first_theory_var + id`.
    pub theory_atoms: Vec<Row>,
    atom_ids: HashMap<Row, TheoryAtomId>,
    /// Structural formula `Ω` ([K4], [K5], [K8]).
    pub structure: Vec<Formula>,
    /// Conditional facts `G ⇒ φ` in `Ψ` ([N4]).
    pub facts: Vec<Formula>,
    /// Conditional definitions `G ⇒ u_id = rhs` for model completion.
    pub definitions: Vec<(Formula, TermId, DefRhs)>,
    /// Axiom instances instantiated so far ([J3]).
    pub instances: Vec<AxiomInstance>,
    instantiated_terms: HashSet<TermId>,
    instantiated_pairs: HashSet<(TermId, TermId)>,
    instantiated_ext: HashSet<(TermId, TermId)>,
    instantiated_update_frames: HashSet<(TermId, LinearTerm)>,
    /// Theory lemmas learned across queries of this body.
    pub lemmas: Vec<TheoryLemma>,
    /// The count of steps that one query may take ([J6]).
    pub step_limit: u64,
}

impl Solver {
    pub fn new(history_names: Vec<(String, String)>) -> Solver {
        let first_theory_var = history_names.len();
        let mut solver = Solver {
            bdd: Bdd::new(),
            history_names,
            first_theory_var,
            terms: Vec::new(),
            term_ids: HashMap::new(),
            term_sorts: BTreeMap::new(),
            struct_arities: BTreeMap::new(),
            usize_max_term: 0,
            theory_atoms: Vec::new(),
            atom_ids: HashMap::new(),
            structure: Vec::new(),
            facts: Vec::new(),
            definitions: Vec::new(),
            instances: Vec::new(),
            instantiated_terms: HashSet::new(),
            instantiated_pairs: HashSet::new(),
            instantiated_ext: HashSet::new(),
            instantiated_update_frames: HashSet::new(),
            lemmas: Vec::new(),
            step_limit: STEP_LIMIT_HERE.with(std::cell::Cell::get),
        };
        solver.usize_max_term = solver.intern_term(AtomTerm::UsizeMax);
        solver
    }

    pub fn register_sort(&mut self, id: TermId, ty: &Type) {
        if let Some(tag) = SortTag::from_type(ty) {
            self.term_sorts.insert(id, tag);
        }
    }

    pub fn register_struct_arity(&mut self, sid: StructId, arity: usize) {
        self.struct_arities.insert(sid, arity);
    }

    pub fn term_sort(&self, term: &LinearTerm) -> Option<&SortTag> {
        term.as_var().and_then(|id| self.term_sorts.get(&id))
    }

    pub fn is_value_term_linear(&self, term: &LinearTerm) -> bool {
        let Some(id) = term.as_var() else {
            return false;
        };
        matches!(
            self.terms[id],
            AtomTerm::Var {
                is_value_term: true,
                ..
            } | AtomTerm::Field {
                is_value_term: true,
                ..
            } | AtomTerm::Index {
                is_value_term: true,
                ..
            }
        )
    }

    pub fn sorts_compatible(a: Option<&SortTag>, b: Option<&SortTag>) -> bool {
        match (a, b) {
            (Some(x), Some(y)) => x == y,
            _ => true,
        }
    }

    pub fn intern_term(&mut self, term: AtomTerm) -> TermId {
        if let Some(id) = self.term_ids.get(&term) {
            return *id;
        }
        let id = self.terms.len();
        self.terms.push(term.clone());
        self.term_ids.insert(term, id);
        id
    }

    pub fn fresh_var(&mut self, name: String, ty: Option<IntType>, is_value_term: bool) -> TermId {
        let unique = format!("{name}#{}", self.terms.len());
        let id = self.intern_term(AtomTerm::Var {
            name: unique,
            ty,
            is_value_term,
        });
        self.instantiate_all();
        id
    }

    /// Returns the BDD formula for `row` (`Σ a_i · u_i ≤ rhs`), interning its
    /// canonical positive form as a theory atom.
    pub fn row_formula(&mut self, row: Row) -> Formula {
        if row.coeffs.is_empty() {
            return if row.rhs >= Int::zero() {
                bdd::TRUE
            } else {
                bdd::FALSE
            };
        }
        let (norm, _) = row.normalize();
        let first_coeff = norm.coeffs.values().next().expect("non-empty");
        let (canonical, positive) = if !first_coeff.is_negative() {
            (norm, true)
        } else {
            (norm.complement(), false)
        };
        let atom_id = if let Some(id) = self.atom_ids.get(&canonical) {
            *id
        } else {
            let id = self.theory_atoms.len();
            self.theory_atoms.push(canonical.clone());
            self.atom_ids.insert(canonical, id);
            id
        };
        let bdd_var = self.first_theory_var + atom_id;
        self.bdd.literal(bdd_var, positive)
    }

    pub fn le(&mut self, left: &LinearTerm, right: &LinearTerm) -> Formula {
        self.row_formula(Row::le(left, right))
    }

    pub fn lt(&mut self, left: &LinearTerm, right: &LinearTerm) -> Formula {
        self.row_formula(Row::lt(left, right))
    }

    pub fn eq(&mut self, left: &LinearTerm, right: &LinearTerm) -> Formula {
        let a = self.le(left, right);
        let b = self.le(right, left);
        self.bdd.and(a, b)
    }

    pub fn ne(&mut self, left: &LinearTerm, right: &LinearTerm) -> Formula {
        let eq = self.eq(left, right);
        self.bdd.not(eq)
    }

    pub fn add_structure(&mut self, formula: Formula) {
        self.structure.push(formula);
    }

    pub fn add_fact(&mut self, guard: Formula, fact: Formula) {
        let imp = self.bdd.implies(guard, fact);
        self.facts.push(imp);
    }

    pub fn add_def_linear(&mut self, guard: Formula, var_id: TermId, rhs: LinearTerm) {
        let eq = self.eq(&LinearTerm::var(var_id), &rhs);
        self.add_fact(guard, eq);
        self.definitions.push((guard, var_id, DefRhs::Linear(rhs)));
    }

    pub fn add_def_bool(&mut self, guard: Formula, var_id: TermId, phi: Formula) {
        let is_one = self.le(&LinearTerm::from_i128(1), &LinearTerm::var(var_id));
        let iff = self.bdd.iff(is_one, phi);
        self.add_fact(guard, iff);
        self.definitions
            .push((guard, var_id, DefRhs::BoolFormula(phi)));
    }

    fn int_range_formula(&mut self, u: &LinearTerm, int_ty: IntType) -> Formula {
        if int_ty == IntType::Usize {
            let low = self.le(&LinearTerm::from_i128(0), u);
            let umax = LinearTerm::var(self.usize_max_term);
            let high = self.le(u, &umax);
            self.bdd.and(low, high)
        } else {
            let (lo, hi) = int_ty.literal_bounds();
            let low = self.le(&LinearTerm::constant(lo), u);
            let high = self.le(u, &LinearTerm::constant(hi));
            self.bdd.and(low, high)
        }
    }

    fn usize_range_formula(&mut self, u: &LinearTerm) -> Formula {
        let low = self.le(&LinearTerm::from_i128(0), u);
        let umax = LinearTerm::var(self.usize_max_term);
        let high = self.le(u, &umax);
        self.bdd.and(low, high)
    }

    /// Instantiates `[A1]`–`[A9]` and congruence (`[I10]`, `[J3]`) for all terms
    /// currently in `self.terms`.
    pub fn instantiate_all(&mut self) {
        let mut idx = 0;
        loop {
            let prev_len = self.terms.len();
            while idx < self.terms.len() {
                if self.instantiated_terms.insert(idx) {
                    let term = self.terms[idx].clone();
                    let u = LinearTerm::var(idx);
                    match term {
                        AtomTerm::Var {
                            ty: Some(int_ty),
                            is_value_term: true,
                            ..
                        }
                        | AtomTerm::Field {
                            int_ty: Some(int_ty),
                            is_value_term: true,
                            ..
                        }
                        | AtomTerm::Index {
                            int_ty: Some(int_ty),
                            is_value_term: true,
                            ..
                        } => {
                            let formula = self.int_range_formula(&u, int_ty);
                            self.instances.push(AxiomInstance {
                                clause: "A1",
                                term: idx,
                                formula,
                            });
                        }
                        AtomTerm::Field {
                            is_bool: true,
                            is_value_term: true,
                            ..
                        }
                        | AtomTerm::Index {
                            is_bool: true,
                            is_value_term: true,
                            ..
                        } => {
                            let lo = self.le(&LinearTerm::from_i128(0), &u);
                            let hi = self.le(&u, &LinearTerm::from_i128(1));
                            let formula = self.bdd.and(lo, hi);
                            self.instances.push(AxiomInstance {
                                clause: "A1",
                                term: idx,
                                formula,
                            });
                        }
                        AtomTerm::UsizeMax => {
                            let lo = Int::power_of_two(32).minus(&Int::from_u64(1));
                            let hi = Int::power_of_two(64).minus(&Int::from_u64(1));
                            let low = self.le(&LinearTerm::constant(lo), &u);
                            let high = self.le(&u, &LinearTerm::constant(hi));
                            let formula = self.bdd.and(low, high);
                            self.instances.push(AxiomInstance {
                                clause: "A2",
                                term: idx,
                                formula,
                            });
                        }
                        AtomTerm::Len(_) => {
                            let formula = self.usize_range_formula(&u);
                            self.instances.push(AxiomInstance {
                                clause: "A3",
                                term: idx,
                                formula,
                            });
                        }
                        AtomTerm::VecLit(items) => {
                            let len_id = self.intern_term(AtomTerm::Len(u));
                            let eq = self.eq(
                                &LinearTerm::var(len_id),
                                &LinearTerm::from_i128(items.len() as i128),
                            );
                            self.instances.push(AxiomInstance {
                                clause: "A3",
                                term: idx,
                                formula: eq,
                            });
                        }
                        AtomTerm::EmptyMap => {
                            let len_id = self.intern_term(AtomTerm::Len(u));
                            let eq = self.eq(&LinearTerm::var(len_id), &LinearTerm::from_i128(0));
                            self.instances.push(AxiomInstance {
                                clause: "A3",
                                term: idx,
                                formula: eq,
                            });
                        }
                        AtomTerm::VariantCtor {
                            variant_id,
                            ctor_idx,
                            num_ctors,
                            ..
                        } => {
                            self.term_sorts.insert(idx, SortTag::Variant(variant_id));
                            let tag_id = self.intern_term(AtomTerm::VariantTag {
                                base: u,
                                variant_id,
                                num_ctors,
                            });
                            let eq = self.eq(
                                &LinearTerm::var(tag_id),
                                &LinearTerm::from_i128(ctor_idx as i128),
                            );
                            self.instances.push(AxiomInstance {
                                clause: "A5",
                                term: idx,
                                formula: eq,
                            });
                        }
                        AtomTerm::VariantTag { num_ctors, .. } => {
                            let max_tag = (num_ctors.saturating_sub(1)) as i128;
                            let lo = self.le(&LinearTerm::from_i128(0), &u);
                            let hi = self.le(&u, &LinearTerm::from_i128(max_tag));
                            let formula = self.bdd.and(lo, hi);
                            self.instances.push(AxiomInstance {
                                clause: "A5",
                                term: idx,
                                formula,
                            });
                        }
                        AtomTerm::StructCtor(sid, fields) => {
                            self.term_sorts.insert(idx, SortTag::Struct(sid));
                            self.struct_arities.entry(sid).or_insert(fields.len());
                        }
                        AtomTerm::Update { base, index, value } => {
                            if let Some(sort) = self.term_sort(&base).cloned() {
                                self.term_sorts.insert(idx, sort);
                            }
                            let len_u_id = self.intern_term(AtomTerm::Len(u.clone()));
                            let len_b_id = self.intern_term(AtomTerm::Len(base));
                            let len_eq =
                                self.eq(&LinearTerm::var(len_u_id), &LinearTerm::var(len_b_id));
                            self.instances.push(AxiomInstance {
                                clause: "A6",
                                term: idx,
                                formula: len_eq,
                            });

                            let at_i_id = self.intern_term(AtomTerm::Index {
                                base: u,
                                index: index.clone(),
                                int_ty: None,
                                is_bool: false,
                                is_value_term: false,
                            });
                            let zero = LinearTerm::from_i128(0);
                            let ge_zero = self.le(&zero, &index);
                            let lt_len = self.lt(&index, &LinearTerm::var(len_b_id));
                            let in_range = self.bdd.and(ge_zero, lt_len);
                            let eq_val = self.eq(&LinearTerm::var(at_i_id), &value);
                            let rw_formula = self.bdd.implies(in_range, eq_val);
                            self.instances.push(AxiomInstance {
                                clause: "A6",
                                term: idx,
                                formula: rw_formula,
                            });
                        }
                        AtomTerm::DivConst(t, k) => {
                            // [A7]:
                            // t ≥ 0 ⇒ k·q ≤ t ≤ k·q + (k - 1)
                            // t ≤ 0 ⇒ k·q - (k - 1) ≤ t ≤ k·q
                            let zero = LinearTerm::from_i128(0);
                            let kq = u.scale(&k);
                            let slack = LinearTerm::constant(k.minus(&Int::from_u64(1)));

                            let t_ge_0 = self.le(&zero, &t);
                            let pos_lo = self.le(&kq, &t);
                            let pos_hi = self.le(&t, &kq.add(&slack));
                            let pos_both = self.bdd.and(pos_lo, pos_hi);
                            let pos_imp = self.bdd.implies(t_ge_0, pos_both);

                            let t_le_0 = self.le(&t, &zero);
                            let neg_lo = self.le(&kq.sub(&slack), &t);
                            let neg_hi = self.le(&t, &kq);
                            let neg_both = self.bdd.and(neg_lo, neg_hi);
                            let neg_imp = self.bdd.implies(t_le_0, neg_both);

                            let formula = self.bdd.and(pos_imp, neg_imp);
                            self.instances.push(AxiomInstance {
                                clause: "A7",
                                term: idx,
                                formula,
                            });
                        }
                        AtomTerm::Div(s, t) => {
                            let formula = self.instantiate_a8_div(&u, &s, &t);
                            self.instances.push(AxiomInstance {
                                clause: "A8",
                                term: idx,
                                formula,
                            });
                        }
                        AtomTerm::Rem(s, t) => {
                            let formula = self.instantiate_a8_rem(&u, &s, &t);
                            self.instances.push(AxiomInstance {
                                clause: "A8",
                                term: idx,
                                formula,
                            });
                        }
                        AtomTerm::Mul {
                            left: s,
                            right: t,
                            left_bounds: (a, big_a),
                            right_bounds: (b, big_b),
                        } => {
                            let mut conj = bdd::TRUE;
                            // w ≥ a·t + b·s - a·b
                            if let (Some(a), Some(b)) = (&a, &b) {
                                let plane = t
                                    .scale(a)
                                    .add(&s.scale(b))
                                    .sub(&LinearTerm::constant(a.times(b)));
                                let c = self.le(&plane, &u);
                                conj = self.bdd.and(conj, c);
                            }
                            // w ≥ A·t + B·s - A·B
                            if let (Some(big_a), Some(big_b)) = (&big_a, &big_b) {
                                let plane = t
                                    .scale(big_a)
                                    .add(&s.scale(big_b))
                                    .sub(&LinearTerm::constant(big_a.times(big_b)));
                                let c = self.le(&plane, &u);
                                conj = self.bdd.and(conj, c);
                            }
                            // w ≤ A·t + b·s - A·b
                            if let (Some(big_a), Some(b)) = (&big_a, &b) {
                                let plane = t
                                    .scale(big_a)
                                    .add(&s.scale(b))
                                    .sub(&LinearTerm::constant(big_a.times(b)));
                                let c = self.le(&u, &plane);
                                conj = self.bdd.and(conj, c);
                            }
                            // w ≤ a·t + B·s - a·B
                            if let (Some(a), Some(big_b)) = (&a, &big_b) {
                                let plane = t
                                    .scale(a)
                                    .add(&s.scale(big_b))
                                    .sub(&LinearTerm::constant(a.times(big_b)));
                                let c = self.le(&u, &plane);
                                conj = self.bdd.and(conj, c);
                            }
                            self.instances.push(AxiomInstance {
                                clause: "A9",
                                term: idx,
                                formula: conj,
                            });
                        }
                        AtomTerm::Var { .. }
                        | AtomTerm::Field { .. }
                        | AtomTerm::Index { .. }
                        | AtomTerm::PureAlt(_, _)
                        | AtomTerm::PurePay(_, _, _, _)
                        | AtomTerm::StrLit(_)
                        | AtomTerm::Trim(_) => {}
                    }
                }
                idx += 1;
            }

            // [A6] frame axiom for every `Update` together with every index `j`
            // used on a vector of the same sort ([J3]).
            let mut updates = Vec::new();
            let mut indices = Vec::new();
            for (tid, term) in self.terms.iter().enumerate() {
                match term {
                    AtomTerm::Update { base, index, .. } => {
                        updates.push((
                            tid,
                            base.clone(),
                            index.clone(),
                            self.term_sorts.get(&tid).cloned(),
                        ));
                    }
                    AtomTerm::Index {
                        base,
                        index,
                        int_ty,
                        is_bool,
                        ..
                    } => {
                        indices.push((
                            index.clone(),
                            self.term_sort(base).cloned(),
                            *int_ty,
                            *is_bool,
                        ));
                    }
                    _ => {}
                }
            }
            for (upd_id, base, i_term, upd_sort) in updates {
                let u_upd = LinearTerm::var(upd_id);
                let base_is_val = self.is_value_term_linear(&base);
                for (j_term, vec_sort, elem_int_ty, elem_is_bool) in &indices {
                    if *j_term == i_term {
                        continue;
                    }
                    if !Solver::sorts_compatible(upd_sort.as_ref(), vec_sort.as_ref()) {
                        continue;
                    }
                    if !self
                        .instantiated_update_frames
                        .insert((upd_id, j_term.clone()))
                    {
                        continue;
                    }
                    let u_at_j = self.intern_term(AtomTerm::Index {
                        base: u_upd.clone(),
                        index: j_term.clone(),
                        int_ty: None,
                        is_bool: false,
                        is_value_term: false,
                    });
                    let b_at_j = self.intern_term(AtomTerm::Index {
                        base: base.clone(),
                        index: j_term.clone(),
                        int_ty: *elem_int_ty,
                        is_bool: *elem_is_bool,
                        is_value_term: base_is_val,
                    });
                    let j_neq_i = self.ne(j_term, &i_term);
                    let eq_frame = self.eq(&LinearTerm::var(u_at_j), &LinearTerm::var(b_at_j));
                    let formula = self.bdd.implies(j_neq_i, eq_frame);
                    self.instances.push(AxiomInstance {
                        clause: "A6",
                        term: upd_id,
                        formula,
                    });
                }
            }

            // Pairwise theory and congruence instances ([A3], [A4], [A5], [I10]).
            let len = self.terms.len();
            for i in 0..len {
                for j in (i + 1)..len {
                    if !self.instantiated_pairs.insert((i, j)) {
                        continue;
                    }
                    self.instantiate_term_pair(i, j);
                }
            }

            // [A4] struct extensionality across pairs where both have full fields.
            self.instantiate_struct_extensionality();

            if self.terms.len() == prev_len {
                break;
            }
        }
    }

    fn instantiate_term_pair(&mut self, i: TermId, j: TermId) {
        enum PairRule {
            Congruence {
                clause: &'static str,
                args1: Vec<LinearTerm>,
                args2: Vec<LinearTerm>,
                iff: bool,
            },
            Distinct {
                clause: &'static str,
            },
            FieldOfCtor {
                base: LinearTerm,
                field_idx: usize,
                ctor_id: TermId,
                fields: Vec<LinearTerm>,
            },
        }

        let rule = match (&self.terms[i], &self.terms[j]) {
            (AtomTerm::Div(s1, t1), AtomTerm::Div(s2, t2))
            | (AtomTerm::Rem(s1, t1), AtomTerm::Rem(s2, t2))
            | (
                AtomTerm::Mul {
                    left: s1,
                    right: t1,
                    ..
                },
                AtomTerm::Mul {
                    left: s2,
                    right: t2,
                    ..
                },
            ) => Some(PairRule::Congruence {
                clause: "I10",
                args1: vec![s1.clone(), t1.clone()],
                args2: vec![s2.clone(), t2.clone()],
                iff: false,
            }),
            (AtomTerm::Trim(a1), AtomTerm::Trim(a2)) => Some(PairRule::Congruence {
                clause: "I10",
                args1: vec![a1.clone()],
                args2: vec![a2.clone()],
                iff: false,
            }),
            (AtomTerm::PureAlt(c1, a1), AtomTerm::PureAlt(c2, a2)) if c1 == c2 => {
                Some(PairRule::Congruence {
                    clause: "I10",
                    args1: a1.clone(),
                    args2: a2.clone(),
                    iff: false,
                })
            }
            (AtomTerm::PurePay(c1, alt1, f1, a1), AtomTerm::PurePay(c2, alt2, f2, a2))
                if c1 == c2 && alt1 == alt2 && f1 == f2 =>
            {
                Some(PairRule::Congruence {
                    clause: "I10",
                    args1: a1.clone(),
                    args2: a2.clone(),
                    iff: false,
                })
            }
            (AtomTerm::Len(b1), AtomTerm::Len(b2)) => Some(PairRule::Congruence {
                clause: "A3",
                args1: vec![b1.clone()],
                args2: vec![b2.clone()],
                iff: false,
            }),
            (AtomTerm::StrLit(s1), AtomTerm::StrLit(s2)) if s1 != s2 => {
                Some(PairRule::Distinct { clause: "A3" })
            }
            (AtomTerm::StructCtor(sid1, f1), AtomTerm::StructCtor(sid2, f2)) if sid1 == sid2 => {
                Some(PairRule::Congruence {
                    clause: "A4",
                    args1: f1.clone(),
                    args2: f2.clone(),
                    iff: true,
                })
            }
            (
                AtomTerm::Field {
                    base: b1,
                    struct_id: sid1,
                    field_idx: fidx1,
                    ..
                },
                AtomTerm::Field {
                    base: b2,
                    struct_id: sid2,
                    field_idx: fidx2,
                    ..
                },
            ) if sid1 == sid2 && fidx1 == fidx2 => Some(PairRule::Congruence {
                clause: "A4",
                args1: vec![b1.clone()],
                args2: vec![b2.clone()],
                iff: false,
            }),
            (
                AtomTerm::Field {
                    base,
                    struct_id,
                    field_idx,
                    ..
                },
                AtomTerm::StructCtor(sid2, fields),
            ) if struct_id == sid2 && *field_idx < fields.len() => Some(PairRule::FieldOfCtor {
                base: base.clone(),
                field_idx: *field_idx,
                ctor_id: j,
                fields: fields.clone(),
            }),
            (
                AtomTerm::StructCtor(sid2, fields),
                AtomTerm::Field {
                    base,
                    struct_id,
                    field_idx,
                    ..
                },
            ) if struct_id == sid2 && *field_idx < fields.len() => Some(PairRule::FieldOfCtor {
                base: base.clone(),
                field_idx: *field_idx,
                ctor_id: i,
                fields: fields.clone(),
            }),
            (
                AtomTerm::VariantCtor {
                    variant_id: v1,
                    ctor_idx: c1,
                    fields: f1,
                    ..
                },
                AtomTerm::VariantCtor {
                    variant_id: v2,
                    ctor_idx: c2,
                    fields: f2,
                    ..
                },
            ) if v1 == v2 => {
                if c1 == c2 {
                    Some(PairRule::Congruence {
                        clause: "A5",
                        args1: f1.clone(),
                        args2: f2.clone(),
                        iff: true,
                    })
                } else {
                    Some(PairRule::Distinct { clause: "A5" })
                }
            }
            (
                AtomTerm::VariantTag {
                    base: b1,
                    variant_id: v1,
                    ..
                },
                AtomTerm::VariantTag {
                    base: b2,
                    variant_id: v2,
                    ..
                },
            ) if v1 == v2 => Some(PairRule::Congruence {
                clause: "A5",
                args1: vec![b1.clone()],
                args2: vec![b2.clone()],
                iff: false,
            }),
            (
                AtomTerm::Index {
                    base: b1,
                    index: idx1,
                    ..
                },
                AtomTerm::Index {
                    base: b2,
                    index: idx2,
                    ..
                },
            ) if Solver::sorts_compatible(self.term_sort(b1), self.term_sort(b2)) => {
                Some(PairRule::Congruence {
                    clause: "A6",
                    args1: vec![b1.clone(), idx1.clone()],
                    args2: vec![b2.clone(), idx2.clone()],
                    iff: false,
                })
            }
            (
                AtomTerm::Update {
                    base: b1,
                    index: i1,
                    value: v1,
                },
                AtomTerm::Update {
                    base: b2,
                    index: i2,
                    value: v2,
                },
            ) if Solver::sorts_compatible(self.term_sort(b1), self.term_sort(b2)) => {
                Some(PairRule::Congruence {
                    clause: "A6",
                    args1: vec![b1.clone(), i1.clone(), v1.clone()],
                    args2: vec![b2.clone(), i2.clone(), v2.clone()],
                    iff: false,
                })
            }
            _ => None,
        };

        let Some(rule) = rule else {
            return;
        };

        match rule {
            PairRule::Congruence {
                clause,
                args1,
                args2,
                iff,
            } => {
                let mut eq_args = bdd::TRUE;
                for (a, b) in args1.iter().zip(&args2) {
                    let e = self.eq(a, b);
                    eq_args = self.bdd.and(eq_args, e);
                }
                let eq_res = self.eq(&LinearTerm::var(i), &LinearTerm::var(j));
                let formula = if iff {
                    self.bdd.iff(eq_args, eq_res)
                } else {
                    self.bdd.implies(eq_args, eq_res)
                };
                self.instances.push(AxiomInstance {
                    clause,
                    term: i,
                    formula,
                });
            }
            PairRule::Distinct { clause } => {
                let formula = self.ne(&LinearTerm::var(i), &LinearTerm::var(j));
                self.instances.push(AxiomInstance {
                    clause,
                    term: i,
                    formula,
                });
            }
            PairRule::FieldOfCtor {
                base,
                field_idx,
                ctor_id,
                fields,
            } => {
                let is_ctor = self.eq(&base, &LinearTerm::var(ctor_id));
                let field_tid = if ctor_id == j { i } else { j };
                let eq_val = self.eq(&LinearTerm::var(field_tid), &fields[field_idx]);
                let formula = self.bdd.implies(is_ctor, eq_val);
                self.instances.push(AxiomInstance {
                    clause: "A4",
                    term: field_tid,
                    formula,
                });
            }
        }
    }

    fn instantiate_struct_extensionality(&mut self) {
        // Collect struct field terms already present for non-ctor terms.
        let mut fields_by_base_struct: BTreeMap<(TermId, StructId), Vec<Option<LinearTerm>>> =
            BTreeMap::new();
        for (tid, term) in self.terms.iter().enumerate() {
            if let AtomTerm::Field {
                base,
                struct_id,
                field_idx,
                ..
            } = term
                && let Some(base_id) = base.as_var()
                && !matches!(self.terms[base_id], AtomTerm::StructCtor(_, _))
                && let Some(&arity) = self.struct_arities.get(struct_id)
                && *field_idx < arity
            {
                fields_by_base_struct
                    .entry((base_id, *struct_id))
                    .or_insert_with(|| vec![None; arity])[*field_idx] = Some(LinearTerm::var(tid));
            }
        }
        let mut by_struct: BTreeMap<StructId, Vec<(TermId, Vec<LinearTerm>)>> = BTreeMap::new();
        for ((base_id, sid), slots) in fields_by_base_struct {
            if slots.iter().all(Option::is_some) {
                let full: Vec<LinearTerm> = slots.into_iter().map(Option::unwrap).collect();
                by_struct.entry(sid).or_default().push((base_id, full));
            }
        }
        for (tid, term) in self.terms.iter().enumerate() {
            if let AtomTerm::StructCtor(sid, fields) = term {
                by_struct
                    .entry(*sid)
                    .or_default()
                    .push((tid, fields.clone()));
            }
        }

        for (_sid, entries) in by_struct {
            for idx_a in 0..entries.len() {
                for idx_b in (idx_a + 1)..entries.len() {
                    let (id_a, ref f_a) = entries[idx_a];
                    let (id_b, ref f_b) = entries[idx_b];
                    if matches!(self.terms[id_a], AtomTerm::StructCtor(_, _))
                        && matches!(self.terms[id_b], AtomTerm::StructCtor(_, _))
                    {
                        continue;
                    }
                    let key = if id_a < id_b {
                        (id_a, id_b)
                    } else {
                        (id_b, id_a)
                    };
                    if !self.instantiated_ext.insert(key) {
                        continue;
                    }
                    let mut eq_fields = bdd::TRUE;
                    for (fa, fb) in f_a.iter().zip(f_b) {
                        let e = self.eq(fa, fb);
                        eq_fields = self.bdd.and(eq_fields, e);
                    }
                    let eq_whole = self.eq(&LinearTerm::var(id_a), &LinearTerm::var(id_b));
                    let formula = self.bdd.implies(eq_fields, eq_whole);
                    self.instances.push(AxiomInstance {
                        clause: "A4",
                        term: key.0,
                        formula,
                    });
                }
            }
        }
    }

    fn instantiate_a8_div(&mut self, q: &LinearTerm, s: &LinearTerm, t: &LinearTerm) -> Formula {
        let zero = LinearTerm::from_i128(0);
        let one = LinearTerm::from_i128(1);
        let neg_one = LinearTerm::from_i128(-1);
        let neg_s = s.negate();

        let t_ge_1 = self.le(&one, t);
        let t_le_neg1 = self.le(t, &neg_one);
        let s_ge_0 = self.le(&zero, s);
        let s_le_0 = self.le(s, &zero);

        // Row 1: t ≥ 1 ∧ s ≥ 0 ⇒ 0 ≤ q ≤ s
        let c1 = self.bdd.and(t_ge_1, s_ge_0);
        let r1_a = self.le(&zero, q);
        let r1_b = self.le(q, s);
        let r1 = self.bdd.and(r1_a, r1_b);
        let imp1 = self.bdd.implies(c1, r1);

        // Row 2: t ≥ 1 ∧ s ≤ 0 ⇒ s ≤ q ≤ 0
        let c2 = self.bdd.and(t_ge_1, s_le_0);
        let r2_a = self.le(s, q);
        let r2_b = self.le(q, &zero);
        let r2 = self.bdd.and(r2_a, r2_b);
        let imp2 = self.bdd.implies(c2, r2);

        // Row 3: t ≤ -1 ∧ s ≥ 0 ⇒ -s ≤ q ≤ 0
        let c3 = self.bdd.and(t_le_neg1, s_ge_0);
        let r3_a = self.le(&neg_s, q);
        let r3_b = self.le(q, &zero);
        let r3 = self.bdd.and(r3_a, r3_b);
        let imp3 = self.bdd.implies(c3, r3);

        // Row 4: t ≤ -1 ∧ s ≤ 0 ⇒ 0 ≤ q ≤ -s
        let c4 = self.bdd.and(t_le_neg1, s_le_0);
        let r4_a = self.le(&zero, q);
        let r4_b = self.le(q, &neg_s);
        let r4 = self.bdd.and(r4_a, r4_b);
        let imp4 = self.bdd.implies(c4, r4);

        let a = self.bdd.and(imp1, imp2);
        let b = self.bdd.and(imp3, imp4);
        self.bdd.and(a, b)
    }

    fn instantiate_a8_rem(&mut self, r: &LinearTerm, s: &LinearTerm, t: &LinearTerm) -> Formula {
        let zero = LinearTerm::from_i128(0);
        let one = LinearTerm::from_i128(1);
        let neg_one = LinearTerm::from_i128(-1);
        let t_minus_1 = t.sub(&one);
        let one_minus_t = one.sub(t);
        let neg_t_minus_1 = t.negate().sub(&one);
        let t_plus_1 = t.add(&one);

        let t_ge_1 = self.le(&one, t);
        let t_le_neg1 = self.le(t, &neg_one);
        let s_ge_0 = self.le(&zero, s);
        let s_le_0 = self.le(s, &zero);

        // Row 1: t ≥ 1 ∧ s ≥ 0 ⇒ 0 ≤ r ≤ t - 1 ∧ r ≤ s
        let c1 = self.bdd.and(t_ge_1, s_ge_0);
        let r1_a = self.le(&zero, r);
        let r1_b = self.le(r, &t_minus_1);
        let r1_c = self.le(r, s);
        let r1_ab = self.bdd.and(r1_a, r1_b);
        let r1 = self.bdd.and(r1_ab, r1_c);
        let imp1 = self.bdd.implies(c1, r1);

        // Row 2: t ≥ 1 ∧ s ≤ 0 ⇒ -(t - 1) ≤ r ≤ 0 ∧ r ≥ s
        let c2 = self.bdd.and(t_ge_1, s_le_0);
        let r2_a = self.le(&one_minus_t, r);
        let r2_b = self.le(r, &zero);
        let r2_c = self.le(s, r);
        let r2_ab = self.bdd.and(r2_a, r2_b);
        let r2 = self.bdd.and(r2_ab, r2_c);
        let imp2 = self.bdd.implies(c2, r2);

        // Row 3: t ≤ -1 ∧ s ≥ 0 ⇒ 0 ≤ r ≤ -t - 1
        let c3 = self.bdd.and(t_le_neg1, s_ge_0);
        let r3_a = self.le(&zero, r);
        let r3_b = self.le(r, &neg_t_minus_1);
        let r3 = self.bdd.and(r3_a, r3_b);
        let imp3 = self.bdd.implies(c3, r3);

        // Row 4: t ≤ -1 ∧ s ≤ 0 ⇒ t + 1 ≤ r ≤ 0
        let c4 = self.bdd.and(t_le_neg1, s_le_0);
        let r4_a = self.le(&t_plus_1, r);
        let r4_b = self.le(r, &zero);
        let r4 = self.bdd.and(r4_a, r4_b);
        let imp4 = self.bdd.implies(c4, r4);

        let a = self.bdd.and(imp1, imp2);
        let b = self.bdd.and(imp3, imp4);
        self.bdd.and(a, b)
    }

    pub fn lemma_formula(&mut self, lemma: &TheoryLemma) -> Formula {
        let mut conj = bdd::TRUE;
        for &(atom_id, polarity) in &lemma.literals {
            let lit = self.bdd.literal(self.first_theory_var + atom_id, polarity);
            conj = self.bdd.and(conj, lit);
        }
        self.bdd.not(conj)
    }

    fn complete_int_model(
        &self,
        candidate_literals: &[(TheoryAtomId, bool)],
        assignment: &BTreeMap<usize, bool>,
        int_model: &mut BTreeMap<TermId, Int>,
    ) {
        let mut constrained = HashSet::new();
        for &(atom_id, _) in candidate_literals {
            for &var in self.theory_atoms[atom_id].coeffs.keys() {
                constrained.insert(var);
            }
        }
        let u32_max = Int::power_of_two(32).minus(&Int::from_u64(1));

        for _ in 0..8 {
            let mut changed = false;
            for (id, term) in self.terms.iter().enumerate() {
                if constrained.contains(&id) {
                    continue;
                }
                let val = match term {
                    AtomTerm::UsizeMax => Some(u32_max.clone()),
                    AtomTerm::DivConst(t, k) => {
                        Some(t.eval(int_model).divide(k).map_or(Int::zero(), |p| p.0))
                    }
                    AtomTerm::Div(s, t) => Some(
                        s.eval(int_model)
                            .divide(&t.eval(int_model))
                            .map_or(Int::zero(), |p| p.0),
                    ),
                    AtomTerm::Rem(s, t) => Some(
                        s.eval(int_model)
                            .divide(&t.eval(int_model))
                            .map_or(Int::zero(), |p| p.1),
                    ),
                    AtomTerm::Mul { left, right, .. } => {
                        Some(left.eval(int_model).times(&right.eval(int_model)))
                    }
                    AtomTerm::Len(base) => base.as_var().and_then(|bid| match &self.terms[bid] {
                        AtomTerm::VecLit(items) => Some(Int::from_u64(items.len() as u64)),
                        AtomTerm::EmptyMap => Some(Int::zero()),
                        _ => None,
                    }),
                    AtomTerm::VariantTag { base, .. } => {
                        base.as_var().and_then(|bid| match &self.terms[bid] {
                            AtomTerm::VariantCtor { ctor_idx, .. } => {
                                Some(Int::from_u64(*ctor_idx as u64))
                            }
                            _ => None,
                        })
                    }
                    AtomTerm::Var { .. }
                    | AtomTerm::PureAlt(_, _)
                    | AtomTerm::PurePay(_, _, _, _)
                    | AtomTerm::StrLit(_)
                    | AtomTerm::EmptyMap
                    | AtomTerm::VecLit(_)
                    | AtomTerm::StructCtor(_, _)
                    | AtomTerm::Field { .. }
                    | AtomTerm::VariantCtor { .. }
                    | AtomTerm::Index { .. }
                    | AtomTerm::Update { .. }
                    | AtomTerm::Trim(_) => None,
                };
                if let Some(v) = val
                    && int_model.get(&id) != Some(&v)
                {
                    int_model.insert(id, v);
                    changed = true;
                }
            }

            let full = self.complete_bool_model(assignment, int_model);
            for (guard, var_id, rhs) in &self.definitions {
                if constrained.contains(var_id) || !self.bdd.evaluate(*guard, &full) {
                    continue;
                }
                let v = match rhs {
                    DefRhs::Linear(term) => term.eval(int_model),
                    DefRhs::BoolFormula(phi) => {
                        let b = self.bdd.evaluate(*phi, &full);
                        Int::from_u64(u64::from(b))
                    }
                };
                if int_model.get(var_id) != Some(&v) {
                    int_model.insert(*var_id, v);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
    }

    fn complete_bool_model(
        &self,
        assignment: &BTreeMap<usize, bool>,
        int_model: &BTreeMap<TermId, Int>,
    ) -> BTreeMap<usize, bool> {
        let mut full = BTreeMap::new();
        for var in 0..self.first_theory_var {
            full.insert(var, assignment.get(&var).copied().unwrap_or(false));
        }
        for (atom_id, atom) in self.theory_atoms.iter().enumerate() {
            let var = self.first_theory_var + atom_id;
            let holds = atom.holds(int_model);
            full.insert(var, holds);
        }
        full
    }

    /// Decides whether `negated_goal` (`¬F` for [N1], `G ∧ ¬φ` for [N2]) is
    /// unsatisfiable under `Ω` and `Ψ` (`docs/v2/facts.md`, section 7).
    pub fn decide(
        &mut self,
        negated_goal: Formula,
        visible_vars: &[(String, TermId, bool)],
        in_loop: bool,
    ) -> Decision {
        self.instantiate_all();
        let mut query = negated_goal;
        let mut working = negated_goal;
        let mut added_structure = vec![false; self.structure.len()];
        let mut added_facts = vec![false; self.facts.len()];
        let mut added_instances = vec![false; self.instances.len()];
        let mut added_lemmas = vec![false; self.lemmas.len()];
        let mut used_instances = Vec::new();
        let mut used_lemmas = Vec::new();
        let mut budget = self.step_limit;

        for (idx, &s) in self.structure.iter().enumerate() {
            query = self.bdd.and(query, s);
            working = self.bdd.and(working, s);
            added_structure[idx] = true;
        }

        'search: while let Some(assignment) = self.bdd.witness(working) {
            if budget == 0 {
                return Decision::Limit {
                    steps: self.step_limit,
                };
            }
            budget -= 1;
            for (idx, added) in added_lemmas.iter_mut().enumerate() {
                if *added {
                    continue;
                }
                let matches_all = self.lemmas[idx].literals.iter().all(|&(atom_id, pol)| {
                    assignment.get(&(self.first_theory_var + atom_id)).copied() == Some(pol)
                });
                if matches_all {
                    *added = true;
                    let lemma = self.lemmas[idx].clone();
                    let lf = self.lemma_formula(&lemma);
                    working = self.bdd.and(working, lf);
                    used_lemmas.push(lemma);
                    continue 'search;
                }
            }

            let mut candidate_literals = Vec::new();
            for (&bdd_var, &polarity) in &assignment {
                if bdd_var >= self.first_theory_var {
                    candidate_literals.push((bdd_var - self.first_theory_var, polarity));
                }
            }

            let rows: Vec<Row> = candidate_literals
                .iter()
                .map(|&(atom_id, polarity)| {
                    let atom = &self.theory_atoms[atom_id];
                    if polarity {
                        atom.clone()
                    } else {
                        atom.complement()
                    }
                })
                .collect();
            match lia::solve(&rows, &mut budget) {
                lia::Outcome::Limit => {
                    return Decision::Limit {
                        steps: self.step_limit,
                    };
                }
                lia::Outcome::Unsat { proof, literals } => {
                    let lemma = TheoryLemma {
                        literals: literals
                            .iter()
                            .map(|index| candidate_literals[*index])
                            .collect(),
                        proof,
                    };
                    let lf = self.lemma_formula(&lemma);
                    working = self.bdd.and(working, lf);
                    self.lemmas.push(lemma.clone());
                    added_lemmas.push(true);
                    used_lemmas.push(lemma);
                }
                lia::Outcome::Sat(mut int_model) => {
                    if let Some(row) = rows.iter().find(|row| !row.holds(&int_model)) {
                        return Decision::Fault(format!(
                            "the theory check gave a model that fails the row {row:?}"
                        ));
                    }
                    self.complete_int_model(&candidate_literals, &assignment, &mut int_model);
                    let full_bool_model = self.complete_bool_model(&assignment, &int_model);

                    for (idx, &s) in self.structure.iter().enumerate() {
                        if !added_structure[idx] && !self.bdd.evaluate(s, &full_bool_model) {
                            added_structure[idx] = true;
                            query = self.bdd.and(query, s);
                            working = self.bdd.and(working, s);
                            continue 'search;
                        }
                    }

                    for (idx, &f) in self.facts.iter().enumerate() {
                        if !added_facts[idx] && !self.bdd.evaluate(f, &full_bool_model) {
                            added_facts[idx] = true;
                            query = self.bdd.and(query, f);
                            working = self.bdd.and(working, f);
                            continue 'search;
                        }
                    }

                    for (idx, added) in added_instances.iter_mut().enumerate() {
                        if !*added
                            && !self
                                .bdd
                                .evaluate(self.instances[idx].formula, &full_bool_model)
                        {
                            *added = true;
                            let inst = self.instances[idx].clone();
                            working = self.bdd.and(working, inst.formula);
                            used_instances.push(inst);
                            continue 'search;
                        }
                    }

                    return match self.build_counterexample(
                        query,
                        full_bool_model,
                        int_model,
                        visible_vars,
                        in_loop,
                    ) {
                        Ok(cex) => Decision::Refuted(Box::new(cex)),
                        Err(fault) => Decision::Fault(fault),
                    };
                }
            }
        }

        Decision::Proved(Certificate {
            bdd: self.bdd.clone(),
            first_theory_var: self.first_theory_var,
            theory_atoms: self.theory_atoms.clone(),
            query,
            instances: used_instances,
            lemmas: used_lemmas,
        })
    }

    fn build_counterexample(
        &self,
        query: Formula,
        bool_model: BTreeMap<usize, bool>,
        int_model: BTreeMap<TermId, Int>,
        visible_vars: &[(String, TermId, bool)],
        in_loop: bool,
    ) -> Result<Counterexample, String> {
        // [M1]: the query is evaluated in the model before it is shown.
        if !self.bdd.evaluate(query, &bool_model) {
            return Err("the model of a counterexample fails the query".to_string());
        }
        for (&bdd_var, &polarity) in &bool_model {
            if bdd_var >= self.first_theory_var {
                let atom = &self.theory_atoms[bdd_var - self.first_theory_var];
                if atom.holds(&int_model) != polarity {
                    return Err(format!(
                        "the model of a counterexample disagrees with itself on the row {atom:?}"
                    ));
                }
            }
        }

        let mut history = Vec::new();
        for (idx, (site, alt)) in self.history_names.iter().enumerate() {
            if bool_model.get(&idx).copied().unwrap_or(false) && !site.starts_with('_') {
                history.push((site.clone(), alt.clone()));
            }
        }

        let mut values = BTreeMap::new();
        for (name, term_id, is_bool) in visible_vars {
            if name.starts_with('_') {
                continue;
            }
            let val = int_model.get(term_id).cloned().unwrap_or_default();
            let shown = if *is_bool {
                (!val.is_zero()).to_string()
            } else {
                val.to_string()
            };
            values.insert(name.clone(), shown);
        }

        // [M3]: Check if any nonlinear symbol (`Mul`, `Div`, `Rem`) was given
        // an assumed value in `int_model` that differs from the real operation
        // on the model's arguments.
        let mut assumed_remark = None;
        for (id, term) in self.terms.iter().enumerate() {
            let Some(chosen) = int_model.get(&id) else {
                continue;
            };
            match term {
                AtomTerm::Mul { left, right, .. } => {
                    let real = left.eval(&int_model).times(&right.eval(&int_model));
                    if *chosen != real {
                        assumed_remark = Some(
                            "depends on `*`, which the linear logic bounds only by declared intervals"
                                .to_string(),
                        );
                        break;
                    }
                }
                AtomTerm::Div(s, t) => {
                    let denom = t.eval(&int_model);
                    if let Some((q, _)) = s.eval(&int_model).divide(&denom)
                        && *chosen != q
                    {
                        assumed_remark = Some(
                            "depends on `÷` by a variable, which the linear logic bounds only by sign and magnitude"
                                .to_string(),
                        );
                        break;
                    }
                }
                AtomTerm::Rem(s, t) => {
                    let denom = t.eval(&int_model);
                    if let Some((_, r)) = s.eval(&int_model).divide(&denom)
                        && *chosen != r
                    {
                        assumed_remark = Some(
                            "depends on `mod` by a variable, which the linear logic bounds only by sign and magnitude"
                                .to_string(),
                        );
                        break;
                    }
                }
                _ => {}
            }
        }

        // [M7]: Check if two vectors, strings, or maps have distinct model values
        // although they agree in length and every mentioned element.
        let mut extensionality_note = None;
        let len_for_val = |v: &Int| -> Option<Int> {
            for (tid, term) in self.terms.iter().enumerate() {
                if let AtomTerm::Len(base) = term
                    && base.eval(&int_model) == *v
                {
                    return Some(int_model.get(&tid).cloned().unwrap_or_default());
                }
            }
            None
        };
        let mut idx_entries: Vec<(Int, Int, Int)> = Vec::new();
        for (tid, term) in self.terms.iter().enumerate() {
            if let AtomTerm::Index { base, index, .. } = term {
                idx_entries.push((
                    base.eval(&int_model),
                    index.eval(&int_model),
                    int_model.get(&tid).cloned().unwrap_or_default(),
                ));
            }
        }
        'm7: for i in 0..visible_vars.len() {
            let (ref name1, tid1, _) = visible_vars[i];
            if name1.starts_with('_') {
                continue;
            }
            let Some(sort1) = self.term_sorts.get(&tid1) else {
                continue;
            };
            if !sort1.is_extensional_collection() {
                continue;
            }
            let val1 = int_model.get(&tid1).cloned().unwrap_or_default();
            for (name2, tid2, _) in visible_vars.iter().skip(i + 1) {
                if name2.starts_with('_') || tid1 == *tid2 {
                    continue;
                }
                if self.term_sorts.get(tid2) != Some(sort1) {
                    continue;
                }
                let val2 = int_model.get(tid2).cloned().unwrap_or_default();
                if val1 == val2 {
                    continue;
                }
                let queried_together = bool_model.iter().any(|(&bdd_var, _)| {
                    bdd_var >= self.first_theory_var && {
                        let row = &self.theory_atoms[bdd_var - self.first_theory_var];
                        row.coeffs.contains_key(&tid1) && row.coeffs.contains_key(tid2)
                    }
                });
                if !queried_together {
                    continue;
                }
                let lens_disagree = match (len_for_val(&val1), len_for_val(&val2)) {
                    (Some(l1), Some(l2)) => l1 != l2,
                    _ => false,
                };
                if lens_disagree {
                    continue;
                }
                let mut elem_disagrees = false;
                for (b1, j1, e1) in &idx_entries {
                    if *b1 != val1 {
                        continue;
                    }
                    for (b2, j2, e2) in &idx_entries {
                        if *b2 == val2 && j1 == j2 && e1 != e2 {
                            elem_disagrees = true;
                            break;
                        }
                    }
                    if elem_disagrees {
                        break;
                    }
                }
                if !elem_disagrees {
                    extensionality_note = Some(format!(
                        "the checker cannot conclude `{name1}` and `{name2}` are equal from their length and elements alone"
                    ));
                    break 'm7;
                }
            }
        }

        Ok(Counterexample {
            history,
            values,
            assumed_remark,
            extensionality_note,
            in_loop,
            bool_model,
            int_model,
        })
    }
}
