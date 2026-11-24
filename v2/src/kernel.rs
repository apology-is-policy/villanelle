//! The certificate kernel (`docs/v2/facts.md`, section 8, [V1] to [V4]).
//!
//! The checker accepts an entailment only after [`Kernel::validate`] has
//! accepted its certificate. What the kernel is asked is a [`Query`]: the
//! goal, the premises, the terms and the rows, as the checker wrote them. What
//! the search found is a [`Certificate`]: which premises it used, the names of
//! the instances and the lemmas with their proofs.
//!
//! The kernel trusts the query and nothing in the certificate.
//!
//! - It reads a premise from the checker's list, by the position that the
//!   certificate names.
//! - It makes the formula of every instance itself, from the name and the
//!   terms, with the matcher for the axiom list that is in this file. That is
//!   how it checks that an instance is an instance ([V2]). A term that the
//!   search added to the table is a name and no more: what the theory says of
//!   a term because of what the checker wrote beside it (a type, a declared
//!   interval, the number of constructors) is granted only for a term that the
//!   checker wrote.
//! - It validates the proof of every lemma by integer arithmetic ([V3]).
//! - It then conjoins the goal, the premises, the instances and the lemmas in
//!   a diagram of its own and requires the result to be false.
//!
//! It shares no code with the search ([`crate::facts`], [`crate::lia`]). It
//! uses the mathematical integers, the diagram and the data of
//! [`crate::terms`], and has its own arithmetic on rows and linear terms. So a
//! defect in the search can cause a rejection or a compiler error, and cannot
//! cause a wrong acceptance. That the query is the right one for the program
//! is outside the kernel ([V4]).

use crate::bdd::{self, Bdd, Formula};
use crate::int::Int;
use crate::terms::{
    AtomTerm, Certificate, End, Instance, LinearTerm, Part, Proof, Row, Step, TermId, TheoryLemma,
};
use crate::typed::{IntType, StructId};
use std::collections::{BTreeMap, HashMap};

/// What the kernel is asked: whether `goal`, the premises and the theory have
/// no model together. Everything here is the checker's. `goal` is the negated
/// goal: `¬F` for [N1] and `G ∧ ¬φ` for [N2].
#[derive(Clone, Copy)]
pub struct Query<'a> {
    /// The diagram in which `goal`, `structure` and `facts` are written.
    pub diagram: &'a Bdd,
    /// The variable of the row at position `k` of `atoms` is
    /// `first_theory_var + k`. The variables below are the history atoms.
    pub first_theory_var: usize,
    pub terms: &'a [AtomTerm],
    /// Whether the checker wrote the term at each position.
    pub given: &'a [bool],
    /// The number of fields of each struct.
    pub arities: &'a BTreeMap<StructId, usize>,
    pub atoms: &'a [Row],
    /// `Ω`.
    pub structure: &'a [Formula],
    /// `Ψ`.
    pub facts: &'a [Formula],
    pub goal: Formula,
}

fn one() -> Int {
    Int::from_u64(1)
}

fn magnitude(value: &Int) -> Int {
    if value.is_negative() {
        value.negate()
    } else {
        value.clone()
    }
}

fn common_factor(a: &Int, b: &Int) -> Int {
    let (mut x, mut y) = (magnitude(a), magnitude(b));
    while !y.is_zero() {
        let (_, remainder) = x.divide(&y).expect("the divisor is not zero");
        x = y;
        y = remainder;
    }
    x
}

/// The row that holds exactly when `row` does not, over the integers.
fn complement(row: &Row) -> Row {
    Row {
        coeffs: row
            .coeffs
            .iter()
            .map(|(term, coeff)| (*term, coeff.negate()))
            .collect(),
        rhs: row.rhs.negate().minus(&one()),
    }
}

/// `⌊a / d⌋` for `d ≥ 1`.
fn floor(a: &Int, d: &Int) -> Int {
    let (quotient, remainder) = a.divide(d).expect("the divisor is positive");
    if a.is_negative() && !remainder.is_zero() {
        quotient.minus(&one())
    } else {
        quotient
    }
}

fn constant(value: Int) -> LinearTerm {
    LinearTerm {
        constant: value,
        coeffs: BTreeMap::new(),
    }
}

fn number(value: i128) -> LinearTerm {
    constant(Int::from_i128(value))
}

fn variable(term: TermId) -> LinearTerm {
    LinearTerm {
        constant: Int::zero(),
        coeffs: BTreeMap::from([(term, one())]),
    }
}

/// The term, if the linear term is one atomic term and nothing else.
fn as_variable(term: &LinearTerm) -> Option<TermId> {
    if !term.constant.is_zero() || term.coeffs.len() != 1 {
        return None;
    }
    let (id, coeff) = term.coeffs.iter().next()?;
    (*coeff == one()).then_some(*id)
}

/// `a + factor · b`.
fn plus_scaled(a: &LinearTerm, b: &LinearTerm, factor: &Int) -> LinearTerm {
    let mut coeffs = a.coeffs.clone();
    for (term, coeff) in &b.coeffs {
        let sum = coeffs
            .get(term)
            .cloned()
            .unwrap_or_default()
            .plus(&coeff.times(factor));
        if sum.is_zero() {
            coeffs.remove(term);
        } else {
            coeffs.insert(*term, sum);
        }
    }
    LinearTerm {
        constant: a.constant.plus(&b.constant.times(factor)),
        coeffs,
    }
}

fn sum(a: &LinearTerm, b: &LinearTerm) -> LinearTerm {
    plus_scaled(a, b, &one())
}

fn difference(a: &LinearTerm, b: &LinearTerm) -> LinearTerm {
    plus_scaled(a, b, &one().negate())
}

fn scaled(a: &LinearTerm, factor: &Int) -> LinearTerm {
    plus_scaled(&LinearTerm::default(), a, factor)
}

fn negated(a: &LinearTerm) -> LinearTerm {
    scaled(a, &one().negate())
}

/// Whether the row holds for the values given. A term without a value is 0.
fn row_holds(row: &Row, values: &BTreeMap<TermId, Int>) -> bool {
    let mut left = Int::zero();
    for (term, coeff) in &row.coeffs {
        if let Some(value) = values.get(term) {
            left = left.plus(&coeff.times(value));
        }
    }
    left <= row.rhs
}

/// The row that a step derives from the rows of its path.
fn derive(
    step: &Step,
    literals: &[(usize, bool)],
    atoms: &[Row],
    path: &[Row],
) -> Result<Row, String> {
    match step {
        Step::Literal(index) => {
            let Some(&(atom, positive)) = literals.get(*index) else {
                return Err(format!("the lemma has no literal {index}"));
            };
            let Some(row) = atoms.get(atom) else {
                return Err(format!("there is no theory atom {atom}"));
            };
            Ok(if positive {
                row.clone()
            } else {
                complement(row)
            })
        }
        Step::Combine(parts) => {
            if parts.is_empty() {
                return Err("a sum of no rows".to_string());
            }
            let mut coeffs: BTreeMap<usize, Int> = BTreeMap::new();
            let mut rhs = Int::zero();
            for (source, multiplier) in parts {
                let Some(row) = path.get(*source) else {
                    return Err(format!("row {source} is not on the path"));
                };
                if multiplier.is_negative() || multiplier.is_zero() {
                    return Err(format!("the multiplier {multiplier} is not positive"));
                }
                for (term, coeff) in &row.coeffs {
                    let sum = coeffs
                        .get(term)
                        .cloned()
                        .unwrap_or_default()
                        .plus(&coeff.times(multiplier));
                    if sum.is_zero() {
                        coeffs.remove(term);
                    } else {
                        coeffs.insert(*term, sum);
                    }
                }
                rhs = rhs.plus(&row.rhs.times(multiplier));
            }
            Ok(Row { coeffs, rhs })
        }
        Step::Round { source, divisor } => {
            let Some(row) = path.get(*source) else {
                return Err(format!("row {source} is not on the path"));
            };
            if *divisor < one() {
                return Err(format!("the divisor {divisor} is not positive"));
            }
            let mut coeffs = BTreeMap::new();
            for (term, coeff) in &row.coeffs {
                let (quotient, remainder) = coeff.divide(divisor).expect("a positive divisor");
                if !remainder.is_zero() {
                    return Err(format!(
                        "the divisor {divisor} does not divide the coefficient {coeff}"
                    ));
                }
                coeffs.insert(*term, quotient);
            }
            Ok(Row {
                coeffs,
                rhs: floor(&row.rhs, divisor),
            })
        }
    }
}

/// Validates one branch of a proof, and the branches below it. `path` holds
/// the rows of the branches above.
fn branch(
    proof: &Proof,
    literals: &[(usize, bool)],
    atoms: &[Row],
    path: &mut Vec<Row>,
) -> Result<(), String> {
    let base = path.len();
    for (index, step) in proof.steps.iter().enumerate() {
        let row = derive(step, literals, atoms, path)
            .map_err(|error| format!("row {}: {error}", base + index))?;
        path.push(row);
    }
    match &proof.end {
        End::Close(row) => {
            let Some(row) = path.get(*row) else {
                return Err(format!("the closing row {row} is not on the path"));
            };
            if !row.coeffs.is_empty() || !row.rhs.is_negative() {
                return Err("the closing row is not `0 ≤ b` with `b < 0`".to_string());
            }
        }
        End::Split {
            form,
            bound,
            low,
            high,
        } => {
            if form.values().any(Int::is_zero) {
                return Err("a split on a term with the coefficient 0".to_string());
            }
            // `form ≤ bound`, and then `form ≥ bound + 1`: every integer
            // value of the form is in one of the two.
            let split = path.len();
            let at_most = Row {
                coeffs: form.clone(),
                rhs: bound.clone(),
            };
            let above = complement(&at_most);
            path.push(at_most);
            branch(low, literals, atoms, path)?;
            path.truncate(split);
            path.push(above);
            branch(high, literals, atoms, path)?;
        }
    }
    path.truncate(base);
    Ok(())
}

/// Validates the proof of a [`TheoryLemma`] against the atoms that its
/// literals name ([V3]): every branch of the tree ends in a contradiction.
pub fn validate_lemma(lemma: &TheoryLemma, theory_atoms: &[Row]) -> Result<(), String> {
    branch(&lemma.proof, &lemma.literals, theory_atoms, &mut Vec::new())
}

/// The kernel, for the queries of one body. The checker's lists only grow
/// while a body is checked, so what the kernel has read of them stays true,
/// and it keeps its diagram and its indexes from one query to the next. A
/// kernel must not be given the queries of two bodies.
#[derive(Default)]
pub struct Kernel {
    /// The kernel's own diagram. No formula of the search is in it.
    diagram: Bdd,
    /// The checker's formulas that were copied into it.
    imported: HashMap<Formula, Formula>,
    /// The position of each row in the table of the query.
    atoms: HashMap<Row, usize>,
    atoms_read: usize,
    /// The position of each term in the table of the query.
    terms: HashMap<AtomTerm, TermId>,
    terms_read: usize,
    /// The instances already made.
    instances: HashMap<Instance, Formula>,
}

/// Validates one certificate with a kernel of its own.
pub fn validate(query: &Query, certificate: &Certificate) -> Result<(), String> {
    Kernel::new().validate(query, certificate)
}

impl Kernel {
    pub fn new() -> Kernel {
        Kernel::default()
    }

    /// Validates a certificate for a query ([V1] to [V3]).
    pub fn validate(&mut self, query: &Query, certificate: &Certificate) -> Result<(), String> {
        self.read(query)?;
        let mut total = self.import(query, query.goal);
        for (position, part) in certificate.parts.iter().enumerate() {
            let formula = match part {
                Part::Structure(index) => match query.structure.get(*index) {
                    Some(formula) => Ok(self.import(query, *formula)),
                    None => Err(format!("`Ω` has no formula {index}")),
                },
                Part::Fact(index) => match query.facts.get(*index) {
                    Some(formula) => Ok(self.import(query, *formula)),
                    None => Err(format!("`Ψ` has no fact {index}")),
                },
                Part::Instance(instance) => self.instance(query, instance),
                Part::Lemma(lemma) => self.lemma(query, lemma),
            }
            .map_err(|error| format!("part {position}: {error}"))?;
            total = self.diagram.and(total, formula);
        }
        if total != bdd::FALSE {
            return Err(
                "the goal, the premises, the instances and the lemmas leave a case open"
                    .to_string(),
            );
        }
        Ok(())
    }

    /// The formula of an instance, in the kernel's diagram ([V2]). It is an
    /// error when the name is not the name of an instance.
    pub fn instance(&mut self, query: &Query, instance: &Instance) -> Result<Formula, String> {
        self.read(query)?;
        if let Some(formula) = self.instances.get(instance) {
            return Ok(*formula);
        }
        let formula = match instance {
            Instance::Term(term) => self.of_term(query, *term),
            Instance::Pair(left, right) => self.of_pair(query, *left, *right),
            Instance::Frame {
                update,
                element,
                original,
            } => self.of_frame(query, *update, *element, *original),
            Instance::Extension {
                structure,
                left,
                left_fields,
                right,
                right_fields,
            } => self.of_extension(
                query,
                *structure,
                (*left, left_fields),
                (*right, right_fields),
            ),
        }?;
        self.instances.insert(instance.clone(), formula);
        Ok(formula)
    }

    /// Whether an instance holds when the terms have the values given. The
    /// tests ask this with the values that the real operations give.
    pub fn instance_holds(
        &mut self,
        query: &Query,
        instance: &Instance,
        values: &BTreeMap<TermId, Int>,
    ) -> Result<bool, String> {
        let rows = Kernel::rows(query, values);
        self.instance_holds_for(query, instance, &rows)
    }

    /// The truth of every row of a query when the terms have the values
    /// given, by the variable of the row.
    pub fn rows(query: &Query, values: &BTreeMap<TermId, Int>) -> BTreeMap<usize, bool> {
        query
            .atoms
            .iter()
            .enumerate()
            .map(|(atom, row)| (query.first_theory_var + atom, row_holds(row, values)))
            .collect()
    }

    /// Whether an instance holds when the rows have the truth given
    /// ([`Kernel::rows`]). An instance has no row that the query has not.
    pub fn instance_holds_for(
        &mut self,
        query: &Query,
        instance: &Instance,
        rows: &BTreeMap<usize, bool>,
    ) -> Result<bool, String> {
        let formula = self.instance(query, instance)?;
        Ok(self.diagram.evaluate(formula, rows))
    }

    /// Reads what the checker's tables have gained since the last query.
    fn read(&mut self, query: &Query) -> Result<(), String> {
        if query.atoms.len() < self.atoms_read
            || query.terms.len() < self.terms_read
            || query.given.len() != query.terms.len()
        {
            return Err("the tables are not those of the body this kernel has read".to_string());
        }
        for (position, row) in query.atoms.iter().enumerate().skip(self.atoms_read) {
            self.atoms.entry(row.clone()).or_insert(position);
        }
        self.atoms_read = query.atoms.len();
        for (position, term) in query.terms.iter().enumerate().skip(self.terms_read) {
            self.terms.entry(term.clone()).or_insert(position);
        }
        self.terms_read = query.terms.len();
        Ok(())
    }

    /// Copies a formula of the checker into the kernel's diagram.
    fn import(&mut self, query: &Query, formula: Formula) -> Formula {
        if formula == bdd::FALSE || formula == bdd::TRUE {
            return formula;
        }
        if let Some(own) = self.imported.get(&formula) {
            return *own;
        }
        let node = query.diagram.node(formula);
        let low = self.import(query, node.low);
        let high = self.import(query, node.high);
        let test = self.diagram.variable(node.var);
        let when = self.diagram.and(test, high);
        let unless = self.diagram.minus(low, test);
        let own = self.diagram.or(when, unless);
        self.imported.insert(formula, own);
        own
    }

    /// `¬(l₁ ∧ … ∧ lₙ)` for a lemma whose proof refutes its literals.
    fn lemma(&mut self, query: &Query, lemma: &TheoryLemma) -> Result<Formula, String> {
        validate_lemma(lemma, query.atoms)?;
        let mut all = bdd::TRUE;
        for &(atom, positive) in &lemma.literals {
            let literal = self
                .diagram
                .literal(query.first_theory_var + atom, positive);
            all = self.diagram.and(all, literal);
        }
        Ok(self.diagram.not(all))
    }

    // The formulas of the logic, over the rows of the query.

    /// The literal of a row: the variable of its canonical form (section 7,
    /// step 2), or the negation of the variable of its complement.
    fn row(&mut self, query: &Query, row: Row) -> Result<Formula, String> {
        let mut factor = Int::zero();
        for coeff in row.coeffs.values() {
            factor = common_factor(&factor, coeff);
        }
        if factor.is_zero() {
            // No term is left: the row is `0 ≤ b`.
            return Ok(if row.rhs.is_negative() {
                bdd::FALSE
            } else {
                bdd::TRUE
            });
        }
        let row = Row {
            coeffs: row
                .coeffs
                .iter()
                .filter(|(_, coeff)| !coeff.is_zero())
                .map(|(term, coeff)| {
                    let (quotient, _) = coeff.divide(&factor).expect("a factor that is not zero");
                    (*term, quotient)
                })
                .collect(),
            rhs: floor(&row.rhs, &factor),
        };
        let positive = row
            .coeffs
            .values()
            .next()
            .is_some_and(|coeff| !coeff.is_negative());
        let canonical = if positive { row } else { complement(&row) };
        let Some(atom) = self.atoms.get(&canonical) else {
            return Err("the instance has a row that the query does not have".to_string());
        };
        Ok(self
            .diagram
            .literal(query.first_theory_var + *atom, positive))
    }

    /// `left ≤ right`.
    fn le(
        &mut self,
        query: &Query,
        left: &LinearTerm,
        right: &LinearTerm,
    ) -> Result<Formula, String> {
        let form = difference(left, right);
        self.row(
            query,
            Row {
                coeffs: form.coeffs,
                rhs: form.constant.negate(),
            },
        )
    }

    /// `left < right`, which is `left + 1 ≤ right` on integers.
    fn lt(
        &mut self,
        query: &Query,
        left: &LinearTerm,
        right: &LinearTerm,
    ) -> Result<Formula, String> {
        self.le(query, &sum(left, &number(1)), right)
    }

    /// `left = right`.
    fn eq(
        &mut self,
        query: &Query,
        left: &LinearTerm,
        right: &LinearTerm,
    ) -> Result<Formula, String> {
        let at_most = self.le(query, left, right)?;
        let at_least = self.le(query, right, left)?;
        Ok(self.diagram.and(at_most, at_least))
    }

    /// `low ≤ middle ≤ high`.
    fn between(
        &mut self,
        query: &Query,
        low: &LinearTerm,
        middle: &LinearTerm,
        high: &LinearTerm,
    ) -> Result<Formula, String> {
        let above = self.le(query, low, middle)?;
        let below = self.le(query, middle, high)?;
        Ok(self.diagram.and(above, below))
    }

    /// Every pair of the two lists is equal. The lists have one length.
    fn all_equal(
        &mut self,
        query: &Query,
        left: &[LinearTerm],
        right: &[LinearTerm],
    ) -> Result<Formula, String> {
        if left.len() != right.len() {
            return Err("two applications of one symbol differ in the number of arguments".into());
        }
        let mut all = bdd::TRUE;
        for (a, b) in left.iter().zip(right) {
            let equal = self.eq(query, a, b)?;
            all = self.diagram.and(all, equal);
        }
        Ok(all)
    }

    // The matcher for the axiom list.

    fn term<'a>(&self, query: &Query<'a>, term: TermId) -> Result<&'a AtomTerm, String> {
        query
            .terms
            .get(term)
            .ok_or_else(|| format!("there is no term u{term}"))
    }

    /// The position of a term that an instance speaks of.
    fn find(&self, term: &AtomTerm) -> Result<TermId, String> {
        self.terms
            .get(term)
            .copied()
            .ok_or_else(|| "the instance has a term that the query does not have".to_string())
    }

    /// That the checker wrote the term. What stands beside a term (a type, a
    /// declared interval, the number of constructors) is the checker's to
    /// say, and the search's addition of a term says nothing.
    fn written(&self, query: &Query, term: TermId) -> Result<(), String> {
        if query.given.get(term) == Some(&true) {
            Ok(())
        } else {
            Err(format!(
                "the checker did not write the term u{term}, so nothing is known of it by its type"
            ))
        }
    }

    /// `0 ≤ u ≤ usize.max`.
    fn within_usize(&mut self, query: &Query, u: &LinearTerm) -> Result<Formula, String> {
        let greatest = variable(self.find(&AtomTerm::UsizeMax)?);
        self.between(query, &number(0), u, &greatest)
    }

    /// The range of an integer type ([A1]).
    fn within(&mut self, query: &Query, u: &LinearTerm, ty: IntType) -> Result<Formula, String> {
        let bits = |bits: u32, signed: bool| {
            if signed {
                let half = Int::power_of_two(bits - 1);
                (half.negate(), half.minus(&one()))
            } else {
                (Int::zero(), Int::power_of_two(bits).minus(&one()))
            }
        };
        let (least, greatest) = match ty {
            IntType::Usize => return self.within_usize(query, u),
            IntType::U8 => bits(8, false),
            IntType::U16 => bits(16, false),
            IntType::U32 => bits(32, false),
            IntType::U64 => bits(64, false),
            IntType::I8 => bits(8, true),
            IntType::I16 => bits(16, true),
            IntType::I32 => bits(32, true),
            IntType::I64 => bits(64, true),
        };
        self.between(query, &constant(least), u, &constant(greatest))
    }

    /// The range of a part of a value ([A1]): a field or an element of a
    /// value term. A part of a constructor term or of an update term is
    /// whatever was put there, and has none.
    fn part_range(
        &mut self,
        query: &Query,
        id: TermId,
        base: &LinearTerm,
        (int_ty, is_bool, is_value_term): (Option<IntType>, bool, bool),
    ) -> Result<Formula, String> {
        if !is_value_term {
            return Err(format!("the term u{id} is not a value term"));
        }
        self.written(query, id)?;
        let made = as_variable(base).is_some_and(|base| {
            matches!(
                query.terms.get(base),
                Some(
                    AtomTerm::StructCtor(_, _)
                        | AtomTerm::VariantCtor { .. }
                        | AtomTerm::VecLit(_, _)
                        | AtomTerm::EmptyMap(_, _)
                        | AtomTerm::Update { .. }
                )
            )
        });
        if made {
            return Err(format!(
                "the term u{id} is a part of a constructor or update term"
            ));
        }
        let u = variable(id);
        match (int_ty, is_bool) {
            (Some(ty), _) => self.within(query, &u, ty),
            (None, true) => self.between(query, &number(0), &u, &number(1)),
            (None, false) => Err(format!("the term u{id} has no range")),
        }
    }

    /// What the theory says of one term by itself.
    fn of_term(&mut self, query: &Query, id: TermId) -> Result<Formula, String> {
        let u = variable(id);
        match self.term(query, id)? {
            // [A1].
            AtomTerm::Var {
                ty: Some(ty),
                is_value_term: true,
                ..
            } => {
                self.written(query, id)?;
                self.within(query, &u, *ty)
            }
            AtomTerm::Field {
                base,
                int_ty,
                is_bool,
                is_value_term,
                ..
            }
            | AtomTerm::Index {
                base,
                int_ty,
                is_bool,
                is_value_term,
                ..
            } => self.part_range(query, id, base, (*int_ty, *is_bool, *is_value_term)),
            // [A2]: `2³² - 1 ≤ usize.max ≤ 2⁶⁴ - 1`.
            AtomTerm::UsizeMax => {
                let least = Int::power_of_two(32).minus(&one());
                let greatest = Int::power_of_two(64).minus(&one());
                self.between(query, &constant(least), &u, &constant(greatest))
            }
            // [A3]: `0 ≤ len(t) ≤ usize.max`.
            AtomTerm::Len(_) => self.within_usize(query, &u),
            // [A3]: `len([t₁, …, tₙ]) = n` and `len(∅) = 0`.
            AtomTerm::VecLit(_, items) => {
                let length = variable(self.find(&AtomTerm::Len(u.clone()))?);
                self.eq(query, &length, &number(items.len() as i128))
            }
            AtomTerm::EmptyMap(_, _) => {
                let length = variable(self.find(&AtomTerm::Len(u.clone()))?);
                self.eq(query, &length, &number(0))
            }
            // [A5]: `V.c {t̄} is c`, written with the number of `c`.
            AtomTerm::VariantCtor {
                variant_id,
                ctor_idx,
                num_ctors,
                ..
            } => {
                self.written(query, id)?;
                if ctor_idx >= num_ctors {
                    return Err(format!("the variant has no constructor {ctor_idx}"));
                }
                let tag = variable(self.find(&AtomTerm::VariantTag {
                    base: u.clone(),
                    variant_id: *variant_id,
                    num_ctors: *num_ctors,
                })?);
                self.eq(query, &tag, &number(*ctor_idx as i128))
            }
            // [A5]: `t is c` holds for one constructor of the type of `t`.
            AtomTerm::VariantTag {
                base,
                variant_id,
                num_ctors,
            } => {
                let of_constructor = as_variable(base).is_some_and(|base| {
                    query.given.get(base) == Some(&true)
                        && matches!(
                            query.terms.get(base),
                            Some(AtomTerm::VariantCtor { variant_id: v, num_ctors: n, .. })
                                if v == variant_id && n == num_ctors
                        )
                });
                if !of_constructor {
                    self.written(query, id)?;
                }
                let last = (*num_ctors).max(1) - 1;
                self.between(query, &number(0), &u, &number(last as i128))
            }
            // [A6]: `len(t[i ↦ e]) = len(t)`, and `0 ≤ i < len(t)` implies
            // `t[i ↦ e][i] = e`.
            AtomTerm::Update { base, index, value } => {
                let length = variable(self.find(&AtomTerm::Len(u.clone()))?);
                let length_before = variable(self.find(&AtomTerm::Len(base.clone()))?);
                let element = variable(self.find(&AtomTerm::Index {
                    base: u.clone(),
                    index: index.clone(),
                    int_ty: None,
                    is_bool: false,
                    is_value_term: false,
                })?);
                let same_length = self.eq(query, &length, &length_before)?;
                let from_zero = self.le(query, &number(0), index)?;
                let below_length = self.lt(query, index, &length_before)?;
                let in_range = self.diagram.and(from_zero, below_length);
                let written = self.eq(query, &element, value)?;
                let read_back = self.diagram.implies(in_range, written);
                Ok(self.diagram.and(same_length, read_back))
            }
            // [A7], for `q = t ÷ k` with a literal `k ≥ 1`:
            //   t ≥ 0  implies  k·q ≤ t ≤ k·q + (k - 1)
            //   t ≤ 0  implies  k·q - (k - 1) ≤ t ≤ k·q
            AtomTerm::DivConst(t, k) => {
                if *k < one() {
                    return Err(format!(
                        "a quotient by the literal {k}, which is not positive"
                    ));
                }
                let kq = scaled(&u, k);
                let rest = constant(k.minus(&one()));
                let not_negative = self.le(query, &number(0), t)?;
                let then = self.between(query, &kq, t, &sum(&kq, &rest))?;
                let first = self.diagram.implies(not_negative, then);
                let not_positive = self.le(query, t, &number(0))?;
                let then = self.between(query, &difference(&kq, &rest), t, &kq)?;
                let second = self.diagram.implies(not_positive, then);
                Ok(self.diagram.and(first, second))
            }
            // [A8], for `q = div(s, t)`.
            AtomTerm::Div(s, t) => {
                let zero = number(0);
                let minus_s = negated(s);
                let cases = [
                    (true, true, &zero, s),
                    (true, false, s, &zero),
                    (false, true, &minus_s, &zero),
                    (false, false, &zero, &minus_s),
                ];
                let mut all = bdd::TRUE;
                for (divisor_positive, dividend_positive, low, high) in cases {
                    let when = self.signs(query, s, t, divisor_positive, dividend_positive)?;
                    let then = self.between(query, low, &u, high)?;
                    let case = self.diagram.implies(when, then);
                    all = self.diagram.and(all, case);
                }
                Ok(all)
            }
            // [A8], for `r = rem(s, t)`.
            AtomTerm::Rem(s, t) => {
                let zero = number(0);
                let t_less_one = difference(t, &number(1));
                let one_less_t = negated(&t_less_one);
                let minus_t_less_one = difference(&negated(t), &number(1));
                let t_and_one = sum(t, &number(1));
                // The bounds of `r`, and whether `r ≤ s` (`Some(true)`) or
                // `r ≥ s` (`Some(false)`) is known too.
                let cases = [
                    (true, true, &zero, &t_less_one, Some(true)),
                    (true, false, &one_less_t, &zero, Some(false)),
                    (false, true, &zero, &minus_t_less_one, None),
                    (false, false, &t_and_one, &zero, None),
                ];
                let mut all = bdd::TRUE;
                for (divisor_positive, dividend_positive, low, high, by_dividend) in cases {
                    let when = self.signs(query, s, t, divisor_positive, dividend_positive)?;
                    let mut then = self.between(query, low, &u, high)?;
                    if let Some(at_most) = by_dividend {
                        let nearer = if at_most {
                            self.le(query, &u, s)?
                        } else {
                            self.le(query, s, &u)?
                        };
                        then = self.diagram.and(then, nearer);
                    }
                    let case = self.diagram.implies(when, then);
                    all = self.diagram.and(all, case);
                }
                Ok(all)
            }
            // [A9], for `w = mul(s, t)` with `s` in `[a, A]` and `t` in
            // `[b, B]`: those of the four planes whose two bounds exist.
            //   w ≥ a·t + b·s - a·b        w ≤ A·t + b·s - A·b
            //   w ≥ A·t + B·s - A·B        w ≤ a·t + B·s - a·B
            AtomTerm::Mul {
                left: s,
                right: t,
                left_bounds: (a, big_a),
                right_bounds: (b, big_b),
            } => {
                self.written(query, id)?;
                let plane = |of_s: &Int, of_t: &Int| {
                    let through = sum(&scaled(t, of_s), &scaled(s, of_t));
                    difference(&through, &constant(of_s.times(of_t)))
                };
                let mut all = bdd::TRUE;
                for (of_s, of_t, from_below) in [
                    (a, b, true),
                    (big_a, big_b, true),
                    (big_a, b, false),
                    (a, big_b, false),
                ] {
                    let (Some(of_s), Some(of_t)) = (of_s, of_t) else {
                        continue;
                    };
                    let plane = plane(of_s, of_t);
                    let bound = if from_below {
                        self.le(query, &plane, &u)?
                    } else {
                        self.le(query, &u, &plane)?
                    };
                    all = self.diagram.and(all, bound);
                }
                Ok(all)
            }
            AtomTerm::Var { .. }
            | AtomTerm::PureAlt(_, _)
            | AtomTerm::PurePay(_, _, _, _)
            | AtomTerm::StrLit(_)
            | AtomTerm::StructCtor(_, _)
            | AtomTerm::Trim(_) => Err(format!(
                "the theory says nothing of the term u{id} by itself"
            )),
        }
    }

    /// The condition of a row of [A8]: the sign of the divisor `t`, which is
    /// not zero, and of the dividend `s`.
    fn signs(
        &mut self,
        query: &Query,
        s: &LinearTerm,
        t: &LinearTerm,
        divisor_positive: bool,
        dividend_positive: bool,
    ) -> Result<Formula, String> {
        let divisor = if divisor_positive {
            self.le(query, &number(1), t)?
        } else {
            self.le(query, t, &number(-1))?
        };
        let dividend = if dividend_positive {
            self.le(query, &number(0), s)?
        } else {
            self.le(query, s, &number(0))?
        };
        Ok(self.diagram.and(divisor, dividend))
    }

    /// What the theory says of two terms together.
    fn of_pair(&mut self, query: &Query, i: TermId, j: TermId) -> Result<Formula, String> {
        /// What a pair of terms is to the theory.
        enum Rule {
            /// Two applications of one symbol ([S5]): equal arguments give
            /// equal results. A constructor is one to one as well ([A4],
            /// [A5]), so that equal results give equal arguments.
            Same {
                left: Vec<LinearTerm>,
                right: Vec<LinearTerm>,
                one_to_one: bool,
            },
            /// Different values: two string literals ([A3]), two
            /// constructors of one variant ([A5]).
            Different,
            /// [A4], `S {t̄}.xᵢ = tᵢ`: when `base` is the constructor term,
            /// the field term is the argument.
            FieldOf {
                base: LinearTerm,
                constructor: TermId,
                field: TermId,
                argument: LinearTerm,
            },
        }
        let same = |left: &[&LinearTerm], right: &[&LinearTerm]| Rule::Same {
            left: left.iter().map(|term| (*term).clone()).collect(),
            right: right.iter().map(|term| (*term).clone()).collect(),
            one_to_one: false,
        };
        let field_of = |field: TermId,
                        base: &LinearTerm,
                        index: usize,
                        constructor: TermId,
                        arguments: &[LinearTerm]| {
            arguments.get(index).map(|argument| Rule::FieldOf {
                base: base.clone(),
                constructor,
                field,
                argument: argument.clone(),
            })
        };
        let rule = match (self.term(query, i)?, self.term(query, j)?) {
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
            ) => Some(same(&[s1, t1], &[s2, t2])),
            (AtomTerm::Trim(a), AtomTerm::Trim(b)) | (AtomTerm::Len(a), AtomTerm::Len(b)) => {
                Some(same(&[a], &[b]))
            }
            (AtomTerm::PureAlt(f, a), AtomTerm::PureAlt(g, b)) if f == g => Some(Rule::Same {
                left: a.clone(),
                right: b.clone(),
                one_to_one: false,
            }),
            (AtomTerm::PurePay(f, alt1, field1, a), AtomTerm::PurePay(g, alt2, field2, b))
                if f == g && alt1 == alt2 && field1 == field2 =>
            {
                Some(Rule::Same {
                    left: a.clone(),
                    right: b.clone(),
                    one_to_one: false,
                })
            }
            (AtomTerm::StrLit(a), AtomTerm::StrLit(b)) if a != b => Some(Rule::Different),
            (AtomTerm::StructCtor(s1, a), AtomTerm::StructCtor(s2, b)) if s1 == s2 => {
                Some(Rule::Same {
                    left: a.clone(),
                    right: b.clone(),
                    one_to_one: true,
                })
            }
            (
                AtomTerm::Field {
                    base: a,
                    struct_id: s1,
                    field_idx: x1,
                    ..
                },
                AtomTerm::Field {
                    base: b,
                    struct_id: s2,
                    field_idx: x2,
                    ..
                },
            ) if s1 == s2 && x1 == x2 => Some(same(&[a], &[b])),
            (
                AtomTerm::Field {
                    base,
                    struct_id,
                    field_idx,
                    ..
                },
                AtomTerm::StructCtor(structure, arguments),
            ) if struct_id == structure => field_of(i, base, *field_idx, j, arguments),
            (
                AtomTerm::StructCtor(structure, arguments),
                AtomTerm::Field {
                    base,
                    struct_id,
                    field_idx,
                    ..
                },
            ) if struct_id == structure => field_of(j, base, *field_idx, i, arguments),
            (
                AtomTerm::VariantCtor {
                    variant_id: v1,
                    ctor_idx: c1,
                    fields: a,
                    ..
                },
                AtomTerm::VariantCtor {
                    variant_id: v2,
                    ctor_idx: c2,
                    fields: b,
                    ..
                },
            ) if v1 == v2 => Some(if c1 == c2 {
                Rule::Same {
                    left: a.clone(),
                    right: b.clone(),
                    one_to_one: true,
                }
            } else {
                Rule::Different
            }),
            (
                AtomTerm::VariantTag {
                    base: a,
                    variant_id: v1,
                    ..
                },
                AtomTerm::VariantTag {
                    base: b,
                    variant_id: v2,
                    ..
                },
            ) if v1 == v2 => Some(same(&[a], &[b])),
            (
                AtomTerm::Index {
                    base: a, index: x, ..
                },
                AtomTerm::Index {
                    base: b, index: y, ..
                },
            ) => Some(same(&[a, x], &[b, y])),
            (
                AtomTerm::Update {
                    base: a,
                    index: x,
                    value: e,
                },
                AtomTerm::Update {
                    base: b,
                    index: y,
                    value: f,
                },
            ) => Some(same(&[a, x, e], &[b, y, f])),
            _ => None,
        };
        let Some(rule) = rule else {
            return Err(format!(
                "the theory says nothing of the terms u{i} and u{j} together"
            ));
        };
        match rule {
            Rule::Same {
                left,
                right,
                one_to_one,
            } => {
                let arguments = self.all_equal(query, &left, &right)?;
                let results = self.eq(query, &variable(i), &variable(j))?;
                Ok(if one_to_one {
                    self.diagram.iff(arguments, results)
                } else {
                    self.diagram.implies(arguments, results)
                })
            }
            Rule::Different => {
                let equal = self.eq(query, &variable(i), &variable(j))?;
                Ok(self.diagram.not(equal))
            }
            Rule::FieldOf {
                base,
                constructor,
                field,
                argument,
            } => {
                let is_constructor = self.eq(query, &base, &variable(constructor))?;
                let is_argument = self.eq(query, &variable(field), &argument)?;
                Ok(self.diagram.implies(is_constructor, is_argument))
            }
        }
    }

    /// The frame part of [A6]: `i ≠ j` implies `t[i ↦ e][j] = t[j]`.
    fn of_frame(
        &mut self,
        query: &Query,
        update: TermId,
        element: TermId,
        original: TermId,
    ) -> Result<Formula, String> {
        let AtomTerm::Update { base, index: i, .. } = self.term(query, update)? else {
            return Err(format!("the term u{update} is not an update term"));
        };
        let AtomTerm::Index {
            base: updated,
            index: j,
            ..
        } = self.term(query, element)?
        else {
            return Err(format!("the term u{element} is not an element"));
        };
        let AtomTerm::Index {
            base: before,
            index: at,
            ..
        } = self.term(query, original)?
        else {
            return Err(format!("the term u{original} is not an element"));
        };
        if *updated != variable(update) || before != base || at != j {
            return Err(format!(
                "u{element} and u{original} are not one element of u{update} and of what it updates"
            ));
        }
        let same_index = self.eq(query, j, i)?;
        let other_index = self.diagram.not(same_index);
        let kept = self.eq(query, &variable(element), &variable(original))?;
        Ok(self.diagram.implies(other_index, kept))
    }

    /// The fields of one side of an extension: the arguments of a
    /// constructor term, or the field terms named, which must be the fields
    /// of the side, one for each field, and written by the checker.
    fn fields_of(
        &self,
        query: &Query,
        structure: StructId,
        (side, named): (TermId, &[TermId]),
    ) -> Result<Vec<LinearTerm>, String> {
        if let AtomTerm::StructCtor(of, arguments) = self.term(query, side)? {
            if *of != structure || !named.is_empty() {
                return Err(format!(
                    "the term u{side} is a constructor term, which has its fields"
                ));
            }
            return Ok(arguments.clone());
        }
        let mut fields = Vec::new();
        for (position, field) in named.iter().enumerate() {
            let is_field = matches!(
                self.term(query, *field)?,
                AtomTerm::Field { base, struct_id, field_idx, .. }
                    if *base == variable(side) && *struct_id == structure && *field_idx == position
            );
            if !is_field {
                return Err(format!(
                    "the term u{field} is not field {position} of u{side}"
                ));
            }
            self.written(query, *field)?;
            fields.push(variable(*field));
        }
        Ok(fields)
    }

    /// [A4], `t = S {t.x₁, …, t.xₙ}`: two values of `S` with equal fields
    /// are equal.
    fn of_extension(
        &mut self,
        query: &Query,
        structure: StructId,
        left: (TermId, &Vec<TermId>),
        right: (TermId, &Vec<TermId>),
    ) -> Result<Formula, String> {
        let Some(&arity) = query.arities.get(&structure) else {
            return Err(format!(
                "the number of fields of struct {structure} is not known"
            ));
        };
        let left_fields = self.fields_of(query, structure, (left.0, left.1.as_slice()))?;
        let right_fields = self.fields_of(query, structure, (right.0, right.1.as_slice()))?;
        if left_fields.len() != arity || right_fields.len() != arity {
            return Err(format!(
                "struct {structure} has {arity} fields, and not all of them are named"
            ));
        }
        let fields = self.all_equal(query, &left_fields, &right_fields)?;
        let values = self.eq(query, &variable(left.0), &variable(right.0))?;
        Ok(self.diagram.implies(fields, values))
    }
}
