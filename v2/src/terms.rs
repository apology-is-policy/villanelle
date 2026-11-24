//! Terms, rows and proofs of the fact logic (`docs/v2/facts.md`): the data
//! that the search ([`crate::facts`], [`crate::lia`]) and the kernel
//! ([`crate::kernel`]) both read.
//!
//! Nothing here searches. An atomic term ([S6]) stands for one integer in a
//! structure of the base logic ([J1]); a value of another sort is a member of
//! a non-empty set, and is counted by an integer too. A row is a linear
//! comparison in canonical form (section 7, step 2). A proof is the tree of
//! steps of [V3], and a certificate is what [V2] lists.

use crate::int::Int;
use crate::typed::{ControlId, IntType, StructId, Type, VariantId};
use std::collections::BTreeMap;
use std::fmt;

pub type TermId = usize;
pub type TheoryAtomId = usize;

/// Greatest common divisor of two magnitudes, always non-negative.
pub fn gcd(a: &Int, b: &Int) -> Int {
    // Machine integers where they suffice; the answer is the same.
    if let (Some(x), Some(y)) = (a.to_i128(), b.to_i128()) {
        let (mut x, mut y) = (x.unsigned_abs(), y.unsigned_abs());
        while y != 0 {
            let r = x % y;
            x = y;
            y = r;
        }
        return Int::from_u128(x);
    }
    let mut x = if a.is_negative() {
        a.negate()
    } else {
        a.clone()
    };
    let mut y = if b.is_negative() {
        b.negate()
    } else {
        b.clone()
    };
    while !y.is_zero() {
        let (_, r) = x.divide(&y).expect("non-zero divisor");
        x = y;
        y = r;
    }
    x
}

/// Floor quotient `⌊a / d⌋` toward `-∞`, for `d > 0`.
pub fn div_floor(a: &Int, d: &Int) -> Int {
    let (q, r) = a.divide(d).expect("positive divisor");
    if a.is_negative() && !r.is_zero() {
        q.minus(&Int::from_u64(1))
    } else {
        q
    }
}

/// Ceiling quotient `⌈a / d⌉` toward `+∞`, for `d > 0`.
pub fn div_ceil(a: &Int, d: &Int) -> Int {
    let (q, r) = a.divide(d).expect("positive divisor");
    if !a.is_negative() && !r.is_zero() {
        q.plus(&Int::from_u64(1))
    } else {
        q
    }
}

/// An atomic integer term (`[S6]`).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AtomTerm {
    /// A logical name. `is_value_term` is true when `[A1]` gives it the range
    /// of `ty`.
    Var {
        name: String,
        ty: Option<IntType>,
        is_value_term: bool,
    },
    /// The constant `usize.max` ([A2]).
    UsizeMax,
    /// `t ÷ k` for a literal `k ≥ 1` ([A7]).
    DivConst(LinearTerm, Int),
    /// `div(s, t)` for a non-constant divisor ([A8]).
    Div(LinearTerm, LinearTerm),
    /// `rem(s, t)` for a non-constant divisor ([A8]).
    Rem(LinearTerm, LinearTerm),
    /// `mul(s, t)` with ordered operands and their declared intervals ([A9]).
    Mul {
        left: LinearTerm,
        right: LinearTerm,
        left_bounds: (Option<Int>, Option<Int>),
        right_bounds: (Option<Int>, Option<Int>),
    },
    /// Uninterpreted alternative `alt_f(args)` of a pure operation ([I10]).
    PureAlt(ControlId, Vec<LinearTerm>),
    /// Uninterpreted payload `pay_{f, alt, field}(args)` of a pure operation ([I10]).
    PurePay(ControlId, usize, usize, Vec<LinearTerm>),
    /// `len(t)` for vectors, strings, and maps ([A3]).
    Len(LinearTerm),
    /// String literal ([A3]).
    StrLit(String),
    /// Empty map literal `∅` ([A3]), with the types of its keys and of its
    /// values. A literal at two types is two terms: every term has one sort.
    EmptyMap(String, String),
    /// Vector literal `[t₁, …, tₙ]` ([A3]), with the type of its elements.
    VecLit(String, Vec<LinearTerm>),
    /// Struct constructor `S {t̄}` ([A4]).
    StructCtor(StructId, Vec<LinearTerm>),
    /// Struct field projection `t.xᵢ` ([A4], [A1]).
    Field {
        base: LinearTerm,
        struct_id: StructId,
        field_idx: usize,
        int_ty: Option<IntType>,
        is_bool: bool,
        is_value_term: bool,
    },
    /// Variant constructor `V.c {t̄}` ([A5]).
    VariantCtor {
        variant_id: VariantId,
        ctor_idx: usize,
        fields: Vec<LinearTerm>,
        num_ctors: usize,
    },
    /// Variant constructor tag `tag(t)` in `0..num_ctors` ([A5]).
    VariantTag {
        base: LinearTerm,
        variant_id: VariantId,
        num_ctors: usize,
    },
    /// Vector element `t[i]` ([A6], [A1]).
    Index {
        base: LinearTerm,
        index: LinearTerm,
        int_ty: Option<IntType>,
        is_bool: bool,
        is_value_term: bool,
    },
    /// Vector element update `t[i ↦ e]` ([A6]).
    Update {
        base: LinearTerm,
        index: LinearTerm,
        value: LinearTerm,
    },
    /// Uninterpreted `trim(s)` on strings ([S5]).
    Trim(LinearTerm),
}

/// Sort tag of a logical term for `[J3]` and `[M7]`.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SortTag {
    Bool,
    Int,
    String,
    Struct(StructId),
    Variant(VariantId),
    Resource(usize),
    Outcome(usize),
    Vector(String),
    Map(String, String),
}

impl SortTag {
    pub fn from_type(ty: &Type) -> Option<SortTag> {
        match ty.deref_type() {
            Type::Bool => Some(SortTag::Bool),
            Type::Int(_) => Some(SortTag::Int),
            Type::String => Some(SortTag::String),
            Type::Struct(id, _) => Some(SortTag::Struct(*id)),
            Type::Variant(id, _) => Some(SortTag::Variant(*id)),
            Type::Resource(id, _) => Some(SortTag::Resource(*id)),
            Type::Outcome(id, _) => Some(SortTag::Outcome(*id)),
            Type::Vector(elem) => Some(SortTag::Vector(elem.to_string())),
            Type::Map(k, v) => Some(SortTag::Map(k.to_string(), v.to_string())),
            Type::Named(_)
            | Type::OutcomeNamed(_)
            | Type::TasksNamed(_)
            | Type::Tasks(_, _)
            | Type::Ref(_, _) => None,
        }
    }

    pub fn is_extensional_collection(&self) -> bool {
        matches!(
            self,
            SortTag::Vector(_) | SortTag::Map(_, _) | SortTag::String
        )
    }
}

/// A linear combination `constant + Σ coeff_i · u_i` ([S6]).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct LinearTerm {
    pub constant: Int,
    pub coeffs: BTreeMap<TermId, Int>,
}

impl LinearTerm {
    pub fn constant(value: Int) -> LinearTerm {
        LinearTerm {
            constant: value,
            coeffs: BTreeMap::new(),
        }
    }

    pub fn from_i128(value: i128) -> LinearTerm {
        LinearTerm::constant(Int::from_i128(value))
    }

    pub fn var(id: TermId) -> LinearTerm {
        let mut coeffs = BTreeMap::new();
        coeffs.insert(id, Int::from_u64(1));
        LinearTerm {
            constant: Int::zero(),
            coeffs,
        }
    }

    pub fn as_constant(&self) -> Option<Int> {
        if self.coeffs.is_empty() {
            Some(self.constant.clone())
        } else {
            None
        }
    }

    pub fn as_var(&self) -> Option<TermId> {
        if self.constant.is_zero()
            && self.coeffs.len() == 1
            && let Some((&id, coeff)) = self.coeffs.iter().next()
            && *coeff == Int::from_u64(1)
        {
            Some(id)
        } else {
            None
        }
    }

    pub fn negate(&self) -> LinearTerm {
        LinearTerm {
            constant: self.constant.negate(),
            coeffs: self
                .coeffs
                .iter()
                .map(|(id, c)| (*id, c.negate()))
                .collect(),
        }
    }

    pub fn add(&self, other: &LinearTerm) -> LinearTerm {
        let mut coeffs = self.coeffs.clone();
        for (id, c) in &other.coeffs {
            let sum = coeffs.get(id).cloned().unwrap_or_default().plus(c);
            if sum.is_zero() {
                coeffs.remove(id);
            } else {
                coeffs.insert(*id, sum);
            }
        }
        LinearTerm {
            constant: self.constant.plus(&other.constant),
            coeffs,
        }
    }

    pub fn sub(&self, other: &LinearTerm) -> LinearTerm {
        self.add(&other.negate())
    }

    pub fn scale(&self, factor: &Int) -> LinearTerm {
        if factor.is_zero() {
            return LinearTerm::default();
        }
        LinearTerm {
            constant: self.constant.times(factor),
            coeffs: self
                .coeffs
                .iter()
                .map(|(id, c)| (*id, c.times(factor)))
                .collect(),
        }
    }

    pub fn eval(&self, model: &BTreeMap<TermId, Int>) -> Int {
        let mut sum = self.constant.clone();
        for (id, coeff) in &self.coeffs {
            let val = model.get(id).cloned().unwrap_or_default();
            sum = sum.plus(&coeff.times(&val));
        }
        sum
    }
}

/// A linear inequality row `Σ a_i · u_i ≤ rhs` (`docs/v2/facts.md`, section 7).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Row {
    pub coeffs: BTreeMap<TermId, Int>,
    pub rhs: Int,
}

impl Row {
    /// Builds the row `term ≤ 0`.
    pub fn le_zero(term: &LinearTerm) -> Row {
        Row {
            coeffs: term.coeffs.clone(),
            rhs: term.constant.negate(),
        }
    }

    /// Builds `left ≤ right`.
    pub fn le(left: &LinearTerm, right: &LinearTerm) -> Row {
        Row::le_zero(&left.sub(right))
    }

    /// Builds `left < right` (`left + 1 ≤ right`).
    pub fn lt(left: &LinearTerm, right: &LinearTerm) -> Row {
        Row::le(&left.add(&LinearTerm::from_i128(1)), right)
    }

    /// The negation `¬(Σ a_i · u_i ≤ rhs)` over the integers:
    /// `Σ (-a_i) · u_i ≤ -rhs - 1`.
    pub fn complement(&self) -> Row {
        Row {
            coeffs: self
                .coeffs
                .iter()
                .map(|(id, c)| (*id, c.negate()))
                .collect(),
            rhs: self.rhs.negate().minus(&Int::from_u64(1)),
        }
    }

    /// The positive common factor of all coefficients, or `1` if `coeffs` is
    /// empty.
    pub fn coeff_gcd(&self) -> Int {
        let mut g = Int::zero();
        for coeff in self.coeffs.values() {
            g = if g.is_zero() {
                if coeff.is_negative() {
                    coeff.negate()
                } else {
                    coeff.clone()
                }
            } else {
                gcd(&g, coeff)
            };
        }
        if g.is_zero() { Int::from_u64(1) } else { g }
    }

    /// Divides all coefficients by their GCD `g ≥ 1` and replaces `rhs` with
    /// `⌊rhs / g⌋`.
    pub fn normalize(&self) -> (Row, Int) {
        let g = self.coeff_gcd();
        if g <= Int::from_u64(1) {
            return (self.clone(), Int::from_u64(1));
        }
        let coeffs = self
            .coeffs
            .iter()
            .map(|(id, c)| (*id, c.divide(&g).expect("divisible").0))
            .collect();
        let rhs = div_floor(&self.rhs, &g);
        (Row { coeffs, rhs }, g)
    }

    pub fn combine(&self, mult_self: &Int, other: &Row, mult_other: &Int) -> Row {
        let mut coeffs = BTreeMap::new();
        for (id, c) in &self.coeffs {
            let prod = c.times(mult_self);
            if !prod.is_zero() {
                coeffs.insert(*id, prod);
            }
        }
        for (id, c) in &other.coeffs {
            let sum = coeffs
                .get(id)
                .cloned()
                .unwrap_or_default()
                .plus(&c.times(mult_other));
            if sum.is_zero() {
                coeffs.remove(id);
            } else {
                coeffs.insert(*id, sum);
            }
        }
        Row {
            coeffs,
            rhs: self.rhs.times(mult_self).plus(&other.rhs.times(mult_other)),
        }
    }

    pub fn holds(&self, model: &BTreeMap<TermId, Int>) -> bool {
        let mut lhs = Int::zero();
        for (id, coeff) in &self.coeffs {
            let val = model.get(id).cloned().unwrap_or_default();
            lhs = lhs.plus(&coeff.times(&val));
        }
        lhs <= self.rhs
    }
}

/// One row derived on the way to a contradiction ([V3]). A step refers to a
/// row by its position on the path from the root of the proof: the rows of
/// the steps of every branch above, the row that each split adds, and the
/// rows of the earlier steps of the same branch.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Step {
    /// The row of literal `index` of the lemma: the atom, or its complement
    /// for a negative literal.
    Literal(usize),
    /// A sum of earlier rows, each with a positive integer multiplier.
    Combine(Vec<(usize, Int)>),
    /// From `e ≤ b`, where `divisor ≥ 1` divides every coefficient of `e`:
    /// `e/divisor ≤ ⌊b/divisor⌋`.
    Round { source: usize, divisor: Int },
}

/// How a branch of a proof ends ([V3]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum End {
    /// By the row `0 ≤ b` with `b < 0`.
    Close(usize),
    /// In two branches: `low` has the row `form ≤ bound` more, and `high` the
    /// row `form ≥ bound + 1`. Every integer value of `form` is in one of
    /// them.
    Split {
        form: BTreeMap<TermId, Int>,
        bound: Int,
        low: Box<Proof>,
        high: Box<Proof>,
    },
}

/// A refutation of a set of literals ([V3]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Proof {
    pub steps: Vec<Step>,
    pub end: End,
}

impl Proof {
    /// The number of steps and ends in the whole tree.
    pub fn size(&self) -> usize {
        self.steps.len()
            + match &self.end {
                End::Close(_) => 1,
                End::Split { low, high, .. } => 1 + low.size() + high.size(),
            }
    }

    /// The number of splits in the whole tree.
    pub fn splits(&self) -> usize {
        match &self.end {
            End::Close(_) => 0,
            End::Split { low, high, .. } => 1 + low.splits() + high.splits(),
        }
    }

    /// Whether a step of the tree is a [`Step::Round`].
    pub fn rounds(&self) -> bool {
        self.steps
            .iter()
            .any(|step| matches!(step, Step::Round { .. }))
            || match &self.end {
                End::Close(_) => false,
                End::Split { low, high, .. } => low.rounds() || high.rounds(),
            }
    }
}

/// A theory lemma: literals that cannot hold together, with the proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TheoryLemma {
    pub literals: Vec<(TheoryAtomId, bool)>,
    pub proof: Proof,
}

/// The name of an instance of the theory ([J3]). The search names the
/// instances it used. The kernel makes the formula of each from the name and
/// the terms, and takes no formula from the search ([V2]).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Instance {
    /// What the theory says of one term by itself: its range ([A1], [A2],
    /// [A3], [A5]), the length of a literal ([A3]), the constructor of a
    /// variant value ([A5]), the first two parts of [A6], and the bounds of
    /// [A7], [A8] and [A9].
    Term(TermId),
    /// What it says of two terms together: equal arguments of one symbol
    /// give equal results ([S5]), and the constructor axioms of [A3], [A4]
    /// and [A5].
    Pair(TermId, TermId),
    /// The frame part of [A6] for the update term `t[i ↦ e]` and an index
    /// `j`: `element` is the term `t[i ↦ e][j]` and `original` is `t[j]`.
    Frame {
        update: TermId,
        element: TermId,
        original: TermId,
    },
    /// [A4], `t = S {t.x₁, …, t.xₙ}`, for two values of the struct `S`:
    /// equal fields make them equal. A side is a constructor term, with no
    /// field listed, or another term with the term of each of its fields.
    Extension {
        structure: StructId,
        left: TermId,
        left_fields: Vec<TermId>,
        right: TermId,
        right_fields: Vec<TermId>,
    },
}

/// One thing that a certificate conjoins with the goal ([V2]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Part {
    /// A formula of `Ω`, by its position in the checker's list.
    Structure(usize),
    /// A fact of `Ψ`, by its position in the checker's list.
    Fact(usize),
    /// An instance of the theory, by its name.
    Instance(Instance),
    /// A theory lemma, with its proof.
    Lemma(TheoryLemma),
}

/// What the search found for a yes ([V1], [V2]): the premises it used, the
/// instances and the lemmas, in the order in which it added them. It holds
/// no formula. The goal and the premises are the checker's, and the kernel
/// is given them by the checker ([`crate::kernel::Query`]).
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct Certificate {
    pub parts: Vec<Part>,
}

impl Certificate {
    pub fn instances(&self) -> impl Iterator<Item = &Instance> {
        self.parts.iter().filter_map(|part| match part {
            Part::Instance(instance) => Some(instance),
            _ => None,
        })
    }

    pub fn lemmas(&self) -> impl Iterator<Item = &TheoryLemma> {
        self.parts.iter().filter_map(|part| match part {
            Part::Lemma(lemma) => Some(lemma),
            _ => None,
        })
    }

    /// The number of premises that the certificate names.
    pub fn premises(&self) -> usize {
        self.parts
            .iter()
            .filter(|part| matches!(part, Part::Structure(_) | Part::Fact(_)))
            .count()
    }
}

impl fmt::Display for Instance {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let list = |terms: &[TermId]| {
            terms
                .iter()
                .map(|term| format!("u{term}"))
                .collect::<Vec<_>>()
                .join(" ")
        };
        match self {
            Instance::Term(term) => write!(formatter, "term u{term}"),
            Instance::Pair(left, right) => write!(formatter, "pair u{left} u{right}"),
            Instance::Frame {
                update,
                element,
                original,
            } => write!(formatter, "frame u{update} u{element} u{original}"),
            Instance::Extension {
                structure,
                left,
                left_fields,
                right,
                right_fields,
            } => write!(
                formatter,
                "extension {structure} u{left} [{}] u{right} [{}]",
                list(left_fields),
                list(right_fields)
            ),
        }
    }
}

impl fmt::Display for Certificate {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(
            formatter,
            "certificate (premises: {}, instances: {}, lemmas: {})",
            self.premises(),
            self.instances().count(),
            self.lemmas().count()
        )?;
        for part in &self.parts {
            match part {
                Part::Structure(_) | Part::Fact(_) => {}
                Part::Instance(instance) => writeln!(formatter, "  instance {instance}")?,
                Part::Lemma(lemma) => writeln!(
                    formatter,
                    "  lemma ({} literals, {} steps, {} splits)",
                    lemma.literals.len(),
                    lemma.proof.size(),
                    lemma.proof.splits()
                )?,
            }
        }
        Ok(())
    }
}
