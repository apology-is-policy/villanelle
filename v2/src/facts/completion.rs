//! Model completion: the values of the terms that a candidate leaves open,
//! and of the terms whose values have no arithmetic
//! (`docs/v2/facts.md`, section 7, the note on the search of the crate).
//!
//! The theory check answers a candidate with integers for the terms of its
//! rows. Every premise and every instance is then evaluated in that model,
//! and what the model fails is added to the search. A model that fails an
//! instance for no reason of the program costs a premise, its rows and the
//! lemmas about them, so the completion makes the model as real values are:
//! a quotient is the quotient of its operands, a constructor term is its
//! content, and two constructor terms are one value exactly where their
//! contents are. Nothing here decides an answer: a model is what the
//! premises and the instances hold in, and they are all evaluated after it.

use super::{DefRhs, Solver, Truth};
use crate::int::Int;
use crate::terms::{AtomTerm, LinearTerm, Row, SortTag, TermId};
use crate::typed::{StructId, VariantId};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

/// What a value of a sort without arithmetic is made of in a model: its
/// constructor and the values of the arguments.
#[derive(Clone, PartialEq, Eq, Hash)]
enum Content {
    Struct(StructId, Vec<Int>),
    Variant(VariantId, usize, Vec<Int>),
    /// The type of the elements, and the elements.
    Vector(String, Vec<Int>),
    Text(String),
    /// The types of the keys and of the values.
    EmptyMap(String, String),
}

/// The numbers of the contents that no row of the candidate speaks of. A
/// model is a structure of [J1]: a value of a sort without arithmetic is a
/// number that says only which value it is. A content has one number, and
/// the numbers are beyond those of the classes of a candidate.
struct Contents {
    made: HashMap<Content, Int>,
}

impl Contents {
    fn number(&mut self, known: &HashMap<Content, Int>, content: Content) -> Int {
        if let Some(value) = known.get(&content) {
            return value.clone();
        }
        let next = Int::power_of_two(96).plus(&Int::from_u64(self.made.len() as u64));
        self.made.entry(content).or_insert(next).clone()
    }
}

/// The terms of a candidate whose values have no arithmetic: the rows
/// say of them only that two are equal, or which of two is the smaller.
struct Symbolic {
    /// The terms that the rows make equal, each class in the order of the
    /// terms, and the classes in the order of their first terms.
    classes: Vec<Vec<TermId>>,
    /// `low ≤ high` between two classes, or `low < high` where the flag is
    /// set.
    order: Vec<(usize, usize, bool)>,
}

/// What the terms of the candidate's rows fix of the symbols: the number of
/// a content, the constructor term or the variant constructor behind a
/// number, and the field, the length and the tag of a number. The first
/// term in the order of the terms speaks for the others.
#[derive(Default)]
struct Fixed {
    known: HashMap<Content, Int>,
    structs: HashMap<(StructId, Int), TermId>,
    ctors: HashMap<(VariantId, Int), usize>,
    fields: HashMap<(StructId, usize, Int), Int>,
    lens: HashMap<Int, Int>,
    tags: HashMap<(VariantId, Int), Int>,
}

fn eval_all(terms: &[LinearTerm], model: &BTreeMap<TermId, Int>) -> Vec<Int> {
    terms.iter().map(|term| term.eval(model)).collect()
}

/// The root of `item` in a forest of classes.
fn root(parent: &mut [usize], mut item: usize) -> usize {
    while parent[item] != item {
        parent[item] = parent[parent[item]];
        item = parent[item];
    }
    item
}

impl Solver {
    fn content_of(&self, id: TermId, model: &BTreeMap<TermId, Int>) -> Option<Content> {
        match &self.terms[id] {
            AtomTerm::StructCtor(sid, args) => Some(Content::Struct(*sid, eval_all(args, model))),
            AtomTerm::VariantCtor {
                variant_id,
                ctor_idx,
                fields,
                ..
            } => Some(Content::Variant(
                *variant_id,
                *ctor_idx,
                eval_all(fields, model),
            )),
            AtomTerm::VecLit(element, items) => {
                Some(Content::Vector(element.clone(), eval_all(items, model)))
            }
            AtomTerm::EmptyMap(key, value) => Some(Content::EmptyMap(key.clone(), value.clone())),
            AtomTerm::StrLit(text) => Some(Content::Text(text.clone())),
            _ => None,
        }
    }

    /// Whether the values of a term have no arithmetic, as far as its form
    /// or the sort that the checker wrote beside it says.
    fn has_no_arithmetic(&self, id: TermId) -> bool {
        matches!(
            self.terms[id],
            AtomTerm::StructCtor(_, _)
                | AtomTerm::VariantCtor { .. }
                | AtomTerm::VecLit(_, _)
                | AtomTerm::EmptyMap(_, _)
                | AtomTerm::StrLit(_)
                | AtomTerm::Update { .. }
        ) || matches!(
            self.term_sorts.get(&id),
            Some(
                SortTag::String
                    | SortTag::Struct(_)
                    | SortTag::Variant(_)
                    | SortTag::Resource(_)
                    | SortTag::Outcome(_)
                    | SortTag::Vector(_)
                    | SortTag::Map(_, _)
            )
        )
    }

    /// The terms of the candidate's rows whose values have no arithmetic.
    /// A row `s - t ≤ 0` or `s - t ≤ -1` links two terms. Terms that such
    /// rows link, of which one is without arithmetic by its form or sort
    /// and none stands in a row of another form, are taken together.
    fn symbolic(&self, rows: &[Row]) -> Symbolic {
        let zero = Int::zero();
        let one = Int::from_u64(1);
        let minus_one = one.negate();
        let mut links: Vec<(TermId, TermId, bool)> = Vec::new();
        let mut mixed: BTreeSet<TermId> = BTreeSet::new();
        for row in rows {
            let strict = row.rhs == minus_one;
            let mut link = None;
            if row.coeffs.len() == 2 && (strict || row.rhs == zero) {
                let mut pair = row.coeffs.iter();
                if let (Some((first, by_first)), Some((second, by_second))) =
                    (pair.next(), pair.next())
                {
                    if *by_first == one && *by_second == minus_one {
                        link = Some((*first, *second, strict));
                    } else if *by_first == minus_one && *by_second == one {
                        link = Some((*second, *first, strict));
                    }
                }
            }
            match link {
                Some(link) => links.push(link),
                None => mixed.extend(row.coeffs.keys().copied()),
            }
        }
        let mut symbolic = Symbolic {
            classes: Vec::new(),
            order: Vec::new(),
        };
        if links.is_empty() {
            return symbolic;
        }

        let mut index: BTreeMap<TermId, usize> = BTreeMap::new();
        for (low, high, _) in &links {
            let next = index.len();
            index.entry(*low).or_insert(next);
            let next = index.len();
            index.entry(*high).or_insert(next);
        }
        // The terms that the rows link, and among them those that the rows
        // make equal: `s ≤ t` with `t ≤ s`.
        let mut linked: Vec<usize> = (0..index.len()).collect();
        let mut equal: Vec<usize> = (0..index.len()).collect();
        let weak: BTreeSet<(TermId, TermId)> = links
            .iter()
            .filter(|(_, _, strict)| !strict)
            .map(|(low, high, _)| (*low, *high))
            .collect();
        for (low, high, strict) in &links {
            let (a, b) = (index[low], index[high]);
            let (ra, rb) = (root(&mut linked, a), root(&mut linked, b));
            linked[ra.max(rb)] = ra.min(rb);
            if !strict && weak.contains(&(*high, *low)) {
                let (ra, rb) = (root(&mut equal, a), root(&mut equal, b));
                equal[ra.max(rb)] = ra.min(rb);
            }
        }
        let mut seeded = vec![false; index.len()];
        let mut spoiled = vec![false; index.len()];
        for (&term, &at) in &index {
            let group = root(&mut linked, at);
            if self.has_no_arithmetic(term) {
                seeded[group] = true;
            }
            if mixed.contains(&term) {
                spoiled[group] = true;
            }
        }

        let mut class_of: BTreeMap<usize, usize> = BTreeMap::new();
        let mut class_of_term: BTreeMap<TermId, usize> = BTreeMap::new();
        for (&term, &at) in &index {
            let group = root(&mut linked, at);
            if !seeded[group] || spoiled[group] {
                continue;
            }
            let class = root(&mut equal, at);
            let next = symbolic.classes.len();
            let class = *class_of.entry(class).or_insert(next);
            if class == next {
                symbolic.classes.push(Vec::new());
            }
            symbolic.classes[class].push(term);
            class_of_term.insert(term, class);
        }
        for (low, high, strict) in &links {
            if let (Some(&low), Some(&high)) = (class_of_term.get(low), class_of_term.get(high))
                && (low != high || *strict)
            {
                symbolic.order.push((low, high, *strict));
            }
        }
        symbolic
    }

    /// Gives the classes of `symbolic` their numbers: one number for the
    /// classes of one content where the rows allow that, a number of its
    /// own for every other class, and the numbers in an order that the rows
    /// of the candidate hold in. Where the rows order two classes of one
    /// content, every class has its own number. Returns whether a value
    /// changed.
    fn number_symbolic(&self, symbolic: &Symbolic, model: &mut BTreeMap<TermId, Int>) -> bool {
        if symbolic.classes.is_empty() {
            return false;
        }
        let mut merged_of: Vec<usize> = Vec::with_capacity(symbolic.classes.len());
        let mut by_content: HashMap<Content, usize> = HashMap::new();
        let mut merged = 0;
        for members in &symbolic.classes {
            let content = members.iter().find_map(|id| self.content_of(*id, model));
            let group = match content {
                Some(content) => *by_content.entry(content).or_insert_with(|| {
                    merged += 1;
                    merged - 1
                }),
                None => {
                    merged += 1;
                    merged - 1
                }
            };
            merged_of.push(group);
        }

        'attempt: for by_content in [true, false] {
            let count = if by_content {
                merged
            } else {
                symbolic.classes.len()
            };
            let group = |class: usize| {
                if by_content { merged_of[class] } else { class }
            };
            let mut after: Vec<BTreeSet<usize>> = vec![BTreeSet::new(); count];
            let mut waits = vec![0usize; count];
            for &(low, high, strict) in &symbolic.order {
                let (low, high) = (group(low), group(high));
                if low == high {
                    if strict {
                        continue 'attempt;
                    }
                } else if after[low].insert(high) {
                    waits[high] += 1;
                }
            }
            let mut ready: BTreeSet<usize> = (0..count).filter(|at| waits[*at] == 0).collect();
            let mut place = vec![0usize; count];
            let mut placed = 0;
            while let Some(at) = ready.pop_first() {
                place[at] = placed;
                placed += 1;
                for &next in &after[at] {
                    waits[next] -= 1;
                    if waits[next] == 0 {
                        ready.insert(next);
                    }
                }
            }
            if placed < count {
                continue;
            }
            let base = Int::power_of_two(95);
            let mut changed = false;
            for (class, members) in symbolic.classes.iter().enumerate() {
                let value = base.plus(&Int::from_u64(place[group(class)] as u64));
                for id in members {
                    if model.get(id) != Some(&value) {
                        model.insert(*id, value.clone());
                        changed = true;
                    }
                }
            }
            return changed;
        }
        false
    }

    fn fixed(&self, constrained: &HashSet<TermId>, model: &BTreeMap<TermId, Int>) -> Fixed {
        let mut fixed = Fixed::default();
        for (id, term) in self.terms.iter().enumerate() {
            if !constrained.contains(&id) {
                continue;
            }
            let value = model.get(&id).cloned().unwrap_or_default();
            if let Some(content) = self.content_of(id, model) {
                fixed.known.entry(content).or_insert_with(|| value.clone());
            }
            match term {
                AtomTerm::StructCtor(sid, _) => {
                    fixed.structs.entry((*sid, value)).or_insert(id);
                }
                AtomTerm::VariantCtor {
                    variant_id,
                    ctor_idx,
                    ..
                } => {
                    fixed.ctors.entry((*variant_id, value)).or_insert(*ctor_idx);
                }
                AtomTerm::VecLit(_, items) => {
                    fixed
                        .lens
                        .entry(value)
                        .or_insert_with(|| Int::from_u64(items.len() as u64));
                }
                AtomTerm::EmptyMap(_, _) => {
                    fixed.lens.entry(value).or_insert_with(Int::zero);
                }
                AtomTerm::Field {
                    base,
                    struct_id,
                    field_idx,
                    ..
                } => {
                    fixed
                        .fields
                        .entry((*struct_id, *field_idx, base.eval(model)))
                        .or_insert(value);
                }
                AtomTerm::Len(base) => {
                    fixed.lens.entry(base.eval(model)).or_insert(value);
                }
                AtomTerm::VariantTag {
                    base, variant_id, ..
                } => {
                    fixed
                        .tags
                        .entry((*variant_id, base.eval(model)))
                        .or_insert(value);
                }
                _ => {}
            }
        }
        fixed
    }

    /// Completes the model that the theory check gave for the rows of a
    /// candidate, which are `rows` as they hold.
    pub(super) fn complete_int_model(
        &self,
        rows: &[Row],
        assignment: &BTreeMap<usize, bool>,
        int_model: &mut BTreeMap<TermId, Int>,
    ) {
        let mut constrained = HashSet::new();
        for row in rows {
            for &var in row.coeffs.keys() {
                constrained.insert(var);
            }
        }
        let u32_max = Int::power_of_two(32).minus(&Int::from_u64(1));
        let zero = Int::zero();
        let symbolic = self.symbolic(rows);
        let mut contents = Contents {
            made: HashMap::new(),
        };

        for _ in 0..8 {
            let mut changed = self.number_symbolic(&symbolic, int_model);
            let mut fixed = self.fixed(&constrained, int_model);

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
                    AtomTerm::Len(base) => base
                        .as_var()
                        .and_then(|bid| match &self.terms[bid] {
                            AtomTerm::VecLit(_, items) => Some(Int::from_u64(items.len() as u64)),
                            AtomTerm::EmptyMap(_, _) => Some(Int::zero()),
                            _ => None,
                        })
                        .or_else(|| fixed.lens.get(&base.eval(int_model)).cloned()),
                    AtomTerm::VariantTag {
                        base, variant_id, ..
                    } => base
                        .as_var()
                        .and_then(|bid| match &self.terms[bid] {
                            AtomTerm::VariantCtor { ctor_idx, .. } => Some(*ctor_idx),
                            _ => None,
                        })
                        .or_else(|| {
                            fixed
                                .ctors
                                .get(&(*variant_id, base.eval(int_model)))
                                .copied()
                        })
                        .map(|ctor| Int::from_u64(ctor as u64))
                        .or_else(|| {
                            fixed
                                .tags
                                .get(&(*variant_id, base.eval(int_model)))
                                .cloned()
                        }),
                    // A constructor term is the number of its content.
                    AtomTerm::StructCtor(sid, _) => {
                        let value = self.number_of(id, &mut contents, &fixed, int_model);
                        fixed.structs.entry((*sid, value.clone())).or_insert(id);
                        Some(value)
                    }
                    AtomTerm::VariantCtor {
                        variant_id,
                        ctor_idx,
                        ..
                    } => {
                        let value = self.number_of(id, &mut contents, &fixed, int_model);
                        fixed
                            .ctors
                            .entry((*variant_id, value.clone()))
                            .or_insert(*ctor_idx);
                        Some(value)
                    }
                    AtomTerm::VecLit(_, items) => {
                        let value = self.number_of(id, &mut contents, &fixed, int_model);
                        fixed
                            .lens
                            .entry(value.clone())
                            .or_insert_with(|| Int::from_u64(items.len() as u64));
                        Some(value)
                    }
                    AtomTerm::EmptyMap(_, _) => {
                        let value = self.number_of(id, &mut contents, &fixed, int_model);
                        fixed.lens.entry(value.clone()).or_insert_with(Int::zero);
                        Some(value)
                    }
                    AtomTerm::StrLit(_) => {
                        Some(self.number_of(id, &mut contents, &fixed, int_model))
                    }
                    // A field of a number that a constructor term has is the
                    // argument of that term; of any other number, what the
                    // first field term of that number is.
                    AtomTerm::Field {
                        base,
                        struct_id,
                        field_idx,
                        ..
                    } => {
                        let whole = base.eval(int_model);
                        let argument = fixed
                            .structs
                            .get(&(*struct_id, whole.clone()))
                            .and_then(|ctor| match &self.terms[*ctor] {
                                AtomTerm::StructCtor(_, args) => args.get(*field_idx),
                                _ => None,
                            })
                            .map(|argument| argument.eval(int_model));
                        Some(argument.unwrap_or_else(|| {
                            fixed
                                .fields
                                .entry((*struct_id, *field_idx, whole))
                                .or_insert_with(|| zero.clone())
                                .clone()
                        }))
                    }
                    AtomTerm::Var { .. }
                    | AtomTerm::PureAlt(_, _)
                    | AtomTerm::PurePay(_, _, _, _)
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

            // The guards are read in the values as they are here, whatever
            // the definitions below then change.
            let values = int_model.clone();
            let mut truth = Truth::new(assignment, &values, self.theory_atoms.len());
            let mut defined = HashSet::new();
            for (guard, var_id, rhs) in &self.definitions {
                if constrained.contains(var_id) || !self.holds_in(*guard, &mut truth) {
                    continue;
                }
                defined.insert(*var_id);
                let v = match rhs {
                    DefRhs::Linear(term) => term.eval(int_model),
                    DefRhs::BoolFormula(phi) => {
                        let b = self.holds_in(*phi, &mut truth);
                        Int::from_u64(u64::from(b))
                    }
                };
                if int_model.get(var_id) != Some(&v) {
                    int_model.insert(*var_id, v);
                    changed = true;
                }
            }

            // A struct of which nothing is said but its fields is the
            // number of its content, as a constructor term of those fields
            // would be.
            for (base, sid, named) in &self.whole {
                if constrained.contains(base)
                    || defined.contains(base)
                    || !matches!(self.terms[*base], AtomTerm::Var { .. })
                {
                    continue;
                }
                let of_fields = named
                    .iter()
                    .map(|field| int_model.get(field).cloned().unwrap_or_default())
                    .collect();
                let v = contents.number(&fixed.known, Content::Struct(*sid, of_fields));
                if int_model.get(base) != Some(&v) {
                    int_model.insert(*base, v);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
    }

    /// The number of the content of the constructor term `id`.
    fn number_of(
        &self,
        id: TermId,
        contents: &mut Contents,
        fixed: &Fixed,
        model: &BTreeMap<TermId, Int>,
    ) -> Int {
        match self.content_of(id, model) {
            Some(content) => contents.number(&fixed.known, content),
            None => model.get(&id).cloned().unwrap_or_default(),
        }
    }
}
