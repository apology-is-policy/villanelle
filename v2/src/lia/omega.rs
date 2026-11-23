//! Part 6 of the theory check: the Omega test (W. Pugh, "The Omega test: a
//! fast and practical integer programming algorithm for dependence
//! analysis", 1991). It decides every set of rows, with bounds or without,
//! and so the theory check gives up only at the count of steps.
//!
//! The test removes one variable after another. Parts 1 and 3 do that
//! where a coefficient is a unit; two things are added here.
//!
//! **An equality in which no coefficient is a unit.** Let `a` be its
//! smallest coefficient, on the variable `y`, and `m = |a| + 1`. With `c`
//! the integer nearest to `b/m` for every other coefficient `b`, on `x`,
//! the variable `y` is replaced by a new one, `n`:
//!
//! ```text
//! y = -sign(a)·(n + Σ c·x)        n = -sign(a)·y - Σ c·x
//! ```
//!
//! Every integer `y` has one integer `n` and the other way round, so the
//! rows are the rows they were, written in other variables: the change is
//! no step of a proof. In the equality the coefficient of `n` is `-|a|`,
//! and every other coefficient falls to five sixths of what it was or less.
//! After some changes a coefficient is a unit, and part 1 removes the
//! equality. A new variable is a sum of the terms of the rows that were
//! given, and where a proof splits on a row, it names that sum.
//!
//! **A variable that no side bounds with units.** Let the rows that bound
//! `y` on one side, the tight side, be `f ≤ β`, with the coefficient `t` on
//! `y`, and let `o` be the greatest coefficient of `y` on the other side.
//!
//! - The sums of a row of each side, in which `y` is gone, hold wherever
//!   the rows hold (the real shadow). If no integers satisfy them, none
//!   satisfy the rows. If some do, and they leave an integer for `y`, that
//!   is a model.
//! - Otherwise the proof splits on each row of the tight side at
//!   `β - w`, where `w = t - ⌈t/o⌉`. Above the split `f` is one of the `w`
//!   values `β - w + 1` to `β`, and each is an equality, a splinter, that
//!   is decided on its own. The values are told apart by splits in halves,
//!   so that `w` splinters nest `log₂ w` deep.
//! - Below every split, each row of the tight side is `f ≤ β - w`. The
//!   sums of these with the rows of the other side say at least what
//!   Pugh's dark shadow says: for a lower bound `L ≤ a·y` and an upper
//!   bound `b·y ≤ U` they give `a·U - b·L ≥ (a - 1)·(b - 1)`, and integers
//!   that satisfy this for every pair leave an integer for `y`, the least
//!   that the lower bounds allow. If no integers satisfy the sums, this
//!   branch is refuted too.
//!
//! The search has the shape of the proof, so the proof of each branch is
//! made where it is and none is searched for twice. Where every coefficient
//! of one side is a unit, `w` is zero for every row: there is no split, the
//! sums are the real shadow, and the step is part 3 without its limit on
//! growth.
//!
//! Before rows are added up, the simplex method is asked whether they have
//! a rational solution at all. A branch that has none is closed by one
//! sum, where adding up would take one for every pair of rows.
//!
//! The test counts a step for every row that a turn reads and for every
//! sum it makes, so the count of steps bounds its work and not only its
//! turns. It ends without the count on every set of rows; the count ends
//! it where the splinters are too many, since their number grows with the
//! coefficients.

use super::{
    Found, Limit, Removed, SPLIT_DEPTH, Simplex, absolute, equalities, negated, one, sums, within,
};
use crate::counts;
use crate::int::Int;
use crate::terms::{End, LinearTerm, Proof, Row, Step, TermId, div_ceil, div_floor};
use std::collections::BTreeMap;

pub(super) enum Answer {
    /// Values for the variables of the rows. A variable that is absent is
    /// zero.
    Model(BTreeMap<TermId, Int>),
    /// The end of a proof. Its steps were added to the path.
    Refuted(End),
}

/// Decides `active`, the rows with the numbers they have on the path.
/// `steps` holds the steps of the path so far, and receives those of the
/// proof.
pub(super) fn decide(
    active: Vec<(Row, usize)>,
    steps: &mut Vec<Step>,
    budget: &mut u64,
) -> Result<Answer, Limit> {
    let first = active
        .iter()
        .flat_map(|(row, _)| row.coeffs.keys())
        .max()
        .map_or(0, |term| term + 1);
    let mut omega = Omega {
        budget,
        fresh: first,
        forms: BTreeMap::new(),
    };
    Ok(match omega.decide(active, steps, SPLIT_DEPTH)? {
        Answer::Model(mut model) => {
            model.retain(|term, _| *term < first);
            Answer::Model(model)
        }
        refuted => refuted,
    })
}

struct Omega<'a> {
    budget: &'a mut u64,
    /// The number of the next new variable. The new variables have the
    /// numbers after those of the terms.
    fresh: TermId,
    /// Each new variable as a sum of terms.
    forms: BTreeMap<TermId, BTreeMap<TermId, Int>>,
}

/// The removal of a variable that no side bounds with units.
struct Removal {
    term: TermId,
    /// Every row of the node.
    all: Vec<(Row, usize)>,
    /// The rows without the term.
    rest: Vec<(Row, usize)>,
    /// The rows with the term: they give it a value in a model.
    bounds: Vec<Row>,
    /// The rows of the tight side, each with the number of its splinters.
    tight: Vec<(Row, usize, Int)>,
    other: Vec<(Row, usize)>,
}

/// The values that a row of the tight side may still have in a branch:
/// `least` to `greatest`, stated by the rows `at_least` and `at_most` of
/// the path.
struct Range {
    least: Int,
    greatest: Int,
    at_least: usize,
    at_most: usize,
}

/// Which variable to remove next, and from which side.
struct Choice {
    term: TermId,
    /// Whether the rows that bound the term below are the tight side.
    lower_is_tight: bool,
    splinters: Int,
    /// The number of pairs of a row of each side, and of rows with the term.
    pairs: usize,
    rows: usize,
}

/// The variable with the fewest splinters, then with the fewest sums, then
/// the first. `None` when there is no row.
fn chosen(active: &[(Row, usize)]) -> Option<Choice> {
    // For each term, the coefficients of the rows that bound it below and
    // above, without their signs.
    let mut sides: BTreeMap<TermId, (Vec<Int>, Vec<Int>)> = BTreeMap::new();
    for (row, _) in active {
        for (term, coeff) in &row.coeffs {
            let entry = sides.entry(*term).or_default();
            if coeff.is_negative() {
                entry.0.push(coeff.negate());
            } else {
                entry.1.push(coeff.clone());
            }
        }
    }
    let mut best: Option<Choice> = None;
    for (term, (lower, upper)) in &sides {
        let pairs = lower.len() * upper.len();
        for lower_is_tight in [true, false] {
            let (tight, other) = if lower_is_tight {
                (lower, upper)
            } else {
                (upper, lower)
            };
            let splinters = match other.iter().max() {
                None => Int::zero(),
                Some(greatest) => tight.iter().fold(Int::zero(), |sum, coeff| {
                    sum.plus(&coeff.minus(&div_ceil(coeff, greatest)))
                }),
            };
            let better = best.as_ref().is_none_or(|best| {
                splinters < best.splinters || (splinters == best.splinters && pairs < best.pairs)
            });
            if better {
                best = Some(Choice {
                    term: *term,
                    lower_is_tight,
                    splinters,
                    pairs,
                    rows: lower.len() + upper.len(),
                });
            }
        }
    }
    best
}

/// The place of a row that states an equality with the row opposite to
/// it. Part 1 has left one row for each left-hand side, and no equality
/// with a unit.
fn stated_equality(active: &[(Row, usize)]) -> Option<usize> {
    let sides: BTreeMap<&BTreeMap<TermId, Int>, &Int> = active
        .iter()
        .map(|(row, _)| (&row.coeffs, &row.rhs))
        .collect();
    active.iter().position(|(row, _)| {
        row.coeffs
            .values()
            .next()
            .is_some_and(|coeff| !coeff.is_negative())
            && sides
                .get(&negated(&row.coeffs))
                .is_some_and(|opposite| row.rhs.plus(opposite).is_zero())
    })
}

/// Adds `amount` to the coefficient of `term`.
fn add(sum: &mut BTreeMap<TermId, Int>, term: TermId, amount: &Int) {
    let total = sum.get(&term).cloned().unwrap_or_default().plus(amount);
    if total.is_zero() {
        sum.remove(&term);
    } else {
        sum.insert(term, total);
    }
}

/// The step that stands on the path for the row of a split. It is in no
/// proof: a branch takes its steps from behind it.
fn row_of_split() -> Step {
    Step::Literal(usize::MAX)
}

impl Omega<'_> {
    fn spend(&mut self, steps: usize) -> Result<(), Limit> {
        let steps = steps as u64;
        if *self.budget < steps {
            *self.budget = 0;
            return Err(Limit);
        }
        *self.budget -= steps;
        Ok(())
    }

    /// The left-hand side `coeffs` as a sum of terms.
    fn expanded(&self, coeffs: &BTreeMap<TermId, Int>) -> BTreeMap<TermId, Int> {
        let mut form = BTreeMap::new();
        for (variable, coeff) in coeffs {
            match self.forms.get(variable) {
                None => add(&mut form, *variable, coeff),
                Some(parts) => {
                    for (term, part) in parts {
                        add(&mut form, *term, &coeff.times(part));
                    }
                }
            }
        }
        form
    }

    /// Decides `active`. On a model the path is left as it happens to be;
    /// on a proof the steps of this branch are behind those it had.
    fn decide(
        &mut self,
        active: Vec<(Row, usize)>,
        path: &mut Vec<Step>,
        depth: usize,
    ) -> Result<Answer, Limit> {
        let given = cfg!(debug_assertions).then(|| active.clone());
        let mut removed = Vec::new();
        Ok(match self.node(active, path, depth, &mut removed)? {
            Answer::Model(mut model) => {
                for entry in removed.iter().rev() {
                    match entry {
                        Removed::Defined(term, definition) => {
                            let value = definition.eval(&model);
                            model.insert(*term, value);
                        }
                        Removed::Projected(term, bounds) => {
                            let value = within(*term, bounds, &model);
                            model.insert(*term, value);
                        }
                    }
                }
                debug_assert!(given.iter().flatten().all(|(row, _)| row.holds(&model)));
                Answer::Model(model)
            }
            refuted => refuted,
        })
    }

    fn node(
        &mut self,
        mut active: Vec<(Row, usize)>,
        path: &mut Vec<Step>,
        depth: usize,
        removed: &mut Vec<Removed>,
    ) -> Result<Answer, Limit> {
        let choice = loop {
            // A step for each row: every part of a turn reads them all.
            self.spend(active.len().max(1))?;
            if let Some(row) = equalities(&mut active, path, removed) {
                return Ok(Answer::Refuted(End::Close(row)));
            }
            if let Some(at) = stated_equality(&active) {
                self.change_variables(&mut active, at, removed)?;
                continue;
            }
            let Some(choice) = chosen(&active) else {
                return Ok(Answer::Model(BTreeMap::new()));
            };
            let exact = choice.splinters.is_zero();
            if !exact || choice.pairs > choice.rows {
                match Simplex::new(&active).search(path.len(), 0, 0, self.budget)? {
                    Found::Refuted(found) => {
                        path.extend(found.steps);
                        return Ok(Answer::Refuted(found.end));
                    }
                    Found::Model(model) => return Ok(Answer::Model(model)),
                    Found::Open => {}
                }
            }
            if !exact {
                break choice;
            }
            // Part 3, whatever it adds.
            self.spend(choice.pairs)?;
            let (with, without): (Vec<_>, Vec<_>) = active
                .drain(..)
                .partition(|(row, _)| row.coeffs.contains_key(&choice.term));
            active = without;
            let (lower, upper): (Vec<_>, Vec<_>) = with
                .iter()
                .partition(|(row, _)| row.coeffs[&choice.term].is_negative());
            if let Some(row) = sums(choice.term, &lower, &upper, path, &mut active) {
                return Ok(Answer::Refuted(End::Close(row)));
            }
            removed.push(Removed::Projected(
                choice.term,
                with.into_iter().map(|(row, _)| row).collect(),
            ));
        };
        let term = choice.term;
        self.spend(choice.pairs)?;
        let (with, rest): (Vec<_>, Vec<_>) = active
            .iter()
            .cloned()
            .partition(|(row, _)| row.coeffs.contains_key(&term));
        let (tight, other): (Vec<_>, Vec<_>) = with
            .iter()
            .cloned()
            .partition(|(row, _)| row.coeffs[&term].is_negative() == choice.lower_is_tight);
        let bounds: Vec<Row> = with.into_iter().map(|(row, _)| row).collect();
        // The real shadow.
        let mark = path.len();
        let mut shadow = rest.clone();
        if let Some(row) = sums(term, &tight, &other, path, &mut shadow) {
            return Ok(Answer::Refuted(End::Close(row)));
        }
        match self.decide(shadow, path, depth)? {
            Answer::Refuted(end) => return Ok(Answer::Refuted(end)),
            Answer::Model(mut model) => {
                let value = within(term, &bounds, &model);
                model.insert(term, value);
                if bounds.iter().all(|row| row.holds(&model)) {
                    return Ok(Answer::Model(model));
                }
                path.truncate(mark);
            }
        }
        // The splits, with the sums of the tightened rows below them all.
        let greatest = other
            .iter()
            .map(|(row, _)| absolute(&row.coeffs[&term]))
            .max()
            .expect("a variable with splinters has rows on both sides");
        let tight = tight
            .into_iter()
            .map(|(row, id)| {
                let coeff = absolute(&row.coeffs[&term]);
                let splinters = coeff.minus(&div_ceil(&coeff, &greatest));
                (row, id, splinters)
            })
            .collect();
        let removal = Removal {
            term,
            all: active,
            rest,
            bounds,
            tight,
            other,
        };
        self.chain(&removal, 0, &mut Vec::new(), path, depth)
    }

    /// Replaces a variable of the equality that the row at `at` states by a
    /// new one, until a coefficient of the equality is a unit.
    fn change_variables(
        &mut self,
        active: &mut [(Row, usize)],
        at: usize,
        removed: &mut Vec<Removed>,
    ) -> Result<(), Limit> {
        let two = Int::from_u64(2);
        loop {
            let equality = active[at].0.coeffs.clone();
            let Some((gone, least)) = equality
                .iter()
                .min_by_key(|(term, coeff)| (absolute(coeff), **term))
            else {
                return Ok(());
            };
            if absolute(least) == one() {
                return Ok(());
            }
            self.spend(active.len())?;
            let gone = *gone;
            // `gone = -sign·(new + Σ nearest·other)`, which is the same as
            // `new = -sign·gone - Σ nearest·other`.
            let positive = !least.is_negative();
            let signed = |value: Int| if positive { value.negate() } else { value };
            let modulus = absolute(least).plus(&one());
            let new = self.fresh;
            self.fresh += 1;
            let mut definition = LinearTerm::default();
            definition.coeffs.insert(new, signed(one()));
            let mut form = self.expanded(&BTreeMap::from([(gone, signed(one()))]));
            let mut nearest = Vec::new();
            for (other, coeff) in &equality {
                if *other == gone {
                    continue;
                }
                let quotient = div_floor(&coeff.times(&two).plus(&modulus), &modulus.times(&two));
                if quotient.is_zero() {
                    continue;
                }
                definition.coeffs.insert(*other, signed(quotient.clone()));
                for (term, part) in self.expanded(&BTreeMap::from([(*other, quotient.negate())])) {
                    add(&mut form, term, &part);
                }
                nearest.push((*other, quotient));
            }
            self.forms.insert(new, form);
            removed.push(Removed::Defined(gone, definition));
            for (row, _) in active.iter_mut() {
                let Some(coeff) = row.coeffs.remove(&gone) else {
                    continue;
                };
                let on_new = signed(coeff);
                for (other, quotient) in &nearest {
                    add(&mut row.coeffs, *other, &on_new.times(quotient));
                }
                row.coeffs.insert(new, on_new);
            }
        }
    }

    /// The splits on the rows of the tight side from `at` on. `tightened`
    /// holds the rows before `at` as they are in this branch.
    fn chain(
        &mut self,
        of: &Removal,
        at: usize,
        tightened: &mut Vec<(Row, usize)>,
        path: &mut Vec<Step>,
        depth: usize,
    ) -> Result<Answer, Limit> {
        let Some((row, id, splinters)) = of.tight.get(at) else {
            // Every row of the tight side is tightened.
            self.spend(tightened.len() * of.other.len())?;
            let mut shadow = of.rest.clone();
            if let Some(row) = sums(of.term, tightened, &of.other, path, &mut shadow) {
                return Ok(Answer::Refuted(End::Close(row)));
            }
            return Ok(match self.decide(shadow, path, depth)? {
                Answer::Model(mut model) => {
                    let value = within(of.term, &of.bounds, &model);
                    model.insert(of.term, value);
                    debug_assert!(of.bounds.iter().all(|row| row.holds(&model)));
                    Answer::Model(model)
                }
                refuted => refuted,
            });
        };
        if splinters.is_zero() {
            tightened.push((row.clone(), *id));
            let answer = self.chain(of, at + 1, tightened, path, depth);
            tightened.pop();
            return answer;
        }
        if depth == 0 {
            return Err(Limit);
        }
        let bound = row.rhs.minus(splinters);
        let split = path.len();
        // Below the split: the row is tightened, and the next row follows.
        path.push(row_of_split());
        tightened.push((
            Row {
                coeffs: row.coeffs.clone(),
                rhs: bound.clone(),
            },
            split,
        ));
        let low = self.chain(of, at + 1, tightened, path, depth - 1)?;
        tightened.pop();
        let steps = path.split_off(split + 1);
        path.pop();
        let low = match low {
            Answer::Model(model) => return Ok(Answer::Model(model)),
            Answer::Refuted(end) => Proof { steps, end },
        };
        // Above it: the splinters of the row.
        path.push(row_of_split());
        let range = Range {
            least: bound.plus(&one()),
            greatest: row.rhs.clone(),
            at_least: split,
            at_most: *id,
        };
        let high = self.splinters(of, at, tightened, range, path, depth - 1)?;
        let steps = path.split_off(split + 1);
        path.pop();
        let high = match high {
            Answer::Model(model) => return Ok(Answer::Model(model)),
            Answer::Refuted(end) => Proof { steps, end },
        };
        Ok(Answer::Refuted(End::Split {
            form: self.expanded(&row.coeffs),
            bound,
            low: Box::new(low),
            high: Box::new(high),
        }))
    }

    /// The splinters of the row at `at` of the tight side for the values in
    /// `range`, told apart by splits in halves.
    fn splinters(
        &mut self,
        of: &Removal,
        at: usize,
        tightened: &[(Row, usize)],
        range: Range,
        path: &mut Vec<Step>,
        depth: usize,
    ) -> Result<Answer, Limit> {
        let coeffs = &of.tight[at].0.coeffs;
        if range.least == range.greatest {
            counts::count(|counts| counts.splinters += 1);
            let mut rows = of.all.clone();
            rows.extend(tightened.iter().cloned());
            rows.push((
                Row {
                    coeffs: coeffs.clone(),
                    rhs: range.greatest,
                },
                range.at_most,
            ));
            rows.push((
                Row {
                    coeffs: negated(coeffs),
                    rhs: range.least.negate(),
                },
                range.at_least,
            ));
            return self.decide(rows, path, depth);
        }
        if depth == 0 {
            return Err(Limit);
        }
        self.spend(1)?;
        let middle = div_floor(&range.least.plus(&range.greatest), &Int::from_u64(2));
        let split = path.len();
        path.push(row_of_split());
        let below = Range {
            least: range.least,
            greatest: middle.clone(),
            at_least: range.at_least,
            at_most: split,
        };
        let low = self.splinters(of, at, tightened, below, path, depth - 1)?;
        let steps = path.split_off(split + 1);
        path.pop();
        let low = match low {
            Answer::Model(model) => return Ok(Answer::Model(model)),
            Answer::Refuted(end) => Proof { steps, end },
        };
        path.push(row_of_split());
        let above = Range {
            least: middle.plus(&one()),
            greatest: range.greatest,
            at_least: split,
            at_most: range.at_most,
        };
        let high = self.splinters(of, at, tightened, above, path, depth - 1)?;
        let steps = path.split_off(split + 1);
        path.pop();
        let high = match high {
            Answer::Model(model) => return Ok(Answer::Model(model)),
            Answer::Refuted(end) => Proof { steps, end },
        };
        Ok(Answer::Refuted(End::Split {
            form: self.expanded(coeffs),
            bound: middle,
            low: Box::new(low),
            high: Box::new(high),
        }))
    }
}

#[cfg(test)]
mod tests {
    use crate::counts;
    use crate::int::Int;
    use crate::lia::tests::{answer, boxed, decided, row};
    use crate::lia::{Outcome, complete, solve};
    use crate::rng::Rng;
    use crate::terms::{Row, Step, TermId};
    use std::collections::BTreeMap;

    /// Part 6 alone, with the count of steps it may take.
    fn omega(rows: &[Row], mut budget: u64) -> Outcome {
        let steps = (0..rows.len()).map(Step::Literal).collect();
        complete(rows, steps, &mut budget)
    }

    /// The answer of part 6 alone.
    fn completed(rows: &[Row]) -> Option<bool> {
        answer(omega(rows, 200_000), rows)
    }

    /// Pugh's example: rational solutions, and no integer one.
    fn thin(x: &[(TermId, i128)]) -> Vec<Row> {
        // `27 ≤ 11·x + 13·y ≤ 45` and `-10 ≤ 7·x - 9·y ≤ 4`, with `x` the
        // sum that is given and `y` the term 9.
        let with = |on_x: i128, on_y: i128| -> Vec<(TermId, i128)> {
            let mut coeffs: Vec<(TermId, i128)> =
                x.iter().map(|(term, part)| (*term, on_x * part)).collect();
            coeffs.push((9, on_y));
            coeffs
        };
        vec![
            row(&with(-11, -13), -27),
            row(&with(11, 13), 45),
            row(&with(-7, 9), 10),
            row(&with(7, -9), 4),
        ]
    }

    /// Against a search of every point of a small box, without the other
    /// parts: the answer is the same, every model holds, and the kernel
    /// validates every proof.
    #[test]
    fn the_omega_test_alone_gives_the_answer_of_a_search_of_every_point() {
        let mut rng = Rng::new(0x6f6d656761);
        let before = counts::now();
        let mut refuted = 0;
        for _ in 0..3_000 {
            let (rows, exists) = boxed(&mut rng);
            assert_eq!(completed(&rows), Some(exists), "{rows:?}");
            refuted += usize::from(!exists);
        }
        let done = counts::now().since(&before);
        assert!(refuted > 300, "{refuted} sets of rows were refuted");
        assert!(done.splinters > 30, "{done}");
    }

    /// Rows that bound no variable. Each variable of rows in a box is
    /// replaced by a sum of two new ones that takes every value, so the
    /// answer stays that of the search of every point, and the solutions
    /// have no bound.
    #[test]
    fn rows_without_a_bound_have_the_answer_of_a_search_of_every_point() {
        let sums: [(i128, i128); 6] = [(1, -1), (2, 3), (3, -2), (2, -5), (3, 4), (5, -3)];
        let mut rng = Rng::new(0x626f756e64);
        let before = counts::now();
        let mut refuted = 0;
        for round in 0..1_500 {
            let (boxed, exists) = boxed(&mut rng);
            let parts: Vec<(i128, i128)> = (0..3)
                .map(|_| sums[rng.below(sums.len() as u64) as usize])
                .collect();
            let rows: Vec<Row> = boxed
                .iter()
                .map(|row| {
                    let mut coeffs = BTreeMap::new();
                    for (term, coeff) in &row.coeffs {
                        let (first, second) = parts[*term];
                        coeffs.insert(2 * term, coeff.times(&Int::from_i128(first)));
                        coeffs.insert(2 * term + 1, coeff.times(&Int::from_i128(second)));
                    }
                    Row {
                        coeffs,
                        rhs: row.rhs.clone(),
                    }
                })
                .collect();
            assert_eq!(completed(&rows), Some(exists), "{rows:?}");
            // The whole method, on some of them: it takes half of its
            // steps for the splits that do not end.
            if round % 10 == 0 {
                let mut budget = 20_000;
                assert_eq!(
                    answer(solve(&rows, &mut budget), &rows),
                    Some(exists),
                    "{rows:?}"
                );
            }
            refuted += usize::from(!exists);
        }
        let done = counts::now().since(&before);
        assert!(refuted > 150, "{refuted} sets of rows were refuted");
        assert!(done.splinters > 100, "{done}");
    }

    /// Two thin bands across a box, as in Pugh's example: many have rational
    /// solutions and no integer one, and only splinters refute those. Half
    /// of them are stated with a difference of two terms for the first
    /// variable, which then has no bound.
    #[test]
    fn thin_bands_have_the_answer_of_a_search_of_every_point() {
        let mut rng = Rng::new(0x7468696e);
        let before = counts::now();
        let (mut refuted, mut with_split) = (0, 0);
        for round in 0..1_500 {
            let coefficient = |rng: &mut Rng| {
                let size = 2 + rng.below(11) as i128;
                if rng.below(2) == 0 { size } else { -size }
            };
            let mut rows = vec![
                row(&[(0, 1)], 8),
                row(&[(0, -1)], 8),
                row(&[(1, 1)], 8),
                row(&[(1, -1)], 8),
            ];
            for _ in 0..2 {
                let (on_x, on_y) = (coefficient(&mut rng), coefficient(&mut rng));
                let least = rng.below(41) as i128 - 20;
                let width = rng.below(8) as i128;
                rows.push(row(&[(0, -on_x), (1, -on_y)], -least));
                rows.push(row(&[(0, on_x), (1, on_y)], least + width));
            }
            let exists = (-8..=8).any(|x| {
                (-8..=8).any(|y| {
                    let model: BTreeMap<TermId, Int> =
                        BTreeMap::from([(0, Int::from_i128(x)), (1, Int::from_i128(y))]);
                    rows.iter().all(|row| row.holds(&model))
                })
            });
            let rows: Vec<Row> = rows
                .iter()
                .map(|row| {
                    let mut row = row.normalize().0;
                    if round % 2 == 1
                        && let Some(coeff) = row.coeffs.get(&0).cloned()
                    {
                        row.coeffs.insert(2, coeff.negate());
                    }
                    row
                })
                .collect();
            assert_eq!(completed(&rows), Some(exists), "{rows:?}");
            if !exists {
                refuted += 1;
                if let Outcome::Unsat { proof, .. } = omega(&rows, 200_000)
                    && proof.splits() > 0
                {
                    with_split += 1;
                }
            }
        }
        let done = counts::now().since(&before);
        assert!(refuted > 300, "{refuted} sets of rows were refuted");
        assert!(with_split > 50, "{with_split} proofs have a split");
        assert!(done.splinters > 500, "{done}");
    }

    /// Pugh's example needs splinters: the sums of its tightened rows have
    /// no solution, and the sums of the rows as they are have one.
    #[test]
    fn the_thin_triangle_is_refuted_by_its_splinters() {
        let rows = thin(&[(0, 1)]);
        let before = counts::now();
        let Outcome::Unsat { proof, .. } = omega(&rows, 200_000) else {
            panic!("the rows have no integer solution");
        };
        let done = counts::now().since(&before);
        // Ten values of `11·x + 13·y - 27` and six of `7·x - 9·y + 10`.
        assert_eq!(done.splinters, 16, "{done}");
        assert!(proof.splits() >= 16, "{} splits", proof.splits());
        assert_eq!(completed(&rows), Some(false));
        // One row less, and there is a solution: 2 and 1.
        assert_eq!(completed(&rows[..3]), Some(true));
    }

    /// The same rows with a difference of two terms for `x`. No term has a
    /// bound, and the splits of part 5 do not end: before part 6 the answer
    /// was the limit.
    #[test]
    fn rows_that_splitting_does_not_end_on_are_decided() {
        let rows = thin(&[(0, 1), (1, -1)]);
        assert_eq!(completed(&rows), Some(false));
        let before = counts::now();
        assert_eq!(decided(&rows), Some(false));
        let done = counts::now().since(&before);
        assert_eq!(done.omega_tests, 1, "{done}");
        assert_eq!(decided(&rows[..3]), Some(true));
    }

    /// An equality in which no coefficient is a unit is solved by changes
    /// of variable.
    #[test]
    fn an_equality_without_a_unit_is_solved_by_changes_of_variable() {
        // `3·x + 5·y = 1`: `x` is 2, 7, 12 and so on, and -3, -8.
        let equality = [row(&[(0, 3), (1, 5)], 1), row(&[(0, -3), (1, -5)], -1)];
        let within = |least: i128, greatest: i128| {
            let mut rows = equality.to_vec();
            rows.push(row(&[(0, -1)], -least));
            rows.push(row(&[(0, 1)], greatest));
            rows
        };
        assert_eq!(completed(&equality), Some(true));
        assert_eq!(completed(&within(3, 6)), Some(false));
        assert_eq!(completed(&within(3, 7)), Some(true));
        assert_eq!(decided(&within(3, 6)), Some(false));
        // `6·x + 10·y + 15·z = 1` has solutions, and none in which `z` is
        // even: `3·z = 2·t`.
        let mut rows = vec![
            row(&[(0, 6), (1, 10), (2, 15)], 1),
            row(&[(0, -6), (1, -10), (2, -15)], -1),
        ];
        assert_eq!(completed(&rows), Some(true));
        assert_eq!(decided(&rows), Some(true));
        rows.push(row(&[(2, 3), (3, -2)], 0));
        rows.push(row(&[(2, -3), (3, 2)], 0));
        assert_eq!(completed(&rows), Some(false));
        assert_eq!(decided(&rows), Some(false));
    }

    /// The count of steps ends part 6 too.
    #[test]
    fn the_count_of_steps_ends_the_omega_test() {
        let rows = thin(&[(0, 1), (1, -1)]);
        assert!(matches!(omega(&rows, 5), Outcome::Limit));
        let mut budget = 40;
        assert!(matches!(solve(&rows, &mut budget), Outcome::Limit));
        // `1 ≤ m·x - (m - 1)·y ≤ 3` with `4 ≤ y ≤ m`: `y - 1`, `y - 2` or
        // `y - 3` would be a multiple of `m`, and none is. Every value of
        // `y` has a rational `x`, so only splinters say it, and there are
        // about `m` of them.
        let wedge = |m: i128| {
            [
                row(&[(0, -m), (1, m - 1)], -1),
                row(&[(0, m), (1, 1 - m)], 3),
                row(&[(1, -1)], -4),
                row(&[(1, 1)], m),
            ]
        };
        let before = counts::now();
        assert_eq!(completed(&wedge(12)), Some(false));
        let small = counts::now().since(&before);
        assert!(small.splinters >= 10, "{small}");
        let before = counts::now();
        assert!(matches!(omega(&wedge(1_000_000), 50_000), Outcome::Limit));
        let done = counts::now().since(&before);
        assert!(done.splinters > 100, "{done}");
    }
}
