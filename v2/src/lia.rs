//! The theory check for the rows of a candidate (`docs/v2/facts.md`, section
//! 7, step 5): whether integers exist that satisfy every row.
//!
//! The answer is a model, a proof in the steps of [V3], or the limit of
//! [J6]. A model is evaluated in the rows before it is returned, and a proof
//! is validated by the kernel before anything relies on it, so a defect here
//! can cost an answer and cannot change one.
//!
//! The method, in six parts:
//!
//! 1. **Equalities.** Two rows `e ≤ b` and `-e ≤ -b` are an equality. One
//!    with a coefficient of `1` or `-1` defines its variable, which is then
//!    replaced in every other row. A row that gains a common factor is
//!    rounded, and that is where divisibility is decided: `x = 2·q` with
//!    `x = 2·r + 1` becomes `2·q - 2·r = 1`, which rounds to a contradiction.
//! 2. **The simplex method** over the rationals, in the form with bounds on
//!    every variable and Bland's rule, which always ends. Rows that have no
//!    rational solution give the multipliers of Farkas' lemma at once, and
//!    a rational solution that happens to be whole is a model.
//! 3. **Projection.** A variable whose coefficient is `1` or `-1` in every
//!    row that bounds it from one side is removed: each pair of a lower and
//!    an upper bound is added up, and the sums have an integer solution
//!    exactly when the rows had one. The sums are rounded like any row,
//!    which decides what depends on a remainder: `4·s ≥ t` with `t ≥ 1`
//!    gives `s ≥ 1`.
//! 4. **Rounded sums.** Where the variable cannot be removed, the sum of a
//!    lower and an upper bound is still a consequence, and it is kept when
//!    rounding makes it say more than the two rows did: `7·q ≤ t` and
//!    `t ≤ 7·r + 6` give `q ≤ r`. Parts 1 to 4 are repeated while they find
//!    something, a fixed number of times at most.
//! 5. **Splitting.** A rational solution with a value `v` that is not an
//!    integer splits its variable at `⌊v⌋`. The branch with the integer
//!    nearer to `v` is preferred. Where it is refuted the other branch is
//!    entered, which leaves nothing open behind; a preferred branch that is
//!    still open may be left only a number of times, the turns, and that
//!    number is raised step by step. A model that lies along the preferred
//!    branches is then found at once, and one that lies a turn away is
//!    found before a branch that never ends is followed to the limit of
//!    nesting.
//! 6. **The Omega test** (`omega`), which decides every set of rows.
//!    Splitting ends when the solutions are bounded; on rows that have
//!    rational solutions without a bound and no integer one, and that the
//!    first four parts do not decide, it can go on for ever, and on rows
//!    with bounds it can go on for tens of thousands of tableaus. So part
//!    6 starts from the rows as they were given as soon as splitting
//!    without a turn has found nothing, with half of the steps that are
//!    left. Its splinters are as many as the coefficients are large; where
//!    it runs out of steps, part 5 takes turns with the other half.
//!
//! Splitting without a turn is tried before part 4, and again after each
//! round of it. Most candidates have a model, and it is found in the
//! tableau of the rows as they are: part 4 can add many times the rows it
//! was given, each round several times those of the round before, and
//! every exchange after that pays for them. A model that the first search
//! missed is often found with the rows of one round.
//!
//! With part 6 the method is complete: it ends without the count of steps
//! on every set of rows. The count still ends a search that is too long,
//! and the caller reports the limit.

use crate::counts;
use crate::int::Int;
use crate::rational::{Rat, gcd_u128, lcm};
use crate::terms::{End, LinearTerm, Proof, Row, Step, TermId, div_floor};
use std::borrow::Borrow;
use std::collections::BTreeMap;

mod omega;

pub enum Outcome {
    /// No integers satisfy the rows. `Step::Literal(i)` of the proof is entry
    /// `i` of `literals`, which is an index into the rows given.
    Unsat { proof: Proof, literals: Vec<usize> },
    /// Values for the atomic terms of the rows. A term that is absent may
    /// have any value.
    Sat(BTreeMap<TermId, Int>),
    /// The count of steps ran out.
    Limit,
}

/// The deepest that splits may nest. A search that needs more is ended as
/// one that ran out of steps.
const SPLIT_DEPTH: usize = 256;

fn one() -> Int {
    Int::from_u64(1)
}

fn absolute(value: &Int) -> Int {
    if value.is_negative() {
        value.negate()
    } else {
        value.clone()
    }
}

fn negated(coeffs: &BTreeMap<TermId, Int>) -> BTreeMap<TermId, Int> {
    coeffs
        .iter()
        .map(|(term, coeff)| (*term, coeff.negate()))
        .collect()
}

/// What a derived row is once its common factor is divided out.
enum Normal {
    /// `0 ≤ b` with `b ≥ 0`: it says nothing.
    Nothing,
    /// `0 ≤ b` with `b < 0`, as the row with this number.
    Contradiction(usize),
    Row(Row, usize),
}

/// Divides the common factor out of row `id`, with a [`Step::Round`] if
/// there is one.
fn normal(row: Row, id: usize, steps: &mut Vec<Step>) -> Normal {
    if row.coeffs.is_empty() {
        return if row.rhs.is_negative() {
            Normal::Contradiction(id)
        } else {
            Normal::Nothing
        };
    }
    let (rounded, divisor) = row.normalize();
    if divisor > one() {
        steps.push(Step::Round {
            source: id,
            divisor,
        });
        Normal::Row(rounded, steps.len() - 1)
    } else {
        Normal::Row(row, id)
    }
}

/// A variable that parts 1 and 3 took out of the rows, with what gives it
/// a value once the others have one.
enum Removed {
    /// The variable is this sum of the others.
    Defined(TermId, LinearTerm),
    /// The variable lies within the bounds that these rows give it.
    Projected(TermId, Vec<Row>),
}

/// How many more rows than it removes a projection may add.
const GROWTH: usize = 8;

/// How often parts 1 to 4 are repeated before splitting begins.
const ROUNDS: usize = 4;

/// Part 1. Leaves in `active` rows without a stated equality that has a
/// unit coefficient, and returns the number of a contradictory row if it
/// meets one. `removed` receives each replaced variable with its definition,
/// in the order of replacement.
fn equalities(
    active: &mut Vec<(Row, usize)>,
    steps: &mut Vec<Step>,
    removed: &mut Vec<Removed>,
) -> Option<usize> {
    loop {
        // The tightest row for each left-hand side.
        let mut best: BTreeMap<BTreeMap<TermId, Int>, (Int, usize)> = BTreeMap::new();
        for (row, id) in active.drain(..) {
            match best.get(&row.coeffs) {
                Some((rhs, _)) if *rhs <= row.rhs => {}
                _ => {
                    best.insert(row.coeffs, (row.rhs, id));
                }
            }
        }
        // Opposite rows: a contradiction, or an equality.
        let mut equality = None;
        for (coeffs, (rhs, id)) in &best {
            if coeffs.values().next().is_none_or(Int::is_negative) {
                continue;
            }
            let Some((other_rhs, other_id)) = best.get(&negated(coeffs)) else {
                continue;
            };
            let sum = rhs.plus(other_rhs);
            if sum.is_negative() {
                steps.push(Step::Combine(vec![(*id, one()), (*other_id, one())]));
                return Some(steps.len() - 1);
            }
            if sum.is_zero()
                && equality.is_none()
                && let Some((term, coeff)) =
                    coeffs.iter().find(|(_, coeff)| absolute(coeff) == one())
            {
                equality = Some((
                    coeffs.clone(),
                    rhs.clone(),
                    *id,
                    *other_id,
                    *term,
                    !coeff.is_negative(),
                ));
            }
        }
        let Some((coeffs, rhs, at_most, at_least, term, positive)) = equality else {
            *active = best
                .into_iter()
                .map(|(coeffs, (rhs, id))| (Row { coeffs, rhs }, id))
                .collect();
            return None;
        };
        // `sign·term + rest = rhs`, so `term = sign·(rhs - rest)`.
        let mut definition = LinearTerm::constant(rhs.clone());
        for (other, coeff) in &coeffs {
            if *other != term {
                definition.coeffs.insert(*other, coeff.negate());
            }
        }
        if !positive {
            definition = definition.negate();
        }
        removed.push(Removed::Defined(term, definition));
        let opposite = negated(&coeffs);
        let upper = Row {
            coeffs: coeffs.clone(),
            rhs: rhs.clone(),
        };
        let lower = Row {
            coeffs: opposite.clone(),
            rhs: rhs.negate(),
        };
        for (row_coeffs, (row_rhs, id)) in best {
            if row_coeffs == coeffs || row_coeffs == opposite {
                continue;
            }
            let row = Row {
                coeffs: row_coeffs,
                rhs: row_rhs,
            };
            let Some(coeff) = row.coeffs.get(&term).cloned() else {
                active.push((row, id));
                continue;
            };
            // The side of the equality that cancels the term.
            let multiplier = absolute(&coeff);
            let (side, side_id) = if coeff.is_negative() == positive {
                (&upper, at_most)
            } else {
                (&lower, at_least)
            };
            let combined = row.combine(&one(), side, &multiplier);
            steps.push(Step::Combine(vec![(id, one()), (side_id, multiplier)]));
            match normal(combined, steps.len() - 1, steps) {
                Normal::Nothing => {}
                Normal::Contradiction(contradiction) => return Some(contradiction),
                Normal::Row(row, id) => active.push((row, id)),
            }
        }
    }
}

/// Part 3, one variable. `Ok(false)` when no variable can be removed.
/// `Err` has the number of a contradictory row.
fn projection(
    active: &mut Vec<(Row, usize)>,
    steps: &mut Vec<Step>,
    removed: &mut Vec<Removed>,
) -> Result<bool, usize> {
    // For each variable: the rows that bound it from below and from above,
    // and whether its coefficient is a unit in all of each kind.
    struct Sides {
        lower: usize,
        upper: usize,
        lower_unit: bool,
        upper_unit: bool,
    }
    let mut sides: BTreeMap<TermId, Sides> = BTreeMap::new();
    for (row, _) in active.iter() {
        for (term, coeff) in &row.coeffs {
            let entry = sides.entry(*term).or_insert(Sides {
                lower: 0,
                upper: 0,
                lower_unit: true,
                upper_unit: true,
            });
            let unit = absolute(coeff) == one();
            if coeff.is_negative() {
                entry.lower += 1;
                entry.lower_unit &= unit;
            } else {
                entry.upper += 1;
                entry.upper_unit &= unit;
            }
        }
    }
    let chosen = sides
        .iter()
        .filter(|(_, side)| {
            (side.lower == 0 || side.upper == 0 || side.lower_unit || side.upper_unit)
                && side.lower * side.upper <= side.lower + side.upper + GROWTH
        })
        .min_by_key(|(term, side)| (side.lower * side.upper, **term))
        .map(|(term, _)| *term);
    let Some(term) = chosen else {
        return Ok(false);
    };
    let (with, without): (Vec<_>, Vec<_>) = active
        .drain(..)
        .partition(|(row, _)| row.coeffs.contains_key(&term));
    *active = without;
    let (lower, upper): (Vec<_>, Vec<_>) = with
        .iter()
        .partition(|(row, _)| row.coeffs[&term].is_negative());
    if let Some(contradiction) = sums(term, &lower, &upper, steps, active) {
        return Err(contradiction);
    }
    removed.push(Removed::Projected(
        term,
        with.into_iter().map(|(row, _)| row).collect(),
    ));
    Ok(true)
}

/// Adds up each row of `lower` with each row of `upper` so that `term` is
/// gone, and puts the sums that say something into `active`. The two sides
/// bound the term from opposite directions. Returns the number of a
/// contradictory row if it meets one.
fn sums<L: Borrow<(Row, usize)>, U: Borrow<(Row, usize)>>(
    term: TermId,
    lower: &[L],
    upper: &[U],
    steps: &mut Vec<Step>,
    active: &mut Vec<(Row, usize)>,
) -> Option<usize> {
    for low in lower {
        let (low, low_id) = low.borrow();
        for high in upper {
            let (high, high_id) = high.borrow();
            let on_low = absolute(&high.coeffs[&term]);
            let on_high = absolute(&low.coeffs[&term]);
            let combined = low.combine(&on_low, high, &on_high);
            steps.push(Step::Combine(vec![(*low_id, on_low), (*high_id, on_high)]));
            match normal(combined, steps.len() - 1, steps) {
                Normal::Nothing => {}
                Normal::Contradiction(contradiction) => return Some(contradiction),
                Normal::Row(row, id) => active.push((row, id)),
            }
        }
    }
    None
}

/// The rows in which a term occurs, each with the coefficient of the term.
type Occurrences = Vec<(usize, i128)>;

/// Whether the sum `by_low·low + by_high·high` can have a common factor
/// above 1 in its coefficients. The rows are given with machine integers,
/// in the order of their terms; `None` when the arithmetic leaves them.
fn may_round(
    low: &[(TermId, i128)],
    by_low: i128,
    high: &[(TermId, i128)],
    by_high: i128,
) -> Option<bool> {
    let mut common: u128 = 0;
    let (mut i, mut j) = (0, 0);
    while i < low.len() || j < high.len() {
        let coeff = if j == high.len() || (i < low.len() && low[i].0 < high[j].0) {
            i += 1;
            by_low.checked_mul(low[i - 1].1)?
        } else if i == low.len() || high[j].0 < low[i].0 {
            j += 1;
            by_high.checked_mul(high[j - 1].1)?
        } else {
            i += 1;
            j += 1;
            by_low
                .checked_mul(low[i - 1].1)?
                .checked_add(by_high.checked_mul(high[j - 1].1)?)?
        };
        if coeff != 0 {
            common = gcd_u128(common, coeff.unsigned_abs());
            if common == 1 {
                return Some(false);
            }
        }
    }
    Some(common > 1)
}

/// Part 4, once over every pair of rows. `Ok(true)` when a row was added.
/// `Err` has the number of a contradictory row, or nothing when the count
/// of steps ran out.
fn rounded_sums(
    active: &mut Vec<(Row, usize)>,
    steps: &mut Vec<Step>,
    budget: &mut u64,
) -> Result<bool, Option<usize>> {
    let mut tightest: BTreeMap<BTreeMap<TermId, Int>, Int> = BTreeMap::new();
    for (row, _) in active.iter() {
        match tightest.get(&row.coeffs) {
            Some(rhs) if *rhs <= row.rhs => {}
            _ => {
                tightest.insert(row.coeffs.clone(), row.rhs.clone());
            }
        }
    }
    // The rows with machine integers, and for each term the rows that bound
    // it below and above. A row with a larger coefficient takes no part.
    let small: Vec<Option<Vec<(TermId, i128)>>> = active
        .iter()
        .map(|(row, _)| {
            row.coeffs
                .iter()
                .map(|(term, coeff)| coeff.to_i128().map(|coeff| (*term, coeff)))
                .collect()
        })
        .collect();
    let mut sides: BTreeMap<TermId, (Occurrences, Occurrences)> = BTreeMap::new();
    for (index, row) in small.iter().enumerate() {
        for (term, coeff) in row.iter().flatten() {
            let entry = sides.entry(*term).or_default();
            if *coeff < 0 {
                entry.0.push((index, *coeff));
            } else {
                entry.1.push((index, *coeff));
            }
        }
    }
    let mut added = false;
    for (lower, upper) in sides.values() {
        if *budget == 0 {
            return Err(None);
        }
        *budget -= 1;
        for (low, on_low) in lower {
            for (high, on_high) in upper {
                let (Some(low_row), Some(high_row)) = (&small[*low], &small[*high]) else {
                    continue;
                };
                let (Some(on_low), Ok(common)) = (
                    on_low.checked_neg(),
                    i128::try_from(gcd_u128(on_low.unsigned_abs(), on_high.unsigned_abs())),
                ) else {
                    continue;
                };
                let (by_low, by_high) = (on_high / common, on_low / common);
                if may_round(low_row, by_low, high_row, by_high) != Some(true) {
                    continue;
                }
                let (by_low, by_high) = (Int::from_i128(by_low), Int::from_i128(by_high));
                let sum = active[*low].0.combine(&by_low, &active[*high].0, &by_high);
                let (rounded, divisor) = sum.normalize();
                // Without a remainder the rounded row says what the sum
                // says, and the sum says nothing that the two rows do not.
                if divisor <= one()
                    || sum
                        .rhs
                        .divide(&divisor)
                        .expect("a positive divisor")
                        .1
                        .is_zero()
                    || tightest
                        .get(&rounded.coeffs)
                        .is_some_and(|rhs| *rhs <= rounded.rhs)
                {
                    continue;
                }
                steps.push(Step::Combine(vec![
                    (active[*low].1, by_low),
                    (active[*high].1, by_high),
                ]));
                steps.push(Step::Round {
                    source: steps.len() - 1,
                    divisor,
                });
                tightest.insert(rounded.coeffs.clone(), rounded.rhs.clone());
                active.push((rounded, steps.len() - 1));
                added = true;
            }
        }
    }
    Ok(added)
}

/// The value of a projected variable: the least that its lower bounds
/// allow, or the greatest that its upper bounds allow when it has no lower
/// bound.
fn within(term: TermId, rows: &[Row], model: &BTreeMap<TermId, Int>) -> Int {
    let mut lower: Option<Int> = None;
    let mut upper: Option<Int> = None;
    for row in rows {
        let coeff = &row.coeffs[&term];
        let mut rest = row.rhs.clone();
        for (other, other_coeff) in &row.coeffs {
            if *other != term {
                let value = model.get(other).cloned().unwrap_or_default();
                rest = rest.minus(&other_coeff.times(&value));
            }
        }
        // `coeff·term ≤ rest`.
        if coeff.is_negative() {
            // `term ≥ ⌈-rest / -coeff⌉ = -⌊rest / -coeff⌋`.
            let bound = div_floor(&rest, &coeff.negate()).negate();
            lower = Some(match lower {
                Some(old) if old >= bound => old,
                _ => bound,
            });
        } else {
            let bound = div_floor(&rest, coeff);
            upper = Some(match upper {
                Some(old) if old <= bound => old,
                _ => bound,
            });
        }
    }
    lower.or(upper).unwrap_or_default()
}

/// The count of steps ran out.
struct Limit;

/// A bound of a variable, with the number of the row that states it.
type Bound = Option<(Rat, usize)>;

/// Part 2: a tableau in which every basic variable is a sum of the others,
/// and every variable has its bounds and a value within them, or a basic
/// variable is still out of its bounds.
///
/// Every entry is a rational in lowest terms. One denominator for a whole
/// row would make an exchange cheaper, and was tried: the denominators grow
/// past the machine integers on the rows of ordinary programs, where the
/// entries in lowest terms stay small.
struct Simplex {
    /// The atomic terms; the variables after them are the left-hand sides of
    /// rows of more than one term.
    terms: Vec<TermId>,
    rows: Vec<Option<BTreeMap<usize, Rat>>>,
    value: Vec<Rat>,
    lower: Vec<Bound>,
    upper: Vec<Bound>,
    /// The bounds of left-hand sides that are not yet in force. They are
    /// brought in one at a time, each from a state in which the others hold:
    /// that takes a few exchanges for each, where all at once can take
    /// thousands.
    pending: Vec<(usize, Bound, Bound)>,
}

impl Simplex {
    fn new(active: &[(Row, usize)]) -> Simplex {
        counts::count(|counts| counts.tableaus += 1);
        let mut terms: Vec<TermId> = active
            .iter()
            .flat_map(|(row, _)| row.coeffs.keys().copied())
            .collect();
        terms.sort_unstable();
        terms.dedup();
        let index: BTreeMap<TermId, usize> = terms
            .iter()
            .enumerate()
            .map(|(position, term)| (*term, position))
            .collect();
        let mut simplex = Simplex {
            rows: vec![None; terms.len()],
            value: vec![Rat::zero(); terms.len()],
            lower: vec![None; terms.len()],
            upper: vec![None; terms.len()],
            pending: Vec::new(),
            terms,
        };
        let mut sides: BTreeMap<BTreeMap<TermId, Int>, usize> = BTreeMap::new();
        for (row, id) in active {
            let positive = row.coeffs.values().next().is_some_and(|c| !c.is_negative());
            let variable = if row.coeffs.len() == 1 {
                index[row.coeffs.keys().next().expect("one term")]
            } else {
                let side = if positive {
                    row.coeffs.clone()
                } else {
                    negated(&row.coeffs)
                };
                match sides.get(&side) {
                    Some(variable) => *variable,
                    None => {
                        let variable = simplex.rows.len();
                        simplex.rows.push(Some(
                            side.iter()
                                .map(|(term, coeff)| (index[term], Rat::from_int(coeff)))
                                .collect(),
                        ));
                        simplex.value.push(Rat::zero());
                        simplex.lower.push(None);
                        simplex.upper.push(None);
                        sides.insert(side, variable);
                        variable
                    }
                }
            };
            // The rows are normal, so a row of one term has the coefficient
            // 1 or -1.
            if positive {
                let bound = Rat::from_int(&row.rhs);
                if simplex.upper[variable]
                    .as_ref()
                    .is_none_or(|(old, _)| bound < *old)
                {
                    simplex.upper[variable] = Some((bound, *id));
                }
            } else {
                let bound = Rat::from_int(&row.rhs.negate());
                if simplex.lower[variable]
                    .as_ref()
                    .is_none_or(|(old, _)| bound > *old)
                {
                    simplex.lower[variable] = Some((bound, *id));
                }
            }
        }
        // Every term starts at the value within its bounds that is nearest
        // to zero, and every left-hand side at the value that follows.
        for variable in 0..simplex.terms.len() {
            if let Some((bound, _)) = &simplex.lower[variable]
                && !bound.is_negative()
            {
                simplex.value[variable] = bound.clone();
            } else if let Some((bound, _)) = &simplex.upper[variable]
                && bound.is_negative()
            {
                simplex.value[variable] = bound.clone();
            }
        }
        for variable in simplex.terms.len()..simplex.rows.len() {
            let mut sum = Rat::zero();
            for (other, coeff) in simplex.rows[variable].as_ref().expect("a basic row") {
                sum = sum.plus(&coeff.times(&simplex.value[*other]));
            }
            simplex.value[variable] = sum;
        }
        for variable in (simplex.terms.len()..simplex.rows.len()).rev() {
            let lower = simplex.lower[variable].take();
            let upper = simplex.upper[variable].take();
            simplex.pending.push((variable, lower, upper));
        }
        simplex
    }

    fn below_lower(&self, variable: usize) -> bool {
        self.lower[variable]
            .as_ref()
            .is_some_and(|(bound, _)| self.value[variable] < *bound)
    }

    fn above_upper(&self, variable: usize) -> bool {
        self.upper[variable]
            .as_ref()
            .is_some_and(|(bound, _)| self.value[variable] > *bound)
    }

    fn can_rise(&self, variable: usize) -> bool {
        self.upper[variable]
            .as_ref()
            .is_none_or(|(bound, _)| self.value[variable] < *bound)
    }

    fn can_fall(&self, variable: usize) -> bool {
        self.lower[variable]
            .as_ref()
            .is_none_or(|(bound, _)| self.value[variable] > *bound)
    }

    /// Changes the value of `variable`, which is not basic, by `change`,
    /// and the values of the basic variables with it.
    fn shift(&mut self, variable: usize, change: &Rat) {
        for basic in 0..self.rows.len() {
            if let Some(row) = &self.rows[basic]
                && let Some(coeff) = row.get(&variable)
            {
                self.value[basic] = self.value[basic].plus(&coeff.times(change));
            }
        }
        self.value[variable] = self.value[variable].plus(change);
    }

    /// Exchanges the basic variable `leaving` with `entering`, and gives
    /// `leaving` the value `to`.
    fn pivot(&mut self, leaving: usize, entering: usize, to: &Rat) {
        let row = self.rows[leaving].take().expect("a basic row");
        let coeff = row[&entering].clone();
        let change = to
            .minus(&self.value[leaving])
            .over(&coeff)
            .expect("the coefficient is not zero");
        self.value[leaving] = to.clone();
        self.shift(entering, &change);
        // `entering` as a sum of the others.
        let inverse = Rat::one()
            .over(&coeff)
            .expect("the coefficient is not zero");
        let mut written = row.len() as u64;
        let mut solved: BTreeMap<usize, Rat> = BTreeMap::new();
        solved.insert(leaving, inverse.clone());
        for (variable, other) in &row {
            if *variable != entering {
                solved.insert(*variable, other.times(&inverse).negate());
            }
        }
        for basic in 0..self.rows.len() {
            let Some(other) = &mut self.rows[basic] else {
                continue;
            };
            let Some(factor) = other.remove(&entering) else {
                continue;
            };
            written += solved.len() as u64;
            for (variable, part) in &solved {
                let sum = other
                    .get(variable)
                    .cloned()
                    .unwrap_or_else(Rat::zero)
                    .plus(&factor.times(part));
                if sum.is_zero() {
                    other.remove(variable);
                } else {
                    other.insert(*variable, sum);
                }
            }
        }
        self.rows[entering] = Some(solved);
        counts::count(|counts| {
            counts.exchanges += 1;
            counts.entries += written;
        });
    }

    /// The multipliers of a contradiction, as integers.
    fn farkas(parts: Vec<(usize, Rat)>) -> Vec<(usize, Int)> {
        let mut common = one();
        for (_, multiplier) in &parts {
            common = lcm(&common, &multiplier.parts().1);
        }
        let scale = Rat::from_int(&common);
        parts
            .into_iter()
            .map(|(id, multiplier)| {
                let scaled = multiplier.times(&scale);
                (id, scaled.to_int().expect("the denominators are cleared"))
            })
            .collect()
    }

    /// Brings the pending bounds into force one after another, and every
    /// basic variable within its bounds; or returns the rows and multipliers
    /// that add up to a contradiction.
    fn check(&mut self, budget: &mut u64) -> Result<Option<Vec<(usize, Int)>>, Limit> {
        while let Some((variable, lower, upper)) = self.pending.pop() {
            for (bound, is_lower) in [(lower, true), (upper, false)] {
                let Some((bound, reason)) = bound else {
                    continue;
                };
                let contradiction = if is_lower {
                    self.at_least(variable, bound, reason)
                } else {
                    self.at_most(variable, bound, reason)
                };
                if let Some(parts) = contradiction {
                    return Ok(Some(parts));
                }
                if let Some(parts) = self.repair(budget)? {
                    return Ok(Some(parts));
                }
            }
        }
        self.repair(budget)
    }

    /// Brings every basic variable within the bounds that are in force, by
    /// Bland's rule: the first variable that is out of its bounds leaves,
    /// and the first that can move the right way enters. It cannot go round
    /// in a circle.
    fn repair(&mut self, budget: &mut u64) -> Result<Option<Vec<(usize, Int)>>, Limit> {
        loop {
            let Some(leaving) = (0..self.rows.len()).find(|variable| {
                self.rows[*variable].is_some()
                    && (self.below_lower(*variable) || self.above_upper(*variable))
            }) else {
                return Ok(None);
            };
            if *budget == 0 {
                return Err(Limit);
            }
            *budget -= 1;
            let rising = self.below_lower(leaving);
            let row = self.rows[leaving].as_ref().expect("a basic row");
            let entering = row.iter().find_map(|(variable, coeff)| {
                let helps = if coeff.is_positive() == rising {
                    self.can_rise(*variable)
                } else {
                    self.can_fall(*variable)
                };
                helps.then_some(*variable)
            });
            let (bound, reason) = if rising {
                self.lower[leaving].clone().expect("a lower bound")
            } else {
                self.upper[leaving].clone().expect("an upper bound")
            };
            match entering {
                Some(entering) => self.pivot(leaving, entering, &bound),
                None => {
                    // No variable of the row can move: each stands at the
                    // bound that keeps `leaving` out of its own.
                    let mut parts = vec![(reason, Rat::one())];
                    for (variable, coeff) in row {
                        let at_upper = coeff.is_positive() == rising;
                        let (_, id) = if at_upper {
                            self.upper[*variable].as_ref().expect("an upper bound")
                        } else {
                            self.lower[*variable].as_ref().expect("a lower bound")
                        };
                        let multiplier = if coeff.is_negative() {
                            coeff.negate()
                        } else {
                            coeff.clone()
                        };
                        parts.push((*id, multiplier));
                    }
                    return Ok(Some(Simplex::farkas(parts)));
                }
            }
        }
    }

    /// States `variable ≤ bound` by row `reason`. Returns a contradiction
    /// with the lower bound, if there is one.
    fn at_most(&mut self, variable: usize, bound: Rat, reason: usize) -> Option<Vec<(usize, Int)>> {
        if let Some((old, _)) = &self.upper[variable]
            && *old <= bound
        {
            return None;
        }
        if let Some((lower, id)) = &self.lower[variable]
            && *lower > bound
        {
            return Some(vec![(*id, one()), (reason, one())]);
        }
        if self.rows[variable].is_none() && self.value[variable] > bound {
            let change = bound.minus(&self.value[variable]);
            self.shift(variable, &change);
        }
        self.upper[variable] = Some((bound, reason));
        None
    }

    fn at_least(
        &mut self,
        variable: usize,
        bound: Rat,
        reason: usize,
    ) -> Option<Vec<(usize, Int)>> {
        if let Some((old, _)) = &self.lower[variable]
            && *old >= bound
        {
            return None;
        }
        if let Some((upper, id)) = &self.upper[variable]
            && *upper < bound
        {
            return Some(vec![(*id, one()), (reason, one())]);
        }
        if self.rows[variable].is_none() && self.value[variable] < bound {
            let change = bound.minus(&self.value[variable]);
            self.shift(variable, &change);
        }
        self.lower[variable] = Some((bound, reason));
        None
    }

    /// Part 5. `next` is the number that the next row on this path gets,
    /// `depth` the number of splits that may still nest, and `turns` the
    /// number of times the search may still leave the branch it prefers. A
    /// branch that would need more of either is left open.
    fn search(
        &mut self,
        next: usize,
        depth: usize,
        turns: usize,
        budget: &mut u64,
    ) -> Result<Found, Limit> {
        if *budget == 0 {
            return Err(Limit);
        }
        *budget -= 1;
        if let Some(parts) = self.check(budget)? {
            return Ok(Found::Refuted(Proof {
                steps: vec![Step::Combine(parts)],
                end: End::Close(next),
            }));
        }
        let Some(variable) =
            (0..self.terms.len()).find(|variable| !self.value[*variable].is_integer())
        else {
            return Ok(Found::Model(
                self.terms
                    .iter()
                    .enumerate()
                    .map(|(variable, term)| {
                        (*term, self.value[variable].to_int().expect("an integer"))
                    })
                    .collect(),
            ));
        };
        if depth == 0 {
            return Ok(Found::Open);
        }
        counts::count(|counts| counts.splits += 1);
        let bound = self.value[variable].floor();
        let floor = Rat::from_int(&bound);
        // The branch with the nearer integer is preferred.
        let prefers_low = self.value[variable].minus(&floor) <= Rat::ratio(1, 2);
        let mut low = Found::Open;
        let mut high = Found::Open;
        // With a turn to spend, the other branch is tried first: a model is
        // often one turn away near the root, and a preferred branch can be
        // long. Without one, the preferred branch is tried, and the other
        // only when the preferred one is refuted: that costs no turn, since
        // nothing is left open behind.
        let spends = turns > 0;
        let mut order = if spends {
            vec![(prefers_low, turns), (!prefers_low, turns - 1)]
        } else {
            vec![(!prefers_low, 0), (prefers_low, 0)]
        };
        while let Some((is_low, turns)) = order.pop() {
            // The row of the split has the number `next` in both branches.
            let saved = if is_low {
                self.upper[variable].clone()
            } else {
                self.lower[variable].clone()
            };
            let contradiction = if is_low {
                self.at_most(variable, floor.clone(), next)
            } else {
                self.at_least(variable, floor.plus(&Rat::one()), next)
            };
            let found = match contradiction {
                Some(parts) => Found::Refuted(Proof {
                    steps: vec![Step::Combine(parts)],
                    end: End::Close(next + 1),
                }),
                None => self.search(next + 1, depth - 1, turns, budget)?,
            };
            if is_low {
                self.upper[variable] = saved;
            } else {
                self.lower[variable] = saved;
            }
            if let Found::Model(model) = found {
                return Ok(Found::Model(model));
            }
            if !spends && !matches!(found, Found::Refuted(_)) {
                order.clear();
            }
            if is_low {
                low = found;
            } else {
                high = found;
            }
        }
        let (Found::Refuted(low), Found::Refuted(high)) = (low, high) else {
            return Ok(Found::Open);
        };
        let mut form = BTreeMap::new();
        form.insert(self.terms[variable], one());
        Ok(Found::Refuted(Proof {
            steps: Vec::new(),
            end: End::Split {
                form,
                bound,
                low: Box::new(low),
                high: Box::new(high),
            },
        }))
    }
}

enum Found {
    Model(BTreeMap<TermId, Int>),
    Refuted(Proof),
    /// Neither: a branch needs more nested splits or more turns than were
    /// allowed.
    Open,
}

/// Which rows of a proof its ends rely on.
struct Used {
    steps: Vec<bool>,
    /// For a split: whether each branch relies on the row of the split.
    branches: Option<Box<(bool, Used, bool, Used)>>,
}

fn mark(proof: &Proof, path: &mut Vec<bool>) -> Used {
    let base = path.len();
    path.resize(base + proof.steps.len(), false);
    let branches = match &proof.end {
        End::Close(row) => {
            path[*row] = true;
            None
        }
        End::Split { low, high, .. } => {
            path.push(false);
            let low_used = mark(low, path);
            let low_split = path.pop().expect("the row of the split");
            path.push(false);
            let high_used = mark(high, path);
            let high_split = path.pop().expect("the row of the split");
            Some(Box::new((low_split, low_used, high_split, high_used)))
        }
    };
    for (index, step) in proof.steps.iter().enumerate().rev() {
        if !path[base + index] {
            continue;
        }
        match step {
            Step::Literal(_) => {}
            Step::Combine(parts) => {
                for (source, _) in parts {
                    path[*source] = true;
                }
            }
            Step::Round { source, .. } => path[*source] = true,
        }
    }
    let steps = path[base..].to_vec();
    path.truncate(base);
    Used { steps, branches }
}

/// The proof without the rows that nothing relies on, and without a split
/// one branch of which does not rely on it. `renumber` maps a row of the
/// old path to its number on the new one; `length` is the length of the new
/// path.
fn rebuild(
    proof: &Proof,
    used: &Used,
    renumber: &mut Vec<usize>,
    length: usize,
    literals: &mut Vec<usize>,
) -> Proof {
    let base = renumber.len();
    let mut length = length;
    let mut steps = Vec::new();
    for (index, step) in proof.steps.iter().enumerate() {
        if !used.steps[index] {
            renumber.push(usize::MAX);
            continue;
        }
        steps.push(match step {
            Step::Literal(literal) => {
                let position = literals
                    .iter()
                    .position(|seen| seen == literal)
                    .unwrap_or_else(|| {
                        literals.push(*literal);
                        literals.len() - 1
                    });
                Step::Literal(position)
            }
            Step::Combine(parts) => Step::Combine(
                parts
                    .iter()
                    .map(|(source, multiplier)| (renumber[*source], multiplier.clone()))
                    .collect(),
            ),
            Step::Round { source, divisor } => Step::Round {
                source: renumber[*source],
                divisor: divisor.clone(),
            },
        });
        renumber.push(length);
        length += 1;
    }
    let end = match (&proof.end, &used.branches) {
        (End::Close(row), _) => End::Close(renumber[*row]),
        (
            End::Split {
                form,
                bound,
                low,
                high,
            },
            Some(branches),
        ) => {
            let (low_split, low_used, high_split, high_used) = &**branches;
            // A branch that does not rely on the row of the split refutes
            // the rows above it alone.
            let alone = if !low_split {
                Some((low, low_used))
            } else if !high_split {
                Some((high, high_used))
            } else {
                None
            };
            if let Some((branch, branch_used)) = alone {
                renumber.push(usize::MAX);
                let inner = rebuild(branch, branch_used, renumber, length, literals);
                renumber.truncate(base);
                steps.extend(inner.steps);
                return Proof {
                    steps,
                    end: inner.end,
                };
            }
            renumber.push(length);
            let low = rebuild(low, low_used, renumber, length + 1, literals);
            let high = rebuild(high, high_used, renumber, length + 1, literals);
            End::Split {
                form: form.clone(),
                bound: bound.clone(),
                low: Box::new(low),
                high: Box::new(high),
            }
        }
        (End::Split { .. }, None) => unreachable!("a split is marked with its branches"),
    };
    renumber.truncate(base);
    Proof { steps, end }
}

fn pruned(proof: &Proof) -> Outcome {
    let used = mark(proof, &mut Vec::new());
    let mut literals = Vec::new();
    let proof = rebuild(proof, &used, &mut Vec::new(), 0, &mut literals);
    Outcome::Unsat { proof, literals }
}

/// Decides whether integers satisfy every row. `budget` is the count of
/// steps that may still be taken; it is reduced by the steps taken.
pub fn solve(rows: &[Row], budget: &mut u64) -> Outcome {
    let mut steps: Vec<Step> = (0..rows.len()).map(Step::Literal).collect();
    let close = |steps: Vec<Step>, row: usize| {
        pruned(&Proof {
            steps,
            end: End::Close(row),
        })
    };
    let mut active = Vec::new();
    for (index, row) in rows.iter().enumerate() {
        match normal(row.clone(), index, &mut steps) {
            Normal::Nothing => {}
            Normal::Contradiction(row) => return close(steps, row),
            Normal::Row(row, id) => active.push((row, id)),
        }
    }
    let mut removed = Vec::new();
    if let Some(row) = equalities(&mut active, &mut steps, &mut removed) {
        return close(steps, row);
    }
    let finish = |mut model: BTreeMap<TermId, Int>, removed: &[Removed]| {
        for row in rows {
            for term in row.coeffs.keys() {
                if !removed.iter().any(|entry| match entry {
                    Removed::Defined(gone, _) | Removed::Projected(gone, _) => gone == term,
                }) {
                    model.entry(*term).or_default();
                }
            }
        }
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
        debug_assert!(rows.iter().all(|row| row.holds(&model)));
        Outcome::Sat(model)
    };
    let refuted = |mut steps: Vec<Step>, found: Proof| {
        steps.extend(found.steps);
        pruned(&Proof {
            steps,
            end: found.end,
        })
    };
    let mut simplex;
    let mut round = 0;
    loop {
        // Part 3, with part 1 after each projection.
        loop {
            if *budget == 0 {
                return Outcome::Limit;
            }
            *budget -= 1;
            match projection(&mut active, &mut steps, &mut removed) {
                Err(row) => return close(steps, row),
                Ok(false) => break,
                Ok(true) => {}
            }
            if let Some(row) = equalities(&mut active, &mut steps, &mut removed) {
                return close(steps, row);
            }
        }
        // Part 2, and a rational solution that is whole.
        simplex = Simplex::new(&active);
        match simplex.search(steps.len(), 0, 0, budget) {
            Err(Limit) => return Outcome::Limit,
            Ok(Found::Refuted(found)) => return refuted(steps, found),
            Ok(Found::Model(model)) => return finish(model, &removed),
            Ok(Found::Open) => {}
        }
        // Part 5 without a turn, before part 4 adds rows: most candidates
        // have a model, and it is found in the small tableau. Where it is
        // not, the rows that part 4 adds may show the way to one, and each
        // round of part 4 has several times the rows of the one before:
        // the search is made again before the next.
        match simplex.search(steps.len(), SPLIT_DEPTH, 0, budget) {
            Err(Limit) => return Outcome::Limit,
            Ok(Found::Refuted(found)) => return refuted(steps, found),
            Ok(Found::Model(model)) => return finish(model, &removed),
            Ok(Found::Open) => {}
        }
        if round == ROUNDS {
            break;
        }
        round += 1;
        // Part 4, and part 1 on what it adds.
        match rounded_sums(&mut active, &mut steps, budget) {
            Err(None) => return Outcome::Limit,
            Err(Some(row)) => return close(steps, row),
            Ok(false) => break,
            Ok(true) => {
                if let Some(row) = equalities(&mut active, &mut steps, &mut removed) {
                    return close(steps, row);
                }
            }
        }
    }
    // Part 6, with half of the steps that are left. The rows have kept
    // their secret from a search without a turn in every round, and the
    // splits can go on with such rows for tens of thousands of tableaus
    // where the test decides them in a few sums.
    let mut share = *budget / 2;
    *budget -= share;
    match complete(rows, steps.clone(), budget) {
        Outcome::Limit => {}
        answer => {
            *budget += share;
            return answer;
        }
    }
    // Part 5 with turns, with the other half, where the test did not end:
    // its splinters are as many as the coefficients are large. The number
    // of turns is raised step by step: a search to the end of the branches
    // it prefers would not return from one in which every split leaves a
    // rational solution.
    let mut turns = 1;
    loop {
        match simplex.search(steps.len(), SPLIT_DEPTH, turns, &mut share) {
            Err(Limit) => break,
            Ok(Found::Open) if turns < SPLIT_DEPTH => turns *= 2,
            Ok(Found::Open) => break,
            Ok(Found::Refuted(found)) => {
                *budget += share;
                return refuted(steps, found);
            }
            Ok(Found::Model(model)) => {
                *budget += share;
                return finish(model, &removed);
            }
        }
    }
    *budget += share;
    Outcome::Limit
}

/// Part 6, on the rows as they were given. `steps` holds the steps so far,
/// the literals first.
fn complete(rows: &[Row], mut steps: Vec<Step>, budget: &mut u64) -> Outcome {
    counts::count(|counts| counts.omega_tests += 1);
    let mut active = Vec::new();
    for (index, row) in rows.iter().enumerate() {
        match normal(row.clone(), index, &mut steps) {
            Normal::Nothing => {}
            Normal::Contradiction(row) => {
                return pruned(&Proof {
                    steps,
                    end: End::Close(row),
                });
            }
            Normal::Row(row, id) => active.push((row, id)),
        }
    }
    match omega::decide(active, &mut steps, budget) {
        Err(Limit) => Outcome::Limit,
        Ok(omega::Answer::Refuted(end)) => pruned(&Proof { steps, end }),
        Ok(omega::Answer::Model(mut model)) => {
            for row in rows {
                for term in row.coeffs.keys() {
                    model.entry(*term).or_default();
                }
            }
            debug_assert!(rows.iter().all(|row| row.holds(&model)));
            Outcome::Sat(model)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel;
    use crate::rng::Rng;
    use crate::terms::TheoryLemma;

    pub(super) fn row(coeffs: &[(TermId, i128)], rhs: i128) -> Row {
        Row {
            coeffs: coeffs
                .iter()
                .filter(|(_, coeff)| *coeff != 0)
                .map(|(term, coeff)| (*term, Int::from_i128(*coeff)))
                .collect(),
            rhs: Int::from_i128(rhs),
        }
    }

    /// What an outcome says, with a proof validated by the kernel and a
    /// model evaluated in the rows.
    pub(super) fn answer(outcome: Outcome, rows: &[Row]) -> Option<bool> {
        match outcome {
            Outcome::Limit => None,
            Outcome::Sat(model) => {
                for row in rows {
                    assert!(row.holds(&model), "the model fails {row:?}");
                }
                let terms: Vec<TermId> = rows
                    .iter()
                    .flat_map(|row| row.coeffs.keys().copied())
                    .collect();
                for term in model.keys() {
                    assert!(terms.contains(term), "{term} is no term of the rows");
                }
                Some(true)
            }
            Outcome::Unsat { proof, literals } => {
                let lemma = TheoryLemma {
                    literals: literals.iter().map(|index| (*index, true)).collect(),
                    proof,
                };
                kernel::validate_lemma(&lemma, rows).expect("the kernel validates the proof");
                Some(false)
            }
        }
    }

    /// The answer of [`solve`].
    pub(super) fn decided(rows: &[Row]) -> Option<bool> {
        let mut budget = 200_000;
        answer(solve(rows, &mut budget), rows)
    }

    /// Rows of up to three variables in a small box, as the checker gives
    /// them, and whether a point of the box satisfies them: every point is
    /// tried.
    pub(super) fn boxed(rng: &mut Rng) -> (Vec<Row>, bool) {
        let variables = 1 + rng.below(3) as usize;
        let mut rows = Vec::new();
        // A box, so that every point can be tried.
        for term in 0..variables {
            rows.push(row(&[(term, 1)], 4));
            rows.push(row(&[(term, -1)], 4));
        }
        for _ in 0..1 + rng.below(5) {
            let coeffs: Vec<(TermId, i128)> = (0..variables)
                .map(|term| (term, rng.below(15) as i128 - 7))
                .collect();
            if coeffs.iter().all(|(_, coeff)| *coeff == 0) {
                continue;
            }
            let rhs = rng.below(41) as i128 - 20;
            // An equality now and then.
            if rng.below(4) == 0 {
                let opposite: Vec<(TermId, i128)> =
                    coeffs.iter().map(|(term, c)| (*term, -c)).collect();
                rows.push(row(&opposite, -rhs));
            }
            rows.push(row(&coeffs, rhs));
        }
        let mut exists = false;
        let mut point = vec![-4i128; variables];
        'points: loop {
            let model: BTreeMap<TermId, Int> = point
                .iter()
                .enumerate()
                .map(|(term, value)| (term, Int::from_i128(*value)))
                .collect();
            if rows.iter().all(|row| row.holds(&model)) {
                exists = true;
                break;
            }
            for value in point.iter_mut() {
                if *value < 4 {
                    *value += 1;
                    continue 'points;
                }
                *value = -4;
            }
            break;
        }
        // The rows as the checker gives them: with no common factor.
        (rows.iter().map(|row| row.normalize().0).collect(), exists)
    }

    #[test]
    fn rows_without_a_rational_solution_are_refuted() {
        // x ≤ 3, y ≤ 4, x + y ≥ 8.
        let rows = [
            row(&[(0, 1)], 3),
            row(&[(1, 1)], 4),
            row(&[(0, -1), (1, -1)], -8),
        ];
        assert_eq!(decided(&rows), Some(false));
        assert_eq!(decided(&rows[..2]), Some(true));
    }

    /// The precondition of review finding RC12: rational solutions, and no
    /// integer one.
    #[test]
    fn rows_with_rational_solutions_and_no_integer_one_are_refuted() {
        let rows = [
            row(&[(0, -11), (1, -13)], -27),
            row(&[(0, 11), (1, 13)], 45),
            row(&[(0, -7), (1, 9)], 10),
            row(&[(0, 7), (1, -9)], 4),
        ];
        let mut budget = 200_000;
        let Outcome::Unsat { proof, .. } = solve(&rows, &mut budget) else {
            panic!("the rows have no integer solution");
        };
        assert!(proof.splits() > 0, "only a split refutes these rows");
        assert_eq!(decided(&rows), Some(false));
    }

    /// Divisibility is decided by the equalities, without a bound on any
    /// variable: `x = 2·q` and `x = 2·r + 1`.
    #[test]
    fn an_even_number_is_not_odd() {
        let rows = [
            row(&[(0, 1), (1, -2)], 0),
            row(&[(0, -1), (1, 2)], 0),
            row(&[(0, 1), (2, -2)], 1),
            row(&[(0, -1), (2, 2)], -1),
        ];
        let mut budget = 200_000;
        let Outcome::Unsat { proof, .. } = solve(&rows, &mut budget) else {
            panic!("no integer is even and odd");
        };
        assert!(proof.rounds());
        assert_eq!(proof.splits(), 0);
        assert_eq!(decided(&rows), Some(false));
    }

    /// The count of steps ends a search, and that is the third answer.
    /// The rows of a candidate of the data kernel of slice 2, as parts 1
    /// and 3 leave them: quotients and remainders by 1,000,000, and a sum
    /// that is asked to pass the greatest `u64`. The rational solution is
    /// not whole, the branch that the first split prefers is refuted at
    /// once, and the model lies in the other. Part 4 made 10,149 rows of
    /// these 25 before that branch was entered.
    #[test]
    fn a_model_behind_a_refuted_branch_is_found_in_the_first_tableau() {
        let rows = [
            row(&[(37, -4), (54, 1000000), (76, 1)], 1),
            row(&[(37, -4), (56, 1000000), (79, 1)], 3),
            row(&[(37, 4), (54, -1000000), (76, -1)], 4998),
            row(&[(37, 4), (56, -1000000), (79, -1)], 18446744073709551612),
            row(
                &[
                    (54, -7000000),
                    (56, 7000000),
                    (74, 1000000),
                    (76, -7),
                    (79, 7),
                ],
                25,
            ),
            row(
                &[
                    (54, -7000000),
                    (56, 7000000),
                    (74, 1000000),
                    (76, -6),
                    (79, 7),
                ],
                24,
            ),
            row(
                &[
                    (54, -3000000),
                    (56, 2000000),
                    (68, 1000000),
                    (76, -3),
                    (79, 2),
                ],
                3,
            ),
            row(&[(54, -3000000), (56, 2000000), (76, -3), (79, 2)], 2),
            row(
                &[
                    (54, -1000000),
                    (56, -1000000),
                    (76, -1),
                    (77, 1000000),
                    (79, -1),
                ],
                -4,
            ),
            row(&[(54, -1000000), (56, -1000000), (76, -1), (79, -1)], -5),
            row(
                &[
                    (54, -1000000),
                    (56, 1000000),
                    (65, 1000000),
                    (76, -1),
                    (79, 1),
                ],
                7,
            ),
            row(&[(54, -1000000), (56, 1000000), (76, -1), (79, 1)], 2),
            row(&[(54, -1000000), (56, 2000000), (76, -1), (79, 2)], 5),
            row(
                &[
                    (54, 1000000),
                    (56, -1000000),
                    (65, -1000000),
                    (76, 1),
                    (79, -1),
                ],
                999992,
            ),
            row(&[(54, 1000000), (56, -1000000), (76, 1), (79, -1)], 999997),
            row(
                &[
                    (54, 1000000),
                    (56, 1000000),
                    (76, 1),
                    (77, -1000000),
                    (79, 1),
                ],
                1000003,
            ),
            row(
                &[
                    (54, 3000000),
                    (56, -2000000),
                    (68, -1000000),
                    (76, 3),
                    (79, -2),
                ],
                999996,
            ),
            row(
                &[
                    (54, 7000000),
                    (56, -7000000),
                    (74, -1000000),
                    (76, 7),
                    (79, -7),
                ],
                999974,
            ),
            row(&[(56, -1000000), (71, 200000), (79, -1)], -2),
            row(&[(56, -1000000), (79, -1)], -3),
            row(&[(56, 1000000), (71, -200000), (79, 1)], 200001),
            row(&[(56, 1000000), (79, 1)], 1000002),
            row(&[(76, -1)], 1000000006),
            row(&[(76, -1), (79, -1)], -18446744072709551610),
            row(&[(79, -1)], -1),
        ];
        let before = counts::now();
        let mut budget = 100_000;
        let Outcome::Sat(model) = solve(&rows, &mut budget) else {
            panic!("the rows have a model");
        };
        assert!(rows.iter().all(|row| row.holds(&model)));
        let done = counts::now().since(&before);
        assert_eq!(done.tableaus, 1, "{done}");
        assert!(done.entries <= 5_000, "{done}");
    }

    /// Without a turn the search enters the other branch only where the
    /// preferred one is refuted, so it follows one path: its splits are at
    /// most as many as may nest, whatever the rows are.
    #[test]
    fn a_search_without_a_turn_follows_one_path() {
        // `3·x - 3·y = 1` with bounds: no integer solution, and every split
        // leaves a rational one until the bounds close in.
        let rows = [
            row(&[(0, 3), (1, -3)], 2),
            row(&[(0, -3), (1, 3)], -1),
            row(&[(0, 1)], 40),
            row(&[(0, -1)], 0),
            row(&[(1, 1)], 40),
            row(&[(1, -1)], 0),
        ];
        let active: Vec<(Row, usize)> = rows.iter().cloned().zip(0..).collect();
        let mut simplex = Simplex::new(&active);
        let before = counts::now();
        let mut budget = 100_000;
        let found = simplex.search(rows.len(), SPLIT_DEPTH, 0, &mut budget);
        assert!(matches!(found, Ok(Found::Open | Found::Refuted(_))));
        let done = counts::now().since(&before);
        assert!(done.splits <= SPLIT_DEPTH as u64, "{done}");
        // The answer of the whole method is a proof.
        assert_eq!(decided(&rows), Some(false));
    }

    #[test]
    fn the_count_of_steps_ends_a_search() {
        let rows = [
            row(&[(0, -11), (1, -13)], -27),
            row(&[(0, 11), (1, 13)], 45),
            row(&[(0, -7), (1, 9)], 10),
            row(&[(0, 7), (1, -9)], 4),
        ];
        let mut budget = 3;
        assert!(matches!(solve(&rows, &mut budget), Outcome::Limit));
        assert_eq!(budget, 0);
        // Rational solutions without a bound, and no integer one, where no
        // equality is stated: `1 ≤ 2·x - 2·y + z ≤ 1` with `0 ≤ z ≤ 0` given
        // through a fourth variable. Splitting alone would not end here; the
        // equalities, found one after another, decide it.
        let rows = [
            row(&[(0, 2), (1, -2), (2, 1)], 1),
            row(&[(0, -2), (1, 2), (2, -1)], -1),
            row(&[(2, 1), (3, 2)], 0),
            row(&[(2, -1), (3, -2)], 0),
            row(&[(3, 1)], 0),
            row(&[(3, -1)], 0),
        ];
        assert_eq!(decided(&rows), Some(false));
    }

    /// Against a search of every point of a small box: the answer is the
    /// same, every model holds, and the kernel validates every proof.
    #[test]
    fn the_answer_is_that_of_a_search_of_every_point() {
        let mut rng = Rng::new(0x6c6961);
        let mut refuted = 0;
        let mut with_split = 0;
        for _ in 0..3_000 {
            let (rows, exists) = boxed(&mut rng);
            assert_eq!(decided(&rows), Some(exists), "{rows:?}");
            if !exists {
                refuted += 1;
                let mut budget = 200_000;
                if let Outcome::Unsat { proof, .. } = solve(&rows, &mut budget)
                    && proof.splits() > 0
                {
                    with_split += 1;
                }
            }
        }
        assert!(refuted > 300, "{refuted} sets of rows were refuted");
        assert!(with_split > 10, "{with_split} proofs have a split");
    }
}
