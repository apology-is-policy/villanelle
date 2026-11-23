//! Rational numbers, for the simplex method of the theory check
//! (`docs/v2/facts.md`, section 7, step 5).
//!
//! Only the search uses them. A proof holds integers alone ([V3]), so the
//! kernel needs none.
//!
//! A value is kept in lowest terms with a positive denominator. Numerator and
//! denominator are machine integers while they fit, and mathematical integers
//! ([`crate::int::Int`]) when they do not; the smaller form is always used
//! when it can be, so that equal values have equal representations.

use crate::int::Int;
use std::cmp::Ordering;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Repr {
    Small(i128, i128),
    Big(Int, Int),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Rat(Repr);

pub fn gcd_u128(mut a: u128, mut b: u128) -> u128 {
    // Division of 128-bit values is done in software and is slow, so the
    // remainders are taken in 64 bits as soon as both values fit.
    loop {
        if let (Ok(small_a), Ok(small_b)) = (u64::try_from(a), u64::try_from(b)) {
            let (mut x, mut y) = (small_a, small_b);
            while y != 0 {
                let r = x % y;
                x = y;
                y = r;
            }
            return u128::from(x);
        }
        if b == 0 {
            return a;
        }
        let r = a % b;
        a = b;
        b = r;
    }
}

fn gcd_int(a: &Int, b: &Int) -> Int {
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
        let (_, r) = x.divide(&y).expect("the divisor is not zero");
        x = y;
        y = r;
    }
    x
}

fn small(n: i128, d: i128) -> Option<Rat> {
    if d == 0 {
        return None;
    }
    if n == 0 {
        return Some(Rat(Repr::Small(0, 1)));
    }
    if d == 1 {
        return Some(Rat(Repr::Small(n, 1)));
    }
    let g = gcd_u128(n.unsigned_abs(), d.unsigned_abs());
    let g = i128::try_from(g).ok()?;
    let (n, d) = (n.checked_div(g)?, d.checked_div(g)?);
    if d < 0 {
        Some(Rat(Repr::Small(n.checked_neg()?, d.checked_neg()?)))
    } else {
        Some(Rat(Repr::Small(n, d)))
    }
}

fn big(n: Int, d: Int) -> Rat {
    debug_assert!(!d.is_zero());
    if n.is_zero() {
        return Rat(Repr::Small(0, 1));
    }
    let g = gcd_int(&n, &d);
    let (mut n, mut d) = (
        n.divide(&g).expect("the divisor is not zero").0,
        d.divide(&g).expect("the divisor is not zero").0,
    );
    if d.is_negative() {
        n = n.negate();
        d = d.negate();
    }
    match (n.to_i128(), d.to_i128()) {
        (Some(small_n), Some(small_d)) => Rat(Repr::Small(small_n, small_d)),
        _ => Rat(Repr::Big(n, d)),
    }
}

impl Rat {
    pub fn zero() -> Rat {
        Rat(Repr::Small(0, 1))
    }

    pub fn one() -> Rat {
        Rat(Repr::Small(1, 1))
    }

    /// `n / d`, for a `d` that is not zero.
    pub fn ratio(n: i128, d: i128) -> Rat {
        small(n, d).unwrap_or_else(|| big(Int::from_i128(n), Int::from_i128(d)))
    }

    pub fn from_int(value: &Int) -> Rat {
        match value.to_i128() {
            Some(n) => Rat(Repr::Small(n, 1)),
            None => Rat(Repr::Big(value.clone(), Int::from_u64(1))),
        }
    }

    /// The numerator and the denominator, the denominator positive.
    pub fn parts(&self) -> (Int, Int) {
        match &self.0 {
            Repr::Small(n, d) => (Int::from_i128(*n), Int::from_i128(*d)),
            Repr::Big(n, d) => (n.clone(), d.clone()),
        }
    }

    pub fn is_zero(&self) -> bool {
        matches!(self.0, Repr::Small(0, _))
    }

    pub fn is_negative(&self) -> bool {
        match &self.0 {
            Repr::Small(n, _) => *n < 0,
            Repr::Big(n, _) => n.is_negative(),
        }
    }

    pub fn is_positive(&self) -> bool {
        !self.is_zero() && !self.is_negative()
    }

    pub fn is_integer(&self) -> bool {
        match &self.0 {
            Repr::Small(_, d) => *d == 1,
            Repr::Big(_, d) => *d == Int::from_u64(1),
        }
    }

    /// The value, if it is an integer.
    pub fn to_int(&self) -> Option<Int> {
        self.is_integer().then(|| self.parts().0)
    }

    /// The greatest integer that is not above the value.
    pub fn floor(&self) -> Int {
        let (n, d) = self.parts();
        let (q, r) = n.divide(&d).expect("the denominator is not zero");
        if n.is_negative() && !r.is_zero() {
            q.minus(&Int::from_u64(1))
        } else {
            q
        }
    }

    pub fn negate(&self) -> Rat {
        match &self.0 {
            Repr::Small(n, d) => match n.checked_neg() {
                Some(negated) => Rat(Repr::Small(negated, *d)),
                None => big(Int::from_i128(*n).negate(), Int::from_i128(*d)),
            },
            Repr::Big(n, d) => big(n.negate(), d.clone()),
        }
    }

    pub fn plus(&self, other: &Rat) -> Rat {
        if let (Repr::Small(n1, 1), Repr::Small(n2, 1)) = (&self.0, &other.0)
            && let Some(sum) = n1.checked_add(*n2)
        {
            return Rat(Repr::Small(sum, 1));
        }
        if let (Repr::Small(n1, d1), Repr::Small(n2, d2)) = (&self.0, &other.0)
            && let Some(sum) = (|| {
                let n = n1.checked_mul(*d2)?.checked_add(n2.checked_mul(*d1)?)?;
                small(n, d1.checked_mul(*d2)?)
            })()
        {
            return sum;
        }
        let (n1, d1) = self.parts();
        let (n2, d2) = other.parts();
        big(n1.times(&d2).plus(&n2.times(&d1)), d1.times(&d2))
    }

    pub fn minus(&self, other: &Rat) -> Rat {
        self.plus(&other.negate())
    }

    pub fn times(&self, other: &Rat) -> Rat {
        if let (Repr::Small(n1, 1), Repr::Small(n2, 1)) = (&self.0, &other.0)
            && let Some(product) = n1.checked_mul(*n2)
        {
            return Rat(Repr::Small(product, 1));
        }
        if let (Repr::Small(n1, d1), Repr::Small(n2, d2)) = (&self.0, &other.0)
            && let Some(product) = (|| small(n1.checked_mul(*n2)?, d1.checked_mul(*d2)?))()
        {
            return product;
        }
        let (n1, d1) = self.parts();
        let (n2, d2) = other.parts();
        big(n1.times(&n2), d1.times(&d2))
    }

    /// `self / other`. `None` for a zero divisor.
    pub fn over(&self, other: &Rat) -> Option<Rat> {
        if other.is_zero() {
            return None;
        }
        if let (Repr::Small(n1, d1), Repr::Small(n2, d2)) = (&self.0, &other.0)
            && let Some(quotient) = (|| small(n1.checked_mul(*d2)?, d1.checked_mul(*n2)?))()
        {
            return Some(quotient);
        }
        let (n1, d1) = self.parts();
        let (n2, d2) = other.parts();
        Some(big(n1.times(&d2), d1.times(&n2)))
    }
}

impl Ord for Rat {
    fn cmp(&self, other: &Rat) -> Ordering {
        if let (Repr::Small(n1, 1), Repr::Small(n2, 1)) = (&self.0, &other.0) {
            return n1.cmp(n2);
        }
        if let (Repr::Small(n1, d1), Repr::Small(n2, d2)) = (&self.0, &other.0)
            && let (Some(left), Some(right)) = (n1.checked_mul(*d2), n2.checked_mul(*d1))
        {
            return left.cmp(&right);
        }
        let (n1, d1) = self.parts();
        let (n2, d2) = other.parts();
        n1.times(&d2).cmp(&n2.times(&d1))
    }
}

impl PartialOrd for Rat {
    fn partial_cmp(&self, other: &Rat) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// The least common multiple of two positive integers.
pub fn lcm(a: &Int, b: &Int) -> Int {
    let g = gcd_int(a, b);
    a.divide(&g).expect("the divisor is not zero").0.times(b)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rat(n: i128, d: i128) -> Rat {
        Rat::from_int(&Int::from_i128(n))
            .over(&Rat::from_int(&Int::from_i128(d)))
            .expect("the divisor is not zero")
    }

    #[test]
    fn arithmetic_agrees_with_fractions_in_lowest_terms() {
        assert_eq!(rat(1, 2).plus(&rat(1, 3)), rat(5, 6));
        assert_eq!(rat(1, 2).minus(&rat(1, 2)), Rat::zero());
        assert_eq!(rat(2, 4), rat(1, 2));
        assert_eq!(rat(1, -2), rat(-1, 2));
        assert_eq!(rat(-3, 4).times(&rat(8, 9)), rat(-2, 3));
        assert_eq!(rat(3, 4).over(&rat(-9, 8)), Some(rat(-2, 3)));
        assert_eq!(rat(3, 4).over(&Rat::zero()), None);
        assert!(rat(-1, 2) < rat(-1, 3));
        assert!(rat(7, 3) > rat(2, 1));
        assert_eq!(rat(7, 2).floor(), Int::from_i128(3));
        assert_eq!(rat(-7, 2).floor(), Int::from_i128(-4));
        assert_eq!(rat(-8, 2).floor(), Int::from_i128(-4));
        assert_eq!(rat(6, 3).to_int(), Some(Int::from_i128(2)));
        assert_eq!(rat(5, 3).to_int(), None);
        assert!(rat(-1, 7).is_negative() && rat(1, 7).is_positive());
    }

    /// Beyond the machine integers the value is still exact, and it comes
    /// back to the small form when it fits again.
    #[test]
    fn large_values_stay_exact() {
        let huge = Rat::from_int(&Int::power_of_two(126));
        let square = huge.times(&huge);
        assert_eq!(square.parts().0, Int::power_of_two(252));
        assert_eq!(square.over(&huge), Some(huge.clone()));
        assert_eq!(
            square.over(&huge).map(|value| value.0),
            Some(Repr::Small(1 << 126, 1))
        );
        let third = rat(1, 3);
        let sum = square.plus(&third).minus(&square);
        assert_eq!(sum, third);
        assert!(square > huge && square.negate() < huge.negate());
        assert_eq!(
            lcm(&Int::from_i128(4), &Int::from_i128(6)),
            Int::from_i128(12)
        );
    }
}
