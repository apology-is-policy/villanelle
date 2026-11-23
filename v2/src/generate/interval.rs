//! Intervals of mathematical integers, with the bounds that the fact logic
//! gives to the operators it interprets in part (`docs/v2/facts.md`, [A7] to
//! [A9]).
//!
//! The generator of valid programs reasons with these and with nothing
//! stronger. Whatever it concludes, the fact logic entails, so a checker that
//! is exact ([J5]) accepts every program the generator calls valid.

/// An end at or beyond this is absent: the interval has no bound there.
pub const POS: i128 = 1 << 100;
pub const NEG: i128 = -POS;

/// A closed interval. `lo ≤ NEG` and `hi ≥ POS` mean that the end is absent.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Range {
    pub lo: i128,
    pub hi: i128,
}

fn clamp(value: i128) -> i128 {
    value.clamp(NEG, POS)
}

impl Range {
    pub const ALL: Range = Range { lo: NEG, hi: POS };

    pub fn new(lo: i128, hi: i128) -> Range {
        Range {
            lo: clamp(lo),
            hi: clamp(hi),
        }
    }

    pub fn point(value: i128) -> Range {
        Range::new(value, value)
    }

    pub fn is_empty(self) -> bool {
        self.lo > self.hi
    }

    pub fn has_lo(self) -> bool {
        self.lo > NEG
    }

    pub fn has_hi(self) -> bool {
        self.hi < POS
    }

    pub fn bounded(self) -> bool {
        self.has_lo() && self.has_hi()
    }

    /// Whether every value of this interval is a value of `outer`. An empty
    /// interval is within nothing: it stands for a mistake of the caller.
    pub fn within(self, outer: Range) -> bool {
        !self.is_empty() && outer.lo <= self.lo && self.hi <= outer.hi
    }

    pub fn hull(self, other: Range) -> Range {
        Range {
            lo: self.lo.min(other.lo),
            hi: self.hi.max(other.hi),
        }
    }

    pub fn meet(self, other: Range) -> Range {
        Range {
            lo: self.lo.max(other.lo),
            hi: self.hi.min(other.hi),
        }
    }

    pub fn as_point(self) -> Option<i128> {
        (self.lo == self.hi && self.bounded()).then_some(self.lo)
    }

    /// The number of values, or `None` when an end is absent.
    pub fn width(self) -> Option<i128> {
        (self.bounded() && !self.is_empty()).then(|| self.hi - self.lo + 1)
    }
}

/// `x + 1`, with an absent end staying absent.
pub fn above(value: i128) -> i128 {
    if value >= POS || value <= NEG {
        value
    } else {
        value + 1
    }
}

/// `x - 1`, with an absent end staying absent.
pub fn below(value: i128) -> i128 {
    if value >= POS || value <= NEG {
        value
    } else {
        value - 1
    }
}

pub fn add(a: Range, b: Range) -> Range {
    let lo = if !a.has_lo() || !b.has_lo() {
        NEG
    } else {
        clamp(a.lo + b.lo)
    };
    let hi = if !a.has_hi() || !b.has_hi() {
        POS
    } else {
        clamp(a.hi + b.hi)
    };
    Range { lo, hi }
}

pub fn negate(a: Range) -> Range {
    Range {
        lo: clamp(-a.hi),
        hi: clamp(-a.lo),
    }
}

pub fn subtract(a: Range, b: Range) -> Range {
    add(a, negate(b))
}

fn end_times(x: i128, y: i128) -> i128 {
    if x == 0 || y == 0 {
        return 0;
    }
    let negative = (x < 0) != (y < 0);
    let absent = x <= NEG || x >= POS || y <= NEG || y >= POS;
    let limit = if negative { NEG } else { POS };
    if absent {
        return limit;
    }
    x.checked_mul(y).map_or(limit, clamp)
}

/// The least and the greatest of the four products of the ends.
pub fn multiply(a: Range, b: Range) -> Range {
    let corners = [
        end_times(a.lo, b.lo),
        end_times(a.lo, b.hi),
        end_times(a.hi, b.lo),
        end_times(a.hi, b.hi),
    ];
    Range {
        lo: corners.iter().copied().min().unwrap_or(NEG),
        hi: corners.iter().copied().max().unwrap_or(POS),
    }
}

pub fn scale(a: Range, factor: i128) -> Range {
    multiply(a, Range::point(factor))
}

fn end_over(x: i128, divisor: i128) -> i128 {
    if x <= NEG {
        if divisor > 0 { NEG } else { POS }
    } else if x >= POS {
        if divisor > 0 { POS } else { NEG }
    } else {
        x / divisor
    }
}

/// `t ÷ k` for a nonzero literal `k`, truncating toward zero ([A7]). The
/// quotient is monotone in `t`, so the ends give the ends.
pub fn divide_by_literal(a: Range, divisor: i128) -> Range {
    let p = end_over(a.lo, divisor);
    let q = end_over(a.hi, divisor);
    Range {
        lo: p.min(q),
        hi: p.max(q),
    }
}

/// `t mod k` for a nonzero literal `k`, with the sign of the dividend ([A7]).
/// Where every `t` has one quotient, the remainder is `t` shifted.
pub fn remainder_by_literal(a: Range, divisor: i128) -> Range {
    let modulus = divisor.abs();
    let top = modulus - 1;
    if a.lo >= 0 {
        if a.has_hi() && a.lo / modulus == a.hi / modulus {
            Range::new(a.lo % modulus, a.hi % modulus)
        } else {
            Range::new(0, top.min(a.hi))
        }
    } else if a.hi <= 0 {
        if a.has_lo() && a.lo / modulus == a.hi / modulus {
            Range::new(a.lo % modulus, a.hi % modulus)
        } else {
            Range::new((-top).max(a.lo), 0)
        }
    } else {
        Range::new((-top).max(a.lo), top.min(a.hi))
    }
}

/// The declared interval of `t mod k` for a nonzero literal `k` ([A9]): the
/// remainders that the sign of the dividend's declared interval allows, and
/// nothing finer. [`remainder_by_literal`] is what the facts give.
pub fn remainder_declared(a: Range, divisor: i128) -> Range {
    let top = divisor.abs() - 1;
    Range::new(
        if a.has_lo() && a.lo >= 0 { 0 } else { -top },
        if a.has_hi() && a.hi <= 0 { 0 } else { top },
    )
}

/// `div(s, t)` for a divisor that is not a literal ([A8]). `None` when the
/// divisor is not known to be nonzero.
pub fn divide_by_term(s: Range, t: Range) -> Option<Range> {
    if t.lo >= 1 {
        Some(Range::new(
            if s.lo >= 0 { 0 } else { s.lo },
            if s.hi <= 0 { 0 } else { s.hi },
        ))
    } else if t.hi <= -1 {
        Some(Range::new(
            if s.hi <= 0 { 0 } else { clamp(-s.hi) },
            if s.lo >= 0 { 0 } else { clamp(-s.lo) },
        ))
    } else {
        None
    }
}

/// `rem(s, t)` for a divisor that is not a literal ([A8]).
pub fn remainder_by_term(s: Range, t: Range) -> Option<Range> {
    let (cap, bounded_by_dividend) = if t.lo >= 1 {
        (below(t.hi), true)
    } else if t.hi <= -1 {
        (below(clamp(-t.lo)), false)
    } else {
        return None;
    };
    let mut out: Option<Range> = None;
    let mut join = |part: Range| {
        out = Some(match out {
            Some(seen) => seen.hull(part),
            None => part,
        });
    };
    if s.hi >= 0 {
        let top = if bounded_by_dividend {
            cap.min(s.hi)
        } else {
            cap
        };
        join(Range::new(0, top));
    }
    if s.lo <= 0 {
        let bottom = if bounded_by_dividend {
            clamp(-cap).max(s.lo)
        } else {
            clamp(-cap)
        };
        join(Range::new(bottom, 0));
    }
    out
}

/// What the instances of [A9] give for `w = mul(s, t)`: the planes that the
/// declared intervals of the operands allow, each taken over the intervals
/// that the facts give.
pub fn product_by_planes(s: Range, s_declared: Range, t: Range, t_declared: Range) -> Range {
    let plane = |on_t: i128, on_s: i128, constant: i128| {
        add(add(scale(t, on_t), scale(s, on_s)), Range::point(-constant))
    };
    let (a, big_a) = (s_declared.lo, s_declared.hi);
    let (b, big_b) = (t_declared.lo, t_declared.hi);
    let mut lo = NEG;
    let mut hi = POS;
    if s_declared.has_lo() && t_declared.has_lo() {
        lo = lo.max(plane(a, b, end_times(a, b)).lo);
    }
    if s_declared.has_hi() && t_declared.has_hi() {
        lo = lo.max(plane(big_a, big_b, end_times(big_a, big_b)).lo);
    }
    if s_declared.has_hi() && t_declared.has_lo() {
        hi = hi.min(plane(big_a, b, end_times(big_a, b)).hi);
    }
    if s_declared.has_lo() && t_declared.has_hi() {
        hi = hi.min(plane(a, big_b, end_times(a, big_b)).hi);
    }
    Range { lo, hi }
}

#[cfg(test)]
mod tests {
    use super::*;

    impl Range {
        fn contains(self, value: i128) -> bool {
            self.lo <= value && value <= self.hi
        }
    }

    /// Every bound is checked against the arithmetic it speaks about, on
    /// every pair of values of small intervals.
    #[test]
    fn bounds_hold_for_every_pair_of_values() {
        let ends = [-9, -4, -1, 0, 1, 3, 8];
        for &lo_s in &ends {
            for &hi_s in ends.iter().filter(|&&hi| hi >= lo_s) {
                let s = Range::new(lo_s, hi_s);
                for divisor in [-7, -2, -1, 1, 2, 3, 8] {
                    let quotient = divide_by_literal(s, divisor);
                    let remainder = remainder_by_literal(s, divisor);
                    for x in lo_s..=hi_s {
                        assert!(quotient.contains(x / divisor), "{x} ÷ {divisor}");
                        assert!(remainder.contains(x % divisor), "{x} mod {divisor}");
                    }
                }
                for &lo_t in &ends {
                    for &hi_t in ends.iter().filter(|&&hi| hi >= lo_t) {
                        let t = Range::new(lo_t, hi_t);
                        let product = product_by_planes(s, s, t, t);
                        let wide =
                            product_by_planes(s, Range::new(-20, 20), t, Range::new(-20, 20));
                        let quotient = divide_by_term(s, t);
                        let remainder = remainder_by_term(s, t);
                        assert_eq!(quotient.is_some(), lo_t >= 1 || hi_t <= -1);
                        for x in lo_s..=hi_s {
                            for y in lo_t..=hi_t {
                                assert!(product.contains(x * y), "{x} * {y} in {product:?}");
                                assert!(wide.contains(x * y), "{x} * {y} in {wide:?}");
                                assert!(multiply(s, t).contains(x * y));
                                assert!(add(s, t).contains(x + y));
                                assert!(subtract(s, t).contains(x - y));
                                if let Some(quotient) = quotient {
                                    assert!(quotient.contains(x / y), "{x} ÷ {y}");
                                }
                                if let Some(remainder) = remainder {
                                    assert!(remainder.contains(x % y), "{x} mod {y}");
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn absent_ends_stay_absent() {
        let from_zero = Range::new(0, POS);
        assert_eq!(add(from_zero, Range::point(5)), Range::new(5, POS));
        assert_eq!(negate(from_zero), Range::new(NEG, 0));
        assert_eq!(scale(from_zero, -2), Range::new(NEG, 0));
        assert_eq!(divide_by_literal(from_zero, 4), Range::new(0, POS));
        assert_eq!(remainder_by_literal(from_zero, 8), Range::new(0, 7));
        assert_eq!(remainder_by_literal(Range::ALL, 8), Range::new(-7, 7));
        // An operand whose declared interval has no upper end ([A9]: a
        // `usize`) leaves two planes: the product is not negative, and it is
        // at most the other operand's bound times what the facts give.
        let small = Range::new(0, 3);
        let known = Range::new(0, 10);
        assert_eq!(
            product_by_planes(known, from_zero, small, small),
            Range::new(0, 30)
        );
        assert_eq!(
            product_by_planes(from_zero, from_zero, small, small),
            Range::new(0, POS)
        );
        let unbounded = product_by_planes(from_zero, from_zero, from_zero, from_zero);
        assert_eq!(unbounded, Range::new(0, POS));
    }
}
