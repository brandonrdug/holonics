//! **The release** (N5): the only narrowing. It moves a value's grain up by `k` places, names its rounding
//! rule (each a different Euclidean descent) and returns the remainder at the released places, so the
//! released value and its remainder recompose the class (`value · 2^k + remainder = x`). Dropping the
//! remainder is a second, declared step: the merge.

use super::value::{Digits, Section, Value};
use super::{refuse, Grain, Result, Width};

/// How a release's tie is broken under [`Rounding::Nearest`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Tie {
    /// Half away from zero.
    Away,
    /// Half to the even quotient.
    Even,
    /// Half up (toward the larger quotient): the field's present `release`.
    Up,
}

/// A release's rounding rule.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Rounding {
    Floor,
    Nearest(Tie),
    Ceiling,
}

/// **A released value**: the value at its coarser grain, the remainder at the released places (at the value's
/// old grain, on the open ray, signed where the rule rounded up), and the rule that chose them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Released {
    pub value: Value,
    pub remainder: Value,
    pub rule: Rounding,
}

/// **Release `k` places** of a value by a rounding rule: `x = q · 2^k + r`, `q` the released value at grain
/// `lo + k`, `r` the remainder at grain `lo`. The released value's width is the need of `q`, never a picked one.
pub fn release(x: &Value, k: u32, rule: Rounding) -> Result<Released> {
    if k == 0 {
        return Ok(Released { value: x.clone(), remainder: Value::zero(x.grain), rule });
    }
    let lo = x.grain.lo().checked_add(k as i32).ok_or(super::NumberError::Refused("a release's grain past its count"))?;
    let (mut q, mut r) = x.digits.floor_split(k);
    // r ∈ [0, 2^k): decide whether to round up by the rule.
    let half = Digits::Small(1).shl(k - 1);
    let up = match rule {
        Rounding::Floor => false,
        Rounding::Ceiling => !r.is_zero(),
        Rounding::Nearest(tie) => match r.cmp(&half) {
            std::cmp::Ordering::Greater => true,
            std::cmp::Ordering::Less => false,
            std::cmp::Ordering::Equal => match tie {
                Tie::Up => true,
                // Away from zero: up where the class is nonnegative.
                Tie::Away => !x.digits.negative(),
                Tie::Even => {
                    let (_, parity) = q.floor_split(1);
                    !parity.is_zero()
                }
            },
        },
    };
    if up {
        q = q.add(&Digits::Small(1));
        r = r.sub(&Digits::Small(1).shl(k));
    }
    let section = if x.section == Section::Low && !q.negative() { Section::Low } else { Section::TwosComplement };
    let qw = q.places_in(section).max(1);
    let value = Value::of(Grain::new(lo), Width::new(qw), section, q)?;
    let rsection = if r.negative() { Section::TwosComplement } else { Section::Low };
    let rw = r.places_in(rsection).max(1);
    let remainder = Value::of(x.grain, Width::new(rw), rsection, r)?;
    if remainder.used().places() > k + 1 {
        return refuse("a release's remainder outside its released places");
    }
    Ok(Released { value, remainder, rule })
}
