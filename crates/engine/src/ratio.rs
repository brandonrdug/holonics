//! The engine's ratio (C5 of #603: cut from `field.rs` by object, each item's text as it stood but for its visibility).

#[allow(unused_imports)]
use crate::field::*;
#[allow(unused_imports)]
use crate::inherited::tower::{affine, covector, deposit_step, div_nearest, exp_series, face_code, fewer_bits_weighed, fit32, fit64, half_turn, on_step_grain, outer_sum, ratio_adjoint, ratio_to_power, reach, refuse, release, toward, transposed, weighed_code, Result, TowerError, TowerFace, FACE_BITS, FIRST_RATE, MATERIAL_BITS, MOVE_BITS, SECOND_RATE};
#[allow(unused_imports)]
use crate::inherited::keyed_modes::{ln2_face, log2_face, Exponential};
#[allow(unused_imports)]
use rayon::prelude::*;

/// [definition; agent-inferred, November 1] **A contact row as a series** (the dispersing field's
/// §14.11; one row a head, §15.2): each term `2^z · μ` (its face and whole bits from [`Field::face`], `μ`
/// its multiplier on `2^(−62)`: `2^62` in the near field, a far source's weight, a crowd's count `· 2^62`
/// in the mass with `2^62` against its value sum) keeps its own exponent; the terms are summed whole,
/// shifted from the row's least exponent, in a carrier as wide as the row's own exponents need (never
/// past [`FieldDeclaration::row_bits`]); the current `ỹ = Σ e v / Σ e` is released once, to the nearest
/// numerator on the value's grain; and each term's share of the mass is formed once on `2^(−63)`. No
/// peak is subtracted and no term is released before the current: a source outscored by any number of
/// bits still enters the sums. Integer sums, so any order gives the same bits.
pub struct SeriesRow {
    pub(crate) span: usize,
    pub(crate) terms: Vec<(i64, u128, u128, u128, Vec<i128>)>,
}

impl SeriesRow {
    pub fn new(span: usize) -> Self {
        Self { span, terms: Vec::new() }
    }

    /// A term: its score's `(a, face)`, its mass multiplier, its value multiplier and its values.
    pub fn push(&mut self, (a, face): (i64, u128), mass: u128, value_mult: u128, value: &[i128]) {
        self.terms.push((a, face, mass, value_mult, value.to_vec()));
    }

    /// The released current (each value entry `div_nearest(Σ 2^(a − a₀) face μ_v v, Σ 2^(a − a₀) face
    /// μ)`) and each term's share `div_nearest(2^(a − a₀) face μ 2^63, Σ …)`.
    pub fn release(&self) -> (Vec<i128>, Vec<u64>) {
        use num_bigint::BigInt;
        // A receiver whose support holds no keyed source (§16.20) gathers nothing.
        if self.terms.is_empty() {
            return (vec![0; self.span], Vec::new());
        }
        let a0 = self.terms.iter().map(|t| t.0).min().unwrap_or(0);
        let mass_of = |t: &(i64, u128, u128, u128, Vec<i128>)| (BigInt::from(t.1) * BigInt::from(t.2)) << ((t.0 - a0) as usize);
        let mass: BigInt = self.terms.iter().map(mass_of).sum();
        let nearest = |x: BigInt| -> BigInt {
            let half: BigInt = &mass / 2;
            let negative = x < BigInt::from(0);
            let q: BigInt = (if negative { -x } else { x } + half) / &mass;
            if negative { -q } else { q }
        };
        let current = (0..self.span)
            .map(|r| {
                let sum: BigInt = self.terms.iter().map(|t| ((BigInt::from(t.1) * BigInt::from(t.3)) << ((t.0 - a0) as usize)) * BigInt::from(t.4[r])).sum();
                i128::try_from(nearest(sum)).unwrap_or(0)
            })
            .collect();
        let shares = self.terms.iter().map(|t| u64::try_from(nearest(mass_of(t) << SHARE_BITS as usize)).unwrap_or(u64::MAX)).collect();
        (current, shares)
    }
}

/// [definition; agent-inferred, November 1] **The definite words' and values' prefix sums** over a
/// region, one head (§14.10): `words[t]`, `values[t]` the sums of the definite sites' framed unit words
/// and framed values before place `t` (the span's entries), `counts[t]` their number, so a crowd's sums
/// are two reads.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Sums {
    pub words: Vec<i128>,
    pub values: Vec<i128>,
    pub counts: Vec<u64>,
    pub span: usize,
}

impl Sums {
    pub fn of(words: &[i64], values: &[i64], definite: &[bool], span: usize) -> Self {
        let sites = definite.len();
        let (mut w, mut v, mut c) = (vec![0i128; (sites + 1) * span], vec![0i128; (sites + 1) * span], vec![0u64; sites + 1]);
        for t in 0..sites {
            for r in 0..span {
                let on = i128::from(definite[t]);
                w[(t + 1) * span + r] = w[t * span + r] + on * words[t * span + r] as i128;
                v[(t + 1) * span + r] = v[t * span + r] + on * values[t * span + r] as i128;
            }
            c[t + 1] = c[t] + u64::from(definite[t]);
        }
        Self { words: w, values: v, counts: c, span }
    }

    pub(crate) fn count(&self, lo: usize, hi: usize) -> u64 {
        self.counts[hi + 1] - self.counts[lo]
    }

    pub(crate) fn words(&self, lo: usize, hi: usize) -> Vec<i128> {
        (0..self.span).map(|r| self.words[(hi + 1) * self.span + r] - self.words[lo * self.span + r]).collect()
    }

    pub(crate) fn value(&self, lo: usize, hi: usize, r: usize) -> i128 {
        self.values[(hi + 1) * self.span + r] - self.values[lo * self.span + r]
    }
}

/// `⌊log₂ d⌋` for `d ≥ 1`, the falloff's octave in bits (§2.3).
pub fn octave(d: usize) -> u32 {
    usize::BITS - 1 - d.leading_zeros()
}
