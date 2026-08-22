//! **The serial reference of layer zero: an independent enclosure of the same source law on the
//! serial chart, for PARITY TESTIMONY beside the resident deed and never in its place.**
//!
//! `AGENTS.md`: *"CPU implementations remain admission audits only."* This module shares no
//! arithmetic with `resident_section` — it is `BigInt` intervals at its own grain, with the
//! transcendental and radical enclosures taken from `exact_value` on the serial chart — so where the
//! two enclosures of one value fail to intersect, one of them is wrong, and the resident deed cannot
//! have been moved by anything here: the falsifier is that poisoning this reference makes the
//! parity testimony fail while the card's read-out is bit-identical.
//!
//! It is deliberately slow and deliberately not the deed. Nothing in the production cone reaches it.

#![allow(dead_code)]

use holonic_engine::exact_value::{AlgebraicRoot, CertifiedSeries, ExactInterval};
use holonic_engine::resident_section::{Dyadic, DyadicEnclosure};
use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, Zero};
use relational_geometry::Rat;

/// One coordinate: `[lo, hi] · 2^-grain`.
pub type Iv = (BigInt, BigInt);

pub struct Serial {
    pub grain: u32,
}

fn pow2(octaves: u32) -> BigInt {
    BigInt::from(BigUint::from(1u8) << octaves as usize)
}

/// Floor division by a power of two on a `BigInt`: an arithmetic right shift is exactly that on
/// two's complement, and `num_bigint`'s `>>` on a negative value rounds toward negative infinity.
fn floor_div_pow2(v: &BigInt, octaves: u32) -> BigInt {
    let d = pow2(octaves);
    let q = v / &d;
    if (v % &d).is_zero() || !v.is_negative() {
        q
    } else {
        q - BigInt::one()
    }
}

/// `v · 2^s` floored / ceiled.
fn shift_floor(v: &BigInt, s: i64) -> BigInt {
    if s >= 0 {
        v << (s as usize)
    } else {
        floor_div_pow2(v, (-s) as u32)
    }
}
fn shift_ceil(v: &BigInt, s: i64) -> BigInt {
    if s >= 0 {
        v << (s as usize)
    } else {
        -floor_div_pow2(&-v, (-s) as u32)
    }
}

fn corners(a: &BigInt, b: &BigInt, c: &BigInt, d: &BigInt) -> (BigInt, BigInt) {
    let p = [a * c, a * d, b * c, b * d];
    let lo = p.iter().min().cloned().unwrap();
    let hi = p.iter().max().cloned().unwrap();
    (lo, hi)
}

impl Serial {
    pub fn new(grain: u32) -> Self {
        Self { grain }
    }

    fn rat_of(&self, word: &BigInt) -> Rat {
        Rat::new(word.clone(), pow2(self.grain))
    }

    fn floor_of(&self, value: &Rat) -> BigInt {
        (value * Rat::from_integer(pow2(self.grain)))
            .floor()
            .to_integer()
    }

    fn ceil_of(&self, value: &Rat) -> BigInt {
        (value * Rat::from_integer(pow2(self.grain)))
            .ceil()
            .to_integer()
    }

    /// Entering codewords times an exact dyadic, placed at the grain.
    pub fn enter(&self, words: &[u16], scale: Dyadic) -> Result<Vec<Iv>, String> {
        words
            .iter()
            .map(|word| {
                let d = Dyadic::of_bfloat16_bits(*word).map_err(|e| e.to_string())?;
                let product = BigInt::from(d.significand) * BigInt::from(scale.significand);
                let s = i64::from(self.grain) + i64::from(d.exponent) + i64::from(scale.exponent);
                Ok((shift_floor(&product, s), shift_ceil(&product, s)))
            })
            .collect()
    }

    /// `out[t, o] = Σ_i map[o, i] · x[t, i]` with the map's stored codewords decoded exactly.
    pub fn contract(
        &self,
        x: &[Iv],
        rows: usize,
        inner: usize,
        map: &[u16],
        out_width: usize,
    ) -> Result<Vec<Iv>, String> {
        let decoded: Vec<Dyadic> = map
            .iter()
            .map(|w| Dyadic::of_bfloat16_bits(*w).map_err(|e| e.to_string()))
            .collect::<Result<_, _>>()?;
        let mut out = Vec::with_capacity(rows * out_width);
        for t in 0..rows {
            for o in 0..out_width {
                // Accumulate at the finest exponent among the row's entries: exact.
                let row = &decoded[o * inner..(o + 1) * inner];
                let lowest = row.iter().map(|d| d.exponent).min().unwrap_or(0);
                let mut lo = BigInt::zero();
                let mut hi = BigInt::zero();
                for (i, w) in row.iter().enumerate() {
                    let m = BigInt::from(w.significand) << ((w.exponent - lowest) as usize);
                    let (a, b) = &x[t * inner + i];
                    if m.is_negative() {
                        lo += &m * b;
                        hi += &m * a;
                    } else {
                        lo += &m * a;
                        hi += &m * b;
                    }
                }
                out.push((
                    shift_floor(&lo, i64::from(lowest)),
                    shift_ceil(&hi, i64::from(lowest)),
                ));
            }
        }
        Ok(out)
    }

    /// The RMS rebase over runs of `group`, gain optional, `eps` exact; the reciprocal root through
    /// `AlgebraicRoot` on the serial chart.
    pub fn rms(
        &self,
        x: &[Iv],
        group: usize,
        gain: Option<&[u16]>,
        eps: Dyadic,
    ) -> Result<Vec<Iv>, String> {
        let gains: Option<Vec<Dyadic>> = match gain {
            Some(words) => Some(
                words
                    .iter()
                    .map(|w| Dyadic::of_bfloat16_bits(*w).map_err(|e| e.to_string()))
                    .collect::<Result<_, _>>()?,
            ),
            None => None,
        };
        let mut out = Vec::with_capacity(x.len());
        for chunk in x.chunks(group) {
            let mut sq_lo = BigInt::zero();
            let mut sq_hi = BigInt::zero();
            for (a, b) in chunk {
                let (aa, bb) = (a * a, b * b);
                if a.is_negative() && !b.is_negative() {
                    sq_hi += aa.max(bb);
                } else {
                    sq_lo += aa.clone().min(bb.clone());
                    sq_hi += aa.max(bb);
                }
            }
            let two_g = pow2(2 * self.grain);
            let mean_lo = Rat::new(sq_lo, &two_g * BigInt::from(group)) + eps.value();
            let mean_hi = Rat::new(sq_hi, &two_g * BigInt::from(group)) + eps.value();
            let r_hi = AlgebraicRoot::reciprocal_square_root(&mean_lo, 100)
                .map_err(|e| format!("{e:?}"))?;
            let r_lo = AlgebraicRoot::reciprocal_square_root(&mean_hi, 100)
                .map_err(|e| format!("{e:?}"))?;
            let r = ExactInterval::new(
                r_lo.enclosure().lower.clone(),
                r_hi.enclosure().upper.clone(),
            )
            .map_err(|e| format!("{e:?}"))?;
            let (rl, rh) = (self.floor_of(&r.lower), self.ceil_of(&r.upper));
            for (i, (a, b)) in chunk.iter().enumerate() {
                let (pl, ph) = corners(a, b, &rl, &rh);
                let mut yl = shift_floor(&pl, -i64::from(self.grain));
                let mut yh = shift_ceil(&ph, -i64::from(self.grain));
                if let Some(gains) = &gains {
                    let g = gains[i];
                    let m = BigInt::from(g.significand);
                    let (ql, qh) = if m.is_negative() {
                        (&yh * &m, &yl * &m)
                    } else {
                        (&yl * &m, &yh * &m)
                    };
                    yl = shift_floor(&ql, i64::from(g.exponent));
                    yh = shift_ceil(&qh, i64::from(g.exponent));
                }
                out.push((yl, yh));
            }
        }
        Ok(out)
    }

    /// The chronology, with `cos(p·θ_b)` and `sin(p·θ_b)` enclosed directly on the serial chart for
    /// every `(row, band)` — independent of the card's powering.
    pub fn chronology(
        &self,
        x: &[Iv],
        rows: usize,
        heads: usize,
        head_width: usize,
        theta: u64,
        terms: usize,
    ) -> Result<Vec<Iv>, String> {
        let bands = head_width / 2;
        let ratio =
            AlgebraicRoot::nth_root(&Rat::from_integer(BigInt::from(theta)), bands as u32, 64)
                .map_err(|e| format!("{e:?}"))?
                .enclosure()
                .reciprocal()
                .map_err(|e| format!("{e:?}"))?;
        // angle_b as an interval, then p·angle_b for each row.
        let mut angles = Vec::with_capacity(bands);
        let mut angle = ExactInterval::point(Rat::one());
        for _ in 0..bands {
            angles.push(angle.clone());
            angle = angle
                .times(&ratio)
                .map_err(|e| format!("{e:?}"))?
                .round_out(80)
                .map_err(|e| format!("{e:?}"))?;
        }
        let mut out = x.to_vec();
        for t in 0..rows {
            let p = Rat::from_integer(BigInt::from(t as u64));
            for band in 0..bands {
                let arc = ExactInterval::new(&angles[band].lower * &p, &angles[band].upper * &p)
                    .map_err(|e| format!("{e:?}"))?;
                // cos and sin over an interval: enclose by the hull of endpoint enclosures plus the
                // extremal values where the interval crosses a critical point. p·θ ≤ T, and for the
                // small T of a reference run the arc stays under π, where cos is monotone
                // decreasing; sin is monotone only under π/2, so include 1 when the arc reaches it.
                let (c_lo_s, s_lo_s) = CertifiedSeries::circular_series(&arc.lower, terms)
                    .map_err(|e| format!("{e:?}"))?;
                let (c_hi_s, s_hi_s) = CertifiedSeries::circular_series(&arc.upper, terms)
                    .map_err(|e| format!("{e:?}"))?;
                let (cl0, ch0) = (c_lo_s.enclosure().clone(), c_hi_s.enclosure().clone());
                let (sl0, sh0) = (s_lo_s.enclosure().clone(), s_hi_s.enclosure().clone());
                let mut c_lo = cl0.lower.clone().min(ch0.lower.clone());
                let c_hi = cl0.upper.clone().max(ch0.upper.clone());
                let s_lo = sl0.lower.clone().min(sh0.lower.clone());
                let mut s_hi = sl0.upper.clone().max(sh0.upper.clone());
                // Critical points inside the arc: sin peaks at π/2, cos troughs at π. The tests use
                // conservative rational brackets of each, so an arc that touches the bracket takes
                // the extremal value — widening only, never narrowing.
                let (half_pi_low, half_pi_high) = (
                    Rat::new(BigInt::from(15707), BigInt::from(10000)),
                    Rat::new(BigInt::from(15709), BigInt::from(10000)),
                );
                let (pi_low, pi_high) = (
                    Rat::new(BigInt::from(31415), BigInt::from(10000)),
                    Rat::new(BigInt::from(31417), BigInt::from(10000)),
                );
                if arc.lower <= half_pi_high && arc.upper >= half_pi_low {
                    s_hi = s_hi.max(Rat::one());
                }
                if arc.lower <= pi_high && arc.upper >= pi_low {
                    c_lo = c_lo.min(-Rat::one());
                }
                if arc.upper > Rat::from_integer(BigInt::from(4)) {
                    return Err(
                        "the serial reference encloses the chronology only up to an arc of 4"
                            .to_owned(),
                    );
                }
                let (cl, ch) = (self.floor_of(&c_lo), self.ceil_of(&c_hi));
                let (sl, sh) = (self.floor_of(&s_lo), self.ceil_of(&s_hi));
                for head in 0..heads {
                    let base = (t * heads + head) * head_width;
                    let (first, second) = (base + band, base + band + bands);
                    let (xl, xh) = x[first].clone();
                    let (yl, yh) = x[second].clone();
                    let (xc_l, xc_h) = corners(&xl, &xh, &cl, &ch);
                    let (ys_l, ys_h) = corners(&yl, &yh, &sl, &sh);
                    let (xs_l, xs_h) = corners(&xl, &xh, &sl, &sh);
                    let (yc_l, yc_h) = corners(&yl, &yh, &cl, &ch);
                    let g = -i64::from(self.grain);
                    out[first] = (
                        shift_floor(&(xc_l - ys_h), g),
                        shift_ceil(&(xc_h - ys_l), g),
                    );
                    out[second] = (
                        shift_floor(&(xs_l + yc_l), g),
                        shift_ceil(&(xs_h + yc_h), g),
                    );
                }
            }
        }
        Ok(out)
    }

    /// The contact: brackets, null, certified weights through `CertifiedSeries::exponential_enclosure`,
    /// sign-correct division, hull.
    #[allow(clippy::too_many_arguments)]
    pub fn contact(
        &self,
        q: &[Iv],
        k: &[Iv],
        v: &[Iv],
        rows: usize,
        heads: usize,
        kv_heads: usize,
        head_width: usize,
        window: usize,
        terms: usize,
    ) -> Result<Vec<Iv>, String> {
        let group = heads / kv_heads;
        let mut out = vec![(BigInt::zero(), BigInt::zero()); rows * heads * head_width];
        for t in 0..rows {
            let start = if t + 1 > window { t + 1 - window } else { 0 };
            for h in 0..heads {
                let g = h / group;
                let q_base = (t * heads + h) * head_width;
                let mut scores = Vec::new();
                for j in start..=t {
                    let k_base = (j * kv_heads + g) * head_width;
                    let mut lo = BigInt::zero();
                    let mut hi = BigInt::zero();
                    for d in 0..head_width {
                        let (l, u) = corners(
                            &q[q_base + d].0,
                            &q[q_base + d].1,
                            &k[k_base + d].0,
                            &k[k_base + d].1,
                        );
                        lo += l;
                        hi += u;
                    }
                    scores.push((
                        self.rat_of(&shift_floor(&lo, -i64::from(self.grain))),
                        self.rat_of(&shift_ceil(&hi, -i64::from(self.grain))),
                    ));
                }
                let null = scores.iter().map(|(_, h)| h.clone()).max().unwrap();
                let weights: Vec<ExactInterval> = scores
                    .iter()
                    .map(|(l, h)| {
                        let lo_arg = l - &null;
                        let hi_arg = (h - &null).min(Rat::zero());
                        let e_lo = CertifiedSeries::exponential_enclosure(&lo_arg, terms)
                            .map_err(|e| format!("{e:?}"))?;
                        let e_hi = CertifiedSeries::exponential_enclosure(&hi_arg, terms)
                            .map_err(|e| format!("{e:?}"))?;
                        ExactInterval::new(e_lo.lower.clone(), e_hi.upper.clone())
                            .map_err(|e| format!("{e:?}"))
                    })
                    .collect::<Result<_, _>>()?;
                let total_lo: Rat = weights.iter().map(|w| w.lower.clone()).sum();
                let total_hi: Rat = weights.iter().map(|w| w.upper.clone()).sum();
                if total_lo <= Rat::zero() {
                    return Err("the serial partition function is not positive".to_owned());
                }
                for d in 0..head_width {
                    let mut num_lo = Rat::zero();
                    let mut num_hi = Rat::zero();
                    let mut hull_lo: Option<Rat> = None;
                    let mut hull_hi: Option<Rat> = None;
                    for (r, j) in (start..=t).enumerate() {
                        let v_at = (j * kv_heads + g) * head_width + d;
                        let vl = self.rat_of(&v[v_at].0);
                        let vh = self.rat_of(&v[v_at].1);
                        let w = &weights[r];
                        let products = [
                            &w.lower * &vl,
                            &w.lower * &vh,
                            &w.upper * &vl,
                            &w.upper * &vh,
                        ];
                        num_lo += products.iter().min().unwrap();
                        num_hi += products.iter().max().unwrap();
                        hull_lo = Some(hull_lo.map_or(vl.clone(), |h| h.min(vl.clone())));
                        hull_hi = Some(hull_hi.map_or(vh.clone(), |h| h.max(vh.clone())));
                    }
                    let q_lo = if num_lo.is_negative() {
                        &num_lo / &total_lo
                    } else {
                        &num_lo / &total_hi
                    };
                    let q_hi = if num_hi.is_negative() {
                        &num_hi / &total_hi
                    } else {
                        &num_hi / &total_lo
                    };
                    let q_lo = q_lo.max(hull_lo.unwrap());
                    let q_hi = q_hi.min(hull_hi.unwrap());
                    if q_lo > q_hi {
                        return Err("the serial contact enclosure inverted".to_owned());
                    }
                    out[q_base + d] = (self.floor_of(&q_lo), self.ceil_of(&q_hi));
                }
            }
        }
        Ok(out)
    }

    /// `½x(1 + tanh(c1(x + c2x³)))` through `CertifiedSeries::hyperbolic_tangent_enclosure`.
    pub fn gelu(&self, x: &[Iv], c1: Dyadic, c2: Dyadic, terms: usize) -> Result<Vec<Iv>, String> {
        let (c1, c2) = (c1.value(), c2.value());
        x.iter()
            .map(|(a, b)| {
                let (a_r, b_r) = (self.rat_of(a), self.rat_of(b));
                // x + c2·x³ is increasing (c2 > 0), so its enclosure is at the endpoints.
                let inner = |x: &Rat| &c1 * (x + &c2 * x * x * x);
                let (u_lo, u_hi) = (inner(&a_r), inner(&b_r));
                let t_lo = CertifiedSeries::hyperbolic_tangent_enclosure(&u_lo, terms)
                    .map_err(|e| format!("{e:?}"))?;
                let t_hi = CertifiedSeries::hyperbolic_tangent_enclosure(&u_hi, terms)
                    .map_err(|e| format!("{e:?}"))?;
                let f_lo = Rat::one() + t_lo.lower.clone();
                let f_hi = Rat::one() + t_hi.upper.clone();
                let two = Rat::from_integer(BigInt::from(2));
                let products = [&a_r * &f_lo, &a_r * &f_hi, &b_r * &f_lo, &b_r * &f_hi];
                let y_lo = products.iter().min().unwrap() / &two;
                let y_hi = products.iter().max().unwrap() / &two;
                Ok((self.floor_of(&y_lo), self.ceil_of(&y_hi)))
            })
            .collect()
    }

    pub fn hadamard(&self, a: &[Iv], b: &[Iv]) -> Vec<Iv> {
        a.iter()
            .zip(b)
            .map(|((al, ah), (bl, bh))| {
                let (l, h) = corners(al, ah, bl, bh);
                (
                    shift_floor(&l, -i64::from(self.grain)),
                    shift_ceil(&h, -i64::from(self.grain)),
                )
            })
            .collect()
    }

    pub fn re_entry(&self, a: &[Iv], b: &[Iv]) -> Vec<Iv> {
        a.iter()
            .zip(b)
            .map(|((al, ah), (bl, bh))| (al + bl, ah + bh))
            .collect()
    }

    pub fn scale(&self, x: &[Iv], by: DyadicEnclosure) -> Vec<Iv> {
        let (sl, sh) = (BigInt::from(by.lo), BigInt::from(by.hi));
        x.iter()
            .map(|(a, b)| {
                let (l, h) = corners(a, b, &sl, &sh);
                (
                    shift_floor(&l, -i64::from(by.grain)),
                    shift_ceil(&h, -i64::from(by.grain)),
                )
            })
            .collect()
    }

    /// The parity face: does every serial enclosure intersect the card's, coordinate by coordinate?
    /// Returns the disagreeing coordinates and, for the report, the widest of each.
    pub fn parity(&self, resident: &[(i64, i64)], resident_grain: u32, serial: &[Iv]) -> Parity {
        let lift = i64::from(self.grain) - i64::from(resident_grain);
        let mut disagreeing = Vec::new();
        let mut widest_resident = 0i64;
        let mut widest_serial = BigInt::zero();
        for (at, ((rl, rh), (sl, sh))) in resident.iter().zip(serial).enumerate() {
            let rl_lifted = shift_floor(&BigInt::from(*rl), lift);
            let rh_lifted = shift_ceil(&BigInt::from(*rh), lift);
            if rl_lifted > *sh || *sl > rh_lifted {
                disagreeing.push(at);
            }
            widest_resident = widest_resident.max(rh - rl);
            widest_serial = widest_serial.max(sh - sl);
        }
        Parity {
            coordinates: resident.len().min(serial.len()),
            disagreeing,
            widest_resident_grains: widest_resident,
            widest_serial_grains: widest_serial,
        }
    }
}

#[derive(Debug)]
pub struct Parity {
    pub coordinates: usize,
    pub disagreeing: Vec<usize>,
    pub widest_resident_grains: i64,
    pub widest_serial_grains: BigInt,
}

impl Parity {
    pub fn holds(&self) -> bool {
        self.disagreeing.is_empty()
    }
}
