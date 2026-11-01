//! **A site carries its helical moment** (the dispersing field's §15.1): the superposition of
//! every source of a strand at its skin, none selected; the contact is the filter. Its card image
//! is `crates/holonics-cuda/kernels/field_moment.cuh`.
//!
//! [definition; agent-inferred, November 1] Of the winding guide's six objects this module touches
//! the **helix** (a ring's phase carried with its whole winding: `ζ^r`, `r` an integer place),
//! **faces and placement** (a span's face is read at its two boundaries) and the **tube** (the
//! strand); the pair, the cell holonomy and the tower thread stay attached through the field that
//! consumes it. It names no alphabet: a strand is complex encodings `E⁺_k`, `E⁻_k` at places `k`,
//! whatever boundary chart produced them.
//!
//! One turned ring slot has period `n`, resident phasors `ring[r] = e^(2πi r/n)` on `2^(−30)` and
//! skin decay `decay[d] = e^(−2π d/n)` on `2^(−30)` (`decay[0] = 2^30` exactly). Write `ζ^r` for
//! `ring[r rem_euclid n]`. A strand of `S` sites carries two encodings a site on `2^(−16)`:
//! `E⁺_k = before[k]`, read by every later site `t ≥ k` (the forward strand), and
//! `E⁻_k = after[k]`, read by every earlier site `t ≤ k` (the backward strand).
//!
//! ```text
//! s_t = Σ_(k ≤ t, t−k < NEAR) ζ^(k−t) D(t−k) E⁺_k  +  Σ_(k ≥ t, k−t < NEAR) ζ^(k−t) D(k−t) E⁻_k     near, term by term
//!     + Σ_(octaves (lo,hi,ℓ) of t, hi < t) D(2^ℓ) conj(ζ^t) Σ_(k=lo..hi) ζ^k E⁺_k                      far, blurred
//!     + Σ_(octaves (lo,hi,ℓ) of t, lo > t) D(2^ℓ) conj(ζ^t) Σ_(k=lo..hi) ζ^k E⁻_k                      at the octave's near edge
//! ```
//!
//! - **The frame.** The field's contact turns a source at `k` seen from `t` by `ζ^(k−t)`: the
//!   framed word is `w̃_t = ζ^t w_t` (`Field::frame`), so `Re(conj(w̃_t) w̃_k) = Re(conj(w_t) w_k ζ^(k−t))`.
//!   The moment carries `ζ^(k−t)`, the conjugate of the record's `ζ^(t−k)` notation. In the far
//!   part it is `conj(ζ^t) ζ^k` through the absolute places `t` and `k`, which are residues of a
//!   resident ring (`t, k < S ≤ reach`); only the near part reads a difference.
//! - **The octaves** are `field::crowd_ranges(t, S)`: each `(lo, hi, ℓ)` is one side of `t`, the
//!   places with `|t − k| ≥ NEAR` and `⌊log₂ |t − k|⌋ = ℓ`, `ℓ ≥ 2`. Every pair `NEAR ≤ |t − k| < S`
//!   is in exactly one, so the moment sees every source once, near term by term and far blurred.
//! - **The far sums are prefix sums** `P±[j] = Σ_(k<j) ζ^k E±_k` (exact complex integers on `2^(−46)`),
//!   an octave's sum is `P[hi+1] − P[lo]`: two reads, `O(S log S)` for the strand.
//!
//! **One release.** Every term is carried exactly on the common grain `2^(−106)`: a near term
//! `ζ D E` is on `2^(−30−30−16) = 2^(−76)`, shifted up 30; a far term `D · conj(ζ^t) · P` is
//! `2^(−30−30−46) = 2^(−106)`. The terms are integers and their sum is an integer sum, so any order
//! and any partition give the same bits; `s_t` is released once to `2^(−16)`, to the nearest
//! numerator (`release(·, 90)`). Equivalently the unreleased moment is
//! `S_t = Σ_(k,±) W_(t,k) E±_k` with `W` an exact Gaussian integer on `2^(−90)`
//! (`ζ^(k−t) D 2^30` near, `D(2^ℓ) conj(ζ^t) ζ^k` far), which is what the adjoint transposes.
//!
//! **The carrier.** The l1 norm of a Gaussian integer is `|re| + |im|`; it is submultiplicative.
//! With `R` the largest l1 of the resident ring, `D̂` the largest decay (at least 1) and `Ê` the
//! largest l1 of an input, every term of `S_t` has l1 at most `D̂ · R · max(R, 2^30) · l1(E_k)`, the
//! prefix sums at most `S · R · Ê`, and the terms of one `t` are at most `S + 1` (a place enters
//! once a strand, `k = t` in both), so every partial sum of every order has l1 at most
//! `(S + 1) · D̂ · R · max(R, 2^30) · Ê`, which below `2^127` keeps every product and every sum
//! inside `i128` (`certificate`, a property of the exact inputs alone, never of the order, so the
//! card refuses the same strands). With the founded rings (every phasor within a few grains of unit
//! modulus, so l1 below `2^31` and `R · max(R, 2^30) < 2^62`) and `D̂ ≤ 2^30` the bound is below
//! `(S + 1) · 2^92 · Ê`. For the encodings, components below `2^17` (l1 below `2^18`) give
//! `(S + 1) · 2^110`: every strand of fewer than `2^17 − 1` sites is admitted. For the covector of
//! the return, `(S + 1) · l1(δs) < 2^35`: at the reach of reading 8 (2,221 sites) components below
//! about `2^22` on `2^(−24)` (a quarter of a unit) are admitted, one past it is refused, as the
//! contact's return is (`FieldDeclaration::contact_return_bits`). Every product and sum is also
//! checked, so a bound mis-derived is a refusal and never a wrapped bit.
//!
//! **The adjoint** is the exact transpose of that integer map (the covector law: the paired adjoint
//! uses the operands that produced the forward). Multiplication by a Gaussian integer `W` is a real
//! `2 × 2` matrix whose transpose is multiplication by `conj(W)`, so with `δs` on `2^(−24)`
//!
//! ```text
//! δE⁺_k = release( Σ_(t ≥ k, t−k < NEAR) conj(ζ^(k−t)) D(t−k) δs_t 2^30  +  conj(ζ^k) Σ_ℓ D(2^ℓ) Σ_(t ∈ right octave ℓ of k) ζ^t δs_t , 90 )
//! δE⁻_k = release( Σ_(t ≤ k, k−t < NEAR) conj(ζ^(k−t)) D(k−t) δs_t 2^30  +  conj(ζ^k) Σ_ℓ D(2^ℓ) Σ_(t ∈ left octave ℓ of k) ζ^t δs_t , 90 )
//! ```
//!
//! The octaves of the transpose are the same `crowd_ranges`: the forward strand reads `k` from the
//! left octave of `t` (`t − 2^(ℓ+1) + 1 ≤ k ≤ t − max(2^ℓ, NEAR)`, clipped at 0), which is
//! `max(2^ℓ, NEAR) ≤ t − k ≤ 2^(ℓ+1) − 1` with `t < S`, that is `t` in the right octave `ℓ` of `k`
//! (`k + max(2^ℓ, NEAR) ≤ t ≤ min(k + 2^(ℓ+1) − 1, S − 1)`), and the backward strand mirrors it. So
//! `δE⁺_k` reads the right octaves of `k` and `δE⁻_k` its left octaves, from the single prefix sum
//! `Q[j] = Σ_(u<j) ζ^u δs_u` (exact, on `2^(−54)`). The identity tested on the unreleased
//! integers is `Σ_t Re(conj(δs_t) S_t) = Σ_k Re(conj(Δ⁺_k) E⁺_k) + Re(conj(Δ⁻_k) E⁻_k)`.
//!
//! **The span's face.** For `i < j`, `f_(i,j] = s⁺_j − ζ^(i−j) D(j−i) s⁺_i` (with `s⁺` the forward
//! strand's part: a strand with `after = 0`) reads the sources `i < k ≤ j` between the two
//! boundaries: `D` is exponential, so the transport composes, and the near part cancels the
//! sources at or before `i` exactly when the faces compose exactly (`ζ^a ζ^b = ζ^(a+b)`,
//! `D(a) D(b) = D(a+b)`); with attained faces the cancellation is exact to their rounding, and the
//! octave blur is the declared approximation. The value does not depend on where the span stands:
//! a shift of every site of a strand moves the near part not at all (it reads `k − t`) and the far
//! part by the ring faces' rounding.

use super::{crowd_ranges, NEAR};
use crate::hnn::keyed_modes::release;
use crate::hnn::tower::{fit64, refuse, Result, COVECTOR_BITS, FACE_BITS, MOVE_BITS};

/// A Gaussian integer `(re, im)`.
type Gauss = (i128, i128);

/// The coefficient's grain, three faces on `2^(−30)` (`ζ`, `ζ`, `D`; or `ζ`, `D` and the shift of
/// 30): `W` is on `2^(−90)`, and a moment or a return is released this many bits.
pub const COEFFICIENT_BITS: u32 = 3 * MOVE_BITS;
/// The unreleased moment's grain, `2^(−106)`: `W` times an encoding on `2^(−16)`.
pub const MOMENT_BITS: u32 = COEFFICIENT_BITS + FACE_BITS;
/// The unreleased return's grain, `2^(−114)`: `conj(W)` times a covector on `2^(−24)`.
pub const RETURN_BITS: u32 = COEFFICIENT_BITS + COVECTOR_BITS;

const CARRIER: &str = "a moment's term outgrew its 128-bit carrier";

fn carried(x: Option<i128>) -> Result<i128> {
    match x {
        Some(v) => Ok(v),
        None => refuse(CARRIER),
    }
}

fn mul(a: i128, b: i128) -> Result<i128> {
    carried(a.checked_mul(b))
}

fn add(a: i128, b: i128) -> Result<i128> {
    carried(a.checked_add(b))
}

fn sub(a: i128, b: i128) -> Result<i128> {
    carried(a.checked_sub(b))
}

/// `a · b`, checked.
fn cmul(a: Gauss, b: Gauss) -> Result<Gauss> {
    Ok((sub(mul(a.0, b.0)?, mul(a.1, b.1)?)?, add(mul(a.0, b.1)?, mul(a.1, b.0)?)?))
}

/// `conj(a) · b`, checked.
fn cmul_conj(a: Gauss, b: Gauss) -> Result<Gauss> {
    Ok((add(mul(a.0, b.0)?, mul(a.1, b.1)?)?, sub(mul(a.0, b.1)?, mul(a.1, b.0)?)?))
}

fn cadd(a: Gauss, b: Gauss) -> Result<Gauss> {
    Ok((add(a.0, b.0)?, add(a.1, b.1)?))
}

fn csub(a: Gauss, b: Gauss) -> Result<Gauss> {
    Ok((sub(a.0, b.0)?, sub(a.1, b.1)?))
}

fn conj(a: Gauss) -> Gauss {
    (a.0, -a.1)
}

fn cscale(a: Gauss, k: i128) -> Result<Gauss> {
    Ok((mul(a.0, k)?, mul(a.1, k)?))
}

/// `a · 2^bits`, checked.
fn cshift(a: Gauss, bits: u32) -> Result<Gauss> {
    cscale(a, 1i128 << bits)
}

fn wide((re, im): (i64, i64)) -> Gauss {
    (re as i128, im as i128)
}

fn l1((re, im): (i64, i64)) -> u128 {
    re.unsigned_abs() as u128 + im.unsigned_abs() as u128
}

/// [definition; agent-inferred, November 1] **The l1 certificate**: a strand of `sites` places, a
/// ring of largest l1 `ring_l1`, a decay of largest magnitude `decay_max` and inputs of largest l1
/// `input_l1` are admitted when `(sites + 1) · max(decay_max, 1) · ring_l1 · max(ring_l1, 2^30) ·
/// input_l1 < 2^127` (module doc: every term and every partial sum of every order then has l1
/// below the carrier). A property of the exact inputs alone: the card evaluates the same and
/// refuses the same strands.
pub fn certificate(sites: u128, ring_l1: u128, decay_max: u128, input_l1: u128) -> bool {
    let unit = ring_l1.max(1u128 << MOVE_BITS);
    let mut bound = sites + 1;
    for factor in [decay_max.max(1), ring_l1, unit, input_l1] {
        bound = match bound.checked_mul(factor) {
            Some(b) => b,
            None => return false,
        };
    }
    bound < 1u128 << 127
}

/// The resident faces of one ring slot over a strand of `sites` places, validated.
struct Law<'a> {
    ring: &'a [(i64, i64)],
    n: usize,
    decay: &'a [i64],
    sites: usize,
    ring_l1: u128,
    decay_max: u128,
}

impl<'a> Law<'a> {
    fn new(sites: usize, ring: &'a [(i64, i64)], n: usize, decay: &'a [i64]) -> Result<Self> {
        if n == 0 || i64::try_from(n).is_err() {
            return refuse("a ring of period zero turns nothing");
        }
        // The far part reads the absolute places `k < S` as `ring[k mod n]`, which is resident when
        // the ring holds `min(n, S)` phasors (`Field::rings`: `min(n, reach)`, `S ≤ reach`).
        if ring.len() < n.min(sites) {
            return refuse("a strand's places outrun the resident ring");
        }
        // The farthest decay read is `D(S − 1)` (near) or `D(2^ℓ)`, `2^ℓ < S` (far).
        if decay.len() < sites {
            return refuse("a strand outruns the skin's reach");
        }
        let resident = &ring[..ring.len().min(n)];
        let ring_l1 = resident.iter().map(|&p| l1(p)).max().unwrap_or(0);
        let decay_max = decay[..sites].iter().map(|d| d.unsigned_abs() as u128).max().unwrap_or(0);
        Ok(Self { ring, n, decay, sites, ring_l1, decay_max })
    }

    /// The l1 certificate for inputs of largest l1 `input_l1`.
    fn certify(&self, input_l1: u128) -> Result<()> {
        if certificate(self.sites as u128, self.ring_l1, self.decay_max, input_l1) {
            Ok(())
        } else {
            refuse("a strand past the l1 certificate of its 128-bit carrier")
        }
    }

    /// `ζ^k` for an absolute place `k < S`: the resident `ring[k mod n]`.
    fn absolute(&self, k: usize) -> Gauss {
        wide(self.ring[k % self.n])
    }

    /// `ζ^r = ring[r rem_euclid n]` for a near difference `|r| < S`. [agent-inferred] Where the
    /// ring holds fewer than `n` phasors (`n` past the reach) a negative `r` lands past it, and the
    /// face is the conjugate of the resident `ring[−r]`: the ring is closed under conjugation,
    /// `ring[n − m] = conj(ring[m])` bit for bit (`ring_phasor` is odd under `r → −r`, the quarter
    /// points are exact), tested against the full ring.
    fn zeta(&self, r: i64) -> Result<Gauss> {
        let n = self.n as i64;
        let m = r.rem_euclid(n) as usize;
        if let Some(&p) = self.ring.get(m) {
            return Ok(wide(p));
        }
        match self.ring.get(self.n - m) {
            Some(&p) => Ok(conj(wide(p))),
            None => refuse("a near phase outside the resident ring"),
        }
    }

    /// `D(d)`, the skin decay across `d` places.
    fn decay(&self, d: usize) -> i128 {
        self.decay[d] as i128
    }
}

/// `P[j] = Σ_(k<j) ζ^k x_k`, the prefix sums of a strand's absolute phases (exact, `grain(x) − 30`).
fn prefix(law: &Law, x: &[(i64, i64)]) -> Result<Vec<Gauss>> {
    let mut out = Vec::with_capacity(x.len() + 1);
    let mut sum = (0i128, 0i128);
    out.push(sum);
    for (k, &e) in x.iter().enumerate() {
        sum = cadd(sum, cmul(law.absolute(k), wide(e))?)?;
        out.push(sum);
    }
    Ok(out)
}

/// A near term `ζ D x 2^30`: the product of two faces on `2^(−30)` with `x`, shifted up the frames'
/// 30 bits, so the term is on `grain(x) − 30` (an encoding on `2^(−16)` gives `2^(−106)`).
fn near(zeta: Gauss, decay: i128, x: Gauss) -> Result<Gauss> {
    cshift(cscale(cmul(zeta, x)?, decay)?, MOVE_BITS)
}

/// The transpose of a near term, `conj(ζ) D x 2^30` (a covector on `2^(−24)` gives `2^(−114)`).
fn near_back(zeta: Gauss, decay: i128, x: Gauss) -> Result<Gauss> {
    cshift(cscale(cmul_conj(zeta, x)?, decay)?, MOVE_BITS)
}

/// The largest l1 of a set of inputs.
fn extent<'a>(strands: impl IntoIterator<Item = &'a [(i64, i64)]>) -> u128 {
    strands.into_iter().flat_map(|s| s.iter().map(|&p| l1(p))).max().unwrap_or(0)
}

/// [definition; agent-inferred, November 1] **The moments, unreleased**: `S_t` on `2^(−106)` for
/// every site of the strand (module doc). `before[k] = E⁺_k`, `after[k] = E⁻_k` on `2^(−16)`;
/// `ring` the slot's resident phasors on `2^(−30)` of period `n`; `decay` its skin on `2^(−30)` over
/// at least `S` distances.
pub fn moment_exact(before: &[(i64, i64)], after: &[(i64, i64)], ring: &[(i64, i64)], n: usize, decay: &[i64]) -> Result<Vec<(i128, i128)>> {
    let sites = before.len();
    if after.len() != sites {
        return refuse("a strand's two encodings are of different lengths");
    }
    if sites == 0 {
        return Ok(Vec::new());
    }
    let law = Law::new(sites, ring, n, decay)?;
    law.certify(extent([before, after]))?;
    let (up, down) = (prefix(&law, before)?, prefix(&law, after)?);
    (0..sites)
        .map(|t| -> Result<Gauss> {
            let mut s = (0i128, 0i128);
            for d in 0..NEAR.min(t + 1) {
                s = cadd(s, near(law.zeta(-(d as i64))?, law.decay(d), wide(before[t - d]))?)?;
            }
            for d in 0..NEAR.min(sites - t) {
                s = cadd(s, near(law.zeta(d as i64)?, law.decay(d), wide(after[t + d]))?)?;
            }
            let home = conj(law.absolute(t));
            for (lo, hi, level) in crowd_ranges(t, sites) {
                let sum = if hi < t { csub(up[hi + 1], up[lo])? } else { csub(down[hi + 1], down[lo])? };
                s = cadd(s, cscale(cmul(home, sum)?, law.decay(1 << level))?)?;
            }
            Ok(s)
        })
        .collect()
}

/// **The moments** `s_t` on `2^(−16)`: [`moment_exact`] released once, to the nearest numerator.
pub fn moments(before: &[(i64, i64)], after: &[(i64, i64)], ring: &[(i64, i64)], n: usize, decay: &[i64]) -> Result<Vec<(i64, i64)>> {
    moment_exact(before, after, ring, n, decay)?
        .into_iter()
        .map(|(re, im)| -> Result<(i64, i64)> { Ok((fit64(release(re, COEFFICIENT_BITS))?, fit64(release(im, COEFFICIENT_BITS))?)) })
        .collect()
}

/// [definition; agent-inferred, November 1] **The moments' return, unreleased**: `(Δ⁺, Δ⁻)` on
/// `2^(−114)`, the exact transpose of [`moment_exact`]'s integer map applied to `ds = δs` on
/// `2^(−24)` (module doc).
pub fn moment_return_exact(ds: &[(i64, i64)], ring: &[(i64, i64)], n: usize, decay: &[i64]) -> Result<(Vec<(i128, i128)>, Vec<(i128, i128)>)> {
    let sites = ds.len();
    if sites == 0 {
        return Ok((Vec::new(), Vec::new()));
    }
    let law = Law::new(sites, ring, n, decay)?;
    law.certify(extent([ds]))?;
    let q = prefix(&law, ds)?;
    let (mut plus, mut minus) = (Vec::with_capacity(sites), Vec::with_capacity(sites));
    for k in 0..sites {
        let (mut p, mut m) = ((0i128, 0i128), (0i128, 0i128));
        // δE⁺_k reads the sites t = k + d at ζ^(k−t) = ζ^(−d); δE⁻_k the sites t = k − d at ζ^(d).
        for d in 0..NEAR.min(sites - k) {
            p = cadd(p, near_back(law.zeta(-(d as i64))?, law.decay(d), wide(ds[k + d]))?)?;
        }
        for d in 0..NEAR.min(k + 1) {
            m = cadd(m, near_back(law.zeta(d as i64)?, law.decay(d), wide(ds[k - d]))?)?;
        }
        let home = conj(law.absolute(k));
        for (lo, hi, level) in crowd_ranges(k, sites) {
            let far = cscale(cmul(home, csub(q[hi + 1], q[lo])?)?, law.decay(1 << level))?;
            if lo > k {
                p = cadd(p, far)?;
            } else {
                m = cadd(m, far)?;
            }
        }
        plus.push(p);
        minus.push(m);
    }
    Ok((plus, minus))
}

/// **The moments' return** `(δE⁺, δE⁻)` on `2^(−24)`: [`moment_return_exact`] released once, to the
/// nearest numerator (the covector's carrier is wide, `i128`, as the field's).
pub fn moments_return(ds: &[(i64, i64)], ring: &[(i64, i64)], n: usize, decay: &[i64]) -> Result<(Vec<(i128, i128)>, Vec<(i128, i128)>)> {
    let (plus, minus) = moment_return_exact(ds, ring, n, decay)?;
    let released = |v: Vec<Gauss>| -> Vec<Gauss> { v.into_iter().map(|(re, im)| (release(re, COEFFICIENT_BITS), release(im, COEFFICIENT_BITS))).collect() };
    Ok((released(plus), released(minus)))
}

#[cfg(test)]
mod tests;
