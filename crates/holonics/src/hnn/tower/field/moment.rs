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
//! (`ζ^(k−t) D 2^30` near, `D(2^ℓ) conj(ζ^t) ζ^k` far), which the return transposes.
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
//! `(S + 1) · 2^110`: every strand of fewer than `2^17 − 1` sites is admitted. Every product and sum
//! is also checked, so a bound mis-derived is a refusal and never a wrapped bit.
//!
//! **The return** is the forward map's transpose, with the turned covector released once a term. The
//! exact transpose (multiplication by a Gaussian integer `W` transposes to multiplication by
//! `conj(W)`) carries `conj(W) δs` on `2^(−114)`, and a covector's components reach tens of units
//! (the value covector summed over the ticks at a 406-site crib region had l1 `2^28.1`, about 16
//! units on `2^(−24)`), so its carrier is `(S + 1) · 2^91 · l1(δs) < 2^127`, which admits only about
//! `2^27.3`: training refused at its second section. A released reverse is the field's norm (every
//! reverse product of the field is released at its grain), so the far part's turned covector is
//! released once a term, at the covector's own grain: one declared crossing a term, its rounding the
//! only error of the return. With `δs` on `2^(−24)`:
//!
//! ```text
//! r_u    = release(ζ^u δs_u, 30)                                      on 2^(−24)    the turned covector, once
//! Q[j]   = Σ_(u<j) r_u                                                on 2^(−24)    exact sums of released terms
//! Δ⁺_k   = Σ_(t ≥ k, t−k < NEAR) conj(ζ^(k−t)) D(t−k) δs_t
//!        + conj(ζ^k) Σ_ℓ D(2^ℓ) (Q[hi+1] − Q[lo])  over the right octaves (lo,hi,ℓ) of k       on 2^(−84)
//! Δ⁻_k   = the same over t ≤ k (near) and the left octaves of k
//! δE±_k  = release(Δ±_k, 60)                                          on 2^(−24)
//! ```
//!
//! The near term is `conj(ζ^(k−t)) D δs` on `2^(−30−30−24) = 2^(−84)` (no shift up 30); the far term
//! `conj(ζ^k) · D(2^ℓ) · (Q[hi+1] − Q[lo])` is on `2^(−30−30−24) = 2^(−84)` too. `RETURN_BITS = 84`,
//! released 60 bits to the covector's grain. The forward stays exact.
//!
//! The octaves of the return are the same `crowd_ranges`: the forward strand reads `k` from the left
//! octave of `t` (`t − 2^(ℓ+1) + 1 ≤ k ≤ t − max(2^ℓ, NEAR)`, clipped at 0), which is
//! `max(2^ℓ, NEAR) ≤ t − k ≤ 2^(ℓ+1) − 1` with `t < S`, that is `t` in the right octave `ℓ` of `k`
//! (`k + max(2^ℓ, NEAR) ≤ t ≤ min(k + 2^(ℓ+1) − 1, S − 1)`), and the backward strand mirrors it. So
//! `δE⁺_k` reads the right octaves of `k` and `δE⁻_k` its left octaves, from the single prefix `Q`.
//!
//! **The return's pairing.** Let `Δ̃±` be the exact transpose on `2^(−114)`. Then
//! `Δ̂±_k − Δ̃±_k / 2^30 = conj(ζ^k) Σ_ℓ D(2^ℓ) Σ_(t ∈ octave ℓ) ε_t` with `ε_t = r_t − ζ^t δs_t / 2^30`,
//! both components of `ε_t` at most `½`, so `l1(ε_t) ≤ 1`, and the exact transpose pairs exactly,
//! `Σ_t Re(conj(δs_t) S_t) = Σ_k Re(conj(Δ̃⁺_k) E⁺_k) + Re(conj(Δ̃⁻_k) E⁻_k)`, hence
//!
//! ```text
//! | Σ_t Re(conj(δs_t) S_t) − 2^30 Σ_k [Re(conj(Δ⁺_k) E⁺_k) + Re(conj(Δ⁻_k) E⁻_k)] |
//!     ≤ 2^30 Σ_k [ l1(ζ^k) (Σ_(far t>k) D(2^ℓ_(t,k))) ‖E⁺_k‖∞ + l1(ζ^k) (Σ_(far t<k) D(2^ℓ_(t,k))) ‖E⁻_k‖∞ ]
//! ```
//!
//! (`Re(conj(e) E) ≤ l1(e) ‖E‖∞`). It is an equality where no release rounds (no far pair, `S ≤ NEAR`;
//! or a stationary ring, whose turned covector `2^30 δs` releases exactly).
//!
//! **The return's carrier** (`return_certificate`, again a property of the exact inputs alone). With
//! `G` the largest l1 of a covector entry: the turned term `ζ^u δs_u` has l1 at most `R G`, the
//! released term `T = ⌊R G / 2^30⌋ + 1` (each component at most `|x| / 2^30 + ½`); an entry of `Q` and
//! a range sum of it at most `S T`; a near term at most `D̂ R G`; a far term `D̂ R S_range T`; the far
//! sources of one side are disjoint and the near terms at most `NEAR` a side, so every partial sum of
//! every order has l1 at most
//!
//! ```text
//! K = max(D̂, 1) · R · ( NEAR · G + S · ( ⌊R G / 2^30⌋ + 1 ) )  <  2^127
//! ```
//!
//! With the founded rings (`R < 2^31`) and `D̂ ≤ 2^30`, `K < 2^61 (NEAR + 3 S) G` (for `G ≥ 1`; about
//! `(S + 2 NEAR) 2^61 G`), so covectors of l1 up to about `2^66 / (NEAR + 3 S)` are admitted: `2^55.7`
//! at 406 sites, `2^53.3` at the reach of reading 8 (2,221 sites).
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
/// 30): `W` is on `2^(−90)`, and a moment is released this many bits.
pub const COEFFICIENT_BITS: u32 = 3 * MOVE_BITS;
/// The unreleased moment's grain, `2^(−106)`: `W` times an encoding on `2^(−16)`.
pub const MOMENT_BITS: u32 = COEFFICIENT_BITS + FACE_BITS;
/// The unreleased return's grain, `2^(−84)`: `conj(ζ) D` (two faces on `2^(−30)`) times a covector on
/// `2^(−24)`, with the far part's prefix of the turned covector released to `2^(−24)`.
pub const RETURN_BITS: u32 = 2 * MOVE_BITS + COVECTOR_BITS;
/// The bits the return is released: to the covector's own grain `2^(−24)`.
pub const RETURN_RELEASE_BITS: u32 = RETURN_BITS - COVECTOR_BITS;

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

/// [definition; agent-inferred, November 1] **The return's l1 certificate** (module doc): a covector
/// of largest l1 `input_l1` over a strand of `sites` places is admitted when
/// `max(decay_max, 1) · ring_l1 · (NEAR · input_l1 + sites · (⌊ring_l1 · input_l1 / 2^30⌋ + 1)) < 2^127`,
/// the products formed in that order and an overflow of one a refusal. A term released once at the
/// covector's grain adds one grain of l1 to the turned term's `R G / 2^30`, and the far part's sources
/// are disjoint, so the bound is linear in the strand. A property of the exact inputs alone, as
/// [`certificate`] is.
pub fn return_certificate(sites: u128, ring_l1: u128, decay_max: u128, input_l1: u128) -> bool {
    let bound = (|| {
        let released = (ring_l1.checked_mul(input_l1)? >> MOVE_BITS) + 1;
        let inner = (NEAR as u128).checked_mul(input_l1)?.checked_add(sites.checked_mul(released)?)?;
        decay_max.max(1).checked_mul(ring_l1)?.checked_mul(inner)
    })();
    matches!(bound, Some(b) if b < 1u128 << 127)
}

/// [definition; agent-inferred, November 2] **A strand's own clock** (§16, Law 1): each place's clock `τ_t` and
/// its turn's variation `σ_t` on `2^(−24)`, with the slot's faces at any clock: `turn(ρ) = ζ^ρ` on `2^(−30)` (the
/// resident ring at a whole place, the exponential's series between) and `skin(s) = e^(−2π|s|/n)`. The moment
/// then turns a source at `k` seen from `t` by `ζ^(τ_k − τ_t)` and carries it by `e^(−2π|σ_t − σ_k|/n)`, its far
/// octave at the skin of the place `2^ℓ` away on its side; with `τ_t = σ_t = t` it is the byte place's moment bit
/// for bit.
pub struct Pace<'a> {
    pub tau: &'a [i64],
    pub sigma: &'a [i64],
    pub turn: &'a dyn Fn(i128) -> (i64, i64),
    pub skin: &'a dyn Fn(i128) -> i64,
}

/// The resident faces of one ring slot over a strand of `sites` places, validated.
struct Law<'a> {
    ring: &'a [(i64, i64)],
    n: usize,
    decay: &'a [i64],
    sites: usize,
    ring_l1: u128,
    decay_max: u128,
    pace: Option<&'a Pace<'a>>,
}

impl<'a> Law<'a> {
    fn new(sites: usize, ring: &'a [(i64, i64)], n: usize, decay: &'a [i64], pace: Option<&'a Pace<'a>>) -> Result<Self> {
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
        let mut ring_l1 = resident.iter().map(|&p| l1(p)).max().unwrap_or(0);
        if let Some(pace) = pace {
            if pace.tau.len() != sites || pace.sigma.len() != sites {
                return refuse("a strand's clock that is not one a place");
            }
            // Every face the paced strand reads: each place's own and each near difference's.
            for t in 0..sites {
                ring_l1 = ring_l1.max(l1((pace.turn)(pace.tau[t] as i128)));
                for k in t.saturating_sub(NEAR - 1)..(t + NEAR).min(sites) {
                    ring_l1 = ring_l1.max(l1((pace.turn)(pace.tau[k] as i128 - pace.tau[t] as i128)));
                }
            }
        }
        let decay_max = decay[..sites].iter().map(|d| d.unsigned_abs() as u128).max().unwrap_or(0);
        Ok(Self { ring, n, decay, sites, ring_l1, decay_max, pace })
    }

    /// The l1 certificate for inputs of largest l1 `input_l1`.
    fn certify(&self, input_l1: u128) -> Result<()> {
        if certificate(self.sites as u128, self.ring_l1, self.decay_max, input_l1) {
            Ok(())
        } else {
            refuse("a strand past the l1 certificate of its 128-bit carrier")
        }
    }

    /// The return's l1 certificate for covectors of largest l1 `input_l1`.
    fn certify_return(&self, input_l1: u128) -> Result<()> {
        if return_certificate(self.sites as u128, self.ring_l1, self.decay_max, input_l1) {
            Ok(())
        } else {
            refuse("a covector past the l1 certificate of the return's 128-bit carrier")
        }
    }

    /// `ζ^k` for an absolute place `k < S`: the resident `ring[k mod n]`; on a paced strand `ζ^(τ_k)`.
    fn absolute(&self, k: usize) -> Gauss {
        match self.pace {
            Some(p) => wide((p.turn)(p.tau[k] as i128)),
            None => wide(self.ring[k % self.n]),
        }
    }

    /// The near face of a source at `k` seen from `t`: `ζ^(k−t)`, or `ζ^(τ_k − τ_t)` on a paced strand.
    fn phase(&self, t: usize, k: usize) -> Result<Gauss> {
        match self.pace {
            Some(p) => Ok(wide((p.turn)(p.tau[k] as i128 - p.tau[t] as i128))),
            None => self.zeta(k as i64 - t as i64),
        }
    }

    /// The near skin between `t` and `k`: `D(|t − k|)`, or `e^(−2π|σ_t − σ_k|/n)` on a paced strand.
    fn between(&self, t: usize, k: usize) -> i128 {
        match self.pace {
            Some(p) => (p.skin)(p.sigma[t] as i128 - p.sigma[k] as i128) as i128,
            None => self.decay(t.abs_diff(k)),
        }
    }

    /// A far octave's skin from `t` on one side: `D(2^ℓ)`, or the skin to the place `2^ℓ` away on that side on
    /// a paced strand (inside the strand wherever the octave is: its near edge is at least `2^ℓ` away).
    fn octave(&self, t: usize, level: u32, right: bool) -> i128 {
        match self.pace {
            Some(p) => {
                let k = if right { t + (1 << level) } else { t - (1 << level) };
                (p.skin)(p.sigma[t] as i128 - p.sigma[k] as i128) as i128
            }
            None => self.decay(1 << level),
        }
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

/// A near term of the return, `conj(ζ) D x`: two faces on `2^(−30)` and a covector on `2^(−24)`, so
/// on `2^(−84)`, with no shift up (the return is released, not the exact transpose on `2^(−114)`).
fn near_back(zeta: Gauss, decay: i128, x: Gauss) -> Result<Gauss> {
    cscale(cmul_conj(zeta, x)?, decay)
}

/// `Q[j] = Σ_(u<j) release(ζ^u x_u, 30)`: the prefix of the turned covector, released once a term to
/// the covector's own grain `2^(−24)` (exact integer sums of released terms).
fn released_prefix(law: &Law, x: &[(i64, i64)]) -> Result<Vec<Gauss>> {
    let mut out = Vec::with_capacity(x.len() + 1);
    let mut sum = (0i128, 0i128);
    out.push(sum);
    for (k, &e) in x.iter().enumerate() {
        let (re, im) = cmul(law.absolute(k), wide(e))?;
        sum = cadd(sum, (release(re, MOVE_BITS), release(im, MOVE_BITS)))?;
        out.push(sum);
    }
    Ok(out)
}

/// The largest l1 of a set of inputs.
fn extent<'a>(strands: impl IntoIterator<Item = &'a [(i64, i64)]>) -> u128 {
    strands.into_iter().flat_map(|s| s.iter().map(|&p| l1(p))).max().unwrap_or(0)
}

/// [definition; agent-inferred, November 1] **The moments, unreleased**: `S_t` on `2^(−106)` for
/// every site of the strand (module doc). `before[k] = E⁺_k`, `after[k] = E⁻_k` on `2^(−16)`;
/// `ring` the slot's resident phasors on `2^(−30)` of period `n`; `decay` its skin on `2^(−30)` over
/// at least `S` distances.
pub fn moment_exact(before: &[(i64, i64)], after: &[(i64, i64)], ring: &[(i64, i64)], n: usize, decay: &[i64], pace: Option<&Pace>) -> Result<Vec<(i128, i128)>> {
    let sites = before.len();
    if after.len() != sites {
        return refuse("a strand's two encodings are of different lengths");
    }
    if sites == 0 {
        return Ok(Vec::new());
    }
    let law = Law::new(sites, ring, n, decay, pace)?;
    law.certify(extent([before, after]))?;
    let (up, down) = (prefix(&law, before)?, prefix(&law, after)?);
    (0..sites)
        .map(|t| -> Result<Gauss> {
            let mut s = (0i128, 0i128);
            for d in 0..NEAR.min(t + 1) {
                s = cadd(s, near(law.phase(t, t - d)?, law.between(t, t - d), wide(before[t - d]))?)?;
            }
            for d in 0..NEAR.min(sites - t) {
                s = cadd(s, near(law.phase(t, t + d)?, law.between(t, t + d), wide(after[t + d]))?)?;
            }
            let home = conj(law.absolute(t));
            for (lo, hi, level) in crowd_ranges(t, sites) {
                let sum = if hi < t { csub(up[hi + 1], up[lo])? } else { csub(down[hi + 1], down[lo])? };
                s = cadd(s, cscale(cmul(home, sum)?, law.octave(t, level, hi > t))?)?;
            }
            Ok(s)
        })
        .collect()
}

/// **The moments** `s_t` on `2^(−16)`: [`moment_exact`] released once, to the nearest numerator.
pub fn moments(before: &[(i64, i64)], after: &[(i64, i64)], ring: &[(i64, i64)], n: usize, decay: &[i64], pace: Option<&Pace>) -> Result<Vec<(i64, i64)>> {
    moment_exact(before, after, ring, n, decay, pace)?
        .into_iter()
        .map(|(re, im)| -> Result<(i64, i64)> { Ok((fit64(release(re, COEFFICIENT_BITS))?, fit64(release(im, COEFFICIENT_BITS))?)) })
        .collect()
}

/// [definition; agent-inferred, November 1] **The moments' return, unreleased**: `(Δ⁺, Δ⁻)` on
/// `2^(−84)` for `ds = δs` on `2^(−24)` (module doc): the near terms exact, the far part's turned
/// covector released once a term to `2^(−24)`, every sum an integer sum.
pub fn moment_return_exact(ds: &[(i64, i64)], ring: &[(i64, i64)], n: usize, decay: &[i64], pace: Option<&Pace>) -> Result<(Vec<(i128, i128)>, Vec<(i128, i128)>)> {
    let sites = ds.len();
    if sites == 0 {
        return Ok((Vec::new(), Vec::new()));
    }
    let law = Law::new(sites, ring, n, decay, pace)?;
    law.certify_return(extent([ds]))?;
    let q = released_prefix(&law, ds)?;
    // [agent-inferred, November 2] On a paced strand each receiving site `t` read its far octave at its own skin
    // (`Law::octave`), so the turned covector is prefixed once a level and side with each `t`'s skin:
    // `[2(ℓ − 2) + side][j] = Σ_(t<j) D_(t,ℓ,side) release(ζ^(τ_t) δs_t, 30)`, side 1 the sites `t` that read
    // their octave on the left (`t` right of the source), so a source reads a range in two reads, `O(S log S)`.
    let skinned: Option<Vec<Vec<Gauss>>> = match law.pace {
        None => None,
        Some(_) => {
            let levels = (2u32..).take_while(|&l| (1usize << l) < sites).count();
            let mut out = Vec::with_capacity(2 * levels);
            for level in (2u32..).take(levels) {
                for left in [false, true] {
                    let mut sum = (0i128, 0i128);
                    let mut row = Vec::with_capacity(sites + 1);
                    row.push(sum);
                    for t in 0..sites {
                        let reads = if left { t >= 1 << level } else { t + (1 << level) < sites };
                        if reads {
                            let (re, im) = cmul(law.absolute(t), wide(ds[t]))?;
                            sum = cadd(sum, cscale((release(re, MOVE_BITS), release(im, MOVE_BITS)), law.octave(t, level, !left))?)?;
                        }
                        row.push(sum);
                    }
                    out.push(row);
                }
            }
            Some(out)
        }
    };
    let (mut plus, mut minus) = (Vec::with_capacity(sites), Vec::with_capacity(sites));
    for k in 0..sites {
        let (mut p, mut m) = ((0i128, 0i128), (0i128, 0i128));
        // δE⁺_k reads the sites t = k + d at ζ^(k−t) = ζ^(−d); δE⁻_k the sites t = k − d at ζ^(d).
        for d in 0..NEAR.min(sites - k) {
            p = cadd(p, near_back(law.phase(k + d, k)?, law.between(k + d, k), wide(ds[k + d]))?)?;
        }
        for d in 0..NEAR.min(k + 1) {
            m = cadd(m, near_back(law.phase(k - d, k)?, law.between(k - d, k), wide(ds[k - d]))?)?;
        }
        let home = conj(law.absolute(k));
        for (lo, hi, level) in crowd_ranges(k, sites) {
            // The far source `k` is in octave `ℓ` of each site `t` of this range (on `t`'s other side), whose
            // skin the forward read at `t`: on a paced strand that skin is `t`'s own, so the octave's turned
            // covector is summed with each `t`'s skin (the byte place's `D(2^ℓ)` is one for them all).
            let far = match &skinned {
                None => cscale(cmul(home, csub(q[hi + 1], q[lo])?)?, law.decay(1 << level))?,
                Some(sk) => {
                    let side = &sk[2 * (level as usize - 2) + usize::from(lo > k)];
                    cmul(home, csub(side[hi + 1], side[lo])?)?
                }
            };
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

/// **The moments' return** `(δE⁺, δE⁻)` on `2^(−24)`: [`moment_return_exact`] released once, 60 bits, to
/// the nearest numerator (the covector's carrier is wide, `i128`, as the field's).
pub fn moments_return(ds: &[(i64, i64)], ring: &[(i64, i64)], n: usize, decay: &[i64], pace: Option<&Pace>) -> Result<(Vec<(i128, i128)>, Vec<(i128, i128)>)> {
    let (plus, minus) = moment_return_exact(ds, ring, n, decay, pace)?;
    let released = |v: Vec<Gauss>| -> Vec<Gauss> { v.into_iter().map(|(re, im)| (release(re, RETURN_RELEASE_BITS), release(im, RETURN_RELEASE_BITS))).collect() };
    Ok((released(plus), released(minus)))
}

/// `Im(conj(a) z)`-like cross `a_i z_r − a_r z_i`, which is `Re(conj(a) · i z)`: the turn's covector of `z` read
/// against `a`.
fn cross(a: Gauss, z: Gauss) -> Result<i128> {
    sub(mul(a.1, z.0)?, mul(a.0, z.1)?)
}

/// `release(x · y, bits)`, checked.
fn scaled(x: i128, y: i128, bits: u32) -> Result<i128> {
    Ok(release(mul(x, y)?, bits))
}

/// [definition; agent-inferred, November 2] **The moments' clock covector** (§16, Law 1): on a strand whose moments
/// `s` (on `2^(−16)`) read the encodings `E±` (on `2^(−16)`) through its clock, with the moments' covector `δs` and
/// their return `δE±` (both on `2^(−24)`), and `b = 2π/n` on `2^(−30)`, the covectors of its clock `τ` and of its
/// turn's variation `σ`, `2^24 ∂/∂τ_t` and `2^24 ∂/∂σ_t` on `2^(−24)`:
///
/// ```text
/// τ:  every term of s_t turns as conj(ζ^(τ_t)) ζ^(τ_k):  ∂s_t/∂τ_t = −i b s_t,  ∂s_t/∂τ_k = i b W_tk E_k
///     δτ_t += −b Re(conj(δs_t) i s_t),   δτ_k += b Re(conj(δE±_k) i E±_k)   (δE = Σ_t conj(W_tk) δs_t)
/// σ:  a near term's skin D(σ_t − σ_k), a far octave's D(σ_t − σ_(t±2^ℓ)):  ∂D/∂σ_t = −b sgn D,  the other +b sgn D
///     with ∂s_t/∂D the term without its skin: near ζ^(τ_k − τ_t) E_k, far conj(ζ^(τ_t)) Σ_(k∈octave) ζ^(τ_k) E_k
/// ```
///
/// Each product released once at its grain (the order fixed: the near term's `Re(conj(δs) ζ E)` on `2^(−70)`, times
/// `D` released 30, times `b` released 30, released 46; the far octave's face `conj(ζ^τ) P` released 30 first).
#[allow(clippy::too_many_arguments)]
pub fn pace_return(before: &[(i64, i64)], after: &[(i64, i64)], s: &[(i64, i64)], ds: &[(i64, i64)], back_before: &[(i128, i128)], back_after: &[(i128, i128)], ring: &[(i64, i64)], n: usize, decay: &[i64], pace: &Pace, b: i128) -> Result<(Vec<i128>, Vec<i128>)> {
    let sites = before.len();
    if [after.len(), s.len(), ds.len(), back_before.len(), back_after.len()].iter().any(|&l| l != sites) {
        return refuse("a strand's clock covector over parts of different lengths");
    }
    let (mut dtau, mut dsig) = (vec![0i128; sites], vec![0i128; sites]);
    if sites == 0 {
        return Ok((dtau, dsig));
    }
    let law = Law::new(sites, ring, n, decay, Some(pace))?;
    let sign = |x: i64| -> i128 { x.signum() as i128 };
    for t in 0..sites {
        dtau[t] = sub(dtau[t], scaled(cross(wide(ds[t]), wide(s[t]))?, b, MOVE_BITS + FACE_BITS)?)?;
        dtau[t] = add(dtau[t], scaled(add(cross(back_before[t], wide(before[t]))?, cross(back_after[t], wide(after[t]))?)?, b, MOVE_BITS + FACE_BITS)?)?;
    }
    // The skins: one term a pair or an octave, its share of `σ` at its two ends.
    let mut skin = |t: usize, k: usize, d: i128, inner: i128| -> Result<()> {
        let at = scaled(scaled(inner, d, MOVE_BITS)?, b, MOVE_BITS)?;
        let term = release(at, MOVE_BITS + FACE_BITS);
        let sgn = sign(pace.sigma[t] - pace.sigma[k]);
        dsig[t] = sub(dsig[t], mul(sgn, term)?)?;
        dsig[k] = add(dsig[k], mul(sgn, term)?)?;
        Ok(())
    };
    let re = |a: Gauss, z: Gauss| -> Result<i128> { add(mul(a.0, z.0)?, mul(a.1, z.1)?) };
    let (up, down) = (prefix(&law, before)?, prefix(&law, after)?);
    for t in 0..sites {
        for d in 0..NEAR.min(t + 1) {
            let k = t - d;
            skin(t, k, law.between(t, k), re(wide(ds[t]), cmul(law.phase(t, k)?, wide(before[k]))?)?)?;
        }
        for d in 0..NEAR.min(sites - t) {
            let k = t + d;
            skin(t, k, law.between(t, k), re(wide(ds[t]), cmul(law.phase(t, k)?, wide(after[k]))?)?)?;
        }
        let home = conj(law.absolute(t));
        for (lo, hi, level) in crowd_ranges(t, sites) {
            let right = hi > t;
            let sum = if right { csub(down[hi + 1], down[lo])? } else { csub(up[hi + 1], up[lo])? };
            let (fr, fi) = cmul(home, sum)?;
            let face = (release(fr, MOVE_BITS), release(fi, MOVE_BITS));
            let k = if right { t + (1 << level) } else { t - (1 << level) };
            skin(t, k, law.octave(t, level, right), re(wide(ds[t]), face)?)?;
        }
    }
    Ok((dtau, dsig))
}

#[cfg(test)]
mod tests;
