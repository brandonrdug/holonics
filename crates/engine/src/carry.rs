//! **The strand: the pair, the carry circle, the junction and the triad.**
//!
//! the pair `x_t ← x_t + W_c(a_t · b_(s(t))) + b_c`; the carry circle `Q_t = κ_t b_t + γ_t Q_(t∓1)`, `γ = γ̂(q)/(1 + d)`,
//! `κ = N₀ d/(1 + d)`; the triad's products along the strand
//!
//! Kind: gate a site, then chain along the strand. Kernels: `field_pair`, `field_pair_gamma`, `field_carry_gates_read`, `field_pair_scan`, `field_pair_scan_face`,
//! `field_triad` (`hnn/carry.rs`, `hnn/contact.rs`).
//! Lean: `HNN/CarryGate`, `HNN/TriadGauge`.
//! Atlas: `contact.carried-product`, `tower.field-carry-leak-runs`.
//! Records: `2026-11-11_RAISED_RATES_BUY…`, `2026-11-12_THE_FRICTION_A_REGION_SETS…`. The derivations' history is in the records; the items below
//! keep their reasons.

#[allow(unused_imports)]
use crate::field::*;
#[allow(unused_imports)]
use rayon::prelude::*;

/// Each family's `max |w|`, read once a pass.
/// [definition; theory, November 11 00:22] The carry's `γ` grain: `2^(−30)`, the frames' (`|γ| ≤ 1`, so a value at most `2^30`).
pub(crate) const GAMMA_BITS: u32 = MOVE_BITS;

/// The turn's carrier bound: `2^34 + q²` (on `2^(−32)`) must stay under `2^78`, so `|q| < 2^39` on `2^(−16)` (read first, so `q²` is
/// formed only within 128 bits).
pub(crate) const CARRY_TURN_BOUND: i128 = 1 << 78;

pub(crate) const CARRY_TURN_ROOT: u128 = 1 << 39;

/// The friction's carrier bound: `d` (on `2^(−16)`) must stay under `2^47`.
pub(crate) const CARRY_FRICTION_BOUND: i128 = 1 << 47;

/// [definition; theory, November 11 19:56, G85, and November 12, G96's third branch] **A circle's founded friction** `d₀ = 1/(NEAR − 2)` on the
/// face's grain (`2^14` on `2^(−16)`): the leak's log chart reads `d = d₀ 2^ℓ` ([`carry_friction`]), so a circle founded at `ℓ = 0` has `d = 1/4`
/// and `|γ| = 4/5` at every site, the group `N = (1 + d)/d` founded at `NEAR − 1` places, the near field's reach a tick on one side
/// ([`Declaration::carry`]).
pub const CARRY_LEAK_FOUNDING: i32 = ((1usize << FACE_BITS) / (NEAR - 2)) as i32;

// The leak's return forms `δd ln 2 · d₀ · v` with `v` released to 47 bits: under `2^65 · 2^14 · 2^47 = 2^126` while `d₀` stays within `2^14`.
const _: () = assert!(CARRY_LEAK_FOUNDING <= 1 << 14 && CARRY_LEAK_FOUNDING > 0);

/// [definition; theory, November 12, G98; `CarryGate.lean`, `coupling_leak_zero`] **A circle's founded group** `N₀ = (1 + d₀)/d₀ = NEAR − 1`
/// places: the charge a circle founded at `d₀` holds under a constant drive, and the level its drive charges it toward at every friction
/// ([`carry_coupling`]).
pub const CARRY_GROUP_FOUNDING: i32 = (NEAR - 1) as i32;

// `N₀ d₀ = 1 + d₀` on the face's grain, so the coupling is one at the founding and a founded circle's forward is the sum form's bit for bit.
const _: () = assert!((1i64 << FACE_BITS) + CARRY_LEAK_FOUNDING as i64 == CARRY_GROUP_FOUNDING as i64 * CARRY_LEAK_FOUNDING as i64);

/// [definition; theory, November 12, G98 (G97 (f)'s carrier); `CarryGate.lean`, `coupling`, `charge_step_le`, `charge_le`] **The drive is charged
/// through the leak**: a circle's charge is `Q(t) = γ(t) Qm(t) + κ(t) b(t)` with the coupling `κ = N₀ d/(1 + d)` ([`CARRY_GROUP_FOUNDING`]), the
/// friction `d` the gate's ([`carry_friction`]), on `2^(−30)` from `d` on `2^(−16)` by one division to the nearest:
/// `κ = (N₀ d) 2^30 / (2^16 + d)`, under `N₀ 2^30`. Why: `|γ| + κ/N₀ = 1/(1 + d) + d/(1 + d) = 1`, so the move is the implicit step of a
/// dissipation that relaxes the turned charge toward the level `N₀ b` (a capacitor charged through the resistor it leaks by), never toward zero
/// with the drive added on top; the charge is a turned mean of `N₀ b` and stays within `N₀ max |b|` at every friction and every run of sites
/// (`charge_le`), where the sum form's grew with its group, to `2^16 + 1` places at the friction's floor (G97 scored: at the six bursts a
/// circle's largest charge stood at 2.6 to 20 times the median section's, at the refused section 54 times). At the founding `κ = 2^30` (`N₀ d₀ = 1 + d₀`), so `release(κ b, 30) = b`: a founded circle is the sum form's bit
/// for bit, and `C = 0` is the plain line's.
pub(crate) fn carry_coupling(d: i128) -> i128 {
    div_nearest((i128::from(CARRY_GROUP_FOUNDING) * d) << GAMMA_BITS, (1i128 << FACE_BITS) + d)
}

/// The drive coupled through the leak, `release(κ b, 30)` ([`carry_coupling`]), refused past 64 bits.
pub(crate) fn carry_drive(kappa: i128, b: i64) -> Result<i64> {
    fit64(release(kappa * i128::from(b), GAMMA_BITS))
}

/// [definition; theory, November 12, G96's third branch; `CarryGate.lean`, `leak`] **The leak's log chart**: from `ℓ` on `2^(−16)` (a site's leak
/// read), the friction `d = d₀ 2^ℓ` on `2^(−16)`, `d₀` the founded friction ([`CARRY_LEAK_FOUNDING`]). `2^ℓ` is read through the field's exponential
/// navigator as [`Constitution::face`] reads a score's term, `2^ℓ = v 2^(a − 61)` with `a = ⌊ℓ⌋` and `v` in `[2^61, 2^62)`, and the friction is that face
/// released to the face's grain, at least one grain: `d = max(1, release(d₀ v, 61 − a))`. A friction is never released to zero by its chart, as a
/// class is never released to zero mass by its exponent ([`Exponential::below_one`]): a circle's quality is finite (atlas `store.finite-quality`),
/// at most `2^16 + 1` places. Refused, typed, where `d` reaches `2^47` (the friction's carrier). Returns `d` and the chart's face `(a, v)`, at which
/// the gate's return reads the chart's derivative ([`carry_gate_return`]).
pub(crate) fn carry_friction(exponential: &Exponential, l: i128) -> Result<(i128, i64, u128)> {
    let l = fit64(l)?;
    let whole = l >> FACE_BITS;
    // Past `a = 61` the friction is past `2^47` whatever its fraction (`d₀ ≥ 1`): refused before the shift.
    if whole > 61 {
        return refuse("a carry circle's turn or friction past its 128-bit carrier");
    }
    let v = exponential.below_one(i128::from(l & ((1 << FACE_BITS) - 1)) - (1i128 << FACE_BITS));
    // `d₀ v < 2^76`: a release by more than 77 bits leaves nothing, and the floor keeps one grain.
    let shift = 61 - whole;
    let d = if shift > 77 { 0 } else { release(i128::from(CARRY_LEAK_FOUNDING) * v as i128, shift as u32) };
    let d = d.max(1);
    if d >= CARRY_FRICTION_BOUND {
        return refuse("a carry circle's turn or friction past its 128-bit carrier");
    }
    Ok((d, whole, v))
}

/// [definition; theory, November 13, the junction record §7] **The return's reflection on its log chart** ([`Declaration::junction`]): from
/// `ℓ` on `2^(−16)` (a site's junction read), `ρ = 2^ℓ` read through the field's exponential navigator as the carry's leak reads it
/// ([`carry_friction`]: `a = ⌊ℓ⌋` and `v` in `[2^61, 2^62)`, so `ρ = v 2^(a − 61)`), and `Γ = (ρ − 1)/(ρ + 1)` on `2^(−30)` by one division to the
/// nearest: `(v 2^a − 2^61)/(v 2^a + 2^61)` for `a ≥ 0`, `(v − 2^(61 − a))/(v + 2^(61 − a))` below. At `ℓ = 0`, `v = 2^61` and `Γ = 0`: the matched
/// load. Refused, typed, where `a` leaves `[−31, 30]`: past it `1 − |Γ|` falls under the grain and the reflection rounds to one, a store with no
/// loss (atlas `store.finite-quality`); inside it every numerator stays under `2^92` before its shift of 30. Returns `Γ`.
pub(crate) fn junction_gamma(exponential: &Exponential, l: i64) -> Result<i64> {
    let whole = l >> FACE_BITS;
    if !(JUNCTION_WHOLE_FLOOR..=JUNCTION_WHOLE_TOP).contains(&whole) {
        return refuse("a junction's return whose reflection reaches one at its grain");
    }
    let v = exponential.below_one(i128::from(l & ((1 << FACE_BITS) - 1)) - (1i128 << FACE_BITS)) as i128;
    let (num, den) = if whole >= 0 { ((v << whole) - (1i128 << 61), (v << whole) + (1i128 << 61)) } else { (v - (1i128 << (61 - whole)), v + (1i128 << (61 - whole))) };
    fit64(div_nearest(num << GAMMA_BITS, den))
}

/// The return's chart's whole part, `⌊ℓ⌋`, admitted from `−31` to `30` ([`junction_gamma`]).
pub(crate) const JUNCTION_WHOLE_FLOOR: i64 = -31;

pub(crate) const JUNCTION_WHOLE_TOP: i64 = 30;

/// [definition; theory, November 13, the junction record §7] **The return's sensitivity** `∂Γ/∂ℓ = (ln 2/2)(1 − Γ²)` on `2^(−30)`:
/// `release(ln 2 · (2^60 − Γ²), 61)` with `ln 2` on `2^(−30)` ([`ln2_face`]) and `Γ` on `2^(−30)`, at most `ln 2/2`.
pub(crate) fn junction_sensitivity(gamma: i64) -> i128 {
    let g = i128::from(gamma);
    release(ln2_face() * ((1i128 << (2 * GAMMA_BITS)) - g * g), 2 * GAMMA_BITS + 1)
}

/// [definition; theory, November 13, the junction record §7] **The return's covector at one site**: from the covector `λ` of the state the return
/// formed (`x^(k+1)`, on the covector's grain), the difference `Δ = v^k − x^(k−1)` it carried and its `Γ`: the chart's `δℓ = release(S c, 46)` with
/// `S = Σ_i λ_i Δ_i` and `c` the sensitivity ([`junction_sensitivity`]), so `δℓ` is `ℓ`'s covector on `2^(−16)` at the covector's grain (`Γ` on
/// `2^(−30)` moves `x` by `Γ Δ 2^(−30)`, and `ℓ` on `2^(−16)` moves `Γ` by `c 2^(−16)`); and `r = release(Γ λ, 30)` an entry, so the output's
/// covector is `λ + r` (`(1 + Γ) λ`) and the state two ticks back takes `−r`. Refused, typed, where `S` or `S c` passes its carrier.
pub(crate) fn junction_return(lambda: &[i64], diff: &[i64], gamma: i64) -> Result<(i64, Vec<i64>)> {
    let mut sum = 0i128;
    for (&y, &x) in lambda.iter().zip(diff) {
        sum = sum.checked_add(i128::from(y) * i128::from(x)).ok_or(TowerError::Refused(JUNCTION_RETURN))?;
    }
    let dl = fit64(release(sum.checked_mul(junction_sensitivity(gamma)).ok_or(TowerError::Refused(JUNCTION_RETURN))?, GAMMA_BITS + FACE_BITS))?;
    let g = i128::from(gamma);
    let r = lambda.iter().map(|&y| fit64(release(g * i128::from(y), GAMMA_BITS))).collect::<Result<Vec<_>>>()?;
    Ok((dl, r))
}

pub(crate) const JUNCTION_RETURN: &str = "a junction's return covector past its 128-bit carrier";

/// [definition; theory, November 11 17:25 and November 12 (G96's third branch); `lean/Holonics/HNN/CarryGate.lean`] **The carry's gate, a turn and a
/// friction charted apart** ([`Declaration::carry`]): from `q` and `ℓ` on `2^(−16)` (a site's turn and leak charts), the friction `d` on the
/// leak's log chart ([`carry_friction`]), and on `2^(−30)`, each part by one division to the nearest ([`div_nearest`], the card's own rounding),
///
/// ```text
/// den = (2^34 + q²)(2^16 + d),   γ_re = (2^34 − q²) 2^46 / den,   γ_im = q 2^64 / den,
/// ```
///
/// which is `γ = γ̂(q)/(1 + d)` with `γ̂(q) = ((4 − q²) + 4iq)/(4 + q²)` read at `q 2^(−16)` and `d 2^(−16)` (`carryGate`): the Cayley step of `iq/2`
/// on one circle (`carryTurn_eq_cayley`) over the implicit step of a pure dissipation. Refused, typed, where `2^34 + q²` reaches `2^78` or `d`
/// reaches `2^47`; below those every numerator and the denominator stay within 128 bits (`den < 2^125`). At `q = ℓ = 0` the gate is
/// `(858,993,459, 0)`, `2^32/5` to the nearest: a turn without work at the founded friction, `|γ| = 4/5`. Returns `(γ_re, γ_im)` and `d`.
pub(crate) fn carry_gate(exponential: &Exponential, q: i128, l: i128) -> Result<((i64, i64), i128)> {
    if q.unsigned_abs() >= CARRY_TURN_ROOT || (1i128 << 34) + q * q >= CARRY_TURN_BOUND {
        return refuse("a carry circle's turn or friction past its 128-bit carrier");
    }
    let (d, _, _) = carry_friction(exponential, l)?;
    let turn = (1i128 << 34) + q * q;
    let den = turn * ((1i128 << 16) + d);
    let re = div_nearest(((1i128 << 34) - q * q) << 46, den);
    let im = div_nearest(q << 64, den);
    Ok(((fit64(re)?, fit64(im)?), d))
}

/// [definition; theory, November 11 17:25 and November 12 (G96's third branch, G98); `CarryGate.lean`, `carryTurn_re_hasDerivAt`,
/// `carryTurn_im_hasDerivAt`, `friction_hasDerivAt`, `leak_hasDerivAt`, `coupling_hasDerivAt`] **The gate's and the coupling's covectors**:
/// from `δγ` (on its covector's grain, each part within 64 bits as the scan's reverse writes it), the covector `u` of the circle's charge at the
/// site (`δQ(t)`, on the same grain), the drive `b` the pair's affine produced (before its coupling) and the producing `γ`, `q`, `ℓ`:
/// `im = Im(conj(γ) δγ)` and `re = Re(conj(γ) δγ)`, each one release from `2^(−30)` to `δγ`'s grain; `δq = (4/(4 + q²)) im = im 2^34 / (2^34 + q²)`;
/// the friction's two covectors at the friction the forward applied, the gate's `δd = −re/(1 + d) = −re 2^16 / (2^16 + d)` and the coupling's
/// `δd_κ = N₀ Re(conj(b) u)/(1 + d)² = N₀ w 2^32 / (2^16 + d)²` with `w = Re(conj(b) u)` released from the face's grain to the covector's, each
/// one division to the nearest (`δd_κ` within 64 bits); then each lifted through the leak chart's derivative at the producing `ℓ`,
/// `ln 2 · d₀ 2^ℓ · δd` read at the chart's face ([`carry_friction`]'s `(a, v)`, `v` released to 47 bits):
/// `release(release(δd ln 2, 30) · d₀ · release(v, 15), 62 − a)`, the two added into `δℓ`. Both stand at every read and both read the chart's own
/// derivative (where the friction keeps its floor of one grain, `2^ℓ` smaller than the floor's). The drive's own covector is `δb = κ u`, each
/// part `release(κ u, 30)`. Returns `(δq, δℓ)` and `δb`. Why: `∂γ/∂q = i γ 4/(4 + q²)`, `∂γ/∂d = −γ/(1 + d)`, `∂κ/∂d = N₀/(1 + d)²` and
/// `∂d/∂ℓ = ln 2 · d`, so `δq = Re(conj(δγ) ∂γ/∂q) = (4/(4 + q²)) Im(conj(γ) δγ)`, `δℓ = ln 2 · d · (δd + δd_κ)` with
/// `δd = −Re(conj(γ) δγ)/(1 + d)` and `δd_κ = Re(conj(u) b) ∂κ/∂d`, and `∂Q/∂b = κ` (real).
pub(crate) fn carry_gate_return(exponential: &Exponential, gamma: (i64, i64), dgamma: (i64, i64), drive: (i64, i64), du: (i64, i64), q: i128, l: i128) -> Result<((i64, i64), (i64, i64))> {
    let ((yr, yi), (dr, di)) = ((i128::from(gamma.0), i128::from(gamma.1)), (i128::from(dgamma.0), i128::from(dgamma.1)));
    // `|γ| ≤ 2^30` and `δγ` within 64 bits: each product under `2^94`, `im` and `re` under `2^65`, so `im 2^34` and `re 2^16` fit.
    let im = release(yr * di - yi * dr, GAMMA_BITS);
    let re = release(yr * dr + yi * di, GAMMA_BITS);
    let dq = div_nearest(im << 34, (1i128 << 34) + q * q);
    let (d, whole, v) = carry_friction(exponential, l)?;
    let one = (1i128 << FACE_BITS) + d;
    let dd = -div_nearest(re << 16, one);
    // `w` within 64 bits, so `N₀ w 2^32` stays under `2^99`, and `(2^16 + d)² < 2^95`.
    let w = fit64(release(i128::from(drive.0) * i128::from(du.0) + i128::from(drive.1) * i128::from(du.1), FACE_BITS))?;
    let ddk = fit64(div_nearest((i128::from(CARRY_GROUP_FOUNDING) * i128::from(w)) << (2 * FACE_BITS), one * one))?;
    // `|δd| ≤ |re| < 2^65` (and `δd_κ` within 64 bits) and `ln 2 < 2^30`, so `δd ln 2 < 2^95`, released to under `2^65`; `d₀ ≤ 2^14`; and `v` on
    // `2^(−62)` released 15 bits, to under `2^47` (`2^ℓ = v′ 2^(a − 46)`): the product stays under `2^126`. A shift past 126 leaves nothing (`a`
    // far below zero, where the chart's derivative is under one grain of the covector).
    let shift = 62 - whole;
    let lift = |x: i128| -> i128 {
        let product = release(x * ln2_face(), LN2_FACE_BITS) * i128::from(CARRY_LEAK_FOUNDING) * release(v as i128, 15);
        if shift > 126 { 0 } else { release(product, shift as u32) }
    };
    let dl = lift(dd) + lift(i128::from(ddk));
    let kappa = carry_coupling(d);
    Ok(((fit64(dq)?, fit64(dl)?), (carry_drive(kappa, du.0)?, carry_drive(kappa, du.1)?)))
}

/// The pump's chart's bound: each part of `p` (on `2^(−16)`) under `2^39`, as the turn's chart is bounded ([`CARRY_TURN_ROOT`]), so the leak's
/// budget `n = |p_re| + |p_im|` stays under `2^40` and `2^16 + d + n` under `2^48`.
pub(crate) const CARRY_PUMP_ROOT: u128 = 1 << 39;

/// [definition; the lead, November 19 (G-1119-7); `CarryGate.lean`, `pumped_charge_step_le`] **The pumped circle's gate** ([`Declaration::pump`]):
/// from `q`, `ℓ` and the pump's chart `p = (p_re, p_im)` on `2^(−16)`, the friction `d` on the leak's log chart ([`carry_friction`]) and the pump's
/// budget `n = |p_re| + |p_im|`, with `one = 2^16 + d + n` and `den = (2^34 + q²) one`, on `2^(−30)` each by one division to the nearest:
///
/// ```text
/// γ_re = (2^34 − q²) 2^46 / den,   γ_im = q 2^64 / den,   η = p 2^30 / one,   κ = (N₀ d) 2^30 / one,
/// ```
///
/// which is `γ = γ̂(q)/(1 + d + n)`, `η = p/(1 + d + n)` and `κ = N₀ d/(1 + d + n)`, so `|γ| + |η| + κ/N₀ ≤ (1 + n + d)/(1 + d + n) = 1`. At `p = 0`,
/// `n = 0` and every term is [`carry_gate`]'s and [`carry_coupling`]'s in integers. Refused, typed, where the turn's chart refuses
/// ([`carry_gate`]), where a part of `p` reaches `2^39`, or where the friction's chart refuses. Returns `(γ_re, γ_im)`, `(η_re, η_im)`, `d`, `n`
/// and `κ`.
#[allow(clippy::type_complexity)]
pub(crate) fn carry_gate_pumped(exponential: &Exponential, q: i128, l: i128, p: (i128, i128)) -> Result<((i64, i64), (i64, i64), i128, i128, i128)> {
    if q.unsigned_abs() >= CARRY_TURN_ROOT || (1i128 << 34) + q * q >= CARRY_TURN_BOUND {
        return refuse("a carry circle's turn or friction past its 128-bit carrier");
    }
    if p.0.unsigned_abs() >= CARRY_PUMP_ROOT || p.1.unsigned_abs() >= CARRY_PUMP_ROOT {
        return refuse("a carry circle's pump past its carrier");
    }
    let (d, _, _) = carry_friction(exponential, l)?;
    let n = p.0.abs() + p.1.abs();
    let one = (1i128 << FACE_BITS) + d + n;
    let turn = (1i128 << 34) + q * q;
    let den = turn * one;
    let re = div_nearest(((1i128 << 34) - q * q) << 46, den);
    let im = div_nearest(q << 64, den);
    let eta = (div_nearest(p.0 << GAMMA_BITS, one), div_nearest(p.1 << GAMMA_BITS, one));
    let kappa = div_nearest((i128::from(CARRY_GROUP_FOUNDING) * d) << GAMMA_BITS, one);
    Ok(((fit64(re)?, fit64(im)?), (fit64(eta.0)?, fit64(eta.1)?), d, n, kappa))
}

/// [definition; the lead, November 19 (G-1119-7)] **The pumped gate's covectors** ([`carry_gate_pumped`]): from `δγ = conj(Qm) u` and `δη = u Qm`
/// (each on the covector's grain, as the scan's reverse writes them), the drive `b` before its coupling, the covector `u` of the circle's charge,
/// the producing `γ`, `η`, `q`, `ℓ` and `p`: `re = Re(conj(γ) δγ) + Re(conj(η) δη)` and `im = Im(conj(γ) δγ)`, each part one release from
/// `2^(−30)`; `δq = im 2^34 / (2^34 + q²)`; with `one = 2^16 + d + n`, the friction's covectors `δd = −re 2^16 / one` and
/// `δd_κ = N₀ w (2^16 + n) 2^16 / one²` (`w = Re(conj(b) u)` released from the face's grain), lifted into `δℓ` through the leak chart's
/// derivative as [`carry_gate_return`] lifts them; the budget's covector `δn = δd + δn_κ` with `δn_κ = −(N₀ w 2^16 / one) d / one`, two
/// divisions to the nearest; and the pump's `δp = δη 2^16 / one + sgn(p) δn`, each part (`sgn 0 = 0`). The drive's covector is `δb = κ u`.
/// Returns `(δq, δℓ)`, `(δp_re, δp_im)` and `δb`. At `p = 0` (so `η = 0`, `δη`'s pairing zero and `n = 0`), `δq`, `δℓ` and `δb` are
/// [`carry_gate_return`]'s in integers. Why: `∂γ/∂d = ∂γ/∂n = −γ/(1 + d + n)`, `∂η/∂d = ∂η/∂n = −η/(1 + d + n)`, `∂η/∂p = 1/(1 + d + n)`,
/// `∂κ/∂d = N₀ (1 + n)/(1 + d + n)²`, `∂κ/∂n = −N₀ d/(1 + d + n)²` and `∂n/∂p_re = sgn(p_re)`; `Q = γ Qm + η conj(Qm) + κ b` gives `∂Q/∂γ = Qm`
/// (read through `conj`) and `∂Q/∂η = conj(Qm)`, so `η`'s covector is `u Qm`.
#[allow(clippy::too_many_arguments, clippy::type_complexity)]
pub(crate) fn carry_gate_return_pumped(exponential: &Exponential, gamma: (i64, i64), dgamma: (i64, i64), eta: (i64, i64), deta: (i64, i64), drive: (i64, i64), du: (i64, i64), q: i128, l: i128, p: (i128, i128)) -> Result<((i64, i64), (i64, i64), (i64, i64))> {
    let ((yr, yi), (dr, di)) = ((i128::from(gamma.0), i128::from(gamma.1)), (i128::from(dgamma.0), i128::from(dgamma.1)));
    let ((er, ei), (fr, fi)) = ((i128::from(eta.0), i128::from(eta.1)), (i128::from(deta.0), i128::from(deta.1)));
    let im = release(yr * di - yi * dr, GAMMA_BITS);
    let re = release(yr * dr + yi * di, GAMMA_BITS) + release(er * fr + ei * fi, GAMMA_BITS);
    let dq = div_nearest(im << 34, (1i128 << 34) + q * q);
    let (d, whole, v) = carry_friction(exponential, l)?;
    let n = p.0.abs() + p.1.abs();
    let one = (1i128 << FACE_BITS) + d + n;
    let dd = -div_nearest(re << 16, one);
    let w = fit64(release(i128::from(drive.0) * i128::from(du.0) + i128::from(drive.1) * i128::from(du.1), FACE_BITS))?;
    let nw = i128::from(CARRY_GROUP_FOUNDING) * i128::from(w);
    // `N₀ w < 2^67` and `2^16 + n < 2^41`: the product under `2^108`, shifted 16 under `2^124`; `one² < 2^96`.
    let ddk = fit64(div_nearest((nw * ((1i128 << FACE_BITS) + n)) << FACE_BITS, one * one))?;
    let shift = 62 - whole;
    let lift = |x: i128| -> i128 {
        let product = release(x * ln2_face(), LN2_FACE_BITS) * i128::from(CARRY_LEAK_FOUNDING) * release(v as i128, 15);
        if shift > 126 { 0 } else { release(product, shift as u32) }
    };
    let dl = lift(dd) + lift(i128::from(ddk));
    // `|N₀ w 2^16 / one| ≤ N₀ w`, and its product with `d` stays under `N₀ w 2^16 < 2^83` (`d < one`).
    let m = div_nearest(nw << FACE_BITS, one);
    let dn = dd - div_nearest(m * d, one);
    let dp = |f: i128, part: i128| -> Result<i64> { fit64(div_nearest(f << FACE_BITS, one) + part.signum() * dn) };
    let kappa = div_nearest((i128::from(CARRY_GROUP_FOUNDING) * d) << GAMMA_BITS, one);
    Ok(((fit64(dq)?, fit64(dl)?), (dp(fr, p.0)?, dp(fi, p.1)?), (carry_drive(kappa, du.0)?, carry_drive(kappa, du.1)?)))
}

/// [definition; theory, November 12, the triad record §3 and §4] **The triads' products** ([`Declaration::triads`]): from the charts' reads
/// `abg` (`[t][6J]` on `2^(−16)`: `α`'s real parts, then imaginary, then `β`'s, then `γ`'s), at each site with both strand mates in the region
/// (`1 ≤ t ≤ sites − 2`) and each triad `k`,
///
/// ```text
/// p = release(α_k(t) β_k(t − 1), 16),   c^T = release(p γ_k(t + 1), 16),
/// ```
///
/// each a complex product as the plain contact forms it (`re = a_r b_r − a_i b_i`, `im = a_r b_i + a_i b_r`) and fitted to 64 bits as its `c` is;
/// `p` and `c^T` are zero at the region's first and last sites, where a mate is missing. Returns `(p, c^T)`, each `[t][2J]`, real parts then
/// imaginary. Why two releases: the triad is the plain contact with one operand more, a word of two contacts through the place, and each contact
/// of the word is released at the face's grain as a plain contact is; each product is one site's, so no sum is formed and no order chosen, and
/// the card's per-site products give the same bits.
///
/// [definition; theory, November 16 19:10Z, [`Declaration::crossing`]] With `crossing` the three legs stand at the site, `p = α_k(t) β_k(t)` and
/// `c^T = p γ_k(t)`, at every site of the region; each product is still one site's, so nothing is summed and no order chosen.
pub(crate) fn triad_products(triads: usize, sites: usize, abg: &[i64], crossing: bool) -> Result<(Vec<i64>, Vec<i64>)> {
    let (j2, j6) = (2 * triads, 6 * triads);
    let (mut p, mut c) = (vec![0i64; sites * j2], vec![0i64; sites * j2]);
    let (from, to) = if crossing { (0, sites) } else { (1, sites.saturating_sub(1)) };
    for t in from..to {
        let (tb, tg) = if crossing { (t, t) } else { (t - 1, t + 1) };
        for k in 0..triads {
            let (ar, ai) = (i128::from(abg[t * j6 + k]), i128::from(abg[t * j6 + triads + k]));
            let (br, bi) = (i128::from(abg[tb * j6 + j2 + k]), i128::from(abg[tb * j6 + j2 + triads + k]));
            let (gr, gi) = (i128::from(abg[tg * j6 + 2 * j2 + k]), i128::from(abg[tg * j6 + 2 * j2 + triads + k]));
            let (pr, pi) = (fit64(release(ar * br - ai * bi, FACE_BITS))?, fit64(release(ar * bi + ai * br, FACE_BITS))?);
            (p[t * j2 + k], p[t * j2 + triads + k]) = (pr, pi);
            let (pr, pi) = (i128::from(pr), i128::from(pi));
            c[t * j2 + k] = fit64(release(pr * gr - pi * gi, FACE_BITS))?;
            c[t * j2 + triads + k] = fit64(release(pr * gi + pi * gr, FACE_BITS))?;
        }
    }
    Ok((p, c))
}

/// [definition; theory, November 12, the triad record §4] **The triads' reverse**, by the product rule through the producing operands: with
/// `u = δc^T_k(t)` (`dct`, `[t][2J]` on the covector's grain) at each site with both strand mates and each triad `k`,
///
/// ```text
/// δγ_k(t + 1) = release(conj(p) u, 16),   δp = release(conj(γ_k(t + 1)) u, 16),
/// δα_k(t) = release(conj(β_k(t − 1)) δp, 16),   δβ_k(t − 1) = release(conj(α_k(t)) δp, 16),
/// ```
///
/// with `conj(z) u` as the plain contact's `δa` forms it (`re = z_r u_r + z_i u_i`, `im = z_r u_i − z_i u_r`), each fitted to 64 bits. Returns
/// `δ(α, β, γ)`, `[t][6J]` as `abg` is laid. Each site's `α` is read by its own place alone, its `β` by the place after it and its `γ` by the place
/// before it, so each slot is written by one place: nothing is summed and no order is chosen. `δα` is zero at the region's two ends, `δβ` at its
/// last two sites and `δγ` at its first two.
///
/// [definition; theory, November 16 19:10Z, [`Declaration::crossing`]] With `crossing` every leg is the site's own and every site has them: each of the
/// site's three slots is still written by one place, its own.
pub(crate) fn triad_back(triads: usize, sites: usize, abg: &[i64], p: &[i64], dct: &[i64], crossing: bool) -> Result<Vec<i64>> {
    let (j2, j6) = (2 * triads, 6 * triads);
    let mut out = vec![0i64; sites * j6];
    let conj = |(zr, zi): (i128, i128), (ur, ui): (i128, i128)| -> Result<(i64, i64)> { Ok((fit64(release(zr * ur + zi * ui, FACE_BITS))?, fit64(release(zr * ui - zi * ur, FACE_BITS))?)) };
    let (from, to) = if crossing { (0, sites) } else { (1, sites.saturating_sub(1)) };
    for t in from..to {
        let (tb, tg) = if crossing { (t, t) } else { (t - 1, t + 1) };
        for k in 0..triads {
            let u = (i128::from(dct[t * j2 + k]), i128::from(dct[t * j2 + triads + k]));
            let pt = (i128::from(p[t * j2 + k]), i128::from(p[t * j2 + triads + k]));
            let alpha = (i128::from(abg[t * j6 + k]), i128::from(abg[t * j6 + triads + k]));
            let beta = (i128::from(abg[tb * j6 + j2 + k]), i128::from(abg[tb * j6 + j2 + triads + k]));
            let gamma = (i128::from(abg[tg * j6 + 2 * j2 + k]), i128::from(abg[tg * j6 + 2 * j2 + triads + k]));
            let dgamma = conj(pt, u)?;
            let (dpr, dpi) = conj(gamma, u)?;
            let dp = (i128::from(dpr), i128::from(dpi));
            let dalpha = conj(beta, dp)?;
            let dbeta = conj(alpha, dp)?;
            (out[tg * j6 + 2 * j2 + k], out[tg * j6 + 2 * j2 + triads + k]) = dgamma;
            (out[t * j6 + k], out[t * j6 + triads + k]) = dalpha;
            (out[tb * j6 + j2 + k], out[tb * j6 + j2 + triads + k]) = dbeta;
        }
    }
    Ok(out)
}

/// [definition; theory, November 12, the triad record §3 and §4] **The pair's return with the triads' beside it, one sum released once**:
/// `out[o] = release(Σ_i w[o·cols + i] x[i] + Σ_j wt[o·cols_t + j] xt[j] + bias[o] 2^bias_shift, shift)`, `W c + W_T c^T + b_c` at a site. The
/// carrier bound and its refusal are read over both blocks together, as the sum of each block's bound as [`affine`] reads it
/// (`max|w| max|x| (cols + 1)`), refused at `2^126`; the sum runs in `i64` only where that joint bound is under `2^62`, and the integer is the
/// same either way. Why one sum: a release per block would round twice where the law rounds once, and the card sums both blocks whole with
/// the bias before its one release, so host and card release the same sum (integer addition being associative, any order of its terms gives
/// the same bits). At `J = 0` the forward calls [`affine`] itself, so every bit is as before.
#[allow(clippy::too_many_arguments)]
pub(crate) fn affine_joint(w: &[i32], wmax: u64, cols: usize, x: &[i64], wt: &[i32], wtmax: u64, cols_t: usize, xt: &[i64], bias: &[i32], bias_shift: u32, shift: u32, out: &mut [i64]) -> Result<()> {
    let bound = |wmax: u64, x: &[i64], cols: usize| (wmax as u128) * (x.iter().map(|v| v.unsigned_abs()).max().unwrap_or(0) as u128) * (cols as u128 + 1);
    let terms = bound(wmax, x, cols).saturating_add(bound(wtmax, xt, cols_t));
    if terms >= 1u128 << 126 {
        return refuse("an affine sum outgrew its 128-bit carrier");
    }
    let narrow = terms < (1u128 << 62);
    for (o, slot) in out.iter_mut().enumerate() {
        let (row, row_t) = (&w[o * cols..(o + 1) * cols], &wt[o * cols_t..(o + 1) * cols_t]);
        let mut sum: i128 = if narrow {
            (row.iter().zip(x).map(|(a, &b)| *a as i64 * b).sum::<i64>() + row_t.iter().zip(xt).map(|(a, &b)| *a as i64 * b).sum::<i64>()) as i128
        } else {
            row.iter().zip(x).map(|(a, &b)| *a as i128 * b as i128).sum::<i128>() + row_t.iter().zip(xt).map(|(a, &b)| *a as i128 * b as i128).sum::<i128>()
        };
        sum += (bias[o] as i128) << bias_shift;
        *slot = fit64(release(sum, shift))?;
    }
    Ok(())
}

impl Constitution {

    /// Site `s`'s row of a family at `base` of `width` a class (its class's row, or its carried face's mixture
    /// `release(Σ_a w_a E(a), 16)`; zero at a silent site, [`Constitution::silent`]).
    pub(crate) fn strand_row(&self, region: &Region, base: usize, width: usize, s: usize) -> Vec<i64> {
        if Self::silent(region, s) {
            return vec![0; width];
        }
        match Self::carried(region, s) {
            None => self.theta[base + self.row(region, s) * width..base + (self.row(region, s) + 1) * width].iter().map(|&e| e as i64).collect(),
            Some(face) => (0..width).map(|i| release(face.iter().map(|&(c, w)| w as i128 * self.theta[base + c as usize * width + i] as i128).sum(), STATE_BITS) as i64).collect(),
        }
    }

    /// A strand row's return: `d` (on `2^(−24)`) into site `s`'s row, or each carried class's row by
    /// its share; nothing at a silent site.
    pub(crate) fn strand_return(&self, region: &Region, base: usize, width: usize, s: usize, d: &[i128], g: &mut [i128]) {
        if Self::silent(region, s) {
            return;
        }
        match Self::carried(region, s) {
            None => {
                let start = base + self.row(region, s) * width;
                for i in 0..width {
                    g[start + i] += d[i];
                }
            }
            Some(face) => {
                for &(c, w) in face {
                    for i in 0..width {
                        g[base + c as usize * width + i] += release(w as i128 * d[i], STATE_BITS);
                    }
                }
            }
        }
    }

    /// [definition; theory, November 13, the junction record §7] **The tick's return** ([`Declaration::junction`]), after a tick past the
    /// first: at each site the chart `ℓ = L r̂(x^k) + ℓ_b` (one affine of the tick's opening chart, at the grains the carry's leak is read at), the
    /// reflection `Γ` ([`junction_gamma`]) and `x^(k+1) = v^k + release(Γ (v^k − x^(k−1)), 30)` an entry, with `x` holding `v^k` and `prev` the
    /// state the tick before began from. The reads are kept in the cell for the reverse.
    pub(crate) fn junction_forward(&self, x: &mut [i64], prev: &[i64], reaches: &Reaches, cell: &mut TickCell) -> Result<()> {
        let (l, dw) = (&self.layout, self.declaration.width);
        let sites = x.len() / dw;
        (cell.jl, cell.jg, cell.jd) = (vec![0i64; sites], vec![0i64; sites], vec![0i64; sites * dw]);
        let mut ell = [0i64; 1];
        for t in 0..sites {
            affine(&self.theta[l.junction..l.junction + dw], reaches.junction, dw, &cell.read[t * dw..(t + 1) * dw], Some(&self.theta[l.junction_bias..l.junction_bias + 1]), MATERIAL_BITS, MATERIAL_BITS, &mut ell)?;
            let gamma = junction_gamma(&self.exponential, ell[0])?;
            (cell.jl[t], cell.jg[t]) = (ell[0], gamma);
            for i in t * dw..(t + 1) * dw {
                let diff = fit64(i128::from(x[i]) - i128::from(prev[i]))?;
                cell.jd[i] = diff;
                x[i] = fit64(i128::from(x[i]) + release(i128::from(gamma) * i128::from(diff), GAMMA_BITS))?;
            }
        }
        Ok(())
    }

    /// [definition; theory, November 13, the junction record §7] **The return's reverse at its output**: with `dx` the covector `λ^(k+1)` of the
    /// state the return formed, each site's chart covector `δℓ` and the output's covector `(1 + Γ) λ^(k+1)` written over `dx`
    /// ([`junction_return`]); returns `δℓ` (`[t]`) and what the state two ticks back takes, `−Γ λ^(k+1)` (`[t][D]`).
    pub(crate) fn junction_back(&self, cell: &TickCell, dx: &mut [i64]) -> Result<(Vec<i64>, Vec<i64>)> {
        let dw = self.declaration.width;
        let sites = dx.len() / dw;
        let (mut dl, mut back) = (vec![0i64; sites], vec![0i64; sites * dw]);
        for t in 0..sites {
            let span = t * dw..(t + 1) * dw;
            let (d, r) = junction_return(&dx[span.clone()], &cell.jd[span.clone()], cell.jg[t])?;
            dl[t] = d;
            for ((slot, o), &v) in dx[span.clone()].iter_mut().zip(&mut back[span]).zip(&r) {
                *slot = fit64(i128::from(*slot) + i128::from(v))?;
                *o = -v;
            }
        }
        Ok((dl, back))
    }

    /// [definition; theory, November 13, the junction record §7] **The return's chart's reverse**: `Σ_t δℓ_t r̂_tᵀ` into `L`, `Σ_t δℓ_t` into `ℓ_b`,
    /// and `Lᵀ δℓ_t` through the lane adjoint of the tick's opening chart into the covector of the state the tick began from.
    pub(crate) fn junction_chart_back(&self, cell: &TickCell, dl: &[i64], reaches: &Reaches, dx: &mut [i64], g: &mut [i128]) -> Result<()> {
        let (l, dw, lanes) = (&self.layout, self.declaration.width, self.declaration.lanes);
        let rs: Vec<&[i32]> = cell.read.chunks_exact(dw).collect();
        let dls: Vec<&[i64]> = dl.chunks_exact(1).collect();
        outer_sum(&mut g[l.junction..l.junction + dw], dw, &dls, &rs)?;
        let mut dr = vec![0i64; dw];
        for (t, &d) in dl.iter().enumerate() {
            g[l.junction_bias] += i128::from(d);
            transposed(&self.theta[l.junction..l.junction + dw], reaches.junction, dw, &dl[t..t + 1], MATERIAL_BITS, &mut dr)?;
            let back = lane_adjoint(rs[t], &cell.scale[t * lanes..(t + 1) * lanes], &dr)?;
            for (slot, &b) in dx[t * dw..(t + 1) * dw].iter_mut().zip(&back) {
                *slot = fit64(i128::from(*slot) + i128::from(b))?;
            }
        }
        Ok(())
    }
}

/// [definition; agent-inferred, November 3, §16.34] **A site's strand mate for pair contact `e`**: the site before it at an
/// even `e`, the one after at an odd, `None` past the region's ends. The parity survives growth by copies (a contact's copy
/// stands at `c · f/2 + e`, `f/2` even), so a grown merge reads the old one exactly.
pub fn strand_mate(t: usize, e: usize, sites: usize) -> Option<usize> {
    if e % 2 == 0 {
        t.checked_sub(1)
    } else {
        (t + 1 < sites).then_some(t + 1)
    }
}

impl Constitution {

    /// [measurement; theory, November 12, G90's first branch] **The carry circles' leaks and charges over a read pair chart**
    /// (`TickRead::pair_read`, `[t][D]`), from the forward's own arithmetic on the chart the realization read: at every site and carry circle
    /// the leak read `ℓ = L r̂ + ℓ_b` on `2^(−16)` (the `ℓ` of [`carry_gate`]), and the circle's charge after the site, `|Q(t)|` on `2^(−16)`
    /// (the floor of the square root of `Q_re² + Q_im²`), the scan run as the forward runs it ([`Declaration::carry`]): `Q(t) = κ(t) b(t) +
    /// release(γ(t) Q(t ∓ 1), 30)` with the drive coupled through the leak ([`carry_coupling`]), `Q` zero before the region's first site, even
    /// contacts from the left and odd from the right. Each `[t][C]`. Where `ℓ < 0` the friction stands below its founding (`d = d₀ 2^ℓ < d₀`), so
    /// a run of such sites along the strand carries the charge further than the near field, and its drive is admitted by as much less (the
    /// charge stays within `N₀` places' drive); deep below (`ℓ < −14`) the friction holds its floor of one grain, a circle's longest reach. A
    /// reading; a sum past its carrier is refused as the forward refuses it.
    pub fn carry_leaks(&self, pair_read: &[i32]) -> Result<(Vec<i64>, Vec<u64>)> {
        let d = &self.declaration;
        if d.carry == 0 {
            return refuse("a field without carry circles has no leak");
        }
        // [the lead, November 19] This ruler scans the unpumped move; a pumped circle's charge it would misread.
        if d.pump {
            return refuse("a reading of the carry's leaks on a field whose circles are pumped (the ruler scans the unpumped move)");
        }
        let (dw, f, circles) = (d.width, d.contacts, d.carry);
        let (half, plain, c2) = (f / 2, d.carry_first(), 2 * circles);
        let (l, reaches) = (&self.layout, self.reaches());
        let sites = pair_read.len() / dw;
        let mut qh = vec![0i64; c2];
        let mut b = vec![0i64; sites * f];
        let mut gam = vec![(0i64, 0i64); sites * circles];
        let mut leak = Vec::with_capacity(sites * circles);
        for (t, rt) in pair_read.chunks_exact(dw).enumerate() {
            affine(&self.theta[l.carry..l.carry + c2 * dw], reaches.carry, dw, rt, Some(&self.theta[l.carry_bias..l.carry_bias + c2]), MATERIAL_BITS, MATERIAL_BITS, &mut qh)?;
            affine(&self.theta[l.b..l.b + f * dw], reaches.b, dw, rt, Some(&self.theta[l.b_bias..l.b_bias + f]), MATERIAL_BITS, MATERIAL_BITS, &mut b[t * f..(t + 1) * f])?;
            for k in 0..circles {
                let (gate, friction) = carry_gate(&self.exponential, qh[k] as i128, qh[circles + k] as i128)?;
                gam[t * circles + k] = gate;
                leak.push(qh[circles + k]);
                let (kappa, e) = (carry_coupling(friction), plain + k);
                b[t * f + e] = carry_drive(kappa, b[t * f + e])?;
                b[t * f + half + e] = carry_drive(kappa, b[t * f + half + e])?;
            }
        }
        let mut charge = vec![0u64; sites * circles];
        for k in 0..circles {
            let e = plain + k;
            let (mut qr, mut qi) = (0i128, 0i128);
            for step in 0..sites {
                let t = if e % 2 == 0 { step } else { sites - 1 - step };
                let (yr, yi) = (i128::from(gam[t * circles + k].0), i128::from(gam[t * circles + k].1));
                let next_r = b[t * f + e] as i128 + release(yr * qr - yi * qi, GAMMA_BITS);
                let next_i = b[t * f + half + e] as i128 + release(yr * qi + yi * qr, GAMMA_BITS);
                (qr, qi) = (i128::from(fit64(next_r)?), i128::from(fit64(next_i)?));
                // Each part within 64 bits, so the square sum stays under 2^127.
                charge[t * circles + k] = ((qr * qr + qi * qi) as u128).isqrt() as u64;
            }
        }
        Ok((leak, charge))
    }

    /// [measurement; theory, November 11 18:33, part P2] **The carry circles' gates over a region's open sites** ([`CarryGates`]): from the forward's
    /// own cells (every tick's gate and leak read, [`carry_gate`]), at each unresolved site and every tick, each circle's `|γ|` on `2^(−30)` (the
    /// floor of the square root of `γ_re² + γ_im²`) added into its sum, its `ℓ ≥ 0` counted (the friction at its founding or above), and the reads
    /// counted. A reading: the field is not changed and no other read is.
    pub fn carry_gates_of(&self, region: &Region) -> Result<CarryGates> {
        let circles = self.declaration.carry;
        let mut out = CarryGates::new(circles);
        if circles == 0 {
            return Ok(out);
        }
        let c2 = 2 * circles;
        let pass = self.pass(region, true)?;
        for cell in &pass.ticks {
            for t in (0..region.classes.len()).filter(|&t| region.unresolved[t]) {
                out.reads += 1;
                for k in 0..circles {
                    let (re, im) = (i128::from(cell.gam[t * c2 + k]), i128::from(cell.gam[t * c2 + circles + k]));
                    out.modulus[k] += ((re * re + im * im) as u128).isqrt();
                    out.friction[k] += u64::from(cell.qh[t * c2 + circles + k] >= 0);
                }
            }
        }
        Ok(out)
    }
}

/// [measurement; theory, November 11 18:33, part P2] **The carry circles' gates over a read's open sites** ([`Constitution::carry_gates_of`],
/// [`Realization::read_faces_gated`]): `reads` the (open site, tick) pairs read, and for each carry circle `k` the sum of `|γ|` on `2^(−30)`
/// over them and the count of them whose leak read `ℓ` stands at `0` or above (the friction at its founding or above, a reach of at most the near
/// field's). Integers; a mean is `modulus[k] / reads`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct CarryGates {
    pub reads: u64,
    pub modulus: Vec<u128>,
    pub friction: Vec<u64>,
}

impl CarryGates {
    pub fn new(circles: usize) -> Self {
        Self { reads: 0, modulus: vec![0; circles], friction: vec![0; circles] }
    }

    /// The sums of another read added in (the same circles).
    pub fn add(&mut self, other: &CarryGates) {
        self.reads += other.reads;
        for (a, b) in self.modulus.iter_mut().zip(&other.modulus) {
            *a += b;
        }
        for (a, b) in self.friction.iter_mut().zip(&other.friction) {
            *a += b;
        }
    }
}
