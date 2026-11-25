//! **Rings, clocks and paces: the navigators' phase.**
//!
//! a turned ring set's phasor `U_(t,m) = e^(2πi (t mod n_m)/n_m)` on the solenoid's periods; a still set `U = 1`; a skin
//! `D_m(d) = e^(−2πd/n_m)`; paced heads turn by located increments
//!
//! Kind: gate, a site. Kernels: `field_paces`, `field_skin_addresses`, `field_pframes`, `field_clock_fill`, `field_blank_*` (`hnn/clock.rs`).
//! Lean: `HNN/Ring`, `HNN/RingLoci`.
//! Atlas: `radix.face-width-from-readers`, `tower.field-one-region`, `tower.field-pace`, `tower.field-ring-face-route`,
//! `tower.field-temperature-log`.
//! Records: `2026-11-01_THE_FIELD_DISPERSES…`. The derivations' history is in the records; the items below keep their reasons.

#[allow(unused_imports)]
use crate::field::*;
#[allow(unused_imports)]
use rayon::prelude::*;

/// A prime's tower of closures from `p` to the first power that spans `reach` sites.
pub(crate) fn tower(p: usize, reach: usize) -> Vec<usize> {
    let mut out = vec![p];
    while let Some(&top) = out.last() {
        if top >= reach {
            break;
        }
        match top.checked_mul(p) {
            Some(next) => out.push(next),
            None => break,
        }
    }
    out
}

/// [definition; agent-inferred, November 1] **The turned slots' ring periods**: the solenoid's two
/// coprime towers, the dyadic `2, 4, 8, …` and the triadic `3, 9, 27, …`, each from its finest
/// closure to the first that spans the reach. A tower's ring `p^(k+1)` reads the residue of ring
/// `p^k` and its whole winding, so a tower read together is a place's residue and its windings at
/// every scale, and its top ring turns less than once across any region (a distance, not only a
/// residue). The slots take `⌈S/2⌉` rings of the dyadic tower and `⌊S/2⌋` of the triadic, each
/// spread evenly from the finest to the top (a lone slot takes the top; more slots than closures
/// cycle the tower), merged in ascending period. Slot `s` of [`Declaration::turned_slots`]
/// is turned ring set `still + s mod (frames − still)`'s local mode `s / (frames − still)`, so every
/// turned set spans fine to coarse. Two sites that agree modulo every ring are at least the top dyadic closure apart,
/// beyond the reach: no two sites of an admitted region share every frame.
///
/// (The prime powers `2, 3, 4, 5, 7, 8, …` of the first draft closed every ring within a few
/// tens of sites and aliased sites `lcm` apart, 840 for six rings: the review of November 1.)
pub fn ring_periods(slots: usize, reach: usize) -> Vec<usize> {
    let sample = |tower: &[usize], count: usize| -> Vec<usize> {
        (0..count)
            .map(|k| match count {
                1 => tower[tower.len() - 1],
                _ if count <= tower.len() => tower[k * (tower.len() - 1) / (count - 1)],
                _ => tower[k % tower.len()],
            })
            .collect()
    };
    let mut out = sample(&tower(2, reach), slots.div_ceil(2));
    out.extend(sample(&tower(3, reach), slots / 2));
    out.sort_unstable();
    out
}

/// [definition; agent-inferred, November 1] **The skin decay** `e^(−2π d/n)` on `2^(−30)` (the
/// dispersing field's §12): a diffusive medium carries spatial period `n` with one e-fold of decay a
/// radian of turn (`J ∝ e^(−(1+i)x/δ)`, the skin effect), read as `2^(−x)` with
/// `x = 2π d/(n ln 2)` bits on `2^(−16)` through the exponential's face on `2^(−62)` and released
/// to the frames' grain: `1` at `d = 0` exactly, and zero where it falls below the grain, so a fine
/// ring is heard only a few sites away.
pub(crate) fn skin_decay(d: usize, n: usize, pi: i128, exponential: &Exponential) -> i64 {
    skin_of((d as i128) << PACE_BITS, n, pi, exponential)
}

/// [definition; agent-inferred, November 2] **The skin across a turn's variation** `s` on `2^(−24)` (§16, Law 1):
/// `e^(−2π |s|/n)`, one e-fold a radian of turn, read as [`skin_decay`] reads a whole distance (the same bits at a
/// whole `s`), so a head whose clock is its own decays by the turn it makes between two sites, not by their bytes.
pub(crate) fn skin_of(s: i128, n: usize, pi: i128, exponential: &Exponential) -> i64 {
    skin_of_k(s, skin_denominator(n), pi, exponential)
}

/// The skin's denominator of a ring of period `n` at one e-fold a radian, `n ln 2 2^24` (the `k` of [`skin_of`]).
pub(crate) fn skin_denominator(n: usize) -> i128 {
    (n as i128 * ln2_face()) << PACE_BITS
}

/// [measurement; the lead, November 24, the calendar record §6 item 1] **The skin across a variation `s` with its denominator `k`**:
/// `e^(−2π |s|/k)` read as [`skin_of`] reads it; a ring whose fade is `γ` e-folds a radian of its own turn has `k = n ln 2 2^24 / γ`
/// ([`Constitution::set_ruler_fade`]), and at `γ = 1` the same bits as [`skin_of`].
pub(crate) fn skin_of_k(s: i128, k: i128, pi: i128, exponential: &Exponential) -> i64 {
    let bits = div_nearest(2 * pi * s.abs(), k);
    release(exponential.below_one(-bits) as i128, 62 - MOVE_BITS) as i64
}

/// The grain of `ln 2`'s face ([`ln2_face`]), `2^(−30)`.
pub const LN2_FACE_BITS: u32 = LN2_BITS;

/// [§16.44] The bits a blank's return through its face is held finer than the readout's, from its lift's covector to
/// the state's (`2^16`, the face's own grain), so a small covector reaches the state rather than rounding away.
pub(crate) const BLANK_HELD: u32 = STATE_BITS;

/// The temperature's carrier in its chart: `⌈log₂ T⌉ ≤ 7`, the reach its additive chart held on 32 bits, and
/// `T ≥ 2^(−23)`, above the material's grain.
pub const TEMPER_TOP: i128 = 7;

/// [definition; agent-inferred, November 2] **A temperature is a scale, carried in the ratio law's logarithmic
/// chart** (§16.12, §15.10): the material holds `ℓ = log₂ T` on `2^(−24)`, so a step multiplies the temperature
/// (`ℓ = log R`, the ratio of two scales), and the lock's sharpness moves by octaves however far it has come. `T =
/// 2^c · 2^(ℓ − c)` with `c = ⌈ℓ⌉`, the fraction read through the exponential's navigator at `ℓ`'s own grain
/// (`fine`, whose first sixteen roots are the resident face's), released to `2^(−24)`; no partition of `ℓ` hides
/// beneath its step. Past its carrier (`c > 7` or `c < −23`)
/// a temperature is refused, never clipped. Why: in the additive chart a step moved `T` by the same amount at 1 as at
/// 100, so crib13's learned temperatures moved about ±10 % in ten laps where the copy needs them 4 to 12 times
/// higher (§16.12).
pub(crate) fn temperature_of(ell: i32, fine: &Exponential) -> Result<i128> {
    let c = temper_octave(ell)?;
    let face = fine.below_one(ell as i128 - (c << MATERIAL_BITS));
    Ok(release(face as i128, (62 - MATERIAL_BITS as i128 - c) as u32))
}

/// A temperature's ceiling octave `c = ⌈ℓ⌉` from its logarithm on `2^(−24)`, refused past the carrier.
pub(crate) fn temper_octave(ell: i32) -> Result<i128> {
    let c = (ell as i128 + (1i128 << MATERIAL_BITS) - 1) >> MATERIAL_BITS;
    if c > TEMPER_TOP || c < 1 - MATERIAL_BITS as i128 {
        return refuse("a temperature past its carrier (2^(−23) to 2^7)");
    }
    Ok(c)
}

/// [definition; agent-inferred, November 2] **A row's temperature covector in its own chart** (§16.12): the row's
/// `δT = Σ release(δz S, 16)` over its sources and crowds, carried into `ℓ = log₂ T` as `δℓ = δT T ln 2`, on the same
/// scale: `release(δT · release(T ln 2, 30), 24)`, one a receiver's row, so the rows' covectors sum in any order to
/// the same bits (the card's `temper_chain`).
pub(crate) fn temperature_chain(temper: i128, dt: i128) -> Result<i128> {
    let rate = release(temper * ln2_face(), LN2_FACE_BITS);
    Ok(release(dt.checked_mul(rate).ok_or(TowerError::Refused("a temperature's covector past its 128-bit carrier"))?, MATERIAL_BITS))
}

/// The refusal of a clock's covector past its 128-bit carrier.
pub(crate) const PACE_RETURN: &str = "a clock's covector past its 128-bit carrier";

/// [definition; agent-inferred, November 2] The lock's covector `δs` read as `2^40 ∂/∂D` of the code over a skin `D`
/// (§16): the probe's return reads `δs D ŵ_j / 2^(40 + 16 + g − 24)` as the covector of the word, and the base is the
/// lock released `16 + 2g + 1` bits, so `∂code/∂base = δs / 2^56` and `2^40 ∂code/∂D = δs (∂lock/∂D on 2^(−g))
/// / 2^(2·16 + 2g + 1 − 30)`: `LOCK_BACK_BITS + 2g − 30` bits with `LOCK_BACK_BITS = 2·16 + 1`.
pub(crate) const LOCK_BACK_BITS: u32 = 2 * FACE_BITS + 1;

/// `release(b · (a_i z_r − a_r z_i), 46)`: the turn's covector `2^24 b Re(conj(a) i z)` on `2^(−24)` of a quantity `z`
/// on `2^(−16)` with covector `a` on `2^(−24)`, turned at the rate `b` on `2^(−30)` (§16).
pub(crate) fn turned_back(b: i128, a: (i128, i128), z: (i128, i128)) -> Result<i128> {
    let cross = a.1.checked_mul(z.0).zip(a.0.checked_mul(z.1)).and_then(|(x, y)| x.checked_sub(y)).ok_or(TowerError::Refused(PACE_RETURN))?;
    Ok(release(b.checked_mul(cross).ok_or(TowerError::Refused(PACE_RETURN))?, MOVE_BITS + FACE_BITS))
}

/// The skin's covector on the variation: `2^24 ∂/∂σ = 2^24 (E/2^40) b D` for `E = 2^40 ∂/∂D`, `b` and `D` on
/// `2^(−30)`, each product released once in that order (§16); its sign is the caller's.
pub(crate) fn skin_back(b: i128, decay: i128, e: i128) -> Result<i128> {
    let at = release(e.checked_mul(decay).ok_or(TowerError::Refused(PACE_RETURN))?, MOVE_BITS);
    Ok(release(release(at.checked_mul(b).ok_or(TowerError::Refused(PACE_RETURN))?, MOVE_BITS), 16))
}

/// [definition; agent-inferred, November 2] **The pace's grain**: a clock's rate `κ`, the clock `τ` and its
/// variation `σ` are on `2^(−24)`, the material's grain, so the rate is `1` plus a material row's pairing with the
/// opening face released once.
pub const PACE_BITS: u32 = MATERIAL_BITS;

/// [definition; agent-inferred, November 2] **A turned head's own clock over a region** (§16, Law 1): for each head
/// that reads a pace ([`Declaration::paced_heads`], its index `row[h]`), the rate `κ_h(t) = 1 + ⟨c_h, x⁰_t⟩`,
/// the clock `τ_h(t) = Σ_(0<k≤t) κ_h(k)` (an exact prefix sum: `τ_h(0) = 0`, each step into a site ticked by that
/// site's face) and the turn's variation `σ_h(t) = Σ_(0<k≤t) |κ_h(k)|`, on `2^(−24)`; `plain[p]` where every rate
/// is `1` exactly (the founding), so the clock is the byte place and the field reads its resident faces.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Paces {
    pub(crate) row: Vec<Option<usize>>,
    pub(crate) kappa: Vec<Vec<i64>>,
    pub(crate) tau: Vec<Vec<i64>>,
    pub(crate) sigma: Vec<Vec<i64>>,
    pub(crate) plain: Vec<bool>,
    /// [definition; the lead, November 25] Each paced head's skin-clock step `κ_h(t) + ρ_h[u_t]` where the classes fade at their own rates
    /// ([`Declaration::fade_rate`]); empty where they do not, and the skin clock steps by the turn's `|κ_h(t)|`.
    pub(crate) kappa_sigma: Vec<Vec<i64>>,
}

impl Paces {
    /// The sign of the skin clock's step at site `k` of paced head `p`: its own where the classes fade at their own rates, the turn's
    /// otherwise (the clock is the sum of the steps' magnitudes, so its covector reaches a step through this sign).
    pub(crate) fn skin_sign(&self, p: usize, k: usize) -> i128 {
        self.kappa_sigma.get(p).map_or(self.kappa[p][k], |ks| ks[k]).signum() as i128
    }
}

/// `e^(2πi r/n)` on `2^(−30)`, `r` taken in `(−n/2, n/2]`, from the half turn on `2^(−46)` by the
/// exponential's series: the ring's navigator face, read once and held resident. The four quarter
/// points are the turn's own constraint identities (`1`, `i`, `−1`, `−i`) and are held exactly; only
/// the faces between them are the series' attained faces.
pub(crate) fn ring_phasor(r: usize, n: usize, pi: i128) -> (i64, i64) {
    turn_phasor((r as i128) << PACE_BITS, n, pi)
}

/// [definition; agent-inferred, November 2] **The turn's face at a clock** `ρ` on `2^(−24)` (§16, Law 1):
/// `e^(2πi ρ/n)`, `ρ` taken in `(−n/2, n/2]`, by [`ring_phasor`]'s series (the same bits at a whole `ρ`), the
/// four quarter points held exactly.
pub(crate) fn turn_phasor(rho: i128, n: usize, pi: i128) -> (i64, i64) {
    let one = 1i64 << MOVE_BITS;
    let period = (n as i128) << PACE_BITS;
    let r = rho.rem_euclid(period);
    let c = if 2 * r > period { r - period } else { r };
    match (c, 2 * c == period, 4 * c == period, 4 * c == -period) {
        (0, ..) => return (one, 0),
        (_, true, ..) => return (-one, 0),
        (_, _, true, _) => return (0, one),
        (_, _, _, true) => return (0, -one),
        _ => {}
    }
    let theta = div_nearest(2 * pi * c, period);
    let (re, im) = exp_series(0, release(theta, 16));
    (re as i64, im as i64)
}

/// [definition; §16.44] A tick's own clocks where they are not the pass's: the clocks with its blanks at the faces the tick
/// before gave them, the moments read on those clocks, those faces' shares, and each blank's read (the return runs
/// through it).
#[derive(Clone, Debug, Default)]
pub(crate) struct TickClock {
    pub(crate) paces: Paces,
    pub(crate) moment: Vec<i64>,
    pub(crate) blank: Vec<Option<Shares>>,
    pub(crate) reads: Vec<Option<BlankRead>>,
}

/// [§16.44] A blank's read of its face off a state: the chart `r̂` and its scales, the lift `R r̂ + b_R`, and the face.
#[derive(Clone, Debug, Default)]
pub(crate) struct BlankRead {
    pub(crate) read: Vec<i32>,
    pub(crate) scale: Vec<i128>,
    pub(crate) lift: Vec<i64>,
    pub(crate) face: TowerFace,
}

/// [measurement; agent-inferred, November 5, §16.44] **A blank's clocks by tick** ([`Constitution::blank_clocks`]): at each tick
/// whose clocks the blanks set (`None` at a tick that reads the pass's), each paced head's rate `κ` at the site on
/// `2^(−24)` and the face the clock read there.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct BlankClocks {
    pub ticks: Vec<Option<(Vec<i64>, TowerFace)>>,
}

impl Constitution {

    /// The skin of turned slot `slot` across a variation `s` on `2^(−24)`: the resident decay at a whole distance
    /// within the reach, [`skin_of`] otherwise (the same bits).
    pub(crate) fn skin(&self, slot: usize, s: i128) -> i64 {
        let s = s.abs();
        if s & ((1i128 << PACE_BITS) - 1) == 0 {
            if let Some(&dv) = self.decays[slot].get((s >> PACE_BITS) as usize) {
                return dv;
            }
        }
        match self.ruler_skin_k.as_ref().or(self.fade_skin_k.as_ref()) {
            Some(k) => skin_of_k(s, k[slot], self.pi, &self.exponential),
            None => skin_of(s, self.rings[slot].0, self.pi, &self.exponential),
        }
    }

    /// The skin denominator of turned slot `slot` as the field reads it: a ruler's, else its fade's ([`Declaration::fade`]), else one
    /// e-fold a radian ([`skin_denominator`]). The card reads the same words ([`Constitution::skin_denominators`]).
    pub fn skin_denominator_of(&self, slot: usize) -> i128 {
        self.ruler_skin_k.as_ref().or(self.fade_skin_k.as_ref()).map_or_else(|| skin_denominator(self.rings[slot].0), |k| k[slot])
    }

    /// Every turned slot's skin denominator ([`Constitution::skin_denominator_of`]), in slot order.
    pub fn skin_denominators(&self) -> Vec<i128> {
        (0..self.rings.len()).map(|slot| self.skin_denominator_of(slot)).collect()
    }

    /// [definition; the lead, November 25] **The rings' second skins formed from their second fades** ([`Declaration::twin`]): each turned
    /// slot's `γ′ = 2^(ℓ′)` read from the material through the temperatures' chart, its denominator `n ln 2 2^24 / γ′` and its decays at a
    /// whole distance formed again where it moved. A field whose rings hold no second fade is untouched.
    fn refresh_twin(&mut self) -> Result<()> {
        if !self.declaration.twin {
            return Ok(());
        }
        let at = self.layout.twin_fade;
        let ks: Vec<i128> = (0..self.rings.len())
            .map(|slot| -> Result<i128> {
                let base = skin_denominator(self.rings[slot].0);
                let ell = self.theta[at + slot];
                Ok(if ell == 0 { base } else { div_nearest(base << MATERIAL_BITS, temperature_of(ell, &self.fine)?) })
            })
            .collect::<Result<_>>()?;
        let reach = self.declaration.reach;
        let (pi, exponential) = (self.pi, &self.exponential);
        let stale: Vec<usize> = (0..ks.len()).filter(|&slot| self.twin_skin_k.get(slot) != Some(&ks[slot])).collect();
        let fresh: Vec<(usize, Vec<i64>)> = stale.par_iter().map(|&slot| (slot, (0..reach).map(|d| skin_of_k((d as i128) << PACE_BITS, ks[slot], pi, exponential)).collect())).collect();
        if self.twin_decays.len() != ks.len() {
            self.twin_decays = vec![Vec::new(); ks.len()];
        }
        for (slot, row) in fresh {
            self.twin_decays[slot] = row;
        }
        self.twin_skin_k = ks;
        Ok(())
    }

    /// [the lead, November 25] The rings' second skin denominators ([`Declaration::twin`]; empty where they hold none), for the card's upload.
    pub fn twin_skin_denominators(&self) -> &[i128] {
        &self.twin_skin_k
    }

    /// [the lead, November 25] The rings' second decays at a whole distance (`[slot][d]`, [`Declaration::twin`]; empty where they hold none).
    pub fn twin_decays(&self) -> &[Vec<i64>] {
        &self.twin_decays
    }

    /// The skin of turned slot `slot`, or of its second fade where `twin` ([`Declaration::twin`]), across a variation `s` on `2^(−24)`.
    pub(crate) fn skin_with(&self, twin: bool, slot: usize, s: i128) -> i64 {
        if !twin {
            return self.skin(slot, s);
        }
        let s = s.abs();
        if s & ((1i128 << PACE_BITS) - 1) == 0 {
            if let Some(&dv) = self.twin_decays[slot].get((s >> PACE_BITS) as usize) {
                return dv;
            }
        }
        skin_of_k(s, self.twin_skin_k[slot], self.pi, &self.exponential)
    }

    /// Turned slot `slot`'s decays at a whole distance, or its second fade's where `twin`.
    pub(crate) fn decays_with(&self, twin: bool, slot: usize) -> &[i64] {
        if twin { &self.twin_decays[slot] } else { &self.decays[slot] }
    }

    /// Turned slot `slot`'s rate of fade ([`Constitution::skin_rate`]), or its second fade's where `twin`: `div_nearest(b n ln 2 2^24, k′)`.
    pub fn skin_rate_with(&self, twin: bool, slot: usize) -> i128 {
        if !twin {
            return self.skin_rate(slot);
        }
        let b = self.turn_rate(slot);
        let (base, k) = (skin_denominator(self.rings[slot].0), self.twin_skin_k[slot]);
        if k == base { b } else { div_nearest(b * base, k) }
    }

    /// [definition; the lead, November 24] **The rings' skins formed from their fades** ([`Declaration::fade`]): each turned slot's fade
    /// `γ_s = 2^(ℓ_s)` read from the material through the temperatures' chart, its skin denominator `k = n ln 2 2^24 / γ` and its decays at a
    /// whole distance formed again where `k` moved. A field whose rings do not hold their fades is untouched. At `ℓ = 0` every word is the
    /// constant skin's, bit for bit.
    pub fn refresh_fade(&mut self) -> Result<()> {
        self.refresh_twin()?;
        if !self.declaration.fade {
            return Ok(());
        }
        let at = self.layout.fade;
        let ks: Vec<i128> = (0..self.rings.len())
            .map(|slot| -> Result<i128> {
                let base = skin_denominator(self.rings[slot].0);
                let ell = self.theta[at + slot];
                Ok(if ell == 0 { base } else { div_nearest(base << MATERIAL_BITS, temperature_of(ell, &self.fine)?) })
            })
            .collect::<Result<_>>()?;
        let reach = self.declaration.reach;
        let (pi, exponential) = (self.pi, &self.exponential);
        let stale: Vec<usize> = (0..ks.len()).filter(|&slot| self.fade_skin_k.as_ref().is_none_or(|old| old[slot] != ks[slot])).collect();
        let fresh: Vec<(usize, Vec<i64>)> = stale.par_iter().map(|&slot| (slot, (0..reach).map(|d| skin_of_k((d as i128) << PACE_BITS, ks[slot], pi, exponential)).collect())).collect();
        for (slot, row) in fresh {
            self.decays[slot] = row;
        }
        self.fade_skin_k = Some(ks);
        Ok(())
    }

    /// [measurement; the lead, November 24, the calendar record §6 item 1, a read before the fade is a law] **The rings of period `from` and
    /// more faded at `γ = 2^ℓ` e-folds a radian of their own turn** (`ℓ` on `2^(−24)`, read through the temperatures' chart), every other
    /// ring at one: each such ring's skin denominator `k = n ln 2 2^24 / γ` and its decays at a whole distance formed again. A ruler's
    /// setting on a clone of the field (`read-reach`'s `fade:FROM:MILLI`): not part of the state, and no reverse reads it.
    pub fn set_ruler_fade(&mut self, from: usize, ell: i32) -> Result<()> {
        self.set_ruler_fade_between(from, usize::MAX, ell)
    }

    /// [`Constitution::set_ruler_fade`] on the rings of period `from` to `to` alone.
    pub fn set_ruler_fade_between(&mut self, from: usize, to: usize, ell: i32) -> Result<()> {
        let gamma = temperature_of(ell, &self.fine)?;
        let ks: Vec<i128> = self.rings.iter().map(|&(n, _)| if n >= from && n <= to { div_nearest(skin_denominator(n) << MATERIAL_BITS, gamma) } else { skin_denominator(n) }).collect();
        let reach = self.declaration.reach;
        self.decays = ks.iter().map(|&k| (0..reach).map(|d| skin_of_k((d as i128) << PACE_BITS, k, self.pi, &self.exponential)).collect()).collect();
        self.ruler_skin_k = Some(ks);
        Ok(())
    }

    /// The face of turned slot `slot` at a clock `ρ` on `2^(−24)`: the resident ring at a whole place it holds,
    /// [`turn_phasor`] otherwise (the same bits).
    pub(crate) fn turn(&self, slot: usize, rho: i128) -> (i64, i64) {
        let (n, ring) = &self.rings[slot];
        if rho & ((1i128 << PACE_BITS) - 1) == 0 {
            if let Some(&p) = ring.get((rho >> PACE_BITS).rem_euclid(*n as i128) as usize) {
                return p;
            }
        }
        turn_phasor(rho, *n, self.pi)
    }

    /// [definition; agent-inferred, November 2] **The turned heads' clocks over a region** ([`Paces`]), read on the
    /// class sheet (§16.16): a site's rate is its own class's, `κ = 1 + c_h[u_t]` on `2^(−24)` (one at a silent open
    /// site, §16.28; a carried face's mixture `release(Σ_a w_a c_h[a], 16)`), one rate a codec cell, a navigator's
    /// resident face beside `E(u)`, opening at `κ ≡ 1` and deposited by the covector like every other parameter
    /// (§16.19). The neighbours' rows of the opening do not enter: a copy's turn is
    /// the sum of its span's rates, and the loop law reads only the span's classes.
    pub(crate) fn paces(&self, region: &Region) -> Result<Paces> {
        self.paces_with(region, &[])
    }

    /// [definition; agent-inferred, November 4, §16.44] **A blank place runs at its expected duration**: the clocks
    /// ([`Constitution::paces`]) with each silent open site `t` that `blank` gives a face `p_t` running at
    /// `κ_h(t) = 1 + Σ_a p_t(a) c_h[a]`, the duration a written byte there would take in expectation, `release(Σ_a w_a c_h[a],
    /// 24)` as a carried face's mixture; every other site as in [`Constitution::paces`]. Why (the unified-theory reading of
    /// November 4, `a_blank_place_is_a_potential` §4, and §16.42): a turned head reads a source across `τ_t − τ_s = Σ_(u∈(s,t])
    /// κ_u`, and a blank at the bare rate makes a gap read `1/1.62` and `1/1.91` of its written length on the two clocks, so a
    /// restated result drawn into a blank surround lands one place off; at its expected duration the gap's clock has the
    /// expectation it will have once written, and only its spread remains. The blank carries nothing else: its rows at its
    /// own place would be a self-energy, and as a source it costs the trained field 0.87 bits a class (that reading, §5).
    pub(crate) fn paces_with(&self, region: &Region, blank: &[Option<Shares>]) -> Result<Paces> {
        let d = &self.declaration;
        let sites = region.classes.len();
        let width = d.alphabet + 1;
        let one = 1i128 << PACE_BITS;
        let stretch = if self.per_blank_clock { sites } else { Self::silent_stretch(region) };
        let mut out = Paces { row: vec![None; d.heads], ..Default::default() };
        for h in (0..d.heads).filter(|&h| d.carries_moment(h)) {
            let p = out.kappa.len();
            out.row[h] = Some(p);
            let base = self.layout.pace + p * width;
            let fade_base = d.fade_rate.then(|| self.layout.fade_rate + p * width);
            let (mut kappa, mut tau, mut sigma) = (Vec::with_capacity(sites), Vec::with_capacity(sites), Vec::with_capacity(sites));
            let mut kappa_sigma = Vec::with_capacity(if fade_base.is_some() { sites } else { 0 });
            let (mut clock, mut variation) = (0i128, 0i128);
            for t in 0..sites {
                // [§16.47] Past the last arrival every silent place runs at the first one's rate (one passage); under
                // `bare_stretch` at its own place, which reads no face there, so at the bare rate.
                let at = if t > stretch && !self.bare_stretch { stretch } else { t };
                // [the unified-theory reading of November 6, 05:45] A depth ring takes no blank face: a silent site runs at
                // rate zero every tick (exact on what arrived; an expected increment `ζ^E[r]` would read a blank at full
                // coherence and turn a closer's frame by its own guess).
                let rate = match blank.get(at).and_then(Option::as_ref).filter(|_| Self::silent(region, at) && !d.is_depth(h)) {
                    Some(face) => release(face.iter().map(|&(c, w)| w as i128 * self.theta[base + c as usize] as i128).sum(), STATE_BITS),
                    None => self.strand_row(region, base, 1, at)[0] as i128,
                };
                // A depth ring's rate is its located increment alone (base zero, [`Declaration::depth`]).
                let k = if d.is_depth(h) { rate } else { one + rate };
                // [the lead, November 25] Where the classes fade at their own rates the skin clock steps by `κ + ρ[u]`, the fade's row read at a
                // written site as the turn's is (a carried face by its shares) and zero at a silent one, whose fade is the turn's
                // ([`Declaration::fade_rate`]).
                let ks = match fade_base {
                    Some(fb) => {
                        let rho = self.strand_row(region, fb, 1, at)[0] as i128;
                        kappa_sigma.push(fit64(k + rho)?);
                        k + rho
                    }
                    None => k,
                };
                if t > 0 {
                    clock += k;
                    variation += ks.abs();
                }
                kappa.push(fit64(k)?);
                tau.push(fit64(clock)?);
                sigma.push(fit64(variation)?);
            }
            let rest = if d.is_depth(h) { 0 } else { one };
            out.plain.push(kappa.iter().all(|&k| k as i128 == rest) && kappa_sigma.iter().zip(&kappa).all(|(s, k)| s == k));
            out.kappa.push(kappa);
            out.tau.push(tau);
            out.sigma.push(sigma);
            if fade_base.is_some() {
                out.kappa_sigma.push(kappa_sigma);
            }
        }
        Ok(out)
    }

    /// Each turned slot's period and its ring's phasors on `2^(−30)` (a realization's resident
    /// frames).
    pub fn rings(&self) -> &[(usize, Vec<(i64, i64)>)] {
        &self.rings
    }

    /// The exponential's resident face (the Gibbs weights' navigator).
    pub fn exponential(&self) -> &Exponential {
        &self.exponential
    }

    /// The temperatures' exponential at the material's grain (§16.12), whose roots past the sixteenth the card
    /// multiplies after its resident face.
    pub fn fine_exponential(&self) -> &Exponential {
        &self.fine
    }

    /// The half turn on `2^(−46)`, the turn's faces' navigator (§16; the card reads it).
    pub fn half_turn(&self) -> i128 {
        self.pi
    }

    /// `ln 2` on `2^(−30)`, the weights' return reads it.
    pub fn ln2(&self) -> i128 {
        ln2_face()
    }

    /// The frame of local mode `l` of head `h` at site `t`, on `2^(−30)`: the identity in a head of
    /// a still ring set, the mode's ring in a turned one.
    pub(crate) fn frame(&self, paces: &Paces, t: usize, h: usize, l: usize) -> (i64, i64) {
        self.frame_placed(paces, t, t, h, l)
    }

    /// [`Constitution::frame`] of the site whose clock is `paces`' at `t` and whose place on the strand is `place` (its index, but for an
    /// open place of a strand's second stream, [`crate::contact::ClassLists::twins_from`]): a plain pace's frame is the place's.
    pub(crate) fn frame_placed(&self, paces: &Paces, t: usize, place: usize, h: usize, l: usize) -> (i64, i64) {
        let d = &self.declaration;
        let set = h % d.frames;
        if set < d.still {
            return (1i64 << MOVE_BITS, 0);
        }
        let slot = l * (d.frames - d.still) + set - d.still;
        let (n, ring) = &self.rings[slot];
        // A turned head's frame is its own clock's (§16, Law 1): the byte place where its pace is plain.
        match paces.row.get(h).copied().flatten() {
            Some(p) if !paces.plain[p] || d.is_depth(h) => self.turn(slot, paces.tau[p][t] as i128),
            _ => ring[place % n],
        }
    }

    /// A turned slot's rate of turn `b = 2π/n` per unit of its clock, on `2^(−30)`.
    pub(crate) fn turn_rate(&self, slot: usize) -> i128 {
        release(div_nearest(2 * self.pi, self.rings[slot].0 as i128), FACE_BITS)
    }

    /// [definition; the lead, November 24] **A turned slot's rate of fade** on `2^(−30)`: its turn rate `2π/n` times its fade `γ`
    /// ([`Declaration::fade`]), read as `div_nearest(b n ln 2 2^24, k)` from its skin denominator `k = n ln 2 2^24/γ`, so at one e-fold a
    /// radian it is the turn rate bit for bit. The skin's slope in the clock's variation is this rate, where the frame's is the turn rate.
    pub fn skin_rate(&self, slot: usize) -> i128 {
        let b = self.turn_rate(slot);
        let (base, k) = (skin_denominator(self.rings[slot].0), self.skin_denominator_of(slot));
        if k == base { b } else { div_nearest(b * base, k) }
    }

    /// [definition; the lead, November 24] **A ring's fade covector from its skin's homogeneity** ([`Declaration::fade`]): the skin reads
    /// her clock only through `γ |s|`, so `∂L/∂ℓ = ln 2 Σ_pairs s ∂L/∂s`. One pair's term, with `s` on `2^(−24)` and `term` its share of the
    /// clock covector (`2^24 ∂/∂σ`, so that `−sgn term` is the pair's `∂/∂s`), is `−release(ln 2 · release(|s| term, MATERIAL_BITS − FACE_BITS), LN2_FACE_BITS)` on the
    /// material's covector at the slot's fade (`2^40 ∂/∂ℓ`). Each term is released alone and the terms meet at that one grain, so their sum
    /// is the same bits on any partition of the pairs (the card's, the host's cells).
    pub(crate) fn fade_term(s: i128, term: i128) -> Result<i128> {
        let at = release(s.abs().checked_mul(term).ok_or(TowerError::Refused(PACE_RETURN))?, MATERIAL_BITS - FACE_BITS);
        Ok(-release(ln2_face().checked_mul(at).ok_or(TowerError::Refused(PACE_RETURN))?, LN2_FACE_BITS))
    }

    /// Head `h`'s clock as the moment reads it ([`moment::Pace`]): none where its pace is plain (the byte place).
    pub(crate) fn pace_of<'a>(&self, paces: &'a Paces, h: usize, turn: &'a dyn Fn(i128) -> (i64, i64), skin: &'a dyn Fn(i128) -> i64) -> Option<moment::Pace<'a>> {
        let p = paces.row.get(h).copied().flatten()?;
        (!paces.plain[p]).then(|| moment::Pace { tau: &paces.tau[p], sigma: &paces.sigma[p], turn, skin })
    }

    /// The (slot, period) of head `h`'s local mode `l` among the turned rings.
    pub(crate) fn slot(&self, h: usize, l: usize) -> usize {
        let d = &self.declaration;
        l * (d.frames - d.still) + h % d.frames - d.still
    }
}

pub fn octave_of(d: usize) -> u32 {
    usize::BITS - 1 - d.leading_zeros()
}
