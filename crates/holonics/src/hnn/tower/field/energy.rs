//! [definition; the unified-theory reading of November 6, 22:52] **The faces are one stored energy's forces**
//! ([`FieldDeclaration::energy`]).
//!
//! Why: on the line's field each pair of letters is read inconsistently from its two ends at every distance (the curl
//! reading, truth120: curl/λ 1.20 at `d = 1`, above 1.0 in every band), training the two readings to agree reached only a
//! fast mode (squares126, κ 0.485), and a fixed scan direction moved the walk's resting law (scans127): the faces are no
//! joint's conditionals, and the release refines a joint only lawfully when they are. The Holon law gives the cure: a
//! constitution is storage with dissipation and power-neutral turns, so the field's faces are one stored energy's forces,
//! each contact's energy counted once with its force at both ends.
//!
//! **The energy** of a region's state `x` and letters `u`, on one support:
//!
//! ```text
//! locks      Σ_(h, i) −log₂ Σ_(j ∈ S_i^h) μ_j 2^(z_ij)        each receiver's lock partition per head (z_ij as the field's lock,
//!                                                              a crowd a term at its count; a receiver outside a cut room's
//!                                                              windows carries none)
//! pair       −Σ_t Re⟨c, a_t · b_(s(t))⟩                        the strand pair's energy through its contraction `c`
//! letters    −Σ_t [⟨E(u_t), R r̂_t + b_R⟩ + c_(u_t) + ⟨E₋(u_t), r̂_(t+1)⟩ + ⟨E₊(u_t), r̂_(t−1)⟩ + ⟨C s_t + b, r̂_t⟩]
//! ```
//!
//! with the probes reading the moments as now (`p_t = W_p r̂_t + b_p + s_t` at the turned modes), so a letter enters the
//! locks through every probe its moment reaches. The classes and supports are read at the opening and held through the
//! ticks (one energy, one support). **The tick descends it**: `x ← x − η ∂Φ/∂r̂`, each site's step on its lanes' own
//! scale, `Δx = η ‖x‖_rms (−∂Φ/∂r̂)`. `r̂ = x/‖x‖_rms` is the gradient of the convex `√D |x|`, so the step's first-order
//! change is `−η gᵀ Hess g ≤ 0`; `η` is halved wherever a tick's fall is not certified on the energy's own reading, and
//! a tick no halving certifies leaves the state at rest. The opening as now is its start. **The face is the energy's force
//! on a letter**: `z_t(a) = −∂Φ/∂e_t(a)` at the last state, one backward of `Φ` to the letter rows at fixed state,
//! `⟨E(a), R r̂_t + b_R⟩ + c_a + ⟨E₋(a), r̂_(t+1)⟩ + ⟨E₊(a), r̂_(t−1)⟩` with the moment's part, the letter's moment rows
//! read against the transported covector `−∂Φ/∂s` (each site's `Cᵀ r̂` and its probe's lock force at the turned modes).
//! At rest `∂z_i(a)/∂e_j(b) = ∂z_j(b)/∂e_i(a)` (Maxwell–Betti), so each square's two readings agree to first order by
//! construction; the residual force at the last tick is read with the curl.
//!
//! A receiver gathers its lock's force (its sources' framed keys through the probe chart's transpose) and a source its
//! receivers' probes (through the key chart's): one contact, one energy, the force at both ends. The value chart, the
//! current's return and the pair's return leave. [agent-inferred, November 6] The first build reads plain clocks (a paced
//! head's clock is read from the arriving classes, so its letters would enter the energy through its frames, whose force
//! is not built), no depth ring and no tower of scales, and its training return is not built: an energy field is read,
//! not trained, until the return through the ticks (the energy's Hessian on the tick's covector) is built and checked.

use super::*;
use num_bigint::BigInt;
use num_traits::ToPrimitive;

/// [definition; agent-inferred, November 6] The energy's grain: `Φ` read on `2^(−32)` bits, each lock row's logarithm to
/// `2^(−32)`, so a certified fall is read past the rows' summed reading error.
pub const ENERGY_BITS: u32 = 32;
/// [agent-inferred, November 6] The first tick's step `η = 2^(−2)` of a site's own scale a unit of force; each later tick
/// starts one halving above the halvings its tick before stood at, so the step can grow back.
const FIRST_HALVINGS: u32 = 2;
/// The most halvings a tick reads before the state rests: past them the step is below the state's grain.
const MOST_HALVINGS: u32 = STATE_BITS + 8;

/// A state's read under the held supports: its charts, its rows' shares and crowds, its pair drives, its lifts, and its
/// energy on `2^(−32)` bits with the count of the logarithms read (the reading's slack).
#[derive(Clone, Debug, Default)]
pub(super) struct EnergyCell {
    read: Vec<i32>,
    scale: Vec<i128>,
    q: Vec<i64>,
    qscale: Vec<i128>,
    pq: Vec<i64>,
    pscale: Vec<i128>,
    rows: Vec<Vec<Source>>,
    crowds: Vec<Vec<Crowd>>,
    sums: Vec<Sums>,
    a: Vec<i64>,
    b: Vec<i64>,
    lift: Vec<i64>,
    pub(super) phi: i128,
    logs: u64,
    pairs: u64,
}

/// Each site's letter in the energy: its rows of the encoding and of its two strand contacts (its class's, its carried
/// face's mixture, or the unresolved row, as the opening reads them) and its class bias, on `2^(−16)`.
struct Letters {
    own: Vec<Vec<i64>>,
    before: Vec<Vec<i64>>,
    after: Vec<Vec<i64>>,
    bias: Vec<i64>,
}

/// A region's energy read held across its ticks: the letters, the moments and the moment's term in the face, and the
/// supports.
struct Held {
    letters: Letters,
    moment: Vec<i64>,
    moment_term: Vec<i64>,
    classes: Vec<ClassLists>,
    definite: Vec<bool>,
}

/// A region relaxed under its energy: the last state, its read, what the ticks held, the clocks and the read's receipt
/// (the state and the windows are read again only by the tests' letter reading).
#[cfg_attr(not(test), allow(dead_code))]
struct Relaxed {
    x: Vec<i64>,
    cell: EnergyCell,
    held: Held,
    paces: Paces,
    window: Option<Vec<bool>>,
    read: EnergyRead,
}

/// `log₂ m` on `2^(−ENERGY_BITS)` for a positive integer `m`, from its leading 127 bits.
fn log2_big(m: &BigInt) -> i128 {
    let width = m.bits();
    let (top, shift) = if width > 127 { ((m >> (width - 127) as usize).to_u128().unwrap_or(u128::MAX), width - 127) } else { (m.to_u128().unwrap_or(u128::MAX), 0) };
    super::super::log2_reading_at(top, ENERGY_BITS) + ((shift as i128) << ENERGY_BITS)
}

/// A lock row's terms `(a, face, μ)` (each `face · μ · 2^(a − 123)`, [`Field::face`]): each term's share of the row on
/// `2^(−63)` and `log₂ Z` on `2^(−32)` bits, the sums whole as [`SeriesRow::release`]'s.
fn log_row(terms: &[(i64, u128, u128)]) -> (Vec<u64>, i128) {
    let a0 = terms.iter().map(|t| t.0).min().unwrap_or(0);
    let mass_of = |t: &(i64, u128, u128)| (BigInt::from(t.1) * BigInt::from(t.2)) << ((t.0 - a0) as usize);
    let masses: Vec<BigInt> = terms.iter().map(mass_of).collect();
    let mass: BigInt = masses.iter().sum();
    let half: BigInt = &mass / 2;
    let shares = masses.iter().map(|m| (((m << SHARE_BITS as usize) + &half) / &mass).to_u64().unwrap_or(u64::MAX)).collect();
    (shares, log2_big(&mass) + (((a0 - 123) as i128) << ENERGY_BITS))
}

impl Field {
    /// Each site's letter rows and class bias ([`Letters`]).
    fn energy_letters(&self, region: &Region) -> Letters {
        let (d, l) = (&self.declaration, &self.layout);
        let dw = d.width;
        let sites = region.classes.len();
        let row = |base: usize, t: usize| {
            let mut e = vec![0i64; dw];
            self.opening_term(region, base, t, &mut e);
            e
        };
        Letters {
            own: (0..sites).map(|t| row(l.enc, t)).collect(),
            before: (0..sites).map(|t| row(l.before, t)).collect(),
            after: (0..sites).map(|t| row(l.after, t)).collect(),
            bias: (0..sites)
                .map(|t| match Self::carried(region, t) {
                    Some(face) => release(face.iter().map(|&(c, w)| w as i128 * self.theta[l.read_bias + c as usize] as i128).sum(), STATE_BITS) as i64,
                    None if region.unresolved[t] => 0,
                    None => self.theta[l.read_bias + region.classes[t]] as i64,
                })
                .collect(),
        }
    }

    /// The key and probe words of a chart's read (`[t][2M]`, unframed), the probe reading its site's moment.
    fn energy_words(&self, read: &[i32], moment: &[i64], reaches: &Reaches) -> Result<(Vec<i64>, Vec<i64>)> {
        let d = &self.declaration;
        let (dw, m2) = (d.width, 2 * d.complex());
        let sites = read.len() / dw;
        let l = &self.layout;
        let mut q = vec![0i64; sites * m2];
        let mut pr = vec![0i64; sites * m2];
        for t in 0..sites {
            let rt = &read[t * dw..(t + 1) * dw];
            affine(&self.theta[l.q..l.q + m2 * dw], reaches.q, dw, rt, Some(&self.theta[l.q_bias..l.q_bias + m2]), MATERIAL_BITS, MATERIAL_BITS, &mut q[t * m2..(t + 1) * m2])?;
            affine(&self.theta[l.probe..l.probe + m2 * dw], reaches.probe, dw, rt, Some(&self.theta[l.probe_bias..l.probe_bias + m2]), MATERIAL_BITS, MATERIAL_BITS, &mut pr[t * m2..(t + 1) * m2])?;
            for (pp, &mv) in pr[t * m2..(t + 1) * m2].iter_mut().zip(&moment[t * m2..(t + 1) * m2]) {
                *pp = fit64(*pp as i128 + mv as i128)?;
            }
        }
        Ok((q, pr))
    }

    /// The resonance classes of the opening's chart, held through the ticks (as the tick reads them, §12, §16.19).
    fn energy_classes(&self, read: &[i32], moment: &[i64], definite: &[bool], keyed: &[bool], reaches: &Reaches) -> Result<Vec<ClassLists>> {
        let d = &self.declaration;
        let (m, n, heads) = (d.complex(), d.modes, d.heads);
        let m2 = 2 * m;
        let sites = definite.len();
        let (trits, buckets) = (d.class_trits(), d.classes());
        let (q, pr) = self.energy_words(read, moment, reaches)?;
        let class_of = |word: &[i64], t: usize, h: usize| (0..trits).rev().fold(0u32, |c, li| 3 * c + shell(word[t * m2 + h * n + li], word[t * m2 + m + h * n + li]));
        Ok((0..heads)
            .map(|h| {
                let class = (0..sites).map(|t| class_of(&q, t, h)).collect();
                let probe_class = (0..sites).map(|t| class_of(&pr, t, h)).collect();
                let probed = (0..sites).map(|t| probes((0..trits).map(|li| (pr[t * m2 + h * n + li], pr[t * m2 + m + h * n + li])), band_bits(trits))).collect();
                ClassLists::of(class, definite.to_vec(), buckets).probing(probe_class, probed).keyed(keyed.to_vec())
            })
            .collect())
    }

    /// The energy's read at state `x` under the held supports ([`EnergyCell`]).
    fn energy_cell(&self, x: &[i64], held: &Held, paces: &Paces, reaches: &Reaches, window: Option<&[bool]>) -> Result<EnergyCell> {
        let d = &self.declaration;
        let (dw, m, n, f, heads) = (d.width, d.complex(), d.modes, d.contacts, d.heads);
        let m2 = 2 * m;
        let span = 2 * n;
        let sites = x.len() / dw;
        let l = &self.layout;
        let mut c = EnergyCell { read: Vec::with_capacity(sites * dw), scale: Vec::with_capacity(sites * d.lanes), ..Default::default() };
        for xt in x.chunks_exact(dw) {
            lane_chart(xt, d.lanes, &mut c.read, &mut c.scale)?;
        }
        let (q, pr) = self.energy_words(&c.read, &held.moment, reaches)?;
        // The frame and the unit power, by head, as the tick reads them.
        c.q = vec![0i64; heads * sites * span];
        c.pq = vec![0i64; heads * sites * span];
        for h in 0..heads {
            for t in 0..sites {
                let at = (h * sites + t) * span;
                for li in 0..n {
                    let k = h * n + li;
                    let (ur, ui) = self.frame(paces, t, h, li);
                    let (ur, ui) = (ur as i128, ui as i128);
                    for (word, out) in [(&q, &mut c.q), (&pr, &mut c.pq)] {
                        let (wr, wi) = (word[t * m2 + k] as i128, word[t * m2 + m + k] as i128);
                        out[at + li] = fit64(release(ur * wr - ui * wi, MOVE_BITS))?;
                        out[at + n + li] = fit64(release(ui * wr + ur * wi, MOVE_BITS))?;
                    }
                }
            }
        }
        c.qscale = vec![0i128; heads * sites];
        c.pscale = vec![0i128; heads * sites];
        for hs in 0..heads * sites {
            for (word, scale) in [(&mut c.q, &mut c.qscale), (&mut c.pq, &mut c.pscale)] {
                let slice = &mut word[hs * span..(hs + 1) * span];
                let (r, s) = ratio_to_power(slice)?;
                for (slot, v) in slice.iter_mut().zip(r) {
                    *slot = v as i64;
                }
                scale[hs] = s;
            }
        }
        // The locks' partitions over the held supports.
        let one = 1u128 << WEIGHT_BITS;
        let carried = |v: Option<i128>| v.ok_or(TowerError::Refused("a lock past its 128-bit carrier"));
        let zeros = vec![0i64; sites * span];
        let mut phi_lock = 0i128;
        for h in 0..heads {
            let lists = &held.classes[h];
            let sums = Sums::of(&c.q[h * sites * span..(h + 1) * sites * span], &zeros, &held.definite, span);
            let shared = !d.carries_moment(h);
            let falloff = |gap: usize, j: usize| -> i128 {
                if !shared {
                    return octave(gap) as i128;
                }
                let k = lists.class[j] as usize;
                octave(((lists.off[2 * k + 1] - lists.off[2 * k]) as usize).max(1)) as i128
            };
            for i in 0..sites {
                if window.is_some_and(|w| !w[i]) {
                    c.rows.push(Vec::new());
                    c.crowds.push(Vec::new());
                    continue;
                }
                let wi = &c.pq[(h * sites + i) * span..(h * sites + i + 1) * span];
                let temper = self.temper(h, lists.listens(i))?;
                let mut terms: Vec<(i64, u128, u128)> = Vec::new();
                let mut row: Vec<Source> = Vec::new();
                for j in lists.support(i) {
                    let wj = &c.q[(h * sites + j) * span..(h * sites + j + 1) * span];
                    let gap = i.abs_diff(j);
                    let mut s = 0i128;
                    for li in 0..n {
                        let decay = self.pair_decay(paces, h, li, i, j);
                        s = carried(s.checked_add(lock((wi[li] as i128, wi[n + li] as i128), (wj[li] as i128, wj[n + li] as i128), 1, decay)?))?;
                    }
                    let base = fit64(release(s, FACE_BITS + 2 * self.decay(h, 0, gap).1 + 1))?;
                    let z = fit64(release(temper * base as i128, MATERIAL_BITS) - (falloff(gap, j) << FACE_BITS))?;
                    let (a, face) = self.face(z);
                    terms.push((a, face, one));
                    row.push(Source { j: j as u32, p: 0, s: base });
                }
                let mut crowds: Vec<Crowd> = Vec::new();
                for (lo, hi_, level) in crowd_ranges(i, sites).into_iter().filter(|_| !lists.listens(i)) {
                    let count = sums.count(lo, hi_);
                    if count == 0 {
                        continue;
                    }
                    let word = sums.words(lo, hi_);
                    let mut score = 0i128;
                    for li in 0..n {
                        let decay = self.octave_decay(paces, h, li, i, level, lo > i);
                        score = carried(score.checked_add(lock((wi[li] as i128, wi[n + li] as i128), (word[li], word[n + li]), count as i128, decay)?))?;
                    }
                    let base = fit64(div_nearest(score, ((count * count) as i128) << (FACE_BITS + 2 * self.decay(h, 0, 1 << level).1 + 1)))?;
                    let z = fit64(release(temper * base as i128, MATERIAL_BITS) - ((level as i128) << FACE_BITS))?;
                    let (a, face) = self.face(z);
                    terms.push((a, face, (count as u128) << WEIGHT_BITS));
                    crowds.push(Crowd { lo, hi: hi_, level, count, z, e: 0, s: base });
                }
                if !terms.is_empty() {
                    let (shares, log) = log_row(&terms);
                    phi_lock -= log;
                    c.logs += 1;
                    for (src, &share) in row.iter_mut().zip(&shares) {
                        src.p = share;
                    }
                    for (cr, &share) in crowds.iter_mut().zip(&shares[row.len()..]) {
                        cr.e = share;
                    }
                }
                c.pairs += row.len() as u64;
                c.rows.push(row);
                c.crowds.push(crowds);
            }
            c.sums.push(sums);
        }
        // The strand pair's energy through its contraction, on 2^(−40).
        c.a = vec![0i64; sites * f];
        c.b = vec![0i64; sites * f];
        for t in 0..sites {
            let rt = &c.read[t * dw..(t + 1) * dw];
            affine(&self.theta[l.a..l.a + f * dw], reaches.a, dw, rt, Some(&self.theta[l.a_bias..l.a_bias + f]), MATERIAL_BITS, MATERIAL_BITS, &mut c.a[t * f..(t + 1) * f])?;
            affine(&self.theta[l.b..l.b + f * dw], reaches.b, dw, rt, Some(&self.theta[l.b_bias..l.b_bias + f]), MATERIAL_BITS, MATERIAL_BITS, &mut c.b[t * f..(t + 1) * f])?;
        }
        let half = f / 2;
        let mut phi_pair = 0i128;
        for t in 0..sites {
            for e in 0..half {
                let Some(s) = strand_mate(t, e, sites) else { continue };
                let (ar, ai) = (c.a[t * f + e] as i128, c.a[t * f + half + e] as i128);
                let (br, bi) = (c.b[s * f + e] as i128, c.b[s * f + half + e] as i128);
                let (pr_, pi_) = (release(ar * br - ai * bi, FACE_BITS), release(ar * bi + ai * br, FACE_BITS));
                let (cr, ci) = (self.theta[l.pair_c + e] as i128, self.theta[l.pair_c + half + e] as i128);
                phi_pair -= cr * pr_ + ci * pi_;
            }
        }
        // The letters' energy on 2^(−32): each letter with every site its rows reach.
        c.lift = vec![0i64; sites * dw];
        let reach_read = reaches.read;
        let mut phi_letters = 0i128;
        let dot = |a: &[i64], b: &[i32]| -> i128 { a.iter().zip(b).map(|(&x, &y)| x as i128 * y as i128).sum() };
        for t in 0..sites {
            let rt = &c.read[t * dw..(t + 1) * dw];
            affine(&self.theta[l.read..l.read + dw * dw], reach_read, dw, rt, Some(&self.theta[l.lift_bias..l.lift_bias + dw]), MATERIAL_BITS, MATERIAL_BITS, &mut c.lift[t * dw..(t + 1) * dw])?;
            let lift: i128 = held.letters.own[t].iter().zip(&c.lift[t * dw..(t + 1) * dw]).map(|(&e, &y)| e as i128 * y as i128).sum();
            phi_letters -= lift + ((held.letters.bias[t] as i128) << FACE_BITS) + dot(&held.moment_term[t * dw..(t + 1) * dw], rt);
            if t + 1 < sites {
                phi_letters -= dot(&held.letters.before[t], &c.read[(t + 1) * dw..(t + 2) * dw]);
            }
            if t > 0 {
                phi_letters -= dot(&held.letters.after[t], &c.read[(t - 1) * dw..t * dw]);
            }
        }
        c.phi = phi_lock + phi_letters + release(phi_pair, MATERIAL_BITS + FACE_BITS - ENERGY_BITS);
        Ok(c)
    }

    /// The energy's force on each site's chart read, `−∂Φ/∂r̂` (`[t][D]` on `2^(−24)`), and the probes' share of it
    /// `[t][2M]` (unframed, on `2^(−24)`), whose turned modes the moment's face reads.
    fn energy_force(&self, c: &EnergyCell, held: &Held, paces: &Paces, reaches: &Reaches) -> Result<(Vec<i64>, Vec<i64>)> {
        let d = &self.declaration;
        let (dw, m, n, f, heads) = (d.width, d.complex(), d.modes, d.contacts, d.heads);
        let m2 = 2 * m;
        let span = 2 * n;
        let sites = held.definite.len();
        let l = &self.layout;
        // The locks: the row's share is the force on its score (`−∂Φ/∂z_ij = p_ij`), carried to 2^(−40) as the
        // reverse's score covector, then each mode's lock returns to its two words as the tick's reverse reads it.
        let mut dq = vec![0i64; sites * m2];
        let mut dp = vec![0i64; sites * m2];
        for h in 0..heads {
            let lists = &held.classes[h];
            let rows = &c.rows[h * sites..(h + 1) * sites];
            let crowds = &c.crowds[h * sites..(h + 1) * sites];
            let sums = &c.sums[h];
            let qh = &c.q[h * sites * span..(h + 1) * sites * span];
            let ph = &c.pq[h * sites * span..(h + 1) * sites * span];
            let back = CONTACT_BITS + FACE_BITS + self.decay(h, 0, 0).1 - super::super::COVECTOR_BITS;
            let mut ds: Vec<Vec<i128>> = Vec::with_capacity(sites);
            let mut dsc: Vec<Vec<i128>> = Vec::with_capacity(sites);
            for i in 0..sites {
                let temper = self.temper(h, lists.listens(i))?;
                let force = |p: u64| release(temper * release(p as i128, SHARE_BITS - CONTACT_BITS), MATERIAL_BITS);
                ds.push(rows[i].iter().map(|src| force(src.p)).collect());
                dsc.push(crowds[i].iter().map(|cr| force(cr.e)).collect());
            }
            let prefixed = |diff: &[i128]| -> Vec<i128> {
                let mut out = diff[..sites * span].to_vec();
                for t in 1..sites {
                    for r in 0..span {
                        out[t * span + r] += out[(t - 1) * span + r];
                    }
                }
                out
            };
            let mut col = vec![0i128; sites * span];
            let mut crowd_w = vec![0i128; (sites + 1) * span];
            for i in 0..sites {
                for (k, src) in rows[i].iter().enumerate() {
                    let j = src.j as usize;
                    for r in 0..span {
                        let (dec, g) = self.pair_decay(paces, h, r % n, i, j);
                        let bracket = release(((dec * ph[i * span + r] as i128) << g) - dec * dec * qh[j * span + r] as i128, g);
                        col[j * span + r] = col[j * span + r].checked_add(ds[i][k].checked_mul(bracket).ok_or(TowerError::Refused(KEY_RETURN))?).ok_or(TowerError::Refused(KEY_RETURN))?;
                    }
                }
                for (k, cr) in crowds[i].iter().enumerate() {
                    for r in 0..span {
                        let (dec, g) = self.octave_decay(paces, h, r % n, i, cr.level, cr.lo > i);
                        let mean = sums.words[(cr.hi + 1) * span + r] - sums.words[cr.lo * span + r];
                        let bracket = release(((dec * ph[i * span + r] as i128 * cr.count as i128) << g) - dec * dec * mean, g);
                        let part = div_nearest(dsc[i][k].checked_mul(bracket).ok_or(TowerError::Refused(KEY_RETURN))?, (cr.count * cr.count) as i128);
                        crowd_w[cr.lo * span + r] += part;
                        crowd_w[(cr.hi + 1) * span + r] -= part;
                    }
                }
            }
            let spread_w = prefixed(&crowd_w);
            for i in 0..sites {
                for r in 0..span {
                    let sq: i128 = rows[i].iter().enumerate().map(|(k, src)| ds[i][k] * self.pair_decay(paces, h, r % n, i, src.j as usize).0 * qh[src.j as usize * span + r] as i128).sum::<i128>()
                        + crowds[i].iter().enumerate().map(|(k, cr)| div_nearest(dsc[i][k] * self.octave_decay(paces, h, r % n, i, cr.level, cr.lo > i).0 * (sums.words[(cr.hi + 1) * span + r] - sums.words[cr.lo * span + r]), cr.count as i128)).sum::<i128>();
                    let k = h * n + r % n;
                    let slot = if r < n { k } else { m + k };
                    dp[i * m2 + slot] = fit64(release(sq, back))?;
                    dq[i * m2 + slot] = fit64(release(col[i * span + r], back))?;
                    if held.definite[i] {
                        dq[i * m2 + slot] = fit64(dq[i * m2 + slot] as i128 + release(spread_w[i * span + r], back))?;
                    }
                }
            }
        }
        // Through each word's ratio to its own power, then out of the frame.
        for (word, scale, cov) in [(&c.q, &c.qscale, &mut dq), (&c.pq, &c.pscale, &mut dp)] {
            for h in 0..heads {
                for t in 0..sites {
                    let at = (h * sites + t) * span;
                    let slot = |r: usize| t * m2 + if r < n { h * n + r } else { m + h * n + r - n };
                    let v: Vec<i64> = (0..span).map(|r| cov[slot(r)]).collect();
                    if v.iter().all(|&x| x == 0) {
                        continue;
                    }
                    let unit: Vec<i32> = word[at..at + span].iter().map(|&x| x as i32).collect();
                    for (r, b) in ratio_adjoint(&unit, scale[h * sites + t], &v)?.into_iter().enumerate() {
                        cov[slot(r)] = b;
                    }
                }
            }
        }
        for t in 0..sites {
            for k in 0..m {
                let (ur, ui) = self.frame(paces, t, k / n, k % n);
                let (ur, ui) = (ur as i128, ui as i128);
                for chart in [&mut dq, &mut dp] {
                    let (gr, gi) = (chart[t * m2 + k] as i128, chart[t * m2 + m + k] as i128);
                    chart[t * m2 + k] = fit64(release(ur * gr + ui * gi, MOVE_BITS))?;
                    chart[t * m2 + m + k] = fit64(release(ur * gi - ui * gr, MOVE_BITS))?;
                }
            }
        }
        let mut force = vec![0i64; sites * dw];
        let mut back = vec![0i64; dw];
        let add = |force: &mut [i64], t: usize, v: &[i64]| -> Result<()> {
            for (slot, &x) in force[t * dw..(t + 1) * dw].iter_mut().zip(v) {
                *slot = fit64(*slot as i128 + x as i128)?;
            }
            Ok(())
        };
        for (w, reach_w, cov) in [(l.q, reaches.q, &dq), (l.probe, reaches.probe, &dp)] {
            for t in 0..sites {
                transposed(&self.theta[w..w + m2 * dw], reach_w, dw, &cov[t * m2..(t + 1) * m2], MATERIAL_BITS, &mut back)?;
                add(&mut force, t, &back)?;
            }
        }
        // The pair: `−∂Φ/∂a_t = ∂ Re⟨c, a_t b_s⟩/∂a_t`, and so to the mate's `b`, on 2^(−24), through the drives' transposes.
        let half = f / 2;
        let mut da = vec![0i64; sites * f];
        let mut db = vec![0i64; sites * f];
        for t in 0..sites {
            for e in 0..half {
                let Some(s) = strand_mate(t, e, sites) else { continue };
                let (cr, ci) = (self.theta[l.pair_c + e] as i128, self.theta[l.pair_c + half + e] as i128);
                let (ar, ai) = (c.a[t * f + e] as i128, c.a[t * f + half + e] as i128);
                let (br, bi) = (c.b[s * f + e] as i128, c.b[s * f + half + e] as i128);
                da[t * f + e] = fit64(da[t * f + e] as i128 + release(cr * br + ci * bi, FACE_BITS))?;
                da[t * f + half + e] = fit64(da[t * f + half + e] as i128 + release(ci * br - cr * bi, FACE_BITS))?;
                db[s * f + e] = fit64(db[s * f + e] as i128 + release(cr * ar + ci * ai, FACE_BITS))?;
                db[s * f + half + e] = fit64(db[s * f + half + e] as i128 + release(ci * ar - cr * ai, FACE_BITS))?;
            }
        }
        for (w, reach_w, cov) in [(l.a, reaches.a, &da), (l.b, reaches.b, &db)] {
            for t in 0..sites {
                transposed(&self.theta[w..w + f * dw], reach_w, dw, &cov[t * f..(t + 1) * f], MATERIAL_BITS, &mut back)?;
                add(&mut force, t, &back)?;
            }
        }
        // The letters: `Rᵀ E(u_t)` from the site's own, its strand neighbours' contact rows and its moment's term.
        for t in 0..sites {
            transposed(&self.theta[l.read..l.read + dw * dw], reaches.read, dw, &held.letters.own[t], FACE_BITS, &mut back)?;
            for i in 0..dw {
                let mut v = back[i] as i128 + ((held.moment_term[t * dw + i] as i128) << (super::super::COVECTOR_BITS - FACE_BITS));
                if t > 0 {
                    v += (held.letters.before[t - 1][i] as i128) << (super::super::COVECTOR_BITS - FACE_BITS);
                }
                if t + 1 < sites {
                    v += (held.letters.after[t + 1][i] as i128) << (super::super::COVECTOR_BITS - FACE_BITS);
                }
                force[t * dw + i] = fit64(force[t * dw + i] as i128 + v)?;
            }
        }
        Ok((force, dp))
    }

    /// One descent step: each site's lanes moved by `2^(−h)` of their own scale a unit of force.
    fn energy_step(&self, x: &[i64], scale: &[i128], force: &[i64], h: u32) -> Result<Vec<i64>> {
        let d = &self.declaration;
        let (dw, lanes) = (d.width, d.lanes);
        let w = dw / lanes;
        let mut out = x.to_vec();
        for (k, slot) in out.iter_mut().enumerate() {
            let (t, i) = (k / dw, k % dw);
            let s = scale[t * lanes + i / w];
            *slot = fit64(*slot as i128 + release(s * force[k] as i128, super::super::COVECTOR_BITS + h))?;
        }
        Ok(out)
    }

    /// The moment's covector `dm` (`[t][2M]` on `2^(−24)`) transported back to each site's moment rows: the per-site
    /// covectors on its letter's before and after moment rows (`[t][2T]` each), as [`Field::moments_return`] reads them
    /// before they enter the encodings.
    fn moment_letters(&self, paces: &Paces, sites: usize, dm: &[i64]) -> Result<(Vec<Vec<i128>>, Vec<Vec<i128>>)> {
        let d = &self.declaration;
        let (m, n, tm) = (d.complex(), d.modes, d.moment_modes());
        let (mut db, mut da) = (vec![vec![0i128; 2 * tm]; sites], vec![vec![0i128; 2 * tm]; sites]);
        if tm == 0 {
            return Ok((db, da));
        }
        for h in (0..d.heads).filter(|&h| d.carries_moment(h) && !d.is_depth(h)) {
            for li in 0..n {
                let idx = d.moment_index(h) + li;
                let slot = self.slot(h, li);
                let (period, ring) = &self.rings[slot];
                let ds: Vec<(i64, i64)> = (0..sites).map(|t| (dm[t * 2 * m + h * n + li], dm[t * 2 * m + m + h * n + li])).collect();
                let (turn, skin) = (|r: i128| self.turn(slot, r), |s: i128| self.skin(slot, s));
                let pace = self.pace_of(paces, h, &turn, &skin);
                let (back_b, back_a) = moment::moments_return(&ds, ring, *period, &self.decays[slot], pace.as_ref())?;
                for t in 0..sites {
                    (db[t][idx], db[t][tm + idx]) = back_b[t];
                    (da[t][idx], da[t][tm + idx]) = back_a[t];
                }
            }
        }
        Ok((db, da))
    }

    /// The moments of a region, their term in the face (`C s_t + b` on `2^(−16)`, `[t][D]`) and its letters.
    fn energy_letters_of(&self, region: &Region, paces: &Paces, reaches: &Reaches) -> Result<(Letters, Vec<i64>, Vec<i64>)> {
        let d = &self.declaration;
        let (dw, m2) = (d.width, 2 * d.complex());
        let sites = region.classes.len();
        let l = &self.layout;
        let moment = self.moments_of(region, paces)?;
        let mut moment_term = vec![0i64; sites * dw];
        for t in 0..sites {
            affine(&self.theta[l.moment_face..l.moment_face + dw * m2], reaches.moment_face, m2, &moment[t * m2..(t + 1) * m2], Some(&self.theta[l.moment_face_bias..l.moment_face_bias + dw]), MATERIAL_BITS, MATERIAL_BITS, &mut moment_term[t * dw..(t + 1) * dw])?;
        }
        Ok((self.energy_letters(region), moment, moment_term))
    }

    /// The opening and `ticks` ticks of certified descent under the held supports ([`Relaxed`]).
    fn energy_relax(&self, region: &Region, ticks: usize) -> Result<Relaxed> {
        self.admit_region(region)?;
        let d = &self.declaration;
        if self.scale.is_some() {
            return refuse("an energy field read with a tower of scales (its energy is not built)");
        }
        let dw = d.width;
        let sites = region.classes.len();
        let reaches = self.reaches();
        let paces = self.paces(region)?;
        if paces.plain.iter().any(|&p| !p) {
            return refuse("an energy field read with a clock that is not plain (its letters' force through the frames is not built)");
        }
        let (letters, moment, moment_term) = self.energy_letters_of(region, &paces, &reaches)?;
        let mut x = self.open(region, &moment)?;
        let definite: Vec<bool> = (0..sites).map(|t| Self::definite(region, t)).collect();
        let keyed: Vec<bool> = (0..sites).map(|t| !region.unresolved[t] || Self::carried(region, t).is_some()).collect();
        let window = region.window(d.ticks);
        let (mut read0, mut scale0) = (Vec::with_capacity(sites * dw), Vec::with_capacity(sites * d.lanes));
        for xt in x.chunks_exact(dw) {
            lane_chart(xt, d.lanes, &mut read0, &mut scale0)?;
        }
        let classes = self.energy_classes(&read0, &moment, &definite, &keyed, &reaches)?;
        let held = Held { letters, moment, moment_term, classes, definite };
        let mut cell = self.energy_cell(&x, &held, &paces, &reaches, window.as_deref())?;
        let mut read = EnergyRead { opening: cell.phi, last: cell.phi, halvings: Vec::with_capacity(d.ticks), reads: 1, pairs: 0 };
        let mut pairs = cell.pairs;
        let mut first = FIRST_HALVINGS;
        for _ in 0..ticks {
            let (force, _) = self.energy_force(&cell, &held, &paces, &reaches)?;
            let mut stood = None;
            let mut h = first;
            while h <= MOST_HALVINGS {
                let next = self.energy_step(&x, &cell.scale, &force, h)?;
                if next == x {
                    break;
                }
                let candidate = self.energy_cell(&next, &held, &paces, &reaches, window.as_deref())?;
                read.reads += 1;
                pairs += candidate.pairs;
                // The fall is certified past the two reads' summed reading error, one unit of `2^(−32)` a logarithm.
                let slack = (cell.logs + candidate.logs) as i128 + 2;
                if candidate.phi + slack <= cell.phi {
                    x = next;
                    cell = candidate;
                    stood = Some(h);
                    break;
                }
                h += 1;
            }
            read.halvings.push(stood);
            match stood {
                Some(h) => first = h.saturating_sub(1),
                None => break,
            }
        }
        read.last = cell.phi;
        read.pairs = pairs;
        Ok(Relaxed { x, cell, held, paces, window, read })
    }

    /// [definition; the unified-theory reading of November 6, 22:52] **A region's forward under one energy**
    /// ([`energy`](self)): the opening, `K` ticks of certified descent under the held supports, and each unresolved site's
    /// face as the energy's force on its letter. Returns the pass's faces and readings (no tick is held: the return is not
    /// built), and the energy at the opening and at the last tick with each tick's halvings (`None` where it rested).
    pub(super) fn energy_pass(&self, region: &Region) -> Result<(FieldPass, EnergyRead)> {
        let Relaxed { cell, held, paces, read, .. } = self.energy_relax(region, self.declaration.ticks)?;
        let d = &self.declaration;
        let (dw, m2) = (d.width, 2 * d.complex());
        let sites = region.classes.len();
        let l = &self.layout;
        let reaches = self.reaches();
        let pairs = read.pairs;
        // The faces: each unresolved site's letter force at the last state.
        let (_, dp) = self.energy_force(&cell, &held, &paces, &reaches)?;
        let tm = d.moment_modes();
        let (fb, fa) = if tm > 0 {
            let mut dm = vec![0i64; sites * m2];
            let mut back = vec![0i64; m2];
            for t in 0..sites {
                transposed(&self.theta[l.moment_face..l.moment_face + dw * m2], reaches.moment_face, m2, &cell.read[t * dw..(t + 1) * dw].iter().map(|&v| v as i64).collect::<Vec<_>>(), FACE_BITS, &mut back)?;
                for k in 0..m2 {
                    dm[t * m2 + k] = fit64(back[k] as i128 + dp[t * m2 + k] as i128)?;
                }
            }
            self.moment_letters(&paces, sites, &dm)?
        } else {
            (Vec::new(), Vec::new())
        };
        let mut out = FieldPass { pairs, echo: vec![0; sites], read: vec![0i32; sites * dw], lift: vec![0i64; sites * dw], scale: vec![0i128; sites * d.lanes], faces: vec![None; sites], logits: vec![None; sites], ..Default::default() };
        let mut z = vec![0i64; d.alphabet];
        let dot = |row: &[i32], r: &[i32]| -> i128 { row.iter().zip(r).map(|(&e, &v)| e as i128 * v as i128).sum() };
        for t in 0..sites {
            if !region.unresolved[t] {
                continue;
            }
            let lift = &cell.lift[t * dw..(t + 1) * dw];
            self.tied(lift, &mut z)?;
            for (a, slot) in z.iter_mut().enumerate() {
                let mut strand = 0i128;
                if t + 1 < sites {
                    strand += dot(&self.theta[l.before + a * dw..l.before + (a + 1) * dw], &cell.read[(t + 1) * dw..(t + 2) * dw]);
                }
                if t > 0 {
                    strand += dot(&self.theta[l.after + a * dw..l.after + (a + 1) * dw], &cell.read[(t - 1) * dw..t * dw]);
                }
                let mut moment_part = 0i128;
                if tm > 0 {
                    for k in 0..2 * tm {
                        moment_part += self.theta[l.moment_before + a * 2 * tm + k] as i128 * fb[t][k] + self.theta[l.moment_after + a * 2 * tm + k] as i128 * fa[t][k];
                    }
                }
                *slot = fit64(*slot as i128 + release(strand, FACE_BITS) + release(moment_part, super::super::COVECTOR_BITS))?;
            }
            if let Some(Some(echo)) = region.echo.get(t) {
                for (zc, &lc) in z.iter_mut().zip(&echo.logits) {
                    *zc = fit64(*zc as i128 - release(echo.b as i128 * lc as i128, SHARE_BITS))?;
                }
            }
            out.faces[t] = Some(self.tempered(&z, 1));
            out.logits[t] = Some(z.clone());
            out.read[t * dw..(t + 1) * dw].copy_from_slice(&cell.read[t * dw..(t + 1) * dw]);
            out.lift[t * dw..(t + 1) * dw].copy_from_slice(lift);
            out.scale[t * d.lanes..(t + 1) * d.lanes].copy_from_slice(&cell.scale[t * d.lanes..(t + 1) * d.lanes]);
        }
        out.paces = paces;
        out.moment = held.moment;
        Ok((out, read))
    }

    /// [measurement; a test's reading] **The force is the energy's slope**: at the opening, the energy's fall under a step of
    /// `2^(−h)` beside the step's first-order fall `2^(−h) Σ_t (|F_t|² − ⟨r̂_t, F_t⟩²/W)` (each lane's), both on `2^(−32)` bits.
    #[cfg(test)]
    pub(super) fn energy_slope(&self, region: &Region, h: u32) -> Result<(i128, i128)> {
        let d = &self.declaration;
        let Relaxed { x, cell, held, paces, window, .. } = self.energy_relax(region, 0)?;
        let reaches = self.reaches();
        let (force, _) = self.energy_force(&cell, &held, &paces, &reaches)?;
        let next = self.energy_step(&x, &cell.scale, &force, h)?;
        let after = self.energy_cell(&next, &held, &paces, &reaches, window.as_deref())?;
        let (dw, lanes) = (d.width, d.lanes);
        let w = dw / lanes;
        // |F|² on 2^(−48), ⟨r̂, F⟩² on 2^(−80) over the lane's width.
        let mut first = 0i128;
        for t in 0..x.len() / dw {
            for k in 0..lanes {
                let at = t * dw + k * w;
                let ff: i128 = (0..w).map(|i| force[at + i] as i128 * force[at + i] as i128).sum();
                let rf: i128 = (0..w).map(|i| force[at + i] as i128 * cell.read[at + i] as i128).sum();
                first += ff - release(div_nearest(rf * rf, w as i128), 32);
            }
        }
        Ok((release(first, 16 + h), cell.phi - after.phi))
    }

    /// [measurement; a test's reading] The energy at a region's relaxed state with site `t`'s letter set to each of
    /// `letters` (the state, the supports and the clocks held), beside the region's faces: at fixed state the face is the
    /// energy's force on the letter, so `Φ(b) − Φ(a) = −(z_t(b) − z_t(a))` where the energy is linear in the letter.
    #[cfg(test)]
    pub(super) fn energy_at_letters(&self, region: &Region, t: usize, letters: &[usize]) -> Result<Vec<i128>> {
        let Relaxed { x, held, paces, window, .. } = self.energy_relax(region, self.declaration.ticks)?;
        let reaches = self.reaches();
        let mut out = Vec::with_capacity(letters.len());
        for &a in letters {
            let mut classes = region.classes.to_vec();
            let mut unresolved = region.unresolved.to_vec();
            classes[t] = a;
            unresolved[t] = false;
            let set = Region { classes: &classes, unresolved: &unresolved, ..*region };
            let (letters, moment, moment_term) = self.energy_letters_of(&set, &paces, &reaches)?;
            let with = Held { letters, moment, moment_term, classes: held.classes.clone(), definite: held.definite.clone() };
            out.push(self.energy_cell(&x, &with, &paces, &reaches, window.as_deref())?.phi);
        }
        Ok(out)
    }

    /// [measurement] **A region's energy read** ([`EnergyRead`]): the energy at the opening and at the last tick, each
    /// tick's halvings, and the energy's reads.
    pub fn energy_read(&self, region: &Region) -> Result<EnergyRead> {
        if !self.declaration.energy {
            return refuse("an energy read of a field whose faces are not one energy's forces");
        }
        Ok(self.energy_pass(region)?.1)
    }
}

/// [measurement] A region's energy across its ticks: `Φ` on `2^(−32)` bits at the opening and at the last tick, each
/// tick's halvings (`None` where no halving certified a fall and the state rested), and the energy's reads.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EnergyRead {
    pub opening: i128,
    pub last: i128,
    pub halvings: Vec<Option<u32>>,
    pub reads: u64,
    /// The site pairs the locks met over every read.
    pub pairs: u64,
}
