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
pub const FIRST_HALVINGS: u32 = 2;
/// [definition; theory, November 8 02:56, retiring `MOST_HALVINGS = STATE_BITS + 8`] **The halvings a tick may read are
/// bounded by the step itself**: a tick halves its step until a fall stands or the step moves nothing (it rests when every
/// coordinate's step releases to zero, at most its own bit length on the state's grain plus one halvings: the census read
/// that step at 42 places, so the old bound of 24, whose reason was that past it the step lies below the grain, did not
/// hold). The one bound left is the release's carrier: the step `release(s·F, COVECTOR_BITS + h)` is read on a 128-place
/// word, so `h` stops where the shift would leave it. The rest by the step's own width comes first for every step a word
/// holds, so the bits are those of the old law wherever no tick read past 24 halvings (every tick the census read).
pub const STEP_CARRIER_HALVINGS: u32 = 126 - super::super::COVECTOR_BITS;

/// The width census's reads (c) and (g) ([`crate::number::census`]).
const CENSUS_RELAXED: &str = "relaxation: regions relaxed";
const CENSUS_ALL_TICKS: &str = "relaxation: regions that stood at every tick";
const CENSUS_REST_GRAIN: &str = "relaxation: rested, the step below the state's grain";
const CENSUS_REST_HALVINGS: &str = "relaxation: rested, no fall past the slack by the step's carrier";
const CENSUS_INSIDE_SLACK: &str = "relaxation: a fall inside the slack 2R + 2";
const CENSUS_SLACK: &str = "relaxation: the slack 2R + 2, on 2^-32";
const CENSUS_STOOD_AT: &str = "relaxation: the halvings a tick stood at";
const CENSUS_STEP_AT_NO_HALVING: &str = "relaxation: |scale x force| on the state's grain at no halving";

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

/// The energy's force on the chart reads and on the words it is read through, or their tangents: `[t][D]` on the reads,
/// the keys' and probes' unframed `[t][2M]`, the pair drives' `[t][f]`, all on `2^(−24)`.
struct ForceParts {
    force: Vec<i64>,
    keys: Vec<i64>,
    probes: Vec<i64>,
    a: Vec<i64>,
    b: Vec<i64>,
}

/// The locks' force on the words and its tangent ([`Field::lock_words`]), each `[t][2M]` on `2^(−24)` in the framed unit
/// chart: the keys' and the probes', and their tangents (empty without one).
struct LockWords {
    dq: Vec<i64>,
    dp: Vec<i64>,
    tq: Vec<i64>,
    tp: Vec<i64>,
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
    /// Each tick that stood: the state it stepped from, that state's read, its force and its halvings.
    trail: Vec<Step>,
}

/// A tick that stood ([`Relaxed::trail`]).
struct Step {
    cell: EnergyCell,
    force: Vec<i64>,
    halvings: u32,
}

/// [definition; the unified-theory reading of November 7, 00:02] The letters' covectors of the region's opening and ticks,
/// `(∂x⁰/∂e)ᵀ λ⁰ + Σ_k (∂x^(k+1)/∂e)ᵀ λ^(k+1)` read on each site's rows: its own encoding row's, its before and after contact
/// rows' (`[t][D]`), and its moment's (`[t][2M]`), all on `2^(−24)`.
struct LetterCovectors {
    own: Vec<i64>,
    before: Vec<i64>,
    after: Vec<i64>,
    moment: Vec<i64>,
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
        // [definition; the unified-theory reading of November 7, 23:34] The width law: each head's lists over its leaves.
        if let Some(cap) = self.widen {
            let words = |w: &[i64], h: usize| -> Vec<Vec<(i64, i64)>> { (0..sites).map(|t| (0..n).map(|li| (w[t * m2 + h * n + li], w[t * m2 + m + h * n + li])).collect()).collect() };
            return Ok((0..heads).map(|h| ClassLists::widened(&words(&q, h), &words(&pr, h), definite.to_vec(), trits, cap).0.keyed(keyed.to_vec())).collect());
        }
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
        let carried = |v: Option<i128>| v.inspect(|v| crate::number::census::reach("a lock past its 128-bit carrier", v)).ok_or(TowerError::Refused("a lock past its 128-bit carrier"));
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

    /// [definition; the unified-theory reading of November 6, 22:52] **The locks' force on the words** in each head's framed
    /// unit chart (`[t][2M]`, before the unit power's return, on `2^(−24)`): the row's share is the force on its score
    /// (`−∂Φ/∂z_ij = p_ij`, carried to `2^(−40)` as the reverse's score covector), and each mode's lock returns to its two
    /// words as the tick's reverse reads it: the probe `Σ_j p_ij T D k̂_j`, each key `Σ_i p_ij T (D p̂_i − D² k̂_j)`, a crowd at
    /// its mean word. With a tangent of the unit words `(δk̂, δp̂)` (`[h][t][2n]` on `2^(−24)`) also the forces' tangents: the
    /// scores' `δz = T Σ_m (D(δp̂·k̂ + p̂·δk̂) − D² k̂·δk̂)`, the shares' `δp = ln 2 · p (δz − Σ p δz)`, and the brackets'.
    fn lock_words(&self, c: &EnergyCell, held: &Held, paces: &Paces, tangent: Option<(&[i64], &[i64])>) -> Result<LockWords> {
        let d = &self.declaration;
        let (m, n, heads) = (d.complex(), d.modes, d.heads);
        let m2 = 2 * m;
        let span = 2 * n;
        let sites = held.definite.len();
        let ln2 = ln2_face();
        let mut out = LockWords { dq: vec![0i64; sites * m2], dp: vec![0i64; sites * m2], tq: Vec::new(), tp: Vec::new() };
        if tangent.is_some() {
            out.tq = vec![0i64; sites * m2];
            out.tp = vec![0i64; sites * m2];
        }
        let carry = |what: &'static str, v: Option<i128>| v.inspect(|x| crate::number::census::reach(what, x)).ok_or(TowerError::Refused(what));
        for h in 0..heads {
            let lists = &held.classes[h];
            let rows = &c.rows[h * sites..(h + 1) * sites];
            let crowds = &c.crowds[h * sites..(h + 1) * sites];
            let sums = &c.sums[h];
            let qh = &c.q[h * sites * span..(h + 1) * sites * span];
            let ph = &c.pq[h * sites * span..(h + 1) * sites * span];
            let g0 = self.decay(h, 0, 0).1;
            let back = CONTACT_BITS + FACE_BITS + g0 - super::super::COVECTOR_BITS;
            let tangent_h = tangent.map(|(tk, tp)| (&tk[h * sites * span..(h + 1) * sites * span], &tp[h * sites * span..(h + 1) * sites * span]));
            let zeros = vec![0i64; sites * span];
            let tsums = tangent_h.map(|(tk, _)| Sums::of(tk, &zeros, &held.definite, span));
            let mut ds: Vec<Vec<i128>> = Vec::with_capacity(sites);
            let mut dsc: Vec<Vec<i128>> = Vec::with_capacity(sites);
            let mut tds: Vec<Vec<i128>> = Vec::with_capacity(sites);
            let mut tdsc: Vec<Vec<i128>> = Vec::with_capacity(sites);
            for i in 0..sites {
                let temper = self.temper(h, lists.listens(i))?;
                let force = |p: i128| release(temper * release(p, SHARE_BITS - CONTACT_BITS), MATERIAL_BITS);
                ds.push(rows[i].iter().map(|src| force(src.p as i128)).collect());
                dsc.push(crowds[i].iter().map(|cr| force(cr.e as i128)).collect());
                let Some((tk, tp)) = tangent_h else { continue };
                let ts = tsums.as_ref().expect("a tangent's sums");
                // The scores' tangents on 2^(−40).
                let mut dz: Vec<i128> = Vec::with_capacity(rows[i].len() + crowds[i].len());
                for src in &rows[i] {
                    let j = src.j as usize;
                    let mut acc = 0i128;
                    let mut g_ = 0u32;
                    for li in 0..n {
                        let (dec, g) = self.pair_decay(paces, h, li, i, j);
                        g_ = g;
                        let mut pair = 0i128;
                        let mut power = 0i128;
                        for r in [li, n + li] {
                            pair += tp[i * span + r] as i128 * qh[j * span + r] as i128 + ph[i * span + r] as i128 * tk[j * span + r] as i128;
                            power += qh[j * span + r] as i128 * tk[j * span + r] as i128;
                        }
                        acc = carry("a lock score's tangent past its 128-bit carrier", acc.checked_add(carry("a lock score's tangent past its 128-bit carrier", (dec * pair).checked_mul(1i128 << g))? - dec * dec * power))?;
                    }
                    dz.push(release(temper * release(acc, 2 * g_), MATERIAL_BITS));
                }
                for cr in &crowds[i] {
                    let count = cr.count as i128;
                    let mut acc = 0i128;
                    let mut g_ = 0u32;
                    for li in 0..n {
                        let (dec, g) = self.octave_decay(paces, h, li, i, cr.level, cr.lo > i);
                        g_ = g;
                        // [agent-inferred, November 7] A crowd's tangent reads its mean word `m = W/|C|` and its tangent `δm`
                        // (each to the nearest on its grain), as a source at the mean: the count's square never multiplies a
                        // tangent, whose words carry the reverse's covectors (a writer state's crowds passed the 128-bit
                        // carrier read through `|C|²`, energy131's temper read).
                        let mut pair = 0i128;
                        let mut power = 0i128;
                        for r in [li, n + li] {
                            let w = div_nearest(sums.words[(cr.hi + 1) * span + r] - sums.words[cr.lo * span + r], count);
                            let dw = div_nearest(ts.words[(cr.hi + 1) * span + r] - ts.words[cr.lo * span + r], count);
                            pair += tp[i * span + r] as i128 * w + ph[i * span + r] as i128 * dw;
                            power += w * dw;
                        }
                        acc = carry("a crowd score's tangent past its 128-bit carrier", acc.checked_add(carry("a crowd score's tangent past its 128-bit carrier", (dec * pair).checked_mul(1i128 << g))? - dec * dec * power))?;
                    }
                    dz.push(release(temper * release(acc, 2 * g_), MATERIAL_BITS));
                }
                // The shares' tangents on 2^(−63): `ln 2 · p (δz − Σ p δz)`.
                let shares: Vec<i128> = rows[i].iter().map(|s| s.p as i128).chain(crowds[i].iter().map(|cr| cr.e as i128)).collect();
                let mean = release(shares.iter().zip(&dz).map(|(&p, &z)| p * z).sum::<i128>(), SHARE_BITS);
                let dp: Vec<i128> = shares.iter().zip(&dz).map(|(&p, &z)| release(ln2 * release(p * (z - mean), CONTACT_BITS), MOVE_BITS)).collect();
                tds.push(dp[..rows[i].len()].iter().map(|&p| force(p)).collect());
                tdsc.push(dp[rows[i].len()..].iter().map(|&p| force(p)).collect());
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
            let (mut tcol, mut tcrowd_w) = (vec![0i128; sites * span], vec![0i128; (sites + 1) * span]);
            for i in 0..sites {
                for (k, src) in rows[i].iter().enumerate() {
                    let j = src.j as usize;
                    for r in 0..span {
                        let (dec, g) = self.pair_decay(paces, h, r % n, i, j);
                        let bracket = release(((dec * ph[i * span + r] as i128) << g) - dec * dec * qh[j * span + r] as i128, g);
                        col[j * span + r] = carry("a key's column past its 128-bit carrier", col[j * span + r].checked_add(carry("a key's column past its 128-bit carrier", ds[i][k].checked_mul(bracket))?))?;
                        if let Some((tk, tp)) = tangent_h {
                            let tbracket = release(((dec * tp[i * span + r] as i128) << g) - dec * dec * tk[j * span + r] as i128, g);
                            let v = carry("a key's tangent bracket past its 128-bit carrier", carry("a key's tangent bracket past its 128-bit carrier", tds[i][k].checked_mul(bracket))?.checked_mul(1 << 8))? + carry("a key's tangent bracket past its 128-bit carrier", ds[i][k].checked_mul(tbracket))?;
                            tcol[j * span + r] = carry("a key's tangent column past its 128-bit carrier", tcol[j * span + r].checked_add(v))?;
                        }
                    }
                }
                for (k, cr) in crowds[i].iter().enumerate() {
                    let count = cr.count as i128;
                    for r in 0..span {
                        let (dec, g) = self.octave_decay(paces, h, r % n, i, cr.level, cr.lo > i);
                        let mean = sums.words[(cr.hi + 1) * span + r] - sums.words[cr.lo * span + r];
                        let bracket = release(((dec * ph[i * span + r] as i128 * count) << g) - dec * dec * mean, g);
                        let part = div_nearest(carry("a crowd key's part past its 128-bit carrier", dsc[i][k].checked_mul(bracket))?, count * count);
                        crowd_w[cr.lo * span + r] += part;
                        crowd_w[(cr.hi + 1) * span + r] -= part;
                        if let Some((_, tp)) = tangent_h {
                            // At the mean word, as the score's tangent reads it: each member's key force `p_C T (D p̂ − D² m)/|C|`.
                            let ts = tsums.as_ref().expect("a tangent's sums");
                            let m_ = div_nearest(mean, count);
                            let tm = div_nearest(ts.words[(cr.hi + 1) * span + r] - ts.words[cr.lo * span + r], count);
                            let bracket_m = release(((dec * ph[i * span + r] as i128) << g) - dec * dec * m_, g);
                            let tbracket = release(((dec * tp[i * span + r] as i128) << g) - dec * dec * tm, g);
                            let v = carry("a crowd key's tangent part past its 128-bit carrier", carry("a crowd key's tangent part past its 128-bit carrier", tdsc[i][k].checked_mul(bracket_m))?.checked_mul(1 << 8))? + carry("a crowd key's tangent part past its 128-bit carrier", dsc[i][k].checked_mul(tbracket))?;
                            let part = div_nearest(v, count);
                            tcrowd_w[cr.lo * span + r] += part;
                            tcrowd_w[(cr.hi + 1) * span + r] -= part;
                        }
                    }
                }
            }
            let spread_w = prefixed(&crowd_w);
            let tspread_w = prefixed(&tcrowd_w);
            for i in 0..sites {
                for r in 0..span {
                    let k = h * n + r % n;
                    let slot = i * m2 + if r < n { k } else { m + k };
                    let mut sq = 0i128;
                    let mut tsq = 0i128;
                    for (kk, src) in rows[i].iter().enumerate() {
                        let j = src.j as usize;
                        let dec = self.pair_decay(paces, h, r % n, i, j).0;
                        sq += ds[i][kk] * dec * qh[j * span + r] as i128;
                        if let Some((tk, _)) = tangent_h {
                            tsq += ((tds[i][kk] * dec * qh[j * span + r] as i128) << 8) + ds[i][kk] * dec * tk[j * span + r] as i128;
                        }
                    }
                    for (kk, cr) in crowds[i].iter().enumerate() {
                        let dec = self.octave_decay(paces, h, r % n, i, cr.level, cr.lo > i).0;
                        let w = sums.words[(cr.hi + 1) * span + r] - sums.words[cr.lo * span + r];
                        sq += div_nearest(dsc[i][kk] * dec * w, cr.count as i128);
                        if tangent_h.is_some() {
                            // At the mean word, as the score's tangent reads it.
                            let ts = tsums.as_ref().expect("a tangent's sums");
                            let m_ = div_nearest(w, cr.count as i128);
                            let tm = div_nearest(ts.words[(cr.hi + 1) * span + r] - ts.words[cr.lo * span + r], cr.count as i128);
                            tsq += ((tdsc[i][kk] * dec * m_) << 8) + dsc[i][kk] * dec * tm;
                        }
                    }
                    out.dp[slot] = fit64(release(sq, back))?;
                    out.dq[slot] = fit64(release(col[i * span + r], back))?;
                    if held.definite[i] {
                        out.dq[slot] = fit64(out.dq[slot] as i128 + release(spread_w[i * span + r], back))?;
                    }
                    if tangent_h.is_some() {
                        out.tp[slot] = fit64(release(tsq, back + 8))?;
                        out.tq[slot] = fit64(release(tcol[i * span + r], back + 8))?;
                        if held.definite[i] {
                            out.tq[slot] = fit64(out.tq[slot] as i128 + release(tspread_w[i * span + r], back + 8))?;
                        }
                    }
                }
            }
        }
        Ok(out)
    }

    /// The energy's force on each site's chart read, `−∂Φ/∂r̂` (`[t][D]` on `2^(−24)`), and the probes' share of it
    /// `[t][2M]` (unframed, on `2^(−24)`), whose turned modes the moment's face reads.
    fn energy_force(&self, c: &EnergyCell, held: &Held, paces: &Paces, reaches: &Reaches) -> Result<(Vec<i64>, Vec<i64>)> {
        let parts = self.energy_force_parts(c, held, paces, reaches)?;
        Ok((parts.force, parts.probes))
    }

    /// [`Field::energy_force`] with the forces on its words beside it ([`ForceParts`]).
    fn energy_force_parts(&self, c: &EnergyCell, held: &Held, paces: &Paces, reaches: &Reaches) -> Result<ForceParts> {
        let d = &self.declaration;
        let (dw, m, n, f, heads) = (d.width, d.complex(), d.modes, d.contacts, d.heads);
        let m2 = 2 * m;
        let span = 2 * n;
        let sites = held.definite.len();
        let l = &self.layout;
        let LockWords { mut dq, mut dp, .. } = self.lock_words(c, held, paces, None)?;
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
        Ok(ForceParts { force, keys: dq, probes: dp, a: da, b: db })
    }

    /// [definition; the unified-theory reading of November 7, 00:02] **The force's tangent**, `δF = (∂F/∂r̂) v = −Hess Φ · v`
    /// along a direction `v` of the chart reads (`[t][D]` on `2^(−24)`), and the probes' share of it (`[t][2M]`, unframed,
    /// on `2^(−24)`): the words' tangents through the charts, the frame and the unit power (whose Jacobian is its own
    /// return, [`ratio_adjoint`]), the locks' ([`Field::lock_words`]), the unit power's return differentiated along them
    /// (`δ(J f) = J δf − (δŵ⟨ŵ, f⟩ + ŵ⟨δŵ, f⟩)/(d ‖w̃‖) − J f ⟨ŵ, δw̃⟩/(d ‖w̃‖)`), the frame's and the charts' transposes, and the
    /// pair's (linear in each drive). The letters' force does not move with the state. `Φ`'s Hessian is symmetric, so the
    /// tangent is also the tick's adjoint on a covector.
    fn energy_tangent(&self, c: &EnergyCell, held: &Held, paces: &Paces, reaches: &Reaches, v: &[i64]) -> Result<(Vec<i64>, Vec<i64>)> {
        let parts = self.energy_tangent_parts(c, held, paces, reaches, v)?;
        Ok((parts.force, parts.probes))
    }

    /// [`Field::energy_tangent`] with the tangents of the forces on its words beside it ([`ForceParts`]).
    fn energy_tangent_parts(&self, c: &EnergyCell, held: &Held, paces: &Paces, reaches: &Reaches, v: &[i64]) -> Result<ForceParts> {
        let d = &self.declaration;
        let (dw, m, n, f, heads) = (d.width, d.complex(), d.modes, d.contacts, d.heads);
        let m2 = 2 * m;
        let span = 2 * n;
        let sites = held.definite.len();
        let l = &self.layout;
        // The words' tangents, framed and through the unit power: `[h][t][2n]` on 2^(−24).
        let mut wq = vec![0i64; m2];
        let mut wp = vec![0i64; m2];
        let (mut fq, mut fp) = (vec![0i64; heads * sites * span], vec![0i64; heads * sites * span]);
        for t in 0..sites {
            let vt = &v[t * dw..(t + 1) * dw];
            affine(&self.theta[l.q..l.q + m2 * dw], reaches.q, dw, vt, None, 0, MATERIAL_BITS, &mut wq)?;
            affine(&self.theta[l.probe..l.probe + m2 * dw], reaches.probe, dw, vt, None, 0, MATERIAL_BITS, &mut wp)?;
            for h in 0..heads {
                let at = (h * sites + t) * span;
                for li in 0..n {
                    let k = h * n + li;
                    let (ur, ui) = self.frame(paces, t, h, li);
                    let (ur, ui) = (ur as i128, ui as i128);
                    for (word, out) in [(&wq, &mut fq), (&wp, &mut fp)] {
                        let (wr, wi) = (word[k] as i128, word[m + k] as i128);
                        out[at + li] = fit64(release(ur * wr - ui * wi, MOVE_BITS))?;
                        out[at + n + li] = fit64(release(ui * wr + ur * wi, MOVE_BITS))?;
                    }
                }
            }
        }
        let (mut uq, mut up) = (vec![0i64; heads * sites * span], vec![0i64; heads * sites * span]);
        for (word, scale, framed, out) in [(&c.q, &c.qscale, &fq, &mut uq), (&c.pq, &c.pscale, &fp, &mut up)] {
            for hs in 0..heads * sites {
                let unit: Vec<i32> = word[hs * span..(hs + 1) * span].iter().map(|&x| x as i32).collect();
                let back = ratio_adjoint(&unit, scale[hs], &framed[hs * span..(hs + 1) * span])?;
                out[hs * span..(hs + 1) * span].copy_from_slice(&back);
            }
        }
        let LockWords { dq, dp, tq, tp } = self.lock_words(c, held, paces, Some((&uq, &up)))?;
        // The unit power's return and its tangent, then out of the frame: `[t][2M]`.
        let (mut cq, mut cp) = (vec![0i64; sites * m2], vec![0i64; sites * m2]);
        for (word, scale, framed, unit_t, force, tforce, out) in [(&c.q, &c.qscale, &fq, &uq, &dq, &tq, &mut cq), (&c.pq, &c.pscale, &fp, &up, &dp, &tp, &mut cp)] {
            for h in 0..heads {
                for t in 0..sites {
                    let hs = h * sites + t;
                    let slot = |r: usize| t * m2 + if r < n { h * n + r } else { m + h * n + r - n };
                    let fv: Vec<i64> = (0..span).map(|r| force[slot(r)]).collect();
                    let tv: Vec<i64> = (0..span).map(|r| tforce[slot(r)]).collect();
                    let scale_hs = scale[hs];
                    if scale_hs == 0 {
                        continue;
                    }
                    let unit: Vec<i32> = word[hs * span..(hs + 1) * span].iter().map(|&x| x as i32).collect();
                    let du = &unit_t[hs * span..(hs + 1) * span];
                    let dwt = &framed[hs * span..(hs + 1) * span];
                    let jf = ratio_adjoint(&unit, scale_hs, &fv)?;
                    let base = ratio_adjoint(&unit, scale_hs, &tv)?;
                    let a_wf: i128 = unit.iter().zip(&fv).map(|(&u, &x)| u as i128 * x as i128).sum();
                    let b_df: i128 = du.iter().zip(&fv).map(|(&u, &x)| u as i128 * x as i128).sum();
                    let c_wd: i128 = unit.iter().zip(dwt).map(|(&u, &x)| u as i128 * x as i128).sum();
                    let den = span as i128 * scale_hs;
                    for r in 0..span {
                        let s1 = du[r] as i128 * a_wf + unit[r] as i128 * b_df;
                        let corr = release(div_nearest(-(s1 << FACE_BITS), den), 2 * FACE_BITS + 8) + release(div_nearest(-((jf[r] as i128 * c_wd) << FACE_BITS), den), 2 * FACE_BITS + 8);
                        out[slot(r)] = fit64(base[r] as i128 + corr)?;
                    }
                }
            }
        }
        for t in 0..sites {
            for k in 0..m {
                let (ur, ui) = self.frame(paces, t, k / n, k % n);
                let (ur, ui) = (ur as i128, ui as i128);
                for chart in [&mut cq, &mut cp] {
                    let (gr, gi) = (chart[t * m2 + k] as i128, chart[t * m2 + m + k] as i128);
                    chart[t * m2 + k] = fit64(release(ur * gr + ui * gi, MOVE_BITS))?;
                    chart[t * m2 + m + k] = fit64(release(ur * gi - ui * gr, MOVE_BITS))?;
                }
            }
        }
        let mut out = vec![0i64; sites * dw];
        let mut back = vec![0i64; dw];
        let add = |out: &mut [i64], t: usize, v: &[i64]| -> Result<()> {
            for (slot, &x) in out[t * dw..(t + 1) * dw].iter_mut().zip(v) {
                *slot = fit64(*slot as i128 + x as i128)?;
            }
            Ok(())
        };
        for (w, reach_w, cov) in [(l.q, reaches.q, &cq), (l.probe, reaches.probe, &cp)] {
            for t in 0..sites {
                transposed(&self.theta[w..w + m2 * dw], reach_w, dw, &cov[t * m2..(t + 1) * m2], MATERIAL_BITS, &mut back)?;
                add(&mut out, t, &back)?;
            }
        }
        // The pair: each drive's force is linear in the other's drive, `δ(∂/∂a_t) = c ⊙ δb_s`, through the transposes.
        let half = f / 2;
        let (mut ta, mut tb) = (vec![0i64; sites * f], vec![0i64; sites * f]);
        for t in 0..sites {
            let vt = &v[t * dw..(t + 1) * dw];
            affine(&self.theta[l.a..l.a + f * dw], reaches.a, dw, vt, None, 0, MATERIAL_BITS, &mut ta[t * f..(t + 1) * f])?;
            affine(&self.theta[l.b..l.b + f * dw], reaches.b, dw, vt, None, 0, MATERIAL_BITS, &mut tb[t * f..(t + 1) * f])?;
        }
        let (mut da, mut db) = (vec![0i64; sites * f], vec![0i64; sites * f]);
        for t in 0..sites {
            for e in 0..half {
                let Some(s) = strand_mate(t, e, sites) else { continue };
                let (cr, ci) = (self.theta[l.pair_c + e] as i128, self.theta[l.pair_c + half + e] as i128);
                let (ar, ai) = (ta[t * f + e] as i128, ta[t * f + half + e] as i128);
                let (br, bi) = (tb[s * f + e] as i128, tb[s * f + half + e] as i128);
                da[t * f + e] = fit64(da[t * f + e] as i128 + release(cr * br + ci * bi, MATERIAL_BITS))?;
                da[t * f + half + e] = fit64(da[t * f + half + e] as i128 + release(ci * br - cr * bi, MATERIAL_BITS))?;
                db[s * f + e] = fit64(db[s * f + e] as i128 + release(cr * ar + ci * ai, MATERIAL_BITS))?;
                db[s * f + half + e] = fit64(db[s * f + half + e] as i128 + release(ci * ar - cr * ai, MATERIAL_BITS))?;
            }
        }
        for (w, reach_w, cov) in [(l.a, reaches.a, &da), (l.b, reaches.b, &db)] {
            for t in 0..sites {
                transposed(&self.theta[w..w + f * dw], reach_w, dw, &cov[t * f..(t + 1) * f], MATERIAL_BITS, &mut back)?;
                add(&mut out, t, &back)?;
            }
        }
        Ok(ForceParts { force: out, keys: cq, probes: cp, a: da, b: db })
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
            // The width census's read (g): `|scale × force|` on the state's grain at no halving, against the
            // `STATE_BITS + 8` halvings the retired `MOST_HALVINGS` read.
            if crate::number::census::enabled() {
                crate::number::census::reach(CENSUS_STEP_AT_NO_HALVING, &(s * force[k] as i128 >> super::super::COVECTOR_BITS));
            }
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

    /// [definition; the unified-theory reading of November 7, 00:02] **An open site stays a source carrying the locked
    /// mixture**: every unresolved site with no carried face is read as carrying the uniform mixture over the alphabet,
    /// locked, so it is a definite keyed source and no receiver listens (§16.20's exclusion of the unresolved site goes in an
    /// energy field). Why: the face is one scalar's gradient only where every letter state compared is read in one
    /// structure; an open site read apart (unkeyed, a listener at its own temperature, no crowds) makes the energy of a
    /// region with `i` open another function than the energy with `j` open. Returns the region's faces and locks so read
    /// (public: a realization stages these sites, `holonics_cuda::hnn::CardField`'s energy forward).
    pub fn energy_sites(&self, region: &Region) -> (Vec<Option<Shares>>, Vec<bool>) {
        let alphabet = self.declaration.alphabet as u32;
        let uniform: Shares = (0..alphabet).map(|c| (c, (1u32 << STATE_BITS) / alphabet)).collect();
        let sites = region.classes.len();
        let mut faces: Vec<Option<Shares>> = (0..sites).map(|t| region.faces.get(t).cloned().flatten()).collect();
        let mut locked: Vec<bool> = (0..sites).map(|t| region.locked.get(t).copied().unwrap_or(false)).collect();
        for t in 0..sites {
            if region.unresolved[t] && faces[t].is_none() {
                faces[t] = Some(uniform.clone());
                locked[t] = true;
            }
        }
        (faces, locked)
    }

    /// The opening and `ticks` ticks of certified descent under the held supports ([`Relaxed`]).
    fn energy_relax(&self, region: &Region, ticks: usize, replay: Option<&[Option<u32>]>, base: Option<&Held>) -> Result<Relaxed> {
        let (faces, locked) = self.energy_sites(region);
        let region = &Region { faces: &faces, locked: &locked, ..*region };
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
        // A base's classes and supports are held where one is given (the derivative's one scalar, read at other letters).
        let (classes, definite) = match base {
            Some(b) => (b.classes.clone(), b.definite.clone()),
            None => (self.energy_classes(&read0, &moment, &definite, &keyed, &reaches)?, definite),
        };
        let held = Held { letters, moment, moment_term, classes, definite };
        let mut cell = self.energy_cell(&x, &held, &paces, &reaches, window.as_deref())?;
        let mut read = EnergyRead { opening: cell.phi, last: cell.phi, halvings: Vec::with_capacity(d.ticks), reads: 1, pairs: 0 };
        let mut pairs = cell.pairs;
        let mut first = FIRST_HALVINGS;
        let mut trail = Vec::new();
        for k in 0..ticks {
            let (force, _) = self.energy_force(&cell, &held, &paces, &reaches)?;
            // A replay steps at the halvings it is given, uncertified (the base's descent read again on other letters).
            if let Some(hs) = replay {
                let Some(Some(h)) = hs.get(k).copied() else { break };
                let next = self.energy_step(&x, &cell.scale, &force, h)?;
                let candidate = self.energy_cell(&next, &held, &paces, &reaches, window.as_deref())?;
                read.reads += 1;
                pairs += candidate.pairs;
                read.halvings.push(Some(h));
                trail.push(Step { cell: std::mem::replace(&mut cell, candidate), force, halvings: h });
                x = next;
                continue;
            }
            let mut stood = None;
            let mut h = first;
            // The width census's read (c): why a tick rests (its step below the state's grain, or no fall past the slack
            // by the step's carrier), each fall that stayed inside the slack, and the slack's `R`.
            let census = crate::number::census::enabled();
            let mut below_grain = false;
            while h <= STEP_CARRIER_HALVINGS {
                let next = self.energy_step(&x, &cell.scale, &force, h)?;
                if next == x {
                    below_grain = true;
                    break;
                }
                let candidate = self.energy_cell(&next, &held, &paces, &reaches, window.as_deref())?;
                read.reads += 1;
                pairs += candidate.pairs;
                // The fall is certified past the two reads' summed reading error, one unit of `2^(−32)` a logarithm.
                let slack = (cell.logs + candidate.logs) as i128 + 2;
                if census {
                    crate::number::census::reach(CENSUS_SLACK, &slack);
                    if candidate.phi < cell.phi && candidate.phi + slack > cell.phi {
                        crate::number::census::tally(CENSUS_INSIDE_SLACK, 1);
                    }
                }
                if candidate.phi + slack <= cell.phi {
                    x = next;
                    trail.push(Step { cell: std::mem::replace(&mut cell, candidate), force: force.clone(), halvings: h });
                    stood = Some(h);
                    break;
                }
                h += 1;
            }
            read.halvings.push(stood);
            match stood {
                Some(h) => {
                    if census {
                        crate::number::census::reach(CENSUS_STOOD_AT, &i128::from(h));
                    }
                    first = h.saturating_sub(1)
                }
                None => {
                    if census {
                        crate::number::census::tally(if below_grain { CENSUS_REST_GRAIN } else { CENSUS_REST_HALVINGS }, 1);
                    }
                    break;
                }
            }
        }
        if crate::number::census::enabled() {
            crate::number::census::tally(CENSUS_RELAXED, 1);
            if read.halvings.len() == ticks && read.halvings.last().is_some_and(Option::is_some) {
                crate::number::census::tally(CENSUS_ALL_TICKS, 1);
            }
        }
        read.last = cell.phi;
        read.pairs = pairs;
        Ok(Relaxed { x, cell, held, paces, window, read, trail })
    }

    /// [definition; the unified-theory reading of November 7, 00:02] **The reverse through the ticks and the opening**: the
    /// letters' covectors of `G(e) = Φ(x^K(e); e)` beyond its partial derivative at the last state ([`LetterCovectors`]).
    /// From `λ^K = ∂Φ/∂x^K = −J F^K` back over each tick that stood, `x' = x + 2^(−h) s F` (`s` each lane's scale): with
    /// `w = s ⊙ λ'`, the tick's letters take `2^(−h) ⟨w, ∂F/∂e⟩` (`R w` on the own row, `w_(t+1)` on the before row, `w_(t−1)` on
    /// the after row, `Cᵀ w + δg_s(w)` on the moment), and `λ = λ' + 2^(−h) (r̂ ⟨λ', F⟩/W + J δF(w))`, `δF(w) = −Hess Φ · w`
    /// ([`Field::energy_tangent`], the Hessian symmetric, so the tangent is the adjoint); then the opening takes `λ⁰` on its
    /// rows and `Cᵀ λ⁰` on the moments. The classes, the supports and the halvings are held at the base.
    fn energy_reverse(&self, relaxed: &Relaxed) -> Result<LetterCovectors> {
        let d = &self.declaration;
        let (dw, m2, lanes) = (d.width, 2 * d.complex(), d.lanes);
        let w = dw / lanes;
        let l = &self.layout;
        let reaches = self.reaches();
        let Relaxed { cell, held, paces, trail, .. } = relaxed;
        let sites = held.definite.len();
        let mut out = LetterCovectors { own: vec![0i64; sites * dw], before: vec![0i64; sites * dw], after: vec![0i64; sites * dw], moment: vec![0i64; sites * m2] };
        let add = |slot: &mut i64, v: i128| -> Result<()> {
            *slot = fit64(*slot as i128 + v)?;
            Ok(())
        };
        // λ^K = −J F^K: the energy's covector on the last state.
        let (last_force, _) = self.energy_force(cell, held, paces, &reaches)?;
        let mut lambda = vec![0i64; sites * dw];
        for t in 0..sites {
            let back = lane_adjoint(&cell.read[t * dw..(t + 1) * dw], &cell.scale[t * lanes..(t + 1) * lanes], &last_force[t * dw..(t + 1) * dw])?;
            for i in 0..dw {
                lambda[t * dw + i] = -back[i];
            }
        }
        census_lambda(&lambda, &cell.scale, &last_force);
        let mut lift = vec![0i64; dw];
        let mut chart = vec![0i64; m2];
        for step in trail.iter().rev() {
            let (c, force, h) = (&step.cell, &step.force, step.halvings);
            // `w = s ⊙ λ'` on 2^(−24).
            let mut wv = vec![0i64; sites * dw];
            for (k, slot) in wv.iter_mut().enumerate() {
                let (t, i) = (k / dw, k % dw);
                *slot = fit64(release(c.scale[t * lanes + i / w] * lambda[k] as i128, FACE_BITS))?;
            }
            let (tangent, probe) = self.energy_tangent(c, held, paces, &reaches, &wv)?;
            for t in 0..sites {
                let wt = &wv[t * dw..(t + 1) * dw];
                affine(&self.theta[l.read..l.read + dw * dw], reaches.read, dw, wt, None, 0, MATERIAL_BITS, &mut lift)?;
                transposed(&self.theta[l.moment_face..l.moment_face + dw * m2], reaches.moment_face, m2, wt, MATERIAL_BITS, &mut chart)?;
                for i in 0..dw {
                    add(&mut out.own[t * dw + i], release(lift[i] as i128, h))?;
                    if t + 1 < sites {
                        add(&mut out.before[t * dw + i], release(wv[(t + 1) * dw + i] as i128, h))?;
                    }
                    if t > 0 {
                        add(&mut out.after[t * dw + i], release(wv[(t - 1) * dw + i] as i128, h))?;
                    }
                }
                for k in 0..m2 {
                    add(&mut out.moment[t * m2 + k], release(chart[k] as i128 + probe[t * m2 + k] as i128, h))?;
                }
            }
            // `λ = λ' + 2^(−h) (r̂ ⟨λ', F⟩/W + J δF)`, each lane's.
            let mut next = lambda.clone();
            for t in 0..sites {
                let jt = lane_adjoint(&c.read[t * dw..(t + 1) * dw], &c.scale[t * lanes..(t + 1) * lanes], &tangent[t * dw..(t + 1) * dw])?;
                for k_ in 0..lanes {
                    let at = t * dw + k_ * w;
                    let dot: i128 = (0..w).map(|i| lambda[at + i] as i128 * force[at + i] as i128).sum();
                    let mean = div_nearest(dot, w as i128);
                    for i in 0..w {
                        let radial = release(c.read[at + i] as i128 * mean, 2 * FACE_BITS + 8);
                        add(&mut next[at + i], release(radial + jt[k_ * w + i] as i128, h))?;
                    }
                }
            }
            lambda = next;
        }
        // The opening: `x⁰_t = E(u_t) + E₋(u_(t−1)) + E₊(u_(t+1)) + C s_t + b`.
        for t in 0..sites {
            transposed(&self.theta[l.moment_face..l.moment_face + dw * m2], reaches.moment_face, m2, &lambda[t * dw..(t + 1) * dw], MATERIAL_BITS, &mut chart)?;
            for i in 0..dw {
                add(&mut out.own[t * dw + i], lambda[t * dw + i] as i128)?;
                if t + 1 < sites {
                    add(&mut out.before[t * dw + i], lambda[(t + 1) * dw + i] as i128)?;
                }
                if t > 0 {
                    add(&mut out.after[t * dw + i], lambda[(t - 1) * dw + i] as i128)?;
                }
            }
            for k in 0..m2 {
                add(&mut out.moment[t * m2 + k], chart[k] as i128)?;
            }
        }
        Ok(out)
    }

    /// [definition; the unified-theory reading of November 6, 22:52] **A region's forward under one energy**
    /// ([`energy`](self)): the opening, `K` ticks of certified descent under the held supports, and each unresolved site's
    /// face as the energy's force on its letter. Returns the pass's faces and readings (no tick is held: the return is not
    /// built), and the energy at the opening and at the last tick with each tick's halvings (`None` where it rested).
    pub(super) fn energy_pass(&self, region: &Region) -> Result<(FieldPass, EnergyRead)> {
        self.energy_faces(region, None, None)
    }

    /// [`Field::energy_pass`], its descent replayed at given halvings under a base's supports where they are given.
    fn energy_faces(&self, region: &Region, replay: Option<&[Option<u32>]>, base: Option<&Held>) -> Result<(FieldPass, EnergyRead)> {
        let relaxed = self.energy_relax(region, replay.map_or(self.declaration.ticks, <[Option<u32>]>::len), replay, base)?;
        let total = self.energy_reverse(&relaxed)?;
        let Relaxed { cell, held, paces, read, .. } = relaxed;
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
                    dm[t * m2 + k] = fit64(back[k] as i128 + dp[t * m2 + k] as i128 - total.moment[t * m2 + k] as i128)?;
                }
            }
            self.moment_letters(&paces, sites, &dm)?
        } else {
            (Vec::new(), Vec::new())
        };
        let mut out = FieldPass { pairs, echo: vec![0; sites], read: vec![0i32; sites * dw], lift: vec![0i64; sites * dw], scale: vec![0i128; sites * d.lanes], faces: vec![None; sites], logits: vec![None; sites], ..Default::default() };
        let mut z = vec![0i64; d.alphabet];
        let inverse_temper = temperature_of(-self.theta[l.face_temper], &self.fine)?;
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
                // The opening's and the ticks' part of the total derivative: `−⟨rows(a), covectors⟩` on 2^(−40).
                let mut through = 0i128;
                for (base, cov) in [(l.enc, &total.own), (l.before, &total.before), (l.after, &total.after)] {
                    through += self.theta[base + a * dw..base + (a + 1) * dw].iter().zip(&cov[t * dw..(t + 1) * dw]).map(|(&e, &c)| e as i128 * c as i128).sum::<i128>();
                }
                let mut moment_part = 0i128;
                if tm > 0 {
                    for k in 0..2 * tm {
                        moment_part += self.theta[l.moment_before + a * 2 * tm + k] as i128 * fb[t][k] + self.theta[l.moment_after + a * 2 * tm + k] as i128 * fa[t][k];
                    }
                }
                *slot = fit64(*slot as i128 + release(strand, FACE_BITS) + release(moment_part - through, super::super::COVECTOR_BITS))?;
            }
            // The letters read the energy at the field's one temperature: `z = −(1/T) dG/de` (the unified-theory reading of
            // November 7, 01:37).
            for zc in z.iter_mut() {
                *zc = fit64(release(*zc as i128 * inverse_temper, MATERIAL_BITS))?;
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

    /// [measurement; the unified-theory readings of November 6, 22:52 and November 7, 04:04] **The fall along the force**: on
    /// the state after `ticks` ticks of descent, the step's first-order fall `2^(−h) Σ_t (|F_t|² − ⟨r̂_t, F_t⟩²/W)` (each
    /// lane's), the energy's fall `Φ(x) − Φ(x + 2^(−h) ‖x‖ F)` under it, and the central fall `Φ(x − 2^(−h) ‖x‖ F) − Φ(x +
    /// 2^(−h) ‖x‖ F)` against twice the first order, its curvature cancelled; all on `2^(−32)` bits. If `F` is the energy's
    /// gradient, the central fall's distance from twice the first order falls four times per halving of the step, until the
    /// state's grain.
    pub fn energy_fall(&self, region: &Region, ticks: usize, h: u32) -> Result<(i128, i128, i128)> {
        let d = &self.declaration;
        let Relaxed { x, cell, held, paces, window, .. } = self.energy_relax(region, ticks, None, None)?;
        let reaches = self.reaches();
        let (force, _) = self.energy_force(&cell, &held, &paces, &reaches)?;
        let next = self.energy_step(&x, &cell.scale, &force, h)?;
        let after = self.energy_cell(&next, &held, &paces, &reaches, window.as_deref())?;
        let back: Vec<i64> = force.iter().map(|&f| -f).collect();
        let behind = self.energy_cell(&self.energy_step(&x, &cell.scale, &back, h)?, &held, &paces, &reaches, window.as_deref())?;
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
        Ok((release(first, 16 + h), cell.phi - after.phi, behind.phi - after.phi))
    }

    /// [measurement; a test's reading] **The force's tangent against the force's difference**: at the opening, for a keyed
    /// direction `v` held in each lane's tangent (`v − r̂⟨r̂, v⟩/W`, on `2^(−24)`), the tangent `δF` beside `2^e (F(x + 2^(−e)
    /// ‖x‖ v) − F(x))`, and for a second keyed direction `u` the two pairings `⟨u, δF(v)⟩` and `⟨v, δF(u)⟩` (Hessian symmetry),
    /// each pairing on `2^(−48)`.
    #[cfg(test)]
    pub(super) fn energy_tangent_check(&self, region: &Region, e: u32, seed: u64) -> Result<(Vec<i64>, Vec<i64>, i128, i128)> {
        let read = self.energy_tangent_read(region, 0, e, seed)?;
        Ok((read.tangent, read.difference, read.uv, read.vu))
    }

    /// [measurement; the unified-theory reading of November 7, 03:05] **The force and its tangent on a state** after `ticks`
    /// ticks of descent: for keyed lane-tangent directions `u`, `v` (on `2^(−24)`), the tangent `δF(v)` beside the force's
    /// difference across a step of `2^(−e)` along `v`, the two pairings `⟨u, δF(v)⟩` and `⟨v, δF(u)⟩` (on `2^(−48)`), and the
    /// energy's fall along `v` beside its first order `2^(−e) ⟨F, v⟩` (both on `2^(−32)` bits; a non-gradient force passes
    /// along `F` itself but not along a random `v`).
    pub fn energy_tangent_read(&self, region: &Region, ticks: usize, e: u32, seed: u64) -> Result<EnergyTangentRead> {
        let d = &self.declaration;
        let (dw, lanes) = (d.width, d.lanes);
        let w = dw / lanes;
        let Relaxed { x, cell, held, paces, window, .. } = self.energy_relax(region, ticks, None, None)?;
        let reaches = self.reaches();
        let mix = |counter: u64| -> u64 {
            let mut z = seed.wrapping_add(counter.wrapping_mul(0x9E37_79B9_7F4A_7C15));
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
            z ^ (z >> 31)
        };
        let direction = |salt: u64| -> Vec<i64> {
            let mut v: Vec<i64> = (0..x.len()).map(|k| ((mix(((k as u64) << 8) ^ salt) >> 40) as i64) - (1 << 23)).collect();
            for t in 0..x.len() / dw {
                for l_ in 0..lanes {
                    let at = t * dw + l_ * w;
                    let rv: i128 = (0..w).map(|i| cell.read[at + i] as i128 * v[at + i] as i128).sum();
                    let mean = div_nearest(rv, w as i128);
                    for i in 0..w {
                        v[at + i] -= release(mean * cell.read[at + i] as i128, 2 * FACE_BITS) as i64;
                    }
                }
            }
            v
        };
        let (v, u) = (direction(1), direction(2));
        let (tv, _) = self.energy_tangent(&cell, &held, &paces, &reaches, &v)?;
        let (tu, _) = self.energy_tangent(&cell, &held, &paces, &reaches, &u)?;
        let (f0, _) = self.energy_force(&cell, &held, &paces, &reaches)?;
        let next = self.energy_step(&x, &cell.scale, &v, e)?;
        let moved = self.energy_cell(&next, &held, &paces, &reaches, window.as_deref())?;
        let (f1, _) = self.energy_force(&moved, &held, &paces, &reaches)?;
        let difference: Vec<i64> = f1.iter().zip(&f0).map(|(&a, &b)| (a - b) << e).collect();
        let pair = |a: &[i64], b: &[i64]| -> i128 { a.iter().zip(b).map(|(&x, &y)| x as i128 * y as i128).sum() };
        let (uv, vu) = (pair(&u, &tv), pair(&v, &tu));
        // The energy's fall along `v` against its first order: `Δr̂ = 2^(−e) v` for a lane-tangent `v`, so `ΔΦ ≈ −2^(−e) ⟨F, v⟩`
        // with `F` on 2^(−24) and `v` on 2^(−24) (2^(−48)), carried to 2^(−32).
        let first = release(pair(&f0, &v), 16 + e);
        // The central fall: `Φ(x − δv) − Φ(x + δv)` against `2 δ ⟨F, v⟩`, its curvature cancelled.
        let minus: Vec<i64> = v.iter().map(|&x| -x).collect();
        let behind = self.energy_cell(&self.energy_step(&x, &cell.scale, &minus, e)?, &held, &paces, &reaches, window.as_deref())?;
        Ok(EnergyTangentRead { tangent: tv, difference, uv, vu, fall: cell.phi - moved.phi, first, central: behind.phi - moved.phi })
    }

    /// [measurement; a test's reading] **`G` at other letters**: `G(e) = Φ(x^K(e); e)` with site `t` carrying `shares`
    /// (locked), the opening and the ticks read again from it at the base's halvings, under the base's classes and supports
    /// (the derivative's one scalar), on `2^(−32)` bits.
    #[cfg(test)]
    pub(super) fn energy_g_at(&self, region: &Region, t: usize, shares: &Shares) -> Result<i128> {
        let base = self.energy_relax(region, self.declaration.ticks, None, None)?;
        let (mut faces, mut locked) = self.energy_sites(region);
        (faces[t], locked[t]) = (Some(shares.clone()), true);
        let set = Region { faces: &faces, locked: &locked, ..*region };
        let replayed = self.energy_relax(&set, base.read.halvings.len(), Some(&base.read.halvings), Some(&base.held))?;
        Ok(replayed.cell.phi)
    }

    /// [measurement; a test's reading] **A square read at one base** (the unified-theory reading of November 7, 00:02): with
    /// sites `i` and `j` both carrying the uniform mixture (locked), the face's change `z_i(a′) − z_i(a)` as `j`'s mixture
    /// moves by `ε(b′ − b)`, and `z_j(b′) − z_j(b)` as `i`'s moves by `ε(a′ − a)`, every read replayed at the base's halvings
    /// under its supports; `ε` on `2^(−16)` of a mixture's weight, the two readings on `2^(−16)` bits.
    #[cfg(test)]
    pub(super) fn energy_square(&self, region: &Region, (i, a, a2): (usize, usize, usize), (j, b, b2): (usize, usize, usize), eps: u32) -> Result<(i128, i128)> {
        let alphabet = self.declaration.alphabet as u32;
        let base_w = (1u32 << STATE_BITS) / alphabet;
        let mixture = |shift: Option<(usize, usize)>| -> Shares { (0..alphabet).map(|c| (c, match shift { Some((up, _)) if c as usize == up => base_w + eps, Some((_, down)) if c as usize == down => base_w - eps, _ => base_w })).collect() };
        let sites = region.classes.len();
        let mut unresolved = region.unresolved.to_vec();
        (unresolved[i], unresolved[j]) = (true, true);
        let read = |si: Option<(usize, usize)>, sj: Option<(usize, usize)>, replay: Option<&[Option<u32>]>, base: Option<&Held>| -> Result<(Vec<Option<Vec<i64>>>, Relaxed)> {
            let mut faces: Vec<Option<Shares>> = (0..sites).map(|t| region.faces.get(t).cloned().flatten()).collect();
            let mut locked: Vec<bool> = (0..sites).map(|t| region.locked.get(t).copied().unwrap_or(false)).collect();
            (faces[i], faces[j], locked[i], locked[j]) = (Some(mixture(si)), Some(mixture(sj)), true, true);
            let r = Region { unresolved: &unresolved, faces: &faces, locked: &locked, ..*region };
            let relaxed = self.energy_relax(&r, replay.map_or(self.declaration.ticks, <[Option<u32>]>::len), replay, base)?;
            Ok((self.energy_faces(&r, replay, base)?.0.logits, relaxed))
        };
        let (base_logits, base) = read(None, None, None, None)?;
        let halvings = base.read.halvings.clone();
        let gap = |z: &[Option<Vec<i64>>], t: usize, hi: usize, lo: usize| -> i128 { let z = z[t].as_ref().expect("an open site's face"); (z[hi] - z[lo]) as i128 };
        let (moved_j, _) = read(None, Some((b2, b)), Some(&halvings), Some(&base.held))?;
        let (moved_i, _) = read(Some((a2, a)), None, Some(&halvings), Some(&base.held))?;
        Ok((gap(&moved_j, i, a2, a) - gap(&base_logits, i, a2, a), gap(&moved_i, j, b2, b) - gap(&base_logits, j, b2, b)))
    }

    /// [definition; the unified-theory reading of November 7, 01:37] **The founding's temperature**: over the regions' open
    /// sites, the root mean square of each face's spread across the letters at `T = 1`, so that at `T₀` a face opens at one
    /// bit of spread (near flat, nothing on the face's floor). Returns `log₂ T₀` on the material's grain and the spread on
    /// `2^(−16)` bits.
    pub fn energy_temperature(&self, regions: &[Region]) -> Result<(i32, i128)> {
        if !self.declaration.energy {
            return refuse("a temperature of the letters for a field whose faces are not one energy's forces");
        }
        let mut flat = self.clone();
        flat.theta[self.layout.face_temper] = 0;
        let reads = regions.par_iter().map(|r| flat.energy_pass(r).map(|(p, _)| p.logits)).collect::<Result<Vec<_>>>()?;
        let a = self.declaration.alphabet as i128;
        let (mut second, mut sites) = (0i128, 0i128);
        for z in reads.iter().flatten().flatten() {
            let mean = div_nearest(z.iter().map(|&v| v as i128).sum(), a);
            second += div_nearest(z.iter().map(|&v| (v as i128 - mean) * (v as i128 - mean)).sum(), a);
            sites += 1;
        }
        if sites == 0 {
            return refuse("a temperature read over no open site");
        }
        let spread = (div_nearest(second, sites) as u128).isqrt() as i128;
        let ell = super::super::log2_reading_at(spread.max(1) as u128, MATERIAL_BITS) - ((FACE_BITS as i128) << MATERIAL_BITS);
        Ok((fit32(ell, "a temperature past its carrier")?, spread))
    }

    /// [measurement; the unified-theory reading of November 7, 01:37] **A square's four corners at one base**: on a state of
    /// the truth, the base reads `i` and `j` both open (each carrying the locked mixture); every corner is read again at the
    /// base's halvings under its classes and supports, so the square is one scalar's: `i`'s face with `j` at its letter and
    /// at its runner-up `b′`, and `j`'s with `i` at its letter and at its runner-up `a′` (each runner-up read beside the
    /// other's letter). Returns `λ_i = c_i(a′|b) + c_i(a|b′) − c_i(a|b) − c_i(a′|b′)` and `λ_j` alike on the faces' letters
    /// (the void off), on `2^(−20)` bits, and beside them the attribution read at `ε` of a mixture's weight (`2^(−16)`
    /// units): the change of `z_i(a′) − z_i(a)` as `j`'s mixture moves by `ε(b′ − b)`, and of `z_j(b′) − z_j(b)` as `i`'s moves
    /// by `ε(a′ − a)`, on `2^(−16)` bits. `None` where a face has no runner-up.
    pub fn energy_square_corners(&self, truth: &[usize], (i, j): (usize, usize), void: usize, eps: u32) -> Result<Option<EnergySquare>> {
        let sites = truth.len();
        let base_w = (1u32 << STATE_BITS) / self.declaration.alphabet as u32;
        if 4 * eps > base_w {
            return refuse("a square's step past a letter's weight in the uniform mixture (its wide read leaves the mixtures)");
        }
        let mut open = vec![false; sites];
        (open[i], open[j]) = (true, true);
        let base_region = Region { classes: truth, unresolved: &open, faces: &[], locked: &[], echo: &[], domain: None, port: None };
        let base = self.energy_relax(&base_region, self.declaration.ticks, None, None)?;
        let halvings = base.read.halvings.clone();
        // A corner: `at` read open, the other site `(t, letter)` set to a letter, or carrying a moved mixture.
        let corner = |at: usize, other: usize, letter: Option<usize>, mixture: Option<Shares>| -> Result<Vec<i64>> {
            let mut classes = truth.to_vec();
            let mut unresolved = vec![false; sites];
            let mut faces: Vec<Option<Shares>> = vec![None; sites];
            let mut locked = vec![false; sites];
            unresolved[at] = true;
            match letter {
                Some(c) => classes[other] = c,
                None => {
                    unresolved[other] = true;
                    (faces[other], locked[other]) = (mixture, true);
                }
            }
            let r = Region { classes: &classes, unresolved: &unresolved, faces: &faces, locked: &locked, echo: &[], domain: None, port: None };
            let (pass, _) = self.energy_faces(&r, Some(&halvings), Some(&base.held))?;
            pass.logits[at].clone().ok_or(TowerError::Refused("a square's open place with no face"))
        };
        let (a, b) = (truth[i], truth[j]);
        let zi_b = corner(i, j, Some(b), None)?;
        let zj_a = corner(j, i, Some(a), None)?;
        let Some((a2, b2)) = self.energy_square_runners(&zi_b, &zj_a, (a, b), void) else { return Ok(None) };
        let zi_b2 = corner(i, j, Some(b2), None)?;
        let zj_a2 = corner(j, i, Some(a2), None)?;
        // The energy's own square: `G` at the four corners with both letters set, read again at the base.
        let energy_at = |ai: usize, bj: usize| -> Result<i128> {
            let mut classes = truth.to_vec();
            (classes[i], classes[j]) = (ai, bj);
            let r = Region { classes: &classes, unresolved: &vec![false; sites], faces: &[], locked: &[], echo: &[], domain: None, port: None };
            Ok(self.energy_relax(&r, halvings.len(), Some(&halvings), Some(&base.held))?.cell.phi)
        };
        let g = [energy_at(a2, b)?, energy_at(a, b2)?, energy_at(a, b)?, energy_at(a2, b2)?];
        // The attribution read at one base: the base's own faces, and each site's with the other's mixture moved.
        let (pass, _) = self.energy_faces(&base_region, Some(&halvings), Some(&base.held))?;
        let (zi, zj) = (pass.logits[i].clone().ok_or(TowerError::Refused("a square's open place with no face"))?, pass.logits[j].clone().ok_or(TowerError::Refused("a square's open place with no face"))?);
        let zi_moved = corner(i, j, None, Some(self.energy_square_mixture(Some((b2, b)), eps)))?;
        let zj_moved = corner(j, i, None, Some(self.energy_square_mixture(Some((a2, a)), eps)))?;
        // And at four times the step.
        let zi_wide = corner(i, j, None, Some(self.energy_square_mixture(Some((b2, b)), 4 * eps)))?;
        let zj_wide = corner(j, i, None, Some(self.energy_square_mixture(Some((a2, a)), 4 * eps)))?;
        let corners = SquareCorners { zi_b: &zi_b, zj_a: &zj_a, zi_b2: &zi_b2, zj_a2: &zj_a2, zi: &zi, zj: &zj, zi_moved: &zi_moved, zj_moved: &zj_moved, zi_wide: &zi_wide, zj_wide: &zj_wide, g };
        self.energy_square_reading((a, b), (a2, b2), &corners, void).map(Some)
    }

    /// [measurement; the unified-theory reading of November 7, 03:22] **A square's central readings at one base**: at each step
    /// `ε` of `steps` (`2^(−16)` of a mixture's weight), `i`'s reading `(z_i(a′) − z_i(a))` with `j`'s mixture moved by `+ε(b′ − b)`
    /// less the same with it moved by `−ε(b′ − b)`, and `j`'s alike, every read at the base's halvings under its supports, so the
    /// curvature cancels to third order. Each reading is twice the central difference, on `2^(−16)` bits; `None` where a face
    /// has no runner-up.
    pub fn energy_central_square(&self, truth: &[usize], (i, j): (usize, usize), void: usize, steps: &[u32]) -> Result<Option<Vec<(i128, i128)>>> {
        let sites = truth.len();
        let base_w = (1u32 << STATE_BITS) / self.declaration.alphabet as u32;
        if steps.iter().any(|&e| e > base_w) {
            return refuse("a square's step past a letter's weight in the uniform mixture");
        }
        let mut open = vec![false; sites];
        (open[i], open[j]) = (true, true);
        let base_region = Region { classes: truth, unresolved: &open, faces: &[], locked: &[], echo: &[], domain: None, port: None };
        let base = self.energy_relax(&base_region, self.declaration.ticks, None, None)?;
        let halvings = base.read.halvings.clone();
        let corner = |at: usize, other: usize, letter: Option<usize>, mixture: Option<Shares>| -> Result<Vec<i64>> {
            let mut classes = truth.to_vec();
            let mut unresolved = vec![false; sites];
            let mut faces: Vec<Option<Shares>> = vec![None; sites];
            let mut locked = vec![false; sites];
            unresolved[at] = true;
            match letter {
                Some(c) => classes[other] = c,
                None => {
                    unresolved[other] = true;
                    (faces[other], locked[other]) = (mixture, true);
                }
            }
            let r = Region { classes: &classes, unresolved: &unresolved, faces: &faces, locked: &locked, echo: &[], domain: None, port: None };
            let (pass, _) = self.energy_faces(&r, Some(&halvings), Some(&base.held))?;
            pass.logits[at].clone().ok_or(TowerError::Refused("a square's open place with no face"))
        };
        let (a, b) = (truth[i], truth[j]);
        let zi_b = corner(i, j, Some(b), None)?;
        let zj_a = corner(j, i, Some(a), None)?;
        let Some((a2, b2)) = self.energy_square_runners(&zi_b, &zj_a, (a, b), void) else { return Ok(None) };
        let gap = |z: &[i64], hi: usize, lo: usize| (z[hi] - z[lo]) as i128;
        let mut out = Vec::with_capacity(steps.len());
        for &eps in steps {
            let ri = gap(&corner(i, j, None, Some(self.energy_square_mixture(Some((b2, b)), eps)))?, a2, a) - gap(&corner(i, j, None, Some(self.energy_square_mixture(Some((b, b2)), eps)))?, a2, a);
            let rj = gap(&corner(j, i, None, Some(self.energy_square_mixture(Some((a2, a)), eps)))?, b2, b) - gap(&corner(j, i, None, Some(self.energy_square_mixture(Some((a, a2)), eps)))?, b2, b);
            out.push((ri, rj));
        }
        Ok(Some(out))
    }

    /// [definition; the unified-theory reading of November 7, 01:37] A square's moved mixture ([`Field::energy_square_corners`]):
    /// the uniform mixture over the alphabet (`2^16/A` a letter), `ε` moved from the letter `down` to `up` where `shift` is
    /// given. Public: a realization reads a square's corners on the same mixtures.
    pub fn energy_square_mixture(&self, shift: Option<(usize, usize)>, eps: u32) -> Shares {
        let alphabet = self.declaration.alphabet as u32;
        let base_w = (1u32 << STATE_BITS) / alphabet;
        (0..alphabet).map(|c| (c, match shift { Some((up, _)) if c as usize == up => base_w + eps, Some((_, down)) if c as usize == down => base_w - eps, _ => base_w })).collect()
    }

    /// [definition; the unified-theory reading of November 7, 01:37] **A square's runner-ups** (the void off): `i`'s next letter
    /// beside `a` on its face with `j` at `b`, and `j`'s beside `b` with `i` at `a` (the most mass, the least letter on a tie);
    /// `None` where a face has no runner-up. Public: a realization's corners read the same.
    pub fn energy_square_runners(&self, zi_b: &[i64], zj_a: &[i64], (a, b): (usize, usize), void: usize) -> Option<(usize, usize)> {
        let runner = |z: &[i64], standing: usize| -> Option<usize> {
            let face = letters_face(&self.tempered(z, 1), void)?;
            (0..face.masses.len()).filter(|&c| c != standing && face.masses[c] > 0).max_by_key(|&c| (face.masses[c], std::cmp::Reverse(c)))
        };
        Some((runner(zi_b, a)?, runner(zj_a, b)?))
    }

    /// [measurement; the unified-theory reading of November 7, 01:37] **A square read from its corners** ([`EnergySquare`]):
    /// the readings over whole letters, on the faces' logits and on the floor, the energy's own square over `T`, and the
    /// attribution read at `ε`, from the corners' logits and the four energies ([`SquareCorners`]). Public: a realization's
    /// corners are read into the same square.
    pub fn energy_square_reading(&self, (a, b): (usize, usize), (a2, b2): (usize, usize), c: &SquareCorners, void: usize) -> Result<EnergySquare> {
        let (zi_b, zj_a, zi_b2, zj_a2) = (c.zi_b, c.zj_a, c.zi_b2, c.zj_a2);
        let code = |z: &[i64], a: usize| -> i64 {
            let face = letters_face(&self.tempered(z, 1), void).expect("a face with a letter");
            face.code(a)
        };
        let lambda_i = code(zi_b, a2) + code(zi_b2, a) - code(zi_b, a) - code(zi_b2, a2);
        let lambda_j = code(zj_a, b2) + code(zj_a2, b) - code(zj_a, b) - code(zj_a2, b2);
        // The readings on the faces' logits (`c(a′) − c(a) = −(z(a′) − z(a))` where neither letter is on the floor), on
        // 2^(−20) bits, and how many of the eight codes stand on the face's floor (2^(−62)).
        let z = |zs: &[i64], a: usize| zs[a] as i64;
        let zlambda_i = (z(zi_b, a) + z(zi_b2, a2) - z(zi_b, a2) - z(zi_b2, a)) << 4;
        let zlambda_j = (z(zj_a, b) + z(zj_a2, b2) - z(zj_a, b2) - z(zj_a2, b)) << 4;
        let floor = (62i64 << 20) - (1 << 20);
        let floors = [code(zi_b, a2), code(zi_b2, a), code(zi_b, a), code(zi_b2, a2), code(zj_a, b2), code(zj_a2, b), code(zj_a, b), code(zj_a2, b2)].iter().filter(|&&c| c >= floor).count() as u32;
        // The energy's own square over `T`: the joint `2^(−G/T)`'s conditionals read `λ = (G(a′,b) + G(a,b′) − G(a,b) −
        // G(a′,b′))/T` from both ends.
        let g_square = c.g[0] + c.g[1] - c.g[2] - c.g[3];
        let inverse = temperature_of(-self.theta[self.layout.face_temper], &self.fine)?;
        let glambda = fit64(release(g_square * inverse, MATERIAL_BITS + ENERGY_BITS - 20))?;
        let gap = |z: &[i64], hi: usize, lo: usize| (z[hi] - z[lo]) as i128;
        let small_i = gap(c.zi_moved, a2, a) - gap(c.zi, a2, a);
        let small_j = gap(c.zj_moved, b2, b) - gap(c.zj, b2, b);
        // And at four times the step, so the readings' growth and the curl's are read beside each other.
        let wide_i = gap(c.zi_wide, a2, a) - gap(c.zi, a2, a);
        let wide_j = gap(c.zj_wide, b2, b) - gap(c.zj, b2, b);
        Ok(EnergySquare { runners: (a2, b2), lambda_i, lambda_j, small_i, small_j, wide_i, wide_j, zlambda_i, zlambda_j, glambda, floors })
    }

    /// [definition; agent-inferred, November 7] **The energy's material covector**: `∂G/∂θ` for `G(θ) = Φ(x^K(θ); θ)` at the
    /// base's halvings and supports, every family's covector per real unit of its entries on `2^(−40)` (the moment encodings'
    /// through the moments' return), beside `G` on `2^(−32)` bits. Three parts: the energy's explicit `∂Φ/∂θ` at the last
    /// state (each chart's word force against its read, the pair's drives and contraction, the letters' rows against the reads
    /// and lifts they meet, the moments' covector); each stood tick's `2^(−h) ⟨w, ∂F/∂θ⟩` with `w = s ⊙ λ'`, which is
    /// `−D_w(∂Φ/∂θ)`: the word forces' tangents against the reads and the word forces against `w` (the tick's adjoint `λ` as
    /// in [`Field::energy_reverse`]); and the opening's `(∂x⁰/∂θ)ᵀ λ⁰`. The locks' temperatures are held (theory: lap 4 keeps
    /// the line's lock gain), and the letters' temperature does not enter `G`.
    pub fn energy_material(&self, region: &Region) -> Result<(Vec<i128>, i128)> {
        let (faces, locked) = self.energy_sites(region);
        let region = &Region { faces: &faces, locked: &locked, ..*region };
        let relaxed = self.energy_relax(region, self.declaration.ticks, None, None)?;
        let d = &self.declaration;
        let (dw, m2, f, lanes, alphabet) = (d.width, 2 * d.complex(), d.contacts, d.lanes, d.alphabet);
        let w_ = dw / lanes;
        let half = f / 2;
        let l = &self.layout;
        let reaches = self.reaches();
        let Relaxed { cell, held, paces, trail, .. } = &relaxed;
        let sites = held.definite.len();
        let mut g = vec![0i128; self.theta.len()];
        let mut dm = vec![0i128; sites * m2];
        // Each site's letter: its rows and their weights on 2^(−16) (a class's whole weight, or a carried mixture's shares).
        let weights: Vec<Vec<(usize, i128)>> = (0..sites)
            .map(|t| match Self::carried(region, t) {
                Some(face) => face.iter().map(|&(c, w)| (c as usize, w as i128)).collect(),
                None if region.unresolved[t] => vec![(alphabet, 1i128 << STATE_BITS)],
                None => vec![(region.classes[t], 1i128 << STATE_BITS)],
            })
            .collect();
        let moment = &held.moment;
        // `y_t ⊗ x_t` into a chart's material of `rows` by `cols`, released by `shift` (2^(−40) at the caller's grains).
        let outer = |g: &mut [i128], base: usize, rows: usize, cols: usize, y: &[i64], x: &[i128], shift: i32| {
            for o in 0..rows {
                if y[o] == 0 {
                    continue;
                }
                for i in 0..cols {
                    let v = y[o] as i128 * x[i];
                    g[base + o * cols + i] += if shift >= 0 { v << shift } else { release(v, (-shift) as u32) };
                }
            }
        };
        let reads = |c: &EnergyCell, t: usize| -> Vec<i128> { c.read[t * dw..(t + 1) * dw].iter().map(|&v| v as i128).collect() };
        // 1. The explicit `∂Φ/∂θ` at the last state: every term is minus the force's.
        let last = self.energy_force_parts(cell, held, paces, &reaches)?;
        for t in 0..sites {
            let r = reads(cell, t);
            let neg = |v: &[i64]| -> Vec<i64> { v.iter().map(|&x| -x).collect() };
            for (w, bias, cov, rows) in [(l.q, l.q_bias, &last.keys, m2), (l.probe, l.probe_bias, &last.probes, m2)] {
                let c_ = neg(&cov[t * rows..(t + 1) * rows]);
                outer(&mut g, w, rows, dw, &c_, &r, 0);
                for o in 0..rows {
                    g[bias + o] += (c_[o] as i128) << FACE_BITS;
                }
            }
            for (w, bias, cov) in [(l.a, l.a_bias, &last.a), (l.b, l.b_bias, &last.b)] {
                let c_ = neg(&cov[t * f..(t + 1) * f]);
                outer(&mut g, w, f, dw, &c_, &r, 0);
                for o in 0..f {
                    g[bias + o] += (c_[o] as i128) << FACE_BITS;
                }
            }
            // The pair's contraction: `∂Φ/∂c = −Σ_t a_t · b_(s(t))`.
            for e in 0..half {
                let Some(s) = strand_mate(t, e, sites) else { continue };
                let (ar, ai) = (cell.a[t * f + e] as i128, cell.a[t * f + half + e] as i128);
                let (br, bi) = (cell.b[s * f + e] as i128, cell.b[s * f + half + e] as i128);
                g[l.pair_c + e] -= release(ar * br - ai * bi, FACE_BITS) << MATERIAL_BITS;
                g[l.pair_c + half + e] -= release(ar * bi + ai * br, FACE_BITS) << MATERIAL_BITS;
            }
            // The letters: `−⟨E(u_t), R r̂_t + b_R⟩ − c_(u_t) − ⟨E₋(u_t), r̂_(t+1)⟩ − ⟨E₊(u_t), r̂_(t−1)⟩ − ⟨C s_t + b, r̂_t⟩`.
            let own = &held.letters.own[t];
            outer(&mut g, l.read, dw, dw, &neg(own), &r, 8);
            for o in 0..dw {
                g[l.lift_bias + o] -= (own[o] as i128) << (MATERIAL_BITS);
            }
            let lift = &cell.lift[t * dw..(t + 1) * dw];
            for &(row, wt) in &weights[t] {
                for o in 0..dw {
                    g[l.enc + row * dw + o] -= (wt * lift[o] as i128) << 8;
                    if t + 1 < sites {
                        g[l.before + row * dw + o] -= (wt * cell.read[(t + 1) * dw + o] as i128) << 8;
                    }
                    if t > 0 {
                        g[l.after + row * dw + o] -= (wt * cell.read[(t - 1) * dw + o] as i128) << 8;
                    }
                }
                if row < alphabet {
                    g[l.read_bias + row] -= wt << MATERIAL_BITS;
                }
            }
            let s_t: Vec<i128> = moment[t * m2..(t + 1) * m2].iter().map(|&v| v as i128).collect();
            outer(&mut g, l.moment_face, dw, m2, &neg(&cell.read[t * dw..(t + 1) * dw].iter().map(|&v| v as i64).collect::<Vec<_>>()), &s_t, 8);
            for o in 0..dw {
                g[l.moment_face_bias + o] -= (cell.read[t * dw + o] as i128) << MATERIAL_BITS;
            }
            // The moment's covector of `G`: `∂Φ/∂s_t = −(Cᵀ r̂_t + the probe's force)`, on 2^(−24).
            let mut chart = vec![0i64; m2];
            transposed(&self.theta[l.moment_face..l.moment_face + dw * m2], reaches.moment_face, m2, &cell.read[t * dw..(t + 1) * dw].iter().map(|&v| v as i64).collect::<Vec<_>>(), FACE_BITS, &mut chart)?;
            for k in 0..m2 {
                dm[t * m2 + k] -= chart[k] as i128 + last.probes[t * m2 + k] as i128;
            }
        }
        // 2. The ticks, back from `λ^K = −J F^K`.
        let mut lambda = vec![0i64; sites * dw];
        for t in 0..sites {
            let back = lane_adjoint(&cell.read[t * dw..(t + 1) * dw], &cell.scale[t * lanes..(t + 1) * lanes], &last.force[t * dw..(t + 1) * dw])?;
            for i in 0..dw {
                lambda[t * dw + i] = -back[i];
            }
        }
        census_lambda(&lambda, &cell.scale, &last.force);
        let mut lift = vec![0i64; dw];
        let mut chart = vec![0i64; m2];
        let (mut ta, mut tb) = (vec![0i64; f], vec![0i64; f]);
        for step in trail.iter().rev() {
            let (c, force, h) = (&step.cell, &step.force, step.halvings);
            let mut wv = vec![0i64; sites * dw];
            for (k, slot) in wv.iter_mut().enumerate() {
                let (t, i) = (k / dw, k % dw);
                *slot = fit64(release(c.scale[t * lanes + i / w_] * lambda[k] as i128, FACE_BITS))?;
            }
            let fp = self.energy_force_parts(c, held, paces, &reaches)?;
            let tp = self.energy_tangent_parts(c, held, paces, &reaches, &wv)?;
            // The tick's material, `2^(−h) Σ (δF ⊗ r̂ + F ⊗ w)` for each chart and drive, gathered on 2^(−40) and released by `h`.
            let mut tick = vec![0i128; self.theta.len()];
            for t in 0..sites {
                let r = reads(c, t);
                let wt: Vec<i128> = wv[t * dw..(t + 1) * dw].iter().map(|&v| v as i128).collect();
                for (w, bias, fw, tw, rows) in [(l.q, l.q_bias, &fp.keys, &tp.keys, m2), (l.probe, l.probe_bias, &fp.probes, &tp.probes, m2), (l.a, l.a_bias, &fp.a, &tp.a, f), (l.b, l.b_bias, &fp.b, &tp.b, f)] {
                    outer(&mut tick, w, rows, dw, &tw[t * rows..(t + 1) * rows], &r, 0);
                    outer(&mut tick, w, rows, dw, &fw[t * rows..(t + 1) * rows], &wt, -8);
                    for o in 0..rows {
                        tick[bias + o] += (tw[t * rows + o] as i128) << FACE_BITS;
                    }
                }
                // The contraction: `Σ δ(a_t · b_s)` with `δa = W_a w_t`, `δb_s = W_b w_s`.
                affine(&self.theta[l.a..l.a + f * dw], reaches.a, dw, &wv[t * dw..(t + 1) * dw], None, 0, MATERIAL_BITS, &mut ta)?;
                for e in 0..half {
                    let Some(s) = strand_mate(t, e, sites) else { continue };
                    affine(&self.theta[l.b..l.b + f * dw], reaches.b, dw, &wv[s * dw..(s + 1) * dw], None, 0, MATERIAL_BITS, &mut tb)?;
                    let (ar, ai) = (c.a[t * f + e] as i128, c.a[t * f + half + e] as i128);
                    let (br, bi) = (c.b[s * f + e] as i128, c.b[s * f + half + e] as i128);
                    let (dar, dai, dbr, dbi) = (ta[e] as i128, ta[half + e] as i128, tb[e] as i128, tb[half + e] as i128);
                    tick[l.pair_c + e] += dar * br - dai * bi + ar * dbr - ai * dbi;
                    tick[l.pair_c + half + e] += dar * bi + dai * br + ar * dbi + ai * dbr;
                }
                // The letters: `⟨w, ∂F/∂θ⟩` on their rows.
                let own = &held.letters.own[t];
                outer(&mut tick, l.read, dw, dw, own, &wt, 0);
                affine(&self.theta[l.read..l.read + dw * dw], reaches.read, dw, &wv[t * dw..(t + 1) * dw], None, 0, MATERIAL_BITS, &mut lift)?;
                for &(row, wgt) in &weights[t] {
                    for o in 0..dw {
                        tick[l.enc + row * dw + o] += wgt * lift[o] as i128;
                        if t + 1 < sites {
                            tick[l.before + row * dw + o] += wgt * wv[(t + 1) * dw + o] as i128;
                        }
                        if t > 0 {
                            tick[l.after + row * dw + o] += wgt * wv[(t - 1) * dw + o] as i128;
                        }
                    }
                }
                let s_t: Vec<i128> = moment[t * m2..(t + 1) * m2].iter().map(|&v| v as i128).collect();
                outer(&mut tick, l.moment_face, dw, m2, &wv[t * dw..(t + 1) * dw], &s_t, 0);
                for o in 0..dw {
                    tick[l.moment_face_bias + o] += (wv[t * dw + o] as i128) << FACE_BITS;
                }
                transposed(&self.theta[l.moment_face..l.moment_face + dw * m2], reaches.moment_face, m2, &wv[t * dw..(t + 1) * dw], MATERIAL_BITS, &mut chart)?;
                for k in 0..m2 {
                    dm[t * m2 + k] += release(chart[k] as i128 + tp.probes[t * m2 + k] as i128, h);
                }
            }
            for (slot, v) in g.iter_mut().zip(tick) {
                *slot += release(v, h);
            }
            // `λ = λ' + 2^(−h) (r̂ ⟨λ', F⟩/W + J δF)`.
            let mut next = lambda.clone();
            for t in 0..sites {
                let jt = lane_adjoint(&c.read[t * dw..(t + 1) * dw], &c.scale[t * lanes..(t + 1) * lanes], &tp.force[t * dw..(t + 1) * dw])?;
                for k_ in 0..lanes {
                    let at = t * dw + k_ * w_;
                    let dot: i128 = (0..w_).map(|i| lambda[at + i] as i128 * force[at + i] as i128).sum();
                    let mean = div_nearest(dot, w_ as i128);
                    for i in 0..w_ {
                        let radial = release(c.read[at + i] as i128 * mean, 2 * FACE_BITS + 8);
                        next[at + i] = fit64(next[at + i] as i128 + release(radial + jt[k_ * w_ + i] as i128, h))?;
                    }
                }
            }
            lambda = next;
        }
        // 3. The opening: `x⁰_t = E(u_t) + E₋(u_(t−1)) + E₊(u_(t+1)) + C s_t + b`.
        for t in 0..sites {
            let lt: Vec<i128> = lambda[t * dw..(t + 1) * dw].iter().map(|&v| v as i128).collect();
            for &(row, wgt) in &weights[t] {
                for o in 0..dw {
                    g[l.enc + row * dw + o] += wgt * lt[o];
                    if t + 1 < sites {
                        g[l.before + row * dw + o] += wgt * lambda[(t + 1) * dw + o] as i128;
                    }
                    if t > 0 {
                        g[l.after + row * dw + o] += wgt * lambda[(t - 1) * dw + o] as i128;
                    }
                }
            }
            let s_t: Vec<i128> = moment[t * m2..(t + 1) * m2].iter().map(|&v| v as i128).collect();
            outer(&mut g, l.moment_face, dw, m2, &lambda[t * dw..(t + 1) * dw], &s_t, 0);
            for o in 0..dw {
                g[l.moment_face_bias + o] += lt[o] << FACE_BITS;
            }
            transposed(&self.theta[l.moment_face..l.moment_face + dw * m2], reaches.moment_face, m2, &lambda[t * dw..(t + 1) * dw], MATERIAL_BITS, &mut chart)?;
            for k in 0..m2 {
                dm[t * m2 + k] += chart[k] as i128;
            }
        }
        // The moments' covector back to the strands' moment encodings (the training return's own law), on 2^(−40).
        let paced = paces.kappa.len();
        let (mut gtau, mut gsig) = (vec![vec![0i128; sites]; paced], vec![vec![0i128; sites]; paced]);
        let mut gm = vec![0i128; self.theta.len()];
        self.moments_return(region, paces, &dm, &mut gm, &mut gtau, &mut gsig)?;
        for (slot, v) in g.iter_mut().zip(gm) {
            *slot += v << FACE_BITS;
        }
        Ok((g, cell.phi))
    }

    /// [measurement; a test's reading] `G` at the base's halvings and supports for a field whose material differs from the
    /// base's (the material covector's difference read), on `2^(−32)` bits.
    #[cfg(test)]
    pub(super) fn energy_g_replayed(&self, base_field: &Field, region: &Region) -> Result<i128> {
        let base = base_field.energy_relax(region, base_field.declaration.ticks, None, None)?;
        Ok(self.energy_relax(region, base.read.halvings.len(), Some(&base.read.halvings), Some(&base.held))?.cell.phi)
    }

    /// [definition; agent-inferred, November 7, Brandon's lens of 04:42] **An energy field releases jointly**: the open places
    /// of each answer (its given length; the question and the near tail resolved) carry letter mixtures `q_t`, every one moved
    /// at once each read toward its face, `q ← q + 2^(−s)(p(q) − q)`, with `p_t = 2^(z_t)` normalized off the void and
    /// `z_t = −(1/T) dG/de_t` read at the current mixtures, every region in one read through `realization`. The fixed point
    /// `q = p(q)` is the stationary point of the answer's free energy `F(q) = G(q)/T − H₂(q)` (bits, on `2^(−32)`), and the step
    /// is certified on it as the ticks' steps are on `Φ`: a proposal stands where `F` does not rise, and its step then widens
    /// one octave back toward a half; where `F` rises, the proposal is refused and the step halves. An answer rests when its
    /// standing move is at most one grain (`2^(−16)`) or its step falls below a grain; the walk ends when every answer rests or
    /// after `reads` reads. Each place is then drawn from its mixture, keyed by `seed`. `observe` is shown each read's index,
    /// the answers still moving and the largest standing move. Why (Brandon, November 7 04:42: "if you're implying one pass
    /// over a negligible amount of data should take 20 minutes, that is unreasonable"): the writer re-read the whole field
    /// once a place (about 22,000 reads an answer at room 2,062), while every read already returns the energy's slope at every
    /// open place. Why certified (lap4's development read, November 7): at a fixed half step the mixtures oscillated on real
    /// fields, their largest move at 300 to 30,000 grains after 64 reads.
    #[allow(clippy::too_many_arguments)]
    pub fn energy_release(&self, problems: &[(&[usize], usize)], lengths: &[usize], void: usize, reads: usize, seed: u64, realization: &mut dyn FieldRealization, observe: &mut dyn FnMut(usize, usize, u32)) -> Result<Vec<Vec<usize>>> {
        let alphabet = self.declaration.alphabet;
        if !self.declaration.energy || void >= alphabet || alphabet < 2 || problems.len() != lengths.len() || lengths.iter().zip(problems).any(|(&n, &(_, room))| n == 0 || n > room) {
            return refuse("a joint release needs an energy field, a void in its alphabet and each answer's length within its room");
        }
        let one = 1u32 << STATE_BITS;
        let inverse = temperature_of(-self.theta[self.layout.face_temper], &self.fine)?;
        // The uniform mixture over the letters off the void, its remainder on the lowest letters.
        let letters = (alphabet - 1) as u32;
        let uniform: Vec<u32> = (0..alphabet).map(|c| if c == void { 0 } else { one / letters + u32::from(((if c < void { c } else { c - 1 }) as u32) < one % letters) }).collect();
        let n = problems.len();
        let mut classes: Vec<Vec<usize>> = Vec::with_capacity(n);
        let mut open: Vec<Vec<bool>> = Vec::with_capacity(n);
        for (&(q, room), &len) in problems.iter().zip(lengths) {
            let sites = q.len() + len + NEAR.min(room - len);
            classes.push((0..sites).map(|t| if t < q.len() { q[t] } else { void }).collect());
            open.push((0..sites).map(|t| t >= q.len() && t < q.len() + len).collect());
        }
        let to_shares = |w: &[u32]| -> Shares { w.iter().enumerate().filter(|&(_, &x)| x > 0).map(|(c, &x)| (c as u32, x)).collect() };
        // A face's masses off the void as weights on 2^(−16) summing to one, the remainder to the largest remainders.
        let off_void = |face: &TowerFace| -> Option<Vec<u32>> {
            let total: u128 = face.masses.iter().enumerate().filter(|&(c, _)| c != void).map(|(_, &m)| m).sum();
            if total == 0 {
                return None;
            }
            let mut w: Vec<u32> = vec![0; alphabet];
            let mut rest: Vec<(u128, usize)> = Vec::with_capacity(alphabet);
            let mut sum = 0u32;
            for (c, &m) in face.masses.iter().enumerate() {
                if c == void {
                    continue;
                }
                let scaled = m << STATE_BITS;
                w[c] = (scaled / total) as u32;
                sum += w[c];
                rest.push((scaled % total, c));
            }
            rest.sort_by(|a, b| b.0.cmp(&a.0).then(a.1.cmp(&b.1)));
            for &(_, c) in rest.iter().take((one - sum) as usize) {
                w[c] += 1;
            }
            Some(w)
        };
        // `−H₂(q)` on 2^(−32) bits: `Σ w (log₂ w − 16) / 2^16` over the open places' weights.
        let neg_entropy = |mixtures: &[Vec<u32>]| -> i128 {
            mixtures.iter().flat_map(|q| q.iter()).filter(|&&w| w > 0).map(|&w| (w as i128) * (super::super::log2_reading_at(w as u128, ENERGY_BITS) - ((STATE_BITS as i128) << ENERGY_BITS))).sum::<i128>() >> STATE_BITS
        };
        // One read of the answers `which` at their mixtures: each one's faces off the void at its open places and `F`.
        let read_at = |which: &[usize], mixtures: &[Vec<Vec<u32>>], realization: &mut dyn FieldRealization| -> Result<Vec<(i128, Vec<Option<Vec<u32>>>)>> {
            let carried: Vec<Vec<Option<Shares>>> = which
                .iter()
                .map(|&k| {
                    let start = problems[k].0.len();
                    (0..classes[k].len()).map(|t| open[k][t].then(|| to_shares(&mixtures[k][t - start]))).collect()
                })
                .collect();
            let views: Vec<Region> = which.iter().zip(&carried).map(|(&k, c)| Region { classes: &classes[k], unresolved: &open[k], faces: c, locked: &open[k], echo: &[], domain: None, port: None }).collect();
            let (faces, energies) = realization.read_energy_faces(self, &views)?;
            which
                .iter()
                .enumerate()
                .map(|(i, &k)| {
                    let start = problems[k].0.len();
                    let p: Vec<Option<Vec<u32>>> = (0..lengths[k]).map(|j| faces[i][start + j].as_ref().and_then(off_void)).collect();
                    let g = release(energies[i].checked_mul(inverse).ok_or(TowerError::Refused("a release's energy past its carrier"))?, MATERIAL_BITS);
                    Ok((g + neg_entropy(&mixtures[k]), p))
                })
                .collect()
        };
        let mut mixtures: Vec<Vec<Vec<u32>>> = lengths.iter().map(|&len| vec![uniform.clone(); len]).collect();
        let everyone: Vec<usize> = (0..n).collect();
        // Each answer's standing point: its free energy and faces, and its step's halvings.
        let mut standing: Vec<(i128, Vec<Option<Vec<u32>>>)> = read_at(&everyone, &mixtures, realization)?;
        let mut halvings = vec![1u32; n];
        let mut resting = vec![false; n];
        for read in 1..reads {
            let moving: Vec<usize> = (0..n).filter(|&k| !resting[k]).collect();
            if moving.is_empty() {
                break;
            }
            // Each moving answer's proposal: every open place stepped `2^(−s)` toward its face, summing to one.
            let mut proposed = mixtures.clone();
            for &k in &moving {
                for (q, p) in proposed[k].iter_mut().zip(&standing[k].1) {
                    let Some(p) = p else { continue };
                    let half = 1i64 << (halvings[k] - 1);
                    let mut next: Vec<u32> = q.iter().zip(p).map(|(&a, &b)| (a as i64 + ((b as i64 - a as i64 + half) >> halvings[k])).max(0) as u32).collect();
                    let sum: i64 = next.iter().map(|&x| x as i64).sum();
                    let top = (0..alphabet).max_by_key(|&c| (next[c], std::cmp::Reverse(c))).unwrap_or(0);
                    next[top] = (next[top] as i64 + one as i64 - sum).max(0) as u32;
                    *q = next;
                }
            }
            let reread = read_at(&moving, &proposed, realization)?;
            let mut largest = 0u32;
            for (&k, (f, p)) in moving.iter().zip(reread) {
                if f <= standing[k].0 {
                    let moved = proposed[k].iter().zip(&mixtures[k]).flat_map(|(a, b)| a.iter().zip(b).map(|(&x, &y)| x.abs_diff(y))).max().unwrap_or(0);
                    largest = largest.max(moved);
                    mixtures[k] = std::mem::take(&mut proposed[k]);
                    standing[k] = (f, p);
                    halvings[k] = halvings[k].saturating_sub(1).max(1);
                    resting[k] = moved <= 1;
                } else {
                    halvings[k] += 1;
                    resting[k] = halvings[k] > STATE_BITS;
                }
            }
            observe(read, moving.len(), largest);
        }
        // Each place drawn from its mixture, keyed.
        let mix = |counter: u64| -> u64 {
            let mut z = seed.wrapping_add(counter.wrapping_mul(0x9E37_79B9_7F4A_7C15));
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
            z ^ (z >> 31)
        };
        Ok(mixtures
            .iter()
            .enumerate()
            .map(|(k, answer)| {
                answer
                    .iter()
                    .enumerate()
                    .map(|(i, q)| {
                        let u = (mix((k as u64) << 32 | i as u64) >> 48) as u32;
                        let mut acc = 0u32;
                        (0..alphabet)
                            .find(|&c| {
                                acc += q[c];
                                acc > u
                            })
                            .unwrap_or(void)
                    })
                    .collect()
            })
            .collect())
    }

    /// [definition; the unified-theory readings of November 7, 09:02 and 09:09] **One sweep of the energy's own kernel over
    /// answers**: every answer place carries its present letter whole in every read (as [`Field::energy_release`]'s reads
    /// carry their mixtures), so one read gives `G` and every place's face. Each answer place in turn (the `j`-th place of
    /// every answer, the answers sharing the read) draws `a′` from its face at the current state, off the void; the read at
    /// the proposal gives `G′` and `face′`, and the place moves when its keyed coin falls under
    /// `A = 2^((G − G′)/T) q′(a)/q(a′)`, `q` the face off the void, at the temperature `2^(log₂ T − cool)` (`cool` halvings of
    /// the field's own). A taken move's proposal read is the next position's current read, so a position costs one read.
    /// The questions' places never move; each answer keeps its length, its near tail resolved at the void. Returns the places
    /// moved, the places proposed, and each answer's energy a place, the mean of its positions' `G/T` over its length, in
    /// nats on `2^(−32)`. `observe` is shown each position and the moves so far.
    #[allow(clippy::too_many_arguments)]
    pub fn energy_sweep(&self, problems: &[(&[usize], usize)], answers: &mut [Vec<usize>], void: usize, cool: u32, seed: u64, realization: &mut dyn FieldRealization, observe: &mut dyn FnMut(usize, usize)) -> Result<(usize, usize, Vec<i128>)> {
        self.energy_sweep_at(problems, answers, None, void, cool, seed, realization, observe)
    }

    /// [`Field::energy_sweep`] over the answer places `positions[k]` of each answer `k` (answer-relative, in their order;
    /// every place where `None`), the positions of all answers walked together (the unified-theory reading of November 7,
    /// 09:36: a persistent write moves the kernel's places, one residue class a problem). The energy a place is the mean
    /// over the positions walked.
    #[allow(clippy::too_many_arguments)]
    pub fn energy_sweep_at(&self, problems: &[(&[usize], usize)], answers: &mut [Vec<usize>], positions: Option<&[Vec<usize>]>, void: usize, cool: u32, seed: u64, realization: &mut dyn FieldRealization, observe: &mut dyn FnMut(usize, usize)) -> Result<(usize, usize, Vec<i128>)> {
        let alphabet = self.declaration.alphabet;
        if !self.declaration.energy || problems.len() != answers.len() || void >= alphabet || answers.iter().zip(problems).any(|(a, &(_, room))| a.is_empty() || a.len() > room) {
            return refuse("a kernel sweep needs an energy field and each answer within its room");
        }
        let mut field = self.clone();
        let at = field.layout.face_temper;
        field.theta[at] = fit32(field.theta[at] as i128 - ((cool as i128) << MATERIAL_BITS), "a cooled temperature past its carrier")?;
        let inverse = temperature_of(-field.theta[at], &field.fine)?;
        let one = 1u32 << STATE_BITS;
        let mix = |counter: u64| -> u64 {
            let mut z = seed.wrapping_add(counter.wrapping_mul(0x9E37_79B9_7F4A_7C15));
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
            z ^ (z >> 31)
        };
        let n = problems.len();
        let longest = answers.iter().map(Vec::len).max().unwrap_or(0);
        // The walk: each step's place for each answer (`None` where an answer has no place at that step).
        let steps: Vec<Vec<Option<usize>>> = match positions {
            None => (0..longest).map(|j| (0..n).map(|k| (j < answers[k].len()).then_some(j)).collect()).collect(),
            Some(pos) => {
                if pos.len() != n || pos.iter().zip(answers.iter()).any(|(p, a)| p.iter().any(|&j| j >= a.len())) {
                    return refuse("a sweep's places outside their answers");
                }
                let most = pos.iter().map(Vec::len).max().unwrap_or(0);
                (0..most).map(|i| (0..n).map(|k| pos[k].get(i).copied()).collect()).collect()
            }
        };
        let (mut moved, mut proposed) = (0usize, 0usize);
        let mut energy = vec![0i128; n];
        let mut walked = vec![0i128; n];
        // An answer's region, every answer place open and carrying its letter whole.
        let region_of = |k: usize, answer: &[usize]| -> (Vec<usize>, Vec<bool>, Vec<Option<Shares>>) {
            let (q, room) = problems[k];
            let len = q.len() + answer.len() + NEAR.min(room - answer.len());
            let classes: Vec<usize> = (0..len).map(|t| if t < q.len() { q[t] } else if t < q.len() + answer.len() { answer[t - q.len()] } else { void }).collect();
            let open: Vec<bool> = (0..len).map(|t| t >= q.len() && t < q.len() + answer.len()).collect();
            let faces: Vec<Option<Shares>> = (0..len).map(|t| open[t].then(|| vec![(classes[t] as u32, one)])).collect();
            (classes, open, faces)
        };
        let read = |states: &[(Vec<usize>, Vec<bool>, Vec<Option<Shares>>)], realization: &mut dyn FieldRealization| -> Result<(Vec<Vec<Option<TowerFace>>>, Vec<i128>)> {
            let views: Vec<Region> = states.iter().map(|(c, o, f)| Region { classes: c, unresolved: o, faces: f, locked: o, echo: &[], domain: None, port: None }).collect();
            realization.read_energy_faces(&field, &views)
        };
        // The current read of every answer.
        let states: Vec<_> = (0..n).map(|k| region_of(k, &answers[k])).collect();
        let (mut faces_now, mut g_now) = read(&states, realization)?;
        let off_void = |face: &TowerFace, c: usize| -> (u128, u128) { (face.masses[c], face.total - face.masses[void]) };
        let lg = |x: u128| -> i128 { super::super::log2_reading_at(x, ENERGY_BITS) };
        for (step, at_step) in steps.iter().enumerate() {
            // Each answer at its place of this step draws from its current face off the void; a draw of its present letter
            // moves nothing and needs no read.
            let mut asked: Vec<(usize, usize, usize)> = Vec::new();
            for (k, j) in at_step.iter().enumerate().filter_map(|(k, j)| j.map(|j| (k, j))) {
                energy[k] += release(g_now[k].checked_mul(inverse).ok_or(TowerError::Refused("a sweep's energy past its carrier"))?, MATERIAL_BITS);
                walked[k] += 1;
                let t = problems[k].0.len() + j;
                let face = faces_now[k][t].as_ref().ok_or(TowerError::Refused("a sweep's place with no face"))?;
                let letters = face.total - face.masses[void];
                if letters == 0 {
                    continue;
                }
                let u = ((mix(((k as u64) << 40) | (j as u64) << 8 | 1) as u128) << 64 | mix(((k as u64) << 40) | (j as u64) << 8 | 2) as u128) % letters;
                let mut acc = 0u128;
                let pick = (0..alphabet).filter(|&c| c != void).find(|&c| {
                    acc += face.masses[c];
                    acc > u
                }).unwrap_or(answers[k][j]);
                if pick != answers[k][j] {
                    asked.push((k, j, pick));
                }
            }
            if !asked.is_empty() {
                let next: Vec<_> = asked
                    .iter()
                    .map(|&(k, j, pick)| {
                        let mut a = answers[k].clone();
                        a[j] = pick;
                        region_of(k, &a)
                    })
                    .collect();
                let (faces_next, g_next) = read(&next, realization)?;
                for (&(k, j, b), (fnext, gnext)) in asked.iter().zip(faces_next.into_iter().zip(g_next)) {
                    proposed += 1;
                    let t = problems[k].0.len() + j;
                    let a = answers[k][j];
                    let (face, face2) = (faces_now[k][t].as_ref().ok_or(TowerError::Refused("a sweep's place with no face"))?, fnext[t].as_ref().ok_or(TowerError::Refused("a sweep's place with no face at its proposal"))?);
                    let (qa_m, qa_t) = off_void(face2, a);
                    let (qb_m, qb_t) = off_void(face, b);
                    if qa_m == 0 || qb_m == 0 || qa_t == 0 || qb_t == 0 {
                        continue;
                    }
                    let log_a = release((g_now[k] - gnext).checked_mul(inverse).ok_or(TowerError::Refused("a sweep's energy past its carrier"))?, MATERIAL_BITS) + (lg(qa_m) - lg(qa_t)) - (lg(qb_m) - lg(qb_t));
                    let u = (mix(((k as u64) << 40) | (j as u64) << 8 | 3) >> 1).max(1) as u128;
                    if lg(u) - (63i128 << ENERGY_BITS) < log_a {
                        answers[k][j] = b;
                        faces_now[k] = fnext;
                        g_now[k] = gnext;
                        moved += 1;
                    }
                }
            }
            observe(step, moved);
        }
        let per: Vec<i128> = energy
            .iter()
            .zip(answers.iter())
            .zip(&walked)
            .map(|((&e, a), &w)| {
                let len = a.len() as i128;
                release((e / w.max(1) / len).checked_mul(crate::hnn::keyed_modes::ln2_face()).unwrap_or(i128::MAX), 30)
            })
            .collect();
        Ok((moved, proposed, per))
    }

    /// [measurement; November 7] **A region's faces and its energy at the last state** ([`Field::energy_pass`]): the read the
    /// joint release certifies its step on.
    pub fn energy_faces_read(&self, region: &Region) -> Result<(Vec<Option<TowerFace>>, i128)> {
        let (pass, read) = self.energy_pass(region)?;
        Ok((pass.faces, read.last))
    }

    /// [measurement; theory, November 7 23:05] **A region's pairs by kind**, read from its opening's held supports (the
    /// classes a relaxation holds through its ticks): over every head and receiving site, the near field's keyed sources
    /// (`0 < |i − j| < NEAR`), a definite receiver's sharp class members past it (its probe's class and the classes it probes
    /// across its seams, §15.2), and an open receiver's listen-to-all past it (§15.9); and each head's eight largest definite
    /// classes, beside `reach / classes`. A reading only.
    pub fn energy_pair_kinds(&self, region: &Region) -> Result<EnergyPairKinds> {
        if !self.declaration.energy {
            return refuse("an energy read of a field whose faces are not one energy's forces");
        }
        let relaxed = self.energy_relax(region, 0, None, None)?;
        let sites = region.classes.len();
        let mut out = EnergyPairKinds { sites, near: 0, sharp: 0, listened: 0, largest: Vec::new(), classes: self.declaration.classes() };
        for lists in &relaxed.held.classes {
            for i in 0..sites {
                let open = !lists.definite[i];
                for j in lists.support(i) {
                    if j.abs_diff(i) < NEAR {
                        out.near += 1;
                    } else if open {
                        out.listened += 1;
                    } else {
                        out.sharp += 1;
                    }
                }
            }
            let mut sizes: Vec<usize> = (0..out.classes).map(|c| (lists.off[2 * c + 1] - lists.off[2 * c]) as usize).collect();
            sizes.sort_unstable_by(|a, b| b.cmp(a));
            sizes.truncate(8);
            out.largest.push(sizes);
        }
        Ok(out)
    }

    /// [measurement; the unified-theory reading of November 7, 04:05] **A configuration's energy**: `G(e) = Φ(x^K(e); e)` with
    /// every site resolved at `classes`, relaxed at its own certified halvings, on `2^(−32)` bits; the enumerated conditional's
    /// terms (`P(e_t = c | rest) ∝ 2^(−G/T)`) and route (b)'s `G`.
    pub fn energy_g(&self, classes: &[usize]) -> Result<i128> {
        if !self.declaration.energy {
            return refuse("an energy read of a field whose faces are not one energy's forces");
        }
        let none = vec![false; classes.len()];
        let region = Region { classes, unresolved: &none, faces: &[], locked: &[], echo: &[], domain: None, port: None };
        Ok(self.energy_relax(&region, self.declaration.ticks, None, None)?.cell.phi)
    }

    /// [measurement] **A region's energy read** ([`EnergyRead`]): the energy at the opening and at the last tick, each
    /// tick's halvings, and the energy's reads.
    pub fn energy_read(&self, region: &Region) -> Result<EnergyRead> {
        if !self.declaration.energy {
            return refuse("an energy read of a field whose faces are not one energy's forces");
        }
        Ok(self.energy_pass(region)?.1)
    }

    /// [measurement; theory, November 8 02:56] **The descent read to rest**: the relaxation of [`Field::energy_material`]'s
    /// region with no tick count, at most `most` ticks, each tick's halvings, fall and slack `2R + 2` (both on `2^(−32)`), and
    /// why it ended: whether the ticks' need `K` is a pick, and whether the energy's grain decides where the descent rests
    /// (falls near rest come down to the slack) or not. The same law as [`Field::energy_relax`]'s loop, keeping no trail.
    ///
    /// [measurement; theory, November 8 03:32] With `rebase`, each lane is re-based after each tick to its opening scale,
    /// `x_ℓ ← s⁰_ℓ·r̂_ℓ`: Φ reads a lane only through its direction, so the scale lies in the kernel of every reading of
    /// Φ, and each tick otherwise multiplies it by `√(1 + 2η·mean(r̂F) + η²·mean(F²)) > 1`; each tick reports the lanes'
    /// largest scale's top place before the re-base and the change of Φ the re-base makes (the chart's release).
    ///
    /// [measurement; theory, November 8 04:21 and 04:54] With [`RestMode::Flow`], the tick is a certified flow step: each
    /// candidate is re-based inside itself (`s⁰·N(x + η s F)`, before its energy is read, so acceptance sees the re-base's
    /// rounding), and it stands only where its fall passes both the slack and half its first-order claim
    /// `η Σ (|F|² − ⟨r̂, F⟩²/W)` (half the claim is a quadratic's line minimum, so `η` stops at the energy's own curvature).
    pub fn energy_rest_read(&self, region: &Region, most: usize, mode: RestMode) -> Result<EnergyRest> {
        let (faces, locked) = self.energy_sites(region);
        let region = &Region { faces: &faces, locked: &locked, ..*region };
        self.admit_region(region)?;
        let d = &self.declaration;
        if self.scale.is_some() || !d.energy {
            return refuse("a rest read of a field without one energy");
        }
        let (dw, sites) = (d.width, region.classes.len());
        let reaches = self.reaches();
        let paces = self.paces(region)?;
        if paces.plain.iter().any(|&p| !p) {
            return refuse("a rest read with a clock that is not plain");
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
        let lanes = d.lanes;
        let lane_width = dw / lanes;
        let scale_top = |x: &[i64]| -> Result<u32> {
            let mut top = 0u32;
            for lane in x.chunks_exact(lane_width) {
                let (_, s) = ratio_to_power(lane)?;
                top = top.max(128 - s.unsigned_abs().leading_zeros());
            }
            Ok(top)
        };
        let mut out = EnergyRest { opening: cell.phi, last: cell.phi, opening_scale_top: scale_top(&x)?, ticks: Vec::new(), tries: Vec::new(), ended: RestEnd::Most };
        let mut first = FIRST_HALVINGS;
        let swinging = matches!(mode, RestMode::SwingProjected | RestMode::SwingPerLane);
        let projected = matches!(mode, RestMode::Projected | RestMode::PerLane) || swinging;
        let per_lane = matches!(mode, RestMode::PerLane | RestMode::SwingPerLane);
        let flowing = matches!(mode, RestMode::Flow | RestMode::Line) || projected;
        let lined = matches!(mode, RestMode::Line) || projected;
        // The swing (theory, November 8 06:40): the motion v that brought x (on the state's grain), held across ticks at a
        // held η, and its μ on 2^(−16): μ = (1 − √(ηλ_soft))², ηλ_soft = 1 − 2^(r/2) from the first-order gap rate r a tick
        // the projected and per-lane reads measured (−0.0068 and −0.0182), so the softest mode is critical.
        let mu: i128 = match mode {
            RestMode::SwingProjected => 59_310,
            RestMode::SwingPerLane => 55_575,
            _ => 0,
        };
        let mut v = vec![0i64; x.len()];
        let mut swing_h: Option<u32> = None;
        // The metric the carried motion was formed in (theory, 08:01): each lane's rms(F) at the tick that formed v; when the
        // unit is re-read, v_ℓ ← v_ℓ √(rms_(t−1)/rms_t), so Σ_ℓ |v_ℓ|²/η_ℓ is unchanged and the re-read does no work.
        let mut prev_rms: Vec<i128> = Vec::new();
        // The last standing swing tick's Q at x' in its parts (Φ, ½⟨F, v⟩, the kinetic term), to read Q's gap across ticks.
        let mut last_q: Option<(i128, i128, i128)> = None;
        // (theory, 07:28) A state on its chart re-bases to itself: a lane is re-based only when its rms has left its held
        // scale by more than one unit of its grain, so a below-grain step returns x and the read ends by the grain or the
        // field, never by the chart's rounding.
        let rebase = |stepped: &[i64]| -> Result<Vec<i64>> {
            let mut based = Vec::with_capacity(stepped.len());
            for (k, lane) in stepped.chunks_exact(lane_width).enumerate() {
                let (r, s) = ratio_to_power(lane)?;
                if (s - scale0[k]).abs() <= 1 {
                    based.extend_from_slice(lane);
                    continue;
                }
                for &rk in &r {
                    based.push(fit64(release(scale0[k] * rk as i128, FACE_BITS))?);
                }
            }
            Ok(based)
        };

        // ⟨F, v⟩ on Φ's 2^(−32): F on 2^(−24) a unit of r̂, v on the state's grain over the lane's held scale.
        let work = |f: &[i64], vv: &[i64]| -> i128 {
            f.chunks_exact(lane_width).zip(vv.chunks_exact(lane_width)).enumerate().map(|(k, (fl, vl))| {
                let fv: i128 = fl.iter().zip(vl).map(|(&a, &b)| a as i128 * b as i128).sum();
                div_nearest(fv << 8, scale0[k].max(1))
            }).sum()
        };
        for tick in 0..most {
            // A refusal ends the read where it happened (its tick and the state's top place there), never the whole read.
            let top = x.iter().map(|v| 64 - v.unsigned_abs().leading_zeros()).max().unwrap_or(0);
            let Ok((force, _)) = self.energy_force(&cell, &held, &paces, &reaches) else {
                out.ended = RestEnd::Refused { state_top: top };
                break;
            };
            let (mut stood, mut below_grain, mut last_slack, mut refused) = (None, false, 0i128, false);
            // The first-order claim on 2^(−48) before its halvings: Σ over lanes of |F|² − ⟨r̂, F⟩²/W (`energy_fall`'s).
            let mut first_order = 0i128;
            // Each lane's radial curvature ρ = ⟨r̂, F⟩/W (theory, 05:39: the sphere is the line's curvature, η's unit is 1/ρ),
            // on F's 2^(−24), and the force a step takes: F, its tangential part F_⊥ = F − r̂⟨r̂, F⟩/W (projected), or F_⊥
            // over the lane's own rms(F) (each lane at its own unit).
            let mut rhos: Vec<i128> = Vec::with_capacity(x.len() / lane_width);
            let mut lane_rms: Vec<i128> = Vec::with_capacity(x.len() / lane_width);
            // Each lane's radial share ρ_ℓ²/rms(F_ℓ)², in thousandths.
            let mut radial: Vec<i128> = Vec::with_capacity(x.len() / lane_width);
            let mut step_force = force.clone();
            let mut perp_force = force.clone();
            if flowing {
                for t in 0..x.len() / dw {
                    for k in 0..lanes {
                        let at = t * dw + k * lane_width;
                        let ff: i128 = (0..lane_width).map(|i| force[at + i] as i128 * force[at + i] as i128).sum();
                        let rf: i128 = (0..lane_width).map(|i| force[at + i] as i128 * cell.read[at + i] as i128).sum();
                        let perp = ff - release(div_nearest(rf * rf, lane_width as i128), 32);
                        let mean_rf = div_nearest(rf, lane_width as i128);
                        rhos.push(release(mean_rf, FACE_BITS));
                        // (theory, 08:01) A lane's unit is re-read every tick: rms(F_ℓ) carries its radial part ρ_ℓ, the
                        // sphere's own curvature, so near rest it is the lane's curvature unit.
                        let rms = ((ff / lane_width as i128) as u128).isqrt() as i128;
                        lane_rms.push(rms);
                        radial.push(if rms > 0 { (release(mean_rf * mean_rf, 32) * 1000) / (rms * rms) } else { 0 });
                        if projected {
                            for i in 0..lane_width {
                                let fp = force[at + i] as i128 - release(cell.read[at + i] as i128 * mean_rf, 32);
                                perp_force[at + i] = fit64(fp)?;
                                step_force[at + i] = if per_lane {
                                    if rms == 0 { 0 } else { fit64(div_nearest(fp << super::super::COVECTOR_BITS, rms))? }
                                } else {
                                    fit64(fp)?
                                };
                            }
                            first_order += if per_lane { if rms == 0 { 0 } else { div_nearest(perp << 8, rms) << 16 } } else { perp };
                        } else {
                            first_order += perp;
                        }
                    }
                }
            }
            let (radial_least, radial_median, radial_top) = {
                let mut r = radial.clone();
                r.sort_unstable();
                if r.is_empty() { (0, 0, 0) } else { (r[0], r[r.len() / 2], r[r.len() - 1]) }
            };
            let rho_bits = |v: i128| 128 - v.unsigned_abs().leading_zeros();
            let (rho_nonpositive, rho_least, rho_median, rho_top) = {
                let mut pos: Vec<i128> = rhos.iter().copied().filter(|&r| r > 0).collect();
                pos.sort_unstable();
                let n = rhos.len() - pos.len();
                if pos.is_empty() { (n, 0, 0, 0) } else { (n, rho_bits(pos[0]), rho_bits(pos[pos.len() / 2]), rho_bits(pos[pos.len() - 1])) }
            };
            // The swing's tick: v' = μv + η F(x) (its step's force), x' = N(x + v') re-based inside, standing where
            // Q(x, v) = Φ(x) + ½⟨F(x), v⟩ + (1 + μ)/4 Σ_ℓ |v_ℓ|²/η_ℓ falls past the slack and the band guard
            // ⟨F(x) − F(x'), v'⟩ < 2(1 + μ) Σ_ℓ |v'_ℓ|²/η_ℓ holds; otherwise the motion is released and the tick is the flow
            // step's, whose halvings the next swing holds.
            if let Some(hs) = swing_h.filter(|_| swinging) {
                // Σ_ℓ |v_ℓ|²/η_ℓ on 2^(−32): (|v|/s)² 2^h, times rms(F) on 2^(−24) a lane at its own unit.
                let kinetic = |vv: &[i64]| -> i128 {
                    vv.chunks_exact(lane_width).enumerate().map(|(k, vl)| {
                        let vv2: i128 = vl.iter().map(|&b| b as i128 * b as i128).sum();
                        let s2 = (scale0[k] * scale0[k]).max(1);
                        let base = div_nearest(vv2 << 32, s2) << hs;
                        if per_lane { release(base * lane_rms[k], super::super::COVECTOR_BITS) } else { base }
                    }).sum()
                };
                // The carried motion into this tick's metric: v_ℓ √(rms_(t−1)/rms_t) on 2^(−16), lane by lane.
                let v_before = v.clone();
                if per_lane && prev_rms.len() == lane_rms.len() {
                    for (k, vl) in v.chunks_exact_mut(lane_width).enumerate() {
                        let (was, now) = (prev_rms[k], lane_rms[k]);
                        if was > 0 && now > 0 && was != now {
                            let factor = (((was as u128) << 32) / now as u128).isqrt() as i128;
                            for e in vl.iter_mut() {
                                *e = fit64(release(*e as i128 * factor, 16))?;
                            }
                        }
                    }
                }
                // [measurement] Q's gap across ticks, q_now(t) − q_next(t−1), in its parts: Φ, the work as F is read again,
                // the work under the re-read's rescale, and the kinetic term.
                let gaps = last_q.map(|(phi, w, k)| {
                    let w_before = work(&force, &v_before) / 2;
                    let w_now = work(&force, &v) / 2;
                    let k_now = ((1 << 16) + mu) * kinetic(&v) >> 18;
                    [cell.phi - phi, w_before - w, w_now - w_before, k_now - k]
                }).unwrap_or([0; 4]);
                let stepped = self.energy_step(&x, &cell.scale, &step_force, hs)?;
                let moved: Vec<i64> = stepped.iter().zip(&x).zip(&v).map(|((&st, _), &vi)| st + release(mu * vi as i128, 16) as i64).collect();
                let next = rebase(&moved)?;
                if next != x {
                    let candidate = self.energy_cell(&next, &held, &paces, &reaches, window.as_deref())?;
                    let (cand_force, _) = self.energy_force(&candidate, &held, &paces, &reaches)?;
                    // The motion that brought x': the re-based displacement's tangent part at x'.
                    let mut v_new: Vec<i64> = next.iter().zip(&x).map(|(&a, &b)| a - b).collect();
                    for (vl, xl) in v_new.chunks_exact_mut(lane_width).zip(next.chunks_exact(lane_width)) {
                        let xx: i128 = xl.iter().map(|&a| a as i128 * a as i128).sum();
                        let xv: i128 = xl.iter().zip(vl.iter()).map(|(&a, &b)| a as i128 * b as i128).sum();
                        if xx > 0 {
                            for (vi, &xi) in vl.iter_mut().zip(xl) {
                                *vi -= div_nearest(xi as i128 * xv, xx) as i64;
                            }
                        }
                    }
                    // The certificate spans the unit's re-read (measured November 8, problem 16370: from tick 100 on the
                    // rescale's work put back 1.6743e13 of the 1.6711e13 the ticks certified): the tick falls from the Q it
                    // stood at, q_next(t − 1), not from Q after the re-read, so the re-read's work is the tick's to pay.
                    let q_now = last_q.map(|(phi, w, k)| phi + w + k).unwrap_or(cell.phi + work(&force, &v) / 2 + (((1 << 16) + mu) * kinetic(&v) >> 18));
                    let q_next = candidate.phi + work(&cand_force, &v_new) / 2 + (((1 << 16) + mu) * kinetic(&v_new) >> 18);
                    let sum: Vec<i64> = v.iter().zip(&v_new).map(|(&a, &b)| a + b).collect();
                    let claim = ((1 << 16) - mu) * kinetic(&sum) >> 18;
                    let diff: Vec<i64> = force.iter().zip(&cand_force).map(|(&a, &b)| a - b).collect();
                    let (lhs, rhs) = (work(&diff, &v_new), ((1 << 16) + mu) * kinetic(&v_new) >> 15);
                    let inside = lhs < rhs;
                    let slack = (cell.logs + candidate.logs) as i128 + 2;
                    // Why a swing tick would release: the band guard's ratio (milli) and whether Q fell past the slack.
                    let note = if !inside { 1 } else if q_next + slack > q_now { 2 } else { 0 };
                    out.tries.push(RestTry { tick, halvings: hs, fall: q_now - q_next, claim, slack, note, guard_milli: if rhs > 0 { lhs * 1000 / rhs } else { 0 } });
                    if inside && q_next + slack <= q_now {
                        out.ticks.push(RestTick { halvings: hs, fall: q_now - q_next, slack, scale_top: 0, rebase_change: cell.phi - candidate.phi, claim, rho_nonpositive, rho_least, rho_median, rho_top, radial_least, radial_median, radial_top, gaps, swing: true });
                        last_q = Some((candidate.phi, work(&cand_force, &v_new) / 2, ((1 << 16) + mu) * kinetic(&v_new) >> 18));
                        x = next;
                        cell = candidate;
                        v = v_new;
                        prev_rms = lane_rms.clone();
                        continue;
                    }
                }
                // Released: the motion lets go, and the tick is the flow step's.
                v.iter_mut().for_each(|e| *e = 0);
                swing_h = None;
                last_q = None;
            }
            let mut h = first;
            // The line's controller (theory, 05:13): the least halvings whose half-claim failed this tick.
            let mut failed_half: Option<u32> = None;
            let mut line_rest = false;
            while h <= STEP_CARRIER_HALVINGS {
                let Ok(stepped) = self.energy_step(&x, &cell.scale, &step_force, h) else {
                    refused = true;
                    break;
                };
                // The flow step's candidate is re-based inside itself, before its energy is read.
                let next = if flowing { rebase(&stepped)? } else { stepped };
                if next == x {
                    below_grain = true;
                    break;
                }
                let Ok(candidate) = self.energy_cell(&next, &held, &paces, &reaches, window.as_deref()) else {
                    refused = true;
                    break;
                };
                let slack = (cell.logs + candidate.logs) as i128 + 2;
                last_slack = slack;
                let claim = if flowing { release(first_order, 16 + h) } else { 0 };
                let tried = cell.phi - candidate.phi;
                if flowing {
                    out.tries.push(RestTry { tick, halvings: h, fall: tried, claim, slack, note: 0, guard_milli: 0 });
                }
                let half_passes = 2 * tried >= claim;
                if lined && !(half_passes && tried >= slack) {
                    // Passing half the claim but not the slack, the step is short of the line's minimum: double it, unless
                    // the half-claim failed just above (one doubling up), where the field rests at its release error.
                    // Failing half the claim, the step is past the minimum: halve it.
                    if half_passes {
                        if h == 0 || failed_half == Some(h - 1) {
                            line_rest = true;
                            break;
                        }
                        h -= 1;
                    } else {
                        failed_half = Some(failed_half.map_or(h, |f| f.min(h)));
                        h += 1;
                    }
                    continue;
                }
                if candidate.phi + slack <= cell.phi && half_passes {
                    let fall = cell.phi - candidate.phi;
                    let top = scale_top(&next).unwrap_or(u32::MAX);
                    let (next, candidate, rebase_change) = if mode == RestMode::Rebase {
                        // Each lane back to its opening scale: its direction kept, released to the state's grain.
                        let mut based = Vec::with_capacity(next.len());
                        for (k, lane) in next.chunks_exact(lane_width).enumerate() {
                            let (r, _) = ratio_to_power(lane)?;
                            let s0 = scale0[k];
                            for &rk in &r {
                                based.push(fit64(release(s0 * rk as i128, FACE_BITS))?);
                            }
                        }
                        let based_cell = self.energy_cell(&based, &held, &paces, &reaches, window.as_deref())?;
                        let change = based_cell.phi - candidate.phi;
                        (based, based_cell, change)
                    } else {
                        (next, candidate, 0)
                    };
                    out.ticks.push(RestTick { halvings: h, fall, slack, scale_top: top, rebase_change, claim, rho_nonpositive, rho_least, rho_median, rho_top, radial_least, radial_median, radial_top, gaps: [0; 4], swing: false });
                    x = next;
                    cell = candidate;
                    stood = Some(h);
                    break;
                }
                h += 1;
            }
            match stood {
                // Each tick starts one halving above the last stood one, so a step that keeps passing grows back.
                Some(h) => {
                    first = h.saturating_sub(1);
                    if swinging {
                        // The swing holds the flow step's η, its per-lane unit included, until a release re-reads it.
                        swing_h = Some(h);
                        prev_rms = lane_rms.clone();
                    }
                }
                None => {
                    out.ended = if refused {
                        RestEnd::Refused { state_top: top }
                    } else if line_rest {
                        RestEnd::AtTheLine { slack: last_slack }
                    } else if below_grain {
                        RestEnd::BelowGrain
                    } else {
                        RestEnd::InsideSlack { slack: last_slack }
                    };
                    break;
                }
            }
        }
        out.last = cell.phi;
        Ok(out)
    }
}

/// The width census (theory, November 8 04:08): the reverse's opening covector `λ^K` (on `2^(−24)`), its top place, its
/// entries at zero and within one unit (the places the last tick's lane scale took from it), beside the last state's lane
/// scales and the last tick's force.
fn census_lambda(lambda: &[i64], scales: &[i128], force: &[i64]) {
    if !crate::number::census::enabled() {
        return;
    }
    for &l in lambda {
        crate::number::census::reach("reverse: λ^K's entries, on 2^-24", &l);
    }
    crate::number::census::tally("reverse: λ^K's entries", lambda.len() as u64);
    crate::number::census::tally("reverse: λ^K's entries at zero", lambda.iter().filter(|&&l| l == 0).count() as u64);
    crate::number::census::tally("reverse: λ^K's entries within one unit", lambda.iter().filter(|&&l| l.unsigned_abs() <= 1).count() as u64);
    for &s in scales {
        crate::number::census::reach("reverse: the last state's lane scales", &s);
    }
    for &f in force {
        crate::number::census::reach("reverse: the last tick's force F^K, on 2^-24", &f);
    }
}

/// [measurement] A descent read to rest ([`Field::energy_rest_read`]).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct EnergyRest {
    pub opening: i128,
    pub last: i128,
    /// The lanes' largest scale's top place at the opening (on the state's grain).
    pub opening_scale_top: u32,
    pub ticks: Vec<RestTick>,
    /// Every candidate the flow modes tried, stood or not (theory, 05:13: three halvings' falls give the line's offset,
    /// slope and curvature).
    pub tries: Vec<RestTry>,
    pub ended: RestEnd,
}

/// One tried candidate of a flow-mode tick: its tick, halvings, fall, first-order claim and slack (on `2^(−32)`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RestTry {
    pub tick: usize,
    pub halvings: u32,
    pub fall: i128,
    pub claim: i128,
    pub slack: i128,
    /// A swing try's release reason: 0 none, 1 the band guard failed, 2 Q did not fall past the slack.
    pub note: u8,
    /// The band guard's ⟨F(x) − F(x'), v'⟩ over 2(1 + μ) Σ|v'|²/η, in thousandths (swing tries).
    pub guard_milli: i128,
}

/// One tick that stood: its halvings, its fall and the slack it fell past (on `2^(−32)`), the lanes' largest scale's top
/// place after the step, and the change of Φ the re-base made (zero without it).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RestTick {
    pub halvings: u32,
    pub fall: i128,
    pub slack: i128,
    pub scale_top: u32,
    pub rebase_change: i128,
    /// The flow step's first-order claim at its halvings (zero in the other modes), on `2^(−32)`.
    pub claim: i128,
    /// The lanes' radial curvature `ρ = ⟨r̂, F⟩/W` (on F's `2^(−24)`; flow modes): the lanes at or below zero, and the
    /// least, median and top places of the positive ones.
    pub rho_nonpositive: usize,
    pub rho_least: u32,
    pub rho_median: u32,
    pub rho_top: u32,
    /// Each lane's radial share ρ_ℓ²/rms(F_ℓ)² in thousandths (flow modes): least, median and top.
    pub radial_least: i128,
    pub radial_median: i128,
    pub radial_top: i128,
    /// [measurement] A swing tick's gap from the last standing swing tick's Q at x', `q_now(t) − q_next(t−1)`, in parts: Φ,
    /// the work ½⟨F, v⟩ as F is read again, the work under the unit re-read's rescale, and the kinetic term (2^(−32)).
    pub gaps: [i128; 4],
    /// Whether the tick was the swing's (its fall and claim are then Q's, and `rebase_change` holds Φ's own fall).
    pub swing: bool,
}

/// How a rest read ticks: as the law runs, re-based to the opening scale after each tick, or as a certified flow step
/// (re-based inside the candidate, standing at half its first-order claim).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RestMode {
    Law,
    Rebase,
    Flow,
    /// The flow step with the line's controller (theory, November 8 05:13): passing half the claim but not the slack it
    /// doubles, failing half the claim it halves, and it rests only on a halving under the slack just below a failed
    /// half-claim, so every rest is the field's own (its line's best fall under 4/3 of the slack). Each tick starts one halving
    /// above the last stood one, so a step that keeps passing half its claim grows back a doubling a tick.
    Line,
    /// The line's controller on the projected step `N(r̂ + η F_⊥)`, whose half-claim reads a true line (theory, 05:39).
    Projected,
    /// The projected step with each lane at its own unit, `η = 2^(−h)/rms(F)` a lane, the claim `Σ η_ℓ |F_⊥ℓ|²`.
    PerLane,
    /// The swing on the projected step (theory, November 8 06:40): motion carried across ticks at a held η, certified on
    /// `Q = Φ + ½⟨F, v⟩ + (1 + μ)/4 Σ|v|²/η` with the band guard, released to the flow step where either fails.
    SwingProjected,
    /// The swing on the per-lane unit (theory, November 8 08:01): each lane's unit rms(F_ℓ) is re-read every tick, in the
    /// swing and the flow alike, and the carried motion enters the new metric as `v_ℓ √(rms_(t−1)/rms_t)`, which keeps
    /// `Σ_ℓ |v_ℓ|²/η_ℓ` unchanged. The rescale still changes the work `½⟨F, v⟩`, so a swing tick is certified from the Q it
    /// last stood at, `q_next(t − 1)`, and pays for the re-read (agent-inferred from the measured gap, November 8).
    ///
    /// [theory, 09:33] With `s = √(rms_t/rms_(t+1))` the rescale adds `μ(s − 1)v` to the next displacement, whose first-order
    /// change of Φ, `−μ(s − 1)⟨F, v⟩`, is negative on both legs of an orbit: the transport is a push downhill. Its cost is
    /// the work's rise `½(s − 1)⟨F, v⟩`, and charging it to the tick whose step carries the rescaled motion takes the push
    /// only where that tick's fall covers it. Carrying v untransported with Q at x' read in the next tick's metric also
    /// closes Q (bit for bit, measured on problem 16370) but throws the push away. [measurement, November 8] The four census
    /// problems rest below the grain under both; here against untransported, ticks and fall: 23957 288 at 3.88964e15
    /// against 344 at 3.88470e15, 22383 232 at 3.56344e15 against 273 at 3.52481e15, 16370 84 at 6.61400e14 against 221
    /// at 6.61026e14, and 21778 416 at 3.53770e15 against 220 at 3.54590e15, the one problem where untransported rests
    /// sooner and deeper. The lanes past their own band are no guard to add: the low-radial lanes that carried the
    /// transport's whole work (100.5% of it from tick 100 on) stayed inside their bands.
    ///
    /// [measurement, November 8 09:55] Declining the push before dropping the motion (theory, 09:43: a refused transported
    /// try re-taken with the motion untransported against the same stood Q) did not keep the motion: the retake stood on
    /// 2 of 27, 2 of 34, 2 of 29 and 0 of 8 refused ticks (23957, 22383, 21778, 16370), and its Q fell less than the
    /// transported try's on all but 3, 5, 5 and 0 of them (median −2.2e11 against −5.5e10 on 23957), since a refusal
    /// comes where the unit grows and the untransported motion then carries the heavier weight. Releases went 25, 32, 27
    /// and 8 against 22, 16, 34 and 8, and the rests were shallower on 23957 (3.88843e15) and 22383 (3.56285e15), deeper
    /// on 21778 (3.53862e15, short of the untransported form's 3.54590e15) and the same on 16370, so it is not kept.
    SwingPerLane,
}

/// Why a descent ended: at the read's most ticks, a step below the state's grain at every halving left, no fall past the
/// slack by the step's carrier (the last slack read), or a carrier's refusal (the state's top place where it came).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum RestEnd {
    #[default]
    Most,
    BelowGrain,
    InsideSlack { slack: i128 },
    Refused { state_top: u32 },
    /// The line's rest: a halving under the slack just below a failed half-claim (the slack read there).
    AtTheLine { slack: i128 },
}

/// [measurement; theory, November 7 23:05] A region's pairs by kind ([`Field::energy_pair_kinds`]), summed over its heads.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EnergyPairKinds {
    pub sites: usize,
    pub near: u64,
    pub sharp: u64,
    pub listened: u64,
    /// Each head's eight largest definite classes.
    pub largest: Vec<Vec<usize>>,
    pub classes: usize,
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

/// A one-base square's corners as read ([`Field::energy_square_reading`]): `i`'s logits with `j` at `b` and at `b′`, `j`'s with
/// `i` at `a` and at `a′`, the base's own at `i` and `j` and each with the other's mixture moved by `ε` and by `4ε` (`b′` up from
/// `b`, `a′` up from `a`), and `G` at `(a′, b)`, `(a, b′)`, `(a, b)` and `(a′, b′)` on `2^(−32)` bits.
#[derive(Clone, Copy, Debug)]
pub struct SquareCorners<'a> {
    pub zi_b: &'a [i64],
    pub zj_a: &'a [i64],
    pub zi_b2: &'a [i64],
    pub zj_a2: &'a [i64],
    pub zi: &'a [i64],
    pub zj: &'a [i64],
    pub zi_moved: &'a [i64],
    pub zj_moved: &'a [i64],
    /// The same at four times the step.
    pub zi_wide: &'a [i64],
    pub zj_wide: &'a [i64],
    pub g: [i128; 4],
}

/// [measurement] A square read at one base ([`Field::energy_square_corners`]): the runner-ups `(a′, b′)`, the two readings
/// over whole letters on `2^(−20)` bits, and the attribution read's two readings at `ε` on `2^(−16)` bits.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EnergySquare {
    pub runners: (usize, usize),
    pub lambda_i: i64,
    pub lambda_j: i64,
    pub small_i: i128,
    pub small_j: i128,
    /// The attribution read at four times the step.
    pub wide_i: i128,
    pub wide_j: i128,
    /// The readings on the faces' logits, on `2^(−20)` bits.
    pub zlambda_i: i64,
    pub zlambda_j: i64,
    /// The energy's own square over `T`, `(G(a′,b) + G(a,b′) − G(a,b) − G(a′,b′))/T`, on `2^(−20)` bits.
    pub glambda: i64,
    /// The eight codes on the face's floor.
    pub floors: u32,
}

/// [measurement] The force and its tangent read on a state ([`Field::energy_tangent_read`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EnergyTangentRead {
    pub tangent: Vec<i64>,
    pub difference: Vec<i64>,
    pub uv: i128,
    pub vu: i128,
    pub fall: i128,
    pub first: i128,
    /// `Φ(x − δv) − Φ(x + δv)`, on `2^(−32)` bits, against `2 · first`.
    pub central: i128,
}
