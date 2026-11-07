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
/// The most halvings a tick reads before the state rests: past them the step is below the state's grain.
pub const MOST_HALVINGS: u32 = STATE_BITS + 8;

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
        let carry = |what: &'static str, v: Option<i128>| v.ok_or(TowerError::Refused(what));
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
        Ok((force, dp))
    }

    /// [definition; the unified-theory reading of November 7, 00:02] **The force's tangent**, `δF = (∂F/∂r̂) v = −Hess Φ · v`
    /// along a direction `v` of the chart reads (`[t][D]` on `2^(−24)`), and the probes' share of it (`[t][2M]`, unframed,
    /// on `2^(−24)`): the words' tangents through the charts, the frame and the unit power (whose Jacobian is its own
    /// return, [`ratio_adjoint`]), the locks' ([`Field::lock_words`]), the unit power's return differentiated along them
    /// (`δ(J f) = J δf − (δŵ⟨ŵ, f⟩ + ŵ⟨δŵ, f⟩)/(d ‖w̃‖) − J f ⟨ŵ, δw̃⟩/(d ‖w̃‖)`), the frame's and the charts' transposes, and the
    /// pair's (linear in each drive). The letters' force does not move with the state. `Φ`'s Hessian is symmetric, so the
    /// tangent is also the tick's adjoint on a covector.
    fn energy_tangent(&self, c: &EnergyCell, held: &Held, paces: &Paces, reaches: &Reaches, v: &[i64]) -> Result<(Vec<i64>, Vec<i64>)> {
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
        Ok((out, cp))
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
                    trail.push(Step { cell: std::mem::replace(&mut cell, candidate), force: force.clone(), halvings: h });
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

    /// [measurement; a test's reading] **The force is the energy's slope**: at the opening, the energy's fall under a step of
    /// `2^(−h)` beside the step's first-order fall `2^(−h) Σ_t (|F_t|² − ⟨r̂_t, F_t⟩²/W)` (each lane's), both on `2^(−32)` bits.
    #[cfg(test)]
    pub(super) fn energy_slope(&self, region: &Region, h: u32) -> Result<(i128, i128)> {
        let d = &self.declaration;
        let Relaxed { x, cell, held, paces, window, .. } = self.energy_relax(region, 0, None, None)?;
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
        Ok(EnergyTangentRead { tangent: tv, difference, uv, vu, fall: cell.phi - moved.phi, first })
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
}
