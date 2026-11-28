//! [definition; theory, November 13, the design record of that day §4.2 to §4.9 (`agent-inferred`)] **The level above**: level 0 is
//! the field on the places; level 1 is a field of its own on **epochs**, each led by a **site**, a landmark of the news below it. After
//! the fine field's first `split` ticks each epoch is opened on its places' reads charted by the **news phase**, the level's field runs its
//! own ticks on **its own clock**, the news between its sites, each place receives its epoch back through the same chart, and the fine
//! field's remaining ticks and its face follow:
//!
//! ```text
//! news      c_t        the opening's code: a written place's class at its cavity face, elsewhere the face's expected code
//! section   σ          the flat face's code over the alphabet: the news of one place nothing predicts
//! sites     ρ_t ≥ σ    ρ_t = min(S_t − S_u at the last u < t with c_u ≥ c_t, S_u − S_t at the first u > t with c_u > c_t), S the news's sum
//! phase     φ_t = (S_t − S_(a_j))/σ       from the anchor a_j of t's epoch (its site, or the region's first place before the first site)
//! chart     h(φ) = (1, cos 2πφ, sin 2πφ, cos 4πφ, sin 4πφ, cos 6πφ, …)   `harmonics` of them, each the field's turn at a declared width
//! restrict  x¹_j = A [m_0(j), …, m_(H−1)(j)] + b_A,   m_k(j) = release(Σ_(t∈e_j) h_k(φ_t) r̂(x_t), 30)
//! clock     τ¹_j = (S_(a_j) − S_(a_0))/σ,  κ¹_j = τ¹_j − τ¹_(j−1)        every turned head of the level on that one clock
//! prolong   x_t += release(Σ_k h_k(φ_t) v_k(j), 30),   v(j) = B r̂(x¹_j) + b_B        founded with B = 0, b_B = 0
//! ```
//!
//! An epoch is definite where every one of its places is, and keyed where any is. The cut, the phases and the clock are data: a carry
//! has no first-order return, so nothing returns to the news. The material is the fine field's, the level's field's and the glue (`A`,
//! `b_A`, `B`, `b_B`), in that order, one covector over all three ([`Constitution::material_len`], [`Constitution::families_all`]). Founded as a
//! growth in scale ([`Constitution::scaled_up`]): `B` and `b_B` open at zero, so the level reads every face of the field it was founded on.
//! With equal news a section a place and six harmonics, the chart is the discrete Fourier chart of six places: the packets of November
//! 3 (retired with this law) are its plain case.

use super::*;

/// The level's field above a field ([`Constitution::scaled_up`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Scale {
    /// The harmonics of the news phase the glue charts (`h_0 = 1`, then a cosine and a sine a whole turn, the last a cosine where
    /// the count is even).
    pub harmonics: usize,
    /// The fine ticks read before the restriction, `0 < split < K`.
    pub split: usize,
    /// The level's field.
    pub coarse: Constitution,
    /// `A` (`D₁ × H D₀`, an epoch's harmonics of its places' reads) and `b_A` (`D₁`), then `B` (`H D₀ × D₁`) and `b_B` (`H D₀`, a bias
    /// a harmonic); matrices on `2^(−24)`, biases on the faces' `2^(−16)`.
    pub glue: Vec<i32>,
    /// [definition; the lead, November 23, the level's design record of November 17 §3 and §4 item 2; `agent-inferred`] **The level's
    /// receipt at its own grain**: where set, on a passage read by two streams each open place that reads an epoch has its prolonged row
    /// alone (the level's state through `B⁻`, with no fine tick after it) read through the opening's reader and compared with the
    /// written symbol there; its covector returns through `B⁻`, the level's ticks and the restriction only, the reader taking none (a part
    /// trained by its own comparison, the objects' receipt law: every receiver has its own). Written as the word `receipt` after the
    /// level's two counts, only where set. Why: one comparison at the fine face gives the level no slope (the design record §9: nothing
    /// linear in the units relieves the fine comparison at the level's locus), and at a word's first letter her state holds the word two
    /// before at 24 thousandths (the play record of November 23, §6).
    pub receipt: bool,
    /// [definition; the lead, November 26, the receipt record of November 23 §5 and the record of the class hairs §10] **The receipt's
    /// pull kept inside the level**: where set beside [`Scale::receipt`], the reverse runs two streams through the level. The places'
    /// covector alone runs the whole route and returns into the fine states before the prolongation, as it does with no receipt; the
    /// receipt's covector alone runs `B⁻`, the level's ticks and the restriction's material (`A`, `b_A`) and stops there, so it changes the
    /// level's own material and never the fine states it reads. Written as the word `inside` after `receipt`, only where set. Why: on
    /// W101r the receipt joined to the places' covector ran back through the restriction's adjoint into the fine states, and every
    /// register's code rose by about the same amount (+0.0355 nats a place over 140,564 places) while the level's face fell from 21.7 to
    /// 2.96 nats a place.
    pub inside: bool,
    /// [definition; the formal thread, November 27 03:28 UTC, the record of the class hairs §14; the build the lead's] **The level's
    /// unit is its epoch's strand face**: where set, the restriction sums each known site's symbol word
    /// `E(u_t)` (its encoding row read as a ratio to its own power, as a read is) on the fine field's rings' phases counted from the
    /// epoch's site, `m_k(j) = Σ_(t ∈ e_j) ρ_k(t − s_j) r̂(E(u_t))` with `ρ = (1, the turn back on each ring of the fine field's periods,
    /// cos and sin, the period 2 by its cosine)` to the level's `H` terms ([`strand_face_terms`]), in place of the six harmonics of the
    /// news phase on her reads. The news still decides where a unit ends, and the prolongation still reads it at each place's news phase.
    /// The restriction's covector stops at its own material (`A`, `b_A`): the encoding is the fine field's boundary chart, read as data
    /// by the level. Written as the word `strand` after the level's counts, only where set. Why: on W132i's end the built restriction
    /// held the bytes at an epoch's first eight places at 0.13 to 0.33 and its own moment at 0.25 to 0.55, where `E` on the rings held
    /// places 1 to 6 at 0.79 to 0.94 (`tools/level_unit_ruler.py`); and on G-L5 a second comparison through the shared fine field cost
    /// every register.
    pub strand: bool,
    /// [definition; the formal thread, November 27 08:51 UTC, its law of the slow store; the lead's build] **The level's slow store**: the
    /// periods `P` (in sections of news on the level's clock `τ¹`) of a bank of rings beside the level's state, each charged once by every
    /// closed epoch's restricted state before the level's ticks, `m_P(j) = Σ_(i ≤ j) e^(−2π γ_P (τ_j − τ_i)/P) e^(−2πi (τ_j − τ_i)/P) x¹_i`
    /// (the strand face one level up: the epochs are the level's symbols), each ring's fade `γ_P = 2^(ℓ_P)` e-folds a radian held as state
    /// beside it ([`Scale::bank_offsets`]; one e-fold a turn is `ℓ = log₂ 1/2π`), so its only loss is its own fade and its reach is built
    /// in. The prolongation reads it through its own block `B_bank` (`H D₀ × 2 R D₁`, founded at zero) at each place's news phase, beside
    /// `B⁻`'s read of the level's state; its covector returns through the bank's reverse into the restricted state's and the restriction's
    /// material; the fades take none (held). Written as the word `bank` and the periods, comma-joined, last on the level's line, only where
    /// set. Why: on W133s's end the level after its ticks held the third byte of the epoch 4 and 8 back at 0.020 and 0.010, and such a bank,
    /// built on the host and untrained, at 0.147 and 0.082 (`tools/level_back_ruler.py`).
    pub bank: Vec<u32>,
    /// [definition; the review of November 27, its build step 1; the lead's build] **The level's founded units** ([`units::Units`]):
    /// where set and charged, the level's cut is its rise store's peaks (her mean news after the runs ending at each place, a property
    /// of the runs' types), so a recurring span is cut alike at every meeting, and its units are founded between those ends; charged and
    /// founded at a crossing (`found-units`), never stepped. Written as its own lines after the glue, only where set. Why: on November 27
    /// her epochs cut a word met again alike in 0.559 of its meetings, as her news moves the landmarks (the record of the class hairs §24);
    /// the store's peaks cut it alike in 0.948 (the record of November 28 §8).
    pub units: Option<super::units::Units>,
    /// [definition; the lead, November 24, the record of the evening of November 23 §7; the formal thread's reading of the join,
    /// `agent-inferred`] **The level's own lane**: where set, the fine field's last face lane is the level's. The prolongation writes it
    /// alone (`B⁻`'s and `b_B⁻`'s rows of every other coordinate are held at zero) and nothing else writes it (the encodings' and the strand
    /// rows' columns into it, the current's, the pair contact's and the triads' returns into it, the moment's chart into it and their
    /// biases, all held at zero: [`Constitution::level_lane_held`]), so every reader reads the handed row as a ratio to its own power,
    /// a partition with its own unit translated at the readers' charts, never leading zeros under the state it would join. Why: on W101's
    /// and W101r's means the row stood at 0.08 and 0.03 of the state's power at the open places, and what it held of the epochs before
    /// (0.07 and 0.16) stood at 0.03 and 0.02 once joined (the precision law's clause of November 21). Written as the word `lane` after
    /// the level's counts (and `receipt`), only where set.
    pub lane: bool,
}

impl Scale {
    /// The glue's offsets of `A`, `b_A`, `B` and `b_B`, and its length, over a fine field of `fine_width` (a realization's
    /// read of [`Scale::glue`]).
    pub fn glue_offsets(&self, fine_width: usize) -> (usize, usize, usize, usize, usize) {
        glue_layout(self.harmonics, fine_width, self.coarse.declaration.width)
    }

    /// [definition; the lead, November 18, the record of the two streams §11] **The block a one-sided stream reads the level through**:
    /// `B⁻` (`H D₀ × D₁`) and `b_B⁻` (`H D₀`) after the law's glue, where the level carries them ([`Constitution::level_before`]): their
    /// offsets and the glue's whole length. A place of a passage read by two streams takes the epoch before its own through them
    /// ([`Constitution::scale_forward_before`]). `None` where the glue is the law's alone.
    pub fn before_offsets(&self, fine_width: usize) -> Option<(usize, usize, usize)> {
        let (_, _, b, bb, len) = self.glue_offsets(fine_width);
        (self.glue.len() == len + (len - b) + self.bank_len(fine_width)).then_some((len, len + (bb - b), len + (len - b)))
    }

    /// The slow store's offsets laid after the one-sided block whatever the glue's length (for the founding that lays them).
    pub(crate) fn bank_offsets_unchecked(&self, fine_width: usize) -> (usize, usize, usize) {
        let (_, _, b, _, len) = self.glue_offsets(fine_width);
        let end = len + (len - b);
        let fades = end + self.harmonics * fine_width * 2 * self.bank.len() * self.coarse.declaration.width;
        (end, fades, fades + self.bank.len())
    }

    /// The length of the slow store's block in the glue ([`Scale::bank`]): `B_bank` and the rings' fades, none where the level holds no bank.
    pub fn bank_len(&self, fine_width: usize) -> usize {
        glue_bank_len(self.harmonics, fine_width, self.coarse.declaration.width, self.bank.len())
    }

    /// [definition; the lead, November 27] **The slow store's block** ([`Scale::bank`]): `B_bank` (`H D₀ × 2 R D₁`) and the rings' fades
    /// (`R`, on `2^(−24)`) after the one-sided block: the offsets of `B_bank`, of the fades, and the glue's whole length. `None` where the
    /// level holds no bank (or no one-sided block, which the bank follows).
    pub fn bank_offsets(&self, fine_width: usize) -> Option<(usize, usize, usize)> {
        if self.bank.is_empty() {
            return None;
        }
        let (_, _, end) = self.before_offsets(fine_width)?;
        let fades = end + self.harmonics * fine_width * 2 * self.bank.len() * self.coarse.declaration.width;
        Some((end, fades, fades + self.bank.len()))
    }
}

/// The length of the slow store's block ([`Scale::bank_len`]): `B_bank` and one fade a ring.
pub(crate) fn glue_bank_len(harmonics: usize, fine: usize, coarse: usize, rings: usize) -> usize {
    if rings == 0 {
        0
    } else {
        harmonics * fine * 2 * rings * coarse + rings
    }
}

/// [definition; the formal thread, November 27 08:51 UTC; the lead's build] **The slow store's turn at each epoch** ([`Scale::bank`]): for
/// epoch `j ≥ 1` of a region and each ring of period `P` and fade `ℓ`, `e^(−2π γ Δτ/P) e^(−2πi Δτ/P)` on `2^(−30)` (its real and imaginary
/// parts, `[j][R][2]`), `Δτ = τ_j − τ_(j−1)` on the pace grain, the decay read as the fine field's faded skin reads it ([`skin_of_k`], its
/// denominator `P ln 2 2^24/γ`) and the turn as a ring's phasor; the region's first epoch takes zero, so each region's bank opens empty.
pub fn bank_rotations(field: &Constitution, periods: &[u32], fades: &[i32], tau: &[i64]) -> Result<Vec<i64>> {
    let r = periods.len();
    let ks: Vec<i128> = periods
        .iter()
        .zip(fades)
        .map(|(&p, &ell)| -> Result<i128> {
            let base = skin_denominator(p as usize);
            Ok(if ell == 0 { base } else { div_nearest(base << MATERIAL_BITS, temperature_of(ell, &field.fine)?) })
        })
        .collect::<Result<_>>()?;
    let mut out = vec![0i64; tau.len() * r * 2];
    for j in 1..tau.len() {
        let dt = i128::from(tau[j]) - i128::from(tau[j - 1]);
        for (q, (&p, &k)) in periods.iter().zip(&ks).enumerate() {
            let decay = i128::from(skin_of_k(dt, k, field.pi, &field.exponential));
            let (re, im) = turn_phasor(dt, p as usize, field.pi);
            out[(j * r + q) * 2] = fit64(release(decay * i128::from(re), MOVE_BITS))?;
            out[(j * r + q) * 2 + 1] = fit64(release(-decay * i128::from(im), MOVE_BITS))?;
        }
    }
    Ok(out)
}

/// The slow store's charge ([`Scale::bank`]): `m_q(j) = rot_q(j) ⊗ m_q(j − 1) + x¹_j` over a region's epochs (`x¹` on its grain, the turn
/// released at `2^(−30)`), each epoch's bank `[j][R][re D₁, im D₁]`.
pub(crate) fn bank_scan(rot: &[i64], x1: &[i64], r: usize, d1: usize) -> Result<Vec<i64>> {
    let epochs = x1.len() / d1.max(1);
    let mut out = vec![0i64; epochs * 2 * r * d1];
    for j in 0..epochs {
        for q in 0..r {
            let (rr, ri) = (i128::from(rot[(j * r + q) * 2]), i128::from(rot[(j * r + q) * 2 + 1]));
            for c in 0..d1 {
                let (pre, pim) = if j == 0 { (0, 0) } else { let at = ((j - 1) * r + q) * 2 * d1; (i128::from(out[at + c]), i128::from(out[at + d1 + c])) };
                let at = (j * r + q) * 2 * d1;
                out[at + c] = fit64(release(rr * pre - ri * pim, MOVE_BITS) + i128::from(x1[j * d1 + c]))?;
                out[at + d1 + c] = fit64(release(rr * pim + ri * pre, MOVE_BITS))?;
            }
        }
    }
    Ok(out)
}

/// The reverse of [`bank_scan`]: from each epoch's bank covector `[j][R][re D₁, im D₁]`, `δm_q(j) = δbank_q(j) + rot_q(j + 1)ᵀ δm_q(j + 1)`
/// (released at `2^(−30)`), and the restricted states' covector `δx¹_j = Σ_q Re δm_q(j)`.
pub(crate) fn bank_return(rot: &[i64], dbank: &[i64], r: usize, d1: usize) -> Result<Vec<i64>> {
    let epochs = dbank.len() / (2 * r * d1).max(1);
    let mut dx = vec![0i128; epochs * d1];
    let mut carry = vec![0i128; r * 2 * d1];
    for j in (0..epochs).rev() {
        for q in 0..r {
            let at = (j * r + q) * 2 * d1;
            for c in 0..d1 {
                let (re, im) = (carry[q * 2 * d1 + c] + i128::from(dbank[at + c]), carry[q * 2 * d1 + d1 + c] + i128::from(dbank[at + d1 + c]));
                dx[j * d1 + c] += re;
                // the carry into epoch j − 1 through epoch j's turn, its transpose
                let (rr, ri) = (i128::from(rot[(j * r + q) * 2]), i128::from(rot[(j * r + q) * 2 + 1]));
                carry[q * 2 * d1 + c] = release(rr * re + ri * im, MOVE_BITS);
                carry[q * 2 * d1 + d1 + c] = release(rr * im - ri * re, MOVE_BITS);
            }
        }
    }
    dx.into_iter().map(fit64).collect()
}

/// The length of the block a one-sided stream reads the level through ([`Scale::before_offsets`]): `B`'s and `b_B`'s.
pub(crate) fn glue_before_len(harmonics: usize, fine: usize, coarse: usize) -> usize {
    harmonics * fine * coarse + harmonics * fine
}

/// The glue's offsets: `A`, `b_A`, `B`, `b_B` and the length.
pub(crate) fn glue_len(harmonics: usize, fine: usize, coarse: usize) -> (usize, usize, usize, usize, usize) {
    glue_layout(harmonics, fine, coarse)
}

fn glue_layout(harmonics: usize, fine: usize, coarse: usize) -> (usize, usize, usize, usize, usize) {
    let a = 0;
    let ab = a + harmonics * coarse * fine;
    let b = ab + coarse;
    let bb = b + harmonics * fine * coarse;
    (a, ab, b, bb, bb + harmonics * fine)
}

/// [definition; theory, November 13, the design record §4.9 (`agent-inferred`)] **The level's field's declaration** over a field's `d`:
/// the fine field's with an alphabet of two (a level names no symbol), no triads, no carry circles, no opening of its own, and the ticks
/// the fine field has after its split (`d.ticks / 2` of them, the split [`level_split`]). Its reach is the fine field's: a region's
/// epochs are at most its places.
pub fn level_declaration(d: &Declaration) -> Declaration {
    Declaration { alphabet: 2, triads: 0, carry: 0, opening: false, junction: false, mark: false, loud: false, crossing: false, closed: 0, pump: false, lane_leak: false, friction: false, friction_gate: false, ticks: d.ticks - level_split(d), ..*d }
}

/// The fine ticks before a level's restriction: half the fine field's, at least one.
pub fn level_split(d: &Declaration) -> usize {
    (d.ticks / 2).max(1)
}

/// The harmonics a level founded now charts (the design record §4.9: the packets' six, the discrete Fourier chart of six equal places
/// in real form; how many an epoch's interior needs is read on a state once epochs are cut).
pub const LEVEL_HARMONICS: usize = 6;

/// [definition; theory, November 13, the design record §4.6 and §4.9] **The level's section**: the flat face's code over `alphabet`
/// classes, on the code's grain (`2^(−20)` bits), the news of one place nothing predicts, so that under a flat face every place carries a
/// section and is a site (the founding is the identity).
pub fn level_section(alphabet: usize) -> i64 {
    face_code(1, alphabet.max(2) as u128)
}

/// [definition; theory, November 13, the record of the landmarks §5] **Each place's isolation** `ρ_t` over a region's news `c`: the
/// news to the nearest greater place on either side (`u ≻ t` where `c_u > c_t`, or `c_u = c_t` and `u < t`), `None` where no greater place
/// stands on either side. Two nearest-greater reads, one each way, on integer sums.
pub fn level_isolation(news: &[i64]) -> Vec<Option<i128>> {
    let n = news.len();
    let mut sum = vec![0i128; n + 1];
    for (t, &c) in news.iter().enumerate() {
        sum[t + 1] = sum[t] + c as i128;
    }
    // `S_t` is `sum[t + 1]`: the news up to and with place `t`.
    let s = |t: usize| sum[t + 1];
    let mut left: Vec<Option<usize>> = vec![None; n];
    let mut stack: Vec<usize> = Vec::new();
    for t in 0..n {
        // The last earlier place with news at least `c_t`.
        while let Some(&u) = stack.last() {
            if news[u] >= news[t] {
                break;
            }
            stack.pop();
        }
        left[t] = stack.last().copied();
        stack.push(t);
    }
    let mut right: Vec<Option<usize>> = vec![None; n];
    stack.clear();
    for t in (0..n).rev() {
        // The first later place with news greater than `c_t`.
        while let Some(&u) = stack.last() {
            if news[u] > news[t] {
                break;
            }
            stack.pop();
        }
        right[t] = stack.last().copied();
        stack.push(t);
    }
    (0..n)
        .map(|t| {
            let l = left[t].map(|u| s(t) - s(u));
            let r = right[t].map(|u| s(u) - s(t));
            match (l, r) {
                (Some(a), Some(b)) => Some(a.min(b)),
                (a, b) => a.or(b),
            }
        })
        .collect()
}

/// [definition; theory, November 13, the design record §4.2 and §4.9] **The anchors of a region's epochs**: its sites (`ρ_t ≥ σ`, a
/// place with no greater place on either side among them), each leading its epoch, after the region's first place where that is no site
/// (the leading epoch). Increasing, the first `0`; empty for an empty region.
pub fn level_anchors(news: &[i64], section: i64) -> Vec<usize> {
    if news.is_empty() {
        return Vec::new();
    }
    let rho = level_isolation(news);
    let mut out = vec![0usize];
    out.extend((1..news.len()).filter(|&t| rho[t].is_none_or(|r| r >= section as i128)));
    out
}

/// [measurement; the lead, November 18, the record of the two streams §10] **The anchors a one-sided stream can name**: a place is a
/// site where no earlier place within a section of news carries news at least its own (the left half of [`level_isolation`]; what
/// stands after a place has not arrived). Increasing, the first `0`. A ruler's cut ([`Constitution::ruler_level`] at `4`).
pub fn level_anchors_before(news: &[i64], section: i64) -> Vec<usize> {
    if news.is_empty() {
        return Vec::new();
    }
    let mut sum = vec![0i128; news.len() + 1];
    for (t, &c) in news.iter().enumerate() {
        sum[t + 1] = sum[t] + c as i128;
    }
    let mut out = vec![0usize];
    let mut stack: Vec<usize> = Vec::new();
    for t in 0..news.len() {
        while let Some(&u) = stack.last() {
            if news[u] >= news[t] {
                break;
            }
            stack.pop();
        }
        let left = stack.last().map(|&u| sum[t + 1] - sum[u + 1]);
        stack.push(t);
        if t > 0 && left.is_none_or(|r| r >= section as i128) {
            out.push(t);
        }
    }
    out
}

/// A region's cut for the level: its epochs' anchors, each place's epoch, each place's harmonics `[t][H]` on `2^(−30)` and the level's
/// clock on its epochs.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct LevelCut {
    pub anchors: Vec<usize>,
    pub epoch: Vec<usize>,
    pub harmonics: Vec<i64>,
    /// `τ¹_j` on `2^(−24)`: the news from the first epoch's anchor to epoch `j`'s, in sections.
    pub tau: Vec<i64>,
}

/// [definition; theory, November 13, the design record §4.5 and §4.9] **A region's cut** from its news: the anchors, each place's phase
/// `φ_t = (S_t − S_(a_j))/σ` on the pace grain (`2^(−24)`) and its `harmonics` on the turn's grain (`2^(−30)`, the field's turn on a ring
/// of one turn at `k φ_t`), and the level's clock `τ¹_j = (S_(a_j) − S_(a_0))/σ` on the pace grain, each a nearest quotient of the news's
/// integer sums by the section (released there, at the pace grain).
pub fn level_cut(news: &[i64], section: i64, harmonics: usize, pi: i128) -> Result<LevelCut> {
    level_cut_sided(news, section, harmonics, pi, false)
}

/// [`level_cut`], or with `before` the cut a one-sided stream can name ([`level_anchors_before`]).
pub fn level_cut_sided(news: &[i64], section: i64, harmonics: usize, pi: i128, before: bool) -> Result<LevelCut> {
    level_cut_units(news, None, section, harmonics, pi, before)
}

/// [definition; the lead, November 27, the review's build step 1] [`level_cut_sided`] with the level's founded units
/// ([`super::units::Units::anchors`]): where a run of `classes` is a founded unit it is held whole, closed at its end, read from the places
/// before each anchor. `units` names the store, the region's classes and the alphabet.
pub fn level_cut_units(news: &[i64], units: Option<(&super::units::Units, &[usize], usize)>, section: i64, harmonics: usize, pi: i128, before: bool) -> Result<LevelCut> {
    if section <= 0 || harmonics == 0 {
        return refuse("a level's cut needs a positive section and a harmonic");
    }
    let anchors = if before { level_anchors_before(news, section) } else { level_anchors(news, section) };
    let anchors = match units {
        Some((u, classes, alphabet)) if classes.len() == news.len() => u.read_anchors(&anchors, classes, alphabet, before),
        Some(_) => return refuse("a level's founded units read over classes that are not the news's places"),
        None => anchors,
    };
    let n = news.len();
    let mut sum = vec![0i128; n + 1];
    for (t, &c) in news.iter().enumerate() {
        if c < 0 {
            return refuse("a level's news below zero");
        }
        sum[t + 1] = sum[t] + c as i128;
    }
    let pace = |news: i128| div_nearest(news << PACE_BITS, section as i128);
    let mut epoch = vec![0usize; n];
    for (j, &a) in anchors.iter().enumerate() {
        let end = anchors.get(j + 1).copied().unwrap_or(n);
        epoch[a..end].fill(j);
    }
    let mut out = vec![0i64; n * harmonics];
    for t in 0..n {
        let phi = pace(sum[t + 1] - sum[anchors[epoch[t]] + 1]);
        phase_harmonics(phi, &mut out[t * harmonics..(t + 1) * harmonics], pi);
    }
    let base = anchors.first().map_or(0, |&a| sum[a + 1]);
    let tau = anchors.iter().map(|&a| fit64(pace(sum[a + 1] - base))).collect::<Result<_>>()?;
    Ok(LevelCut { anchors, epoch, harmonics: out, tau })
}

/// A strand's cut for the level ([`strand_level_cut`]): the known stream's cut, each open place's harmonics `[n][H]` on `2^(−30)`, and
/// the epoch each of the `2n` sites reads (the known sites, then the open places; `None` where a site reads none).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct StrandCut {
    pub cut: LevelCut,
    pub open_harmonics: Vec<i64>,
    pub source: Vec<Option<usize>>,
}

/// [definition; the lead, November 18, the record of the two streams §11] **A strand's cut** from its places' news
/// ([`Constitution::scale_forward_before`]): the known stream cut where a one-sided stream can name a site ([`level_anchors_before`]);
/// a known site of epoch `j` reads epoch `j − 1`; the open place at place `t ≥ 1` stands in the epoch of the place before it, at the
/// phase `(S_(t−1) + ĉ_t − S_(a))/σ` its expected news `ĉ_t` (`open_news`) carries it to, and reads the same epoch before. Data: one
/// function for the host's law and a card's batch.
pub fn strand_level_cut(known_news: &[i64], open_news: &[i64], section: i64, harmonics: usize, pi: i128) -> Result<StrandCut> {
    strand_level_cut_units(known_news, open_news, None, section, harmonics, pi)
}

/// [`strand_level_cut`] with the level's founded units ([`level_cut_units`]) over the known stream's classes.
pub fn strand_level_cut_units(known_news: &[i64], open_news: &[i64], units: Option<(&super::units::Units, &[usize], usize)>, section: i64, harmonics: usize, pi: i128) -> Result<StrandCut> {
    let n = known_news.len();
    if open_news.len() != n {
        return refuse("a strand's cut needs each place's news and its expected news");
    }
    let cut = level_cut_units(known_news, units, section, harmonics, pi, true)?;
    let mut sum = vec![0i128; n + 1];
    for (t, &c) in known_news.iter().enumerate() {
        sum[t + 1] = sum[t] + c as i128;
    }
    let mut open_harmonics = vec![0i64; n * harmonics];
    let mut source: Vec<Option<usize>> = (0..n).map(|t| cut.epoch[t].checked_sub(1)).collect();
    if n > 0 {
        source.push(None);
    }
    for t in 1..n {
        let e = cut.epoch[t - 1];
        let phi = div_nearest((sum[t] + open_news[t].max(0) as i128 - sum[cut.anchors[e] + 1]) << PACE_BITS, section as i128);
        phase_harmonics(phi, &mut open_harmonics[t * harmonics..(t + 1) * harmonics], pi);
        source.push(e.checked_sub(1));
    }
    Ok(StrandCut { cut, open_harmonics, source })
}

/// The harmonics of a news phase `phi` (on the pace grain), on the turn's grain: `1`, then a cosine and a sine a whole turn.
fn phase_harmonics(phi: i128, h: &mut [i64], pi: i128) {
    h[0] = 1i64 << MOVE_BITS;
    for (i, slot) in h.iter_mut().enumerate().skip(1) {
        let k = i.div_ceil(2) as i128;
        let (re, im) = turn_phasor(k * phi, 1, pi);
        *slot = if i % 2 == 1 { re } else { im };
    }
}

/// What [`Constitution::level_trace`] reads of a region's level.
#[derive(Clone, Debug)]
pub struct LevelTrace {
    pub news: Vec<i64>,
    pub anchors: Vec<usize>,
    pub coarse_read: Vec<i32>,
    /// The links of the level's own equation, where [`Constitution::level_links`] read them (empty from [`Constitution::level_trace`]):
    /// each place's harmonics of its news phase (`[t][H]` on `2^(−30)`), each place's read at the split (`[t][D₀]` on `2^(−16)`), each
    /// epoch's moment (`[j][H D₀]`, the chart's sums on the read's grain), each epoch's restricted state before the level's ticks
    /// (`[j][D₁]` on `2^(−16)`), each place's prolonged row (`[t][D₀]` on `2^(−16)`), and the covector the reverse holds at the level's
    /// locus, of the state the prolongation wrote (`[t][D₀]` on the covector's grain `2^(−24)`).
    pub phase: Vec<i64>,
    pub read: Vec<i32>,
    pub moment: Vec<i64>,
    pub restricted: Vec<i64>,
    pub prolonged: Vec<i64>,
    pub covector: Vec<i64>,
}

/// What a level's forward keeps for its reverse.
#[derive(Clone, Debug, Default)]
pub(crate) struct ScalePass {
    /// Each fine place's read at the split `[t][D₀]`, with its scale.
    read: Vec<i32>,
    scale: Vec<i128>,
    /// The region's cut, and each epoch's restricted harmonics `[j][H D₀]`.
    cut: LevelCut,
    restricted: Vec<i64>,
    /// The level's ticks, its read after the last `[j][D₁]` with its scale, and which epochs are definite.
    ticks: Vec<TickCell>,
    coarse_read: Vec<i32>,
    coarse_scale: Vec<i128>,
    definite: Vec<bool>,
    paces: Paces,
    /// Where the forward keeps for a reading: each epoch's restricted state before the level's ticks `[j][D₁]`, and each place's
    /// prolonged row `[t][D₀]`.
    before_ticks: Vec<i64>,
    prolonged: Vec<i64>,
    /// A strand's level ([`Constitution::scale_forward_before`]): each open place's harmonics `[t][H]` and the epoch each known site
    /// and each open place reads (`[2n]`, `None` where it reads none).
    open_harmonics: Vec<i64>,
    source: Vec<Option<usize>>,
    /// The level's receipt ([`Scale::receipt`]): each open place that reads an epoch, its site, the opening's read of its prolonged row
    /// alone and the written symbol it is compared with.
    receipt: Vec<(usize, crate::navigator::BlankRead, usize)>,
    /// [measurement; the lead, November 27] Where the forward keeps for a reading under the receipt: each compared open place's
    /// prolonged row (`[r][D₀]`, in the receipt's order), for the level's standing state, the mean of its rows.
    receipt_rows: Vec<i64>,
    /// The slow store ([`Scale::bank`]): each epoch's turn `[j][R][2]`, and its bank's read `[j][2 R D₁]` with each lane's scale `[j][2 R]`.
    bank_rot: Vec<i64>,
    bank_read: Vec<i32>,
    bank_scale: Vec<i128>,
}

impl ScalePass {
    /// The level's receipt's code ([`Scale::receipt`]): the summed code of the written symbols at the prolonged rows' faces, on the
    /// codes' grain, and the count of places it compared (a reading: the tests read it against the covector).
    #[cfg(test)]
    pub(crate) fn receipt_code(&self) -> (i64, usize) {
        (self.receipt.iter().map(|(_, read, c)| read.face.code(*c)).sum(), self.receipt.len())
    }
}

impl ScalePass {
    /// The known stream's anchors and the epoch each of a strand's `2n` sites reads (the known sites, then the open places), as
    /// [`strand_level_cut`] formed them (a reading for a ruler: [`Constitution::strand_cut_read`]).
    pub(crate) fn strand_cut(&self) -> (&[usize], &[Option<usize>]) {
        (&self.cut.anchors, &self.source)
    }

    /// [measurement; the lead, November 26, the level's face before a second level] Each compared open place of the receipt
    /// ([`Scale::receipt`]) with its code at the prolonged row's face alone (the level through its own decoder and the receiver's face,
    /// no fine tick after it), on the codes' grain: a reading for a ruler ([`Constitution::strand_level_face`]).
    /// The compared open places' prolonged rows (`[r][D₀]`, the receipt's order), kept where the forward kept.
    pub(crate) fn receipt_rows(&self) -> &[i64] {
        &self.receipt_rows
    }

    pub(crate) fn receipt_codes(&self) -> Vec<(usize, i64)> {
        self.receipt.iter().map(|(t, read, c)| (*t, read.face.code(*c))).collect()
    }

    /// Each epoch's restricted state before the level's ticks (`[j][D₁]`, kept where the forward keeps) and its read after the last
    /// (`[j][D₁]`, the lane chart on `2^(−16)`): two links of the level's equation, for a ruler ([`Constitution::strand_level_links`]).
    pub(crate) fn level_links(&self) -> (&[i64], &[i32]) {
        (&self.before_ticks, &self.coarse_read)
    }

    /// [measurement; the lead, November 27, the record of the class hairs §13] What the restriction reads and what it sums: each known
    /// site's read at the split (`[n][D₀]` on `2^(−16)`, the lane chart's ratio), each epoch's harmonics of its places' reads
    /// (`[j][H D₀]`, the chart's sums), each known site's harmonics of its news phase (`[n][H]` on `2^(−30)`) and the level's clock at
    /// each epoch (`τ¹_j`, on the pace grain), for a ruler of what the level's unit keeps of its epoch, link by link.
    pub(crate) fn level_moment(&self) -> (&[i32], &[i64], &[i64], &[i64], &[i64]) {
        (&self.read, &self.restricted, &self.cut.harmonics, &self.cut.tau, &self.open_harmonics)
    }

    /// The level's ticks kept for the reverse.
    #[cfg(test)]
    pub(super) fn ticks(&self) -> &[TickCell] {
        &self.ticks
    }

    /// The region's cut the level read.
    #[cfg(test)]
    pub(super) fn cut(&self) -> &LevelCut {
        &self.cut
    }

    /// A strand's open places' harmonics ([`Constitution::scale_forward_before`]).
    #[cfg(test)]
    pub(super) fn open_harmonics(&self) -> &[i64] {
        &self.open_harmonics
    }
}

/// [definition; theory, November 13, the design record §4.3 and §4.9] **The level's clock** on a region's epochs for every turned head:
/// `τ¹` the news between the anchors in sections, `κ¹_j = τ¹_j − τ¹_(j−1)` (the first epoch's rate one), its variation the same (the
/// rates are not negative), plain where every rate is one exactly.
fn level_paces(d: &Declaration, cut: &LevelCut) -> Result<Paces> {
    let one = 1i64 << PACE_BITS;
    let kappa: Vec<i64> = (0..cut.tau.len()).map(|j| if j == 0 { one } else { cut.tau[j] - cut.tau[j - 1] }).collect();
    let plain = kappa.iter().all(|&k| k == one);
    let mut out = Paces { row: vec![None; d.heads], ..Default::default() };
    for h in (0..d.heads).filter(|&h| d.carries_moment(h)) {
        out.row[h] = Some(out.kappa.len());
        out.kappa.push(kappa.clone());
        out.tau.push(cut.tau.clone());
        out.sigma.push(cut.tau.clone());
        out.plain.push(plain);
    }
    Ok(out)
}

/// `out[j][k D₀ + c] += Σ_(t∈e_j) h_k(φ_t) rows[t][c]`, released by 30 once an entry (the chart's sums over an epoch's places).
fn charted<V: Copy + Into<i64>>(cut: &LevelCut, h: usize, rows: &[V], width: usize) -> Result<Vec<i64>> {
    let epochs = cut.anchors.len();
    let mut acc = vec![0i128; epochs * h * width];
    for (t, &j) in cut.epoch.iter().enumerate() {
        let ht = &cut.harmonics[t * h..(t + 1) * h];
        let row = &rows[t * width..(t + 1) * width];
        let slot = &mut acc[j * h * width..(j + 1) * h * width];
        for (k, &hk) in ht.iter().enumerate() {
            for (c, &v) in row.iter().enumerate() {
                slot[k * width + c] += hk as i128 * v.into() as i128;
            }
        }
    }
    acc.into_iter().map(|v| fit64(release(v, MOVE_BITS))).collect()
}

/// [definition; the formal thread, November 27 03:28 UTC; the lead's build] **The strand face's terms** at each known site of a cut
/// ([`Scale::strand`]): `ρ(t − s_j)` on the turn's grain (`2^(−30)`), the constant term first, then for each distinct ring period `P` of
/// the fine field's turned slots ([`crate::navigator::ring_periods`], ascending) the turn back by `t − s_j` places, `cos 2π(t − s_j)/P`
/// and `−sin 2π(t − s_j)/P` (the period 2 by its cosine alone, its sine being zero), until the level's `h` terms are filled. Positions
/// inside an epoch are told apart up to the product of the periods the terms reach.
pub fn strand_face_terms(field: &Constitution, cut: &LevelCut, h: usize) -> Vec<i64> {
    let d = &field.declaration;
    let mut periods = crate::navigator::ring_periods(d.turned_slots(), d.reach);
    periods.dedup();
    let n = cut.epoch.len();
    let mut out = vec![0i64; n * h];
    for t in 0..n {
        let dist = t - cut.anchors[cut.epoch[t]];
        let slot = &mut out[t * h..(t + 1) * h];
        slot[0] = 1i64 << MOVE_BITS;
        let mut k = 1;
        for &p in &periods {
            if k >= h {
                break;
            }
            let (re, im) = crate::navigator::ring_phasor(dist % p, p, field.pi);
            slot[k] = re;
            k += 1;
            if p > 2 && k < h {
                slot[k] = -im;
                k += 1;
            }
        }
    }
    out
}

/// The strand face's rows ([`Scale::strand`]): each symbol's encoding row `E(u)` read as a ratio to its own power through the lane chart
/// (`[n][D₀]` on the read's grain, as a place's read is), for the classes of a strand's known sites.
pub fn strand_face_reads(field: &Constitution, classes: &[usize]) -> Result<Vec<i32>> {
    let (dw, enc) = (field.declaration.width, field.layout.enc);
    let (mut read, mut scale) = (Vec::with_capacity(classes.len() * dw), Vec::new());
    for &c in classes {
        let row: Vec<i64> = field.theta[enc + c * dw..enc + (c + 1) * dw].iter().map(|&v| i64::from(v)).collect();
        lane_chart(&row, field.declaration.lanes, &mut read, &mut scale)?;
    }
    Ok(read)
}

/// Place `t`'s row from its epoch's harmonic blocks `v` (`[H][width]`): `release(Σ_k h_k(φ_t) v_k, 30)`.
fn uncharted(ht: &[i64], v: &[i64], width: usize, out: &mut [i64]) -> Result<()> {
    for (c, slot) in out.iter_mut().enumerate() {
        let sum: i128 = ht.iter().enumerate().map(|(k, &hk)| hk as i128 * v[k * width + c] as i128).sum();
        *slot = fit64(release(sum, MOVE_BITS))?;
    }
    Ok(())
}

impl Constitution {
    /// The material's length: the field's, and with a level the level's field's and the glue's.
    pub fn material_len(&self) -> usize {
        self.theta.len() + self.scale.as_ref().map_or(0, |s| s.coarse.theta.len() + s.glue.len())
    }

    /// Every family of the material, `(start, len, grain)` over [`Constitution::material_len`].
    pub fn families_all(&self) -> Vec<(usize, usize, u32)> {
        let mut out = self.layout.families.clone();
        if let Some(s) = &self.scale {
            let base = self.theta.len();
            out.extend(s.coarse.layout.families.iter().map(|&(start, len, grain)| (base + start, len, grain)));
            let at = base + s.coarse.theta.len();
            let (d0, d1) = (self.declaration.width, s.coarse.declaration.width);
            let (a, ab, b, bb, _) = glue_layout(s.harmonics, d0, d1);
            out.extend([(at + a, ab - a, MATERIAL_BITS), (at + ab, d1, FACE_BITS), (at + b, bb - b, MATERIAL_BITS), (at + bb, s.harmonics * d0, FACE_BITS)]);
            if let Some((b2, bb2, end)) = s.before_offsets(d0) {
                out.extend([(at + b2, bb2 - b2, MATERIAL_BITS), (at + bb2, end - bb2, FACE_BITS)]);
            }
            if let Some((bk, bf, end)) = s.bank_offsets(d0) {
                out.extend([(at + bk, bf - bk, MATERIAL_BITS), (at + bf, end - bf, MATERIAL_BITS)]);
            }
        }
        out
    }

    /// [definition; the lead, November 21, E5 of #1088] **Each family's read part by the lattice rule**: for a receiver whose code tolerance is
    /// `ε = 2^(−eps_bits)` nats at every symbol, the grain `L_R = 2/ε` (a face whose exponents are within `B` codes every symbol within `2B`,
    /// Lean `face_tail_moves_code`) and each family's places `L = ⌈log₂(2 L_R X)⌉` ([`lattice_exponent`]) by its fan-in `X`
    /// ([`Loci::fan_in`]; the level's families by the level's layout; the glue's maps by their input widths, their biases by one), one a family
    /// of [`Constitution::families_all`].
    pub fn lattice_by_rule(&self, eps_bits: u32) -> Vec<u32> {
        let grain = 1u128 << (eps_bits + 1);
        self.fan_ins().into_iter().map(|x| lattice_exponent(grain, u128::from(x))).collect()
    }

    /// [definition; the lead, November 22, the second precision pass (G-R3)] **Each family's fan-in**, one a family of
    /// [`Constitution::families_all`]: [`Loci::fan_in`] for the fine and the level's families, the glue's maps by their input widths and their
    /// biases by one. A map's entries stand in rows of its fan-in, one row an output ([`crate::adjoint::affine`]'s `cols`).
    pub fn fan_ins(&self) -> Vec<u64> {
        let mut out: Vec<u64> = self.layout.families.iter().map(|&(start, _, _)| self.layout.fan_in(&self.declaration, start)).collect();
        if let Some(s) = &self.scale {
            out.extend(s.coarse.layout.families.iter().map(|&(start, _, _)| s.coarse.layout.fan_in(&s.coarse.declaration, start)));
            let (d0, d1) = (self.declaration.width as u64, s.coarse.declaration.width as u64);
            out.extend([s.harmonics as u64 * d0, 1, d1, 1]);
            if s.before_offsets(self.declaration.width).is_some() {
                out.extend([d1, 1]);
            }
            if s.bank_offsets(self.declaration.width).is_some() {
                out.extend([2 * s.bank.len() as u64 * d1, 1]);
            }
        }
        out
    }

    /// [definition; the lead, November 18, the record of the two streams §11] **The level opened to one-sided streams**: this tower with
    /// the block `B⁻`, `b_B⁻` after its glue, at zero, so every face reads as before (a passage read by two streams then takes the epoch
    /// before each place through it, [`Constitution::scale_forward_before`]). Refused without a level or where the level carries it.
    pub fn level_before(&self) -> Result<Self> {
        let Some(s) = self.scale.as_deref() else {
            return refuse("a level opened to one-sided streams on a field without a level");
        };
        if s.before_offsets(self.declaration.width).is_some() || !s.bank.is_empty() {
            return refuse("a level that already carries its one-sided block (or a slow store, which follows it)");
        }
        let mut out = self.clone();
        let extra = glue_before_len(s.harmonics, self.declaration.width, s.coarse.declaration.width);
        if let Some(sc) = out.scale.as_deref_mut() {
            sc.glue.extend(std::iter::repeat_n(0i32, extra));
        }
        Ok(out)
    }

    /// The material entry `i` of [`Constitution::material_len`].
    pub fn material(&self) -> impl Iterator<Item = &i32> {
        let (coarse, glue): (&[i32], &[i32]) = match self.scale.as_deref() {
            Some(s) => (&s.coarse.theta[..], &s.glue[..]),
            None => (&[], &[]),
        };
        self.theta.iter().chain(coarse.iter()).chain(glue.iter())
    }

    /// The material entry `i` of [`Constitution::material_len`], mutable.
    pub fn material_mut(&mut self) -> impl Iterator<Item = &mut i32> {
        let (coarse, glue): (&mut [i32], &mut [i32]) = match self.scale.as_deref_mut() {
            Some(s) => (&mut s.coarse.theta[..], &mut s.glue[..]),
            None => (&mut [], &mut []),
        };
        self.theta.iter_mut().chain(coarse.iter_mut()).chain(glue.iter_mut())
    }

    /// [definition; theory, November 13, the design record §4.4 and §4.9] **The news of every place** of a region, on the code's grain: at
    /// a written place (definite) the code of its class at its opening face, elsewhere the face's expected code `Σ_a p̃_t(a) code_t(a)`
    /// (a nearest quotient of the masses' sum by the total). An open place's class is its comparison's target and is never read here.
    /// Refused on a field without the opening's block.
    pub fn level_news(&self, region: &Region) -> Result<Vec<i64>> {
        let faces = self.opening_faces(region)?;
        faces
            .iter()
            .enumerate()
            .map(|(t, f)| {
                if Self::definite(region, t) {
                    return Ok(f.code(region.classes[t]));
                }
                let sum: i128 = f.masses.iter().map(|&m| m as i128 * face_code(m, f.total) as i128).sum();
                fit64(div_nearest(sum, f.total as i128))
            })
            .collect()
    }

    /// [definition; theory, November 13, the design record §4.9] **Growth in scale**: this field with a level of `harmonics` after `split`
    /// of its ticks, the level's field founded on its own `declaration` from the key stream at `offset`, the restriction's `A` drawn after
    /// it on `±√(3/(H D₀))`, and `b_A`, `B`, `b_B` at zero, so every face reads as before. The level reads the opening's news, so the field
    /// carries the opening's block. Returns the tower and the key bytes read through.
    pub fn scaled_up(&self, harmonics: usize, split: usize, declaration: Declaration, keys: &[u8], offset: usize) -> Result<(Self, usize)> {
        if self.scale.is_some() || harmonics == 0 || split == 0 || split >= self.declaration.ticks || !self.declaration.opening || declaration.opening {
            return refuse("a level needs a field with the opening's block and without a level, a harmonic, and a split inside the ticks; the level's own field has no opening");
        }
        let coarse = Constitution::found(declaration, keys.get(offset..).ok_or(TowerError::Refused("a key file shorter than a level's founding"))?)?;
        let mut at = offset + 4 * declaration.founding_draws();
        let (d0, d1) = (self.declaration.width, declaration.width);
        let (a, ab, _, _, len) = glue_layout(harmonics, d0, d1);
        let mut glue = vec![0i32; len];
        let ((three, _), (_, pd)) = (chart_scale(d0), chart_scale(harmonics * d0));
        for v in &mut glue[a..ab] {
            let word = keys.get(at..at + 4).ok_or(TowerError::Refused("a key file shorter than a level's founding"))?;
            at += 4;
            let k = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) as i128;
            *v = fit32((k * ((three << MATERIAL_BITS) / pd) as i128) >> 31, "a founded value outgrew its 32-bit carrier")?;
        }
        let mut out = self.clone();
        out.scale = Some(Box::new(Scale { units: None, harmonics, split, coarse, glue, receipt: false, inside: false, strand: false, bank: Vec::new(), lane: false }));
        Ok((out, at))
    }

    /// [measurement; the lead, November 17, the record of the dwell §19] **A region's level as its forward left it**, for a ruler on the
    /// host: each place's news ([`Constitution::level_news`]), the epochs' anchors, and each epoch's read after the level's last tick
    /// (`[j][D₁]` on `2^(−16)`, what the prolongation hands back to the epoch's places). `None` on a field without a level. A reading:
    /// the state is the same with it.
    pub fn level_trace(&self, region: &Region) -> Result<Option<LevelTrace>> {
        if self.scale.is_none() {
            return Ok(None);
        }
        let news = self.level_news(region)?;
        let pass = self.pass(region, true)?;
        Ok(pass.tower.map(|t| LevelTrace { news, anchors: t.cut.anchors, coarse_read: t.coarse_read, phase: Vec::new(), read: Vec::new(), moment: Vec::new(), restricted: Vec::new(), prolonged: Vec::new(), covector: Vec::new() }))
    }

    /// [measurement; the lead, November 17, the level's design record §6] **A region's level link by link**, for a ruler on the host:
    /// [`Constitution::level_trace`] with every link of the level's equation as the forward left it (the places' phases and reads at
    /// the split, the epochs' moments, their restricted states before the level's ticks, the prolonged rows) and the covector the
    /// region's reverse holds at the level's locus. `None` on a field without a level. A reading: the state is the same with it.
    pub fn level_links(&self, region: &Region) -> Result<Option<LevelTrace>> {
        if self.scale.is_none() {
            return Ok(None);
        }
        let news = self.level_news(region)?;
        let pass = self.pass(region, true)?;
        let mut g = vec![0i128; self.material_len()];
        let mut covector = Vec::new();
        self.returned_with(region, &pass, &mut g, None, None, None, None, None, None, Some(&mut covector))?;
        Ok(pass.tower.map(|t| LevelTrace { news, anchors: t.cut.anchors, coarse_read: t.coarse_read, phase: t.cut.harmonics, read: t.read, moment: t.restricted, restricted: t.before_ticks, prolonged: t.prolonged, covector }))
    }

    /// The level's forward at the split: the region's cut from its `news`, `x` restricted to the epochs by the news phase, the level's
    /// ticks on its own clock, and the prolongation added back into `x`.
    /// The slow store's forward ([`Scale::bank`]): each epoch's turn from the level's clock, the bank charged by the restricted states `x¹`
    /// (`[j][D₁]`, before the level's ticks), and each epoch's bank read as a ratio to its own power, one lane a ring's part.
    fn bank_forward(&self, s: &Scale, tau: &[i64], x1: &[i64], out: &mut ScalePass) -> Result<()> {
        let Some((_, bf, end)) = s.bank_offsets(self.declaration.width) else { return Ok(()) };
        let (r, d1) = (s.bank.len(), s.coarse.declaration.width);
        out.bank_rot = bank_rotations(self, &s.bank, &s.glue[bf..end], tau)?;
        let bank = bank_scan(&out.bank_rot, x1, r, d1)?;
        for bj in bank.chunks_exact(2 * r * d1) {
            lane_chart(bj, 2 * r, &mut out.bank_read, &mut out.bank_scale)?;
        }
        Ok(())
    }

    /// Epoch `j`'s harmonic blocks from the slow store, `B_bank r̂(bank_j)`, added into `v` (`[H D₀]`); nothing where the level holds no bank.
    fn bank_prolonged(&self, s: &Scale, pass: &ScalePass, reach_k: u64, j: usize, v: &mut [i64]) -> Result<()> {
        let d0 = self.declaration.width;
        let Some((bk, bf, _)) = s.bank_offsets(d0) else { return Ok(()) };
        let w = 2 * s.bank.len() * s.coarse.declaration.width;
        let mut vb = vec![0i64; v.len()];
        affine(&s.glue[bk..bf], reach_k, w, &pass.bank_read[j * w..(j + 1) * w], None, MATERIAL_BITS, MATERIAL_BITS, &mut vb)?;
        for (a, &b) in v.iter_mut().zip(&vb) {
            *a = fit64(*a as i128 + b as i128)?;
        }
        Ok(())
    }

    /// The slow store's reverse ([`Scale::bank`]): from each epoch's covector of its harmonic blocks `δv(j)`, `δB_bank += δv(j) r̂(bank_j)ᵀ`
    /// into the glue's covector `gg`, and the restricted states' covector through `B_bankᵀ`, the lanes' adjoint and the bank's reverse
    /// (`[j][D₁]`, to join `δx¹` before the level's ticks); empty where the level holds no bank. The fades take none (held).
    fn bank_returned(&self, s: &Scale, pass: &ScalePass, douts: &[&[i64]], gg: &mut [i128]) -> Result<Vec<i64>> {
        let d0 = self.declaration.width;
        let Some((bk, bf, _)) = s.bank_offsets(d0) else { return Ok(Vec::new()) };
        let (r, d1) = (s.bank.len(), s.coarse.declaration.width);
        let w = 2 * r * d1;
        let reads: Vec<&[i32]> = pass.bank_read.chunks_exact(w).collect();
        outer_sum(&mut gg[bk..bf], w, douts, &reads)?;
        let reach_k = reach(&s.glue[bk..bf]);
        let mut dbank = vec![0i64; douts.len() * w];
        let mut drb = vec![0i64; w];
        for (j, dout) in douts.iter().enumerate() {
            transposed(&s.glue[bk..bf], reach_k, w, dout, MATERIAL_BITS, &mut drb)?;
            let back = lane_adjoint(reads[j], &pass.bank_scale[j * 2 * r..(j + 1) * 2 * r], &drb)?;
            dbank[j * w..(j + 1) * w].copy_from_slice(&back);
        }
        bank_return(&pass.bank_rot, &dbank, r, d1)
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn scale_forward(&self, s: &Scale, x: &mut [i64], news: &[i64], definite: &[bool], keyed: &[bool], keep: bool, classes: &[usize], unresolved: &[bool]) -> Result<ScalePass> {
        let (d0, d1, h) = (self.declaration.width, s.coarse.declaration.width, s.harmonics);
        let sites = definite.len();
        // [measurement] A ruler's forward ([`Constitution::ruler_level`]): at `4` the cut a one-sided stream can name, the level's ticks
        // one-sided and every place reading the epoch before its own; at `1` to `3` the prolongation's source alone changes.
        let rl = self.ruler_level;
        let cut = level_cut_units(news, s.units.as_ref().map(|u| (u, classes, self.declaration.alphabet)), level_section(self.declaration.alphabet), h, self.pi, rl == 4)?;
        let epochs = cut.anchors.len();
        let (a, ab, b, bb, _) = glue_layout(h, d0, d1);
        let g = &s.glue;
        let mut out = ScalePass::default();
        for xt in x.chunks_exact(d0) {
            lane_chart(xt, self.declaration.lanes, &mut out.read, &mut out.scale)?;
        }
        // The restriction: each epoch's harmonics of its places' reads, through `A`; [`Scale::strand`] on the strand face, each known
        // place's symbol word on the rings, an open place's symbol unwritten and adding nothing.
        out.restricted = if s.strand {
            let ring = LevelCut { harmonics: strand_face_terms(self, &cut, h), ..cut.clone() };
            let shown: Vec<usize> = classes.iter().zip(unresolved).map(|(&c, &u)| if u { 0 } else { c }).collect();
            let mut reads = strand_face_reads(self, &shown)?;
            for t in (0..unresolved.len()).filter(|&t| unresolved[t]) {
                reads[t * d0..(t + 1) * d0].fill(0);
            }
            charted(&ring, h, &reads, d0)?
        } else {
            charted(&cut, h, &out.read, d0)?
        };
        let reach_a = reach(&g[a..ab]);
        let mut x1 = vec![0i64; epochs * d1];
        for j in 0..epochs {
            affine(&g[a..ab], reach_a, h * d0, &out.restricted[j * h * d0..(j + 1) * h * d0], Some(&g[ab..ab + d1]), MATERIAL_BITS, MATERIAL_BITS, &mut x1[j * d1..(j + 1) * d1])?;
        }
        // [`Scale::bank`] The slow store, charged by each epoch's restricted state before the level's ticks.
        self.bank_forward(s, &cut.tau, &x1, &mut out)?;
        // The level's field, on its own clock.
        let span = |j: usize| cut.anchors[j]..cut.anchors.get(j + 1).copied().unwrap_or(sites);
        out.definite = (0..epochs).map(|j| span(j).all(|t| definite[t])).collect();
        let keyed1: Vec<bool> = (0..epochs).map(|j| span(j).any(|t| keyed[t])).collect();
        out.paces = level_paces(&s.coarse.declaration, &cut)?;
        if keep {
            out.before_ticks = x1.clone();
        }
        let moment = vec![0i64; epochs * 2 * s.coarse.declaration.complex()];
        let reaches = s.coarse.reaches();
        for _ in 0..s.coarse.declaration.ticks {
            let mut cell = TickCell::default();
            s.coarse.tick(&mut x1, &out.definite, &keyed1, &out.paces, &moment, &reaches, None, &mut cell, if rl == 4 { crate::contact::Sided::Before { past: false } } else { crate::contact::Sided::Both })?;
            if keep {
                out.ticks.push(cell);
            }
        }
        for xj in x1.chunks_exact(d1) {
            lane_chart(xj, s.coarse.declaration.lanes, &mut out.coarse_read, &mut out.coarse_scale)?;
        }
        // The prolongation: each epoch's harmonic blocks, each place reading them at its own phase.
        let reach_b = reach(&g[b..bb]);
        let mut v = vec![0i64; h * d0];
        let mut row = vec![0i64; d0];
        if keep {
            out.prolonged = vec![0i64; sites * d0];
        }
        // The epoch a place reads: its own, or under a ruler the one before it or none ([`Constitution::ruler_level`]).
        let source = |t: usize, j: usize| match rl {
            1 if !definite[t] => None,
            3 if !definite[t] => j.checked_sub(1),
            2 | 4 => j.checked_sub(1),
            _ => Some(j),
        };
        let reach_k = s.bank_offsets(d0).map_or(0, |(bk, bf, _)| reach(&g[bk..bf]));
        for j in 0..epochs {
            affine(&g[b..bb], reach_b, d1, &out.coarse_read[j * d1..(j + 1) * d1], Some(&g[bb..bb + h * d0]), MATERIAL_BITS, MATERIAL_BITS, &mut v)?;
            self.bank_prolonged(s, &out, reach_k, j, &mut v)?;
            for t in (0..sites).filter(|&t| source(t, cut.epoch[t]) == Some(j)) {
                uncharted(&cut.harmonics[t * h..(t + 1) * h], &v, d0, &mut row)?;
                for (xv, &r) in x[t * d0..(t + 1) * d0].iter_mut().zip(&row) {
                    *xv = fit64(*xv as i128 + r as i128)?;
                }
                if keep {
                    out.prolonged[t * d0..(t + 1) * d0].copy_from_slice(&row);
                }
            }
        }
        out.cut = cut;
        Ok(out)
    }

    /// [definition; the lead, November 24] **The entries the level's own lane holds at zero** ([`Scale::lane`]), as indices of the whole
    /// material (the fine field's, then the level's field's, then the glue, as a section's covector lays them): every writer into the fine
    /// field's last lane but the prolongation (the encodings' `E`, `E₋`, `E₊` columns of the lane, the current's return `out`, the pair
    /// contact's `W`, the triads' `W_T` and the moment's chart `C`, their rows of the lane, and their biases there), and the prolongation's
    /// `B⁻` and `b_B⁻` rows of every coordinate outside the lane. `None` where the level has no lane of its own. Refused where the tick has
    /// a junction's return (a writer this list does not name) or the level no one-sided block.
    pub fn level_lane_held(&self) -> Result<Option<Vec<usize>>> {
        let Some(s) = self.scale.as_deref().filter(|s| s.lane) else { return Ok(None) };
        let d = &self.declaration;
        if d.junction {
            return refuse("the level's own lane on a field whose tick has a junction's return");
        }
        let Some((b2, bb2, _)) = s.before_offsets(d.width) else {
            return refuse("the level's own lane on a level without its one-sided block");
        };
        let (dw, a, m2, f, j2, w) = (d.width, d.alphabet, 2 * d.complex(), d.contacts, 2 * d.triads, d.lane_width());
        let lane = dw - w..dw;
        let l = &self.layout;
        let mut out = Vec::new();
        for base in [l.enc, l.before, l.after] {
            for c in 0..=a {
                out.extend(lane.clone().map(|i| base + c * dw + i));
            }
        }
        for (base, cols) in [(l.out, m2), (l.w, f), (l.w_triad, j2), (l.moment_face, m2)] {
            for o in lane.clone() {
                out.extend((0..cols).map(|j| base + o * cols + j));
            }
        }
        for base in [l.out_bias, l.w_bias, l.moment_face_bias] {
            out.extend(lane.clone().map(|o| base + o));
        }
        let glue = self.theta.len() + s.coarse.theta.len();
        let d1 = s.coarse.declaration.width;
        for k in 0..s.harmonics {
            for c in (0..dw).filter(|c| !lane.contains(c)) {
                let row = k * dw + c;
                out.extend((0..d1).map(|j| glue + b2 + row * d1 + j));
                out.push(glue + bb2 + row);
            }
        }
        debug_assert!(out.iter().all(|&i| i < self.material_len()));
        Ok(Some(out))
    }

    /// [definition; the lead, November 18, the record of the two streams §11; `agent-inferred`] **The level as a passage read by two
    /// streams hears it**, at the split. `x` holds the `n` known sites and then the `n` open places.
    ///
    /// ```text
    /// news      c_t = the code of u_t at the retarded opening's face of place t (`known_news`); an open place's is that face's
    ///           expected code (`open_news`)
    /// sites     a place is a site where no earlier place within a section of news carries news at least its own
    ///           ([`level_anchors_before`]): what stands after a place has not arrived
    /// restrict  x¹_j = A m(j) + b_A over epoch j's known sites, as the law's; an open place is restricted by no one
    /// ticks     the level's field on its own clock, each epoch hearing only the epochs before it
    /// prolong   a known site of epoch j, j ≥ 1, takes release(Σ_k h_k(φ_t) v⁻_k(j − 1), 30), v⁻(j) = B⁻ r̂(x¹_j) + b_B⁻: the epoch that
    ///           ended before its own began. The open place at place t ≥ 1 stands in the epoch of the place before it, at the phase
    ///           its expected news carries it to, and takes the same epoch before.
    /// ```
    ///
    /// So a known site's state stays a function of the symbols up to its own, and an open place's of the symbols before its place. `B⁻`
    /// is a block of its own because the law's `B` hands an epoch to its own places (read on the line's states the law's block under
    /// one-sided hearing costs 0.24 to 0.26 nats at the frontier before any training, `read-far`'s `24` and `25`); founded at zero
    /// ([`Constitution::level_before`]). Why the epoch before: under the law's hearing three quarters of what the level hands the
    /// frontier arrives through the known places' states, and two thirds of the whole survives every place reading the epoch before
    /// its own, before any training in that relation (`read-far`'s `21` and `22` on the line's state of November 18).
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn scale_forward_before(&self, s: &Scale, x: &mut [i64], n: usize, known_news: &[i64], open_news: &[i64], past: bool, keep: bool, targets: &[usize]) -> Result<ScalePass> {
        let (d0, d1, h) = (self.declaration.width, s.coarse.declaration.width, s.harmonics);
        let Some((b2, bb2, _)) = s.before_offsets(d0) else {
            return refuse("a strand's level on a tower without its one-sided block");
        };
        let StrandCut { cut, open_harmonics, source } = strand_level_cut_units(known_news, open_news, s.units.as_ref().map(|u| (u, &targets[..n.min(targets.len())], self.declaration.alphabet)), level_section(self.declaration.alphabet), h, self.pi)?;
        let epochs = cut.anchors.len();
        let (a, ab, _, _, _) = glue_layout(h, d0, d1);
        let g = &s.glue;
        let mut out = ScalePass { open_harmonics, source, ..Default::default() };
        for xt in x[..n * d0].chunks_exact(d0) {
            lane_chart(xt, self.declaration.lanes, &mut out.read, &mut out.scale)?;
        }
        // The restriction over the known sites, through `A`; [`Scale::strand`] on the strand face, each site's symbol word on the rings.
        out.restricted = if s.strand {
            let ring = LevelCut { harmonics: strand_face_terms(self, &cut, h), ..cut.clone() };
            charted(&ring, h, &strand_face_reads(self, &targets[..n])?, d0)?
        } else {
            charted(&cut, h, &out.read, d0)?
        };
        let reach_a = reach(&g[a..ab]);
        let mut x1 = vec![0i64; epochs * d1];
        for j in 0..epochs {
            affine(&g[a..ab], reach_a, h * d0, &out.restricted[j * h * d0..(j + 1) * h * d0], Some(&g[ab..ab + d1]), MATERIAL_BITS, MATERIAL_BITS, &mut x1[j * d1..(j + 1) * d1])?;
        }
        // [`Scale::bank`] The slow store, charged by each epoch's restricted state before the level's ticks.
        self.bank_forward(s, &cut.tau, &x1, &mut out)?;
        // The level's field on its own clock, each epoch hearing only the epochs before it.
        out.definite = vec![true; epochs];
        out.paces = level_paces(&s.coarse.declaration, &cut)?;
        if keep {
            out.before_ticks = x1.clone();
        }
        let moment = vec![0i64; epochs * 2 * s.coarse.declaration.complex()];
        let reaches = s.coarse.reaches();
        for _ in 0..s.coarse.declaration.ticks {
            let mut cell = TickCell::default();
            s.coarse.tick(&mut x1, &out.definite, &out.definite, &out.paces, &moment, &reaches, None, &mut cell, crate::contact::Sided::Before { past })?;
            if keep {
                out.ticks.push(cell);
            }
        }
        for xj in x1.chunks_exact(d1) {
            lane_chart(xj, s.coarse.declaration.lanes, &mut out.coarse_read, &mut out.coarse_scale)?;
        }
        // The prolongation of the epoch before, through `B⁻` (and the slow store's `B_bank`, [`Scale::bank`]).
        let reach_b = reach(&g[b2..bb2]);
        let reach_k = s.bank_offsets(d0).map_or(0, |(bk, bf, _)| reach(&g[bk..bf]));
        let mut v = vec![0i64; h * d0];
        let mut row = vec![0i64; d0];
        for j in 0..epochs {
            if !out.source.contains(&Some(j)) {
                continue;
            }
            affine(&g[b2..bb2], reach_b, d1, &out.coarse_read[j * d1..(j + 1) * d1], Some(&g[bb2..bb2 + h * d0]), MATERIAL_BITS, MATERIAL_BITS, &mut v)?;
            self.bank_prolonged(s, &out, reach_k, j, &mut v)?;
            for t in (0..2 * n).filter(|&t| out.source[t] == Some(j)) {
                let ht = if t < n { &cut.harmonics[t * h..(t + 1) * h] } else { &out.open_harmonics[(t - n) * h..(t - n + 1) * h] };
                uncharted(ht, &v, d0, &mut row)?;
                // [the level's receipt] The prolonged row alone, read through the opening's reader at an open place, against its symbol.
                if s.receipt && t >= n {
                    let reach_o = reach(&self.theta[self.layout.opening..self.layout.opening + d0 * d0]);
                    out.receipt.push((t, self.opening_read(&row, reach_o)?, targets[t - n]));
                    if keep {
                        out.receipt_rows.extend_from_slice(&row);
                    }
                }
                for (xv, &r) in x[t * d0..(t + 1) * d0].iter_mut().zip(&row) {
                    *xv = fit64(*xv as i128 + r as i128)?;
                }
            }
        }
        out.cut = cut;
        Ok(out)
    }

    /// The news a strand's level reads ([`Constitution::scale_forward_before`]) from its places' retarded cavity openings `open_x`
    /// (`[n][D₀]`): at each place the code of its symbol at the opening's face, and that face's expected code (an open place's news).
    pub(crate) fn strand_news(&self, classes: &[usize], open_x: &[i64]) -> Result<(Vec<i64>, Vec<i64>)> {
        if !self.declaration.opening {
            return refuse("a strand's level on a field without the opening's block");
        }
        let dw = self.declaration.width;
        let l = &self.layout;
        let reach_o = reach(&self.theta[l.opening..l.opening + dw * dw]);
        let (mut known, mut open) = (Vec::with_capacity(classes.len()), Vec::with_capacity(classes.len()));
        for (t, xt) in open_x.chunks_exact(dw).enumerate() {
            let f = self.opening_read(xt, reach_o)?.face;
            known.push(f.code(classes[t]));
            let sum: i128 = f.masses.iter().map(|&m| m as i128 * face_code(m, f.total) as i128).sum();
            open.push(fit64(div_nearest(sum, f.total as i128))?);
        }
        Ok((known, open))
    }

    /// The reverse of [`Constitution::scale_forward_before`]: `dx`, the covector of the `2n` sites' states after the prolongation, is
    /// carried through `B⁻`, the level's ticks and the restriction into the covector of the known sites' states before it; the level's
    /// field's covector and the glue's (`A`, `b_A`, `B⁻`, `b_B⁻`) are added into `g`. The cut and the phases are data and take nothing.
    /// Under [`Scale::inside`] the receipt's covector runs as a stream of its own that stops at the restriction's material.
    pub(crate) fn scale_return_before(&self, s: &Scale, pass: &ScalePass, dx: &mut [i64], g: &mut [i128]) -> Result<()> {
        let d0 = self.declaration.width;
        let n = pass.cut.epoch.len();
        // The prolongation: `δv⁻_k(j) = release(Σ_(t reads j) h_k(φ_t) δx_t, 30)` over the known sites and the open places that read
        // epoch `j`, then `δb_B⁻ += Σ_j δv⁻(j)`, `δB⁻ += δv⁻(j) r̂¹_jᵀ` and `δr̂¹_j = B⁻ᵀ δv⁻(j)`.
        // [the level's receipt] Each compared row's covector through the opening's reader, held (the reader takes none): `δy⁰ =
        // release(Σ_c δz_c E(c), 16)`, `δr̂ = Rᵀ δy⁰`, `δrow` through the lane chart's adjoint. It joins the place's `δx_t` on the level's
        // route alone: the fine state before the prolongation takes none of it.
        let mut own = vec![0i64; 2 * n * d0];
        if !pass.receipt.is_empty() {
            let l = &self.layout;
            let reach_o = reach(&self.theta[l.opening..l.opening + d0 * d0]);
            for (t, read, c) in &pass.receipt {
                let dz = covector(&read.face, *c);
                let mut dy = vec![0i64; d0];
                for (i, slot) in dy.iter_mut().enumerate() {
                    let sum: i128 = dz.iter().enumerate().map(|(cc, &dzc)| dzc as i128 * self.theta[l.enc + cc * d0 + i] as i128).sum();
                    *slot = fit64(release(sum, STATE_BITS))?;
                }
                let mut dr = vec![0i64; d0];
                transposed(&self.theta[l.opening..l.opening + d0 * d0], reach_o, d0, &dy, MATERIAL_BITS, &mut dr)?;
                let back = lane_adjoint(&read.read, &read.scale[..self.declaration.lanes], &dr)?;
                own[t * d0..(t + 1) * d0].copy_from_slice(&back);
            }
        }
        if s.inside && !pass.receipt.is_empty() {
            // [the receipt kept inside the level] Two streams: the places' covector runs the whole route into the fine states; the
            // receipt's runs the level's own material and stops at the restriction's.
            let places = dx.to_vec();
            let none = vec![0i64; 2 * n * d0];
            self.level_stream_before(s, pass, &places, &none, Some(dx), g)?;
            self.level_stream_before(s, pass, &own, &none, None, g)
        } else {
            let places = dx.to_vec();
            self.level_stream_before(s, pass, &places, &own, Some(dx), g)
        }
    }

    /// One stream of [`Constitution::scale_return_before`]: the covector `src + extra` of the `2n` sites' states after the prolongation,
    /// through `B⁻`, the level's ticks and the restriction, the level's field's and the glue's covectors added into `g`; where `push` is
    /// given, the restriction's adjoint returns it into the known sites' states before the prolongation there.
    fn level_stream_before(&self, s: &Scale, pass: &ScalePass, src: &[i64], extra: &[i64], push: Option<&mut [i64]>, g: &mut [i128]) -> Result<()> {
        let (d0, d1, h) = (self.declaration.width, s.coarse.declaration.width, s.harmonics);
        let Some((b2, bb2, _)) = s.before_offsets(d0) else {
            return refuse("a strand's level's reverse on a tower without its one-sided block");
        };
        let cut = &pass.cut;
        let n = cut.epoch.len();
        let epochs = pass.definite.len();
        let (a, ab, _, _, _) = glue_layout(h, d0, d1);
        let len0 = self.theta.len();
        let len1 = s.coarse.theta.len();
        let (_, rest) = g.split_at_mut(len0);
        let (gc, gg) = rest.split_at_mut(len1);
        let gl = &s.glue;
        let mut acc = vec![0i128; epochs * h * d0];
        for t in 0..2 * n {
            let Some(j) = pass.source[t] else { continue };
            let ht = if t < n { &cut.harmonics[t * h..(t + 1) * h] } else { &pass.open_harmonics[(t - n) * h..(t - n + 1) * h] };
            let slot = &mut acc[j * h * d0..(j + 1) * h * d0];
            for (k, &hk) in ht.iter().enumerate() {
                for (c, (&v, &o)) in src[t * d0..(t + 1) * d0].iter().zip(&extra[t * d0..(t + 1) * d0]).enumerate() {
                    slot[k * d0 + c] += hk as i128 * (v as i128 + o as i128);
                }
            }
        }
        let dv: Vec<i64> = acc.into_iter().map(|v| fit64(release(v, MOVE_BITS))).collect::<Result<_>>()?;
        let douts: Vec<&[i64]> = dv.chunks_exact(h * d0).collect();
        // [`Scale::bank`] The slow store's block and the restricted states' covector through it, joined after the level's ticks' reverse.
        let dxb = self.bank_returned(s, pass, &douts, gg)?;
        for dout in &douts {
            for (i, &v) in dout.iter().enumerate() {
                gg[bb2 + i] += v as i128;
            }
        }
        let reads1: Vec<&[i32]> = (0..epochs).map(|j| &pass.coarse_read[j * d1..(j + 1) * d1]).collect();
        outer_sum(&mut gg[b2..bb2], d1, &douts, &reads1)?;
        let reach_b = reach(&gl[b2..bb2]);
        let mut dx1 = vec![0i64; epochs * d1];
        let mut dr1 = vec![0i64; d1];
        let l1 = s.coarse.declaration.lanes;
        for (j, dout) in douts.iter().enumerate() {
            transposed(&gl[b2..bb2], reach_b, d1, dout, MATERIAL_BITS, &mut dr1)?;
            let back = lane_adjoint(&pass.coarse_read[j * d1..(j + 1) * d1], &pass.coarse_scale[j * l1..(j + 1) * l1], &dr1)?;
            dx1[j * d1..(j + 1) * d1].copy_from_slice(&back);
        }
        // The level's ticks, in reverse.
        let paced = pass.paces.kappa.len();
        let (mut gtau, mut gsig) = (vec![vec![0i128; epochs]; paced], vec![vec![0i128; epochs]; paced]);
        let mut dm = vec![0i128; epochs * 2 * s.coarse.declaration.complex()];
        for cell in pass.ticks.iter().rev() {
            s.coarse.tick_return(cell, &mut dx1, gc, &pass.paces, &pass.definite, &mut dm, &mut gtau, &mut gsig, None, None, None, None)?;
        }
        for (a, &b) in dx1.iter_mut().zip(&dxb) {
            *a = fit64(*a as i128 + b as i128)?;
        }
        // The restriction, over the known sites.
        for j in 0..epochs {
            for (i, &v) in dx1[j * d1..(j + 1) * d1].iter().enumerate() {
                gg[ab + i] += v as i128;
            }
        }
        let ds: Vec<&[i64]> = dx1.chunks_exact(d1).collect();
        let ms: Vec<&[i64]> = pass.restricted.chunks_exact(h * d0).collect();
        outer_sum(&mut gg[a..ab], h * d0, &ds, &ms)?;
        // [`Scale::strand`] The strand face reads the encoding as data: the restriction's covector stops at its own material.
        let Some(dx) = push.filter(|_| !s.strand) else { return Ok(()) };
        let reach_a = reach(&gl[a..ab]);
        let mut dm_k = vec![0i64; h * d0];
        let mut dr = vec![0i64; d0];
        let l0 = self.declaration.lanes;
        for j in 0..epochs {
            transposed(&gl[a..ab], reach_a, h * d0, ds[j], MATERIAL_BITS, &mut dm_k)?;
            let end = cut.anchors.get(j + 1).copied().unwrap_or(n);
            for t in cut.anchors[j]..end {
                uncharted(&cut.harmonics[t * h..(t + 1) * h], &dm_k, d0, &mut dr)?;
                let back = lane_adjoint(&pass.read[t * d0..(t + 1) * d0], &pass.scale[t * l0..(t + 1) * l0], &dr)?;
                for (slot, &v) in dx[t * d0..(t + 1) * d0].iter_mut().zip(&back) {
                    *slot = fit64(*slot as i128 + v as i128)?;
                }
            }
        }
        Ok(())
    }

    /// The level's reverse at the split: `dx`, the covector of the faces after the prolongation, is carried through the prolongation,
    /// the level's ticks and the restriction into the covector of the faces before it; the level's field's covector and the glue's are
    /// added into `g` at their places in the material ([`Constitution::families_all`]). The cut is data and takes nothing.
    pub(crate) fn scale_return(&self, s: &Scale, pass: &ScalePass, dx: &mut [i64], g: &mut [i128]) -> Result<()> {
        let (d0, d1, h) = (self.declaration.width, s.coarse.declaration.width, s.harmonics);
        let cut = &pass.cut;
        let epochs = pass.definite.len();
        let (a, ab, b, bb, _) = glue_layout(h, d0, d1);
        let len0 = self.theta.len();
        let len1 = s.coarse.theta.len();
        let (_, rest) = g.split_at_mut(len0);
        let (gc, gg) = rest.split_at_mut(len1);
        let gl = &s.glue;
        // The prolongation: `δv_k(j) = release(Σ_(t∈e_j) h_k(φ_t) δx_t, 30)`, then `δb_B += Σ_j δv(j)`, `δB += δv(j) r̂¹_jᵀ` and
        // `δr̂¹_j = Bᵀ δv(j)`.
        let dv = charted(cut, h, dx, d0)?;
        let douts: Vec<&[i64]> = dv.chunks_exact(h * d0).collect();
        // [`Scale::bank`] The slow store's block and the restricted states' covector through it, joined after the level's ticks' reverse.
        let dxb = self.bank_returned(s, pass, &douts, gg)?;
        for dout in &douts {
            for (i, &v) in dout.iter().enumerate() {
                gg[bb + i] += v as i128;
            }
        }
        let reads1: Vec<&[i32]> = (0..epochs).map(|j| &pass.coarse_read[j * d1..(j + 1) * d1]).collect();
        outer_sum(&mut gg[b..bb], d1, &douts, &reads1)?;
        let reach_b = reach(&gl[b..bb]);
        let mut dx1 = vec![0i64; epochs * d1];
        let mut dr1 = vec![0i64; d1];
        let l1 = s.coarse.declaration.lanes;
        for (j, dout) in douts.iter().enumerate() {
            transposed(&gl[b..bb], reach_b, d1, dout, MATERIAL_BITS, &mut dr1)?;
            let back = lane_adjoint(&pass.coarse_read[j * d1..(j + 1) * d1], &pass.coarse_scale[j * l1..(j + 1) * l1], &dr1)?;
            dx1[j * d1..(j + 1) * d1].copy_from_slice(&back);
        }
        // The level's ticks, in reverse; its clock is data and carries no covector, nor its absent moments.
        let paced = pass.paces.kappa.len();
        let (mut gtau, mut gsig) = (vec![vec![0i128; epochs]; paced], vec![vec![0i128; epochs]; paced]);
        let mut dm = vec![0i128; epochs * 2 * s.coarse.declaration.complex()];
        for cell in pass.ticks.iter().rev() {
            s.coarse.tick_return(cell, &mut dx1, gc, &pass.paces, &pass.definite, &mut dm, &mut gtau, &mut gsig, None, None, None, None)?;
        }
        for (a, &b) in dx1.iter_mut().zip(&dxb) {
            *a = fit64(*a as i128 + b as i128)?;
        }
        // The restriction: `δb_A += Σ_j δx¹_j`, `δA += δx¹_j m(j)ᵀ` and `δm(j) = Aᵀ δx¹_j`, each place's part
        // `release(Σ_k h_k(φ_t) δm_k(j), 30)` through its read's adjoint into `δx_t`.
        for j in 0..epochs {
            for (i, &v) in dx1[j * d1..(j + 1) * d1].iter().enumerate() {
                gg[ab + i] += v as i128;
            }
        }
        let ds: Vec<&[i64]> = dx1.chunks_exact(d1).collect();
        let ms: Vec<&[i64]> = pass.restricted.chunks_exact(h * d0).collect();
        outer_sum(&mut gg[a..ab], h * d0, &ds, &ms)?;
        // [`Scale::strand`] The strand face reads the encoding as data: the restriction's covector stops at its own material.
        if s.strand {
            return Ok(());
        }
        let reach_a = reach(&gl[a..ab]);
        let mut dm_k = vec![0i64; h * d0];
        let mut dr = vec![0i64; d0];
        let l0 = self.declaration.lanes;
        for j in 0..epochs {
            transposed(&gl[a..ab], reach_a, h * d0, ds[j], MATERIAL_BITS, &mut dm_k)?;
            let end = cut.anchors.get(j + 1).copied().unwrap_or(cut.epoch.len());
            for t in cut.anchors[j]..end {
                uncharted(&cut.harmonics[t * h..(t + 1) * h], &dm_k, d0, &mut dr)?;
                let back = lane_adjoint(&pass.read[t * d0..(t + 1) * d0], &pass.scale[t * l0..(t + 1) * l0], &dr)?;
                for (slot, &v) in dx[t * d0..(t + 1) * d0].iter_mut().zip(&back) {
                    *slot = fit64(*slot as i128 + v as i128)?;
                }
            }
        }
        Ok(())
    }
}
