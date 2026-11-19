//! **Deposition: the only law that changes the constitution.**
//!
//! the covector's two moments at `2^(−3)` and `2^(−8)`; each entry's step `m/(⌊√v⌋ + 1)` at `2^(−rate)`, its rate its own where
//! the parts carry rates; the lap's mean of states
//!
//! Kind: chain over the sections; sum over a lap. Kernels: host, beside the card.
//! Lean: `HNN/DepositHold`, `HNN/PairedDeposit`, `HNN/LatticeDeposit`.
//! Atlas: `deposition.lap-cosine-drift-over-noise`, `deposition.rate-temperature-standing-spread`, `tower.field-lap-mean`, `tower.field-part-rates`,
//! `tower.field-step-price`.
//! Records: `2026-11-11_A_DEPOSITS_RATE_IS…`. The derivations' history is in the records; the items below keep their reasons.

#[allow(unused_imports)]
use crate::field::*;
#[allow(unused_imports)]
use rayon::prelude::*;

/// [definition; theory, November 10 19:05] **The founded parts**: a part is a family of entries founded together, and steps at a rate
/// of its own ([`RateParts`]): `W`'s new columns, the new `a` rows, the new `b` rows (with the contacts' biases founded with them),
/// and each lane family on its own (the second lane's coordinates, [`Constitution::laned`], of the encodings `E`, `E₋`, `E₊`, the key,
/// value and probe charts, the current's return, the moment's chart, the readout's lift, the face biases together, and the lane's
/// columns of `a` and `b`). The old entries (and `W`'s lane rows) are no part.
///
/// [definition; theory, November 11 17:25] The carry circles are founded together and step at rates of their own ([`Declaration::carry`]):
/// `carry` their charts `Q`, `H` and both biases (part 15, which was the retired carry's third chart, `g_chart`), `w_carry` their columns of `W`,
/// `a_carry` and `b_carry` their rows of the pair drives with the drives' biases. A parts line carries the three circle parts only where the field
/// has carry circles ([`RateParts`]).
///
/// [definition; theory, November 11 21:15, G86] The first lane's letter rows are parts of their own: `enc_first`, `before_first` and
/// `after_first`, the encodings' rows (each class as itself, as the neighbour before and after) over the first lane's columns, old entries
/// at the base rate until then. Why: a part's rate follows its polarization (its fall two laps on over its heat, read at lap means), and
/// these rows are the field's most polarized blocks (G84, G86's premise), so they need a rate of their own.
///
/// [definition; theory, November 12, the triad record §3.2 and §4] The triads are one part, `triad` (index 22, [`TRIAD_PART`]): their charts `A`,
/// `B`, `G`, the charts' biases and their return `W_T`. Why one: the gauge `(α, β, γ, w) → (λα, μβ, νγ, (λμν)⁻¹ w)` leaves the return
/// unchanged, so the legs and the return are one family that no receiver tells apart, and their covectors keep the scale identity at every
/// state. Under a plain step at one rate that identity gives each leg the same squared norm to first order (the Manley–Rowe relation); this
/// learner divides each entry's step by its own `⌊√v⌋ + 1` (`deposit_step`), and its divisors move with what reaches each entry, so equal gains
/// of the legs are no prediction for it. The part's one octave stands because an octave between the legs would be a rate set by hand. A parts
/// line carries it only where the field has triads ([`written_parts`]).
///
/// [definition; theory, November 13, P60 item 1f] The opening's lift is one part, `opening` (index 23, [`OPENING_PART`]): `R⁰` and `b⁰`. Why a part
/// of its own: it is a new block whose covector reaches it from the opening's comparison alone, and the part rates' law sets each block's rate
/// from its own travel. A parts line carries it only where the field has the opening's lift ([`written_parts`]).
///
/// [definition; theory, November 13, the junction record §7] The junction's chart is one part, `junction` (index 24, [`JUNCTION_PART`]): `L` and
/// `ℓ_b`. Why a part of its own: it is a new block whose covector reaches it only through the tick's return, founded where that covector stands
/// at first order, and the part rates' law sets each block's rate from its own travel. A parts line carries it only where the tick has the return.
///
/// [definition; agent-inferred, November 14, the ring record §4] The mark's strengths are one part, `mark` (index 25, [`MARK_PART`]): `α_b`.
/// Why a part of its own: a new block whose covector reaches it only through the second read's opening, founded where G175 read that covector,
/// and the part rates' law sets each block's rate from its own travel. A parts line carries it only where the field reads twice.
/// [definition; Brandon, November 15 02:06Z] The face's loudness is one part, `loud` (index 26, [`LOUD_PART`]): `κ_ℓ` and `b`. Why a part of its
/// own: a new block whose covector reaches it only through the readout's sharpness, founded at zero, and the part rates' law sets each block's
/// rate from its own travel. A parts line carries it only where the face reads its sites' loudness.
pub const PART_NAMES: [&str; 27] = ["w_new", "a_new", "b_new", "enc_lane", "before_lane", "after_lane", "q_lane", "v_lane", "probe_lane", "out_lane", "moment_face_lane", "read_lane", "face_biases_lane", "a_lane", "b_lane", "carry", "w_carry", "a_carry", "b_carry", "enc_first", "before_first", "after_first", "triad", "opening", "junction", "mark", "loud"];

/// The triads' one part ([`PART_NAMES`] index 22), written after the first lane's letter rows only where the field has triads.
pub const TRIAD_PART: usize = 22;

/// The opening's lift's one part ([`PART_NAMES`] index 23), written after the triad's only where the field has the opening's lift.
pub const OPENING_PART: usize = 23;

/// The junction's chart's one part ([`PART_NAMES`] index 24), written last only where the tick has the junction's return.
pub const JUNCTION_PART: usize = 24;

/// The mark's strengths' one part ([`PART_NAMES`] index 25), written last only where the field reads twice.
pub const MARK_PART: usize = 25;

/// The face's loudness's one part ([`PART_NAMES`] index 26), written last only where the face reads its sites' loudness.
pub const LOUD_PART: usize = 26;

/// The plain founded parts (the first sixteen of [`PART_NAMES`]): every field writes them.
pub const PLAIN_PARTS: usize = 16;

/// The carry circles' three parts after the plain ones (`w_carry`, `a_carry`, `b_carry`), written only where the field has circles.
pub const CIRCLE_PARTS: std::ops::Range<usize> = 16..19;

/// The first lane's letter rows' three parts (`enc_first`, `before_first`, `after_first`), written by every field.
pub const FIRST_PARTS: std::ops::Range<usize> = 19..22;

/// [definition; theory, November 11 21:15] **The parts a parts line carries, in its order**: the plain sixteen, the circles' three where the
/// field has circles, then the first lane's letter rows' three, then (November 12, the triad record §4) the triad's one where the field has
/// triads. A line read is matched against this by its length, and an older line (fifteen or sixteen, or nineteen with circles: the lines before
/// the letter rows' parts; or a triad field's line without the triad's octave) reads with the parts it lacks at octave 0. Why the triad's comes
/// last and only with triads: at `J = 0` every line the field writes is the line before, so a build reproduces a line's lap and compares like
/// with like.
///
/// [definition; theory, November 13, P60 item 1f] The opening's one part comes after them only where the field has the opening's lift, for the
/// same reason: a field without it writes every line it wrote before. So does the junction's one part, last, only where the tick has the return.
pub fn written_parts(carry: usize, triads: usize, opening: bool, junction: bool, mark: bool, loud: bool) -> Vec<usize> {
    let mut out: Vec<usize> = (0..PLAIN_PARTS).collect();
    if carry > 0 {
        out.extend(CIRCLE_PARTS);
    }
    out.extend(FIRST_PARTS);
    if triads > 0 {
        out.push(TRIAD_PART);
    }
    if opening {
        out.push(OPENING_PART);
    }
    if junction {
        out.push(JUNCTION_PART);
    }
    if mark {
        out.push(MARK_PART);
    }
    if loud {
        out.push(LOUD_PART);
    }
    out
}

/// The number of founded parts ([`PART_NAMES`]).
pub const PARTS: usize = PART_NAMES.len();

/// The part of an entry no founded part holds.
pub const OLD_PART: u8 = u8::MAX;

/// [definition; theory, November 10 19:05] **A deposit rate per founded part**: part `p` steps at `2^(−(rate − octaves[p]))`, `octaves[p]`
/// octaves faster than the old entries' `2^(−rate)`; `contacts_before` the contact count before the growth in contacts, which
/// tells the new contacts ([`Constitution::founded_parts`]). Carried in the learner's text, with no run switch; moved between laps from the
/// saved states by [`RateParts::updated`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RateParts {
    pub contacts_before: usize,
    pub octaves: [u32; PARTS],
}

/// [definition; theory, November 10 19:05] **A part's travel over two laps**: with `d₁ = S_(k−1) − S_(k−2)` and `d₂ = S_k − S_(k−1)` the
/// part's displacements over the entries it holds, `Σ d₁d₂`, `Σ d₁²` and `Σ d₂²` (on the material's integers, each within `i128`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PartTravel {
    pub entries: usize,
    pub dot: i128,
    pub first: i128,
    pub second: i128,
}

impl PartTravel {
    /// The cosine of the two displacements against `1/2`, exactly: `Greater` where `c > 1/2` (straight travel: `4 (Σ d₁d₂)² > Σd₁² Σd₂²`
    /// with the dot positive), `Less` where `c < 1/2` (a wander, a reversal, or no travel at all), `Equal` where a lap's travel
    /// equals its wander.
    pub fn against_half(&self) -> std::cmp::Ordering {
        use num_bigint::BigInt;
        if self.first == 0 || self.second == 0 || self.dot <= 0 {
            return std::cmp::Ordering::Less;
        }
        (BigInt::from(4) * BigInt::from(self.dot) * BigInt::from(self.dot)).cmp(&(BigInt::from(self.first) * BigInt::from(self.second)))
    }

    /// The cosine in millionths (`⌊10⁶ c⌋` toward zero; `0` where a displacement is zero).
    pub fn cosine_micro(&self) -> i64 {
        use num_bigint::BigInt;
        use num_traits::ToPrimitive;
        let root = (BigInt::from(self.first) * BigInt::from(self.second)).sqrt();
        if root.sign() != num_bigint::Sign::Plus {
            return 0;
        }
        (BigInt::from(self.dot) * BigInt::from(1_000_000) / root).to_i64().unwrap_or(0)
    }
}

/// [definition; theory, November 10 19:05] Each part's travel from three saved materials (`older`, `old`, `now`, each the field's
/// material in order) over the entries `parts` ([`Constitution::founded_parts`]) assigns it.
pub fn part_travel(parts: &[u8], older: &[i32], old: &[i32], now: &[i32]) -> [PartTravel; PARTS] {
    let mut out = [PartTravel::default(); PARTS];
    for (i, &p) in parts.iter().enumerate() {
        if p == OLD_PART {
            continue;
        }
        let (d1, d2) = (i128::from(old[i]) - i128::from(older[i]), i128::from(now[i]) - i128::from(old[i]));
        let t = &mut out[p as usize];
        t.entries += 1;
        t.dot += d1 * d2;
        t.first += d1 * d1;
        t.second += d2 * d2;
    }
    out
}

impl RateParts {
    /// [definition; theory, November 10 19:05] **The update at a lap's end**: each part with `c > 1/2` goes one octave faster, each with
    /// `c < 1/2` one slower, never under the old rate (`octaves 0`) nor past the rate's own bits (`rate_bits − 1`); a part whose
    /// travel equals its wander rests.
    pub fn updated(&self, travel: &[PartTravel; PARTS], rate_bits: u32) -> Self {
        let mut octaves = self.octaves;
        for (k, t) in octaves.iter_mut().zip(travel) {
            *k = match t.against_half() {
                std::cmp::Ordering::Greater => (*k + 1).min(rate_bits.saturating_sub(1)),
                std::cmp::Ordering::Less => k.saturating_sub(1),
                std::cmp::Ordering::Equal => *k,
            };
        }
        Self { octaves, ..*self }
    }
}

impl Constitution {
    /// [definition; theory, November 10 19:05] **Each material entry's founded part** ([`PART_NAMES`] by index; [`OLD_PART`] none): the
    /// lane's entries (the face coordinates past the first lane, where the field has more than one) by family, the new contacts'
    /// (the pair drives' rows and their biases, the pair's return's columns, of the contacts past `contacts_before`'s: real parts
    /// `[before/2, f/2)`, imaginary `[f/2 + before/2, f)`) over them.
    pub fn founded_parts(&self, contacts_before: usize) -> Vec<u8> {
        let (d, l) = (&self.declaration, &self.layout);
        let (dw, f, m2, a1) = (d.width, d.contacts, 2 * d.complex(), d.alphabet + 1);
        let lw = if d.lanes > 1 { d.lane_width() } else { dw };
        let (half_old, half_new) = (contacts_before / 2, f / 2);
        let new_contact = |e: usize| (half_old..half_new).contains(&e) || e >= half_new + half_old;
        let mut parts = vec![OLD_PART; self.theta.len()];
        for (part, start) in [(3u8, l.enc), (4, l.before), (5, l.after)] {
            for r in 0..a1 {
                parts[start + r * dw + lw..start + (r + 1) * dw].fill(part);
            }
        }
        for (part, start) in [(6u8, l.q), (7, l.v), (8, l.probe)] {
            for r in 0..m2 {
                parts[start + r * dw + lw..start + (r + 1) * dw].fill(part);
            }
        }
        for (part, start) in [(9u8, l.out), (10, l.moment_face)] {
            parts[start + lw * m2..start + dw * m2].fill(part);
        }
        for r in 0..dw {
            for c in 0..dw {
                if r >= lw || c >= lw {
                    parts[l.read + r * dw + c] = 11;
                }
            }
        }
        for start in [l.out_bias, l.w_bias, l.moment_face_bias, l.lift_bias] {
            parts[start + lw..start + dw].fill(12);
        }
        // [theory, November 11 21:15, G86] The first lane's letter rows: the encodings' columns over the first lane.
        for (part, start) in [(FIRST_PARTS.start as u8, l.enc), (FIRST_PARTS.start as u8 + 1, l.before), (FIRST_PARTS.start as u8 + 2, l.after)] {
            for r in 0..a1 {
                parts[start + r * dw..start + r * dw + lw].fill(part);
            }
        }
        for (part, start) in [(13u8, l.a), (14, l.b)] {
            for e in 0..f {
                parts[start + e * dw + lw..start + (e + 1) * dw].fill(part);
            }
        }
        // The new contacts', over the lane's.
        for e in (0..f).filter(|&e| new_contact(e)) {
            for (part, start, bias) in [(1u8, l.a, l.a_bias), (2, l.b, l.b_bias)] {
                parts[start + e * dw..start + (e + 1) * dw].fill(part);
                parts[bias + e] = part;
            }
            for r in 0..dw {
                parts[l.w + r * f + e] = 0;
            }
        }
        // [theory, November 11 17:25] The carry circles', over the lane's and the new contacts': their charts and biases, their columns of `W`
        // (real and imaginary parts), and their rows of `a` and `b` with the drives' biases.
        if d.carry > 0 {
            parts[l.carry..l.carry + 2 * d.carry * dw].fill(15);
            parts[l.carry_bias..l.carry_bias + 2 * d.carry].fill(15);
            // [the lead, November 19] The pump's chart is the circles' gate's third chart: the `carry` part's ([`Declaration::pump`]).
            if d.pump {
                parts[l.pump..l.pump + 2 * d.carry * dw].fill(15);
                parts[l.pump_bias..l.pump_bias + 2 * d.carry].fill(15);
            }
            for e in (d.carry_first()..f / 2).flat_map(|e| [e, f / 2 + e]) {
                for r in 0..dw {
                    parts[l.w + r * f + e] = 16;
                }
                for (part, start, bias) in [(17u8, l.a, l.a_bias), (18, l.b, l.b_bias)] {
                    parts[start + e * dw..start + (e + 1) * dw].fill(part);
                    parts[bias + e] = part;
                }
            }
        }
        // [theory, November 12, the triad record §4] The triads', one part over the lane's: their charts `A`, `B`, `G`, the charts' biases and
        // their return `W_T` ([`TRIAD_PART`]).
        if d.triads > 0 {
            let (j2, j6) = (2 * d.triads, 6 * d.triads);
            parts[l.triad..l.triad + j6 * dw].fill(TRIAD_PART as u8);
            parts[l.triad_bias..l.triad_bias + j6].fill(TRIAD_PART as u8);
            parts[l.w_triad..l.w_triad + dw * j2].fill(TRIAD_PART as u8);
        }
        // [theory, November 13, P60 item 1f] The opening's lift, one part: `R⁰` and `b⁰` ([`OPENING_PART`]).
        if d.opening {
            parts[l.opening..l.opening + dw * dw].fill(OPENING_PART as u8);
            parts[l.opening_bias..l.opening_bias + dw].fill(OPENING_PART as u8);
        }
        // [theory, November 13, the junction record §7] The junction's chart, one part: `L` and `ℓ_b` ([`JUNCTION_PART`]).
        if d.junction {
            parts[l.junction..l.junction + dw].fill(JUNCTION_PART as u8);
            parts[l.junction_bias] = JUNCTION_PART as u8;
        }
        // [agent-inferred, November 14, the ring record §4] The mark's strengths, one part ([`MARK_PART`]).
        if d.mark {
            parts[l.mark..l.mark + MARK_BASES].fill(MARK_PART as u8);
        }
        // [Brandon, November 15 02:06Z] The face's loudness, one part ([`LOUD_PART`]).
        if d.loud {
            parts[l.loud..l.loud + d.lanes + 1].fill(LOUD_PART as u8);
        }
        parts
    }
}

/// `base` less `release(step, halvings)` in each entry, and whether any entry moved.
pub(crate) fn stepped(base: &Constitution, step: &[i128], halvings: u32) -> Result<(Constitution, bool)> {
    let mut candidate = base.clone();
    let mut moved = false;
    for (slot, &q) in candidate.material_mut().zip(step) {
        let s = release(q, halvings);
        if s != 0 {
            moved = true;
            *slot = fit32(*slot as i128 - s, "a deposited parameter outgrew its 32-bit carrier")?;
        }
    }
    Ok((candidate, moved))
}

/// What [`scaled`] read: the regions' code under the step at its size less `old`'s (on `2^(−20)`
/// bits), the further halvings of the last size read, and the stepped material that stands with
/// its faces (`None`: the step stands at no size read).
pub(crate) struct Scaled {
    pub(crate) change: i64,
    pub(crate) halvings: u32,
    pub(crate) standing: Option<(Constitution, Vec<Vec<Option<TowerFace>>>)>,
}

/// [definition; agent-inferred, November 1] **A step's size read in at most three reads**: the held
/// step's read on the next regions ([`Learner::next_scale`]: no more bits), a declared
/// comparison under [`Learner::read_held`] only. From November 1 to 5 it was also the
/// certificate's law ([`Learner::section_realized`], `strict`: the stepped material had to code
/// the regions strictly fewer bits than `old`); the step fluxes since November 5, and `strict` has had
/// no caller since (history, kept with its reading below). The step `base − release(step, h0)` is
/// read; where it stands, it stands. Otherwise it is read at half its size; where that stands, it
/// stands halved. Otherwise the excess `e(μ)` of the regions' code over `old`'s at the step's
/// fraction `μ` is read at `μ = 1` and `μ = ½`, and the parabola `e(μ) = aμ + bμ²` through them
/// (`e(0) = 0`) has `a = 4e(½) − e(1)`, `b = 2e(1) − 4e(½)`: with `a ≥ 0` (or an excess the codes
/// read at or below zero where the exact comparison did not stand) the step's direction raises the
/// regions' code at every size the reads resolve, and it stands nowhere; with `a < 0` (then
/// `b > 0`) the parabola is lowest at `μ* = −a/2b ≤ ¼`, and the step is read once more at the
/// largest halving `2^(−h) ≤ μ*`, where the parabola is below zero, standing there or nowhere. A
/// size that moves no entry stands nowhere.
///
/// Why bounded (the second reading, receipts `…_receipts/reading-2/`): halving until the step
/// stood took 1,608 rereads of the next regions over 131 of 336 sections, 67 of the 105 halved
/// steps standing only at `2^(−12)` of their size or less, and the certificate's own halvings
/// reached 9 to 18 on 14 sections; their direction, not their size, raised the code, which the
/// parabola reads from two reads where the halvings read it from a dozen.
pub(crate) fn scaled(base: &Constitution, step: &[i128], h0: u32, old: &Compared, strict: bool, regions: &[Region], realization: &mut dyn Realization) -> Result<Scaled> {
    let spans = spans_of(regions);
    let stands = |new: &Compared| if strict { fewer(old, new, &spans) } else { !fewer(new, old, &spans) };
    let code_old = code_of(old, &spans);
    let (full, moved) = stepped(base, step, h0)?;
    if !moved {
        return Ok(Scaled { change: 0, halvings: 0, standing: None });
    }
    let full_faces = realization.read_faces(&full, regions)?;
    let at_full = compared(&full_faces, regions)?;
    let change = code_of(&at_full, &spans) - code_old;
    if stands(&at_full) {
        return Ok(Scaled { change, halvings: 0, standing: Some((full, full_faces)) });
    }
    let nowhere = |halvings: u32| Scaled { change, halvings, standing: None };
    let (half, moved) = stepped(base, step, h0 + 1)?;
    if !moved {
        return Ok(nowhere(1));
    }
    let half_faces = realization.read_faces(&half, regions)?;
    let at_half = compared(&half_faces, regions)?;
    if stands(&at_half) {
        return Ok(Scaled { change, halvings: 1, standing: Some((half, half_faces)) });
    }
    // The parabola through the two excesses (on the codes' `2^(−20)` bits).
    let (e1, e2) = (i128::from(change), i128::from(code_of(&at_half, &spans) - code_old));
    let a = 4 * e2 - e1;
    if e1 <= 0 || e2 <= 0 || a >= 0 {
        return Ok(nowhere(1));
    }
    // `1/μ* = 2b/(−a) = (4e(1) − 8e(½))/(e(1) − 4e(½))`; `h` the least with `2^h ≥ 1/μ*`.
    let (num, den) = (4 * e1 - 8 * e2, e1 - 4 * e2);
    let mut h = 2u32;
    while h < 127 && (den << h) < num {
        h += 1;
    }
    let (candidate, moved) = stepped(base, step, h0 + h)?;
    if !moved {
        return Ok(nowhere(h));
    }
    let candidate_faces = realization.read_faces(&candidate, regions)?;
    if stands(&compared(&candidate_faces, regions)?) {
        return Ok(Scaled { change, halvings: h, standing: Some((candidate, candidate_faces)) });
    }
    Ok(nowhere(h))
}

/// [measurement; theory, November 11] **The lap's mean of the material**: the sum, entry by entry, of the material as it stands after
/// each section's deposit over one lap, released to the grain (`Σ_s θ_s / n` to the nearest, a half away from zero). A reading: no
/// deposit reads it and the learner's state is the same with it. Why (the readings of November 11): a deposit at rate `2^(−k)`
/// holds each entry in a standing spread about a rest position (its cost `2^(−k) σ/4` an entry, in place within about a fifth of a
/// lap at the old rate), a saved state is one draw of that spread, and lap ends a lap apart do not remember each other; the mean
/// over the cycle the passage makes, every section once, sheds what reverses inside the lap, so a line's level and a rate's worth
/// are read at it. The sums are `i64`: an entry is under `2^31` and at most `2^31` states join.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MaterialMean {
    pub(crate) sum: Vec<i64>,
    pub(crate) states: i64,
}

impl MaterialMean {
    /// No state joined, over a material of `entries` ([`Constitution::material_len`]).
    pub fn new(entries: usize) -> Self {
        Self { sum: vec![0; entries], states: 0 }
    }

    /// The field's material joins the sum; refused on a material of another length and past `2^31` states.
    pub fn take(&mut self, field: &Constitution) -> Result<()> {
        if field.material_len() != self.sum.len() || self.states >= 1 << 31 {
            return refuse("a material joined to a mean of another length, or past the states its sums hold");
        }
        for (sum, &v) in self.sum.iter_mut().zip(field.material()) {
            *sum += i64::from(v);
        }
        self.states += 1;
        Ok(())
    }

    /// The states joined.
    pub fn states(&self) -> i64 {
        self.states
    }

    /// `field` with its material at the mean, the entries that differ from `field`'s own and `Σ (mean − θ)²` over them; refused
    /// before a state joined and onto a material of another length.
    pub fn released(&self, field: &Constitution) -> Result<(Constitution, usize, i128)> {
        if self.states == 0 || field.material_len() != self.sum.len() {
            return refuse("a mean released before a state joined, or onto a material of another length");
        }
        let mut out = field.clone();
        let (mut moved, mut square) = (0usize, 0i128);
        for (slot, &sum) in out.material_mut().zip(&self.sum) {
            let mean = fit32(div_nearest(i128::from(sum), i128::from(self.states)), "a material's mean outgrew its 32-bit carrier")?;
            let d = i128::from(mean) - i128::from(*slot);
            if d != 0 {
                moved += 1;
                square += d * d;
            }
            *slot = mean;
        }
        Ok((out, moved, square))
    }
}

impl Learner {

    /// [definition; theory, November 10 19:05] **Each entry's deposit rate**: the learner's `rate_bits`, and for an entry of a founded
    /// part ([`Constitution::founded_parts`]) that many bits less its part's octaves ([`RateParts`]), never under one bit; where the learner
    /// carries each entry's own rate ([`Learner::own_rates`], November 12), that rate.
    pub fn entry_rates(&self) -> Vec<u32> {
        // [theory, November 12 00:20] An entry's own rate, where the learner carries the line, is its rate.
        if let Some(own) = &self.own_rates {
            return own.clone();
        }
        let mut rates = vec![self.rate_bits; self.field.material_len()];
        if let Some(rp) = self.rate_parts {
            for (rate, &p) in rates.iter_mut().zip(&self.field.founded_parts(rp.contacts_before)) {
                if p != OLD_PART {
                    *rate = self.rate_bits.saturating_sub(rp.octaves[p as usize]).max(1);
                }
            }
        }
        rates
    }

    /// [measurement; theory, November 12] **The founded parts a reading gathers by** ([`Constitution::founded_parts`]): the new contacts
    /// told from the contact count the learner's parts' rates carry, and from the field's own count where it carries none (so no
    /// contact is new). A reading's partition; no rate is read from it.
    pub fn reading_parts(&self) -> Vec<u8> {
        self.field.founded_parts(self.rate_parts.map_or(self.field.declaration.contacts, |rp| rp.contacts_before))
    }
}

// The items this object owns that stood in the October tower until C5 (#603), each as it stood.

/// The first moment's rate, `2^(−3)`, and the second's, `2^(−8)` (agent-inferred: the classical
/// 0.9 and 0.999 read as dyadic rates; the second at `2^(−8)` so a pass of a few hundred sections
/// renews it).
pub const FIRST_RATE: u32 = 3;

/// [definition; the lead, November 17] **The rate past which an entry is held**: at an own rate of this many bits or more
/// ([`Learner::own_rates`]) an entry's step `((m ≪ grain) ≫ rate) / root` releases to zero for every moment (the ratio `m / root` is
/// under about 4.2 and the grain at most 24 bits), so the entry is outside the deposit and its leak ([`Learner::leak`]) passes it by.
pub const HELD_RATE: u32 = 64;

pub const SECOND_RATE: u32 = 8;

/// [definition; the lead, November 18] **The bits a step's carried remainder holds under its entry's grain** ([`crate::learner::Learner::remainder`]):
/// sixteen, so a face-grain entry's step is resolved to `2^(−32)`, the grain its first moment is carried on, and a rate of up to 28 bits
/// still moves it.
pub const REMAINDER_BITS: u32 = 16;

/// A covector entry on the deposit's grain `2^(−32)` from its family's natural grain: a material
/// family's `Σ δz x` on `2^(−40)` is released, a face family's `Σ δz` on `2^(−24)` raised. The moves
/// step through their chart ([`Tower::to_move_chart`]) and are not read here.
pub fn on_step_grain(grain: u32, v: i128) -> i128 {
    if grain == MATERIAL_BITS {
        release(v, COVECTOR_BITS + FACE_BITS - STEP_BITS)
    } else {
        v << (STEP_BITS - COVECTOR_BITS)
    }
}

/// The deposit's step for one entry: its first moment `m` (on `2^(−32)`) over the root of its
/// second `v`, at the rate `2^(−rate)`, on its family's own grain:
/// `((m ≪ grain) ≫ rate) / (⌊√v⌋ + 1)`. The tower's certificate halves it; the field deposits it
/// at this size (the step fluxes, Brandon, November 5).
pub fn deposit_step(m: i128, v: i128, grain: u32, rate: u32) -> i128 {
    deposit_over(m, deposit_root(v), grain, rate)
}

/// The deposit's divisor for a second moment `v`: `⌊√v⌋ + 1`.
pub fn deposit_root(v: i128) -> i128 {
    (v.max(0) as u128).isqrt() as i128 + 1
}

/// The deposit's step for a first moment `m` over its second moment's divisor `root`.
pub fn deposit_over(m: i128, root: i128, grain: u32, rate: u32) -> i128 {
    ((m << grain) >> rate) / root
}

/// A moment moved toward its input at the rate `2^(−rate)`: `m + release(g − m, rate)`, and at
/// least one grain when that release rounds to zero. Released to the nearest grain alone, a moment
/// within `2^(rate−1)` grains of its input never reaches it, so a contact that stops conducting
/// keeps its last moments (`|m| ≤ 3`, `v ≤ 127` grains) and the step `m/(√v + 2^(−32))` reads that
/// remainder as a covector of a quarter of the rate (measured October 23 on all 6,726 GSM8K
/// problems, the narrow tower: no weight stalled through pass 2; 980 had by pass 3 and 2,146 by
/// pass 4, the most of two contacts that had stopped conducting, each moving `2^(−9)` every section,
/// one from 0.64 at pass 2 to 15.9 at pass 5). A silent contact's drifted weights meet the residual
/// stream at full scale when it conducts again. Moved by a grain, the moment reaches its input.
pub fn toward(m: i128, g: i128, rate: u32) -> i128 {
    let step = release(g - m, rate);
    m + if step == 0 { (g - m).signum() } else { step }
}
