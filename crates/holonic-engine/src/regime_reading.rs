//! What a walk's material admits, read as a pair of octave counts and never as a quotient.
//!
//! # Why this exists
//!
//! `docs/canon/THE_INFORMATION_ENGINE.md` §1.1 states that the cooling stroke's middle row —
//! condensation with a certified remainder — has a **termination condition set by the material**,
//! and §4 item 0 records that this body carries no organ that reads it. An engine that cannot say
//! what its material admits is choosing strokes blind.
//!
//! The instrument is not new. It was built in the frozen laboratory as
//! `experiments/fractal/dimension_probe.py`, calibrated on eight deterministic walks of known
//! dimension and then turned on the machine's own lattice, and its doctrine is
//! `archive/reference/holobrochos-a07ff376/src/holobrochos/CANON/FRACTAL.md` §3. This module is the port,
//! and it ports the **discipline** as carefully as the arithmetic.
//!
//! # The reading
//!
//! A walk accumulates a signed deviation `S` over a span. `FRACTAL.md` §3:
//!
//! ```text
//!   d̂ = rank(span) / rank(|S|)
//! ```
//!
//! read as *path packed per unit of crossing*: `S ~ span^(1/d)`. A headed walk has `|S|` growing
//! like the span, so the two octave counts track and `d̂ → 1`. A plane-filling walk has `|S|`
//! growing like the square root, so `d̂ → 2`. A walk that cancels — `+1, −1, +1, …` — has `|S|`
//! bounded while the span runs away, so `d̂ → ∞`.
//!
//! # Three disciplines this port inherits, and each is a defect if dropped
//!
//! **1. The quotient is never formed.** [`RegimeReading`] holds the two counts and nothing else.
//! The verdict is the integer compare `span < 2 · deviation`; the decimal exists only in
//! [`RegimeReading::centi_face`], which is display and is documented as display. Brandon caught the
//! probe's first draft computing `d̂` by float division and had it purged the same night. Ordering
//! two readings uses the same cross-multiplication
//! [`crate::cuda_aperture::CarrierDilation::cmp_against`] uses — *"it never divides and never
//! rounds."*
//!
//! **2. It is not called `rank`.** In this crate `rank` already means a dimension or a cardinality
//! in six public places, including [`crate::inertia::Inertia::rank`]. The probe's `rank` is a
//! **bit-length**, so it is [`octaves`] here — the count of doublings a magnitude spans, which is
//! what `CLAUDE.md` §2b already calls the octave. Note also that
//! [`crate::corpus_census::density_band`] is bit-length **minus one** and `u64`-only, so the tree
//! already carries two conventions; `FRACTAL.md:110-112` flags exactly this and says the displayed
//! threshold sits near `d̂ ≈ 1.9–2.1` when the conventions differ.
//!
//! **3. It measures and never gates.** `CLAUDE.md` §13 rule 2: a scalar that measures is lawful, a
//! scalar that governs is not. The probe itself gates nowhere — its only control flow is the
//! sampling schedule. But the laboratory ring that used the same compare labelled its dark class
//! *"looked past, free"* and did not process it, so **meter and gate were one organ where this was
//! built**, and a port that does not separate them inherits the gate. Nothing in this module
//! branches on a [`Regime`]. It is returned and never consulted.
//!
//! # What this does NOT return
//!
//! `docs/canon/THE_INFORMATION_ENGINE.md` §1.1 names three regimes — `SETTLED`, `BENT`, `GROWING`. This
//! compare separates **two**, and inventing a third would be a partition the material never
//! supplied. `BENT` is a curvature reading and belongs to `contact_gluing::hinge_deficits`, not to a
//! dimension meter. What this organ detects is the `GROWING` case specifically, and
//! [`Regime::PlaneFilling`] is named for what it measures rather than for the regime it suggests.
//!
//! And per `research/records/2026-08-13_SCALING_IS_REPETITION_OF_AN_INVARIANT_UNIT…`, a
//! `PlaneFilling` reading does **not** say no compact representative exists. It says the
//! representative cannot be a sample: `H.0256`'s Hutchinson fixed point is compact, so the
//! representative is the **generator**. This organ licenses looking for one; it supplies none, and
//! `H.0256`'s separation hypotheses are checked nowhere.

use core::cmp::Ordering;

use num_bigint::{BigInt, BigUint};

/// The count of doublings a magnitude spans — the leading-bit position, never a dimension.
///
/// `octaves(0) = octaves(1) = 1`, `octaves(2) = 2`, `octaves(4) = 3`. Zero and one share a reading
/// because a magnitude that never left its first octave has spanned one, and because the ratio's
/// denominator may not be zero.
pub fn octaves(magnitude: &BigUint) -> u64 {
    magnitude.bits().max(1)
}

/// What the compare separates. **Returned and never consulted by this module.**
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Regime {
    /// `span < 2 · deviation`. The deviation keeps pace with the span, so the walk is headed and
    /// carries an axis. `FRACTAL.md` §3 calls this FOUND.
    Headed,
    /// `span ≥ 2 · deviation`. The deviation falls behind, so the walk fills rather than heads.
    /// `FRACTAL.md` §3 calls this DARK and gives the threshold's ground: **Brownian paths have
    /// Hausdorff dimension exactly 2**, `proved-standard`, so `d̂ = 2` is the chance boundary.
    PlaneFilling,
}

impl Regime {
    pub const fn name(self) -> &'static str {
        match self {
            Self::Headed => "headed",
            Self::PlaneFilling => "plane-filling",
        }
    }
}

/// One reading, held as the octave pair and never divided.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RegimeReading {
    span_octaves: u64,
    deviation_octaves: u64,
}

impl RegimeReading {
    /// Read a walk's accumulated signed deviation against the span it accumulated over.
    ///
    /// The sign of `deviation` is discarded **here and only here**, because the reading is about how
    /// far the walk got from its origin and not which way. That is a declared face, not a deletion
    /// of the turn: the walk's own hand remains in the material this was read from.
    pub fn read(deviation: &BigInt, span: &BigUint) -> Self {
        Self {
            span_octaves: octaves(span),
            deviation_octaves: octaves(&deviation.magnitude().clone()),
        }
    }

    /// Found a reading directly from two octave counts. Both are clamped to at least one, so the
    /// pair can never carry a zero denominator.
    pub const fn from_octaves(span_octaves: u64, deviation_octaves: u64) -> Self {
        Self {
            span_octaves: if span_octaves == 0 { 1 } else { span_octaves },
            deviation_octaves: if deviation_octaves == 0 {
                1
            } else {
                deviation_octaves
            },
        }
    }

    pub const fn span_octaves(&self) -> u64 {
        self.span_octaves
    }

    pub const fn deviation_octaves(&self) -> u64 {
        self.deviation_octaves
    }

    /// The verdict, by integer compare. No quotient is formed.
    pub const fn regime(&self) -> Regime {
        if self.span_octaves < 2 * self.deviation_octaves {
            Regime::Headed
        } else {
            Regime::PlaneFilling
        }
    }

    /// Order two readings **without forming either quotient** — `a₁·d₂` against `a₂·d₁`, the same
    /// cross-multiplication [`crate::cuda_aperture::CarrierDilation::cmp_against`] uses. Widened to
    /// `u128` so the product cannot wrap.
    pub fn cmp_against(&self, other: &Self) -> Ordering {
        let left = u128::from(self.span_octaves) * u128::from(other.deviation_octaves);
        let right = u128::from(other.span_octaves) * u128::from(self.deviation_octaves);
        left.cmp(&right)
    }

    /// **Display only.** The ratio in centi-units by integer division — `FRACTAL.md`'s *"the eyes'
    /// costume, never float arithmetic"*. No construction may read this; it exists so a printed
    /// table can be compared against the laboratory's calibration.
    pub const fn centi_face(&self) -> u64 {
        (self.span_octaves * 100) / self.deviation_octaves
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::Sign;

    /// Accumulate a walk and read it at each declared span.
    ///
    /// **The generator is indexed from zero**, and that is not a convention: the Thue–Morse
    /// sequence `(−1)^popcount(k)` sums to exactly zero over a complete `2^n` block **starting at
    /// zero**, because `k` and `k + 2^(n−1)` differ by one bit and therefore cancel in pairs. Run
    /// from one instead and the block is no longer complete — the sum lands on `−2` at span `1024`,
    /// its octave count moves `1 → 2`, and the reading halves. The calibration caught exactly that
    /// off-by-one in this port, which is what a table of known dimensions is for.
    fn walk(steps: impl Fn(u64) -> i64, spans: &[u64]) -> Vec<(u64, RegimeReading)> {
        let mut deviation = BigInt::from(0);
        let mut readings = Vec::new();
        let mut next = 0usize;
        let last = *spans.last().expect("a declared span");
        for k in 0..last {
            deviation += BigInt::from(steps(k));
            let taken = k + 1;
            if next < spans.len() && taken == spans[next] {
                readings.push((
                    taken,
                    RegimeReading::read(&deviation, &BigUint::from(taken)),
                ));
                next += 1;
            }
        }
        readings
    }

    /// The laboratory's own sampling schedule: `4^5 … 4^10`.
    fn declared_spans() -> Vec<u64> {
        (5..=10).map(|k| 4u64.pow(k)).collect()
    }

    /// **The calibration. These rows are the falsifier.**
    ///
    /// Every walk is deterministic and its dimension is known in advance, so a defect in the meter
    /// shows up as a moved row rather than as a judgement call. The expected centi-faces are the
    /// laboratory's measured table at
    /// `a07ff376:src/holobrochos/experiments/fractal/output.txt`.
    #[test]
    fn the_calibration_walks_reproduce_the_laboratory_table() {
        let spans = declared_spans();

        // BALLISTIC: +1 forever. The deviation IS the span, so the octaves coincide.
        let ballistic = walk(|_| 1, &spans);
        for (_, reading) in &ballistic {
            assert_eq!(reading.centi_face(), 100);
            assert_eq!(reading.regime(), Regime::Headed);
        }

        // THE GRANNY: +1, −1 forever. The deviation is bounded while the span runs away.
        let granny = walk(|k| if k % 2 == 1 { 1 } else { -1 }, &spans);
        let granny_faces: Vec<u64> = granny.iter().map(|(_, r)| r.centi_face()).collect();
        assert_eq!(granny_faces, vec![1100, 1300, 1500, 1700, 1900, 2100]);
        for (_, reading) in &granny {
            assert_eq!(reading.regime(), Regime::PlaneFilling);
        }

        // THUE–MORSE: ±1 by popcount parity. The laboratory measured it IDENTICAL to the granny,
        // which is the sharpest row in the table — two structurally unrelated walks landing on one
        // reading is what a meter that could not discriminate would also produce, so the rows that
        // separate below are what make this one evidence rather than coincidence.
        let thue_morse = walk(|k| if k.count_ones() % 2 == 1 { -1 } else { 1 }, &spans);
        let thue_faces: Vec<u64> = thue_morse.iter().map(|(_, r)| r.centi_face()).collect();
        assert_eq!(thue_faces, granny_faces);

        // RUDIN–SHAPIRO: −1 when the count of adjacent `11` pairs is odd. Its partial sums grow
        // like √n with a loud constant, so it climbs toward the dimension-2 seam without reaching
        // it. **This is the discriminating row** — the exact figures are the laboratory's, and a
        // port that is faithful in shape but wrong in arithmetic would land near them and not on
        // them.
        let rudin_shapiro = walk(
            |k| {
                if (k & (k >> 1)).count_ones() % 2 == 1 {
                    -1
                } else {
                    1
                }
            },
            &spans,
        );
        let rudin_faces: Vec<u64> = rudin_shapiro.iter().map(|(_, r)| r.centi_face()).collect();
        assert_eq!(rudin_faces, vec![183, 185, 187, 188, 190, 190]);
        for (_, reading) in &rudin_shapiro {
            assert_eq!(reading.regime(), Regime::Headed);
        }

        // BIASED 3:1 — three up, one down. A headed walk that settles just above the ballistic axis.
        let biased = walk(|k| if k % 4 == 0 { -1 } else { 1 }, &spans);
        let biased_faces: Vec<u64> = biased.iter().map(|(_, r)| r.centi_face()).collect();
        assert_eq!(biased_faces, vec![110, 108, 107, 106, 105, 105]);
        for (_, reading) in &biased {
            assert_eq!(reading.regime(), Regime::Headed);
        }

        // AND THE DISCRIMINATION IS THE POINT: the five walks must not all read alike.
        let ballistic_face = ballistic[0].1.centi_face();
        assert_ne!(ballistic_face, granny_faces[0]);
        assert_ne!(ballistic_face, rudin_shapiro[0].1.centi_face());
        assert_ne!(rudin_shapiro[0].1.centi_face(), granny_faces[0]);
    }

    /// The quotient is never formed, and ordering two readings does not divide.
    #[test]
    fn two_readings_order_without_dividing() {
        let coarse = RegimeReading::from_octaves(11, 1);
        let fine = RegimeReading::from_octaves(11, 7);
        assert_eq!(coarse.cmp_against(&fine), Ordering::Greater);
        assert_eq!(fine.cmp_against(&coarse), Ordering::Less);
        assert_eq!(coarse.cmp_against(&coarse), Ordering::Equal);

        // Two readings whose centi-faces collide still order strictly, because the pair carries more
        // than its printed face: 300/200 and 3/2 both display 150.
        let big = RegimeReading::from_octaves(300, 200);
        let small = RegimeReading::from_octaves(3, 2);
        assert_eq!(big.centi_face(), small.centi_face());
        assert_eq!(big.cmp_against(&small), Ordering::Equal);
    }

    /// The denominator can never be zero, and a zero deviation is a reading rather than a refusal.
    #[test]
    fn a_walk_that_returned_to_its_origin_still_reads() {
        let reading = RegimeReading::read(&BigInt::from(0), &BigUint::from(1024u64));
        assert_eq!(reading.deviation_octaves(), 1);
        assert_eq!(reading.span_octaves(), 11);
        assert_eq!(reading.regime(), Regime::PlaneFilling);
        assert_eq!(reading.centi_face(), 1100);
    }

    /// `octaves` is a bit-length, and it is deliberately NOT the tree's other convention.
    #[test]
    fn octaves_is_the_bit_length_and_not_the_density_band() {
        assert_eq!(octaves(&BigUint::from(0u64)), 1);
        assert_eq!(octaves(&BigUint::from(1u64)), 1);
        assert_eq!(octaves(&BigUint::from(2u64)), 2);
        assert_eq!(octaves(&BigUint::from(3u64)), 2);
        assert_eq!(octaves(&BigUint::from(4u64)), 3);
        // `corpus_census::density_band` is this minus one. The two must never be confused, which is
        // exactly the differing-convention caveat `FRACTAL.md:110-112` records.
        assert_eq!(
            octaves(&BigUint::from(4u64)) - 1,
            crate::corpus_census::density_band(4)
        );
    }

    /// The sign is discarded at the read and nowhere else.
    #[test]
    fn the_reading_is_of_the_magnitude_and_the_hand_does_not_move_it() {
        let span = BigUint::from(4096u64);
        let forward = RegimeReading::read(&BigInt::from(255), &span);
        let backward = RegimeReading::read(&BigInt::new(Sign::Minus, vec![255]), &span);
        assert_eq!(forward, backward);
    }
}
