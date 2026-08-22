//! The junction law over integer populations — the substrate face of the interface coefficient.
//!
//! ```text
//!   Γ  =  (R − M) : (R + M)              carried as a pair, never divided
//!   T  =  4 R M   : (R + M)²             carried as a pair, never divided
//!   service rounds = ⌈(R + M)² / (4 R M)⌉   the only division in the law
//! ```
//!
//! # Both of those pairs are entries of one matrix — 2026-08-15
//!
//! The junction's whole transport is the two-component interface matrix, over integers:
//!
//! ```text
//!         1    [ R+M   R−M ]                        R+M                     R−M
//!   M =  ───   [           ]        diagonal  =  ───────── ,  off-diagonal  ─────────
//!        2R    [ R−M   R+M ]                        2R                       2R
//! ```
//!
//! and the two pairs above are **read off it** rather than declared beside it:
//!
//! ```text
//!   Γ  =  M₂₁ / M₁₁  =  (R − M) : (R + M)
//!   τ  =  1   / M₁₁  =  2R      : (R + M)
//!   T  =  det M / M₁₁²          =  4RM : (R + M)²          det M = M : R
//! ```
//!
//! `Γ` and `τ` were two declarations that happened to agree with a matrix nobody had written; they
//! are now one object with two faces, and [`CountedCrossing::transfer_pair`] is the object.
//! `holonic_engine::traversible_chain` carries the same matrix over exact rationals and checks the
//! two charts against each other entry by entry over a swept material.
//!
//! This is Fresnel at normal incidence, the transmission-line reflection coefficient, and the Smith
//! chart — one law. `holonic_engine::analytic_field` computes it over exact rationals and
//! `holonic_engine::traversible_chain` checks the two charts against each other over a swept
//! material. It lives **here** because it is pure integer arithmetic over populations and because
//! two crates that cannot see each other both need it: `holonic-engine` for transport, and
//! `soma/membrane` for the co-present seam closure, whose candidate admission is the same junction.
//!
//! # Why this is the right carrier for an admission
//!
//! A count cannot bound an admission: on measured material every finite count refused at exactly
//! `count + 1`, and the unbounded setting made the omitted population zero by construction. The
//! mismatch between what arrives and what a site offers is a **ratio**, so it crosses a frame
//! boundary where a count cannot — and it dilates, which is what a queue is.
//!
//! **The mismatch is symmetric, and that is correct physics.** A narrow front meeting a wide site
//! and a wide front meeting a narrow one are both reflections; what reflects is capacity nobody
//! carried. Under-filling a surface is a mismatch exactly as over-filling it is.

use serde::{Deserialize, Serialize};

/// A junction between an arriving population and what a site offers it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct CountedCrossing {
    incident: u64,
    transmitted: u64,
}

impl CountedCrossing {
    /// Meet a site. Both populations must be positive: a site offering nothing admits no traveling
    /// section, and that is a **terminus by type** rather than a small number to compare against a
    /// bound.
    pub const fn meet(incident: u64, transmitted: u64) -> Option<Self> {
        if incident == 0 || transmitted == 0 {
            return None;
        }
        Some(Self {
            incident,
            transmitted,
        })
    }

    pub const fn incident(self) -> u64 {
        self.incident
    }

    pub const fn transmitted(self) -> u64 {
        self.transmitted
    }

    /// The interface transfer matrix over integers, as `((diagonal, off-diagonal), denominator)`.
    ///
    /// Both entries share the denominator `2R`, so the matrix is carried as three integers and
    /// **never divided**. The matrix is symmetric — `M₁₁ = M₂₂` and `M₁₂ = M₂₁` — which is not a
    /// storage convenience: it is the condition under which `T = 1 − Γ²`, and the engine's rational
    /// chart measures it rather than assuming it.
    ///
    /// `R + M` and `2R` are both positive, so the diagonal never vanishes and `τ = 1/M₁₁` is always
    /// defined at a real junction. The off-diagonal is zero exactly at a match.
    pub const fn transfer_pair(self) -> ((i128, i128), u128) {
        let incident = self.incident as i128;
        let transmitted = self.transmitted as i128;
        (
            (incident + transmitted, incident - transmitted),
            2 * self.incident as u128,
        )
    }

    /// `Γ = M₂₁ : M₁₁ = (R − M) : (R + M)`, a signed numerator over a positive denominator. Never
    /// divided.
    ///
    /// The shared `2R` cancels between the two matrix entries, which is why the reflection is a
    /// frame-crossing ratio while the entries themselves are not.
    pub const fn reflection_pair(self) -> (i128, u128) {
        let incident = self.incident as i128;
        let transmitted = self.transmitted as i128;
        (
            incident - transmitted,
            self.incident as u128 + self.transmitted as u128,
        )
    }

    /// `T = det M : M₁₁² = 4RM : (R + M)²`, as a pair. Never divided.
    pub const fn power_transmission_pair(self) -> (u128, u128) {
        let total = self.incident as u128 + self.transmitted as u128;
        (
            4 * (self.incident as u128) * (self.transmitted as u128),
            total * total,
        )
    }

    /// `⌈(R + M)² / (4RM)⌉` — how many passes the junction needs to carry what arrived.
    ///
    /// One at a match, growing as the populations separate. This is the traffic law's own quantity
    /// taken from the junction rather than authored: a site that transmits a third of what arrives
    /// needs three passes to carry it.
    pub const fn service_rounds(self) -> u128 {
        let (numerator, denominator) = self.power_transmission_pair();
        denominator.div_ceil(numerator)
    }

    /// Whether the populations match whole — the rebase case: one round, nothing reflected.
    pub const fn is_matched(self) -> bool {
        self.incident == self.transmitted
    }

    /// Whether this junction is crossed within a declared chronology horizon.
    ///
    /// The horizon is the **caller's** declaration and is reported in its receipt; the cost is the
    /// material's. What exceeds it defers — retained — and never refuses.
    pub const fn crosses_within(self, horizon: u64) -> bool {
        self.service_rounds() <= horizon as u128
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_match_costs_one_round_and_reflects_nothing() {
        let matched = CountedCrossing::meet(9, 9).expect("positive");
        assert!(matched.is_matched());
        assert_eq!(matched.service_rounds(), 1);
        assert_eq!(matched.reflection_pair(), (0, 18));
    }

    #[test]
    fn nothing_offered_is_a_terminus_rather_than_a_comparison() {
        assert_eq!(CountedCrossing::meet(9, 0), None);
        assert_eq!(CountedCrossing::meet(0, 9), None);
    }

    #[test]
    fn the_cost_is_symmetric_in_the_mismatch() {
        // A narrow front meeting a wide site costs exactly what a wide front meeting a narrow site
        // costs. What reflects is capacity nobody carried, in whichever direction the step runs.
        let narrow_into_wide = CountedCrossing::meet(1, 76).expect("positive");
        let wide_into_narrow = CountedCrossing::meet(76, 1).expect("positive");
        assert_eq!(
            narrow_into_wide.service_rounds(),
            wide_into_narrow.service_rounds()
        );
        // One lane meeting seventy-six: 4·76/77² transmitted, so twenty passes.
        assert_eq!(narrow_into_wide.service_rounds(), 20);
    }

    #[test]
    fn the_dilation_is_invariant_under_a_common_rescaling() {
        // The horizon law: the cost is a function of the RATIO, so scaling both populations leaves
        // it bit-identical. A count in this position could not do that.
        let plain = CountedCrossing::meet(10, 1).expect("positive");
        let scaled = CountedCrossing::meet(70, 7).expect("positive");
        assert_eq!(plain.service_rounds(), scaled.service_rounds());
        assert_eq!(
            plain.power_transmission_pair().0 as u128 * scaled.power_transmission_pair().1,
            scaled.power_transmission_pair().0 as u128 * plain.power_transmission_pair().1
        );
    }

    /// ★ The two declared pairs are entries of one matrix, over a swept material rather than at a
    /// chosen point — and the arm that makes it a test is the foil: reversing the junction leaves
    /// the power face **bit-identical** and negates the matrix's off-diagonal.
    ///
    /// That is the phase-object statement at integer grain. A receiver reading only `T` cannot tell
    /// a step up from a step down; the matrix can, because the returned amplitude is signed and the
    /// power face squares it away.
    #[test]
    fn the_declared_pairs_are_entries_of_the_transfer_matrix_and_the_power_face_is_blind_to_the_hand()
     {
        let mut swept = 0usize;
        let mut hands_that_differed = 0usize;
        for incident in 1..=16u64 {
            for transmitted in 1..=16u64 {
                let crossing = CountedCrossing::meet(incident, transmitted).expect("positive");
                let ((diagonal, off_diagonal), denominator) = crossing.transfer_pair();

                // Γ = M₂₁ : M₁₁ — the shared denominator cancels, which is the whole reason a
                // reflection crosses a frame boundary and an entry does not.
                assert_eq!(
                    crossing.reflection_pair(),
                    (off_diagonal, diagonal as u128),
                    "reflection is not the matrix ratio at ({incident}, {transmitted})"
                );

                // T = det M : M₁₁², cross-multiplied so nothing is divided. det M = M : R.
                let (share_numerator, share_denominator) = crossing.power_transmission_pair();
                let determinant_over_diagonal_square_numerator =
                    transmitted as u128 * denominator * denominator;
                let determinant_over_diagonal_square_denominator =
                    incident as u128 * (diagonal as u128) * (diagonal as u128);
                assert_eq!(
                    share_numerator * determinant_over_diagonal_square_denominator,
                    determinant_over_diagonal_square_numerator * share_denominator,
                    "power is not det M : M₁₁² at ({incident}, {transmitted})"
                );

                // The off-diagonal is zero exactly at a match, so `is_matched` is the matrix's own
                // reading and not a second declaration beside it.
                assert_eq!(off_diagonal == 0, crossing.is_matched());

                // THE FOIL. Reverse the junction: the power face does not move, the matrix does.
                let reversed = CountedCrossing::meet(transmitted, incident).expect("positive");
                assert_eq!(
                    reversed.power_transmission_pair(),
                    crossing.power_transmission_pair(),
                    "the power face must be blind to the hand at ({incident}, {transmitted})"
                );
                let ((reversed_diagonal, reversed_off), _) = reversed.transfer_pair();
                assert_eq!(reversed_diagonal, diagonal);
                assert_eq!(reversed_off, -off_diagonal);
                if off_diagonal != 0 {
                    hands_that_differed += 1;
                }
                swept += 1;
            }
        }
        assert_eq!(swept, 256);
        // And the foil actually fired: 240 of the 256 swept junctions are mismatched, so the
        // blindness is exhibited on real material rather than asserted over a matched population
        // where both faces agree trivially.
        assert_eq!(hands_that_differed, 240);
    }

    #[test]
    fn a_replicated_site_meeting_a_narrow_front_defers() {
        // The shape this exists for: a standing factor at multiplicity 500 meeting a front of 2 is
        // a mismatch, and most of it reflects. At a horizon of eight it defers rather than being
        // admitted whole.
        let replicated = CountedCrossing::meet(2, 500).expect("positive");
        assert!(replicated.service_rounds() > 8);
        assert!(!replicated.crosses_within(8));
        // A factor whose multiplicity matches the front crosses at one round.
        let matched = CountedCrossing::meet(2, 2).expect("positive");
        assert!(matched.crosses_within(8));
    }
}
