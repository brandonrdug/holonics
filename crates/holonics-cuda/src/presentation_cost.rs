//! **C5 — cost as a receipt, and the receiver-relative Pareto frontier of presentations.**
//!
//! A [`CostReceipt`] carries five exact natural coordinates — `bytes`, `decode_work`,
//! `update_work`, `certificate_work`, `residual` — and **each one carries the provenance that
//! produced it**. A coordinate is a count that was measured off actual data or derived from
//! measured counts by a stated rule, or else it is explicitly `Declared` by an exterior party and
//! marked as not accounted. There is no way to construct a coordinate without saying which.
//!
//! The representation objective
//! `C(P;q) = a*bytes + b*decode + c*update + d*certificate + e*residual`
//! is [`Weighting::objective`]. It is **one receiver of the receipt**, a declared nonnegative
//! weight vector, and never the identity of a presentation. The target is the
//! receiver-relative [`pareto_frontier`]: the antichain of nondominated presentations under the
//! product partial order on the five coordinates.
//!
//! # Kolmogorov minimality is not claimed
//!
//! Nothing here defines, computes, approximates or bounds the shortest program for an object.
//! Kolmogorov complexity is incomputable; no minimal encoding is asserted anywhere in this module.
//! [`pareto_frontier`] returns the nondominated members of a **finite declared family**, and
//! `PresentationCost.lean::frontier_has_no_least_point` proves that in general no member of a
//! frontier is below all the others — so "the optimal presentation" is not a well-formed request
//! at a receiver that weighs more than one axis.
//!
//! # The paired Lean owner
//!
//! `formal/elementary-holonics/ElementaryHolonics/Foundation/PresentationCost.lean`, namespace
//! `Soma.Holonics.Foundation.PresentationCost`, which names this file. The citation is
//! bidirectional on purpose.
//!
//! | Lean declaration | Rust owner |
//! |---|---|
//! | `Axis`, `sum_axis` | [`Axis`], [`Axis::ALL`] |
//! | `Provenance`, `Provenance.Accounted` | [`Provenance`], [`Provenance::is_accounted`] |
//! | `Counted` | [`Counted`] |
//! | `CostReceipt`, `CostReceipt.vector` | [`CostReceipt`], [`CostReceipt::vector`] |
//! | `Dominates`, `dominates_refl`, `dominates_trans` | [`CostReceipt::dominates`] |
//! | `dominates_antisymm_vector`, `dominates_antisymm_fails_on_receipts` | [`CostReceipt::dominates`] on equal vectors with different provenance |
//! | `StrictlyDominates`, `strictlyDominates_iff` | [`CostReceipt::strictly_dominates`] |
//! | `CostReceipt.compose`, `compose_vector` | [`CostReceipt::compose`] |
//! | `serial_receipt_balance` (cites `ReceiverCodeCost.serial_boundary_balance`) | [`CostReceipt::compose`]'s derived provenance names that owner |
//! | `IsFrontierPoint`, `frontier`, `mem_frontier` | [`pareto_frontier`]; [`frontier_by`] generalizes it to a declared three-valued axis comparison, whose `Undecided` case has no Lean counterpart (implemented-exact, tested) |
//! | `exists_frontier_dominating`, `frontier_nonempty` | [`frontier_dominator`] |
//! | `Weighting`, `Weighting.objective`, `Weighting.Positive` | [`Weighting`], [`Weighting::objective`], [`Weighting::is_positive`] |
//! | `minimizer_isFrontierPoint` | [`scalar_minimizers`] and its invariant test |
//! | `unsupported_not_minimizer` | [`chord_family`] and `unsupported_point_is_selected_by_no_weighting` |
//! | `Reparameterization`, `frontier_reparameterization_invariant` | [`Reparameterization`], [`Reparameterization::apply`] |
//! | `scalar_minimizer_not_reparameterization_invariant` | the same test, on the scalar side |
//! | `codeBits`, `codeBits_mul_le` | [`code_bits`] |
//! | `codeBits_residual_comp_le` | [`CostReceipt::compose`]'s residual axis, with [`code_bits`] on the product |
//! | `CostedTower`, `costBoundedByRefinementRoute_of_route` | [`RouteComparison`] |
//! | `padicCostedTower`, `padicStepReceipt`, `costBoundedByRefinementRoute_padic` | [`CostedResidueTower`], [`CostedResidueTower::receipt`], [`CostedResidueTower::route_comparison`] |
//! | `squaredGapReceipt`, `no_costedTower_with_squaredGapReceipt` | [`squared_gap_receipt`] |
//! | `costBoundedByRefinementRoute_is_caller_decided` | [`RouteComparison::is_caller_decided`] |
//!
//! # Hostile input
//!
//! Every constructor that takes an exterior declaration checks it against what was actually read
//! and refuses by name rather than panicking, and nothing allocates from a declaration:
//! [`Weighting::declare`] refuses a negative weight, [`AtomSiteMeasurement::check_declared_rows`]
//! refuses a row count that disagrees with the measurement, and [`decode_wire_record_count`]
//! refuses a declared atom count whose record span overflows or disagrees with the buffer it was
//! handed — `checked_mul` throughout, and the buffer is never resized to fit the declaration.
//!
//! # The measured M5 presentations
//!
//! [`measure_atom_site_block`] and [`m5_presentations`] produce receipts for three real
//! presentations of one real object — the `_atom_site` table of an mmCIF deposit — with every byte
//! count measured from the actual file. See `presentation_cost/tests.rs`.

use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::fmt;

use num_bigint::BigUint;
use num_traits::{One, Zero};
use holonics::geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use holonics::restriction::tower::{ResidueTower, SplittingRefusal};

// -------------------------------------------------------------------------------------------
// Axes
// -------------------------------------------------------------------------------------------

/// The five declared coordinates of a presentation receipt.
///
/// Lean counterpart: `Foundation/PresentationCost.lean::Axis`. The receipt never sums them;
/// summing them is what a [`Weighting`] does, and that is a receiver reading.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum Axis {
    /// Octets the presentation occupies.
    Bytes,
    /// Elementary steps to decode the object from the presentation.
    DecodeWork,
    /// Elementary steps to re-present after one admitted change.
    UpdateWork,
    /// Elementary steps to verify that the presentation decodes to the object.
    CertificateWork,
    /// Code size, in bits, of the residual the presentation does not carry.
    Residual,
}

impl Axis {
    /// Every axis, in the order the objective writes them.
    ///
    /// Lean counterpart: the `Fintype Axis` instance and `sum_axis`.
    pub const ALL: [Axis; 5] = [
        Axis::Bytes,
        Axis::DecodeWork,
        Axis::UpdateWork,
        Axis::CertificateWork,
        Axis::Residual,
    ];

    /// The axis's position in [`Axis::ALL`], by **exhaustive match**.
    ///
    /// Lean counterpart: the `Fintype Axis` instance's enumeration. Every positional lookup in this
    /// module goes through here, so adding a coordinate to `Axis` is a compile error at this match
    /// rather than a silent read of the `Bytes` slot — which is what a `position(..).unwrap_or(0)`
    /// search would have done.
    pub const fn index(self) -> usize {
        match self {
            Axis::Bytes => 0,
            Axis::DecodeWork => 1,
            Axis::UpdateWork => 2,
            Axis::CertificateWork => 3,
            Axis::Residual => 4,
        }
    }

    /// The axis's name, for receipts and refusals.
    pub fn name(self) -> &'static str {
        match self {
            Axis::Bytes => "bytes",
            Axis::DecodeWork => "decodeWork",
            Axis::UpdateWork => "updateWork",
            Axis::CertificateWork => "certificateWork",
            Axis::Residual => "residual",
        }
    }
}

impl fmt::Display for Axis {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.name())
    }
}

// -------------------------------------------------------------------------------------------
// Provenance
// -------------------------------------------------------------------------------------------

/// How one coordinate was obtained.
///
/// Lean counterpart: `Foundation/PresentationCost.lean::Provenance`. A [`CostReceipt`] cannot be
/// formed without one of these per coordinate; that is what makes it a receipt rather than a tuple
/// of numbers.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum Provenance {
    /// Counted directly off the presented data by the named instrument.
    Measured {
        /// What did the counting.
        instrument: String,
    },
    /// Computed from measured counts by the named rule.
    Derived {
        /// The rule, written out so the count can be recomputed.
        rule: String,
    },
    /// Supplied by the named exterior party. Not a measurement; carried, never trusted.
    Declared {
        /// Who declared it.
        declarer: String,
    },
}

impl Provenance {
    /// A coordinate is **accounted** when it was measured or derived from measurements.
    ///
    /// Lean counterpart: `Provenance.Accounted`.
    pub fn is_accounted(&self) -> bool {
        matches!(self, Provenance::Measured { .. } | Provenance::Derived { .. })
    }
}

/// One coordinate: an exact natural count together with the provenance that produced it.
///
/// Lean counterpart: `Foundation/PresentationCost.lean::Counted`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Counted {
    /// The exact count.
    pub count: BigUint,
    /// Where the count came from.
    pub provenance: Provenance,
}

impl Counted {
    /// A count produced by a named instrument reading actual data.
    pub fn measured(count: impl Into<BigUint>, instrument: impl Into<String>) -> Self {
        Self {
            count: count.into(),
            provenance: Provenance::Measured {
                instrument: instrument.into(),
            },
        }
    }

    /// A count computed from measured counts by a named rule.
    pub fn derived(count: impl Into<BigUint>, rule: impl Into<String>) -> Self {
        Self {
            count: count.into(),
            provenance: Provenance::Derived { rule: rule.into() },
        }
    }

    /// A count an exterior party supplied. Carried, and marked not accounted.
    pub fn declared(count: impl Into<BigUint>, declarer: impl Into<String>) -> Self {
        Self {
            count: count.into(),
            provenance: Provenance::Declared {
                declarer: declarer.into(),
            },
        }
    }
}

// -------------------------------------------------------------------------------------------
// The receipt
// -------------------------------------------------------------------------------------------

/// A cost receipt for one presentation of one object at one receiver.
///
/// Lean counterpart: `Foundation/PresentationCost.lean::CostReceipt`. This is not a score;
/// [`Weighting::objective`] is the score and it is a receiver reading *of* this receipt.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CostReceipt {
    /// What is being presented, and how. Testimony, never an identity.
    pub presentation: String,
    /// Octets occupied.
    pub bytes: Counted,
    /// Steps to decode the object from the presentation.
    pub decode_work: Counted,
    /// Steps to re-present after one admitted change.
    pub update_work: Counted,
    /// Steps to verify the presentation decodes to the object.
    pub certificate_work: Counted,
    /// Code size, in bits, of what the presentation does not carry.
    pub residual: Counted,
}

impl CostReceipt {
    /// The coordinate carried at one axis.
    ///
    /// Lean counterpart: `CostReceipt.counted`.
    pub fn coordinate(&self, axis: Axis) -> &Counted {
        match axis {
            Axis::Bytes => &self.bytes,
            Axis::DecodeWork => &self.decode_work,
            Axis::UpdateWork => &self.update_work,
            Axis::CertificateWork => &self.certificate_work,
            Axis::Residual => &self.residual,
        }
    }

    /// The exact count at one axis.
    pub fn count(&self, axis: Axis) -> &BigUint {
        &self.coordinate(axis).count
    }

    /// The exact cost vector: the counts, with provenance forgotten.
    ///
    /// Lean counterpart: `CostReceipt.vector`. Forgetting provenance is exactly what makes
    /// dominance a partial order rather than an equality — see
    /// `dominates_antisymm_fails_on_receipts`.
    pub fn vector(&self) -> [BigUint; 5] {
        [
            self.bytes.count.clone(),
            self.decode_work.count.clone(),
            self.update_work.count.clone(),
            self.certificate_work.count.clone(),
            self.residual.count.clone(),
        ]
    }

    /// Every coordinate was measured or derived.
    ///
    /// Lean counterpart: `CostReceipt.Accounted`.
    pub fn is_accounted(&self) -> bool {
        Axis::ALL
            .iter()
            .all(|axis| self.coordinate(*axis).provenance.is_accounted())
    }

    /// `self` costs no more than `other` on **every** axis: the product partial order.
    ///
    /// Lean counterpart: `Dominates`, with `dominates_refl`, `dominates_trans` and
    /// `dominates_antisymm_vector`.
    pub fn dominates(&self, other: &Self) -> bool {
        Axis::ALL
            .iter()
            .all(|axis| self.count(*axis) <= other.count(*axis))
    }

    /// No more on every axis, and strictly less somewhere.
    ///
    /// Lean counterpart: `StrictlyDominates`, `strictlyDominates_iff`.
    pub fn strictly_dominates(&self, other: &Self) -> bool {
        self.dominates(other)
            && Axis::ALL
                .iter()
                .any(|axis| self.count(*axis) < other.count(*axis))
    }

    /// Neither dominates the other.
    pub fn incomparable_with(&self, other: &Self) -> bool {
        !self.dominates(other) && !other.dominates(self)
    }

    /// Serial composition of receipts: coordinatewise addition, every coordinate marked derived and
    /// naming the law that licenses it.
    ///
    /// Lean counterpart: `CostReceipt.compose` and `compose_vector`. The law is
    /// `Foundation/ReceiverCodeCost.lean::serial_boundary_balance` — serial code costs add and the
    /// endpoint potentials cancel at the joined boundary — instantiated at
    /// `PresentationCost.lean::serial_receipt_balance`. It is cited here, never rebuilt.
    ///
    /// On the residual axis this is an **upper bound and not always the composite's own residual**:
    /// `Foundation/ContinuingTower.lean::Transition.comp` makes the composite residual the *pair*
    /// of component residuals, so the residual fibre multiplies and its code size is subadditive
    /// ([`code_bits`], and `PresentationCost.lean::codeBits_residual_comp_lt_witness` for a case
    /// where the inequality is strict).
    pub fn compose(&self, second: &Self) -> Self {
        let rule = format!(
            "serial composition of {:?} then {:?}; \
             ReceiverCodeCost.serial_boundary_balance via PresentationCost.serial_receipt_balance",
            self.presentation, second.presentation
        );
        let add = |axis: Axis| Counted {
            count: self.count(axis) + second.count(axis),
            provenance: Provenance::Derived { rule: rule.clone() },
        };
        Self {
            presentation: format!("{} ∘ {}", second.presentation, self.presentation),
            bytes: add(Axis::Bytes),
            decode_work: add(Axis::DecodeWork),
            update_work: add(Axis::UpdateWork),
            certificate_work: add(Axis::CertificateWork),
            residual: add(Axis::Residual),
        }
    }
}

/// The exact code size of a residual fibre of `n` values: the least `k` with `n <= 2^k`.
///
/// Lean counterpart: `Foundation/PresentationCost.lean::codeBits`, which is `Nat.clog 2`.
/// `code_bits(0) = code_bits(1) = 0`: a residual that carries nothing owes no bits.
/// `codeBits_mul_le` is the subadditivity over a product of residual fibres, which is what the
/// carrier's composed residual needs.
pub fn code_bits(fibre: &BigUint) -> BigUint {
    if fibre <= &BigUint::one() {
        return BigUint::zero();
    }
    // The least k with fibre <= 2^k is the bit length of fibre - 1.
    BigUint::from((fibre - BigUint::one()).bits())
}

// -------------------------------------------------------------------------------------------
// The weighting: one receiver of the receipt
// -------------------------------------------------------------------------------------------

/// A declared nonnegative weight per axis. This is the receiver; [`Weighting::objective`] is its
/// reading.
///
/// Lean counterpart: `Foundation/PresentationCost.lean::Weighting`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Weighting {
    /// The declared name of the receiver whose weights these are.
    pub receiver: String,
    weights: [Rat; 5],
}

impl Weighting {
    /// Declare a weighting. A negative weight is refused by name: a negative weight would make a
    /// *more* expensive presentation score better, which is not a cost reading.
    pub fn declare(
        receiver: impl Into<String>,
        weights: [Rat; 5],
    ) -> Result<Self, CostRefusal> {
        for (at, weight) in weights.iter().enumerate() {
            if weight < &Rat::zero() {
                return Err(CostRefusal::NegativeWeight {
                    axis: Axis::ALL[at],
                    weight: weight.to_string(),
                });
            }
        }
        Ok(Self {
            receiver: receiver.into(),
            weights,
        })
    }

    /// The weight at one axis. The slot is [`Axis::index`], an exhaustive match, so a new axis is
    /// a compile error rather than a silent read of the `Bytes` weight.
    pub fn weight(&self, axis: Axis) -> &Rat {
        &self.weights[axis.index()]
    }

    /// Every axis carries weight.
    ///
    /// Lean counterpart: `Weighting.Positive`, the hypothesis of `minimizer_isFrontierPoint`.
    pub fn is_positive(&self) -> bool {
        self.weights.iter().all(|weight| weight > &Rat::zero())
    }

    /// `C(P;q) = a*bytes + b*decode + c*update + d*certificate + e*residual`, exactly.
    ///
    /// Lean counterpart: `Weighting.objective`. One number: a receiver reading of the receipt,
    /// never the identity of the presentation.
    pub fn objective(&self, receipt: &CostReceipt) -> Rat {
        Axis::ALL.iter().fold(Rat::zero(), |total, axis| {
            total + self.weight(*axis) * Rat::from_integer(receipt.count(*axis).clone().into())
        })
    }
}

// -------------------------------------------------------------------------------------------
// The frontier
// -------------------------------------------------------------------------------------------

/// A labelled presentation carrying its receipt. The label is what the receipt is *of*; the
/// receipt never replaces it.
///
/// Lean counterpart: `Foundation/PresentationCost.lean::ParetoPoint`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ParetoPoint {
    /// Which presentation this is.
    pub label: String,
    /// What it cost.
    pub receipt: CostReceipt,
}

impl ParetoPoint {
    /// Pair a label with a receipt.
    pub fn new(label: impl Into<String>, receipt: CostReceipt) -> Self {
        Self {
            label: label.into(),
            receipt,
        }
    }
}

/// The indices of the nondominated members of a finite declared family: the Pareto frontier.
///
/// Lean counterpart: `Foundation/PresentationCost.lean::frontier`, whose `IsFrontierPoint` is the
/// same predicate. `frontier_nonempty` and `frontier_isAntichain` are the invariants; both are
/// tested here.
///
/// A family with repeated cost vectors keeps **every** copy: equal vectors do not strictly dominate
/// each other, and two presentations with equal counts are still two presentations.
pub fn pareto_frontier(points: &[ParetoPoint]) -> Vec<usize> {
    frontier_by(points.len(), Axis::ALL.len(), &|rival, candidate, axis| {
        let axis = Axis::ALL[axis];
        match points[rival].receipt.count(axis).cmp(points[candidate].receipt.count(axis)) {
            Ordering::Less => AxisComparison::Better,
            Ordering::Equal => AxisComparison::Equal,
            Ordering::Greater => AxisComparison::Worse,
        }
    })
}

/// How a rival stands to a candidate at one declared axis of a generalized frontier.
///
/// [definition] Lifted out of [`pareto_frontier`] 2026-09-18 when item **B8** of
/// `docs/plans/THE_BIOLOGICAL_ECOLOGY_INSTANTIATES_THE_CARRIER.md` needed the same rule over a
/// design's **receiver-reading vector** rather than over the five cost axes. The reading axes
/// carry an exact comparison that can be *undecided* — a plural reading whose exact intervals
/// overlap without coinciding, or an axis a receiver did not read — which the five `BigUint` cost
/// coordinates never are. The rule is the same rule, and a second spelling of a Pareto front is
/// how a pre-check and a guard drift apart, so [`pareto_frontier`] is expressed **through**
/// [`frontier_by`] rather than beside it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AxisComparison {
    /// The rival is strictly better here.
    Better,
    /// The rival is strictly worse here.
    Worse,
    /// The two readings are exactly equal here.
    Equal,
    /// The exact comparison does not decide. **This never licenses a discard.**
    Undecided,
}

/// The nondominated members of a finite declared family under a finite declared axis family whose
/// per-axis comparison is exact and three-valued.
///
/// `compare(rival, candidate, axis)` says how the rival stands to the candidate at that axis. A
/// rival strictly dominates the candidate when it is [`AxisComparison::Better`] or
/// [`AxisComparison::Equal`] at **every** axis and `Better` at at least one — so a single
/// [`AxisComparison::Undecided`] anywhere leaves the candidate on the frontier. Openness is never
/// resolved by a default here, exactly as `physical_constraint_grading` never resolves it.
///
/// [definition] `members` and `axes` are the family's and the declaration's own counts, and the
/// comparison closure owns the indexing: this performs `members² · axes` comparisons and bounds
/// nothing itself. Every caller checks that product with checked arithmetic against its own
/// declared ceiling before calling — `design_selection::DesignFamily::frontier` does, and
/// [`pareto_frontier`] derives both counts from the slice it was handed.
///
/// Lean counterpart: `Foundation/PresentationCost.lean::IsFrontierPoint`, whose `∀ j ∈ S, ¬ w j < w i`
/// is this predicate at a decided axis family.
pub fn frontier_by(
    members: usize,
    axes: usize,
    compare: &dyn Fn(usize, usize, usize) -> AxisComparison,
) -> Vec<usize> {
    (0..members)
        .filter(|candidate| {
            !(0..members)
                .any(|rival| rival != *candidate && dominates_by(rival, *candidate, axes, compare))
        })
        .collect()
}

/// Whether the rival is better or equal at every declared axis and strictly better at one.
fn dominates_by(
    rival: usize,
    candidate: usize,
    axes: usize,
    compare: &dyn Fn(usize, usize, usize) -> AxisComparison,
) -> bool {
    let mut strict = false;
    for axis in 0..axes {
        match compare(rival, candidate, axis) {
            AxisComparison::Better => strict = true,
            AxisComparison::Equal => {}
            AxisComparison::Worse | AxisComparison::Undecided => return false,
        }
    }
    strict
}

/// A frontier point that dominates the given member of the family, or `None` when the index is out
/// of range.
///
/// Lean counterpart: `exists_frontier_dominating`, which proves such a point always exists for a
/// member of a finite family.
pub fn frontier_dominator(points: &[ParetoPoint], at: usize) -> Option<usize> {
    let target = points.get(at)?;
    let frontier = pareto_frontier(points);
    frontier
        .into_iter()
        .find(|candidate| points[*candidate].receipt.dominates(&target.receipt))
}

/// Every index minimizing the objective over the family, in ascending order.
///
/// Lean counterpart: the hypothesis of `minimizer_isFrontierPoint`. With a strictly positive
/// weighting every returned index is on [`pareto_frontier`]; the converse fails, and
/// `unsupported_not_minimizer` is the witness.
pub fn scalar_minimizers(points: &[ParetoPoint], weighting: &Weighting) -> Vec<usize> {
    let Some(best) = points
        .iter()
        .map(|point| weighting.objective(&point.receipt))
        .min()
    else {
        return Vec::new();
    };
    (0..points.len())
        .filter(|at| weighting.objective(&points[*at].receipt) == best)
        .collect()
}

// -------------------------------------------------------------------------------------------
// Monotone reparameterization
// -------------------------------------------------------------------------------------------

/// One axis's declared unit change: an exact map on counts, which the declarer asserts is strictly
/// monotone. Lean counterpart: one component of `Reparameterization.map`.
pub type UnitChange = Box<dyn Fn(&BigUint) -> BigUint + Send + Sync>;

/// A strictly monotone change of unit on each coordinate, independently. Reporting decode work in
/// operation-pairs rather than operations, or bytes after a fixed framing, is such a change.
///
/// Lean counterpart: `Foundation/PresentationCost.lean::Reparameterization`, and
/// `frontier_reparameterization_invariant` — the frontier survives it — against
/// `scalar_minimizer_not_reparameterization_invariant` — the scalar minimizer does not.
///
/// Strict monotonicity is a **declared obligation** of the supplied maps, exactly as in Lean where
/// it is a field. [`Reparameterization::check_strict_monotone_on`] returns a receipt that the
/// declaration held over a declared sample, and returns the witnessing pair when it did not.
pub struct Reparameterization {
    /// The declared name of the unit change.
    pub name: String,
    maps: [UnitChange; 5],
}

impl fmt::Debug for Reparameterization {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("Reparameterization")
            .field("name", &self.name)
            .finish_non_exhaustive()
    }
}

impl Reparameterization {
    /// Declare a unit change, one map per axis.
    pub fn declare(name: impl Into<String>, maps: [UnitChange; 5]) -> Self {
        Self {
            name: name.into(),
            maps,
        }
    }

    /// The unit change at one axis. The slot is [`Axis::index`], an exhaustive match, so a new axis
    /// is a compile error rather than a silent application of the `Bytes` unit change.
    pub fn map(&self, axis: Axis, count: &BigUint) -> BigUint {
        (self.maps[axis.index()])(count)
    }

    /// Reparameterize a receipt. Every coordinate becomes derived and names the unit change, so a
    /// reparameterized measurement never passes itself off as the original measurement.
    ///
    /// Lean counterpart: `Reparameterization.onVector`.
    pub fn apply(&self, receipt: &CostReceipt) -> CostReceipt {
        let rule = |axis: Axis| {
            format!(
                "unit change {:?} applied to the {} coordinate of {:?}",
                self.name,
                axis.name(),
                receipt.presentation
            )
        };
        let change = |axis: Axis| Counted {
            count: self.map(axis, receipt.count(axis)),
            provenance: Provenance::Derived { rule: rule(axis) },
        };
        CostReceipt {
            presentation: format!("{} [{}]", receipt.presentation, self.name),
            bytes: change(Axis::Bytes),
            decode_work: change(Axis::DecodeWork),
            update_work: change(Axis::UpdateWork),
            certificate_work: change(Axis::CertificateWork),
            residual: change(Axis::Residual),
        }
    }

    /// Reparameterize a whole family, keeping the labels.
    pub fn apply_family(&self, points: &[ParetoPoint]) -> Vec<ParetoPoint> {
        points
            .iter()
            .map(|point| ParetoPoint::new(point.label.clone(), self.apply(&point.receipt)))
            .collect()
    }

    /// Check the declared strict monotonicity over a declared ascending sample, returning the
    /// witnessing pair when it fails. This is a receipt over the sample, not a proof over all of
    /// `ℕ`; the proof lives in Lean as the `strictMono` field.
    pub fn check_strict_monotone_on(&self, sample: &[BigUint]) -> Result<usize, CostRefusal> {
        let mut checked = 0usize;
        for axis in Axis::ALL {
            for window in sample.windows(2) {
                let (low, high) = (&window[0], &window[1]);
                if low >= high {
                    return Err(CostRefusal::SampleNotAscending {
                        low: low.to_string(),
                        high: high.to_string(),
                    });
                }
                if self.map(axis, low) >= self.map(axis, high) {
                    return Err(CostRefusal::ReparameterizationNotStrictlyMonotone {
                        axis,
                        low: low.to_string(),
                        high: high.to_string(),
                    });
                }
                checked += 1;
            }
        }
        Ok(checked)
    }
}

// -------------------------------------------------------------------------------------------
// The route comparison: `Migration.CostBoundedByRefinementRoute`, discharged and sharpened
// -------------------------------------------------------------------------------------------

/// The comparison `Foundation/ContinuingTower.lean::Migration.CostBoundedByRefinementRoute` states
/// and leaves open: the direct migration's receipt against the "refine to a common chart, then
/// restrict back" route's composed receipt.
///
/// Lean counterparts: `PresentationCost.lean::costBoundedByRefinementRoute_of_route` (it holds for
/// a costed tower whose restrictions satisfy `route_dominates`, and the proof is that law),
/// `costBoundedByRefinementRoute_is_caller_decided` (as originally stated, over a caller-supplied
/// route cost, it records a choice of the caller and not a property of the migration) and
/// `swapMigration_route_isEmpty` (where the migration connects incomparable charts there is no
/// route at all, so nothing is compared).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RouteComparison {
    /// The direct migration's own receipt.
    pub direct: CostReceipt,
    /// The receipts of the route's steps, in the order they run. Empty means **there is no route**,
    /// which is a different return from "the route is free".
    pub route: Vec<CostReceipt>,
}

impl RouteComparison {
    /// The route's composed receipt, or `None` when there is no route.
    ///
    /// Lean counterpart: the right-hand side of `costBoundedByRefinementRoute_of_route`, built with
    /// [`CostReceipt::compose`].
    pub fn route_receipt(&self) -> Option<CostReceipt> {
        let mut steps = self.route.iter();
        let first = steps.next()?.clone();
        Some(steps.fold(first, |total, step| total.compose(step)))
    }

    /// Whether the direct receipt is bounded by the route's composed receipt, or `None` when there
    /// is no route to compare with.
    ///
    /// `None` is the honest return for a migration that connects incomparable charts: by
    /// `twoCharts_no_common_refinement` there may be no common refinement at all, so the right-hand
    /// cost has nothing to measure. A caller that wants a `bool` there is asking the wrong
    /// question.
    pub fn is_bounded(&self) -> Option<bool> {
        self.route_receipt()
            .map(|route| self.direct.dominates(&route))
    }

    /// The same statement over an arbitrary caller-supplied route cost: with one supplied cost it
    /// holds and with another it fails, for one fixed direct receipt.
    ///
    /// Lean counterpart: `costBoundedByRefinementRoute_is_caller_decided`. This returns the two
    /// witnessing comparisons, so the emptiness of the open statement is executable rather than
    /// asserted.
    pub fn is_caller_decided(direct: &CostReceipt) -> (RouteComparison, RouteComparison) {
        let inflate = |axis: Axis| Counted {
            count: direct.count(axis) + BigUint::one(),
            provenance: Provenance::Declared {
                declarer: "a caller choosing a route cost that makes the comparison hold".into(),
            },
        };
        let deflate = |_axis: Axis| Counted {
            count: BigUint::zero(),
            provenance: Provenance::Declared {
                declarer: "a caller choosing a route cost that makes the comparison fail".into(),
            },
        };
        let holds = CostReceipt {
            presentation: "caller-supplied route cost, generous".into(),
            bytes: inflate(Axis::Bytes),
            decode_work: inflate(Axis::DecodeWork),
            update_work: inflate(Axis::UpdateWork),
            certificate_work: inflate(Axis::CertificateWork),
            residual: inflate(Axis::Residual),
        };
        let fails = CostReceipt {
            presentation: "caller-supplied route cost, mean".into(),
            bytes: deflate(Axis::Bytes),
            decode_work: deflate(Axis::DecodeWork),
            update_work: deflate(Axis::UpdateWork),
            certificate_work: deflate(Axis::CertificateWork),
            residual: deflate(Axis::Residual),
        };
        (
            RouteComparison {
                direct: direct.clone(),
                route: vec![holds],
            },
            RouteComparison {
                direct: direct.clone(),
                route: vec![fails],
            },
        )
    }
}

// -------------------------------------------------------------------------------------------
// A costed tower: receipts the tower itself determines
// -------------------------------------------------------------------------------------------

/// A [`ResidueTower`] whose restrictions carry the receipt the tower itself determines.
///
/// Lean counterpart: `PresentationCost.lean::padicCostedTower` — a `CostedTower` on
/// `ContinuingTower.lean::padicTower`, whose `route_dominates` field is *derived* there
/// (`padicStepReceipt_route`) rather than assumed. Nothing here is supplied by a caller except the
/// declared carrier aperture: every coordinate of [`Self::receipt`] is read off the tower's own
/// [`ResidueTower::split_fibre`], and [`Self::route_comparison`] builds both sides of
/// `Migration.CostBoundedByRefinementRoute` from that one function.
///
/// The five coordinates, at a gap of `d = fine - coarse` charts (Lean: `padicStepReceipt`):
///
/// | axis | count | why |
/// |---|---|---|
/// | `bytes` | `d * digit_octets(base)` | one digit-octet per dropped base-`p` digit |
/// | `decode_work` | `d` | one Horner step per dropped digit |
/// | `update_work` | `d` | one digit rewritten per dropped digit |
/// | `certificate_work` | `d + 1` | one digit compared each, after one header check |
/// | `residual` | `code_bits(coset_count)` | the fibre `split_fibre` counted, `base ^ d` exactly |
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CostedResidueTower {
    tower: ResidueTower,
    ceiling_bits: u128,
}

impl CostedResidueTower {
    /// Cost the restrictions of `tower`, refusing any chart whose carrier is wider than
    /// `ceiling_bits`. The aperture is declared by the caller and checked before anything of that
    /// width is built; see [`ResidueTower::split_fibre`].
    pub fn new(tower: ResidueTower, ceiling_bits: u128) -> Self {
        Self {
            tower,
            ceiling_bits,
        }
    }

    /// The tower being costed.
    pub fn tower(&self) -> &ResidueTower {
        &self.tower
    }

    /// The declared carrier aperture.
    pub fn ceiling_bits(&self) -> u128 {
        self.ceiling_bits
    }

    /// The octets one base-`p` digit occupies when it is written out: `⌈code_bits(base) / 8⌉`.
    ///
    /// Lean counterpart: `PresentationCost.lean::digitOctets`. Exact natural division; no float.
    pub fn digit_octets(&self) -> BigUint {
        (code_bits(self.tower.base()) + BigUint::from(7u32)) / BigUint::from(8u32)
    }

    /// The receipt of restricting from chart `fine` to chart `coarse`, computed from the tower.
    ///
    /// Lean counterpart: `padicCostedTower.receipt`, which is `padicStepReceipt p (j - i)`. The
    /// `residual` coordinate is `code_bits` of the fibre cardinality the tower's own
    /// [`ResidueTower::split_fibre`] returns — Lean's `Nat.card` of `padicRestrictTransition`'s
    /// residual, whose value `padicFibre_card` fixes at `p ^ k`.
    pub fn receipt(&self, coarse: u32, fine: u32) -> Result<CostReceipt, SplittingRefusal> {
        let splitting = self
            .tower
            .split_fibre(coarse, fine, &BigUint::zero(), self.ceiling_bits)?;
        let gap = BigUint::from(fine - coarse);
        Ok(CostReceipt {
            presentation: format!(
                "restriction of the residue tower base {} from chart {fine} to chart {coarse}",
                self.tower.base()
            ),
            bytes: Counted::derived(
                &gap * self.digit_octets(),
                "one digit-octet per dropped base-p digit",
            ),
            decode_work: Counted::derived(gap.clone(), "one Horner step per dropped digit"),
            update_work: Counted::derived(gap.clone(), "one digit rewritten per dropped digit"),
            certificate_work: Counted::derived(
                gap + BigUint::one(),
                "one digit compared per dropped digit, after one header check per presentation",
            ),
            residual: Counted::derived(
                code_bits(splitting.coset_count()),
                "code_bits of ResidueTower::split_fibre's exact coset count, which is the residual \
                 fibre of ContinuingTower.lean::padicRestrictTransition",
            ),
        })
    }

    /// The route comparison at `coarse ≤ middle ≤ fine`: the direct restriction against the
    /// two-step route, **with every receipt taken from this tower**.
    ///
    /// Lean counterpart: `PresentationCost.lean::costBoundedByRefinementRoute_padic`, which is
    /// `costBoundedByRefinementRoute_of_route` at `padicCostedTower`. Because both sides are the
    /// tower's own receipts, [`RouteComparison::is_bounded`] returns `Some(true)` at every triple —
    /// that is the executable form of the `route_dominates` field, and
    /// [`squared_gap_receipt`] is the assignment for which it does not hold.
    pub fn route_comparison(
        &self,
        coarse: u32,
        middle: u32,
        fine: u32,
    ) -> Result<RouteComparison, SplittingRefusal> {
        Ok(RouteComparison {
            direct: self.receipt(coarse, fine)?,
            route: vec![self.receipt(middle, fine)?, self.receipt(coarse, middle)?],
        })
    }
}

/// A receipt assignment that is **not** a costed tower's: it bills the *square* of the chart gap.
///
/// Lean counterpart: `PresentationCost.lean::squaredGapReceipt`, with
/// `squaredGapReceipt_route_fails` and `no_costedTower_with_squaredGapReceipt` — no `CostedTower`
/// over any ℕ-indexed tower can carry these receipts, because its own `route_dominates` at charts
/// `0 ≤ 1 ≤ 2` would say `4 ≤ 2`. Every coordinate is `Declared`, and says so: this is a receiver's
/// billing rule, not a measurement.
pub fn squared_gap_receipt(coarse: u32, fine: u32) -> CostReceipt {
    let gap = BigUint::from(fine.saturating_sub(coarse));
    let declarer = "a receiver billing the square of the chart gap";
    CostReceipt {
        presentation: format!("squared-gap billing from chart {fine} to chart {coarse}"),
        bytes: Counted::declared(&gap * &gap, declarer),
        decode_work: Counted::declared(BigUint::zero(), declarer),
        update_work: Counted::declared(BigUint::zero(), declarer),
        certificate_work: Counted::declared(BigUint::zero(), declarer),
        residual: Counted::declared(BigUint::zero(), declarer),
    }
}

// -------------------------------------------------------------------------------------------
// The measured M5 presentations
// -------------------------------------------------------------------------------------------

/// The exact counts an `_atom_site` block actually carries, measured by scanning the deposited
/// text. Nothing here is declared: every field is a count this module produced.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AtomSiteMeasurement {
    /// Exterior lineage of the source, retained as testimony.
    pub source_lineage: String,
    /// Bytes of the whole `_atom_site` block: its `loop_`, its header lines and its data rows.
    pub block_bytes: u64,
    /// Bytes of the data rows alone.
    pub row_bytes: u64,
    /// Bytes of the first data row, including its newline.
    pub first_row_bytes: u64,
    /// How many `_atom_site.` header lines the block declares.
    pub header_columns: u64,
    /// How many data rows the block carries.
    pub rows: u64,
    /// ASCII digit characters in the data rows.
    pub digit_characters: u64,
}

impl AtomSiteMeasurement {
    /// Check an exterior declaration of the row count against what was measured. Nothing is
    /// allocated from the declaration and no count is adjusted to agree with it.
    pub fn check_declared_rows(&self, declared: u64) -> Result<(), CostRefusal> {
        if declared == self.rows {
            Ok(())
        } else {
            Err(CostRefusal::DeclaredRowsDisagree {
                declared,
                measured: self.rows,
            })
        }
    }
}

/// Measure the `_atom_site` block of an mmCIF text: its byte extents, its row count and its digit
/// characters.
///
/// The decoding owner of mmCIF is `physical_intake::mmcif::StructurePresentation`; this function
/// does no decoding at all, only counting, and [`m5_presentations`] uses both.
pub fn measure_atom_site_block(
    source_lineage: impl Into<String>,
    text: &str,
) -> Result<AtomSiteMeasurement, CostRefusal> {
    let source_lineage = source_lineage.into();
    let mut offset: u64 = 0;
    let mut block_start: Option<u64> = None;
    let mut header_columns: u64 = 0;
    let mut rows: u64 = 0;
    let mut row_bytes: u64 = 0;
    let mut first_row_bytes: u64 = 0;
    let mut digit_characters: u64 = 0;
    let mut state = 0u8; // 0 before the loop, 1 in the headers, 2 in the rows, 3 finished.

    for line in text.split_inclusive('\n') {
        let width = line.len() as u64;
        let body = line.trim_end_matches(['\n', '\r']).trim();
        match state {
            0 => {
                if body == "loop_" {
                    block_start = Some(offset);
                    header_columns = 0;
                    state = 1;
                }
            }
            1 => {
                if body.starts_with('_') {
                    if body.starts_with("_atom_site.") {
                        header_columns += 1;
                    } else if header_columns == 0 {
                        // A different loop; look for the next `loop_`.
                        state = 0;
                        block_start = None;
                    }
                } else if header_columns == 0 {
                    state = 0;
                    block_start = None;
                    if body == "loop_" {
                        block_start = Some(offset);
                        state = 1;
                    }
                } else if body.is_empty() {
                    // A blank line inside the block is not a row; keep scanning.
                } else {
                    state = 2;
                    rows += 1;
                    row_bytes += width;
                    first_row_bytes = width;
                    digit_characters +=
                        body.chars().filter(|ch| ch.is_ascii_digit()).count() as u64;
                }
            }
            2 => {
                if body == "#" || body == "loop_" || body.starts_with('_') || body.is_empty() {
                    state = 3;
                } else {
                    rows += 1;
                    row_bytes += width;
                    digit_characters +=
                        body.chars().filter(|ch| ch.is_ascii_digit()).count() as u64;
                }
            }
            _ => {}
        }
        if state == 3 {
            let start = block_start.unwrap_or(0);
            return Ok(AtomSiteMeasurement {
                source_lineage,
                block_bytes: offset.saturating_sub(start),
                row_bytes,
                first_row_bytes,
                header_columns,
                rows,
                digit_characters,
            });
        }
        offset += width;
    }

    match (block_start, rows) {
        (Some(start), rows) if rows > 0 => Ok(AtomSiteMeasurement {
            source_lineage,
            block_bytes: offset.saturating_sub(start),
            row_bytes,
            first_row_bytes,
            header_columns,
            rows,
            digit_characters,
        }),
        _ => Err(CostRefusal::NoAtomSiteBlock {
            source_lineage: source_lineage.clone(),
        }),
    }
}

/// Bytes of one scaled-integer wire coordinate record: six `i64` interval words.
pub const WIRE_COORDINATE_BYTES: u64 = 48;
/// Bytes of one wire record's residue ordinal: one `i32`.
pub const WIRE_ORDINAL_BYTES: u64 = 4;
/// Fixed-width fields one wire record decodes: six interval words and the residue ordinal.
pub const WIRE_FIXED_FIELDS: u64 = 7;
/// Fields of the object each atom row carries: chain, ordinal, monomer, label, x, y, z.
pub const OBJECT_FIELDS_PER_ATOM: u64 = 7;

/// Check a declared atom count against a wire buffer without allocating from the declaration.
///
/// The record span is computed with `checked_mul`, so a declaration large enough to overflow is
/// refused by name rather than wrapping; the buffer is never resized to fit.
pub fn decode_wire_record_count(
    buffer_len: usize,
    declared_atoms: u64,
    identifier_bytes: u64,
) -> Result<u64, CostRefusal> {
    let fixed = WIRE_COORDINATE_BYTES
        .checked_add(WIRE_ORDINAL_BYTES)
        .and_then(|per| per.checked_mul(declared_atoms))
        .ok_or(CostRefusal::DeclaredExtentOverflows {
            declared_atoms,
            identifier_bytes,
        })?;
    let span = fixed
        .checked_add(identifier_bytes)
        .ok_or(CostRefusal::DeclaredExtentOverflows {
            declared_atoms,
            identifier_bytes,
        })?;
    if span == buffer_len as u64 {
        Ok(declared_atoms)
    } else {
        Err(CostRefusal::DeclaredExtentDisagrees {
            declared_span: span,
            buffer_len: buffer_len as u64,
        })
    }
}




// -------------------------------------------------------------------------------------------
// The formal witnesses, executable
// -------------------------------------------------------------------------------------------

/// A receipt whose every coordinate is declared, for use as a formal witness only.
///
/// Lean counterpart: `Foundation/PresentationCost.lean::witnessReceipt`.
pub fn witness_receipt(name: &str, counts: [u64; 5]) -> CostReceipt {
    let declared = |at: usize| Counted::declared(counts[at], format!("formal witness {name}"));
    CostReceipt {
        presentation: format!("formal witness {name}"),
        bytes: declared(0),
        decode_work: declared(1),
        update_work: declared(2),
        certificate_work: declared(3),
        residual: declared(4),
    }
}

/// The three-point family of `PresentationCost.lean::chordFamily`: a byte-free corner, a
/// decode-free corner, and a balanced presentation strictly above the chord between them.
///
/// All three are on the frontier; no weighting that weighs either varying axis selects the third.
/// That is `unsupported_not_minimizer`, and it is the formal reason a scalar score cannot stand in
/// for the frontier.
pub fn chord_family() -> Vec<ParetoPoint> {
    vec![
        ParetoPoint::new("chordLeft", witness_receipt("chordLeft", [0, 10, 0, 0, 0])),
        ParetoPoint::new("chordRight", witness_receipt("chordRight", [10, 0, 0, 0, 0])),
        ParetoPoint::new(
            "unsupported",
            witness_receipt("unsupported", [6, 6, 0, 0, 0]),
        ),
    ]
}

// -------------------------------------------------------------------------------------------
// Refusals
// -------------------------------------------------------------------------------------------

/// Every way this module refuses rather than guessing.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum CostRefusal {
    /// A weight was negative, so a costlier presentation would score better.
    #[error("the weight {weight} declared at axis {axis} is negative")]
    NegativeWeight {
        /// Which axis.
        axis: Axis,
        /// The declared weight, rendered.
        weight: String,
    },
    /// The text carries no `_atom_site` loop.
    #[error("{source_lineage} carries no _atom_site block to measure")]
    NoAtomSiteBlock {
        /// Exterior lineage of the text.
        source_lineage: String,
    },
    /// An exterior declaration of the row count disagreed with the measurement.
    #[error("the declared {declared} _atom_site rows disagree with the {measured} measured")]
    DeclaredRowsDisagree {
        /// What the exterior party declared.
        declared: u64,
        /// What was measured.
        measured: u64,
    },
    /// The scan and the decoder disagree about how many rows the block carries.
    #[error("the block scan counted {scanned_rows} rows and the intake decoded {decoded_atoms}")]
    RowsDisagreeWithIntake {
        /// What `measure_atom_site_block` counted.
        scanned_rows: u64,
        /// What `StructurePresentation::parse` decoded.
        decoded_atoms: u64,
    },
    /// A declared wire extent overflows the exact arithmetic.
    #[error(
        "the declared {declared_atoms} atoms with {identifier_bytes} identifier bytes overflow the \
         exact record span"
    )]
    DeclaredExtentOverflows {
        /// The declared atom count.
        declared_atoms: u64,
        /// The declared identifier byte total.
        identifier_bytes: u64,
    },
    /// A declared wire extent disagrees with the buffer actually supplied.
    #[error("the declared record span {declared_span} disagrees with the {buffer_len} byte buffer")]
    DeclaredExtentDisagrees {
        /// The span the declaration implies.
        declared_span: u64,
        /// The bytes actually supplied.
        buffer_len: u64,
    },
    /// The sample offered to a monotonicity check was not ascending, so it decides nothing.
    #[error("the monotonicity sample is not ascending at {low} followed by {high}")]
    SampleNotAscending {
        /// The earlier sample.
        low: String,
        /// The later sample.
        high: String,
    },
    /// A declared unit change reordered two counts, so it is not a reparameterization.
    #[error("the unit change at axis {axis} does not keep {low} below {high}")]
    ReparameterizationNotStrictlyMonotone {
        /// Which axis.
        axis: Axis,
        /// The smaller count.
        low: String,
        /// The larger count.
        high: String,
    },
    /// The mmCIF decoding owner refused the text.
    #[error("{source_lineage} was refused by physical_intake::mmcif: {detail}")]
    IntakeRefused {
        /// Exterior lineage of the text.
        source_lineage: String,
        /// The decoder's own refusal, rendered.
        detail: String,
    },
}

#[cfg(test)]
#[path = "presentation_cost/tests.rs"]
mod tests;
