//! **The jet staircase: the finite jet ladder, its compatible continuations, and the passage
//! between difference orders and grains.**
//!
//! [definition] This module owns item **T8** of
//! `docs/plans/THE_TUBE_CARRIES_RELEASE_THROUGH_NECKS_FOLDS_AND_JUNCTIONS.md`. It is the
//! executable half of
//! `formal/elementary-holonics/ElementaryHolonics/Transport/JetStaircase.lean`, namespace
//! `Soma.Holonics.Transport.JetStaircase`.
//!
//! # The tube, the tower and the staircase
//!
//! [definition] The general object is the **tube**; a **tower** is what one instantaneous frame of
//! it shows; a **staircase** is its passage between grains or difference orders. This owner builds
//! the staircase. A neck station reads its order from here ([`FiniteJet::vanishing_order`]), and
//! `neck.rs` is the consumer.
//!
//! # The ladder
//!
//! [definition] A [`JetChart`] declares where the jet sits and at what step the difference chart
//! samples: a base point `x₀ ∈ Q` and a nonzero step `h ∈ Q`. A [`FiniteJet`] of order `r` in that
//! chart is the coefficient vector `c₀ … c_r` of
//!
//! ```text
//!   Σ_{i=0}^{r} c_i (x − x₀)^i ,
//! ```
//!
//! so `c_i = f⁽ⁱ⁾(x₀)/i!` and [`FiniteJet::derivative_values`] multiplies back by `i!`. The
//! coefficient convention is the one that stays inside `Q`: no factorial ever has to be inverted
//! on a deciding path.
//!
//! [proved-derived; implemented-exact] [`FiniteJet::restrict`] forgets the top order. That is the
//! ladder `J⁰ ← J¹ ← … ← J^r`, and [`jet_ladder`] returns every rung. It is a **projection with a
//! fibre, not an isomorphism**: the restriction to order `r−1` has a one-parameter fibre — the
//! discarded `c_r` — and [`JetLadder::restriction_fibre_dimension`] returns it. Lean:
//! `Transport/JetStaircase.lean::truncate_idem`, `Transport/JetStaircase.lean::truncate_comp`,
//! `Transport/JetStaircase.lean::truncate_fibre_is_the_top_coefficient`.
//!
//! # A finite jet retains several continuations, and the family is the return
//!
//! [definition] [`FiniteJet::compatible_polynomials`] returns the **affine space** of degree-`≤ d`
//! polynomials agreeing with the jet: a base point and `d − r` free directions, never a chosen
//! member. [`compatible_splines`] does the same over declared knots with a declared smoothness,
//! solving the exact linear system through
//! [`ExactRatMatrix::preimage_fibre`](holonics::exact_linear::ExactRatMatrix::preimage_fibre) so that
//! the particular solution and the kernel come from one reduction. Neither returns "the"
//! continuation: `PolynomialFamily::member` makes the caller declare the coordinates it wants.
//!
//! # Difference data and jet data are one triangular change of basis over `Q`
//!
//! [proved-derived; implemented-exact] For a declared step `h`, Newton's forward formula
//!
//! ```text
//!   f(x₀ + t h) = Σ_k Δ^k f(x₀) · C(t, k)
//! ```
//!
//! and `C(t,k) = (1/k!) Π_{j<k} (t − j)` give the coefficient of `(x − x₀)^i` as
//!
//! ```text
//!   c_i = Σ_{k ≥ i} Δ^k f(x₀) · s(k,i) / (k! · h^i) ,
//! ```
//!
//! where `s(k,i)` are the coefficients of the falling factorial — the signed Stirling numbers of
//! the first kind, built here by the exact integer recurrence rather than named. The matrix is
//! upper triangular with nonzero diagonal `1/(k! h^k)`, so it is invertible over `Q`;
//! [`DifferenceTable::to_jet`] is the map and [`jet_to_differences`] is its inverse — evaluation at
//! the nodes followed by differencing, which is the binomial matrix the other way. Lean states the
//! same change of basis on the Newton chart:
//! `Transport/JetStaircase.lean::coefficient_eq_iteratedDelta_at_zero`,
//! `Transport/JetStaircase.lean::delta_ofCoefficients` and
//! `Transport/JetStaircase.lean::iteratedDelta_ofCoefficients_eq_zero`, whose `Δ` **is**
//! `Foundation/HigherDifferenceTransport.lean::difference`
//! (`Transport/JetStaircase.lean::delta_eq_difference`).
//! [`DifferenceTable::reconstruction_residual`] is what the change of basis costs on input that is
//! **not** polynomial: the exact per-node difference between the source and the degree-`r`
//! reconstruction. It is never zero-by-assumption; it is computed.
//!
//! # The staircase proper
//!
//! [proved-derived; implemented-exact] **(i) Repeated integration with boundary data is an
//! encoding.** [`encode_sparse_differences`] stores the `k` boundary differences
//! `Δ⁰f(x₀) … Δ^{k−1}f(x₀)` together with the nonzero entries of the `Δ^k` column;
//! [`SparseDifferenceEncoding::decode`] rebuilds the sequence by repeated summation and the
//! reconstruction is exact. [`SparseDifferenceEncoding::cost`] reports the **actual** stored
//! rationals and stored bits against the raw sequence's, computed from the numerators and
//! denominators, never estimated. [`SparseDifferenceEncoding::factors_through`] checks that a
//! declared future receiver — a linear functional on the raw sequence — factors through the
//! encoding, by transporting it to the encoding's coordinates and re-pairing. Lean:
//! `Transport/JetStaircase.lean::rebuild_iteratedDelta`,
//! `Transport/JetStaircase.lean::integrate_delta`.
//!
//! [proved-derived; implemented-exact] **(ii) A grain changes the apparent difference order, and
//! by how much is computed per instance.** [`coarse_grain_order`] applies a declared
//! [`GrainMap`] — block sum or subsampling by `m` — and returns the **pair** of orders, the fine
//! one and the coarse one. There is no universal one-order drop and this owner asserts none:
//! subsampling a polynomial keeps its degree, block-summing a polynomial keeps its degree, and
//! block-summing a sequence that is not polynomial can lower, raise or leave the resolved order.
//! The reading is an [`OrderReading`], which says `NotResolvedWithin` when the sample is too short
//! to decide rather than reporting the largest `k` it happened to reach.
//!
//! [definition] **(iii) A joint is a spline knot whose order is the lowest derivative that
//! jumps.** [`PiecewisePolynomial::knot_reading`] computes it and returns
//! [`JointOrder`](crate::junction_law::JointOrder) — `junction_law`'s field, which that owner
//! declares and does not compute.
//!
//! [proved-derived; formal-checked] **(iv) The cusp is the first exact instance of a transport
//! raising difference order on an induced face.** [`cusp_staircase`] reproduces
//! `Millennium/HolonicInteractionExterior.lean`: the dual cusp `M₀` has square-zero defect
//! `N = M₀ − 1`, so a fibre orbit is affine in the time `n`; its second exterior power
//! `Λ²M₀ = cuspFluxTransport` has defect `D` with `D³ = 0` and `D² ≠ 0`, the orbit of `e₀∧e₁` is
//! `e01 + n e02 + n e13 + n² e23`, its second difference is exactly `2 e23` and its third
//! vanishes. Every one of those is **recomputed here over `Q`** from the two integer matrices,
//! not copied from the Lean statement. Lean names cited, in
//! `Millennium/HolonicInteractionExterior.lean`: `cuspFluxDefect_cubicZero`,
//! `cuspFluxDefect_squareNonzero`, `cuspFluxTransport_advancesOrbit`,
//! `cuspFluxOrbit_secondDifference`, `cuspFluxOrbit_thirdDifference`.
//!
//! # The Mahler/Iwasawa comparison, and where it stops
//!
//! [interpretation] `T = γ − 1` on the Iwasawa side and `Δ` on the jet side are the **same
//! operator on the polynomial chart**: `(γ − 1)f(n) = f(n+1) − f(n) = Δf(n)`, and
//! [`gamma_minus_one_is_forward_difference`] builds that map and checks it on declared data. So a
//! functor exists between the declared coefficient categories: Mahler coefficients of a function on
//! `N` **are** its finite differences at `0`, which [`mahler_coefficients`] computes, and on
//! polynomial functions the Mahler chart and the jet chart at step `1` agree exactly
//! ([`mahler_chart_agreement`]).
//!
//! [open] It stops at two places, and both are computed rather than asserted.
//! **(a)** The Iwasawa *level* filtration is by `ω_n = (1+T)^{p^n} − 1 = γ^{p^n} − 1`, which as an
//! operator on sequences is `f(n + p^k) − f(n)` and is **not** `Δ^{p^k}`;
//! [`omega_action_is_not_iterated_difference`] evaluates both on a declared sample and returns the
//! disagreement witness. A p-adic difference chart and a real time jet are therefore not
//! identified merely because both have levels.
//! **(b)** The functor is defined on polynomial functions; [`mahler_stop_witness`] returns the
//! exact node at which the degree-`r` Newton truncation of `n ↦ 2ⁿ` leaves the source, together
//! with the residual there. `2ⁿ` has every Mahler coefficient equal to `1`, so no finite jet
//! reproduces it and the truncation's residual is the return.
//!
//! # Floats
//!
//! [implemented-exact] No `f32` and no `f64` appears in this owner or in its tests. Every
//! coefficient, difference, residual and cost is exact over `Q` or an exact integer bit count.

use std::collections::BTreeMap;

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use holonics::exact_linear::{ExactLinearError, ExactRatMatrix};
use crate::iwasawa_tower::{IwasawaLevel, IwasawaRefusal, omega};
use crate::junction_law::JointOrder;
use crate::leader_quadrature::{LeaderError, LocalJet};

/// The wire schema this owner's serialized values carry.
pub const JET_STAIRCASE_SCHEMA: &str = "holonic-engine.jet-staircase.v1";

// ===============================================================================================
// ceilings — every declared size is bounded before the work it sizes
// ===============================================================================================

/// The largest jet order a declaration may name.
///
/// The Newton change of basis forms `k!` for every `k ≤ r` and `h^i` for every `i ≤ r`, so the
/// work is quadratic in the order and the integers grow factorially. The ceiling is checked in
/// [`FiniteJet::declare`], before the first coefficient is touched.
pub const JET_ORDER_CEILING: usize = 256;

/// The largest sample count a [`DifferenceTable`] may declare.
///
/// The difference triangle is `n(n+1)/2` exact rationals, so the ceiling bounds the triangle and
/// not merely the row. Checked in [`DifferenceTable::declare`].
pub const SAMPLE_CEILING: usize = 4096;

/// The largest polynomial degree a compatible family may be taken to.
pub const FAMILY_DEGREE_CEILING: usize = 512;

/// The largest number of interior knots a spline family may declare.
pub const KNOT_CEILING: usize = 256;

/// The largest linear system, in entries, that a spline family may raise.
///
/// The exact reduction is cubic in the smaller dimension; this bounds the matrix that enters it.
pub const SPLINE_WORK_CEILING: usize = 1 << 20;

// ===============================================================================================
// refusals
// ===============================================================================================

/// Every way this owner declines, by name.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum StaircaseRefusal {
    #[error("a jet chart's step is zero, so no difference chart is declared")]
    ZeroStep,
    #[error("a jet needs at least its value: an empty coefficient list is no jet")]
    EmptyJet,
    #[error("a difference table needs at least one sample")]
    EmptySamples,
    #[error("the declared order {declared} is past the ceiling {ceiling}")]
    OrderBeyondCeiling { declared: usize, ceiling: usize },
    #[error("the declared sample count {declared} is past the ceiling {ceiling}")]
    SamplesBeyondCeiling { declared: usize, ceiling: usize },
    #[error("the declared degree {declared} is past the ceiling {ceiling}")]
    DegreeBeyondCeiling { declared: usize, ceiling: usize },
    #[error("the declared knot count {declared} is past the ceiling {ceiling}")]
    KnotsBeyondCeiling { declared: usize, ceiling: usize },
    #[error("the declared spline system carries {declared} entries, past the ceiling {ceiling}")]
    SplineWorkBeyondCeiling { declared: usize, ceiling: usize },
    #[error("order {order} cannot be read from {samples} samples: it needs {needed}")]
    OrderExceedsSamples {
        order: usize,
        samples: usize,
        needed: usize,
    },
    #[error("a compatible family of degree {degree} cannot carry a jet of order {order}")]
    DegreeBelowJetOrder { degree: usize, order: usize },
    #[error("the order-zero jet has nothing above it to forget")]
    NothingToRestrict,
    #[error("two readings were taken in different charts: {left} against {right}")]
    ChartMismatch { left: String, right: String },
    #[error("a declared functional of length {declared} does not pair with {samples} samples")]
    FunctionalLengthMismatch { declared: usize, samples: usize },
    #[error("a grain of {grain} does not divide a sample of {samples}, and no partial block is minted")]
    GrainDoesNotDivide { grain: usize, samples: usize },
    #[error("a grain of zero is no grain")]
    ZeroGrain,
    #[error("the declared knots are not strictly increasing at position {at}")]
    KnotsNotIncreasing { at: usize },
    #[error("knot index {at} names no interior knot of the {declared} declared")]
    NoSuchKnot { at: usize, declared: usize },
    #[error("a piecewise polynomial over {knots} knots needs {needed} pieces, not {declared}")]
    PieceCountMismatch {
        knots: usize,
        needed: usize,
        declared: usize,
    },
    #[error("the declared spline constraints are inconsistent: no continuation exists")]
    NoCompatibleSpline,
    #[error("exact linear algebra declined: {0}")]
    Linear(#[from] ExactLinearError),
    #[error("the local-jet owner declined: {0}")]
    Leader(#[from] LeaderError),
    #[error("the Iwasawa tower declined: {0}")]
    Iwasawa(#[from] IwasawaRefusal),
}

// ===============================================================================================
// 1. the chart, the jet and the ladder
// ===============================================================================================

/// **Where a jet sits and at what step its difference chart samples.**
///
/// [definition] The base `x₀` and a **nonzero** step `h`. The step is part of the chart and not of
/// the reading: the same function has different finite differences at different steps, and the
/// change of basis to jet coefficients divides by `h^i`, so a zero step is refused at the
/// declaration rather than divided by later.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "JetChartWire")]
pub struct JetChart {
    lineage: String,
    base: Rat,
    step: Rat,
}

#[derive(Deserialize)]
struct JetChartWire {
    lineage: String,
    base: Rat,
    step: Rat,
}

impl TryFrom<JetChartWire> for JetChart {
    type Error = StaircaseRefusal;

    fn try_from(wire: JetChartWire) -> Result<Self, Self::Error> {
        Self::declare(wire.lineage, wire.base, wire.step)
    }
}

impl JetChart {
    /// Declare the chart. A zero step is refused by name.
    pub fn declare(
        lineage: impl Into<String>,
        base: Rat,
        step: Rat,
    ) -> Result<Self, StaircaseRefusal> {
        if step.is_zero() {
            return Err(StaircaseRefusal::ZeroStep);
        }
        Ok(Self {
            lineage: lineage.into(),
            base,
            step,
        })
    }

    /// The unit chart at the origin: base `0`, step `1`. The Mahler chart.
    pub fn unit(lineage: impl Into<String>) -> Self {
        Self {
            lineage: lineage.into(),
            base: Rat::zero(),
            step: Rat::one(),
        }
    }

    pub fn lineage(&self) -> &str {
        &self.lineage
    }

    pub fn base(&self) -> &Rat {
        &self.base
    }

    pub fn step(&self) -> &Rat {
        &self.step
    }

    /// The `index`-th node of this chart: `x₀ + index · h`.
    pub fn node(&self, index: usize) -> Rat {
        &self.base + &(&self.step * &Rat::from_integer(BigInt::from(index as u64)))
    }

    fn agrees_with(&self, other: &Self) -> Result<(), StaircaseRefusal> {
        if self.base == other.base && self.step == other.step {
            Ok(())
        } else {
            Err(StaircaseRefusal::ChartMismatch {
                left: self.lineage.clone(),
                right: other.lineage.clone(),
            })
        }
    }
}

/// **A finite jet of order `r` in a declared chart.**
///
/// [definition] The coefficients of `Σ_i c_i (x − x₀)^i`. Unlike
/// [`LocalJet`](crate::leader_quadrature::LocalJet), trailing zeros are **kept**: the order is a
/// declaration about how much of the ladder this reading occupies, and a jet of order 3 whose top
/// coefficient vanishes is a different rung from a jet of order 2. [`Self::local_jet`] hands the
/// data to the existing local-jet owner when the normalized form is what a caller wants.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "FiniteJetWire")]
pub struct FiniteJet {
    chart: JetChart,
    coefficients: Vec<Rat>,
}

#[derive(Deserialize)]
struct FiniteJetWire {
    chart: JetChart,
    coefficients: Vec<Rat>,
}

impl TryFrom<FiniteJetWire> for FiniteJet {
    type Error = StaircaseRefusal;

    fn try_from(wire: FiniteJetWire) -> Result<Self, Self::Error> {
        Self::declare(wire.chart, wire.coefficients)
    }
}

impl FiniteJet {
    /// Declare the jet. The order is bounded against [`JET_ORDER_CEILING`] before anything is
    /// sized by it, and an empty coefficient list is refused by name.
    pub fn declare(chart: JetChart, coefficients: Vec<Rat>) -> Result<Self, StaircaseRefusal> {
        if coefficients.is_empty() {
            return Err(StaircaseRefusal::EmptyJet);
        }
        let order = coefficients.len() - 1;
        if order > JET_ORDER_CEILING {
            return Err(StaircaseRefusal::OrderBeyondCeiling {
                declared: order,
                ceiling: JET_ORDER_CEILING,
            });
        }
        Ok(Self {
            chart,
            coefficients,
        })
    }

    /// Convenience: integer coefficients in a declared chart.
    pub fn from_integers(chart: JetChart, coefficients: &[i64]) -> Result<Self, StaircaseRefusal> {
        Self::declare(
            chart,
            coefficients
                .iter()
                .map(|value| Rat::from_integer(BigInt::from(*value)))
                .collect(),
        )
    }

    pub fn chart(&self) -> &JetChart {
        &self.chart
    }

    pub fn coefficients(&self) -> &[Rat] {
        &self.coefficients
    }

    /// The order: one less than the coefficient count.
    pub fn order(&self) -> usize {
        self.coefficients.len() - 1
    }

    /// **Forget the top order.** `J^r → J^{r−1}`, the ladder's one step. The order-zero jet has
    /// nothing above it and the restriction is refused rather than returning itself.
    pub fn restrict(&self) -> Result<Self, StaircaseRefusal> {
        if self.coefficients.len() <= 1 {
            return Err(StaircaseRefusal::NothingToRestrict);
        }
        let mut coefficients = self.coefficients.clone();
        coefficients.pop();
        Ok(Self {
            chart: self.chart.clone(),
            coefficients,
        })
    }

    /// The exact value of the jet polynomial at a point.
    pub fn evaluate(&self, point: &Rat) -> Rat {
        let offset = point - &self.chart.base;
        let mut total = Rat::zero();
        for coefficient in self.coefficients.iter().rev() {
            total = &total * &offset + coefficient;
        }
        total
    }

    /// The derivative of order `m` of the jet polynomial at a point, exactly.
    pub fn derivative_at(&self, order: usize, point: &Rat) -> Rat {
        let offset = point - &self.chart.base;
        let mut total = Rat::zero();
        for index in (order..self.coefficients.len()).rev() {
            let mut falling = BigInt::one();
            for step in 0..order {
                falling *= BigInt::from((index - step) as u64);
            }
            let term = &self.coefficients[index] * &Rat::from_integer(falling);
            total = &total * &offset + &term;
        }
        total
    }

    /// The actual derivatives `f⁽ⁱ⁾(x₀) = i! · c_i` at the base.
    pub fn derivative_values(&self) -> Vec<Rat> {
        let mut factorial = BigInt::one();
        let mut out = Vec::with_capacity(self.coefficients.len());
        for (index, coefficient) in self.coefficients.iter().enumerate() {
            if index > 0 {
                factorial *= BigInt::from(index as u64);
            }
            out.push(coefficient * &Rat::from_integer(factorial.clone()));
        }
        out
    }

    /// **The order of vanishing at the base**: the least `i` with `c_i ≠ 0`, or `None` when every
    /// declared coefficient vanishes and the reading is undecided at this order.
    ///
    /// This is what a neck station reads: a simple zero of `A(s) − A_min` is order one — a lens
    /// pinhole — and a higher order is a cusp.
    pub fn vanishing_order(&self) -> Option<usize> {
        self.coefficients.iter().position(|value| !value.is_zero())
    }

    /// Subtract a constant from the jet, in place of the caller doing it by hand before reading a
    /// vanishing order.
    pub fn shifted_by(&self, constant: &Rat) -> Self {
        let mut coefficients = self.coefficients.clone();
        coefficients[0] = &coefficients[0] - constant;
        Self {
            chart: self.chart.clone(),
            coefficients,
        }
    }

    /// Hand the coefficients to the existing local-jet owner, which normalizes trailing zeros.
    pub fn local_jet(&self) -> Result<LocalJet, StaircaseRefusal> {
        Ok(LocalJet::new(self.coefficients.clone())?)
    }

    /// Read a [`LocalJet`] back into a declared chart.
    pub fn from_local_jet(chart: JetChart, jet: &LocalJet) -> Result<Self, StaircaseRefusal> {
        Self::declare(chart, jet.coefficients().to_vec())
    }

    /// **The affine space of degree-`≤ degree` polynomials agreeing with this jet.**
    ///
    /// Never a chosen member: a base point and the free directions. The dimension is
    /// `degree − order`.
    pub fn compatible_polynomials(
        &self,
        degree: usize,
    ) -> Result<PolynomialFamily, StaircaseRefusal> {
        if degree > FAMILY_DEGREE_CEILING {
            return Err(StaircaseRefusal::DegreeBeyondCeiling {
                declared: degree,
                ceiling: FAMILY_DEGREE_CEILING,
            });
        }
        let order = self.order();
        if degree < order {
            return Err(StaircaseRefusal::DegreeBelowJetOrder { degree, order });
        }
        let mut particular = self.coefficients.clone();
        particular.resize(degree + 1, Rat::zero());
        let free = (order + 1..=degree)
            .map(|index| {
                let mut direction = vec![Rat::zero(); degree + 1];
                direction[index] = Rat::one();
                direction
            })
            .collect();
        Ok(PolynomialFamily {
            chart: self.chart.clone(),
            jet_order: order,
            degree,
            particular,
            free_directions: free,
        })
    }
}

/// **The compatible family a finite jet retains: an affine space, returned whole.**
///
/// [definition] `particular + Σ λ_j · direction_j`. The base point is **not** a selection and the
/// type offers no accessor that returns "the" continuation; [`Self::member`] makes the caller
/// declare the coordinates it wants, and [`Self::contains`] decides membership.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct PolynomialFamily {
    chart: JetChart,
    jet_order: usize,
    degree: usize,
    particular: Vec<Rat>,
    free_directions: Vec<Vec<Rat>>,
}

impl PolynomialFamily {
    pub fn chart(&self) -> &JetChart {
        &self.chart
    }

    pub fn jet_order(&self) -> usize {
        self.jet_order
    }

    pub fn degree(&self) -> usize {
        self.degree
    }

    /// The dimension of the fibre: how many continuations' worth of freedom the jet retains.
    pub fn dimension(&self) -> usize {
        self.free_directions.len()
    }

    /// A base point of the affine space. Not a selection: every member is
    /// `base_point + Σ λ_j direction_j` and no `λ` is preferred.
    pub fn base_point(&self) -> &[Rat] {
        &self.particular
    }

    pub fn free_directions(&self) -> &[Vec<Rat>] {
        &self.free_directions
    }

    /// The member at declared coordinates.
    pub fn member(&self, coordinates: &[Rat]) -> Result<FiniteJet, StaircaseRefusal> {
        if coordinates.len() != self.free_directions.len() {
            return Err(StaircaseRefusal::FunctionalLengthMismatch {
                declared: coordinates.len(),
                samples: self.free_directions.len(),
            });
        }
        let mut out = self.particular.clone();
        for (coordinate, direction) in coordinates.iter().zip(&self.free_directions) {
            for (slot, entry) in out.iter_mut().zip(direction) {
                *slot = &*slot + &(coordinate * entry);
            }
        }
        FiniteJet::declare(self.chart.clone(), out)
    }

    /// Whether a declared coefficient vector lies in this family.
    pub fn contains(&self, coefficients: &[Rat]) -> bool {
        if coefficients.len() != self.particular.len() {
            return false;
        }
        // The family is `particular + span(e_{r+1} … e_d)`, so membership is agreement on the
        // first `r+1` coordinates. Decided on the directions rather than on that description:
        // a coordinate no direction moves must agree.
        for index in 0..self.particular.len() {
            let moved = self
                .free_directions
                .iter()
                .any(|direction| !direction[index].is_zero());
            if !moved && coefficients[index] != self.particular[index] {
                return false;
            }
        }
        true
    }
}

/// **The ladder `J⁰ ← J¹ ← … ← J^r`, every rung present.**
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct JetLadder {
    rungs: Vec<FiniteJet>,
}

/// Build the ladder by restricting repeatedly from the declared top.
pub fn jet_ladder(top: &FiniteJet) -> Result<JetLadder, StaircaseRefusal> {
    let mut rungs = vec![top.clone()];
    let mut current = top.clone();
    while current.order() > 0 {
        current = current.restrict()?;
        rungs.push(current.clone());
    }
    rungs.reverse();
    Ok(JetLadder { rungs })
}

impl JetLadder {
    /// The rung at a declared order, or `None` when the ladder does not reach it.
    pub fn rung(&self, order: usize) -> Option<&FiniteJet> {
        self.rungs.get(order)
    }

    pub fn top_order(&self) -> usize {
        self.rungs.len() - 1
    }

    pub fn rungs(&self) -> &[FiniteJet] {
        &self.rungs
    }

    /// **Restriction is a projection**: every rung is the restriction of the one above it, checked
    /// rather than assumed. Lean: `Transport/JetStaircase.lean::truncate_idem` and
    /// `Transport/JetStaircase.lean::truncate_comp`.
    pub fn restriction_is_projection(&self) -> bool {
        self.rungs.windows(2).all(|pair| {
            let [lower, upper] = pair else { return false };
            upper.restrict().as_ref() == Ok(lower)
        })
    }

    /// The fibre of one restriction step: one free coefficient, at every step of the ladder.
    /// Lean: `Transport/JetStaircase.lean::truncate_fibre_is_the_top_coefficient`.
    pub fn restriction_fibre_dimension(&self, from_order: usize) -> Option<usize> {
        if from_order == 0 || from_order > self.top_order() {
            None
        } else {
            Some(1)
        }
    }
}

// ===============================================================================================
// 2. spline continuations over declared knots
// ===============================================================================================

/// **A piecewise polynomial over declared knots, each piece expanded about its own left end.**
///
/// [definition] `pieces[0]` is expanded about the chart's base and `pieces[i]` about
/// `knots[i−1]`, so the piece count is one more than the knot count. Each piece carries the same
/// chart's step; the base of a piece is the knot it starts at, held here rather than in the piece.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct PiecewisePolynomial {
    chart: JetChart,
    knots: Vec<Rat>,
    pieces: Vec<Vec<Rat>>,
}

impl PiecewisePolynomial {
    /// Declare it. The knots must be strictly increasing, the piece count must be one more than
    /// the knot count, and both are bounded before anything is sized by them.
    pub fn declare(
        chart: JetChart,
        knots: Vec<Rat>,
        pieces: Vec<Vec<Rat>>,
    ) -> Result<Self, StaircaseRefusal> {
        if knots.len() > KNOT_CEILING {
            return Err(StaircaseRefusal::KnotsBeyondCeiling {
                declared: knots.len(),
                ceiling: KNOT_CEILING,
            });
        }
        for at in 1..knots.len() {
            if knots[at] <= knots[at - 1] {
                return Err(StaircaseRefusal::KnotsNotIncreasing { at });
            }
        }
        if pieces.len() != knots.len() + 1 {
            return Err(StaircaseRefusal::PieceCountMismatch {
                knots: knots.len(),
                needed: knots.len() + 1,
                declared: pieces.len(),
            });
        }
        for piece in &pieces {
            if piece.is_empty() {
                return Err(StaircaseRefusal::EmptyJet);
            }
            if piece.len() - 1 > JET_ORDER_CEILING {
                return Err(StaircaseRefusal::OrderBeyondCeiling {
                    declared: piece.len() - 1,
                    ceiling: JET_ORDER_CEILING,
                });
            }
        }
        Ok(Self {
            chart,
            knots,
            pieces,
        })
    }

    pub fn knots(&self) -> &[Rat] {
        &self.knots
    }

    pub fn pieces(&self) -> &[Vec<Rat>] {
        &self.pieces
    }

    /// The base point of piece `index`: the chart's base for the first piece, the preceding knot
    /// otherwise.
    pub fn piece_base(&self, index: usize) -> Option<Rat> {
        if index > self.knots.len() {
            return None;
        }
        Some(if index == 0 {
            self.chart.base.clone()
        } else {
            self.knots[index - 1].clone()
        })
    }

    fn piece_jet(&self, index: usize) -> Result<FiniteJet, StaircaseRefusal> {
        let base = self
            .piece_base(index)
            .ok_or(StaircaseRefusal::NoSuchKnot {
                at: index,
                declared: self.knots.len(),
            })?;
        FiniteJet::declare(
            JetChart::declare(
                format!("{}|piece-{index}", self.chart.lineage),
                base,
                self.chart.step.clone(),
            )?,
            self.pieces[index].clone(),
        )
    }

    /// **The joint order at a knot: the lowest derivative that jumps.**
    ///
    /// Returns [`JointOrder`] — `junction_law`'s declared field, which that owner keeps empty
    /// precisely so this reading can fill it. When nothing jumps up to the highest order both
    /// pieces carry, the return says so and names that order rather than minting a jump.
    pub fn knot_reading(&self, knot_index: usize) -> Result<KnotReading, StaircaseRefusal> {
        if knot_index >= self.knots.len() {
            return Err(StaircaseRefusal::NoSuchKnot {
                at: knot_index,
                declared: self.knots.len(),
            });
        }
        let knot = self.knots[knot_index].clone();
        let left = self.piece_jet(knot_index)?;
        let right = self.piece_jet(knot_index + 1)?;
        let compared = left.order().max(right.order());
        for order in 0..=compared {
            let left_value = left.derivative_at(order, &knot);
            let right_value = right.derivative_at(order, &knot);
            if left_value != right_value {
                return Ok(KnotReading::Jumps {
                    order: JointOrder(u32::try_from(order).unwrap_or(u32::MAX)),
                    left: left_value,
                    right: right_value,
                });
            }
        }
        Ok(KnotReading::SmoothThrough { order: compared })
    }
}

/// What a knot reading returned.
///
/// Not `Serialize`: it carries `junction_law`'s [`JointOrder`], which that owner does not
/// serialize, and this owner does not widen another owner's type to make its own derive land.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum KnotReading {
    /// The lowest derivative that jumps, with both one-sided values.
    Jumps {
        order: JointOrder,
        left: Rat,
        right: Rat,
    },
    /// No derivative up to `order` jumps. This is the honest return, not a `JointOrder` of
    /// `order + 1`: the pieces carry no higher derivative to compare.
    SmoothThrough { order: usize },
}

/// **The affine family of splines continuing a declared jet across declared knots.**
///
/// [definition] Unknowns are the coefficients of every piece in its own local coordinate.
/// Constraints are: the first piece agrees with the jet to its order, and at every interior knot
/// the derivatives of order `0 … smoothness` agree across. The return is the complete affine
/// fibre — a base point and the kernel — from one exact reduction, or
/// [`StaircaseRefusal::NoCompatibleSpline`] when the constraints are inconsistent.
pub fn compatible_splines(
    jet: &FiniteJet,
    knots: &[Rat],
    degree: usize,
    smoothness: usize,
) -> Result<SplineFamily, StaircaseRefusal> {
    if knots.len() > KNOT_CEILING {
        return Err(StaircaseRefusal::KnotsBeyondCeiling {
            declared: knots.len(),
            ceiling: KNOT_CEILING,
        });
    }
    if degree > FAMILY_DEGREE_CEILING {
        return Err(StaircaseRefusal::DegreeBeyondCeiling {
            declared: degree,
            ceiling: FAMILY_DEGREE_CEILING,
        });
    }
    let order = jet.order();
    if degree < order {
        return Err(StaircaseRefusal::DegreeBelowJetOrder { degree, order });
    }
    if smoothness > degree {
        return Err(StaircaseRefusal::OrderExceedsSamples {
            order: smoothness,
            samples: degree,
            needed: smoothness,
        });
    }
    for at in 1..knots.len() {
        if knots[at] <= knots[at - 1] {
            return Err(StaircaseRefusal::KnotsNotIncreasing { at });
        }
    }
    let pieces = knots.len() + 1;
    let width = degree + 1;
    let columns = pieces * width;
    let rows = (order + 1) + knots.len() * (smoothness + 1);
    let entries = rows
        .checked_mul(columns)
        .ok_or(StaircaseRefusal::SplineWorkBeyondCeiling {
            declared: usize::MAX,
            ceiling: SPLINE_WORK_CEILING,
        })?;
    if entries > SPLINE_WORK_CEILING {
        return Err(StaircaseRefusal::SplineWorkBeyondCeiling {
            declared: entries,
            ceiling: SPLINE_WORK_CEILING,
        });
    }

    let base_of = |index: usize| -> Rat {
        if index == 0 {
            jet.chart.base.clone()
        } else {
            knots[index - 1].clone()
        }
    };

    let mut matrix = vec![vec![Rat::zero(); columns]; rows];
    let mut target = vec![Rat::zero(); rows];
    // The jet constraints: the first piece's low coefficients are the jet's.
    for index in 0..=order {
        matrix[index][index] = Rat::one();
        target[index] = jet.coefficients[index].clone();
    }
    // The knot constraints: the derivatives of order `0 … smoothness` agree across each knot.
    let mut row = order + 1;
    for (knot_at, knot) in knots.iter().enumerate() {
        let left_piece = knot_at;
        let right_piece = knot_at + 1;
        let left_offset = knot - &base_of(left_piece);
        for derivative in 0..=smoothness {
            for power in derivative..=degree {
                let mut falling = BigInt::one();
                for step in 0..derivative {
                    falling *= BigInt::from((power - step) as u64);
                }
                let mut shift = Rat::one();
                for _ in 0..(power - derivative) {
                    shift = &shift * &left_offset;
                }
                matrix[row][left_piece * width + power] = &Rat::from_integer(falling) * &shift;
            }
            // The right piece is expanded about the knot itself, so only one coefficient survives.
            let mut factorial = BigInt::one();
            for step in 1..=derivative {
                factorial *= BigInt::from(step as u64);
            }
            matrix[row][right_piece * width + derivative] =
                -Rat::from_integer(factorial);
            row += 1;
        }
    }

    let system = ExactRatMatrix::new(matrix)?;
    let Some((particular, kernel)) = system.preimage_fibre(&target)? else {
        return Err(StaircaseRefusal::NoCompatibleSpline);
    };
    Ok(SplineFamily {
        chart: jet.chart.clone(),
        knots: knots.to_vec(),
        degree,
        smoothness,
        jet_order: order,
        particular,
        free_directions: kernel,
    })
}

/// The affine family of splines a jet retains over declared knots.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct SplineFamily {
    chart: JetChart,
    knots: Vec<Rat>,
    degree: usize,
    smoothness: usize,
    jet_order: usize,
    particular: Vec<Rat>,
    free_directions: Vec<Vec<Rat>>,
}

impl SplineFamily {
    pub fn degree(&self) -> usize {
        self.degree
    }

    pub fn smoothness(&self) -> usize {
        self.smoothness
    }

    pub fn jet_order(&self) -> usize {
        self.jet_order
    }

    pub fn knots(&self) -> &[Rat] {
        &self.knots
    }

    /// How many continuations' worth of freedom the jet retains over these knots.
    pub fn dimension(&self) -> usize {
        self.free_directions.len()
    }

    pub fn base_point(&self) -> &[Rat] {
        &self.particular
    }

    pub fn free_directions(&self) -> &[Vec<Rat>] {
        &self.free_directions
    }

    /// The member at declared coordinates, assembled as a [`PiecewisePolynomial`].
    pub fn member(&self, coordinates: &[Rat]) -> Result<PiecewisePolynomial, StaircaseRefusal> {
        if coordinates.len() != self.free_directions.len() {
            return Err(StaircaseRefusal::FunctionalLengthMismatch {
                declared: coordinates.len(),
                samples: self.free_directions.len(),
            });
        }
        let mut flat = self.particular.clone();
        for (coordinate, direction) in coordinates.iter().zip(&self.free_directions) {
            for (slot, entry) in flat.iter_mut().zip(direction) {
                *slot = &*slot + &(coordinate * entry);
            }
        }
        let width = self.degree + 1;
        let pieces = flat.chunks(width).map(<[Rat]>::to_vec).collect();
        PiecewisePolynomial::declare(self.chart.clone(), self.knots.clone(), pieces)
    }
}

// ===============================================================================================
// 3. difference data and the exact change of basis
// ===============================================================================================

/// **Sampled data in a declared chart: `f(x₀ + i h)` for `i = 0 … n−1`.**
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "DifferenceTableWire")]
pub struct DifferenceTable {
    chart: JetChart,
    values: Vec<Rat>,
}

#[derive(Deserialize)]
struct DifferenceTableWire {
    chart: JetChart,
    values: Vec<Rat>,
}

impl TryFrom<DifferenceTableWire> for DifferenceTable {
    type Error = StaircaseRefusal;

    fn try_from(wire: DifferenceTableWire) -> Result<Self, Self::Error> {
        Self::declare(wire.chart, wire.values)
    }
}

impl DifferenceTable {
    /// Declare it. The sample count is bounded against [`SAMPLE_CEILING`] before the difference
    /// triangle it sizes is formed.
    pub fn declare(chart: JetChart, values: Vec<Rat>) -> Result<Self, StaircaseRefusal> {
        if values.is_empty() {
            return Err(StaircaseRefusal::EmptySamples);
        }
        if values.len() > SAMPLE_CEILING {
            return Err(StaircaseRefusal::SamplesBeyondCeiling {
                declared: values.len(),
                ceiling: SAMPLE_CEILING,
            });
        }
        Ok(Self { chart, values })
    }

    /// Sample a declared jet polynomial at the chart's own nodes.
    pub fn sampled_from(jet: &FiniteJet, count: usize) -> Result<Self, StaircaseRefusal> {
        if count == 0 {
            return Err(StaircaseRefusal::EmptySamples);
        }
        if count > SAMPLE_CEILING {
            return Err(StaircaseRefusal::SamplesBeyondCeiling {
                declared: count,
                ceiling: SAMPLE_CEILING,
            });
        }
        let values = (0..count)
            .map(|index| jet.evaluate(&jet.chart.node(index)))
            .collect();
        Self::declare(jet.chart.clone(), values)
    }

    pub fn chart(&self) -> &JetChart {
        &self.chart
    }

    pub fn values(&self) -> &[Rat] {
        &self.values
    }

    pub fn len(&self) -> usize {
        self.values.len()
    }

    pub fn is_empty(&self) -> bool {
        false
    }

    /// The `order`-th forward-difference column, `Δ^order f` at every node it is defined at.
    pub fn difference_column(&self, order: usize) -> Result<Vec<Rat>, StaircaseRefusal> {
        if order >= self.values.len() {
            return Err(StaircaseRefusal::OrderExceedsSamples {
                order,
                samples: self.values.len(),
                needed: order + 1,
            });
        }
        let mut column = self.values.clone();
        for _ in 0..order {
            column = column
                .windows(2)
                .map(|pair| &pair[1] - &pair[0])
                .collect();
        }
        Ok(column)
    }

    /// The leading edge of the difference triangle: `Δ^k f(x₀)` for `k = 0 … n−1`.
    pub fn forward_differences(&self) -> Vec<Rat> {
        let mut column = self.values.clone();
        let mut out = Vec::with_capacity(self.values.len());
        while let Some(head) = column.first() {
            out.push(head.clone());
            column = column
                .windows(2)
                .map(|pair| &pair[1] - &pair[0])
                .collect();
        }
        out
    }

    /// **The least `k` whose difference column vanishes identically over the whole sample.**
    ///
    /// `Δ^n` on `n` samples is the empty column and would pass vacuously, so the search stops at
    /// `n−1` and returns [`OrderReading::NotResolvedWithin`] rather than reporting the length.
    pub fn annihilating_order(&self) -> OrderReading {
        let samples = self.values.len();
        for order in 0..samples {
            let Ok(column) = self.difference_column(order) else {
                break;
            };
            if column.iter().all(Zero::is_zero) {
                return OrderReading::Annihilated(order);
            }
        }
        OrderReading::NotResolvedWithin(samples)
    }

    /// **Difference data to jet data, exactly, at the declared step.**
    ///
    /// Newton's forward formula with the falling factorial expanded by the exact integer
    /// recurrence. Upper triangular in the difference index with diagonal `1/(k! h^k)`.
    pub fn to_jet(&self, order: usize) -> Result<FiniteJet, StaircaseRefusal> {
        if order > JET_ORDER_CEILING {
            return Err(StaircaseRefusal::OrderBeyondCeiling {
                declared: order,
                ceiling: JET_ORDER_CEILING,
            });
        }
        if order >= self.values.len() {
            return Err(StaircaseRefusal::OrderExceedsSamples {
                order,
                samples: self.values.len(),
                needed: order + 1,
            });
        }
        let differences = self.forward_differences();
        let mut coefficients = vec![Rat::zero(); order + 1];
        let mut factorial = BigInt::one();
        // `falling[i]` holds the coefficient of `t^i` in `Π_{j<k} (t − j)`, rebuilt for each `k`.
        let mut falling = vec![Rat::one()];
        for index in 0..=order {
            if index > 0 {
                factorial *= BigInt::from(index as u64);
                // Multiply by `(t − (index − 1))`.
                let shift = Rat::from_integer(BigInt::from((index - 1) as u64));
                let mut next = vec![Rat::zero(); falling.len() + 1];
                for (power, entry) in falling.iter().enumerate() {
                    next[power + 1] = &next[power + 1] + entry;
                    next[power] = &next[power] - &(entry * &shift);
                }
                falling = next;
            }
            let scale = &differences[index] / &Rat::from_integer(factorial.clone());
            for (power, entry) in falling.iter().enumerate() {
                if power > order {
                    break;
                }
                coefficients[power] = &coefficients[power] + &(&scale * entry);
            }
        }
        // Divide the coefficient of `t^i` by `h^i` to reach `(x − x₀)^i`.
        let mut power_of_step = Rat::one();
        for (index, coefficient) in coefficients.iter_mut().enumerate() {
            if index > 0 {
                power_of_step = &power_of_step * &self.chart.step;
            }
            *coefficient = &*coefficient / &power_of_step;
        }
        FiniteJet::declare(self.chart.clone(), coefficients)
    }

    /// **What the degree-`r` reconstruction costs on input that is not polynomial**: the exact
    /// per-node difference `f(x_i) − jet(x_i)`, computed and never assumed zero.
    pub fn reconstruction_residual(&self, jet: &FiniteJet) -> Result<Vec<Rat>, StaircaseRefusal> {
        self.chart.agrees_with(&jet.chart)?;
        Ok(self
            .values
            .iter()
            .enumerate()
            .map(|(index, value)| value - &jet.evaluate(&self.chart.node(index)))
            .collect())
    }
}

/// **Jet data back to difference data**: evaluation at the chart's nodes. The inverse of
/// [`DifferenceTable::to_jet`], and triangular the other way — the binomial matrix.
pub fn jet_to_differences(jet: &FiniteJet, count: usize) -> Result<Vec<Rat>, StaircaseRefusal> {
    let table = DifferenceTable::sampled_from(jet, count)?;
    Ok(table.forward_differences())
}

/// A difference-order reading, with the honest arm for a sample too short to decide.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum OrderReading {
    /// `Δ^k` vanishes identically over the declared sample and no smaller `k` does.
    Annihilated(usize),
    /// No `k < samples` annihilates. The sample is named; nothing is inferred about a longer one.
    NotResolvedWithin(usize),
}

impl OrderReading {
    /// The annihilating order, when one was resolved.
    pub fn order(self) -> Option<usize> {
        match self {
            Self::Annihilated(order) => Some(order),
            Self::NotResolvedWithin(_) => None,
        }
    }

    /// The polynomial degree the reading exhibits: one less than the annihilating order. The
    /// zero sequence is annihilated at order zero and exhibits no degree.
    pub fn degree(self) -> Option<usize> {
        match self {
            Self::Annihilated(0) => None,
            Self::Annihilated(order) => Some(order - 1),
            Self::NotResolvedWithin(_) => None,
        }
    }
}

// ===============================================================================================
// 4. the staircase (i): repeated integration with boundary data as an encoding
// ===============================================================================================

/// **The encoding: `k` boundary differences and the nonzero entries of the `Δ^k` column.**
///
/// [definition] Repeated integration is repeated summation, and its constants of integration are
/// the boundary differences `Δ⁰f(x₀) … Δ^{k−1}f(x₀)`. Nothing is lost: the pair is a change of
/// basis on `Q^n` and [`Self::decode`] inverts it exactly. What changes is the **cost**, and
/// [`Self::cost`] measures it rather than estimating it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct SparseDifferenceEncoding {
    chart: JetChart,
    order: usize,
    length: usize,
    boundary: Vec<Rat>,
    sparse: BTreeMap<usize, Rat>,
}

/// Encode a table at a declared difference order.
pub fn encode_sparse_differences(
    table: &DifferenceTable,
    order: usize,
) -> Result<SparseDifferenceEncoding, StaircaseRefusal> {
    let length = table.len();
    if order >= length {
        return Err(StaircaseRefusal::OrderExceedsSamples {
            order,
            samples: length,
            needed: order + 1,
        });
    }
    let differences = table.forward_differences();
    let boundary = differences[..order].to_vec();
    let column = table.difference_column(order)?;
    let sparse = column
        .into_iter()
        .enumerate()
        .filter(|(_, value)| !value.is_zero())
        .collect();
    Ok(SparseDifferenceEncoding {
        chart: table.chart.clone(),
        order,
        length,
        boundary,
        sparse,
    })
}

impl SparseDifferenceEncoding {
    pub fn order(&self) -> usize {
        self.order
    }

    pub fn length(&self) -> usize {
        self.length
    }

    pub fn boundary(&self) -> &[Rat] {
        &self.boundary
    }

    pub fn sparse(&self) -> &BTreeMap<usize, Rat> {
        &self.sparse
    }

    /// **Exact reconstruction by repeated summation.** The `Δ^k` column is integrated up to
    /// `Δ⁰`, one prefix sum per level, each starting from its boundary difference.
    pub fn decode(&self) -> Result<DifferenceTable, StaircaseRefusal> {
        let mut column: Vec<Rat> = (0..self.length - self.order)
            .map(|index| self.sparse.get(&index).cloned().unwrap_or_else(Rat::zero))
            .collect();
        for level in (0..self.order).rev() {
            let mut next = Vec::with_capacity(column.len() + 1);
            let mut running = self.boundary[level].clone();
            next.push(running.clone());
            for entry in &column {
                running = &running + entry;
                next.push(running.clone());
            }
            column = next;
        }
        DifferenceTable::declare(self.chart.clone(), column)
    }

    /// **What the encoding actually costs**, against the raw sequence: stored rationals and stored
    /// bits, both counted from the numerators and denominators that are really held.
    pub fn cost(&self) -> Result<EncodingCost, StaircaseRefusal> {
        let raw = self.decode()?;
        let raw_bits = raw.values().iter().map(rational_bits).sum::<u64>();
        let stored_bits = self
            .boundary
            .iter()
            .chain(self.sparse.values())
            .map(rational_bits)
            .sum::<u64>()
            // An index is stored beside every sparse entry; count it, at the width the length
            // needs, rather than pretending the sparse column is free of addressing.
            + (self.sparse.len() as u64) * (u64::from(self.length.max(1).ilog2()) + 1);
        Ok(EncodingCost {
            raw_terms: self.length,
            stored_terms: self.boundary.len() + self.sparse.len(),
            raw_bits,
            stored_bits,
        })
    }

    /// **The declared receiver, transported to the encoding's coordinates.**
    ///
    /// A linear functional `L` on the raw sequence factors through the encoding as
    /// `L ∘ decode`, and its coordinates are `L(decode(e_j))`. The encoding's coordinates are the
    /// `k` boundary differences followed by the `n − k` entries of the `Δ^k` column, in that
    /// order — the full basis, not only the stored ones, so the support of the returned covector
    /// is itself a reading.
    pub fn induced_functional(&self, functional: &[Rat]) -> Result<Vec<Rat>, StaircaseRefusal> {
        if functional.len() != self.length {
            return Err(StaircaseRefusal::FunctionalLengthMismatch {
                declared: functional.len(),
                samples: self.length,
            });
        }
        let mut induced = Vec::with_capacity(self.length);
        for coordinate in 0..self.length {
            let basis = self.basis_encoding(coordinate);
            let decoded = basis.decode()?;
            induced.push(pair(functional, decoded.values()));
        }
        Ok(induced)
    }

    fn basis_encoding(&self, coordinate: usize) -> Self {
        let mut boundary = vec![Rat::zero(); self.order];
        let mut sparse = BTreeMap::new();
        if coordinate < self.order {
            boundary[coordinate] = Rat::one();
        } else {
            sparse.insert(coordinate - self.order, Rat::one());
        }
        Self {
            chart: self.chart.clone(),
            order: self.order,
            length: self.length,
            boundary,
            sparse,
        }
    }

    /// **Whether a declared future receiver factors through the encoding**, with both values and
    /// the induced covector returned so the caller sees what it factored through.
    pub fn factors_through(
        &self,
        functional: &[Rat],
    ) -> Result<FactorisationReceipt, StaircaseRefusal> {
        let induced = self.induced_functional(functional)?;
        let raw = self.decode()?;
        let raw_value = pair(functional, raw.values());
        let mut coordinates = Vec::with_capacity(self.length);
        coordinates.extend(self.boundary.iter().cloned());
        for index in 0..self.length - self.order {
            coordinates.push(self.sparse.get(&index).cloned().unwrap_or_else(Rat::zero));
        }
        let encoded_value = pair(&induced, &coordinates);
        let support = induced
            .iter()
            .enumerate()
            .filter(|(_, value)| !value.is_zero())
            .map(|(index, _)| index)
            .collect();
        Ok(FactorisationReceipt {
            agrees: raw_value == encoded_value,
            raw_value,
            encoded_value,
            induced,
            support,
        })
    }
}

fn pair(left: &[Rat], right: &[Rat]) -> Rat {
    left.iter()
        .zip(right)
        .fold(Rat::zero(), |sum, (a, b)| &sum + &(a * b))
}

fn rational_bits(value: &Rat) -> u64 {
    // A rational is held as a numerator and a denominator; both are counted, and the sign costs
    // the bit it costs. The zero numerator still occupies its slot, so it costs one.
    value.numer().magnitude().bits().max(1) + value.denom().magnitude().bits().max(1)
}

/// The measured cost of an encoding against the raw sequence.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct EncodingCost {
    /// Rationals in the raw sequence.
    pub raw_terms: usize,
    /// Rationals the encoding actually stores: the boundary and the nonzero sparse entries.
    pub stored_terms: usize,
    /// Bits in the raw sequence's numerators and denominators.
    pub raw_bits: u64,
    /// Bits the encoding stores, including one index per sparse entry.
    pub stored_bits: u64,
}

impl EncodingCost {
    /// Whether the encoding stores strictly fewer bits than the raw sequence. A reading, not a
    /// promise: an encoding whose `Δ^k` column is dense costs more, and the accessor says so.
    pub fn is_cheaper(&self) -> bool {
        self.stored_bits < self.raw_bits
    }
}

/// What a factorisation check returned.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct FactorisationReceipt {
    /// Whether the receiver's value on the raw sequence equals its value through the encoding.
    pub agrees: bool,
    /// `L(f)` on the raw sequence.
    pub raw_value: Rat,
    /// `(L ∘ decode)` paired with the encoding's coordinates.
    pub encoded_value: Rat,
    /// The induced covector on the encoding's coordinates.
    pub induced: Vec<Rat>,
    /// Which encoding coordinates the receiver actually touches.
    pub support: Vec<usize>,
}

// ===============================================================================================
// 5. the staircase (ii): a grain changes the apparent difference order, and by how much is computed
// ===============================================================================================

/// **A declared grain/receiver map on a sampled sequence.**
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum GrainMap {
    /// Sum consecutive blocks of `block` samples. The sample count must be divisible: a partial
    /// block is refused rather than padded.
    BlockSum { block: usize },
    /// Keep every `stride`-th sample.
    Subsample { stride: usize },
}

impl GrainMap {
    /// Apply the grain. The refusals are by name: a zero grain, and a block that does not divide.
    pub fn apply(&self, values: &[Rat]) -> Result<Vec<Rat>, StaircaseRefusal> {
        match *self {
            Self::BlockSum { block } => {
                if block == 0 {
                    return Err(StaircaseRefusal::ZeroGrain);
                }
                if !values.len().is_multiple_of(block) {
                    return Err(StaircaseRefusal::GrainDoesNotDivide {
                        grain: block,
                        samples: values.len(),
                    });
                }
                Ok(values
                    .chunks(block)
                    .map(|chunk| chunk.iter().fold(Rat::zero(), |sum, entry| &sum + entry))
                    .collect())
            }
            Self::Subsample { stride } => {
                if stride == 0 {
                    return Err(StaircaseRefusal::ZeroGrain);
                }
                Ok(values
                    .iter()
                    .step_by(stride)
                    .cloned()
                    .collect())
            }
        }
    }

    /// The chart the coarse reading sits in: the same base, the step multiplied by the grain.
    pub fn coarsened_chart(&self, chart: &JetChart) -> Result<JetChart, StaircaseRefusal> {
        let factor = match *self {
            Self::BlockSum { block } => block,
            Self::Subsample { stride } => stride,
        };
        if factor == 0 {
            return Err(StaircaseRefusal::ZeroGrain);
        }
        JetChart::declare(
            format!("{}|grain-{factor}", chart.lineage),
            chart.base.clone(),
            &chart.step * &Rat::from_integer(BigInt::from(factor as u64)),
        )
    }
}

/// **The order pair a grain produced.** Both orders are computed on their own sample; no universal
/// drop is asserted and none is available from this type.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct GrainOrderReading {
    pub grain: GrainMap,
    pub fine: OrderReading,
    pub coarse: OrderReading,
    pub fine_length: usize,
    pub coarse_length: usize,
}

impl GrainOrderReading {
    /// The signed change in annihilating order, when **both** orders were resolved. `None` is the
    /// honest return when either sample was too short: a change cannot be read off an unresolved
    /// order.
    pub fn order_change(&self) -> Option<i64> {
        let fine = i64::try_from(self.fine.order()?).ok()?;
        let coarse = i64::try_from(self.coarse.order()?).ok()?;
        Some(coarse - fine)
    }
}

/// **Compute the order pair for one declared grain on one declared sample.**
pub fn coarse_grain_order(
    table: &DifferenceTable,
    grain: &GrainMap,
) -> Result<GrainOrderReading, StaircaseRefusal> {
    let coarse_values = grain.apply(table.values())?;
    let coarse_chart = grain.coarsened_chart(table.chart())?;
    let coarse = DifferenceTable::declare(coarse_chart, coarse_values)?;
    Ok(GrainOrderReading {
        grain: *grain,
        fine: table.annihilating_order(),
        coarse: coarse.annihilating_order(),
        fine_length: table.len(),
        coarse_length: coarse.len(),
    })
}

// ===============================================================================================
// 6. the staircase (iv): the cusp raises difference order on the induced face
// ===============================================================================================

/// The dual cusp monodromy `M₀ = (T₀⁻¹)ᵀ` on the rank-four lattice.
///
/// Lean: `Geometry/SixSphereMonodromy.lean::M0`.
pub fn cusp_fibre_transport() -> ExactRatMatrix {
    integer_matrix(&[
        &[1, 0, 0, 0],
        &[0, 1, 0, 0],
        &[0, 1, 1, 0],
        &[-1, 0, 0, 1],
    ])
}

/// The exact cusp transport on oriented flux planes, in the ordered blade basis
/// `e01, e02, e03, e12, e13, e23`.
///
/// Lean: `Millennium/HolonicInteractionExterior.lean::cuspFluxTransport`, which
/// `cuspFluxTransport_isExteriorSquare` proves is literally `Λ²M₀`. That identity is re-derived
/// here by [`exterior_square`] rather than taken on the Lean statement's word.
pub fn cusp_flux_transport() -> ExactRatMatrix {
    integer_matrix(&[
        &[1, 0, 0, 0, 0, 0],
        &[1, 1, 0, 0, 0, 0],
        &[0, 0, 1, 0, 0, 0],
        &[0, 0, 0, 1, 0, 0],
        &[1, 0, 0, 0, 1, 0],
        &[1, 1, 0, 0, 1, 1],
    ])
}

/// The ordered blade basis' first index, `bladeFirst` in Lean.
const BLADE_FIRST: [usize; 6] = [0, 0, 0, 1, 1, 2];
/// The ordered blade basis' second index, `bladeSecond` in Lean.
const BLADE_SECOND: [usize; 6] = [1, 2, 3, 2, 3, 3];

/// **The second exterior power of a rank-four transport, in the ordered blade basis.**
///
/// Lean: `exteriorSquareAction`.
pub fn exterior_square(transport: &ExactRatMatrix) -> Result<ExactRatMatrix, StaircaseRefusal> {
    let mut rows = Vec::with_capacity(6);
    for row in 0..6 {
        let mut entries = Vec::with_capacity(6);
        for column in 0..6 {
            let a = transport.get(BLADE_FIRST[row], BLADE_FIRST[column])?;
            let b = transport.get(BLADE_SECOND[row], BLADE_SECOND[column])?;
            let c = transport.get(BLADE_FIRST[row], BLADE_SECOND[column])?;
            let d = transport.get(BLADE_SECOND[row], BLADE_FIRST[column])?;
            entries.push(&(a * b) - &(c * d));
        }
        rows.push(entries);
    }
    Ok(ExactRatMatrix::new(rows)?)
}

fn integer_matrix(rows: &[&[i64]]) -> ExactRatMatrix {
    ExactRatMatrix::new(
        rows.iter()
            .map(|row| {
                row.iter()
                    .map(|value| Rat::from_integer(BigInt::from(*value)))
                    .collect()
            })
            .collect(),
    )
    .expect("a rectangular literal matrix")
}

/// **The cusp instance of the staircase**, every entry recomputed over `Q`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct CuspStaircase {
    /// `Λ²M₀` agrees with the matrix Lean displays.
    pub exterior_square_agrees: bool,
    /// `N = M₀ − 1` is square-zero.
    pub fibre_defect_square_zero: bool,
    /// `D = Λ²M₀ − 1` is cubic-zero. Lean: `HolonicInteractionExterior.cuspFluxDefect_cubicZero`.
    pub flux_defect_cube_zero: bool,
    /// `D²` does not vanish. Lean: `HolonicInteractionExterior.cuspFluxDefect_squareNonzero`.
    pub flux_defect_square_nonzero: bool,
    /// The annihilating difference order of the fibre orbit, per the longest coordinate.
    pub fibre_order: OrderReading,
    /// The annihilating difference order of the induced flux orbit.
    pub flux_order: OrderReading,
    /// The flux orbit's second difference, constant. Lean:
    /// `HolonicInteractionExterior.cuspFluxOrbit_secondDifference`, and the difference law it
    /// satisfies is `Transport/JetStaircase.lean::square_secondDifference`.
    pub flux_second_difference: Vec<Rat>,
    /// The flux orbit's third difference, zero. Lean:
    /// `HolonicInteractionExterior.cuspFluxOrbit_thirdDifference`, and
    /// `Transport/JetStaircase.lean::square_thirdDifference`.
    pub flux_third_difference: Vec<Rat>,
    /// The displayed orbit `e01 + n e02 + n e13 + n² e23` at the last sampled time.
    pub flux_orbit_tail: Vec<Rat>,
}

/// Recompute the cusp staircase from the two integer matrices over `samples` chronological steps.
///
/// `samples` must reach at least the fourth difference for the third-difference reading to be
/// taken, so four is the least declaration this accepts.
pub fn cusp_staircase(samples: usize) -> Result<CuspStaircase, StaircaseRefusal> {
    if samples < 4 {
        return Err(StaircaseRefusal::OrderExceedsSamples {
            order: 3,
            samples,
            needed: 4,
        });
    }
    let fibre = cusp_fibre_transport();
    let flux = cusp_flux_transport();
    let exterior_square_agrees = exterior_square(&fibre)? == flux;

    let identity4 = ExactRatMatrix::identity(4)?;
    let identity6 = ExactRatMatrix::identity(6)?;
    let fibre_defect = fibre.subtract(&identity4)?;
    let flux_defect = flux.subtract(&identity6)?;
    let fibre_defect_square = fibre_defect.multiply(&fibre_defect)?;
    let flux_defect_square = flux_defect.multiply(&flux_defect)?;
    let flux_defect_cube = flux_defect_square.multiply(&flux_defect)?;
    let zero4 = ExactRatMatrix::zero(4, 4)?;
    let zero6 = ExactRatMatrix::zero(6, 6)?;

    // The fibre orbit of `e₀`, which `N = M₀ − 1` moves: `N e₀ = −e₃ ≠ 0` and `N² = 0`, so
    // `M₀ⁿ e₀ = e₀ − n e₃` is affine in `n` and its second difference vanishes.
    let mut fibre_state = vec![Rat::one(), Rat::zero(), Rat::zero(), Rat::zero()];
    let mut fibre_orbit: Vec<Vec<Rat>> = vec![fibre_state.clone()];
    for _ in 1..samples {
        fibre_state = fibre.apply(&fibre_state)?;
        fibre_orbit.push(fibre_state.clone());
    }

    // The flux orbit of `e₀∧e₁`, the first blade.
    let mut flux_state = vec![
        Rat::one(),
        Rat::zero(),
        Rat::zero(),
        Rat::zero(),
        Rat::zero(),
        Rat::zero(),
    ];
    let mut flux_orbit: Vec<Vec<Rat>> = vec![flux_state.clone()];
    for _ in 1..samples {
        flux_state = flux.apply(&flux_state)?;
        flux_orbit.push(flux_state.clone());
    }

    let chart = JetChart::unit("cusp|chronological");
    let fibre_order = vector_annihilating_order(&chart, &fibre_orbit, 4)?;
    let flux_order = vector_annihilating_order(&chart, &flux_orbit, 6)?;

    let mut second = Vec::with_capacity(6);
    let mut third = Vec::with_capacity(6);
    for coordinate in 0..6 {
        let table = coordinate_table(&chart, &flux_orbit, coordinate)?;
        second.push(table.difference_column(2)?[0].clone());
        third.push(table.difference_column(3)?[0].clone());
    }

    Ok(CuspStaircase {
        exterior_square_agrees,
        fibre_defect_square_zero: fibre_defect_square == zero4,
        flux_defect_cube_zero: flux_defect_cube == zero6,
        flux_defect_square_nonzero: flux_defect_square != zero6,
        fibre_order,
        flux_order,
        flux_second_difference: second,
        flux_third_difference: third,
        flux_orbit_tail: flux_orbit
            .last()
            .cloned()
            .unwrap_or_default(),
    })
}

fn coordinate_table(
    chart: &JetChart,
    orbit: &[Vec<Rat>],
    coordinate: usize,
) -> Result<DifferenceTable, StaircaseRefusal> {
    DifferenceTable::declare(
        chart.clone(),
        orbit
            .iter()
            .map(|state| state[coordinate].clone())
            .collect(),
    )
}

fn vector_annihilating_order(
    chart: &JetChart,
    orbit: &[Vec<Rat>],
    extent: usize,
) -> Result<OrderReading, StaircaseRefusal> {
    let mut best = OrderReading::Annihilated(0);
    for coordinate in 0..extent {
        let reading = coordinate_table(chart, orbit, coordinate)?.annihilating_order();
        best = match (best, reading) {
            (OrderReading::NotResolvedWithin(length), _) => OrderReading::NotResolvedWithin(length),
            (_, OrderReading::NotResolvedWithin(length)) => {
                OrderReading::NotResolvedWithin(length)
            }
            (OrderReading::Annihilated(left), OrderReading::Annihilated(right)) => {
                OrderReading::Annihilated(left.max(right))
            }
        };
    }
    Ok(best)
}

// ===============================================================================================
// 7. the Mahler/Iwasawa comparison and where it stops
// ===============================================================================================

/// **`T = γ − 1` acting on a sampled sequence is the forward difference.**
///
/// Applies `(γ − 1)^order` by iterating the shift-minus-identity and returns the column, which is
/// [`DifferenceTable::difference_column`] recomputed by the Iwasawa side's own operator. The two
/// are compared by [`gamma_minus_one_is_forward_difference`].
pub fn gamma_minus_one_power(
    table: &DifferenceTable,
    order: usize,
) -> Result<Vec<Rat>, StaircaseRefusal> {
    if order >= table.len() {
        return Err(StaircaseRefusal::OrderExceedsSamples {
            order,
            samples: table.len(),
            needed: order + 1,
        });
    }
    let mut column = table.values().to_vec();
    for _ in 0..order {
        // `γ` is the shift `f ↦ f(· + 1)`; `γ − 1` loses the last sample, exactly as `Δ` does.
        let shifted = &column[1..];
        column = shifted
            .iter()
            .zip(&column[..column.len() - 1])
            .map(|(later, earlier)| later - earlier)
            .collect();
    }
    Ok(column)
}

/// **The functor, checked**: `(γ − 1)^k` and `Δ^k` agree on the declared sample at every order up
/// to `order`.
pub fn gamma_minus_one_is_forward_difference(
    table: &DifferenceTable,
    order: usize,
) -> Result<bool, StaircaseRefusal> {
    for level in 0..=order {
        if gamma_minus_one_power(table, level)? != table.difference_column(level)? {
            return Ok(false);
        }
    }
    Ok(true)
}

/// **The Mahler coefficients of a sampled function on `N`: its finite differences at `0`.**
///
/// The chart must be the unit chart — base `0`, step `1` — because that is what the Mahler chart
/// is; a different step is a different expansion and is refused by name rather than rescaled.
pub fn mahler_coefficients(table: &DifferenceTable) -> Result<Vec<Rat>, StaircaseRefusal> {
    table.chart.agrees_with(&JetChart::unit("mahler"))?;
    Ok(table.forward_differences())
}

/// What the Mahler/jet comparison returned on a declared source.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub enum MahlerScope {
    /// The source is polynomial at the declared order: the Mahler chart and the jet chart agree,
    /// and the reconstruction residual vanishes at every sampled node.
    PolynomialAgreement {
        degree: usize,
        mahler: Vec<Rat>,
        jet: Vec<Rat>,
    },
    /// The source is not polynomial at the declared order. The witness is the first node at which
    /// the truncation leaves the source, with the exact residual there.
    StopsAtNonPolynomial {
        order: usize,
        witness_node: usize,
        source_value: Rat,
        truncation_value: Rat,
        residual: Rat,
    },
}

/// **Compare the Mahler chart with the jet chart at step 1 on a declared source.**
pub fn mahler_chart_agreement(
    table: &DifferenceTable,
    order: usize,
) -> Result<MahlerScope, StaircaseRefusal> {
    let mahler = mahler_coefficients(table)?;
    let jet = table.to_jet(order)?;
    let residual = table.reconstruction_residual(&jet)?;
    if let Some((node, value)) = residual
        .iter()
        .enumerate()
        .find(|(_, value)| !value.is_zero())
    {
        return Ok(MahlerScope::StopsAtNonPolynomial {
            order,
            witness_node: node,
            source_value: table.values()[node].clone(),
            truncation_value: jet.evaluate(&table.chart.node(node)),
            residual: value.clone(),
        });
    }
    Ok(MahlerScope::PolynomialAgreement {
        degree: order,
        mahler: mahler[..=order].to_vec(),
        jet: jet.coefficients().to_vec(),
    })
}

/// **The stop: `n ↦ 2ⁿ` has every Mahler coefficient equal to `1`, so no finite jet reproduces
/// it.** The return is the node at which the declared truncation leaves it, with the residual.
pub fn mahler_stop_witness(order: usize, samples: usize) -> Result<MahlerScope, StaircaseRefusal> {
    if samples > SAMPLE_CEILING {
        return Err(StaircaseRefusal::SamplesBeyondCeiling {
            declared: samples,
            ceiling: SAMPLE_CEILING,
        });
    }
    let values = (0..samples)
        .map(|index| Rat::from_integer(BigInt::from(2u64).pow(u32::try_from(index).unwrap_or(0))))
        .collect();
    let table = DifferenceTable::declare(JetChart::unit("mahler"), values)?;
    mahler_chart_agreement(&table, order)
}

/// **Where the Iwasawa level filtration parts from the jet order filtration.**
///
/// `ω_n = (1+T)^{p^n} − 1`, so as an operator with `T = Δ` it is `γ^{p^n} − 1`, which on a
/// sequence is `f(· + p^n) − f(·)` and is **not** `Δ^{p^n}`. Both are evaluated on the declared
/// sample and the disagreement is returned. `[open]`: this is the honest boundary of the functor,
/// not a defect in either owner.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct OmegaComparison {
    pub prime: u64,
    pub level: u32,
    /// `p^n`, the degree of `ω_n`.
    pub degree: usize,
    /// `ω_n(Δ)` applied to the sample, at the base node.
    pub omega_at_base: Rat,
    /// `Δ^{p^n}` applied to the sample, at the base node.
    pub iterated_difference_at_base: Rat,
    /// Whether the two operators agreed on this sample.
    pub agrees: bool,
}

/// Evaluate `ω_n(T)` with `T = Δ` and `Δ^{p^n}` on the declared sample and return both.
pub fn omega_action_is_not_iterated_difference(
    table: &DifferenceTable,
    prime: u64,
    level: u32,
) -> Result<OmegaComparison, StaircaseRefusal> {
    let iwasawa_level = IwasawaLevel::new(prime, level)?;
    let coefficients = omega(&iwasawa_level);
    let degree = coefficients.len() - 1;
    if degree >= table.len() {
        return Err(StaircaseRefusal::OrderExceedsSamples {
            order: degree,
            samples: table.len(),
            needed: degree + 1,
        });
    }
    let mut omega_value = Rat::zero();
    for (power, coefficient) in coefficients.iter().enumerate() {
        if coefficient.is_zero() {
            continue;
        }
        let column = table.difference_column(power)?;
        omega_value = &omega_value + &(&Rat::from_integer(coefficient.clone()) * &column[0]);
    }
    let iterated = table.difference_column(degree)?[0].clone();
    Ok(OmegaComparison {
        prime,
        level,
        degree,
        agrees: omega_value == iterated,
        omega_at_base: omega_value,
        iterated_difference_at_base: iterated,
    })
}

/// A readout helper the neck station uses: the sign of a rational, without a float anywhere.
pub(crate) fn is_strictly_positive(value: &Rat) -> bool {
    value.is_positive()
}

#[cfg(test)]
mod tests;
