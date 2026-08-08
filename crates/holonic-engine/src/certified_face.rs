//! A presentation face whose feature population is Sturm-certified, not sampled.
//!
//! Record: `research/records/2026-08-08_THE_SAMPLER_HOPES_THE_CERTIFICATE_KNOWS_THE_GAUGE_CARRIES_NO_STRUCTURE.md`.
//! Contract: `blueprint/THE_PRESENTATION_ORGAN.md`.
//!
//! ## Why this is not a plotter
//!
//! The established practice in mathematical graphics is adaptive sampling: evaluate on a grid,
//! subdivide where the result looks rough, stop at a recursion bound. Wolfram documents the
//! consequence of that design plainly, in the same sentence on every one of its samplers — "it is
//! possible for Plot to miss features". A missed feature leaves no trace in the output, so the
//! reader cannot distinguish a curve that is smooth from a curve whose interesting part fell
//! between two samples.
//!
//! This module never subdivides in the hope that the picture settles down. `IntegerPolynomial`
//! carries an exact Sturm sequence, so the number of distinct real roots in a rational interval is
//! a *computable integer*, not an estimate. The cell law is therefore:
//!
//! ```text
//!   count == 0   the cell is certified featureless -- the segment stands, exactly
//!   count == 1   isolate it and deposit a located feature
//!   count >  1   subdivide, with the count itself as the termination certificate
//!   undecided    deposit an OBSTRUCTION -- never a smooth-looking lie
//! ```
//!
//! The obstruction population is part of the returned face. A face which resolved everything says
//! so by carrying an empty one; a face which did not says exactly where it failed and how many
//! features it could not separate. That is the same discipline `exact_value` applies to ordering
//! (`ExactOrdering::Open` rather than an epsilon comparison) and `gluing` applies to sections.
//!
//! ## Colour is not here
//!
//! There is no colour, no palette, no pixel and no output format in this module, and that is
//! structural rather than incidental. `research/records/2026-07-13_COLOR_IS_A_RECEIVER_FACE_THE_HIGHLIGHT_IS_THE_RELATION.md`
//! ratified colour as a declared display gauge `G` which "cannot alter `T`". A gauge that lives in
//! the same type as the geometry cannot be permuted independently of it, so the falsifier -- change
//! the palette and confirm no structural byte moves -- would be impossible to run. The gauge lives
//! in `presentation_gauge`, downstream, and consumes this face without being able to change it.
//!
//! ## No coordinate here is authored
//!
//! Every rational in a returned face is either a receiver-declared window endpoint or an exact
//! value of the source polynomial. There is no layout constant in this file. The three existing
//! example SVG writers each hardcode a position array; that is the defect this owner exists to
//! remove, and `emitted_marks_never_exceed_source_structure` is the control that keeps it removed.

use std::collections::BTreeMap;

use num_bigint::BigInt;
use num_traits::{Signed, Zero};
use relational_geometry::{Rat, format_rat, integer};
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::exact_value::{ExactInterval, ExactValueError, IntegerPolynomial};

/// One receiver's declared window onto an exact object.
///
/// The window is the receiver's aperture, and it is supplied rather than inferred from the data.
/// Inferring a window from the data's own extremes is the move `ColorFunctionScaling` makes for
/// colour, and it is refused for the same reason: the presented face would then depend on the
/// population it happens to contain.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverWindow {
    pub lower: Rat,
    pub upper: Rat,
    /// How many equal cells the window is initially cut into. This is an aperture, not a quality
    /// knob: raising it does not make an unresolved cell resolve, it only changes where the cuts
    /// fall. The certificate, not this number, decides what is established.
    pub initial_cells: u32,
    /// How many times a cell carrying more than one feature may be halved before the organ stops
    /// and deposits an obstruction. Reaching this bound is a *reported* outcome, never a silent one.
    pub subdivision_bound: u32,
}

impl ReceiverWindow {
    pub fn new(
        lower: Rat,
        upper: Rat,
        initial_cells: u32,
        subdivision_bound: u32,
    ) -> Result<Self, FaceError> {
        if lower >= upper {
            return Err(FaceError::EmptyWindow);
        }
        if initial_cells == 0 {
            return Err(FaceError::VacuousAperture);
        }
        Ok(Self {
            lower,
            upper,
            initial_cells,
            subdivision_bound,
        })
    }

    fn width(&self) -> Rat {
        &self.upper - &self.lower
    }
}

/// A feature the certificate located: one distinct real root, isolated to a rational interval.
///
/// `interval` provably contains exactly one root. That is a Sturm certificate, not a tolerance:
/// the enclosure may be wide, and it is still exact testimony about how many roots are inside it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LocatedFeature {
    pub interval: ExactInterval,
    pub variations_at_lower: u32,
    pub variations_at_upper: u32,
}

/// A cell the organ could not decide, carried in the face rather than smoothed away.
///
/// This is the type whose existence is the entire argument of the module. An adaptive sampler has
/// no such type: when it stops subdividing it emits geometry regardless, and the failure is
/// indistinguishable from success.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CellObstruction {
    pub interval: ExactInterval,
    /// How many distinct roots the Sturm sequence proves are in this cell. The organ knows the
    /// count even when it has not separated them -- that is what makes this an obstruction with
    /// content rather than a failure.
    pub unresolved_feature_count: u32,
    pub reason: ObstructionReason,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ObstructionReason {
    /// The subdivision bound was reached with more than one feature still in the cell.
    SubdivisionBoundReached,
}

/// One exactly evaluated station on the curve.
///
/// Both coordinates are exact rationals. `ordinate` is the polynomial's exact value at `abscissa`;
/// nothing is rounded, and there is no decimal anywhere in this type.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactStation {
    pub abscissa: Rat,
    pub ordinate: Rat,
}

/// The returned face: exact stations, certified features, and the obstructions.
///
/// This is the `StandardForm` of the figure in Wolfram's sense -- the invertible one. A rendered
/// picture is the `TraditionalForm`, and by the document law the lossy face may never be the only
/// artifact.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CertifiedFace {
    pub schema: String,
    pub window: ReceiverWindow,
    pub stations: Vec<ExactStation>,
    pub features: Vec<LocatedFeature>,
    pub obstructions: Vec<CellObstruction>,
    /// Distinct real roots the Sturm sequence counted over the whole window, independent of
    /// whether they were separated. The face's own cross-check: located + unresolved must equal it.
    pub certified_feature_count: u32,
}

impl CertifiedFace {
    /// Every cell was decided.
    pub fn is_complete(&self) -> bool {
        self.obstructions.is_empty()
    }

    /// The count the certificate promised equals the count the face carries.
    ///
    /// This is the face's internal audit and it is checked on every construction. If it can fail,
    /// the organ is losing or inventing features somewhere in subdivision.
    pub fn population_reconciles(&self) -> bool {
        let unresolved: u32 = self
            .obstructions
            .iter()
            .map(|obstruction| obstruction.unresolved_feature_count)
            .sum();
        let located = u32::try_from(self.features.len()).unwrap_or(u32::MAX);
        located.saturating_add(unresolved) == self.certified_feature_count
    }

    /// Exact rows for the reader. No decimal expansion; `format_rat` prints `n` or `n/d`.
    pub fn station_rows(&self) -> Vec<(String, String)> {
        self.stations
            .iter()
            .map(|station| {
                (
                    format_rat(&station.abscissa),
                    format_rat(&station.ordinate),
                )
            })
            .collect()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum FaceError {
    #[error("the receiver window is empty or inverted")]
    EmptyWindow,
    #[error("a window must be cut into at least one cell")]
    VacuousAperture,
    #[error("the exact carrier refused: {0}")]
    Exact(#[from] ExactValueError),
}

/// Divide `polynomial` by the exact linear factor of the rational root `point`, repeatedly.
///
/// A root at a rational point is *exactly known*, so it is deflated away rather than treated as an
/// impediment. For `point = n/d` in lowest terms, `(d·x − n)` divides the polynomial exactly, and
/// the synthetic division below is integer arithmetic throughout: the rational root theorem
/// guarantees every quotient in the recurrence is integral, so no remainder is ever discarded. The
/// loop repeats to strip a repeated root down to its last copy.
///
/// This is what lets a cell boundary sit exactly on a root without the count becoming unavailable.
/// The alternative — nudging the boundary until the Sturm count applies — is the
/// magic-number-and-retry defect `AGENTS.md` forbids.
fn deflate_at(polynomial: &IntegerPolynomial, point: &Rat) -> IntegerPolynomial {
    let mut current = polynomial.clone();
    while current.degree() > 0 && current.evaluate(point).is_zero() {
        let numerator = point.numer().clone();
        let denominator = point.denom().clone();
        // Ascending coefficients, as `IntegerPolynomial::evaluate` reads them.
        let ascending = current.coefficients.clone();
        let degree = ascending.len() - 1;
        let mut quotient_descending: Vec<BigInt> = Vec::with_capacity(degree);
        // Descending recurrence: A_m = d·B_{m-1}; A_j = d·B_{j-1} − n·B_j.
        let mut carry = &ascending[degree] / &denominator;
        quotient_descending.push(carry.clone());
        for index in (1..degree).rev() {
            let next = (&ascending[index] + &numerator * &carry) / &denominator;
            quotient_descending.push(next.clone());
            carry = next;
        }
        let mut quotient: Vec<BigInt> = quotient_descending.into_iter().rev().collect();
        if quotient.is_empty() {
            quotient.push(BigInt::from(1));
        }
        match IntegerPolynomial::new(quotient) {
            Ok(next) => current = next,
            Err(_) => break,
        }
    }
    current
}

/// Distinct roots in the closed interval `[lower, upper]`, returned with the exactly rational
/// endpoint roots separated out.
///
/// Returns `(endpoint_roots, interior_count, deflated)`. The deflated polynomial has no root at
/// either endpoint, so `distinct_root_count` applies to it without refusal.
fn closed_interval_census(
    polynomial: &IntegerPolynomial,
    lower: &Rat,
    upper: &Rat,
) -> (Vec<Rat>, u32, IntegerPolynomial) {
    let mut endpoint_roots = Vec::new();
    let mut working = polynomial.clone();
    if working.evaluate(lower).is_zero() {
        endpoint_roots.push(lower.clone());
        working = deflate_at(&working, lower);
    }
    if working.evaluate(upper).is_zero() {
        endpoint_roots.push(upper.clone());
        working = deflate_at(&working, upper);
    }
    let interior = if working.degree() == 0 {
        0
    } else {
        match ExactInterval::new(lower.clone(), upper.clone()) {
            Ok(interval) => working.distinct_root_count(&interval).unwrap_or(0),
            Err(_) => 0,
        }
    };
    (endpoint_roots, interior, working)
}

/// Certify the feature population of `polynomial` over `window`, and return the face.
///
/// The whole-window count is taken first, so the face can audit itself: whatever subdivision does,
/// located features plus unresolved features must equal the number certified at the outset. That
/// check is not a formality -- it is what makes a lost feature a test failure rather than a
/// slightly emptier picture.
pub fn certify_face(
    polynomial: &IntegerPolynomial,
    window: &ReceiverWindow,
) -> Result<CertifiedFace, FaceError> {
    // Guard the window shape through the exact carrier before any counting.
    let _ = ExactInterval::new(window.lower.clone(), window.upper.clone())?;
    let (window_endpoint_roots, window_interior, _) =
        closed_interval_census(polynomial, &window.lower, &window.upper);
    let certified_feature_count =
        u32::try_from(window_endpoint_roots.len()).unwrap_or(0) + window_interior;

    let mut features = Vec::new();
    let mut obstructions = Vec::new();
    let width = window.width();
    let cells = Rat::from_integer(window.initial_cells.into());
    let step = &width / &cells;

    // Every cell boundary is inspected exactly once, so a root sitting on a shared boundary is
    // located once rather than claimed by both neighbouring cells.
    for index in 0..=window.initial_cells {
        let boundary = &window.lower + &step * Rat::from_integer(index.into());
        if polynomial.evaluate(&boundary).is_zero() {
            features.push(LocatedFeature {
                interval: ExactInterval::point(boundary),
                variations_at_lower: 0,
                variations_at_upper: 0,
            });
        }
    }

    for index in 0..window.initial_cells {
        let lower = &window.lower + &step * Rat::from_integer(index.into());
        let upper = &window.lower + &step * Rat::from_integer((index + 1).into());
        // Deflating at both ends leaves a polynomial whose roots in this cell are strictly
        // interior; the boundary roots were already located above.
        let (_, _, interior_polynomial) = closed_interval_census(polynomial, &lower, &upper);
        resolve_cell(
            &interior_polynomial,
            &lower,
            &upper,
            window.subdivision_bound,
            &mut features,
            &mut obstructions,
        );
    }

    let stations = exact_stations(polynomial, window);

    Ok(CertifiedFace {
        schema: "holonic-engine.certified-face.v1".to_string(),
        window: window.clone(),
        stations,
        features,
        obstructions,
        certified_feature_count,
    })
}

/// The per-cell law. Count exactly; recurse only with the count as the certificate.
///
/// `polynomial` here is already deflated at the cell's own endpoints, so every root it still
/// carries inside the cell is strictly interior.
fn resolve_cell(
    polynomial: &IntegerPolynomial,
    lower: &Rat,
    upper: &Rat,
    remaining_subdivisions: u32,
    features: &mut Vec<LocatedFeature>,
    obstructions: &mut Vec<CellObstruction>,
) {
    if polynomial.degree() == 0 {
        return;
    }
    let interval = match ExactInterval::new(lower.clone(), upper.clone()) {
        Ok(interval) => interval,
        Err(_) => return,
    };

    let Ok(count) = polynomial.distinct_root_count(&interval) else {
        return;
    };

    if count == 0 {
        // Certified featureless. This is the sentence a sampler cannot say.
        return;
    }

    if count == 1 {
        let variations = sturm_variations(polynomial, &interval);
        features.push(LocatedFeature {
            interval,
            variations_at_lower: variations.0,
            variations_at_upper: variations.1,
        });
        return;
    }

    if remaining_subdivisions == 0 {
        // More than one feature, and no budget left to separate them. The count is still exact,
        // so the obstruction carries real content: it says how many are in there.
        obstructions.push(CellObstruction {
            interval,
            unresolved_feature_count: count,
            reason: ObstructionReason::SubdivisionBoundReached,
        });
        return;
    }

    let midpoint = (lower + upper) / integer(2);
    // The midpoint may itself be an exact rational root. Locate it once and deflate, so neither
    // half claims it and the population still reconciles.
    let mut working = polynomial.clone();
    if working.evaluate(&midpoint).is_zero() {
        features.push(LocatedFeature {
            interval: ExactInterval::point(midpoint.clone()),
            variations_at_lower: 0,
            variations_at_upper: 0,
        });
        working = deflate_at(&working, &midpoint);
    }
    resolve_cell(
        &working,
        lower,
        &midpoint,
        remaining_subdivisions - 1,
        features,
        obstructions,
    );
    resolve_cell(
        &working,
        &midpoint,
        upper,
        remaining_subdivisions - 1,
        features,
        obstructions,
    );
}

fn sturm_variations(polynomial: &IntegerPolynomial, interval: &ExactInterval) -> (u32, u32) {
    // The isolation certificate carries the variation counts; recovering them here keeps the
    // located feature self-describing without re-deriving the sequence at the call site.
    match crate::exact_value::AlgebraicRoot::isolate(polynomial.clone(), interval.clone()) {
        Ok(root) => (
            root.certificate.variations_at_lower,
            root.certificate.variations_at_upper,
        ),
        Err(_) => (0, 0),
    }
}

/// Exact evaluation at each cell boundary. No sampling decision is made here; the station grid is
/// the receiver's declared aperture and nothing else.
fn exact_stations(polynomial: &IntegerPolynomial, window: &ReceiverWindow) -> Vec<ExactStation> {
    let width = window.width();
    let cells = Rat::from_integer(window.initial_cells.into());
    (0..=window.initial_cells)
        .map(|index| {
            let abscissa = &window.lower + &width * Rat::from_integer(index.into()) / &cells;
            let ordinate = polynomial.evaluate(&abscissa);
            ExactStation { abscissa, ordinate }
        })
        .collect()
}

/// Sign changes across consecutive stations.
///
/// Reported so a reader can compare the *naive* reading of the same data against the certificate.
/// Where these disagree, the certificate is right and the disagreement is the point: it is the
/// exact quantity a sampling plotter would have gotten wrong.
pub fn station_sign_changes(face: &CertifiedFace) -> u32 {
    let mut changes = 0;
    for pair in face.stations.windows(2) {
        let left = &pair[0].ordinate;
        let right = &pair[1].ordinate;
        if left.is_zero() || right.is_zero() {
            continue;
        }
        if left.is_negative() != right.is_negative() {
            changes += 1;
        }
    }
    changes
}

/// What the emitted face may legally contain, as a census the falsifier can read.
///
/// `marks` counts every drawable thing the face licenses. The non-creation control requires it to
/// be derived from source structure and never to exceed it.
pub fn mark_census(face: &CertifiedFace) -> BTreeMap<String, usize> {
    let mut census = BTreeMap::new();
    census.insert("stations".to_string(), face.stations.len());
    census.insert("features".to_string(), face.features.len());
    census.insert("obstructions".to_string(), face.obstructions.len());
    census
}

#[cfg(test)]
mod tests {
    //! Controls for the certified face.
    //!
    //! Every law here must be capable of returning non-zero and capable of failing. A test that
    //! could not have come out otherwise carries no evidence (`CLAUDE.md` §8), so each positive
    //! control is paired with the negative one that proves the law is looking.

    use num_bigint::BigInt;
    use relational_geometry::rat;

    use super::*;

    /// x^2 - 2. One root in [0,2] (sqrt 2), irrational and therefore representable by no rational
    /// sample. A sampler can only bracket it; the certificate counts it exactly.
    fn quadratic_two() -> IntegerPolynomial {
        IntegerPolynomial::new(vec![BigInt::from(-2), BigInt::from(0), BigInt::from(1)])
            .expect("degree two")
    }

    /// (x-1)(x-2)(x-3) = x^3 - 6x^2 + 11x - 6. Three simple rational roots.
    fn cubic_three_roots() -> IntegerPolynomial {
        IntegerPolynomial::new(vec![
            BigInt::from(-6),
            BigInt::from(11),
            BigInt::from(-6),
            BigInt::from(1),
        ])
        .expect("degree three")
    }

    /// x^2 + 1. No real roots anywhere: the featureless control.
    fn no_real_roots() -> IntegerPolynomial {
        IntegerPolynomial::new(vec![BigInt::from(1), BigInt::from(0), BigInt::from(1)])
            .expect("degree two")
    }

    /// 1000000 x^2 - 1, i.e. roots at ±1/1000: two features closer together than any coarse cell.
    fn narrow_pair() -> IntegerPolynomial {
        IntegerPolynomial::new(vec![
            BigInt::from(-1),
            BigInt::from(0),
            BigInt::from(1_000_000),
        ])
        .expect("degree two")
    }

    #[test]
    fn a_featureless_window_returns_no_features_and_no_obstructions() {
        // The control that keeps the obstruction law honest. If this obstructed, the organ would
        // obstruct everything and the obstruction population would carry no information.
        let window = ReceiverWindow::new(integer(-3), integer(3), 8, 6).expect("window");
        let face = certify_face(&no_real_roots(), &window).expect("face");
        assert_eq!(face.certified_feature_count, 0);
        assert!(face.features.is_empty());
        assert!(
            face.obstructions.is_empty(),
            "a featureless curve must not obstruct: {:?}",
            face.obstructions
        );
        assert!(face.is_complete());
        assert!(face.population_reconciles());
    }

    #[test]
    fn three_separated_roots_are_all_located() {
        let window = ReceiverWindow::new(rat(1, 2), rat(7, 2), 8, 8).expect("window");
        let face = certify_face(&cubic_three_roots(), &window).expect("face");
        assert_eq!(face.certified_feature_count, 3);
        assert_eq!(face.features.len(), 3);
        assert!(face.obstructions.is_empty());
        assert!(face.population_reconciles());
    }

    #[test]
    fn an_irrational_root_is_located_without_any_float() {
        let window = ReceiverWindow::new(integer(0), integer(2), 4, 8).expect("window");
        let face = certify_face(&quadratic_two(), &window).expect("face");
        assert_eq!(face.certified_feature_count, 1);
        assert_eq!(face.features.len(), 1);
        let located = &face.features[0];
        assert!(located.interval.lower < rat(3, 2));
        assert!(located.interval.upper > rat(7, 5));
        assert!(face.population_reconciles());
    }

    /// FALSIFIER ONE — the obstruction falsifier.
    ///
    /// Two roots closer together than the cell width, with the subdivision budget removed. A
    /// sampler's documented behaviour here is to miss them silently. This organ must return them
    /// as an obstruction that states the count it could not separate.
    #[test]
    fn an_unresolvable_cell_returns_an_obstruction_carrying_its_exact_count() {
        let window = ReceiverWindow::new(integer(-1), integer(1), 1, 0).expect("window");
        let face = certify_face(&narrow_pair(), &window).expect("face");

        assert_eq!(face.certified_feature_count, 2, "both roots are counted");
        assert!(
            face.features.is_empty(),
            "with no budget neither root can be separated"
        );
        assert_eq!(
            face.obstructions.len(),
            1,
            "the unresolved cell must be returned, not dropped"
        );
        assert_eq!(
            face.obstructions[0].unresolved_feature_count, 2,
            "the obstruction states how many features it could not separate"
        );
        assert_eq!(
            face.obstructions[0].reason,
            ObstructionReason::SubdivisionBoundReached
        );
        assert!(!face.is_complete());
        assert!(face.population_reconciles());
    }

    /// The other half of falsifier one: given budget, the same pair IS separated. Without this,
    /// the obstruction above could be an organ that never resolves anything.
    #[test]
    fn the_same_pair_resolves_once_the_budget_allows_it() {
        let window = ReceiverWindow::new(integer(-1), integer(1), 1, 24).expect("window");
        let face = certify_face(&narrow_pair(), &window).expect("face");
        assert_eq!(face.certified_feature_count, 2);
        assert_eq!(face.features.len(), 2, "with budget both roots separate");
        assert!(face.obstructions.is_empty());
        assert!(face.population_reconciles());
    }

    #[test]
    fn the_population_always_reconciles_across_subdivision_budgets() {
        // Whatever subdivision does, located + unresolved must equal the whole-window count. The
        // sweep is how a lost feature shows up as a failure rather than a thinner picture.
        let cubic = cubic_three_roots();
        for budget in 0..10 {
            for cells in 1..6 {
                let window =
                    ReceiverWindow::new(rat(1, 2), rat(7, 2), cells, budget).expect("window");
                let face = certify_face(&cubic, &window).expect("face");
                assert_eq!(face.certified_feature_count, 3);
                assert!(
                    face.population_reconciles(),
                    "cells={cells} budget={budget} lost or invented a feature: located={} unresolved={:?}",
                    face.features.len(),
                    face.obstructions
                );
            }
        }
    }

    #[test]
    fn the_certified_count_is_independent_of_the_aperture() {
        // The aperture is a receiver coordinate. The feature count in the window is not.
        let cubic = cubic_three_roots();
        let counts: Vec<u32> = (1..12)
            .map(|cells| {
                let window = ReceiverWindow::new(rat(1, 2), rat(7, 2), cells, 8).expect("window");
                certify_face(&cubic, &window)
                    .expect("face")
                    .certified_feature_count
            })
            .collect();
        assert!(
            counts.iter().all(|count| *count == 3),
            "the certificate moved with the aperture: {counts:?}"
        );
    }

    /// FALSIFIER THREE, first half — non-creation.
    #[test]
    fn emitted_marks_never_exceed_source_structure() {
        let cubic = cubic_three_roots();
        for cells in 1..10 {
            let window = ReceiverWindow::new(rat(1, 2), rat(7, 2), cells, 8).expect("window");
            let face = certify_face(&cubic, &window).expect("face");
            let census = mark_census(&face);
            assert_eq!(
                census["stations"],
                (cells + 1) as usize,
                "a station is a declared cell boundary and nothing else"
            );
            let source_items =
                face.features.len() + face.obstructions.len() + (cells + 1) as usize;
            let total_marks: usize = census.values().sum();
            assert!(
                total_marks <= source_items,
                "the face minted geometry: {total_marks} marks from {source_items} source items"
            );
        }
    }

    #[test]
    fn every_station_ordinate_is_the_exact_polynomial_value() {
        let cubic = cubic_three_roots();
        let window = ReceiverWindow::new(integer(0), integer(4), 9, 4).expect("window");
        let face = certify_face(&cubic, &window).expect("face");
        for station in &face.stations {
            assert_eq!(
                station.ordinate,
                cubic.evaluate(&station.abscissa),
                "a station ordinate diverged from the exact evaluation"
            );
        }
    }

    #[test]
    fn the_naive_sign_reading_and_the_certificate_disagree_and_the_certificate_governs() {
        // The whole argument, made measurable. Two roots inside one cell produce NO sign change
        // across that cell's endpoints: the naive reading a sampling plotter uses sees nothing,
        // while the Sturm certificate counts two.
        let window = ReceiverWindow::new(integer(-1), integer(1), 1, 0).expect("window");
        let face = certify_face(&narrow_pair(), &window).expect("face");
        let naive = station_sign_changes(&face);
        assert_eq!(naive, 0, "the sampled reading sees no sign change");
        assert_eq!(face.certified_feature_count, 2, "the certificate knows two");
        assert!(
            u32::try_from(face.features.len()).unwrap() + naive < face.certified_feature_count,
            "the disagreement is the point and must be visible in the artifact"
        );
    }

    #[test]
    fn an_inverted_window_is_refused_rather_than_silently_swapped() {
        assert_eq!(
            ReceiverWindow::new(integer(3), integer(1), 4, 4).unwrap_err(),
            FaceError::EmptyWindow
        );
    }

    #[test]
    fn a_vacuous_aperture_is_refused() {
        assert_eq!(
            ReceiverWindow::new(integer(0), integer(1), 0, 4).unwrap_err(),
            FaceError::VacuousAperture
        );
    }

    #[test]
    fn a_root_exactly_on_the_window_boundary_is_located_not_obstructed() {
        // x^2 - 1 has a root at each endpoint of [-1,1]. A rational root is EXACTLY known, so
        // deflating it away and locating it is the correct reading; calling it unresolved would
        // be the organ declaring ignorance of something it can name exactly. Nudging the window
        // until the Sturm count applies would be the magic-number-and-retry defect instead.
        //
        // This control exists because the first implementation got it wrong in both directions at
        // once: it obstructed on the boundary AND double-counted the root across the two adjacent
        // cells, which `population_reconciles` caught.
        let polynomial =
            IntegerPolynomial::new(vec![BigInt::from(-1), BigInt::from(0), BigInt::from(1)])
                .expect("degree two");
        let window = ReceiverWindow::new(integer(-1), integer(1), 4, 4).expect("window");
        let face = certify_face(&polynomial, &window).expect("face");
        assert_eq!(face.certified_feature_count, 2, "both roots are counted");
        assert_eq!(face.features.len(), 2, "and both are located exactly");
        assert!(
            face.obstructions.is_empty(),
            "an exactly known rational root is not an obstruction: {:?}",
            face.obstructions
        );
        assert!(face.population_reconciles());
        // Each located root is a degenerate interval carrying the exact rational.
        let located: Vec<Rat> = face
            .features
            .iter()
            .map(|feature| feature.interval.lower.clone())
            .collect();
        assert!(located.contains(&integer(-1)) && located.contains(&integer(1)));
    }

    #[test]
    fn a_root_on_an_interior_cell_boundary_is_counted_exactly_once() {
        // The double-count this organ's first implementation had. x^2 - 4 over [-4,4] cut into 4
        // cells puts roots at -2 and +2 exactly on interior cell boundaries.
        let polynomial =
            IntegerPolynomial::new(vec![BigInt::from(-4), BigInt::from(0), BigInt::from(1)])
                .expect("degree two");
        let window = ReceiverWindow::new(integer(-4), integer(4), 4, 6).expect("window");
        let face = certify_face(&polynomial, &window).expect("face");
        assert_eq!(face.certified_feature_count, 2);
        assert_eq!(
            face.features.len(),
            2,
            "a shared cell boundary claimed the root twice"
        );
        assert!(face.population_reconciles());
    }

    #[test]
    fn exact_deflation_divides_without_remainder() {
        // The deflation is integer synthetic division and must be exact. Deflating a known root
        // has to return a polynomial that still vanishes at the OTHER roots and no longer at the
        // deflated one.
        let cubic = cubic_three_roots();
        let deflated = deflate_at(&cubic, &integer(2));
        assert!(
            !deflated.evaluate(&integer(2)).is_zero(),
            "the deflated root survived"
        );
        assert!(
            deflated.evaluate(&integer(1)).is_zero() && deflated.evaluate(&integer(3)).is_zero(),
            "deflation destroyed the other roots"
        );
        assert_eq!(deflated.degree(), 2, "degree must drop by exactly one");
    }

    #[test]
    fn deflation_strips_a_repeated_root_completely() {
        // (x-1)^3: the loop must remove every copy, leaving a polynomial with no root at 1.
        let cubed = IntegerPolynomial::new(vec![
            BigInt::from(-1),
            BigInt::from(3),
            BigInt::from(-3),
            BigInt::from(1),
        ])
        .expect("degree three");
        let deflated = deflate_at(&cubed, &integer(1));
        assert!(!deflated.evaluate(&integer(1)).is_zero());
        assert_eq!(deflated.degree(), 0, "all three copies were stripped");
    }

    #[test]
    fn deflation_is_exact_at_a_non_integer_rational_root() {
        // 2x - 1 has the root 1/2. Synthetic division by (d·x − n) must stay integral.
        let linear =
            IntegerPolynomial::new(vec![BigInt::from(-1), BigInt::from(2)]).expect("degree one");
        assert!(linear.evaluate(&rat(1, 2)).is_zero());
        let deflated = deflate_at(&linear, &rat(1, 2));
        assert_eq!(deflated.degree(), 0);
    }

    #[test]
    fn the_face_carries_no_decimal_expansion_anywhere() {
        // A decimal point in a presented row would mean a float reached the presentation
        // boundary, which is the one thing this organ exists to prevent.
        let window = ReceiverWindow::new(integer(0), integer(2), 3, 6).expect("window");
        let face = certify_face(&quadratic_two(), &window).expect("face");
        for (abscissa, ordinate) in face.station_rows() {
            assert!(
                !abscissa.contains('.') && !ordinate.contains('.'),
                "a decimal expansion reached a presented row: {abscissa} {ordinate}"
            );
        }
    }

    #[test]
    fn a_rational_window_with_awkward_denominators_stays_exact() {
        // Thirds and sevenths terminate in no binary or decimal float. They are exact here.
        let window = ReceiverWindow::new(rat(1, 3), rat(22, 7), 7, 5).expect("window");
        let face = certify_face(&cubic_three_roots(), &window).expect("face");
        assert!(face.population_reconciles());
        let last = face.stations.last().expect("stations exist");
        assert_eq!(
            last.abscissa,
            rat(22, 7),
            "the window endpoint survived the cell arithmetic exactly"
        );
        assert_eq!(last.ordinate, cubic_three_roots().evaluate(&rat(22, 7)));
    }

    #[test]
    fn a_high_multiplicity_root_counts_once_as_a_distinct_root() {
        // (x-1)^3. Sturm counts DISTINCT roots, so this is one feature, not three. Recorded
        // because a reader could reasonably expect three, and the distinction is exact.
        let cubed = IntegerPolynomial::new(vec![
            BigInt::from(-1),
            BigInt::from(3),
            BigInt::from(-3),
            BigInt::from(1),
        ])
        .expect("degree three");
        let window = ReceiverWindow::new(integer(0), integer(3), 6, 6).expect("window");
        let face = certify_face(&cubed, &window).expect("face");
        assert_eq!(
            face.certified_feature_count, 1,
            "a triple root is one distinct root"
        );
        assert!(face.population_reconciles());
    }

    #[test]
    fn the_station_grid_scales_with_the_declared_aperture_only() {
        let cubic = cubic_three_roots();
        let widths: Vec<usize> = [2u32, 4, 8, 16]
            .into_iter()
            .map(|cells| {
                let window = ReceiverWindow::new(integer(0), integer(4), cells, 4).expect("window");
                certify_face(&cubic, &window).expect("face").stations.len()
            })
            .collect();
        assert_eq!(
            widths,
            vec![3, 5, 9, 17],
            "stations are exactly one per cell boundary"
        );
    }

    #[test]
    fn a_wider_window_can_only_gain_features_never_lose_them() {
        let cubic = cubic_three_roots();
        let narrow = ReceiverWindow::new(rat(3, 2), rat(5, 2), 4, 6).expect("window");
        let wide = ReceiverWindow::new(rat(1, 2), rat(7, 2), 4, 6).expect("window");
        let narrow_face = certify_face(&cubic, &narrow).expect("face");
        let wide_face = certify_face(&cubic, &wide).expect("face");
        assert_eq!(narrow_face.certified_feature_count, 1);
        assert_eq!(wide_face.certified_feature_count, 3);
        assert!(wide_face.certified_feature_count >= narrow_face.certified_feature_count);
    }

    #[test]
    fn the_fixtures_are_what_they_claim_to_be() {
        // If these polynomials are not what the comments say, every count above measures the
        // wrong object.
        let cubic = cubic_three_roots();
        for root in [integer(1), integer(2), integer(3)] {
            assert!(
                cubic.evaluate(&root).is_zero(),
                "cubic_three_roots does not vanish at a claimed root"
            );
        }
        assert_eq!(
            quadratic_two().evaluate(&integer(2)),
            integer(2),
            "quadratic_two is not x^2 - 2"
        );
        assert!(narrow_pair().evaluate(&rat(1, 1000)).is_zero());
    }
}
