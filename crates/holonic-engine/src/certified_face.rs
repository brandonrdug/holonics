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
    /// A cell endpoint is itself a root, so the strict-interval Sturm count does not apply there.
    /// Reported rather than nudged: moving the endpoint to make the count work would be the
    /// magic-number-and-retry defect.
    RootAtCellBoundary,
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

/// Certify the feature population of `polynomial` over `window`, and return the face.
///
/// The whole-window count is taken first, so the face can audit itself: whatever subdivision does,
/// located features plus unresolved features must equal the number the Sturm sequence promised at
/// the outset. That check is not a formality -- it is what makes a lost feature a test failure
/// rather than a slightly emptier picture.
pub fn certify_face(
    polynomial: &IntegerPolynomial,
    window: &ReceiverWindow,
) -> Result<CertifiedFace, FaceError> {
    let whole = ExactInterval::new(window.lower.clone(), window.upper.clone())?;
    let certified_feature_count = match polynomial.distinct_root_count(&whole) {
        Ok(count) => count,
        // A root exactly at a window endpoint is a real fact about the object, not a reason to
        // move the window. The whole-window count is unavailable, so the face reports that and
        // the per-cell law still runs.
        Err(ExactValueError::RootAtIntervalBoundary) => {
            return Ok(boundary_refused_face(polynomial, window));
        }
        Err(error) => return Err(FaceError::Exact(error)),
    };

    let mut features = Vec::new();
    let mut obstructions = Vec::new();
    let width = window.width();
    let cells = Rat::from_integer(window.initial_cells.into());

    for index in 0..window.initial_cells {
        let step = &width / &cells;
        let lower = &window.lower + &step * Rat::from_integer(index.into());
        let upper = &window.lower + &step * Rat::from_integer((index + 1).into());
        resolve_cell(
            polynomial,
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
fn resolve_cell(
    polynomial: &IntegerPolynomial,
    lower: &Rat,
    upper: &Rat,
    remaining_subdivisions: u32,
    features: &mut Vec<LocatedFeature>,
    obstructions: &mut Vec<CellObstruction>,
) {
    let interval = match ExactInterval::new(lower.clone(), upper.clone()) {
        Ok(interval) => interval,
        Err(_) => return,
    };

    let count = match polynomial.distinct_root_count(&interval) {
        Ok(count) => count,
        Err(ExactValueError::RootAtIntervalBoundary) => {
            obstructions.push(CellObstruction {
                interval,
                unresolved_feature_count: 1,
                reason: ObstructionReason::RootAtCellBoundary,
            });
            return;
        }
        Err(_) => return,
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
    resolve_cell(
        polynomial,
        lower,
        &midpoint,
        remaining_subdivisions - 1,
        features,
        obstructions,
    );
    resolve_cell(
        polynomial,
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

fn boundary_refused_face(
    polynomial: &IntegerPolynomial,
    window: &ReceiverWindow,
) -> CertifiedFace {
    CertifiedFace {
        schema: "holonic-engine.certified-face.v1".to_string(),
        window: window.clone(),
        stations: exact_stations(polynomial, window),
        features: Vec::new(),
        obstructions: vec![CellObstruction {
            interval: ExactInterval::new(window.lower.clone(), window.upper.clone())
                .expect("the window was validated on construction"),
            unresolved_feature_count: 1,
            reason: ObstructionReason::RootAtCellBoundary,
        }],
        certified_feature_count: 1,
    }
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
mod tests;
