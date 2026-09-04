//! Exact co-present receiver atlases.
//!
//! A receiver face is not an independently populated screen.  Every face in
//! this module is projected from the same marked occurrence population.  The
//! joint object therefore contains only tuples which actually share a source
//! occurrence; it never completes those tuples to a Cartesian product.

use std::collections::{BTreeMap, BTreeSet};

use num_traits::{One, Signed, ToPrimitive, Zero};
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::exact::{Rat, RatVec2, RatVec3, integer};
use crate::model::{Construction, FrameId};
use crate::projection::{
    CrossingAnalysis, ProjectedPoint, ProjectionError, Receiver, ReceiverId, analyze_crossings,
    project_point,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct OccurrenceId(pub u64);

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MarkedOccurrence {
    pub id: OccurrenceId,
    pub name: String,
    pub frame: FrameId,
    pub point: RatVec3,
}

impl MarkedOccurrence {
    pub fn new(id: OccurrenceId, name: impl Into<String>, frame: FrameId, point: RatVec3) -> Self {
        Self {
            id,
            name: name.into(),
            frame,
            point,
        }
    }
}

/// One finite face quotient.
///
/// The horizontal receiving interval is `[-width/height,width/height]` and
/// the vertical interval is `[-1,1]`.  Pixel apertures therefore retain the
/// exact aspect ratio without a rendering scalar.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverGrain {
    pub width: u32,
    pub height: u32,
}

impl ReceiverGrain {
    pub fn new(width: u32, height: u32) -> Self {
        assert!(width > 0, "a receiver grain must have positive width");
        assert!(height > 0, "a receiver grain must have positive height");
        Self { width, height }
    }

    pub fn aspect_ratio(&self) -> Rat {
        integer(i64::from(self.width)) / integer(i64::from(self.height))
    }

    pub fn aperture(&self, column: u32, row: u32) -> Option<PixelAperture> {
        if column >= self.width || row >= self.height {
            return None;
        }
        let width = i64::from(self.width);
        let height = i64::from(self.height);
        let column = i64::from(column);
        let row = i64::from(row);
        Some(PixelAperture {
            cell: PixelCell {
                column: column as u32,
                row: row as u32,
            },
            x_min: integer(2 * column - width) / integer(height),
            x_max: integer(2 * (column + 1) - width) / integer(height),
            y_min: integer(2 * row - height) / integer(height),
            y_max: integer(2 * (row + 1) - height) / integer(height),
        })
    }

    /// Return every closed aperture containing the exact point.
    ///
    /// A point on a seam deliberately returns two or four cells.  Selecting
    /// one by array convention would erase a real receiver discriminant.
    pub fn address(&self, point: &RatVec2) -> ApertureAddress {
        let columns = axis_cells(&point.x, self.width, self.height, self.width);
        let rows = axis_cells(&point.y, self.height, self.height, self.height);
        let mut cells = Vec::new();
        for row in rows {
            for column in &columns {
                cells.push(PixelCell {
                    column: *column,
                    row,
                });
            }
        }
        ApertureAddress { cells }
    }
}

fn axis_cells(coordinate: &Rat, cell_count: u32, coordinate_scale: u32, offset: u32) -> Vec<u32> {
    let scaled = (integer(i64::from(coordinate_scale)) * coordinate + integer(i64::from(offset)))
        / integer(2);
    if scaled.is_negative() || scaled > integer(i64::from(cell_count)) {
        return Vec::new();
    }

    if scaled.denom().is_one() {
        let seam = scaled
            .numer()
            .to_u32()
            .expect("a bounded nonnegative seam fits in u32");
        let mut cells = Vec::with_capacity(2);
        if seam > 0 {
            cells.push(seam - 1);
        }
        if seam < cell_count {
            cells.push(seam);
        }
        cells
    } else {
        let floor = (scaled.numer() / scaled.denom())
            .to_u32()
            .expect("a bounded nonnegative aperture coordinate fits in u32");
        vec![floor]
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct PixelCell {
    pub column: u32,
    pub row: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PixelAperture {
    pub cell: PixelCell,
    pub x_min: Rat,
    pub x_max: Rat,
    pub y_min: Rat,
    pub y_max: Rat,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ApertureAddress {
    pub cells: Vec<PixelCell>,
}

impl ApertureAddress {
    pub fn is_outside(&self) -> bool {
        self.cells.is_empty()
    }

    pub fn shares_cell_with(&self, other: &Self) -> bool {
        self.cells
            .iter()
            .any(|cell| other.cells.iter().any(|candidate| candidate == cell))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GrainedReceiver {
    pub receiver: Receiver,
    pub grain: ReceiverGrain,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SwingCell {
    pub id: u64,
    pub name: String,
    /// Three marked occurrences establish the local projective frame.
    pub pivot: [OccurrenceId; 3],
    /// The fourth occurrence supplies the cross-ratio coordinate.
    pub witness: OccurrenceId,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceivedOccurrence {
    pub occurrence: OccurrenceId,
    pub name: String,
    pub projected: ProjectedPoint,
    pub aperture: Option<ApertureAddress>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceivedSwing {
    pub cell: u64,
    pub cross_ratio: Rat,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverAtlasFace {
    pub receiver: ReceiverId,
    pub receiver_name: String,
    pub grain: ReceiverGrain,
    pub occurrences: Vec<ReceivedOccurrence>,
    pub swings: Vec<ReceivedSwing>,
    pub crossings: CrossingAnalysis,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct JointOccurrence {
    pub occurrence: OccurrenceId,
    pub faces: BTreeMap<ReceiverId, ReceivedOccurrence>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct JointSwing {
    pub cell: u64,
    pub name: String,
    pub receiver_values: BTreeMap<ReceiverId, Rat>,
    /// Present exactly when every participating receiver carries one value.
    pub invariant: Option<Rat>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GrainComparison {
    pub first: OccurrenceId,
    pub second: OccurrenceId,
    pub indistinguishable_at: Vec<ReceiverId>,
    pub distinguished_at: Vec<ReceiverId>,
    pub unaddressed_at: Vec<ReceiverId>,
}

impl GrainComparison {
    pub fn jointly_distinguished(&self) -> bool {
        !self.distinguished_at.is_empty()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct JointReceiverAtlas {
    pub schema: String,
    pub faces: Vec<ReceiverAtlasFace>,
    pub occurrences: Vec<JointOccurrence>,
    pub swings: Vec<JointSwing>,
    pub grain_comparisons: Vec<GrainComparison>,
}

impl JointReceiverAtlas {
    pub fn occurrence(&self, id: OccurrenceId) -> Option<&JointOccurrence> {
        self.occurrences
            .iter()
            .find(|occurrence| occurrence.occurrence == id)
    }

    pub fn swing(&self, id: u64) -> Option<&JointSwing> {
        self.swings.iter().find(|cell| cell.cell == id)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OccurrenceEmanation {
    pub occurrence: OccurrenceId,
    /// Exact face geometry changed at these receivers.
    pub changed_faces: Vec<ReceiverId>,
    /// Their finite quotient also changed.
    pub grain_visible_at: Vec<ReceiverId>,
    /// Exact geometry changed while the finite quotient retained one cell.
    pub grain_dark_at: Vec<ReceiverId>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SwingEmanation {
    pub cell: u64,
    pub before: Option<Rat>,
    pub after: Option<Rat>,
    pub changed_at: Vec<ReceiverId>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverAtlasEmanation {
    pub occurrences: Vec<OccurrenceEmanation>,
    pub swings: Vec<SwingEmanation>,
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum ReceiverAtlasError {
    #[error(transparent)]
    Projection(#[from] ProjectionError),
    #[error("receiver {0:?} occurs more than once in the same cut")]
    DuplicateReceiver(ReceiverId),
    #[error("marked occurrence {0:?} occurs more than once in the same cut")]
    DuplicateOccurrence(OccurrenceId),
    #[error("swing {cell} names missing occurrence {occurrence:?}")]
    MissingSwingOccurrence { cell: u64, occurrence: OccurrenceId },
    #[error("receiver {receiver:?} does not expose rational points for swing {cell}")]
    NonRationalSwing { receiver: ReceiverId, cell: u64 },
    #[error("swing {cell} is degenerate in receiver {receiver:?}: {reason}")]
    DegenerateSwing {
        receiver: ReceiverId,
        cell: u64,
        reason: CrossRatioRefusal,
    },
    #[error("atlas comparison requires the same receiver and occurrence identities")]
    IncompatibleAtlases,
}

pub fn analyze_receiver_atlas(
    construction: &Construction,
    receivers: &[GrainedReceiver],
    occurrences: &[MarkedOccurrence],
    swing_cells: &[SwingCell],
) -> Result<JointReceiverAtlas, ReceiverAtlasError> {
    ensure_unique_receivers(receivers)?;
    ensure_unique_occurrences(occurrences)?;

    let occurrence_rows = occurrences
        .iter()
        .map(|occurrence| (occurrence.id, occurrence))
        .collect::<BTreeMap<_, _>>();
    for cell in swing_cells {
        for occurrence in cell.pivot.into_iter().chain([cell.witness]) {
            if !occurrence_rows.contains_key(&occurrence) {
                return Err(ReceiverAtlasError::MissingSwingOccurrence {
                    cell: cell.id,
                    occurrence,
                });
            }
        }
    }

    let mut faces = Vec::new();
    for specification in receivers {
        let mut received = Vec::new();
        for occurrence in occurrences {
            let projected = project_point(
                construction,
                occurrence.frame,
                &occurrence.point,
                &specification.receiver,
            )?;
            let aperture = projected
                .rational
                .as_ref()
                .map(|point| specification.grain.address(point));
            received.push(ReceivedOccurrence {
                occurrence: occurrence.id,
                name: occurrence.name.clone(),
                projected,
                aperture,
            });
        }
        let received_rows = received
            .iter()
            .map(|occurrence| (occurrence.occurrence, occurrence))
            .collect::<BTreeMap<_, _>>();
        let mut swings = Vec::new();
        for cell in swing_cells {
            let ids = [cell.pivot[0], cell.pivot[1], cell.pivot[2], cell.witness];
            let mut points = Vec::with_capacity(4);
            for id in ids {
                let point = received_rows[&id].projected.rational.clone().ok_or(
                    ReceiverAtlasError::NonRationalSwing {
                        receiver: specification.receiver.id,
                        cell: cell.id,
                    },
                )?;
                points.push(point);
            }
            let cross_ratio =
                cross_ratio(&points).map_err(|reason| ReceiverAtlasError::DegenerateSwing {
                    receiver: specification.receiver.id,
                    cell: cell.id,
                    reason,
                })?;
            swings.push(ReceivedSwing {
                cell: cell.id,
                cross_ratio,
            });
        }
        faces.push(ReceiverAtlasFace {
            receiver: specification.receiver.id,
            receiver_name: specification.receiver.name.clone(),
            grain: specification.grain.clone(),
            occurrences: received,
            swings,
            crossings: analyze_crossings(construction, &specification.receiver)?,
        });
    }

    let joint_occurrences = occurrences
        .iter()
        .map(|occurrence| JointOccurrence {
            occurrence: occurrence.id,
            faces: faces
                .iter()
                .map(|face| {
                    (
                        face.receiver,
                        face.occurrences
                            .iter()
                            .find(|candidate| candidate.occurrence == occurrence.id)
                            .expect("every receiver projected every occurrence")
                            .clone(),
                    )
                })
                .collect(),
        })
        .collect::<Vec<_>>();

    let joint_swings = swing_cells
        .iter()
        .map(|cell| {
            let receiver_values = faces
                .iter()
                .map(|face| {
                    (
                        face.receiver,
                        face.swings
                            .iter()
                            .find(|candidate| candidate.cell == cell.id)
                            .expect("every receiver evaluated every swing")
                            .cross_ratio
                            .clone(),
                    )
                })
                .collect::<BTreeMap<_, _>>();
            let invariant = receiver_values
                .values()
                .next()
                .filter(|first| receiver_values.values().all(|value| value == *first))
                .cloned();
            JointSwing {
                cell: cell.id,
                name: cell.name.clone(),
                receiver_values,
                invariant,
            }
        })
        .collect::<Vec<_>>();

    let mut grain_comparisons = Vec::new();
    for first_index in 0..occurrences.len() {
        for second_index in (first_index + 1)..occurrences.len() {
            let first = occurrences[first_index].id;
            let second = occurrences[second_index].id;
            let mut indistinguishable_at = Vec::new();
            let mut distinguished_at = Vec::new();
            let mut unaddressed_at = Vec::new();
            for face in &faces {
                let left = face
                    .occurrences
                    .iter()
                    .find(|occurrence| occurrence.occurrence == first)
                    .expect("first occurrence was projected");
                let right = face
                    .occurrences
                    .iter()
                    .find(|occurrence| occurrence.occurrence == second)
                    .expect("second occurrence was projected");
                match (&left.aperture, &right.aperture) {
                    (Some(left), Some(right))
                        if !left.is_outside()
                            && !right.is_outside()
                            && left.shares_cell_with(right) =>
                    {
                        indistinguishable_at.push(face.receiver);
                    }
                    (Some(left), Some(right)) if !left.is_outside() && !right.is_outside() => {
                        distinguished_at.push(face.receiver);
                    }
                    _ => unaddressed_at.push(face.receiver),
                }
            }
            grain_comparisons.push(GrainComparison {
                first,
                second,
                indistinguishable_at,
                distinguished_at,
                unaddressed_at,
            });
        }
    }

    Ok(JointReceiverAtlas {
        schema: "relational-geometry.receiver-atlas.v1".to_owned(),
        faces,
        occurrences: joint_occurrences,
        swings: joint_swings,
        grain_comparisons,
    })
}

pub fn compare_receiver_atlases(
    before: &JointReceiverAtlas,
    after: &JointReceiverAtlas,
) -> Result<ReceiverAtlasEmanation, ReceiverAtlasError> {
    let before_receivers = before
        .faces
        .iter()
        .map(|face| face.receiver)
        .collect::<BTreeSet<_>>();
    let after_receivers = after
        .faces
        .iter()
        .map(|face| face.receiver)
        .collect::<BTreeSet<_>>();
    let before_occurrences = before
        .occurrences
        .iter()
        .map(|occurrence| occurrence.occurrence)
        .collect::<BTreeSet<_>>();
    let after_occurrences = after
        .occurrences
        .iter()
        .map(|occurrence| occurrence.occurrence)
        .collect::<BTreeSet<_>>();
    if before_receivers != after_receivers || before_occurrences != after_occurrences {
        return Err(ReceiverAtlasError::IncompatibleAtlases);
    }

    let occurrences = before
        .occurrences
        .iter()
        .map(|before_occurrence| {
            let after_occurrence = after
                .occurrence(before_occurrence.occurrence)
                .expect("compatible atlas retains occurrence");
            let mut changed_faces = Vec::new();
            let mut grain_visible_at = Vec::new();
            let mut grain_dark_at = Vec::new();
            for receiver in &before_receivers {
                let before_face = &before_occurrence.faces[receiver];
                let after_face = &after_occurrence.faces[receiver];
                if before_face.projected != after_face.projected {
                    changed_faces.push(*receiver);
                    if before_face.aperture != after_face.aperture {
                        grain_visible_at.push(*receiver);
                    } else {
                        grain_dark_at.push(*receiver);
                    }
                }
            }
            OccurrenceEmanation {
                occurrence: before_occurrence.occurrence,
                changed_faces,
                grain_visible_at,
                grain_dark_at,
            }
        })
        .collect();

    let before_swings = before
        .swings
        .iter()
        .map(|swing| swing.cell)
        .collect::<BTreeSet<_>>();
    let after_swings = after
        .swings
        .iter()
        .map(|swing| swing.cell)
        .collect::<BTreeSet<_>>();
    if before_swings != after_swings {
        return Err(ReceiverAtlasError::IncompatibleAtlases);
    }
    let swings = before
        .swings
        .iter()
        .map(|before_swing| {
            let after_swing = after
                .swing(before_swing.cell)
                .expect("compatible atlas retains swing");
            let changed_at = before_swing
                .receiver_values
                .iter()
                .filter_map(|(receiver, value)| {
                    (after_swing.receiver_values.get(receiver) != Some(value)).then_some(*receiver)
                })
                .collect();
            SwingEmanation {
                cell: before_swing.cell,
                before: before_swing.invariant.clone(),
                after: after_swing.invariant.clone(),
                changed_at,
            }
        })
        .collect();

    Ok(ReceiverAtlasEmanation {
        occurrences,
        swings,
    })
}

fn ensure_unique_receivers(receivers: &[GrainedReceiver]) -> Result<(), ReceiverAtlasError> {
    let mut seen = BTreeSet::new();
    for receiver in receivers {
        if !seen.insert(receiver.receiver.id) {
            return Err(ReceiverAtlasError::DuplicateReceiver(receiver.receiver.id));
        }
    }
    Ok(())
}

fn ensure_unique_occurrences(occurrences: &[MarkedOccurrence]) -> Result<(), ReceiverAtlasError> {
    let mut seen = BTreeSet::new();
    for occurrence in occurrences {
        if !seen.insert(occurrence.id) {
            return Err(ReceiverAtlasError::DuplicateOccurrence(occurrence.id));
        }
    }
    Ok(())
}

/// Why one marked quadruple carries no cross-ratio.
///
/// Every variant is a **return**, never a panic and never a silent repair.  A
/// receiver that supplied a degenerate quadruple is told which degeneracy it
/// supplied, by name, and the refusal is a value it can carry.
#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum CrossRatioRefusal {
    #[error("a swing requires exactly four points, and {0} were supplied")]
    NotFourMarks(usize),
    #[error("the first two pivot marks coincide")]
    CoincidentPivotMarks,
    #[error("the four marks do not lie in one projective pencil")]
    MarksOutsideOnePencil,
    #[error("the marked quadruple has a repeated projective member")]
    RepeatedProjectiveMember,
}

/// The exact cross-ratio of four marks lying in one projective pencil.
///
/// The four marks are reduced to one line coordinate — the pencil's `x` when
/// its direction has nonzero `x`, otherwise its `y` — and returned as
/// `(c-a)(d-b) / ((c-b)(d-a))` over `Rat`.  Nothing here is approximated and
/// no quadruple is repaired: a degenerate one is refused by name above.
///
/// # Why this is `pub`
///
/// The cross-ratio's *defining* property is that it is the invariant of the
/// projective group acting on a line, and until 2026-08-08 that property was
/// asserted nowhere in this workspace.  The computation lived here as a
/// private `fn` while the only genuine `PGL(2,ℚ)` carrier in the tree —
/// `holonic_engine::simplicial::ProjectiveTurn`, exact over `Rat`, with
/// `apply`, `followed_by`, `inverse` and a refusal for singular matrices —
/// lives one crate *above* this one.  `holonic-engine` depends on
/// `relational-geometry`, so `cross_ratio(T·p) == cross_ratio(p)` could not
/// be written on either side of that seam.  The property most cited in this
/// project was the one property of it nothing checked.
///
/// Three closures were available and this is the smallest of them.
///
/// - **Publish the reading** (taken): one visibility word and a typed refusal.
///   No dependency moves and no second implementation appears.
/// - **Move `ProjectiveTurn` down into this crate** (refused): it would drag
///   `SimplicialError` and the hinge-transport vocabulary into a crate that
///   has no hinges, to make a group visible to a function that does not use
///   it.  The group belongs with the transports that carry it.
/// - **Grow a second projective action here** (refused): two `PGL(2,ℚ)`
///   carriers in one workspace, and a second implementation agreeing with the
///   first is one computation compared with itself twice — `CLAUDE.md` §8.
///   `crates/holonic-body/src/soul.rs:159` is already a third cross-ratio, and its own
///   invariance test covers only the affine subgroup.
///
/// The invariance itself is asserted in `holonic-engine`, where the group
/// lives: `crates/holonic-engine/src/simplicial.rs` and the driver
/// `crates/holonic-engine/examples/the_swing_is_the_invariant.rs`.
pub fn cross_ratio(points: &[RatVec2]) -> Result<Rat, CrossRatioRefusal> {
    if points.len() != 4 {
        return Err(CrossRatioRefusal::NotFourMarks(points.len()));
    }
    let direction = points[1].subtract(&points[0]);
    if direction.x.is_zero() && direction.y.is_zero() {
        return Err(CrossRatioRefusal::CoincidentPivotMarks);
    }
    for point in &points[2..] {
        if direction.cross(&point.subtract(&points[0])) != Rat::zero() {
            return Err(CrossRatioRefusal::MarksOutsideOnePencil);
        }
    }
    let coordinates = if !direction.x.is_zero() {
        points
            .iter()
            .map(|point| point.x.clone())
            .collect::<Vec<_>>()
    } else {
        points
            .iter()
            .map(|point| point.y.clone())
            .collect::<Vec<_>>()
    };
    let numerator = (&coordinates[2] - &coordinates[0]) * (&coordinates[3] - &coordinates[1]);
    let denominator = (&coordinates[2] - &coordinates[1]) * (&coordinates[3] - &coordinates[0]);
    if denominator.is_zero() {
        return Err(CrossRatioRefusal::RepeatedProjectiveMember);
    }
    Ok(numerator / denominator)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::exact::rat;
    use crate::projection::{ProjectionLaw, ReceiverOrientation};

    fn point_on_line(parameter: Rat) -> RatVec3 {
        RatVec3::new(
            &parameter + integer(1),
            integer(2) * &parameter - integer(1),
            &parameter / integer(2) + integer(1),
        )
    }

    fn receiver_family(frame: FrameId) -> Vec<GrainedReceiver> {
        let first = Receiver::new(
            ReceiverId(1),
            "coarse orthographic",
            frame,
            ProjectionLaw::Orthographic,
        );
        let mut second = Receiver::new(
            ReceiverId(2),
            "fine perspective",
            frame,
            ProjectionLaw::PerspectiveRay {
                focal_distance: integer(7),
            },
        );
        second.orientation = ReceiverOrientation::from_cayley_xyz(rat(1, 5), rat(-1, 4), rat(1, 3));
        vec![
            GrainedReceiver {
                receiver: first,
                grain: ReceiverGrain::new(5, 5),
            },
            GrainedReceiver {
                receiver: second,
                grain: ReceiverGrain::new(31, 17),
            },
        ]
    }

    #[test]
    fn aperture_seams_remain_plural() {
        let grain = ReceiverGrain::new(4, 4);
        let center = grain.address(&RatVec2::zero());
        assert_eq!(center.cells.len(), 4);
        assert_eq!(grain.aspect_ratio(), Rat::one());
    }

    /// **Two receivers, two genuinely different faces, one swing.**
    ///
    /// This fixture asserted `receiver_values.len() == 2` and nothing else until
    /// 2026-08-08.  `receiver_values` is a `BTreeMap<ReceiverId, _>`, so that
    /// length counts *receivers* and is fixed by `receiver_family` before any
    /// geometry runs — it cannot fall.  Agreement between two receivers is
    /// evidence only once the two receivers are known to have projected the
    /// marks differently, exactly as `holonic-engine`'s pivot gauge requires its
    /// three walks to be three walks
    /// (`crates/holonic-engine/src/rebase_invariants.rs:1220`).
    ///
    /// So the orbit is taken first: the four received coordinates are collected
    /// per receiver and the collection is *required* to have two members, and
    /// then required to differ at every single mark rather than at one stray
    /// one.  The two maps are also different in kind — orthographic against a
    /// rotated perspective ray — so the surviving cross-ratio crosses an affine
    /// face and a genuinely projective one.
    #[test]
    fn four_marks_carry_one_cross_ratio_through_distinct_receivers() {
        let (construction, frame) = Construction::new("source");
        let occurrences = [-1, 0, 1, 3]
            .into_iter()
            .enumerate()
            .map(|(index, parameter)| {
                MarkedOccurrence::new(
                    OccurrenceId(index as u64 + 1),
                    format!("m{index}"),
                    frame,
                    point_on_line(integer(parameter)),
                )
            })
            .collect::<Vec<_>>();
        let cell = SwingCell {
            id: 1,
            name: "one swing".to_owned(),
            pivot: [OccurrenceId(1), OccurrenceId(2), OccurrenceId(3)],
            witness: OccurrenceId(4),
        };
        let atlas = analyze_receiver_atlas(
            &construction,
            &receiver_family(frame),
            &occurrences,
            &[cell],
        )
        .unwrap();

        // THE ORBIT.  What each receiver actually put on its own face.
        let received: BTreeSet<Vec<(Rat, Rat)>> = atlas
            .faces
            .iter()
            .map(|face| {
                face.occurrences
                    .iter()
                    .map(|occurrence| {
                        let point = occurrence
                            .projected
                            .rational
                            .clone()
                            .expect("both declared receivers stay rational on this line");
                        (point.x, point.y)
                    })
                    .collect()
            })
            .collect();
        assert_eq!(
            received.len(),
            2,
            "the two receivers put the same four coordinates on their faces, so the surviving \
             cross-ratio below is one computation compared with itself twice: {received:?}"
        );

        // And at every mark, so no single stray coordinate carries the whole
        // difference while the rest of the quadruple is shared.
        for joint in &atlas.occurrences {
            let first = joint.faces[&ReceiverId(1)]
                .projected
                .rational
                .clone()
                .expect("the orthographic receiver stays rational");
            let second = joint.faces[&ReceiverId(2)]
                .projected
                .rational
                .clone()
                .expect("the perspective receiver stays rational");
            assert_ne!(
                first, second,
                "mark {:?} landed on the same coordinate in both receivers",
                joint.occurrence
            );
        }

        let swing = atlas.swing(1).unwrap();
        assert_eq!(swing.receiver_values.len(), 2);
        assert!(
            swing.invariant.is_some(),
            "two receivers that moved every mark still returned one cross-ratio: {:?}",
            swing.receiver_values
        );
    }

    #[test]
    fn a_fine_receiver_can_resolve_a_coarse_receiver_fiber() {
        let (construction, frame) = Construction::new("source");
        let occurrences = vec![
            MarkedOccurrence::new(
                OccurrenceId(1),
                "first",
                frame,
                RatVec3::new(rat(1, 20), Rat::zero(), Rat::zero()),
            ),
            MarkedOccurrence::new(
                OccurrenceId(2),
                "second",
                frame,
                RatVec3::new(rat(1, 5), Rat::zero(), Rat::zero()),
            ),
        ];
        let atlas =
            analyze_receiver_atlas(&construction, &receiver_family(frame), &occurrences, &[])
                .unwrap();
        let comparison = &atlas.grain_comparisons[0];
        assert!(comparison.indistinguishable_at.contains(&ReceiverId(1)));
        assert!(comparison.distinguished_at.contains(&ReceiverId(2)));
        assert!(comparison.jointly_distinguished());
    }
}
