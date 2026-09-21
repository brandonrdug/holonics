//! Reusable exact linked-torus source for geometric HNA specifications.
//!
//! The source supports are founded by `CausalFieldAtlasLaw`; the shared point and overlap are
//! selected from the atlas result after its normal/gluing checks. Arcs retain the analytic torus
//! geometry and derive each finite phase step from its two endpoint phases.

use super::GeometricFieldSpec;
use holonic_engine::{
    AnalyticFieldArcId, AnalyticFieldJunctionId, AnalyticFieldJunctionOrigin, CausalFieldAtlasLaw,
    CausalFieldEvent, CausalFieldStanding, DimensionalWaveModeId, EventId, ExactAnalyticFieldArc,
    ExactAnalyticFieldJunction, ExactAnalyticFieldMode, ExactAnalyticFieldWaveLaw,
    ExactAnalyticOrbitGeometry, ExactEventLaw, ExactTorus, ExactTorusPhaseFrame,
    ExactUnitConicPhase, FieldOverlapOutcome, FieldRegionId, FieldSupportStanding, ImplicitCellId,
    OrientedFieldSample, SourceTorusOccurrence,
};
use num_bigint::BigInt;
use num_traits::{One, Zero};
use relational_geometry::{Rat, RatVec3, integer, rational_circle};
use std::collections::{BTreeMap, BTreeSet};

pub const LINKED_TORUS_MODE: DimensionalWaveModeId = DimensionalWaveModeId(1);

/// Incident-field aperture order for the linked rings. The legacy geometric chart keeps its
/// historical order; this chart follows admitted arcs through the shared overlap:
/// A[1..] → A[0]=B[0] → B[1..].
pub fn linked_torus_incident_slot_junctions(
    spec: &GeometricFieldSpec,
) -> Result<Vec<AnalyticFieldJunctionId>, String> {
    let mut germs = BTreeSet::new();
    let mut overlap = None;
    for junction in &spec.junctions {
        match junction.origin {
            AnalyticFieldJunctionOrigin::LocalSupport { germ } => {
                germs.insert(germ);
            }
            AnalyticFieldJunctionOrigin::InteractingOverlap { .. } => {
                overlap = Some(junction.id);
            }
        }
    }
    let germs = germs.into_iter().collect::<Vec<_>>();
    if germs.len() != 2 {
        return Err("linked torus incident aperture requires two local germs".to_owned());
    }
    let shared = overlap.ok_or_else(|| "linked torus shared overlap is absent".to_owned())?;
    let mut first = Vec::new();
    let mut second = Vec::new();
    for junction in &spec.junctions {
        match junction.origin {
            AnalyticFieldJunctionOrigin::LocalSupport { germ } if germ == germs[0] => {
                first.push(junction.id)
            }
            AnalyticFieldJunctionOrigin::LocalSupport { germ } if germ == germs[1] => {
                second.push(junction.id)
            }
            _ => {}
        }
    }
    if first.is_empty() || second.is_empty() {
        return Err("linked torus incident aperture has an empty ring".to_owned());
    }
    Ok(first
        .into_iter()
        .chain(std::iter::once(shared))
        .chain(second)
        .collect())
}

/// Derive material owners from the declared source-origin and ordered incoming port chart.
/// Local A and local B supports share material within their own germ only when their ordered
/// arc roles agree; the glued overlap receives its own owner. Degree alone is never used as the
/// grouping criterion.
pub fn linked_torus_material_owners(spec: &GeometricFieldSpec) -> Result<Vec<usize>, String> {
    let mut origin_by_id = BTreeMap::new();
    for junction in &spec.junctions {
        origin_by_id.insert(junction.id, origin_key(&junction.origin));
    }
    let mut incoming = BTreeMap::<AnalyticFieldJunctionId, Vec<String>>::new();
    for arc in &spec.arcs {
        let source = origin_by_id
            .get(&arc.from)
            .ok_or_else(|| "arc source is outside declared junctions".to_owned())?;
        incoming.entry(arc.to).or_default().push(format!(
            "{}:{}:{}",
            arc.from == arc.to,
            source,
            arc.delay
        ));
    }
    let mut signature_by_id = BTreeMap::<AnalyticFieldJunctionId, String>::new();
    for junction in &spec.junctions {
        let mut ports = incoming
            .remove(&junction.id)
            .ok_or_else(|| "junction has no incoming port chart".to_owned())?;
        ports.sort();
        signature_by_id.insert(
            junction.id,
            format!("{}|{}", origin_by_id[&junction.id], ports.join(",")),
        );
    }
    let mut owners = BTreeMap::new();
    let mut next = 0usize;
    let mut result = Vec::with_capacity(spec.junctions.len());
    for junction in &spec.junctions {
        let key = signature_by_id
            .get(&junction.id)
            .ok_or_else(|| "junction material signature is missing".to_owned())?;
        let owner = *owners.entry(key.clone()).or_insert_with(|| {
            let owner = next;
            next += 1;
            owner
        });
        result.push(owner);
    }
    if result.is_empty() {
        return Err("linked torus has no material owner sites".to_owned());
    }
    Ok(result)
}

fn origin_key(origin: &AnalyticFieldJunctionOrigin) -> String {
    match origin {
        AnalyticFieldJunctionOrigin::LocalSupport { germ } => format!("germ:{germ:?}"),
        AnalyticFieldJunctionOrigin::InteractingOverlap { overlap } => {
            format!("overlap:{overlap:?}")
        }
    }
}

/// Construct the validated geometric source used by the geometric field session.
pub fn linked_torus_field_spec(
    subdivisions: usize,
    refinement_steps: usize,
    relaxation_bits: u32,
) -> Result<GeometricFieldSpec, String> {
    if subdivisions == 0 {
        return Err("linked torus subdivisions must be positive".to_owned());
    }
    subdivisions
        .checked_mul(8)
        .and_then(|n| n.checked_sub(1))
        .ok_or_else(|| "linked torus extent overflow".to_owned())?;
    let law = CausalFieldAtlasLaw;
    let shared_point = RatVec3::from_i64(1, 0, 0);
    let first_torus = torus(
        ImplicitCellId(1),
        FieldRegionId(1),
        RatVec3::zero(),
        RatVec3::from_i64(0, 0, 1),
    )?;
    let second_torus = torus(
        ImplicitCellId(2),
        FieldRegionId(2),
        RatVec3::from_i64(2, 0, 0),
        RatVec3::from_i64(0, 1, 0),
    )?;
    for source in [&first_torus, &second_torus] {
        if source.torus.evaluate(&shared_point) != Rat::zero() {
            return Err("declared shared torus point is outside its exact support".to_owned());
        }
    }

    let first = law
        .enact(
            &law.initial_standing(),
            &CausalFieldEvent {
                event: EventId(1),
                chronology: 1,
                images: Vec::new(),
                oriented_samples: Vec::new(),
                source_tori: vec![first_torus.clone(), second_torus.clone()],
            },
        )
        .map_err(|error| format!("source torus event refused: {error}"))?;
    let second = law
        .enact(
            &first.standing_after,
            &CausalFieldEvent {
                event: EventId(2),
                chronology: 2,
                images: Vec::new(),
                oriented_samples: vec![OrientedFieldSample {
                    regions: BTreeSet::from([FieldRegionId(1), FieldRegionId(2)]),
                    point: shared_point.clone(),
                    // The two exact torus gradients have opposite signs here. The atlas retains
                    // both source germs and records their glued overlap even though this one
                    // oriented sample continues only one source germ directly.
                    normal: RatVec3::from_i64(1, 0, 0),
                    phase: BTreeMap::new(),
                    receiver_contact: None,
                }],
                source_tori: Vec::new(),
            },
        )
        .map_err(|error| format!("shared torus sample refused: {error}"))?;
    let field = second.standing_after;
    let first_germ = source_germ(&field, FieldRegionId(1))?;
    let second_germ = source_germ(&field, FieldRegionId(2))?;
    let overlap = field
        .overlaps
        .values()
        .find(|overlap| {
            overlap.outcome == FieldOverlapOutcome::Glued
                && overlap.germs == canonical_pair(first_germ, second_germ)
                && field
                    .observations
                    .get(&overlap.observation)
                    .is_some_and(|observation| observation.point == shared_point)
        })
        .ok_or_else(|| "the atlas did not return the exact glued torus overlap".to_owned())?;

    let first_frame = ExactTorusPhaseFrame {
        radial_cosine: RatVec3::from_i64(1, 0, 0),
        radial_sine: RatVec3::from_i64(0, 1, 0),
        axial: RatVec3::from_i64(0, 0, 1),
    };
    let second_frame = ExactTorusPhaseFrame {
        radial_cosine: RatVec3::from_i64(1, 0, 0),
        radial_sine: RatVec3::from_i64(0, 0, -1),
        axial: RatVec3::from_i64(0, 1, 0),
    };
    let first_phases = circle_phases(subdivisions)?;
    let second_phases = first_phases
        .iter()
        .map(|phase| ExactUnitConicPhase {
            cosine: -phase.cosine.clone(),
            sine: -phase.sine.clone(),
        })
        .collect::<Vec<_>>();
    let ring_size = first_phases.len();
    let shared_junction = AnalyticFieldJunctionId(1);
    let first_ids = (0..ring_size)
        .map(|index| AnalyticFieldJunctionId(1 + index as u64))
        .collect::<Vec<_>>();
    let second_ids = std::iter::once(shared_junction)
        .chain(
            (1..ring_size)
                .map(|index| AnalyticFieldJunctionId(1 + ring_size as u64 + (index - 1) as u64)),
        )
        .collect::<Vec<_>>();

    let first_geometry = ExactAnalyticOrbitGeometry::TorusLongitude {
        germ: first_germ,
        frame: first_frame,
        meridian: ExactUnitConicPhase {
            cosine: -Rat::one(),
            sine: Rat::zero(),
        },
    };
    let second_geometry = ExactAnalyticOrbitGeometry::TorusLongitude {
        germ: second_germ,
        frame: second_frame,
        meridian: ExactUnitConicPhase {
            cosine: -Rat::one(),
            sine: Rat::zero(),
        },
    };
    let mut junctions = Vec::with_capacity(first_ids.len() + second_ids.len() - 1);
    for (index, phase) in first_phases.iter().enumerate() {
        let id = first_ids[index];
        let origin = if index == 0 {
            AnalyticFieldJunctionOrigin::InteractingOverlap {
                overlap: overlap.id,
            }
        } else {
            AnalyticFieldJunctionOrigin::LocalSupport { germ: first_germ }
        };
        junctions.push(junction(
            &field,
            id,
            &format!("linked torus A longitude {index}"),
            &first_geometry,
            phase,
            origin,
        )?);
    }
    for (index, phase) in second_phases.iter().enumerate().skip(1) {
        let id = second_ids[index];
        junctions.push(junction(
            &field,
            id,
            &format!("linked torus B longitude {index}"),
            &second_geometry,
            phase,
            AnalyticFieldJunctionOrigin::LocalSupport { germ: second_germ },
        )?);
    }

    let mut arcs = Vec::with_capacity(ring_size * 2);
    let mut next_arc = 1_u64;
    append_ring_arcs(
        &mut arcs,
        &mut next_arc,
        &first_ids,
        &first_phases,
        first_geometry,
        "linked torus A",
    );
    append_ring_arcs(
        &mut arcs,
        &mut next_arc,
        &second_ids,
        &second_phases,
        second_geometry,
        "linked torus B",
    );

    let mode = ExactAnalyticFieldMode {
        id: LINKED_TORUS_MODE,
        name: "linked torus unit material".to_owned(),
        coherence_lineage: BTreeSet::from([EventId(1), EventId(2)]),
        frequency_square: Rat::one(),
        wave_number_square: BTreeMap::from([(first_germ, Rat::one()), (second_germ, Rat::one())]),
        interface_admittance: BTreeMap::from([(first_germ, Rat::one()), (second_germ, Rat::one())]),
    };
    let modes = vec![mode];
    ExactAnalyticFieldWaveLaw::new(
        field.clone(),
        junctions.clone(),
        arcs.clone(),
        modes.clone(),
    )
    .map_err(|error| format!("linked torus wave law refused: {error}"))?;
    let slot_junctions = first_ids
        .iter()
        .chain(second_ids.iter().skip(1))
        .copied()
        .collect();
    Ok(GeometricFieldSpec {
        field,
        junctions,
        arcs,
        modes,
        mode: LINKED_TORUS_MODE,
        slot_junctions,
        self_comparison: true,
        beta_significand: 1,
        beta_exponent: 0,
        series_terms: 32,
        refinement_steps,
        relaxation_bits,
    })
}

fn torus(
    id: ImplicitCellId,
    region: FieldRegionId,
    center: RatVec3,
    axis: RatVec3,
) -> Result<SourceTorusOccurrence, String> {
    Ok(SourceTorusOccurrence {
        region,
        torus: ExactTorus::new(id, EventId(1), center, axis, integer(2), integer(1))
            .map_err(|error| format!("torus construction failed: {error}"))?,
        // Positive unit material data is carried by the selected wave mode; the source torus
        // itself has no inferred phase law and therefore retains an empty phase declaration.
        phases: BTreeMap::new(),
    })
}

fn source_germ(
    field: &CausalFieldStanding,
    region: FieldRegionId,
) -> Result<holonic_engine::FieldGermId, String> {
    let germs = field
        .active_regions
        .get(&region)
        .into_iter()
        .flatten()
        .filter(|id| matches!(&field.germs[id].support, FieldSupportStanding::Torus(_)))
        .copied()
        .collect::<Vec<_>>();
    match germs.as_slice() {
        [germ] => Ok(*germ),
        _ => Err(format!(
            "region {region:?} did not retain one source torus germ"
        )),
    }
}

fn canonical_pair(
    left: holonic_engine::FieldGermId,
    right: holonic_engine::FieldGermId,
) -> [holonic_engine::FieldGermId; 2] {
    if left < right {
        [left, right]
    } else {
        [right, left]
    }
}

fn circle_phases(subdivisions: usize) -> Result<Vec<ExactUnitConicPhase>, String> {
    let count = subdivisions
        .checked_mul(4)
        .ok_or_else(|| "longitude extent overflow".to_owned())?;
    let mut phases = Vec::new();
    phases.try_reserve_exact(count).map_err(|e| e.to_string())?;
    // Traverse each quadrant before the next; interleaving quadrants would wind n times.
    for quadrant in 0..4 {
        for index in 0..subdivisions {
            let parameter = Rat::new(BigInt::from(index), BigInt::from(subdivisions));
            let (c, s) = rational_circle(&parameter);
            let (c, s) = match quadrant {
                0 => (c, s),
                1 => (-s, c),
                2 => (-c, -s),
                _ => (s, -c),
            };
            phases.push(ExactUnitConicPhase::new(c, s).map_err(|e| e.to_string())?);
        }
    }
    Ok(phases)
}

fn junction(
    field: &CausalFieldStanding,
    id: AnalyticFieldJunctionId,
    name: &str,
    geometry: &ExactAnalyticOrbitGeometry,
    phase: &ExactUnitConicPhase,
    origin: AnalyticFieldJunctionOrigin,
) -> Result<ExactAnalyticFieldJunction, String> {
    Ok(ExactAnalyticFieldJunction {
        id,
        name: name.to_owned(),
        point: geometry
            .point(field, phase)
            .map_err(|error| format!("junction geometry refused: {error}"))?,
        origin,
    })
}

fn append_ring_arcs(
    arcs: &mut Vec<ExactAnalyticFieldArc>,
    next_arc: &mut u64,
    junctions: &[AnalyticFieldJunctionId],
    phases: &[ExactUnitConicPhase],
    geometry: ExactAnalyticOrbitGeometry,
    name: &str,
) {
    for index in 0..junctions.len() {
        let next = (index + 1) % junctions.len();
        let step = phases[index].transport_to(&phases[next]);
        arcs.push(ExactAnalyticFieldArc {
            id: AnalyticFieldArcId(*next_arc),
            name: format!("{name} arc {index}"),
            source_event: EventId(1),
            from: junctions[index],
            to: junctions[next],
            geometry: geometry.clone(),
            start_phase: phases[index].clone(),
            geometric_step: step.clone(),
            delay: 1,
            admittance: Rat::one(),
            modal_admittance: BTreeMap::from([(LINKED_TORUS_MODE, Rat::one())]),
            modal_phase_step: BTreeMap::from([(LINKED_TORUS_MODE, step)]),
        });
        *next_arc += 1;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn incident_aperture_uses_the_shared_ring_path() {
        let spec = linked_torus_field_spec(1, 1, 1).unwrap();
        let slots = linked_torus_incident_slot_junctions(&spec).unwrap();
        assert_eq!(slots.len(), spec.slot_junctions.len());
        for pair in slots.windows(2) {
            assert!(
                spec.arcs
                    .iter()
                    .any(|arc| arc.from == pair[0] && arc.to == pair[1])
            );
        }
    }
}
