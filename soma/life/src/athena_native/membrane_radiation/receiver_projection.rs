//! Owner-local radiation seam: receiver projection.

use super::*;
use holonic_engine::cuda_refine::{ResidentMembraneInteriorReturn, ResidentQuadraticMomentReturn};
use std::collections::BTreeSet;
/// Form the native outward cell population before the exterior codec sees it. Every candidate
/// obtains its current from its exact barycentric support over the rested Complex-Parametron
/// factors, then meets the resident constitutive radiation and this occurrence's complete action
/// current. The maximal signed receiver phase remains plural on exact ties; no caller supplies a
/// deed, a top-k extent, a sentence candidate, or an expected answer.
pub(super) fn emitted_relational_front(
    rest: &impl super::super::AthenaMembraneStanding,
    aperture: &NativeRadiationAperture,
    exterior: &ExteriorActionCurrent,
    resident: &ResidentMembraneInteriorReturn,
    predecessor: Option<&NativeRadiationSection>,
) -> Result<
    (
        ExteriorParticipantReceiverChart,
        Vec<String>,
        Vec<String>,
        Vec<NativeRelationalCellRadiation>,
        Vec<String>,
        Vec<String>,
    ),
    NativeRadiationError,
> {
    if exterior.causal_octets.is_empty()
        || rest.membrane_identity() != aperture.rested_identity_sha256
    {
        return Err(NativeRadiationError::RadiationDetail(
            "the exterior section or rested aperture identity is absent".to_owned(),
        ));
    }
    let receiver_chart = resolve_participant_receiver_chart(aperture, exterior)?.clone();
    let aperture_addresses = receiver_chart
        .relational_cell_addresses
        .iter()
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    let mut receiver_factor_sections = receiver_chart
        .receiver_factor_sections
        .iter()
        .map(|section| (section.factor, section.clone()))
        .collect::<std::collections::BTreeMap<_, _>>();
    let requested_phases = exterior
        .relation_phase_words
        .iter()
        .map(|phase| vec![phase.clone()])
        .collect::<BTreeSet<_>>();
    let relation_charts = aperture
        .relation_receiver_charts
        .iter()
        .filter(|chart| requested_phases.contains(&chart.receiver_region))
        .collect::<Vec<_>>();
    let matched_phase_regions = relation_charts
        .iter()
        .map(|chart| chart.receiver_region.clone())
        .collect::<BTreeSet<_>>();
    let unresolved_relation_phase_words = exterior
        .relation_phase_words
        .iter()
        .filter(|phase| !matched_phase_regions.contains(&vec![(**phase).clone()]))
        .cloned()
        .collect::<Vec<_>>();
    let mut relation_receiver_chart_identities_sha256 = Vec::new();
    for chart in relation_charts {
        relation_receiver_chart_identities_sha256.push(chart.identity_sha256.clone());
        for section in &chart.receiver_factor_sections {
            receiver_factor_sections
                .entry(section.factor)
                .and_modify(|held| {
                    held.current = held.current.add(&section.current);
                    held.caused_population = held
                        .caused_population
                        .checked_add(section.caused_population)
                        .unwrap_or(u64::MAX);
                    held.oriented_causal_moment += &section.oriented_causal_moment;
                })
                .or_insert_with(|| section.clone());
        }
    }
    if receiver_factor_sections
        .values()
        .any(|section| section.caused_population == u64::MAX)
    {
        return Err(NativeRadiationError::Extent);
    }
    relation_receiver_chart_identities_sha256.sort();
    relation_receiver_chart_identities_sha256.dedup();
    let refinement_boundary = predecessor
        .map(|section| {
            aperture
                .relational_cell_addresses
                .iter()
                .zip(&aperture.relational_cell_boundaries)
                .filter(|(address, _)| section.emitted_relational_cell_addresses.contains(address))
                .flat_map(|(_, boundary)| boundary.iter().copied())
                .collect::<BTreeSet<_>>()
        })
        .unwrap_or_default();
    if predecessor.is_some() && refinement_boundary.is_empty() {
        return Err(NativeRadiationError::RadiationDetail(
            "the returned radiation has no affine support for later refinement".to_owned(),
        ));
    }
    let mut relational_cell_radiation = Vec::<NativeRelationalCellRadiation>::new();
    let mut candidates = Vec::<(String, Rat, Rat)>::new();
    for affine in rest.membrane_affine_cells() {
        if !aperture_addresses.contains(affine.cell_address.as_str()) {
            continue;
        }
        if predecessor.is_some() {
            let boundary = aperture
                .relational_cell_addresses
                .iter()
                .position(|address| address == &affine.cell_address)
                .and_then(|at| aperture.relational_cell_boundaries.get(at))
                .ok_or_else(|| {
                    NativeRadiationError::Aperture(
                        "the affine cell escaped the simplicial boundary chart".to_owned(),
                    )
                })?;
            if !boundary
                .iter()
                .any(|face| refinement_boundary.contains(face))
            {
                continue;
            }
        }
        if affine.landmark_factors.len() != affine.barycentric_weights.len() {
            return Err(NativeRadiationError::RadiationDetail(format!(
                "affine cell {} lost its coefficient support",
                affine.cell_address
            )));
        }
        let mut native = ExactComplexWaveCurrent::zero();
        for (factor, coefficient) in affine
            .landmark_factors
            .iter()
            .zip(&affine.barycentric_weights)
        {
            if let Some(receiver_section) = receiver_factor_sections.get(factor) {
                let (exterior_local, relation_local) =
                    wound_exterior_sections(exterior, receiver_section)?;
                let native_population =
                    Rat::from_integer(BigInt::from(receiver_section.caused_population));
                let native_moment =
                    Rat::from_integer(receiver_section.oriented_causal_moment.clone());
                let mut phase =
                    relative_action_phase(&native_population, &native_moment, &exterior_local);
                if let Some(relation_local) = relation_local {
                    phase = phase.multiply(&relative_action_phase(
                        &native_population,
                        &native_moment,
                        &relation_local,
                    ));
                }
                let local_action = receiver_section
                    .current
                    .multiply(&phase)
                    .multiply(&exterior.current);
                native = native.add(&local_action.scaled(coefficient));
            }
        }
        let returned = native.multiply(&resident.native_radiation);
        relational_cell_radiation.push(NativeRelationalCellRadiation {
            cell_address: affine.cell_address.clone(),
            returned_current: returned.clone(),
        });
        // A successor is received through its complete situated difference from the predecessor's
        // port-resolved section.  Factoring through the predecessor's single emitted address is
        // precisely the coarse-receiver obstruction proved by the granular boundary law.
        let received = predecessor
            .and_then(|section| {
                section
                    .relational_cell_radiation
                    .iter()
                    .find(|standing| standing.cell_address == affine.cell_address)
            })
            .map(|standing| returned.subtract(&standing.returned_current))
            .unwrap_or(returned);
        if received.is_zero() {
            continue;
        }
        candidates.push((
            affine.cell_address.clone(),
            received.real.clone(),
            received.norm_square(),
        ));
    }
    if candidates.is_empty() {
        return Err(NativeRadiationError::RadiationDetail(
            "the participant aperture returned no nonzero barycentric current".to_owned(),
        ));
    }
    let best = candidates
        .iter()
        .map(|(_, compatibility, norm)| (compatibility, norm))
        .max_by(|left, right| compare_receiver_phase(left.0, left.1, right.0, right.1))
        .ok_or_else(|| {
            NativeRadiationError::RadiationDetail(
                "the receiver phase front has no maximal section".to_owned(),
            )
        })?;
    let mut emitted = candidates
        .iter()
        .filter(|(_, compatibility, norm)| {
            compare_receiver_phase(compatibility, norm, best.0, best.1) == std::cmp::Ordering::Equal
        })
        .map(|(address, _, _)| address.clone())
        .collect::<Vec<_>>();
    emitted.sort();
    emitted.dedup();
    let emitted_set = emitted.iter().map(String::as_str).collect::<BTreeSet<_>>();
    let retained = receiver_chart
        .relational_cell_addresses
        .iter()
        .filter(|address| !emitted_set.contains(address.as_str()))
        .cloned()
        .collect::<Vec<_>>();
    if emitted.is_empty()
        || emitted.len() + retained.len() != receiver_chart.relational_cell_addresses.len()
    {
        return Err(NativeRadiationError::RadiationDetail(
            "the emitted and retained relation fibres do not reconstruct the aperture".to_owned(),
        ));
    }
    Ok((
        receiver_chart,
        relation_receiver_chart_identities_sha256,
        unresolved_relation_phase_words,
        relational_cell_radiation,
        emitted,
        retained,
    ))
}

fn derive_receiver_factor_sections(
    potential: &super::super::native_relational_potential::NativeRelationalPotentialComplex,
    receiver_faces: &[u32],
) -> Result<Vec<ReceiverFactorActionSection>, NativeRadiationError> {
    use super::super::native_relational_potential::{NativeDeliveryPhase, NativeRelationalRole};
    let receiver_faces = receiver_faces.iter().copied().collect::<BTreeSet<_>>();
    let mut sections = std::collections::BTreeMap::<u32, ExactComplexWaveCurrent>::new();
    let mut populations = std::collections::BTreeMap::<u32, u64>::new();
    let mut moments = std::collections::BTreeMap::<u32, BigInt>::new();
    for face in receiver_faces {
        let face = potential.faces.get(face as usize).ok_or_else(|| {
            NativeRadiationError::Aperture("receiver face escaped standing".to_owned())
        })?;
        for occurrence in &face.occurrences {
            let t = BigInt::from(occurrence.first_delivery_order)
                + BigInt::from(occurrence.last_delivery_order)
                + BigInt::from(occurrence.occurrence_population);
            let t_square = &t * &t;
            let denominator = BigInt::from(1) + &t_square;
            let cosine = Rat::new(BigInt::from(1) - t_square, denominator.clone());
            let sine = Rat::new(BigInt::from(2) * t.clone(), denominator);
            let role_hand = match occurrence.role {
                NativeRelationalRole::Subject => 1,
                NativeRelationalRole::Object => -1,
                NativeRelationalRole::Relation | NativeRelationalRole::Modality => 1,
            };
            let phase_hand = match occurrence.phase {
                NativeDeliveryPhase::Ingress => -1,
                NativeDeliveryPhase::Emanation => 1,
                NativeDeliveryPhase::Return => -1,
            };
            let scale = Rat::from_integer(BigInt::from(
                i128::from(role_hand)
                    * i128::from(phase_hand)
                    * i128::from(occurrence.occurrence_population),
            ));
            let local = ExactComplexWaveCurrent::new(cosine, sine).scaled(&scale);
            sections
                .entry(occurrence.factor)
                .and_modify(|held| *held = held.add(&local))
                .or_insert(local);
            let population = populations.entry(occurrence.factor).or_default();
            *population = population
                .checked_add(occurrence.occurrence_population)
                .ok_or(NativeRadiationError::Extent)?;
            let hand = BigInt::from(i128::from(role_hand) * i128::from(phase_hand));
            let moment = hand * BigInt::from(occurrence.occurrence_population) * t;
            moments
                .entry(occurrence.factor)
                .and_modify(|held| *held += &moment)
                .or_insert(moment);
        }
    }
    sections.retain(|_, section| !section.is_zero());
    if sections.is_empty() {
        return Err(NativeRadiationError::Aperture(
            "the receiver port has no nonzero factor section".to_owned(),
        ));
    }
    sections
        .into_iter()
        .map(|(factor, current)| {
            let caused_population = populations.get(&factor).copied().ok_or_else(|| {
                NativeRadiationError::Aperture(
                    "a receiver factor lost its caused population".to_owned(),
                )
            })?;
            let oriented_causal_moment = moments.remove(&factor).ok_or_else(|| {
                NativeRadiationError::Aperture(
                    "a receiver factor lost its oriented causal moment".to_owned(),
                )
            })?;
            Ok(ReceiverFactorActionSection {
                factor,
                current,
                caused_population,
                oriented_causal_moment,
            })
        })
        .collect()
}

pub(super) fn derive_participant_receiver_charts(
    codec: &super::super::native_relational_potential::NativeRelationalCodec,
    potential: &super::super::native_relational_potential::NativeRelationalPotentialComplex,
    participants: &BTreeSet<u32>,
) -> Result<Vec<ExteriorParticipantReceiverChart>, NativeRadiationError> {
    let mut charts = Vec::new();
    for (receiver_region, participant_alias) in codec
        .participant_alias_charts(potential, participants)
        .map_err(|error| NativeRadiationError::Standing(error.to_string()))?
    {
        let mut receiver_faces = vec![participant_alias.0, participant_alias.1];
        receiver_faces.sort();
        receiver_faces.dedup();
        let receiver_factor_sections = derive_receiver_factor_sections(potential, &receiver_faces)?;
        let relational_cell_addresses = potential
            .cells
            .iter()
            .filter(|cell| {
                receiver_faces.contains(&cell.subject) || receiver_faces.contains(&cell.object)
            })
            .map(|cell| cell.address.clone())
            .collect::<Vec<_>>();
        if relational_cell_addresses.is_empty() {
            return Err(NativeRadiationError::Aperture(
                "a participant receiver chart has no incident relational cell".to_owned(),
            ));
        }
        let identity_sha256 = digest(&(
            NATIVE_RADIATION_SCHEMA,
            &receiver_region,
            &participant_alias,
            &receiver_faces,
            &receiver_factor_sections,
            &relational_cell_addresses,
        ))?;
        charts.push(ExteriorParticipantReceiverChart {
            receiver_region,
            participant_alias,
            receiver_faces,
            receiver_factor_sections,
            relational_cell_addresses,
            identity_sha256,
        });
    }
    charts.sort_by(|left, right| {
        (&left.receiver_region, left.participant_alias)
            .cmp(&(&right.receiver_region, right.participant_alias))
    });
    charts.dedup_by(|left, right| {
        left.receiver_region == right.receiver_region
            && left.participant_alias == right.participant_alias
    });
    if charts.is_empty() {
        return Err(NativeRadiationError::Aperture(
            "the participant aperture has no receiver chart".to_owned(),
        ));
    }
    Ok(charts)
}

pub(super) fn derive_relation_receiver_charts(
    codec: &super::super::native_relational_potential::NativeRelationalCodec,
    potential: &super::super::native_relational_potential::NativeRelationalPotentialComplex,
) -> Result<Vec<ExteriorRelationReceiverChart>, NativeRadiationError> {
    let mut charts = Vec::new();
    for (receiver_region, receiver_face) in codec.relation_face_charts() {
        let receiver_factor_sections =
            derive_receiver_factor_sections(potential, &[receiver_face])?;
        let identity_sha256 = digest(&(
            NATIVE_RADIATION_SCHEMA,
            &receiver_region,
            receiver_face,
            &receiver_factor_sections,
        ))?;
        charts.push(ExteriorRelationReceiverChart {
            receiver_region,
            receiver_face,
            receiver_factor_sections,
            identity_sha256,
        });
    }
    charts.sort_by(|left, right| {
        (&left.receiver_region, left.receiver_face)
            .cmp(&(&right.receiver_region, right.receiver_face))
    });
    charts.dedup_by(|left, right| {
        left.receiver_region == right.receiver_region && left.receiver_face == right.receiver_face
    });
    if charts.is_empty() {
        return Err(NativeRadiationError::Aperture(
            "the relational boundary has no witnessed relation receiver chart".to_owned(),
        ));
    }
    Ok(charts)
}

fn resolve_participant_receiver_chart<'a>(
    aperture: &'a NativeRadiationAperture,
    exterior: &ExteriorActionCurrent,
) -> Result<&'a ExteriorParticipantReceiverChart, NativeRadiationError> {
    let requested = exterior.receiver_regions.iter().collect::<BTreeSet<_>>();
    let matches = aperture
        .participant_receiver_charts
        .iter()
        .filter(|chart| requested.contains(&chart.receiver_region))
        .collect::<Vec<_>>();
    let aliases = matches
        .iter()
        .map(|chart| chart.participant_alias)
        .collect::<BTreeSet<_>>();
    if aliases.len() != 1 {
        return Err(NativeRadiationError::RadiationDetail(format!(
            "the exterior receiver regions {:?} met {} participant aliases among {:?}",
            exterior.receiver_regions,
            aliases.len(),
            aperture
                .participant_receiver_charts
                .iter()
                .map(|chart| &chart.receiver_region)
                .collect::<Vec<_>>()
        )));
    }
    matches
        .into_iter()
        .min_by(|left, right| left.identity_sha256.cmp(&right.identity_sha256))
        .ok_or_else(|| {
            NativeRadiationError::RadiationDetail(
                "the exterior receiver did not meet the frozen participant aperture".to_owned(),
            )
        })
}

/// Rational parametrization of the unit circle. This is the exact local phase chart used by the
/// Complex-Parametron carrier; no floating trigonometric approximation or caller aperture enters.
fn exact_conic_phase(parameter: &Rat) -> ExactComplexWaveCurrent {
    let square = parameter * parameter;
    let denominator = Rat::from_integer(BigInt::from(1)) + &square;
    ExactComplexWaveCurrent::new(
        (Rat::from_integer(BigInt::from(1)) - square) / &denominator,
        (Rat::from_integer(BigInt::from(2)) * parameter) / denominator,
    )
}

fn rational_absolute(value: &Rat) -> Rat {
    if value < &Rat::from_integer(BigInt::from(0)) {
        -value.clone()
    } else {
        value.clone()
    }
}

fn relative_action_phase(
    native_population: &Rat,
    native_moment: &Rat,
    exterior: &ExactComplexWaveCurrent,
) -> ExactComplexWaveCurrent {
    let dot = native_population * &exterior.real + native_moment * &exterior.imaginary;
    let wedge = native_population * &exterior.imaginary - native_moment * &exterior.real;
    let projective_scale = rational_absolute(&dot) + rational_absolute(&wedge);
    let relative_phase = if projective_scale == Rat::from_integer(BigInt::from(0)) {
        Rat::from_integer(BigInt::from(0))
    } else {
        wedge / projective_scale
    };
    exact_conic_phase(&relative_phase)
}

/// Pull one factor's causal chronology around the complete exterior occurrence cycle. The
/// factor's oriented moment determines the addressed point; the immediate predecessor/successor
/// difference is the local boundary current. This is a receiver projection of the retained octet
/// fibre, not a tokenization or authored semantic partition.
fn wound_exterior_sections(
    exterior: &ExteriorActionCurrent,
    receiver: &ReceiverFactorActionSection,
) -> Result<(ExactComplexWaveCurrent, Option<ExactComplexWaveCurrent>), NativeRadiationError> {
    let extent = exterior.causal_octets.len();
    if extent == 0 {
        return Err(NativeRadiationError::Exterior);
    }
    let extent_integer = BigInt::from(extent);
    let wound = &receiver.oriented_causal_moment % &extent_integer;
    let wound = if wound.sign() == num_bigint::Sign::Minus {
        -wound
    } else {
        wound
    };
    let at = usize::try_from(wound).map_err(|_| NativeRadiationError::Extent)?;
    let prior = if at == 0 { extent - 1 } else { at - 1 };
    let next = if at + 1 == extent { 0 } else { at + 1 };
    let population_at = usize::try_from(receiver.caused_population)
        .map_err(|_| NativeRadiationError::Extent)?
        % extent;
    let population_prior = if population_at == 0 {
        extent - 1
    } else {
        population_at - 1
    };
    let population_next = if population_at + 1 == extent {
        0
    } else {
        population_at + 1
    };
    let local_mass = BigInt::from(exterior.causal_octets[at])
        + BigInt::from(exterior.causal_octets[population_at]);
    let local_difference = BigInt::from(exterior.causal_octets[next])
        - BigInt::from(exterior.causal_octets[prior])
        + BigInt::from(exterior.causal_octets[population_next])
        - BigInt::from(exterior.causal_octets[population_prior]);
    let relation = if !exterior.causal_relation_phase_octets.is_empty() {
        let phase_at = at % exterior.causal_relation_phase_octets.len();
        let phase = &exterior.causal_relation_phase_octets[phase_at];
        if !phase.is_empty() {
            let phase_position = population_at % phase.len();
            let phase_prior = if phase_position == 0 {
                phase.len() - 1
            } else {
                phase_position - 1
            };
            let phase_next = if phase_position + 1 == phase.len() {
                0
            } else {
                phase_position + 1
            };
            Some(ExactComplexWaveCurrent::new(
                Rat::from_integer(BigInt::from(phase[phase_position])),
                Rat::from_integer(
                    BigInt::from(phase[phase_next]) - BigInt::from(phase[phase_prior]),
                ),
            ))
        } else {
            None
        }
    } else {
        None
    };
    Ok((
        ExactComplexWaveCurrent::new(
            Rat::from_integer(local_mass),
            Rat::from_integer(local_difference),
        ),
        relation,
    ))
}

fn compare_receiver_phase(
    left_compatibility: &Rat,
    left_norm_square: &Rat,
    right_compatibility: &Rat,
    right_norm_square: &Rat,
) -> std::cmp::Ordering {
    use std::cmp::Ordering;
    let zero = Rat::from_integer(BigInt::from(0));
    let class = |compatibility: &Rat, norm_square: &Rat| {
        if norm_square == &zero {
            0u8
        } else if compatibility < &zero {
            1
        } else if compatibility == &zero {
            2
        } else {
            3
        }
    };
    let left_class = class(left_compatibility, left_norm_square);
    let right_class = class(right_compatibility, right_norm_square);
    match left_class.cmp(&right_class) {
        Ordering::Equal => {}
        ordering => return ordering,
    }
    if matches!(left_class, 0 | 2) {
        return Ordering::Equal;
    }
    let left_cross = left_compatibility * left_compatibility * right_norm_square;
    let right_cross = right_compatibility * right_compatibility * left_norm_square;
    if left_class == 1 {
        right_cross.cmp(&left_cross)
    } else {
        left_cross.cmp(&right_cross)
    }
}

pub(super) fn quadratic_receiver_projection_identity_sha256(
    entering_boundary_front: &[u32],
    section: &GranularRadiationSection,
) -> Result<String, NativeRadiationError> {
    let branch_projection = section
        .branches
        .iter()
        .map(|branch| {
            (
                &branch.higher_face,
                &branch.exterior_port,
                &branch.resident_current,
                &branch.returned_response,
                branch.lies_in_port_kernel,
                branch.lies_in_receiver_phase_front,
            )
        })
        .collect::<Vec<_>>();
    digest(&(
        "soma-life.mem6-quadratic-receiver-projection.v1",
        entering_boundary_front,
        branch_projection,
        &section.resident_joint_current.port_returns,
        &section.resident_joint_current.entering_current,
        &section.resident_joint_current.total_returned_current,
        &section.resident_joint_current.stored_difference,
        section.resident_joint_current.local_balance_closes,
        section.resident_joint_current.phase_locked_port_population,
        section.resident_joint_current.phase_front_is_unique,
        &section.visible_higher_faces,
    ))
}

pub(super) fn first_quadratic_receiver_separator(
    left: &ResidentQuadraticMomentReturn,
    right: &ResidentQuadraticMomentReturn,
) -> Option<String> {
    if left.ports.len() != right.ports.len() {
        return Some(format!(
            "port_population:{}!={}",
            left.ports.len(),
            right.ports.len()
        ));
    }
    for (port_at, (left, right)) in left.ports.iter().zip(&right.ports).enumerate() {
        if left.port != right.port {
            return Some(format!(
                "port[{port_at}].address:{}!={}",
                left.port, right.port
            ));
        }
        for (coordinate, (left, right)) in left
            .reflected_family_overlaps
            .iter()
            .zip(&right.reflected_family_overlaps)
            .enumerate()
        {
            if left != right {
                return Some(format!(
                    "port[{port_at}].reflected_family_overlaps[{coordinate}]:{left}!={right}"
                ));
            }
        }
        for (coordinate, (left, right)) in left
            .family_overlaps
            .iter()
            .zip(&right.family_overlaps)
            .enumerate()
        {
            if left != right {
                return Some(format!(
                    "port[{port_at}].family_overlaps[{coordinate}]:{left}!={right}"
                ));
            }
        }
        for (coordinate, (left, right)) in left
            .receiver_overlaps
            .iter()
            .zip(&right.receiver_overlaps)
            .enumerate()
        {
            if left != right {
                return Some(format!(
                    "port[{port_at}].receiver_overlaps[{coordinate}]:{left}!={right}"
                ));
            }
        }
        for (coordinate, (left, right)) in left
            .receiver_action_norms
            .iter()
            .zip(&right.receiver_action_norms)
            .enumerate()
        {
            if left != right {
                return Some(format!(
                    "port[{port_at}].receiver_action_norms[{coordinate}]:{left}!={right}"
                ));
            }
        }
    }
    if left.port_returns != right.port_returns {
        return Some("port_return_current_or_phase_front".to_owned());
    }
    if left.total_returned_current != right.total_returned_current {
        return Some("total_returned_current".to_owned());
    }
    if left.stored_difference != right.stored_difference {
        return Some("stored_difference".to_owned());
    }
    None
}

/// Return the first coordinate which proves that two equal-boundary quadratic receiver sections
/// are not related by one positive global projective scale. A missing separator means only that
/// this declared contraction family cannot distinguish the two presentations; their complete
/// reconstruction fibres remain different objects.

/// Return the first coordinate which proves that two equal-boundary quadratic receiver sections
/// are not related by one positive global projective scale. A missing separator means only that
/// this declared contraction family cannot distinguish the two presentations; their complete
/// reconstruction fibres remain different objects.
pub(super) fn first_quadratic_receiver_projective_separator(
    left: &ResidentQuadraticMomentReturn,
    right: &ResidentQuadraticMomentReturn,
) -> Option<String> {
    if left.ports.len() != right.ports.len() {
        return Some(format!(
            "port_population:{}!={}",
            left.ports.len(),
            right.ports.len()
        ));
    }
    let mut coordinates = Vec::<(String, BigInt, BigInt)>::new();
    for (port_at, (left, right)) in left.ports.iter().zip(&right.ports).enumerate() {
        if left.port != right.port {
            return Some(format!(
                "port[{port_at}].address:{}!={}",
                left.port, right.port
            ));
        }
        for (coordinate, (left, right)) in left
            .reflected_family_overlaps
            .iter()
            .zip(&right.reflected_family_overlaps)
            .enumerate()
        {
            coordinates.push((
                format!("port[{port_at}].reflected_family_overlaps[{coordinate}]"),
                left.clone(),
                right.clone(),
            ));
        }
        for (coordinate, (left, right)) in left
            .family_overlaps
            .iter()
            .zip(&right.family_overlaps)
            .enumerate()
        {
            coordinates.push((
                format!("port[{port_at}].family_overlaps[{coordinate}]"),
                left.clone(),
                right.clone(),
            ));
        }
        for (coordinate, (left, right)) in left
            .receiver_overlaps
            .iter()
            .zip(&right.receiver_overlaps)
            .enumerate()
        {
            coordinates.push((
                format!("port[{port_at}].receiver_overlaps[{coordinate}]"),
                left.clone(),
                right.clone(),
            ));
        }
        for (coordinate, (left, right)) in left
            .receiver_action_norms
            .iter()
            .zip(&right.receiver_action_norms)
            .enumerate()
        {
            coordinates.push((
                format!("port[{port_at}].receiver_action_norms[{coordinate}]"),
                BigInt::from(left.clone()),
                BigInt::from(right.clone()),
            ));
        }
    }
    let Some((reference_name, reference_left, reference_right)) = coordinates
        .iter()
        .find(|(_, left, right)| left != &BigInt::from(0) || right != &BigInt::from(0))
    else {
        return None;
    };
    if reference_left == &BigInt::from(0)
        || reference_right == &BigInt::from(0)
        || reference_left.sign() != reference_right.sign()
    {
        return Some(format!(
            "{reference_name}:{reference_left}!~{reference_right}"
        ));
    }
    for (name, left, right) in &coordinates {
        if left * reference_right != right * reference_left {
            return Some(format!("{name} not-proportional-to {reference_name}"));
        }
    }
    None
}
