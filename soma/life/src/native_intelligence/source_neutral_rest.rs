//! Source-neutral Athena rest after the UAR0 developmental-chart quotient.
//!
//! This module is the productive root of the corrected body.  It owns only continuing native
//! morphology: the returned ecology, generator-compatible granular potential, and acoustic and
//! optical incidence.  Developmental corpus surfaces and their inverse charts live in a separate
//! cold witness which is neither stored here nor accepted by any method in this module.

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use thiserror::Error;

use holonic_engine::{
    cuda_refine::{
        CudaRefineExecutor, ResidentBoundaryRestrictionFront, ResidentCurrentAddress,
        ResidentFactoredMomentReceiverReturn, ResidentGeneratedPortLocalCurrent,
        ResidentMembraneInteriorWord, ResidentQuadraticMomentFront,
        ResidentQuadraticMomentPortReturn, ResidentQuadraticMomentRestrictionSource,
        ResidentQuadraticMomentReturn, ResidentReceiverHistoryCompressionReceipt,
        ResidentSparseQuadraticMomentFoundationReturn,
    },
    native_spool::{
        NativeCollapsedFibre, NativeConstitutiveResponse, NativeIncidenceTerm,
        NativePullbackOccurrence, NativeSituatedRadicalWithdrawal, NativeSituatedSpoolBundle,
        NativeSituatedSpoolPredecessor, NativeSituatedThreadWithdrawal, NativeThreadDeposit,
        NativeThreadDepositBatchReceipt, NativeThreadDepositReceipt, NativeThreadHand,
        ReceiverInsufficiency,
    },
    receiver_exact_compression::{
        compress, InputId, ItemId, Observation, ObservedSystem, ReceiverId,
    },
    receiver_history_compression::{
        NativeStateId, OrderedWordConsequence, ReceiverHistoryCompression,
    },
    AddressedCurrentSection, AddressedGeneratedPortJunctionPassage, EventId,
    ExactComplexWaveCurrent, ExactRatMatrix, OccurrencePort,
};
use num_bigint::{BigInt, BigUint};
use num_rational::BigRational as Rat;
use num_traits::{Signed, Zero};

use crate::native_intelligence::granular_potential::{
    GranularAddressedHigherBoundaryFace, GranularBoundaryBranch, GranularBoundaryEmanation,
    GranularExteriorPort, GranularHigherBoundaryFace, GranularNativeProjectiveCurrent,
    GranularReconstructionNode, NativeGranularPotential,
};
use crate::native_intelligence::returned_difference_deposit::derive_returned_difference_deposit_from_history;
use crate::native_intelligence::situated_difference::{
    CausalAdjointStepInput, SituatedDifferenceInput, SituatedDifferenceSection,
};
use crate::native_intelligence::source_neutral_relational::{
    SourceNeutralAddressedRealizationPairCurrent,
    SourceNeutralExteriorRealizationComplexSiteCurrent, SourceNeutralExteriorRealizationMorphology,
    SourceNeutralExteriorRealizationPassage, SourceNeutralExteriorSiteHistoryQuotient,
    SourceNeutralNativeOrientedFace, SourceNeutralNativeOrientedLocalCurrent,
    SourceNeutralRelationalMorphology,
};
use crate::native_intelligence::types::{NativeConductedSection, NativeSectionAddress};
use std::collections::{BTreeMap, BTreeSet};

mod ablation_wire;
mod conduct;
mod cultivation;
mod exterior_wire;
mod resident;
mod wire;

pub use ablation_wire::*;
pub use exterior_wire::*;
pub use wire::*;
use wire::{
    found_continuation_receiver_history, native_oriented_realization_faces,
    SourceNeutralContinuationState, SourceNeutralFactorReceiverHistorySystem,
    SourceNeutralReceiverHistoryConstitution, SourceNeutralSituatedDifferenceBody,
    SOURCE_NEUTRAL_ACOUSTIC_MORPHOLOGY_SCHEMA, SOURCE_NEUTRAL_OPTICAL_MORPHOLOGY_SCHEMA,
};

fn universal_byte_glyph_codec_identity() -> String {
    digest(&(
        "soma-life.universal-byte-glyph-codec.v1",
        (0_u16..=u8::MAX as u16).collect::<Vec<_>>(),
    ))
}

fn section_hand(
    factor: u32,
    section: &[Rat],
    orientations: &BTreeMap<(u32, usize), i8>,
) -> Result<i8, SourceNeutralEcologyError> {
    let pairing = section.iter().enumerate().try_fold(
        Rat::from_integer(BigInt::from(0)),
        |sum, (coordinate, coefficient)| {
            orientations
                .get(&(factor, coordinate))
                .map(|hand| sum + coefficient * Rat::from_integer(BigInt::from(*hand)))
                .ok_or_else(|| {
                    SourceNeutralEcologyError::Body(
                        "a winding section escaped the native orientation chart".to_owned(),
                    )
                })
        },
    )?;
    Ok(if pairing > Rat::from_integer(BigInt::from(0)) {
        1
    } else if pairing < Rat::from_integer(BigInt::from(0)) {
        -1
    } else {
        0
    })
}

fn digest(value: &impl Serialize) -> String {
    let bytes = serde_json::to_vec(value).expect("fixed source-neutral identity tuple serializes");
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn orientation(section: &[Rat]) -> Option<i8> {
    let total = section
        .iter()
        .fold(Rat::from_integer(BigInt::from(0)), |sum, value| sum + value);
    if total > Rat::from_integer(BigInt::from(0)) {
        Some(1)
    } else if total < Rat::from_integer(BigInt::from(0)) {
        Some(-1)
    } else {
        None
    }
}

pub(super) use holonic_engine::is_sha256_digest as is_digest;
// Shared exact projective and native-current helpers retained by the split owner modules.
fn canonical_positive_projective_resident_receiver_section(
    section: &SourceNeutralResidentRadiationSection,
) -> Result<Vec<BigInt>, SourceNeutralEcologyError> {
    let radiation = &section.radiation;
    if radiation.receiver_coordinate_denominator <= BigInt::ZERO {
        return Err(SourceNeutralEcologyError::Wire(
            "the native receiver section has no positive coordinate chart".to_owned(),
        ));
    }
    let receiver_denominator = radiation.receiver_coordinate_denominator.clone();
    let mut coordinates = Vec::new();
    for port in &radiation.ports {
        coordinates.extend(
            port.moment
                .iter()
                .cloned()
                .map(|coordinate| Rat::from_integer(BigInt::from(coordinate))),
        );
        coordinates.extend(
            port.reflected_family_overlaps
                .iter()
                .cloned()
                .map(|coordinate| Rat::new(coordinate, receiver_denominator.clone())),
        );
        coordinates.extend(
            port.family_overlaps
                .iter()
                .cloned()
                .map(|coordinate| Rat::new(coordinate, receiver_denominator.clone())),
        );
        coordinates.extend(
            port.receiver_overlaps
                .iter()
                .cloned()
                .map(|coordinate| Rat::new(coordinate, receiver_denominator.clone())),
        );
        coordinates.extend(
            port.receiver_action_norms
                .iter()
                .cloned()
                .map(|coordinate| Rat::new(BigInt::from(coordinate), receiver_denominator.clone())),
        );
    }
    for returned in &radiation.port_returns {
        coordinates.push(returned.returned_response.real.clone());
        coordinates.push(returned.returned_response.imaginary.clone());
    }
    coordinates.push(radiation.total_returned_current.real.clone());
    coordinates.push(radiation.total_returned_current.imaginary.clone());
    if let Some(situated) = &radiation.situated_receiver_pairing {
        if situated.coordinate_denominator <= BigInt::ZERO {
            return Err(SourceNeutralEcologyError::Wire(
                "the situated receiver section has no positive coordinate chart".to_owned(),
            ));
        }
        coordinates.extend(
            situated
                .coordinates
                .iter()
                .cloned()
                .map(|coordinate| Rat::new(coordinate, situated.coordinate_denominator.clone())),
        );
    }
    canonical_positive_projective_coordinates(&coordinates)
}

fn canonical_positive_projective_coordinates(
    coordinates: &[Rat],
) -> Result<Vec<BigInt>, SourceNeutralEcologyError> {
    if coordinates.is_empty() || coordinates.iter().all(Rat::is_zero) {
        return Err(SourceNeutralEcologyError::Wire(
            "the complete homogeneous receiver section lies in the zero fibre".to_owned(),
        ));
    }

    let common_denominator = coordinates
        .iter()
        .fold(BigInt::from(1_u8), |common, coordinate| {
            exact_bigint_lcm(common, coordinate.denom().clone())
        });
    let integral = coordinates
        .iter()
        .map(|coordinate| coordinate.numer() * (&common_denominator / coordinate.denom()))
        .collect::<Vec<_>>();
    let divisor = integral
        .iter()
        .filter(|coordinate| !coordinate.is_zero())
        .map(|coordinate| coordinate.abs())
        .reduce(exact_bigint_gcd)
        .ok_or_else(|| {
            SourceNeutralEcologyError::Wire(
                "the complete homogeneous receiver section lost its projective divisor".to_owned(),
            )
        })?;
    Ok(integral
        .into_iter()
        .map(|coordinate| coordinate / &divisor)
        .collect())
}

fn exact_bigint_gcd(mut left: BigInt, mut right: BigInt) -> BigInt {
    left = left.abs();
    right = right.abs();
    while !right.is_zero() {
        let remainder = &left % &right;
        left = right;
        right = remainder;
    }
    left
}

fn exact_bigint_lcm(left: BigInt, right: BigInt) -> BigInt {
    let divisor = exact_bigint_gcd(left.clone(), right.clone());
    if divisor.is_zero() {
        BigInt::ZERO
    } else {
        ((left / divisor) * right).abs()
    }
}

#[cfg(test)]
mod projective_receiver_tests {
    use super::*;

    #[test]
    fn positive_common_scale_is_removed_without_identifying_opposite_orientation() {
        let first = vec![
            Rat::new(BigInt::from(2), BigInt::from(3)),
            Rat::new(BigInt::from(-4), BigInt::from(5)),
            Rat::ZERO,
        ];
        let doubled = first
            .iter()
            .map(|coordinate| coordinate * Rat::from_integer(BigInt::from(2)))
            .collect::<Vec<_>>();
        let opposite = first
            .iter()
            .map(|coordinate| -coordinate)
            .collect::<Vec<_>>();

        let first = canonical_positive_projective_coordinates(&first).expect("first ray");
        let doubled =
            canonical_positive_projective_coordinates(&doubled).expect("positive rescale");
        let opposite = canonical_positive_projective_coordinates(&opposite).expect("opposite ray");
        assert_eq!(first, doubled);
        assert_ne!(first, opposite);
    }
}

fn source_neutral_situated_difference_from_world_return(
    rest: &SourceNeutralEcologyRest,
    chart: &SourceNeutralFactorWindingConstitutiveChart,
    candidate_current: &GranularNativeProjectiveCurrent,
    returned_current: &GranularNativeProjectiveCurrent,
    emission: &SourceNeutralExteriorEmission,
    exterior_return: &SourceNeutralExteriorInferenceReturn,
) -> Result<SourceNeutralSituatedDifferenceBody, SourceNeutralEcologyError> {
    if emission.identity_sha256.is_empty()
        || exterior_return.emission_occurrence != emission.occurrence
        || exterior_return.emitting_native_section_identity_sha256
            != emission.native_section_identity_sha256
        || exterior_return.returned_native_current_identity_sha256
            != returned_current.identity_sha256
        || candidate_current.standing_potential_identity_sha256 != rest.granular.identity()
        || returned_current.standing_potential_identity_sha256 != rest.granular.identity()
    {
        return Err(SourceNeutralEcologyError::Wire(
            "the published emission and world return lost their common rested boundary".to_owned(),
        ));
    }
    let candidate_factor_current = candidate_current
        .integrated_factor_current
        .iter()
        .map(|coordinate| (coordinate.factor, coordinate.incidence.clone()))
        .collect::<Vec<_>>();
    let returned_factor_current = returned_current
        .integrated_factor_current
        .iter()
        .map(|coordinate| (coordinate.factor, coordinate.incidence.clone()))
        .collect::<Vec<_>>();
    let factor_difference = complete_signed_factor_difference(
        chart.factor_native_addresses.len(),
        &candidate_factor_current,
        &returned_factor_current,
    )?;
    let candidate_winding_coordinates = chart.project_factor_current(&candidate_factor_current)?;
    let returned_winding_coordinates = chart.project_factor_current(&returned_factor_current)?;
    let winding_difference = chart.return_difference(factor_difference)?;
    let direct_winding_difference = returned_winding_coordinates
        .iter()
        .zip(&candidate_winding_coordinates)
        .map(|(returned, candidate)| returned - candidate)
        .collect::<Vec<_>>();
    if direct_winding_difference != winding_difference.returned_winding_covector
        || winding_difference.receiver_radical
    {
        return Err(SourceNeutralEcologyError::Body(
            "the world return lies in the winding receiver radical or failed exact linearity"
                .to_owned(),
        ));
    }

    let selected_branch = unique_largest_rational_magnitude(
        winding_difference
            .returned_winding_covector
            .iter()
            .enumerate()
            .map(|(branch, coefficient)| (branch, coefficient.clone())),
        "the returned winding current has plural maximal branch anchors",
    )?;
    let branch_functional = chart
        .branch_functionals
        .get(selected_branch)
        .ok_or_else(|| {
            SourceNeutralEcologyError::Body(
                "the returned winding anchor escaped the standing branch chart".to_owned(),
            )
        })?;
    let selected_factor = unique_largest_rational_magnitude(
        winding_difference
            .factor_difference
            .iter()
            .enumerate()
            .filter(|(_, difference)| !difference.is_zero())
            .map(|(factor, difference)| {
                (
                    factor,
                    &branch_functional.coefficients[factor] * Rat::from_integer(difference.clone()),
                )
            }),
        "the returned factor current has plural maximal constitutive anchors",
    )?;
    let face = rest
        .granular
        .factor_faces()
        .get(selected_factor)
        .ok_or_else(|| {
            SourceNeutralEcologyError::Body(
                "the returned factor anchor escaped the native face chart".to_owned(),
            )
        })?;
    let selected_factor = face.factor;
    let selected_factor_native = face.native;
    let selected_fibre = rest
        .body
        .ecology()
        .exact_reconstruction_fibres()
        .iter()
        .find(|fibre| {
            fibre.thread == branch_functional.thread_address
                && fibre.dependent_receiver_fibre == BTreeSet::from([selected_factor_native])
        })
        .ok_or_else(|| {
            SourceNeutralEcologyError::Body(
                "the selected factor/branch anchor has no exact reconstruction fibre".to_owned(),
            )
        })?;
    let spool = rest
        .body
        .ecology()
        .native()
        .spools
        .iter()
        .find(|spool| {
            spool
                .threads
                .iter()
                .any(|thread| thread.address == branch_functional.thread_address)
        })
        .ok_or_else(|| {
            SourceNeutralEcologyError::Body(
                "the selected winding branch escaped the standing spool".to_owned(),
            )
        })?;
    let thread = spool
        .threads
        .iter()
        .find(|thread| thread.address == branch_functional.thread_address)
        .expect("the enclosing spool contains the selected thread");
    let template_occurrence = thread
        .occurrences
        .iter()
        .find(|occurrence| occurrence.occurrence == selected_fibre.carrying_pullback.right)
        .ok_or_else(|| {
            SourceNeutralEcologyError::Body(
                "the selected reconstruction fibre lost its carrying occurrence".to_owned(),
            )
        })?;
    let template_incidence = thread
        .incidence
        .iter()
        .find(|incidence| incidence.occurrence == template_occurrence.occurrence)
        .ok_or_else(|| {
            SourceNeutralEcologyError::Body(
                "the selected carrying occurrence lost its incidence".to_owned(),
            )
        })?;
    let entering_cell = thread
        .parametrons
        .iter()
        .find(|cell| cell.native == template_occurrence.entering_native)
        .ok_or_else(|| {
            SourceNeutralEcologyError::Body(
                "the selected carrying occurrence lost its entering Parametron".to_owned(),
            )
        })?;
    let emitting_cell = thread
        .parametrons
        .iter()
        .find(|cell| cell.native == template_occurrence.emitting_native)
        .ok_or_else(|| {
            SourceNeutralEcologyError::Body(
                "the selected carrying occurrence lost its emitting Parametron".to_owned(),
            )
        })?;
    let receivers = thread
        .constitutive_responses
        .iter()
        .filter(|response| response.native == template_occurrence.entering_native)
        .map(|response| response.receiver)
        .filter(|receiver| {
            thread.constitutive_responses.iter().any(|response| {
                response.native == template_occurrence.emitting_native
                    && response.receiver == *receiver
            })
        })
        .collect::<BTreeSet<_>>();
    if receivers.len() != 1 {
        return Err(SourceNeutralEcologyError::Body(
            "the selected carrying occurrence has no unique common constitutive receiver"
                .to_owned(),
        ));
    }
    let receiver = *receivers.iter().next().expect("one exact receiver");
    let candidate_observation = thread
        .receiver_consequences
        .iter()
        .find(|consequence| {
            consequence.native == template_occurrence.emitting_native
                && consequence.receiver == receiver
        })
        .map(|consequence| consequence.observation)
        .ok_or_else(|| {
            SourceNeutralEcologyError::Body(
                "the candidate anchor lost its receiver consequence".to_owned(),
            )
        })?;
    let returned_observation = thread
        .receiver_consequences
        .iter()
        .find(|consequence| {
            consequence.native == template_occurrence.entering_native
                && consequence.receiver == receiver
        })
        .map(|consequence| consequence.observation)
        .ok_or_else(|| {
            SourceNeutralEcologyError::Body(
                "the returned anchor lost its receiver consequence".to_owned(),
            )
        })?;

    let latest_event = rest
        .body
        .ecology()
        .native()
        .spools
        .iter()
        .flat_map(|spool| &spool.threads)
        .flat_map(|thread| &thread.occurrences)
        .map(|occurrence| occurrence.occurrence.0)
        .max()
        .ok_or_else(|| {
            SourceNeutralEcologyError::Body("the standing spool has no event chronology".to_owned())
        })?;
    let candidate_event = EventId(latest_event.checked_add(1).ok_or_else(|| {
        SourceNeutralEcologyError::Body(
            "the candidate world-return event exceeded its causal address".to_owned(),
        )
    })?);
    let returned_event = EventId(candidate_event.0.checked_add(1).ok_or_else(|| {
        SourceNeutralEcologyError::Body(
            "the returned world event exceeded its causal address".to_owned(),
        )
    })?);
    let candidate_address = NativeSectionAddress {
        spool: spool.address.clone(),
        thread: format!("native-world-section/{}", candidate_event.0),
        occurrence: candidate_event,
    };
    let returned_address = NativeSectionAddress {
        spool: spool.address.clone(),
        thread: format!("native-world-return/{}", returned_event.0),
        occurrence: returned_event,
    };
    let candidate_entering_section = entering_cell
        .section
        .multiply(&candidate_current.entering_current);
    let candidate_entering_current = entering_cell
        .current
        .multiply(&candidate_current.entering_current);
    let candidate_emitting_section = emitting_cell
        .section
        .multiply(&candidate_current.entering_current);
    let candidate_emitting_current = emitting_cell
        .current
        .multiply(&candidate_current.entering_current);
    let returned_entering_section = emitting_cell
        .section
        .multiply(&returned_current.entering_current);
    let returned_entering_current = emitting_cell
        .current
        .multiply(&returned_current.entering_current);
    let returned_emitting_section = entering_cell
        .section
        .multiply(&returned_current.entering_current);
    let returned_emitting_current = entering_cell
        .current
        .multiply(&returned_current.entering_current);
    let candidate = NativeConductedSection {
        address: candidate_address.clone(),
        predecessor: Some(template_occurrence.occurrence),
        entering_boundary: thread.entering_boundary,
        emitting_boundary: thread.emitting_boundary,
        entering_port: OccurrencePort::input(
            candidate_event,
            template_occurrence.entering_port.ordinal,
        ),
        emitting_port: OccurrencePort::output(
            candidate_event,
            template_occurrence.emitting_port.ordinal,
        ),
        entering_native: template_occurrence.entering_native,
        emitting_native: template_occurrence.emitting_native,
        incidence: NativeIncidenceTerm {
            occurrence: candidate_event,
            from: template_occurrence.entering_native,
            to: template_occurrence.emitting_native,
            coefficient: template_incidence.coefficient,
        },
        entering_section: candidate_entering_section,
        entering_current: candidate_entering_current,
        emitting_section: candidate_emitting_section.clone(),
        emitting_current: candidate_emitting_current.clone(),
        relative_phase: emitting_cell.relative_phase.clone(),
        hand: emitting_cell.hand,
        constitutive_response: NativeConstitutiveResponse {
            native: template_occurrence.emitting_native,
            receiver,
            presented: candidate_emitting_section,
            stored: candidate_emitting_current,
        },
        mutual_constitutive_responses: Vec::new(),
        ordered_word: thread.chronology.clone(),
        receiver,
        observation: candidate_observation,
        reconstruction_fibre: BTreeSet::from([candidate_event]),
        successor_sections: vec![returned_address.clone()],
        open_exterior: vec![
            "the published native section remains open to a separately caused world return"
                .to_owned(),
        ],
    };
    let mut returned_word = thread.chronology.clone();
    returned_word.reverse();
    let returned_hand = match entering_cell.hand {
        NativeThreadHand::Along => NativeThreadHand::Against,
        NativeThreadHand::Against => NativeThreadHand::Along,
    };
    let returned = NativeConductedSection {
        address: returned_address,
        predecessor: Some(candidate_event),
        entering_boundary: thread.emitting_boundary,
        emitting_boundary: thread.entering_boundary,
        entering_port: OccurrencePort::input(
            returned_event,
            template_occurrence.emitting_port.ordinal,
        ),
        emitting_port: OccurrencePort::output(
            returned_event,
            template_occurrence.entering_port.ordinal,
        ),
        entering_native: template_occurrence.emitting_native,
        emitting_native: template_occurrence.entering_native,
        incidence: NativeIncidenceTerm {
            occurrence: returned_event,
            from: template_occurrence.emitting_native,
            to: template_occurrence.entering_native,
            coefficient: template_incidence
                .coefficient
                .checked_neg()
                .ok_or_else(|| {
                    SourceNeutralEcologyError::Body(
                        "the returned incidence escaped its signed carrier".to_owned(),
                    )
                })?,
        },
        entering_section: returned_entering_section,
        entering_current: returned_entering_current,
        emitting_section: returned_emitting_section.clone(),
        emitting_current: returned_emitting_current.clone(),
        relative_phase: entering_cell.relative_phase.clone(),
        hand: returned_hand,
        constitutive_response: NativeConstitutiveResponse {
            native: template_occurrence.entering_native,
            receiver,
            presented: returned_emitting_section,
            stored: returned_emitting_current,
        },
        mutual_constitutive_responses: Vec::new(),
        ordered_word: returned_word,
        receiver,
        observation: returned_observation,
        reconstruction_fibre: BTreeSet::from([returned_event]),
        successor_sections: Vec::new(),
        open_exterior: vec![
            "the world return awaits atomic deposition into the same continuing ecology".to_owned(),
        ],
    };
    let winding_rank = chart.branch_functionals.len();
    let identity = ExactRatMatrix::identity(winding_rank)
        .map_err(|error| SourceNeutralEcologyError::Body(error.to_string()))?;
    let metric = ExactRatMatrix::from_diagonal(
        chart
            .branch_functionals
            .iter()
            .map(|branch| branch.constitutive_norm.clone())
            .collect(),
    )
    .map_err(|error| SourceNeutralEcologyError::Body(error.to_string()))?;
    let situated_difference = SituatedDifferenceSection::found(SituatedDifferenceInput {
        candidate,
        returned,
        carrying_occurrence: NativePullbackOccurrence {
            left: candidate_event,
            right: returned_event,
            joining_native: template_occurrence.emitting_native,
        },
        occurrence_fibres: vec![NativeCollapsedFibre {
            native: template_occurrence.emitting_native,
            occurrences: BTreeSet::from([candidate_event, returned_event]),
        }],
        source_transport: identity.clone(),
        rebased_transport: identity.clone(),
        source_chart: identity.clone(),
        target_chart: identity.clone(),
        candidate_coordinates: candidate_winding_coordinates.clone(),
        returned_coordinates: returned_winding_coordinates.clone(),
        adjoint_steps: vec![CausalAdjointStepInput {
            name: "factor-current-through-rested-winding-constitution".to_owned(),
            forward: identity,
            domain_metric: metric.clone(),
            codomain_metric: metric,
        }],
        terminal_covector: winding_difference.returned_winding_covector.clone(),
        native_obstructions: Vec::new(),
        open_deposition_boundary:
            "the complete world-return difference awaits atomic same-body cultivation".to_owned(),
        open_exterior: vec![
            "the complete factor reconstruction fibre remains open to richer future receivers"
                .to_owned(),
        ],
    })
    .map_err(|error| SourceNeutralEcologyError::Body(error.to_string()))?;
    if situated_difference.causal_adjoint.returned_source_covector
        != winding_difference.returned_winding_covector
        || situated_difference.chart.oriented_difference
            != winding_difference.returned_winding_covector
    {
        return Err(SourceNeutralEcologyError::Body(
            "the situated causal adjoint did not return the complete winding difference".to_owned(),
        ));
    }
    Ok(SourceNeutralSituatedDifferenceBody {
        candidate_winding_coordinates,
        returned_winding_coordinates,
        winding_difference,
        selected_branch,
        selected_branch_thread: branch_functional.thread_address.clone(),
        selected_factor,
        selected_factor_native,
        selected_reconstruction_fibre_address: selected_fibre.address.clone(),
        situated_difference,
    })
}

fn complete_signed_factor_difference(
    factor_population: usize,
    candidate: &[(u32, BigUint)],
    returned: &[(u32, BigUint)],
) -> Result<Vec<BigInt>, SourceNeutralEcologyError> {
    fn dense(
        factor_population: usize,
        current: &[(u32, BigUint)],
    ) -> Result<Vec<BigInt>, SourceNeutralEcologyError> {
        let mut dense = vec![BigInt::ZERO; factor_population];
        let mut seen = BTreeSet::new();
        for (factor, coefficient) in current {
            let at = usize::try_from(*factor).map_err(|_| {
                SourceNeutralEcologyError::Body(
                    "a factor current escaped its complete address".to_owned(),
                )
            })?;
            if at >= factor_population || !seen.insert(*factor) {
                return Err(SourceNeutralEcologyError::Body(
                    "a factor current is duplicated or outside its complete carrier".to_owned(),
                ));
            }
            dense[at] = BigInt::from(coefficient.clone());
        }
        Ok(dense)
    }
    let candidate = dense(factor_population, candidate)?;
    let returned = dense(factor_population, returned)?;
    Ok(returned
        .into_iter()
        .zip(candidate)
        .map(|(returned, candidate)| returned - candidate)
        .collect())
}

fn unique_largest_rational_magnitude(
    values: impl IntoIterator<Item = (usize, Rat)>,
    plural_reason: &str,
) -> Result<usize, SourceNeutralEcologyError> {
    let mut maximum = None::<Rat>;
    let mut anchors = Vec::new();
    for (at, value) in values {
        let magnitude = value.abs();
        if magnitude.is_zero() {
            continue;
        }
        match maximum.as_ref() {
            None => {
                maximum = Some(magnitude);
                anchors = vec![at];
            }
            Some(standing) if &magnitude > standing => {
                maximum = Some(magnitude);
                anchors = vec![at];
            }
            Some(standing) if &magnitude == standing => anchors.push(at),
            Some(_) => {}
        }
    }
    if anchors.len() != 1 {
        return Err(SourceNeutralEcologyError::Body(plural_reason.to_owned()));
    }
    Ok(anchors[0])
}

fn source_neutral_family_orientation(
    rest: &SourceNeutralEcologyRest,
) -> Result<Vec<i8>, SourceNeutralEcologyError> {
    let rank = rest.body.branches().len();
    let zero = Rat::from_integer(BigInt::from(0));
    if rank == 0 {
        return Err(SourceNeutralEcologyError::Body(
            "the source-neutral winding chart is empty".to_owned(),
        ));
    }
    let branch_coordinates = rest
        .body
        .branches()
        .iter()
        .map(|branch| (branch.thread_address.as_str(), branch.branch))
        .collect::<BTreeMap<_, _>>();
    if branch_coordinates.len() != rank
        || branch_coordinates
            .values()
            .any(|coordinate| *coordinate >= rank)
    {
        return Err(SourceNeutralEcologyError::Body(
            "the source-neutral winding chart is not a total coordinate family".to_owned(),
        ));
    }
    let fibres = rest.body.ecology().exact_reconstruction_fibres();
    let mut thread_sections = branch_coordinates
        .iter()
        .map(|(thread, coordinate)| {
            let mut section = vec![zero.clone(); rank];
            section[*coordinate] = Rat::from_integer(BigInt::from(1));
            ((*thread).to_owned(), section)
        })
        .collect::<BTreeMap<_, _>>();
    for thread in rest
        .body
        .ecology()
        .mixed_constitutive_families()
        .iter()
        .flat_map(|family| [&family.left_thread, &family.right_thread])
    {
        if thread_sections.contains_key(thread) {
            continue;
        }
        let sections = fibres
            .iter()
            .filter(|fibre| &fibre.thread == thread)
            .map(|fibre| fibre.returned_covector.clone())
            .collect::<BTreeSet<_>>();
        if sections.len() != 1 {
            return Err(SourceNeutralEcologyError::Body(format!(
                "thread {thread} has no unique returned winding section"
            )));
        }
        let section = sections.into_iter().next().expect("one exact section");
        if section.len() != rank || section.iter().all(|coefficient| coefficient == &zero) {
            return Err(SourceNeutralEcologyError::Body(format!(
                "thread {thread} escaped the source-neutral winding chart"
            )));
        }
        thread_sections.insert(thread.clone(), section);
    }

    let factor_hands = source_neutral_factor_hands(rest)?;

    let mut family_orientation = Vec::with_capacity(
        rest.body
            .ecology()
            .mixed_constitutive_families()
            .len()
            .saturating_mul(rest.granular.factor_faces().len()),
    );
    for family in rest.body.ecology().mixed_constitutive_families() {
        let left = thread_sections.get(&family.left_thread).ok_or_else(|| {
            SourceNeutralEcologyError::Body("a left winding section is absent".to_owned())
        })?;
        let right = thread_sections.get(&family.right_thread).ok_or_else(|| {
            SourceNeutralEcologyError::Body("a right winding section is absent".to_owned())
        })?;
        for face in rest.granular.factor_faces() {
            if !family.dependent_receiver_support.contains(&face.native) {
                family_orientation.push(0);
                continue;
            }
            let left_hand = section_hand(face.factor, left, &factor_hands)?;
            let right_hand = section_hand(face.factor, right, &factor_hands)?;
            family_orientation.push(left_hand.checked_mul(right_hand).ok_or_else(|| {
                SourceNeutralEcologyError::Body(
                    "the constitutive orientation escaped its signed line".to_owned(),
                )
            })?);
        }
    }
    Ok(family_orientation)
}

/// Recover the complete signed factor/branch incidence from the exact dependent receiver fibres.
/// This is shared by the resident receiver-history constitution and the UAR3 cross-organ chart so
/// the two passages cannot silently invent different factor orientations.
fn source_neutral_factor_hands(
    rest: &SourceNeutralEcologyRest,
) -> Result<BTreeMap<(u32, usize), i8>, SourceNeutralEcologyError> {
    let fibres = rest.body.ecology().exact_reconstruction_fibres();
    let mut factor_hands = BTreeMap::<(u32, usize), i8>::new();
    for face in rest.granular.factor_faces() {
        for branch in rest.body.branches() {
            let hands = fibres
                .iter()
                .filter(|fibre| {
                    fibre.thread == branch.thread_address
                        && fibre.dependent_receiver_fibre == BTreeSet::from([face.native])
                })
                .filter_map(|fibre| orientation(&fibre.returned_covector))
                .collect::<BTreeSet<_>>();
            if hands.len() != 1 {
                return Err(SourceNeutralEcologyError::Body(format!(
                    "native factor {} lost coordinate {} orientation",
                    face.factor, branch.branch
                )));
            }
            factor_hands.insert(
                (face.factor, branch.branch),
                *hands.iter().next().expect("one exact orientation"),
            );
        }
    }
    Ok(factor_hands)
}

fn source_neutral_emitting_thread_current(
    ecology: &NativeSituatedSpoolBundle,
    thread_address: &str,
) -> Result<ExactComplexWaveCurrent, SourceNeutralEcologyError> {
    let thread = ecology
        .native()
        .spools
        .iter()
        .flat_map(|spool| &spool.threads)
        .find(|thread| thread.address == thread_address)
        .ok_or_else(|| {
            SourceNeutralEcologyError::Body(format!(
                "standing winding thread {thread_address} disappeared"
            ))
        })?;
    let emitting_native = thread
        .occurrences
        .first()
        .map(|occurrence| occurrence.emitting_native)
        .ok_or_else(|| {
            SourceNeutralEcologyError::Body(format!(
                "standing winding thread {thread_address} has no occurrence"
            ))
        })?;
    thread
        .parametrons
        .iter()
        .find(|cell| cell.native == emitting_native)
        .map(|cell| cell.current.clone())
        .ok_or_else(|| {
            SourceNeutralEcologyError::Body(format!(
                "standing winding thread {thread_address} has no emitting current"
            ))
        })
}

/// Exact dependency closure of the source-neutral native-radiation law.  Receiver-radical basis
/// vectors are deliberately absent: the executable mount consumes the native spool, mixed
/// constitutive families, returned winding sections/orientations, and organ constitutions, while
/// the radical remains reconstruction testimony beside that law.
fn source_neutral_native_conduct_constitution_identity(
    ecology: &NativeSituatedSpoolBundle,
    branches: &[SourceNeutralCultivationBranch],
    returned_deposits: &[SourceNeutralReturnedDeposit],
    granular: &NativeGranularPotential,
    relational: &SourceNeutralRelationalMorphology,
    acoustic: &SourceNeutralAcousticMorphology,
    optical: &SourceNeutralOpticalMorphology,
) -> String {
    let returned_receiver_sections = ecology
        .exact_reconstruction_fibres()
        .iter()
        .map(|fibre| {
            (
                fibre.address.as_str(),
                fibre.thread.as_str(),
                &fibre.returned_covector,
                &fibre.dependent_receiver_fibre,
            )
        })
        .collect::<Vec<_>>();
    digest(&(
        "soma-life.source-neutral-native-conduct-constitution.v1",
        ecology.native(),
        ecology.mixed_constitutive_families(),
        returned_receiver_sections,
        branches,
        returned_deposits,
        granular.identity(),
        relational.identity(),
        acoustic.identity(),
        optical.identity(),
    ))
}

/// Receiver identity of one complete native radiation consequence, excluding only the parent-rest
/// lineage label and the section digest which necessarily rehashes that label.  Every productive
/// current, boundary, phase-front, successor, reconstruction and apparatus flag remains present.
fn source_neutral_native_receiver_consequence_identity(
    section: &SourceNeutralResidentRadiationSection,
) -> String {
    let conditioned = section
        .radiation
        .conditioned_current
        .as_ref()
        .map(|conditioned| &conditioned.passage);
    digest(&(
        "soma-life.source-neutral-native-receiver-consequence.v1",
        (
            section.schema.as_str(),
            section.rest_identity_sha256.as_str(),
            section.ingress_current_identity_sha256.as_str(),
            section.entered_octet_population,
            &section.crossed_structural_ports,
            &section.boundary_front,
            &section.branches,
        ),
        (
            &section.phase_front_higher_faces,
            &section.phase_front_ports,
            &section.situated_receiver_higher_faces,
            &section.situated_receiver_ports,
            &section.complete_successor_addressed_faces,
            section.complete_successor_zero_face_population,
            conditioned,
        ),
        (
            &section.radiation.receiver_coordinate_denominator,
            &section.radiation.ports,
            &section.radiation.port_returns,
            &section.radiation.entering_current,
            &section.radiation.total_returned_current,
            &section.radiation.stored_difference,
            section.radiation.local_balance_closes,
            section.radiation.phase_locked_port_population,
            section.radiation.phase_front_is_unique,
            &section.radiation.situated_receiver_pairing,
        ),
        (
            &section.radiation.complete_successor_faces,
            section.radiation.complete_successor_face_population,
            section.radiation.active_factor_population,
            section.radiation.native_factor_population,
            section.radiation.moment_field_materialized,
            section.radiation.moment_factorization_retained,
            section.radiation.context_population,
            section.radiation.restriction_population,
            section.radiation.generator_population,
            &section.reconstruction_dag,
        ),
        (
            section.source_codec_consulted,
            section.exterior_reconstruction_fibre_reachable,
            section.invariant_transport_reuploaded,
            section.cpu_semantic_replay_after_device,
        ),
    ))
}

fn source_neutral_entering_current(
    _rest: &SourceNeutralEcologyRest,
    projective: &GranularNativeProjectiveCurrent,
) -> Result<ExactComplexWaveCurrent, SourceNeutralEcologyError> {
    if projective.entering_current.is_zero() {
        return Err(SourceNeutralEcologyError::Body(
            "the native projective ingress lies in the complete current kernel".to_owned(),
        ));
    }
    Ok(projective.entering_current.clone())
}

/// Exact quadratic charge of one source-neutral ingress section.  This is the separately caused
/// realization current which later meets the exterior target-current partition.  No factor
/// ordinal, source byte, requested answer, or digest contributes to its magnitude.
fn quadratic_realization_current(
    projective: &GranularNativeProjectiveCurrent,
) -> Result<BigUint, SourceNeutralEcologyError> {
    let charge = projective
        .integrated_factor_current
        .iter()
        .fold(BigUint::ZERO, |sum, coordinate| {
            sum + &coordinate.incidence * &coordinate.incidence
        });
    if charge.is_zero() {
        return Err(SourceNeutralEcologyError::Body(
            "the exterior realization current lies in the complete native factor kernel".to_owned(),
        ));
    }
    Ok(charge)
}

fn realization_port(index: u16) -> Option<GranularExteriorPort> {
    if index == 0 {
        Some(GranularExteriorPort::Opening)
    } else if index <= 256 {
        Some(GranularExteriorPort::Octet(u8::try_from(index - 1).ok()?))
    } else if index == 257 {
        Some(GranularExteriorPort::Closure)
    } else {
        None
    }
}
