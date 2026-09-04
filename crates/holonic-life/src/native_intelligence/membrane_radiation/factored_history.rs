//! Owner-local radiation seam: factored history.

use super::super::{GranularMembraneStanding, NativeCausalMembrane};
use super::*;
use holonic_engine::cuda_refine::{
    ResidentQuadraticMomentFront, ResidentQuadraticMomentRestrictionSource,
};
use std::collections::BTreeMap;
impl<Standing: GranularMembraneStanding> NativeCausalMembrane<Standing> {
    /// Compare the production resident restriction atlas with the retained direct sparse witness
    /// on one actual occurrence.  This is a receiver gate, not a second inference route: only the
    /// resident result continues into ordinary radiation.
    pub fn verify_factored_receiver_history_occurrence(
        &mut self,
        occurrence: &str,
        payload: &[u8],
    ) -> Result<FactoredReceiverHistoryGateReceipt, NativeRadiationError> {
        let phase_trace = holonic_engine::cuda_refine::trace_configuration().holonics_phase_trace;
        let phase_origin = std::time::Instant::now();
        let section = self.radiate_granular_occurrence(occurrence, payload)?;
        if phase_trace {
            eprintln!("mem6-phase radiation {:?}", phase_origin.elapsed());
        }
        let resident = &section.resident_joint_current;
        let boundary = match &section.quadratic_moment_factorization.restrictions {
            ResidentQuadraticMomentRestrictionSource::ResidentBoundary(boundary) => boundary,
            ResidentQuadraticMomentRestrictionSource::DirectWitness(_) => {
                return Err(NativeRadiationError::RadiationDetail(
                    "the production receiver did not use its resident restriction atlas".to_owned(),
                ));
            }
        };
        let direct_restrictions = self
            .rested_body()
            .membrane_granular_potential()
            .mount()
            .and_then(|mounted| mounted.direct_boundary_restrictions(boundary))
            .map_err(|error| NativeRadiationError::RadiationDetail(error.to_string()))?;
        if phase_trace {
            eprintln!(
                "mem6-phase direct-restrictions {:?}",
                phase_origin.elapsed()
            );
        }
        let factor_population = section
            .quadratic_moment_factorization
            .generator_targets
            .len()
            .checked_div(section.quadratic_moment_factorization.generator_count as usize)
            .filter(|population| *population != 0)
            .ok_or_else(|| {
                NativeRadiationError::RadiationDetail(
                    "the projective current action lost its factor population".to_owned(),
                )
            })?;
        let generators = self
            .receiver_history_generators()
            .map_err(|error| NativeRadiationError::RadiationDetail(error.to_string()))?
            .to_vec();
        let source_family = section
            .quadratic_moment_factorization
            .contexts
            .iter()
            .map(|context| {
                let mut current = vec![BigInt::from(0); factor_population];
                for (factor, coefficient) in &context.factor_current {
                    current[*factor as usize] = BigInt::from(coefficient.clone());
                }
                (BigInt::from(context.quadratic_weight.clone()), current)
            })
            .collect::<Vec<_>>();
        let addressed_transition_receivers = direct_restrictions
            .iter()
            .map(|restriction| {
                let complex = self
                    .found_addressed_present_receiver_complex(&restriction.factor_current)
                    .map_err(|error| NativeRadiationError::RadiationDetail(error.to_string()))?;
                if phase_trace {
                    eprintln!(
                        "mem6-phase addressed-forms {:?} receivers={} functionals={} terms={}",
                        phase_origin.elapsed(),
                        complex.receivers.len(),
                        complex.functionals.len(),
                        complex
                            .receivers
                            .iter()
                            .map(|receiver| receiver.terms.len())
                            .sum::<usize>(),
                    );
                }
                let values = complex
                    .contract_rank_one_family(&source_family)
                    .map_err(|error| NativeRadiationError::RadiationDetail(error.to_string()))?;
                Ok((complex, values))
            })
            .collect::<Result<Vec<_>, NativeRadiationError>>()?;
        if phase_trace {
            eprintln!("mem6-phase factored-readout {:?}", phase_origin.elapsed());
        }
        let factored_present_receiver_population = addressed_transition_receivers
            .iter()
            .map(|(complex, _)| complex.receivers.len())
            .sum::<usize>();
        let direct_transported_family = generators
            .iter()
            .flat_map(|generator| {
                source_family.iter().map(|(weight, current)| {
                    let mut transported = vec![BigInt::from(0); factor_population];
                    for (source, target) in generator.iter().copied().enumerate() {
                        transported[target as usize] += &current[source];
                    }
                    (weight.clone(), transported)
                })
            })
            .collect::<Vec<_>>();
        let resident_current_address = resident.resident_current.as_ref().ok_or_else(|| {
            NativeRadiationError::RadiationDetail(
                "the resident receiver returned no addressed current occurrence".to_owned(),
            )
        })?;
        let resident_transport = self
            .continue_resident_addressed_current_passage(
                resident_current_address,
                &section.quadratic_moment_factorization.contexts,
                &section.quadratic_moment_factorization.generator_targets,
                section.quadratic_moment_factorization.generator_count,
            )
            .map_err(|error| NativeRadiationError::RadiationDetail(error.to_string()))?;
        let direct_equal_sections = direct_transported_family.iter().fold(
            BTreeMap::<Vec<BigInt>, BigInt>::new(),
            |mut sections, (weight, current)| {
                *sections.entry(current.clone()).or_default() += weight;
                sections
            },
        );
        let resident_equal_sections = resident_transport.passage.target.iter().fold(
            BTreeMap::<Vec<BigInt>, BigInt>::new(),
            |mut sections, context| {
                let mut current = vec![BigInt::from(0); factor_population];
                for (factor, coefficient) in &context.factor_current {
                    current[*factor as usize] = BigInt::from(coefficient.clone());
                }
                *sections.entry(current).or_default() +=
                    BigInt::from(context.quadratic_weight.clone());
                sections
            },
        );
        let exact_direct_versus_resident_transport = direct_equal_sections
            == resident_equal_sections
            && resident_transport.passage.occurrences.len()
                == source_family
                    .len()
                    .checked_mul(generators.len())
                    .ok_or(NativeRadiationError::Extent)?
            && resident_transport.passage.occurrences.iter().all(|edge| {
                (edge.source_section as usize) < source_family.len()
                    && (edge.generator as usize) < generators.len()
                    && (edge.target_section as usize) < resident_transport.passage.target.len()
            });
        let resident_transported_family = resident_transport
            .passage
            .target
            .iter()
            .map(|context| {
                let mut current = vec![BigInt::from(0); factor_population];
                for (factor, coefficient) in &context.factor_current {
                    current[*factor as usize] = BigInt::from(coefficient.clone());
                }
                (BigInt::from(context.quadratic_weight.clone()), current)
            })
            .collect::<Vec<_>>();
        let first_target_sections = resident_transport.passage.target.clone();
        let first_target_address = resident_transport.target_address.clone();
        let resident_successor_transport = self
            .continue_resident_addressed_current_passage(
                &first_target_address,
                &first_target_sections,
                &section.quadratic_moment_factorization.generator_targets,
                section.quadratic_moment_factorization.generator_count,
            )
            .map_err(|error| NativeRadiationError::RadiationDetail(error.to_string()))?;
        let direct_successor_family = generators
            .iter()
            .flat_map(|generator| {
                first_target_sections.iter().map(|context| {
                    let mut transported = vec![BigInt::from(0); factor_population];
                    for (source, target) in generator.iter().copied().enumerate() {
                        if let Some((_, coefficient)) = context
                            .factor_current
                            .iter()
                            .find(|(factor, _)| *factor as usize == source)
                        {
                            transported[target as usize] += BigInt::from(coefficient.clone());
                        }
                    }
                    (BigInt::from(context.quadratic_weight.clone()), transported)
                })
            })
            .collect::<Vec<_>>();
        let direct_successor_sections = direct_successor_family.iter().fold(
            BTreeMap::<Vec<BigInt>, BigInt>::new(),
            |mut sections, (weight, current)| {
                *sections.entry(current.clone()).or_default() += weight;
                sections
            },
        );
        let resident_successor_sections = resident_successor_transport.passage.target.iter().fold(
            BTreeMap::<Vec<BigInt>, BigInt>::new(),
            |mut sections, context| {
                let mut current = vec![BigInt::from(0); factor_population];
                for (factor, coefficient) in &context.factor_current {
                    current[*factor as usize] = BigInt::from(coefficient.clone());
                }
                *sections.entry(current).or_default() +=
                    BigInt::from(context.quadratic_weight.clone());
                sections
            },
        );
        let resident_joining_addresses_close = resident_transport.source_address
            == *resident_current_address
            && resident_successor_transport.source_address == resident_transport.target_address;
        let exact_direct_versus_resident_successor = direct_successor_sections
            == resident_successor_sections
            && resident_successor_transport.passage.occurrences.len()
                == first_target_sections
                    .len()
                    .checked_mul(generators.len())
                    .ok_or(NativeRadiationError::Extent)?
            && !resident_successor_transport.source_current_mounted_this_pass
            && !resident_successor_transport.invariant_transport_reuploaded
            && resident_successor_transport.host_ingress_octets == 0
            && resident_joining_addresses_close;
        let exact_direct_versus_resident_transport =
            exact_direct_versus_resident_transport && exact_direct_versus_resident_successor;
        let resident_successor_family = resident_successor_transport
            .passage
            .target
            .iter()
            .map(|context| {
                let mut current = vec![BigInt::from(0); factor_population];
                for (factor, coefficient) in &context.factor_current {
                    current[*factor as usize] = BigInt::from(coefficient.clone());
                }
                (BigInt::from(context.quadratic_weight.clone()), current)
            })
            .collect::<Vec<_>>();
        if phase_trace {
            let source_weight_bits = section
                .quadratic_moment_factorization
                .contexts
                .iter()
                .map(|context| context.quadratic_weight.bits())
                .max()
                .unwrap_or(0);
            let source_coefficient_bits = section
                .quadratic_moment_factorization
                .contexts
                .iter()
                .flat_map(|context| {
                    context
                        .factor_current
                        .iter()
                        .map(|(_, coefficient)| coefficient.bits())
                })
                .max()
                .unwrap_or(0);
            eprintln!(
                "mem6-phase resident-current-transport {:?} first={}->{} successor={}->{} successor_ingress={} source_weight_bits={} source_coefficient_bits={}",
                phase_origin.elapsed(),
                resident_transport.passage.source.len(),
                resident_transport.passage.target.len(),
                resident_successor_transport.passage.source.len(),
                resident_successor_transport.passage.target.len(),
                resident_successor_transport.host_ingress_octets,
                source_weight_bits,
                source_coefficient_bits,
            );
        }
        let receiver_history_generator_square_closes = addressed_transition_receivers
            .iter()
            .map(|(complex, _)| {
                let direct_first = complex
                    .contract_rank_one_family(&direct_transported_family)
                    .map_err(|error| NativeRadiationError::RadiationDetail(error.to_string()))?;
                let resident_first = complex
                    .contract_rank_one_family(&resident_transported_family)
                    .map_err(|error| NativeRadiationError::RadiationDetail(error.to_string()))?;
                let direct_second = complex
                    .contract_rank_one_family(&direct_successor_family)
                    .map_err(|error| NativeRadiationError::RadiationDetail(error.to_string()))?;
                let resident_second = complex
                    .contract_rank_one_family(&resident_successor_family)
                    .map_err(|error| NativeRadiationError::RadiationDetail(error.to_string()))?;
                Ok(direct_first == resident_first && direct_second == resident_second)
            })
            .collect::<Result<Vec<_>, NativeRadiationError>>()?
            .into_iter()
            .all(|closed| closed);
        if phase_trace {
            eprintln!(
                "mem6-phase addressed-receiver-square {:?} source={} first={} second={}",
                phase_origin.elapsed(),
                source_family.len(),
                resident_transported_family.len(),
                resident_successor_family.len(),
            );
        }
        let families = resident
            .ports
            .first()
            .map(|port| port.family_overlaps.len())
            .ok_or_else(|| {
                NativeRadiationError::RadiationDetail(
                    "the resident receiver returned no addressed port".to_owned(),
                )
            })?;
        let receivers = resident.ports[0].receiver_overlaps.len();
        let mut factored_ports = (0..resident.ports.len())
            .map(|_| {
                (
                    vec![BigInt::from(0); families],
                    vec![BigInt::from(0); families],
                    vec![BigInt::from(0); receivers],
                    vec![BigInt::from(0); receivers],
                )
            })
            .collect::<Vec<_>>();
        for (restriction, values) in direct_restrictions.iter().zip(
            addressed_transition_receivers
                .iter()
                .map(|(_, values)| values),
        ) {
            let port = factored_ports
                .get_mut(restriction.port as usize)
                .ok_or_else(|| {
                    NativeRadiationError::RadiationDetail(
                        "a factored transition escaped its exterior port".to_owned(),
                    )
                })?;
            if values.len() != families * 2 + receivers * 2 {
                return Err(NativeRadiationError::RadiationDetail(
                    "a factored transition lost a declared receiver".to_owned(),
                ));
            }
            for family in 0..families {
                port.0[family] += &values[family];
                port.1[family] += &values[families + family];
            }
            for receiver in 0..receivers {
                port.2[receiver] += &values[families * 2 + receiver * 2];
                port.3[receiver] += &values[families * 2 + receiver * 2 + 1];
            }
        }
        let exact_direct_versus_factored_consequence = resident
            .ports
            .iter()
            .zip(&factored_ports)
            .all(|(direct, factored)| {
                direct
                    .reflected_family_overlaps
                    .iter()
                    .zip(&factored.0)
                    .all(|(direct, factored)| direct == factored)
                    && direct
                        .family_overlaps
                        .iter()
                        .zip(&factored.1)
                        .all(|(direct, factored)| direct == factored)
                    && direct
                        .receiver_overlaps
                        .iter()
                        .zip(&factored.2)
                        .all(|(direct, factored)| direct == factored)
                    && direct.receiver_action_norms.len() == factored.3.len()
                    && direct
                        .receiver_action_norms
                        .iter()
                        .zip(&factored.3)
                        .all(|(direct, factored)| BigInt::from(direct.clone()) == *factored)
            });
        let exact_direct_versus_descended_transport = receiver_history_generator_square_closes;
        if phase_trace {
            eprintln!("mem6-phase descended-witness {:?}", phase_origin.elapsed());
        }
        let direct_front = ResidentQuadraticMomentFront {
            contexts: section.quadratic_moment_factorization.contexts.clone(),
            resident_source: None,
            resident_image: None,
            restrictions: ResidentQuadraticMomentRestrictionSource::DirectWitness(
                direct_restrictions.clone(),
            ),
            generator_targets: section
                .quadratic_moment_factorization
                .generator_targets
                .clone(),
            generator_count: section.quadratic_moment_factorization.generator_count,
            presented_current: None,
        };
        let (entering_current, _) = exterior_boundary_current(payload)?;
        let direct = self
            .conduct_resident_quadratic_moment_front(
                &direct_front,
                boundary.universal_ports.len(),
                &entering_current,
                false,
            )
            .map_err(|error| NativeRadiationError::RadiationDetail(error.to_string()))?;
        if phase_trace {
            eprintln!(
                "mem6-phase resident-direct-witness {:?}",
                phase_origin.elapsed()
            );
        }
        let exact_direct_versus_resident_consequence = resident.factored_receiver_history
            == direct.factored_receiver_history
            && resident.ports == direct.ports
            && resident.port_returns == direct.port_returns
            && resident.entering_current == direct.entering_current
            && resident.total_returned_current == direct.total_returned_current
            && resident.stored_difference == direct.stored_difference
            && resident.local_balance_closes == direct.local_balance_closes
            && resident.phase_locked_port_population == direct.phase_locked_port_population
            && resident.phase_front_is_unique == direct.phase_front_is_unique
            && resident.context_population == direct.context_population
            && resident.restriction_population == direct.restriction_population
            && resident.generator_population == direct.generator_population;

        // Pivot the same operation complex from its source-current presentation into the native
        // image owner. The addressed functional-pair complexes are the membrane's actual dual
        // occurrence; no ambient factor-square form or source-family successor is founded here.
        let addressed_complexes = addressed_transition_receivers
            .iter()
            .map(|(complex, _)| complex.clone())
            .collect::<Vec<_>>();
        let addressed_complex_ports = direct_restrictions
            .iter()
            .map(|restriction| restriction.port)
            .collect::<Vec<_>>();
        let addressed_complex_classes = (0..addressed_complexes.len())
            .map(|address| u32::try_from(address).map_err(|_| NativeRadiationError::Extent))
            .collect::<Result<Vec<_>, _>>()?;
        let addressed_complex_scales =
            vec![num_bigint::BigUint::from(1_u8); addressed_complexes.len()];
        let image_receiver_mount = self
            .mount_resident_addressed_factored_receivers(
                &addressed_complexes,
                &addressed_complex_classes,
                &addressed_complex_scales,
                &addressed_complex_ports,
            )
            .map_err(|error| NativeRadiationError::RadiationDetail(error.to_string()))?;
        if phase_trace {
            eprintln!(
                "mem6-phase image-receiver-mount {:?}",
                phase_origin.elapsed()
            );
        }
        let flattened_generator_targets = generators.iter().flatten().copied().collect::<Vec<_>>();
        let image_foundation = self
            .mount_resident_factored_moment_foundation(
                &section.quadratic_moment_factorization.contexts,
                &flattened_generator_targets,
                generators.len() as u32,
            )
            .map_err(|error| NativeRadiationError::RadiationDetail(error.to_string()))?;
        if phase_trace {
            eprintln!("mem6-phase image-foundation {:?}", phase_origin.elapsed());
        }
        let expected_image_first = addressed_complexes
            .iter()
            .map(|complex| {
                complex
                    .contract_rank_one_family(&direct_transported_family)
                    .map(|values| {
                        values
                            .into_iter()
                            .map(Rat::from_integer)
                            .collect::<Vec<_>>()
                    })
            })
            .collect::<Result<Vec<_>, _>>()
            .map_err(|error| NativeRadiationError::RadiationDetail(error.to_string()))?
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();
        let expected_image_second = addressed_complexes
            .iter()
            .map(|complex| {
                complex
                    .contract_rank_one_family(&direct_successor_family)
                    .map(|values| {
                        values
                            .into_iter()
                            .map(Rat::from_integer)
                            .collect::<Vec<_>>()
                    })
            })
            .collect::<Result<Vec<_>, _>>()
            .map_err(|error| NativeRadiationError::RadiationDetail(error.to_string()))?
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();
        if expected_image_first.len() != image_receiver_mount.receiver_population as usize
            || expected_image_second.len() != image_receiver_mount.receiver_population as usize
        {
            return Err(NativeRadiationError::RadiationDetail(
                "the actual membrane receiver occurrence lost a functional-pair coordinate"
                    .to_owned(),
            ));
        }
        let image_first = self
            .continue_resident_factored_moment_passage(
                &image_foundation.target_address,
                &flattened_generator_targets,
                generators.len() as u32,
            )
            .map_err(|error| NativeRadiationError::RadiationDetail(error.to_string()))?;
        let image_second = self
            .continue_resident_factored_moment_passage(
                &image_first.target_address,
                &flattened_generator_targets,
                generators.len() as u32,
            )
            .map_err(|error| NativeRadiationError::RadiationDetail(error.to_string()))?;
        let resident_image_joining_addresses_close = image_first.source_address
            == image_foundation.target_address
            && image_second.source_address == image_first.target_address;
        let exact_direct_versus_resident_image_receivers = image_first.receiver_coordinates
            == expected_image_first
            && image_second.receiver_coordinates == expected_image_second;
        let resident_image_atomic_replacements =
            image_first.atomic_image_replacement && image_second.atomic_image_replacement;
        let resident_image_source_release_after_device_admission = image_first
            .source_released_only_after_device_admission
            && image_second.source_released_only_after_device_admission;
        let resident_image_host_rational_continuation =
            image_first.host_rational_continuation || image_second.host_rational_continuation;
        let resident_image_intermediate_host_egress_octets = image_first
            .intermediate_host_egress_octets
            .checked_add(image_second.intermediate_host_egress_octets)
            .ok_or(NativeRadiationError::Extent)?;
        let resident_image_apparatus_shape_host_egress_octets = image_first
            .apparatus_shape_host_egress_octets
            .checked_add(image_second.apparatus_shape_host_egress_octets)
            .ok_or(NativeRadiationError::Extent)?;
        let resident_image_launches = image_first
            .launches
            .checked_add(image_second.launches)
            .ok_or(NativeRadiationError::Extent)?;
        let resident_image_synchronizations = image_first
            .synchronizations
            .checked_add(image_second.synchronizations)
            .ok_or(NativeRadiationError::Extent)?;
        if phase_trace {
            eprintln!(
                "mem6-phase resident-image {:?} foundation_rank={} first_rank={} second_rank={} receivers={} launches={}",
                phase_origin.elapsed(),
                image_foundation.target_address.image_population,
                image_first.target_address.image_population,
                image_second.target_address.image_population,
                image_receiver_mount.receiver_population,
                resident_image_launches,
            );
        }
        let same_card_context = resident.context_identity == direct.context_identity
            && resident.context_identity == resident_transport.context_identity
            && resident.context_identity == resident_successor_transport.context_identity
            && resident.context_identity == image_receiver_mount.context_identity
            && resident.context_identity == image_foundation.context_identity
            && resident.context_identity == image_first.context_identity
            && resident.context_identity == image_second.context_identity;
        let resident_apparatus_closes = same_card_context
            && resident.intermediate_host_egress_octets == 0
            && !resident.invariant_transport_reuploaded
            && !resident.cpu_semantic_replay_after_device
            && resident.synchronizations == 1
            && resident_transport.intermediate_host_egress_octets == 0
            && !resident_transport.cpu_semantic_replay_after_device
            && resident_transport.synchronizations == 1
            && resident_successor_transport.intermediate_host_egress_octets == 0
            && !resident_successor_transport.cpu_semantic_replay_after_device
            && resident_successor_transport.synchronizations == 1
            && resident.successor_host_ingress_octets < direct.successor_host_ingress_octets
            && !image_receiver_mount.ambient_factor_square_materialized
            && !image_foundation.source_current_retained_hot
            && !image_foundation.ambient_covariance_materialized
            && exact_direct_versus_resident_image_receivers
            && resident_image_joining_addresses_close
            && resident_image_atomic_replacements
            && resident_image_source_release_after_device_admission
            && !resident_image_host_rational_continuation
            && resident_image_intermediate_host_egress_octets == 0
            && image_first.apparatus_shape_host_egress_octets == std::mem::size_of::<u32>() as u64
            && image_second.apparatus_shape_host_egress_octets == std::mem::size_of::<u32>() as u64
            && image_first.synchronizations == 2
            && image_second.synchronizations == 2;
        if !exact_direct_versus_resident_consequence
            || !exact_direct_versus_factored_consequence
            || !exact_direct_versus_descended_transport
            || !exact_direct_versus_resident_transport
            || !resident_apparatus_closes
        {
            return Err(NativeRadiationError::RadiationDetail(
                "the actual factored receiver-history gate did not close".to_owned(),
            ));
        }
        let operation_complex = resident.factored_receiver_history.clone();
        let identity_sha256 = digest(&(
            "soma-life.factored-receiver-history-gate.v8",
            occurrence,
            &section.exterior_source_sha256,
            &operation_complex,
            (
                exact_direct_versus_resident_transport,
                resident_transport.passage.source.len(),
                resident_transport.passage.occurrences.len(),
                resident_transport.passage.target.len(),
                resident_transport.passage.occurrences.len(),
                resident_successor_transport.passage.target.len(),
                resident_successor_transport.passage.occurrences.len(),
                resident_successor_transport.host_ingress_octets,
            ),
            [
                resident_current_address.generation,
                resident_transport.target_address.generation,
                resident_successor_transport.target_address.generation,
            ],
            resident_joining_addresses_close,
            [
                image_foundation.target_address.generation,
                image_first.target_address.generation,
                image_second.target_address.generation,
            ],
            resident_image_joining_addresses_close,
            exact_direct_versus_resident_image_receivers,
            resident_image_launches,
            (
                factored_present_receiver_population,
                resident.restriction_population,
                direct.restriction_population,
                resident.successor_host_ingress_octets,
                direct.successor_host_ingress_octets,
                resident.context_identity,
            ),
        ))?;
        Ok(FactoredReceiverHistoryGateReceipt {
            schema: "soma-life.factored-receiver-history-gate.v8".to_owned(),
            exterior_occurrence: occurrence.to_owned(),
            exterior_source_sha256: section.exterior_source_sha256,
            operation_complex,
            resident_restriction_population: resident.restriction_population,
            direct_restriction_population: direct.restriction_population,
            exact_direct_versus_resident_consequence,
            exact_direct_versus_factored_consequence,
            exact_direct_versus_descended_transport,
            exact_direct_versus_resident_transport,
            source_current_section_population: source_family.len(),
            first_target_current_section_population: resident_transported_family.len(),
            second_target_current_section_population: resident_successor_family.len(),
            resident_current_generations: [
                resident_current_address.generation,
                resident_transport.target_address.generation,
                resident_successor_transport.target_address.generation,
            ],
            resident_joining_addresses_close,
            resident_image_generations: [
                image_foundation.target_address.generation,
                image_first.target_address.generation,
                image_second.target_address.generation,
            ],
            resident_image_joining_addresses_close,
            resident_image_receiver_population: image_receiver_mount.receiver_population as usize,
            exact_direct_versus_resident_image_receivers,
            resident_image_atomic_replacements,
            resident_image_source_release_after_device_admission,
            resident_image_host_rational_continuation,
            resident_image_apparatus_shape_host_egress_octets,
            resident_image_intermediate_host_egress_octets,
            resident_image_launches,
            resident_image_synchronizations,
            factored_present_receiver_population,
            ambient_covariance_materialized: false,
            source_family_rescanned_by_successor: resident_successor_transport
                .source_current_mounted_this_pass
                || resident_successor_transport.invariant_transport_reuploaded
                || resident_successor_transport.host_ingress_octets != 0,
            resident_transport_source_context_population: resident_transport.passage.source.len(),
            resident_transport_candidate_context_population: resident_transport
                .passage
                .occurrences
                .len(),
            resident_transport_target_context_population: resident_transport.passage.target.len(),
            resident_transport_reconstruction_edge_population: resident_transport
                .passage
                .occurrences
                .len(),
            resident_successor_transport_target_context_population: resident_successor_transport
                .passage
                .target
                .len(),
            resident_successor_transport_reconstruction_edge_population:
                resident_successor_transport.passage.occurrences.len(),
            resident_successor_transport_host_ingress_octets: resident_successor_transport
                .host_ingress_octets,
            same_card_context,
            resident_successor_host_ingress_octets: resident.successor_host_ingress_octets,
            direct_successor_host_ingress_octets: direct.successor_host_ingress_octets,
            resident_intermediate_host_egress_octets: resident.intermediate_host_egress_octets,
            resident_invariant_transport_reuploaded: resident.invariant_transport_reuploaded,
            resident_cpu_semantic_replay_after_device: resident.cpu_semantic_replay_after_device,
            resident_launches: resident.launches,
            resident_synchronizations: resident.synchronizations,
            resident_transport_launches: resident_transport.launches
                + resident_successor_transport.launches,
            resident_transport_synchronizations: resident_transport.synchronizations
                + resident_successor_transport.synchronizations,
            identity_sha256,
        })
    }
}
