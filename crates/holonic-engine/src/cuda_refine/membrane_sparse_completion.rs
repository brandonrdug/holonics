use super::*;

impl ResidentMembraneInteriorWord {
    pub(super) fn complete_resident_sparse_quadratic_receivers(
        &mut self,
        address: &ResidentFactoredMomentReceiverAddress,
    ) -> Result<ResidentFactoredMomentReceiverReturn, CudaRefineError> {
        if trace_configuration().holonics_phase_trace {
            let shape = self
                .factored_receiver_history
                .as_ref()
                .and_then(|mount| mount.transported_image.as_ref())
                .map(|transport| {
                    (
                        transport.sparse_pair_completion,
                        transport.sparse_conditioned.is_some(),
                        transport.productive_receiver.is_some(),
                    )
                });
            eprintln!("mem6-pair-complete enter shape={shape:?}");
        }
        let live_address = match self.resident_factored_moment_receiver_address() {
            Ok(address) => address,
            Err(error) => {
                if trace_configuration().holonics_phase_trace {
                    eprintln!("mem6-pair-complete live-address-refusal: {error}");
                }
                return Err(error);
            }
        };
        if &live_address != address {
            if trace_configuration().holonics_phase_trace {
                eprintln!(
                    "mem6-pair-complete address-join-refusal live={:?} supplied={:?}",
                    live_address, address,
                );
            }
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let (
            source_address,
            target_generation,
            pair_population,
            target_limb_count,
            maximal_target,
            receiver_population,
            output_limb_count,
            output_bound,
            output_denominator,
            receiver_launches,
            apparatus_shape_host_egress_octets,
            continuation_launches,
            continuation_synchronizations,
            native_unconditioned_continuation,
        ) = {
            let Some(transport) = self
                .factored_receiver_history
                .as_ref()
                .and_then(|mount| mount.transported_image.as_ref())
            else {
                if trace_configuration().holonics_phase_trace {
                    eprintln!("mem6-pair-complete absent-transport");
                }
                return Err(CudaRefineError::MembraneInteriorWordShape);
            };
            let Some(receiver) = transport.productive_receiver.as_ref() else {
                if trace_configuration().holonics_phase_trace {
                    eprintln!("mem6-pair-complete absent-receiver");
                }
                return Err(CudaRefineError::MembraneInteriorWordShape);
            };
            if !transport.sparse_pair_completion {
                return Err(CudaRefineError::MembraneInteriorWordShape);
            }
            let (
                target_limb_count,
                maximal_target,
                continuation_launches,
                continuation_synchronizations,
                continuation_shape_octets,
                native_unconditioned_continuation,
            ) = if let Some(conditioned) = transport.sparse_conditioned.as_ref() {
                (
                    conditioned.coefficient_limb_count as usize,
                    conditioned.maximal_coefficient.clone(),
                    conditioned.launches,
                    conditioned.synchronizations,
                    conditioned.apparatus_shape_host_egress_octets,
                    false,
                )
            } else if transport.sparse_native_boundary.is_some() {
                (
                    transport.numerator_limb_count as usize,
                    transport
                        .maximal_numerator
                        .to_biguint()
                        .ok_or(CudaRefineError::MembraneInteriorWordShape)?,
                    0,
                    0,
                    0,
                    true,
                )
            } else {
                if trace_configuration().holonics_phase_trace {
                    eprintln!("mem6-pair-complete absent-continuing-current");
                }
                return Err(CudaRefineError::MembraneInteriorWordShape);
            };
            (
                transport.source_address.clone(),
                transport.target_generation,
                transport.transported_row_population as usize,
                target_limb_count,
                maximal_target,
                receiver.receiver_population as usize,
                receiver.output_limb_count as usize,
                receiver.output_bound.clone(),
                receiver
                    .output_denominator
                    .clone()
                    .ok_or(CudaRefineError::MembraneInteriorWordShape)?,
                receiver.launches,
                receiver
                    .apparatus_shape_host_egress_octets
                    .checked_add(continuation_shape_octets)
                    .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
                continuation_launches,
                continuation_synchronizations,
                native_unconditioned_continuation,
            )
        };
        if pair_population == 0
            || target_limb_count == 0
            || receiver_population == 0
            || output_limb_count == 0
            || output_denominator != BigInt::one()
        {
            if trace_configuration().holonics_phase_trace {
                eprintln!(
                    "mem6-pair-complete malformed-shape pairs={} target-limbs={} receivers={} output-limbs={} denominator={}",
                    pair_population,
                    target_limb_count,
                    receiver_population,
                    output_limb_count,
                    output_denominator,
                );
            }
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let mut obstruction = [0_u32; 1];
        let mut admitted = [0_u32; 1];
        let mut output_signs = vec![0_u8; receiver_population];
        let mut output_limbs = vec![0_u32; receiver_population * output_limb_count];
        {
            let transport = self
                .factored_receiver_history
                .as_ref()
                .and_then(|mount| mount.transported_image.as_ref())
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let receiver = transport
                .productive_receiver
                .as_ref()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            transport.overflow.read(&mut obstruction).map_err(|error| {
                if trace_configuration().holonics_phase_trace {
                    eprintln!("mem6-pair-complete overflow-read-refusal: {error}");
                }
                error
            })?;
            transport
                .productive_admitted
                .read(&mut admitted)
                .map_err(|error| {
                    if trace_configuration().holonics_phase_trace {
                        eprintln!("mem6-pair-complete admission-read-refusal: {error}");
                    }
                    error
                })?;
            receiver
                .output_signs
                .read(&mut output_signs)
                .map_err(|error| {
                    if trace_configuration().holonics_phase_trace {
                        eprintln!("mem6-pair-complete receiver-sign-read-refusal: {error}");
                    }
                    error
                })?;
            receiver
                .output_limbs
                .read(&mut output_limbs)
                .map_err(|error| {
                    if trace_configuration().holonics_phase_trace {
                        eprintln!("mem6-pair-complete receiver-limb-read-refusal: {error}");
                    }
                    error
                })?;
        }
        if obstruction[0] != 0 || admitted[0] != 1 {
            if trace_configuration().holonics_phase_trace {
                eprintln!(
                    "mem6-pair-complete device-refusal obstruction={} admitted={}",
                    obstruction[0], admitted[0],
                );
            }
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let receiver_numerators = output_signs
            .iter()
            .enumerate()
            .map(|(output, sign)| {
                let begin = output * output_limb_count;
                decode_signed_magnitude(*sign, &output_limbs[begin..begin + output_limb_count])
                    .map_err(|error| {
                        if trace_configuration().holonics_phase_trace {
                            let nonzero = output_limbs[begin..begin + output_limb_count]
                                .iter()
                                .any(|limb| *limb != 0);
                            eprintln!(
                                "mem6-pair-complete receiver-decode-refusal output={} sign={} nonzero={} limbs={}: {error}",
                                output,
                                sign,
                                nonzero,
                                output_limb_count,
                            );
                        }
                        error
                    })
            })
            .collect::<Result<Vec<_>, _>>()?;
        if receiver_numerators
            .iter()
            .any(|numerator| numerator.magnitude() > &output_bound)
        {
            if trace_configuration().holonics_phase_trace {
                let observed = receiver_numerators
                    .iter()
                    .map(|value| value.magnitude())
                    .max()
                    .cloned()
                    .unwrap_or_else(BigUint::zero);
                eprintln!(
                    "mem6-pair-complete receiver-bound-refusal observed={} bound={}",
                    observed, output_bound,
                );
            }
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let receiver_coordinates = receiver_numerators
            .into_iter()
            .map(Rat::from_integer)
            .collect::<Vec<_>>();

        let (next_state_population, next_state_ids_host) = {
            let mount = self
                .factored_receiver_history
                .as_ref()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let source = mount
                .sparse_pair
                .as_ref()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let transport = mount
                .transported_image
                .as_ref()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            if let Some(conditioned) = transport.sparse_conditioned.as_ref() {
                if conditioned.state_population == 0 {
                    let mut population = [0_u32; 1];
                    conditioned.state_population_device.read(&mut population)?;
                    let population = population[0] as usize;
                    if population == 0
                        || population
                            > transport
                                .sparse_native_boundary
                                .as_ref()
                                .map(|native| native.face_population as usize)
                                .unwrap_or(1)
                    {
                        return Err(CudaRefineError::MembraneInteriorWordShape);
                    }
                    let mut state_ids = vec![0_u32; population];
                    conditioned.state_ids.read(&mut state_ids)?;
                    (population, state_ids)
                } else {
                    if conditioned.state_ids_host.len() != conditioned.state_population as usize {
                        return Err(CudaRefineError::MembraneInteriorWordShape);
                    }
                    (
                        conditioned.state_population as usize,
                        conditioned.state_ids_host.clone(),
                    )
                }
            } else if native_unconditioned_continuation {
                let population = (source.state_population as usize)
                    .checked_mul(source.action.generator_population as usize)
                    .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
                let state_ids = source
                    .state_ids_host
                    .iter()
                    .flat_map(|state| {
                        std::iter::repeat_n(*state, source.action.generator_population as usize)
                    })
                    .collect::<Vec<_>>();
                if population == 0 || state_ids.len() != population {
                    return Err(CudaRefineError::MembraneInteriorWordShape);
                }
                (population, state_ids)
            } else {
                return Err(CudaRefineError::MembraneInteriorWordShape);
            }
        };

        let mut admitted_relational_continuation = None;
        {
            let mount = self
                .factored_receiver_history
                .as_mut()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let mut transport = mount
                .transported_image
                .take()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let source = mount
                .sparse_pair
                .take()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let receiver = transport
                .productive_receiver
                .take()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let (next_coefficients, next_state_ids, next_coefficient_state_capacity) =
                if native_unconditioned_continuation {
                    if transport.sparse_conditioned.is_some()
                        || transport.sparse_native_boundary.is_none()
                    {
                        return Err(CudaRefineError::MembraneInteriorWordShape);
                    }
                    (
                        transport.limbs,
                        Buffer::of(&next_state_ids_host)?,
                        next_state_population,
                    )
                } else {
                    let mut conditioned = transport
                        .sparse_conditioned
                        .take()
                        .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
                    if conditioned.coefficient_state_capacity < next_state_population as u32 {
                        return Err(CudaRefineError::MembraneInteriorWordShape);
                    }
                    admitted_relational_continuation = conditioned.relational_continuation.take();
                    (
                        conditioned.coefficients,
                        conditioned.state_ids,
                        conditioned.coefficient_state_capacity as usize,
                    )
                };
            if source.generation != source_address.generation
                || source.pair_population as usize != pair_population
                || target_generation != source.generation.saturating_add(1)
            {
                if trace_configuration().holonics_phase_trace {
                    eprintln!(
                        "mem6-pair-complete lineage-refusal source={} address={} pairs={}/{} target={} expected={}",
                        source.generation,
                        source_address.generation,
                        source.pair_population,
                        pair_population,
                        target_generation,
                        source.generation.saturating_add(1),
                    );
                }
                return Err(CudaRefineError::MembraneInteriorWordShape);
            }
            let old_coefficient_octets = (source.coefficient_state_capacity as u64)
                .checked_mul(pair_population as u64)
                .and_then(|held| held.checked_mul(source.coefficient_limb_count as u64))
                .and_then(|held| held.checked_mul(std::mem::size_of::<u32>() as u64))
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            let new_coefficient_octets = (next_coefficient_state_capacity as u64)
                .checked_mul(pair_population as u64)
                .and_then(|held| held.checked_mul(target_limb_count as u64))
                .and_then(|held| held.checked_mul(std::mem::size_of::<u32>() as u64))
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            let resident_octets = source
                .resident_octets
                .checked_sub(old_coefficient_octets)
                .and_then(|held| held.checked_add(new_coefficient_octets))
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            let mut section_identity = Sha256::new();
            section_identity.update(b"holonic-engine.state-addressed-sparse-quadratic-section.v1");
            section_identity.update(receiver.section_lineage_identity_sha256.as_bytes());
            for state in &next_state_ids_host {
                section_identity.update(state.to_le_bytes());
            }
            let section_identity_sha256 = section_identity
                .finalize()
                .iter()
                .map(|octet| format!("{octet:02x}"))
                .collect::<String>();
            mount.sparse_pair = Some(ResidentSparseQuadraticMomentState {
                generation: target_generation,
                section_identity_sha256,
                state_population: next_state_population as u32,
                coefficient_state_capacity: next_coefficient_state_capacity as u32,
                state_ids_host: next_state_ids_host,
                state_ids: next_state_ids,
                factor_population: source.factor_population,
                pair_population: source.pair_population,
                coefficient_limb_count: target_limb_count as u32,
                maximal_coefficient: maximal_target,
                coefficients: next_coefficients,
                situated_receiver_coefficients: source.situated_receiver_coefficients,
                situated_receiver_limb_count: source.situated_receiver_limb_count,
                maximal_situated_receiver_coefficient: source.maximal_situated_receiver_coefficient,
                pair_factors: source.pair_factors,
                pair_row_offsets: source.pair_row_offsets,
                target_offsets: source.target_offsets,
                source_pairs: source.source_pairs,
                multiplicities: source.multiplicities,
                generator_target_offsets: source.generator_target_offsets,
                generator_source_pairs: source.generator_source_pairs,
                generator_multiplicities: source.generator_multiplicities,
                maximal_incoming_multiplicity: source.maximal_incoming_multiplicity,
                action: source.action,
                resident_octets,
            });
        }
        let target_address = self
            .resident_sparse_quadratic_moment_address()
            .map_err(|error| {
                if trace_configuration().holonics_phase_trace {
                    eprintln!("mem6-pair-complete target-address-refusal: {error}");
                }
                error
            })?;
        if let Some(next) = admitted_relational_continuation {
            let mut state_present = vec![0_u32; next.state_count];
            let mut real_sign = vec![0_u8; next.state_count.saturating_mul(self.factors as usize)];
            let mut imaginary_sign =
                vec![0_u8; next.state_count.saturating_mul(self.factors as usize)];
            next.state_present.read(&mut state_present)?;
            next.factor_real_sign.read(&mut real_sign)?;
            next.factor_imaginary_sign.read(&mut imaginary_sign)?;
            if state_present.iter().all(|present| *present == 0)
                || real_sign
                    .iter()
                    .chain(&imaginary_sign)
                    .all(|sign| *sign == 0)
                || next.state_ids_host.len() != next.state_count
            {
                if trace_configuration().holonics_phase_trace {
                    eprintln!(
                        "mem6-pair-complete relational-continuation-refusal states={:?} present={:?} real={} imaginary={}",
                        next.state_ids_host,
                        state_present,
                        real_sign.iter().filter(|sign| **sign != 0).count(),
                        imaginary_sign.iter().filter(|sign| **sign != 0).count(),
                    );
                }
                return Err(CudaRefineError::MembraneInteriorWordShape);
            }
            let old = self
                .sparse_relational_current
                .take()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let mut receipt = old.receipt;
            let addressed_state_identity_sha256 = serde_json::to_vec(&(
                "holonic-engine.resident-sparse-relational-addressed-states.v3",
                &next.state_ids_host,
                &state_present,
                target_address.generation,
            ))
            .map(|bytes| {
                Sha256::digest(bytes)
                    .iter()
                    .map(|octet| format!("{octet:02x}"))
                    .collect::<String>()
            })
            .map_err(|_| CudaRefineError::MembraneInteriorWordShape)?;
            let source_current_identity_sha256 = serde_json::to_vec(&(
                "holonic-engine.state-addressed-sparse-quadratic-current.v1",
                &target_address,
            ))
            .map(|bytes| {
                Sha256::digest(bytes)
                    .iter()
                    .map(|octet| format!("{octet:02x}"))
                    .collect::<String>()
            })
            .map_err(|_| CudaRefineError::MembraneInteriorWordShape)?;
            let returned_current_identity_sha256 = serde_json::to_vec(&(
                "holonic-engine.resident-sparse-relational-current.v3",
                receipt.incidence_identity_sha256.as_str(),
                receipt.constitutive_family_identity_sha256.as_str(),
                source_current_identity_sha256.as_str(),
                addressed_state_identity_sha256.as_str(),
                target_address.generation,
            ))
            .map(|bytes| {
                Sha256::digest(bytes)
                    .iter()
                    .map(|octet| format!("{octet:02x}"))
                    .collect::<String>()
            })
            .map_err(|_| CudaRefineError::MembraneInteriorWordShape)?;
            let present_states = next
                .state_ids_host
                .iter()
                .copied()
                .zip(&state_present)
                .filter_map(|(state, present)| (*present != 0).then_some(state))
                .collect::<Vec<_>>();
            receipt.source_current_identity_sha256 = source_current_identity_sha256;
            receipt.returned_current_identity_sha256 = returned_current_identity_sha256;
            receipt.addressed_state_identity_sha256 = addressed_state_identity_sha256;
            receipt.addressed_state_population = next.state_count;
            receipt.present_state_population = present_states.len();
            receipt.root_state = if present_states.len() == 1 {
                present_states[0]
            } else {
                u32::MAX
            };
            receipt.returned_factor_bound = next.returned_factor_bound.clone();
            receipt.factor_limb_count = next.factor_limb_count;
            receipt.addressed_target_receiver_joined = true;
            receipt.launches = receipt.launches.saturating_add(next.launches);
            receipt.device_dependency_edges = receipt
                .device_dependency_edges
                .saturating_add(next.launches);
            receipt.synchronizations = receipt.synchronizations.saturating_add(1);
            receipt.successor_host_ingress_octets = receipt
                .successor_host_ingress_octets
                .saturating_add((next.state_count * std::mem::size_of::<u32>()) as u64);
            receipt.successor_host_egress_octets =
                receipt.successor_host_egress_octets.saturating_add(
                    (state_present.len() + real_sign.len() + imaginary_sign.len()) as u64,
                );
            receipt.resident_working_octets = next.resident_octets;
            let factor_real = Buffer::alloc(1)?;
            let factor_imaginary = Buffer::alloc(1)?;
            self.sparse_relational_current = Some(ResidentSparseRelationalCurrentState {
                receipt,
                state_present: next.state_present,
                states: next.states,
                state_count: next.state_count,
                bounded_i64_face_valid: false,
                factor_real,
                factor_imaginary,
                factor_real_sign: next.factor_real_sign,
                factor_real_limbs: next.factor_real_limbs,
                factor_imaginary_sign: next.factor_imaginary_sign,
                factor_imaginary_limbs: next.factor_imaginary_limbs,
                factor_limb_count: next.factor_limb_count,
                returned_factor_bound: next.returned_factor_bound,
            });
        }
        let terminal_host_egress_octets = [
            std::mem::size_of_val(&obstruction),
            std::mem::size_of_val(&admitted),
            std::mem::size_of_val(output_signs.as_slice()),
            std::mem::size_of_val(output_limbs.as_slice()),
        ]
        .into_iter()
        .try_fold(0_u64, |sum, octets| {
            sum.checked_add(u64::try_from(octets).ok()?)
        })
        .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        Ok(ResidentFactoredMomentReceiverReturn {
            address: address.clone(),
            source_address,
            target_address,
            receiver_coordinates,
            device: self.card.device_name.clone(),
            context_identity: self.card.context as usize,
            launches: receiver_launches.saturating_add(continuation_launches),
            device_dependency_edges: receiver_launches
                .saturating_add(continuation_launches)
                .saturating_sub(1),
            synchronizations: 1_u64.saturating_add(continuation_synchronizations),
            apparatus_shape_host_egress_octets,
            intermediate_host_egress_octets: 0,
            terminal_host_egress_octets,
            atomic_image_replacement: true,
            source_released_only_after_device_admission: true,
            receiver_history_quotient_rested: true,
            rooted_history_retained_hot: false,
            ambient_factor_square_materialized: false,
            host_rational_continuation: false,
        })
    }
}
