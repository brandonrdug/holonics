//! Resident generated-port current conditioning and successor completion.

use super::*;

impl ResidentMembraneInteriorWord {
    /// `D_p T_g x_s` before any receiver observes it. Resident joining addresses cross as apparatus testimony before the target
    /// word; no native coefficient or receiver value does. The complete restriction and target
    /// sections return only after that successor has been founded, so they are terminal passage
    /// testimony rather than a host-authored successor or an intermediate semantic replay.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn condition_resident_current_by_generated_ports(
        &mut self,
        source_address: &ResidentCurrentAddress,
        source_contexts: &[AddressedCurrentSection],
        generator_targets: &[u32],
        generator_count: u32,
        port_population: usize,
        boundary_states: &[u32],
        restriction_target_states: &Buffer,
        restriction_current: &Buffer,
        restriction_present: &Buffer,
        restriction_limb_count: usize,
        maximal_restriction: &BigUint,
        source_current_mounted_this_pass: bool,
        relational_continuation: Option<(
            CuDevicePtr,
            CuDevicePtr,
            usize,
            CuDevicePtr,
            CuDevicePtr,
            CuDevicePtr,
            CuDevicePtr,
            usize,
            ResidentSparseRelationalCurrentReceipt,
            BigUint,
        )>,
        presented_current: Option<&[(u32, BigUint)]>,
    ) -> Result<ResidentCompletedTargetObservationAperture, CudaRefineError> {
        self.validate_resident_current_address(source_address)?;
        let reference_ecology_compared = trace_configuration().holonics_uar2_conformance;
        let factors = self.factors as usize;
        let generators = generator_count as usize;
        let boundary_state_count = boundary_states.len();
        if factors == 0
            || boundary_state_count == 0
            || source_contexts.len() != source_address.section_population
            || generator_targets.len() != factors.saturating_mul(generators)
            || port_population == 0
            || port_population > u32::MAX as usize
            || restriction_limb_count == 0
            || maximal_restriction.is_zero()
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let maximal_slots = port_population
            .checked_mul(generators)
            .and_then(|extent| extent.checked_mul(boundary_state_count))
            .filter(|extent| *extent <= u32::MAX as usize)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let presented_generator_mask = vec![1_u8; generators];
        let selected_faces = Buffer::alloc(
            maximal_slots
                .checked_mul(std::mem::size_of::<u32>())
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        )?;
        let selected_restrictions = Buffer::alloc(
            maximal_slots
                .checked_mul(std::mem::size_of::<u32>())
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        )?;
        let selected_count = Buffer::alloc(std::mem::size_of::<u32>())?;
        selected_count.fill(0, std::mem::size_of::<u32>())?;
        let presented_generator_mask = Buffer::of(&presented_generator_mask)?;
        let mut presented_generator_mask_pointer = presented_generator_mask.pointer;
        let mut restriction_present_pointer = restriction_present.pointer;
        let mut selected_faces_pointer = selected_faces.pointer;
        let mut selected_restrictions_pointer = selected_restrictions.pointer;
        let mut selected_count_pointer = selected_count.pointer;
        let mut port_count_wire = port_population as u32;
        let mut generator_count_wire = generator_count;
        let mut boundary_state_count_wire = boundary_state_count as u32;
        let mut collect_arguments: [*mut c_void; 8] = [
            &mut presented_generator_mask_pointer as *mut u64 as *mut c_void,
            &mut restriction_present_pointer as *mut u64 as *mut c_void,
            &mut selected_faces_pointer as *mut u64 as *mut c_void,
            &mut selected_restrictions_pointer as *mut u64 as *mut c_void,
            &mut selected_count_pointer as *mut u64 as *mut c_void,
            &mut port_count_wire as *mut u32 as *mut c_void,
            &mut generator_count_wire as *mut u32 as *mut c_void,
            &mut boundary_state_count_wire as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card.membrane_generated_port_restriction_collect,
                    1,
                    1,
                    1,
                    1,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    collect_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(collect_membrane_selected_generated_port_restrictions)",
        )?;
        driver(
            unsafe { cuCtxSynchronize() },
            "cuCtxSynchronize(selected generated-port allocation extent)",
        )?;
        let mut selected_count_host = [0_u32; 1];
        selected_count.read(&mut selected_count_host)?;
        let selected_slot_count = selected_count_host[0] as usize;
        if selected_slot_count == 0 || selected_slot_count > maximal_slots {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let mut selected_faces_host = vec![0_u32; maximal_slots];
        let mut selected_restrictions_host = vec![0_u32; maximal_slots];
        selected_faces.read(&mut selected_faces_host)?;
        selected_restrictions.read(&mut selected_restrictions_host)?;
        selected_faces_host.truncate(selected_slot_count);
        selected_restrictions_host.truncate(selected_slot_count);
        let restriction_count = port_population
            .checked_mul(boundary_state_count)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let selected_source_states = selected_restrictions_host
            .iter()
            .map(|restriction| {
                let restriction = *restriction as usize;
                if restriction >= restriction_count {
                    return Err(CudaRefineError::MembraneInteriorWordShape);
                }
                Ok(boundary_states[restriction % boundary_state_count])
            })
            .collect::<Result<Vec<_>, _>>()?;
        // The direct sum contains only incidences whose addressed source states meet. The
        // cross-state complement is exactly radical and remains reconstructible from the source
        // and slot state populations; it is not materialized as a quadratic GPU rectangle.
        let mut candidate_source_contexts_host = Vec::<u32>::new();
        let mut candidate_selected_slots_host = Vec::<u32>::new();
        for (source_context, source) in source_contexts.iter().enumerate() {
            let source_state = source
                .boundary_state
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            if !boundary_states.contains(&source_state) {
                return Err(CudaRefineError::MembraneInteriorWordShape);
            }
            for (selected_slot, selected_state) in selected_source_states.iter().enumerate() {
                if source_state == *selected_state {
                    candidate_source_contexts_host.push(source_context as u32);
                    candidate_selected_slots_host.push(selected_slot as u32);
                }
            }
        }
        let candidate_count = candidate_source_contexts_host.len();
        if trace_configuration().holonics_phase_trace || trace_configuration().holonics_uar2_trace {
            eprintln!(
                "generated-port-continuation selected_slots={} source_contexts={} state_matched_candidates={} factors={} restriction_limbs={}",
                selected_slot_count,
                source_contexts.len(),
                candidate_count,
                factors,
                restriction_limb_count,
            );
        }
        if candidate_count == 0
            || candidate_count != candidate_selected_slots_host.len()
            || candidate_count > u32::MAX as usize
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }

        let (
            source_context_population,
            source_limb_count,
            maximal_current,
            source_active_factors,
            mut source_current_pointer,
            mut source_state_present_pointer,
            mut source_states_pointer,
        ) = {
            let source = self
                .factored_receiver_history
                .as_ref()
                .and_then(|mounted| mounted.current.as_ref())
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            (
                source.context_count as usize,
                source.current_limb_count as usize,
                source.maximal_current.clone(),
                source.active_factors.clone(),
                source.current_limbs.pointer,
                source.boundary_state_present.pointer,
                source.boundary_states.pointer,
            )
        };
        let (
            presented_current_device,
            presented_limb_count,
            maximal_presented_current,
            presented_current_ingress_octets,
        ) = match presented_current {
            None => (None, 0_usize, BigUint::from(1_u8), 0_u64),
            Some(current)
                if !current.is_empty()
                    && !current.windows(2).any(|pair| pair[0].0 >= pair[1].0)
                    && current.iter().all(|(factor, coefficient)| {
                        *factor < self.factors && !coefficient.is_zero()
                    }) =>
            {
                let maximal = current
                    .iter()
                    .map(|(_, coefficient)| coefficient)
                    .max()
                    .cloned()
                    .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
                let limb_count = maximal.to_u32_digits().len().max(1);
                let mut limbs = vec![0_u32; factors.saturating_mul(limb_count)];
                for (factor, coefficient) in current {
                    let digits = coefficient.to_u32_digits();
                    let begin = *factor as usize * limb_count;
                    limbs[begin..begin + digits.len()].copy_from_slice(&digits);
                }
                let ingress = u64::try_from(std::mem::size_of_val(&limbs[..]))
                    .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
                (Some(Buffer::of(&limbs)?), limb_count, maximal, ingress)
            }
            Some(_) => return Err(CudaRefineError::MembraneInteriorWordShape),
        };
        let maximal_preimage = generator_targets
            .chunks_exact(factors)
            .map(|generator| {
                let mut preimages = vec![0_usize; factors];
                for target in generator {
                    preimages[*target as usize] += 1;
                }
                preimages.into_iter().max().unwrap_or(0)
            })
            .max()
            .filter(|extent| *extent != 0)
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let maximal_transported = &maximal_current * BigUint::from(maximal_preimage);
        let transported_limb_count = maximal_transported.to_u32_digits().len().max(1);
        let first_product_bound = &maximal_transported * maximal_restriction;
        let first_product_limb_count = first_product_bound.to_u32_digits().len().max(1);
        let local_current_bound = &first_product_bound * &maximal_presented_current;
        let candidate_limb_count = local_current_bound.to_u32_digits().len().max(1);
        let target_maximal_bound = &local_current_bound * BigUint::from(candidate_count);
        let target_limb_count = target_maximal_bound.to_u32_digits().len().max(1);
        let target_weight_limb_count = 1_usize;
        let successor_factors = (0..generators)
            .flat_map(|generator| {
                source_active_factors
                    .iter()
                    .map(move |source| generator_targets[generator * factors + *source as usize])
            })
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        if successor_factors.is_empty() {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let mut successor_factor_coordinates = vec![u32::MAX; factors];
        for (local, factor) in successor_factors.iter().copied().enumerate() {
            successor_factor_coordinates[factor as usize] = local as u32;
        }
        let successor_factor_count = successor_factors.len();
        let transported_population = source_context_population
            .checked_mul(generators)
            .and_then(|extent| extent.checked_mul(successor_factor_count))
            .and_then(|extent| extent.checked_mul(transported_limb_count))
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let candidate_population = candidate_count
            .checked_mul(successor_factor_count)
            .and_then(|extent| extent.checked_mul(candidate_limb_count))
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let transported = Buffer::alloc(
            transported_population
                .checked_mul(std::mem::size_of::<u32>())
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        )?;
        let transported_state_present = Buffer::alloc(source_context_population * generators)?;
        let transported_states = Buffer::alloc(
            source_context_population
                .checked_mul(generators)
                .and_then(|extent| extent.checked_mul(std::mem::size_of::<u32>()))
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        )?;
        let candidates = Buffer::alloc(
            candidate_population
                .checked_mul(std::mem::size_of::<u32>())
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        )?;
        let first_product_scratch = Buffer::alloc(
            candidate_count
                .checked_mul(successor_factor_count)
                .and_then(|extent| extent.checked_mul(first_product_limb_count))
                .and_then(|extent| extent.checked_mul(std::mem::size_of::<u32>()))
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        )?;
        let candidate_source_contexts = Buffer::of(&candidate_source_contexts_host)?;
        let candidate_selected_slots = Buffer::of(&candidate_selected_slots_host)?;
        let candidate_state_present = Buffer::alloc(candidate_count)?;
        let candidate_states = Buffer::alloc(
            candidate_count
                .checked_mul(std::mem::size_of::<u32>())
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        )?;
        let target_state_present = Buffer::alloc(candidate_count)?;
        let target_states = Buffer::alloc(
            candidate_count
                .checked_mul(std::mem::size_of::<u32>())
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        )?;
        let candidate_to_target = Buffer::alloc(candidate_count * std::mem::size_of::<u32>())?;
        let target_member_offsets = Buffer::alloc(
            candidate_count
                .checked_add(1)
                .and_then(|extent| extent.checked_mul(std::mem::size_of::<u32>()))
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        )?;
        let target_members = Buffer::alloc(
            candidate_count
                .checked_mul(std::mem::size_of::<u32>())
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        )?;
        let target_cursors = Buffer::alloc(
            candidate_count
                .checked_mul(std::mem::size_of::<u32>())
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        )?;
        let target_count = Buffer::alloc(std::mem::size_of::<u32>())?;
        target_count.fill(0, std::mem::size_of::<u32>())?;
        let aggregation_obstruction = Buffer::alloc(std::mem::size_of::<u32>())?;
        aggregation_obstruction.fill(0, std::mem::size_of::<u32>())?;

        let action = self
            .quadratic_action
            .as_ref()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let mut generator_pointer = action.native_generator_targets.pointer;
        let source_active_factors_device = Buffer::of(&source_active_factors)?;
        let successor_factors_device = Buffer::of(&successor_factors)?;
        let successor_factor_coordinates_device = Buffer::of(&successor_factor_coordinates)?;
        let mut source_active_factors_pointer = source_active_factors_device.pointer;
        let mut successor_factors_pointer = successor_factors_device.pointer;
        let mut successor_factor_coordinates_pointer = successor_factor_coordinates_device.pointer;
        let mut transported_pointer = transported.pointer;
        let mut transported_state_present_pointer = transported_state_present.pointer;
        let mut transported_states_pointer = transported_states.pointer;
        let mut context_count_wire = source_context_population as u32;
        let mut factor_count_wire = self.factors;
        let mut source_active_factor_count_wire = source_active_factors.len() as u32;
        let mut successor_factor_count_wire = successor_factor_count as u32;
        let mut source_limb_count_wire = source_limb_count as u32;
        let mut transported_limb_count_wire = transported_limb_count as u32;
        let mut transport_active = ptr::null_mut();
        driver(
            unsafe {
                cuModuleGetFunction(
                    &mut transport_active,
                    self.card.module,
                    c"transport_membrane_active_factor_current_sections".as_ptr(),
                )
            },
            "cuModuleGetFunction(transport_membrane_active_factor_current_sections)",
        )?;
        let mut transport_arguments: [*mut c_void; 16] = [
            &mut source_current_pointer as *mut u64 as *mut c_void,
            &mut source_state_present_pointer as *mut u64 as *mut c_void,
            &mut source_states_pointer as *mut u64 as *mut c_void,
            &mut generator_pointer as *mut u64 as *mut c_void,
            &mut source_active_factors_pointer as *mut u64 as *mut c_void,
            &mut successor_factor_coordinates_pointer as *mut u64 as *mut c_void,
            &mut transported_pointer as *mut u64 as *mut c_void,
            &mut transported_state_present_pointer as *mut u64 as *mut c_void,
            &mut transported_states_pointer as *mut u64 as *mut c_void,
            &mut context_count_wire as *mut u32 as *mut c_void,
            &mut factor_count_wire as *mut u32 as *mut c_void,
            &mut source_active_factor_count_wire as *mut u32 as *mut c_void,
            &mut successor_factor_count_wire as *mut u32 as *mut c_void,
            &mut generator_count_wire as *mut u32 as *mut c_void,
            &mut source_limb_count_wire as *mut u32 as *mut c_void,
            &mut transported_limb_count_wire as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    transport_active,
                    self.card
                        .grid_for((source_context_population * generators) as u64)?,
                    1,
                    1,
                    self.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    transport_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(transport_membrane_active_factor_current_sections)",
        )?;
        let mut restriction_current_pointer = restriction_current.pointer;
        let mut restriction_target_states_pointer = restriction_target_states.pointer;
        let boundary_states_device = Buffer::of(boundary_states)?;
        let mut boundary_states_pointer = boundary_states_device.pointer;
        let mut candidate_source_contexts_pointer = candidate_source_contexts.pointer;
        let mut candidate_selected_slots_pointer = candidate_selected_slots.pointer;
        let mut candidate_pointer = candidates.pointer;
        let mut first_product_scratch_pointer = first_product_scratch.pointer;
        let mut presented_current_pointer = presented_current_device
            .as_ref()
            .map_or(0, |current| current.pointer);
        let mut candidate_state_present_pointer = candidate_state_present.pointer;
        let mut candidate_states_pointer = candidate_states.pointer;
        let mut selected_slot_count_wire = selected_slot_count as u32;
        let mut candidate_count_wire = candidate_count as u32;
        let mut restriction_limb_count_wire = restriction_limb_count as u32;
        let mut presented_limb_count_wire = presented_limb_count as u32;
        let mut presented_current_present_wire = u32::from(presented_current_device.is_some());
        let mut first_product_limb_count_wire = first_product_limb_count as u32;
        let mut candidate_limb_count_wire = candidate_limb_count as u32;
        let mut condition_active = ptr::null_mut();
        driver(
            unsafe {
                cuModuleGetFunction(
                    &mut condition_active,
                    self.card.module,
                    c"condition_membrane_active_factor_current_sections_by_generated_ports"
                        .as_ptr(),
                )
            },
            "cuModuleGetFunction(condition_membrane_active_factor_current_sections_by_generated_ports)",
        )?;
        let mut condition_arguments: [*mut c_void; 29] = [
            &mut transported_pointer as *mut u64 as *mut c_void,
            &mut transported_state_present_pointer as *mut u64 as *mut c_void,
            &mut transported_states_pointer as *mut u64 as *mut c_void,
            &mut restriction_current_pointer as *mut u64 as *mut c_void,
            &mut presented_current_pointer as *mut u64 as *mut c_void,
            &mut successor_factors_pointer as *mut u64 as *mut c_void,
            &mut selected_faces_pointer as *mut u64 as *mut c_void,
            &mut selected_restrictions_pointer as *mut u64 as *mut c_void,
            &mut restriction_target_states_pointer as *mut u64 as *mut c_void,
            &mut boundary_states_pointer as *mut u64 as *mut c_void,
            &mut candidate_source_contexts_pointer as *mut u64 as *mut c_void,
            &mut candidate_selected_slots_pointer as *mut u64 as *mut c_void,
            &mut candidate_pointer as *mut u64 as *mut c_void,
            &mut first_product_scratch_pointer as *mut u64 as *mut c_void,
            &mut candidate_state_present_pointer as *mut u64 as *mut c_void,
            &mut candidate_states_pointer as *mut u64 as *mut c_void,
            &mut context_count_wire as *mut u32 as *mut c_void,
            &mut factor_count_wire as *mut u32 as *mut c_void,
            &mut successor_factor_count_wire as *mut u32 as *mut c_void,
            &mut generator_count_wire as *mut u32 as *mut c_void,
            &mut selected_slot_count_wire as *mut u32 as *mut c_void,
            &mut candidate_count_wire as *mut u32 as *mut c_void,
            &mut boundary_state_count_wire as *mut u32 as *mut c_void,
            &mut transported_limb_count_wire as *mut u32 as *mut c_void,
            &mut restriction_limb_count_wire as *mut u32 as *mut c_void,
            &mut presented_limb_count_wire as *mut u32 as *mut c_void,
            &mut presented_current_present_wire as *mut u32 as *mut c_void,
            &mut first_product_limb_count_wire as *mut u32 as *mut c_void,
            &mut candidate_limb_count_wire as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    condition_active,
                    self.card.grid_for(candidate_count as u64)?,
                    1,
                    1,
                    self.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    condition_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(condition_membrane_active_factor_current_sections_by_generated_ports)",
        )?;
        if trace_configuration().holonics_phase_trace && source_context_population <= 2 {
            driver(
                unsafe { cuCtxSynchronize() },
                "cuCtxSynchronize(pre-junction generated-port trace)",
            )?;
            let mut transported_debug = vec![0_u32; transported_population];
            let mut candidate_debug = vec![0_u32; candidate_population];
            transported.read(&mut transported_debug)?;
            candidates.read(&mut candidate_debug)?;
            let transported_support = transported_debug
                .chunks_exact(successor_factor_count * transported_limb_count)
                .map(|row| {
                    row.chunks_exact(transported_limb_count)
                        .enumerate()
                        .filter_map(|(local, limbs)| {
                            limbs.iter().any(|limb| *limb != 0).then_some(
                                successor_factors.get(local).copied().unwrap_or(u32::MAX),
                            )
                        })
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();
            let candidate_support = candidate_debug
                .chunks_exact(successor_factor_count * candidate_limb_count)
                .map(|row| {
                    row.chunks_exact(candidate_limb_count)
                        .enumerate()
                        .filter_map(|(local, limbs)| {
                            limbs.iter().any(|limb| *limb != 0).then_some(
                                successor_factors.get(local).copied().unwrap_or(u32::MAX),
                            )
                        })
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();
            let mut mounted_generator_targets = vec![u32::MAX; generators.saturating_mul(factors)];
            action
                .native_generator_targets
                .read(&mut mounted_generator_targets)?;
            let active_generator_images = (0..generators)
                .map(|generator| {
                    source_active_factors
                        .iter()
                        .map(|source| {
                            (
                                *source,
                                generator_targets[generator * factors + *source as usize],
                                mounted_generator_targets[generator * factors + *source as usize],
                            )
                        })
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();
            eprintln!(
                "generated-port-pre-junction active-generator-images(host,mounted)={active_generator_images:?} transported-support={transported_support:?} candidate-support={candidate_support:?}"
            );
        }
        // The candidate rows are local incidences.  Index only their addressed target states and
        // retain each exact target fibre; row equality and projective scale are receiver shadows
        // and cannot found recurrence.
        let mut index_targets = ptr::null_mut();
        driver(
            unsafe {
                cuModuleGetFunction(
                    &mut index_targets,
                    self.card.module,
                    c"index_membrane_generated_port_target_site_fibres".as_ptr(),
                )
            },
            "cuModuleGetFunction(index_membrane_generated_port_target_sites)",
        )?;
        let mut candidate_to_target_pointer = candidate_to_target.pointer;
        let mut target_states_pointer = target_states.pointer;
        let mut target_member_offsets_pointer = target_member_offsets.pointer;
        let mut target_members_pointer = target_members.pointer;
        let mut target_cursors_pointer = target_cursors.pointer;
        let mut target_count_pointer = target_count.pointer;
        let mut index_arguments: [*mut c_void; 9] = [
            &mut candidate_state_present_pointer as *mut u64 as *mut c_void,
            &mut candidate_states_pointer as *mut u64 as *mut c_void,
            &mut candidate_to_target_pointer as *mut u64 as *mut c_void,
            &mut target_states_pointer as *mut u64 as *mut c_void,
            &mut target_member_offsets_pointer as *mut u64 as *mut c_void,
            &mut target_members_pointer as *mut u64 as *mut c_void,
            &mut target_cursors_pointer as *mut u64 as *mut c_void,
            &mut target_count_pointer as *mut u64 as *mut c_void,
            &mut candidate_count_wire as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    index_targets,
                    1,
                    1,
                    1,
                    1,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    index_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(index_membrane_generated_port_target_sites)",
        )?;
        driver(
            unsafe { cuCtxSynchronize() },
            "cuCtxSynchronize(generated-port target-site extent)",
        )?;
        let mut target_count_host = [0_u32; 1];
        target_count.read(&mut target_count_host)?;
        let target_context_population = target_count_host[0] as usize;
        if target_context_population == 0 || target_context_population > candidate_count {
            return Err(CudaRefineError::GeneratedPortReceiverRadical {
                occurrence_population: candidate_count,
            });
        }
        let compact_target_population = target_context_population
            .checked_mul(successor_factor_count)
            .and_then(|extent| extent.checked_mul(target_limb_count))
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let compact_target_currents = Buffer::alloc(
            compact_target_population
                .checked_mul(std::mem::size_of::<u32>())
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        )?;
        let target_weights = Buffer::alloc(
            target_context_population
                .checked_mul(std::mem::size_of::<u32>())
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        )?;
        let mut aggregate_targets = ptr::null_mut();
        driver(
            unsafe {
                cuModuleGetFunction(
                    &mut aggregate_targets,
                    self.card.module,
                    c"aggregate_membrane_factor_current_candidates_by_target_state".as_ptr(),
                )
            },
            "cuModuleGetFunction(aggregate_membrane_factor_current_candidates_by_target_state)",
        )?;
        let mut target_current_pointer = compact_target_currents.pointer;
        let mut target_state_present_pointer = target_state_present.pointer;
        let mut target_weight_pointer = target_weights.pointer;
        let mut aggregation_obstruction_pointer = aggregation_obstruction.pointer;
        let mut target_context_count_wire = target_context_population as u32;
        let mut target_limb_count_wire = target_limb_count as u32;
        let mut aggregate_arguments: [*mut c_void; 11] = [
            &mut candidate_pointer as *mut u64 as *mut c_void,
            &mut target_member_offsets_pointer as *mut u64 as *mut c_void,
            &mut target_members_pointer as *mut u64 as *mut c_void,
            &mut target_current_pointer as *mut u64 as *mut c_void,
            &mut target_state_present_pointer as *mut u64 as *mut c_void,
            &mut target_weight_pointer as *mut u64 as *mut c_void,
            &mut aggregation_obstruction_pointer as *mut u64 as *mut c_void,
            &mut target_context_count_wire as *mut u32 as *mut c_void,
            &mut successor_factor_count_wire as *mut u32 as *mut c_void,
            &mut candidate_limb_count_wire as *mut u32 as *mut c_void,
            &mut target_limb_count_wire as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    aggregate_targets,
                    self.card
                        .grid_for((target_context_population * successor_factor_count) as u64)?,
                    1,
                    1,
                    self.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    aggregate_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(aggregate_membrane_factor_current_candidates_by_target_state)",
        )?;
        let conditioned_relational = if let Some((
            mut source_relational_state_present_pointer,
            mut source_relational_states_pointer,
            source_relational_state_count,
            mut transported_real_sign_pointer,
            mut transported_real_limbs_pointer,
            mut transported_imaginary_sign_pointer,
            mut transported_imaginary_limbs_pointer,
            source_limb_count,
            receipt,
            source_bound,
        )) = relational_continuation
        {
            let relational_target_bound = source_bound
                * maximal_restriction
                * &maximal_presented_current
                * BigUint::from(source_relational_state_count)
                * BigUint::from(candidate_count);
            let relational_target_limb_count = relational_target_bound.to_u32_digits().len().max(2);
            let target_relational_population = factors
                .checked_mul(target_context_population)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            let target_relational_octets = target_relational_population
                .checked_mul(relational_target_limb_count)
                .and_then(|extent| extent.checked_mul(std::mem::size_of::<u32>()))
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            let target_relational_state_present = Buffer::alloc(
                target_context_population
                    .checked_mul(std::mem::size_of::<u32>())
                    .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
            )?;
            target_relational_state_present.fill(
                0,
                target_context_population.saturating_mul(std::mem::size_of::<u32>()),
            )?;
            let target_relational_states = Buffer::alloc(
                target_context_population
                    .checked_mul(std::mem::size_of::<u32>())
                    .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
            )?;
            let target_real_sign = Buffer::alloc(target_relational_population)?;
            let target_real_limbs = Buffer::alloc(target_relational_octets)?;
            let target_imaginary_sign = Buffer::alloc(target_relational_population)?;
            let target_imaginary_limbs = Buffer::alloc(target_relational_octets)?;
            let product_scratch = Buffer::alloc(target_relational_octets)?;
            let returned_product_scratch = Buffer::alloc(target_relational_octets)?;
            let obstruction = Buffer::alloc(std::mem::size_of::<u32>())?;
            obstruction.fill(0, std::mem::size_of::<u32>())?;
            let mut join_relational = ptr::null_mut();
            driver(
                unsafe {
                    cuModuleGetFunction(
                        &mut join_relational,
                        self.card.module,
                        c"condition_and_aggregate_membrane_sparse_relational_current_by_target_state".as_ptr(),
                    )
                },
                "cuModuleGetFunction(condition_and_aggregate_membrane_sparse_relational_current_by_target_state)",
            )?;
            let mut target_relational_state_present_pointer =
                target_relational_state_present.pointer;
            let mut target_relational_states_pointer = target_relational_states.pointer;
            let mut target_real_sign_pointer = target_real_sign.pointer;
            let mut target_real_limbs_pointer = target_real_limbs.pointer;
            let mut target_imaginary_sign_pointer = target_imaginary_sign.pointer;
            let mut target_imaginary_limbs_pointer = target_imaginary_limbs.pointer;
            let mut product_scratch_pointer = product_scratch.pointer;
            let mut returned_product_scratch_pointer = returned_product_scratch.pointer;
            let mut relational_obstruction_pointer = obstruction.pointer;
            let mut relational_source_state_count_wire = source_relational_state_count as u32;
            let mut relational_selected_slot_count_wire = selected_slot_count as u32;
            let mut relational_source_limb_count_wire = source_limb_count as u32;
            let mut relational_target_limb_count_wire = relational_target_limb_count as u32;
            let mut join_relational_arguments: [*mut c_void; 36] = [
                &mut source_relational_state_present_pointer as *mut u64 as *mut c_void,
                &mut source_relational_states_pointer as *mut u64 as *mut c_void,
                &mut transported_real_sign_pointer as *mut u64 as *mut c_void,
                &mut transported_real_limbs_pointer as *mut u64 as *mut c_void,
                &mut transported_imaginary_sign_pointer as *mut u64 as *mut c_void,
                &mut transported_imaginary_limbs_pointer as *mut u64 as *mut c_void,
                &mut selected_faces_pointer as *mut u64 as *mut c_void,
                &mut selected_restrictions_pointer as *mut u64 as *mut c_void,
                &mut restriction_current_pointer as *mut u64 as *mut c_void,
                &mut presented_current_pointer as *mut u64 as *mut c_void,
                &mut boundary_states_pointer as *mut u64 as *mut c_void,
                &mut restriction_target_states_pointer as *mut u64 as *mut c_void,
                &mut candidate_selected_slots_pointer as *mut u64 as *mut c_void,
                &mut target_member_offsets_pointer as *mut u64 as *mut c_void,
                &mut target_members_pointer as *mut u64 as *mut c_void,
                &mut target_states_pointer as *mut u64 as *mut c_void,
                &mut target_relational_state_present_pointer as *mut u64 as *mut c_void,
                &mut target_relational_states_pointer as *mut u64 as *mut c_void,
                &mut target_real_sign_pointer as *mut u64 as *mut c_void,
                &mut target_real_limbs_pointer as *mut u64 as *mut c_void,
                &mut target_imaginary_sign_pointer as *mut u64 as *mut c_void,
                &mut target_imaginary_limbs_pointer as *mut u64 as *mut c_void,
                &mut product_scratch_pointer as *mut u64 as *mut c_void,
                &mut returned_product_scratch_pointer as *mut u64 as *mut c_void,
                &mut factor_count_wire as *mut u32 as *mut c_void,
                &mut generator_count_wire as *mut u32 as *mut c_void,
                &mut boundary_state_count_wire as *mut u32 as *mut c_void,
                &mut relational_source_state_count_wire as *mut u32 as *mut c_void,
                &mut relational_selected_slot_count_wire as *mut u32 as *mut c_void,
                &mut target_context_count_wire as *mut u32 as *mut c_void,
                &mut relational_source_limb_count_wire as *mut u32 as *mut c_void,
                &mut restriction_limb_count_wire as *mut u32 as *mut c_void,
                &mut presented_limb_count_wire as *mut u32 as *mut c_void,
                &mut presented_current_present_wire as *mut u32 as *mut c_void,
                &mut relational_target_limb_count_wire as *mut u32 as *mut c_void,
                &mut relational_obstruction_pointer as *mut u64 as *mut c_void,
            ];
            driver(
                unsafe {
                    cuLaunchKernel(
                        join_relational,
                        self.card.grid_for(target_relational_population as u64)?,
                        1,
                        1,
                        self.card.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        join_relational_arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(condition_and_aggregate_membrane_sparse_relational_current_by_target_state)",
            )?;
            Some((
                target_relational_state_present,
                target_relational_states,
                target_context_population,
                target_real_sign,
                target_real_limbs,
                target_imaginary_sign,
                target_imaginary_limbs,
                obstruction,
                receipt,
                relational_target_limb_count,
                relational_target_bound,
            ))
        } else {
            None
        };
        let relational_continuation_launched = conditioned_relational.is_some();
        if trace_configuration().holonics_phase_trace || trace_configuration().holonics_uar2_trace {
            eprintln!(
                "generated-port-continuation launched candidates={} relational={}",
                candidate_count, relational_continuation_launched,
            );
        }
        driver(
            unsafe { cuCtxSynchronize() },
            "cuCtxSynchronize(generated-port current continuation)",
        )?;
        self.card.launches = self
            .card
            .launches
            .checked_add(6 + u64::from(relational_continuation_launched))
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;

        let mut aggregation_obstruction_host = [0_u32; 1];
        aggregation_obstruction.read(&mut aggregation_obstruction_host)?;
        if aggregation_obstruction_host[0] != 0 {
            if trace_configuration().holonics_phase_trace
                || trace_configuration().holonics_uar2_trace
            {
                eprintln!(
                    "generated-port-target-junction-obstruction code={}",
                    aggregation_obstruction_host[0]
                );
            }
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }

        if let Some((
            state_present,
            _,
            state_count,
            real_sign,
            _,
            imaginary_sign,
            _,
            obstruction,
            ..,
        )) = conditioned_relational.as_ref()
        {
            let mut obstruction_host = [0_u32; 1];
            let mut state_present_host = vec![0_u32; *state_count];
            let mut real_sign_host = vec![0_u8; factors.saturating_mul(*state_count)];
            let mut imaginary_sign_host = vec![0_u8; factors.saturating_mul(*state_count)];
            obstruction.read(&mut obstruction_host)?;
            state_present.read(&mut state_present_host)?;
            real_sign.read(&mut real_sign_host)?;
            imaginary_sign.read(&mut imaginary_sign_host)?;
            let nonzero = real_sign_host
                .iter()
                .chain(&imaginary_sign_host)
                .any(|sign| *sign != 0);
            let present = state_present_host.iter().any(|present| *present != 0);
            if obstruction_host[0] != 0 || !present || !nonzero {
                if trace_configuration().holonics_phase_trace
                    || trace_configuration().holonics_uar2_trace
                {
                    eprintln!(
                        "relational-continuation-obstruction code={} present={} nonzero={}",
                        obstruction_host[0], present, nonzero
                    );
                }
                return Err(CudaRefineError::MembraneInteriorWordShape);
            }
        }

        // Reconstruct the complete selected slot testimony after the resident successor has
        // already been founded.  The apparatus-neutral ecology is evaluated only in an explicitly
        // requested one-time conformance pass; production still returns the exact resident passage
        // and validates its own boundary maps, but never executes a CPU successor as a fallback.
        let mut restriction_host =
            vec![
                0_u32;
                restriction_count
                    .checked_mul(factors)
                    .and_then(|extent| extent.checked_mul(restriction_limb_count))
                    .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?
            ];
        restriction_current.read(&mut restriction_host)?;
        let mut restriction_target_states_host = vec![u32::MAX; restriction_count];
        restriction_target_states.read(&mut restriction_target_states_host)?;
        let mut slots = Vec::with_capacity(selected_slot_count);
        for (&face, &restriction) in selected_faces_host.iter().zip(&selected_restrictions_host) {
            let local_face_population = (port_population as u32)
                .checked_mul(generator_count)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            let source_state_coordinate = face / local_face_population;
            let local_face = face % local_face_population;
            let port = local_face / generator_count;
            let generator = local_face % generator_count;
            if port as usize >= port_population
                || source_state_coordinate as usize >= boundary_state_count
                || restriction as usize >= restriction_count
                || restriction as usize / boundary_state_count != port as usize
                || restriction as usize % boundary_state_count != source_state_coordinate as usize
                || restriction_target_states_host[restriction as usize] == u32::MAX
            {
                return Err(CudaRefineError::MembraneInteriorWordShape);
            }
            let mut factor_current = Vec::new();
            for factor in 0..factors {
                let begin = ((restriction as usize * factors) + factor) * restriction_limb_count;
                let coefficient =
                    BigUint::new(restriction_host[begin..begin + restriction_limb_count].to_vec());
                if !coefficient.is_zero() {
                    factor_current.push((factor as u32, coefficient));
                }
            }
            if factor_current.is_empty() {
                return Err(CudaRefineError::MembraneInteriorWordShape);
            }
            slots.push(AddressedGeneratedPortSlot {
                port,
                generator,
                source_boundary_state: boundary_states[source_state_coordinate as usize],
                boundary_state: restriction_target_states_host[restriction as usize],
                restriction: factor_current,
            });
        }
        let reference_passage = reference_ecology_compared
            .then(|| {
                AddressedGeneratedPortJunctionPassage::derive_with_presented_current(
                    self.factors,
                    port_population as u32,
                    generator_targets.to_vec(),
                    source_contexts.to_vec(),
                    presented_current.map(<[(u32, BigUint)]>::to_vec),
                    slots.clone(),
                )
            })
            .transpose()
            .map_err(|error| {
                if trace_configuration().holonics_phase_trace
                    || trace_configuration().holonics_uar2_trace
                {
                    eprintln!("generated-port-reference-ecology-obstruction={error:?}");
                }
                CudaRefineError::MembraneInteriorWordShape
            })?;
        if trace_configuration().holonics_phase_trace || trace_configuration().holonics_uar2_trace {
            eprintln!(
                "generated-port-continuation synchronized targets={} candidates={}",
                target_context_population, candidate_count,
            );
        }
        if let Some(reference) = &reference_passage {
            if target_context_population != reference.target.len() {
                return Err(CudaRefineError::GeneratedPortEcologyMismatch {
                    expected_target_sections: reference.target.len(),
                    returned_target_sections: target_context_population,
                });
            }
            if reference.receiver_radical() {
                return Err(CudaRefineError::GeneratedPortReceiverRadical {
                    occurrence_population: reference.occurrences.len(),
                });
            }
        } else if target_context_population == 0 {
            return Err(CudaRefineError::GeneratedPortReceiverRadical {
                occurrence_population: candidate_count,
            });
        }
        if target_context_population > candidate_count {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let target_current_population = target_context_population
            .checked_mul(factors)
            .and_then(|extent| extent.checked_mul(target_limb_count))
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let target_currents = Buffer::alloc(
            target_current_population
                .checked_mul(std::mem::size_of::<u32>())
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        )?;
        let mut expand_compact = ptr::null_mut();
        driver(
            unsafe {
                cuModuleGetFunction(
                    &mut expand_compact,
                    self.card.module,
                    c"expand_membrane_compact_factor_current_sections".as_ptr(),
                )
            },
            "cuModuleGetFunction(expand_membrane_compact_factor_current_sections)",
        )?;
        let mut compact_target_current_pointer = compact_target_currents.pointer;
        let mut native_target_current_pointer = target_currents.pointer;
        let mut target_context_count_wire = target_context_population as u32;
        let mut expand_arguments: [*mut c_void; 7] = [
            &mut compact_target_current_pointer as *mut u64 as *mut c_void,
            &mut successor_factors_pointer as *mut u64 as *mut c_void,
            &mut native_target_current_pointer as *mut u64 as *mut c_void,
            &mut target_context_count_wire as *mut u32 as *mut c_void,
            &mut successor_factor_count_wire as *mut u32 as *mut c_void,
            &mut factor_count_wire as *mut u32 as *mut c_void,
            &mut target_limb_count_wire as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    expand_compact,
                    self.card.grid_for(target_context_population as u64)?,
                    1,
                    1,
                    self.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    expand_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(expand_membrane_compact_factor_current_sections)",
        )?;
        driver(
            unsafe { cuCtxSynchronize() },
            "cuCtxSynchronize(expanded generated-port current)",
        )?;
        let mut target_current_host =
            vec![0_u32; target_context_population * factors * target_limb_count];
        let mut target_weight_host =
            vec![0_u32; target_context_population * target_weight_limb_count];
        let mut target_state_present_host = vec![0_u8; candidate_count];
        let mut target_states_host = vec![0_u32; candidate_count];
        let mut candidate_to_target_host = vec![u32::MAX; candidate_count];
        let mut candidate_current_host = vec![0_u32; candidate_population];
        target_currents.read(&mut target_current_host)?;
        target_weights.read(&mut target_weight_host)?;
        target_state_present.read(&mut target_state_present_host)?;
        target_states.read(&mut target_states_host)?;
        target_state_present_host.truncate(target_context_population);
        target_states_host.truncate(target_context_population);
        candidate_to_target.read(&mut candidate_to_target_host)?;
        candidates.read(&mut candidate_current_host)?;
        if candidate_to_target_host
            .iter()
            .any(|target| *target != u32::MAX && *target as usize >= target_context_population)
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let mut returned_contexts = Vec::with_capacity(target_context_population);
        for target in 0..target_context_population {
            let weight_begin = target * target_weight_limb_count;
            let quadratic_weight = BigUint::new(
                target_weight_host[weight_begin..weight_begin + target_weight_limb_count].to_vec(),
            );
            let mut factor_current = Vec::new();
            for factor in 0..factors {
                let begin = (target * factors + factor) * target_limb_count;
                let coefficient =
                    BigUint::new(target_current_host[begin..begin + target_limb_count].to_vec());
                if !coefficient.is_zero() {
                    factor_current.push((factor as u32, coefficient));
                }
            }
            if quadratic_weight.is_zero() || factor_current.is_empty() {
                return Err(CudaRefineError::MembraneInteriorWordShape);
            }
            returned_contexts.push(AddressedCurrentSection {
                boundary_state: (target_state_present_host[target] != 0)
                    .then_some(target_states_host[target]),
                quadratic_weight,
                factor_current,
            });
        }
        let occurrences = candidate_to_target_host
            .iter()
            .copied()
            .enumerate()
            .map(
                |(candidate, target)| AddressedGeneratedPortJunctionOccurrence {
                    source_section: candidate_source_contexts_host[candidate],
                    selected_slot: candidate_selected_slots_host[candidate],
                    target_section: (target != u32::MAX).then_some(target),
                },
            )
            .collect::<Vec<_>>();
        let mut local_currents = Vec::new();
        for (candidate, target_section) in candidate_to_target_host.iter().copied().enumerate() {
            let mut factor_current = Vec::new();
            for (local_factor, factor) in successor_factors.iter().copied().enumerate() {
                let begin =
                    (candidate * successor_factor_count + local_factor) * candidate_limb_count;
                let coefficient = BigUint::new(
                    candidate_current_host[begin..begin + candidate_limb_count].to_vec(),
                );
                if !coefficient.is_zero() {
                    factor_current.push((factor, coefficient));
                }
            }
            if target_section == u32::MAX {
                if !factor_current.is_empty() {
                    return Err(CudaRefineError::MembraneInteriorWordShape);
                }
                continue;
            }
            if factor_current.is_empty() {
                return Err(CudaRefineError::MembraneInteriorWordShape);
            }
            local_currents.push(ResidentGeneratedPortLocalCurrent {
                source_section: candidate_source_contexts_host[candidate],
                selected_slot: candidate_selected_slots_host[candidate],
                target_section,
                factor_current,
            });
        }
        let passage = AddressedGeneratedPortJunctionPassage::found_with_presented_current(
            self.factors,
            port_population as u32,
            generator_targets.to_vec(),
            source_contexts.to_vec(),
            returned_contexts.clone(),
            presented_current.map(<[(u32, BigUint)]>::to_vec),
            slots,
            occurrences,
        )
        .map_err(|error| {
            if trace_configuration().holonics_phase_trace {
                eprintln!("generated-port-continuation passage-obstruction={error:?}");
            }
            CudaRefineError::MembraneInteriorWordShape
        })?;
        if reference_passage
            .as_ref()
            .is_some_and(|reference| &passage != reference)
        {
            return Err(CudaRefineError::GeneratedPortEcologyContentMismatch);
        }
        let target_generation = source_address
            .generation
            .checked_add(1)
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        self.factored_receiver_history
            .as_mut()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?
            .current = Some(ResidentFactoredCurrentState {
            generation: target_generation,
            context_count: target_context_population as u32,
            current_limb_count: target_limb_count as u32,
            weight_limb_count: target_weight_limb_count as u32,
            maximal_current: returned_contexts
                .iter()
                .flat_map(|context| &context.factor_current)
                .map(|(_, coefficient)| coefficient)
                .max()
                .cloned()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?,
            maximal_weight: returned_contexts
                .iter()
                .map(|context| &context.quadratic_weight)
                .max()
                .cloned()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?,
            active_factors: returned_contexts
                .iter()
                .flat_map(|context| context.factor_current.iter().map(|(factor, _)| *factor))
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect(),
            boundary_state_present: target_state_present,
            boundary_states: target_states,
            current_limbs: target_currents,
            weight_limbs: target_weights,
        });
        let target_address = self.resident_current_address()?;
        if let Some((
            relational_state_present,
            relational_states,
            relational_state_count,
            factor_real_sign,
            factor_real_limbs,
            factor_imaginary_sign,
            factor_imaginary_limbs,
            _,
            mut receipt,
            factor_limb_count,
            exact_returned_factor_bound,
        )) = conditioned_relational
        {
            let returned_factor_bound = exact_returned_factor_bound;
            let mut relational_state_present_host = vec![0_u32; relational_state_count];
            let mut relational_states_host = vec![0_u32; relational_state_count];
            relational_state_present.read(&mut relational_state_present_host)?;
            relational_states.read(&mut relational_states_host)?;
            let present_states = relational_states_host
                .iter()
                .copied()
                .zip(&relational_state_present_host)
                .filter_map(|(state, present)| (*present != 0).then_some(state))
                .collect::<Vec<_>>();
            if present_states.is_empty() || present_states.contains(&u32::MAX) {
                return Err(CudaRefineError::MembraneInteriorWordShape);
            }
            let target_state = if present_states.len() == 1 {
                present_states[0]
            } else {
                u32::MAX
            };
            let addressed_state_identity_sha256 = serde_json::to_vec(&(
                "holonic-engine.resident-sparse-relational-addressed-states.v2",
                &relational_states_host,
                &relational_state_present_host,
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
                "holonic-engine.resident-factored-current-address.v1",
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
                "holonic-engine.resident-sparse-relational-current.v2",
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
            receipt.source_current_identity_sha256 = source_current_identity_sha256;
            receipt.returned_current_identity_sha256 = returned_current_identity_sha256;
            receipt.addressed_state_identity_sha256 = addressed_state_identity_sha256;
            receipt.addressed_state_population = relational_state_count;
            receipt.present_state_population = present_states.len();
            receipt.root_state = target_state;
            receipt.returned_factor_bound = returned_factor_bound.clone();
            receipt.factor_limb_count = factor_limb_count;
            receipt.addressed_target_receiver_joined = true;
            receipt.launches = 1;
            receipt.device_dependency_edges = 0;
            receipt.synchronizations = 1;
            receipt.successor_host_ingress_octets = 0;
            receipt.successor_host_egress_octets = u64::try_from(
                std::mem::size_of::<u32>()
                    .checked_add(relational_state_count)
                    .and_then(|octets| {
                        octets.checked_add(
                            factors
                                .saturating_mul(relational_state_count)
                                .saturating_mul(2),
                        )
                    })
                    .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
            )
            .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            receipt.intermediate_host_egress_octets = 0;
            receipt.resident_working_octets = (factors
                .checked_mul(relational_state_count)
                .and_then(|population| population.checked_mul(factor_limb_count))
                .and_then(|words| words.checked_mul(std::mem::size_of::<u32>()))
                .and_then(|octets| octets.checked_mul(2))
                .and_then(|octets| {
                    octets.checked_add(
                        factors
                            .saturating_mul(relational_state_count)
                            .saturating_mul(2),
                    )
                })
                .and_then(|octets| octets.checked_add(relational_state_count))
                .and_then(|octets| {
                    octets.checked_add(
                        relational_state_count.saturating_mul(std::mem::size_of::<u32>()),
                    )
                })
                .and_then(|octets| octets.checked_add(std::mem::size_of::<u32>()))
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?)
                as u64;
            // The historical bounded face is deliberately unavailable after the first exact
            // arbitrary-limb return.  Keep one inert allocation only because the legacy sparse-
            // pair diagnostic still owns that apparatus type; its aperture rejects this state.
            let factor_real = Buffer::alloc(1)?;
            let factor_imaginary = Buffer::alloc(1)?;
            self.sparse_relational_current = Some(ResidentSparseRelationalCurrentState {
                receipt,
                state_present: relational_state_present,
                states: relational_states,
                state_count: relational_state_count,
                bounded_i64_face_valid: false,
                factor_real,
                factor_imaginary,
                factor_real_sign,
                factor_real_limbs,
                factor_imaginary_sign,
                factor_imaginary_limbs,
                factor_limb_count,
                returned_factor_bound,
            });
        }
        let host_egress_octets = [
            std::mem::size_of_val(&selected_count_host[..]),
            std::mem::size_of_val(&selected_faces_host[..]),
            std::mem::size_of_val(&selected_restrictions_host[..]),
            std::mem::size_of_val(&restriction_host[..]),
            std::mem::size_of_val(&restriction_target_states_host[..]),
            std::mem::size_of_val(&target_current_host[..]),
            std::mem::size_of_val(&target_weight_host[..]),
            std::mem::size_of_val(&candidate_to_target_host[..]),
            std::mem::size_of_val(&candidate_current_host[..]),
        ]
        .into_iter()
        .try_fold(0_u64, |sum, octets| {
            sum.checked_add(u64::try_from(octets).ok()?)
        })
        .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let intermediate_joining_address_egress_octets =
            std::mem::size_of_val(&selected_count_host)
                .checked_add(std::mem::size_of_val(&selected_faces_host[..]))
                .and_then(|octets| {
                    octets.checked_add(std::mem::size_of_val(&selected_restrictions_host[..]))
                })
                .and_then(|octets| u64::try_from(octets).ok())
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let intermediate_apparatus_shape_egress_octets = std::mem::size_of::<u32>() as u64;
        let intermediate_host_egress_octets = intermediate_joining_address_egress_octets
            .checked_add(intermediate_apparatus_shape_egress_octets)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let terminal_semantic_egress_octets = host_egress_octets
            .checked_sub(intermediate_joining_address_egress_octets)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let returned = ResidentGeneratedPortCurrentPassageReturn {
            passage,
            local_currents,
            source_address: source_address.clone(),
            target_address,
            device: self.card.device_name.clone(),
            context_identity: self.card.context as usize,
            launches: 6 + u64::from(relational_continuation_launched),
            synchronizations: 4,
            host_ingress_octets: presented_current_ingress_octets,
            host_egress_octets,
            intermediate_host_egress_octets,
            intermediate_joining_address_egress_octets,
            intermediate_apparatus_shape_egress_octets,
            intermediate_semantic_egress_octets: 0,
            terminal_semantic_egress_octets,
            reference_ecology_compared,
            source_current_mounted_this_pass,
            invariant_transport_reuploaded: false,
            cpu_semantic_replay_after_device: false,
        };
        Ok(ResidentCompletedTargetObservationAperture {
            returned,
            selected_faces,
            candidate_selected_slots,
            candidate_to_target,
            selected_slot_count,
            candidate_count,
            local_face_population: port_population
                .checked_mul(generators)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        })
    }
}
