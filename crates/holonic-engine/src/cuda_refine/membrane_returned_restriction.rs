use super::*;

impl ResidentMembraneInteriorWord {
    // Loop coordinates are consumed by CUDA through raw pointers retained in one argument array.
    #[allow(unused_assignments)]
    fn stage_resident_state_sparse_quadratic_returned_restriction(
        &mut self,
        situated_front_pointer: u64,
        face_population: usize,
    ) -> Result<(), CudaRefineError> {
        let phase_trace = trace_configuration().holonics_phase_trace;
        driver(
            unsafe { cuCtxSetCurrent(self.card.context) },
            "cuCtxSetCurrent",
        )?;
        let (
            pair_population,
            factor_population,
            source_state_population,
            generator_population,
            port_population,
            source_limb_count,
            maximal_source,
            pair_factors_pointer,
            restriction_limb_count,
            maximal_restriction,
            restrictions_pointer,
            restriction_present_pointer,
            restriction_target_states_pointer,
            source_pointer,
            source_state_ids_pointer,
            native_generator_targets_pointer,
            maximal_generator_preimage,
            obstruction_pointer,
        ) = {
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
            let native = transport
                .sparse_native_boundary
                .as_ref()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let action = self
                .quadratic_action
                .as_ref()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let maximal_generator_preimage = action
                .generator_targets
                .chunks_exact(source.factor_population as usize)
                .map(|generator| {
                    let mut preimages = vec![0_usize; source.factor_population as usize];
                    for target in generator {
                        preimages[*target as usize] += 1;
                    }
                    preimages.into_iter().max().unwrap_or(0)
                })
                .max()
                .filter(|extent| *extent != 0)
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            if !transport.sparse_pair_completion
                || transport.sparse_conditioned.is_some()
                || native.face_population as usize != face_population
                || source.pair_population != transport.transported_row_population
                || source.factor_population != transport.factor_population
                || native.port_population == 0
                || native.restrictions.pointer == 0
                || native.restriction_present.pointer == 0
                || native.restriction_target_states.pointer == 0
            {
                return Err(CudaRefineError::MembraneInteriorWordShape);
            }
            (
                source.pair_population as usize,
                source.factor_population as usize,
                source.state_population as usize,
                source.action.generator_population as usize,
                native.port_population as usize,
                transport.numerator_limb_count as usize,
                transport
                    .maximal_numerator
                    .to_biguint()
                    .ok_or(CudaRefineError::MembraneInteriorWordShape)?,
                source.pair_factors.pointer,
                native.restriction_limb_count as usize,
                native.maximal_restriction.clone(),
                native.restrictions.pointer,
                native.restriction_present.pointer,
                native.restriction_target_states.pointer,
                transport.limbs.pointer,
                source.state_ids.pointer,
                action.native_generator_targets.pointer,
                maximal_generator_preimage,
                transport.overflow.pointer,
            )
        };
        if pair_population == 0
            || factor_population == 0
            || source_state_population == 0
            || generator_population == 0
            || port_population == 0
            || source_limb_count == 0
            || restriction_limb_count == 0
            || face_population
                != source_state_population
                    .checked_mul(port_population)
                    .and_then(|held| held.checked_mul(generator_population))
                    .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        if phase_trace {
            eprintln!(
                "uar2-returned-restriction-enter faces={} source-states={} ports={} generators={} pairs={} factors={} source-limbs={} restriction-limbs={}",
                face_population,
                source_state_population,
                port_population,
                generator_population,
                pair_population,
                factor_population,
                source_limb_count,
                restriction_limb_count,
            );
        }
        let maximal_conditioned = &maximal_source
            * &maximal_restriction
            * &maximal_restriction
            * BigUint::from(face_population);
        let conditioned_limb_count = maximal_conditioned
            .to_u32_digits()
            .len()
            .max(source_limb_count);
        if conditioned_limb_count > u32::MAX as usize {
            return Err(CudaRefineError::MembraneInteriorCurrentOutsideApparatus);
        }
        let face_target_blocks = Buffer::alloc(
            face_population
                .checked_mul(std::mem::size_of::<u32>())
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        )?;
        let state_ids = Buffer::alloc(
            face_population
                .checked_mul(std::mem::size_of::<u32>())
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        )?;
        let state_population_device = Buffer::of(&[0_u32])?;
        let returned_port_selection = Buffer::of(&[0_u32, 0_u32])?;

        let mut situated_front = situated_front_pointer;
        let mut restriction_present = restriction_present_pointer;
        let mut restriction_target_states = restriction_target_states_pointer;
        let mut face_target_blocks_pointer = face_target_blocks.pointer;
        let mut state_ids_pointer = state_ids.pointer;
        let mut state_population_pointer = state_population_device.pointer;
        let mut face_count_wire = face_population as u32;
        let mut index_arguments: [*mut c_void; 7] = [
            &mut situated_front as *mut u64 as *mut c_void,
            &mut restriction_present as *mut u64 as *mut c_void,
            &mut restriction_target_states as *mut u64 as *mut c_void,
            &mut face_target_blocks_pointer as *mut u64 as *mut c_void,
            &mut state_ids_pointer as *mut u64 as *mut c_void,
            &mut state_population_pointer as *mut u64 as *mut c_void,
            &mut face_count_wire as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card
                        .membrane_sparse_quadratic_state_returned_face_index,
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
            "cuLaunchKernel(index_membrane_sparse_quadratic_returned_state_faces)",
        )?;
        driver(
            unsafe { cuCtxSynchronize() },
            "cuCtxSynchronize(state-addressed target-state extent)",
        )?;
        let mut state_population_host = [0_u32; 1];
        state_population_device.read(&mut state_population_host)?;
        let target_state_population = state_population_host[0] as usize;
        if phase_trace {
            eprintln!(
                "uar2-returned-restriction-indexed target-states={} faces={}",
                target_state_population, face_population,
            );
        }
        if target_state_population == 0 || target_state_population > face_population {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let mut state_ids_host = vec![0_u32; target_state_population];
        state_ids.read(&mut state_ids_host)?;
        if state_ids_host
            .iter()
            .copied()
            .collect::<BTreeSet<_>>()
            .len()
            != target_state_population
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let target_block_entries = target_state_population
            .checked_mul(pair_population)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let conditioned_octets = target_block_entries
            .checked_mul(conditioned_limb_count)
            .and_then(|words| words.checked_mul(std::mem::size_of::<u32>()))
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        if phase_trace {
            eprintln!(
                "uar2-returned-restriction-quadratic target-blocks={} limbs={} octets-each={}",
                target_block_entries, conditioned_limb_count, conditioned_octets,
            );
        }
        let coefficients = Buffer::alloc(conditioned_octets)?;
        coefficients.fill(0, conditioned_octets)?;

        // The target-state direct sum is continuing morphology.  Multiplication scratch is only
        // an apparatus witness for one exact coefficient and must not acquire the same complete
        // rectangular residency.  Request one complete target-state pair fibre and let the live
        // CUDA aperture narrow it if necessary; every global `(target state, pair)` address is
        // still visited once, and no semantic population controls the apparatus window.
        let requested_window_population = pair_population
            .min(target_block_entries)
            .min(u32::MAX as usize);
        let arithmetic_workspace_octets_for = |population: usize| {
            population
                .checked_mul(conditioned_limb_count)
                .and_then(|words| words.checked_mul(std::mem::size_of::<u32>()))
                .and_then(|one_scratch| one_scratch.checked_mul(2))
        };
        let (condition_window_population, arithmetic_workspace) = Buffer::widest_repeated_aperture(
            requested_window_population,
            arithmetic_workspace_octets_for,
        )?;
        let one_scratch_octets = condition_window_population
            .checked_mul(conditioned_limb_count)
            .and_then(|words| words.checked_mul(std::mem::size_of::<u32>()))
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let arithmetic_workspace_octets =
            arithmetic_workspace_octets_for(condition_window_population)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let first_scratch_pointer = arithmetic_workspace.pointer;
        let second_scratch_pointer = arithmetic_workspace
            .pointer
            .checked_add(one_scratch_octets as u64)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;

        let mut pair_factors = pair_factors_pointer;
        let mut restrictions = restrictions_pointer;
        let mut source = source_pointer;
        let mut coefficients_pointer = coefficients.pointer;
        let mut scratch_pointer = first_scratch_pointer;
        let mut second_scratch_pointer = second_scratch_pointer;
        let mut obstruction = obstruction_pointer;
        // These values are read by CUDA through pointers retained in `condition_arguments`.
        #[allow(unused_assignments)]
        let mut work_offset_wire = 0_u64;
        #[allow(unused_assignments)]
        let mut window_count_wire = 0_u32;
        let mut pair_count_wire = pair_population as u32;
        let mut factor_count_wire = factor_population as u32;
        let mut source_state_count_wire = source_state_population as u32;
        let mut port_count_wire = port_population as u32;
        let mut generator_count_wire = generator_population as u32;
        let mut source_limb_count_wire = source_limb_count as u32;
        let mut restriction_limb_count_wire = restriction_limb_count as u32;
        let mut conditioned_limb_count_wire = conditioned_limb_count as u32;
        let mut target_state_count_wire = target_state_population as u32;
        let mut condition_arguments: [*mut c_void; 22] = [
            &mut pair_factors as *mut u64 as *mut c_void,
            &mut restrictions as *mut u64 as *mut c_void,
            &mut source as *mut u64 as *mut c_void,
            &mut situated_front as *mut u64 as *mut c_void,
            &mut restriction_target_states as *mut u64 as *mut c_void,
            &mut face_target_blocks_pointer as *mut u64 as *mut c_void,
            &mut coefficients_pointer as *mut u64 as *mut c_void,
            &mut scratch_pointer as *mut u64 as *mut c_void,
            &mut second_scratch_pointer as *mut u64 as *mut c_void,
            &mut work_offset_wire as *mut u64 as *mut c_void,
            &mut window_count_wire as *mut u32 as *mut c_void,
            &mut pair_count_wire as *mut u32 as *mut c_void,
            &mut factor_count_wire as *mut u32 as *mut c_void,
            &mut source_state_count_wire as *mut u32 as *mut c_void,
            &mut port_count_wire as *mut u32 as *mut c_void,
            &mut generator_count_wire as *mut u32 as *mut c_void,
            &mut face_count_wire as *mut u32 as *mut c_void,
            &mut target_state_count_wire as *mut u32 as *mut c_void,
            &mut source_limb_count_wire as *mut u32 as *mut c_void,
            &mut restriction_limb_count_wire as *mut u32 as *mut c_void,
            &mut conditioned_limb_count_wire as *mut u32 as *mut c_void,
            &mut obstruction as *mut u64 as *mut c_void,
        ];
        let mut condition_launches = 0_u64;
        let mut work_offset = 0_usize;
        while work_offset < target_block_entries {
            let window_count = condition_window_population.min(target_block_entries - work_offset);
            work_offset_wire = work_offset as u64;
            window_count_wire = window_count as u32;
            driver(
                unsafe {
                    cuLaunchKernel(
                        self.card
                            .membrane_sparse_quadratic_state_returned_faces_condition,
                        self.card.grid_for(window_count as u64)?,
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
                "cuLaunchKernel(condition_membrane_sparse_quadratic_state_addressed_pairs_by_returned_faces_window)",
            )?;
            condition_launches = condition_launches
                .checked_add(1)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            work_offset = work_offset
                .checked_add(window_count)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        }
        if phase_trace {
            eprintln!(
                "uar2-returned-restriction-windowed entries={} window={} launches={} workspace-octets={}",
                target_block_entries,
                condition_window_population,
                condition_launches,
                arithmetic_workspace_octets,
            );
        }
        let relational_continuation = if let Some((
            mut relational_state_present,
            mut relational_states,
            relational_state_count,
            mut source_real_sign,
            mut source_real_limbs,
            mut source_imaginary_sign,
            mut source_imaginary_limbs,
            relational_source_limb_count,
            returned_factor_bound,
        )) =
            self.sparse_relational_current.as_ref().map(|current| {
                (
                    current.state_present.pointer,
                    current.states.pointer,
                    current.state_count,
                    current.factor_real_sign.pointer,
                    current.factor_real_limbs.pointer,
                    current.factor_imaginary_sign.pointer,
                    current.factor_imaginary_limbs.pointer,
                    current.factor_limb_count,
                    current.returned_factor_bound.clone(),
                )
            }) {
            let transported_bound =
                &returned_factor_bound * BigUint::from(maximal_generator_preimage);
            let transported_limb_count = transported_bound
                .to_u32_digits()
                .len()
                .max(relational_source_limb_count)
                .max(1)
                .saturating_add(1);
            let returned_bound =
                &transported_bound * &maximal_restriction * BigUint::from(face_population);
            let returned_limb_count = returned_bound
                .to_u32_digits()
                .len()
                .max(transported_limb_count)
                .max(1)
                .saturating_add(1);
            if transported_limb_count > u32::MAX as usize || returned_limb_count > u32::MAX as usize
            {
                return Err(CudaRefineError::MembraneInteriorCurrentOutsideApparatus);
            }
            let transported_population = relational_state_count
                .checked_mul(generator_population)
                .and_then(|extent| extent.checked_mul(factor_population))
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            let returned_population = target_state_population
                .checked_mul(factor_population)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            let transported_limb_octets = transported_population
                .checked_mul(transported_limb_count)
                .and_then(|words| words.checked_mul(std::mem::size_of::<u32>()))
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            let returned_limb_octets = returned_population
                .checked_mul(returned_limb_count)
                .and_then(|words| words.checked_mul(std::mem::size_of::<u32>()))
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            if phase_trace {
                eprintln!(
                    "uar2-returned-restriction-relational source-states={} transported={} returned={} transported-limbs={} returned-limbs={} transported-octets={} returned-octets={}",
                    relational_state_count,
                    transported_population,
                    returned_population,
                    transported_limb_count,
                    returned_limb_count,
                    transported_limb_octets,
                    returned_limb_octets,
                );
            }
            let transported_real_sign = Buffer::alloc(transported_population)?;
            let transported_real_limbs = Buffer::alloc(transported_limb_octets)?;
            let transported_imaginary_sign = Buffer::alloc(transported_population)?;
            let transported_imaginary_limbs = Buffer::alloc(transported_limb_octets)?;
            let target_state_present = Buffer::alloc(
                target_state_population
                    .checked_mul(std::mem::size_of::<u32>())
                    .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
            )?;
            target_state_present.fill(
                0,
                target_state_population.saturating_mul(std::mem::size_of::<u32>()),
            )?;
            let target_states = Buffer::of(&state_ids_host)?;
            let target_real_sign = Buffer::alloc(returned_population)?;
            let target_real_limbs = Buffer::alloc(returned_limb_octets)?;
            let target_imaginary_sign = Buffer::alloc(returned_population)?;
            let target_imaginary_limbs = Buffer::alloc(returned_limb_octets)?;
            let product_scratch = Buffer::alloc(returned_limb_octets)?;

            let mut transport_relational = ptr::null_mut();
            let mut condition_relational = ptr::null_mut();
            driver(
                unsafe {
                    cuModuleGetFunction(
                        &mut transport_relational,
                        self.card.module,
                        c"transport_membrane_sparse_relational_generator_limbs".as_ptr(),
                    )
                },
                "cuModuleGetFunction(transport_membrane_sparse_relational_generator_limbs)",
            )?;
            driver(
                unsafe {
                    cuModuleGetFunction(
                        &mut condition_relational,
                        self.card.module,
                        c"condition_membrane_sparse_relational_state_addressed_current_by_returned_faces".as_ptr(),
                    )
                },
                "cuModuleGetFunction(condition_membrane_sparse_relational_state_addressed_current_by_returned_faces)",
            )?;
            let mut generator_targets = native_generator_targets_pointer;
            let mut transported_real_sign_pointer = transported_real_sign.pointer;
            let mut transported_real_limbs_pointer = transported_real_limbs.pointer;
            let mut transported_imaginary_sign_pointer = transported_imaginary_sign.pointer;
            let mut transported_imaginary_limbs_pointer = transported_imaginary_limbs.pointer;
            let mut relational_state_count_wire = relational_state_count as u32;
            let mut relational_source_limb_count_wire = relational_source_limb_count as u32;
            let mut transported_limb_count_wire = transported_limb_count as u32;
            let mut relational_transport_arguments: [*mut c_void; 16] = [
                &mut generator_targets as *mut u64 as *mut c_void,
                &mut relational_state_present as *mut u64 as *mut c_void,
                &mut source_real_sign as *mut u64 as *mut c_void,
                &mut source_real_limbs as *mut u64 as *mut c_void,
                &mut source_imaginary_sign as *mut u64 as *mut c_void,
                &mut source_imaginary_limbs as *mut u64 as *mut c_void,
                &mut transported_real_sign_pointer as *mut u64 as *mut c_void,
                &mut transported_real_limbs_pointer as *mut u64 as *mut c_void,
                &mut transported_imaginary_sign_pointer as *mut u64 as *mut c_void,
                &mut transported_imaginary_limbs_pointer as *mut u64 as *mut c_void,
                &mut factor_count_wire as *mut u32 as *mut c_void,
                &mut generator_count_wire as *mut u32 as *mut c_void,
                &mut relational_state_count_wire as *mut u32 as *mut c_void,
                &mut relational_source_limb_count_wire as *mut u32 as *mut c_void,
                &mut transported_limb_count_wire as *mut u32 as *mut c_void,
                &mut obstruction as *mut u64 as *mut c_void,
            ];
            driver(
                unsafe {
                    cuLaunchKernel(
                        transport_relational,
                        self.card.grid_for(transported_population as u64)?,
                        1,
                        1,
                        self.card.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        relational_transport_arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(transport_membrane_sparse_relational_generator_limbs)",
            )?;

            let mut source_state_ids = source_state_ids_pointer;
            let mut restrictions = restrictions_pointer;
            let mut target_state_present_pointer = target_state_present.pointer;
            let mut target_real_sign_pointer = target_real_sign.pointer;
            let mut target_real_limbs_pointer = target_real_limbs.pointer;
            let mut target_imaginary_sign_pointer = target_imaginary_sign.pointer;
            let mut target_imaginary_limbs_pointer = target_imaginary_limbs.pointer;
            let mut product_scratch_pointer = product_scratch.pointer;
            let mut returned_limb_count_wire = returned_limb_count as u32;
            let mut relational_condition_arguments: [*mut c_void; 27] = [
                &mut source_state_ids as *mut u64 as *mut c_void,
                &mut relational_state_present as *mut u64 as *mut c_void,
                &mut relational_states as *mut u64 as *mut c_void,
                &mut transported_real_sign_pointer as *mut u64 as *mut c_void,
                &mut transported_real_limbs_pointer as *mut u64 as *mut c_void,
                &mut transported_imaginary_sign_pointer as *mut u64 as *mut c_void,
                &mut transported_imaginary_limbs_pointer as *mut u64 as *mut c_void,
                &mut restrictions as *mut u64 as *mut c_void,
                &mut situated_front as *mut u64 as *mut c_void,
                &mut face_target_blocks_pointer as *mut u64 as *mut c_void,
                &mut target_state_present_pointer as *mut u64 as *mut c_void,
                &mut target_real_sign_pointer as *mut u64 as *mut c_void,
                &mut target_real_limbs_pointer as *mut u64 as *mut c_void,
                &mut target_imaginary_sign_pointer as *mut u64 as *mut c_void,
                &mut target_imaginary_limbs_pointer as *mut u64 as *mut c_void,
                &mut product_scratch_pointer as *mut u64 as *mut c_void,
                &mut factor_count_wire as *mut u32 as *mut c_void,
                &mut source_state_count_wire as *mut u32 as *mut c_void,
                &mut port_count_wire as *mut u32 as *mut c_void,
                &mut generator_count_wire as *mut u32 as *mut c_void,
                &mut face_count_wire as *mut u32 as *mut c_void,
                &mut relational_state_count_wire as *mut u32 as *mut c_void,
                &mut target_state_count_wire as *mut u32 as *mut c_void,
                &mut transported_limb_count_wire as *mut u32 as *mut c_void,
                &mut restriction_limb_count_wire as *mut u32 as *mut c_void,
                &mut returned_limb_count_wire as *mut u32 as *mut c_void,
                &mut obstruction as *mut u64 as *mut c_void,
            ];
            driver(
                unsafe {
                    cuLaunchKernel(
                        condition_relational,
                        self.card.grid_for(returned_population as u64)?,
                        1,
                        1,
                        self.card.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        relational_condition_arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(condition_membrane_sparse_relational_state_addressed_current_by_returned_faces)",
            )?;
            let resident_octets = u64::try_from(
                target_state_population
                    .checked_mul(std::mem::size_of::<u32>() * 2)
                    .and_then(|octets| octets.checked_add(returned_population * 2))
                    .and_then(|held| held.checked_add(returned_limb_octets.saturating_mul(2)))
                    .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
            )
            .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            Some(ResidentSparseRelationalConditionedCurrent {
                state_present: target_state_present,
                states: target_states,
                state_ids_host: state_ids_host.clone(),
                state_count: target_state_population,
                factor_real_sign: target_real_sign,
                factor_real_limbs: target_real_limbs,
                factor_imaginary_sign: target_imaginary_sign,
                factor_imaginary_limbs: target_imaginary_limbs,
                factor_limb_count: returned_limb_count,
                returned_factor_bound: returned_bound,
                work_buffers: vec![
                    transported_real_sign,
                    transported_real_limbs,
                    transported_imaginary_sign,
                    transported_imaginary_limbs,
                    product_scratch,
                ],
                launches: 2,
                resident_octets,
            })
        } else {
            None
        };
        let relational_launches = relational_continuation
            .as_ref()
            .map_or(0, |held| held.launches);
        self.card.launches = self
            .card
            .launches
            .checked_add(
                1_u64
                    .saturating_add(condition_launches)
                    .saturating_add(relational_launches),
            )
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let resident_octets = u64::try_from(
            conditioned_octets
                .checked_add(arithmetic_workspace_octets)
                .and_then(|octets| {
                    octets.checked_add(
                        face_population
                            .checked_mul(std::mem::size_of::<u32>())?
                            .checked_mul(2)?,
                    )
                })
                .and_then(|octets| octets.checked_add(3 * std::mem::size_of::<u32>()))
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        )
        .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let transport = self
            .factored_receiver_history
            .as_mut()
            .and_then(|mount| mount.transported_image.as_mut())
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        transport.sparse_conditioned = Some(ResidentSparseQuadraticConditionedCurrent {
            state_population: target_state_population as u32,
            coefficient_state_capacity: target_state_population as u32,
            state_population_device,
            state_ids_host,
            state_ids,
            coefficient_limb_count: conditioned_limb_count as u32,
            maximal_coefficient: maximal_conditioned,
            coefficients,
            returned_port_selection,
            work_buffers: vec![face_target_blocks, arithmetic_workspace],
            relational_continuation,
            launches: 1_u64
                .saturating_add(condition_launches)
                .saturating_add(relational_launches),
            synchronizations: 1,
            apparatus_shape_host_egress_octets: std::mem::size_of::<u32>() as u64,
        });
        transport.resident_octets = transport
            .resident_octets
            .checked_add(resident_octets)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        if phase_trace {
            eprintln!(
                "uar2-returned-restriction-staged target-states={} resident-octets={}",
                target_state_population, resident_octets,
            );
        }
        Ok(())
    }

    /// factor restriction.  The old current remains owned until the terminal synchronization.
    pub(super) fn stage_resident_sparse_quadratic_returned_restriction(
        &mut self,
        situated_front_pointer: u64,
        port_population: usize,
    ) -> Result<(), CudaRefineError> {
        let native_state_addressed = self
            .factored_receiver_history
            .as_ref()
            .and_then(|mount| mount.transported_image.as_ref())
            .and_then(|transport| transport.sparse_native_boundary.as_ref())
            .is_some();
        if native_state_addressed {
            return self.stage_resident_state_sparse_quadratic_returned_restriction(
                situated_front_pointer,
                port_population,
            );
        }
        driver(
            unsafe { cuCtxSetCurrent(self.card.context) },
            "cuCtxSetCurrent",
        )?;
        let (
            pair_population,
            factor_population,
            source_limb_count,
            maximal_source,
            pair_factors_pointer,
            restriction_limb_count,
            maximal_restriction,
            restriction_pointer,
            source_pointer,
            addressed_face_condensation,
            generator_population,
        ) = {
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
            let (restriction_limb_count, maximal_restriction, restriction_pointer) =
                if let Some(native) = transport.sparse_native_boundary.as_ref() {
                    if native.face_population as usize != port_population
                        || native.restrictions.pointer == 0
                    {
                        return Err(CudaRefineError::MembraneInteriorWordShape);
                    }
                    (
                        native.restriction_limb_count as usize,
                        native.maximal_restriction.clone(),
                        native.restrictions.pointer,
                    )
                } else {
                    let conditioner = self
                        .addressed_factored_receiver_frame
                        .as_ref()
                        .and_then(|frame| frame.sparse_pair_boundary_conditioners.as_ref())
                        .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
                    if conditioner.port_population as usize != port_population
                        || conditioner.factor_population != source.factor_population
                        || conditioner.coefficients.pointer == 0
                    {
                        return Err(CudaRefineError::MembraneInteriorWordShape);
                    }
                    (
                        conditioner.coefficient_limb_count as usize,
                        conditioner.maximal_coefficient.clone(),
                        conditioner.coefficients.pointer,
                    )
                };
            if !transport.sparse_pair_completion
                || transport.sparse_conditioned.is_some()
                || source.pair_population != transport.transported_row_population
                || source.factor_population != transport.factor_population
                || source.pair_factors.pointer == 0
                || transport.limbs.pointer == 0
            {
                return Err(CudaRefineError::MembraneInteriorWordShape);
            }
            (
                source.pair_population as usize,
                source.factor_population as usize,
                transport.numerator_limb_count as usize,
                transport
                    .maximal_numerator
                    .to_biguint()
                    .ok_or(CudaRefineError::MembraneInteriorWordShape)?,
                source.pair_factors.pointer,
                restriction_limb_count,
                maximal_restriction,
                restriction_pointer,
                transport.limbs.pointer,
                transport.sparse_native_boundary.is_some(),
                source.action.generator_population as usize,
            )
        };
        if pair_population == 0
            || factor_population == 0
            || source_limb_count == 0
            || restriction_limb_count == 0
            || maximal_restriction.is_zero()
            || generator_population == 0
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let maximal_conditioned = &maximal_source
            * &maximal_restriction
            * &maximal_restriction
            * BigUint::from(if addressed_face_condensation {
                port_population
            } else {
                1
            });
        let conditioned_limb_count = maximal_conditioned
            .to_u32_digits()
            .len()
            .max(source_limb_count);
        if conditioned_limb_count > u32::MAX as usize {
            return Err(CudaRefineError::MembraneInteriorCurrentOutsideApparatus);
        }
        let conditioned_entries = pair_population
            .checked_mul(conditioned_limb_count)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let conditioned_octets = conditioned_entries
            .checked_mul(std::mem::size_of::<u32>())
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let conditioned = Buffer::alloc(conditioned_octets)?;
        let scratch = Buffer::alloc(conditioned_octets)?;
        let second_scratch = Buffer::alloc(conditioned_octets)?;
        let selection = Buffer::alloc(2 * std::mem::size_of::<u32>())?;
        conditioned.fill(0, conditioned_octets)?;
        scratch.fill(0, conditioned_octets)?;
        second_scratch.fill(0, conditioned_octets)?;
        selection.fill(0, 2 * std::mem::size_of::<u32>())?;

        let mut situated_front = situated_front_pointer;
        let mut selection_pointer = selection.pointer;
        let mut port_count_wire = port_population as u32;
        let mut resolve_arguments: [*mut c_void; 3] = [
            &mut situated_front as *mut u64 as *mut c_void,
            &mut selection_pointer as *mut u64 as *mut c_void,
            &mut port_count_wire as *mut u32 as *mut c_void,
        ];
        if !addressed_face_condensation {
            driver(
                unsafe {
                    cuLaunchKernel(
                        self.card.membrane_sparse_quadratic_returned_port_resolve,
                        1,
                        1,
                        1,
                        1,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        resolve_arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(resolve_membrane_sparse_quadratic_returned_port)",
            )?;
        }

        let mut pair_factors = pair_factors_pointer;
        let mut restrictions = restriction_pointer;
        let mut source = source_pointer;
        let mut conditioned_pointer = conditioned.pointer;
        let mut scratch_pointer = scratch.pointer;
        let mut pair_count_wire = pair_population as u32;
        let mut factor_count_wire = factor_population as u32;
        let mut source_limb_count_wire = source_limb_count as u32;
        let mut restriction_limb_count_wire = restriction_limb_count as u32;
        let mut conditioned_limb_count_wire = conditioned_limb_count as u32;
        let mut generator_count_wire = generator_population as u32;
        let mut second_scratch_pointer = second_scratch.pointer;
        let mut condition_arguments: [*mut c_void; 12] = [
            &mut pair_factors as *mut u64 as *mut c_void,
            &mut restrictions as *mut u64 as *mut c_void,
            &mut source as *mut u64 as *mut c_void,
            &mut selection_pointer as *mut u64 as *mut c_void,
            &mut conditioned_pointer as *mut u64 as *mut c_void,
            &mut scratch_pointer as *mut u64 as *mut c_void,
            &mut pair_count_wire as *mut u32 as *mut c_void,
            &mut factor_count_wire as *mut u32 as *mut c_void,
            &mut port_count_wire as *mut u32 as *mut c_void,
            &mut source_limb_count_wire as *mut u32 as *mut c_void,
            &mut restriction_limb_count_wire as *mut u32 as *mut c_void,
            &mut conditioned_limb_count_wire as *mut u32 as *mut c_void,
        ];
        if addressed_face_condensation {
            let mut face_arguments: [*mut c_void; 14] = [
                &mut pair_factors as *mut u64 as *mut c_void,
                &mut restrictions as *mut u64 as *mut c_void,
                &mut source as *mut u64 as *mut c_void,
                &mut situated_front as *mut u64 as *mut c_void,
                &mut conditioned_pointer as *mut u64 as *mut c_void,
                &mut scratch_pointer as *mut u64 as *mut c_void,
                &mut second_scratch_pointer as *mut u64 as *mut c_void,
                &mut pair_count_wire as *mut u32 as *mut c_void,
                &mut factor_count_wire as *mut u32 as *mut c_void,
                &mut port_count_wire as *mut u32 as *mut c_void,
                &mut generator_count_wire as *mut u32 as *mut c_void,
                &mut source_limb_count_wire as *mut u32 as *mut c_void,
                &mut restriction_limb_count_wire as *mut u32 as *mut c_void,
                &mut conditioned_limb_count_wire as *mut u32 as *mut c_void,
            ];
            driver(
                unsafe {
                    cuLaunchKernel(
                        self.card.membrane_sparse_quadratic_returned_faces_condition,
                        self.card.grid_for(pair_population as u64)?,
                        1,
                        1,
                        self.card.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        face_arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(condition_membrane_sparse_quadratic_pairs_by_returned_faces)",
            )?;
        } else {
            driver(
                unsafe {
                    cuLaunchKernel(
                        self.card.membrane_sparse_quadratic_returned_port_condition,
                        self.card.grid_for(pair_population as u64)?,
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
                "cuLaunchKernel(condition_membrane_sparse_quadratic_pairs_by_returned_port)",
            )?;
        }
        if trace_configuration().holonics_phase_trace {
            if let Err(error) = driver(
                unsafe { cuCtxSynchronize() },
                "cuCtxSynchronize(returned sparse quadratic restriction)",
            ) {
                eprintln!("mem6-pair-returned-restriction device-refusal: {error}");
                return Err(error);
            }
            eprintln!(
                "mem6-pair-returned-restriction admitted pairs={} source-limbs={} restriction-limbs={} target-limbs={}",
                pair_population, source_limb_count, restriction_limb_count, conditioned_limb_count,
            );
        }
        self.card.launches = self
            .card
            .launches
            .checked_add(2)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let resident_octets = u64::try_from(
            conditioned_octets
                .checked_mul(3)
                .and_then(|octets| octets.checked_add(2 * std::mem::size_of::<u32>()))
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        )
        .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let transport = self
            .factored_receiver_history
            .as_mut()
            .and_then(|mount| mount.transported_image.as_mut())
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        transport.sparse_conditioned = Some(ResidentSparseQuadraticConditionedCurrent {
            state_population: 1,
            coefficient_state_capacity: 1,
            state_population_device: Buffer::of(&[1_u32])?,
            state_ids_host: vec![u32::MAX],
            state_ids: Buffer::of(&[u32::MAX])?,
            coefficient_limb_count: conditioned_limb_count as u32,
            maximal_coefficient: maximal_conditioned,
            coefficients: conditioned,
            returned_port_selection: selection,
            work_buffers: vec![scratch, second_scratch],
            relational_continuation: None,
            launches: 2,
            synchronizations: 0,
            apparatus_shape_host_egress_octets: 0,
        });
        transport.resident_octets = transport
            .resident_octets
            .checked_add(resident_octets)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        Ok(())
    }
}
