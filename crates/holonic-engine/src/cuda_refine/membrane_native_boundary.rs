use super::*;

impl ResidentMembraneInteriorWord {
    /// Return the exact projective front without retaining the complete ordered pair square.
    /// One CUDA-warp-width population of challenged-face fibres is an apparatus window; every
    /// ordered comparison still occurs and folds through an idempotent device-local dominance
    /// join.  The omitted cells are reconstructed from the immutable coordinate sections, their
    /// global pair addresses, and the comparison kernel.
    /// Stage the next fixed-pair recurrence and found its complete membrane receiver section
    /// directly from the resident boundary incidence.  This is algebraically identical to the
    /// cold addressed-functional expansion, but no receiver term population is rebuilt on the
    /// host and no source rank-one family is reopened.
    pub fn stage_resident_sparse_quadratic_native_boundary_receivers(
        &mut self,
        source_address: &ResidentFactoredMomentAddress,
        boundary: &ResidentBoundaryRestrictionFront,
    ) -> Result<ResidentFactoredMomentReceiverAddress, CudaRefineError> {
        const FAMILY_CHUNK: usize = 256;
        const NATIVE_BOUNDARY_PAIR_CHUNK: usize = 8192;
        if &self.resident_sparse_quadratic_moment_address()? != source_address
            || boundary.boundary_states.is_empty()
            || boundary.universal_ports.is_empty()
            || boundary.universal_ports.len() > u32::MAX as usize
            || boundary
                .universal_ports
                .iter()
                .collect::<BTreeSet<_>>()
                .len()
                != boundary.universal_ports.len()
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        driver(
            unsafe { cuCtxSetCurrent(self.card.context) },
            "cuCtxSetCurrent",
        )?;
        let port_population = boundary.universal_ports.len();
        let family_count = self.families as usize;
        let receiver_count = self.receiver_count as usize;
        let factor_count = self.factors as usize;
        let receiver_stride = family_count
            .checked_mul(2)
            .and_then(|held| held.checked_add(receiver_count.checked_mul(2)?))
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let (
            source_state_population,
            source_state_ids_host,
            mut source_state_ids,
            pair_population,
            source_limb_count,
            maximal_source,
            maximal_incoming,
            generator_population,
            mut source_limbs,
            mut pair_factors,
            mut pair_row_offsets,
            mut generator_target_offsets,
            mut generator_source_pairs,
            mut generator_multiplicities,
            situated_receiver_limb_count,
            maximal_ingress_receiver,
            mut situated_receiver,
            mut native_generator_targets,
            maximal_generator_fibre_population,
            mut native_factor_receiver_classes,
            atlas_state_count,
            atlas_universal_port_count,
            atlas_transition_count,
            restriction_limb_count,
            maximal_restriction,
            mut state_port_transition,
            mut transition_targets,
            mut transition_factor_offsets,
            mut transition_factors,
            mut transition_current_limbs,
            restriction_atlas_identity,
        ) = {
            let mount = self
                .factored_receiver_history
                .as_ref()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            if mount.transported_image.is_some() {
                return Err(CudaRefineError::MembraneInteriorWordShape);
            }
            let source = mount
                .sparse_pair
                .as_ref()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let action = self
                .quadratic_action
                .as_ref()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let atlas = self
                .boundary_restriction_atlas
                .as_ref()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let mut generator_targets = action.generator_targets.chunks_exact(factor_count);
            let mut generator_count = 0_usize;
            let mut maximal_generator_fibre_population = 0_u32;
            for generator in generator_targets.by_ref() {
                generator_count = generator_count.saturating_add(1);
                let mut fibres = vec![0_u32; factor_count];
                for target in generator {
                    let fibre = fibres
                        .get_mut(*target as usize)
                        .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
                    *fibre = fibre
                        .checked_add(1)
                        .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
                }
                maximal_generator_fibre_population =
                    maximal_generator_fibre_population.max(fibres.into_iter().max().unwrap_or(0));
            }
            if !generator_targets.remainder().is_empty()
                || generator_count != source.action.generator_population as usize
                || maximal_generator_fibre_population == 0
            {
                return Err(CudaRefineError::MembraneInteriorWordShape);
            }
            (
                source.state_population as usize,
                source.state_ids_host.clone(),
                source.state_ids.pointer,
                source.pair_population as usize,
                source.coefficient_limb_count as usize,
                source.maximal_coefficient.clone(),
                source.maximal_incoming_multiplicity.clone(),
                source.action.generator_population as usize,
                source.coefficients.pointer,
                source.pair_factors.pointer,
                source.pair_row_offsets.pointer,
                source.generator_target_offsets.pointer,
                source.generator_source_pairs.pointer,
                source.generator_multiplicities.pointer,
                source.situated_receiver_limb_count as usize,
                source.maximal_situated_receiver_coefficient.clone(),
                source.situated_receiver_coefficients.pointer,
                action.native_generator_targets.pointer,
                maximal_generator_fibre_population,
                action.native_factor_receiver_classes.pointer,
                atlas.state_count,
                atlas.universal_port_count,
                atlas.transition_count,
                atlas.restriction_limb_count as usize,
                atlas.maximal_current.clone(),
                atlas.state_port_transition.pointer,
                atlas.transition_targets.pointer,
                atlas.transition_factor_offsets.pointer,
                atlas.transition_factors.pointer,
                atlas.transition_current_limbs.pointer,
                atlas.identity_sha256.clone(),
            )
        };
        if pair_population == 0
            || source_state_population == 0
            || source_state_ids_host.len() != source_state_population
            || source_state_ids_host
                .iter()
                .copied()
                .collect::<BTreeSet<_>>()
                != boundary
                    .boundary_states
                    .iter()
                    .copied()
                    .collect::<BTreeSet<_>>()
            || source_limb_count == 0
            || generator_population == 0
            || family_count == 0
            || receiver_count == 0
            || situated_receiver_limb_count == 0
            || restriction_limb_count == 0
            || source_state_ids_host
                .iter()
                .any(|state| *state >= atlas_state_count)
            || boundary
                .universal_ports
                .iter()
                .any(|port| *port >= atlas_universal_port_count)
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let relational_current_aperture = self.sparse_relational_current.as_ref().map(|current| {
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
                current.receipt.returned_current_identity_sha256.clone(),
            )
        });
        if trace_configuration().holonics_phase_trace {
            if let Some(current) = self.sparse_relational_current.as_ref() {
                let relational_population = current
                    .state_count
                    .checked_mul(factor_count)
                    .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
                let mut state_present = vec![0_u32; current.state_count];
                let mut states = vec![0_u32; current.state_count];
                let mut real_sign = vec![0_u8; relational_population];
                let mut imaginary_sign = vec![0_u8; relational_population];
                current.state_present.read(&mut state_present)?;
                current.states.read(&mut states)?;
                current.factor_real_sign.read(&mut real_sign)?;
                current.factor_imaginary_sign.read(&mut imaginary_sign)?;
                eprintln!(
                    "uar2-relational-current-support source-states={:?} relation-states={:?} relation-present={:?} nonzero={} real-nonzero={} imaginary-nonzero={} limbs={}",
                    source_state_ids_host,
                    states,
                    state_present,
                    real_sign
                        .iter()
                        .zip(&imaginary_sign)
                        .filter(|(real, imaginary)| **real != 0 || **imaginary != 0)
                        .count(),
                    real_sign.iter().filter(|value| **value != 0).count(),
                    imaginary_sign.iter().filter(|value| **value != 0).count(),
                    current.factor_limb_count,
                );
            }
        }
        let face_population = source_state_population
            .checked_mul(port_population)
            .and_then(|held| held.checked_mul(generator_population))
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        if trace_configuration().holonics_phase_trace {
            eprintln!(
                "uar2-native-boundary-begin states={} ports={} generators={} faces={} pairs={} factors={}",
                source_state_population,
                port_population,
                generator_population,
                face_population,
                pair_population,
                factor_count,
            );
        }
        let receiver_population = face_population
            .checked_mul(receiver_stride)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let face_ports_host = (0..source_state_population)
            .flat_map(|_| 0..port_population as u32)
            .flat_map(|port| std::iter::repeat_n(port, generator_population))
            .collect::<Vec<_>>();
        let face_generators_host = (0..source_state_population)
            .flat_map(|_| 0..port_population)
            .flat_map(|_| 0..generator_population as u32)
            .collect::<Vec<_>>();
        let face_source_states_host = source_state_ids_host
            .iter()
            .flat_map(|state| {
                std::iter::repeat_n(*state, port_population.saturating_mul(generator_population))
            })
            .collect::<Vec<_>>();
        if face_ports_host.len() != face_population
            || face_generators_host.len() != face_population
            || face_source_states_host.len() != face_population
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let maximal_target = &maximal_source * &maximal_incoming;
        let target_limb_count = maximal_target.to_u32_digits().len().max(1);
        let transported_pair_population = source_state_population
            .checked_mul(generator_population)
            .and_then(|held| held.checked_mul(pair_population))
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let target_octets = transported_pair_population
            .checked_mul(target_limb_count)
            .and_then(|words| words.checked_mul(std::mem::size_of::<u32>()))
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let target_limbs = Buffer::alloc(target_octets)?;
        target_limbs.fill(0, target_octets)?;
        let overflow = Buffer::of(&[0_u32])?;
        let mut target_limbs_pointer = target_limbs.pointer;
        let mut pair_population_wire = pair_population as u32;
        let mut source_limb_count_wire = source_limb_count as u32;
        let mut target_limb_count_wire = target_limb_count as u32;
        let mut transport_generator_count_wire = generator_population as u32;
        let mut source_state_population_wire = source_state_population as u32;
        let mut overflow_pointer = overflow.pointer;
        let mut transport_arguments: [*mut c_void; 11] = [
            &mut generator_target_offsets as *mut u64 as *mut c_void,
            &mut generator_source_pairs as *mut u64 as *mut c_void,
            &mut generator_multiplicities as *mut u64 as *mut c_void,
            &mut source_limbs as *mut u64 as *mut c_void,
            &mut target_limbs_pointer as *mut u64 as *mut c_void,
            &mut source_state_population_wire as *mut u32 as *mut c_void,
            &mut transport_generator_count_wire as *mut u32 as *mut c_void,
            &mut pair_population_wire as *mut u32 as *mut c_void,
            &mut source_limb_count_wire as *mut u32 as *mut c_void,
            &mut target_limb_count_wire as *mut u32 as *mut c_void,
            &mut overflow_pointer as *mut u64 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card
                        .membrane_sparse_quadratic_state_generator_pair_transport,
                    self.card.grid_for(transported_pair_population as u64)?,
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
            "cuLaunchKernel(transport_membrane_sparse_quadratic_state_generator_pairs)",
        )?;

        let restriction_entries = face_population
            .checked_mul(factor_count)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let restriction_octets = restriction_entries
            .checked_mul(restriction_limb_count)
            .and_then(|words| words.checked_mul(std::mem::size_of::<u32>()))
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let restrictions = Buffer::alloc(restriction_octets)?;
        let restriction_present = Buffer::alloc(face_population)?;
        let restriction_target_states = Buffer::alloc(
            face_population
                .checked_mul(std::mem::size_of::<u32>())
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        )?;
        let universal_ports_device = Buffer::of(&boundary.universal_ports)?;
        let mut restrictions_pointer = restrictions.pointer;
        let mut restriction_present_pointer = restriction_present.pointer;
        let mut restriction_target_states_pointer = restriction_target_states.pointer;
        let mut universal_ports_pointer = universal_ports_device.pointer;
        let mut local_port_count_wire = port_population as u32;
        let mut generator_count_wire = generator_population as u32;
        let mut port_count_wire = face_population as u32;
        let mut atlas_state_count_wire = atlas_state_count;
        let mut atlas_universal_port_count_wire = atlas_universal_port_count;
        let mut atlas_transition_count_wire = atlas_transition_count;
        let mut factor_count_wire = factor_count as u32;
        let mut restriction_limb_count_wire = restriction_limb_count as u32;
        let mut gather_arguments: [*mut c_void; 19] = [
            &mut state_port_transition as *mut u64 as *mut c_void,
            &mut transition_targets as *mut u64 as *mut c_void,
            &mut transition_factor_offsets as *mut u64 as *mut c_void,
            &mut transition_factors as *mut u64 as *mut c_void,
            &mut transition_current_limbs as *mut u64 as *mut c_void,
            &mut source_state_ids as *mut u64 as *mut c_void,
            &mut universal_ports_pointer as *mut u64 as *mut c_void,
            &mut restrictions_pointer as *mut u64 as *mut c_void,
            &mut restriction_present_pointer as *mut u64 as *mut c_void,
            &mut restriction_target_states_pointer as *mut u64 as *mut c_void,
            &mut source_state_population_wire as *mut u32 as *mut c_void,
            &mut local_port_count_wire as *mut u32 as *mut c_void,
            &mut generator_count_wire as *mut u32 as *mut c_void,
            &mut atlas_state_count_wire as *mut u32 as *mut c_void,
            &mut atlas_universal_port_count_wire as *mut u32 as *mut c_void,
            &mut atlas_transition_count_wire as *mut u32 as *mut c_void,
            &mut factor_count_wire as *mut u32 as *mut c_void,
            &mut restriction_limb_count_wire as *mut u32 as *mut c_void,
            &mut overflow_pointer as *mut u64 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card
                        .membrane_sparse_quadratic_state_face_restriction_gather,
                    self.card.grid_for(face_population as u64)?,
                    1,
                    1,
                    self.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    gather_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(gather_membrane_sparse_quadratic_state_addressed_face_restrictions)",
        )?;

        let conditioned_bound = &maximal_target * &maximal_restriction * &maximal_restriction;
        let family_bound = &conditioned_bound
            * BigUint::from(self.total_factor_capacity)
            * BigUint::from(generator_population)
            * BigUint::from(2_u8);
        let opaque_bound = &conditioned_bound
            * BigUint::from(pair_population)
            * BigUint::from(generator_population)
            * BigUint::from(4_u8);
        let situated_bound = &conditioned_bound
            * &maximal_ingress_receiver
            * BigUint::from(pair_population)
            * BigUint::from(2_u8);
        let situated_current_norm_bound = &conditioned_bound
            * &conditioned_bound
            * BigUint::from(pair_population)
            * BigUint::from(2_u8);
        let restricted_ingress_bound =
            &maximal_ingress_receiver * &maximal_restriction * &maximal_restriction;
        let situated_ingress_norm_bound = &restricted_ingress_bound
            * &restricted_ingress_bound
            * BigUint::from(pair_population)
            * BigUint::from(2_u8);
        let receiver_output_bound = family_bound.max(opaque_bound);
        let common_bound = receiver_output_bound
            .clone()
            .max(situated_bound.clone())
            .max(situated_current_norm_bound.clone())
            .max(situated_ingress_norm_bound.clone());
        let output_limb_count = common_bound.to_u32_digits().len().max(1).saturating_add(1);
        if output_limb_count > u32::MAX as usize {
            return Err(CudaRefineError::MembraneInteriorCurrentOutsideApparatus);
        }
        let octets = |population: usize, limbs: usize| {
            population
                .checked_mul(limbs)
                .and_then(|words| words.checked_mul(std::mem::size_of::<u32>()))
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)
        };
        let family_chunks = factor_count.div_ceil(FAMILY_CHUNK);
        let pair_chunks = pair_population.div_ceil(NATIVE_BOUNDARY_PAIR_CHUNK);
        let family_sections = face_population
            .checked_mul(family_count)
            .and_then(|held| held.checked_mul(2))
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let potential_axis_count = receiver_count
            .checked_mul(2)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let potential_sections = face_population
            .checked_mul(potential_axis_count)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let family_partial_population = family_sections
            .checked_mul(family_chunks)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let potential_partial_population = potential_sections
            .checked_mul(pair_chunks)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let family_work = face_population
            .checked_mul(family_count)
            .and_then(|held| held.checked_mul(family_chunks))
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let potential_work = face_population
            .checked_mul(pair_chunks)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let family_reduce_population = family_sections
            .checked_mul(family_chunks.div_ceil(1024).max(1))
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let potential_reduce_population = potential_sections
            .checked_mul(pair_chunks.div_ceil(1024).max(1))
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let family_partial_signs = Buffer::alloc(family_partial_population)?;
        let family_partial_limbs =
            Buffer::alloc(octets(family_partial_population, output_limb_count)?)?;
        let family_reduce_signs = Buffer::alloc(family_reduce_population)?;
        let family_reduce_limbs =
            Buffer::alloc(octets(family_reduce_population, output_limb_count)?)?;
        let family_final_signs = Buffer::alloc(family_sections)?;
        let family_final_limbs = Buffer::alloc(octets(family_sections, output_limb_count)?)?;
        let family_product_scratch = Buffer::alloc(octets(family_work, output_limb_count)?)?;
        let family_scaled_scratch = Buffer::alloc(octets(family_work, output_limb_count)?)?;
        let potential_partial_signs = Buffer::alloc(potential_partial_population)?;
        let potential_partial_limbs =
            Buffer::alloc(octets(potential_partial_population, output_limb_count)?)?;
        let potential_reduce_signs = Buffer::alloc(potential_reduce_population)?;
        let potential_reduce_limbs =
            Buffer::alloc(octets(potential_reduce_population, output_limb_count)?)?;
        let potential_final_signs = Buffer::alloc(potential_sections)?;
        let potential_final_limbs = Buffer::alloc(octets(potential_sections, output_limb_count)?)?;
        let potential_first_scratch = Buffer::alloc(octets(potential_work, output_limb_count)?)?;
        let potential_second_scratch = Buffer::alloc(octets(potential_work, output_limb_count)?)?;

        let mut family_partial_sign_pointer = family_partial_signs.pointer;
        let mut family_partial_limb_pointer = family_partial_limbs.pointer;
        let mut family_product_pointer = family_product_scratch.pointer;
        let mut family_scaled_pointer = family_scaled_scratch.pointer;
        let mut factor_capacity_pointer = self.factor_capacity.pointer;
        let mut family_orientation_pointer = self.family_orientation.pointer;
        let mut family_count_wire = family_count as u32;
        let mut generator_count_wire = generator_population as u32;
        let mut family_chunk_count_wire = family_chunks as u32;
        let mut family_chunk_wire = FAMILY_CHUNK as u32;
        let mut output_limb_count_wire = output_limb_count as u32;
        let mut family_arguments: [*mut c_void; 23] = [
            &mut pair_row_offsets as *mut u64 as *mut c_void,
            &mut pair_factors as *mut u64 as *mut c_void,
            &mut target_limbs_pointer as *mut u64 as *mut c_void,
            &mut restrictions_pointer as *mut u64 as *mut c_void,
            &mut restriction_present_pointer as *mut u64 as *mut c_void,
            &mut native_generator_targets as *mut u64 as *mut c_void,
            &mut factor_capacity_pointer as *mut u64 as *mut c_void,
            &mut family_orientation_pointer as *mut u64 as *mut c_void,
            &mut family_partial_sign_pointer as *mut u64 as *mut c_void,
            &mut family_partial_limb_pointer as *mut u64 as *mut c_void,
            &mut family_product_pointer as *mut u64 as *mut c_void,
            &mut family_scaled_pointer as *mut u64 as *mut c_void,
            &mut port_count_wire as *mut u32 as *mut c_void,
            &mut source_state_population_wire as *mut u32 as *mut c_void,
            &mut factor_count_wire as *mut u32 as *mut c_void,
            &mut family_count_wire as *mut u32 as *mut c_void,
            &mut generator_count_wire as *mut u32 as *mut c_void,
            &mut family_chunk_count_wire as *mut u32 as *mut c_void,
            &mut family_chunk_wire as *mut u32 as *mut c_void,
            &mut target_limb_count_wire as *mut u32 as *mut c_void,
            &mut restriction_limb_count_wire as *mut u32 as *mut c_void,
            &mut output_limb_count_wire as *mut u32 as *mut c_void,
            &mut overflow_pointer as *mut u64 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card.membrane_sparse_quadratic_native_family_chunks,
                    self.card.grid_for(family_work as u64)?,
                    1,
                    1,
                    self.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    family_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(form_membrane_sparse_quadratic_native_family_chunks)",
        )?;

        let mut potential_partial_sign_pointer = potential_partial_signs.pointer;
        let mut potential_partial_limb_pointer = potential_partial_limbs.pointer;
        let mut potential_first_pointer = potential_first_scratch.pointer;
        let mut potential_second_pointer = potential_second_scratch.pointer;
        let mut receiver_count_wire = receiver_count as u32;
        let mut pair_chunk_count_wire = pair_chunks as u32;
        let mut pair_chunk_wire = NATIVE_BOUNDARY_PAIR_CHUNK as u32;
        let mut situated_receiver_limb_count_wire = situated_receiver_limb_count as u32;
        let mut potential_arguments: [*mut c_void; 24] = [
            &mut pair_factors as *mut u64 as *mut c_void,
            &mut target_limbs_pointer as *mut u64 as *mut c_void,
            &mut situated_receiver as *mut u64 as *mut c_void,
            &mut restrictions_pointer as *mut u64 as *mut c_void,
            &mut restriction_present_pointer as *mut u64 as *mut c_void,
            &mut native_generator_targets as *mut u64 as *mut c_void,
            &mut native_factor_receiver_classes as *mut u64 as *mut c_void,
            &mut potential_partial_sign_pointer as *mut u64 as *mut c_void,
            &mut potential_partial_limb_pointer as *mut u64 as *mut c_void,
            &mut potential_first_pointer as *mut u64 as *mut c_void,
            &mut potential_second_pointer as *mut u64 as *mut c_void,
            &mut pair_population_wire as *mut u32 as *mut c_void,
            &mut factor_count_wire as *mut u32 as *mut c_void,
            &mut port_count_wire as *mut u32 as *mut c_void,
            &mut source_state_population_wire as *mut u32 as *mut c_void,
            &mut receiver_count_wire as *mut u32 as *mut c_void,
            &mut generator_count_wire as *mut u32 as *mut c_void,
            &mut pair_chunk_count_wire as *mut u32 as *mut c_void,
            &mut pair_chunk_wire as *mut u32 as *mut c_void,
            &mut target_limb_count_wire as *mut u32 as *mut c_void,
            &mut situated_receiver_limb_count_wire as *mut u32 as *mut c_void,
            &mut restriction_limb_count_wire as *mut u32 as *mut c_void,
            &mut output_limb_count_wire as *mut u32 as *mut c_void,
            &mut overflow_pointer as *mut u64 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card.membrane_sparse_quadratic_native_potential_chunks,
                    self.card.grid_for(potential_work as u64)?,
                    1,
                    1,
                    self.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    potential_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(form_membrane_sparse_quadratic_native_potential_chunks)",
        )?;
        let family_reduce_launches = self.reduce_sparse_quadratic_signed_sections(
            &family_partial_signs,
            &family_partial_limbs,
            &family_reduce_signs,
            &family_reduce_limbs,
            &family_final_signs,
            &family_final_limbs,
            family_sections,
            family_chunks,
            output_limb_count,
        )?;
        let potential_reduce_launches = self.reduce_sparse_quadratic_signed_sections(
            &potential_partial_signs,
            &potential_partial_limbs,
            &potential_reduce_signs,
            &potential_reduce_limbs,
            &potential_final_signs,
            &potential_final_limbs,
            potential_sections,
            pair_chunks,
            output_limb_count,
        )?;

        let output_signs = Buffer::alloc(receiver_population)?;
        let output_limbs = Buffer::alloc(octets(receiver_population, output_limb_count)?)?;
        let situated_signs = Buffer::alloc(face_population)?;
        let situated_limbs = Buffer::alloc(octets(face_population, output_limb_count)?)?;
        let situated_current_norm_limbs =
            Buffer::alloc(octets(face_population, output_limb_count)?)?;
        let situated_ingress_norm_limbs =
            Buffer::alloc(octets(face_population, output_limb_count)?)?;
        let mut family_final_sign_pointer = family_final_signs.pointer;
        let mut family_final_limb_pointer = family_final_limbs.pointer;
        let mut potential_final_sign_pointer = potential_final_signs.pointer;
        let mut potential_final_limb_pointer = potential_final_limbs.pointer;
        let mut output_sign_pointer = output_signs.pointer;
        let mut output_limb_pointer = output_limbs.pointer;
        let mut situated_sign_pointer = situated_signs.pointer;
        let mut situated_limb_pointer = situated_limbs.pointer;
        let mut situated_current_norm_limb_pointer = situated_current_norm_limbs.pointer;
        let mut situated_ingress_norm_limb_pointer = situated_ingress_norm_limbs.pointer;
        let mut scatter_arguments: [*mut c_void; 14] = [
            &mut family_final_sign_pointer as *mut u64 as *mut c_void,
            &mut family_final_limb_pointer as *mut u64 as *mut c_void,
            &mut potential_final_sign_pointer as *mut u64 as *mut c_void,
            &mut potential_final_limb_pointer as *mut u64 as *mut c_void,
            &mut output_sign_pointer as *mut u64 as *mut c_void,
            &mut output_limb_pointer as *mut u64 as *mut c_void,
            &mut situated_sign_pointer as *mut u64 as *mut c_void,
            &mut situated_limb_pointer as *mut u64 as *mut c_void,
            &mut situated_current_norm_limb_pointer as *mut u64 as *mut c_void,
            &mut situated_ingress_norm_limb_pointer as *mut u64 as *mut c_void,
            &mut port_count_wire as *mut u32 as *mut c_void,
            &mut family_count_wire as *mut u32 as *mut c_void,
            &mut receiver_count_wire as *mut u32 as *mut c_void,
            &mut output_limb_count_wire as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card.membrane_sparse_quadratic_native_receiver_scatter,
                    self.card
                        .grid_for(receiver_population.max(face_population) as u64)?,
                    1,
                    1,
                    self.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    scatter_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(scatter_membrane_sparse_quadratic_native_receivers)",
        )?;

        let relational_receiver = if let Some((
            mut relational_state_present,
            mut relational_states,
            relational_state_count,
            mut relational_real_sign,
            mut relational_real_limbs,
            mut relational_imaginary_sign,
            mut relational_imaginary_limbs,
            relational_source_limb_count,
            returned_factor_bound,
            returned_current_identity_sha256,
        )) = relational_current_aperture
        {
            let relational_factor_bound =
                returned_factor_bound.clone() * BigUint::from(maximal_generator_fibre_population);
            let relational_pair_bound =
                BigUint::from(2_u8) * &relational_factor_bound * &relational_factor_bound;
            let restriction_square = &maximal_restriction * &maximal_restriction;
            let restricted_relational_pair_bound = &relational_pair_bound * &restriction_square;
            let restricted_target_bound = &maximal_target * &restriction_square;
            let pair_extent = BigUint::from(pair_population) * BigUint::from(2_u8);
            let compatibility_bound =
                &pair_extent * &restricted_relational_pair_bound * &restricted_target_bound;
            let transported_norm_bound =
                &pair_extent * &restricted_target_bound * &restricted_target_bound;
            let ingress_norm_bound = &pair_extent
                * &restricted_relational_pair_bound
                * &restricted_relational_pair_bound;
            let relational_bound = compatibility_bound
                .clone()
                .max(transported_norm_bound.clone())
                .max(ingress_norm_bound.clone());
            let relational_limb_count = relational_bound
                .to_u32_digits()
                .len()
                .max(1)
                .saturating_add(1);
            if relational_limb_count > u32::MAX as usize {
                return Err(CudaRefineError::MembraneInteriorCurrentOutsideApparatus);
            }
            if trace_configuration().holonics_phase_trace {
                eprintln!(
                    "uar2-relational-bound returned={} maximal-generator-fibre={} pair-receiver={}",
                    returned_factor_bound,
                    maximal_generator_fibre_population,
                    relational_pair_bound,
                );
            }
            let mut relational_obstruction = overflow_pointer;
            let pair_chunk = NATIVE_BOUNDARY_PAIR_CHUNK;
            let chunk_count = pair_population.div_ceil(pair_chunk);
            let section_count = face_population
                .checked_mul(3)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            let partial_population = section_count
                .checked_mul(chunk_count)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            let reduce_population = section_count
                .checked_mul(chunk_count.div_ceil(1024).max(1))
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            let work_population = face_population
                .checked_mul(chunk_count)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            let transported_factor_population = relational_state_count
                .checked_mul(generator_population)
                .and_then(|extent| extent.checked_mul(factor_count))
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            let transported_relational_limb_count = relational_factor_bound
                .to_u32_digits()
                .len()
                .max(relational_source_limb_count)
                .max(1)
                .saturating_add(1);
            let transported_factor_limb_octets = transported_factor_population
                .checked_mul(transported_relational_limb_count)
                .and_then(|extent| extent.checked_mul(std::mem::size_of::<u32>()))
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            let transported_relational_real_sign = Buffer::alloc(transported_factor_population)?;
            let transported_relational_real_limbs = Buffer::alloc(transported_factor_limb_octets)?;
            let transported_relational_imaginary_sign =
                Buffer::alloc(transported_factor_population)?;
            let transported_relational_imaginary_limbs =
                Buffer::alloc(transported_factor_limb_octets)?;
            let partial_signs = Buffer::alloc(partial_population)?;
            let partial_limbs = Buffer::alloc(octets(partial_population, relational_limb_count)?)?;
            let reduce_signs = Buffer::alloc(reduce_population)?;
            let reduce_limbs = Buffer::alloc(octets(reduce_population, relational_limb_count)?)?;
            let final_signs = Buffer::alloc(section_count)?;
            let final_limbs = Buffer::alloc(octets(section_count, relational_limb_count)?)?;
            let first_scratch = Buffer::alloc(octets(work_population, relational_limb_count)?)?;
            let second_scratch = Buffer::alloc(octets(work_population, relational_limb_count)?)?;
            let third_scratch = Buffer::alloc(octets(work_population, relational_limb_count)?)?;
            let compatibility_signs = Buffer::alloc(face_population)?;
            let compatibility_limbs =
                Buffer::alloc(octets(face_population, relational_limb_count)?)?;
            let relational_transported_norm_limbs =
                Buffer::alloc(octets(face_population, relational_limb_count)?)?;
            let relational_ingress_norm_limbs =
                Buffer::alloc(octets(face_population, relational_limb_count)?)?;

            let mut form_relational = ptr::null_mut();
            let mut scatter_relational = ptr::null_mut();
            let mut transport_relational = ptr::null_mut();
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
                        &mut form_relational,
                        self.card.module,
                        c"form_membrane_sparse_relational_boundary_chunks_arbitrary".as_ptr(),
                    )
                },
                "cuModuleGetFunction(form_membrane_sparse_relational_boundary_chunks_arbitrary)",
            )?;
            driver(
                unsafe {
                    cuModuleGetFunction(
                        &mut scatter_relational,
                        self.card.module,
                        c"scatter_membrane_sparse_relational_boundary".as_ptr(),
                    )
                },
                "cuModuleGetFunction(scatter_membrane_sparse_relational_boundary)",
            )?;
            let mut transported_relational_real_sign_pointer =
                transported_relational_real_sign.pointer;
            let mut transported_relational_real_limbs_pointer =
                transported_relational_real_limbs.pointer;
            let mut transported_relational_imaginary_sign_pointer =
                transported_relational_imaginary_sign.pointer;
            let mut transported_relational_imaginary_limbs_pointer =
                transported_relational_imaginary_limbs.pointer;
            let mut relational_generator_targets = native_generator_targets;
            let mut relational_factor_count_for_transport = factor_count as u32;
            let mut relational_generator_count_for_transport = generator_population as u32;
            let mut relational_state_count_for_transport = relational_state_count as u32;
            let mut relational_source_limb_count_for_transport =
                relational_source_limb_count as u32;
            let mut transported_relational_limb_count_for_transport =
                transported_relational_limb_count as u32;
            let mut relational_obstruction_for_transport = overflow_pointer;
            let mut transport_arguments: [*mut c_void; 16] = [
                &mut relational_generator_targets as *mut u64 as *mut c_void,
                &mut relational_state_present as *mut u64 as *mut c_void,
                &mut relational_real_sign as *mut u64 as *mut c_void,
                &mut relational_real_limbs as *mut u64 as *mut c_void,
                &mut relational_imaginary_sign as *mut u64 as *mut c_void,
                &mut relational_imaginary_limbs as *mut u64 as *mut c_void,
                &mut transported_relational_real_sign_pointer as *mut u64 as *mut c_void,
                &mut transported_relational_real_limbs_pointer as *mut u64 as *mut c_void,
                &mut transported_relational_imaginary_sign_pointer as *mut u64 as *mut c_void,
                &mut transported_relational_imaginary_limbs_pointer as *mut u64 as *mut c_void,
                &mut relational_factor_count_for_transport as *mut u32 as *mut c_void,
                &mut relational_generator_count_for_transport as *mut u32 as *mut c_void,
                &mut relational_state_count_for_transport as *mut u32 as *mut c_void,
                &mut relational_source_limb_count_for_transport as *mut u32 as *mut c_void,
                &mut transported_relational_limb_count_for_transport as *mut u32 as *mut c_void,
                &mut relational_obstruction_for_transport as *mut u64 as *mut c_void,
            ];
            driver(
                unsafe {
                    cuLaunchKernel(
                        transport_relational,
                        self.card.grid_for(transported_factor_population as u64)?,
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
                "cuLaunchKernel(transport_membrane_sparse_relational_generator_limbs)",
            )?;
            if trace_configuration().holonics_phase_trace {
                let mut transported_real = vec![0_u8; transported_factor_population];
                let mut transported_imaginary = vec![0_u8; transported_factor_population];
                transported_relational_real_sign.read(&mut transported_real)?;
                transported_relational_imaginary_sign.read(&mut transported_imaginary)?;
                eprintln!(
                    "uar2-relational-transport-support nonzero={} real={} imaginary={}",
                    transported_real
                        .iter()
                        .zip(&transported_imaginary)
                        .filter(|(real, imaginary)| **real != 0 || **imaginary != 0)
                        .count(),
                    transported_real.iter().filter(|sign| **sign != 0).count(),
                    transported_imaginary
                        .iter()
                        .filter(|sign| **sign != 0)
                        .count(),
                );
            }
            let mut partial_sign_pointer = partial_signs.pointer;
            let mut partial_limb_pointer = partial_limbs.pointer;
            let mut first_scratch_pointer = first_scratch.pointer;
            let mut second_scratch_pointer = second_scratch.pointer;
            let mut third_scratch_pointer = third_scratch.pointer;
            let mut restriction_present_for_relational = restriction_present_pointer;
            let mut chunk_count_wire = chunk_count as u32;
            let mut pair_chunk_wire = pair_chunk as u32;
            let mut relational_pair_count_wire = pair_population as u32;
            let mut relational_factor_count_wire = factor_count as u32;
            let mut relational_face_count_wire = face_population as u32;
            let mut relational_source_state_count_wire = source_state_population as u32;
            let mut relational_port_count_wire = port_population as u32;
            let mut relational_generator_count_wire = generator_population as u32;
            let mut relational_current_limb_count_wire = target_limb_count as u32;
            let mut relational_restriction_limb_count_wire = restriction_limb_count as u32;
            let mut relational_limb_count_wire = relational_limb_count as u32;
            let mut relational_state_count_wire = relational_state_count as u32;
            let mut transported_relational_limb_count_wire =
                transported_relational_limb_count as u32;
            let mut relational_pair_factors = pair_factors;
            let mut relational_current = target_limbs_pointer;
            let mut form_arguments: [*mut c_void; 30] = [
                &mut transported_relational_real_sign_pointer as *mut u64 as *mut c_void,
                &mut transported_relational_real_limbs_pointer as *mut u64 as *mut c_void,
                &mut transported_relational_imaginary_sign_pointer as *mut u64 as *mut c_void,
                &mut transported_relational_imaginary_limbs_pointer as *mut u64 as *mut c_void,
                &mut relational_state_present as *mut u64 as *mut c_void,
                &mut relational_states as *mut u64 as *mut c_void,
                &mut source_state_ids as *mut u64 as *mut c_void,
                &mut relational_pair_factors as *mut u64 as *mut c_void,
                &mut relational_current as *mut u64 as *mut c_void,
                &mut restrictions_pointer as *mut u64 as *mut c_void,
                &mut restriction_present_for_relational as *mut u64 as *mut c_void,
                &mut partial_sign_pointer as *mut u64 as *mut c_void,
                &mut partial_limb_pointer as *mut u64 as *mut c_void,
                &mut first_scratch_pointer as *mut u64 as *mut c_void,
                &mut second_scratch_pointer as *mut u64 as *mut c_void,
                &mut third_scratch_pointer as *mut u64 as *mut c_void,
                &mut relational_pair_count_wire as *mut u32 as *mut c_void,
                &mut relational_factor_count_wire as *mut u32 as *mut c_void,
                &mut relational_face_count_wire as *mut u32 as *mut c_void,
                &mut relational_source_state_count_wire as *mut u32 as *mut c_void,
                &mut relational_port_count_wire as *mut u32 as *mut c_void,
                &mut relational_generator_count_wire as *mut u32 as *mut c_void,
                &mut relational_state_count_wire as *mut u32 as *mut c_void,
                &mut transported_relational_limb_count_wire as *mut u32 as *mut c_void,
                &mut chunk_count_wire as *mut u32 as *mut c_void,
                &mut pair_chunk_wire as *mut u32 as *mut c_void,
                &mut relational_current_limb_count_wire as *mut u32 as *mut c_void,
                &mut relational_restriction_limb_count_wire as *mut u32 as *mut c_void,
                &mut relational_limb_count_wire as *mut u32 as *mut c_void,
                &mut relational_obstruction as *mut u64 as *mut c_void,
            ];
            driver(
                unsafe {
                    cuLaunchKernel(
                        form_relational,
                        self.card.grid_for(work_population as u64)?,
                        1,
                        1,
                        self.card.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        form_arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(form_membrane_sparse_relational_boundary_chunks_arbitrary)",
            )?;
            if trace_configuration().holonics_phase_trace {
                let diagnostic_sections = 3_usize;
                let diagnostic_partials = diagnostic_sections * chunk_count;
                let mut signs = vec![0_u8; diagnostic_partials];
                let mut limbs = vec![0_u32; diagnostic_partials * relational_limb_count];
                partial_signs.read(&mut signs)?;
                partial_limbs.read(&mut limbs)?;
                let axis_support = (0..diagnostic_sections)
                    .map(|axis| {
                        let begin = axis * chunk_count;
                        signs[begin..begin + chunk_count]
                            .iter()
                            .filter(|sign| **sign != 0)
                            .count()
                    })
                    .collect::<Vec<_>>();
                eprintln!("uar2-relational-first-face-partials support={axis_support:?}");
            }
            let reduce_launches = self.reduce_sparse_quadratic_signed_sections(
                &partial_signs,
                &partial_limbs,
                &reduce_signs,
                &reduce_limbs,
                &final_signs,
                &final_limbs,
                section_count,
                chunk_count,
                relational_limb_count,
            )?;
            let mut final_sign_pointer = final_signs.pointer;
            let mut final_limb_pointer = final_limbs.pointer;
            let mut compatibility_sign_pointer = compatibility_signs.pointer;
            let mut compatibility_limb_pointer = compatibility_limbs.pointer;
            let mut transported_norm_pointer = relational_transported_norm_limbs.pointer;
            let mut ingress_norm_pointer = relational_ingress_norm_limbs.pointer;
            let mut relational_scatter_arguments: [*mut c_void; 8] = [
                &mut final_sign_pointer as *mut u64 as *mut c_void,
                &mut final_limb_pointer as *mut u64 as *mut c_void,
                &mut compatibility_sign_pointer as *mut u64 as *mut c_void,
                &mut compatibility_limb_pointer as *mut u64 as *mut c_void,
                &mut transported_norm_pointer as *mut u64 as *mut c_void,
                &mut ingress_norm_pointer as *mut u64 as *mut c_void,
                &mut relational_face_count_wire as *mut u32 as *mut c_void,
                &mut relational_limb_count_wire as *mut u32 as *mut c_void,
            ];
            driver(
                unsafe {
                    cuLaunchKernel(
                        scatter_relational,
                        self.card.grid_for(face_population as u64)?,
                        1,
                        1,
                        self.card.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        relational_scatter_arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(scatter_membrane_sparse_relational_boundary)",
            )?;
            let launches = reduce_launches.saturating_add(3);
            let mut identity = Sha256::new();
            identity.update(b"holonic-engine.sparse-relational-addressed-hermitian-boundary.v2");
            identity.update(returned_current_identity_sha256.as_bytes());
            identity.update(source_address.section_identity_sha256.as_bytes());
            for state in &boundary.boundary_states {
                identity.update(state.to_le_bytes());
            }
            for port in &boundary.universal_ports {
                identity.update(port.to_le_bytes());
            }
            let identity_sha256 = identity
                .finalize()
                .iter()
                .map(|octet| format!("{octet:02x}"))
                .collect::<String>();
            let resident_octets = [
                face_population,
                octets(face_population, relational_limb_count)?,
                octets(face_population, relational_limb_count)?,
                octets(face_population, relational_limb_count)?,
            ]
            .into_iter()
            .try_fold(0_u64, |sum, value| {
                sum.checked_add(u64::try_from(value).ok()?)
            })
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            let working_octets = [
                partial_population,
                octets(partial_population, relational_limb_count)?,
                reduce_population,
                octets(reduce_population, relational_limb_count)?,
                section_count,
                octets(section_count, relational_limb_count)?,
                octets(work_population, relational_limb_count)?,
                octets(work_population, relational_limb_count)?,
                octets(work_population, relational_limb_count)?,
                transported_factor_population,
                transported_factor_limb_octets,
                transported_factor_population,
                transported_factor_limb_octets,
            ]
            .into_iter()
            .try_fold(0_u64, |sum, value| {
                sum.checked_add(u64::try_from(value).ok()?)
            })
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            Some(ResidentSparseRelationalBoundaryReceiver {
                identity_sha256,
                limb_count: relational_limb_count as u32,
                compatibility_bound,
                compatibility_signs,
                compatibility_limbs,
                transported_norm_bound,
                transported_norm_limbs: relational_transported_norm_limbs,
                ingress_norm_bound,
                ingress_norm_limbs: relational_ingress_norm_limbs,
                resident_octets,
                working_octets,
                launches,
                work_buffers: vec![
                    partial_signs,
                    partial_limbs,
                    reduce_signs,
                    reduce_limbs,
                    final_signs,
                    final_limbs,
                    first_scratch,
                    second_scratch,
                    third_scratch,
                    transported_relational_real_sign,
                    transported_relational_real_limbs,
                    transported_relational_imaginary_sign,
                    transported_relational_imaginary_limbs,
                ],
            })
        } else {
            None
        };
        if let Some(receiver) = relational_receiver.as_ref() {
            let relational = self
                .sparse_relational_current
                .as_mut()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            relational.receipt.addressed_target_receiver_joined = true;
            relational.receipt.launches = relational
                .receipt
                .launches
                .checked_add(receiver.launches)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            relational.receipt.device_dependency_edges = relational
                .receipt
                .device_dependency_edges
                .checked_add(receiver.launches)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            relational.receipt.resident_working_octets = relational
                .receipt
                .resident_working_octets
                .checked_add(receiver.resident_octets)
                .and_then(|held| held.checked_add(receiver.working_octets))
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        }

        let support_ports_host = face_ports_host.clone();
        let support_receiver_classes_host = (0..face_population as u32).collect::<Vec<_>>();
        let support_quadratic_scales_host = vec![1_u32; face_population];
        let support_ports = Buffer::of(&support_ports_host)?;
        let support_receiver_classes = Buffer::of(&support_receiver_classes_host)?;
        let support_quadratic_scales = Buffer::of(&support_quadratic_scales_host)?;
        let mut boundary_identity = Sha256::new();
        boundary_identity.update(b"holonic-engine.sparse-quadratic-native-boundary.v2");
        boundary_identity.update(source_address.section_identity_sha256.as_bytes());
        boundary_identity.update(restriction_atlas_identity.as_bytes());
        for state in &boundary.boundary_states {
            boundary_identity.update(state.to_le_bytes());
        }
        for port in &boundary.universal_ports {
            boundary_identity.update(port.to_le_bytes());
        }
        let boundary_identity = boundary_identity
            .finalize()
            .iter()
            .map(|octet| format!("{octet:02x}"))
            .collect::<String>();
        let mut occurrence = Sha256::new();
        occurrence.update(b"holonic-engine.sparse-quadratic-native-boundary-receiver.v1");
        occurrence.update(boundary_identity.as_bytes());
        let receiver_identity = occurrence
            .finalize()
            .iter()
            .map(|octet| format!("{octet:02x}"))
            .collect::<String>();
        let mut lineage = Sha256::new();
        lineage.update(b"holonic-engine.sparse-quadratic-pair-section.v1");
        lineage.update(source_address.section_identity_sha256.as_bytes());
        lineage.update(source_address.generation.saturating_add(1).to_le_bytes());
        let section_lineage_identity_sha256 = lineage
            .finalize()
            .iter()
            .map(|octet| format!("{octet:02x}"))
            .collect::<String>();
        let persistent_octets = [
            restriction_octets,
            face_population,
            face_population * std::mem::size_of::<u32>(),
            std::mem::size_of_val(support_ports_host.as_slice()),
            std::mem::size_of_val(support_receiver_classes_host.as_slice()),
            std::mem::size_of_val(support_quadratic_scales_host.as_slice()),
            receiver_population,
            octets(receiver_population, output_limb_count)?,
            face_population,
            octets(face_population, output_limb_count)?,
            octets(face_population, output_limb_count)?,
            octets(face_population, output_limb_count)?,
        ]
        .into_iter()
        .try_fold(0_u64, |sum, value| {
            sum.checked_add(u64::try_from(value).ok()?)
        })
        .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?
        .checked_add(
            relational_receiver
                .as_ref()
                .map(|receiver| receiver.resident_octets)
                .unwrap_or(0),
        )
        .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let working_octets = [
            std::mem::size_of_val(boundary.boundary_states.as_slice()),
            std::mem::size_of_val(boundary.universal_ports.as_slice()),
            family_reduce_population,
            octets(family_reduce_population, output_limb_count)?,
            family_partial_population,
            octets(family_partial_population, output_limb_count)?,
            family_sections,
            octets(family_sections, output_limb_count)?,
            octets(family_work, output_limb_count)?,
            octets(family_work, output_limb_count)?,
            potential_reduce_population,
            octets(potential_reduce_population, output_limb_count)?,
            potential_partial_population,
            octets(potential_partial_population, output_limb_count)?,
            potential_sections,
            octets(potential_sections, output_limb_count)?,
            octets(potential_work, output_limb_count)?,
            octets(potential_work, output_limb_count)?,
        ]
        .into_iter()
        .try_fold(0_u64, |sum, value| {
            sum.checked_add(u64::try_from(value).ok()?)
        })
        .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?
        .checked_add(
            relational_receiver
                .as_ref()
                .map(|receiver| receiver.working_octets)
                .unwrap_or(0),
        )
        .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let receiver_launches = 5_u64
            .checked_add(family_reduce_launches)
            .and_then(|held| held.checked_add(potential_reduce_launches))
            .and_then(|held| {
                held.checked_add(
                    relational_receiver
                        .as_ref()
                        .map(|receiver| receiver.launches)
                        .unwrap_or(0),
                )
            })
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        self.card.launches = self
            .card
            .launches
            .checked_add(receiver_launches)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let receiver = ResidentFactoredMomentReceiverState {
            identity_sha256: receiver_identity,
            section_lineage_identity_sha256: section_lineage_identity_sha256.clone(),
            frame_identity_sha256: boundary_identity.clone(),
            receiver_population: receiver_population as u32,
            output_limb_count: output_limb_count as u32,
            output_bound: receiver_output_bound.clone(),
            output_denominator: Some(BigInt::one()),
            output_signs,
            output_limbs,
            launches: receiver_launches,
            apparatus_shape_host_egress_octets: 0,
            resident_octets: persistent_octets,
        };
        let admitted = Buffer::of(&[1_u32])?;
        let signs = Buffer::alloc(pair_population)?;
        signs.fill(0, pair_population)?;
        let native_boundary = ResidentSparseQuadraticNativeBoundary {
            identity_sha256: boundary_identity,
            port_population: port_population as u32,
            face_population: face_population as u32,
            face_ports_host,
            face_generators_host,
            face_source_states_host,
            restriction_limb_count: restriction_limb_count as u32,
            maximal_restriction,
            restrictions,
            restriction_present,
            restriction_target_states,
            support_ports,
            support_ports_host,
            support_receiver_classes,
            support_quadratic_scales,
            situated_limb_count: output_limb_count as u32,
            situated_bound,
            situated_signs,
            situated_limbs,
            situated_current_norm_bound,
            situated_current_norm_limbs,
            situated_ingress_norm_bound,
            situated_ingress_norm_limbs,
            relational_receiver,
            resident_octets: persistent_octets,
            working_octets,
            work_buffers: vec![
                universal_ports_device,
                family_partial_signs,
                family_partial_limbs,
                family_reduce_signs,
                family_reduce_limbs,
                family_final_signs,
                family_final_limbs,
                family_product_scratch,
                family_scaled_scratch,
                potential_partial_signs,
                potential_partial_limbs,
                potential_reduce_signs,
                potential_reduce_limbs,
                potential_final_signs,
                potential_final_limbs,
                potential_first_scratch,
                potential_second_scratch,
            ],
        };
        let transport_identity_sha256 = section_lineage_identity_sha256;
        self.factored_receiver_history
            .as_mut()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?
            .transported_image = Some(ResidentTransportedFactoredMomentIncidence {
            transport_identity_sha256,
            source_address: source_address.clone(),
            target_generation: source_address.generation.saturating_add(1),
            generator_population: generator_population as u32,
            transported_row_population: pair_population as u32,
            factor_population: source_address.factor_population,
            numerator_limb_count: target_limb_count as u32,
            maximal_numerator: BigInt::from(maximal_target),
            signs,
            limbs: target_limbs,
            overflow,
            productive_admitted: admitted,
            productive_receiver: Some(receiver),
            constitutive_spine: None,
            productive_history: None,
            rank_atlas: None,
            sparse_conditioned: None,
            sparse_native_boundary: Some(native_boundary),
            resident_octets: u64::try_from(target_octets.saturating_add(pair_population))
                .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
            sparse_pair_completion: true,
        });
        if trace_configuration().holonics_profile_sync {
            let began = std::time::Instant::now();
            driver(
                unsafe { cuCtxSynchronize() },
                "cuCtxSynchronize(profile native boundary)",
            )?;
            eprintln!(
                "uar2-profile-native-boundary-sync milliseconds={}",
                began.elapsed().as_millis(),
            );
        }
        let address = self.resident_factored_moment_receiver_address()?;
        if trace_configuration().holonics_phase_trace {
            eprintln!(
                "uar2-native-boundary-staged source-generation={} target-generation={} receiver-population={}",
                address.source_generation, address.target_generation, address.receiver_population,
            );
        }
        Ok(address)
    }
}
