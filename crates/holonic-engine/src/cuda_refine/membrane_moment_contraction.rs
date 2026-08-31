use super::membrane_moment_execution::{MomentContractionLaunch, MomentFrontExecution};
use super::*;

// CUDA argument arrays retain pointers to these wires; Rust cannot observe the device reads.
#[allow(unused_assignments)]
pub(super) fn launch(
    word: &ResidentMembraneInteriorWord,
    front: &ResidentQuadraticMomentFront,
    port_population: usize,
    completed_step: Option<&ResidentCompletedTargetObservationAperture>,
    execution: &MomentFrontExecution<'_>,
) -> Result<MomentContractionLaunch, CudaRefineError> {
    let plan = &execution.plan;
    let workspace = &execution.workspace;
    let post_target_observer = execution.post_target_observer;
    let materialize_moment_field = execution.materialize_moment_field;
    let cuda_profile = execution.cuda_profile;
    let resident_rectangular_restrictions = plan.resident_rectangular_restrictions;
    let resident_atlas = if resident_rectangular_restrictions {
        Some(
            word.boundary_restriction_atlas
                .as_ref()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?,
        )
    } else {
        None
    };
    let factor_receiver_observations = word
        .factor_receiver_observations
        .as_ref()
        .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
    let quadratic_action = word
        .quadratic_action
        .as_ref()
        .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
    let octets = |population: usize, limbs: usize| {
        population
            .checked_mul(limbs)
            .and_then(|words| words.checked_mul(std::mem::size_of::<u32>()))
            .ok_or(CudaRefineError::MembraneInteriorWordShape)
    };

    let axis_count = plan.axis_count;
    let compatibility_limb_count = plan.compatibility_limb_count;
    let contact_limb_count = plan.contact_limb_count;
    let context_chunk_count = plan.context_chunk_count;
    let context_chunk_size = plan.context_chunk_size;
    let context_count = plan.context_count;
    let context_limb_count = plan.context_limb_count;
    let contraction_work = plan.contraction_work;
    let contribution_work = plan.contribution_work;
    let descend_boundary_state_receiver = plan.descend_boundary_state_receiver;
    let factors = plan.factors;
    let generator_count = plan.generator_count;
    let incidence_chunk_count = plan.incidence_chunk_count;
    let incidence_chunk_size = plan.incidence_chunk_size;
    let local_response_population = plan.local_response_population;
    let maximal_context = &plan.maximal_context;
    let moment_limb_count = plan.moment_limb_count;
    let moment_population = plan.moment_population;
    let native_factors = plan.native_factors;
    let overlap_limb_count = plan.overlap_limb_count;
    let product_limb_count = plan.product_limb_count;
    let quadratic_limb_count = plan.quadratic_limb_count;
    let relational_current_aperture = &plan.relational_current_aperture;
    let resident_boundary = plan.resident_boundary;
    let resident_context_state = &plan.resident_context_state;
    let response_population = plan.response_population;
    let restriction_count = plan.restriction_count;
    let restriction_limb_count = plan.restriction_limb_count;
    let weight_limb_count = plan.weight_limb_count;

    let action_limbs = &workspace.action_limbs;
    let action_sign = &workspace.action_sign;
    let active_factor_chart = &workspace.active_factor_chart;
    let boundary_states_device = &workspace.boundary_states_device;
    let contact_imaginary_limbs = &workspace.contact_imaginary_limbs;
    let contact_imaginary_sign = &workspace.contact_imaginary_sign;
    let contact_real_limbs = &workspace.contact_real_limbs;
    let contact_real_sign = &workspace.contact_real_sign;
    let context_current = &workspace.context_current;
    let context_state_present = &workspace.context_state_present;
    let context_states = &workspace.context_states;
    let context_weight = &workspace.context_weight;
    let contribution_action_limbs = &workspace.contribution_action_limbs;
    let contribution_action_sign = &workspace.contribution_action_sign;
    let contribution_receiver_limbs = &workspace.contribution_receiver_limbs;
    let contribution_receiver_norm_limbs = &workspace.contribution_receiver_norm_limbs;
    let contribution_receiver_norm_sign = &workspace.contribution_receiver_norm_sign;
    let contribution_receiver_sign = &workspace.contribution_receiver_sign;
    let contribution_reflected_limbs = &workspace.contribution_reflected_limbs;
    let contribution_reflected_sign = &workspace.contribution_reflected_sign;
    let factorized_bucket_scratch = &workspace.factorized_bucket_scratch;
    let factorized_left_scratch = &workspace.factorized_left_scratch;
    let factorized_overlap_scratch = &workspace.factorized_overlap_scratch;
    let factorized_quadratic_scratch = &workspace.factorized_quadratic_scratch;
    let factorized_relational_workspace = &workspace.factorized_relational_workspace;
    let factorized_right_scratch = &workspace.factorized_right_scratch;
    let factorized_term_scratch = &workspace.factorized_term_scratch;
    let generator_local_targets = &workspace.generator_local_targets;
    let generator_targets = &workspace.generator_targets;
    let left_scratch = &workspace.left_scratch;
    let moment = &workspace.moment;
    let overlap_scratch = &workspace.overlap_scratch;
    let port_restriction_offset = &workspace.port_restriction_offset;
    let quadratic_scratch = &workspace.quadratic_scratch;
    let receiver_limbs = &workspace.receiver_limbs;
    let receiver_norm_limbs = &workspace.receiver_norm_limbs;
    let receiver_norm_sign = &workspace.receiver_norm_sign;
    let receiver_sign = &workspace.receiver_sign;
    let reflected_limbs = &workspace.reflected_limbs;
    let reflected_sign = &workspace.reflected_sign;
    let restriction_current = &workspace.restriction_current;
    let restriction_port = &workspace.restriction_port;
    let restriction_present = &workspace.restriction_present;
    let restriction_target_states = &workspace.restriction_target_states;
    let right_scratch = &workspace.right_scratch;
    let term_scratch = &workspace.term_scratch;
    let universal_ports_device = &workspace.universal_ports_device;

    let mut context_current_pointer = resident_context_state
        .as_ref()
        .map(|state| state.current_limbs_pointer)
        .or_else(|| context_current.as_ref().map(|buffer| buffer.pointer))
        .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
    let mut context_weight_pointer = resident_context_state
        .as_ref()
        .map(|state| state.weight_limbs_pointer)
        .or_else(|| context_weight.as_ref().map(|buffer| buffer.pointer))
        .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
    let mut context_state_present_pointer = resident_context_state
        .as_ref()
        .map(|state| state.boundary_state_present_pointer)
        .or_else(|| context_state_present.as_ref().map(|buffer| buffer.pointer))
        .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
    let mut context_states_pointer = resident_context_state
        .as_ref()
        .map(|state| state.boundary_states_pointer)
        .or_else(|| context_states.as_ref().map(|buffer| buffer.pointer))
        .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
    let mut restriction_port_pointer = restriction_port.pointer;
    let mut restriction_current_pointer = restriction_current.pointer;
    let mut moment_pointer = moment.pointer;
    let mut left_scratch_pointer = left_scratch.pointer;
    let mut right_scratch_pointer = right_scratch.pointer;
    let mut quadratic_scratch_pointer = quadratic_scratch.pointer;
    let mut term_scratch_pointer = term_scratch.pointer;
    let mut context_count_wire = context_count as u32;
    let mut restriction_count_wire = restriction_count as u32;
    let mut port_count_wire = port_population as u32;
    let mut factor_count_wire = factors as u32;
    let mut context_limb_count_wire = context_limb_count as u32;
    let mut restriction_limb_count_wire = restriction_limb_count as u32;
    let mut weight_limb_count_wire = weight_limb_count as u32;
    let mut product_limb_count_wire = product_limb_count as u32;
    let mut quadratic_limb_count_wire = quadratic_limb_count as u32;
    let mut moment_limb_count_wire = moment_limb_count as u32;
    let mut resident_gather_launches = 0_u64;
    if !post_target_observer {
        if let (Some(boundary), Some(atlas)) = (resident_boundary, resident_atlas) {
            let mut state_port_transition_pointer = atlas.state_port_transition.pointer;
            let mut transition_targets_pointer = atlas.transition_targets.pointer;
            let mut transition_factor_offset_pointer = atlas.transition_factor_offsets.pointer;
            let mut transition_factor_pointer = atlas.transition_factors.pointer;
            let mut transition_current_pointer = atlas.transition_current_limbs.pointer;
            let mut boundary_states_pointer = boundary_states_device.pointer;
            let mut universal_ports_pointer = universal_ports_device.pointer;
            let mut restriction_present_pointer = restriction_present.pointer;
            let mut restriction_target_states_pointer = restriction_target_states.pointer;
            let mut boundary_state_count_wire = boundary.boundary_states.len() as u32;
            let mut atlas_state_count_wire = atlas.state_count;
            let mut universal_port_count_wire = atlas.universal_port_count;
            let mut native_factor_count_wire = word.factors;
            let mut gather_arguments: [*mut c_void; 16] = [
                &mut state_port_transition_pointer as *mut u64 as *mut c_void,
                &mut transition_targets_pointer as *mut u64 as *mut c_void,
                &mut transition_factor_offset_pointer as *mut u64 as *mut c_void,
                &mut transition_factor_pointer as *mut u64 as *mut c_void,
                &mut transition_current_pointer as *mut u64 as *mut c_void,
                &mut boundary_states_pointer as *mut u64 as *mut c_void,
                &mut universal_ports_pointer as *mut u64 as *mut c_void,
                &mut restriction_current_pointer as *mut u64 as *mut c_void,
                &mut restriction_present_pointer as *mut u64 as *mut c_void,
                &mut restriction_target_states_pointer as *mut u64 as *mut c_void,
                &mut boundary_state_count_wire as *mut u32 as *mut c_void,
                &mut port_count_wire as *mut u32 as *mut c_void,
                &mut atlas_state_count_wire as *mut u32 as *mut c_void,
                &mut universal_port_count_wire as *mut u32 as *mut c_void,
                &mut native_factor_count_wire as *mut u32 as *mut c_void,
                &mut restriction_limb_count_wire as *mut u32 as *mut c_void,
            ];
            let gather_grid = word.card.grid_for(restriction_count as u64)?;
            driver(
                unsafe {
                    cuLaunchKernel(
                        word.card.membrane_resident_boundary_restriction_gather,
                        gather_grid,
                        1,
                        1,
                        word.card.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        gather_arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(gather_membrane_resident_boundary_restrictions)",
            )?;
            resident_gather_launches = 1;
        }
    }
    let mut form_arguments: [*mut c_void; 19] = [
        &mut context_current_pointer as *mut u64 as *mut c_void,
        &mut context_weight_pointer as *mut u64 as *mut c_void,
        &mut restriction_port_pointer as *mut u64 as *mut c_void,
        &mut restriction_current_pointer as *mut u64 as *mut c_void,
        &mut moment_pointer as *mut u64 as *mut c_void,
        &mut left_scratch_pointer as *mut u64 as *mut c_void,
        &mut right_scratch_pointer as *mut u64 as *mut c_void,
        &mut quadratic_scratch_pointer as *mut u64 as *mut c_void,
        &mut term_scratch_pointer as *mut u64 as *mut c_void,
        &mut context_count_wire as *mut u32 as *mut c_void,
        &mut restriction_count_wire as *mut u32 as *mut c_void,
        &mut port_count_wire as *mut u32 as *mut c_void,
        &mut factor_count_wire as *mut u32 as *mut c_void,
        &mut context_limb_count_wire as *mut u32 as *mut c_void,
        &mut restriction_limb_count_wire as *mut u32 as *mut c_void,
        &mut weight_limb_count_wire as *mut u32 as *mut c_void,
        &mut product_limb_count_wire as *mut u32 as *mut c_void,
        &mut quadratic_limb_count_wire as *mut u32 as *mut c_void,
        &mut moment_limb_count_wire as *mut u32 as *mut c_void,
    ];
    if materialize_moment_field {
        let moment_grid = word.card.grid_for(moment_population as u64)?;
        driver(
            unsafe {
                cuLaunchKernel(
                    word.card.membrane_quadratic_moment_form,
                    moment_grid,
                    1,
                    1,
                    word.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    form_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(form_membrane_quadratic_moments)",
        )?;
    }

    let mut active_factor_chart_pointer = active_factor_chart.pointer;
    let mut generator_targets_pointer = generator_targets.pointer;
    let mut generator_local_targets_pointer = generator_local_targets.pointer;
    let mut factor_receiver_observations_pointer = factor_receiver_observations.pointer;
    let mut factor_capacity_pointer = word.factor_capacity.pointer;
    let mut family_orientation_pointer = word.family_orientation.pointer;
    let mut family_real_sign_pointer = word.family_real_sign.pointer;
    let mut family_real_limbs_pointer = word.family_real_limbs.pointer;
    let mut family_imaginary_sign_pointer = word.family_imaginary_sign.pointer;
    let mut family_imaginary_limbs_pointer = word.family_imaginary_limbs.pointer;
    let mut action_sign_pointer = action_sign.pointer;
    let mut action_limbs_pointer = action_limbs.pointer;
    let mut reflected_sign_pointer = reflected_sign.pointer;
    let mut reflected_limbs_pointer = reflected_limbs.pointer;
    let mut receiver_sign_pointer = receiver_sign.pointer;
    let mut receiver_limbs_pointer = receiver_limbs.pointer;
    let mut receiver_norm_sign_pointer = receiver_norm_sign.pointer;
    let mut receiver_norm_limbs_pointer = receiver_norm_limbs.pointer;
    let mut contact_real_sign_pointer = contact_real_sign.pointer;
    let mut contact_real_limbs_pointer = contact_real_limbs.pointer;
    let mut contact_imaginary_sign_pointer = contact_imaginary_sign.pointer;
    let mut contact_imaginary_limbs_pointer = contact_imaginary_limbs.pointer;
    let mut overlap_scratch_pointer = overlap_scratch.pointer;
    let mut generator_count_wire = front.generator_count;
    let mut native_factor_count_wire = word.factors;
    let mut family_count_wire = word.families;
    let mut receiver_count_wire = word.receiver_count;
    let mut overlap_limb_count_wire = overlap_limb_count as u32;
    let mut family_limb_count_wire = word.family_limb_count;
    let mut contact_limb_count_wire = contact_limb_count as u32;
    let mut contract_arguments: [*mut c_void; 34] = [
        &mut moment_pointer as *mut u64 as *mut c_void,
        &mut active_factor_chart_pointer as *mut u64 as *mut c_void,
        &mut generator_targets_pointer as *mut u64 as *mut c_void,
        &mut generator_local_targets_pointer as *mut u64 as *mut c_void,
        &mut factor_receiver_observations_pointer as *mut u64 as *mut c_void,
        &mut factor_capacity_pointer as *mut u64 as *mut c_void,
        &mut family_orientation_pointer as *mut u64 as *mut c_void,
        &mut family_real_sign_pointer as *mut u64 as *mut c_void,
        &mut family_real_limbs_pointer as *mut u64 as *mut c_void,
        &mut family_imaginary_sign_pointer as *mut u64 as *mut c_void,
        &mut family_imaginary_limbs_pointer as *mut u64 as *mut c_void,
        &mut action_sign_pointer as *mut u64 as *mut c_void,
        &mut action_limbs_pointer as *mut u64 as *mut c_void,
        &mut reflected_sign_pointer as *mut u64 as *mut c_void,
        &mut reflected_limbs_pointer as *mut u64 as *mut c_void,
        &mut receiver_sign_pointer as *mut u64 as *mut c_void,
        &mut receiver_limbs_pointer as *mut u64 as *mut c_void,
        &mut receiver_norm_sign_pointer as *mut u64 as *mut c_void,
        &mut receiver_norm_limbs_pointer as *mut u64 as *mut c_void,
        &mut contact_real_sign_pointer as *mut u64 as *mut c_void,
        &mut contact_real_limbs_pointer as *mut u64 as *mut c_void,
        &mut contact_imaginary_sign_pointer as *mut u64 as *mut c_void,
        &mut contact_imaginary_limbs_pointer as *mut u64 as *mut c_void,
        &mut overlap_scratch_pointer as *mut u64 as *mut c_void,
        &mut port_count_wire as *mut u32 as *mut c_void,
        &mut factor_count_wire as *mut u32 as *mut c_void,
        &mut native_factor_count_wire as *mut u32 as *mut c_void,
        &mut generator_count_wire as *mut u32 as *mut c_void,
        &mut family_count_wire as *mut u32 as *mut c_void,
        &mut receiver_count_wire as *mut u32 as *mut c_void,
        &mut moment_limb_count_wire as *mut u32 as *mut c_void,
        &mut overlap_limb_count_wire as *mut u32 as *mut c_void,
        &mut family_limb_count_wire as *mut u32 as *mut c_void,
        &mut contact_limb_count_wire as *mut u32 as *mut c_void,
    ];
    let contract_grid = word.card.grid_for(contraction_work as u64)?;
    let mut completed_target_observer_workspace = None;
    if post_target_observer {
        let aperture = completed_step
            .as_ref()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let (
            _,
            _,
            _,
            target_relational_state_count,
            target_relational_real_sign_pointer,
            target_relational_real_limbs_pointer,
            target_relational_imaginary_sign_pointer,
            target_relational_imaginary_limbs_pointer,
            target_relational_limb_count,
            returned_relational_bound,
        ) = relational_current_aperture
            .as_ref()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        if aperture.local_face_population != response_population
            || *target_relational_state_count != context_count
            || aperture.candidate_count == 0
            || aperture.selected_slot_count == 0
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let face_current_bound = maximal_context * BigUint::from(aperture.candidate_count);
        let face_relational_bound =
            returned_relational_bound * BigUint::from(aperture.candidate_count);
        let face_current_limb_count = face_current_bound.to_u32_digits().len().max(1);
        let face_relational_limb_count = face_relational_bound.to_u32_digits().len().max(1);
        let observer_limb_count = compatibility_limb_count;
        let face_factor_population = response_population
            .checked_mul(native_factors)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let observer_work = response_population
            .checked_mul(axis_count)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let membrane_moment_workspace::MomentCompletedTargetObserverBuffers {
            face_current,
            face_relational_real_sign,
            face_relational_real_limbs,
            face_relational_imaginary_sign,
            face_relational_imaginary_limbs,
            relational_dot_real_sign,
            relational_dot_real_limbs,
            relational_dot_imaginary_sign,
            relational_dot_imaginary_limbs,
            target_norm_limbs,
            relational_norm_limbs,
            norm_product_limbs,
            first_scratch,
            second_scratch,
            third_scratch,
            obstruction,
        } = membrane_moment_workspace::allocate_completed_target_observer(
            response_population,
            face_factor_population,
            face_current_limb_count,
            face_relational_limb_count,
            observer_limb_count,
            observer_work,
        )?;

        let mut pushforward = ptr::null_mut();
        driver(
            unsafe {
                cuModuleGetFunction(
                    &mut pushforward,
                    word.card.module,
                    c"pushforward_membrane_completed_target_observer_current".as_ptr(),
                )
            },
            "cuModuleGetFunction(pushforward_membrane_completed_target_observer_current)",
        )?;
        let mut selected_faces_pointer = aperture.selected_faces.pointer;
        let mut target_relational_real_sign_pointer = *target_relational_real_sign_pointer;
        let mut target_relational_real_limbs_pointer = *target_relational_real_limbs_pointer;
        let mut target_relational_imaginary_sign_pointer =
            *target_relational_imaginary_sign_pointer;
        let mut target_relational_imaginary_limbs_pointer =
            *target_relational_imaginary_limbs_pointer;
        let mut candidate_selected_slots_pointer = aperture.candidate_selected_slots.pointer;
        let mut candidate_to_target_pointer = aperture.candidate_to_target.pointer;
        let mut face_current_pointer = face_current.pointer;
        let mut face_relational_real_sign_pointer = face_relational_real_sign.pointer;
        let mut face_relational_real_limbs_pointer = face_relational_real_limbs.pointer;
        let mut face_relational_imaginary_sign_pointer = face_relational_imaginary_sign.pointer;
        let mut face_relational_imaginary_limbs_pointer = face_relational_imaginary_limbs.pointer;
        let mut observer_obstruction_pointer = obstruction.pointer;
        let mut target_count_wire = context_count as u32;
        let mut selected_slot_count_wire = aperture.selected_slot_count as u32;
        let mut candidate_count_wire = aperture.candidate_count as u32;
        let mut observer_face_count_wire = response_population as u32;
        let mut target_relational_limb_count_wire = *target_relational_limb_count as u32;
        let mut face_current_limb_count_wire = face_current_limb_count as u32;
        let mut face_relational_limb_count_wire = face_relational_limb_count as u32;
        let mut pushforward_arguments: [*mut c_void; 23] = [
            &mut context_current_pointer as *mut u64 as *mut c_void,
            &mut target_relational_real_sign_pointer as *mut u64 as *mut c_void,
            &mut target_relational_real_limbs_pointer as *mut u64 as *mut c_void,
            &mut target_relational_imaginary_sign_pointer as *mut u64 as *mut c_void,
            &mut target_relational_imaginary_limbs_pointer as *mut u64 as *mut c_void,
            &mut selected_faces_pointer as *mut u64 as *mut c_void,
            &mut candidate_selected_slots_pointer as *mut u64 as *mut c_void,
            &mut candidate_to_target_pointer as *mut u64 as *mut c_void,
            &mut face_current_pointer as *mut u64 as *mut c_void,
            &mut face_relational_real_sign_pointer as *mut u64 as *mut c_void,
            &mut face_relational_real_limbs_pointer as *mut u64 as *mut c_void,
            &mut face_relational_imaginary_sign_pointer as *mut u64 as *mut c_void,
            &mut face_relational_imaginary_limbs_pointer as *mut u64 as *mut c_void,
            &mut observer_obstruction_pointer as *mut u64 as *mut c_void,
            &mut target_count_wire as *mut u32 as *mut c_void,
            &mut native_factor_count_wire as *mut u32 as *mut c_void,
            &mut selected_slot_count_wire as *mut u32 as *mut c_void,
            &mut candidate_count_wire as *mut u32 as *mut c_void,
            &mut observer_face_count_wire as *mut u32 as *mut c_void,
            &mut context_limb_count_wire as *mut u32 as *mut c_void,
            &mut target_relational_limb_count_wire as *mut u32 as *mut c_void,
            &mut face_current_limb_count_wire as *mut u32 as *mut c_void,
            &mut face_relational_limb_count_wire as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    pushforward,
                    word.card.grid_for(face_factor_population as u64)?,
                    1,
                    1,
                    word.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    pushforward_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(pushforward_membrane_completed_target_observer_current)",
        )?;

        let mut contract_completed = ptr::null_mut();
        driver(
            unsafe {
                cuModuleGetFunction(
                    &mut contract_completed,
                    word.card.module,
                    c"contract_membrane_completed_target_observer".as_ptr(),
                )
            },
            "cuModuleGetFunction(contract_membrane_completed_target_observer)",
        )?;
        let mut receiver_class_base_pointer = quadratic_action.receiver_class_bases.pointer;
        let mut source_class_factor_offset_pointer =
            quadratic_action.source_class_factor_offsets.pointer;
        let mut source_class_factor_pointer = quadratic_action.source_class_factors.pointer;
        let mut relational_dot_real_sign_pointer = relational_dot_real_sign.pointer;
        let mut relational_dot_real_limbs_pointer = relational_dot_real_limbs.pointer;
        let mut relational_dot_imaginary_sign_pointer = relational_dot_imaginary_sign.pointer;
        let mut relational_dot_imaginary_limbs_pointer = relational_dot_imaginary_limbs.pointer;
        let mut target_norm_pointer = target_norm_limbs.pointer;
        let mut relational_norm_pointer = relational_norm_limbs.pointer;
        let mut first_scratch_pointer = first_scratch.pointer;
        let mut second_scratch_pointer = second_scratch.pointer;
        let mut third_scratch_pointer = third_scratch.pointer;
        let mut axis_count_wire = axis_count as u32;
        let mut observer_limb_count_wire = observer_limb_count as u32;
        let mut direct_arguments: [*mut c_void; 47] = [
            &mut face_current_pointer as *mut u64 as *mut c_void,
            &mut face_relational_real_sign_pointer as *mut u64 as *mut c_void,
            &mut face_relational_real_limbs_pointer as *mut u64 as *mut c_void,
            &mut face_relational_imaginary_sign_pointer as *mut u64 as *mut c_void,
            &mut face_relational_imaginary_limbs_pointer as *mut u64 as *mut c_void,
            &mut receiver_class_base_pointer as *mut u64 as *mut c_void,
            &mut source_class_factor_offset_pointer as *mut u64 as *mut c_void,
            &mut source_class_factor_pointer as *mut u64 as *mut c_void,
            &mut factor_capacity_pointer as *mut u64 as *mut c_void,
            &mut family_orientation_pointer as *mut u64 as *mut c_void,
            &mut family_real_sign_pointer as *mut u64 as *mut c_void,
            &mut family_real_limbs_pointer as *mut u64 as *mut c_void,
            &mut family_imaginary_sign_pointer as *mut u64 as *mut c_void,
            &mut family_imaginary_limbs_pointer as *mut u64 as *mut c_void,
            &mut action_sign_pointer as *mut u64 as *mut c_void,
            &mut action_limbs_pointer as *mut u64 as *mut c_void,
            &mut reflected_sign_pointer as *mut u64 as *mut c_void,
            &mut reflected_limbs_pointer as *mut u64 as *mut c_void,
            &mut receiver_sign_pointer as *mut u64 as *mut c_void,
            &mut receiver_limbs_pointer as *mut u64 as *mut c_void,
            &mut receiver_norm_sign_pointer as *mut u64 as *mut c_void,
            &mut receiver_norm_limbs_pointer as *mut u64 as *mut c_void,
            &mut contact_real_sign_pointer as *mut u64 as *mut c_void,
            &mut contact_real_limbs_pointer as *mut u64 as *mut c_void,
            &mut contact_imaginary_sign_pointer as *mut u64 as *mut c_void,
            &mut contact_imaginary_limbs_pointer as *mut u64 as *mut c_void,
            &mut relational_dot_real_sign_pointer as *mut u64 as *mut c_void,
            &mut relational_dot_real_limbs_pointer as *mut u64 as *mut c_void,
            &mut relational_dot_imaginary_sign_pointer as *mut u64 as *mut c_void,
            &mut relational_dot_imaginary_limbs_pointer as *mut u64 as *mut c_void,
            &mut target_norm_pointer as *mut u64 as *mut c_void,
            &mut relational_norm_pointer as *mut u64 as *mut c_void,
            &mut first_scratch_pointer as *mut u64 as *mut c_void,
            &mut second_scratch_pointer as *mut u64 as *mut c_void,
            &mut third_scratch_pointer as *mut u64 as *mut c_void,
            &mut observer_obstruction_pointer as *mut u64 as *mut c_void,
            &mut observer_face_count_wire as *mut u32 as *mut c_void,
            &mut native_factor_count_wire as *mut u32 as *mut c_void,
            &mut family_count_wire as *mut u32 as *mut c_void,
            &mut receiver_count_wire as *mut u32 as *mut c_void,
            &mut axis_count_wire as *mut u32 as *mut c_void,
            &mut face_current_limb_count_wire as *mut u32 as *mut c_void,
            &mut face_relational_limb_count_wire as *mut u32 as *mut c_void,
            &mut family_limb_count_wire as *mut u32 as *mut c_void,
            &mut overlap_limb_count_wire as *mut u32 as *mut c_void,
            &mut observer_limb_count_wire as *mut u32 as *mut c_void,
            &mut contact_limb_count_wire as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    contract_completed,
                    word.card.grid_for(observer_work as u64)?,
                    1,
                    1,
                    word.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    direct_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(contract_membrane_completed_target_observer)",
        )?;
        let resident_working_octets = [
            octets(face_factor_population, face_current_limb_count)?,
            octets(face_factor_population, face_relational_limb_count)?
                .checked_mul(2)
                .and_then(|octets| octets.checked_add(face_factor_population * 2))
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
            octets(response_population, observer_limb_count)?
                .checked_mul(7)
                .and_then(|octets| octets.checked_add(response_population * 2))
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
            octets(observer_work, observer_limb_count)?
                .checked_mul(3)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
            std::mem::size_of::<u32>(),
        ]
        .into_iter()
        .try_fold(0_u64, |sum, octets| {
            sum.checked_add(u64::try_from(octets).ok()?)
        })
        .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        completed_target_observer_workspace = Some(ResidentCompletedTargetObserverWorkspace {
            face_current,
            face_relational_real_sign,
            face_relational_real_limbs,
            face_relational_imaginary_sign,
            face_relational_imaginary_limbs,
            relational_dot_real_sign,
            relational_dot_real_limbs,
            relational_dot_imaginary_sign,
            relational_dot_imaginary_limbs,
            target_norm_limbs,
            relational_norm_limbs,
            norm_product_limbs,
            first_scratch,
            second_scratch,
            third_scratch,
            limb_count: observer_limb_count,
            obstruction,
            resident_working_octets,
        });
    } else if materialize_moment_field {
        driver(
            unsafe {
                cuLaunchKernel(
                    word.card.membrane_quadratic_moment_contract,
                    contract_grid,
                    1,
                    1,
                    word.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    contract_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(contract_membrane_quadratic_moments)",
        )?;
    } else {
        let mut port_restriction_offset_pointer = port_restriction_offset.pointer;
        let mut native_generator_targets_pointer =
            quadratic_action.native_generator_targets.pointer;
        let mut receiver_class_base_pointer = quadratic_action.receiver_class_bases.pointer;
        let mut source_class_factor_offset_pointer =
            quadratic_action.source_class_factor_offsets.pointer;
        let mut source_class_factor_pointer = quadratic_action.source_class_factors.pointer;
        let mut generator_class_factor_offset_pointer =
            quadratic_action.generator_class_factor_offsets.pointer;
        let mut generator_class_factor_pointer = quadratic_action.generator_class_factors.pointer;
        let mut factorized_left_scratch_pointer = factorized_left_scratch.pointer;
        let mut factorized_right_scratch_pointer = factorized_right_scratch.pointer;
        let mut factorized_bucket_scratch_pointer = factorized_bucket_scratch.pointer;
        let mut factorized_quadratic_scratch_pointer = factorized_quadratic_scratch.pointer;
        let mut factorized_term_scratch_pointer = factorized_term_scratch.pointer;
        let mut factorized_overlap_scratch_pointer = factorized_overlap_scratch.pointer;
        let mut contribution_action_sign_pointer = contribution_action_sign.pointer;
        let mut contribution_action_limbs_pointer = contribution_action_limbs.pointer;
        let mut contribution_reflected_sign_pointer = contribution_reflected_sign.pointer;
        let mut contribution_reflected_limbs_pointer = contribution_reflected_limbs.pointer;
        let mut contribution_receiver_sign_pointer = contribution_receiver_sign.pointer;
        let mut contribution_receiver_limbs_pointer = contribution_receiver_limbs.pointer;
        let mut contribution_receiver_norm_sign_pointer = contribution_receiver_norm_sign.pointer;
        let mut contribution_receiver_norm_limbs_pointer = contribution_receiver_norm_limbs.pointer;
        let mut context_chunk_count_wire = context_chunk_count as u32;
        let mut context_chunk_size_wire = context_chunk_size as u32;
        let mut incidence_chunk_count_wire = incidence_chunk_count as u32;
        let mut incidence_chunk_size_wire = incidence_chunk_size as u32;
        let mut selected_context_chunk_wire = 0_u32;
        let mut selected_incidence_chunk_wire = 0_u32;
        let mut resident_rectangular_for_contract = u32::from(resident_rectangular_restrictions);
        let mut resident_boundary_state_count_for_contract = resident_boundary
            .map(|boundary| boundary.boundary_states.len() as u32)
            .unwrap_or(0);
        let mut boundary_states_for_contract_pointer = boundary_states_device.pointer;
        let mut factorized_arguments: [*mut c_void; 50] = [
            &mut context_current_pointer as *mut u64 as *mut c_void,
            &mut context_weight_pointer as *mut u64 as *mut c_void,
            &mut context_state_present_pointer as *mut u64 as *mut c_void,
            &mut context_states_pointer as *mut u64 as *mut c_void,
            &mut restriction_current_pointer as *mut u64 as *mut c_void,
            &mut boundary_states_for_contract_pointer as *mut u64 as *mut c_void,
            &mut native_generator_targets_pointer as *mut u64 as *mut c_void,
            &mut receiver_class_base_pointer as *mut u64 as *mut c_void,
            &mut source_class_factor_offset_pointer as *mut u64 as *mut c_void,
            &mut source_class_factor_pointer as *mut u64 as *mut c_void,
            &mut generator_class_factor_offset_pointer as *mut u64 as *mut c_void,
            &mut generator_class_factor_pointer as *mut u64 as *mut c_void,
            &mut factor_capacity_pointer as *mut u64 as *mut c_void,
            &mut family_orientation_pointer as *mut u64 as *mut c_void,
            &mut contribution_action_sign_pointer as *mut u64 as *mut c_void,
            &mut contribution_action_limbs_pointer as *mut u64 as *mut c_void,
            &mut contribution_reflected_sign_pointer as *mut u64 as *mut c_void,
            &mut contribution_reflected_limbs_pointer as *mut u64 as *mut c_void,
            &mut contribution_receiver_sign_pointer as *mut u64 as *mut c_void,
            &mut contribution_receiver_limbs_pointer as *mut u64 as *mut c_void,
            &mut contribution_receiver_norm_sign_pointer as *mut u64 as *mut c_void,
            &mut contribution_receiver_norm_limbs_pointer as *mut u64 as *mut c_void,
            &mut factorized_left_scratch_pointer as *mut u64 as *mut c_void,
            &mut factorized_right_scratch_pointer as *mut u64 as *mut c_void,
            &mut factorized_bucket_scratch_pointer as *mut u64 as *mut c_void,
            &mut factorized_quadratic_scratch_pointer as *mut u64 as *mut c_void,
            &mut factorized_term_scratch_pointer as *mut u64 as *mut c_void,
            &mut factorized_overlap_scratch_pointer as *mut u64 as *mut c_void,
            &mut context_count_wire as *mut u32 as *mut c_void,
            &mut restriction_count_wire as *mut u32 as *mut c_void,
            &mut port_count_wire as *mut u32 as *mut c_void,
            &mut native_factor_count_wire as *mut u32 as *mut c_void,
            &mut generator_count_wire as *mut u32 as *mut c_void,
            &mut family_count_wire as *mut u32 as *mut c_void,
            &mut receiver_count_wire as *mut u32 as *mut c_void,
            &mut context_chunk_count_wire as *mut u32 as *mut c_void,
            &mut context_chunk_size_wire as *mut u32 as *mut c_void,
            &mut incidence_chunk_count_wire as *mut u32 as *mut c_void,
            &mut incidence_chunk_size_wire as *mut u32 as *mut c_void,
            &mut selected_context_chunk_wire as *mut u32 as *mut c_void,
            &mut selected_incidence_chunk_wire as *mut u32 as *mut c_void,
            &mut context_limb_count_wire as *mut u32 as *mut c_void,
            &mut restriction_limb_count_wire as *mut u32 as *mut c_void,
            &mut weight_limb_count_wire as *mut u32 as *mut c_void,
            &mut product_limb_count_wire as *mut u32 as *mut c_void,
            &mut quadratic_limb_count_wire as *mut u32 as *mut c_void,
            &mut moment_limb_count_wire as *mut u32 as *mut c_void,
            &mut overlap_limb_count_wire as *mut u32 as *mut c_void,
            &mut resident_rectangular_for_contract as *mut u32 as *mut c_void,
            &mut resident_boundary_state_count_for_contract as *mut u32 as *mut c_void,
        ];
        let contribution_grid = word.card.grid_for(contribution_work as u64)?;
        let mut axis_count_wire = axis_count as u32;
        let mut resident_rectangular_wire = u32::from(resident_rectangular_restrictions);
        let mut resident_boundary_state_count_wire = resident_boundary
            .map(|boundary| boundary.boundary_states.len() as u32)
            .unwrap_or(0);
        let mut clear_output_wire = 1_u32;
        let mut finalize_contact_wire = 0_u32;
        let mut descend_boundary_state_receiver_wire = u32::from(descend_boundary_state_receiver);
        let mut reduce_arguments: [*mut c_void; 40] = [
            &mut contribution_action_sign_pointer as *mut u64 as *mut c_void,
            &mut contribution_action_limbs_pointer as *mut u64 as *mut c_void,
            &mut contribution_reflected_sign_pointer as *mut u64 as *mut c_void,
            &mut contribution_reflected_limbs_pointer as *mut u64 as *mut c_void,
            &mut contribution_receiver_sign_pointer as *mut u64 as *mut c_void,
            &mut contribution_receiver_limbs_pointer as *mut u64 as *mut c_void,
            &mut contribution_receiver_norm_sign_pointer as *mut u64 as *mut c_void,
            &mut contribution_receiver_norm_limbs_pointer as *mut u64 as *mut c_void,
            &mut port_restriction_offset_pointer as *mut u64 as *mut c_void,
            &mut family_real_sign_pointer as *mut u64 as *mut c_void,
            &mut family_real_limbs_pointer as *mut u64 as *mut c_void,
            &mut family_imaginary_sign_pointer as *mut u64 as *mut c_void,
            &mut family_imaginary_limbs_pointer as *mut u64 as *mut c_void,
            &mut action_sign_pointer as *mut u64 as *mut c_void,
            &mut action_limbs_pointer as *mut u64 as *mut c_void,
            &mut reflected_sign_pointer as *mut u64 as *mut c_void,
            &mut reflected_limbs_pointer as *mut u64 as *mut c_void,
            &mut receiver_sign_pointer as *mut u64 as *mut c_void,
            &mut receiver_limbs_pointer as *mut u64 as *mut c_void,
            &mut receiver_norm_sign_pointer as *mut u64 as *mut c_void,
            &mut receiver_norm_limbs_pointer as *mut u64 as *mut c_void,
            &mut contact_real_sign_pointer as *mut u64 as *mut c_void,
            &mut contact_real_limbs_pointer as *mut u64 as *mut c_void,
            &mut contact_imaginary_sign_pointer as *mut u64 as *mut c_void,
            &mut contact_imaginary_limbs_pointer as *mut u64 as *mut c_void,
            &mut context_chunk_count_wire as *mut u32 as *mut c_void,
            &mut incidence_chunk_count_wire as *mut u32 as *mut c_void,
            &mut port_count_wire as *mut u32 as *mut c_void,
            &mut generator_count_wire as *mut u32 as *mut c_void,
            &mut family_count_wire as *mut u32 as *mut c_void,
            &mut receiver_count_wire as *mut u32 as *mut c_void,
            &mut axis_count_wire as *mut u32 as *mut c_void,
            &mut overlap_limb_count_wire as *mut u32 as *mut c_void,
            &mut family_limb_count_wire as *mut u32 as *mut c_void,
            &mut contact_limb_count_wire as *mut u32 as *mut c_void,
            &mut resident_rectangular_wire as *mut u32 as *mut c_void,
            &mut resident_boundary_state_count_wire as *mut u32 as *mut c_void,
            &mut descend_boundary_state_receiver_wire as *mut u32 as *mut c_void,
            &mut clear_output_wire as *mut u32 as *mut c_void,
            &mut finalize_contact_wire as *mut u32 as *mut c_void,
        ];
        let contraction_began = std::time::Instant::now();
        for context_chunk in 0..context_chunk_count {
            selected_context_chunk_wire = context_chunk as u32;
            for incidence_chunk in 0..incidence_chunk_count {
                selected_incidence_chunk_wire = incidence_chunk as u32;
                clear_output_wire = u32::from(context_chunk == 0 && incidence_chunk == 0);
                finalize_contact_wire = u32::from(
                    context_chunk + 1 == context_chunk_count
                        && incidence_chunk + 1 == incidence_chunk_count,
                );
                driver(
                    unsafe {
                        cuLaunchKernel(
                            word.card.membrane_factorized_moment_contract,
                            contribution_grid,
                            1,
                            1,
                            word.card.block_x,
                            1,
                            1,
                            0,
                            ptr::null_mut(),
                            factorized_arguments.as_mut_ptr(),
                            ptr::null_mut(),
                        )
                    },
                    "cuLaunchKernel(contract_membrane_factorized_quadratic_moments)",
                )?;
                driver(
                    unsafe {
                        cuLaunchKernel(
                            word.card.membrane_factorized_moment_reduce,
                            contract_grid,
                            1,
                            1,
                            word.card.block_x,
                            1,
                            1,
                            0,
                            ptr::null_mut(),
                            reduce_arguments.as_mut_ptr(),
                            ptr::null_mut(),
                        )
                    },
                    "cuLaunchKernel(reduce_membrane_factorized_quadratic_moments)",
                )?;
            }
        }
        if cuda_profile {
            driver(
                unsafe { cuCtxSynchronize() },
                "cuCtxSynchronize(factorized-cover-profile)",
            )?;
            eprintln!(
                "mem6-cuda contract-reduce-ms={} resident-contributions={} context-chunks={} context-chunk-size={} incidence-chunks={} incidence-chunk-size={} addressed-faces={}",
                contraction_began.elapsed().as_millis(),
                contribution_work,
                context_chunk_count,
                context_chunk_size,
                incidence_chunk_count,
                incidence_chunk_size,
                response_population,
            );
        }
    }

    let mut factorized_relational_launches = 0_u64;
    if let (
        Some(workspace),
        Some((
            _,
            source_relational_state_present,
            source_relational_states,
            source_relational_state_count,
            source_relational_real_sign,
            source_relational_real_limbs,
            source_relational_imaginary_sign,
            source_relational_imaginary_limbs,
            source_relational_limb_count,
            _,
        )),
    ) = (
        factorized_relational_workspace.as_ref(),
        relational_current_aperture.as_ref(),
    ) {
        let boundary = resident_boundary.ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let mut transported_current_pointer = workspace.transported_current.pointer;
        let mut transported_state_present_pointer = workspace.transported_state_present.pointer;
        let mut transported_states_pointer = workspace.transported_states.pointer;
        let mut transported_limb_count_wire = workspace.transported_limb_count as u32;
        let mut relational_generator_targets_pointer =
            quadratic_action.native_generator_targets.pointer;
        let mut source_relational_state_present_pointer = *source_relational_state_present;
        let mut source_relational_states_pointer = *source_relational_states;
        let mut source_relational_real_sign_pointer = *source_relational_real_sign;
        let mut source_relational_real_limbs_pointer = *source_relational_real_limbs;
        let mut source_relational_imaginary_sign_pointer = *source_relational_imaginary_sign;
        let mut source_relational_imaginary_limbs_pointer = *source_relational_imaginary_limbs;
        let mut transported_relational_real_sign_pointer =
            workspace.transported_relational_real_sign.pointer;
        let mut transported_relational_real_limbs_pointer =
            workspace.transported_relational_real_limbs.pointer;
        let mut transported_relational_imaginary_sign_pointer =
            workspace.transported_relational_imaginary_sign.pointer;
        let mut transported_relational_imaginary_limbs_pointer =
            workspace.transported_relational_imaginary_limbs.pointer;
        let mut relational_obstruction_pointer = workspace.obstruction.pointer;
        let mut relational_factor_count_wire = word.factors;
        let mut relational_generator_count_wire = front.generator_count;
        let mut source_relational_state_count_wire = *source_relational_state_count as u32;
        let mut source_relational_limb_count_wire = *source_relational_limb_count as u32;
        let mut transported_relational_limb_count_wire =
            workspace.transported_relational_limb_count as u32;
        let mut relational_transport = ptr::null_mut();
        let mut relational_partial = ptr::null_mut();
        let mut relational_norm = ptr::null_mut();
        driver(
            unsafe {
                cuModuleGetFunction(
                    &mut relational_transport,
                    word.card.module,
                    c"transport_membrane_sparse_relational_generator_limbs".as_ptr(),
                )
            },
            "cuModuleGetFunction(transport_membrane_sparse_relational_generator_limbs)",
        )?;
        driver(
            unsafe {
                cuModuleGetFunction(
                    &mut relational_partial,
                    word.card.module,
                    c"form_membrane_factorized_relational_moment_partials".as_ptr(),
                )
            },
            "cuModuleGetFunction(form_membrane_factorized_relational_moment_partials)",
        )?;
        driver(
            unsafe {
                cuModuleGetFunction(
                    &mut relational_norm,
                    word.card.module,
                    c"form_membrane_factorized_relational_current_norms".as_ptr(),
                )
            },
            "cuModuleGetFunction(form_membrane_factorized_relational_current_norms)",
        )?;

        let mut current_transport_arguments: [*mut c_void; 12] = [
            &mut context_current_pointer as *mut u64 as *mut c_void,
            &mut context_state_present_pointer as *mut u64 as *mut c_void,
            &mut context_states_pointer as *mut u64 as *mut c_void,
            &mut relational_generator_targets_pointer as *mut u64 as *mut c_void,
            &mut transported_current_pointer as *mut u64 as *mut c_void,
            &mut transported_state_present_pointer as *mut u64 as *mut c_void,
            &mut transported_states_pointer as *mut u64 as *mut c_void,
            &mut context_count_wire as *mut u32 as *mut c_void,
            &mut native_factor_count_wire as *mut u32 as *mut c_void,
            &mut generator_count_wire as *mut u32 as *mut c_void,
            &mut context_limb_count_wire as *mut u32 as *mut c_void,
            &mut transported_limb_count_wire as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    word.card.membrane_factor_current_transport,
                    word.card.grid_for(
                        u64::try_from(context_count.saturating_mul(generator_count))
                            .map_err(|_| CudaRefineError::MembraneInteriorWordShape)?,
                    )?,
                    1,
                    1,
                    word.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    current_transport_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(transport_membrane_factorized_relational_source_currents)",
        )?;
        let mut relational_transport_arguments: [*mut c_void; 16] = [
            &mut relational_generator_targets_pointer as *mut u64 as *mut c_void,
            &mut source_relational_state_present_pointer as *mut u64 as *mut c_void,
            &mut source_relational_real_sign_pointer as *mut u64 as *mut c_void,
            &mut source_relational_real_limbs_pointer as *mut u64 as *mut c_void,
            &mut source_relational_imaginary_sign_pointer as *mut u64 as *mut c_void,
            &mut source_relational_imaginary_limbs_pointer as *mut u64 as *mut c_void,
            &mut transported_relational_real_sign_pointer as *mut u64 as *mut c_void,
            &mut transported_relational_real_limbs_pointer as *mut u64 as *mut c_void,
            &mut transported_relational_imaginary_sign_pointer as *mut u64 as *mut c_void,
            &mut transported_relational_imaginary_limbs_pointer as *mut u64 as *mut c_void,
            &mut relational_factor_count_wire as *mut u32 as *mut c_void,
            &mut relational_generator_count_wire as *mut u32 as *mut c_void,
            &mut source_relational_state_count_wire as *mut u32 as *mut c_void,
            &mut source_relational_limb_count_wire as *mut u32 as *mut c_void,
            &mut transported_relational_limb_count_wire as *mut u32 as *mut c_void,
            &mut relational_obstruction_pointer as *mut u64 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    relational_transport,
                    word.card.grid_for(
                        u64::from(word.factors)
                            * u64::from(front.generator_count)
                            * u64::try_from(*source_relational_state_count)
                                .map_err(|_| CudaRefineError::MembraneInteriorWordShape)?,
                    )?,
                    1,
                    1,
                    word.card.block_x,
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

        let mut relational_restriction_pointer = restriction_current.pointer;
        let mut relational_restriction_present_pointer = restriction_present.pointer;
        let mut relational_boundary_states_pointer = boundary_states_device.pointer;
        let mut partial_overlap_pointer = workspace.partial_overlap.pointer;
        let mut partial_target_norm_pointer = workspace.partial_target_norm.pointer;
        let mut dot_real_sign_pointer = workspace.dot_real_signs.pointer;
        let mut dot_real_pointer = workspace.dot_real.pointer;
        let mut dot_imaginary_sign_pointer = workspace.dot_imaginary_signs.pointer;
        let mut dot_imaginary_pointer = workspace.dot_imaginary.pointer;
        let mut partial_first_scratch_pointer = workspace.partial_first_scratch.pointer;
        let mut partial_second_scratch_pointer = workspace.partial_second_scratch.pointer;
        let mut partial_third_scratch_pointer = workspace.partial_third_scratch.pointer;
        let mut relational_port_count_wire = port_population as u32;
        let mut relational_boundary_state_count_wire = boundary.boundary_states.len() as u32;
        let mut relational_output_limb_count_wire = workspace.limb_count as u32;
        let mut relational_partial_arguments: [*mut c_void; 33] = [
            &mut transported_current_pointer as *mut u64 as *mut c_void,
            &mut transported_state_present_pointer as *mut u64 as *mut c_void,
            &mut transported_states_pointer as *mut u64 as *mut c_void,
            &mut context_weight_pointer as *mut u64 as *mut c_void,
            &mut relational_restriction_pointer as *mut u64 as *mut c_void,
            &mut relational_restriction_present_pointer as *mut u64 as *mut c_void,
            &mut relational_boundary_states_pointer as *mut u64 as *mut c_void,
            &mut source_relational_state_present_pointer as *mut u64 as *mut c_void,
            &mut source_relational_states_pointer as *mut u64 as *mut c_void,
            &mut transported_relational_real_sign_pointer as *mut u64 as *mut c_void,
            &mut transported_relational_real_limbs_pointer as *mut u64 as *mut c_void,
            &mut transported_relational_imaginary_sign_pointer as *mut u64 as *mut c_void,
            &mut transported_relational_imaginary_limbs_pointer as *mut u64 as *mut c_void,
            &mut partial_overlap_pointer as *mut u64 as *mut c_void,
            &mut partial_target_norm_pointer as *mut u64 as *mut c_void,
            &mut dot_real_sign_pointer as *mut u64 as *mut c_void,
            &mut dot_real_pointer as *mut u64 as *mut c_void,
            &mut dot_imaginary_sign_pointer as *mut u64 as *mut c_void,
            &mut dot_imaginary_pointer as *mut u64 as *mut c_void,
            &mut partial_first_scratch_pointer as *mut u64 as *mut c_void,
            &mut partial_second_scratch_pointer as *mut u64 as *mut c_void,
            &mut partial_third_scratch_pointer as *mut u64 as *mut c_void,
            &mut context_count_wire as *mut u32 as *mut c_void,
            &mut relational_factor_count_wire as *mut u32 as *mut c_void,
            &mut relational_port_count_wire as *mut u32 as *mut c_void,
            &mut relational_generator_count_wire as *mut u32 as *mut c_void,
            &mut relational_boundary_state_count_wire as *mut u32 as *mut c_void,
            &mut source_relational_state_count_wire as *mut u32 as *mut c_void,
            &mut transported_limb_count_wire as *mut u32 as *mut c_void,
            &mut restriction_limb_count_wire as *mut u32 as *mut c_void,
            &mut transported_relational_limb_count_wire as *mut u32 as *mut c_void,
            &mut weight_limb_count_wire as *mut u32 as *mut c_void,
            &mut relational_output_limb_count_wire as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    relational_partial,
                    word.card.grid_for(
                        u64::try_from(local_response_population.saturating_mul(context_count))
                            .map_err(|_| CudaRefineError::MembraneInteriorWordShape)?,
                    )?,
                    1,
                    1,
                    word.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    relational_partial_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(form_membrane_factorized_relational_moment_partials)",
        )?;

        let mut relational_norm_pointer = workspace.relational_norm.pointer;
        let mut norm_first_scratch_pointer = workspace.norm_first_scratch.pointer;
        let mut norm_second_scratch_pointer = workspace.norm_second_scratch.pointer;
        let mut descend_relational_receiver_wire = u32::from(descend_boundary_state_receiver);
        let mut relational_norm_arguments: [*mut c_void; 21] = [
            &mut relational_restriction_pointer as *mut u64 as *mut c_void,
            &mut relational_restriction_present_pointer as *mut u64 as *mut c_void,
            &mut relational_boundary_states_pointer as *mut u64 as *mut c_void,
            &mut source_relational_state_present_pointer as *mut u64 as *mut c_void,
            &mut source_relational_states_pointer as *mut u64 as *mut c_void,
            &mut transported_relational_real_sign_pointer as *mut u64 as *mut c_void,
            &mut transported_relational_real_limbs_pointer as *mut u64 as *mut c_void,
            &mut transported_relational_imaginary_sign_pointer as *mut u64 as *mut c_void,
            &mut transported_relational_imaginary_limbs_pointer as *mut u64 as *mut c_void,
            &mut relational_norm_pointer as *mut u64 as *mut c_void,
            &mut norm_first_scratch_pointer as *mut u64 as *mut c_void,
            &mut norm_second_scratch_pointer as *mut u64 as *mut c_void,
            &mut relational_port_count_wire as *mut u32 as *mut c_void,
            &mut relational_factor_count_wire as *mut u32 as *mut c_void,
            &mut relational_generator_count_wire as *mut u32 as *mut c_void,
            &mut relational_boundary_state_count_wire as *mut u32 as *mut c_void,
            &mut source_relational_state_count_wire as *mut u32 as *mut c_void,
            &mut restriction_limb_count_wire as *mut u32 as *mut c_void,
            &mut transported_relational_limb_count_wire as *mut u32 as *mut c_void,
            &mut relational_output_limb_count_wire as *mut u32 as *mut c_void,
            &mut descend_relational_receiver_wire as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    relational_norm,
                    word.card.grid_for(response_population as u64)?,
                    1,
                    1,
                    word.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    relational_norm_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(form_membrane_factorized_relational_current_norms)",
        )?;
        factorized_relational_launches = 4;
    }
    Ok(MomentContractionLaunch {
        resident_gather_launches,
        factorized_relational_launches,
        completed_target_observer_workspace,
    })
}
