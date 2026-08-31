use super::membrane_moment_execution::{MomentContractionLaunch, MomentFrontExecution};
use super::*;

pub(super) fn launch(
    word: &ResidentMembraneInteriorWord,
    port_population: usize,
    execution: &MomentFrontExecution<'_>,
    contraction: &mut MomentContractionLaunch,
) -> Result<(), CudaRefineError> {
    let plan = &execution.plan;
    let workspace = &execution.workspace;
    let resident_began = &execution.resident_began;
    let cuda_profile = execution.cuda_profile;

    let compatibility_limb_count = plan.compatibility_limb_count;
    let component_count = plan.component_count;
    let component_population = plan.component_population;
    let context_count = plan.context_count;
    let cross_limb_count = plan.cross_limb_count;
    let descend_boundary_state_receiver = plan.descend_boundary_state_receiver;
    let generator_count = plan.generator_count;
    let joint_scale = plan.joint_scale;
    let norm_limb_count = plan.norm_limb_count;
    let radiation_limb_count = plan.radiation_limb_count;
    let resident_boundary = plan.resident_boundary;
    let response_population = plan.response_population;
    let situated_pairing_limb_count = plan.situated_pairing_limb_count;
    let square_limb_count = plan.square_limb_count;
    let stored_limb_count = plan.stored_limb_count;

    let factorized_relational_workspace = &workspace.factorized_relational_workspace;
    let completed_target_observer_workspace = &contraction.completed_target_observer_workspace;
    let factorized_relational_launches = &mut contraction.factorized_relational_launches;
    let boundary_states_device = &workspace.boundary_states_device;
    let compatibility_limbs = &workspace.compatibility_limbs;
    let compatibility_sign = &workspace.compatibility_sign;
    let complete_native_successor_front = &workspace.complete_native_successor_front;
    let incoming_imaginary_limbs_device = &workspace.incoming_imaginary_limbs_device;
    let incoming_imaginary_sign_device = &workspace.incoming_imaginary_sign_device;
    let incoming_real_limbs_device = &workspace.incoming_real_limbs_device;
    let incoming_real_sign_device = &workspace.incoming_real_sign_device;
    let joint_imaginary_limbs = &workspace.joint_imaginary_limbs;
    let joint_imaginary_sign = &workspace.joint_imaginary_sign;
    let joint_real_limbs = &workspace.joint_real_limbs;
    let joint_real_sign = &workspace.joint_real_sign;
    let phase_left_cross_scratch = &workspace.phase_left_cross_scratch;
    let phase_locked = &workspace.phase_locked;
    let phase_norm_limbs = &workspace.phase_norm_limbs;
    let phase_right_cross_scratch = &workspace.phase_right_cross_scratch;
    let phase_square_scratch = &workspace.phase_square_scratch;
    let port_action_limbs = &workspace.port_action_limbs;
    let port_action_sign = &workspace.port_action_sign;
    let port_imaginary_limbs = &workspace.port_imaginary_limbs;
    let port_imaginary_sign = &workspace.port_imaginary_sign;
    let port_real_limbs = &workspace.port_real_limbs;
    let port_real_sign = &workspace.port_real_sign;
    let port_receiver_limbs = &workspace.port_receiver_limbs;
    let port_receiver_norm_limbs = &workspace.port_receiver_norm_limbs;
    let port_receiver_norm_sign = &workspace.port_receiver_norm_sign;
    let port_receiver_sign = &workspace.port_receiver_sign;
    let port_reflected_limbs = &workspace.port_reflected_limbs;
    let port_reflected_sign = &workspace.port_reflected_sign;
    let situated_pairing_front = &workspace.situated_pairing_front;
    let situated_pairing_imaginary_scratch = &workspace.situated_pairing_imaginary_scratch;
    let situated_pairing_limbs = &workspace.situated_pairing_limbs;
    let situated_pairing_sign = &workspace.situated_pairing_sign;
    let stored_imaginary_limbs = &workspace.stored_imaginary_limbs;
    let stored_imaginary_sign = &workspace.stored_imaginary_sign;
    let stored_real_limbs = &workspace.stored_real_limbs;
    let stored_real_sign = &workspace.stored_real_sign;
    let support_imaginary_limbs = &workspace.support_imaginary_limbs;
    let support_imaginary_sign = &workspace.support_imaginary_sign;
    let support_port = &workspace.support_port;
    let support_real_limbs = &workspace.support_real_limbs;
    let support_real_sign = &workspace.support_real_sign;
    let balance_scratch = &workspace.balance_scratch;

    let mut action_sign_pointer = workspace.action_sign.pointer;
    let mut action_limbs_pointer = workspace.action_limbs.pointer;
    let mut reflected_sign_pointer = workspace.reflected_sign.pointer;
    let mut reflected_limbs_pointer = workspace.reflected_limbs.pointer;
    let mut receiver_sign_pointer = workspace.receiver_sign.pointer;
    let mut receiver_limbs_pointer = workspace.receiver_limbs.pointer;
    let mut receiver_norm_sign_pointer = workspace.receiver_norm_sign.pointer;
    let mut receiver_norm_limbs_pointer = workspace.receiver_norm_limbs.pointer;
    let mut contact_real_sign_pointer = workspace.contact_real_sign.pointer;
    let mut contact_real_limbs_pointer = workspace.contact_real_limbs.pointer;
    let mut contact_imaginary_sign_pointer = workspace.contact_imaginary_sign.pointer;
    let mut contact_imaginary_limbs_pointer = workspace.contact_imaginary_limbs.pointer;
    let mut family_real_limbs_pointer = word.family_real_limbs.pointer;
    let mut family_imaginary_limbs_pointer = word.family_imaginary_limbs.pointer;
    let mut context_state_present_pointer = plan
        .resident_context_state
        .as_ref()
        .map(|state| state.boundary_state_present_pointer)
        .or_else(|| {
            workspace
                .context_state_present
                .as_ref()
                .map(|buffer| buffer.pointer)
        })
        .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
    let mut context_states_pointer = plan
        .resident_context_state
        .as_ref()
        .map(|state| state.boundary_states_pointer)
        .or_else(|| {
            workspace
                .context_states
                .as_ref()
                .map(|buffer| buffer.pointer)
        })
        .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
    let mut family_count_wire = word.families;
    let mut receiver_count_wire = word.receiver_count;
    let mut overlap_limb_count_wire = plan.overlap_limb_count as u32;
    let mut contact_limb_count_wire = plan.contact_limb_count as u32;
    let mut family_limb_count_wire = word.family_limb_count;

    // Every successor below receives the complete addressed higher-face population.  The
    // physical port count remains only in the cold reconstruction chart above.
    let mut port_count_wire = response_population as u32;

    let mut support_port_pointer = support_port.pointer;
    let mut support_real_sign_pointer = support_real_sign.pointer;
    let mut support_real_limbs_pointer = support_real_limbs.pointer;
    let mut support_imaginary_sign_pointer = support_imaginary_sign.pointer;
    let mut support_imaginary_limbs_pointer = support_imaginary_limbs.pointer;
    let mut port_real_sign_pointer = port_real_sign.pointer;
    let mut port_real_limbs_pointer = port_real_limbs.pointer;
    let mut port_imaginary_sign_pointer = port_imaginary_sign.pointer;
    let mut port_imaginary_limbs_pointer = port_imaginary_limbs.pointer;
    let mut joint_real_sign_pointer = joint_real_sign.pointer;
    let mut joint_real_limbs_pointer = joint_real_limbs.pointer;
    let mut joint_imaginary_sign_pointer = joint_imaginary_sign.pointer;
    let mut joint_imaginary_limbs_pointer = joint_imaginary_limbs.pointer;
    let mut port_action_sign_pointer = port_action_sign.pointer;
    let mut port_action_limbs_pointer = port_action_limbs.pointer;
    let mut port_reflected_sign_pointer = port_reflected_sign.pointer;
    let mut port_reflected_limbs_pointer = port_reflected_limbs.pointer;
    let mut port_receiver_sign_pointer = port_receiver_sign.pointer;
    let mut port_receiver_limbs_pointer = port_receiver_limbs.pointer;
    let mut port_receiver_norm_sign_pointer = port_receiver_norm_sign.pointer;
    let mut port_receiver_norm_limbs_pointer = port_receiver_norm_limbs.pointer;
    let mut support_count_wire = response_population as u32;
    let mut radiation_limb_count_wire = radiation_limb_count as u32;
    let mut radiation_arguments: [*mut c_void; 40] = [
        &mut support_port_pointer as *mut u64 as *mut c_void,
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
        &mut support_real_sign_pointer as *mut u64 as *mut c_void,
        &mut support_real_limbs_pointer as *mut u64 as *mut c_void,
        &mut support_imaginary_sign_pointer as *mut u64 as *mut c_void,
        &mut support_imaginary_limbs_pointer as *mut u64 as *mut c_void,
        &mut port_real_sign_pointer as *mut u64 as *mut c_void,
        &mut port_real_limbs_pointer as *mut u64 as *mut c_void,
        &mut port_imaginary_sign_pointer as *mut u64 as *mut c_void,
        &mut port_imaginary_limbs_pointer as *mut u64 as *mut c_void,
        &mut joint_real_sign_pointer as *mut u64 as *mut c_void,
        &mut joint_real_limbs_pointer as *mut u64 as *mut c_void,
        &mut joint_imaginary_sign_pointer as *mut u64 as *mut c_void,
        &mut joint_imaginary_limbs_pointer as *mut u64 as *mut c_void,
        &mut port_action_sign_pointer as *mut u64 as *mut c_void,
        &mut port_action_limbs_pointer as *mut u64 as *mut c_void,
        &mut port_reflected_sign_pointer as *mut u64 as *mut c_void,
        &mut port_reflected_limbs_pointer as *mut u64 as *mut c_void,
        &mut port_receiver_sign_pointer as *mut u64 as *mut c_void,
        &mut port_receiver_limbs_pointer as *mut u64 as *mut c_void,
        &mut port_receiver_norm_sign_pointer as *mut u64 as *mut c_void,
        &mut port_receiver_norm_limbs_pointer as *mut u64 as *mut c_void,
        &mut support_count_wire as *mut u32 as *mut c_void,
        &mut port_count_wire as *mut u32 as *mut c_void,
        &mut family_count_wire as *mut u32 as *mut c_void,
        &mut receiver_count_wire as *mut u32 as *mut c_void,
        &mut overlap_limb_count_wire as *mut u32 as *mut c_void,
        &mut contact_limb_count_wire as *mut u32 as *mut c_void,
        &mut radiation_limb_count_wire as *mut u32 as *mut c_void,
    ];
    driver(
        unsafe {
            cuLaunchKernel(
                word.card.membrane_boundary_chain_radiation,
                1,
                1,
                1,
                1,
                1,
                1,
                0,
                ptr::null_mut(),
                radiation_arguments.as_mut_ptr(),
                ptr::null_mut(),
            )
        },
        "cuLaunchKernel(gather_membrane_quadratic_moment_radiation)",
    )?;

    let mut compatibility_sign_pointer = compatibility_sign.pointer;
    let mut compatibility_limbs_pointer = compatibility_limbs.pointer;
    let mut phase_norm_limbs_pointer = phase_norm_limbs.pointer;
    let mut phase_locked_pointer = phase_locked.pointer;
    let mut phase_square_scratch_pointer = phase_square_scratch.pointer;
    let mut phase_left_cross_scratch_pointer = phase_left_cross_scratch.pointer;
    let mut phase_right_cross_scratch_pointer = phase_right_cross_scratch.pointer;
    let mut compatibility_limb_count_wire = compatibility_limb_count as u32;
    let mut norm_limb_count_wire = norm_limb_count as u32;
    let mut square_limb_count_wire = square_limb_count as u32;
    let mut cross_limb_count_wire = cross_limb_count as u32;
    let mut component_count_wire = component_count;
    let mut phase_component_arguments: [*mut c_void; 20] = [
        &mut family_real_limbs_pointer as *mut u64 as *mut c_void,
        &mut family_imaginary_limbs_pointer as *mut u64 as *mut c_void,
        &mut port_action_sign_pointer as *mut u64 as *mut c_void,
        &mut port_action_limbs_pointer as *mut u64 as *mut c_void,
        &mut port_reflected_sign_pointer as *mut u64 as *mut c_void,
        &mut port_reflected_limbs_pointer as *mut u64 as *mut c_void,
        &mut port_receiver_sign_pointer as *mut u64 as *mut c_void,
        &mut port_receiver_limbs_pointer as *mut u64 as *mut c_void,
        &mut port_receiver_norm_limbs_pointer as *mut u64 as *mut c_void,
        &mut compatibility_sign_pointer as *mut u64 as *mut c_void,
        &mut compatibility_limbs_pointer as *mut u64 as *mut c_void,
        &mut phase_norm_limbs_pointer as *mut u64 as *mut c_void,
        &mut port_count_wire as *mut u32 as *mut c_void,
        &mut family_count_wire as *mut u32 as *mut c_void,
        &mut receiver_count_wire as *mut u32 as *mut c_void,
        &mut component_count_wire as *mut u32 as *mut c_void,
        &mut family_limb_count_wire as *mut u32 as *mut c_void,
        &mut overlap_limb_count_wire as *mut u32 as *mut c_void,
        &mut compatibility_limb_count_wire as *mut u32 as *mut c_void,
        &mut norm_limb_count_wire as *mut u32 as *mut c_void,
    ];
    let phase_component_grid = word.card.grid_for(component_population as u64)?;
    driver(
        unsafe {
            cuLaunchKernel(
                word.card.membrane_boundary_phase_components,
                phase_component_grid,
                1,
                1,
                word.card.block_x,
                1,
                1,
                0,
                ptr::null_mut(),
                phase_component_arguments.as_mut_ptr(),
                ptr::null_mut(),
            )
        },
        "cuLaunchKernel(form_membrane_quadratic_moment_phase_components)",
    )?;
    if let Some(workspace) = factorized_relational_workspace.as_ref() {
        let mut relational_reduce = ptr::null_mut();
        driver(
            unsafe {
                cuModuleGetFunction(
                    &mut relational_reduce,
                    word.card.module,
                    c"reduce_membrane_factorized_relational_moment_components".as_ptr(),
                )
            },
            "cuModuleGetFunction(reduce_membrane_factorized_relational_moment_components)",
        )?;
        let mut partial_overlap_pointer = workspace.partial_overlap.pointer;
        let mut partial_target_norm_pointer = workspace.partial_target_norm.pointer;
        let mut relational_norm_pointer = workspace.relational_norm.pointer;
        let mut reduce_first_scratch_pointer = workspace.reduce_first_scratch.pointer;
        let mut reduce_second_scratch_pointer = workspace.reduce_second_scratch.pointer;
        let mut reduce_third_scratch_pointer = workspace.reduce_third_scratch.pointer;
        let mut relational_face_count_wire = response_population as u32;
        let mut relational_context_count_wire = context_count as u32;
        let mut relational_port_count_wire = port_population as u32;
        let mut relational_generator_count_wire = generator_count as u32;
        let mut relational_boundary_state_count_wire = resident_boundary
            .map(|boundary| boundary.boundary_states.len() as u32)
            .unwrap_or(1);
        let mut relational_reduce_boundary_states_pointer = boundary_states_device.pointer;
        let mut relational_component_wire = word
            .families
            .checked_add(word.receiver_count)
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let mut relational_limb_count_wire = workspace.limb_count as u32;
        let mut descend_relational_reduce_wire = u32::from(descend_boundary_state_receiver);
        let mut relational_reduce_arguments: [*mut c_void; 21] = [
            &mut partial_overlap_pointer as *mut u64 as *mut c_void,
            &mut partial_target_norm_pointer as *mut u64 as *mut c_void,
            &mut relational_norm_pointer as *mut u64 as *mut c_void,
            &mut context_state_present_pointer as *mut u64 as *mut c_void,
            &mut context_states_pointer as *mut u64 as *mut c_void,
            &mut relational_reduce_boundary_states_pointer as *mut u64 as *mut c_void,
            &mut compatibility_sign_pointer as *mut u64 as *mut c_void,
            &mut compatibility_limbs_pointer as *mut u64 as *mut c_void,
            &mut phase_norm_limbs_pointer as *mut u64 as *mut c_void,
            &mut reduce_first_scratch_pointer as *mut u64 as *mut c_void,
            &mut reduce_second_scratch_pointer as *mut u64 as *mut c_void,
            &mut reduce_third_scratch_pointer as *mut u64 as *mut c_void,
            &mut relational_face_count_wire as *mut u32 as *mut c_void,
            &mut relational_context_count_wire as *mut u32 as *mut c_void,
            &mut relational_port_count_wire as *mut u32 as *mut c_void,
            &mut relational_generator_count_wire as *mut u32 as *mut c_void,
            &mut relational_boundary_state_count_wire as *mut u32 as *mut c_void,
            &mut component_count_wire as *mut u32 as *mut c_void,
            &mut relational_component_wire as *mut u32 as *mut c_void,
            &mut relational_limb_count_wire as *mut u32 as *mut c_void,
            &mut descend_relational_reduce_wire as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    relational_reduce,
                    word.card.grid_for(response_population as u64)?,
                    1,
                    1,
                    word.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    relational_reduce_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(reduce_membrane_factorized_relational_moment_components)",
        )?;
        *factorized_relational_launches = factorized_relational_launches.saturating_add(1);
    } else if let Some(workspace) = completed_target_observer_workspace.as_ref() {
        let mut append_relational = ptr::null_mut();
        driver(
            unsafe {
                cuModuleGetFunction(
                    &mut append_relational,
                    word.card.module,
                    c"append_membrane_completed_target_oriented_relational_component".as_ptr(),
                )
            },
            "cuModuleGetFunction(append_membrane_completed_target_oriented_relational_component)",
        )?;
        let mut dot_real_sign_pointer = workspace.relational_dot_real_sign.pointer;
        let mut dot_real_limbs_pointer = workspace.relational_dot_real_limbs.pointer;
        let mut target_norm_pointer = workspace.target_norm_limbs.pointer;
        let mut relational_norm_pointer = workspace.relational_norm_limbs.pointer;
        let mut norm_product_pointer = workspace.norm_product_limbs.pointer;
        let mut first_scratch_pointer = workspace.first_scratch.pointer;
        let mut relational_face_count_wire = response_population as u32;
        let mut relational_component_wire = word
            .families
            .checked_add(word.receiver_count)
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let mut relational_limb_count_wire = workspace.limb_count as u32;
        let mut append_arguments: [*mut c_void; 13] = [
            &mut dot_real_sign_pointer as *mut u64 as *mut c_void,
            &mut dot_real_limbs_pointer as *mut u64 as *mut c_void,
            &mut target_norm_pointer as *mut u64 as *mut c_void,
            &mut relational_norm_pointer as *mut u64 as *mut c_void,
            &mut compatibility_sign_pointer as *mut u64 as *mut c_void,
            &mut compatibility_limbs_pointer as *mut u64 as *mut c_void,
            &mut phase_norm_limbs_pointer as *mut u64 as *mut c_void,
            &mut norm_product_pointer as *mut u64 as *mut c_void,
            &mut first_scratch_pointer as *mut u64 as *mut c_void,
            &mut relational_face_count_wire as *mut u32 as *mut c_void,
            &mut component_count_wire as *mut u32 as *mut c_void,
            &mut relational_component_wire as *mut u32 as *mut c_void,
            &mut relational_limb_count_wire as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    append_relational,
                    word.card.grid_for(response_population as u64)?,
                    1,
                    1,
                    word.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    append_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(append_membrane_completed_target_oriented_relational_component)",
        )?;
        *factorized_relational_launches = factorized_relational_launches.saturating_add(3);
    }
    let mut mark_productive = ptr::null_mut();
    driver(
        unsafe {
            cuModuleGetFunction(
                &mut mark_productive,
                word.card.module,
                c"mark_membrane_productive_current_front".as_ptr(),
            )
        },
        "cuModuleGetFunction(mark_membrane_productive_current_front)",
    )?;
    let (
        mut productive_norm_pointer,
        mut productive_component_count_wire,
        mut productive_limb_count_wire,
    ) = if let Some(workspace) = factorized_relational_workspace.as_ref() {
        (
            workspace.reduce_first_scratch.pointer,
            1_u32,
            workspace.limb_count as u32,
        )
    } else if let Some(workspace) = completed_target_observer_workspace.as_ref() {
        (
            workspace.target_norm_limbs.pointer,
            1_u32,
            workspace.limb_count as u32,
        )
    } else {
        (
            phase_norm_limbs.pointer,
            component_count,
            norm_limb_count as u32,
        )
    };
    let mut productive_front_pointer = complete_native_successor_front.pointer;
    let mut productive_face_count_wire = response_population as u32;
    let mut productive_arguments: [*mut c_void; 5] = [
        &mut productive_norm_pointer as *mut u64 as *mut c_void,
        &mut productive_front_pointer as *mut u64 as *mut c_void,
        &mut productive_face_count_wire as *mut u32 as *mut c_void,
        &mut productive_component_count_wire as *mut u32 as *mut c_void,
        &mut productive_limb_count_wire as *mut u32 as *mut c_void,
    ];
    driver(
        unsafe {
            cuLaunchKernel(
                mark_productive,
                word.card.grid_for(response_population as u64)?,
                1,
                1,
                word.card.block_x,
                1,
                1,
                0,
                ptr::null_mut(),
                productive_arguments.as_mut_ptr(),
                ptr::null_mut(),
            )
        },
        "cuLaunchKernel(mark_membrane_productive_current_front)",
    )?;
    let mut phase_select_direct = ptr::null_mut();
    // `selectedStateAddressedSum` applies the receiver-selected predicate before it forms the
    // target-state direct sum.  The complete component section below is that common receiver
    // family, so all productive addressed faces are commensurable here; target state remains
    // an output address and reconstruction coordinate, not a wall around alternative answers.
    // Partitioning this comparison by prospective target state retained one nondominated face
    // per successor and inverted the proved order of selection and target addressing.
    let relational_observer_present =
        factorized_relational_workspace.is_some() || completed_target_observer_workspace.is_some();
    let phase_select_name = if relational_observer_present {
        c"select_membrane_boundary_phase_front_complete_receiver_direct"
    } else {
        c"select_membrane_boundary_phase_front_direct"
    };
    driver(
        unsafe {
            cuModuleGetFunction(
                &mut phase_select_direct,
                word.card.module,
                phase_select_name.as_ptr(),
            )
        },
        "cuModuleGetFunction(select_membrane_boundary_phase_front_target_state_direct)",
    )?;
    let phase_select_grid = word.card.grid_for(response_population as u64)?;
    let mut complete_native_face_population_wire = response_population as u32;
    if relational_observer_present {
        let (mut productive_target_norm_pointer, mut productive_limb_count_wire) =
            if let Some(workspace) = factorized_relational_workspace.as_ref() {
                (
                    workspace.reduce_first_scratch.pointer,
                    workspace.limb_count as u32,
                )
            } else {
                let workspace = completed_target_observer_workspace
                    .as_ref()
                    .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
                (
                    workspace.target_norm_limbs.pointer,
                    workspace.limb_count as u32,
                )
            };
        let mut phase_select_arguments: [*mut c_void; 15] = [
            &mut compatibility_sign_pointer as *mut u64 as *mut c_void,
            &mut compatibility_limbs_pointer as *mut u64 as *mut c_void,
            &mut phase_norm_limbs_pointer as *mut u64 as *mut c_void,
            &mut productive_target_norm_pointer as *mut u64 as *mut c_void,
            &mut phase_locked_pointer as *mut u64 as *mut c_void,
            &mut phase_square_scratch_pointer as *mut u64 as *mut c_void,
            &mut phase_left_cross_scratch_pointer as *mut u64 as *mut c_void,
            &mut phase_right_cross_scratch_pointer as *mut u64 as *mut c_void,
            &mut complete_native_face_population_wire as *mut u32 as *mut c_void,
            &mut component_count_wire as *mut u32 as *mut c_void,
            &mut compatibility_limb_count_wire as *mut u32 as *mut c_void,
            &mut norm_limb_count_wire as *mut u32 as *mut c_void,
            &mut productive_limb_count_wire as *mut u32 as *mut c_void,
            &mut square_limb_count_wire as *mut u32 as *mut c_void,
            &mut cross_limb_count_wire as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    phase_select_direct,
                    phase_select_grid,
                    1,
                    1,
                    word.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    phase_select_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(select_membrane_boundary_phase_front_complete_receiver_direct)",
        )?;
    } else {
        let mut one_complete_receiver_chart_wire = 1_u32;
        let mut phase_select_arguments: [*mut c_void; 14] = [
            &mut compatibility_sign_pointer as *mut u64 as *mut c_void,
            &mut compatibility_limbs_pointer as *mut u64 as *mut c_void,
            &mut phase_norm_limbs_pointer as *mut u64 as *mut c_void,
            &mut phase_locked_pointer as *mut u64 as *mut c_void,
            &mut phase_square_scratch_pointer as *mut u64 as *mut c_void,
            &mut phase_left_cross_scratch_pointer as *mut u64 as *mut c_void,
            &mut phase_right_cross_scratch_pointer as *mut u64 as *mut c_void,
            &mut complete_native_face_population_wire as *mut u32 as *mut c_void,
            &mut one_complete_receiver_chart_wire as *mut u32 as *mut c_void,
            &mut component_count_wire as *mut u32 as *mut c_void,
            &mut compatibility_limb_count_wire as *mut u32 as *mut c_void,
            &mut norm_limb_count_wire as *mut u32 as *mut c_void,
            &mut square_limb_count_wire as *mut u32 as *mut c_void,
            &mut cross_limb_count_wire as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    phase_select_direct,
                    phase_select_grid,
                    1,
                    1,
                    word.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    phase_select_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(select_membrane_boundary_phase_front_direct)",
        )?;
    }

    let mut incoming_real_sign_pointer = incoming_real_sign_device.pointer;
    let mut incoming_real_limbs_pointer = incoming_real_limbs_device.pointer;
    let mut incoming_imaginary_sign_pointer = incoming_imaginary_sign_device.pointer;
    let mut incoming_imaginary_limbs_pointer = incoming_imaginary_limbs_device.pointer;
    let mut situated_pairing_sign_pointer = situated_pairing_sign.pointer;
    let mut situated_pairing_limbs_pointer = situated_pairing_limbs.pointer;
    let mut situated_pairing_imaginary_scratch_pointer = situated_pairing_imaginary_scratch.pointer;
    let mut situated_pairing_front_pointer = situated_pairing_front.pointer;
    let mut incoming_limb_count_wire = stored_limb_count as u32;
    let mut situated_pairing_limb_count_wire = situated_pairing_limb_count as u32;
    let mut situated_pairing_arguments: [*mut c_void; 16] = [
        &mut port_real_sign_pointer as *mut u64 as *mut c_void,
        &mut port_real_limbs_pointer as *mut u64 as *mut c_void,
        &mut port_imaginary_sign_pointer as *mut u64 as *mut c_void,
        &mut port_imaginary_limbs_pointer as *mut u64 as *mut c_void,
        &mut incoming_real_sign_pointer as *mut u64 as *mut c_void,
        &mut incoming_real_limbs_pointer as *mut u64 as *mut c_void,
        &mut incoming_imaginary_sign_pointer as *mut u64 as *mut c_void,
        &mut incoming_imaginary_limbs_pointer as *mut u64 as *mut c_void,
        &mut phase_locked_pointer as *mut u64 as *mut c_void,
        &mut situated_pairing_sign_pointer as *mut u64 as *mut c_void,
        &mut situated_pairing_limbs_pointer as *mut u64 as *mut c_void,
        &mut situated_pairing_imaginary_scratch_pointer as *mut u64 as *mut c_void,
        &mut port_count_wire as *mut u32 as *mut c_void,
        &mut radiation_limb_count_wire as *mut u32 as *mut c_void,
        &mut incoming_limb_count_wire as *mut u32 as *mut c_void,
        &mut situated_pairing_limb_count_wire as *mut u32 as *mut c_void,
    ];
    driver(
        unsafe {
            cuLaunchKernel(
                word.card.membrane_situated_output_pairing,
                phase_select_grid,
                1,
                1,
                word.card.block_x,
                1,
                1,
                0,
                ptr::null_mut(),
                situated_pairing_arguments.as_mut_ptr(),
                ptr::null_mut(),
            )
        },
        "cuLaunchKernel(form_membrane_situated_output_pairing)",
    )?;
    let mut situated_select_direct = ptr::null_mut();
    // The native phase section retains its addressed target-state direct sum, but the
    // presented exterior current is precisely the receiver which makes those otherwise
    // incomparable alternatives commensurable: every `Re(conj(J) R_face)` occupies the same
    // signed quantity line.  Comparing that returned line separately inside each prospective
    // successor state would preserve one winner *per answer state* and therefore prevent the
    // receiver from ever selecting an answer.  Keep every native phase face and its target
    // address as reconstruction testimony, then take the maximum fibre of this one declared
    // exterior receiver over the complete native population.
    let situated_select_name = if relational_observer_present {
        c"select_membrane_situated_relational_then_output_front_direct"
    } else {
        c"select_membrane_situated_output_pairing_front_direct"
    };
    driver(
        unsafe {
            cuModuleGetFunction(
                &mut situated_select_direct,
                word.card.module,
                situated_select_name.as_ptr(),
            )
        },
        "cuModuleGetFunction(select_membrane_situated_output_pairing_front_target_state_direct)",
    )?;
    let mut complete_response_population_wire = response_population as u32;
    if relational_observer_present {
        let mut relational_component_wire = word
            .families
            .checked_add(word.receiver_count)
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let mut situated_select_arguments: [*mut c_void; 18] = [
            &mut phase_locked_pointer as *mut u64 as *mut c_void,
            &mut compatibility_sign_pointer as *mut u64 as *mut c_void,
            &mut compatibility_limbs_pointer as *mut u64 as *mut c_void,
            &mut phase_norm_limbs_pointer as *mut u64 as *mut c_void,
            &mut situated_pairing_sign_pointer as *mut u64 as *mut c_void,
            &mut situated_pairing_limbs_pointer as *mut u64 as *mut c_void,
            &mut situated_pairing_front_pointer as *mut u64 as *mut c_void,
            &mut phase_square_scratch_pointer as *mut u64 as *mut c_void,
            &mut phase_left_cross_scratch_pointer as *mut u64 as *mut c_void,
            &mut phase_right_cross_scratch_pointer as *mut u64 as *mut c_void,
            &mut complete_response_population_wire as *mut u32 as *mut c_void,
            &mut component_count_wire as *mut u32 as *mut c_void,
            &mut relational_component_wire as *mut u32 as *mut c_void,
            &mut compatibility_limb_count_wire as *mut u32 as *mut c_void,
            &mut norm_limb_count_wire as *mut u32 as *mut c_void,
            &mut situated_pairing_limb_count_wire as *mut u32 as *mut c_void,
            &mut square_limb_count_wire as *mut u32 as *mut c_void,
            &mut cross_limb_count_wire as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    situated_select_direct,
                    phase_select_grid,
                    1,
                    1,
                    word.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    situated_select_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(select_membrane_situated_relational_then_output_front_direct)",
        )?;
    } else {
        let mut one_exterior_receiver_chart_wire = 1_u32;
        let mut situated_select_arguments: [*mut c_void; 7] = [
            &mut phase_locked_pointer as *mut u64 as *mut c_void,
            &mut situated_pairing_sign_pointer as *mut u64 as *mut c_void,
            &mut situated_pairing_limbs_pointer as *mut u64 as *mut c_void,
            &mut situated_pairing_front_pointer as *mut u64 as *mut c_void,
            &mut complete_response_population_wire as *mut u32 as *mut c_void,
            &mut one_exterior_receiver_chart_wire as *mut u32 as *mut c_void,
            &mut situated_pairing_limb_count_wire as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    situated_select_direct,
                    phase_select_grid,
                    1,
                    1,
                    word.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    situated_select_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(select_membrane_situated_output_pairing_front_direct)",
        )?;
    }
    let mut stored_real_sign_pointer = stored_real_sign.pointer;
    let mut stored_real_limbs_pointer = stored_real_limbs.pointer;
    let mut stored_imaginary_sign_pointer = stored_imaginary_sign.pointer;
    let mut stored_imaginary_limbs_pointer = stored_imaginary_limbs.pointer;
    let mut balance_scratch_pointer = balance_scratch.pointer;
    let mut joint_scale_wire = joint_scale;
    let mut stored_limb_count_wire = stored_limb_count as u32;
    let mut balance_arguments: [*mut c_void; 16] = [
        &mut joint_real_sign_pointer as *mut u64 as *mut c_void,
        &mut joint_real_limbs_pointer as *mut u64 as *mut c_void,
        &mut joint_imaginary_sign_pointer as *mut u64 as *mut c_void,
        &mut joint_imaginary_limbs_pointer as *mut u64 as *mut c_void,
        &mut incoming_real_sign_pointer as *mut u64 as *mut c_void,
        &mut incoming_real_limbs_pointer as *mut u64 as *mut c_void,
        &mut incoming_imaginary_sign_pointer as *mut u64 as *mut c_void,
        &mut incoming_imaginary_limbs_pointer as *mut u64 as *mut c_void,
        &mut joint_scale_wire as *mut u64 as *mut c_void,
        &mut stored_real_sign_pointer as *mut u64 as *mut c_void,
        &mut stored_real_limbs_pointer as *mut u64 as *mut c_void,
        &mut stored_imaginary_sign_pointer as *mut u64 as *mut c_void,
        &mut stored_imaginary_limbs_pointer as *mut u64 as *mut c_void,
        &mut balance_scratch_pointer as *mut u64 as *mut c_void,
        &mut radiation_limb_count_wire as *mut u32 as *mut c_void,
        &mut stored_limb_count_wire as *mut u32 as *mut c_void,
    ];
    driver(
        unsafe {
            cuLaunchKernel(
                word.card.membrane_boundary_chain_balance,
                1,
                1,
                1,
                1,
                1,
                1,
                0,
                ptr::null_mut(),
                balance_arguments.as_mut_ptr(),
                ptr::null_mut(),
            )
        },
        "cuLaunchKernel(balance_membrane_quadratic_moment_chain)",
    )?;
    driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
    if cuda_profile {
        eprintln!(
            "mem6-cuda through_terminal_sync_ms={}",
            resident_began.elapsed().as_millis(),
        );
    }
    Ok(())
}
