use super::*;

use super::membrane_boundary_plan::BoundaryCompletionPlan;
use super::membrane_boundary_workspace::BoundaryCompletionWorkspace;

/// State returned by the support/radiation/phase launch sequence.
///
/// The native successor buffer is carried out of the helper so it remains live beside every
/// downstream receiver until the terminal image completion and host readback.
pub(super) struct BoundarySupportPhaseReceipt {
    pub(super) complete_native_successor_front: Buffer,
    pub(super) complete_successor_launches: u64,
    pub(super) situated_phase_locked_pointer: u64,
    pub(super) situated_count_wire: u32,
    pub(super) situated_phase_select_grid: u32,
    pub(super) situated_phase_pair_grid: u32,
}

pub(super) fn enqueue_support_radiation_phase(
    word: &ResidentMembraneInteriorWord,
    plan: &BoundaryCompletionPlan,
    workspace: &BoundaryCompletionWorkspace,
) -> Result<BoundarySupportPhaseReceipt, CudaRefineError> {
    let port_population = plan.port_population;
    let support_count = plan.support_count;
    let family_count = plan.family_count;
    let opaque_receiver_count = plan.opaque_receiver_count;
    let support_port_pointer = plan.support_port_pointer;
    let support_receiver_class_pointer = plan.support_receiver_class_pointer;
    let support_quadratic_scale_pointer = plan.support_quadratic_scale_pointer;
    let support_quadratic_scale_limb_count = plan.support_quadratic_scale_limb_count;
    let receiver_sign_pointer = plan.receiver_sign_pointer;
    let receiver_limbs_pointer = plan.receiver_limbs_pointer;
    let receiver_limb_count = plan.receiver_limb_count;
    let overlap_limb_count = plan.overlap_limb_count;
    let contact_limb_count = plan.contact_limb_count;
    let radiation_limb_count = plan.radiation_limb_count;
    let compatibility_limb_count = plan.compatibility_limb_count;
    let norm_limb_count = plan.norm_limb_count;
    let square_limb_count = plan.square_limb_count;
    let cross_limb_count = plan.cross_limb_count;
    let component_count = plan.component_count;
    let component_population = plan.component_population;
    let phase_pair_population = plan.phase_pair_population;
    let situated_population = plan.situated_population;
    let situated_pair_population = plan.situated_pair_population;

    let obstruction = &workspace.obstruction;
    let action_sign = &workspace.action_sign;
    let action_limbs = &workspace.action_limbs;
    let reflected_sign = &workspace.reflected_sign;
    let reflected_limbs = &workspace.reflected_limbs;
    let opaque_receiver_sign = &workspace.opaque_receiver_sign;
    let opaque_receiver_limbs = &workspace.opaque_receiver_limbs;
    let receiver_norm_sign = &workspace.receiver_norm_sign;
    let receiver_norm_limbs = &workspace.receiver_norm_limbs;
    let contact_real_sign = &workspace.contact_real_sign;
    let contact_real_limbs = &workspace.contact_real_limbs;
    let contact_imaginary_sign = &workspace.contact_imaginary_sign;
    let contact_imaginary_limbs = &workspace.contact_imaginary_limbs;
    let support_real_sign = &workspace.support_real_sign;
    let support_real_limbs = &workspace.support_real_limbs;
    let support_imaginary_sign = &workspace.support_imaginary_sign;
    let support_imaginary_limbs = &workspace.support_imaginary_limbs;
    let port_real_sign = &workspace.port_real_sign;
    let port_real_limbs = &workspace.port_real_limbs;
    let port_imaginary_sign = &workspace.port_imaginary_sign;
    let port_imaginary_limbs = &workspace.port_imaginary_limbs;
    let joint_real_sign = &workspace.joint_real_sign;
    let joint_real_limbs = &workspace.joint_real_limbs;
    let joint_imaginary_sign = &workspace.joint_imaginary_sign;
    let joint_imaginary_limbs = &workspace.joint_imaginary_limbs;
    let port_action_sign = &workspace.port_action_sign;
    let port_action_limbs = &workspace.port_action_limbs;
    let port_reflected_sign = &workspace.port_reflected_sign;
    let port_reflected_limbs = &workspace.port_reflected_limbs;
    let port_receiver_sign = &workspace.port_receiver_sign;
    let port_receiver_limbs = &workspace.port_receiver_limbs;
    let port_receiver_norm_sign = &workspace.port_receiver_norm_sign;
    let port_receiver_norm_limbs = &workspace.port_receiver_norm_limbs;
    let compatibility_sign = &workspace.compatibility_sign;
    let compatibility_limbs = &workspace.compatibility_limbs;
    let phase_norm_limbs = &workspace.phase_norm_limbs;
    let phase_locked = &workspace.phase_locked;
    let phase_pair_dominates = &workspace.phase_pair_dominates;
    let phase_square_scratch = &workspace.phase_square_scratch;
    let phase_left_cross_scratch = &workspace.phase_left_cross_scratch;
    let phase_right_cross_scratch = &workspace.phase_right_cross_scratch;
    let situated_native_phase_front = &workspace.situated_native_phase_front;
    let mut receiver_sign_pointer = receiver_sign_pointer;
    let mut receiver_limbs_pointer = receiver_limbs_pointer;
    let mut support_port_pointer = support_port_pointer;
    let mut support_receiver_class_pointer = support_receiver_class_pointer;
    let mut support_quadratic_scale_pointer = support_quadratic_scale_pointer;
    let mut family_real_sign_pointer = word.family_real_sign.pointer;
    let mut family_real_limbs_pointer = word.family_real_limbs.pointer;
    let mut family_imaginary_sign_pointer = word.family_imaginary_sign.pointer;
    let mut family_imaginary_limbs_pointer = word.family_imaginary_limbs.pointer;
    let mut action_sign_pointer = action_sign.pointer;
    let mut action_limbs_pointer = action_limbs.pointer;
    let mut reflected_sign_pointer = reflected_sign.pointer;
    let mut reflected_limbs_pointer = reflected_limbs.pointer;
    let mut opaque_receiver_sign_pointer = opaque_receiver_sign.pointer;
    let mut opaque_receiver_limbs_pointer = opaque_receiver_limbs.pointer;
    let mut receiver_norm_sign_pointer = receiver_norm_sign.pointer;
    let mut receiver_norm_limbs_pointer = receiver_norm_limbs.pointer;
    let mut contact_real_sign_pointer = contact_real_sign.pointer;
    let mut contact_real_limbs_pointer = contact_real_limbs.pointer;
    let mut contact_imaginary_sign_pointer = contact_imaginary_sign.pointer;
    let mut contact_imaginary_limbs_pointer = contact_imaginary_limbs.pointer;
    let mut obstruction_pointer = obstruction.pointer;
    let mut support_count_wire = support_count as u32;
    let mut port_count_wire = port_population as u32;
    let mut family_count_wire = family_count as u32;
    let mut opaque_receiver_count_wire = opaque_receiver_count as u32;
    let mut receiver_limb_count_wire = receiver_limb_count as u32;
    let mut support_quadratic_scale_limb_count_wire = support_quadratic_scale_limb_count as u32;
    let mut overlap_limb_count_wire = overlap_limb_count as u32;
    let mut family_limb_count_wire = word.family_limb_count;
    let mut contact_limb_count_wire = contact_limb_count as u32;
    let mut prepare_arguments: [*mut c_void; 31] = [
        &mut receiver_sign_pointer as *mut u64 as *mut c_void,
        &mut receiver_limbs_pointer as *mut u64 as *mut c_void,
        &mut support_port_pointer as *mut u64 as *mut c_void,
        &mut support_receiver_class_pointer as *mut u64 as *mut c_void,
        &mut support_quadratic_scale_pointer as *mut u64 as *mut c_void,
        &mut family_real_sign_pointer as *mut u64 as *mut c_void,
        &mut family_real_limbs_pointer as *mut u64 as *mut c_void,
        &mut family_imaginary_sign_pointer as *mut u64 as *mut c_void,
        &mut family_imaginary_limbs_pointer as *mut u64 as *mut c_void,
        &mut action_sign_pointer as *mut u64 as *mut c_void,
        &mut action_limbs_pointer as *mut u64 as *mut c_void,
        &mut reflected_sign_pointer as *mut u64 as *mut c_void,
        &mut reflected_limbs_pointer as *mut u64 as *mut c_void,
        &mut opaque_receiver_sign_pointer as *mut u64 as *mut c_void,
        &mut opaque_receiver_limbs_pointer as *mut u64 as *mut c_void,
        &mut receiver_norm_sign_pointer as *mut u64 as *mut c_void,
        &mut receiver_norm_limbs_pointer as *mut u64 as *mut c_void,
        &mut contact_real_sign_pointer as *mut u64 as *mut c_void,
        &mut contact_real_limbs_pointer as *mut u64 as *mut c_void,
        &mut contact_imaginary_sign_pointer as *mut u64 as *mut c_void,
        &mut contact_imaginary_limbs_pointer as *mut u64 as *mut c_void,
        &mut obstruction_pointer as *mut u64 as *mut c_void,
        &mut support_count_wire as *mut u32 as *mut c_void,
        &mut port_count_wire as *mut u32 as *mut c_void,
        &mut family_count_wire as *mut u32 as *mut c_void,
        &mut opaque_receiver_count_wire as *mut u32 as *mut c_void,
        &mut receiver_limb_count_wire as *mut u32 as *mut c_void,
        &mut support_quadratic_scale_limb_count_wire as *mut u32 as *mut c_void,
        &mut overlap_limb_count_wire as *mut u32 as *mut c_void,
        &mut family_limb_count_wire as *mut u32 as *mut c_void,
        &mut contact_limb_count_wire as *mut u32 as *mut c_void,
    ];
    let prepare_work = support_count
        .checked_mul(family_count.max(opaque_receiver_count))
        .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
    let prepare_grid = word.card.grid_for(prepare_work as u64)?;
    driver(
        unsafe {
            cuLaunchKernel(
                word.card.membrane_factored_receiver_boundary_supports,
                prepare_grid,
                1,
                1,
                word.card.block_x,
                1,
                1,
                0,
                ptr::null_mut(),
                prepare_arguments.as_mut_ptr(),
                ptr::null_mut(),
            )
        },
        "cuLaunchKernel(prepare_membrane_factored_receiver_boundary_supports)",
    )?;

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
    let mut radiation_limb_count_wire = radiation_limb_count as u32;
    let mut radiation_arguments: [*mut c_void; 40] = [
        &mut support_port_pointer as *mut u64 as *mut c_void,
        &mut action_sign_pointer as *mut u64 as *mut c_void,
        &mut action_limbs_pointer as *mut u64 as *mut c_void,
        &mut reflected_sign_pointer as *mut u64 as *mut c_void,
        &mut reflected_limbs_pointer as *mut u64 as *mut c_void,
        &mut opaque_receiver_sign_pointer as *mut u64 as *mut c_void,
        &mut opaque_receiver_limbs_pointer as *mut u64 as *mut c_void,
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
        &mut opaque_receiver_count_wire as *mut u32 as *mut c_void,
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
        "cuLaunchKernel(gather_membrane_factored_image_radiation)",
    )?;

    let mut compatibility_sign_pointer = compatibility_sign.pointer;
    let mut compatibility_limbs_pointer = compatibility_limbs.pointer;
    let mut phase_norm_limbs_pointer = phase_norm_limbs.pointer;
    let mut phase_locked_pointer = phase_locked.pointer;
    let mut phase_pair_dominates_pointer = phase_pair_dominates.pointer;
    let mut phase_square_scratch_pointer = phase_square_scratch.pointer;
    let mut phase_left_cross_scratch_pointer = phase_left_cross_scratch.pointer;
    let mut phase_right_cross_scratch_pointer = phase_right_cross_scratch.pointer;
    let mut compatibility_limb_count_wire = compatibility_limb_count as u32;
    let mut norm_limb_count_wire = norm_limb_count as u32;
    let mut square_limb_count_wire = square_limb_count as u32;
    let mut cross_limb_count_wire = cross_limb_count as u32;
    let mut component_count_wire = component_count as u32;
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
        &mut opaque_receiver_count_wire as *mut u32 as *mut c_void,
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
        "cuLaunchKernel(form_membrane_factored_image_phase_components)",
    )?;
    let mut local_response_population_wire = port_population as u32;
    let mut response_state_count_wire = 1_u32;
    let mut phase_pair_arguments: [*mut c_void; 14] = [
        &mut compatibility_sign_pointer as *mut u64 as *mut c_void,
        &mut compatibility_limbs_pointer as *mut u64 as *mut c_void,
        &mut phase_norm_limbs_pointer as *mut u64 as *mut c_void,
        &mut phase_pair_dominates_pointer as *mut u64 as *mut c_void,
        &mut phase_square_scratch_pointer as *mut u64 as *mut c_void,
        &mut phase_left_cross_scratch_pointer as *mut u64 as *mut c_void,
        &mut phase_right_cross_scratch_pointer as *mut u64 as *mut c_void,
        &mut local_response_population_wire as *mut u32 as *mut c_void,
        &mut response_state_count_wire as *mut u32 as *mut c_void,
        &mut component_count_wire as *mut u32 as *mut c_void,
        &mut compatibility_limb_count_wire as *mut u32 as *mut c_void,
        &mut norm_limb_count_wire as *mut u32 as *mut c_void,
        &mut square_limb_count_wire as *mut u32 as *mut c_void,
        &mut cross_limb_count_wire as *mut u32 as *mut c_void,
    ];
    let phase_pair_grid = word.card.grid_for(phase_pair_population as u64)?;
    driver(
        unsafe {
            cuLaunchKernel(
                word.card.membrane_boundary_phase_pairs,
                phase_pair_grid,
                1,
                1,
                word.card.block_x,
                1,
                1,
                0,
                ptr::null_mut(),
                phase_pair_arguments.as_mut_ptr(),
                ptr::null_mut(),
            )
        },
        "cuLaunchKernel(compare_membrane_factored_image_phase_pairs)",
    )?;
    let mut phase_select_arguments: [*mut c_void; 4] = [
        &mut phase_pair_dominates_pointer as *mut u64 as *mut c_void,
        &mut phase_locked_pointer as *mut u64 as *mut c_void,
        &mut local_response_population_wire as *mut u32 as *mut c_void,
        &mut response_state_count_wire as *mut u32 as *mut c_void,
    ];
    let phase_select_grid = word.card.grid_for(port_population as u64)?;
    driver(
        unsafe {
            cuLaunchKernel(
                word.card.membrane_boundary_phase_select,
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
        "cuLaunchKernel(select_membrane_factored_image_phase_front)",
    )?;

    let mut situated_count_wire = situated_population as u32;
    let situated_phase_select_grid = word.card.grid_for(situated_population as u64)?;
    let situated_phase_pair_grid = word.card.grid_for(situated_pair_population as u64)?;
    // The complete native successor precedes every observer.  This device-local carrier
    // admits every addressed face whose mounted restriction is present; the conditioning
    // kernels themselves retain the exact zero/nonzero current support.  Situated and
    // projective fronts remain downstream receiver testimony and never enter this mask.
    // Only the state-addressed sparse path owns a device support mask in this observer
    // chart.  The compact factored path carries its complete successor as an image address
    // plus an independently typed incidence boundary; zero-initialize this downstream
    // observer buffer so it cannot invent native support.
    let complete_native_successor_front = Buffer::of(&vec![0_u8; situated_population])?;
    let complete_successor_launches = 0_u64;
    let situated_phase_locked_pointer =
        if let Some(face_front) = situated_native_phase_front.as_ref() {
            if trace_configuration().holonics_phase_trace {
                eprintln!("uar2-boundary-phase-lift-enter");
            }
            let mut face_ports_pointer = support_port_pointer;
            let mut face_present_pointer = word
                .factored_receiver_history
                .as_ref()
                .and_then(|mount| mount.transported_image.as_ref())
                .and_then(|transport| transport.sparse_native_boundary.as_ref())
                .map(|native| native.restriction_present.pointer)
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let mut face_front_pointer = face_front.pointer;
            let mut exterior_port_count_wire = port_population as u32;
            let mut lift_arguments: [*mut c_void; 6] = [
                &mut phase_locked_pointer as *mut u64 as *mut c_void,
                &mut face_ports_pointer as *mut u64 as *mut c_void,
                &mut face_present_pointer as *mut u64 as *mut c_void,
                &mut face_front_pointer as *mut u64 as *mut c_void,
                &mut exterior_port_count_wire as *mut u32 as *mut c_void,
                &mut situated_count_wire as *mut u32 as *mut c_void,
            ];
            driver(
                unsafe {
                    cuLaunchKernel(
                        word.card.membrane_sparse_quadratic_phase_front_lift,
                        situated_phase_select_grid,
                        1,
                        1,
                        word.card.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        lift_arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(lift_membrane_phase_front_to_addressed_faces)",
            )?;
            face_front.pointer
        } else {
            phase_locked.pointer
        };

    Ok(BoundarySupportPhaseReceipt {
        complete_native_successor_front,
        complete_successor_launches,
        situated_phase_locked_pointer,
        situated_count_wire,
        situated_phase_select_grid,
        situated_phase_pair_grid,
    })
}
