use super::*;

use super::membrane_boundary_plan::BoundaryCompletionPlan;
use super::membrane_boundary_workspace::buffer_octets;

/// Optional fixed-prefix projective narrowing and its resident evidence.
pub(super) struct BoundaryIntervalStage {
    pub(super) workspace: Vec<Buffer>,
    pub(super) workspace_octets: u64,
    pub(super) launches: u64,
    pub(super) candidate_front: Option<Buffer>,
    pub(super) obstruction: Option<Buffer>,
    pub(super) phase_locked_pointer: u64,
}

pub(super) fn stage_projective_interval(
    word: &mut ResidentMembraneInteriorWord,
    plan: &BoundaryCompletionPlan,
    initial_phase_locked_pointer: u64,
    situated_phase_select_grid: u32,
    situated_phase_pair_grid: u32,
) -> Result<BoundaryIntervalStage, CudaRefineError> {
    let mut situated_phase_locked_pointer = initial_phase_locked_pointer;
    // A fixed-prefix integer interval passage may narrow the exact-work aperture before the
    // arbitrary-limb projective contraction.  Its strict dominance certificate is only an
    // acceleration: interval overlap retains both faces, arithmetic obstruction reopens the
    // complete native phase front on the device, and the final exact comparator remains the
    // sole situated receiver.  The original addressed phase front is never overwritten.
    let mut projective_interval_workspace = Vec::<Buffer>::new();
    let mut projective_interval_workspace_octets = 0_u64;
    let mut projective_interval_launches = 0_u64;
    let mut projective_candidate_front = None::<Buffer>;
    let mut projective_interval_obstruction = None::<Buffer>;
    if let Some((
        source_state_population,
        _,
        pair_population,
        pair_factors,
        current,
        current_limb_count,
        ingress_receiver,
        ingress_receiver_limb_count,
        restrictions,
        restriction_present,
        restriction_limb_count,
        _,
        _,
        _,
        _,
        output_limb_count,
    )) = plan.native_sparse_situated_aperture.as_ref()
    {
        const INTERVAL_PAIR_CHUNK: usize = 4096;
        const INTERVAL_PAYLOAD_LIMBS: usize = 24;
        const INTERVAL_LIMBS: usize = INTERVAL_PAYLOAD_LIMBS + 2;
        if *source_state_population == 1 && *restriction_limb_count == 1 {
            let chunk_count = pair_population.div_ceil(INTERVAL_PAIR_CHUNK);
            let section_count = plan
                .situated_population
                .checked_mul(3)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            let partial_population = section_count
                .checked_mul(chunk_count)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            let reduced_population = section_count
                .checked_mul(chunk_count.div_ceil(1024).max(1))
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            let work_population = plan
                .situated_population
                .checked_mul(chunk_count)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            let interval_square_limbs = INTERVAL_LIMBS
                .checked_mul(2)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            let interval_cross_limbs = interval_square_limbs
                .checked_mul(2)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            let partial_lower = Buffer::alloc(buffer_octets(partial_population, INTERVAL_LIMBS)?)?;
            let partial_upper = Buffer::alloc(buffer_octets(partial_population, INTERVAL_LIMBS)?)?;
            let reduce_lower = Buffer::alloc(buffer_octets(reduced_population, INTERVAL_LIMBS)?)?;
            let reduce_upper = Buffer::alloc(buffer_octets(reduced_population, INTERVAL_LIMBS)?)?;
            let final_lower = Buffer::alloc(buffer_octets(section_count, INTERVAL_LIMBS)?)?;
            let final_upper = Buffer::alloc(buffer_octets(section_count, INTERVAL_LIMBS)?)?;
            let pair_dominates = Buffer::alloc(plan.situated_pair_population)?;
            let interval_square = Buffer::alloc(buffer_octets(
                plan.situated_pair_population,
                interval_square_limbs,
            )?)?;
            let interval_denominator = Buffer::alloc(buffer_octets(
                plan.situated_pair_population,
                interval_square_limbs,
            )?)?;
            let interval_left_cross = Buffer::alloc(buffer_octets(
                plan.situated_pair_population,
                interval_cross_limbs,
            )?)?;
            let interval_right_cross = Buffer::alloc(buffer_octets(
                plan.situated_pair_population,
                interval_cross_limbs,
            )?)?;
            let candidate_front = Buffer::alloc(plan.situated_population)?;
            let interval_obstruction = Buffer::of(&[0_u32])?;

            let mut phase_front_pointer = situated_phase_locked_pointer;
            let mut pair_factors_pointer = *pair_factors;
            let mut current_pointer = *current;
            let mut ingress_receiver_pointer = *ingress_receiver;
            let mut restrictions_pointer = *restrictions;
            let mut restriction_present_pointer = *restriction_present;
            let mut partial_lower_pointer = partial_lower.pointer;
            let mut partial_upper_pointer = partial_upper.pointer;
            let mut pair_count_wire = *pair_population as u32;
            let mut factor_count_wire = word.factors;
            let mut face_count_wire = plan.situated_population as u32;
            let mut generator_count_wire = plan.generator_count as u32;
            let mut chunk_count_wire = chunk_count as u32;
            let mut chunk_size_wire = INTERVAL_PAIR_CHUNK as u32;
            let mut current_limb_count_wire = *current_limb_count as u32;
            let mut ingress_receiver_limb_count_wire = *ingress_receiver_limb_count as u32;
            let mut restriction_limb_count_wire = *restriction_limb_count as u32;
            let mut output_limb_count_wire = *output_limb_count as u32;
            let mut interval_limb_count_wire = INTERVAL_LIMBS as u32;
            let mut interval_payload_limbs_wire = INTERVAL_PAYLOAD_LIMBS as u32;
            let mut interval_obstruction_pointer = interval_obstruction.pointer;
            let mut interval_arguments: [*mut c_void; 21] = [
                &mut phase_front_pointer as *mut u64 as *mut c_void,
                &mut pair_factors_pointer as *mut u64 as *mut c_void,
                &mut current_pointer as *mut u64 as *mut c_void,
                &mut ingress_receiver_pointer as *mut u64 as *mut c_void,
                &mut restrictions_pointer as *mut u64 as *mut c_void,
                &mut restriction_present_pointer as *mut u64 as *mut c_void,
                &mut partial_lower_pointer as *mut u64 as *mut c_void,
                &mut partial_upper_pointer as *mut u64 as *mut c_void,
                &mut pair_count_wire as *mut u32 as *mut c_void,
                &mut factor_count_wire as *mut u32 as *mut c_void,
                &mut face_count_wire as *mut u32 as *mut c_void,
                &mut generator_count_wire as *mut u32 as *mut c_void,
                &mut chunk_count_wire as *mut u32 as *mut c_void,
                &mut chunk_size_wire as *mut u32 as *mut c_void,
                &mut current_limb_count_wire as *mut u32 as *mut c_void,
                &mut ingress_receiver_limb_count_wire as *mut u32 as *mut c_void,
                &mut restriction_limb_count_wire as *mut u32 as *mut c_void,
                &mut output_limb_count_wire as *mut u32 as *mut c_void,
                &mut interval_limb_count_wire as *mut u32 as *mut c_void,
                &mut interval_payload_limbs_wire as *mut u32 as *mut c_void,
                &mut interval_obstruction_pointer as *mut u64 as *mut c_void,
            ];
            driver(
                unsafe {
                    cuLaunchKernel(
                        word.card
                            .membrane_sparse_quadratic_projective_interval_chunks,
                        word.card.grid_for(work_population as u64)?,
                        1,
                        1,
                        word.card.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        interval_arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(form_membrane_sparse_quadratic_projective_interval_chunks)",
            )?;
            let lower_reduction_launches = word.reduce_sparse_quadratic_unsigned_intervals(
                &partial_lower,
                &reduce_lower,
                &final_lower,
                section_count,
                chunk_count,
                INTERVAL_LIMBS,
                &interval_obstruction,
            )?;
            let upper_reduction_launches = word.reduce_sparse_quadratic_unsigned_intervals(
                &partial_upper,
                &reduce_upper,
                &final_upper,
                section_count,
                chunk_count,
                INTERVAL_LIMBS,
                &interval_obstruction,
            )?;
            let mut final_lower_pointer = final_lower.pointer;
            let mut final_upper_pointer = final_upper.pointer;
            let mut pair_dominates_pointer = pair_dominates.pointer;
            let mut square_pointer = interval_square.pointer;
            let mut denominator_pointer = interval_denominator.pointer;
            let mut left_cross_pointer = interval_left_cross.pointer;
            let mut right_cross_pointer = interval_right_cross.pointer;
            let mut interval_square_limbs_wire = interval_square_limbs as u32;
            let mut interval_cross_limbs_wire = interval_cross_limbs as u32;
            let mut compare_arguments: [*mut c_void; 12] = [
                &mut phase_front_pointer as *mut u64 as *mut c_void,
                &mut final_lower_pointer as *mut u64 as *mut c_void,
                &mut final_upper_pointer as *mut u64 as *mut c_void,
                &mut pair_dominates_pointer as *mut u64 as *mut c_void,
                &mut square_pointer as *mut u64 as *mut c_void,
                &mut denominator_pointer as *mut u64 as *mut c_void,
                &mut left_cross_pointer as *mut u64 as *mut c_void,
                &mut right_cross_pointer as *mut u64 as *mut c_void,
                &mut face_count_wire as *mut u32 as *mut c_void,
                &mut interval_limb_count_wire as *mut u32 as *mut c_void,
                &mut interval_square_limbs_wire as *mut u32 as *mut c_void,
                &mut interval_cross_limbs_wire as *mut u32 as *mut c_void,
            ];
            driver(
                unsafe {
                    cuLaunchKernel(
                        word.card
                            .membrane_sparse_quadratic_projective_interval_pairs,
                        situated_phase_pair_grid,
                        1,
                        1,
                        word.card.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        compare_arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(compare_membrane_sparse_quadratic_projective_interval_pairs)",
            )?;
            let mut candidate_pointer = candidate_front.pointer;
            let mut select_arguments: [*mut c_void; 5] = [
                &mut phase_front_pointer as *mut u64 as *mut c_void,
                &mut pair_dominates_pointer as *mut u64 as *mut c_void,
                &mut interval_obstruction_pointer as *mut u64 as *mut c_void,
                &mut candidate_pointer as *mut u64 as *mut c_void,
                &mut face_count_wire as *mut u32 as *mut c_void,
            ];
            driver(
                unsafe {
                    cuLaunchKernel(
                        word.card
                            .membrane_sparse_quadratic_projective_interval_select,
                        situated_phase_select_grid,
                        1,
                        1,
                        word.card.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        select_arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(select_membrane_sparse_quadratic_projective_interval_front)",
            )?;
            let mut ensure_arguments: [*mut c_void; 4] = [
                &mut phase_front_pointer as *mut u64 as *mut c_void,
                &mut candidate_pointer as *mut u64 as *mut c_void,
                &mut face_count_wire as *mut u32 as *mut c_void,
                &mut interval_obstruction_pointer as *mut u64 as *mut c_void,
            ];
            driver(
                unsafe {
                    cuLaunchKernel(
                        word.card
                            .membrane_sparse_quadratic_projective_interval_ensure,
                        1,
                        1,
                        1,
                        1,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        ensure_arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(ensure_membrane_sparse_quadratic_projective_interval_front)",
            )?;
            situated_phase_locked_pointer = candidate_front.pointer;
            projective_interval_launches = lower_reduction_launches
                .saturating_add(upper_reduction_launches)
                .saturating_add(4);
            projective_interval_workspace_octets = [
                buffer_octets(partial_population, INTERVAL_LIMBS)?,
                buffer_octets(partial_population, INTERVAL_LIMBS)?,
                buffer_octets(reduced_population, INTERVAL_LIMBS)?,
                buffer_octets(reduced_population, INTERVAL_LIMBS)?,
                buffer_octets(section_count, INTERVAL_LIMBS)?,
                buffer_octets(section_count, INTERVAL_LIMBS)?,
                plan.situated_pair_population,
                buffer_octets(plan.situated_pair_population, interval_square_limbs)?,
                buffer_octets(plan.situated_pair_population, interval_square_limbs)?,
                buffer_octets(plan.situated_pair_population, interval_cross_limbs)?,
                buffer_octets(plan.situated_pair_population, interval_cross_limbs)?,
                plan.situated_population,
                std::mem::size_of::<u32>(),
            ]
            .into_iter()
            .try_fold(0_u64, |sum, octets| {
                sum.checked_add(u64::try_from(octets).ok()?)
            })
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            projective_interval_workspace.extend([
                partial_lower,
                partial_upper,
                reduce_lower,
                reduce_upper,
                final_lower,
                final_upper,
                pair_dominates,
                interval_square,
                interval_denominator,
                interval_left_cross,
                interval_right_cross,
            ]);
            projective_candidate_front = Some(candidate_front);
            projective_interval_obstruction = Some(interval_obstruction);
        }
    }

    Ok(BoundaryIntervalStage {
        workspace: projective_interval_workspace,
        workspace_octets: projective_interval_workspace_octets,
        launches: projective_interval_launches,
        candidate_front: projective_candidate_front,
        obstruction: projective_interval_obstruction,
        phase_locked_pointer: situated_phase_locked_pointer,
    })
}
