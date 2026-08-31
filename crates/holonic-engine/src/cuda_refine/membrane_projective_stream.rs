use super::*;

impl ResidentMembraneInteriorWord {
    pub(super) fn stage_streamed_sparse_projective_front(
        &mut self,
        native_phase_front_pointer: u64,
        quadratic_sign_pointer: u64,
        quadratic_limbs_pointer: u64,
        quadratic_compatibility_limb_count: usize,
        quadratic_norm_pointer: u64,
        quadratic_norm_limb_count: usize,
        quadratic_square_limb_count: usize,
        quadratic_cross_limb_count: usize,
        relational: Option<(u64, u64, usize, u64, usize, usize, usize)>,
        selected_front_pointer: u64,
        face_population: usize,
    ) -> Result<(Vec<Buffer>, u64, u64, usize), CudaRefineError> {
        if native_phase_front_pointer == 0
            || quadratic_sign_pointer == 0
            || quadratic_limbs_pointer == 0
            || quadratic_norm_pointer == 0
            || selected_front_pointer == 0
            || face_population == 0
            || quadratic_compatibility_limb_count == 0
            || quadratic_norm_limb_count == 0
            || quadratic_square_limb_count == 0
            || quadratic_cross_limb_count == 0
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        if relational.as_ref().is_some_and(
            |(signs, limbs, compatibility_limbs, norms, norm_limbs, square_limbs, cross_limbs)| {
                *signs == 0
                    || *limbs == 0
                    || *compatibility_limbs == 0
                    || *norms == 0
                    || *norm_limbs == 0
                    || *square_limbs == 0
                    || *cross_limbs == 0
            },
        ) {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let complete_pair_population = face_population
            .checked_mul(face_population)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let maximal_square_limb_count = relational
            .as_ref()
            .map(|relation| quadratic_square_limb_count.max(relation.5))
            .unwrap_or(quadratic_square_limb_count);
        let maximal_cross_limb_count = relational
            .as_ref()
            .map(|relation| quadratic_cross_limb_count.max(relation.6))
            .unwrap_or(quadratic_cross_limb_count);
        let relation_count = usize::from(relational.is_some()).saturating_add(1);
        let arena_layout = |population: usize| -> Option<(usize, usize, usize, usize, usize)> {
            let quadratic_relation_offset = 0_usize;
            let relational_relation_offset = population;
            let relation_octets = population.checked_mul(relation_count)?;
            let scratch_offset = relation_octets.checked_add(3)? & !3_usize;
            let square_offset = scratch_offset;
            let square_octets = population
                .checked_mul(maximal_square_limb_count)?
                .checked_mul(std::mem::size_of::<u32>())?;
            let left_cross_offset = square_offset.checked_add(square_octets)?;
            let cross_octets = population
                .checked_mul(maximal_cross_limb_count)?
                .checked_mul(std::mem::size_of::<u32>())?;
            let right_cross_offset = left_cross_offset.checked_add(cross_octets)?;
            let total = right_cross_offset.checked_add(cross_octets)?;
            Some((
                quadratic_relation_offset,
                relational_relation_offset,
                square_offset,
                left_cross_offset,
                total,
            ))
        };

        // CUDA schedules one warp as the elementary SIMD current.  Carry one warp of complete
        // challenged-face fibres per requested window, then let the live allocation aperture
        // narrow that request if the already-resident ecology leaves less space.
        const CUDA_WARP_WIDTH: usize = 32;
        let requested_window_population = face_population
            .checked_mul(CUDA_WARP_WIDTH)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?
            .min(complete_pair_population)
            .min(u32::MAX as usize);
        let challenged_dominated = Buffer::alloc(
            face_population
                .checked_mul(std::mem::size_of::<u32>())
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        )?;
        challenged_dominated.fill(
            0,
            face_population
                .checked_mul(std::mem::size_of::<u32>())
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        )?;
        let (window_population, arena) =
            Buffer::widest_repeated_aperture(requested_window_population, |population| {
                arena_layout(population).map(|layout| layout.4)
            })?;
        let (_, relational_relation_offset, square_offset, left_cross_offset, arena_octets) =
            arena_layout(window_population)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let cross_octets = window_population
            .checked_mul(maximal_cross_limb_count)
            .and_then(|words| words.checked_mul(std::mem::size_of::<u32>()))
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let right_cross_offset = left_cross_offset
            .checked_add(cross_octets)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let quadratic_pair_relation_pointer = arena.pointer;
        let relational_pair_relation_pointer = arena
            .pointer
            .checked_add(relational_relation_offset as u64)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let square_scratch_pointer = arena
            .pointer
            .checked_add(square_offset as u64)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let left_cross_scratch_pointer = arena
            .pointer
            .checked_add(left_cross_offset as u64)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let right_cross_scratch_pointer = arena
            .pointer
            .checked_add(right_cross_offset as u64)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;

        let mut compare_window = ptr::null_mut();
        let mut accumulate_window = ptr::null_mut();
        let mut select_front = ptr::null_mut();
        driver(
            unsafe {
                cuModuleGetFunction(
                    &mut compare_window,
                    self.card.module,
                    c"compare_membrane_sparse_quadratic_situated_projective_pair_window".as_ptr(),
                )
            },
            "cuModuleGetFunction(compare_membrane_sparse_quadratic_situated_projective_pair_window)",
        )?;
        driver(
            unsafe {
                cuModuleGetFunction(
                    &mut accumulate_window,
                    self.card.module,
                    c"accumulate_membrane_sparse_projective_pair_window".as_ptr(),
                )
            },
            "cuModuleGetFunction(accumulate_membrane_sparse_projective_pair_window)",
        )?;
        driver(
            unsafe {
                cuModuleGetFunction(
                    &mut select_front,
                    self.card.module,
                    c"select_membrane_sparse_projective_streamed_front".as_ptr(),
                )
            },
            "cuModuleGetFunction(select_membrane_sparse_projective_streamed_front)",
        )?;

        let mut launches = 0_u64;
        let mut pair_offset = 0_usize;
        while pair_offset < complete_pair_population {
            let pair_count = window_population.min(complete_pair_population - pair_offset);
            let mut native_front = native_phase_front_pointer;
            let mut compatibility_signs = quadratic_sign_pointer;
            let mut compatibility_limbs = quadratic_limbs_pointer;
            let mut norm_limbs = quadratic_norm_pointer;
            let mut pair_relation = quadratic_pair_relation_pointer;
            let mut square = square_scratch_pointer;
            let mut left_cross = left_cross_scratch_pointer;
            let mut right_cross = right_cross_scratch_pointer;
            let mut pair_offset_wire = pair_offset as u64;
            let mut pair_count_wire = pair_count as u32;
            let mut face_count_wire = face_population as u32;
            let mut compatibility_limb_count_wire = quadratic_compatibility_limb_count as u32;
            let mut norm_limb_count_wire = quadratic_norm_limb_count as u32;
            let mut square_limb_count_wire = maximal_square_limb_count as u32;
            let mut cross_limb_count_wire = maximal_cross_limb_count as u32;
            let mut compare_arguments: [*mut c_void; 15] = [
                &mut native_front as *mut u64 as *mut c_void,
                &mut compatibility_signs as *mut u64 as *mut c_void,
                &mut compatibility_limbs as *mut u64 as *mut c_void,
                &mut norm_limbs as *mut u64 as *mut c_void,
                &mut pair_relation as *mut u64 as *mut c_void,
                &mut square as *mut u64 as *mut c_void,
                &mut left_cross as *mut u64 as *mut c_void,
                &mut right_cross as *mut u64 as *mut c_void,
                &mut pair_offset_wire as *mut u64 as *mut c_void,
                &mut pair_count_wire as *mut u32 as *mut c_void,
                &mut face_count_wire as *mut u32 as *mut c_void,
                &mut compatibility_limb_count_wire as *mut u32 as *mut c_void,
                &mut norm_limb_count_wire as *mut u32 as *mut c_void,
                &mut square_limb_count_wire as *mut u32 as *mut c_void,
                &mut cross_limb_count_wire as *mut u32 as *mut c_void,
            ];
            driver(
                unsafe {
                    cuLaunchKernel(
                        compare_window,
                        self.card.grid_for(pair_count as u64)?,
                        1,
                        1,
                        self.card.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        compare_arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(compare sparse projective pair window)",
            )?;
            launches = launches.saturating_add(1);

            let mut relational_present_wire = 0_u32;
            if let Some((
                relational_signs,
                relational_limbs,
                relational_compatibility_limb_count,
                relational_norms,
                relational_norm_limb_count,
                _,
                _,
            )) = relational.as_ref()
            {
                let mut relational_compatibility_signs = *relational_signs;
                let mut relational_compatibility_limbs = *relational_limbs;
                let mut relational_norm_limbs = *relational_norms;
                let mut relational_pair_relation = relational_pair_relation_pointer;
                let mut relational_compatibility_limb_count_wire =
                    *relational_compatibility_limb_count as u32;
                let mut relational_norm_limb_count_wire = *relational_norm_limb_count as u32;
                let mut relational_compare_arguments: [*mut c_void; 15] = [
                    &mut native_front as *mut u64 as *mut c_void,
                    &mut relational_compatibility_signs as *mut u64 as *mut c_void,
                    &mut relational_compatibility_limbs as *mut u64 as *mut c_void,
                    &mut relational_norm_limbs as *mut u64 as *mut c_void,
                    &mut relational_pair_relation as *mut u64 as *mut c_void,
                    &mut square as *mut u64 as *mut c_void,
                    &mut left_cross as *mut u64 as *mut c_void,
                    &mut right_cross as *mut u64 as *mut c_void,
                    &mut pair_offset_wire as *mut u64 as *mut c_void,
                    &mut pair_count_wire as *mut u32 as *mut c_void,
                    &mut face_count_wire as *mut u32 as *mut c_void,
                    &mut relational_compatibility_limb_count_wire as *mut u32 as *mut c_void,
                    &mut relational_norm_limb_count_wire as *mut u32 as *mut c_void,
                    &mut square_limb_count_wire as *mut u32 as *mut c_void,
                    &mut cross_limb_count_wire as *mut u32 as *mut c_void,
                ];
                driver(
                    unsafe {
                        cuLaunchKernel(
                            compare_window,
                            self.card.grid_for(pair_count as u64)?,
                            1,
                            1,
                            self.card.block_x,
                            1,
                            1,
                            0,
                            ptr::null_mut(),
                            relational_compare_arguments.as_mut_ptr(),
                            ptr::null_mut(),
                        )
                    },
                    "cuLaunchKernel(compare sparse relational projective pair window)",
                )?;
                launches = launches.saturating_add(1);
                relational_present_wire = 1;
            }

            let mut quadratic_relation = quadratic_pair_relation_pointer;
            let mut relational_relation = relational_pair_relation_pointer;
            let mut dominated = challenged_dominated.pointer;
            let mut accumulate_arguments: [*mut c_void; 8] = [
                &mut native_front as *mut u64 as *mut c_void,
                &mut quadratic_relation as *mut u64 as *mut c_void,
                &mut relational_relation as *mut u64 as *mut c_void,
                &mut dominated as *mut u64 as *mut c_void,
                &mut pair_offset_wire as *mut u64 as *mut c_void,
                &mut pair_count_wire as *mut u32 as *mut c_void,
                &mut face_count_wire as *mut u32 as *mut c_void,
                &mut relational_present_wire as *mut u32 as *mut c_void,
            ];
            driver(
                unsafe {
                    cuLaunchKernel(
                        accumulate_window,
                        self.card.grid_for(pair_count as u64)?,
                        1,
                        1,
                        self.card.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        accumulate_arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(accumulate sparse projective pair window)",
            )?;
            launches = launches.saturating_add(1);
            pair_offset = pair_offset.saturating_add(pair_count);
        }

        let mut native_front = native_phase_front_pointer;
        let mut dominated = challenged_dominated.pointer;
        let mut selected_front = selected_front_pointer;
        let mut face_count_wire = face_population as u32;
        let mut select_arguments: [*mut c_void; 4] = [
            &mut native_front as *mut u64 as *mut c_void,
            &mut dominated as *mut u64 as *mut c_void,
            &mut selected_front as *mut u64 as *mut c_void,
            &mut face_count_wire as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    select_front,
                    self.card.grid_for(face_population as u64)?,
                    1,
                    1,
                    self.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    select_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(select sparse projective streamed front)",
        )?;
        launches = launches.saturating_add(1);
        let resident_octets = u64::try_from(arena_octets)
            .ok()
            .and_then(|octets| {
                octets.checked_add(u64::try_from(face_population.checked_mul(4)?).ok()?)
            })
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        Ok((
            vec![challenged_dominated, arena],
            launches,
            resident_octets,
            window_population,
        ))
    }
}
