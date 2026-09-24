use super::*;

impl CudaRefineExecutor {
    /// Transport complete homogeneous quadratic sections through their integer chart maps on the
    /// card.  The host performs only an overflow/admission audit and verifies the returned device
    /// testimony; it does not select the semantic route.  `cultivated` is one caused standing bit
    /// crossing the front.  The card returns the expanded, condensed, and obstructed alternatives
    /// together so withdrawal does not require a replay.
    pub fn conduct_quadratic_sections_on_device(
        &mut self,
        coefficients: &[i64],
        transforms: &[i64],
        cultivated: bool,
    ) -> Result<DeviceQuadraticSectionTransport, CudaRefineError> {
        let sections = coefficients.len() / 3;
        if sections == 0
            || coefficients.len() != sections * 3
            || transforms.len() != sections * 4
            || sections > u32::MAX as usize
        {
            return Err(CudaRefineError::QuadraticTransportShape);
        }

        // The device law uses signed 64-bit integer arithmetic.  Establish that every
        // intermediate of the exact declared association fits before launch; this is an apparatus
        // admission audit, not a host implementation of the route decision.
        let product = |factors: &[i64]| -> Option<i64> {
            factors
                .iter()
                .try_fold(1_i64, |value, factor| value.checked_mul(*factor))
        };
        let mut expected = Vec::with_capacity(coefficients.len());
        for at in 0..sections {
            let coefficient_at = at * 3;
            let transform_at = at * 4;
            let a = coefficients[coefficient_at];
            let b = coefficients[coefficient_at + 1];
            let c = coefficients[coefficient_at + 2];
            let p = transforms[transform_at];
            let q = transforms[transform_at + 1];
            let r = transforms[transform_at + 2];
            let s = transforms[transform_at + 3];
            let returned_a = product(&[a, p, p])
                .and_then(|value| value.checked_add(product(&[b, p, r])?))
                .and_then(|value| value.checked_add(product(&[c, r, r])?));
            let returned_b = product(&[2, a, p, q])
                .and_then(|value| {
                    let mixed = product(&[p, s])?.checked_add(product(&[q, r])?)?;
                    value.checked_add(b.checked_mul(mixed)?)
                })
                .and_then(|value| value.checked_add(product(&[2, c, r, s])?));
            let returned_c = product(&[a, q, q])
                .and_then(|value| value.checked_add(product(&[b, q, s])?))
                .and_then(|value| value.checked_add(product(&[c, s, s])?));
            expected.extend([
                returned_a.ok_or(CudaRefineError::QuadraticTransportShape)?,
                returned_b.ok_or(CudaRefineError::QuadraticTransportShape)?,
                returned_c.ok_or(CudaRefineError::QuadraticTransportShape)?,
            ]);
        }

        driver(unsafe { cuCtxSetCurrent(self.context) }, "cuCtxSetCurrent")?;
        let coefficient_device = Buffer::of(coefficients)?;
        let transform_device = Buffer::of(transforms)?;
        let coefficient_octets = std::mem::size_of_val(coefficients);
        let section_octets = sections * std::mem::size_of::<u32>();
        let transported_device = Buffer::alloc(coefficient_octets)?;
        let invariant_device = Buffer::alloc(section_octets)?;
        let selected_route_device = Buffer::alloc(section_octets)?;
        let ablated_route_device = Buffer::alloc(section_octets)?;
        let mut coefficient_pointer = coefficient_device.pointer;
        let mut transform_pointer = transform_device.pointer;
        let mut transported_pointer = transported_device.pointer;
        let mut invariant_pointer = invariant_device.pointer;
        let mut selected_route_pointer = selected_route_device.pointer;
        let mut ablated_route_pointer = ablated_route_device.pointer;
        let mut section_count = sections as u32;
        let mut cultivation = u32::from(cultivated);
        let mut arguments: [*mut c_void; 8] = [
            &mut coefficient_pointer as *mut u64 as *mut c_void,
            &mut transform_pointer as *mut u64 as *mut c_void,
            &mut transported_pointer as *mut u64 as *mut c_void,
            &mut invariant_pointer as *mut u64 as *mut c_void,
            &mut selected_route_pointer as *mut u64 as *mut c_void,
            &mut ablated_route_pointer as *mut u64 as *mut c_void,
            &mut section_count as *mut u32 as *mut c_void,
            &mut cultivation as *mut u32 as *mut c_void,
        ];
        let grid = self.grid_for(sections as u64)?;
        driver(
            unsafe {
                cuLaunchKernel(
                    self.quadratic_section_transport,
                    grid,
                    1,
                    1,
                    self.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(conduct_quadratic_section_transport)",
        )?;
        self.launches += 1;
        driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;

        let mut transported_coefficients = vec![0_i64; coefficients.len()];
        let mut invariant = vec![0_u32; sections];
        let mut selected_route = vec![0_u32; sections];
        let mut ablated_route = vec![0_u32; sections];
        transported_device.read(&mut transported_coefficients)?;
        invariant_device.read(&mut invariant)?;
        selected_route_device.read(&mut selected_route)?;
        ablated_route_device.read(&mut ablated_route)?;
        let expected_invariant = expected
            .chunks_exact(3)
            .zip(coefficients.chunks_exact(3))
            .map(|(returned, entered)| u32::from(returned == entered))
            .collect::<Vec<_>>();
        let expected_selected = expected_invariant
            .iter()
            .enumerate()
            .map(|(at, held)| {
                let chart = &transforms[at * 4..at * 4 + 4];
                if cultivated && chart == [-1, 0, 0, -1] {
                    1
                } else if *held == 0 {
                    2
                } else {
                    0
                }
            })
            .collect::<Vec<_>>();
        let expected_ablated = expected_invariant
            .iter()
            .map(|held| if *held == 0 { 2 } else { 0 })
            .collect::<Vec<_>>();
        if transported_coefficients != expected
            || invariant != expected_invariant
            || selected_route != expected_selected
            || ablated_route != expected_ablated
        {
            return Err(CudaRefineError::QuadraticTransportShape);
        }

        let transform_octets = std::mem::size_of_val(transforms);
        let ingress = coefficient_octets + transform_octets + std::mem::size_of::<u32>();
        let egress = coefficient_octets + 3 * section_octets;
        let expanded_sections = expected_selected
            .iter()
            .filter(|route| **route != 1)
            .count();
        Ok(DeviceQuadraticSectionTransport {
            transported_coefficients,
            invariant,
            selected_route,
            ablated_route,
            sections,
            launches: 1,
            synchronizations: 1,
            block_threads: self.block_x,
            active_lanes: sections as u32,
            // Per expanded section: twenty-one exact products and seven exact sums.  The rested
            // central-inversion route transports its coefficient face without arithmetic.
            semantic_work: (expanded_sections as u128) * 28,
            // The condensed fixed-locus passage is one transport front; an expanded member keeps
            // the five-front coefficient dependency chain.
            semantic_span: if expanded_sections == 0 { 1 } else { 5 },
            host_ingress_octets: ingress as u64,
            host_egress_octets: egress as u64,
            resident_octets: (ingress + egress) as u64,
        })
    }

    /// Conduct several exact fixed-section families and join their complete route returns through
    /// one resident reduction.  Family and coordinate extents are derived from the supplied
    /// sections and modulus population.  A modulus of zero declares the integer carrier; every
    /// positive modulus must be at least two.
    #[allow(clippy::too_many_arguments)]
    pub fn conduct_fixed_section_families_on_device(
        &mut self,
        sections: &[i64],
        actions: &[i64],
        constraints: &[i64],
        constraint_rows: &[u32],
        moduli: &[i64],
        cultivated: &[u32],
    ) -> Result<DeviceFixedSectionFamilies, CudaRefineError> {
        let families = moduli.len();
        let dimension = sections.len().checked_div(families.max(1)).unwrap_or(0);
        let matrix_entries = families
            .checked_mul(dimension)
            .and_then(|extent| extent.checked_mul(dimension))
            .ok_or(CudaRefineError::FixedSectionFamilyShape)?;
        if families < 2
            || dimension == 0
            || sections.len() != families * dimension
            || actions.len() != matrix_entries
            || constraints.len() != matrix_entries
            || constraint_rows.len() != families
            || cultivated.len() != families
            || families > u32::MAX as usize
            || dimension > u32::MAX as usize
            || constraint_rows
                .iter()
                .any(|rows| *rows as usize > dimension)
            || moduli.iter().any(|modulus| *modulus < 0 || *modulus == 1)
            || cultivated.iter().any(|value| *value > 1)
        {
            return Err(CudaRefineError::FixedSectionFamilyShape);
        }
        let dimension_u64 =
            u64::try_from(dimension).map_err(|_| CudaRefineError::FixedSectionFamilyShape)?;
        let dot_work = dimension_u64
            .checked_mul(2)
            .and_then(|work| work.checked_sub(1))
            .ok_or(CudaRefineError::FixedSectionFamilyShape)?;
        let mut predicted_local_semantic_work = Vec::with_capacity(families * 2);
        let mut predicted_local_semantic_span = Vec::with_capacity(families * 2);
        for rows in constraint_rows {
            let rows = u64::from(*rows);
            let constraint_work = rows
                .checked_mul(dot_work)
                .ok_or(CudaRefineError::FixedSectionFamilyShape)?;
            let constraint_span = rows
                .checked_mul(dimension_u64)
                .ok_or(CudaRefineError::FixedSectionFamilyShape)?;
            predicted_local_semantic_work.push(constraint_work);
            predicted_local_semantic_work.push(
                constraint_work
                    .checked_add(
                        dimension_u64
                            .checked_mul(dot_work)
                            .ok_or(CudaRefineError::FixedSectionFamilyShape)?,
                    )
                    .ok_or(CudaRefineError::FixedSectionFamilyShape)?,
            );
            predicted_local_semantic_span.push(constraint_span);
            predicted_local_semantic_span.push(
                constraint_span
                    .checked_add(dimension_u64)
                    .ok_or(CudaRefineError::FixedSectionFamilyShape)?,
            );
        }

        driver(unsafe { cuCtxSetCurrent(self.context) }, "cuCtxSetCurrent")?;
        let sections_device = Buffer::of(sections)?;
        let actions_device = Buffer::of(actions)?;
        let constraints_device = Buffer::of(constraints)?;
        let rows_device = Buffer::of(constraint_rows)?;
        let moduli_device = Buffer::of(moduli)?;
        let cultivated_device = Buffer::of(cultivated)?;
        let section_octets = std::mem::size_of_val(sections);
        let family_octets = families * std::mem::size_of::<u32>();
        let transported_device = Buffer::alloc(section_octets)?;
        let constraint_held_device = Buffer::alloc(family_octets)?;
        let invariant_device = Buffer::alloc(family_octets)?;
        let selected_route_device = Buffer::alloc(family_octets)?;
        let ablated_route_device = Buffer::alloc(family_octets)?;
        let local_measure_octets = families * std::mem::size_of::<u64>();
        let local_work_device = Buffer::alloc(local_measure_octets)?;
        let local_span_device = Buffer::alloc(local_measure_octets)?;
        let joint_device = Buffer::alloc(std::mem::size_of::<u32>())?;
        let local_joint_device = Buffer::alloc(family_octets)?;
        let work_device = Buffer::alloc(std::mem::size_of::<u64>())?;
        let span_device = Buffer::alloc(std::mem::size_of::<u64>())?;
        let mut sections_pointer = sections_device.pointer;
        let mut actions_pointer = actions_device.pointer;
        let mut constraints_pointer = constraints_device.pointer;
        let mut rows_pointer = rows_device.pointer;
        let mut moduli_pointer = moduli_device.pointer;
        let mut cultivated_pointer = cultivated_device.pointer;
        let mut transported_pointer = transported_device.pointer;
        let mut constraint_held_pointer = constraint_held_device.pointer;
        let mut invariant_pointer = invariant_device.pointer;
        let mut selected_route_pointer = selected_route_device.pointer;
        let mut ablated_route_pointer = ablated_route_device.pointer;
        let mut local_work_pointer = local_work_device.pointer;
        let mut local_span_pointer = local_span_device.pointer;
        let mut family_count = families as u32;
        let mut dimension_wire = dimension as u32;
        let mut arguments: [*mut c_void; 15] = [
            &mut sections_pointer as *mut u64 as *mut c_void,
            &mut actions_pointer as *mut u64 as *mut c_void,
            &mut constraints_pointer as *mut u64 as *mut c_void,
            &mut rows_pointer as *mut u64 as *mut c_void,
            &mut moduli_pointer as *mut u64 as *mut c_void,
            &mut cultivated_pointer as *mut u64 as *mut c_void,
            &mut transported_pointer as *mut u64 as *mut c_void,
            &mut constraint_held_pointer as *mut u64 as *mut c_void,
            &mut invariant_pointer as *mut u64 as *mut c_void,
            &mut selected_route_pointer as *mut u64 as *mut c_void,
            &mut ablated_route_pointer as *mut u64 as *mut c_void,
            &mut local_work_pointer as *mut u64 as *mut c_void,
            &mut local_span_pointer as *mut u64 as *mut c_void,
            &mut family_count as *mut u32 as *mut c_void,
            &mut dimension_wire as *mut u32 as *mut c_void,
        ];
        let grid = self.grid_for(families as u64)?;
        driver(
            unsafe {
                cuLaunchKernel(
                    self.fixed_section_families,
                    grid,
                    1,
                    1,
                    self.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(conduct_fixed_section_families)",
        )?;
        self.launches += 1;
        let mut joint_pointer = joint_device.pointer;
        let mut local_joint_pointer = local_joint_device.pointer;
        let mut work_pointer = work_device.pointer;
        let mut span_pointer = span_device.pointer;
        let mut reduction_arguments: [*mut c_void; 9] = [
            &mut selected_route_pointer as *mut u64 as *mut c_void,
            &mut ablated_route_pointer as *mut u64 as *mut c_void,
            &mut local_work_pointer as *mut u64 as *mut c_void,
            &mut local_span_pointer as *mut u64 as *mut c_void,
            &mut joint_pointer as *mut u64 as *mut c_void,
            &mut local_joint_pointer as *mut u64 as *mut c_void,
            &mut work_pointer as *mut u64 as *mut c_void,
            &mut span_pointer as *mut u64 as *mut c_void,
            &mut family_count as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.fixed_section_family_reduction,
                    1,
                    1,
                    1,
                    self.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    reduction_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(reduce_fixed_section_families)",
        )?;
        self.launches += 1;
        driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;

        let mut transported_sections = vec![0_i64; sections.len()];
        let mut constraint_held = vec![0_u32; families];
        let mut invariant = vec![0_u32; families];
        let mut selected_route = vec![0_u32; families];
        let mut ablated_route = vec![0_u32; families];
        let mut local_semantic_work = vec![0_u64; families];
        let mut local_semantic_span = vec![0_u64; families];
        let mut joint_cultivated = [0_u32];
        let mut local_ablated_joint = vec![0_u32; families];
        let mut semantic_work = [0_u64];
        let mut semantic_span = [0_u64];
        transported_device.read(&mut transported_sections)?;
        constraint_held_device.read(&mut constraint_held)?;
        invariant_device.read(&mut invariant)?;
        selected_route_device.read(&mut selected_route)?;
        ablated_route_device.read(&mut ablated_route)?;
        local_work_device.read(&mut local_semantic_work)?;
        local_span_device.read(&mut local_semantic_span)?;
        joint_device.read(&mut joint_cultivated)?;
        local_joint_device.read(&mut local_ablated_joint)?;
        work_device.read(&mut semantic_work)?;
        span_device.read(&mut semantic_span)?;
        let reduction_work = u64::try_from(families)
            .ok()
            .and_then(|count| count.checked_add(count.checked_mul(count)?))
            .ok_or(CudaRefineError::FixedSectionFamilyShape)?;
        let predicted_returned_work = selected_route
            .iter()
            .enumerate()
            .try_fold(reduction_work, |work, (family, route)| {
                let alternative = usize::from(*route != 1);
                work.checked_add(predicted_local_semantic_work[family * 2 + alternative])
            })
            .ok_or(CudaRefineError::FixedSectionFamilyShape)?;
        let predicted_returned_span = selected_route
            .iter()
            .enumerate()
            .map(|(family, route)| {
                predicted_local_semantic_span[family * 2 + usize::from(*route != 1)]
            })
            .max()
            .and_then(|span| span.checked_add(families as u64))
            .ok_or(CudaRefineError::FixedSectionFamilyShape)?;
        if constraint_held.iter().any(|value| *value > 1)
            || invariant.iter().any(|value| *value > 1)
            || selected_route.iter().any(|value| *value > 2)
            || ablated_route.iter().any(|value| *value != 0 && *value != 2)
            || selected_route
                .iter()
                .enumerate()
                .any(|(family, route)| match *route {
                    0 => invariant[family] != 1,
                    1 => {
                        cultivated[family] != 1
                            || constraint_held[family] != 1
                            || invariant[family] != 1
                    }
                    2 => invariant[family] != 0,
                    _ => true,
                })
            || ablated_route
                .iter()
                .enumerate()
                .any(|(family, route)| *route != if invariant[family] == 1 { 0 } else { 2 })
            || joint_cultivated[0] > 1
            || local_ablated_joint.iter().any(|value| *value > 1)
            || (joint_cultivated[0] == 1) != selected_route.iter().all(|route| *route == 1)
            || local_ablated_joint
                .iter()
                .enumerate()
                .any(|(withdrawn, joint)| {
                    (*joint == 1)
                        != selected_route.iter().enumerate().all(|(family, route)| {
                            if family == withdrawn {
                                ablated_route[family] == 1
                            } else {
                                *route == 1
                            }
                        })
                })
            || local_semantic_work
                .iter()
                .zip(selected_route.iter().enumerate())
                .any(|(actual, (family, route))| {
                    *actual != predicted_local_semantic_work[family * 2 + usize::from(*route != 1)]
                })
            || local_semantic_span
                .iter()
                .zip(selected_route.iter().enumerate())
                .any(|(actual, (family, route))| {
                    *actual != predicted_local_semantic_span[family * 2 + usize::from(*route != 1)]
                })
            || semantic_work[0] != predicted_returned_work
            || semantic_span[0] != predicted_returned_span
        {
            return Err(CudaRefineError::FixedSectionFamilyShape);
        }
        let ingress = std::mem::size_of_val(sections)
            + std::mem::size_of_val(actions)
            + std::mem::size_of_val(constraints)
            + std::mem::size_of_val(constraint_rows)
            + std::mem::size_of_val(moduli)
            + std::mem::size_of_val(cultivated);
        let egress = section_octets
            + 5 * family_octets
            + 2 * local_measure_octets
            + std::mem::size_of::<u32>()
            + 2 * std::mem::size_of::<u64>();
        Ok(DeviceFixedSectionFamilies {
            transported_sections,
            constraint_held,
            invariant,
            selected_route,
            ablated_route,
            joint_cultivated: joint_cultivated[0] == 1,
            local_ablated_joint,
            families,
            dimension,
            launches: 2,
            synchronizations: 1,
            typed_reductions: 1,
            block_threads: self.block_x,
            active_lanes: families as u32,
            predicted_local_semantic_work,
            predicted_local_semantic_span,
            semantic_work: u128::from(semantic_work[0]),
            semantic_span: semantic_span[0],
            host_ingress_octets: ingress as u64,
            host_egress_octets: egress as u64,
            resident_octets: (ingress + egress) as u64,
        })
    }

    /// Conduct fixed-section families through one shared oriented relation `T = I + L*C`.
    ///
    /// The incidence orientations are mounted once for the complete family front. The card owns
    /// residual evaluation, native transport, cultivation/obstruction selection, joint return and
    /// every local ablation; the host validates the exact receipt after one synchronization.
    pub fn conduct_native_fixed_section_families_on_device(
        &mut self,
        sections: &[i64],
        constraint_orientation: &[i8],
        factor_orientation: &[i8],
        moduli: &[i64],
        cultivated: &[u32],
    ) -> Result<DeviceNativeFixedSectionFamilies, CudaRefineError> {
        let families = moduli.len();
        let dimension = sections.len().checked_div(families.max(1)).unwrap_or(0);
        if families < 2
            || dimension == 0
            || sections.len() != families * dimension
            || constraint_orientation.len() != dimension
            || factor_orientation.len() != dimension
            || constraint_orientation
                .iter()
                .chain(factor_orientation)
                .any(|orientation| !(-1..=1).contains(orientation))
            || !constraint_orientation
                .iter()
                .any(|orientation| *orientation != 0)
            || !factor_orientation
                .iter()
                .any(|orientation| *orientation != 0)
            || families > u32::MAX as usize
            || dimension > u32::MAX as usize
            || moduli.iter().any(|modulus| *modulus < 0 || *modulus == 1)
            || cultivated.iter().any(|value| *value > 1)
            || cultivated.len() != families
        {
            return Err(CudaRefineError::NativeFixedSectionFamilyShape);
        }
        let constraint_terms = constraint_orientation
            .iter()
            .filter(|orientation| **orientation != 0)
            .count() as u64;
        let factor_terms = factor_orientation
            .iter()
            .filter(|orientation| **orientation != 0)
            .count() as u64;
        let constraint_work = constraint_terms.saturating_sub(1);
        let constraint_span = constraint_work;
        let expanded_work = constraint_work
            .checked_add(factor_terms)
            .ok_or(CudaRefineError::NativeFixedSectionFamilyShape)?;
        let expanded_span = constraint_span
            .checked_add(u64::from(factor_terms != 0))
            .ok_or(CudaRefineError::NativeFixedSectionFamilyShape)?;
        let mut predicted_local_semantic_work = Vec::with_capacity(families * 2);
        let mut predicted_local_semantic_span = Vec::with_capacity(families * 2);
        for _ in 0..families {
            predicted_local_semantic_work.extend([constraint_work, expanded_work]);
            predicted_local_semantic_span.extend([constraint_span, expanded_span]);
        }

        driver(unsafe { cuCtxSetCurrent(self.context) }, "cuCtxSetCurrent")?;
        let sections_device = Buffer::of(sections)?;
        let constraint_device = Buffer::of(constraint_orientation)?;
        let factor_device = Buffer::of(factor_orientation)?;
        let moduli_device = Buffer::of(moduli)?;
        let cultivated_device = Buffer::of(cultivated)?;
        let section_octets = std::mem::size_of_val(sections);
        let family_octets = families * std::mem::size_of::<u32>();
        let family_i64_octets = families * std::mem::size_of::<i64>();
        let local_measure_octets = families * std::mem::size_of::<u64>();
        let transported_device = Buffer::alloc(section_octets)?;
        let residual_device = Buffer::alloc(family_i64_octets)?;
        let constraint_held_device = Buffer::alloc(family_octets)?;
        let invariant_device = Buffer::alloc(family_octets)?;
        let selected_route_device = Buffer::alloc(family_octets)?;
        let ablated_route_device = Buffer::alloc(family_octets)?;
        let local_work_device = Buffer::alloc(local_measure_octets)?;
        let local_span_device = Buffer::alloc(local_measure_octets)?;
        let joint_device = Buffer::alloc(std::mem::size_of::<u32>())?;
        let local_joint_device = Buffer::alloc(family_octets)?;
        let work_device = Buffer::alloc(std::mem::size_of::<u64>())?;
        let span_device = Buffer::alloc(std::mem::size_of::<u64>())?;
        let mut sections_pointer = sections_device.pointer;
        let mut constraint_pointer = constraint_device.pointer;
        let mut factor_pointer = factor_device.pointer;
        let mut moduli_pointer = moduli_device.pointer;
        let mut cultivated_pointer = cultivated_device.pointer;
        let mut transported_pointer = transported_device.pointer;
        let mut residual_pointer = residual_device.pointer;
        let mut constraint_held_pointer = constraint_held_device.pointer;
        let mut invariant_pointer = invariant_device.pointer;
        let mut selected_route_pointer = selected_route_device.pointer;
        let mut ablated_route_pointer = ablated_route_device.pointer;
        let mut local_work_pointer = local_work_device.pointer;
        let mut local_span_pointer = local_span_device.pointer;
        let mut family_count = families as u32;
        let mut dimension_wire = dimension as u32;
        let mut arguments: [*mut c_void; 15] = [
            &mut sections_pointer as *mut u64 as *mut c_void,
            &mut constraint_pointer as *mut u64 as *mut c_void,
            &mut factor_pointer as *mut u64 as *mut c_void,
            &mut moduli_pointer as *mut u64 as *mut c_void,
            &mut cultivated_pointer as *mut u64 as *mut c_void,
            &mut transported_pointer as *mut u64 as *mut c_void,
            &mut residual_pointer as *mut u64 as *mut c_void,
            &mut constraint_held_pointer as *mut u64 as *mut c_void,
            &mut invariant_pointer as *mut u64 as *mut c_void,
            &mut selected_route_pointer as *mut u64 as *mut c_void,
            &mut ablated_route_pointer as *mut u64 as *mut c_void,
            &mut local_work_pointer as *mut u64 as *mut c_void,
            &mut local_span_pointer as *mut u64 as *mut c_void,
            &mut family_count as *mut u32 as *mut c_void,
            &mut dimension_wire as *mut u32 as *mut c_void,
        ];
        let grid = self.grid_for(families as u64)?;
        driver(
            unsafe {
                cuLaunchKernel(
                    self.native_fixed_section_families,
                    grid,
                    1,
                    1,
                    self.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(conduct_native_fixed_section_families)",
        )?;
        self.launches += 1;

        let mut joint_pointer = joint_device.pointer;
        let mut local_joint_pointer = local_joint_device.pointer;
        let mut work_pointer = work_device.pointer;
        let mut span_pointer = span_device.pointer;
        let mut reduction_arguments: [*mut c_void; 9] = [
            &mut selected_route_pointer as *mut u64 as *mut c_void,
            &mut ablated_route_pointer as *mut u64 as *mut c_void,
            &mut local_work_pointer as *mut u64 as *mut c_void,
            &mut local_span_pointer as *mut u64 as *mut c_void,
            &mut joint_pointer as *mut u64 as *mut c_void,
            &mut local_joint_pointer as *mut u64 as *mut c_void,
            &mut work_pointer as *mut u64 as *mut c_void,
            &mut span_pointer as *mut u64 as *mut c_void,
            &mut family_count as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.fixed_section_family_reduction,
                    1,
                    1,
                    1,
                    self.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    reduction_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(reduce_fixed_section_families)",
        )?;
        self.launches += 1;
        driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;

        let mut transported_sections = vec![0_i64; sections.len()];
        let mut constraint_residuals = vec![0_i64; families];
        let mut constraint_held = vec![0_u32; families];
        let mut invariant = vec![0_u32; families];
        let mut selected_route = vec![0_u32; families];
        let mut ablated_route = vec![0_u32; families];
        let mut local_semantic_work = vec![0_u64; families];
        let mut local_semantic_span = vec![0_u64; families];
        let mut joint_cultivated = [0_u32];
        let mut local_ablated_joint = vec![0_u32; families];
        let mut semantic_work = [0_u64];
        let mut semantic_span = [0_u64];
        transported_device.read(&mut transported_sections)?;
        residual_device.read(&mut constraint_residuals)?;
        constraint_held_device.read(&mut constraint_held)?;
        invariant_device.read(&mut invariant)?;
        selected_route_device.read(&mut selected_route)?;
        ablated_route_device.read(&mut ablated_route)?;
        local_work_device.read(&mut local_semantic_work)?;
        local_span_device.read(&mut local_semantic_span)?;
        joint_device.read(&mut joint_cultivated)?;
        local_joint_device.read(&mut local_ablated_joint)?;
        work_device.read(&mut semantic_work)?;
        span_device.read(&mut semantic_span)?;

        let reduction_work = u64::try_from(families)
            .ok()
            .and_then(|count| count.checked_add(count.checked_mul(count)?))
            .ok_or(CudaRefineError::NativeFixedSectionFamilyShape)?;
        let predicted_returned_work = selected_route
            .iter()
            .enumerate()
            .try_fold(reduction_work, |work, (family, route)| {
                work.checked_add(
                    predicted_local_semantic_work[family * 2 + usize::from(*route != 1)],
                )
            })
            .ok_or(CudaRefineError::NativeFixedSectionFamilyShape)?;
        let predicted_returned_span = selected_route
            .iter()
            .enumerate()
            .map(|(family, route)| {
                predicted_local_semantic_span[family * 2 + usize::from(*route != 1)]
            })
            .max()
            .and_then(|span| span.checked_add(families as u64))
            .ok_or(CudaRefineError::NativeFixedSectionFamilyShape)?;
        if constraint_held.iter().any(|value| *value > 1)
            || invariant != constraint_held
            || selected_route.iter().any(|value| *value > 2)
            || ablated_route.iter().any(|value| *value != 0 && *value != 2)
            || selected_route
                .iter()
                .enumerate()
                .any(|(family, route)| match *route {
                    0 => invariant[family] != 1,
                    1 => cultivated[family] != 1 || invariant[family] != 1,
                    2 => invariant[family] != 0,
                    _ => true,
                })
            || ablated_route
                .iter()
                .enumerate()
                .any(|(family, route)| *route != if invariant[family] == 1 { 0 } else { 2 })
            || joint_cultivated[0] > 1
            || local_ablated_joint.iter().any(|value| *value > 1)
            || (joint_cultivated[0] == 1) != selected_route.iter().all(|route| *route == 1)
            || local_ablated_joint
                .iter()
                .enumerate()
                .any(|(withdrawn, joint)| {
                    (*joint == 1)
                        != selected_route.iter().enumerate().all(|(family, route)| {
                            if family == withdrawn {
                                ablated_route[family] == 1
                            } else {
                                *route == 1
                            }
                        })
                })
            || local_semantic_work
                .iter()
                .zip(selected_route.iter().enumerate())
                .any(|(actual, (family, route))| {
                    *actual != predicted_local_semantic_work[family * 2 + usize::from(*route != 1)]
                })
            || local_semantic_span
                .iter()
                .zip(selected_route.iter().enumerate())
                .any(|(actual, (family, route))| {
                    *actual != predicted_local_semantic_span[family * 2 + usize::from(*route != 1)]
                })
            || semantic_work[0] != predicted_returned_work
            || semantic_span[0] != predicted_returned_span
        {
            return Err(CudaRefineError::NativeFixedSectionFamilyShape);
        }
        let ingress = std::mem::size_of_val(sections)
            + std::mem::size_of_val(constraint_orientation)
            + std::mem::size_of_val(factor_orientation)
            + std::mem::size_of_val(moduli)
            + std::mem::size_of_val(cultivated);
        let egress = section_octets
            + family_i64_octets
            + 5 * family_octets
            + 2 * local_measure_octets
            + std::mem::size_of::<u32>()
            + 2 * std::mem::size_of::<u64>();
        Ok(DeviceNativeFixedSectionFamilies {
            transported_sections,
            constraint_residuals,
            constraint_held,
            invariant,
            selected_route,
            ablated_route,
            joint_cultivated: joint_cultivated[0] == 1,
            local_ablated_joint,
            families,
            dimension,
            launches: 2,
            synchronizations: 1,
            typed_reductions: 1,
            block_threads: self.block_x,
            active_lanes: families as u32,
            predicted_local_semantic_work,
            predicted_local_semantic_span,
            semantic_work: u128::from(semantic_work[0]),
            semantic_span: semantic_span[0],
            host_ingress_octets: ingress as u64,
            host_egress_octets: egress as u64,
            resident_octets: (ingress + egress) as u64,
        })
    }
}
