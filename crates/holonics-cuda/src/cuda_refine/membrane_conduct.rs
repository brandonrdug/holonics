use super::*;

impl ResidentMembraneInteriorWord {
    pub fn conduct_observable_integral_form_frame(
        &mut self,
        contexts: &[AddressedCurrentSection],
        generator: u32,
    ) -> Result<ResidentObservableIntegralFormReturn, CudaRefineError> {
        let mounted = self
            .observable_integral_form_frame
            .as_ref()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        if contexts.is_empty() || generator >= mounted.generator_count {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let valid_current = |current: &[(u32, BigUint)]| {
            !current.is_empty()
                && !current.windows(2).any(|pair| pair[0].0 >= pair[1].0)
                && !current
                    .iter()
                    .any(|(factor, coefficient)| *factor >= self.factors || coefficient.is_zero())
        };
        if contexts.iter().any(|context| {
            context.quadratic_weight.is_zero() || !valid_current(&context.factor_current)
        }) {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let maximal_current = contexts
            .iter()
            .flat_map(|context| &context.factor_current)
            .map(|(_, coefficient)| coefficient)
            .max()
            .cloned()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let maximal_weight = contexts
            .iter()
            .map(|context| &context.quadratic_weight)
            .max()
            .cloned()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let context_limb_count = maximal_current.to_u32_digits().len().max(1);
        let weight_limb_count = maximal_weight.to_u32_digits().len().max(1);
        let quadratic_limb_count = context_limb_count
            .checked_mul(2)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let coefficient_product_limb_count = quadratic_limb_count
            .checked_add(mounted.coefficient_limb_count as usize)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let coordinate_bound = maximal_current.pow(2)
            * &maximal_weight
            * &mounted.maximal_coefficient
            * BigUint::from(mounted.maximal_form_entry_population)
            * BigUint::from(contexts.len());
        let coordinate_limb_count = coordinate_bound.to_u32_digits().len().max(1) + 1;
        let factored_bound = &coordinate_bound * &mounted.maximal_scale;
        let factored_limb_count = factored_bound.to_u32_digits().len().max(1) + 1;
        if [
            context_limb_count,
            weight_limb_count,
            quadratic_limb_count,
            coefficient_product_limb_count,
            coordinate_limb_count,
            factored_limb_count,
        ]
        .into_iter()
        .any(|extent| extent > u32::MAX as usize)
        {
            return Err(CudaRefineError::MembraneInteriorCurrentOutsideApparatus);
        }

        let factors = self.factors as usize;
        let mut context_current_limbs = vec![0_u32; contexts.len() * factors * context_limb_count];
        let mut context_weight_limbs = Vec::with_capacity(contexts.len() * weight_limb_count);
        for (context_at, context) in contexts.iter().enumerate() {
            for (factor, coefficient) in &context.factor_current {
                let limbs = coefficient.to_u32_digits();
                let begin = (context_at * factors + *factor as usize) * context_limb_count;
                context_current_limbs[begin..begin + limbs.len()].copy_from_slice(&limbs);
            }
            let mut limbs = context.quadratic_weight.to_u32_digits();
            limbs.resize(weight_limb_count, 0);
            context_weight_limbs.extend(limbs);
        }
        driver(
            unsafe { cuCtxSetCurrent(self.card.context) },
            "cuCtxSetCurrent",
        )?;
        let context_current = Buffer::of(&context_current_limbs)?;
        let context_weight = Buffer::of(&context_weight_limbs)?;
        let coordinate_signs = Buffer::alloc(mounted.form_count as usize)?;
        let coordinates = Buffer::alloc(
            mounted.form_count as usize * coordinate_limb_count * std::mem::size_of::<u32>(),
        )?;
        let quadratic_scratch = Buffer::alloc(
            mounted.form_count as usize * quadratic_limb_count * std::mem::size_of::<u32>(),
        )?;
        let coefficient_scratch = Buffer::alloc(
            mounted.form_count as usize
                * coefficient_product_limb_count
                * std::mem::size_of::<u32>(),
        )?;
        let term_scratch = Buffer::alloc(
            mounted.form_count as usize * coordinate_limb_count * std::mem::size_of::<u32>(),
        )?;
        let transported_signs = Buffer::alloc(mounted.form_count as usize)?;
        let transported = Buffer::alloc(
            mounted.form_count as usize * factored_limb_count * std::mem::size_of::<u32>(),
        )?;
        let present_signs = Buffer::alloc(mounted.present_receiver_count as usize)?;
        let present = Buffer::alloc(
            mounted.present_receiver_count as usize
                * factored_limb_count
                * std::mem::size_of::<u32>(),
        )?;

        let mut context_current_pointer = context_current.pointer;
        let mut context_weight_pointer = context_weight.pointer;
        let mut form_entry_offset_pointer = mounted.form_entry_offsets.pointer;
        let mut form_entry_row_pointer = mounted.form_entry_rows.pointer;
        let mut form_entry_column_pointer = mounted.form_entry_columns.pointer;
        let mut form_entry_sign_pointer = mounted.form_entry_signs.pointer;
        let mut form_entry_limb_pointer = mounted.form_entry_limbs.pointer;
        let mut coordinate_sign_pointer = coordinate_signs.pointer;
        let mut coordinate_pointer = coordinates.pointer;
        let mut quadratic_scratch_pointer = quadratic_scratch.pointer;
        let mut coefficient_scratch_pointer = coefficient_scratch.pointer;
        let mut term_scratch_pointer = term_scratch.pointer;
        let mut context_count_wire = contexts.len() as u32;
        let mut factor_count_wire = self.factors;
        let mut form_count_wire = mounted.form_count;
        let mut context_limb_count_wire = context_limb_count as u32;
        let mut weight_limb_count_wire = weight_limb_count as u32;
        let mut coefficient_limb_count_wire = mounted.coefficient_limb_count;
        let mut quadratic_limb_count_wire = quadratic_limb_count as u32;
        let mut coefficient_product_limb_count_wire = coefficient_product_limb_count as u32;
        let mut coordinate_limb_count_wire = coordinate_limb_count as u32;
        let mut contract_arguments: [*mut c_void; 21] = [
            &mut context_current_pointer as *mut u64 as *mut c_void,
            &mut context_weight_pointer as *mut u64 as *mut c_void,
            &mut form_entry_offset_pointer as *mut u64 as *mut c_void,
            &mut form_entry_row_pointer as *mut u64 as *mut c_void,
            &mut form_entry_column_pointer as *mut u64 as *mut c_void,
            &mut form_entry_sign_pointer as *mut u64 as *mut c_void,
            &mut form_entry_limb_pointer as *mut u64 as *mut c_void,
            &mut coordinate_sign_pointer as *mut u64 as *mut c_void,
            &mut coordinate_pointer as *mut u64 as *mut c_void,
            &mut quadratic_scratch_pointer as *mut u64 as *mut c_void,
            &mut coefficient_scratch_pointer as *mut u64 as *mut c_void,
            &mut term_scratch_pointer as *mut u64 as *mut c_void,
            &mut context_count_wire as *mut u32 as *mut c_void,
            &mut factor_count_wire as *mut u32 as *mut c_void,
            &mut form_count_wire as *mut u32 as *mut c_void,
            &mut context_limb_count_wire as *mut u32 as *mut c_void,
            &mut weight_limb_count_wire as *mut u32 as *mut c_void,
            &mut coefficient_limb_count_wire as *mut u32 as *mut c_void,
            &mut quadratic_limb_count_wire as *mut u32 as *mut c_void,
            &mut coefficient_product_limb_count_wire as *mut u32 as *mut c_void,
            &mut coordinate_limb_count_wire as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card.membrane_observable_form_contract,
                    self.card.grid_for(u64::from(mounted.form_count))?,
                    1,
                    1,
                    self.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    contract_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(contract_membrane_observable_integral_forms)",
        )?;

        let generator_offset = generator as u64 * u64::from(mounted.form_count);
        let mut generator_source_pointer = mounted.generator_factor_sources.pointer
            + generator_offset * std::mem::size_of::<u32>() as u64;
        let mut generator_scale_sign_pointer = mounted.generator_factor_scale_signs.pointer
            + generator_offset * std::mem::size_of::<u8>() as u64;
        let mut generator_scale_limb_pointer = mounted.generator_factor_scale_limbs.pointer
            + generator_offset
                * u64::from(mounted.scale_limb_count)
                * std::mem::size_of::<u32>() as u64;
        let mut transported_sign_pointer = transported_signs.pointer;
        let mut transported_pointer = transported.pointer;
        let mut source_count_wire = mounted.form_count;
        let mut target_count_wire = mounted.form_count;
        let mut scale_limb_count_wire = mounted.scale_limb_count;
        let mut factored_limb_count_wire = factored_limb_count as u32;
        let transport_arguments: [*mut c_void; 11] = [
            &mut coordinate_sign_pointer as *mut u64 as *mut c_void,
            &mut coordinate_pointer as *mut u64 as *mut c_void,
            &mut generator_source_pointer as *mut u64 as *mut c_void,
            &mut generator_scale_sign_pointer as *mut u64 as *mut c_void,
            &mut generator_scale_limb_pointer as *mut u64 as *mut c_void,
            &mut transported_sign_pointer as *mut u64 as *mut c_void,
            &mut transported_pointer as *mut u64 as *mut c_void,
            &mut source_count_wire as *mut u32 as *mut c_void,
            &mut target_count_wire as *mut u32 as *mut c_void,
            &mut coordinate_limb_count_wire as *mut u32 as *mut c_void,
            &mut scale_limb_count_wire as *mut u32 as *mut c_void,
        ];
        // The terminal target limb count is the twelfth scalar argument.
        let mut transport_arguments_extended = transport_arguments.to_vec();
        transport_arguments_extended.push(&mut factored_limb_count_wire as *mut u32 as *mut c_void);
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card.membrane_observable_form_transport,
                    self.card.grid_for(u64::from(mounted.form_count))?,
                    1,
                    1,
                    self.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    transport_arguments_extended.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(transport_membrane_observable_integral_form_factors)",
        )?;

        let mut present_source_pointer = mounted.present_factor_sources.pointer;
        let mut present_scale_sign_pointer = mounted.present_factor_scale_signs.pointer;
        let mut present_scale_limb_pointer = mounted.present_factor_scale_limbs.pointer;
        let mut present_sign_pointer = present_signs.pointer;
        let mut present_pointer = present.pointer;
        target_count_wire = mounted.present_receiver_count;
        let mut present_arguments: [*mut c_void; 12] = [
            &mut coordinate_sign_pointer as *mut u64 as *mut c_void,
            &mut coordinate_pointer as *mut u64 as *mut c_void,
            &mut present_source_pointer as *mut u64 as *mut c_void,
            &mut present_scale_sign_pointer as *mut u64 as *mut c_void,
            &mut present_scale_limb_pointer as *mut u64 as *mut c_void,
            &mut present_sign_pointer as *mut u64 as *mut c_void,
            &mut present_pointer as *mut u64 as *mut c_void,
            &mut source_count_wire as *mut u32 as *mut c_void,
            &mut target_count_wire as *mut u32 as *mut c_void,
            &mut coordinate_limb_count_wire as *mut u32 as *mut c_void,
            &mut scale_limb_count_wire as *mut u32 as *mut c_void,
            &mut factored_limb_count_wire as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card.membrane_observable_form_transport,
                    self.card
                        .grid_for(u64::from(mounted.present_receiver_count))?,
                    1,
                    1,
                    self.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    present_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(project_membrane_observable_integral_form_factors)",
        )?;
        driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
        self.card.launches += 3;

        let decode = |signs: &Buffer,
                      values: &Buffer,
                      population: usize,
                      limbs: usize|
         -> Result<Vec<BigInt>, CudaRefineError> {
            let mut sign_host = vec![0_u8; population];
            let mut limb_host = vec![0_u32; population * limbs];
            signs.read(&mut sign_host)?;
            values.read(&mut limb_host)?;
            sign_host
                .into_iter()
                .zip(limb_host.chunks_exact(limbs))
                .map(|(sign, limbs)| {
                    decode_component(sign, limbs, &BigInt::one()).map(|value| value.numer().clone())
                })
                .collect()
        };
        let coordinates_host = decode(
            &coordinate_signs,
            &coordinates,
            mounted.form_count as usize,
            coordinate_limb_count,
        )?;
        let transported_host = decode(
            &transported_signs,
            &transported,
            mounted.form_count as usize,
            factored_limb_count,
        )?;
        let present_host = decode(
            &present_signs,
            &present,
            mounted.present_receiver_count as usize,
            factored_limb_count,
        )?;
        Ok(ResidentObservableIntegralFormReturn {
            coordinates: coordinates_host,
            present_receivers: present_host,
            transported_coordinates: transported_host,
            generator,
            device: self.card.device_name.clone(),
            context_identity: self.card.context as usize,
            launches: 3,
            synchronizations: 1,
            successor_host_ingress_octets: u64::try_from(
                std::mem::size_of_val(&context_current_limbs[..])
                    .saturating_add(std::mem::size_of_val(&context_weight_limbs[..])),
            )
            .unwrap_or(u64::MAX),
            successor_host_egress_octets: u64::try_from(
                mounted.form_count as usize
                    * (std::mem::size_of::<u8>()
                        + (coordinate_limb_count + factored_limb_count)
                            * std::mem::size_of::<u32>())
                    + mounted.present_receiver_count as usize
                        * (std::mem::size_of::<u8>()
                            + factored_limb_count * std::mem::size_of::<u32>()),
            )
            .unwrap_or(u64::MAX),
            invariant_transport_reuploaded: false,
            cpu_semantic_replay_after_device: false,
        })
    }

    pub fn conduct(
        &mut self,
        left_cell: u32,
        right_cell: u32,
        injected_boundary_current: &ExactComplexWaveCurrent,
    ) -> Result<ResidentMembraneInteriorReturn, CudaRefineError> {
        if left_cell >= self.cells
            || right_cell >= self.cells
            || injected_boundary_current.is_zero()
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let injection_denominator = lcm_positive(
            injected_boundary_current.real.denom().clone(),
            injected_boundary_current.imaginary.denom(),
        );
        let injection_coordinate = |value: &Rat| -> Result<(u8, u64), CudaRefineError> {
            let numerator = value.numer() * (&injection_denominator / value.denom());
            let sign = if numerator.is_zero() {
                0
            } else if numerator.is_negative() {
                2
            } else {
                1
            };
            let magnitude = numerator
                .abs()
                .to_u64()
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            Ok((sign, magnitude))
        };
        let (injection_real_sign, injection_real_magnitude) =
            injection_coordinate(&injected_boundary_current.real)?;
        let (injection_imaginary_sign, injection_imaginary_magnitude) =
            injection_coordinate(&injected_boundary_current.imaginary)?;
        let contact_limb_count = self
            .family_limb_count
            .checked_add(3)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let returned_limb_count = contact_limb_count
            .checked_add(3)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let family_limb_population = (self.families as usize)
            .checked_mul(contact_limb_count as usize)
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let overlap_numerator = Buffer::alloc(self.families as usize * std::mem::size_of::<i64>())?;
        let overlap_denominator =
            Buffer::alloc(self.families as usize * std::mem::size_of::<u64>())?;
        let contact_real_sign = Buffer::alloc(self.families as usize)?;
        let contact_real_limbs =
            Buffer::alloc(family_limb_population * std::mem::size_of::<u32>())?;
        let contact_imaginary_sign = Buffer::alloc(self.families as usize)?;
        let contact_imaginary_limbs =
            Buffer::alloc(family_limb_population * std::mem::size_of::<u32>())?;
        let radiation_real_sign = Buffer::alloc(1)?;
        let radiation_real_limbs =
            Buffer::alloc(contact_limb_count as usize * std::mem::size_of::<u32>())?;
        let radiation_imaginary_sign = Buffer::alloc(1)?;
        let radiation_imaginary_limbs =
            Buffer::alloc(contact_limb_count as usize * std::mem::size_of::<u32>())?;
        let returned_real_sign = Buffer::alloc(1)?;
        let returned_real_limbs =
            Buffer::alloc(returned_limb_count as usize * std::mem::size_of::<u32>())?;
        let returned_imaginary_sign = Buffer::alloc(1)?;
        let returned_imaginary_limbs =
            Buffer::alloc(returned_limb_count as usize * std::mem::size_of::<u32>())?;
        let scratch = Buffer::alloc(returned_limb_count as usize * std::mem::size_of::<u32>())?;

        driver(
            unsafe { cuCtxSetCurrent(self.card.context) },
            "cuCtxSetCurrent",
        )?;
        let grid = self.card.grid_for(u64::from(self.families))?;
        let mut cell_offsets_pointer = self.cell_offsets.pointer;
        let mut cell_factors_pointer = self.cell_factors.pointer;
        let mut cell_multiplicities_pointer = self.cell_multiplicities.pointer;
        let mut cell_total_mass_pointer = self.cell_total_mass.pointer;
        let mut factor_capacity_pointer = self.factor_capacity.pointer;
        let mut family_orientation_pointer = self.family_orientation.pointer;
        let mut family_real_sign_pointer = self.family_real_sign.pointer;
        let mut family_real_limbs_pointer = self.family_real_limbs.pointer;
        let mut family_imaginary_sign_pointer = self.family_imaginary_sign.pointer;
        let mut family_imaginary_limbs_pointer = self.family_imaginary_limbs.pointer;
        let mut overlap_numerator_pointer = overlap_numerator.pointer;
        let mut overlap_denominator_pointer = overlap_denominator.pointer;
        let mut contact_real_sign_pointer = contact_real_sign.pointer;
        let mut contact_real_limbs_pointer = contact_real_limbs.pointer;
        let mut contact_imaginary_sign_pointer = contact_imaginary_sign.pointer;
        let mut contact_imaginary_limbs_pointer = contact_imaginary_limbs.pointer;
        let mut cells = self.cells;
        let mut factors = self.factors;
        let mut families = self.families;
        let mut family_limb_count = self.family_limb_count;
        let mut contact_limb_count_mut = contact_limb_count;
        let mut left_cell_mut = left_cell;
        let mut right_cell_mut = right_cell;
        let mut contact_arguments: [*mut c_void; 23] = [
            &mut cell_offsets_pointer as *mut u64 as *mut c_void,
            &mut cell_factors_pointer as *mut u64 as *mut c_void,
            &mut cell_multiplicities_pointer as *mut u64 as *mut c_void,
            &mut cell_total_mass_pointer as *mut u64 as *mut c_void,
            &mut factor_capacity_pointer as *mut u64 as *mut c_void,
            &mut family_orientation_pointer as *mut u64 as *mut c_void,
            &mut family_real_sign_pointer as *mut u64 as *mut c_void,
            &mut family_real_limbs_pointer as *mut u64 as *mut c_void,
            &mut family_imaginary_sign_pointer as *mut u64 as *mut c_void,
            &mut family_imaginary_limbs_pointer as *mut u64 as *mut c_void,
            &mut overlap_numerator_pointer as *mut u64 as *mut c_void,
            &mut overlap_denominator_pointer as *mut u64 as *mut c_void,
            &mut contact_real_sign_pointer as *mut u64 as *mut c_void,
            &mut contact_real_limbs_pointer as *mut u64 as *mut c_void,
            &mut contact_imaginary_sign_pointer as *mut u64 as *mut c_void,
            &mut contact_imaginary_limbs_pointer as *mut u64 as *mut c_void,
            &mut left_cell_mut as *mut u32 as *mut c_void,
            &mut right_cell_mut as *mut u32 as *mut c_void,
            &mut cells as *mut u32 as *mut c_void,
            &mut factors as *mut u32 as *mut c_void,
            &mut families as *mut u32 as *mut c_void,
            &mut family_limb_count as *mut u32 as *mut c_void,
            &mut contact_limb_count_mut as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card.membrane_local_contacts,
                    grid,
                    1,
                    1,
                    self.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    contact_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(conduct_membrane_local_contacts)",
        )?;

        let mut radiation_real_sign_pointer = radiation_real_sign.pointer;
        let mut radiation_real_limbs_pointer = radiation_real_limbs.pointer;
        let mut radiation_imaginary_sign_pointer = radiation_imaginary_sign.pointer;
        let mut radiation_imaginary_limbs_pointer = radiation_imaginary_limbs.pointer;
        let mut radiation_arguments: [*mut c_void; 10] = [
            &mut contact_real_sign_pointer as *mut u64 as *mut c_void,
            &mut contact_real_limbs_pointer as *mut u64 as *mut c_void,
            &mut contact_imaginary_sign_pointer as *mut u64 as *mut c_void,
            &mut contact_imaginary_limbs_pointer as *mut u64 as *mut c_void,
            &mut radiation_real_sign_pointer as *mut u64 as *mut c_void,
            &mut radiation_real_limbs_pointer as *mut u64 as *mut c_void,
            &mut radiation_imaginary_sign_pointer as *mut u64 as *mut c_void,
            &mut radiation_imaginary_limbs_pointer as *mut u64 as *mut c_void,
            &mut families as *mut u32 as *mut c_void,
            &mut contact_limb_count_mut as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card.membrane_radiation,
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
            "cuLaunchKernel(gather_membrane_radiation)",
        )?;

        let mut returned_real_sign_pointer = returned_real_sign.pointer;
        let mut returned_real_limbs_pointer = returned_real_limbs.pointer;
        let mut returned_imaginary_sign_pointer = returned_imaginary_sign.pointer;
        let mut returned_imaginary_limbs_pointer = returned_imaginary_limbs.pointer;
        let mut scratch_pointer = scratch.pointer;
        let mut injection_real_sign_mut = injection_real_sign;
        let mut injection_real_magnitude_mut = injection_real_magnitude;
        let mut injection_imaginary_sign_mut = injection_imaginary_sign;
        let mut injection_imaginary_magnitude_mut = injection_imaginary_magnitude;
        let mut returned_limb_count_mut = returned_limb_count;
        let mut injection_arguments: [*mut c_void; 15] = [
            &mut radiation_real_sign_pointer as *mut u64 as *mut c_void,
            &mut radiation_real_limbs_pointer as *mut u64 as *mut c_void,
            &mut radiation_imaginary_sign_pointer as *mut u64 as *mut c_void,
            &mut radiation_imaginary_limbs_pointer as *mut u64 as *mut c_void,
            &mut injection_real_sign_mut as *mut u8 as *mut c_void,
            &mut injection_real_magnitude_mut as *mut u64 as *mut c_void,
            &mut injection_imaginary_sign_mut as *mut u8 as *mut c_void,
            &mut injection_imaginary_magnitude_mut as *mut u64 as *mut c_void,
            &mut returned_real_sign_pointer as *mut u64 as *mut c_void,
            &mut returned_real_limbs_pointer as *mut u64 as *mut c_void,
            &mut returned_imaginary_sign_pointer as *mut u64 as *mut c_void,
            &mut returned_imaginary_limbs_pointer as *mut u64 as *mut c_void,
            &mut scratch_pointer as *mut u64 as *mut c_void,
            &mut contact_limb_count_mut as *mut u32 as *mut c_void,
            &mut returned_limb_count_mut as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card.membrane_boundary_injection,
                    1,
                    1,
                    1,
                    1,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    injection_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(inject_membrane_boundary_current)",
        )?;
        driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
        self.card.launches += 3;

        let mut overlap_numerators = vec![0_i64; self.families as usize];
        let mut overlap_denominators = vec![0_u64; self.families as usize];
        overlap_numerator.read(&mut overlap_numerators)?;
        overlap_denominator.read(&mut overlap_denominators)?;
        let overlap_denominator = overlap_denominators
            .first()
            .copied()
            .filter(|denominator| *denominator > 0)
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        if overlap_denominators
            .iter()
            .any(|denominator| *denominator != overlap_denominator)
            || overlap_numerators
                .iter()
                .any(|numerator| numerator.unsigned_abs() > self.maximal_overlap_magnitude)
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let family_overlaps = overlap_numerators
            .iter()
            .map(|numerator| Rat::new(BigInt::from(*numerator), BigInt::from(overlap_denominator)))
            .collect::<Vec<_>>();
        let mut radiation_real_sign_host = [0_u8; 1];
        let mut radiation_imaginary_sign_host = [0_u8; 1];
        let mut radiation_real_limbs_host = vec![0_u32; contact_limb_count as usize];
        let mut radiation_imaginary_limbs_host = vec![0_u32; contact_limb_count as usize];
        radiation_real_sign.read(&mut radiation_real_sign_host)?;
        radiation_imaginary_sign.read(&mut radiation_imaginary_sign_host)?;
        radiation_real_limbs.read(&mut radiation_real_limbs_host)?;
        radiation_imaginary_limbs.read(&mut radiation_imaginary_limbs_host)?;
        let native_denominator =
            &self.family_common_denominator * BigInt::from(overlap_denominator);
        let native_radiation = ExactComplexWaveCurrent::new(
            decode_component(
                radiation_real_sign_host[0],
                &radiation_real_limbs_host,
                &native_denominator,
            )?,
            decode_component(
                radiation_imaginary_sign_host[0],
                &radiation_imaginary_limbs_host,
                &native_denominator,
            )?,
        );
        let mut returned_real_sign_host = [0_u8; 1];
        let mut returned_imaginary_sign_host = [0_u8; 1];
        let mut returned_real_limbs_host = vec![0_u32; returned_limb_count as usize];
        let mut returned_imaginary_limbs_host = vec![0_u32; returned_limb_count as usize];
        returned_real_sign.read(&mut returned_real_sign_host)?;
        returned_imaginary_sign.read(&mut returned_imaginary_sign_host)?;
        returned_real_limbs.read(&mut returned_real_limbs_host)?;
        returned_imaginary_limbs.read(&mut returned_imaginary_limbs_host)?;
        let returned_denominator = &native_denominator * &injection_denominator;
        let returned_radiation = ExactComplexWaveCurrent::new(
            decode_component(
                returned_real_sign_host[0],
                &returned_real_limbs_host,
                &returned_denominator,
            )?,
            decode_component(
                returned_imaginary_sign_host[0],
                &returned_imaginary_limbs_host,
                &returned_denominator,
            )?,
        );
        let successor_host_ingress_octets = 2_u64
            .checked_mul(std::mem::size_of::<u32>() as u64)
            .and_then(|total| total.checked_add(2 * std::mem::size_of::<u8>() as u64))
            .and_then(|total| total.checked_add(2 * std::mem::size_of::<u64>() as u64))
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let successor_host_egress_octets = (self.families as usize)
            .checked_mul(std::mem::size_of::<i64>() + std::mem::size_of::<u64>())
            .and_then(|total| {
                total.checked_add(
                    4 * std::mem::size_of::<u8>()
                        + 2 * contact_limb_count as usize * std::mem::size_of::<u32>()
                        + 2 * returned_limb_count as usize * std::mem::size_of::<u32>(),
                )
            })
            .and_then(|total| u64::try_from(total).ok())
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let resident_working_octets = (self.families as usize)
            .checked_mul(
                2 * std::mem::size_of::<u8>()
                    + 2 * contact_limb_count as usize * std::mem::size_of::<u32>()
                    + std::mem::size_of::<i64>()
                    + std::mem::size_of::<u64>(),
            )
            .and_then(|total| {
                total.checked_add(
                    2 * std::mem::size_of::<u8>()
                        + 2 * contact_limb_count as usize * std::mem::size_of::<u32>()
                        + 2 * std::mem::size_of::<u8>()
                        + 3 * returned_limb_count as usize * std::mem::size_of::<u32>(),
                )
            })
            .and_then(|total| u64::try_from(total).ok())
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        Ok(ResidentMembraneInteriorReturn {
            left_cell,
            right_cell,
            family_overlaps,
            native_radiation,
            injected_boundary_current: injected_boundary_current.clone(),
            returned_radiation,
            device: self.card.device_name.clone(),
            context_identity: self.card.context as usize,
            launches: 3,
            device_dependency_edges: 2,
            synchronizations: 1,
            block_threads: self.card.block_x,
            mount_host_ingress_octets: self.mount_host_ingress_octets,
            successor_host_ingress_octets,
            successor_host_egress_octets,
            intermediate_host_egress_octets: 0,
            resident_invariant_octets: self.mount_host_ingress_octets,
            resident_working_octets,
            invariant_transport_reuploaded: false,
            cpu_semantic_replay_after_device: false,
            cell_selected_or_ranked: false,
            boundary_injection_depended_on_native_radiation: true,
        })
    }

    /// Conduct two exact recurrent factor supports through the resident Complex-Parametron word.
    ///
    /// The temporary two-cell chart has receiver mass one. Context multiplicity is one and target
    /// multiplicity is the caused recurrence population, so the existing contact kernel
    /// returns `recurrence * orientation * capacity` on every shared factor without an affine
    /// normalization quotient.  No constitutive family or current returns to the host between the
    /// contact, radiation, and identity-boundary launches.
    pub fn conduct_factor_support(
        &mut self,
        context_factors: &[u32],
        target_factors: &[u32],
        recurrence_multiplicity: u64,
    ) -> Result<ResidentFactorSupportBoundaryReturn, CudaRefineError> {
        let context_factor_currents = context_factors
            .iter()
            .map(|factor| (*factor, 1_u64))
            .collect::<Vec<_>>();
        self.conduct_factor_current(
            &context_factor_currents,
            target_factors,
            recurrence_multiplicity,
        )
    }

    /// Conduct the complete reflected exterior-path current against one outgoing boundary port.
    /// Each context coordinate is an exact incidence population accumulated by `B^T`; the target
    /// recurrence is the outgoing port capacitance. Their product is formed only in the resident
    /// contact law, not by a host score or token selector.
    pub fn conduct_factor_current(
        &mut self,
        context_factor_currents: &[(u32, u64)],
        target_factors: &[u32],
        recurrence_multiplicity: u64,
    ) -> Result<ResidentFactorSupportBoundaryReturn, CudaRefineError> {
        if recurrence_multiplicity == 0
            || context_factor_currents.is_empty()
            || target_factors.is_empty()
            || context_factor_currents
                .windows(2)
                .any(|pair| pair[0].0 >= pair[1].0)
            || target_factors.windows(2).any(|pair| pair[0] >= pair[1])
            || context_factor_currents
                .iter()
                .any(|(factor, current)| *factor >= self.factors || *current == 0)
            || target_factors.iter().any(|factor| *factor >= self.factors)
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let context_extent = u64::try_from(context_factor_currents.len())
            .map_err(|_| CudaRefineError::MembraneInteriorWordShape)?;
        let total_extent = context_factor_currents
            .len()
            .checked_add(target_factors.len())
            .and_then(|extent| u64::try_from(extent).ok())
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let offsets = [0_u64, context_extent, total_extent];
        let mut factors = Vec::with_capacity(total_extent as usize);
        factors.extend(context_factor_currents.iter().map(|(factor, _)| *factor));
        factors.extend_from_slice(target_factors);
        let mut multiplicities = Vec::with_capacity(total_extent as usize);
        multiplicities.extend(context_factor_currents.iter().map(|(_, current)| *current));
        multiplicities.extend(std::iter::repeat_n(
            recurrence_multiplicity,
            target_factors.len(),
        ));
        let unit_mass = [1_u64, 1_u64];
        let replacement_offsets = Buffer::of(&offsets)?;
        let replacement_factors = Buffer::of(&factors)?;
        let replacement_multiplicities = Buffer::of(&multiplicities)?;
        let replacement_total_mass = Buffer::of(&unit_mass)?;
        let original_offsets = std::mem::replace(&mut self.cell_offsets, replacement_offsets);
        let original_factors = std::mem::replace(&mut self.cell_factors, replacement_factors);
        let original_multiplicities =
            std::mem::replace(&mut self.cell_multiplicities, replacement_multiplicities);
        let original_total_mass =
            std::mem::replace(&mut self.cell_total_mass, replacement_total_mass);
        let original_cells = std::mem::replace(&mut self.cells, 2);
        let maximal_context_current = context_factor_currents
            .iter()
            .map(|(_, current)| *current)
            .max()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let support_overlap_bound = u128::from(self.total_factor_capacity)
            .checked_mul(u128::from(maximal_context_current))
            .and_then(|bound| bound.checked_mul(u128::from(recurrence_multiplicity)))
            .filter(|bound| *bound <= i64::MAX as u128)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?
            as u64;
        let original_overlap_bound =
            std::mem::replace(&mut self.maximal_overlap_magnitude, support_overlap_bound);
        let identity_boundary = ExactComplexWaveCurrent::new(Rat::one(), Rat::zero());
        let conducted = self.conduct(0, 1, &identity_boundary);
        self.cell_offsets = original_offsets;
        self.cell_factors = original_factors;
        self.cell_multiplicities = original_multiplicities;
        self.cell_total_mass = original_total_mass;
        self.cells = original_cells;
        self.maximal_overlap_magnitude = original_overlap_bound;
        let conducted = conducted?;
        if conducted.native_radiation != conducted.returned_radiation {
            return Err(CudaRefineError::MembraneInteriorCurrentOutsideApparatus);
        }
        let support_ingress = context_factor_currents
            .len()
            .checked_mul(std::mem::size_of::<(u32, u64)>())
            .and_then(|octets| {
                target_factors
                    .len()
                    .checked_mul(std::mem::size_of::<u32>())
                    .and_then(|target_octets| octets.checked_add(target_octets))
            })
            .and_then(|octets| octets.checked_add(std::mem::size_of::<u64>()))
            .and_then(|octets| u64::try_from(octets).ok())
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        Ok(ResidentFactorSupportBoundaryReturn {
            context_factors: context_factor_currents
                .iter()
                .map(|(factor, _)| *factor)
                .collect(),
            context_factor_currents: context_factor_currents.to_vec(),
            target_factors: target_factors.to_vec(),
            recurrence_multiplicity,
            family_overlaps: conducted.family_overlaps,
            returned_response: conducted.native_radiation,
            device: conducted.device,
            context_identity: conducted.context_identity,
            launches: conducted.launches,
            device_dependency_edges: conducted.device_dependency_edges,
            synchronizations: conducted.synchronizations,
            block_threads: conducted.block_threads,
            mount_host_ingress_octets: conducted.mount_host_ingress_octets,
            successor_host_ingress_octets: conducted
                .successor_host_ingress_octets
                .checked_add(support_ingress)
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?,
            successor_host_egress_octets: conducted.successor_host_egress_octets,
            intermediate_host_egress_octets: conducted.intermediate_host_egress_octets,
            resident_invariant_octets: conducted.resident_invariant_octets,
            invariant_transport_reuploaded: conducted.invariant_transport_reuploaded,
            cpu_semantic_replay_after_device: conducted.cpu_semantic_replay_after_device,
        })
    }
}
