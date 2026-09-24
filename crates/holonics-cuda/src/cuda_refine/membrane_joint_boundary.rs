use super::*;

impl ResidentMembraneInteriorWord {
    /// Conduct one complete port-resolved causal boundary section on the resident card.
    ///
    /// Every support crosses together. The resident word forms exact Complex-Parametron contact
    /// current, radiates the addressed-port section, resolves its phase components and ordered
    /// Pareto comparisons in independent device fronts, and finally closes
    /// `stored difference + returned = incoming` in one common quantity chart. Only the resulting
    /// boundary testimony crosses back after the one terminal synchronization; no host loop enacts
    /// or replays a constitutive branch.
    pub fn conduct_joint_boundary_chain(
        &mut self,
        supports: &[ResidentBoundaryChainSupport],
        port_population: usize,
        entering_current: &ExactComplexWaveCurrent,
    ) -> Result<ResidentJointBoundaryChainReturn, CudaRefineError> {
        if supports.is_empty()
            || port_population == 0
            || supports.len() > u32::MAX as usize
            || port_population > u32::MAX as usize
            || entering_current.is_zero()
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let factor_receiver_observations = self
            .factor_receiver_observations
            .as_ref()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        if self.receiver_count == 0 {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }

        let mut represented_ports = BTreeSet::new();
        let mut offsets = Vec::with_capacity(supports.len().saturating_mul(2).saturating_add(1));
        let mut factors = Vec::new();
        let mut multiplicity_signs = Vec::<u8>::new();
        let mut multiplicities = Vec::<BigUint>::new();
        let mut support_reflected_scales = Vec::<BigUint>::with_capacity(supports.len());
        let mut support_pair_scales = Vec::<BigUint>::with_capacity(supports.len());
        let mut support_action_scales = Vec::<BigUint>::with_capacity(supports.len());
        let mut support_ports = Vec::with_capacity(supports.len());
        let mut greatest_action_overlap = BigUint::zero();
        let mut greatest_reflected_overlap = BigUint::zero();
        let mut greatest_receiver_overlap = BigUint::zero();
        let mut greatest_receiver_norm = BigUint::zero();
        offsets.push(0_u64);
        for support in supports {
            if support.port as usize >= port_population
                || support.reflected_quadratic_scale.is_zero()
                || support.action_pair_scale.is_zero()
                || support.action_quadratic_scale.is_zero()
                || support.reflected_factor_current.is_empty()
                || support
                    .reflected_factor_current
                    .windows(2)
                    .any(|pair| pair[0].0 >= pair[1].0)
                || support
                    .action_factor_current
                    .windows(2)
                    .any(|pair| pair[0].0 >= pair[1].0)
                || support
                    .reflected_factor_current
                    .iter()
                    .any(|(factor, current)| *factor >= self.factors || current.is_zero())
                || support
                    .action_factor_current
                    .iter()
                    .any(|(factor, current)| *factor >= self.factors || current.is_zero())
            {
                return Err(CudaRefineError::MembraneInteriorWordShape);
            }
            represented_ports.insert(support.port);
            support_ports.push(support.port);
            support_reflected_scales.push(support.reflected_quadratic_scale.clone());
            support_pair_scales.push(support.action_pair_scale.clone());
            support_action_scales.push(support.action_quadratic_scale.clone());
            for (factor, current) in &support.reflected_factor_current {
                factors.push(*factor);
                multiplicity_signs.push(1);
                multiplicities.push(current.clone());
            }
            offsets.push(
                u64::try_from(factors.len())
                    .map_err(|_| CudaRefineError::MembraneInteriorWordShape)?,
            );
            for (factor, current) in &support.action_factor_current {
                factors.push(*factor);
                multiplicity_signs.push(if current.is_positive() { 1 } else { 2 });
                multiplicities.push(current.magnitude().clone());
            }
            offsets.push(
                u64::try_from(factors.len())
                    .map_err(|_| CudaRefineError::MembraneInteriorWordShape)?,
            );

            let maximal_reflected_current = support
                .reflected_factor_current
                .iter()
                .map(|(_, current)| current)
                .max()
                .cloned()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let maximal_action_current = support
                .action_factor_current
                .iter()
                .map(|(_, current)| current.magnitude())
                .max()
                .cloned()
                .unwrap_or_else(BigUint::zero);
            let capacity = BigUint::from(self.total_factor_capacity);
            let action_bound = &capacity * &maximal_reflected_current * &maximal_action_current;
            let reflected_bound =
                capacity * &maximal_reflected_current * &maximal_reflected_current;
            greatest_action_overlap =
                greatest_action_overlap.max(action_bound * &support.action_pair_scale);
            greatest_reflected_overlap = greatest_reflected_overlap
                .max(reflected_bound * &support.reflected_quadratic_scale);

            greatest_receiver_overlap = greatest_receiver_overlap.max(
                &maximal_reflected_current
                    * &maximal_action_current
                    * BigUint::from(self.receiver_count)
                    * BigUint::from(support.reflected_factor_current.len())
                    * BigUint::from(support.action_factor_current.len())
                    * &support.action_pair_scale,
            );
            greatest_receiver_norm = greatest_receiver_norm.max(
                &maximal_action_current
                    * &maximal_action_current
                    * BigUint::from(self.receiver_count)
                    * BigUint::from(support.action_factor_current.len()).pow(2)
                    * &support.action_quadratic_scale,
            );
        }
        if represented_ports.len() != port_population {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }

        let support_count = supports.len() as u32;
        let port_count = port_population as u32;
        let response_population = supports
            .len()
            .checked_mul(self.families as usize)
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let receiver_response_population = supports
            .len()
            .checked_mul(self.receiver_count as usize)
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let contact_work_population = supports
            .len()
            .checked_mul(self.families.max(self.receiver_count) as usize)
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let multiplicity_limb_count = multiplicities
            .iter()
            .map(|current| current.to_u32_digits().len())
            .max()
            .unwrap_or(1)
            .max(1);
        let mut multiplicity_limbs = Vec::with_capacity(
            multiplicities
                .len()
                .checked_mul(multiplicity_limb_count)
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?,
        );
        for current in &multiplicities {
            let mut limbs = current.to_u32_digits();
            limbs.resize(multiplicity_limb_count, 0);
            multiplicity_limbs.extend(limbs);
        }
        let multiplicity_limb_count = u32::try_from(multiplicity_limb_count)
            .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let support_scale_limb_count = support_reflected_scales
            .iter()
            .chain(&support_pair_scales)
            .chain(&support_action_scales)
            .map(|multiplicity| multiplicity.to_u32_digits().len())
            .max()
            .unwrap_or(1)
            .max(1);
        let encode_support_scales = |scales: &[BigUint]| {
            let mut encoded = Vec::with_capacity(
                scales
                    .len()
                    .checked_mul(support_scale_limb_count)
                    .ok_or(CudaRefineError::MembraneInteriorWordShape)?,
            );
            for scale in scales {
                let mut limbs = scale.to_u32_digits();
                limbs.resize(support_scale_limb_count, 0);
                encoded.extend(limbs);
            }
            Ok::<_, CudaRefineError>(encoded)
        };
        let support_reflected_scale_limbs = encode_support_scales(&support_reflected_scales)?;
        let support_pair_scale_limbs = encode_support_scales(&support_pair_scales)?;
        let support_action_scale_limbs = encode_support_scales(&support_action_scales)?;
        let support_scale_limb_count = u32::try_from(support_scale_limb_count)
            .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let greatest_support_overlap = greatest_action_overlap
            .clone()
            .max(greatest_reflected_overlap)
            .max(greatest_receiver_overlap.clone())
            .max(greatest_receiver_norm.clone());
        let port_overlap_bound = &greatest_support_overlap * BigUint::from(support_count);
        let port_receiver_overlap_bound = &greatest_receiver_overlap * BigUint::from(support_count);
        let port_receiver_norm_bound = &greatest_receiver_norm * BigUint::from(support_count);
        let overlap_limb_count = u32::try_from(
            port_overlap_bound
                .to_u32_digits()
                .len()
                .max(1)
                .saturating_add(2),
        )
        .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let contact_bound =
            self.maximal_family_numerator.abs() * BigInt::from(greatest_action_overlap.clone());
        let radiation_bound =
            &contact_bound * BigInt::from(self.families) * BigInt::from(support_count);
        let (_, contact_digits) = contact_bound.to_u32_digits();
        let (_, radiation_digits) = radiation_bound.to_u32_digits();
        let contact_limb_count = u32::try_from(contact_digits.len().max(1).saturating_add(1))
            .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?
            .max(overlap_limb_count);
        let radiation_limb_count =
            u32::try_from(radiation_digits.len().max(1).saturating_add(1))
                .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;

        let incoming_denominator = lcm_positive(
            entering_current.real.denom().clone(),
            entering_current.imaginary.denom(),
        );
        let balance_denominator = lcm_positive(
            self.family_common_denominator.clone(),
            &incoming_denominator,
        );
        let joint_scale = (&balance_denominator / &self.family_common_denominator)
            .to_u64()
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let incoming_real_bound = (entering_current.real.numer()
            * (&balance_denominator / entering_current.real.denom()))
        .abs();
        let incoming_imaginary_bound = (entering_current.imaginary.numer()
            * (&balance_denominator / entering_current.imaginary.denom()))
        .abs();
        let stored_bound = incoming_real_bound.max(incoming_imaginary_bound)
            + radiation_bound * BigInt::from(joint_scale);
        let (_, stored_digits) = stored_bound.to_u32_digits();
        let stored_limb_count = u32::try_from(stored_digits.len().max(2).saturating_add(1))
            .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let phase_component_bound = (&port_overlap_bound * &port_overlap_bound)
            .max(port_receiver_overlap_bound)
            .max(port_receiver_norm_bound);
        let phase_component_limb_count = u32::try_from(
            phase_component_bound
                .to_u32_digits()
                .len()
                .max(1)
                .saturating_add(2),
        )
        .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let compatibility_limb_count = phase_component_limb_count;
        let norm_limb_count = phase_component_limb_count;
        let square_limb_count = compatibility_limb_count
            .checked_mul(2)
            .and_then(|limbs| limbs.checked_add(1))
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let cross_limb_count = square_limb_count
            .checked_add(norm_limb_count)
            .and_then(|limbs| limbs.checked_add(1))
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let component_count = self
            .families
            .checked_add(self.receiver_count)
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let component_population = port_population
            .checked_mul(component_count as usize)
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let phase_pair_population = port_population
            .checked_mul(port_population)
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let (incoming_real_sign, incoming_real_limbs) = encode_component(
            &entering_current.real,
            &balance_denominator,
            stored_limb_count as usize,
        )?;
        let (incoming_imaginary_sign, incoming_imaginary_limbs) = encode_component(
            &entering_current.imaginary,
            &balance_denominator,
            stored_limb_count as usize,
        )?;

        driver(
            unsafe { cuCtxSetCurrent(self.card.context) },
            "cuCtxSetCurrent",
        )?;
        let cell_offsets = Buffer::of(&offsets)?;
        let cell_factors = Buffer::of(&factors)?;
        let cell_multiplicity_signs = Buffer::of(&multiplicity_signs)?;
        let cell_multiplicities = Buffer::of(&multiplicity_limbs)?;
        let support_port = Buffer::of(&support_ports)?;
        let support_reflected_scale = Buffer::of(&support_reflected_scale_limbs)?;
        let support_pair_scale = Buffer::of(&support_pair_scale_limbs)?;
        let support_action_scale = Buffer::of(&support_action_scale_limbs)?;

        let overlap_sign = Buffer::alloc(response_population)?;
        let overlap_limbs = Buffer::alloc(
            response_population
                .checked_mul(overlap_limb_count as usize)
                .and_then(|length| length.checked_mul(std::mem::size_of::<u32>()))
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?,
        )?;
        let reflected_overlap_sign = Buffer::alloc(response_population)?;
        let reflected_overlap_limbs = Buffer::alloc(
            response_population
                .checked_mul(overlap_limb_count as usize)
                .and_then(|length| length.checked_mul(std::mem::size_of::<u32>()))
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?,
        )?;
        let overlap_scratch = Buffer::alloc(
            contact_work_population
                .checked_mul(overlap_limb_count as usize)
                .and_then(|length| length.checked_mul(std::mem::size_of::<u32>()))
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?,
        )?;
        let receiver_overlap_sign = Buffer::alloc(receiver_response_population)?;
        let receiver_overlap_limbs = Buffer::alloc(
            receiver_response_population
                .checked_mul(overlap_limb_count as usize)
                .and_then(|length| length.checked_mul(std::mem::size_of::<u32>()))
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?,
        )?;
        let receiver_action_norm_sign = Buffer::alloc(receiver_response_population)?;
        let receiver_action_norm_limbs = Buffer::alloc(
            receiver_response_population
                .checked_mul(overlap_limb_count as usize)
                .and_then(|length| length.checked_mul(std::mem::size_of::<u32>()))
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?,
        )?;
        let contact_real_sign = Buffer::alloc(response_population)?;
        let contact_real_limbs = Buffer::alloc(
            response_population
                .checked_mul(contact_limb_count as usize)
                .and_then(|length| length.checked_mul(std::mem::size_of::<u32>()))
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?,
        )?;
        let contact_imaginary_sign = Buffer::alloc(response_population)?;
        let contact_imaginary_limbs = Buffer::alloc(
            response_population
                .checked_mul(contact_limb_count as usize)
                .and_then(|length| length.checked_mul(std::mem::size_of::<u32>()))
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?,
        )?;
        let support_real_sign = Buffer::alloc(supports.len())?;
        let support_real_limbs = Buffer::alloc(
            supports
                .len()
                .checked_mul(radiation_limb_count as usize)
                .and_then(|length| length.checked_mul(std::mem::size_of::<u32>()))
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?,
        )?;
        let support_imaginary_sign = Buffer::alloc(supports.len())?;
        let support_imaginary_limbs = Buffer::alloc(
            supports
                .len()
                .checked_mul(radiation_limb_count as usize)
                .and_then(|length| length.checked_mul(std::mem::size_of::<u32>()))
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?,
        )?;
        let port_real_sign = Buffer::alloc(port_population)?;
        let port_real_limbs = Buffer::alloc(
            port_population
                .checked_mul(radiation_limb_count as usize)
                .and_then(|length| length.checked_mul(std::mem::size_of::<u32>()))
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?,
        )?;
        let port_imaginary_sign = Buffer::alloc(port_population)?;
        let port_imaginary_limbs = Buffer::alloc(
            port_population
                .checked_mul(radiation_limb_count as usize)
                .and_then(|length| length.checked_mul(std::mem::size_of::<u32>()))
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?,
        )?;
        let port_family_population = port_population
            .checked_mul(self.families as usize)
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let port_action_overlap_sign = Buffer::alloc(port_family_population)?;
        let port_action_overlap_limbs = Buffer::alloc(
            port_family_population
                .checked_mul(overlap_limb_count as usize)
                .and_then(|length| length.checked_mul(std::mem::size_of::<u32>()))
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?,
        )?;
        let port_reflected_overlap_sign = Buffer::alloc(port_family_population)?;
        let port_reflected_overlap_limbs = Buffer::alloc(
            port_family_population
                .checked_mul(overlap_limb_count as usize)
                .and_then(|length| length.checked_mul(std::mem::size_of::<u32>()))
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?,
        )?;
        let port_receiver_population = port_population
            .checked_mul(self.receiver_count as usize)
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let port_receiver_overlap_sign = Buffer::alloc(port_receiver_population)?;
        let port_receiver_overlap_limbs = Buffer::alloc(
            port_receiver_population
                .checked_mul(overlap_limb_count as usize)
                .and_then(|length| length.checked_mul(std::mem::size_of::<u32>()))
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?,
        )?;
        let port_receiver_action_norm_sign = Buffer::alloc(port_receiver_population)?;
        let port_receiver_action_norm_limbs = Buffer::alloc(
            port_receiver_population
                .checked_mul(overlap_limb_count as usize)
                .and_then(|length| length.checked_mul(std::mem::size_of::<u32>()))
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?,
        )?;
        let joint_real_sign = Buffer::alloc(1)?;
        let joint_real_limbs =
            Buffer::alloc(radiation_limb_count as usize * std::mem::size_of::<u32>())?;
        let joint_imaginary_sign = Buffer::alloc(1)?;
        let joint_imaginary_limbs =
            Buffer::alloc(radiation_limb_count as usize * std::mem::size_of::<u32>())?;
        let incoming_real_sign_device = Buffer::of(&[incoming_real_sign])?;
        let incoming_real_limbs_device = Buffer::of(&incoming_real_limbs)?;
        let incoming_imaginary_sign_device = Buffer::of(&[incoming_imaginary_sign])?;
        let incoming_imaginary_limbs_device = Buffer::of(&incoming_imaginary_limbs)?;
        let compatibility_sign = Buffer::alloc(component_population)?;
        let compatibility_limbs = Buffer::alloc(
            component_population
                .checked_mul(compatibility_limb_count as usize)
                .and_then(|length| length.checked_mul(std::mem::size_of::<u32>()))
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?,
        )?;
        let phase_norm_limbs = Buffer::alloc(
            component_population
                .checked_mul(norm_limb_count as usize)
                .and_then(|length| length.checked_mul(std::mem::size_of::<u32>()))
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?,
        )?;
        let phase_locked = Buffer::alloc(port_population)?;
        let phase_pair_dominates = Buffer::alloc(phase_pair_population)?;
        let phase_square_scratch = Buffer::alloc(
            phase_pair_population
                .checked_mul(square_limb_count as usize)
                .and_then(|length| length.checked_mul(std::mem::size_of::<u32>()))
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?,
        )?;
        let phase_left_cross_scratch = Buffer::alloc(
            phase_pair_population
                .checked_mul(cross_limb_count as usize)
                .and_then(|length| length.checked_mul(std::mem::size_of::<u32>()))
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?,
        )?;
        let phase_right_cross_scratch = Buffer::alloc(
            phase_pair_population
                .checked_mul(cross_limb_count as usize)
                .and_then(|length| length.checked_mul(std::mem::size_of::<u32>()))
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?,
        )?;
        let stored_real_sign = Buffer::alloc(1)?;
        let stored_real_limbs =
            Buffer::alloc(stored_limb_count as usize * std::mem::size_of::<u32>())?;
        let stored_imaginary_sign = Buffer::alloc(1)?;
        let stored_imaginary_limbs =
            Buffer::alloc(stored_limb_count as usize * std::mem::size_of::<u32>())?;
        let scratch = Buffer::alloc(stored_limb_count as usize * std::mem::size_of::<u32>())?;

        let mut cell_offsets_pointer = cell_offsets.pointer;
        let mut cell_factors_pointer = cell_factors.pointer;
        let mut cell_multiplicity_signs_pointer = cell_multiplicity_signs.pointer;
        let mut cell_multiplicities_pointer = cell_multiplicities.pointer;
        let mut support_reflected_scale_pointer = support_reflected_scale.pointer;
        let mut support_pair_scale_pointer = support_pair_scale.pointer;
        let mut support_action_scale_pointer = support_action_scale.pointer;
        let mut factor_receiver_observations_pointer = factor_receiver_observations.pointer;
        let mut factor_capacity_pointer = self.factor_capacity.pointer;
        let mut family_orientation_pointer = self.family_orientation.pointer;
        let mut family_real_sign_pointer = self.family_real_sign.pointer;
        let mut family_real_limbs_pointer = self.family_real_limbs.pointer;
        let mut family_imaginary_sign_pointer = self.family_imaginary_sign.pointer;
        let mut family_imaginary_limbs_pointer = self.family_imaginary_limbs.pointer;
        let mut overlap_sign_pointer = overlap_sign.pointer;
        let mut overlap_limbs_pointer = overlap_limbs.pointer;
        let mut reflected_overlap_sign_pointer = reflected_overlap_sign.pointer;
        let mut reflected_overlap_limbs_pointer = reflected_overlap_limbs.pointer;
        let mut receiver_overlap_sign_pointer = receiver_overlap_sign.pointer;
        let mut receiver_overlap_limbs_pointer = receiver_overlap_limbs.pointer;
        let mut receiver_action_norm_sign_pointer = receiver_action_norm_sign.pointer;
        let mut receiver_action_norm_limbs_pointer = receiver_action_norm_limbs.pointer;
        let mut overlap_scratch_pointer = overlap_scratch.pointer;
        let mut contact_real_sign_pointer = contact_real_sign.pointer;
        let mut contact_real_limbs_pointer = contact_real_limbs.pointer;
        let mut contact_imaginary_sign_pointer = contact_imaginary_sign.pointer;
        let mut contact_imaginary_limbs_pointer = contact_imaginary_limbs.pointer;
        let mut support_count_wire = support_count;
        let mut factor_count_wire = self.factors;
        let mut family_count_wire = self.families;
        let mut multiplicity_limb_count_wire = multiplicity_limb_count;
        let mut support_scale_limb_count_wire = support_scale_limb_count;
        let mut receiver_count_wire = self.receiver_count;
        let mut overlap_limb_count_wire = overlap_limb_count;
        let mut family_limb_count_wire = self.family_limb_count;
        let mut contact_limb_count_wire = contact_limb_count;
        let mut contact_arguments: [*mut c_void; 36] = [
            &mut cell_offsets_pointer as *mut u64 as *mut c_void,
            &mut cell_factors_pointer as *mut u64 as *mut c_void,
            &mut cell_multiplicity_signs_pointer as *mut u64 as *mut c_void,
            &mut cell_multiplicities_pointer as *mut u64 as *mut c_void,
            &mut support_reflected_scale_pointer as *mut u64 as *mut c_void,
            &mut support_pair_scale_pointer as *mut u64 as *mut c_void,
            &mut support_action_scale_pointer as *mut u64 as *mut c_void,
            &mut factor_receiver_observations_pointer as *mut u64 as *mut c_void,
            &mut factor_capacity_pointer as *mut u64 as *mut c_void,
            &mut family_orientation_pointer as *mut u64 as *mut c_void,
            &mut family_real_sign_pointer as *mut u64 as *mut c_void,
            &mut family_real_limbs_pointer as *mut u64 as *mut c_void,
            &mut family_imaginary_sign_pointer as *mut u64 as *mut c_void,
            &mut family_imaginary_limbs_pointer as *mut u64 as *mut c_void,
            &mut overlap_sign_pointer as *mut u64 as *mut c_void,
            &mut overlap_limbs_pointer as *mut u64 as *mut c_void,
            &mut reflected_overlap_sign_pointer as *mut u64 as *mut c_void,
            &mut reflected_overlap_limbs_pointer as *mut u64 as *mut c_void,
            &mut receiver_overlap_sign_pointer as *mut u64 as *mut c_void,
            &mut receiver_overlap_limbs_pointer as *mut u64 as *mut c_void,
            &mut receiver_action_norm_sign_pointer as *mut u64 as *mut c_void,
            &mut receiver_action_norm_limbs_pointer as *mut u64 as *mut c_void,
            &mut overlap_scratch_pointer as *mut u64 as *mut c_void,
            &mut contact_real_sign_pointer as *mut u64 as *mut c_void,
            &mut contact_real_limbs_pointer as *mut u64 as *mut c_void,
            &mut contact_imaginary_sign_pointer as *mut u64 as *mut c_void,
            &mut contact_imaginary_limbs_pointer as *mut u64 as *mut c_void,
            &mut support_count_wire as *mut u32 as *mut c_void,
            &mut factor_count_wire as *mut u32 as *mut c_void,
            &mut family_count_wire as *mut u32 as *mut c_void,
            &mut multiplicity_limb_count_wire as *mut u32 as *mut c_void,
            &mut support_scale_limb_count_wire as *mut u32 as *mut c_void,
            &mut receiver_count_wire as *mut u32 as *mut c_void,
            &mut overlap_limb_count_wire as *mut u32 as *mut c_void,
            &mut family_limb_count_wire as *mut u32 as *mut c_void,
            &mut contact_limb_count_wire as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card.membrane_boundary_chain_contacts,
                    self.card.grid_for(contact_work_population as u64)?,
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
            "cuLaunchKernel(conduct_membrane_boundary_chain_contacts)",
        )?;

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
        let mut port_action_overlap_sign_pointer = port_action_overlap_sign.pointer;
        let mut port_action_overlap_limbs_pointer = port_action_overlap_limbs.pointer;
        let mut port_reflected_overlap_sign_pointer = port_reflected_overlap_sign.pointer;
        let mut port_reflected_overlap_limbs_pointer = port_reflected_overlap_limbs.pointer;
        let mut port_receiver_overlap_sign_pointer = port_receiver_overlap_sign.pointer;
        let mut port_receiver_overlap_limbs_pointer = port_receiver_overlap_limbs.pointer;
        let mut port_receiver_action_norm_sign_pointer = port_receiver_action_norm_sign.pointer;
        let mut port_receiver_action_norm_limbs_pointer = port_receiver_action_norm_limbs.pointer;
        let mut port_count_wire = port_count;
        let mut radiation_limb_count_wire = radiation_limb_count;
        let mut radiation_arguments: [*mut c_void; 40] = [
            &mut support_port_pointer as *mut u64 as *mut c_void,
            &mut overlap_sign_pointer as *mut u64 as *mut c_void,
            &mut overlap_limbs_pointer as *mut u64 as *mut c_void,
            &mut reflected_overlap_sign_pointer as *mut u64 as *mut c_void,
            &mut reflected_overlap_limbs_pointer as *mut u64 as *mut c_void,
            &mut receiver_overlap_sign_pointer as *mut u64 as *mut c_void,
            &mut receiver_overlap_limbs_pointer as *mut u64 as *mut c_void,
            &mut receiver_action_norm_sign_pointer as *mut u64 as *mut c_void,
            &mut receiver_action_norm_limbs_pointer as *mut u64 as *mut c_void,
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
            &mut port_action_overlap_sign_pointer as *mut u64 as *mut c_void,
            &mut port_action_overlap_limbs_pointer as *mut u64 as *mut c_void,
            &mut port_reflected_overlap_sign_pointer as *mut u64 as *mut c_void,
            &mut port_reflected_overlap_limbs_pointer as *mut u64 as *mut c_void,
            &mut port_receiver_overlap_sign_pointer as *mut u64 as *mut c_void,
            &mut port_receiver_overlap_limbs_pointer as *mut u64 as *mut c_void,
            &mut port_receiver_action_norm_sign_pointer as *mut u64 as *mut c_void,
            &mut port_receiver_action_norm_limbs_pointer as *mut u64 as *mut c_void,
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
                    self.card.membrane_boundary_chain_radiation,
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
            "cuLaunchKernel(gather_membrane_boundary_chain_radiation)",
        )?;

        let mut incoming_real_sign_pointer = incoming_real_sign_device.pointer;
        let mut incoming_real_limbs_pointer = incoming_real_limbs_device.pointer;
        let mut incoming_imaginary_sign_pointer = incoming_imaginary_sign_device.pointer;
        let mut incoming_imaginary_limbs_pointer = incoming_imaginary_limbs_device.pointer;
        let mut compatibility_sign_pointer = compatibility_sign.pointer;
        let mut compatibility_limbs_pointer = compatibility_limbs.pointer;
        let mut phase_norm_limbs_pointer = phase_norm_limbs.pointer;
        let mut phase_locked_pointer = phase_locked.pointer;
        let mut phase_pair_dominates_pointer = phase_pair_dominates.pointer;
        let mut phase_square_scratch_pointer = phase_square_scratch.pointer;
        let mut phase_left_cross_scratch_pointer = phase_left_cross_scratch.pointer;
        let mut phase_right_cross_scratch_pointer = phase_right_cross_scratch.pointer;
        let mut compatibility_limb_count_wire = compatibility_limb_count;
        let mut norm_limb_count_wire = norm_limb_count;
        let mut square_limb_count_wire = square_limb_count;
        let mut cross_limb_count_wire = cross_limb_count;
        let mut component_count_wire = component_count;
        let mut phase_component_arguments: [*mut c_void; 20] = [
            &mut family_real_limbs_pointer as *mut u64 as *mut c_void,
            &mut family_imaginary_limbs_pointer as *mut u64 as *mut c_void,
            &mut port_action_overlap_sign_pointer as *mut u64 as *mut c_void,
            &mut port_action_overlap_limbs_pointer as *mut u64 as *mut c_void,
            &mut port_reflected_overlap_sign_pointer as *mut u64 as *mut c_void,
            &mut port_reflected_overlap_limbs_pointer as *mut u64 as *mut c_void,
            &mut port_receiver_overlap_sign_pointer as *mut u64 as *mut c_void,
            &mut port_receiver_overlap_limbs_pointer as *mut u64 as *mut c_void,
            &mut port_receiver_action_norm_limbs_pointer as *mut u64 as *mut c_void,
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
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card.membrane_boundary_phase_components,
                    self.card.grid_for(component_population as u64)?,
                    1,
                    1,
                    self.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    phase_component_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(form_membrane_boundary_phase_components)",
        )?;
        let mut phase_chart_count_wire = 1_u32;
        let mut phase_pair_arguments: [*mut c_void; 14] = [
            &mut compatibility_sign_pointer as *mut u64 as *mut c_void,
            &mut compatibility_limbs_pointer as *mut u64 as *mut c_void,
            &mut phase_norm_limbs_pointer as *mut u64 as *mut c_void,
            &mut phase_pair_dominates_pointer as *mut u64 as *mut c_void,
            &mut phase_square_scratch_pointer as *mut u64 as *mut c_void,
            &mut phase_left_cross_scratch_pointer as *mut u64 as *mut c_void,
            &mut phase_right_cross_scratch_pointer as *mut u64 as *mut c_void,
            &mut port_count_wire as *mut u32 as *mut c_void,
            &mut phase_chart_count_wire as *mut u32 as *mut c_void,
            &mut component_count_wire as *mut u32 as *mut c_void,
            &mut compatibility_limb_count_wire as *mut u32 as *mut c_void,
            &mut norm_limb_count_wire as *mut u32 as *mut c_void,
            &mut square_limb_count_wire as *mut u32 as *mut c_void,
            &mut cross_limb_count_wire as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card.membrane_boundary_phase_pairs,
                    self.card.grid_for(phase_pair_population as u64)?,
                    1,
                    1,
                    self.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    phase_pair_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(compare_membrane_boundary_phase_pairs)",
        )?;
        let mut phase_select_arguments: [*mut c_void; 4] = [
            &mut phase_pair_dominates_pointer as *mut u64 as *mut c_void,
            &mut phase_locked_pointer as *mut u64 as *mut c_void,
            &mut port_count_wire as *mut u32 as *mut c_void,
            &mut phase_chart_count_wire as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card.membrane_boundary_phase_select,
                    self.card.grid_for(port_population as u64)?,
                    1,
                    1,
                    self.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    phase_select_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(select_membrane_boundary_phase_front)",
        )?;

        let mut stored_real_sign_pointer = stored_real_sign.pointer;
        let mut stored_real_limbs_pointer = stored_real_limbs.pointer;
        let mut stored_imaginary_sign_pointer = stored_imaginary_sign.pointer;
        let mut stored_imaginary_limbs_pointer = stored_imaginary_limbs.pointer;
        let mut scratch_pointer = scratch.pointer;
        let mut joint_scale_wire = joint_scale;
        let mut stored_limb_count_wire = stored_limb_count;
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
            &mut scratch_pointer as *mut u64 as *mut c_void,
            &mut radiation_limb_count_wire as *mut u32 as *mut c_void,
            &mut stored_limb_count_wire as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card.membrane_boundary_chain_balance,
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
            "cuLaunchKernel(balance_membrane_boundary_chain)",
        )?;
        driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
        self.card.launches += 6;

        let mut overlap_sign_host = vec![0_u8; response_population];
        let mut overlap_limbs_host = vec![0_u32; response_population * overlap_limb_count as usize];
        let mut reflected_overlap_sign_host = vec![0_u8; response_population];
        let mut reflected_overlap_limbs_host =
            vec![0_u32; response_population * overlap_limb_count as usize];
        let mut receiver_overlap_sign_host = vec![0_u8; receiver_response_population];
        let mut receiver_overlap_limbs_host =
            vec![0_u32; receiver_response_population * overlap_limb_count as usize];
        let mut receiver_action_norm_sign_host = vec![0_u8; receiver_response_population];
        let mut receiver_action_norm_limbs_host =
            vec![0_u32; receiver_response_population * overlap_limb_count as usize];
        overlap_sign.read(&mut overlap_sign_host)?;
        overlap_limbs.read(&mut overlap_limbs_host)?;
        reflected_overlap_sign.read(&mut reflected_overlap_sign_host)?;
        reflected_overlap_limbs.read(&mut reflected_overlap_limbs_host)?;
        receiver_overlap_sign.read(&mut receiver_overlap_sign_host)?;
        receiver_overlap_limbs.read(&mut receiver_overlap_limbs_host)?;
        receiver_action_norm_sign.read(&mut receiver_action_norm_sign_host)?;
        receiver_action_norm_limbs.read(&mut receiver_action_norm_limbs_host)?;
        let mut port_receiver_action_norm_sign_host = vec![0_u8; port_receiver_population];
        port_receiver_action_norm_sign.read(&mut port_receiver_action_norm_sign_host)?;
        if overlap_sign_host.iter().any(|sign| *sign > 2)
            || reflected_overlap_sign_host.iter().any(|sign| *sign > 2)
            || receiver_overlap_sign_host.iter().any(|sign| *sign > 2)
            || receiver_action_norm_sign_host.iter().any(|sign| *sign > 1)
            || port_receiver_action_norm_sign_host
                .iter()
                .any(|sign| *sign > 1)
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let mut support_real_sign_host = vec![0_u8; supports.len()];
        let mut support_imaginary_sign_host = vec![0_u8; supports.len()];
        let mut support_real_limbs_host =
            vec![0_u32; supports.len() * radiation_limb_count as usize];
        let mut support_imaginary_limbs_host =
            vec![0_u32; supports.len() * radiation_limb_count as usize];
        support_real_sign.read(&mut support_real_sign_host)?;
        support_imaginary_sign.read(&mut support_imaginary_sign_host)?;
        support_real_limbs.read(&mut support_real_limbs_host)?;
        support_imaginary_limbs.read(&mut support_imaginary_limbs_host)?;
        let mut port_real_sign_host = vec![0_u8; port_population];
        let mut port_imaginary_sign_host = vec![0_u8; port_population];
        let mut port_real_limbs_host = vec![0_u32; port_population * radiation_limb_count as usize];
        let mut port_imaginary_limbs_host =
            vec![0_u32; port_population * radiation_limb_count as usize];
        port_real_sign.read(&mut port_real_sign_host)?;
        port_imaginary_sign.read(&mut port_imaginary_sign_host)?;
        port_real_limbs.read(&mut port_real_limbs_host)?;
        port_imaginary_limbs.read(&mut port_imaginary_limbs_host)?;
        let mut phase_locked_host = vec![0_u8; port_population];
        phase_locked.read(&mut phase_locked_host)?;
        let phase_locked_port_population = phase_locked_host
            .iter()
            .filter(|selected| **selected != 0)
            .count();
        if phase_locked_port_population == 0
            || phase_locked_host.iter().any(|selected| *selected > 1)
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let mut joint_real_sign_host = [0_u8; 1];
        let mut joint_imaginary_sign_host = [0_u8; 1];
        let mut joint_real_limbs_host = vec![0_u32; radiation_limb_count as usize];
        let mut joint_imaginary_limbs_host = vec![0_u32; radiation_limb_count as usize];
        joint_real_sign.read(&mut joint_real_sign_host)?;
        joint_imaginary_sign.read(&mut joint_imaginary_sign_host)?;
        joint_real_limbs.read(&mut joint_real_limbs_host)?;
        joint_imaginary_limbs.read(&mut joint_imaginary_limbs_host)?;
        let mut stored_real_sign_host = [0_u8; 1];
        let mut stored_imaginary_sign_host = [0_u8; 1];
        let mut stored_real_limbs_host = vec![0_u32; stored_limb_count as usize];
        let mut stored_imaginary_limbs_host = vec![0_u32; stored_limb_count as usize];
        stored_real_sign.read(&mut stored_real_sign_host)?;
        stored_imaginary_sign.read(&mut stored_imaginary_sign_host)?;
        stored_real_limbs.read(&mut stored_real_limbs_host)?;
        stored_imaginary_limbs.read(&mut stored_imaginary_limbs_host)?;

        let decode_current = |real_sign: u8,
                              real_limbs: &[u32],
                              imaginary_sign: u8,
                              imaginary_limbs: &[u32],
                              denominator: &BigInt|
         -> Result<ExactComplexWaveCurrent, CudaRefineError> {
            Ok(ExactComplexWaveCurrent::new(
                decode_component(real_sign, real_limbs, denominator)?,
                decode_component(imaginary_sign, imaginary_limbs, denominator)?,
            ))
        };
        let mut support_returns = Vec::with_capacity(supports.len());
        for (support_at, support) in supports.iter().enumerate() {
            let overlap_begin = support_at * self.families as usize;
            let limb_begin = support_at * radiation_limb_count as usize;
            let limb_end = limb_begin + radiation_limb_count as usize;
            let receiver_begin = support_at * self.receiver_count as usize;
            let receiver_end = receiver_begin + self.receiver_count as usize;
            support_returns.push(ResidentBoundaryChainSupportReturn {
                port: support.port,
                reflected_family_overlaps: (overlap_begin..overlap_begin + self.families as usize)
                    .map(|response| {
                        let begin = response * overlap_limb_count as usize;
                        let end = begin + overlap_limb_count as usize;
                        decode_component(
                            reflected_overlap_sign_host[response],
                            &reflected_overlap_limbs_host[begin..end],
                            &BigInt::one(),
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()?,
                family_overlaps: (overlap_begin..overlap_begin + self.families as usize)
                    .map(|response| {
                        let begin = response * overlap_limb_count as usize;
                        let end = begin + overlap_limb_count as usize;
                        decode_component(
                            overlap_sign_host[response],
                            &overlap_limbs_host[begin..end],
                            &BigInt::one(),
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()?,
                receiver_overlaps: (receiver_begin..receiver_end)
                    .map(|receiver| {
                        let begin = receiver * overlap_limb_count as usize;
                        let end = begin + overlap_limb_count as usize;
                        decode_component(
                            receiver_overlap_sign_host[receiver],
                            &receiver_overlap_limbs_host[begin..end],
                            &BigInt::one(),
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()?,
                receiver_action_norms: (receiver_begin..receiver_end)
                    .map(|receiver| {
                        let begin = receiver * overlap_limb_count as usize;
                        let end = begin + overlap_limb_count as usize;
                        BigUint::new(receiver_action_norm_limbs_host[begin..end].to_vec())
                    })
                    .collect(),
                returned_response: decode_current(
                    support_real_sign_host[support_at],
                    &support_real_limbs_host[limb_begin..limb_end],
                    support_imaginary_sign_host[support_at],
                    &support_imaginary_limbs_host[limb_begin..limb_end],
                    &self.family_common_denominator,
                )?,
            });
        }
        let mut port_returns = Vec::with_capacity(port_population);
        for port in 0..port_population {
            let limb_begin = port * radiation_limb_count as usize;
            let limb_end = limb_begin + radiation_limb_count as usize;
            let returned_response = decode_current(
                port_real_sign_host[port],
                &port_real_limbs_host[limb_begin..limb_end],
                port_imaginary_sign_host[port],
                &port_imaginary_limbs_host[limb_begin..limb_end],
                &self.family_common_denominator,
            )?;
            port_returns.push(ResidentBoundaryChainPortReturn {
                port: port as u32,
                lies_in_joint_port_kernel: returned_response.is_zero(),
                lies_in_receiver_phase_front: phase_locked_host[port] != 0,
                returned_response,
            });
        }
        let total_returned_current = decode_current(
            joint_real_sign_host[0],
            &joint_real_limbs_host,
            joint_imaginary_sign_host[0],
            &joint_imaginary_limbs_host,
            &self.family_common_denominator,
        )?;
        let stored_difference = decode_current(
            stored_real_sign_host[0],
            &stored_real_limbs_host,
            stored_imaginary_sign_host[0],
            &stored_imaginary_limbs_host,
            &balance_denominator,
        )?;
        let local_balance_closes =
            stored_difference.add(&total_returned_current) == *entering_current;
        if !local_balance_closes
            || port_returns
                .iter()
                .fold(ExactComplexWaveCurrent::zero(), |total, port| {
                    total.add(&port.returned_response)
                })
                != total_returned_current
        {
            return Err(CudaRefineError::MembraneInteriorCurrentOutsideApparatus);
        }

        let successor_host_ingress_octets = [
            std::mem::size_of_val(offsets.as_slice()),
            std::mem::size_of_val(factors.as_slice()),
            std::mem::size_of_val(multiplicity_signs.as_slice()),
            std::mem::size_of_val(multiplicity_limbs.as_slice()),
            std::mem::size_of_val(support_ports.as_slice()),
            std::mem::size_of_val(support_reflected_scale_limbs.as_slice()),
            std::mem::size_of_val(support_pair_scale_limbs.as_slice()),
            std::mem::size_of_val(support_action_scale_limbs.as_slice()),
            2 * std::mem::size_of::<u8>()
                + std::mem::size_of_val(incoming_real_limbs.as_slice())
                + std::mem::size_of_val(incoming_imaginary_limbs.as_slice())
                + std::mem::size_of::<u64>(),
        ]
        .into_iter()
        .try_fold(0_u64, |total, octets| {
            total.checked_add(u64::try_from(octets).ok()?)
        })
        .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let successor_host_egress_octets = [
            std::mem::size_of_val(overlap_sign_host.as_slice()),
            std::mem::size_of_val(overlap_limbs_host.as_slice()),
            std::mem::size_of_val(reflected_overlap_sign_host.as_slice()),
            std::mem::size_of_val(reflected_overlap_limbs_host.as_slice()),
            std::mem::size_of_val(receiver_overlap_sign_host.as_slice()),
            std::mem::size_of_val(receiver_overlap_limbs_host.as_slice()),
            std::mem::size_of_val(receiver_action_norm_sign_host.as_slice()),
            std::mem::size_of_val(receiver_action_norm_limbs_host.as_slice()),
            std::mem::size_of_val(port_receiver_action_norm_sign_host.as_slice()),
            std::mem::size_of_val(support_real_sign_host.as_slice()),
            std::mem::size_of_val(support_imaginary_sign_host.as_slice()),
            std::mem::size_of_val(support_real_limbs_host.as_slice()),
            std::mem::size_of_val(support_imaginary_limbs_host.as_slice()),
            std::mem::size_of_val(port_real_sign_host.as_slice()),
            std::mem::size_of_val(port_imaginary_sign_host.as_slice()),
            std::mem::size_of_val(port_real_limbs_host.as_slice()),
            std::mem::size_of_val(port_imaginary_limbs_host.as_slice()),
            std::mem::size_of_val(phase_locked_host.as_slice()),
            std::mem::size_of_val(joint_real_sign_host.as_slice()),
            std::mem::size_of_val(joint_imaginary_sign_host.as_slice()),
            std::mem::size_of_val(joint_real_limbs_host.as_slice()),
            std::mem::size_of_val(joint_imaginary_limbs_host.as_slice()),
            std::mem::size_of_val(stored_real_sign_host.as_slice()),
            std::mem::size_of_val(stored_imaginary_sign_host.as_slice()),
            std::mem::size_of_val(stored_real_limbs_host.as_slice()),
            std::mem::size_of_val(stored_imaginary_limbs_host.as_slice()),
        ]
        .into_iter()
        .try_fold(0_u64, |total, octets| {
            total.checked_add(u64::try_from(octets).ok()?)
        })
        .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let phase_working_octets = component_population
            .checked_mul(compatibility_limb_count as usize + norm_limb_count as usize)
            .and_then(|limbs| limbs.checked_mul(std::mem::size_of::<u32>()))
            .and_then(|octets| octets.checked_add(component_population))
            .and_then(|octets| octets.checked_add(port_population))
            .and_then(|octets| octets.checked_add(phase_pair_population))
            .and_then(|octets| {
                phase_pair_population
                    .checked_mul(square_limb_count as usize + 2 * cross_limb_count as usize)
                    .and_then(|limbs| limbs.checked_mul(std::mem::size_of::<u32>()))
                    .and_then(|scratch| octets.checked_add(scratch))
            })
            .and_then(|octets| u64::try_from(octets).ok())
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let resident_working_octets = successor_host_ingress_octets
            .checked_add(successor_host_egress_octets)
            .and_then(|total| total.checked_add(phase_working_octets))
            .and_then(|total| {
                total.checked_add(
                    u64::from(stored_limb_count).checked_mul(std::mem::size_of::<u32>() as u64)?,
                )
            })
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        Ok(ResidentJointBoundaryChainReturn {
            support_returns,
            port_returns,
            entering_current: entering_current.clone(),
            total_returned_current,
            stored_difference,
            local_balance_closes,
            phase_locked_port_population,
            phase_front_is_unique: phase_locked_port_population == 1,
            device: self.card.device_name.clone(),
            context_identity: self.card.context as usize,
            launches: 6,
            device_dependency_edges: 5,
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
        })
    }
}
