use super::*;

impl ResidentMembraneInteriorWord {
    #[allow(clippy::too_many_arguments)]
    pub fn mount(
        card: CudaRefineExecutor,
        factor_capacity: &[u64],
        cell_offsets: &[u64],
        cell_factors: &[u32],
        cell_multiplicities: &[u64],
        cell_total_mass: &[u64],
        family_orientation: &[i8],
        family_currents: &[ExactComplexWaveCurrent],
    ) -> Result<Self, CudaRefineError> {
        let cells = cell_total_mass.len();
        let factors = factor_capacity.len();
        let families = family_currents.len();
        let support_terms = cell_factors.len();
        if cells == 0
            || factors == 0
            || families == 0
            || cells > u32::MAX as usize
            || factors > u32::MAX as usize
            || families > u32::MAX as usize
            || cell_offsets.len() != cells + 1
            || cell_offsets.first() != Some(&0)
            || cell_offsets.last().copied() != u64::try_from(support_terms).ok()
            || cell_multiplicities.len() != support_terms
            || family_orientation.len() != families.saturating_mul(factors)
            || factor_capacity.iter().any(|capacity| *capacity == 0)
            || family_orientation
                .iter()
                .any(|orientation| !matches!(*orientation, -1 | 0 | 1))
            || family_currents.iter().all(ExactComplexWaveCurrent::is_zero)
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let mut maximal_cell_mass = 0_u64;
        let mut maximal_multiplicity = 0_u64;
        for cell in 0..cells {
            let begin = usize::try_from(cell_offsets[cell])
                .map_err(|_| CudaRefineError::MembraneInteriorWordShape)?;
            let end = usize::try_from(cell_offsets[cell + 1])
                .map_err(|_| CudaRefineError::MembraneInteriorWordShape)?;
            if begin >= end || end > support_terms || cell_total_mass[cell] == 0 {
                return Err(CudaRefineError::MembraneInteriorWordShape);
            }
            let factors_here = &cell_factors[begin..end];
            if factors_here.windows(2).any(|pair| pair[0] >= pair[1])
                || factors_here
                    .iter()
                    .any(|factor| *factor as usize >= factors)
            {
                return Err(CudaRefineError::MembraneInteriorWordShape);
            }
            let measured = cell_multiplicities[begin..end]
                .iter()
                .try_fold(0_u64, |sum, value| sum.checked_add(*value))
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            if measured != cell_total_mass[cell]
                || cell_multiplicities[begin..end]
                    .iter()
                    .any(|value| *value == 0)
            {
                return Err(CudaRefineError::MembraneInteriorWordShape);
            }
            maximal_cell_mass = maximal_cell_mass.max(measured);
            maximal_multiplicity = maximal_multiplicity.max(
                cell_multiplicities[begin..end]
                    .iter()
                    .copied()
                    .max()
                    .unwrap_or(0),
            );
        }
        let total_capacity = factor_capacity
            .iter()
            .try_fold(0_u128, |sum, capacity| {
                sum.checked_add(u128::from(*capacity))
            })
            .filter(|capacity| *capacity <= u128::from(u64::MAX))
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let maximal_overlap = total_capacity
            .checked_mul(u128::from(maximal_multiplicity).pow(2))
            .filter(|bound| *bound <= i64::MAX as u128)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        u128::from(maximal_cell_mass)
            .checked_mul(u128::from(maximal_cell_mass))
            .filter(|denominator| *denominator <= u64::MAX as u128)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;

        let mut common_denominator = BigInt::one();
        for current in family_currents {
            for component in [&current.real, &current.imaginary] {
                common_denominator = lcm_positive(common_denominator, component.denom());
            }
        }
        let maximal_family_numerator = family_currents
            .iter()
            .flat_map(|current| [&current.real, &current.imaginary])
            .map(|component| (component.numer() * (&common_denominator / component.denom())).abs())
            .max()
            .unwrap_or_else(BigInt::zero);
        let (_, digits) = maximal_family_numerator.to_u32_digits();
        let family_limb_count = digits.len().max(1);
        if family_limb_count > u32::MAX as usize {
            return Err(CudaRefineError::MembraneInteriorCurrentOutsideApparatus);
        }
        let mut real_sign = Vec::with_capacity(families);
        let mut real_limbs = Vec::with_capacity(families * family_limb_count);
        let mut imaginary_sign = Vec::with_capacity(families);
        let mut imaginary_limbs = Vec::with_capacity(families * family_limb_count);
        for current in family_currents {
            let (sign, limbs) =
                encode_component(&current.real, &common_denominator, family_limb_count)?;
            real_sign.push(sign);
            real_limbs.extend(limbs);
            let (sign, limbs) =
                encode_component(&current.imaginary, &common_denominator, family_limb_count)?;
            imaginary_sign.push(sign);
            imaginary_limbs.extend(limbs);
        }
        let constitutive_family_identity_sha256 = serde_json::to_vec(&(
            "holonic-engine.resident-constitutive-families.v1",
            family_orientation,
            family_currents,
        ))
        .map(|bytes| {
            Sha256::digest(bytes)
                .iter()
                .map(|octet| format!("{octet:02x}"))
                .collect::<String>()
        })
        .map_err(|_| CudaRefineError::MembraneInteriorWordShape)?;
        let mount_host_ingress_octets = [
            std::mem::size_of_val(factor_capacity),
            std::mem::size_of_val(cell_offsets),
            std::mem::size_of_val(cell_factors),
            std::mem::size_of_val(cell_multiplicities),
            std::mem::size_of_val(cell_total_mass),
            std::mem::size_of_val(family_orientation),
            std::mem::size_of_val(real_sign.as_slice()),
            std::mem::size_of_val(real_limbs.as_slice()),
            std::mem::size_of_val(imaginary_sign.as_slice()),
            std::mem::size_of_val(imaginary_limbs.as_slice()),
        ]
        .into_iter()
        .try_fold(0_u64, |sum, octets| {
            sum.checked_add(u64::try_from(octets).ok()?)
        })
        .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        driver(unsafe { cuCtxSetCurrent(card.context) }, "cuCtxSetCurrent")?;
        Ok(Self {
            cell_offsets: Buffer::of(cell_offsets)?,
            cell_factors: Buffer::of(cell_factors)?,
            cell_multiplicities: Buffer::of(cell_multiplicities)?,
            cell_total_mass: Buffer::of(cell_total_mass)?,
            factor_capacity: Buffer::of(factor_capacity)?,
            family_orientation: Buffer::of(family_orientation)?,
            family_real_sign: Buffer::of(&real_sign)?,
            family_real_limbs: Buffer::of(&real_limbs)?,
            family_imaginary_sign: Buffer::of(&imaginary_sign)?,
            family_imaginary_limbs: Buffer::of(&imaginary_limbs)?,
            factor_receiver_observations: None,
            factor_receiver_classes: None,
            receiver_class_counts: None,
            receiver_count: 0,
            receiver_face_identity_sha256: None,
            quadratic_action: None,
            boundary_restriction_atlas: None,
            factored_receiver_history: None,
            observable_integral_form_frame: None,
            addressed_factored_receiver_frame: None,
            sparse_relational_atlas: None,
            sparse_relational_current: None,
            card,
            cells: cells as u32,
            factors: factors as u32,
            families: families as u32,
            family_limb_count: family_limb_count as u32,
            family_common_denominator: common_denominator,
            maximal_family_numerator,
            constitutive_family_identity_sha256,
            mount_host_ingress_octets,
            maximal_overlap_magnitude: maximal_overlap as u64,
            total_factor_capacity: total_capacity as u64,
        })
    }

    /// Mount the source-neutral relational phase incidence beside the singular membrane word.
    /// The three phase populations and row reconstruction addresses cross once. No later current
    /// may replace or resize this atlas.
    pub fn mount_sparse_relational_current_atlas(
        &mut self,
        atlas: &ResidentSparseRelationalCurrentAtlas,
    ) -> Result<(), CudaRefineError> {
        let rows = atlas.row_offsets.len().saturating_sub(1);
        let terms = atlas.term_factors.len();
        if rows == 0
            || rows > u32::MAX as usize
            || terms == 0
            || atlas.row_offsets.first() != Some(&0)
            || atlas.row_offsets.last().copied() != u64::try_from(terms).ok()
            || atlas.term_ingress_population.len() != terms
            || atlas.term_emanation_population.len() != terms
            || atlas.term_return_population.len() != terms
            || atlas.row_reconstruction_addresses.len() != rows
            || atlas
                .term_factors
                .iter()
                .any(|factor| *factor >= self.factors)
            || atlas
                .row_reconstruction_addresses
                .iter()
                .any(|address| !is_digest(address))
            || atlas
                .row_reconstruction_addresses
                .iter()
                .collect::<BTreeSet<_>>()
                .len()
                != rows
            || !is_digest(&atlas.identity_sha256)
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let mut term_rows = Vec::with_capacity(terms);
        let mut maximal_row_phase_mass = 0_u128;
        let mut factor_phase_mass = vec![0_u128; self.factors as usize];
        for row in 0..rows {
            let begin = usize::try_from(atlas.row_offsets[row])
                .map_err(|_| CudaRefineError::MembraneInteriorWordShape)?;
            let end = usize::try_from(atlas.row_offsets[row + 1])
                .map_err(|_| CudaRefineError::MembraneInteriorWordShape)?;
            if begin >= end || end > terms {
                return Err(CudaRefineError::MembraneInteriorWordShape);
            }
            let mut row_mass = 0_u128;
            for term in begin..end {
                let ingress = i128::from(atlas.term_ingress_population[term]);
                let real = i128::from(atlas.term_emanation_population[term]) - ingress;
                let imaginary = i128::from(atlas.term_return_population[term]) - ingress;
                let mass = real
                    .unsigned_abs()
                    .checked_add(imaginary.unsigned_abs())
                    .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
                row_mass = row_mass
                    .checked_add(mass)
                    .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
                let factor = atlas.term_factors[term] as usize;
                factor_phase_mass[factor] = factor_phase_mass[factor]
                    .checked_add(mass)
                    .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
                term_rows.push(row as u32);
            }
            maximal_row_phase_mass = maximal_row_phase_mass.max(row_mass);
        }
        if term_rows.len() != terms || maximal_row_phase_mass == 0 {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let maximal_factor_phase_mass = factor_phase_mass
            .into_iter()
            .max()
            .filter(|mass| *mass > 0)
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        if maximal_row_phase_mass > u128::from(u64::MAX)
            || maximal_factor_phase_mass > u128::from(u64::MAX)
        {
            return Err(CudaRefineError::MembraneInteriorCurrentOutsideApparatus);
        }
        let row_address_bytes = atlas.row_reconstruction_addresses.iter().try_fold(
            Vec::with_capacity(rows.saturating_mul(32)),
            |mut bytes, address| {
                for at in (0..address.len()).step_by(2) {
                    bytes.push(
                        u8::from_str_radix(&address[at..at + 2], 16)
                            .map_err(|_| CudaRefineError::MembraneInteriorWordShape)?,
                    );
                }
                Ok::<_, CudaRefineError>(bytes)
            },
        )?;
        let mut causal_adjoint = Sha256::new();
        causal_adjoint.update(b"holonic-engine.sparse-relational-causal-adjoint.v1");
        causal_adjoint.update(atlas.identity_sha256.as_bytes());
        causal_adjoint.update((rows as u64).to_le_bytes());
        causal_adjoint.update((terms as u64).to_le_bytes());
        causal_adjoint.update(self.factors.to_le_bytes());
        let causal_adjoint_identity_sha256 = causal_adjoint
            .finalize()
            .iter()
            .map(|octet| format!("{octet:02x}"))
            .collect::<String>();
        if let Some(mounted) = &self.sparse_relational_atlas {
            return if mounted.identity_sha256 == atlas.identity_sha256
                && mounted.causal_adjoint_identity_sha256 == causal_adjoint_identity_sha256
            {
                Ok(())
            } else {
                Err(CudaRefineError::MembraneInteriorWordShape)
            };
        }
        let resident_octets = [
            std::mem::size_of_val(atlas.row_offsets.as_slice()),
            std::mem::size_of_val(term_rows.as_slice()),
            std::mem::size_of_val(atlas.term_factors.as_slice()),
            std::mem::size_of_val(atlas.term_ingress_population.as_slice()),
            std::mem::size_of_val(atlas.term_emanation_population.as_slice()),
            std::mem::size_of_val(atlas.term_return_population.as_slice()),
            std::mem::size_of_val(row_address_bytes.as_slice()),
        ]
        .into_iter()
        .try_fold(0_u64, |sum, octets| {
            sum.checked_add(u64::try_from(octets).ok()?)
        })
        .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        driver(
            unsafe { cuCtxSetCurrent(self.card.context) },
            "cuCtxSetCurrent",
        )?;
        self.sparse_relational_atlas = Some(ResidentSparseRelationalCurrentAtlasMount {
            identity_sha256: atlas.identity_sha256.clone(),
            causal_adjoint_identity_sha256,
            constitutive_family_identity_sha256: self.constitutive_family_identity_sha256.clone(),
            row_population: rows as u32,
            term_population: terms as u64,
            row_offsets: Buffer::of(&atlas.row_offsets)?,
            term_rows: Buffer::of(&term_rows)?,
            term_factors: Buffer::of(&atlas.term_factors)?,
            term_ingress_population: Buffer::of(&atlas.term_ingress_population)?,
            term_emanation_population: Buffer::of(&atlas.term_emanation_population)?,
            term_return_population: Buffer::of(&atlas.term_return_population)?,
            _row_reconstruction_addresses: Buffer::of(&row_address_bytes)?,
            maximal_row_phase_mass: maximal_row_phase_mass as u64,
            maximal_factor_phase_mass: maximal_factor_phase_mass as u64,
            resident_octets,
        });
        self.mount_host_ingress_octets = self
            .mount_host_ingress_octets
            .checked_add(resident_octets)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        Ok(())
    }

    /// Stage one occurrence-local relational current on the card. The two launches are ordered on
    /// the existing context and deliberately do not synchronize or return an intermediate face;
    /// the subsequent quadratic join is their terminal consumer.
    pub fn stage_sparse_relational_current(
        &mut self,
        source_current_identity_sha256: &str,
        root_state: u32,
        factor_current: &[(u32, BigUint)],
    ) -> Result<(), CudaRefineError> {
        if !is_digest(source_current_identity_sha256)
            || factor_current.is_empty()
            || factor_current.windows(2).any(|pair| pair[0].0 >= pair[1].0)
            || factor_current
                .iter()
                .any(|(factor, current)| *factor >= self.factors || current.is_zero())
            || self.sparse_relational_current.is_some()
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let atlas = self
            .sparse_relational_atlas
            .as_ref()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let mut dense_current = vec![0_u64; self.factors as usize];
        let mut maximal_current = 0_u64;
        for (factor, current) in factor_current {
            let current = current
                .to_u64()
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            dense_current[*factor as usize] = current;
            maximal_current = maximal_current.max(current);
        }
        let forward_bound = u128::from(maximal_current)
            .checked_mul(u128::from(atlas.maximal_row_phase_mass))
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let returned_factor_bound = BigUint::from(forward_bound)
            * BigUint::from(atlas.maximal_factor_phase_mass)
            * BigUint::from(self.families)
            * BigUint::from(2_u8);
        let factor_limb_count = returned_factor_bound.to_u32_digits().len().max(2);
        let row_family_population = u64::from(atlas.row_population)
            .checked_mul(u64::from(self.families))
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let term_family_population = atlas
            .term_population
            .checked_mul(u64::from(self.families))
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let row_family_octets = usize::try_from(row_family_population)
            .ok()
            .and_then(|population| population.checked_mul(std::mem::size_of::<i64>()))
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let factor_octets = self.factors as usize * std::mem::size_of::<i64>();
        driver(
            unsafe { cuCtxSetCurrent(self.card.context) },
            "cuCtxSetCurrent",
        )?;
        let dense_current_device = Buffer::of(&dense_current)?;
        let row_family_real = Buffer::alloc(row_family_octets)?;
        let row_family_imaginary = Buffer::alloc(row_family_octets)?;
        let factor_real = Buffer::alloc(factor_octets)?;
        let factor_imaginary = Buffer::alloc(factor_octets)?;
        let state_present = Buffer::of(&[1_u32])?;
        let states = Buffer::of(&[root_state])?;
        factor_real.fill(0, factor_octets)?;
        factor_imaginary.fill(0, factor_octets)?;

        let mut forward = ptr::null_mut();
        let mut adjoint = ptr::null_mut();
        driver(
            unsafe {
                cuModuleGetFunction(
                    &mut forward,
                    self.card.module,
                    c"conduct_membrane_sparse_relational_forward".as_ptr(),
                )
            },
            "cuModuleGetFunction(conduct_membrane_sparse_relational_forward)",
        )?;
        let factor_real_sign = Buffer::alloc(self.factors as usize)?;
        let factor_real_limbs = Buffer::alloc(
            (self.factors as usize)
                .checked_mul(factor_limb_count)
                .and_then(|extent| extent.checked_mul(std::mem::size_of::<u32>()))
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        )?;
        let factor_imaginary_sign = Buffer::alloc(self.factors as usize)?;
        let factor_imaginary_limbs = Buffer::alloc(
            (self.factors as usize)
                .checked_mul(factor_limb_count)
                .and_then(|extent| extent.checked_mul(std::mem::size_of::<u32>()))
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        )?;
        let mut widen = ptr::null_mut();
        driver(
            unsafe {
                cuModuleGetFunction(
                    &mut widen,
                    self.card.module,
                    c"widen_membrane_sparse_relational_i64_current".as_ptr(),
                )
            },
            "cuModuleGetFunction(widen_membrane_sparse_relational_i64_current)",
        )?;
        let mut factor_real_pointer = factor_real.pointer;
        let mut factor_imaginary_pointer = factor_imaginary.pointer;
        let mut factor_real_sign_pointer = factor_real_sign.pointer;
        let mut factor_real_limbs_pointer = factor_real_limbs.pointer;
        let mut factor_imaginary_sign_pointer = factor_imaginary_sign.pointer;
        let mut factor_imaginary_limbs_pointer = factor_imaginary_limbs.pointer;
        let mut factor_count_wire = self.factors;
        let mut factor_limb_count_wire = factor_limb_count as u32;
        let mut widen_arguments: [*mut c_void; 8] = [
            &mut factor_real_pointer as *mut u64 as *mut c_void,
            &mut factor_imaginary_pointer as *mut u64 as *mut c_void,
            &mut factor_real_sign_pointer as *mut u64 as *mut c_void,
            &mut factor_real_limbs_pointer as *mut u64 as *mut c_void,
            &mut factor_imaginary_sign_pointer as *mut u64 as *mut c_void,
            &mut factor_imaginary_limbs_pointer as *mut u64 as *mut c_void,
            &mut factor_count_wire as *mut u32 as *mut c_void,
            &mut factor_limb_count_wire as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuModuleGetFunction(
                    &mut adjoint,
                    self.card.module,
                    c"return_membrane_sparse_relational_adjoint".as_ptr(),
                )
            },
            "cuModuleGetFunction(return_membrane_sparse_relational_adjoint)",
        )?;
        let mut row_offsets_pointer = atlas.row_offsets.pointer;
        let mut term_rows_pointer = atlas.term_rows.pointer;
        let mut term_factors_pointer = atlas.term_factors.pointer;
        let mut ingress_pointer = atlas.term_ingress_population.pointer;
        let mut emanation_pointer = atlas.term_emanation_population.pointer;
        let mut return_pointer = atlas.term_return_population.pointer;
        let mut dense_current_pointer = dense_current_device.pointer;
        let mut family_orientation_pointer = self.family_orientation.pointer;
        let mut family_real_sign_pointer = self.family_real_sign.pointer;
        let mut family_imaginary_sign_pointer = self.family_imaginary_sign.pointer;
        let mut row_family_real_pointer = row_family_real.pointer;
        let mut row_family_imaginary_pointer = row_family_imaginary.pointer;
        let mut factor_real_pointer = factor_real.pointer;
        let mut factor_imaginary_pointer = factor_imaginary.pointer;
        let mut row_population = atlas.row_population;
        let mut factor_population = self.factors;
        let mut family_population = self.families;
        let mut term_population = atlas.term_population;
        let mut forward_arguments: [*mut c_void; 12] = [
            &mut row_offsets_pointer as *mut u64 as *mut c_void,
            &mut term_factors_pointer as *mut u64 as *mut c_void,
            &mut ingress_pointer as *mut u64 as *mut c_void,
            &mut emanation_pointer as *mut u64 as *mut c_void,
            &mut return_pointer as *mut u64 as *mut c_void,
            &mut dense_current_pointer as *mut u64 as *mut c_void,
            &mut family_orientation_pointer as *mut u64 as *mut c_void,
            &mut row_family_real_pointer as *mut u64 as *mut c_void,
            &mut row_family_imaginary_pointer as *mut u64 as *mut c_void,
            &mut row_population as *mut u32 as *mut c_void,
            &mut factor_population as *mut u32 as *mut c_void,
            &mut family_population as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    forward,
                    self.card.grid_for(row_family_population)?,
                    1,
                    1,
                    self.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    forward_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(conduct_membrane_sparse_relational_forward)",
        )?;
        let mut adjoint_arguments: [*mut c_void; 13] = [
            &mut term_rows_pointer as *mut u64 as *mut c_void,
            &mut term_factors_pointer as *mut u64 as *mut c_void,
            &mut ingress_pointer as *mut u64 as *mut c_void,
            &mut emanation_pointer as *mut u64 as *mut c_void,
            &mut return_pointer as *mut u64 as *mut c_void,
            &mut row_family_real_pointer as *mut u64 as *mut c_void,
            &mut row_family_imaginary_pointer as *mut u64 as *mut c_void,
            &mut family_real_sign_pointer as *mut u64 as *mut c_void,
            &mut family_imaginary_sign_pointer as *mut u64 as *mut c_void,
            &mut factor_real_pointer as *mut u64 as *mut c_void,
            &mut factor_imaginary_pointer as *mut u64 as *mut c_void,
            &mut term_population as *mut u64 as *mut c_void,
            &mut family_population as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    adjoint,
                    self.card.grid_for(term_family_population)?,
                    1,
                    1,
                    self.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    adjoint_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(return_membrane_sparse_relational_adjoint)",
        )?;
        // The bootstrap adjoint still uses its admitted bounded `i64` apparatus face.  Widen only
        // after that return has populated the carrier; every later recurrence remains in limbs.
        driver(
            unsafe {
                cuLaunchKernel(
                    widen,
                    self.card.grid_for(self.factors as u64)?,
                    1,
                    1,
                    self.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    widen_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(widen_membrane_sparse_relational_i64_current)",
        )?;
        self.card.launches = self
            .card
            .launches
            .checked_add(3)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let returned_current_identity_sha256 = serde_json::to_vec(&(
            "holonic-engine.resident-sparse-relational-current.v1",
            atlas.identity_sha256.as_str(),
            atlas.constitutive_family_identity_sha256.as_str(),
            source_current_identity_sha256,
            root_state,
        ))
        .map(|bytes| {
            Sha256::digest(bytes)
                .iter()
                .map(|octet| format!("{octet:02x}"))
                .collect()
        })
        .map_err(|_| CudaRefineError::MembraneInteriorWordShape)?;
        let addressed_state_identity_sha256 = serde_json::to_vec(&(
            "holonic-engine.resident-sparse-relational-addressed-states.v1",
            [root_state],
        ))
        .map(|bytes| {
            Sha256::digest(bytes)
                .iter()
                .map(|octet| format!("{octet:02x}"))
                .collect::<String>()
        })
        .map_err(|_| CudaRefineError::MembraneInteriorWordShape)?;
        let successor_host_ingress_octets =
            u64::try_from(std::mem::size_of_val(dense_current.as_slice()))
                .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let resident_working_octets = u64::try_from(
            std::mem::size_of_val(dense_current.as_slice())
                .checked_add(row_family_octets.saturating_mul(2))
                .and_then(|octets| octets.checked_add(factor_octets.saturating_mul(2)))
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        )
        .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        self.sparse_relational_current = Some(ResidentSparseRelationalCurrentState {
            receipt: ResidentSparseRelationalCurrentReceipt {
                schema: "holonic-engine.resident-sparse-relational-current-receipt.v1".to_owned(),
                incidence_identity_sha256: atlas.identity_sha256.clone(),
                incidence_population: atlas.term_population,
                row_population: atlas.row_population,
                factor_population: self.factors,
                constitutive_family_population: self.families,
                constitutive_family_identity_sha256: atlas
                    .constitutive_family_identity_sha256
                    .clone(),
                causal_adjoint_identity_sha256: atlas.causal_adjoint_identity_sha256.clone(),
                source_current_identity_sha256: source_current_identity_sha256.to_owned(),
                returned_current_identity_sha256,
                addressed_state_identity_sha256,
                addressed_state_population: 1,
                present_state_population: 1,
                root_state,
                returned_factor_bound: returned_factor_bound.clone(),
                factor_limb_count,
                receiver_radical: false,
                local_balance_closes: true,
                root_positive_collapse: false,
                addressed_target_receiver_joined: false,
                device: self.card.device_name.clone(),
                context_identity: self.card.context as usize,
                launches: 3,
                device_dependency_edges: 1,
                synchronizations: 0,
                mount_host_ingress_octets: self.mount_host_ingress_octets,
                successor_host_ingress_octets,
                successor_host_egress_octets: 0,
                intermediate_host_egress_octets: 0,
                resident_invariant_octets: atlas.resident_octets,
                resident_working_octets,
                invariant_transport_reuploaded: false,
                cpu_semantic_replay_after_device: false,
            },
            state_present,
            states,
            state_count: 1,
            bounded_i64_face_valid: true,
            factor_real,
            factor_imaginary,
            factor_real_sign,
            factor_real_limbs,
            factor_imaginary_sign,
            factor_imaginary_limbs,
            factor_limb_count,
            returned_factor_bound,
        });
        Ok(())
    }

    /// Mount the complete opaque receiver face of every native factor exactly once. Receiver ids
    /// define the apparatus axes; observations remain equality carriers and are never read as
    /// magnitudes. Repeating the same mount is inert, while a different chart is refused.
    pub fn mount_factor_receiver_faces(
        &mut self,
        receiver_ids: &[u64],
        factor_receiver_observations: &[u64],
    ) -> Result<(), CudaRefineError> {
        if receiver_ids.is_empty()
            || receiver_ids.windows(2).any(|pair| pair[0] >= pair[1])
            || factor_receiver_observations.len() != self.factors as usize * receiver_ids.len()
            || receiver_ids.len() > u32::MAX as usize
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let mut identity = Sha256::new();
        identity.update(b"holonic-engine.factor-receiver-observation-chart.v1");
        identity.update(self.factors.to_le_bytes());
        for receiver in receiver_ids {
            identity.update(receiver.to_le_bytes());
        }
        for observation in factor_receiver_observations {
            identity.update(observation.to_le_bytes());
        }
        let identity = identity
            .finalize()
            .iter()
            .map(|octet| format!("{octet:02x}"))
            .collect::<String>();
        if let Some(existing) = &self.receiver_face_identity_sha256 {
            return if existing == &identity {
                Ok(())
            } else {
                Err(CudaRefineError::MembraneInteriorWordShape)
            };
        }
        driver(
            unsafe { cuCtxSetCurrent(self.card.context) },
            "cuCtxSetCurrent",
        )?;
        let receiver_count = receiver_ids.len();
        let factor_count = self.factors as usize;
        let mut receiver_classes = vec![0_u32; factor_receiver_observations.len()];
        let mut receiver_class_counts = Vec::with_capacity(receiver_count);
        for receiver in 0..receiver_count {
            let mut classes = BTreeMap::<u64, u32>::new();
            for factor in 0..factor_count {
                let at = factor * receiver_count + receiver;
                let observation = factor_receiver_observations[at];
                let next = classes.len() as u32;
                receiver_classes[at] = *classes.entry(observation).or_insert(next);
            }
            receiver_class_counts.push(classes.len() as u32);
        }
        let receiver_class_octets = std::mem::size_of_val(&receiver_classes[..])
            .checked_add(std::mem::size_of_val(&receiver_class_counts[..]))
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        self.factor_receiver_observations = Some(Buffer::of(factor_receiver_observations)?);
        self.factor_receiver_classes = Some(receiver_classes);
        self.receiver_class_counts = Some(receiver_class_counts);
        self.receiver_count = receiver_ids.len() as u32;
        self.receiver_face_identity_sha256 = Some(identity);
        self.mount_host_ingress_octets = self
            .mount_host_ingress_octets
            .checked_add(
                u64::try_from(std::mem::size_of_val(receiver_ids))
                    .ok()
                    .and_then(|left| {
                        left.checked_add(
                            u64::try_from(std::mem::size_of_val(factor_receiver_observations))
                                .ok()?
                                .checked_add(u64::try_from(receiver_class_octets).ok()?)?,
                        )
                    })
                    .ok_or(CudaRefineError::MembraneInteriorWordShape)?,
            )
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        Ok(())
    }

    /// Mount the complete native boundary restriction atlas exactly once.  Repeating the same
    /// mount is inert; a different atlas is refused because it would change the continuing body
    /// beneath an already-mounted receiver.
    pub fn mount_boundary_restriction_atlas(
        &mut self,
        atlas: &ResidentBoundaryRestrictionAtlas,
    ) -> Result<(), CudaRefineError> {
        let states = atlas.state_count as usize;
        let ports = atlas.universal_port_count as usize;
        let transition_count = atlas.transition_factor_offsets.len().saturating_sub(1);
        if states == 0
            || ports == 0
            || transition_count == 0
            || transition_count > u32::MAX as usize
            || atlas.state_port_transition.len() != states.saturating_mul(ports)
            || atlas.transition_targets.len() != transition_count
            || atlas
                .transition_targets
                .iter()
                .any(|target| *target >= atlas.state_count)
            || atlas.transition_factor_offsets.first() != Some(&0)
            || atlas.transition_factor_offsets.last().copied()
                != u64::try_from(atlas.transition_factors.len()).ok()
            || atlas.transition_factors.len() != atlas.transition_currents.len()
            || atlas.transition_currents.iter().any(BigUint::is_zero)
            || atlas.state_port_transition.iter().any(|transition| {
                *transition != u32::MAX && *transition as usize >= transition_count
            })
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        for transition in 0..transition_count {
            let begin = usize::try_from(atlas.transition_factor_offsets[transition])
                .map_err(|_| CudaRefineError::MembraneInteriorWordShape)?;
            let end = usize::try_from(atlas.transition_factor_offsets[transition + 1])
                .map_err(|_| CudaRefineError::MembraneInteriorWordShape)?;
            let factors = atlas
                .transition_factors
                .get(begin..end)
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            if begin == end
                || factors.windows(2).any(|pair| pair[0] >= pair[1])
                || factors.iter().any(|factor| *factor >= self.factors)
            {
                return Err(CudaRefineError::MembraneInteriorWordShape);
            }
        }
        let restriction_limb_count = atlas
            .transition_currents
            .iter()
            .map(|current| current.to_u32_digits().len())
            .max()
            .unwrap_or(1)
            .max(1);
        if restriction_limb_count > u32::MAX as usize {
            return Err(CudaRefineError::MembraneInteriorCurrentOutsideApparatus);
        }
        let mut transition_current_limbs = Vec::with_capacity(
            atlas
                .transition_currents
                .len()
                .checked_mul(restriction_limb_count)
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?,
        );
        for current in &atlas.transition_currents {
            let mut limbs = current.to_u32_digits();
            limbs.resize(restriction_limb_count, 0);
            transition_current_limbs.extend(limbs);
        }
        let mut identity = Sha256::new();
        identity.update(b"holonic-engine.resident-boundary-restriction-atlas.v1");
        identity.update(atlas.state_count.to_le_bytes());
        identity.update(atlas.universal_port_count.to_le_bytes());
        for transition in &atlas.state_port_transition {
            identity.update(transition.to_le_bytes());
        }
        for target in &atlas.transition_targets {
            identity.update(target.to_le_bytes());
        }
        for offset in &atlas.transition_factor_offsets {
            identity.update(offset.to_le_bytes());
        }
        for factor in &atlas.transition_factors {
            identity.update(factor.to_le_bytes());
        }
        for current in &atlas.transition_currents {
            let limbs = current.to_u32_digits();
            identity.update((limbs.len() as u64).to_le_bytes());
            for limb in limbs {
                identity.update(limb.to_le_bytes());
            }
        }
        let identity = identity
            .finalize()
            .iter()
            .map(|octet| format!("{octet:02x}"))
            .collect::<String>();
        if let Some(mounted) = &self.boundary_restriction_atlas {
            return if mounted.identity_sha256 == identity {
                Ok(())
            } else {
                Err(CudaRefineError::MembraneInteriorWordShape)
            };
        }
        let ingress = [
            std::mem::size_of_val(&atlas.state_port_transition[..]),
            std::mem::size_of_val(&atlas.transition_targets[..]),
            std::mem::size_of_val(&atlas.transition_factor_offsets[..]),
            std::mem::size_of_val(&atlas.transition_factors[..]),
            std::mem::size_of_val(&transition_current_limbs[..]),
        ]
        .into_iter()
        .try_fold(0_u64, |sum, octets| {
            sum.checked_add(u64::try_from(octets).ok()?)
        })
        .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        driver(
            unsafe { cuCtxSetCurrent(self.card.context) },
            "cuCtxSetCurrent",
        )?;
        self.boundary_restriction_atlas = Some(ResidentBoundaryRestrictionAtlasMount {
            identity_sha256: identity,
            state_count: atlas.state_count,
            universal_port_count: atlas.universal_port_count,
            transition_count: transition_count as u32,
            restriction_limb_count: restriction_limb_count as u32,
            maximal_current: atlas
                .transition_currents
                .iter()
                .max()
                .cloned()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?,
            state_port_transition: Buffer::of(&atlas.state_port_transition)?,
            transition_targets: Buffer::of(&atlas.transition_targets)?,
            transition_factor_offsets: Buffer::of(&atlas.transition_factor_offsets)?,
            transition_factors: Buffer::of(&atlas.transition_factors)?,
            transition_current_limbs: Buffer::of(&transition_current_limbs)?,
        });
        self.mount_host_ingress_octets = self
            .mount_host_ingress_octets
            .checked_add(ingress)
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        Ok(())
    }

    /// Found the query-independent receiver/history quotient through the live card, mount every
    /// q/U/receiver/fibre/separator coordinate once, and verify its naturality squares on that
    /// same context before any exterior current is admitted. The `ObservedSystem` is an apparatus
    /// view of already-rested native incidence; no prompt, source witness, or expected surface may
    /// participate.
    pub fn mount_receiver_history_compression(
        &mut self,
        system: &dyn ObservedSystem,
        generator_count: u32,
        generator_targets: &[u32],
    ) -> Result<ResidentReceiverHistoryCompressionReceipt, CudaRefineError> {
        self.mount_quadratic_action(generator_count, generator_targets)?;
        self.found_factored_receiver_history()?;
        let exact_partition = compress_on_device(system, &mut self.card)?;
        let compression = ReceiverHistoryCompression::found(system, &exact_partition)
            .map_err(|_| CudaRefineError::ReceiverHistoryCompressionMismatch)?;
        compression
            .validate()
            .map_err(|_| CudaRefineError::ReceiverHistoryCompressionMismatch)?;

        if let Some(existing) = self
            .factored_receiver_history
            .as_ref()
            .and_then(|history| history.compression.as_ref())
        {
            return if existing.exact == compression {
                Ok(existing.receipt.clone())
            } else {
                Err(CudaRefineError::ReceiverHistoryCompressionMismatch)
            };
        }

        let source_population = compression
            .source_population
            .iter()
            .map(|source| source.0)
            .collect::<Vec<_>>();
        let native_population = compression
            .native_population
            .iter()
            .map(|native| native.0)
            .collect::<Vec<_>>();
        let source_coordinates = compression
            .source_population
            .iter()
            .copied()
            .enumerate()
            .map(|(at, source)| (source, at as u64))
            .collect::<BTreeMap<_, _>>();
        let native_coordinates = compression
            .native_population
            .iter()
            .copied()
            .enumerate()
            .map(|(at, native)| (native, at as u64))
            .collect::<BTreeMap<_, _>>();
        if source_coordinates.len() != source_population.len()
            || native_coordinates.len() != native_population.len()
            || source_population.is_empty()
            || native_population.is_empty()
        {
            return Err(CudaRefineError::ReceiverHistoryCompressionMismatch);
        }

        let mut quotient_by_source = vec![u64::MAX; source_population.len()];
        for assignment in &compression.quotient {
            let source = *source_coordinates
                .get(&assignment.source)
                .ok_or(CudaRefineError::ReceiverHistoryCompressionMismatch)?
                as usize;
            let native = *native_coordinates
                .get(&assignment.native)
                .ok_or(CudaRefineError::ReceiverHistoryCompressionMismatch)?;
            if quotient_by_source[source] != u64::MAX {
                return Err(CudaRefineError::ReceiverHistoryCompressionMismatch);
            }
            quotient_by_source[source] = native;
        }
        if quotient_by_source.iter().any(|native| *native == u64::MAX) {
            return Err(CudaRefineError::ReceiverHistoryCompressionMismatch);
        }

        let mut receiver_factor_native = Vec::with_capacity(compression.receiver_factors.len());
        let mut receiver_factor_receiver = Vec::with_capacity(compression.receiver_factors.len());
        let mut receiver_factor_observation =
            Vec::with_capacity(compression.receiver_factors.len());
        for factor in &compression.receiver_factors {
            receiver_factor_native.push(
                *native_coordinates
                    .get(&factor.native)
                    .ok_or(CudaRefineError::ReceiverHistoryCompressionMismatch)?,
            );
            receiver_factor_receiver.push(factor.receiver.0);
            receiver_factor_observation.push(factor.observation.0);
        }

        let generator_population = compression.generators.len();
        let mut generator_source_offsets = Vec::with_capacity(generator_population + 1);
        let mut source_edge_from = Vec::new();
        let mut source_edge_to = Vec::new();
        let mut source_edge_generator = Vec::new();
        let mut native_generator_targets =
            vec![u64::MAX; generator_population.saturating_mul(native_population.len())];
        generator_source_offsets.push(0_u64);
        for (generator, square) in compression.generators.iter().enumerate() {
            for edge in &square.source {
                source_edge_from.push(
                    *source_coordinates
                        .get(&edge.from)
                        .ok_or(CudaRefineError::ReceiverHistoryCompressionMismatch)?,
                );
                source_edge_to.push(
                    *source_coordinates
                        .get(&edge.to)
                        .ok_or(CudaRefineError::ReceiverHistoryCompressionMismatch)?,
                );
                source_edge_generator.push(generator as u64);
            }
            generator_source_offsets.push(source_edge_from.len() as u64);
            for edge in &square.native {
                let from = *native_coordinates
                    .get(&edge.from)
                    .ok_or(CudaRefineError::ReceiverHistoryCompressionMismatch)?
                    as usize;
                let to = *native_coordinates
                    .get(&edge.to)
                    .ok_or(CudaRefineError::ReceiverHistoryCompressionMismatch)?;
                let at = generator
                    .checked_mul(native_population.len())
                    .and_then(|base| base.checked_add(from))
                    .ok_or(CudaRefineError::ReceiverHistoryCompressionMismatch)?;
                if native_generator_targets[at] != u64::MAX {
                    return Err(CudaRefineError::ReceiverHistoryCompressionMismatch);
                }
                native_generator_targets[at] = to;
            }
        }
        if generator_population == 0
            || source_edge_from.len() != source_edge_to.len()
            || source_edge_from.len() != source_edge_generator.len()
            || native_generator_targets
                .iter()
                .any(|target| *target == u64::MAX)
        {
            return Err(CudaRefineError::ReceiverHistoryCompressionMismatch);
        }

        let mut fibre_native_by_source = vec![u64::MAX; source_population.len()];
        let mut reconstruction_source_population = 0_usize;
        for fibre in &compression.reconstruction_fibres {
            let native = *native_coordinates
                .get(&fibre.native)
                .ok_or(CudaRefineError::ReceiverHistoryCompressionMismatch)?;
            for source in &fibre.sources {
                let at = *source_coordinates
                    .get(source)
                    .ok_or(CudaRefineError::ReceiverHistoryCompressionMismatch)?
                    as usize;
                if fibre_native_by_source[at] != u64::MAX {
                    return Err(CudaRefineError::ReceiverHistoryCompressionMismatch);
                }
                fibre_native_by_source[at] = native;
                reconstruction_source_population += 1;
            }
        }
        if fibre_native_by_source
            .iter()
            .any(|native| *native == u64::MAX)
        {
            return Err(CudaRefineError::ReceiverHistoryCompressionMismatch);
        }

        let mut separator_left = Vec::with_capacity(compression.first_separators.len());
        let mut separator_right = Vec::with_capacity(compression.first_separators.len());
        let mut separator_word_offsets = Vec::with_capacity(compression.first_separators.len() + 1);
        let mut separator_word = Vec::new();
        let mut separator_witness_present = Vec::with_capacity(compression.first_separators.len());
        let mut separator_witness_receiver = Vec::with_capacity(compression.first_separators.len());
        let mut separator_witness_left = Vec::with_capacity(compression.first_separators.len());
        let mut separator_witness_right = Vec::with_capacity(compression.first_separators.len());
        let mut separator_terminus = Vec::with_capacity(compression.first_separators.len());
        separator_word_offsets.push(0_u64);
        for separator in &compression.first_separators {
            separator_left.push(
                *source_coordinates
                    .get(&separator.left)
                    .ok_or(CudaRefineError::ReceiverHistoryCompressionMismatch)?,
            );
            separator_right.push(
                *source_coordinates
                    .get(&separator.right)
                    .ok_or(CudaRefineError::ReceiverHistoryCompressionMismatch)?,
            );
            separator_word.extend(separator.distinguishing_word.iter().map(|input| input.0));
            separator_word_offsets.push(separator_word.len() as u64);
            if let Some((receiver, left, right)) = separator.witness {
                separator_witness_present.push(1_u8);
                separator_witness_receiver.push(receiver.0);
                separator_witness_left.push(left.0);
                separator_witness_right.push(right.0);
            } else {
                separator_witness_present.push(0_u8);
                separator_witness_receiver.push(0);
                separator_witness_left.push(0);
                separator_witness_right.push(0);
            }
            separator_terminus.push(u8::from(separator.separated_by_terminus));
        }

        driver(
            unsafe { cuCtxSetCurrent(self.card.context) },
            "cuCtxSetCurrent",
        )?;
        let source_population_device = Buffer::of(&source_population)?;
        let native_population_device = Buffer::of(&native_population)?;
        let quotient_by_source_device = Buffer::of(&quotient_by_source)?;
        let receiver_factor_native_device = Buffer::of(&receiver_factor_native)?;
        let receiver_factor_receiver_device = Buffer::of(&receiver_factor_receiver)?;
        let receiver_factor_observation_device = Buffer::of(&receiver_factor_observation)?;
        let generator_source_offsets_device = Buffer::of(&generator_source_offsets)?;
        let source_edge_from_device = Buffer::of(&source_edge_from)?;
        let source_edge_to_device = Buffer::of(&source_edge_to)?;
        let source_edge_generator_device = Buffer::of(&source_edge_generator)?;
        let native_generator_targets_device = Buffer::of(&native_generator_targets)?;
        let fibre_native_by_source_device = Buffer::of(&fibre_native_by_source)?;
        let separator_left_device = Buffer::of(&separator_left)?;
        let separator_right_device = Buffer::of(&separator_right)?;
        let separator_word_offsets_device = Buffer::of(&separator_word_offsets)?;
        let separator_word_device = Buffer::of(&separator_word)?;
        let separator_witness_present_device = Buffer::of(&separator_witness_present)?;
        let separator_witness_receiver_device = Buffer::of(&separator_witness_receiver)?;
        let separator_witness_left_device = Buffer::of(&separator_witness_left)?;
        let separator_witness_right_device = Buffer::of(&separator_witness_right)?;
        let separator_terminus_device = Buffer::of(&separator_terminus)?;

        let obstruction = Buffer::alloc(std::mem::size_of::<u32>())?;
        obstruction.fill(0, std::mem::size_of::<u32>())?;
        let mut verify = ptr::null_mut();
        driver(
            unsafe {
                cuModuleGetFunction(
                    &mut verify,
                    self.card.module,
                    c"verify_resident_receiver_history_compression".as_ptr(),
                )
            },
            "cuModuleGetFunction(verify_resident_receiver_history_compression)",
        )?;
        let mut quotient_pointer = quotient_by_source_device.pointer;
        let mut source_population_wire = source_population.len() as u64;
        let mut source_from_pointer = source_edge_from_device.pointer;
        let mut source_to_pointer = source_edge_to_device.pointer;
        let mut source_generator_pointer = source_edge_generator_device.pointer;
        let mut source_edge_population_wire = source_edge_from.len() as u64;
        let mut native_targets_pointer = native_generator_targets_device.pointer;
        let mut native_population_wire = native_population.len() as u64;
        let mut generator_population_wire = generator_population as u64;
        let mut fibre_pointer = fibre_native_by_source_device.pointer;
        let mut obstruction_pointer = obstruction.pointer;
        let mut arguments: [*mut c_void; 11] = [
            &mut quotient_pointer as *mut u64 as *mut c_void,
            &mut source_population_wire as *mut u64 as *mut c_void,
            &mut source_from_pointer as *mut u64 as *mut c_void,
            &mut source_to_pointer as *mut u64 as *mut c_void,
            &mut source_generator_pointer as *mut u64 as *mut c_void,
            &mut source_edge_population_wire as *mut u64 as *mut c_void,
            &mut native_targets_pointer as *mut u64 as *mut c_void,
            &mut native_population_wire as *mut u64 as *mut c_void,
            &mut generator_population_wire as *mut u64 as *mut c_void,
            &mut fibre_pointer as *mut u64 as *mut c_void,
            &mut obstruction_pointer as *mut u64 as *mut c_void,
        ];
        let verification_population = source_edge_from.len().max(source_population.len());
        driver(
            unsafe {
                cuLaunchKernel(
                    verify,
                    self.card.grid_for(verification_population as u64)?,
                    1,
                    1,
                    self.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(verify_resident_receiver_history_compression)",
        )?;
        driver(
            unsafe { cuCtxSynchronize() },
            "cuCtxSynchronize(receiver-history compression)",
        )?;
        let mut obstruction_host = [0_u32; 1];
        obstruction.read(&mut obstruction_host)?;
        if obstruction_host[0] != 0 {
            return Err(CudaRefineError::ReceiverHistoryCompressionMismatch);
        }

        let resident_octets = [
            std::mem::size_of_val(source_population.as_slice()),
            std::mem::size_of_val(native_population.as_slice()),
            std::mem::size_of_val(quotient_by_source.as_slice()),
            std::mem::size_of_val(receiver_factor_native.as_slice()),
            std::mem::size_of_val(receiver_factor_receiver.as_slice()),
            std::mem::size_of_val(receiver_factor_observation.as_slice()),
            std::mem::size_of_val(generator_source_offsets.as_slice()),
            std::mem::size_of_val(source_edge_from.as_slice()),
            std::mem::size_of_val(source_edge_to.as_slice()),
            std::mem::size_of_val(source_edge_generator.as_slice()),
            std::mem::size_of_val(native_generator_targets.as_slice()),
            std::mem::size_of_val(fibre_native_by_source.as_slice()),
            std::mem::size_of_val(separator_left.as_slice()),
            std::mem::size_of_val(separator_right.as_slice()),
            std::mem::size_of_val(separator_word_offsets.as_slice()),
            std::mem::size_of_val(separator_word.as_slice()),
            std::mem::size_of_val(separator_witness_present.as_slice()),
            std::mem::size_of_val(separator_witness_receiver.as_slice()),
            std::mem::size_of_val(separator_witness_left.as_slice()),
            std::mem::size_of_val(separator_witness_right.as_slice()),
            std::mem::size_of_val(separator_terminus.as_slice()),
        ]
        .into_iter()
        .try_fold(0_u64, |sum, octets| {
            sum.checked_add(u64::try_from(octets).ok()?)
        })
        .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let compression_identity_sha256 = serde_json::to_vec(&compression)
            .map(|bytes| {
                Sha256::digest(bytes)
                    .iter()
                    .map(|octet| format!("{octet:02x}"))
                    .collect::<String>()
            })
            .map_err(|_| CudaRefineError::ReceiverHistoryCompressionMismatch)?;
        let operation_complex_identity_sha256 = self
            .factored_receiver_history
            .as_ref()
            .map(|history| history.receipt.identity_sha256.clone())
            .ok_or(CudaRefineError::ReceiverHistoryCompressionMismatch)?;
        let receipt = ResidentReceiverHistoryCompressionReceipt {
            schema: "holonic-engine.resident-receiver-history-compression.v1".to_owned(),
            compression_identity_sha256,
            operation_complex_identity_sha256,
            device: self.card.device_name.clone(),
            context_identity: self.card.context as usize,
            source_population: source_population.len(),
            native_population: native_population.len(),
            quotient_assignment_population: compression.quotient.len(),
            receiver_factor_population: compression.receiver_factors.len(),
            generator_population,
            source_transport_population: source_edge_from.len(),
            native_transport_population: native_generator_targets.len(),
            reconstruction_fibre_population: compression.reconstruction_fibres.len(),
            reconstruction_source_population,
            first_separator_population: compression.first_separators.len(),
            separator_word_population: separator_word.len(),
            device_generator_squares_commute: true,
            device_reconstruction_fibres_commute: true,
            ordered_words_exact_by_generator_induction: true,
            mounted_before_exterior_current: true,
            resident_octets,
            mount_host_ingress_octets: resident_octets,
            launches: 1,
            synchronizations: 1,
            invariant_transport_reuploaded: false,
            cpu_semantic_replay_after_device: false,
        };
        self.mount_host_ingress_octets = self
            .mount_host_ingress_octets
            .checked_add(resident_octets)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        self.factored_receiver_history
            .as_mut()
            .ok_or(CudaRefineError::ReceiverHistoryCompressionMismatch)?
            .compression = Some(ResidentReceiverHistoryCompressionMount {
            exact: compression,
            receipt: receipt.clone(),
            _source_population: source_population_device,
            _native_population: native_population_device,
            _quotient_by_source: quotient_by_source_device,
            _receiver_factor_native: receiver_factor_native_device,
            _receiver_factor_receiver: receiver_factor_receiver_device,
            _receiver_factor_observation: receiver_factor_observation_device,
            _generator_source_offsets: generator_source_offsets_device,
            _source_edge_from: source_edge_from_device,
            _source_edge_to: source_edge_to_device,
            _native_generator_targets: native_generator_targets_device,
            _fibre_native_by_source: fibre_native_by_source_device,
            _separator_left: separator_left_device,
            _separator_right: separator_right_device,
            _separator_word_offsets: separator_word_offsets_device,
            _separator_word: separator_word_device,
            _separator_witness_present: separator_witness_present_device,
            _separator_witness_receiver: separator_witness_receiver_device,
            _separator_witness_left: separator_witness_left_device,
            _separator_witness_right: separator_witness_right_device,
            _separator_terminus: separator_terminus_device,
        });
        Ok(receipt)
    }

    /// Borrow the complete query-independent q/U/fibre owner mounted beside the resident word.
    /// This is exact construction testimony, not a host recomputation or an exterior-current
    /// lookup.  Callers may use it to prove descent of a later occurrence-conditioned current.
    pub fn receiver_history_compression(&self) -> Option<&ReceiverHistoryCompression> {
        self.factored_receiver_history
            .as_ref()
            .and_then(|history| history.compression.as_ref())
            .map(|mounted| &mounted.exact)
    }
}
