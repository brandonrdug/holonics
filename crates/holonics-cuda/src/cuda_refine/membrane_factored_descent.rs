//! Resident factored-moment descent staging and inspection.

use super::*;

impl super::ResidentMembraneInteriorWord {
    /// Reconstruct the selected minor determinant, every row-to-image joining numerator, and the
    /// pulled constitutive numerator through a complete sufficient family of finite charts. The
    /// chart family is derived from the resident entry and constitutive bounds. Bad charts are
    /// retained as determinant-divisor testimony; the surviving product is proved large enough
    /// for centered signed reconstruction without any host observation or choice.

    /// Close both exact integer squares in every sufficient finite chart and stage the descended
    /// image as one guarded device delta. The source image is not released here; the next
    /// resident receiver passage consumes the device-owned admission boundary and completes the
    /// atomic transition without a host reconstruction or pivot.
    pub fn stage_resident_factored_moment_descent(
        &mut self,
        coordinate_address: &ResidentFactoredMomentCoordinateAddress,
    ) -> Result<ResidentFactoredMomentDescentAddress, CudaRefineError> {
        if &self.resident_factored_moment_coordinate_address()? != coordinate_address {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        driver(
            unsafe { cuCtxSetCurrent(self.card.context) },
            "cuCtxSetCurrent",
        )?;
        let (
            rows,
            factors,
            source_rank,
            generators,
            source_limb_count,
            constitutive_limb_count,
            maximal_incidence_numerator,
            source_denominator,
            source_denominator_limb_count,
            minor_bound,
            maximal_rank,
            crt_limb_count,
            charts,
            mut transported_signs,
            mut transported_limbs,
            mut constitutive_signs,
            mut constitutive_limbs,
            mut source_denominator_limbs,
            mut selected_rank,
            mut selected_rows,
            mut reconstructed_signs,
            mut reconstructed_limbs,
            mut coordinate_residues,
            mut primes,
            mut obstruction,
        ) = {
            let mount = self
                .factored_receiver_history
                .as_ref()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let source = mount
                .image
                .as_ref()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let transport = mount
                .transported_image
                .as_ref()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let atlas = transport
                .rank_atlas
                .as_ref()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let coordinate = atlas
                .coordinates
                .as_ref()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            if coordinate.candidate.is_some()
                || source.constitutive.common_denominator <= BigInt::zero()
            {
                return Err(CudaRefineError::MembraneInteriorWordShape);
            }
            (
                transport.transported_row_population as usize,
                transport.factor_population as usize,
                source.image_rank as usize,
                transport.generator_population as usize,
                transport.numerator_limb_count as usize,
                source.constitutive.numerator_limb_count as usize,
                transport.maximal_numerator.clone(),
                source.constitutive.common_denominator.clone(),
                source.constitutive.denominator_limb_count as usize,
                atlas.minor_bound.clone(),
                coordinate.maximal_rank as usize,
                coordinate.crt_limb_count as usize,
                coordinate.primes_host_testimony.len(),
                transport.signs.pointer,
                transport.limbs.pointer,
                source.constitutive.numerator_signs.pointer,
                source.constitutive.numerator_limbs.pointer,
                source.constitutive.denominator_limbs.pointer,
                atlas.selected_rank.pointer,
                atlas.selected_rows.pointer,
                coordinate.reconstructed_signs.pointer,
                coordinate.reconstructed_limbs.pointer,
                coordinate.chart_residues.pointer,
                coordinate.primes.pointer,
                transport.overflow.pointer,
            )
        };
        if rows == 0
            || factors == 0
            || source_rank == 0
            || generators == 0
            || rows != source_rank.saturating_mul(generators)
            || maximal_rank == 0
            || crt_limb_count == 0
            || charts == 0
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let denominator_bound = source_denominator
            .to_biguint()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?
            * minor_bound.pow(2);
        let denominator_limb_count = denominator_bound.to_u32_digits().len().max(1);
        if denominator_limb_count > u32::MAX as usize {
            return Err(CudaRefineError::MembraneInteriorCurrentOutsideApparatus);
        }
        let incidence_entries = maximal_rank
            .checked_mul(factors)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let constitutive_entries = maximal_rank
            .checked_mul(maximal_rank)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let word_octets = |entries: usize| {
            entries
                .checked_mul(std::mem::size_of::<u32>())
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)
        };
        let incidence_limb_entries = incidence_entries
            .checked_mul(source_limb_count)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let constitutive_limb_entries = constitutive_entries
            .checked_mul(crt_limb_count)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let incidence_signs = Buffer::alloc(incidence_entries)?;
        let incidence_limbs = Buffer::alloc(word_octets(incidence_limb_entries)?)?;
        let incidence_denominator_limbs = Buffer::of(&[1_u32])?;
        let target_constitutive_signs_buffer = Buffer::alloc(constitutive_entries)?;
        let target_constitutive_limbs = Buffer::alloc(word_octets(constitutive_limb_entries)?)?;
        let denominator_limbs = Buffer::alloc(word_octets(denominator_limb_count)?)?;
        let denominator_scratch = Buffer::alloc(word_octets(denominator_limb_count)?)?;
        let transported_residue_entries = charts
            .checked_mul(rows)
            .and_then(|entries| entries.checked_mul(factors))
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let source_constitutive_residue_entries = charts
            .checked_mul(source_rank)
            .and_then(|entries| entries.checked_mul(source_rank))
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let square_transported_residues = Buffer::alloc(word_octets(transported_residue_entries)?)?;
        let square_constitutive_residues =
            Buffer::alloc(word_octets(source_constitutive_residue_entries)?)?;
        let chart_witnesses = Buffer::alloc(charts)?;
        let admitted = Buffer::of(&[0_u32])?;
        incidence_signs.fill(0, incidence_entries)?;
        incidence_limbs.fill(0, word_octets(incidence_limb_entries)?)?;
        target_constitutive_signs_buffer.fill(0, constitutive_entries)?;
        target_constitutive_limbs.fill(0, word_octets(constitutive_limb_entries)?)?;
        denominator_limbs.fill(0, word_octets(denominator_limb_count)?)?;
        denominator_scratch.fill(0, word_octets(denominator_limb_count)?)?;
        chart_witnesses.fill(1, charts)?;

        let mut square_transported_residues_pointer = square_transported_residues.pointer;
        let mut square_constitutive_residues_pointer = square_constitutive_residues.pointer;
        let mut chart_witnesses_pointer = chart_witnesses.pointer;
        let mut rows_wire = rows as u32;
        let mut factors_wire = factors as u32;
        let mut source_rank_wire = source_rank as u32;
        let mut generators_wire = generators as u32;
        let mut source_limb_count_wire = source_limb_count as u32;
        let mut constitutive_limb_count_wire = constitutive_limb_count as u32;
        let mut maximal_rank_wire = maximal_rank as u32;
        let mut crt_limb_count_wire = crt_limb_count as u32;
        let mut charts_wire = charts as u32;
        let mut source_residue_arguments: [*mut c_void; 14] = [
            &mut transported_signs as *mut u64 as *mut c_void,
            &mut transported_limbs as *mut u64 as *mut c_void,
            &mut constitutive_signs as *mut u64 as *mut c_void,
            &mut constitutive_limbs as *mut u64 as *mut c_void,
            &mut primes as *mut u64 as *mut c_void,
            &mut square_transported_residues_pointer as *mut u64 as *mut c_void,
            &mut square_constitutive_residues_pointer as *mut u64 as *mut c_void,
            &mut rows_wire as *mut u32 as *mut c_void,
            &mut factors_wire as *mut u32 as *mut c_void,
            &mut source_rank_wire as *mut u32 as *mut c_void,
            &mut source_limb_count_wire as *mut u32 as *mut c_void,
            &mut constitutive_limb_count_wire as *mut u32 as *mut c_void,
            &mut charts_wire as *mut u32 as *mut c_void,
            &mut obstruction as *mut u64 as *mut c_void,
        ];
        let source_residue_occurrences = charts
            .checked_mul(
                rows.checked_mul(factors)
                    .and_then(|held| held.checked_add(source_rank.saturating_mul(source_rank)))
                    .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
            )
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let source_residue_grid = self.card.grid_for(source_residue_occurrences as u64)?;
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card.membrane_factored_moment_square_source_projection,
                    source_residue_grid,
                    1,
                    1,
                    self.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    source_residue_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(project_membrane_factored_moment_square_source_residues)",
        )?;

        let mut verify_arguments: [*mut c_void; 14] = [
            &mut coordinate_residues as *mut u64 as *mut c_void,
            &mut square_transported_residues_pointer as *mut u64 as *mut c_void,
            &mut square_constitutive_residues_pointer as *mut u64 as *mut c_void,
            &mut selected_rank as *mut u64 as *mut c_void,
            &mut selected_rows as *mut u64 as *mut c_void,
            &mut primes as *mut u64 as *mut c_void,
            &mut chart_witnesses_pointer as *mut u64 as *mut c_void,
            &mut rows_wire as *mut u32 as *mut c_void,
            &mut factors_wire as *mut u32 as *mut c_void,
            &mut source_rank_wire as *mut u32 as *mut c_void,
            &mut generators_wire as *mut u32 as *mut c_void,
            &mut maximal_rank_wire as *mut u32 as *mut c_void,
            &mut charts_wire as *mut u32 as *mut c_void,
            &mut obstruction as *mut u64 as *mut c_void,
        ];
        let square_cells_per_chart = rows
            .checked_mul(factors)
            .and_then(|held| held.checked_add(maximal_rank.saturating_mul(maximal_rank)))
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let square_occurrences = charts
            .checked_mul(square_cells_per_chart)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let chart_grid = self.card.grid_for(square_occurrences as u64)?;
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card.membrane_factored_moment_square_verify,
                    chart_grid,
                    1,
                    1,
                    self.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    verify_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(verify_membrane_factored_moment_reconstruction_squares)",
        )?;

        let mut target_incidence_signs = incidence_signs.pointer;
        let mut target_incidence_limbs = incidence_limbs.pointer;
        let mut target_constitutive_signs = target_constitutive_signs_buffer.pointer;
        let mut target_constitutive_limbs_pointer = target_constitutive_limbs.pointer;
        let mut target_denominator = denominator_limbs.pointer;
        let mut target_denominator_scratch = denominator_scratch.pointer;
        let mut admitted_pointer = admitted.pointer;
        let mut source_denominator_limb_count_wire = source_denominator_limb_count as u32;
        let mut denominator_limb_count_wire = denominator_limb_count as u32;
        let mut gather_arguments: [*mut c_void; 22] = [
            &mut transported_signs as *mut u64 as *mut c_void,
            &mut transported_limbs as *mut u64 as *mut c_void,
            &mut selected_rank as *mut u64 as *mut c_void,
            &mut selected_rows as *mut u64 as *mut c_void,
            &mut reconstructed_signs as *mut u64 as *mut c_void,
            &mut reconstructed_limbs as *mut u64 as *mut c_void,
            &mut source_denominator_limbs as *mut u64 as *mut c_void,
            &mut target_incidence_signs as *mut u64 as *mut c_void,
            &mut target_incidence_limbs as *mut u64 as *mut c_void,
            &mut target_constitutive_signs as *mut u64 as *mut c_void,
            &mut target_constitutive_limbs_pointer as *mut u64 as *mut c_void,
            &mut target_denominator as *mut u64 as *mut c_void,
            &mut target_denominator_scratch as *mut u64 as *mut c_void,
            &mut admitted_pointer as *mut u64 as *mut c_void,
            &mut rows_wire as *mut u32 as *mut c_void,
            &mut factors_wire as *mut u32 as *mut c_void,
            &mut source_limb_count_wire as *mut u32 as *mut c_void,
            &mut maximal_rank_wire as *mut u32 as *mut c_void,
            &mut crt_limb_count_wire as *mut u32 as *mut c_void,
            &mut source_denominator_limb_count_wire as *mut u32 as *mut c_void,
            &mut denominator_limb_count_wire as *mut u32 as *mut c_void,
            &mut obstruction as *mut u64 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card.membrane_factored_moment_target_gather,
                    1,
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
            "cuLaunchKernel(gather_membrane_factored_moment_target_image)",
        )?;
        self.card.launches = self
            .card
            .launches
            .checked_add(3)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        if trace_configuration().holonics_phase_trace {
            driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
            eprintln!("mem6-image exact-squares-device-complete charts={charts}");
        }

        let transport_identity = coordinate_address.transport_identity_sha256.clone();
        let mut identity = Sha256::new();
        identity.update(b"holonic-engine.resident-factored-moment-descended-image.v1");
        identity.update(
            coordinate_address
                .operation_complex_identity_sha256
                .as_bytes(),
        );
        identity.update(transport_identity.as_bytes());
        identity.update(coordinate_address.source_generation.to_le_bytes());
        identity.update(coordinate_address.target_generation.to_le_bytes());
        let section_lineage_identity_sha256 = identity
            .finalize()
            .iter()
            .map(|octet| format!("{octet:02x}"))
            .collect::<String>();
        let resident_octets = [
            incidence_entries,
            word_octets(incidence_limb_entries)?,
            std::mem::size_of::<u32>(),
            constitutive_entries,
            word_octets(constitutive_limb_entries)?,
            word_octets(denominator_limb_count)?.saturating_mul(2),
            word_octets(transported_residue_entries)?,
            word_octets(source_constitutive_residue_entries)?,
            charts,
            std::mem::size_of::<u32>(),
        ]
        .into_iter()
        .try_fold(0_u64, |sum, octets| {
            sum.checked_add(u64::try_from(octets).ok()?)
        })
        .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        self.factored_receiver_history
            .as_mut()
            .and_then(|mount| mount.transported_image.as_mut())
            .and_then(|transport| transport.rank_atlas.as_mut())
            .and_then(|atlas| atlas.coordinates.as_mut())
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?
            .candidate = Some(ResidentFactoredMomentCandidate {
            section_lineage_identity_sha256,
            target_generation: coordinate_address.target_generation,
            image_rank_capacity: maximal_rank_wire,
            incidence_limb_count: source_limb_count_wire,
            constitutive_limb_count: crt_limb_count_wire,
            denominator_limb_count: denominator_limb_count_wire,
            maximal_incidence_numerator,
            maximal_constitutive_numerator: BigInt::from(
                self.factored_receiver_history
                    .as_ref()
                    .and_then(|mount| mount.transported_image.as_ref())
                    .and_then(|transport| transport.rank_atlas.as_ref())
                    .and_then(|atlas| atlas.coordinates.as_ref())
                    .map(|coordinate| coordinate.absolute_bound.clone())
                    .ok_or(CudaRefineError::MembraneInteriorWordShape)?,
            ),
            denominator_bound,
            incidence_signs,
            incidence_limbs,
            incidence_denominator_limbs,
            constitutive_signs: target_constitutive_signs_buffer,
            constitutive_limbs: target_constitutive_limbs,
            denominator_limbs,
            denominator_scratch,
            square_transported_residues: Some(square_transported_residues),
            square_constitutive_residues: Some(square_constitutive_residues),
            chart_witnesses,
            admitted,
            receiver: None,
            launches: 3,
            resident_octets,
        });
        self.resident_factored_moment_descent_address()
    }

    pub(super) fn resident_factored_moment_descent_address(
        &self,
    ) -> Result<ResidentFactoredMomentDescentAddress, CudaRefineError> {
        let mount = self
            .factored_receiver_history
            .as_ref()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let transport = mount
            .transported_image
            .as_ref()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let coordinate = transport
            .rank_atlas
            .as_ref()
            .and_then(|atlas| atlas.coordinates.as_ref())
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let candidate = coordinate
            .candidate
            .as_ref()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        if candidate.resident_octets == 0
            || candidate.incidence_signs.pointer == 0
            || candidate.incidence_limbs.pointer == 0
            || candidate.incidence_denominator_limbs.pointer == 0
            || candidate.constitutive_signs.pointer == 0
            || candidate.constitutive_limbs.pointer == 0
            || candidate.denominator_limbs.pointer == 0
            || candidate.denominator_scratch.pointer == 0
            || candidate
                .square_transported_residues
                .as_ref()
                .is_some_and(|buffer| buffer.pointer == 0)
            || candidate
                .square_constitutive_residues
                .as_ref()
                .is_some_and(|buffer| buffer.pointer == 0)
            || (candidate.receiver.is_none()
                && (candidate.square_transported_residues.is_none()
                    || candidate.square_constitutive_residues.is_none()))
            || candidate.chart_witnesses.pointer == 0
            || candidate.admitted.pointer == 0
            || candidate.denominator_bound.is_zero()
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        Ok(ResidentFactoredMomentDescentAddress {
            operation_complex_identity_sha256: mount.receipt.identity_sha256.clone(),
            transport_identity_sha256: transport.transport_identity_sha256.clone(),
            section_lineage_identity_sha256: candidate.section_lineage_identity_sha256.clone(),
            device_context_identity: self.card.context as usize,
            source_generation: transport.source_address.generation,
            target_generation: transport.target_generation,
            factor_population: transport.factor_population,
            image_rank_capacity: candidate.image_rank_capacity,
            chart_population: coordinate.primes_host_testimony.len() as u32,
        })
    }

    /// Decode the already-admitted staged delta for the bounded R4Q2C gate. Production R4Q2D
    /// contracts the candidate through its device admission word and returns only once, so this
    /// observer is absent from the continuing circulation.
    pub fn inspect_resident_factored_moment_descent(
        &mut self,
        address: &ResidentFactoredMomentDescentAddress,
    ) -> Result<ResidentFactoredMomentDescentReturn, CudaRefineError> {
        if &self.resident_factored_moment_descent_address()? != address {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
        let (
            rows,
            factors,
            maximal_rank,
            incidence_limb_count,
            constitutive_limb_count,
            denominator_limb_count,
            value_count,
            maximal_incidence_numerator,
            maximal_constitutive_numerator,
            denominator_bound,
            launches,
            chart_count,
        ) = {
            let transport = self
                .factored_receiver_history
                .as_ref()
                .and_then(|mount| mount.transported_image.as_ref())
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let coordinate = transport
                .rank_atlas
                .as_ref()
                .and_then(|atlas| atlas.coordinates.as_ref())
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let candidate = coordinate
                .candidate
                .as_ref()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            (
                transport.transported_row_population as usize,
                transport.factor_population as usize,
                candidate.image_rank_capacity as usize,
                candidate.incidence_limb_count as usize,
                candidate.constitutive_limb_count as usize,
                candidate.denominator_limb_count as usize,
                coordinate.value_count as usize,
                candidate.maximal_incidence_numerator.clone(),
                candidate.maximal_constitutive_numerator.clone(),
                candidate.denominator_bound.clone(),
                candidate.launches,
                coordinate.primes_host_testimony.len(),
            )
        };
        let mut obstruction = [0_u32; 1];
        let mut admitted = [0_u32; 1];
        let mut rank = [0_u32; 1];
        let mut basis_rows = vec![u32::MAX; maximal_rank];
        let mut basis_factors = vec![u32::MAX; maximal_rank];
        let mut chart_witnesses = vec![0_u8; chart_count];
        let mut coordinate_signs = vec![0_u8; value_count];
        let mut coordinate_limbs = vec![0_u32; value_count.saturating_mul(constitutive_limb_count)];
        let mut incidence_signs = vec![0_u8; maximal_rank.saturating_mul(factors)];
        let mut incidence_limbs = vec![
            0_u32;
            maximal_rank
                .saturating_mul(factors)
                .saturating_mul(incidence_limb_count)
        ];
        let mut target_constitutive_signs = vec![0_u8; maximal_rank.saturating_mul(maximal_rank)];
        let mut target_constitutive_limbs = vec![
            0_u32;
            maximal_rank
                .saturating_mul(maximal_rank)
                .saturating_mul(constitutive_limb_count)
        ];
        let mut denominator_limbs = vec![0_u32; denominator_limb_count];
        {
            let transport = self
                .factored_receiver_history
                .as_ref()
                .and_then(|mount| mount.transported_image.as_ref())
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let atlas = transport
                .rank_atlas
                .as_ref()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let coordinate = atlas
                .coordinates
                .as_ref()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let candidate = coordinate
                .candidate
                .as_ref()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            transport.overflow.read(&mut obstruction)?;
            candidate.admitted.read(&mut admitted)?;
            atlas.selected_rank.read(&mut rank)?;
            atlas.selected_rows.read(&mut basis_rows)?;
            atlas.selected_columns.read(&mut basis_factors)?;
            candidate.chart_witnesses.read(&mut chart_witnesses)?;
            coordinate.reconstructed_signs.read(&mut coordinate_signs)?;
            coordinate.reconstructed_limbs.read(&mut coordinate_limbs)?;
            candidate.incidence_signs.read(&mut incidence_signs)?;
            candidate.incidence_limbs.read(&mut incidence_limbs)?;
            candidate
                .constitutive_signs
                .read(&mut target_constitutive_signs)?;
            candidate
                .constitutive_limbs
                .read(&mut target_constitutive_limbs)?;
            candidate.denominator_limbs.read(&mut denominator_limbs)?;
        }
        let rank = rank[0] as usize;
        if obstruction[0] != 0
            || admitted[0] != 1
            || rank == 0
            || rank > maximal_rank
            || chart_witnesses.iter().any(|witness| *witness != 1)
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        basis_rows.truncate(rank);
        basis_factors.truncate(rank);
        if basis_rows.iter().any(|row| *row >= rows as u32)
            || basis_factors.iter().any(|factor| *factor >= factors as u32)
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let coordinate_values = coordinate_signs
            .iter()
            .enumerate()
            .map(|(value, sign)| {
                let begin = value * constitutive_limb_count;
                decode_signed_magnitude(
                    *sign,
                    &coordinate_limbs[begin..begin + constitutive_limb_count],
                )
            })
            .collect::<Result<Vec<_>, _>>()?;
        let determinant = coordinate_values[0].clone();
        if determinant.is_zero() {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let joining_map = ExactRatMatrix::new(
            (0..rows)
                .map(|row| {
                    (0..rank)
                        .map(|column| {
                            Rat::new(
                                coordinate_values[1 + row * maximal_rank + column].clone(),
                                determinant.clone(),
                            )
                        })
                        .collect::<Vec<_>>()
                })
                .collect(),
        )
        .map_err(|_| CudaRefineError::MembraneInteriorWordShape)?;
        let denominator = BigInt::from(BigUint::new(denominator_limbs.clone()));
        if denominator <= BigInt::zero()
            || denominator
                .to_biguint()
                .is_none_or(|held| held > denominator_bound)
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let incidence = ExactRatMatrix::new(
            (0..rank)
                .map(|row| {
                    (0..factors)
                        .map(|factor| {
                            let entry = row * factors + factor;
                            let begin = entry * incidence_limb_count;
                            decode_component(
                                incidence_signs[entry],
                                &incidence_limbs[begin..begin + incidence_limb_count],
                                &BigInt::one(),
                            )
                        })
                        .collect::<Result<Vec<_>, _>>()
                })
                .collect::<Result<Vec<_>, _>>()?,
        )
        .map_err(|_| CudaRefineError::MembraneInteriorWordShape)?;
        let constitutive = ExactRatMatrix::new(
            (0..rank)
                .map(|row| {
                    (0..rank)
                        .map(|column| {
                            let entry = row * rank + column;
                            let begin = entry * constitutive_limb_count;
                            decode_component(
                                target_constitutive_signs[entry],
                                &target_constitutive_limbs[begin..begin + constitutive_limb_count],
                                &denominator,
                            )
                        })
                        .collect::<Result<Vec<_>, _>>()
                })
                .collect::<Result<Vec<_>, _>>()?,
        )
        .map_err(|_| CudaRefineError::MembraneInteriorWordShape)?;
        if incidence.entries().iter().any(|entry| {
            entry.numer().abs().to_biguint().is_some_and(|held| {
                held > maximal_incidence_numerator.to_biguint().unwrap_or_default()
            })
        }) || constitutive.entries().iter().any(|entry| {
            (entry.numer() * (&denominator / entry.denom())).abs() > maximal_constitutive_numerator
        }) {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let target = FactoredMomentSection {
            schema: "holonic-engine.factored-moment-section.v2".to_owned(),
            factor_population: factors as u32,
            image_rank: rank as u32,
            basis_factors: basis_factors.clone(),
            incidence,
            constitutive,
        };
        target
            .validate_admitted()
            .map_err(|_| CudaRefineError::MembraneInteriorWordShape)?;
        let terminal_host_egress_octets = [
            std::mem::size_of_val(&obstruction),
            std::mem::size_of_val(&admitted),
            std::mem::size_of::<u32>(),
            std::mem::size_of_val(basis_rows.as_slice()),
            std::mem::size_of_val(basis_factors.as_slice()),
            std::mem::size_of_val(chart_witnesses.as_slice()),
            std::mem::size_of_val(coordinate_signs.as_slice()),
            std::mem::size_of_val(coordinate_limbs.as_slice()),
            std::mem::size_of_val(incidence_signs.as_slice()),
            std::mem::size_of_val(incidence_limbs.as_slice()),
            std::mem::size_of_val(target_constitutive_signs.as_slice()),
            std::mem::size_of_val(target_constitutive_limbs.as_slice()),
            std::mem::size_of_val(denominator_limbs.as_slice()),
        ]
        .into_iter()
        .try_fold(0_u64, |sum, octets| {
            sum.checked_add(u64::try_from(octets).ok()?)
        })
        .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        Ok(ResidentFactoredMomentDescentReturn {
            address: address.clone(),
            exact_rank: rank as u32,
            basis_rows,
            basis_factors,
            joining_map,
            target,
            chart_witnesses,
            admitted: true,
            device: self.card.device_name.clone(),
            context_identity: self.card.context as usize,
            launches,
            synchronizations: 1,
            intermediate_host_egress_octets: 0,
            terminal_host_egress_octets,
            host_rational_continuation: false,
            source_replaced_before_device_admission: false,
        })
    }
}
