//! Resident factored-moment receiver staging and address construction.

use super::*;

impl super::ResidentMembraneInteriorWord {
    /// Contract the already-mounted primitive receiver family against the admitted descended
    /// image without materializing an ambient factor square. This launch is causally downstream
    /// of the reconstruction and square-verification word through the candidate admission buffer.
    pub fn stage_resident_factored_moment_receivers(
        &mut self,
        descent_address: &ResidentFactoredMomentDescentAddress,
    ) -> Result<ResidentFactoredMomentReceiverAddress, CudaRefineError> {
        if &self.resident_factored_moment_descent_address()? != descent_address {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        driver(
            unsafe { cuCtxSetCurrent(self.card.context) },
            "cuCtxSetCurrent",
        )?;
        let (
            forms,
            factors,
            maximal_rank,
            incidence_limb_count,
            constitutive_limb_count,
            maximal_incidence,
            maximal_constitutive,
            maximal_coefficient,
            maximal_entry_population,
            coefficient_limb_count,
            frame_identity,
            mut incidence_signs,
            mut incidence_limbs,
            mut constitutive_signs,
            mut constitutive_limbs,
            mut selected_rank,
            mut admitted,
            mut form_offsets,
            mut form_rows,
            mut form_columns,
            mut form_signs,
            mut form_limbs,
            mut obstruction,
        ) = {
            let frame = self
                .observable_integral_form_frame
                .as_ref()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let transport = self
                .factored_receiver_history
                .as_ref()
                .and_then(|mount| mount.transported_image.as_ref())
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let atlas = transport
                .rank_atlas
                .as_ref()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let candidate = atlas
                .coordinates
                .as_ref()
                .and_then(|coordinate| coordinate.candidate.as_ref())
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            if candidate.receiver.is_some() || frame.form_count == 0 {
                return Err(CudaRefineError::MembraneInteriorWordShape);
            }
            (
                frame.form_count as usize,
                transport.factor_population as usize,
                candidate.image_rank_capacity as usize,
                candidate.incidence_limb_count as usize,
                candidate.constitutive_limb_count as usize,
                candidate
                    .maximal_incidence_numerator
                    .to_biguint()
                    .ok_or(CudaRefineError::MembraneInteriorWordShape)?,
                candidate
                    .maximal_constitutive_numerator
                    .to_biguint()
                    .ok_or(CudaRefineError::MembraneInteriorWordShape)?,
                frame.maximal_coefficient.clone(),
                frame.maximal_form_entry_population,
                frame.coefficient_limb_count as usize,
                frame.identity_sha256.clone(),
                candidate.incidence_signs.pointer,
                candidate.incidence_limbs.pointer,
                candidate.constitutive_signs.pointer,
                candidate.constitutive_limbs.pointer,
                atlas.selected_rank.pointer,
                candidate.admitted.pointer,
                frame.form_entry_offsets.pointer,
                frame.form_entry_rows.pointer,
                frame.form_entry_columns.pointer,
                frame.form_entry_signs.pointer,
                frame.form_entry_limbs.pointer,
                transport.overflow.pointer,
            )
        };
        if forms == 0
            || factors == 0
            || maximal_rank == 0
            || incidence_limb_count == 0
            || constitutive_limb_count == 0
            || coefficient_limb_count == 0
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let output_bound = BigUint::from(maximal_rank as u64).pow(2)
            * maximal_incidence.pow(2)
            * maximal_constitutive
            * maximal_coefficient
            * BigUint::from(maximal_entry_population);
        if output_bound.is_zero() {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let output_limb_count = output_bound.to_u32_digits().len().max(1).saturating_add(1);
        if output_limb_count > u32::MAX as usize {
            return Err(CudaRefineError::MembraneInteriorCurrentOutsideApparatus);
        }
        let output_limb_entries = forms
            .checked_mul(output_limb_count)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let output_limb_octets = output_limb_entries
            .checked_mul(std::mem::size_of::<u32>())
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let output_signs = Buffer::alloc(forms)?;
        let output_limbs = Buffer::alloc(output_limb_octets)?;
        let left_scratch = Buffer::alloc(output_limb_octets)?;
        let right_scratch = Buffer::alloc(output_limb_octets)?;
        let term_scratch = Buffer::alloc(output_limb_octets)?;
        output_signs.fill(0, forms)?;
        output_limbs.fill(0, output_limb_octets)?;

        let mut output_signs_pointer = output_signs.pointer;
        let mut output_limbs_pointer = output_limbs.pointer;
        let mut left_scratch_pointer = left_scratch.pointer;
        let mut right_scratch_pointer = right_scratch.pointer;
        let mut term_scratch_pointer = term_scratch.pointer;
        let mut forms_wire = forms as u32;
        let mut factors_wire = factors as u32;
        let mut incidence_limb_count_wire = incidence_limb_count as u32;
        let mut constitutive_limb_count_wire = constitutive_limb_count as u32;
        let mut coefficient_limb_count_wire = coefficient_limb_count as u32;
        let mut maximal_rank_wire = maximal_rank as u32;
        let mut output_limb_count_wire = output_limb_count as u32;
        let mut arguments: [*mut c_void; 24] = [
            &mut incidence_signs as *mut u64 as *mut c_void,
            &mut incidence_limbs as *mut u64 as *mut c_void,
            &mut constitutive_signs as *mut u64 as *mut c_void,
            &mut constitutive_limbs as *mut u64 as *mut c_void,
            &mut selected_rank as *mut u64 as *mut c_void,
            &mut admitted as *mut u64 as *mut c_void,
            &mut form_offsets as *mut u64 as *mut c_void,
            &mut form_rows as *mut u64 as *mut c_void,
            &mut form_columns as *mut u64 as *mut c_void,
            &mut form_signs as *mut u64 as *mut c_void,
            &mut form_limbs as *mut u64 as *mut c_void,
            &mut output_signs_pointer as *mut u64 as *mut c_void,
            &mut output_limbs_pointer as *mut u64 as *mut c_void,
            &mut left_scratch_pointer as *mut u64 as *mut c_void,
            &mut right_scratch_pointer as *mut u64 as *mut c_void,
            &mut term_scratch_pointer as *mut u64 as *mut c_void,
            &mut forms_wire as *mut u32 as *mut c_void,
            &mut factors_wire as *mut u32 as *mut c_void,
            &mut incidence_limb_count_wire as *mut u32 as *mut c_void,
            &mut constitutive_limb_count_wire as *mut u32 as *mut c_void,
            &mut coefficient_limb_count_wire as *mut u32 as *mut c_void,
            &mut maximal_rank_wire as *mut u32 as *mut c_void,
            &mut output_limb_count_wire as *mut u32 as *mut c_void,
            &mut obstruction as *mut u64 as *mut c_void,
        ];
        let grid = self.card.grid_for(forms as u64)?;
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card.membrane_factored_moment_candidate_receivers,
                    grid,
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
            "cuLaunchKernel(contract_membrane_factored_moment_candidate_receivers)",
        )?;
        self.card.launches = self
            .card
            .launches
            .checked_add(1)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let mut identity = Sha256::new();
        identity.update(b"holonic-engine.resident-factored-moment-receiver-occurrence.v1");
        identity.update(descent_address.section_lineage_identity_sha256.as_bytes());
        identity.update(frame_identity.as_bytes());
        let identity_sha256 = identity
            .finalize()
            .iter()
            .map(|octet| format!("{octet:02x}"))
            .collect::<String>();
        let resident_octets = u64::try_from(
            forms
                .checked_add(output_limb_octets.saturating_mul(4))
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        )
        .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        self.factored_receiver_history
            .as_mut()
            .and_then(|mount| mount.transported_image.as_mut())
            .and_then(|transport| transport.rank_atlas.as_mut())
            .and_then(|atlas| atlas.coordinates.as_mut())
            .and_then(|coordinate| coordinate.candidate.as_mut())
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?
            .receiver = Some(ResidentFactoredMomentReceiverState {
            identity_sha256,
            section_lineage_identity_sha256: descent_address
                .section_lineage_identity_sha256
                .clone(),
            frame_identity_sha256: frame_identity,
            receiver_population: forms_wire,
            output_limb_count: output_limb_count_wire,
            output_bound,
            output_denominator: None,
            output_signs,
            output_limbs,
            launches: 1,
            apparatus_shape_host_egress_octets: 0,
            resident_octets,
        });
        self.resident_factored_moment_receiver_address()
    }

    /// Contract one mounted addressed functional-pair receiver occurrence through the staged
    /// target image. The first launch projects every shared functional through `B`; the second
    /// consumes those projections through `H` and the complete ordered term populations.
    pub fn stage_resident_factored_moment_addressed_receivers(
        &mut self,
        descent_address: &ResidentFactoredMomentDescentAddress,
    ) -> Result<ResidentFactoredMomentReceiverAddress, CudaRefineError> {
        if &self.resident_factored_moment_descent_address()? != descent_address {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        self.stage_resident_factored_addressed_receiver_current(
            descent_address.section_lineage_identity_sha256.clone(),
            false,
        )
    }

    /// Conduct the same addressed receiver current directly through an admitted rooted spine.
    /// This is not a second inference law: it is the productive presentation already proved equal
    /// to the compact descent chart, used after that chart has become a colder checkpoint.
    pub fn stage_resident_factored_constitutive_spine_receivers(
        &mut self,
        transport_address: &ResidentFactoredMomentTransportAddress,
    ) -> Result<ResidentFactoredMomentReceiverAddress, CudaRefineError> {
        if &self.resident_factored_moment_transport_address()? != transport_address {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let mut identity = Sha256::new();
        identity.update(b"holonic-engine.rooted-constitutive-spine-section.v1");
        identity.update(transport_address.transport_identity_sha256.as_bytes());
        identity.update(transport_address.target_generation.to_le_bytes());
        let section_lineage_identity_sha256 = identity
            .finalize()
            .iter()
            .map(|octet| format!("{octet:02x}"))
            .collect::<String>();
        self.stage_resident_factored_addressed_receiver_current(
            section_lineage_identity_sha256,
            true,
        )
    }

    fn stage_resident_factored_addressed_receiver_current(
        &mut self,
        section_lineage_identity_sha256: String,
        rooted_continuation: bool,
    ) -> Result<ResidentFactoredMomentReceiverAddress, CudaRefineError> {
        let phase_trace = trace_configuration().holonics_phase_trace;
        let phase_began = std::time::Instant::now();
        driver(
            unsafe { cuCtxSetCurrent(self.card.context) },
            "cuCtxSetCurrent",
        )?;
        // The founding compact passage has one occurrence per presented generator and therefore
        // carries unit current on each block.  Later passages receive resident multiplicities
        // from the exact history quotient.  This temporary foundation face lives through every
        // asynchronous launch below and never becomes a caller-authored native width.
        let foundation_history_weights = {
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
            if source.constitutive_spine.is_none() {
                Some(Buffer::of(&vec![
                    1_u32;
                    transport.generator_population as usize
                ])?)
            } else {
                None
            }
        };
        let (
            functional_count,
            pair_count,
            receiver_count,
            term_count,
            projected_rank,
            source_rank,
            constitutive_blocks,
            history_weight_limb_count,
            maximal_history_weight,
            factors,
            incidence_limb_count,
            constitutive_limb_count,
            maximal_incidence,
            maximal_constitutive,
            output_denominator,
            maximal_functional_coefficient,
            maximal_functional_entry_population,
            maximal_receiver_term_population,
            functional_limb_count,
            term_limb_count,
            frame_identity,
            occurrence_receiver_offsets,
            occurrence_term_offsets,
            mut incidence_signs,
            mut incidence_limbs,
            mut constitutive_signs,
            mut constitutive_limbs,
            mut history_weights,
            mut admitted,
            mut functional_offsets,
            mut functional_factors,
            mut functional_signs,
            mut functional_limbs,
            mut receiver_factor_offsets,
            mut pair_left_functionals,
            mut pair_right_functionals,
            mut receiver_factor_pairs,
            mut receiver_factor_signs,
            mut receiver_factor_limbs,
            mut obstruction,
        ) = {
            let frame = self
                .addressed_factored_receiver_frame
                .as_ref()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
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
            let candidate = transport
                .rank_atlas
                .as_ref()
                .and_then(|atlas| atlas.coordinates.as_ref())
                .and_then(|coordinate| coordinate.candidate.as_ref());
            let admitted = if rooted_continuation {
                if candidate.is_some()
                    || transport.productive_receiver.is_some()
                    || source.constitutive_spine.is_none()
                {
                    return Err(CudaRefineError::MembraneInteriorWordShape);
                }
                transport.productive_admitted.pointer
            } else {
                let candidate = candidate.ok_or(CudaRefineError::MembraneInteriorWordShape)?;
                if candidate.receiver.is_some() || transport.productive_receiver.is_some() {
                    return Err(CudaRefineError::MembraneInteriorWordShape);
                }
                candidate.admitted.pointer
            };
            if frame.functional_count == 0 || frame.receiver_count == 0 || frame.term_count == 0 {
                return Err(CudaRefineError::MembraneInteriorWordShape);
            }
            let (
                projected_rank,
                source_rank,
                constitutive_blocks,
                history_weight_limb_count,
                maximal_history_weight,
                incidence_limb_count,
                constitutive_limb_count,
                maximal_incidence,
                maximal_constitutive,
                output_denominator,
                incidence_signs,
                incidence_limbs,
                constitutive_signs,
                constitutive_limbs,
                history_weights,
            ) = match (&source.constitutive_spine, &transport.constitutive_spine) {
                (Some(source_spine), Some(transported_spine)) => {
                    source_spine.validate_layout(source.factor_population)?;
                    transported_spine.validate_layout(transport.factor_population)?;
                    let presented_histories = source_spine
                        .history_population
                        .checked_mul(transport.generator_population)
                        .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
                    if transported_spine.root_rank != source_spine.root_rank
                        || transported_spine.history_population > presented_histories
                        || transport.productive_history.is_some()
                    {
                        return Err(CudaRefineError::MembraneInteriorWordShape);
                    }
                    (
                        transported_spine.effective_incidence.rows as usize,
                        source_spine.root_rank as usize,
                        transported_spine.history_population as usize,
                        transported_spine.history_weight_limb_count as usize,
                        transported_spine.maximal_history_weight.clone(),
                        transported_spine.effective_incidence.numerator_limb_count as usize,
                        source_spine.root_constitutive.numerator_limb_count as usize,
                        transported_spine
                            .effective_incidence
                            .maximal_numerator
                            .to_biguint()
                            .ok_or(CudaRefineError::MembraneInteriorWordShape)?,
                        source_spine
                            .root_constitutive
                            .maximal_numerator
                            .to_biguint()
                            .ok_or(CudaRefineError::MembraneInteriorWordShape)?,
                        source_spine.root_constitutive.common_denominator.clone(),
                        transported_spine.effective_incidence.signs.pointer,
                        transported_spine.effective_incidence.limbs.pointer,
                        source_spine.root_constitutive.numerator_signs.pointer,
                        source_spine.root_constitutive.numerator_limbs.pointer,
                        transported_spine.history_weights.pointer,
                    )
                }
                (Some(source_spine), None) if rooted_continuation => {
                    source_spine.validate_layout(source.factor_population)?;
                    let history = transport
                        .productive_history
                        .as_ref()
                        .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
                    history.validate_layout(transport.transported_row_population)?;
                    if transport.transported_row_population
                        != history
                            .root_rank
                            .checked_mul(history.history_population)
                            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?
                        || history.root_rank != source_spine.root_rank
                    {
                        return Err(CudaRefineError::MembraneInteriorWordShape);
                    }
                    (
                        transport.transported_row_population as usize,
                        source_spine.root_rank as usize,
                        history.history_population as usize,
                        history.history_weight_limb_count as usize,
                        history.maximal_history_weight.clone(),
                        transport.numerator_limb_count as usize,
                        source_spine.root_constitutive.numerator_limb_count as usize,
                        transport
                            .maximal_numerator
                            .to_biguint()
                            .ok_or(CudaRefineError::MembraneInteriorWordShape)?,
                        source_spine
                            .root_constitutive
                            .maximal_numerator
                            .to_biguint()
                            .ok_or(CudaRefineError::MembraneInteriorWordShape)?,
                        source_spine.root_constitutive.common_denominator.clone(),
                        transport.signs.pointer,
                        transport.limbs.pointer,
                        source_spine.root_constitutive.numerator_signs.pointer,
                        source_spine.root_constitutive.numerator_limbs.pointer,
                        history.history_weights.pointer,
                    )
                }
                (None, None) if !rooted_continuation => {
                    if transport.productive_history.is_some() {
                        return Err(CudaRefineError::MembraneInteriorWordShape);
                    }
                    (
                        transport.transported_row_population as usize,
                        source.image_rank as usize,
                        transport.generator_population as usize,
                        1,
                        BigUint::one(),
                        transport.numerator_limb_count as usize,
                        source.constitutive.numerator_limb_count as usize,
                        transport
                            .maximal_numerator
                            .to_biguint()
                            .ok_or(CudaRefineError::MembraneInteriorWordShape)?,
                        source
                            .constitutive
                            .maximal_numerator
                            .to_biguint()
                            .ok_or(CudaRefineError::MembraneInteriorWordShape)?,
                        source.constitutive.common_denominator.clone(),
                        transport.signs.pointer,
                        transport.limbs.pointer,
                        source.constitutive.numerator_signs.pointer,
                        source.constitutive.numerator_limbs.pointer,
                        foundation_history_weights
                            .as_ref()
                            .ok_or(CudaRefineError::MembraneInteriorWordShape)?
                            .pointer,
                    )
                }
                _ => return Err(CudaRefineError::MembraneInteriorWordShape),
            };
            (
                frame.functional_count as usize,
                frame.pair_count as usize,
                frame.receiver_count as usize,
                frame.term_count as usize,
                projected_rank,
                source_rank,
                constitutive_blocks,
                history_weight_limb_count,
                maximal_history_weight,
                transport.factor_population as usize,
                incidence_limb_count,
                constitutive_limb_count,
                maximal_incidence,
                maximal_constitutive,
                output_denominator,
                frame.maximal_functional_coefficient.clone(),
                frame.maximal_functional_entry_population,
                frame.maximal_receiver_term_population,
                frame.functional_limb_count as usize,
                frame.term_limb_count as usize,
                frame.identity_sha256.clone(),
                frame.occurrence_receiver_offsets_host.clone(),
                frame.occurrence_term_offsets_host.clone(),
                incidence_signs,
                incidence_limbs,
                constitutive_signs,
                constitutive_limbs,
                history_weights,
                admitted,
                frame.functional_offsets.pointer,
                frame.functional_factors.pointer,
                frame.functional_signs.pointer,
                frame.functional_limbs.pointer,
                frame.receiver_factor_offsets.pointer,
                frame.pair_left_functionals.pointer,
                frame.pair_right_functionals.pointer,
                frame.receiver_factor_pairs.pointer,
                frame.receiver_factor_signs.pointer,
                frame.receiver_factor_limbs.pointer,
                transport.overflow.pointer,
            )
        };
        if functional_count == 0
            || pair_count == 0
            || receiver_count == 0
            || term_count == 0
            || projected_rank == 0
            || source_rank == 0
            || constitutive_blocks == 0
            || history_weight_limb_count == 0
            || maximal_history_weight.is_zero()
            || projected_rank != source_rank.saturating_mul(constitutive_blocks)
            || factors == 0
            || incidence_limb_count == 0
            || constitutive_limb_count == 0
            || functional_limb_count == 0
            || term_limb_count == 0
            || maximal_functional_entry_population == 0
            || maximal_receiver_term_population == 0
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let occurrence_count = occurrence_receiver_offsets
            .len()
            .checked_sub(1)
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        if occurrence_count == 0
            || occurrence_term_offsets.len() != occurrence_count + 1
            || occurrence_receiver_offsets.first() != Some(&0)
            || occurrence_term_offsets.first() != Some(&0)
            || occurrence_receiver_offsets.last().copied() != Some(receiver_count as u32)
            || occurrence_term_offsets.last().copied() != Some(term_count as u64)
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        // The exact reconstruction family owns a deliberately conservative CRT capacity.  That
        // trailing-zero capacity is not continuing morphology and must not be multiplied through
        // every receiver occurrence.  The card measures the admitted used-word aperture; the
        // driver observes only this allocation shape, never a coefficient, sign, rank, pivot, or
        // receiver consequence.
        let active_constitutive_limbs = Buffer::of(&[1_u32])?;
        let mut active_constitutive_limbs_pointer = active_constitutive_limbs.pointer;
        let mut constitutive_limb_capacity_wire = constitutive_limb_count as u32;
        let mut projected_rank_wire = projected_rank as u32;
        let mut source_rank_wire = source_rank as u32;
        let mut generators_wire = constitutive_blocks as u32;
        let mut aperture_arguments: [*mut c_void; 6] = [
            &mut constitutive_limbs as *mut u64 as *mut c_void,
            &mut admitted as *mut u64 as *mut c_void,
            &mut constitutive_limb_capacity_wire as *mut u32 as *mut c_void,
            &mut source_rank_wire as *mut u32 as *mut c_void,
            &mut active_constitutive_limbs_pointer as *mut u64 as *mut c_void,
            &mut obstruction as *mut u64 as *mut c_void,
        ];
        let constitutive_entries = source_rank
            .checked_mul(source_rank)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let aperture_grid = self.card.grid_for(constitutive_entries as u64)?;
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card.membrane_factored_moment_constitutive_aperture,
                    aperture_grid,
                    1,
                    1,
                    self.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    aperture_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(measure_membrane_factored_moment_candidate_constitutive_aperture)",
        )?;
        driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
        let mut active_constitutive_limb_count = [0_u32; 1];
        active_constitutive_limbs.read(&mut active_constitutive_limb_count)?;
        let active_constitutive_limb_count = active_constitutive_limb_count[0] as usize;
        if active_constitutive_limb_count == 0
            || active_constitutive_limb_count > constitutive_limb_count
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        // The synchronization above is the causal boundary at which every finite-chart cell has
        // already returned into `admitted` and `chart_witnesses`.  The chart-major source
        // projections are proof work fibres, not native rest. Release them before the receiver
        // current allocates its pullback chart; retaining them would turn reconstruction capacity
        // into an accidental hardware governor.
        if !rooted_continuation {
            let candidate = self
                .factored_receiver_history
                .as_mut()
                .and_then(|mount| mount.transported_image.as_mut())
                .and_then(|transport| transport.rank_atlas.as_mut())
                .and_then(|atlas| atlas.coordinates.as_mut())
                .and_then(|coordinate| coordinate.candidate.as_mut())
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let transported_fibre = candidate
                .square_transported_residues
                .take()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let constitutive_fibre = candidate
                .square_constitutive_residues
                .take()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            drop((transported_fibre, constitutive_fibre));
        }
        let projected_bound = BigUint::from(maximal_functional_entry_population)
            * maximal_incidence
            * maximal_functional_coefficient;
        if projected_bound.is_zero() {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let projected_limb_count = projected_bound
            .to_u32_digits()
            .len()
            .max(1)
            .saturating_add(1);
        let dual_bound =
            BigUint::from(source_rank) * maximal_constitutive * projected_bound.clone();
        let dual_limb_count = dual_bound.to_u32_digits().len().max(1).saturating_add(1);
        let pair_bound = BigUint::from(projected_rank)
            * projected_bound.clone()
            * dual_bound
            * maximal_history_weight.clone();
        let pair_limb_count = pair_bound.to_u32_digits().len().max(1).saturating_add(1);
        let term_coefficient_bound = (BigUint::one()
            << term_limb_count
                .checked_mul(u32::BITS as usize)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?)
            - BigUint::one();
        let output_bound =
            BigUint::from(maximal_receiver_term_population) * pair_bound * term_coefficient_bound;
        let output_limb_count = output_bound.to_u32_digits().len().max(1).saturating_add(1);
        if projected_limb_count > u32::MAX as usize
            || dual_limb_count > u32::MAX as usize
            || pair_limb_count > u32::MAX as usize
            || output_limb_count > u32::MAX as usize
        {
            return Err(CudaRefineError::MembraneInteriorCurrentOutsideApparatus);
        }
        // Primitive functional faces are shared morphology and cross the image/constitutive legs
        // once. Addressed terms remain occurrence-local and pass through their already-mounted
        // boundary cover. This is exact bilinear factorization, not a semantic cache: removing
        // any primitive face or occurrence incidence changes the reconstructed receiver family.
        let mut maximal_window_receivers = 0_usize;
        let mut maximal_window_terms = 0_usize;
        for occurrence in 0..occurrence_count {
            let receiver_begin = occurrence_receiver_offsets[occurrence] as usize;
            let receiver_end = occurrence_receiver_offsets[occurrence + 1] as usize;
            let term_begin = usize::try_from(occurrence_term_offsets[occurrence])
                .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            let term_end = usize::try_from(occurrence_term_offsets[occurrence + 1])
                .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            if receiver_begin >= receiver_end
                || term_begin >= term_end
                || receiver_end > receiver_count
                || term_end > term_count
            {
                return Err(CudaRefineError::MembraneInteriorWordShape);
            }
            maximal_window_receivers = maximal_window_receivers.max(receiver_end - receiver_begin);
            maximal_window_terms = maximal_window_terms.max(term_end - term_begin);
        }
        let projection_population = functional_count
            .checked_mul(projected_rank)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let projection_limb_octets = projection_population
            .checked_mul(projected_limb_count)
            .and_then(|entries| entries.checked_mul(std::mem::size_of::<u32>()))
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let receiver_output_limb_octets = receiver_count
            .checked_mul(output_limb_count)
            .and_then(|entries| entries.checked_mul(std::mem::size_of::<u32>()))
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let term_output_limb_octets = maximal_window_terms
            .checked_mul(output_limb_count)
            .and_then(|entries| entries.checked_mul(std::mem::size_of::<u32>()))
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let pair_output_limb_octets = pair_count
            .checked_mul(pair_limb_count)
            .and_then(|entries| entries.checked_mul(std::mem::size_of::<u32>()))
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let projected_signs = Buffer::alloc(projection_population)?;
        let projected_limbs = Buffer::alloc(projection_limb_octets)?;
        let projected_scratch = Buffer::alloc(projection_limb_octets)?;
        projected_signs.fill(0, projection_population)?;
        projected_limbs.fill(0, projection_limb_octets)?;
        let pair_output_signs = Buffer::alloc(pair_count)?;
        let pair_output_limbs = Buffer::alloc(pair_output_limb_octets)?;
        let pair_scratch = Buffer::alloc(pair_output_limb_octets)?;
        let weighted_pair_scratch = Buffer::alloc(pair_output_limb_octets)?;
        let term_output_signs = Buffer::alloc(maximal_window_terms)?;
        let term_output_limbs = Buffer::alloc(term_output_limb_octets)?;
        let output_signs = Buffer::alloc(receiver_count)?;
        let output_limbs = Buffer::alloc(receiver_output_limb_octets)?;
        let scaled_scratch = Buffer::alloc(term_output_limb_octets)?;
        pair_output_signs.fill(0, pair_count)?;
        pair_output_limbs.fill(0, pair_output_limb_octets)?;
        term_output_signs.fill(0, maximal_window_terms)?;
        term_output_limbs.fill(0, term_output_limb_octets)?;
        output_signs.fill(0, receiver_count)?;
        output_limbs.fill(0, receiver_output_limb_octets)?;
        let dual_bytes_for = |population: usize| {
            let signs = population.checked_mul(projected_rank)?;
            let limb_base = signs.checked_add(std::mem::align_of::<u32>() - 1)?
                & !(std::mem::align_of::<u32>() - 1);
            let limbs = signs
                .checked_mul(dual_limb_count)?
                .checked_mul(std::mem::size_of::<u32>())?;
            limb_base.checked_add(limbs.checked_mul(2)?)
        };
        let (dual_functional_aperture, dual_aperture) =
            Buffer::widest_repeated_aperture(functional_count, dual_bytes_for)?;
        let dual_sign_octets = dual_functional_aperture
            .checked_mul(projected_rank)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let dual_limb_base = dual_sign_octets
            .checked_add(std::mem::align_of::<u32>() - 1)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?
            & !(std::mem::align_of::<u32>() - 1);
        let dual_limb_octets = dual_sign_octets
            .checked_mul(dual_limb_count)
            .and_then(|entries| entries.checked_mul(std::mem::size_of::<u32>()))
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let dual_aperture_octets = dual_limb_base
            .checked_add(dual_limb_octets.saturating_mul(2))
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let dual_front_count = functional_count.div_ceil(dual_functional_aperture);
        if phase_trace {
            eprintln!(
                "mem6-image receiver-quotient {:?} occurrences={} receivers={} primitive_functionals={} primitive_pairs={} receiver_factors={} maximal_window_receivers={} maximal_window_factors={} productive_rank={} root_rank={} history_blocks={} active_constitutive_limbs={} projected_limbs={} dual_limbs={} pair_limbs={} output_limbs={} dual_functional_aperture={} dual_fronts={} resident_work_octets={}",
                phase_began.elapsed(),
                occurrence_count,
                receiver_count,
                functional_count,
                pair_count,
                term_count,
                maximal_window_receivers,
                maximal_window_terms,
                projected_rank,
                source_rank,
                constitutive_blocks,
                active_constitutive_limb_count,
                projected_limb_count,
                dual_limb_count,
                pair_limb_count,
                output_limb_count,
                dual_functional_aperture,
                dual_front_count,
                projection_limb_octets
                    .saturating_mul(2)
                    .saturating_add(pair_count)
                    .saturating_add(pair_output_limb_octets.saturating_mul(2))
                    .saturating_add(dual_aperture_octets)
                    .saturating_add(term_output_limb_octets.saturating_mul(2)),
            );
        }

        let mut projected_signs_pointer = projected_signs.pointer;
        let mut projected_limbs_pointer = projected_limbs.pointer;
        let mut projected_scratch_pointer = projected_scratch.pointer;
        let mut factors_wire = factors as u32;
        let mut incidence_limb_count_wire = incidence_limb_count as u32;
        let mut constitutive_limb_count_wire = constitutive_limb_count as u32;
        let mut functional_limb_count_wire = functional_limb_count as u32;
        let mut term_limb_count_wire = term_limb_count as u32;
        let mut projected_limb_count_wire = projected_limb_count as u32;
        let mut dual_limb_count_wire = dual_limb_count as u32;
        let mut pair_limb_count_wire = pair_limb_count as u32;
        let mut active_constitutive_limb_count_wire = active_constitutive_limb_count as u32;
        let mut output_limb_count_wire = output_limb_count as u32;
        let mut dual_signs_pointer = dual_aperture.pointer;
        let mut dual_limbs_pointer = dual_aperture.pointer + dual_limb_base as u64;
        let mut dual_scratch_pointer = dual_limbs_pointer + dual_limb_octets as u64;
        let mut pair_output_signs_pointer = pair_output_signs.pointer;
        let mut pair_output_limbs_pointer = pair_output_limbs.pointer;
        let mut pair_scratch_pointer = pair_scratch.pointer;
        let mut weighted_pair_scratch_pointer = weighted_pair_scratch.pointer;
        let mut history_weight_limb_count_wire = history_weight_limb_count as u32;
        let mut term_output_signs_pointer = term_output_signs.pointer;
        let mut term_output_limbs_pointer = term_output_limbs.pointer;
        let mut scaled_scratch_pointer = scaled_scratch.pointer;
        let mut output_signs_pointer = output_signs.pointer;
        let mut output_limbs_pointer = output_limbs.pointer;
        let mut functional_count_wire = u32::try_from(functional_count)
            .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let mut pair_count_wire = u32::try_from(pair_count)
            .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let mut functional_base_wire = 0_u32;
        let mut projection_arguments: [*mut c_void; 18] = [
            &mut incidence_signs as *mut u64 as *mut c_void,
            &mut incidence_limbs as *mut u64 as *mut c_void,
            &mut admitted as *mut u64 as *mut c_void,
            &mut functional_offsets as *mut u64 as *mut c_void,
            &mut functional_factors as *mut u64 as *mut c_void,
            &mut functional_signs as *mut u64 as *mut c_void,
            &mut functional_limbs as *mut u64 as *mut c_void,
            &mut projected_signs_pointer as *mut u64 as *mut c_void,
            &mut projected_limbs_pointer as *mut u64 as *mut c_void,
            &mut projected_scratch_pointer as *mut u64 as *mut c_void,
            &mut functional_count_wire as *mut u32 as *mut c_void,
            &mut factors_wire as *mut u32 as *mut c_void,
            &mut incidence_limb_count_wire as *mut u32 as *mut c_void,
            &mut functional_limb_count_wire as *mut u32 as *mut c_void,
            &mut projected_rank_wire as *mut u32 as *mut c_void,
            &mut projected_limb_count_wire as *mut u32 as *mut c_void,
            &mut functional_base_wire as *mut u32 as *mut c_void,
            &mut obstruction as *mut u64 as *mut c_void,
        ];
        let projection_grid = self.card.grid_for(projection_population as u64)?;
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card.membrane_factored_moment_functional_projection,
                    projection_grid,
                    1,
                    1,
                    self.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    projection_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(project_membrane_factored_moment_candidate_functionals)",
        )?;
        for functional_base in (0..functional_count).step_by(dual_functional_aperture) {
            let local_functional_count =
                dual_functional_aperture.min(functional_count - functional_base);
            let mut local_functional_count_wire = u32::try_from(local_functional_count)
                .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            functional_base_wire = u32::try_from(functional_base)
                .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            let mut dual_arguments: [*mut c_void; 18] = [
                &mut projected_signs_pointer as *mut u64 as *mut c_void,
                &mut projected_limbs_pointer as *mut u64 as *mut c_void,
                &mut constitutive_signs as *mut u64 as *mut c_void,
                &mut constitutive_limbs as *mut u64 as *mut c_void,
                &mut admitted as *mut u64 as *mut c_void,
                &mut dual_signs_pointer as *mut u64 as *mut c_void,
                &mut dual_limbs_pointer as *mut u64 as *mut c_void,
                &mut dual_scratch_pointer as *mut u64 as *mut c_void,
                &mut local_functional_count_wire as *mut u32 as *mut c_void,
                &mut projected_limb_count_wire as *mut u32 as *mut c_void,
                &mut constitutive_limb_count_wire as *mut u32 as *mut c_void,
                &mut active_constitutive_limb_count_wire as *mut u32 as *mut c_void,
                &mut source_rank_wire as *mut u32 as *mut c_void,
                &mut generators_wire as *mut u32 as *mut c_void,
                &mut projected_rank_wire as *mut u32 as *mut c_void,
                &mut dual_limb_count_wire as *mut u32 as *mut c_void,
                &mut functional_base_wire as *mut u32 as *mut c_void,
                &mut obstruction as *mut u64 as *mut c_void,
            ];
            let dual_grid = self.card.grid_for(
                local_functional_count
                    .checked_mul(projected_rank)
                    .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?
                    as u64,
            )?;
            driver(
                unsafe {
                    cuLaunchKernel(
                        self.card.membrane_factored_moment_functional_dualization,
                        dual_grid,
                        1,
                        1,
                        self.card.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        dual_arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(dualize_membrane_factored_moment_candidate_functionals)",
            )?;
            let mut pair_arguments: [*mut c_void; 23] = [
                &mut projected_signs_pointer as *mut u64 as *mut c_void,
                &mut projected_limbs_pointer as *mut u64 as *mut c_void,
                &mut dual_signs_pointer as *mut u64 as *mut c_void,
                &mut dual_limbs_pointer as *mut u64 as *mut c_void,
                &mut admitted as *mut u64 as *mut c_void,
                &mut pair_left_functionals as *mut u64 as *mut c_void,
                &mut pair_right_functionals as *mut u64 as *mut c_void,
                &mut pair_output_signs_pointer as *mut u64 as *mut c_void,
                &mut pair_output_limbs_pointer as *mut u64 as *mut c_void,
                &mut pair_scratch_pointer as *mut u64 as *mut c_void,
                &mut weighted_pair_scratch_pointer as *mut u64 as *mut c_void,
                &mut history_weights as *mut u64 as *mut c_void,
                &mut pair_count_wire as *mut u32 as *mut c_void,
                &mut functional_count_wire as *mut u32 as *mut c_void,
                &mut projected_limb_count_wire as *mut u32 as *mut c_void,
                &mut dual_limb_count_wire as *mut u32 as *mut c_void,
                &mut projected_rank_wire as *mut u32 as *mut c_void,
                &mut source_rank_wire as *mut u32 as *mut c_void,
                &mut history_weight_limb_count_wire as *mut u32 as *mut c_void,
                &mut pair_limb_count_wire as *mut u32 as *mut c_void,
                &mut functional_base_wire as *mut u32 as *mut c_void,
                &mut local_functional_count_wire as *mut u32 as *mut c_void,
                &mut obstruction as *mut u64 as *mut c_void,
            ];
            let pair_grid = self.card.grid_for(pair_count as u64)?;
            driver(
                unsafe {
                    cuLaunchKernel(
                        self.card.membrane_factored_moment_functional_pairs,
                        pair_grid,
                        1,
                        1,
                        self.card.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        pair_arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(contract_membrane_factored_moment_candidate_functional_pairs)",
            )?;
        }
        for occurrence in 0..occurrence_count {
            let receiver_base = occurrence_receiver_offsets[occurrence];
            let term_base = occurrence_term_offsets[occurrence];
            let mut receiver_base_wire = receiver_base;
            let mut term_base_wire = term_base;
            let mut receiver_count_wire = occurrence_receiver_offsets[occurrence + 1]
                .checked_sub(receiver_base)
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let local_term_count = occurrence_term_offsets[occurrence + 1]
                .checked_sub(term_base)
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let mut term_count_wire = u32::try_from(local_term_count)
                .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            let mut factor_arguments: [*mut c_void; 16] = [
                &mut pair_output_signs_pointer as *mut u64 as *mut c_void,
                &mut pair_output_limbs_pointer as *mut u64 as *mut c_void,
                &mut admitted as *mut u64 as *mut c_void,
                &mut receiver_factor_pairs as *mut u64 as *mut c_void,
                &mut receiver_factor_signs as *mut u64 as *mut c_void,
                &mut receiver_factor_limbs as *mut u64 as *mut c_void,
                &mut term_output_signs_pointer as *mut u64 as *mut c_void,
                &mut term_output_limbs_pointer as *mut u64 as *mut c_void,
                &mut scaled_scratch_pointer as *mut u64 as *mut c_void,
                &mut term_count_wire as *mut u32 as *mut c_void,
                &mut pair_count_wire as *mut u32 as *mut c_void,
                &mut pair_limb_count_wire as *mut u32 as *mut c_void,
                &mut term_limb_count_wire as *mut u32 as *mut c_void,
                &mut output_limb_count_wire as *mut u32 as *mut c_void,
                &mut term_base_wire as *mut u64 as *mut c_void,
                &mut obstruction as *mut u64 as *mut c_void,
            ];
            let factor_grid = self.card.grid_for(local_term_count)?;
            driver(
                unsafe {
                    cuLaunchKernel(
                        self.card
                            .membrane_factored_moment_functional_receiver_factors,
                        factor_grid,
                        1,
                        1,
                        self.card.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        factor_arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(scale_membrane_factored_moment_candidate_receiver_factors)",
            )?;

            let mut reduction_arguments: [*mut c_void; 11] = [
                &mut receiver_factor_offsets as *mut u64 as *mut c_void,
                &mut term_output_signs_pointer as *mut u64 as *mut c_void,
                &mut term_output_limbs_pointer as *mut u64 as *mut c_void,
                &mut output_signs_pointer as *mut u64 as *mut c_void,
                &mut output_limbs_pointer as *mut u64 as *mut c_void,
                &mut receiver_count_wire as *mut u32 as *mut c_void,
                &mut term_count_wire as *mut u32 as *mut c_void,
                &mut output_limb_count_wire as *mut u32 as *mut c_void,
                &mut receiver_base_wire as *mut u32 as *mut c_void,
                &mut term_base_wire as *mut u64 as *mut c_void,
                &mut obstruction as *mut u64 as *mut c_void,
            ];
            let reduction_grid = self.card.grid_for(receiver_count_wire as u64)?;
            driver(
                unsafe {
                    cuLaunchKernel(
                        self.card
                            .membrane_factored_moment_functional_receiver_reduce,
                        reduction_grid,
                        1,
                        1,
                        self.card.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        reduction_arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(reduce_membrane_factored_moment_candidate_functional_receivers)",
            )?;
        }
        if phase_trace {
            driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
            eprintln!(
                "mem6-image receiver-windows-complete {:?}",
                phase_began.elapsed()
            );
        }
        let total_receiver_launches = u64::try_from(dual_front_count)
            .ok()
            .and_then(|fronts| fronts.checked_mul(2))
            .and_then(|launches| {
                u64::try_from(occurrence_count)
                    .ok()
                    .and_then(|occurrences| occurrences.checked_mul(2))
                    .and_then(|occurrence_launches| launches.checked_add(occurrence_launches))
            })
            .and_then(|launches| launches.checked_add(2))
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        self.card.launches = self
            .card
            .launches
            .checked_add(total_receiver_launches)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let mut identity = Sha256::new();
        identity
            .update(b"holonic-engine.resident-factored-moment-addressed-receiver-occurrence.v1");
        identity.update(section_lineage_identity_sha256.as_bytes());
        identity.update(frame_identity.as_bytes());
        let identity_sha256 = identity
            .finalize()
            .iter()
            .map(|octet| format!("{octet:02x}"))
            .collect::<String>();
        // Projection, dual, pair and reduction storage is an admission work fibre and falls out
        // of scope here.  The returned anatomy is only the exact receiver coordinate section.
        let resident_octets = u64::try_from(
            receiver_count
                .checked_add(receiver_output_limb_octets)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        )
        .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let receiver = ResidentFactoredMomentReceiverState {
            identity_sha256,
            section_lineage_identity_sha256,
            frame_identity_sha256: frame_identity,
            receiver_population: u32::try_from(receiver_count)
                .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
            output_limb_count: output_limb_count_wire,
            output_bound,
            output_denominator: Some(output_denominator),
            output_signs,
            output_limbs,
            launches: total_receiver_launches,
            apparatus_shape_host_egress_octets: std::mem::size_of::<u32>() as u64,
            resident_octets,
        };
        let transport = self
            .factored_receiver_history
            .as_mut()
            .and_then(|mount| mount.transported_image.as_mut())
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        if rooted_continuation {
            if transport.productive_receiver.replace(receiver).is_some() {
                return Err(CudaRefineError::MembraneInteriorWordShape);
            }
        } else {
            let candidate = transport
                .rank_atlas
                .as_mut()
                .and_then(|atlas| atlas.coordinates.as_mut())
                .and_then(|coordinate| coordinate.candidate.as_mut())
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            if candidate.receiver.replace(receiver).is_some() {
                return Err(CudaRefineError::MembraneInteriorWordShape);
            }
        }
        self.resident_factored_moment_receiver_address()
    }

    pub(super) fn resident_factored_moment_receiver_address(
        &self,
    ) -> Result<ResidentFactoredMomentReceiverAddress, CudaRefineError> {
        let mount = self
            .factored_receiver_history
            .as_ref()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let transport = mount
            .transported_image
            .as_ref()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let descended_receiver = transport
            .rank_atlas
            .as_ref()
            .and_then(|atlas| atlas.coordinates.as_ref())
            .and_then(|coordinate| coordinate.candidate.as_ref())
            .and_then(|candidate| candidate.receiver.as_ref());
        let receiver = match (descended_receiver, transport.productive_receiver.as_ref()) {
            (Some(receiver), None) | (None, Some(receiver)) => receiver,
            _ => return Err(CudaRefineError::MembraneInteriorWordShape),
        };
        if receiver.resident_octets == 0
            || receiver.output_signs.pointer == 0
            || receiver.output_limbs.pointer == 0
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        Ok(ResidentFactoredMomentReceiverAddress {
            operation_complex_identity_sha256: mount.receipt.identity_sha256.clone(),
            section_lineage_identity_sha256: receiver.section_lineage_identity_sha256.clone(),
            receiver_frame_identity_sha256: receiver.frame_identity_sha256.clone(),
            receiver_occurrence_identity_sha256: receiver.identity_sha256.clone(),
            device_context_identity: self.card.context as usize,
            source_generation: transport.source_address.generation,
            target_generation: transport.target_generation,
            factor_population: transport.factor_population,
            receiver_population: receiver.receiver_population,
        })
    }
}
