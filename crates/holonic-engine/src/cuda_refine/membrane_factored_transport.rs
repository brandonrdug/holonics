use super::*;

impl ResidentMembraneInteriorWord {
    /// Stage one recurrent pair-current and contract the complete addressed receiver occurrence
    /// against it. Both launches remain on the resident CUDA stream; the host supplies no
    /// successor morphology, rank, pivot, history word, or receiver value.
    /// Whether the addressed current already owns the rooted productive presentation admitted by
    /// a prior exact compact passage.  This is a topology/ownership query, not a scheduling knob.

    /// Stage the integral incidence leg through the already-mounted plural generator front.  The
    /// returned address names resident output buffers; no synchronization or device-to-host copy
    /// occurs here, so an exact refactor kernel can consume them in the same CUDA word.
    pub fn stage_resident_factored_moment_transport(
        &mut self,
        source_address: &ResidentFactoredMomentAddress,
        generator_targets: &[u32],
        generator_count: u32,
    ) -> Result<ResidentFactoredMomentTransportAddress, CudaRefineError> {
        let trace = trace_configuration().holonics_phase_trace;
        let began = std::time::Instant::now();
        if let Err(error) = self.validate_resident_factored_moment_address(source_address) {
            if trace {
                eprintln!("mem6-image transport-address-refused: {error}");
            }
            return Err(error);
        }
        if let Err(error) = self.mount_quadratic_action(generator_count, generator_targets) {
            if trace {
                eprintln!("mem6-image transport-action-refused: {error}");
            }
            return Err(error);
        }
        if trace {
            eprintln!("mem6-image transport-action {:?}", began.elapsed());
        }
        let factors = self.factors as usize;
        let generators = generator_count as usize;
        if generators == 0
            || generator_targets.len() != generators.saturating_mul(factors)
            || generator_targets
                .iter()
                .any(|target| *target >= self.factors)
            || self
                .factored_receiver_history
                .as_ref()
                .is_some_and(|mount| mount.transported_image.is_some())
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let (
            source_rank,
            source_limb_count,
            source_maximal_numerator,
            mut source_signs,
            mut source_limbs,
            source_spine,
        ) = {
            let image = self
                .factored_receiver_history
                .as_ref()
                .and_then(|mount| mount.image.as_ref())
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            if image.compact_generation != image.generation
                || image.incidence.common_denominator != BigInt::one()
            {
                return Err(CudaRefineError::MembraneInteriorWordShape);
            }
            let source_spine = image
                .constitutive_spine
                .as_ref()
                .map(|spine| {
                    spine.validate_layout(image.factor_population)?;
                    Ok::<_, CudaRefineError>((
                        spine.root_rank,
                        spine.history_population,
                        spine.effective_incidence.numerator_limb_count as usize,
                        spine.effective_incidence.maximal_numerator.clone(),
                        spine.effective_incidence.signs.pointer,
                        spine.effective_incidence.limbs.pointer,
                        spine.history_weight_limb_count,
                        spine.maximal_history_weight.clone(),
                        spine.history_weights.pointer,
                    ))
                })
                .transpose()?;
            (
                image.image_rank as usize,
                image.incidence.numerator_limb_count as usize,
                image.incidence.maximal_numerator.clone(),
                image.incidence.numerator_signs.pointer,
                image.incidence.numerator_limbs.pointer,
                source_spine,
            )
        };
        let row_population = generators
            .checked_mul(source_rank)
            .filter(|rows| *rows <= u32::MAX as usize)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let maximal_preimage = generator_targets
            .chunks_exact(factors)
            .map(|generator| {
                let mut preimages = vec![0_usize; factors];
                for target in generator {
                    preimages[*target as usize] += 1;
                }
                preimages.into_iter().max().unwrap_or(0)
            })
            .max()
            .filter(|preimage| *preimage != 0)
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let maximal_target_numerator = &source_maximal_numerator * BigInt::from(maximal_preimage);
        let target_limb_count = maximal_target_numerator.to_u32_digits().1.len().max(1);
        if target_limb_count > u32::MAX as usize {
            return Err(CudaRefineError::MembraneInteriorCurrentOutsideApparatus);
        }
        let entry_population = row_population
            .checked_mul(factors)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let sign_octets = entry_population;
        let limb_octets = entry_population
            .checked_mul(target_limb_count)
            .and_then(|entries| entries.checked_mul(std::mem::size_of::<u32>()))
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let target_signs = Buffer::alloc(sign_octets)?;
        let target_limbs = Buffer::alloc(limb_octets)?;
        let overflow = Buffer::of(&[0_u32])?;
        let productive_admitted = Buffer::of(&[1_u32])?;
        if trace {
            eprintln!(
                "mem6-image transport-buffers {:?} rank={} factors={} limbs={} resident_octets={}",
                began.elapsed(),
                source_rank,
                factors,
                target_limb_count,
                sign_octets.saturating_add(limb_octets),
            );
        }
        let action = self
            .quadratic_action
            .as_ref()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let mut generator_pointer = action.native_generator_targets.pointer;
        let mut target_signs_pointer = target_signs.pointer;
        let mut target_limbs_pointer = target_limbs.pointer;
        let mut overflow_pointer = overflow.pointer;
        let mut source_rank_wire = source_rank as u32;
        let mut factor_count_wire = self.factors;
        let mut generator_count_wire = generator_count;
        let mut source_limb_count_wire = source_limb_count as u32;
        let mut target_limb_count_wire = target_limb_count as u32;
        let mut arguments: [*mut c_void; 11] = [
            &mut source_signs as *mut u64 as *mut c_void,
            &mut source_limbs as *mut u64 as *mut c_void,
            &mut generator_pointer as *mut u64 as *mut c_void,
            &mut target_signs_pointer as *mut u64 as *mut c_void,
            &mut target_limbs_pointer as *mut u64 as *mut c_void,
            &mut source_rank_wire as *mut u32 as *mut c_void,
            &mut factor_count_wire as *mut u32 as *mut c_void,
            &mut generator_count_wire as *mut u32 as *mut c_void,
            &mut source_limb_count_wire as *mut u32 as *mut c_void,
            &mut target_limb_count_wire as *mut u32 as *mut c_void,
            &mut overflow_pointer as *mut u64 as *mut c_void,
        ];
        let grid = self.card.grid_for(row_population as u64)?;
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card.membrane_factored_moment_incidence_transport,
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
            "cuLaunchKernel(transport_membrane_factored_moment_incidence)",
        )?;
        if trace {
            eprintln!("mem6-image transport-kernel {:?}", began.elapsed());
        }
        self.card.launches += 1;
        let constitutive_spine = if let Some((
            root_rank,
            source_history_population,
            source_spine_limb_count,
            source_spine_maximal_numerator,
            source_spine_signs,
            source_spine_limbs,
            source_history_weight_limb_count,
            source_maximal_history_weight,
            source_history_weights,
        )) = source_spine
        {
            let spine = self.transport_and_condense_resident_constitutive_spine(
                root_rank,
                source_history_population,
                source_spine_limb_count,
                source_spine_maximal_numerator,
                source_spine_signs,
                source_spine_limbs,
                source_history_weight_limb_count,
                source_maximal_history_weight,
                source_history_weights,
                generator_targets,
                generator_count,
                generator_pointer,
                overflow_pointer,
            )?;
            spine.validate_layout(self.factors)?;
            Some(spine)
        } else {
            None
        };
        let target_generation = source_address
            .generation
            .checked_add(1)
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let operation_identity = self
            .factored_receiver_history
            .as_ref()
            .map(|mount| mount.receipt.identity_sha256.clone())
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let mut identity = Sha256::new();
        identity.update(b"holonic-engine.resident-factored-moment-transport.v1");
        identity.update(operation_identity.as_bytes());
        identity.update(source_address.section_identity_sha256.as_bytes());
        identity.update(source_address.generation.to_le_bytes());
        identity.update(target_generation.to_le_bytes());
        identity.update(generator_count.to_le_bytes());
        identity.update((source_rank as u32).to_le_bytes());
        identity.update((row_population as u32).to_le_bytes());
        identity.update(self.factors.to_le_bytes());
        for target in generator_targets {
            identity.update(target.to_le_bytes());
        }
        let transport_identity_sha256 = identity
            .finalize()
            .iter()
            .map(|octet| format!("{octet:02x}"))
            .collect::<String>();
        let resident_octets = u64::try_from(
            sign_octets
                .checked_add(limb_octets)
                .and_then(|octets| octets.checked_add(2 * std::mem::size_of::<u32>()))
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        )
        .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?
        .checked_add(
            constitutive_spine
                .as_ref()
                .map(|spine| spine.effective_incidence.resident_octets)
                .unwrap_or(0),
        )
        .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        self.factored_receiver_history
            .as_mut()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?
            .transported_image = Some(ResidentTransportedFactoredMomentIncidence {
            transport_identity_sha256,
            source_address: source_address.clone(),
            target_generation,
            generator_population: generator_count,
            transported_row_population: row_population as u32,
            factor_population: self.factors,
            numerator_limb_count: target_limb_count as u32,
            maximal_numerator: maximal_target_numerator,
            signs: target_signs,
            limbs: target_limbs,
            overflow,
            productive_admitted,
            productive_receiver: None,
            constitutive_spine,
            productive_history: None,
            rank_atlas: None,
            sparse_conditioned: None,
            sparse_native_boundary: None,
            resident_octets,
            sparse_pair_completion: false,
        });
        self.resident_factored_moment_transport_address()
    }

    /// Continue an already-admitted rooted constitutive spine without forcing its current through
    /// another compact-coordinate reconstruction.  The same integral transport kernel appends
    /// the plural generator address to every history/root-coordinate row.  The retained compact
    /// chart remains a colder exact checkpoint and does not govern productive conduct.
    pub fn stage_resident_factored_constitutive_spine_transport(
        &mut self,
        source_address: &ResidentFactoredMomentAddress,
        generator_targets: &[u32],
        generator_count: u32,
    ) -> Result<ResidentFactoredMomentTransportAddress, CudaRefineError> {
        self.validate_resident_factored_moment_address(source_address)?;
        self.mount_quadratic_action(generator_count, generator_targets)?;
        if self
            .factored_receiver_history
            .as_ref()
            .is_some_and(|mount| mount.transported_image.is_some())
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let (
            root_rank,
            source_history_population,
            source_limb_count,
            source_maximal_numerator,
            source_signs,
            source_limbs,
            source_history_weight_limb_count,
            source_maximal_history_weight,
            source_history_weights,
        ) = {
            let image = self
                .factored_receiver_history
                .as_ref()
                .and_then(|mount| mount.image.as_ref())
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let spine = image
                .constitutive_spine
                .as_ref()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            spine.validate_layout(image.factor_population)?;
            (
                spine.root_rank,
                spine.history_population,
                spine.effective_incidence.numerator_limb_count as usize,
                spine.effective_incidence.maximal_numerator.clone(),
                spine.effective_incidence.signs.pointer,
                spine.effective_incidence.limbs.pointer,
                spine.history_weight_limb_count,
                spine.maximal_history_weight.clone(),
                spine.history_weights.pointer,
            )
        };
        let generator_pointer = self
            .quadratic_action
            .as_ref()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?
            .native_generator_targets
            .pointer;
        let overflow = Buffer::of(&[0_u32])?;
        let productive_admitted = Buffer::of(&[1_u32])?;
        let transported = self.transport_and_condense_resident_constitutive_spine(
            root_rank,
            source_history_population,
            source_limb_count,
            source_maximal_numerator,
            source_signs,
            source_limbs,
            source_history_weight_limb_count,
            source_maximal_history_weight,
            source_history_weights,
            generator_targets,
            generator_count,
            generator_pointer,
            overflow.pointer,
        )?;
        let target_generation = source_address
            .generation
            .checked_add(1)
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let operation_identity = self
            .factored_receiver_history
            .as_ref()
            .map(|mount| mount.receipt.identity_sha256.clone())
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let mut identity = Sha256::new();
        identity.update(b"holonic-engine.resident-factored-constitutive-spine-transport.v1");
        identity.update(operation_identity.as_bytes());
        identity.update(source_address.section_identity_sha256.as_bytes());
        identity.update(source_address.generation.to_le_bytes());
        identity.update(target_generation.to_le_bytes());
        identity.update(generator_count.to_le_bytes());
        identity.update(transported.effective_incidence.rows.to_le_bytes());
        identity.update(self.factors.to_le_bytes());
        for target in generator_targets {
            identity.update(target.to_le_bytes());
        }
        let transport_identity_sha256 = identity
            .finalize()
            .iter()
            .map(|octet| format!("{octet:02x}"))
            .collect::<String>();
        let resident_octets = transported
            .effective_incidence
            .resident_octets
            .checked_add(2 * std::mem::size_of::<u32>() as u64)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let ResidentTransportedConstitutiveSpine {
            root_rank,
            history_population,
            effective_incidence,
            history_weight_limb_count,
            maximal_history_weight,
            history_weights,
            quotient_passage,
        } = transported;
        let ResidentIntegralMatrix {
            rows,
            columns,
            numerator_limb_count,
            maximal_numerator,
            signs,
            limbs,
            ..
        } = effective_incidence;
        self.factored_receiver_history
            .as_mut()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?
            .transported_image = Some(ResidentTransportedFactoredMomentIncidence {
            transport_identity_sha256,
            source_address: source_address.clone(),
            target_generation,
            generator_population: generator_count,
            transported_row_population: rows,
            factor_population: columns,
            numerator_limb_count,
            maximal_numerator,
            signs,
            limbs,
            overflow,
            productive_admitted,
            productive_receiver: None,
            constitutive_spine: None,
            productive_history: Some(ResidentTransportedFactoredHistory {
                root_rank,
                history_population,
                history_weight_limb_count,
                maximal_history_weight,
                history_weights,
                quotient_passage,
            }),
            rank_atlas: None,
            sparse_conditioned: None,
            sparse_native_boundary: None,
            resident_octets,
            sparse_pair_completion: false,
        });
        self.resident_factored_moment_transport_address()
    }

    pub(super) fn resident_factored_moment_transport_address(
        &self,
    ) -> Result<ResidentFactoredMomentTransportAddress, CudaRefineError> {
        let mount = self
            .factored_receiver_history
            .as_ref()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let transport = mount
            .transported_image
            .as_ref()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        if transport.signs.pointer == 0
            || transport.limbs.pointer == 0
            || transport.overflow.pointer == 0
            || transport.resident_octets == 0
            || transport.maximal_numerator.is_negative()
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        Ok(ResidentFactoredMomentTransportAddress {
            operation_complex_identity_sha256: mount.receipt.identity_sha256.clone(),
            transport_identity_sha256: transport.transport_identity_sha256.clone(),
            source_section_identity_sha256: transport
                .source_address
                .section_identity_sha256
                .clone(),
            device_context_identity: self.card.context as usize,
            source_generation: transport.source_address.generation,
            target_generation: transport.target_generation,
            generator_population: transport.generator_population,
            source_image_population: transport.source_address.image_population,
            transported_row_population: transport.transported_row_population,
            factor_population: transport.factor_population,
        })
    }

    /// Found a nonzero transported-row minor in one deterministic finite chart.  This is the
    /// lower leg of the exact rank certificate, not a probabilistic rank claim: coordinate
    /// reconstruction subsequently proves `D X = J B` with `D != 0`, so the selected rows both
    /// belong to `X` and span every row of `X`.  The device retains the witness throughout; the
    /// host neither observes nor selects a rank, row, or factor.
    pub fn stage_resident_factored_moment_rank(
        &mut self,
        transport_address: &ResidentFactoredMomentTransportAddress,
    ) -> Result<ResidentFactoredMomentRankAddress, CudaRefineError> {
        if &self.resident_factored_moment_transport_address()? != transport_address {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let (rows, factors, limb_count, maximal, source_signs, source_limbs, obstruction) = {
            let transport = self
                .factored_receiver_history
                .as_ref()
                .and_then(|mount| mount.transported_image.as_ref())
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            if transport.rank_atlas.is_some() {
                return Err(CudaRefineError::MembraneInteriorWordShape);
            }
            (
                transport.transported_row_population as usize,
                transport.factor_population as usize,
                transport.numerator_limb_count as usize,
                transport
                    .maximal_numerator
                    .to_biguint()
                    .ok_or(CudaRefineError::MembraneInteriorWordShape)?,
                transport.signs.pointer,
                transport.limbs.pointer,
                transport.overflow.pointer,
            )
        };
        if rows == 0 || factors == 0 || limb_count == 0 || maximal.is_zero() {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let maximal_rank = rows.min(factors);
        let rank_wire = u32::try_from(maximal_rank)
            .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let minor_base = &maximal * BigUint::from(rank_wire);
        let minor_bound = minor_base.pow(rank_wire);
        let (primes_host_testimony, chart_product) = derive_word_prime_rank_witness()?;
        if primes_host_testimony.len() != 1 || primes_host_testimony.len() > u32::MAX as usize {
            return Err(CudaRefineError::MembraneInteriorCurrentOutsideApparatus);
        }
        let charts = primes_host_testimony.len();
        let matrix_entries = charts
            .checked_mul(rows)
            .and_then(|entries| entries.checked_mul(factors))
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let chart_rows = charts
            .checked_mul(rows)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let work = Buffer::alloc(
            matrix_entries
                .checked_mul(std::mem::size_of::<u32>())
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        )?;
        let row_addresses = Buffer::alloc(
            chart_rows
                .checked_mul(std::mem::size_of::<u32>())
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        )?;
        let ranks = Buffer::alloc(
            charts
                .checked_mul(std::mem::size_of::<u32>())
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        )?;
        let pivot_rows = Buffer::alloc(
            chart_rows
                .checked_mul(std::mem::size_of::<u32>())
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        )?;
        let pivot_columns = Buffer::alloc(
            chart_rows
                .checked_mul(std::mem::size_of::<u32>())
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        )?;
        let selected_chart = Buffer::alloc(std::mem::size_of::<u32>())?;
        let selected_rank = Buffer::alloc(std::mem::size_of::<u32>())?;
        let selected_rows = Buffer::alloc(
            rows.checked_mul(std::mem::size_of::<u32>())
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        )?;
        let selected_columns = Buffer::alloc(
            rows.checked_mul(std::mem::size_of::<u32>())
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        )?;
        let primes = Buffer::of(&primes_host_testimony)?;

        let mut source_signs_pointer = source_signs;
        let mut source_limbs_pointer = source_limbs;
        let mut primes_pointer = primes.pointer;
        let mut work_pointer = work.pointer;
        let mut row_addresses_pointer = row_addresses.pointer;
        let mut ranks_pointer = ranks.pointer;
        let mut pivot_rows_pointer = pivot_rows.pointer;
        let mut pivot_columns_pointer = pivot_columns.pointer;
        let mut row_count_wire = rows as u32;
        let mut factor_count_wire = factors as u32;
        let mut limb_count_wire = limb_count as u32;
        let mut chart_count_wire = charts as u32;
        let mut obstruction_pointer = obstruction;
        let mut rank_arguments: [*mut c_void; 13] = [
            &mut source_signs_pointer as *mut u64 as *mut c_void,
            &mut source_limbs_pointer as *mut u64 as *mut c_void,
            &mut primes_pointer as *mut u64 as *mut c_void,
            &mut work_pointer as *mut u64 as *mut c_void,
            &mut row_addresses_pointer as *mut u64 as *mut c_void,
            &mut ranks_pointer as *mut u64 as *mut c_void,
            &mut pivot_rows_pointer as *mut u64 as *mut c_void,
            &mut pivot_columns_pointer as *mut u64 as *mut c_void,
            &mut row_count_wire as *mut u32 as *mut c_void,
            &mut factor_count_wire as *mut u32 as *mut c_void,
            &mut limb_count_wire as *mut u32 as *mut c_void,
            &mut chart_count_wire as *mut u32 as *mut c_void,
            &mut obstruction_pointer as *mut u64 as *mut c_void,
        ];
        let grid = self.card.grid_for(charts as u64)?;
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card.membrane_factored_moment_modular_rank,
                    grid,
                    1,
                    1,
                    self.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    rank_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(derive_membrane_factored_moment_modular_rank)",
        )?;
        self.card.launches += 1;

        let mut selected_chart_pointer = selected_chart.pointer;
        let mut selected_rank_pointer = selected_rank.pointer;
        let mut selected_rows_pointer = selected_rows.pointer;
        let mut selected_columns_pointer = selected_columns.pointer;
        let mut select_arguments: [*mut c_void; 10] = [
            &mut ranks_pointer as *mut u64 as *mut c_void,
            &mut pivot_rows_pointer as *mut u64 as *mut c_void,
            &mut pivot_columns_pointer as *mut u64 as *mut c_void,
            &mut selected_chart_pointer as *mut u64 as *mut c_void,
            &mut selected_rank_pointer as *mut u64 as *mut c_void,
            &mut selected_rows_pointer as *mut u64 as *mut c_void,
            &mut selected_columns_pointer as *mut u64 as *mut c_void,
            &mut row_count_wire as *mut u32 as *mut c_void,
            &mut chart_count_wire as *mut u32 as *mut c_void,
            &mut obstruction_pointer as *mut u64 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card.membrane_factored_moment_modular_rank_select,
                    1,
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
            "cuLaunchKernel(select_membrane_factored_moment_modular_rank)",
        )?;
        self.card.launches += 1;
        if trace_configuration().holonics_phase_trace {
            driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
            eprintln!("mem6-image rank-device-complete charts={charts}");
        }

        let resident_octets = [
            std::mem::size_of_val(primes_host_testimony.as_slice()),
            matrix_entries.saturating_mul(std::mem::size_of::<u32>()),
            chart_rows.saturating_mul(std::mem::size_of::<u32>()) * 3,
            charts.saturating_mul(std::mem::size_of::<u32>()),
            std::mem::size_of::<u32>() * 2,
            rows.saturating_mul(std::mem::size_of::<u32>()) * 2,
        ]
        .into_iter()
        .try_fold(0_u64, |sum, octets| {
            sum.checked_add(u64::try_from(octets).ok()?)
        })
        .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        self.factored_receiver_history
            .as_mut()
            .and_then(|mount| mount.transported_image.as_mut())
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?
            .rank_atlas = Some(ResidentFactoredMomentRankAtlas {
            primes_host_testimony,
            minor_bound,
            chart_product,
            primes,
            work,
            row_addresses,
            ranks,
            pivot_rows,
            pivot_columns,
            selected_chart,
            selected_rank,
            selected_rows,
            selected_columns,
            coordinates: None,
            resident_octets,
        });
        self.resident_factored_moment_rank_address()
    }

    pub(super) fn resident_factored_moment_rank_address(
        &self,
    ) -> Result<ResidentFactoredMomentRankAddress, CudaRefineError> {
        let mount = self
            .factored_receiver_history
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
        if atlas.resident_octets == 0
            || atlas.primes.pointer == 0
            || atlas.work.pointer == 0
            || atlas.row_addresses.pointer == 0
            || atlas.ranks.pointer == 0
            || atlas.pivot_rows.pointer == 0
            || atlas.pivot_columns.pointer == 0
            || atlas.selected_chart.pointer == 0
            || atlas.selected_rank.pointer == 0
            || atlas.selected_rows.pointer == 0
            || atlas.selected_columns.pointer == 0
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        Ok(ResidentFactoredMomentRankAddress {
            operation_complex_identity_sha256: mount.receipt.identity_sha256.clone(),
            transport_identity_sha256: transport.transport_identity_sha256.clone(),
            device_context_identity: self.card.context as usize,
            source_generation: transport.source_address.generation,
            target_generation: transport.target_generation,
            transported_row_population: transport.transported_row_population,
            factor_population: transport.factor_population,
            chart_population: atlas.primes_host_testimony.len() as u32,
            minor_bound_bits: atlas.minor_bound.bits(),
            chart_product_bits: atlas.chart_product.bits(),
        })
    }
}
