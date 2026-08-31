//! Resident factored-moment transport setup and sparse quadratic receiver staging.
//!
//! These methods retain the exact resident CUDA passage while keeping transport setup in its
//! founded membrane owner.

use super::*;

impl ResidentMembraneInteriorWord {
    pub fn stage_resident_sparse_quadratic_receivers(
        &mut self,
        source_address: &ResidentFactoredMomentAddress,
    ) -> Result<ResidentFactoredMomentReceiverAddress, CudaRefineError> {
        if &self.resident_sparse_quadratic_moment_address()? != source_address {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        driver(
            unsafe { cuCtxSetCurrent(self.card.context) },
            "cuCtxSetCurrent",
        )?;
        let (
            pair_population,
            source_limb_count,
            maximal_source,
            maximal_incoming,
            generator_population,
            mut source_limbs,
            mut target_offsets,
            mut source_pairs,
            mut multiplicities,
            frame_identity,
            receiver_population,
            coefficient_limb_count,
            maximal_receiver_l1,
            mut receiver_offsets,
            mut receiver_pair_coordinates,
            mut receiver_coefficient_signs,
            mut receiver_coefficient_limbs,
        ) = {
            let mount = self
                .factored_receiver_history
                .as_ref()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            if mount.transported_image.is_some() {
                return Err(CudaRefineError::MembraneInteriorWordShape);
            }
            let source = mount
                .sparse_pair
                .as_ref()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let frame = self
                .addressed_factored_receiver_frame
                .as_ref()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let sparse_frame = frame
                .sparse_pair_receivers
                .as_ref()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            (
                source.pair_population as usize,
                source.coefficient_limb_count as usize,
                source.maximal_coefficient.clone(),
                source.maximal_incoming_multiplicity.clone(),
                source.action.generator_population,
                source.coefficients.pointer,
                source.target_offsets.pointer,
                source.source_pairs.pointer,
                source.multiplicities.pointer,
                frame.identity_sha256.clone(),
                frame.receiver_count as usize,
                sparse_frame.coefficient_limb_count as usize,
                sparse_frame.maximal_receiver_l1.clone(),
                sparse_frame.receiver_offsets.pointer,
                sparse_frame.pair_coordinates.pointer,
                sparse_frame.coefficient_signs.pointer,
                sparse_frame.coefficient_limbs.pointer,
            )
        };
        if pair_population == 0
            || source_limb_count == 0
            || generator_population == 0
            || receiver_population == 0
            || coefficient_limb_count == 0
            || maximal_incoming.is_zero()
            || maximal_receiver_l1.is_zero()
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let maximal_target = &maximal_source * &maximal_incoming;
        let target_limb_count = maximal_target.to_u32_digits().len().max(1);
        let target_entries = pair_population
            .checked_mul(target_limb_count)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let target_octets = target_entries
            .checked_mul(std::mem::size_of::<u32>())
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let target_limbs = Buffer::alloc(target_octets)?;
        target_limbs.fill(0, target_octets)?;
        let mut target_limbs_pointer = target_limbs.pointer;
        let mut pair_population_wire = pair_population as u32;
        let mut source_limb_count_wire = source_limb_count as u32;
        let mut target_limb_count_wire = target_limb_count as u32;
        let mut transport_arguments: [*mut c_void; 8] = [
            &mut target_offsets as *mut u64 as *mut c_void,
            &mut source_pairs as *mut u64 as *mut c_void,
            &mut multiplicities as *mut u64 as *mut c_void,
            &mut source_limbs as *mut u64 as *mut c_void,
            &mut target_limbs_pointer as *mut u64 as *mut c_void,
            &mut pair_population_wire as *mut u32 as *mut c_void,
            &mut source_limb_count_wire as *mut u32 as *mut c_void,
            &mut target_limb_count_wire as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card.membrane_sparse_quadratic_pair_transport,
                    self.card.grid_for(pair_population as u64)?,
                    1,
                    1,
                    self.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    transport_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(transport_membrane_sparse_quadratic_pairs)",
        )?;

        let output_bound = &maximal_target * &maximal_receiver_l1;
        let output_limb_count = output_bound.to_u32_digits().len().max(1);
        let output_entries = receiver_population
            .checked_mul(output_limb_count)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let output_octets = output_entries
            .checked_mul(std::mem::size_of::<u32>())
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let output_signs = Buffer::alloc(receiver_population)?;
        let output_limbs = Buffer::alloc(output_octets)?;
        output_signs.fill(0, receiver_population)?;
        output_limbs.fill(0, output_octets)?;
        let mut output_signs_pointer = output_signs.pointer;
        let mut output_limbs_pointer = output_limbs.pointer;
        let mut receiver_population_wire = receiver_population as u32;
        let mut coefficient_limb_count_wire = coefficient_limb_count as u32;
        let mut output_limb_count_wire = output_limb_count as u32;
        let mut receiver_arguments: [*mut c_void; 11] = [
            &mut receiver_offsets as *mut u64 as *mut c_void,
            &mut receiver_pair_coordinates as *mut u64 as *mut c_void,
            &mut receiver_coefficient_signs as *mut u64 as *mut c_void,
            &mut receiver_coefficient_limbs as *mut u64 as *mut c_void,
            &mut target_limbs_pointer as *mut u64 as *mut c_void,
            &mut output_signs_pointer as *mut u64 as *mut c_void,
            &mut output_limbs_pointer as *mut u64 as *mut c_void,
            &mut receiver_population_wire as *mut u32 as *mut c_void,
            &mut coefficient_limb_count_wire as *mut u32 as *mut c_void,
            &mut target_limb_count_wire as *mut u32 as *mut c_void,
            &mut output_limb_count_wire as *mut u32 as *mut c_void,
        ];
        let mut receiver_block_threads = self.card.block_x.max(1);
        let shared_limit = 32_usize * 1024;
        let shared_octets_for = |threads: u32| {
            let sign_octets = (threads as usize)
                .checked_add(3)
                .map(|held| held & !3_usize)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            threads
                .try_into()
                .ok()
                .and_then(|threads: usize| {
                    threads
                        .checked_mul(2)
                        .and_then(|held| held.checked_mul(output_limb_count))
                        .and_then(|held| held.checked_mul(std::mem::size_of::<u32>()))
                        .and_then(|held| held.checked_add(sign_octets))
                })
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)
        };
        while receiver_block_threads > 1
            && shared_octets_for(receiver_block_threads)? > shared_limit
        {
            receiver_block_threads = (receiver_block_threads + 1) / 2;
        }
        let receiver_shared_octets = shared_octets_for(receiver_block_threads)?;
        if receiver_shared_octets > shared_limit
            || receiver_shared_octets > u32::MAX as usize
            || receiver_population > self.card.max_grid_x as usize
        {
            return Err(CudaRefineError::MembraneInteriorCurrentOutsideApparatus);
        }
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card.membrane_sparse_quadratic_pair_receivers,
                    receiver_population as u32,
                    1,
                    1,
                    receiver_block_threads,
                    1,
                    1,
                    receiver_shared_octets as u32,
                    ptr::null_mut(),
                    receiver_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(contract_membrane_sparse_quadratic_pair_receivers)",
        )?;
        self.card.launches = self
            .card
            .launches
            .checked_add(2)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;

        let mut lineage = Sha256::new();
        lineage.update(b"holonic-engine.sparse-quadratic-pair-section.v1");
        lineage.update(source_address.section_identity_sha256.as_bytes());
        lineage.update(source_address.generation.saturating_add(1).to_le_bytes());
        let section_lineage_identity_sha256 = lineage
            .finalize()
            .iter()
            .map(|octet| format!("{octet:02x}"))
            .collect::<String>();
        let mut occurrence = Sha256::new();
        occurrence.update(b"holonic-engine.sparse-quadratic-pair-receiver.v1");
        occurrence.update(section_lineage_identity_sha256.as_bytes());
        occurrence.update(frame_identity.as_bytes());
        let identity_sha256 = occurrence
            .finalize()
            .iter()
            .map(|octet| format!("{octet:02x}"))
            .collect::<String>();
        let overflow = Buffer::of(&[0_u32])?;
        let admitted = Buffer::of(&[1_u32])?;
        let signs = Buffer::alloc(pair_population)?;
        signs.fill(0, pair_population)?;
        let receiver = ResidentFactoredMomentReceiverState {
            identity_sha256,
            section_lineage_identity_sha256,
            frame_identity_sha256: frame_identity,
            receiver_population: receiver_population as u32,
            output_limb_count: output_limb_count as u32,
            output_bound,
            output_denominator: Some(BigInt::one()),
            output_signs,
            output_limbs,
            launches: 2,
            apparatus_shape_host_egress_octets: 0,
            resident_octets: u64::try_from(
                receiver_population
                    .checked_add(output_octets.saturating_mul(2))
                    .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
            )
            .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        };
        let transport_identity_sha256 = receiver.section_lineage_identity_sha256.clone();
        let resident_octets = u64::try_from(
            target_octets
                .checked_add(pair_population)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        )
        .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        self.factored_receiver_history
            .as_mut()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?
            .transported_image = Some(ResidentTransportedFactoredMomentIncidence {
            transport_identity_sha256,
            source_address: source_address.clone(),
            target_generation: source_address.generation.saturating_add(1),
            generator_population,
            transported_row_population: pair_population as u32,
            factor_population: source_address.factor_population,
            numerator_limb_count: target_limb_count as u32,
            maximal_numerator: BigInt::from(maximal_target),
            signs,
            limbs: target_limbs,
            overflow,
            productive_admitted: admitted,
            productive_receiver: Some(receiver),
            constitutive_spine: None,
            productive_history: None,
            rank_atlas: None,
            sparse_conditioned: None,
            sparse_native_boundary: None,
            resident_octets,
            sparse_pair_completion: true,
        });
        self.resident_factored_moment_receiver_address()
    }

    pub fn validate_resident_factored_moment_address(
        &self,
        address: &ResidentFactoredMomentAddress,
    ) -> Result<(), CudaRefineError> {
        if &self.resident_factored_moment_address()? != address {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        Ok(())
    }

    pub fn resident_factored_moment_has_constitutive_spine(
        &self,
        address: &ResidentFactoredMomentAddress,
    ) -> Result<bool, CudaRefineError> {
        self.validate_resident_factored_moment_address(address)?;
        self.factored_receiver_history
            .as_ref()
            .and_then(|mount| mount.image.as_ref())
            .map(|image| image.constitutive_spine.is_some())
            .ok_or(CudaRefineError::MembraneInteriorWordShape)
    }

    /// Transport one integral incidence presentation through the already-mounted plural action.
    /// This is shared by the compact image chart and its rooted productive spine; it introduces
    /// no semantic phase and returns only the new addressed matrix occurrence.
    fn transport_resident_integral_matrix(
        &mut self,
        source_rows: usize,
        source_limb_count: usize,
        source_maximal_numerator: BigInt,
        mut source_signs: u64,
        mut source_limbs: u64,
        generator_targets: &[u32],
        generator_count: u32,
        mut generator_pointer: u64,
        mut obstruction_pointer: u64,
    ) -> Result<ResidentIntegralMatrix, CudaRefineError> {
        let factors = self.factors as usize;
        let generators = generator_count as usize;
        if source_rows == 0
            || source_limb_count == 0
            || source_maximal_numerator.is_negative()
            || generators == 0
            || generator_targets.len() != generators.saturating_mul(factors)
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let rows = source_rows
            .checked_mul(generators)
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
        let maximal_numerator = source_maximal_numerator * BigInt::from(maximal_preimage);
        let target_limb_count = maximal_numerator.to_u32_digits().1.len().max(1);
        if target_limb_count > u32::MAX as usize {
            return Err(CudaRefineError::MembraneInteriorCurrentOutsideApparatus);
        }
        let entries = rows
            .checked_mul(factors)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let sign_octets = entries;
        let limb_octets = entries
            .checked_mul(target_limb_count)
            .and_then(|held| held.checked_mul(std::mem::size_of::<u32>()))
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let signs = Buffer::alloc(sign_octets)?;
        let limbs = Buffer::alloc(limb_octets)?;
        let mut target_signs = signs.pointer;
        let mut target_limbs = limbs.pointer;
        let mut source_rows_wire = source_rows as u32;
        let mut factor_count_wire = self.factors;
        let mut generator_count_wire = generator_count;
        let mut source_limb_count_wire = source_limb_count as u32;
        let mut target_limb_count_wire = target_limb_count as u32;
        let mut arguments: [*mut c_void; 11] = [
            &mut source_signs as *mut u64 as *mut c_void,
            &mut source_limbs as *mut u64 as *mut c_void,
            &mut generator_pointer as *mut u64 as *mut c_void,
            &mut target_signs as *mut u64 as *mut c_void,
            &mut target_limbs as *mut u64 as *mut c_void,
            &mut source_rows_wire as *mut u32 as *mut c_void,
            &mut factor_count_wire as *mut u32 as *mut c_void,
            &mut generator_count_wire as *mut u32 as *mut c_void,
            &mut source_limb_count_wire as *mut u32 as *mut c_void,
            &mut target_limb_count_wire as *mut u32 as *mut c_void,
            &mut obstruction_pointer as *mut u64 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card.membrane_factored_moment_incidence_transport,
                    self.card.grid_for(rows as u64)?,
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
            "cuLaunchKernel(transport_membrane_factored_constitutive_spine)",
        )?;
        self.card.launches = self
            .card
            .launches
            .checked_add(1)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let resident_octets = u64::try_from(
            sign_octets
                .checked_add(limb_octets)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        )
        .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let matrix = ResidentIntegralMatrix {
            rows: rows as u32,
            columns: self.factors,
            numerator_limb_count: target_limb_count as u32,
            maximal_numerator,
            signs,
            limbs,
            resident_octets,
        };
        matrix.validate_layout()?;
        Ok(matrix)
    }

    /// Transport and exactly quotient complete rooted history blocks.  Equality compares every
    /// signed incidence entry; the returned multiplicity is the complete size of each collapsed
    /// ordered-history fibre and therefore remains part of later pair contraction.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn transport_and_condense_resident_constitutive_spine(
        &mut self,
        root_rank: u32,
        source_history_population: u32,
        source_incidence_limb_count: usize,
        source_maximal_incidence: BigInt,
        source_incidence_signs: u64,
        source_incidence_limbs: u64,
        source_history_weight_limb_count: u32,
        source_maximal_history_weight: BigUint,
        mut source_history_weights: u64,
        generator_targets: &[u32],
        generator_count: u32,
        generator_pointer: u64,
        overflow_pointer: u64,
    ) -> Result<ResidentTransportedConstitutiveSpine, CudaRefineError> {
        if root_rank == 0
            || source_history_population == 0
            || source_history_weight_limb_count == 0
            || source_maximal_history_weight.is_zero()
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let source_rows = root_rank
            .checked_mul(source_history_population)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let candidate = self.transport_resident_integral_matrix(
            source_rows as usize,
            source_incidence_limb_count,
            source_maximal_incidence,
            source_incidence_signs,
            source_incidence_limbs,
            generator_targets,
            generator_count,
            generator_pointer,
            overflow_pointer,
        )?;
        let candidate_history_population =
            source_history_population
                .checked_mul(generator_count)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        if candidate.rows
            != root_rank
                .checked_mul(candidate_history_population)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let block_entry_count = root_rank
            .checked_mul(self.factors)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let candidate_histories = candidate_history_population as usize;
        let candidate_entries = candidate_histories
            .checked_mul(block_entry_count as usize)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let target_weight_bound =
            source_maximal_history_weight * BigUint::from(candidate_history_population);
        let target_weight_limb_count = target_weight_bound.to_u32_digits().len().max(1);
        if target_weight_limb_count > u32::MAX as usize {
            return Err(CudaRefineError::MembraneInteriorCurrentOutsideApparatus);
        }
        let representatives = Buffer::alloc(
            candidate_histories
                .checked_mul(std::mem::size_of::<u32>())
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        )?;
        let target_signs = Buffer::alloc(candidate_entries)?;
        let target_limb_octets = candidate_entries
            .checked_mul(candidate.numerator_limb_count as usize)
            .and_then(|held| held.checked_mul(std::mem::size_of::<u32>()))
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let target_limbs = Buffer::alloc(target_limb_octets)?;
        let target_weight_octets = candidate_histories
            .checked_mul(target_weight_limb_count)
            .and_then(|held| held.checked_mul(std::mem::size_of::<u32>()))
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let target_weights = Buffer::alloc(target_weight_octets)?;
        let candidate_to_target = Buffer::alloc(
            candidate_histories
                .checked_mul(std::mem::size_of::<u32>())
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        )?;
        let target_count = Buffer::of(&[0_u32])?;

        let mut candidate_signs = candidate.signs.pointer;
        let mut candidate_limbs = candidate.limbs.pointer;
        let mut representatives_pointer = representatives.pointer;
        let mut candidate_history_count_wire = candidate_history_population;
        let mut block_entry_count_wire = block_entry_count;
        let mut incidence_limb_count_wire = candidate.numerator_limb_count;
        let mut identify_arguments: [*mut c_void; 6] = [
            &mut candidate_signs as *mut u64 as *mut c_void,
            &mut candidate_limbs as *mut u64 as *mut c_void,
            &mut representatives_pointer as *mut u64 as *mut c_void,
            &mut candidate_history_count_wire as *mut u32 as *mut c_void,
            &mut block_entry_count_wire as *mut u32 as *mut c_void,
            &mut incidence_limb_count_wire as *mut u32 as *mut c_void,
        ];
        let grid = self.card.grid_for(candidate_histories as u64)?;
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card.membrane_factored_history_identify,
                    grid,
                    1,
                    1,
                    self.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    identify_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(identify_membrane_equal_factored_history_blocks)",
        )?;

        let mut target_signs_pointer = target_signs.pointer;
        let mut target_limbs_pointer = target_limbs.pointer;
        let mut target_weights_pointer = target_weights.pointer;
        let mut candidate_to_target_pointer = candidate_to_target.pointer;
        let mut target_count_pointer = target_count.pointer;
        let mut source_history_count_wire = source_history_population;
        let mut generator_count_wire = generator_count;
        let mut source_weight_limb_count_wire = source_history_weight_limb_count;
        let mut target_weight_limb_count_wire = target_weight_limb_count as u32;
        let mut overflow_pointer_wire = overflow_pointer;
        let mut compact_arguments: [*mut c_void; 16] = [
            &mut candidate_signs as *mut u64 as *mut c_void,
            &mut candidate_limbs as *mut u64 as *mut c_void,
            &mut source_history_weights as *mut u64 as *mut c_void,
            &mut representatives_pointer as *mut u64 as *mut c_void,
            &mut target_signs_pointer as *mut u64 as *mut c_void,
            &mut target_limbs_pointer as *mut u64 as *mut c_void,
            &mut target_weights_pointer as *mut u64 as *mut c_void,
            &mut candidate_to_target_pointer as *mut u64 as *mut c_void,
            &mut target_count_pointer as *mut u64 as *mut c_void,
            &mut source_history_count_wire as *mut u32 as *mut c_void,
            &mut generator_count_wire as *mut u32 as *mut c_void,
            &mut block_entry_count_wire as *mut u32 as *mut c_void,
            &mut incidence_limb_count_wire as *mut u32 as *mut c_void,
            &mut source_weight_limb_count_wire as *mut u32 as *mut c_void,
            &mut target_weight_limb_count_wire as *mut u32 as *mut c_void,
            &mut overflow_pointer_wire as *mut u64 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card.membrane_factored_history_compact,
                    grid,
                    1,
                    1,
                    self.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    compact_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(compact_membrane_equal_factored_history_blocks)",
        )?;
        driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
        self.card.launches = self
            .card
            .launches
            .checked_add(2)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let mut target_history_population = [0_u32; 1];
        target_count.read(&mut target_history_population)?;
        let target_history_population = target_history_population[0];
        if target_history_population == 0
            || target_history_population > candidate_history_population
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let effective_incidence = ResidentIntegralMatrix {
            rows: root_rank
                .checked_mul(target_history_population)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
            columns: self.factors,
            numerator_limb_count: candidate.numerator_limb_count,
            maximal_numerator: candidate.maximal_numerator,
            signs: target_signs,
            limbs: target_limbs,
            resident_octets: u64::try_from(
                candidate_entries
                    .checked_add(target_limb_octets)
                    .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
            )
            .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        };
        let returned = ResidentTransportedConstitutiveSpine {
            root_rank,
            history_population: target_history_population,
            effective_incidence,
            history_weight_limb_count: target_weight_limb_count as u32,
            maximal_history_weight: target_weight_bound,
            history_weights: target_weights,
            quotient_passage: Some(ResidentFactoredHistoryQuotientPassage {
                source_history_population,
                generator_population: generator_count,
                presented_history_population: candidate_history_population,
                target_history_population,
                candidate_to_target,
            }),
        };
        returned.validate_layout(self.factors)?;
        Ok(returned)
    }
}
