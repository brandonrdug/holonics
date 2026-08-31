//! Resident factored-moment coordinate reconstruction and inspection.
use std::ffi::c_void;
use std::ptr;

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, Zero};
use relational_geometry::Rat;

use crate::exact_linear::ExactRatMatrix;

use super::{
    Buffer, CudaRefineError, ResidentFactoredMomentCoordinateAddress,
    ResidentFactoredMomentCoordinateAtlas, ResidentFactoredMomentCoordinateReturn,
    ResidentFactoredMomentRankAddress, ResidentMembraneInteriorWord, cuCtxSetCurrent,
    cuCtxSynchronize, cuLaunchKernel, driver, trace_configuration,
};

impl ResidentMembraneInteriorWord {
    pub fn stage_resident_factored_moment_coordinates(
        &mut self,
        rank_address: &ResidentFactoredMomentRankAddress,
    ) -> Result<ResidentFactoredMomentCoordinateAddress, CudaRefineError> {
        if &self.resident_factored_moment_rank_address()? != rank_address {
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
            maximal_incidence,
            maximal_constitutive,
            minor_bound,
            mut source_signs,
            mut source_limbs,
            mut constitutive_signs,
            mut constitutive_limbs,
            mut selected_rank,
            mut selected_rows,
            mut selected_columns,
            mut obstruction,
        ) = {
            let mount = self
                .factored_receiver_history
                .as_ref()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let image = mount
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
            if atlas.coordinates.is_some()
                || image.incidence.common_denominator != BigInt::one()
                || image.constitutive.maximal_numerator.is_zero()
            {
                return Err(CudaRefineError::MembraneInteriorWordShape);
            }
            (
                transport.transported_row_population as usize,
                transport.factor_population as usize,
                image.image_rank as usize,
                transport.generator_population as usize,
                transport.numerator_limb_count as usize,
                image.constitutive.numerator_limb_count as usize,
                transport
                    .maximal_numerator
                    .to_biguint()
                    .ok_or(CudaRefineError::MembraneInteriorWordShape)?,
                image
                    .constitutive
                    .maximal_numerator
                    .to_biguint()
                    .ok_or(CudaRefineError::MembraneInteriorWordShape)?,
                atlas.minor_bound.clone(),
                transport.signs.pointer,
                transport.limbs.pointer,
                image.constitutive.numerator_signs.pointer,
                image.constitutive.numerator_limbs.pointer,
                atlas.selected_rank.pointer,
                atlas.selected_rows.pointer,
                atlas.selected_columns.pointer,
                transport.overflow.pointer,
            )
        };
        if rows == 0
            || factors == 0
            || source_rank == 0
            || generators == 0
            || rows != source_rank.saturating_mul(generators)
            || source_limb_count == 0
            || constitutive_limb_count == 0
            || minor_bound.is_zero()
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let maximal_rank = rows.min(factors);
        let mut maximal_rank_wire = u32::try_from(maximal_rank)
            .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let mut rows_wire = u32::try_from(rows)
            .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let mut factors_wire = u32::try_from(factors)
            .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let mut source_rank_wire = u32::try_from(source_rank)
            .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let mut generators_wire = u32::try_from(generators)
            .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let mut source_limb_count_wire = u32::try_from(source_limb_count)
            .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let mut constitutive_limb_count_wire = u32::try_from(constitutive_limb_count)
            .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;

        // If D is the selected nonzero minor, every coordinate numerator J is a Cramer minor,
        // hence |D|, |J_ij| <= D_X. For H=N/d and g plural blocks, every entry of J^T N J is
        // bounded by g r^2 h D_X^2. Removing all primes dividing D can discard a product no
        // larger than |D| <= D_X, so the whole family crosses (2U)D_X before its good fibre is
        // admitted. No rank, width, or chart population is supplied by a caller.
        let constitutive_bound = BigUint::from(generators_wire)
            * BigUint::from(source_rank_wire).pow(2)
            * maximal_constitutive
            * minor_bound.pow(2);
        let factorization_difference_bound =
            BigUint::from(maximal_rank_wire + 1) * &minor_bound * maximal_incidence;
        let absolute_bound = minor_bound
            .clone()
            .max(constitutive_bound)
            .max(factorization_difference_bound);
        let signed_reconstruction_bound = &absolute_bound << 1usize;
        let family_bound = &signed_reconstruction_bound * &minor_bound;
        let (primes_host_testimony, chart_product) =
            super::derive_word_prime_family(&family_bound)?;
        if chart_product <= family_bound || primes_host_testimony.len() > u32::MAX as usize {
            return Err(CudaRefineError::MembraneInteriorCurrentOutsideApparatus);
        }
        let charts = primes_host_testimony.len();
        let joining_values = rows
            .checked_mul(maximal_rank)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let constitutive_values = maximal_rank
            .checked_mul(maximal_rank)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let value_count = 1usize
            .checked_add(joining_values)
            .and_then(|count| count.checked_add(constitutive_values))
            .filter(|count| *count <= u32::MAX as usize)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let mut value_count_wire = value_count as u32;
        let crt_limb_count = chart_product.to_u32_digits().len().max(1);
        let bound_limb_count = absolute_bound
            .to_u32_digits()
            .len()
            .max(signed_reconstruction_bound.to_u32_digits().len())
            .max(1);
        if crt_limb_count > u32::MAX as usize || bound_limb_count > u32::MAX as usize {
            return Err(CudaRefineError::MembraneInteriorCurrentOutsideApparatus);
        }
        let mut crt_limb_count_wire = crt_limb_count as u32;
        let mut bound_limb_count_wire = bound_limb_count as u32;
        let mut absolute_bound_digits = absolute_bound.to_u32_digits();
        absolute_bound_digits.resize(bound_limb_count, 0);
        let mut signed_bound_digits = signed_reconstruction_bound.to_u32_digits();
        signed_bound_digits.resize(bound_limb_count, 0);

        let augmented_entries_per_chart = maximal_rank
            .checked_mul(maximal_rank.saturating_mul(2))
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let augmented_entries = charts
            .checked_mul(augmented_entries_per_chart)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let residue_entries_per_chart = value_count;
        let residue_entries = charts
            .checked_mul(residue_entries_per_chart)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let output_limb_entries = value_count
            .checked_mul(crt_limb_count)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let word_octets = |entries: usize| {
            entries
                .checked_mul(std::mem::size_of::<u32>())
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)
        };
        let primes = Buffer::of(&primes_host_testimony)?;
        let augmented_work = Buffer::alloc(word_octets(augmented_entries)?)?;
        let chart_good = Buffer::alloc(charts)?;
        let chart_residues = Buffer::alloc(word_octets(residue_entries)?)?;
        let good_count = Buffer::of(&[0_u32])?;
        let prefix_product = Buffer::alloc(word_octets(crt_limb_count)?)?;
        let prefix_inverse = Buffer::alloc(std::mem::size_of::<u32>())?;
        let active_chart = Buffer::alloc(std::mem::size_of::<u32>())?;
        let mut total_product_digits = vec![0_u32; crt_limb_count];
        total_product_digits[0] = 1;
        let total_product = Buffer::of(&total_product_digits)?;
        let half_product = Buffer::alloc(word_octets(crt_limb_count)?)?;
        let absolute_bound_limbs = Buffer::of(&absolute_bound_digits)?;
        let signed_reconstruction_bound_limbs = Buffer::of(&signed_bound_digits)?;
        let reconstructed_signs = Buffer::alloc(value_count)?;
        let reconstructed_limbs = Buffer::alloc(word_octets(output_limb_entries)?)?;
        reconstructed_limbs.fill(0, word_octets(output_limb_entries)?)?;

        let mut primes_pointer = primes.pointer;
        let mut augmented_pointer = augmented_work.pointer;
        let mut chart_good_base_pointer = chart_good.pointer;
        let mut chart_residues_base_pointer = chart_residues.pointer;
        let mut good_count_pointer = good_count.pointer;
        let mut prefix_pointer = prefix_product.pointer;
        let mut inverse_pointer = prefix_inverse.pointer;
        let mut active_pointer = active_chart.pointer;
        let mut total_pointer = total_product.pointer;
        let mut half_pointer = half_product.pointer;
        let mut reconstructed_signs_pointer = reconstructed_signs.pointer;
        let mut reconstructed_limbs_pointer = reconstructed_limbs.pointer;
        let reconstruction_grid = self.card.grid_for(value_count as u64)?;
        let mut chart_count_wire = charts as u32;
        let mut coordinate_arguments: [*mut c_void; 20] = [
            &mut source_signs as *mut u64 as *mut c_void,
            &mut source_limbs as *mut u64 as *mut c_void,
            &mut selected_rank as *mut u64 as *mut c_void,
            &mut selected_rows as *mut u64 as *mut c_void,
            &mut selected_columns as *mut u64 as *mut c_void,
            &mut primes_pointer as *mut u64 as *mut c_void,
            &mut constitutive_signs as *mut u64 as *mut c_void,
            &mut constitutive_limbs as *mut u64 as *mut c_void,
            &mut augmented_pointer as *mut u64 as *mut c_void,
            &mut chart_good_base_pointer as *mut u64 as *mut c_void,
            &mut chart_residues_base_pointer as *mut u64 as *mut c_void,
            &mut rows_wire as *mut u32 as *mut c_void,
            &mut factors_wire as *mut u32 as *mut c_void,
            &mut source_limb_count_wire as *mut u32 as *mut c_void,
            &mut source_rank_wire as *mut u32 as *mut c_void,
            &mut generators_wire as *mut u32 as *mut c_void,
            &mut constitutive_limb_count_wire as *mut u32 as *mut c_void,
            &mut maximal_rank_wire as *mut u32 as *mut c_void,
            &mut chart_count_wire as *mut u32 as *mut c_void,
            &mut obstruction as *mut u64 as *mut c_void,
        ];
        let coordinate_grid = self.card.grid_for(charts as u64)?;
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card.membrane_factored_moment_coordinate_residues,
                    coordinate_grid,
                    1,
                    1,
                    self.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    coordinate_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(derive_membrane_factored_moment_coordinate_residues)",
        )?;
        let mut launches = 1_u64;
        for chart in 0..charts {
            let chart_octets = chart
                .checked_mul(std::mem::size_of::<u32>())
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            let mut prime_pointer = primes
                .pointer
                .checked_add(chart_octets as u64)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            let mut chart_good_pointer = chart_good_base_pointer
                .checked_add(chart as u64)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            let residue_octets = chart
                .checked_mul(residue_entries_per_chart)
                .and_then(|entries| entries.checked_mul(std::mem::size_of::<u32>()))
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            let mut chart_residues_pointer = chart_residues_base_pointer
                .checked_add(residue_octets as u64)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            let mut prepare_arguments: [*mut c_void; 8] = [
                &mut prime_pointer as *mut u64 as *mut c_void,
                &mut chart_good_pointer as *mut u64 as *mut c_void,
                &mut total_pointer as *mut u64 as *mut c_void,
                &mut prefix_pointer as *mut u64 as *mut c_void,
                &mut inverse_pointer as *mut u64 as *mut c_void,
                &mut active_pointer as *mut u64 as *mut c_void,
                &mut crt_limb_count_wire as *mut u32 as *mut c_void,
                &mut obstruction as *mut u64 as *mut c_void,
            ];
            driver(
                unsafe {
                    cuLaunchKernel(
                        self.card.membrane_factored_moment_crt_prepare,
                        1,
                        1,
                        1,
                        self.card.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        prepare_arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(prepare_membrane_factored_moment_crt_chart)",
            )?;
            let mut accumulate_arguments: [*mut c_void; 9] = [
                &mut prime_pointer as *mut u64 as *mut c_void,
                &mut chart_residues_pointer as *mut u64 as *mut c_void,
                &mut active_pointer as *mut u64 as *mut c_void,
                &mut prefix_pointer as *mut u64 as *mut c_void,
                &mut inverse_pointer as *mut u64 as *mut c_void,
                &mut reconstructed_limbs_pointer as *mut u64 as *mut c_void,
                &mut value_count_wire as *mut u32 as *mut c_void,
                &mut crt_limb_count_wire as *mut u32 as *mut c_void,
                &mut obstruction as *mut u64 as *mut c_void,
            ];
            driver(
                unsafe {
                    cuLaunchKernel(
                        self.card.membrane_factored_moment_crt_accumulate,
                        reconstruction_grid,
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
                "cuLaunchKernel(accumulate_membrane_factored_moment_crt_chart)",
            )?;
            let mut advance_arguments: [*mut c_void; 6] = [
                &mut prime_pointer as *mut u64 as *mut c_void,
                &mut active_pointer as *mut u64 as *mut c_void,
                &mut total_pointer as *mut u64 as *mut c_void,
                &mut good_count_pointer as *mut u64 as *mut c_void,
                &mut crt_limb_count_wire as *mut u32 as *mut c_void,
                &mut obstruction as *mut u64 as *mut c_void,
            ];
            driver(
                unsafe {
                    cuLaunchKernel(
                        self.card.membrane_factored_moment_crt_advance,
                        1,
                        1,
                        1,
                        self.card.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        advance_arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(advance_membrane_factored_moment_crt_chart)",
            )?;
            launches = launches
                .checked_add(3)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        }

        let mut signed_bound_pointer = signed_reconstruction_bound_limbs.pointer;
        let mut close_arguments: [*mut c_void; 7] = [
            &mut total_pointer as *mut u64 as *mut c_void,
            &mut good_count_pointer as *mut u64 as *mut c_void,
            &mut signed_bound_pointer as *mut u64 as *mut c_void,
            &mut half_pointer as *mut u64 as *mut c_void,
            &mut crt_limb_count_wire as *mut u32 as *mut c_void,
            &mut bound_limb_count_wire as *mut u32 as *mut c_void,
            &mut obstruction as *mut u64 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card.membrane_factored_moment_crt_close,
                    1,
                    1,
                    1,
                    self.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    close_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(close_membrane_factored_moment_crt_product)",
        )?;
        let mut absolute_bound_pointer = absolute_bound_limbs.pointer;
        let mut center_arguments: [*mut c_void; 9] = [
            &mut total_pointer as *mut u64 as *mut c_void,
            &mut half_pointer as *mut u64 as *mut c_void,
            &mut absolute_bound_pointer as *mut u64 as *mut c_void,
            &mut reconstructed_signs_pointer as *mut u64 as *mut c_void,
            &mut reconstructed_limbs_pointer as *mut u64 as *mut c_void,
            &mut value_count_wire as *mut u32 as *mut c_void,
            &mut crt_limb_count_wire as *mut u32 as *mut c_void,
            &mut bound_limb_count_wire as *mut u32 as *mut c_void,
            &mut obstruction as *mut u64 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card.membrane_factored_moment_signed_crt,
                    reconstruction_grid,
                    1,
                    1,
                    self.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    center_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(center_membrane_factored_moment_signed_crt)",
        )?;
        launches = launches
            .checked_add(2)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        self.card.launches = self
            .card
            .launches
            .checked_add(launches)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        if trace_configuration().holonics_phase_trace {
            driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
            eprintln!(
                "mem6-image reconstruction-device-complete charts={} values={} limbs={}",
                charts, value_count, crt_limb_count
            );
        }

        let resident_octets = [
            word_octets(charts)?,
            word_octets(augmented_entries)?,
            charts,
            word_octets(residue_entries)?,
            std::mem::size_of::<u32>(),
            word_octets(crt_limb_count)?,
            std::mem::size_of::<u32>() * 2,
            word_octets(crt_limb_count)?.saturating_mul(2),
            word_octets(bound_limb_count)?.saturating_mul(2),
            value_count,
            word_octets(output_limb_entries)?,
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
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?
            .coordinates = Some(ResidentFactoredMomentCoordinateAtlas {
            primes_host_testimony,
            absolute_bound,
            signed_reconstruction_bound,
            chart_product,
            value_count: value_count_wire,
            maximal_rank: maximal_rank_wire,
            crt_limb_count: crt_limb_count_wire,
            bound_limb_count: bound_limb_count_wire,
            launches,
            primes,
            augmented_work,
            chart_good,
            chart_residues,
            good_count,
            prefix_product,
            prefix_inverse,
            active_chart,
            total_product,
            half_product,
            absolute_bound_limbs,
            signed_reconstruction_bound_limbs,
            reconstructed_signs,
            reconstructed_limbs,
            candidate: None,
            resident_octets,
        });
        self.resident_factored_moment_coordinate_address()
    }

    pub(super) fn resident_factored_moment_coordinate_address(
        &self,
    ) -> Result<ResidentFactoredMomentCoordinateAddress, CudaRefineError> {
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
        if coordinate.resident_octets == 0
            || coordinate.primes.pointer == 0
            || coordinate.augmented_work.pointer == 0
            || coordinate.chart_good.pointer == 0
            || coordinate.chart_residues.pointer == 0
            || coordinate.good_count.pointer == 0
            || coordinate.prefix_product.pointer == 0
            || coordinate.prefix_inverse.pointer == 0
            || coordinate.active_chart.pointer == 0
            || coordinate.total_product.pointer == 0
            || coordinate.half_product.pointer == 0
            || coordinate.absolute_bound_limbs.pointer == 0
            || coordinate.signed_reconstruction_bound_limbs.pointer == 0
            || coordinate.reconstructed_signs.pointer == 0
            || coordinate.reconstructed_limbs.pointer == 0
            || coordinate.signed_reconstruction_bound != (&coordinate.absolute_bound << 1usize)
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        Ok(ResidentFactoredMomentCoordinateAddress {
            operation_complex_identity_sha256: mount.receipt.identity_sha256.clone(),
            transport_identity_sha256: transport.transport_identity_sha256.clone(),
            device_context_identity: self.card.context as usize,
            source_generation: transport.source_address.generation,
            target_generation: transport.target_generation,
            transported_row_population: transport.transported_row_population,
            factor_population: transport.factor_population,
            maximal_rank: coordinate.maximal_rank,
            chart_population: coordinate.primes_host_testimony.len() as u32,
            reconstruction_value_population: coordinate.value_count,
            absolute_bound_bits: coordinate.absolute_bound.bits(),
            chart_product_bits: coordinate.chart_product.bits(),
        })
    }
    /// Observe the already-reconstructed signed fibre for a bounded diagnostic. This method does
    /// not perform CRT, select a chart, or construct coordinates on the host; it only decodes the
    /// terminal device result into exact exterior matrices.
    pub fn inspect_resident_factored_moment_coordinates(
        &mut self,
        address: &ResidentFactoredMomentCoordinateAddress,
    ) -> Result<ResidentFactoredMomentCoordinateReturn, CudaRefineError> {
        if &self.resident_factored_moment_coordinate_address()? != address {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
        let (
            rows,
            maximal_rank,
            value_count,
            crt_limb_count,
            bound_limb_count,
            launches,
            primes,
            absolute_bound,
            signed_reconstruction_bound,
            chart_product,
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
            (
                transport.transported_row_population as usize,
                coordinate.maximal_rank as usize,
                coordinate.value_count as usize,
                coordinate.crt_limb_count as usize,
                coordinate.bound_limb_count as usize,
                coordinate.launches,
                coordinate.primes_host_testimony.clone(),
                coordinate.absolute_bound.clone(),
                coordinate.signed_reconstruction_bound.clone(),
                coordinate.chart_product.clone(),
            )
        };
        let mut obstruction = [0_u32; 1];
        let mut selected_rank = [0_u32; 1];
        let mut good_count = [0_u32; 1];
        let mut total_product_limbs = vec![0_u32; crt_limb_count];
        let mut signs = vec![0_u8; value_count];
        let mut limbs = vec![0_u32; value_count.saturating_mul(crt_limb_count)];
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
            transport.overflow.read(&mut obstruction)?;
            atlas.selected_rank.read(&mut selected_rank)?;
            coordinate.good_count.read(&mut good_count)?;
            coordinate.total_product.read(&mut total_product_limbs)?;
            coordinate.reconstructed_signs.read(&mut signs)?;
            coordinate.reconstructed_limbs.read(&mut limbs)?;
        }
        let rank = selected_rank[0] as usize;
        let good_product = BigUint::new(total_product_limbs.clone());
        if obstruction[0] != 0
            || rank == 0
            || rank > maximal_rank
            || good_count[0] == 0
            || good_count[0] as usize > primes.len()
            || good_product <= signed_reconstruction_bound
            || value_count
                != 1usize
                    .saturating_add(rows.saturating_mul(maximal_rank))
                    .saturating_add(maximal_rank.saturating_mul(maximal_rank))
            || bound_limb_count == 0
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let values = signs
            .iter()
            .enumerate()
            .map(|(value, sign)| {
                let begin = value.saturating_mul(crt_limb_count);
                super::decode_signed_magnitude(*sign, &limbs[begin..begin + crt_limb_count])
            })
            .collect::<Result<Vec<_>, _>>()?;
        if values.iter().any(|value| {
            value
                .abs()
                .to_biguint()
                .is_some_and(|held| held > absolute_bound)
        }) || values[0].is_zero()
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let joining_start = 1usize;
        let constitutive_start = joining_start + rows * maximal_rank;
        let joining_numerator = ExactRatMatrix::new(
            (0..rows)
                .map(|row| {
                    (0..rank)
                        .map(|column| {
                            Rat::from_integer(
                                values[joining_start + row * maximal_rank + column].clone(),
                            )
                        })
                        .collect::<Vec<_>>()
                })
                .collect(),
        )
        .map_err(|_| CudaRefineError::MembraneInteriorWordShape)?;
        let constitutive_numerator = ExactRatMatrix::new(
            (0..rank)
                .map(|row| {
                    (0..rank)
                        .map(|column| {
                            Rat::from_integer(
                                values[constitutive_start + row * maximal_rank + column].clone(),
                            )
                        })
                        .collect::<Vec<_>>()
                })
                .collect(),
        )
        .map_err(|_| CudaRefineError::MembraneInteriorWordShape)?;
        let terminal_host_egress_octets = [
            std::mem::size_of_val(&obstruction),
            std::mem::size_of_val(&selected_rank),
            std::mem::size_of_val(&good_count),
            std::mem::size_of_val(total_product_limbs.as_slice()),
            std::mem::size_of_val(signs.as_slice()),
            std::mem::size_of_val(limbs.as_slice()),
        ]
        .into_iter()
        .try_fold(0_u64, |sum, octets| {
            sum.checked_add(u64::try_from(octets).ok()?)
        })
        .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        Ok(ResidentFactoredMomentCoordinateReturn {
            address: address.clone(),
            primes,
            good_chart_population: good_count[0],
            determinant: values[0].clone(),
            joining_numerator,
            constitutive_numerator,
            absolute_bound,
            chart_product,
            device: self.card.device_name.clone(),
            context_identity: self.card.context as usize,
            launches,
            synchronizations: 1,
            intermediate_host_egress_octets: 0,
            terminal_host_egress_octets,
            host_crt_reconstruction: false,
            host_selected_coordinate_chart: false,
        })
    }
}
