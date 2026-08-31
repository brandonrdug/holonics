use super::{
    CudaRefineError, ResidentFactoredMomentRankAddress, ResidentFactoredMomentRankReturn,
    ResidentFactoredMomentTransportAddress, ResidentFactoredMomentTransportOccurrence,
    ResidentFactoredMomentTransportReturn, ResidentMembraneInteriorWord, cuCtxSynchronize, driver,
};
use crate::exact_linear::ExactRatMatrix;
use num_bigint::{BigInt, BigUint};
use num_traits::Zero;
use relational_geometry::Rat;
use std::collections::BTreeSet;

impl ResidentMembraneInteriorWord {
    pub fn inspect_resident_factored_moment_rank(
        &mut self,
        address: &ResidentFactoredMomentRankAddress,
    ) -> Result<ResidentFactoredMomentRankReturn, CudaRefineError> {
        if &self.resident_factored_moment_rank_address()? != address {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
        let (primes, minor_bound, chart_product, rows, factors, exact_square_staged) = {
            let transport = self
                .factored_receiver_history
                .as_ref()
                .and_then(|mount| mount.transported_image.as_ref())
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let atlas = transport
                .rank_atlas
                .as_ref()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            (
                atlas.primes_host_testimony.clone(),
                atlas.minor_bound.clone(),
                atlas.chart_product.clone(),
                transport.transported_row_population as usize,
                transport.factor_population,
                atlas
                    .coordinates
                    .as_ref()
                    .and_then(|coordinate| coordinate.candidate.as_ref())
                    .is_some(),
            )
        };
        let mut obstruction = [0_u32; 1];
        let mut modular_ranks = vec![0_u32; primes.len()];
        let mut selected_chart = [u32::MAX; 1];
        let mut exact_rank = [0_u32; 1];
        let mut selected_rows = vec![u32::MAX; rows];
        let mut selected_columns = vec![u32::MAX; rows];
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
            transport.overflow.read(&mut obstruction)?;
            atlas.ranks.read(&mut modular_ranks)?;
            atlas.selected_chart.read(&mut selected_chart)?;
            atlas.selected_rank.read(&mut exact_rank)?;
            atlas.selected_rows.read(&mut selected_rows)?;
            atlas.selected_columns.read(&mut selected_columns)?;
        }
        let exact_rank = exact_rank[0] as usize;
        if !exact_square_staged
            || obstruction[0] != 0
            || exact_rank == 0
            || exact_rank > rows.min(factors as usize)
            || selected_chart[0] as usize >= primes.len()
            || modular_ranks.iter().copied().max() != Some(exact_rank as u32)
            || modular_ranks[selected_chart[0] as usize] != exact_rank as u32
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        selected_rows.truncate(exact_rank);
        selected_columns.truncate(exact_rank);
        if selected_rows.iter().any(|row| *row >= rows as u32)
            || selected_columns.iter().any(|factor| *factor >= factors)
            || selected_rows.iter().copied().collect::<BTreeSet<_>>().len() != exact_rank
            || selected_columns
                .iter()
                .copied()
                .collect::<BTreeSet<_>>()
                .len()
                != exact_rank
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let terminal_host_egress_octets = [
            std::mem::size_of_val(&obstruction),
            std::mem::size_of_val(modular_ranks.as_slice()),
            std::mem::size_of_val(&selected_chart),
            std::mem::size_of::<u32>(),
            std::mem::size_of_val(selected_rows.as_slice()),
            std::mem::size_of_val(selected_columns.as_slice()),
        ]
        .into_iter()
        .try_fold(0_u64, |sum, octets| {
            sum.checked_add(u64::try_from(octets).ok()?)
        })
        .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        Ok(ResidentFactoredMomentRankReturn {
            address: address.clone(),
            primes,
            modular_ranks,
            selected_chart: selected_chart[0],
            exact_rank: exact_rank as u32,
            basis_rows: selected_rows,
            basis_factors: selected_columns,
            minor_bound,
            chart_product,
            device: self.card.device_name.clone(),
            context_identity: self.card.context as usize,
            launches: 2,
            synchronizations: 1,
            intermediate_host_egress_octets: 0,
            terminal_host_egress_octets,
            host_selected_rank_or_pivot: false,
            probabilistic_rank: false,
        })
    }

    /// Terminally inspect a staged transport for the bounded R4Q2B equality gate. The production
    /// refactor path does not call this observer and therefore retains zero intermediate egress.
    pub fn inspect_resident_factored_moment_transport(
        &mut self,
        address: &ResidentFactoredMomentTransportAddress,
    ) -> Result<ResidentFactoredMomentTransportReturn, CudaRefineError> {
        if &self.resident_factored_moment_transport_address()? != address {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
        let (source_address, generators, rows, factors, limbs) = {
            let mount = self
                .factored_receiver_history
                .as_ref()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let transport = mount
                .transported_image
                .as_ref()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            (
                transport.source_address.clone(),
                transport.generator_population as usize,
                transport.transported_row_population as usize,
                transport.factor_population as usize,
                transport.numerator_limb_count as usize,
            )
        };
        let entry_population = rows
            .checked_mul(factors)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let mut signs = vec![0_u8; entry_population];
        let mut magnitudes = vec![
            0_u32;
            entry_population.checked_mul(limbs).ok_or(
                CudaRefineError::MembraneInteriorCurrentOutsideApparatus
            )?
        ];
        let mut overflow = [0_u32; 1];
        {
            let transport = self
                .factored_receiver_history
                .as_ref()
                .and_then(|mount| mount.transported_image.as_ref())
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            transport.signs.read(&mut signs)?;
            transport.limbs.read(&mut magnitudes)?;
            transport.overflow.read(&mut overflow)?;
        }
        if overflow[0] != 0 {
            return Err(CudaRefineError::MembraneInteriorCurrentOutsideApparatus);
        }
        let transported_incidence = ExactRatMatrix::new(
            (0..rows)
                .map(|row| {
                    (0..factors)
                        .map(|factor| {
                            let entry = row * factors + factor;
                            let begin = entry * limbs;
                            let magnitude = BigUint::new(magnitudes[begin..begin + limbs].to_vec());
                            let integer = match signs[entry] {
                                0 if magnitude.is_zero() => BigInt::zero(),
                                1 if !magnitude.is_zero() => BigInt::from(magnitude),
                                2 if !magnitude.is_zero() => -BigInt::from(magnitude),
                                _ => return Err(CudaRefineError::MembraneInteriorWordShape),
                            };
                            Ok(Rat::from_integer(integer))
                        })
                        .collect::<Result<Vec<_>, CudaRefineError>>()
                })
                .collect::<Result<Vec<_>, CudaRefineError>>()?,
        )
        .map_err(|_| CudaRefineError::MembraneInteriorWordShape)?;
        let action = self
            .quadratic_action
            .as_ref()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let generator_targets = action
            .generator_targets
            .chunks_exact(factors)
            .map(|generator| generator.to_vec())
            .collect::<Vec<_>>();
        if generator_targets.len() != generators {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let occurrences = (0..rows)
            .map(|row| ResidentFactoredMomentTransportOccurrence {
                generator: (row / source_address.image_population as usize) as u32,
                source_image: (row % source_address.image_population as usize) as u32,
                transported_row: row as u32,
            })
            .collect::<Vec<_>>();
        let terminal_host_egress_octets = u64::try_from(
            std::mem::size_of_val(&signs[..])
                .checked_add(std::mem::size_of_val(&magnitudes[..]))
                .and_then(|octets| octets.checked_add(std::mem::size_of_val(&overflow)))
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        )
        .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        Ok(ResidentFactoredMomentTransportReturn {
            source_address,
            transport_address: address.clone(),
            generator_targets,
            occurrences,
            transported_incidence,
            device: self.card.device_name.clone(),
            context_identity: self.card.context as usize,
            launches: 1,
            synchronizations: 1,
            successor_host_ingress_octets: 0,
            terminal_host_egress_octets,
            intermediate_host_egress_octets: 0,
            invariant_transport_reuploaded: false,
            cpu_semantic_replay_after_device: false,
        })
    }
}
