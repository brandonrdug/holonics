//! Terminal completion of factored-moment receiver passages.

use super::*;

impl super::ResidentMembraneInteriorWord {
    /// Complete R4Q2C+D in one terminal return. The method observes only the final admission,
    /// exact receiver coordinates, and dimensional testimony; after those agree it moves the
    /// already-produced target buffers into the continuing image owner and releases the source.
    pub fn complete_resident_factored_moment_receivers(
        &mut self,
        address: &ResidentFactoredMomentReceiverAddress,
    ) -> Result<ResidentFactoredMomentReceiverReturn, CudaRefineError> {
        if &self.resident_factored_moment_receiver_address()? != address {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
        let (
            source_address,
            rank_capacity,
            chart_count,
            output_population,
            output_limb_count,
            output_bound,
            receiver_denominator,
            total_launches,
            apparatus_shape_host_egress_octets,
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
            let receiver = candidate
                .receiver
                .as_ref()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            (
                transport.source_address.clone(),
                candidate.image_rank_capacity as usize,
                coordinate.primes_host_testimony.len(),
                receiver.receiver_population as usize,
                receiver.output_limb_count as usize,
                receiver.output_bound.clone(),
                receiver.output_denominator.clone(),
                3_u64
                    .checked_add(coordinate.launches)
                    .and_then(|held| held.checked_add(candidate.launches))
                    .and_then(|held| held.checked_add(receiver.launches))
                    .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
                receiver.apparatus_shape_host_egress_octets,
            )
        };
        let mut obstruction = [0_u32; 1];
        let mut admitted = [0_u32; 1];
        let mut rank = [0_u32; 1];
        let mut basis_factors = vec![u32::MAX; rank_capacity];
        let mut chart_witnesses = vec![0_u8; chart_count];
        let mut denominator_limbs;
        let mut output_signs = vec![0_u8; output_population];
        let mut output_limbs = vec![0_u32; output_population.saturating_mul(output_limb_count)];
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
            let candidate = atlas
                .coordinates
                .as_ref()
                .and_then(|coordinate| coordinate.candidate.as_ref())
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let receiver = candidate
                .receiver
                .as_ref()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            denominator_limbs = vec![0_u32; candidate.denominator_limb_count as usize];
            transport.overflow.read(&mut obstruction)?;
            candidate.admitted.read(&mut admitted)?;
            atlas.selected_rank.read(&mut rank)?;
            atlas.selected_columns.read(&mut basis_factors)?;
            candidate.chart_witnesses.read(&mut chart_witnesses)?;
            candidate.denominator_limbs.read(&mut denominator_limbs)?;
            receiver.output_signs.read(&mut output_signs)?;
            receiver.output_limbs.read(&mut output_limbs)?;
        }
        let rank = rank[0] as usize;
        if obstruction[0] != 0
            || admitted[0] != 1
            || rank == 0
            || rank > rank_capacity
            || chart_witnesses.iter().any(|witness| *witness != 1)
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        basis_factors.truncate(rank);
        let denominator = BigInt::from(BigUint::new(denominator_limbs.clone()));
        if denominator <= BigInt::zero() {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let receiver_numerators = output_signs
            .iter()
            .enumerate()
            .map(|(output, sign)| {
                let begin = output * output_limb_count;
                decode_signed_magnitude(*sign, &output_limbs[begin..begin + output_limb_count])
            })
            .collect::<Result<Vec<_>, _>>()?;
        if receiver_numerators.iter().any(|numerator| {
            numerator
                .abs()
                .to_biguint()
                .is_some_and(|held| held > output_bound)
        }) {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let receiver_denominator = receiver_denominator.unwrap_or_else(|| denominator.clone());
        if receiver_denominator <= BigInt::zero() {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let receiver_coordinates = receiver_numerators
            .into_iter()
            .map(|numerator| Rat::new(numerator, receiver_denominator.clone()))
            .collect::<Vec<_>>();

        // All host reads above are terminal testimony. Only now move the device-admitted delta
        // into the single continuing image owner and release the source/transport work fibre.
        // The compact target chart and rooted productive spine retain different addresses and
        // reconstruction fibres; their equality was admitted by the exact descent square above.
        let (candidate, reconstruction_spine) = {
            let mount = self
                .factored_receiver_history
                .as_mut()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let source = mount
                .image
                .take()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let mut transport = mount
                .transported_image
                .take()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let mut atlas = transport
                .rank_atlas
                .take()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let mut coordinate = atlas
                .coordinates
                .take()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let candidate = coordinate
                .candidate
                .take()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let transported_spine = transport.constitutive_spine.take();
            let source_rank = source.image_rank;
            let source_factors = source.factor_population;
            let source_constitutive = source.constitutive;
            let source_spine = source.constitutive_spine;
            if transport.productive_history.is_some() {
                return Err(CudaRefineError::MembraneInteriorWordShape);
            }
            let (
                root_rank,
                history_population,
                root_constitutive,
                effective_incidence,
                history_weight_limb_count,
                maximal_history_weight,
                history_weights,
                reconstruction_fibre,
            ) = match (source_spine, transported_spine) {
                (Some(spine), Some(transported)) => {
                    spine.validate_layout(source_factors)?;
                    transported.validate_layout(source_factors)?;
                    let presented_histories = spine
                        .history_population
                        .checked_mul(transport.generator_population)
                        .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
                    if transported.root_rank != spine.root_rank
                        || transported.history_population > presented_histories
                    {
                        return Err(CudaRefineError::MembraneInteriorWordShape);
                    }
                    let ResidentTransportedConstitutiveSpine {
                        history_population,
                        effective_incidence,
                        history_weight_limb_count,
                        maximal_history_weight,
                        history_weights,
                        quotient_passage,
                        ..
                    } = transported;
                    let mut reconstruction_fibre = spine.reconstruction_fibre;
                    if let Some(passage) = quotient_passage {
                        if passage.source_history_population != spine.history_population
                            || passage.generator_population != transport.generator_population
                            || passage.presented_history_population != presented_histories
                            || passage.target_history_population != history_population
                        {
                            return Err(CudaRefineError::MembraneInteriorWordShape);
                        }
                        reconstruction_fibre.push(passage);
                    }
                    (
                        spine.root_rank,
                        history_population,
                        spine.root_constitutive,
                        effective_incidence,
                        history_weight_limb_count,
                        maximal_history_weight,
                        history_weights,
                        reconstruction_fibre,
                    )
                }
                (None, None) => {
                    let entries = (transport.transported_row_population as usize)
                        .checked_mul(transport.factor_population as usize)
                        .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
                    let resident_octets = u64::try_from(
                        entries
                            .checked_add(
                                entries
                                    .checked_mul(transport.numerator_limb_count as usize)
                                    .and_then(|held| held.checked_mul(std::mem::size_of::<u32>()))
                                    .ok_or(
                                        CudaRefineError::MembraneInteriorCurrentOutsideApparatus,
                                    )?,
                            )
                            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
                    )
                    .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
                    (
                        source_rank,
                        transport.generator_population,
                        source_constitutive,
                        ResidentIntegralMatrix {
                            rows: transport.transported_row_population,
                            columns: transport.factor_population,
                            numerator_limb_count: transport.numerator_limb_count,
                            maximal_numerator: transport.maximal_numerator,
                            signs: transport.signs,
                            limbs: transport.limbs,
                            resident_octets,
                        },
                        1,
                        BigUint::one(),
                        Buffer::of(&vec![1_u32; transport.generator_population as usize])?,
                        Vec::new(),
                    )
                }
                _ => return Err(CudaRefineError::MembraneInteriorWordShape),
            };
            let spine = ResidentFactoredConstitutiveSpine {
                root_rank,
                history_population,
                root_constitutive,
                effective_incidence,
                history_weight_limb_count,
                maximal_history_weight,
                history_weights,
                reconstruction_fibre,
            };
            spine.validate_layout(source_factors)?;
            (candidate, spine)
        };
        let incidence_resident_octets = u64::try_from(
            rank_capacity
                .checked_mul(address.factor_population as usize)
                .and_then(|entries| {
                    entries.checked_add(
                        entries
                            .checked_mul(candidate.incidence_limb_count as usize)?
                            .checked_mul(std::mem::size_of::<u32>())?,
                    )
                })
                .and_then(|octets| octets.checked_add(std::mem::size_of::<u32>()))
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        )
        .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let constitutive_capacity = rank_capacity
            .checked_mul(rank_capacity)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let constitutive_resident_octets = u64::try_from(
            constitutive_capacity
                .checked_add(
                    constitutive_capacity
                        .checked_mul(candidate.constitutive_limb_count as usize)
                        .and_then(|entries| entries.checked_mul(std::mem::size_of::<u32>()))
                        .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
                )
                .and_then(|octets| {
                    octets.checked_add(
                        candidate.denominator_limb_count as usize * std::mem::size_of::<u32>(),
                    )
                })
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        )
        .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        // The factorization square above proves the compact candidate and its descended
        // constitutive spine are two charts of the same exact moment.  The candidate remains the
        // compact checkpoint; the spine is not an enumerated source-history family but the
        // generator-compatible incidence/weight quotient which transports the next current
        // without rebuilding the complete dual receiver atlas.  Dropping it here forces every
        // later order to refactor the compact checkpoint and causes coefficient/workspace growth.
        // Preserve the spine in the singular hot owner; its reconstruction passages remain cold
        // inside the spine and its next transport condenses equal histories before conduct.
        let target_state = ResidentFactoredMomentState {
            generation: candidate.target_generation,
            section_identity_sha256: candidate.section_lineage_identity_sha256.clone(),
            factor_population: address.factor_population,
            productive_population: rank as u32,
            compact_generation: candidate.target_generation,
            image_rank: rank as u32,
            basis_factors,
            incidence: ResidentExactRationalMatrix {
                rows: rank as u32,
                columns: address.factor_population,
                numerator_limb_count: candidate.incidence_limb_count,
                denominator_limb_count: 1,
                common_denominator: BigInt::one(),
                maximal_numerator: candidate.maximal_incidence_numerator.clone(),
                numerator_signs: candidate.incidence_signs,
                numerator_limbs: candidate.incidence_limbs,
                denominator_limbs: candidate.incidence_denominator_limbs,
                resident_octets: incidence_resident_octets,
            },
            constitutive: ResidentExactRationalMatrix {
                rows: rank as u32,
                columns: rank as u32,
                numerator_limb_count: candidate.constitutive_limb_count,
                denominator_limb_count: candidate.denominator_limb_count,
                common_denominator: denominator,
                maximal_numerator: candidate.maximal_constitutive_numerator,
                numerator_signs: candidate.constitutive_signs,
                numerator_limbs: candidate.constitutive_limbs,
                denominator_limbs: candidate.denominator_limbs,
                resident_octets: constitutive_resident_octets,
            },
            constitutive_spine: Some(reconstruction_spine),
        };
        target_state.incidence.validate_layout()?;
        target_state.constitutive.validate_layout()?;
        self.factored_receiver_history
            .as_mut()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?
            .image = Some(target_state);
        let target_address = self.resident_factored_moment_address()?;
        let terminal_host_egress_octets = [
            std::mem::size_of_val(&obstruction),
            std::mem::size_of_val(&admitted),
            std::mem::size_of::<u32>(),
            std::mem::size_of_val(chart_witnesses.as_slice()),
            std::mem::size_of_val(denominator_limbs.as_slice()),
            std::mem::size_of_val(output_signs.as_slice()),
            std::mem::size_of_val(output_limbs.as_slice()),
        ]
        .into_iter()
        .try_fold(0_u64, |sum, octets| {
            sum.checked_add(u64::try_from(octets).ok()?)
        })
        .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        Ok(ResidentFactoredMomentReceiverReturn {
            address: address.clone(),
            source_address,
            target_address,
            receiver_coordinates,
            device: self.card.device_name.clone(),
            context_identity: self.card.context as usize,
            launches: total_launches,
            device_dependency_edges: total_launches.saturating_sub(1),
            synchronizations: 1 + u64::from(apparatus_shape_host_egress_octets != 0),
            apparatus_shape_host_egress_octets,
            intermediate_host_egress_octets: 0,
            terminal_host_egress_octets,
            atomic_image_replacement: true,
            source_released_only_after_device_admission: true,
            receiver_history_quotient_rested: true,
            rooted_history_retained_hot: false,
            ambient_factor_square_materialized: false,
            host_rational_continuation: false,
        })
    }

    /// Complete a productive rooted-spine passage without replacing it by a newly canonicalized
    /// dense chart.  The latest compact chart remains an explicitly older reconstruction
    /// checkpoint; the transported rooted incidence is the sole hot target occurrence.
    pub fn complete_resident_factored_constitutive_spine_receivers(
        &mut self,
        address: &ResidentFactoredMomentReceiverAddress,
    ) -> Result<ResidentFactoredMomentReceiverReturn, CudaRefineError> {
        if &self.resident_factored_moment_receiver_address()? != address {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
        let (
            source_address,
            receiver_population,
            output_limb_count,
            output_bound,
            output_denominator,
            receiver_launches,
            apparatus_shape_host_egress_octets,
        ) = {
            let transport = self
                .factored_receiver_history
                .as_ref()
                .and_then(|mount| mount.transported_image.as_ref())
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            if transport.rank_atlas.is_some()
                || transport.constitutive_spine.is_some()
                || transport.productive_history.is_none()
            {
                return Err(CudaRefineError::MembraneInteriorWordShape);
            }
            let receiver = transport
                .productive_receiver
                .as_ref()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            (
                transport.source_address.clone(),
                receiver.receiver_population as usize,
                receiver.output_limb_count as usize,
                receiver.output_bound.clone(),
                receiver
                    .output_denominator
                    .clone()
                    .ok_or(CudaRefineError::MembraneInteriorWordShape)?,
                receiver.launches,
                receiver.apparatus_shape_host_egress_octets,
            )
        };
        if receiver_population == 0
            || output_limb_count == 0
            || output_denominator <= BigInt::zero()
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let mut obstruction = [0_u32; 1];
        let mut admitted = [0_u32; 1];
        let mut output_signs = vec![0_u8; receiver_population];
        let mut output_limbs = vec![
            0_u32;
            receiver_population.checked_mul(output_limb_count).ok_or(
                CudaRefineError::MembraneInteriorCurrentOutsideApparatus
            )?
        ];
        {
            let transport = self
                .factored_receiver_history
                .as_ref()
                .and_then(|mount| mount.transported_image.as_ref())
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let receiver = transport
                .productive_receiver
                .as_ref()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            transport.overflow.read(&mut obstruction)?;
            transport.productive_admitted.read(&mut admitted)?;
            receiver.output_signs.read(&mut output_signs)?;
            receiver.output_limbs.read(&mut output_limbs)?;
        }
        if obstruction[0] != 0 || admitted[0] != 1 {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let receiver_numerators = output_signs
            .iter()
            .enumerate()
            .map(|(output, sign)| {
                let begin = output * output_limb_count;
                decode_signed_magnitude(*sign, &output_limbs[begin..begin + output_limb_count])
            })
            .collect::<Result<Vec<_>, _>>()?;
        if receiver_numerators.iter().any(|numerator| {
            numerator
                .abs()
                .to_biguint()
                .is_some_and(|held| held > output_bound)
        }) {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let receiver_coordinates = receiver_numerators
            .into_iter()
            .map(|numerator| Rat::new(numerator, output_denominator.clone()))
            .collect::<Vec<_>>();

        let target_generation;
        {
            let mount = self
                .factored_receiver_history
                .as_mut()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let mut transport = mount
                .transported_image
                .take()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let source = mount
                .image
                .take()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let receiver = transport
                .productive_receiver
                .take()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let source_spine = source
                .constitutive_spine
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            source_spine.validate_layout(source.factor_population)?;
            let productive_history = transport
                .productive_history
                .take()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            productive_history.validate_layout(transport.transported_row_population)?;
            target_generation = transport.target_generation;
            let presented_history_population = source_spine
                .history_population
                .checked_mul(transport.generator_population)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            let expected_rows = productive_history
                .root_rank
                .checked_mul(productive_history.history_population)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            if transport.transported_row_population != expected_rows
                || transport.factor_population != source.factor_population
                || productive_history.root_rank != source_spine.root_rank
                || productive_history.history_population > presented_history_population
            {
                return Err(CudaRefineError::MembraneInteriorWordShape);
            }
            let mut reconstruction_fibre = source_spine.reconstruction_fibre;
            if let Some(passage) = productive_history.quotient_passage {
                if passage.source_history_population != source_spine.history_population
                    || passage.generator_population != transport.generator_population
                    || passage.presented_history_population != presented_history_population
                    || passage.target_history_population != productive_history.history_population
                {
                    return Err(CudaRefineError::MembraneInteriorWordShape);
                }
                reconstruction_fibre.push(passage);
            }
            let entries = (transport.transported_row_population as usize)
                .checked_mul(transport.factor_population as usize)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            let effective_resident_octets = u64::try_from(
                entries
                    .checked_add(
                        entries
                            .checked_mul(transport.numerator_limb_count as usize)
                            .and_then(|held| held.checked_mul(std::mem::size_of::<u32>()))
                            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
                    )
                    .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
            )
            .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            let target_spine = ResidentFactoredConstitutiveSpine {
                root_rank: source_spine.root_rank,
                history_population: productive_history.history_population,
                root_constitutive: source_spine.root_constitutive,
                effective_incidence: ResidentIntegralMatrix {
                    rows: transport.transported_row_population,
                    columns: transport.factor_population,
                    numerator_limb_count: transport.numerator_limb_count,
                    maximal_numerator: transport.maximal_numerator,
                    signs: transport.signs,
                    limbs: transport.limbs,
                    resident_octets: effective_resident_octets,
                },
                history_weight_limb_count: productive_history.history_weight_limb_count,
                maximal_history_weight: productive_history.maximal_history_weight,
                history_weights: productive_history.history_weights,
                reconstruction_fibre,
            };
            target_spine.validate_layout(source.factor_population)?;
            let target = ResidentFactoredMomentState {
                generation: target_generation,
                section_identity_sha256: receiver.section_lineage_identity_sha256,
                factor_population: source.factor_population,
                productive_population: expected_rows,
                compact_generation: source.compact_generation,
                image_rank: source.image_rank,
                basis_factors: source.basis_factors,
                incidence: source.incidence,
                constitutive: source.constitutive,
                constitutive_spine: Some(target_spine),
            };
            mount.image = Some(target);
        }
        let target_address = self.resident_factored_moment_address()?;
        let terminal_host_egress_octets = [
            std::mem::size_of_val(&obstruction),
            std::mem::size_of_val(&admitted),
            std::mem::size_of_val(output_signs.as_slice()),
            std::mem::size_of_val(output_limbs.as_slice()),
        ]
        .into_iter()
        .try_fold(0_u64, |sum, octets| {
            sum.checked_add(u64::try_from(octets).ok()?)
        })
        .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let launches = receiver_launches
            .checked_add(1)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        Ok(ResidentFactoredMomentReceiverReturn {
            address: address.clone(),
            source_address,
            target_address,
            receiver_coordinates,
            device: self.card.device_name.clone(),
            context_identity: self.card.context as usize,
            launches,
            device_dependency_edges: launches.saturating_sub(1),
            synchronizations: 1 + u64::from(apparatus_shape_host_egress_octets != 0),
            apparatus_shape_host_egress_octets,
            intermediate_host_egress_octets: 0,
            terminal_host_egress_octets,
            atomic_image_replacement: true,
            source_released_only_after_device_admission: true,
            receiver_history_quotient_rested: true,
            rooted_history_retained_hot: false,
            ambient_factor_square_materialized: false,
            host_rational_continuation: false,
        })
    }
}
