use super::*;

impl ResidentMembraneInteriorWord {
    /// Mount an exact primitive integral observable frame once.  All sparse form incidence,
    /// present receiver factors, and descended generator factors become resident invariant
    /// standing; later current supplies only its weighted rank-one section.

    /// Mount one plural exterior receiver occurrence as shared sparse functionals plus ordered
    /// functional-pair terms. Complex boundaries remain reconstructible from the caller's
    /// occurrence list; only their native dual incidence crosses. A later occurrence may replace
    /// this exterior face only when no candidate descent is in flight.

    /// Mount the exact factor section of every currently visible boundary port beside the
    /// addressed sparse receiver frame.  Production recurrence admits one restriction occurrence
    /// per local port: a plural state-dependent restriction would require a richer situated
    /// carrier and therefore returns an obstruction rather than being silently summed.

    /// Mount the complete descended generator action and its receiver-class incidence once. The
    /// exterior caller supplies the already-rested total tables; later front calls must present
    /// the identical action and cannot rebuild or re-upload these invariant spools.

    /// Bind the mounted axes into the single operation complex used by production contraction.
    /// The receipt is derived from their complete identities and the constitutive population; no
    /// ambient form, duplicate current or host-side semantic phase is founded here.
    pub(super) fn found_factored_receiver_history(
        &mut self,
    ) -> Result<ResidentFactoredReceiverHistoryReceipt, CudaRefineError> {
        let receiver_face_identity_sha256 = self
            .receiver_face_identity_sha256
            .clone()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let restriction = self
            .boundary_restriction_atlas
            .as_ref()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let action = self
            .quadratic_action
            .as_ref()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let mut identity = Sha256::new();
        identity.update(b"holonic-engine.resident-factored-receiver-history.v1");
        identity.update(receiver_face_identity_sha256.as_bytes());
        identity.update(restriction.identity_sha256.as_bytes());
        identity.update(action.identity_sha256.as_bytes());
        identity.update(self.factors.to_le_bytes());
        identity.update(self.families.to_le_bytes());
        identity.update(self.receiver_count.to_le_bytes());
        identity.update(action.receiver_class_count.to_le_bytes());
        identity.update(action.generator_count.to_le_bytes());
        identity.update(restriction.state_count.to_le_bytes());
        identity.update(restriction.transition_count.to_le_bytes());
        let identity_sha256 = identity
            .finalize()
            .iter()
            .map(|octet| format!("{octet:02x}"))
            .collect::<String>();
        let receipt = ResidentFactoredReceiverHistoryReceipt {
            schema: "holonic-engine.resident-factored-receiver-history.v1".to_owned(),
            identity_sha256,
            receiver_face_identity_sha256,
            restriction_atlas_identity_sha256: restriction.identity_sha256.clone(),
            generator_action_identity_sha256: action.identity_sha256.clone(),
            native_factor_population: self.factors,
            constitutive_family_population: self.families,
            receiver_population: self.receiver_count,
            receiver_class_population: action.receiver_class_count,
            generator_population: action.generator_count,
            boundary_state_population: restriction.state_count,
            boundary_transition_population: restriction.transition_count,
        };
        if let Some(mounted) = &self.factored_receiver_history {
            return if mounted.receipt == receipt {
                Ok(receipt)
            } else {
                Err(CudaRefineError::MembraneInteriorWordShape)
            };
        }
        self.factored_receiver_history = Some(ResidentFactoredReceiverHistoryMount {
            receipt: receipt.clone(),
            compression: None,
            current: None,
            image: None,
            sparse_pair: None,
            transported_image: None,
        });
        Ok(receipt)
    }

    /// Found the fixed symmetric pair-current from the entering addressed-current family.  The
    /// least generator-closed pair carrier and its inverse action incidence cross once; later
    /// recurrence changes only the resident exact coefficient current.
    pub fn mount_sparse_quadratic_moment_foundation(
        &mut self,
        contexts: &[AddressedCurrentSection],
        generator_targets: &[u32],
        generator_count: u32,
    ) -> Result<ResidentSparseQuadraticMomentFoundationReturn, CudaRefineError> {
        if contexts.is_empty() || generator_count == 0 {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        self.mount_quadratic_action(generator_count, generator_targets)?;
        self.found_factored_receiver_history()?;
        let family = contexts
            .iter()
            .map(|context| WeightedIntegralCurrent {
                weight: context.quadratic_weight.clone(),
                entries: context.factor_current.clone(),
            })
            .collect::<Vec<_>>();
        let generators = generator_targets
            .chunks_exact(self.factors as usize)
            .map(<[u32]>::to_vec)
            .collect::<Vec<_>>();
        if generators.len() != generator_count as usize
            || generator_targets.len() != generator_count as usize * self.factors as usize
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let foundation = SparseQuadraticMomentFoundation::found(self.factors, family, generators)
            .map_err(|_| CudaRefineError::MembraneInteriorWordShape)?;
        let pair_population = foundation.section.pairs.len();
        let state_ids_host = contexts
            .iter()
            .map(|context| context.boundary_state.unwrap_or(u32::MAX))
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        if state_ids_host.is_empty() || state_ids_host.len() > u32::MAX as usize {
            return Err(CudaRefineError::MembraneInteriorCurrentOutsideApparatus);
        }
        let state_coordinates = state_ids_host
            .iter()
            .copied()
            .enumerate()
            .map(|(coordinate, state)| (state, coordinate))
            .collect::<BTreeMap<_, _>>();
        let pair_coordinates = foundation
            .action
            .pairs
            .iter()
            .enumerate()
            .map(|(coordinate, pair)| ((pair.left, pair.right), coordinate))
            .collect::<BTreeMap<_, _>>();
        let mut state_coefficients = vec![
            BigUint::zero();
            state_ids_host.len().checked_mul(pair_population).ok_or(
                CudaRefineError::MembraneInteriorCurrentOutsideApparatus
            )?
        ];
        for context in contexts {
            let state = context.boundary_state.unwrap_or(u32::MAX);
            let state_coordinate = *state_coordinates
                .get(&state)
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            for (left_at, (left, left_coefficient)) in context.factor_current.iter().enumerate() {
                for (right, right_coefficient) in &context.factor_current[left_at..] {
                    let ordered = if left <= right {
                        (*left, *right)
                    } else {
                        (*right, *left)
                    };
                    let pair_coordinate = *pair_coordinates
                        .get(&ordered)
                        .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
                    state_coefficients[state_coordinate * pair_population + pair_coordinate] +=
                        &context.quadratic_weight * left_coefficient * right_coefficient;
                }
            }
        }
        let integrated_coefficients = (0..pair_population)
            .map(|pair| {
                (0..state_ids_host.len()).fold(BigUint::zero(), |sum, state| {
                    sum + &state_coefficients[state * pair_population + pair]
                })
            })
            .collect::<Vec<_>>();
        if integrated_coefficients != foundation.section.coefficients {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let relational_root_state = self
            .sparse_relational_current
            .as_ref()
            .filter(|current| current.bounded_i64_face_valid && current.state_count == 1)
            .map(|current| {
                state_coordinates
                    .get(&current.receipt.root_state)
                    .copied()
                    .ok_or(CudaRefineError::MembraneInteriorWordShape)
            })
            .transpose()?;
        let maximal_native_coefficient = state_coefficients
            .iter()
            .cloned()
            .max()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let maximal_native_situated_coefficient = foundation
            .section
            .coefficients
            .iter()
            .cloned()
            .max()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let maximal_coefficient = maximal_native_coefficient;
        let maximal_situated_receiver_coefficient = maximal_native_situated_coefficient;
        let coefficient_limb_count = maximal_coefficient
            .to_u32_digits()
            .len()
            .max(maximal_situated_receiver_coefficient.to_u32_digits().len())
            .max(1);
        let situated_receiver_limb_count = coefficient_limb_count;
        if pair_population == 0
            || pair_population > u32::MAX as usize
            || coefficient_limb_count > u32::MAX as usize
            || situated_receiver_limb_count > u32::MAX as usize
        {
            return Err(CudaRefineError::MembraneInteriorCurrentOutsideApparatus);
        }
        let mut coefficient_limbs = Vec::with_capacity(
            state_coefficients
                .len()
                .checked_mul(coefficient_limb_count)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        );
        for coefficient in &state_coefficients {
            let mut limbs = coefficient.to_u32_digits();
            limbs.resize(coefficient_limb_count, 0);
            coefficient_limbs.extend(limbs);
        }
        let mut situated_receiver_limbs = Vec::with_capacity(
            pair_population
                .checked_mul(situated_receiver_limb_count)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        );
        for coefficient in &foundation.section.coefficients {
            let mut limbs = coefficient.to_u32_digits();
            limbs.resize(situated_receiver_limb_count, 0);
            situated_receiver_limbs.extend(limbs);
        }
        let pair_factors = foundation
            .action
            .pairs
            .iter()
            .flat_map(|pair| [pair.left, pair.right])
            .collect::<Vec<_>>();
        let mut pair_row_offsets = vec![0_u64; self.factors as usize + 1];
        let mut pair_cursor = 0_usize;
        for left in 0..self.factors as usize {
            pair_row_offsets[left] = u64::try_from(pair_cursor)
                .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            while pair_cursor < foundation.action.pairs.len()
                && foundation.action.pairs[pair_cursor].left as usize == left
            {
                pair_cursor += 1;
            }
        }
        pair_row_offsets[self.factors as usize] = u64::try_from(pair_cursor)
            .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        if pair_cursor != pair_population {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }

        let mut incoming = vec![Vec::<(u32, u8)>::new(); pair_population];
        for (action_at, target) in foundation
            .action
            .target_pair_coordinates
            .iter()
            .copied()
            .enumerate()
        {
            incoming[target as usize].push((
                (action_at % pair_population) as u32,
                foundation.action.multiplicities[action_at],
            ));
        }
        let maximal_incoming_multiplicity = incoming
            .iter()
            .map(|edges| {
                edges
                    .iter()
                    .fold(BigUint::zero(), |sum, (_, multiplicity)| {
                        sum + BigUint::from(*multiplicity)
                    })
            })
            .max()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let mut target_offsets = Vec::with_capacity(pair_population + 1);
        let mut source_pairs = Vec::new();
        let mut multiplicities = Vec::new();
        target_offsets.push(0_u64);
        for edges in incoming {
            for (source, multiplicity) in edges {
                source_pairs.push(source);
                multiplicities.push(multiplicity);
            }
            target_offsets.push(
                u64::try_from(source_pairs.len())
                    .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
            );
        }
        let mut generator_target_offsets =
            Vec::with_capacity(generator_count as usize * (pair_population + 1));
        let mut generator_source_pairs = Vec::new();
        let mut generator_multiplicities = Vec::new();
        for generator in 0..generator_count as usize {
            let mut generator_incoming = vec![Vec::<(u32, u8)>::new(); pair_population];
            for source in 0..pair_population {
                let action_at = generator * pair_population + source;
                let target = foundation.action.target_pair_coordinates[action_at] as usize;
                generator_incoming[target]
                    .push((source as u32, foundation.action.multiplicities[action_at]));
            }
            generator_target_offsets.push(
                u64::try_from(generator_source_pairs.len())
                    .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
            );
            for edges in generator_incoming {
                for (source, multiplicity) in edges {
                    generator_source_pairs.push(source);
                    generator_multiplicities.push(multiplicity);
                }
                generator_target_offsets.push(
                    u64::try_from(generator_source_pairs.len())
                        .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
                );
            }
        }
        if generator_target_offsets.len() != generator_count as usize * (pair_population + 1)
            || generator_source_pairs.len() != generator_count as usize * pair_population
            || generator_multiplicities.len() != generator_source_pairs.len()
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let section_identity_sha256 = serde_json::to_vec(&(
            "holonic-engine.state-addressed-sparse-quadratic-section.v1",
            &state_ids_host,
            &foundation.section.pairs,
            &state_coefficients,
        ))
        .map(|bytes| {
            Sha256::digest(bytes)
                .iter()
                .map(|octet| format!("{octet:02x}"))
                .collect::<String>()
        })
        .map_err(|_| CudaRefineError::MembraneInteriorWordShape)?;
        let resident_octets = [
            std::mem::size_of_val(coefficient_limbs.as_slice()),
            std::mem::size_of_val(situated_receiver_limbs.as_slice()),
            std::mem::size_of_val(state_ids_host.as_slice()),
            std::mem::size_of_val(pair_factors.as_slice()),
            std::mem::size_of_val(pair_row_offsets.as_slice()),
            std::mem::size_of_val(target_offsets.as_slice()),
            std::mem::size_of_val(source_pairs.as_slice()),
            std::mem::size_of_val(multiplicities.as_slice()),
            std::mem::size_of_val(generator_target_offsets.as_slice()),
            std::mem::size_of_val(generator_source_pairs.as_slice()),
            std::mem::size_of_val(generator_multiplicities.as_slice()),
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
        let coefficients = Buffer::of(&coefficient_limbs)?;
        let situated_receiver_coefficients = Buffer::of(&situated_receiver_limbs)?;
        let pair_factors_device = Buffer::of(&pair_factors)?;
        let relational_current_receipt = relational_root_state.and_then(|_| {
            self.sparse_relational_current
                .as_ref()
                .map(|relational| relational.receipt.clone())
        });
        let mounted = self
            .factored_receiver_history
            .as_mut()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        if mounted.image.is_some()
            || mounted.sparse_pair.is_some()
            || mounted.transported_image.is_some()
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        mounted.current = None;
        mounted.sparse_pair = Some(ResidentSparseQuadraticMomentState {
            generation: 0,
            section_identity_sha256,
            state_population: state_ids_host.len() as u32,
            coefficient_state_capacity: state_ids_host.len() as u32,
            state_ids: Buffer::of(&state_ids_host)?,
            state_ids_host,
            factor_population: self.factors,
            pair_population: pair_population as u32,
            coefficient_limb_count: coefficient_limb_count as u32,
            maximal_coefficient,
            coefficients,
            situated_receiver_coefficients,
            situated_receiver_limb_count: situated_receiver_limb_count as u32,
            maximal_situated_receiver_coefficient,
            pair_factors: pair_factors_device,
            pair_row_offsets: Buffer::of(&pair_row_offsets)?,
            target_offsets: Buffer::of(&target_offsets)?,
            source_pairs: Buffer::of(&source_pairs)?,
            multiplicities: Buffer::of(&multiplicities)?,
            generator_target_offsets: Buffer::of(&generator_target_offsets)?,
            generator_source_pairs: Buffer::of(&generator_source_pairs)?,
            generator_multiplicities: Buffer::of(&generator_multiplicities)?,
            maximal_incoming_multiplicity,
            action: foundation.action.clone(),
            resident_octets,
        });
        self.mount_host_ingress_octets = self
            .mount_host_ingress_octets
            .checked_add(resident_octets)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let target_address = self.resident_sparse_quadratic_moment_address()?;
        if trace_configuration().holonics_phase_trace {
            eprintln!(
                "mem6-pair-foundation pair_population={} coefficient_limbs={} resident_octets={}",
                pair_population, coefficient_limb_count, resident_octets,
            );
        }
        Ok(ResidentSparseQuadraticMomentFoundationReturn {
            foundation,
            relational_current: relational_current_receipt,
            target_address,
            device: self.card.device_name.clone(),
            context_identity: self.card.context as usize,
            host_ingress_octets: resident_octets,
            resident_octets,
            source_current_retained_hot: false,
            ambient_covariance_materialized: false,
        })
    }

    /// Found the accumulated quadratic section directly from an ordered diagonal chronology.
    /// The device enacts the exact suffix-moment recurrence on one fixed complete pair carrier;
    /// no suffix row, rank-one history family, or ambient covariance crosses the hot boundary.
    pub fn mount_sparse_quadratic_diagonal_chronology_foundation(
        &mut self,
        chronology: &[AddressedDiagonalCurrentStep],
        generator_targets: &[u32],
        generator_count: u32,
    ) -> Result<ResidentSparseQuadraticChronologyFoundationReturn, CudaRefineError> {
        if chronology.is_empty()
            || chronology.len() > u32::MAX as usize
            || generator_count == 0
            || chronology.iter().any(|step| {
                step.entries.is_empty()
                    || step.entries.windows(2).any(|pair| pair[0].0 >= pair[1].0)
                    || step.entries.iter().any(|(factor, coefficient)| {
                        *factor >= self.factors
                            || coefficient.is_zero()
                            || coefficient.to_u32().is_none()
                    })
            })
            || chronology
                .windows(2)
                .any(|pair| pair[0].target_state != pair[1].source_state)
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        self.mount_quadratic_action(generator_count, generator_targets)?;
        self.found_factored_receiver_history()?;
        let generators = generator_targets
            .chunks_exact(self.factors as usize)
            .map(<[u32]>::to_vec)
            .collect::<Vec<_>>();
        if generators.len() != generator_count as usize
            || generator_targets.len() != generator_count as usize * self.factors as usize
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        if trace_configuration().holonics_phase_trace {
            eprintln!(
                "uar2-chronology-action-begin factors={} generators={} chronology={}",
                self.factors,
                generator_count,
                chronology.len(),
            );
        }
        let action =
            SparseQuadraticMomentAction::complete_symmetric(self.factors, generators.clone())
                .map_err(|_| CudaRefineError::MembraneInteriorWordShape)?;
        let pair_population = action.pairs.len();
        if pair_population == 0 || pair_population > u32::MAX as usize {
            return Err(CudaRefineError::MembraneInteriorCurrentOutsideApparatus);
        }
        if trace_configuration().holonics_phase_trace {
            eprintln!("uar2-chronology-action-derived pairs={pair_population}");
        }
        let action_ingress = derive_sparse_pair_action_ingress(&action)?;
        if trace_configuration().holonics_phase_trace {
            eprintln!(
                "uar2-chronology-action-ingress-derived aggregate_edges={} generator_edges={}",
                action_ingress.source_pairs.len(),
                action_ingress.generator_source_pairs.len(),
            );
        }

        let dense_population = chronology
            .len()
            .checked_mul(self.factors as usize)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let mut dense_chronology = vec![0_u32; dense_population];
        let mut standing_bound = BigUint::zero();
        let mut accumulated_bound = BigUint::zero();
        for (order, step) in chronology.iter().enumerate() {
            let mut maximal_step = 0_u32;
            for (factor, coefficient) in &step.entries {
                let coefficient = coefficient
                    .to_u32()
                    .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
                dense_chronology[order * self.factors as usize + *factor as usize] = coefficient;
                maximal_step = maximal_step.max(coefficient);
            }
            let maximal_scale = BigUint::from(maximal_step) * BigUint::from(maximal_step);
            standing_bound = &maximal_scale * (&standing_bound + BigUint::one());
            accumulated_bound += &standing_bound;
        }
        if accumulated_bound.is_zero() {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let coefficient_limb_count = accumulated_bound.to_u32_digits().len().max(1);
        if coefficient_limb_count > u32::MAX as usize {
            return Err(CudaRefineError::MembraneInteriorCurrentOutsideApparatus);
        }
        let coefficient_entries = pair_population
            .checked_mul(coefficient_limb_count)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let coefficient_octets = coefficient_entries
            .checked_mul(std::mem::size_of::<u32>())
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        if trace_configuration().holonics_phase_trace {
            eprintln!(
                "uar2-chronology-aperture-derived limbs={} coefficient_octets={}",
                coefficient_limb_count, coefficient_octets,
            );
        }

        let mut section_identity = Sha256::new();
        section_identity.update(b"holonic-engine.sparse-quadratic-diagonal-chronology-section.v1");
        section_identity.update(self.factors.to_le_bytes());
        section_identity.update(generator_count.to_le_bytes());
        for target in generator_targets {
            section_identity.update(target.to_le_bytes());
        }
        for step in chronology {
            section_identity.update(step.source_state.to_le_bytes());
            section_identity.update(step.target_state.to_le_bytes());
            section_identity.update((step.entries.len() as u64).to_le_bytes());
            for (factor, coefficient) in &step.entries {
                section_identity.update(factor.to_le_bytes());
                let limbs = coefficient.to_u32_digits();
                section_identity.update((limbs.len() as u64).to_le_bytes());
                for limb in limbs {
                    section_identity.update(limb.to_le_bytes());
                }
            }
        }
        let section_identity_sha256 = section_identity
            .finalize()
            .iter()
            .map(|octet| format!("{octet:02x}"))
            .collect::<String>();

        driver(
            unsafe { cuCtxSetCurrent(self.card.context) },
            "cuCtxSetCurrent",
        )?;
        let pair_factors = Buffer::of(&action_ingress.pair_factors)?;
        let diagonal_currents = Buffer::of(&dense_chronology)?;
        let standing = Buffer::alloc(coefficient_octets)?;
        let coefficients = Buffer::alloc(coefficient_octets)?;
        let situated_receiver_coefficients = Buffer::alloc(coefficient_octets)?;
        let overflow = Buffer::of(&[0_u32])?;
        if trace_configuration().holonics_phase_trace {
            eprintln!("uar2-chronology-device-buffers-mounted");
        }
        let mut pair_factors_pointer = pair_factors.pointer;
        let mut diagonal_currents_pointer = diagonal_currents.pointer;
        let mut standing_pointer = standing.pointer;
        let mut coefficients_pointer = coefficients.pointer;
        let mut overflow_pointer = overflow.pointer;
        let mut pair_population_wire = pair_population as u32;
        let mut factor_population_wire = self.factors;
        let mut chronology_population_wire = chronology.len() as u32;
        let mut coefficient_limb_count_wire = coefficient_limb_count as u32;
        let mut arguments: [*mut c_void; 9] = [
            &mut pair_factors_pointer as *mut u64 as *mut c_void,
            &mut diagonal_currents_pointer as *mut u64 as *mut c_void,
            &mut standing_pointer as *mut u64 as *mut c_void,
            &mut coefficients_pointer as *mut u64 as *mut c_void,
            &mut overflow_pointer as *mut u64 as *mut c_void,
            &mut pair_population_wire as *mut u32 as *mut c_void,
            &mut factor_population_wire as *mut u32 as *mut c_void,
            &mut chronology_population_wire as *mut u32 as *mut c_void,
            &mut coefficient_limb_count_wire as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card.membrane_sparse_quadratic_diagonal_chronology,
                    self.card.grid_for(pair_population as u64)?,
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
            "cuLaunchKernel(form_membrane_sparse_quadratic_diagonal_chronology)",
        )?;
        driver(
            unsafe {
                cuMemcpyDtoDAsync_v2(
                    situated_receiver_coefficients.pointer,
                    coefficients.pointer,
                    coefficient_octets,
                    ptr::null_mut(),
                )
            },
            "cuMemcpyDtoDAsync_v2(situated chronology receiver)",
        )?;
        self.card.launches = self
            .card
            .launches
            .checked_add(1)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
        if trace_configuration().holonics_phase_trace {
            eprintln!("uar2-chronology-device-recurrence-returned");
        }
        let mut overflow_value = [0_u32];
        overflow.read(&mut overflow_value)?;
        if overflow_value[0] != 0 {
            return Err(CudaRefineError::MembraneInteriorCurrentOutsideApparatus);
        }

        let resident_octets = [
            coefficient_octets,
            coefficient_octets,
            std::mem::size_of_val(action_ingress.pair_factors.as_slice()),
            std::mem::size_of_val(action_ingress.pair_row_offsets.as_slice()),
            std::mem::size_of_val(action_ingress.target_offsets.as_slice()),
            std::mem::size_of_val(action_ingress.source_pairs.as_slice()),
            std::mem::size_of_val(action_ingress.multiplicities.as_slice()),
            std::mem::size_of_val(action_ingress.generator_target_offsets.as_slice()),
            std::mem::size_of_val(action_ingress.generator_source_pairs.as_slice()),
            std::mem::size_of_val(action_ingress.generator_multiplicities.as_slice()),
        ]
        .into_iter()
        .try_fold(0_u64, |sum, octets| {
            sum.checked_add(u64::try_from(octets).ok()?)
        })
        .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let host_ingress_octets = [
            std::mem::size_of_val(dense_chronology.as_slice()),
            std::mem::size_of_val(action_ingress.pair_factors.as_slice()),
            std::mem::size_of_val(action_ingress.pair_row_offsets.as_slice()),
            std::mem::size_of_val(action_ingress.target_offsets.as_slice()),
            std::mem::size_of_val(action_ingress.source_pairs.as_slice()),
            std::mem::size_of_val(action_ingress.multiplicities.as_slice()),
            std::mem::size_of_val(action_ingress.generator_target_offsets.as_slice()),
            std::mem::size_of_val(action_ingress.generator_source_pairs.as_slice()),
            std::mem::size_of_val(action_ingress.generator_multiplicities.as_slice()),
        ]
        .into_iter()
        .try_fold(0_u64, |sum, octets| {
            sum.checked_add(u64::try_from(octets).ok()?)
        })
        .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;

        let mounted = self
            .factored_receiver_history
            .as_mut()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        if mounted.image.is_some()
            || mounted.sparse_pair.is_some()
            || mounted.transported_image.is_some()
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        mounted.current = None;
        mounted.sparse_pair = Some(ResidentSparseQuadraticMomentState {
            generation: 0,
            section_identity_sha256,
            state_population: 1,
            coefficient_state_capacity: 1,
            state_ids_host: vec![u32::MAX],
            state_ids: Buffer::of(&[u32::MAX])?,
            factor_population: self.factors,
            pair_population: pair_population as u32,
            coefficient_limb_count: coefficient_limb_count as u32,
            maximal_coefficient: accumulated_bound.clone(),
            coefficients,
            situated_receiver_coefficients,
            situated_receiver_limb_count: coefficient_limb_count as u32,
            maximal_situated_receiver_coefficient: accumulated_bound,
            pair_factors,
            pair_row_offsets: Buffer::of(&action_ingress.pair_row_offsets)?,
            target_offsets: Buffer::of(&action_ingress.target_offsets)?,
            source_pairs: Buffer::of(&action_ingress.source_pairs)?,
            multiplicities: Buffer::of(&action_ingress.multiplicities)?,
            generator_target_offsets: Buffer::of(&action_ingress.generator_target_offsets)?,
            generator_source_pairs: Buffer::of(&action_ingress.generator_source_pairs)?,
            generator_multiplicities: Buffer::of(&action_ingress.generator_multiplicities)?,
            maximal_incoming_multiplicity: action_ingress.maximal_incoming_multiplicity,
            action,
            resident_octets,
        });
        self.mount_host_ingress_octets = self
            .mount_host_ingress_octets
            .checked_add(host_ingress_octets)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let target_address = self.resident_sparse_quadratic_moment_address()?;
        if trace_configuration().holonics_phase_trace {
            eprintln!(
                "uar2-chronology-foundation chronology={} pairs={} coefficient_limbs={} resident_octets={}",
                chronology.len(),
                pair_population,
                coefficient_limb_count,
                resident_octets,
            );
        }
        Ok(ResidentSparseQuadraticChronologyFoundationReturn {
            schema: "holonic-engine.resident-sparse-quadratic-chronology-foundation-return.v1"
                .to_owned(),
            chronology_reconstruction_fibre: chronology.to_vec(),
            generator_targets: generators,
            target_address,
            device: self.card.device_name.clone(),
            context_identity: self.card.context as usize,
            chronology_population: chronology.len() as u32,
            pair_population: pair_population as u32,
            coefficient_limb_count: coefficient_limb_count as u32,
            host_ingress_octets,
            resident_octets,
            source_current_retained_hot: false,
            ambient_covariance_materialized: false,
            terminal_synchronizations: 1,
        })
    }

    /// Found the quadratic image once from the entering addressed-current family and mount only
    /// its exact incidence/constitutive section as the continuing resident occurrence.  The
    /// returned foundation owns the complete cold reconstruction fibre.
    pub fn mount_factored_moment_foundation(
        &mut self,
        contexts: &[AddressedCurrentSection],
        generator_targets: &[u32],
        generator_count: u32,
    ) -> Result<ResidentFactoredMomentFoundationReturn, CudaRefineError> {
        if contexts.is_empty() {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        self.mount_quadratic_action(generator_count, generator_targets)?;
        self.found_factored_receiver_history()?;
        let family = contexts
            .iter()
            .map(|context| WeightedIntegralCurrent {
                weight: context.quadratic_weight.clone(),
                entries: context.factor_current.clone(),
            })
            .collect::<Vec<_>>();
        let foundation = FactoredMomentSection::found(self.factors, family)
            .map_err(|_| CudaRefineError::MembraneInteriorWordShape)?;
        let host_ingress_octets = self.mount_factored_moment_state(&foundation.section)?;
        let target_address = self.resident_factored_moment_address()?;
        let resident_octets = self
            .factored_receiver_history
            .as_ref()
            .and_then(|mount| mount.image.as_ref())
            .map(|image| {
                image
                    .incidence
                    .resident_octets
                    .saturating_add(image.constitutive.resident_octets)
            })
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        Ok(ResidentFactoredMomentFoundationReturn {
            foundation,
            target_address,
            device: self.card.device_name.clone(),
            context_identity: self.card.context as usize,
            host_ingress_octets,
            resident_octets,
            source_current_retained_hot: false,
            ambient_covariance_materialized: false,
        })
    }

    fn mount_factored_moment_state(
        &mut self,
        section: &FactoredMomentSection,
    ) -> Result<u64, CudaRefineError> {
        section
            .validate_admitted()
            .map_err(|_| CudaRefineError::MembraneInteriorWordShape)?;
        let mounted = self
            .factored_receiver_history
            .as_ref()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        if mounted.image.is_some() {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        if section.factor_population != self.factors {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        driver(
            unsafe { cuCtxSetCurrent(self.card.context) },
            "cuCtxSetCurrent",
        )?;
        let incidence = ResidentExactRationalMatrix::mount(&section.incidence)?;
        let constitutive = ResidentExactRationalMatrix::mount(&section.constitutive)?;
        if incidence.rows != section.image_rank
            || incidence.columns != section.factor_population
            || constitutive.rows != section.image_rank
            || constitutive.columns != section.image_rank
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let ingress = incidence
            .resident_octets
            .checked_add(constitutive.resident_octets)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let mounted = self
            .factored_receiver_history
            .as_mut()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        // The exact foundation is the single ownership pivot from source-current presentation to
        // native image rest. Buffers are allocated and validated above before the former hot
        // presentation is released; the complete source family remains in the returned cold
        // reconstruction fibre.
        mounted.current = None;
        mounted.image = Some(ResidentFactoredMomentState {
            generation: 0,
            section_identity_sha256: factored_moment_section_identity(section),
            factor_population: section.factor_population,
            productive_population: section.image_rank,
            compact_generation: 0,
            image_rank: section.image_rank,
            basis_factors: section.basis_factors.clone(),
            incidence,
            constitutive,
            constitutive_spine: None,
        });
        self.mount_host_ingress_octets = self
            .mount_host_ingress_octets
            .checked_add(ingress)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        Ok(ingress)
    }

    pub(super) fn resident_factored_moment_address(
        &self,
    ) -> Result<ResidentFactoredMomentAddress, CudaRefineError> {
        let mounted = self
            .factored_receiver_history
            .as_ref()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let image = mounted
            .image
            .as_ref()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        image.incidence.validate_layout()?;
        image.constitutive.validate_layout()?;
        if let Some(spine) = &image.constitutive_spine {
            spine.validate_layout(image.factor_population)?;
        }
        if image.basis_factors.len() != image.image_rank as usize
            || image
                .basis_factors
                .iter()
                .any(|factor| *factor >= image.factor_population)
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        if image.productive_population == 0 || image.compact_generation > image.generation {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        Ok(ResidentFactoredMomentAddress {
            operation_complex_identity_sha256: mounted.receipt.identity_sha256.clone(),
            section_identity_sha256: image.section_identity_sha256.clone(),
            device_context_identity: self.card.context as usize,
            generation: image.generation,
            factor_population: image.factor_population,
            image_population: image.productive_population,
        })
    }

    pub(super) fn resident_sparse_quadratic_moment_address(
        &self,
    ) -> Result<ResidentFactoredMomentAddress, CudaRefineError> {
        let mounted = self
            .factored_receiver_history
            .as_ref()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let pair = mounted
            .sparse_pair
            .as_ref()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        if pair.factor_population != self.factors
            || pair.state_population == 0
            || pair.coefficient_state_capacity < pair.state_population
            || pair.state_ids_host.len() != pair.state_population as usize
            || pair.state_ids.pointer == 0
            || pair.pair_population == 0
            || pair.coefficient_limb_count == 0
            || pair.coefficients.pointer == 0
            || pair.situated_receiver_coefficients.pointer == 0
            || pair.situated_receiver_limb_count == 0
            || pair.maximal_situated_receiver_coefficient.is_zero()
            || pair.pair_factors.pointer == 0
            || pair.pair_row_offsets.pointer == 0
            || pair.target_offsets.pointer == 0
            || pair.source_pairs.pointer == 0
            || pair.multiplicities.pointer == 0
            || pair.action.pairs.len() != pair.pair_population as usize
            || pair.action.factor_population != pair.factor_population
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        Ok(ResidentFactoredMomentAddress {
            operation_complex_identity_sha256: mounted.receipt.identity_sha256.clone(),
            section_identity_sha256: pair.section_identity_sha256.clone(),
            device_context_identity: self.card.context as usize,
            generation: pair.generation,
            factor_population: pair.factor_population,
            image_population: pair.pair_population,
        })
    }

    pub(super) fn reduce_sparse_quadratic_signed_sections(
        &mut self,
        input_signs: &Buffer,
        input_limbs: &Buffer,
        scratch_signs: &Buffer,
        scratch_limbs: &Buffer,
        output_signs: &Buffer,
        output_limbs: &Buffer,
        section_count: usize,
        input_count_per_section: usize,
        limb_count: usize,
    ) -> Result<u64, CudaRefineError> {
        const SIGNED_SECTION_REDUCTION_CHUNK: usize = 1024;
        if section_count == 0 || input_count_per_section == 0 || limb_count == 0 {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let mut input_sign_pointer = input_signs.pointer;
        let mut input_limb_pointer = input_limbs.pointer;
        let mut input_count = input_count_per_section;
        let mut scratch_is_next = true;
        let mut launches = 0_u64;
        loop {
            let output_count = input_count.div_ceil(SIGNED_SECTION_REDUCTION_CHUNK);
            let terminal = output_count == 1;
            let mut output_sign_pointer = if terminal {
                output_signs.pointer
            } else if scratch_is_next {
                scratch_signs.pointer
            } else {
                input_signs.pointer
            };
            let mut output_limb_pointer = if terminal {
                output_limbs.pointer
            } else if scratch_is_next {
                scratch_limbs.pointer
            } else {
                input_limbs.pointer
            };
            let mut section_count_wire = section_count as u32;
            let mut input_count_wire = input_count as u32;
            let mut output_count_wire = output_count as u32;
            let mut reduction_chunk_wire = SIGNED_SECTION_REDUCTION_CHUNK as u32;
            let mut limb_count_wire = limb_count as u32;
            let mut arguments: [*mut c_void; 9] = [
                &mut input_sign_pointer as *mut u64 as *mut c_void,
                &mut input_limb_pointer as *mut u64 as *mut c_void,
                &mut output_sign_pointer as *mut u64 as *mut c_void,
                &mut output_limb_pointer as *mut u64 as *mut c_void,
                &mut section_count_wire as *mut u32 as *mut c_void,
                &mut input_count_wire as *mut u32 as *mut c_void,
                &mut output_count_wire as *mut u32 as *mut c_void,
                &mut reduction_chunk_wire as *mut u32 as *mut c_void,
                &mut limb_count_wire as *mut u32 as *mut c_void,
            ];
            let work = section_count
                .checked_mul(output_count)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            driver(
                unsafe {
                    cuLaunchKernel(
                        self.card.membrane_sparse_quadratic_signed_reduce,
                        self.card.grid_for(work as u64)?,
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
                "cuLaunchKernel(reduce_membrane_sparse_quadratic_signed_sections)",
            )?;
            launches = launches
                .checked_add(1)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            if terminal {
                break;
            }
            input_sign_pointer = output_sign_pointer;
            input_limb_pointer = output_limb_pointer;
            input_count = output_count;
            scratch_is_next = !scratch_is_next;
        }
        Ok(launches)
    }

    /// Deterministically add independent nonnegative interval sections on the resident device.
    /// The interval construction has already rounded every term outward; this passage performs
    /// only exact base-2^32 addition and reports overflow through the dedicated certificate
    /// obstruction.  It never returns a host partial or substitutes a scalar reduction.
    pub(super) fn reduce_sparse_quadratic_unsigned_intervals(
        &mut self,
        input: &Buffer,
        scratch: &Buffer,
        output: &Buffer,
        section_count: usize,
        input_count_per_section: usize,
        limb_count: usize,
        obstruction: &Buffer,
    ) -> Result<u64, CudaRefineError> {
        const UNSIGNED_INTERVAL_REDUCTION_CHUNK: usize = 1024;
        if section_count == 0 || input_count_per_section == 0 || limb_count == 0 {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let mut input_pointer = input.pointer;
        let mut input_count = input_count_per_section;
        let mut scratch_is_next = true;
        let mut launches = 0_u64;
        loop {
            let output_count = input_count.div_ceil(UNSIGNED_INTERVAL_REDUCTION_CHUNK);
            let terminal = output_count == 1;
            let mut output_pointer = if terminal {
                output.pointer
            } else if scratch_is_next {
                scratch.pointer
            } else {
                input.pointer
            };
            let mut section_count_wire = section_count as u32;
            let mut input_count_wire = input_count as u32;
            let mut output_count_wire = output_count as u32;
            let mut reduction_chunk_wire = UNSIGNED_INTERVAL_REDUCTION_CHUNK as u32;
            let mut limb_count_wire = limb_count as u32;
            let mut obstruction_pointer = obstruction.pointer;
            let mut arguments: [*mut c_void; 8] = [
                &mut input_pointer as *mut u64 as *mut c_void,
                &mut output_pointer as *mut u64 as *mut c_void,
                &mut section_count_wire as *mut u32 as *mut c_void,
                &mut input_count_wire as *mut u32 as *mut c_void,
                &mut output_count_wire as *mut u32 as *mut c_void,
                &mut reduction_chunk_wire as *mut u32 as *mut c_void,
                &mut limb_count_wire as *mut u32 as *mut c_void,
                &mut obstruction_pointer as *mut u64 as *mut c_void,
            ];
            let work = section_count
                .checked_mul(output_count)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            driver(
                unsafe {
                    cuLaunchKernel(
                        self.card.membrane_sparse_quadratic_unsigned_interval_reduce,
                        self.card.grid_for(work as u64)?,
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
                "cuLaunchKernel(reduce_membrane_sparse_quadratic_unsigned_intervals)",
            )?;
            launches = launches
                .checked_add(1)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            if terminal {
                break;
            }
            input_pointer = output_pointer;
            input_count = output_count;
            scratch_is_next = !scratch_is_next;
        }
        Ok(launches)
    }
}
