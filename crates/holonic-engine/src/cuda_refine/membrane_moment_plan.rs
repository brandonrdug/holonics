use super::*;

pub(super) struct MomentFrontAdmission<'a> {
    pub(super) factored_receiver_history: ResidentFactoredReceiverHistoryReceipt,
    pub(super) resident_current: Option<ResidentCurrentAddress>,
    pub(super) direct_restrictions: Option<&'a [ResidentQuadraticMomentRestriction]>,
    pub(super) resident_boundary: Option<&'a ResidentBoundaryRestrictionFront>,
    pub(super) resident_rectangular_restrictions: bool,
    pub(super) restriction_count: usize,
}

pub(super) struct MomentResidentContextState {
    pub(super) context_count: u32,
    pub(super) current_limbs_pointer: u64,
    pub(super) weight_limbs_pointer: u64,
    pub(super) boundary_state_present_pointer: u64,
    pub(super) boundary_states_pointer: u64,
    pub(super) current_limb_count: u32,
    pub(super) weight_limb_count: u32,
    pub(super) active_factors: Vec<u32>,
    pub(super) maximal_current: BigUint,
    pub(super) maximal_weight: BigUint,
}

pub(super) struct MomentFrontPlan<'a> {
    pub(super) post_target_observer: bool,
    pub(super) factored_receiver_history: ResidentFactoredReceiverHistoryReceipt,
    pub(super) resident_current: Option<ResidentCurrentAddress>,
    pub(super) resident_boundary: Option<&'a ResidentBoundaryRestrictionFront>,
    pub(super) resident_rectangular_restrictions: bool,
    pub(super) restriction_count: usize,
    pub(super) resident_context_state: Option<MomentResidentContextState>,
    pub(super) native_factors: usize,
    pub(super) factors: usize,
    pub(super) port_population: usize,
    pub(super) generator_count: usize,
    pub(super) port_restriction_offsets: Vec<u64>,
    pub(super) context_count: usize,
    pub(super) active_factors: Vec<u32>,
    pub(super) active_generator_targets: Vec<u32>,
    pub(super) active_generator_local_targets: Vec<u32>,
    pub(super) context_limb_count: usize,
    pub(super) restriction_limb_count: usize,
    pub(super) weight_limb_count: usize,
    pub(super) current_factor_population: usize,
    pub(super) context_current_limbs: Vec<u32>,
    pub(super) restriction_current_limbs: Vec<u32>,
    pub(super) context_weight_limbs: Vec<u32>,
    pub(super) restriction_ports: Vec<u32>,
    pub(super) maximal_context: BigUint,
    pub(super) relational_current_aperture: Option<(
        ResidentSparseRelationalCurrentReceipt,
        u64,
        u64,
        usize,
        u64,
        u64,
        u64,
        u64,
        usize,
        BigUint,
    )>,
    pub(super) moment_limb_count: usize,
    pub(super) overlap_limb_count: usize,
    pub(super) contact_limb_count: usize,
    pub(super) radiation_limb_count: usize,
    pub(super) compatibility_limb_count: usize,
    pub(super) norm_limb_count: usize,
    pub(super) square_limb_count: usize,
    pub(super) cross_limb_count: usize,
    pub(super) situated_pairing_limb_count: usize,
    pub(super) stored_limb_count: usize,
    pub(super) joint_scale: u64,
    pub(super) balance_denominator: BigInt,
    pub(super) incoming_real_sign: u8,
    pub(super) incoming_real_limbs: Vec<u32>,
    pub(super) incoming_imaginary_sign: u8,
    pub(super) incoming_imaginary_limbs: Vec<u32>,
    pub(super) product_limb_count: usize,
    pub(super) quadratic_limb_count: usize,
    pub(super) component_count: u32,
    pub(super) descend_boundary_state_receiver: bool,
    pub(super) local_response_population: usize,
    pub(super) response_population: usize,
    pub(super) component_population: usize,
    pub(super) moment_population: usize,
    pub(super) axis_count: usize,
    pub(super) contraction_work: usize,
    pub(super) context_chunk_size: usize,
    pub(super) context_chunk_count: usize,
    pub(super) incidence_chunk_size: usize,
    pub(super) incidence_chunk_count: usize,
    pub(super) legacy_restriction_allocation_count: usize,
    pub(super) contribution_work: usize,
    pub(super) family_population: usize,
    pub(super) receiver_population: usize,
    pub(super) maximal_generator_preimage: usize,
}

pub(super) fn admit_moment_front<'a>(
    word: &mut ResidentMembraneInteriorWord,
    front: &'a ResidentQuadraticMomentFront,
    port_population: usize,
    entering_current: &ExactComplexWaveCurrent,
) -> Result<MomentFrontAdmission<'a>, CudaRefineError> {
    let phase_trace = trace_configuration().holonics_phase_trace;
    let native_factors = word.factors as usize;
    let generator_count = front.generator_count as usize;
    if port_population == 0
        || port_population > u32::MAX as usize
        || native_factors == 0
        || generator_count == 0
        || front.generator_targets.len() != generator_count.saturating_mul(native_factors)
        || front
            .generator_targets
            .iter()
            .any(|target| *target >= word.factors)
        || word.receiver_count == 0
        || entering_current.is_zero()
    {
        return Err(CudaRefineError::MembraneInteriorWordShape);
    }
    if phase_trace {
        eprintln!(
            "mem6-front-admission entered contexts={} resident={:?} ports={} generators={}",
            front.contexts.len(),
            front
                .resident_source
                .as_ref()
                .map(|address| (address.generation, address.section_population,)),
            port_population,
            generator_count,
        );
    }
    word.mount_quadratic_action(front.generator_count, &front.generator_targets)?;
    if phase_trace {
        eprintln!("mem6-front-admission action");
    }
    let factored_receiver_history = word.found_factored_receiver_history()?;
    if phase_trace {
        eprintln!("mem6-front-admission receiver-history");
    }
    let resident_current = match &front.restrictions {
        ResidentQuadraticMomentRestrictionSource::ResidentBoundary(_) => {
            match &front.resident_source {
                Some(address) => {
                    word.validate_resident_current_address(address)?;
                    if front.contexts.len() != address.section_population {
                        if phase_trace {
                            eprintln!(
                                "mem6-front-admission address-population-refused contexts={} address={}",
                                front.contexts.len(),
                                address.section_population,
                            );
                        }
                        return Err(CudaRefineError::MembraneInteriorWordShape);
                    }
                    Some(address.clone())
                }
                None => Some(word.mount_factored_current_state(&front.contexts)?.1),
            }
        }
        ResidentQuadraticMomentRestrictionSource::DirectWitness(_) => {
            if front.contexts.is_empty() || front.resident_source.is_some() {
                return Err(CudaRefineError::MembraneInteriorWordShape);
            }
            None
        }
    };
    if phase_trace {
        eprintln!("mem6-front-admission current-address");
    }
    let (direct_restrictions, resident_boundary) = match &front.restrictions {
        ResidentQuadraticMomentRestrictionSource::DirectWitness(restrictions) => {
            (Some(restrictions.as_slice()), None)
        }
        ResidentQuadraticMomentRestrictionSource::ResidentBoundary(boundary) => {
            word.boundary_restriction_atlas
                .as_ref()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            (None, Some(boundary))
        }
    };
    let resident_rectangular_restrictions = resident_boundary.is_some();
    let restriction_count = if let Some(restrictions) = direct_restrictions {
        restrictions.len()
    } else {
        resident_boundary
            .expect("the restriction source has one exact presentation")
            .boundary_states
            .len()
            .checked_mul(port_population)
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?
    };
    if restriction_count == 0 || restriction_count > u32::MAX as usize {
        return Err(CudaRefineError::MembraneInteriorWordShape);
    }
    Ok(MomentFrontAdmission {
        factored_receiver_history,
        resident_current,
        direct_restrictions,
        resident_boundary,
        resident_rectangular_restrictions,
        restriction_count,
    })
}

pub(super) fn observe_completed_target(
    word: &mut ResidentMembraneInteriorWord,
    admission: &MomentFrontAdmission<'_>,
    front: &ResidentQuadraticMomentFront,
    port_population: usize,
    entering_current: &ExactComplexWaveCurrent,
    materialize_moment_field: bool,
    completed_step: Option<&ResidentCompletedTargetObservationAperture>,
) -> Result<Option<ResidentQuadraticMomentReturn>, CudaRefineError> {
    if completed_step.is_some()
        || !admission.resident_rectangular_restrictions
        || materialize_moment_field
    {
        return Ok(None);
    }
    let generator_count = front.generator_count as usize;
    let boundary = admission
        .resident_boundary
        .ok_or(CudaRefineError::MembraneInteriorWordShape)?
        .clone();
    let source_address = admission
        .resident_current
        .as_ref()
        .ok_or(CudaRefineError::MembraneInteriorWordShape)?
        .clone();
    let completed = word.found_complete_resident_generated_port_successor(
        front,
        port_population,
        &boundary,
        &source_address,
    )?;
    let local_face_population = port_population
        .checked_mul(generator_count)
        .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
    let source_state_coordinates = boundary
        .boundary_states
        .iter()
        .enumerate()
        .map(|(coordinate, state)| (*state, coordinate))
        .collect::<BTreeMap<_, _>>();
    let mut complete_successor_faces = completed
        .returned
        .passage
        .slots
        .iter()
        .map(|slot| {
            let state = source_state_coordinates
                .get(&slot.source_boundary_state)
                .copied()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            state
                .checked_mul(local_face_population)
                .and_then(|base| {
                    base.checked_add(
                        (slot.port as usize)
                            .checked_mul(generator_count)?
                            .checked_add(slot.generator as usize)?,
                    )
                })
                .and_then(|face| u32::try_from(face).ok())
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)
        })
        .collect::<Result<Vec<_>, _>>()?;
    complete_successor_faces.sort_unstable();
    complete_successor_faces.dedup();
    let complete_successor_face_population = boundary
        .boundary_states
        .len()
        .checked_mul(local_face_population)
        .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
    let target_boundary_states = completed
        .returned
        .passage
        .target
        .iter()
        .filter_map(|section| section.boundary_state)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    if target_boundary_states.is_empty() {
        return Err(CudaRefineError::MembraneInteriorWordShape);
    }
    let observer_front = ResidentQuadraticMomentFront {
        contexts: completed.returned.passage.target.clone(),
        resident_source: Some(completed.returned.target_address.clone()),
        resident_image: None,
        restrictions: ResidentQuadraticMomentRestrictionSource::ResidentBoundary(
            ResidentBoundaryRestrictionFront {
                boundary_states: target_boundary_states,
                universal_ports: boundary.universal_ports,
            },
        ),
        generator_targets: front.generator_targets.clone(),
        generator_count: front.generator_count,
        // The current step has already enacted its presented generator occurrence. The
        // downstream observer retains the complete rested face chart and cannot select
        // or rewrite that committed target.
        presented_current: None,
    };
    let mut observed = word.conduct_quadratic_moment_front_inner(
        &observer_front,
        port_population,
        entering_current,
        false,
        Some(completed),
    )?;
    observed.complete_successor_faces = complete_successor_faces;
    observed.complete_successor_face_population = complete_successor_face_population;
    Ok(Some(observed))
}

impl<'a> MomentFrontAdmission<'a> {
    pub(super) fn complete(
        self,
        word: &ResidentMembraneInteriorWord,
        front: &'a ResidentQuadraticMomentFront,
        port_population: usize,
        entering_current: &ExactComplexWaveCurrent,
        materialize_moment_field: bool,
        completed_step: Option<&ResidentCompletedTargetObservationAperture>,
    ) -> Result<MomentFrontPlan<'a>, CudaRefineError> {
        let MomentFrontAdmission {
            factored_receiver_history,
            resident_current,
            direct_restrictions,
            resident_boundary,
            resident_rectangular_restrictions,
            restriction_count,
        } = self;
        // With its relational-current chart present, observe the committed target directly;
        // applying its outgoing restrictions again would change the receiver consequence.
        // Without that chart, the ordinary contraction observes the completed factor-current
        // section. A front with no completed step still follows its original transport path.
        let post_target_observer =
            completed_step.is_some() && word.sparse_relational_current.is_some();
        let native_factors = word.factors as usize;
        let generator_count = front.generator_count as usize;

        let phase_trace = trace_configuration().holonics_phase_trace;
        let resident_atlas = word.boundary_restriction_atlas.as_ref();
        let resident_context_state = if resident_current.is_some() {
            let state = word
                .factored_receiver_history
                .as_ref()
                .and_then(|mounted| mounted.current.as_ref())
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            Some(MomentResidentContextState {
                context_count: state.context_count,
                current_limbs_pointer: state.current_limbs.pointer,
                weight_limbs_pointer: state.weight_limbs.pointer,
                boundary_state_present_pointer: state.boundary_state_present.pointer,
                boundary_states_pointer: state.boundary_states.pointer,
                current_limb_count: state.current_limb_count,
                weight_limb_count: state.weight_limb_count,
                active_factors: state.active_factors.clone(),
                maximal_current: state.maximal_current.clone(),
                maximal_weight: state.maximal_weight.clone(),
            })
        } else {
            None
        };
        let valid_current = |current: &[(u32, BigUint)]| {
            !current.is_empty()
                && !current.windows(2).any(|pair| pair[0].0 >= pair[1].0)
                && !current
                    .iter()
                    .any(|(factor, coefficient)| *factor >= word.factors || coefficient.is_zero())
        };
        if resident_context_state.is_none()
            && front.contexts.iter().any(|context| {
                context.quadratic_weight.is_zero() || !valid_current(&context.factor_current)
            })
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let context_count = resident_context_state
            .as_ref()
            .map(|state| state.context_count as usize)
            .unwrap_or(front.contexts.len());
        let context_support = if let Some(state) = resident_context_state.as_ref() {
            state
                .active_factors
                .iter()
                .copied()
                .collect::<BTreeSet<_>>()
        } else {
            front
                .contexts
                .iter()
                .flat_map(|context| context.factor_current.iter().map(|(factor, _)| *factor))
                .collect::<BTreeSet<_>>()
        };
        if phase_trace {
            eprintln!(
                "mem6-front-admission context-support={} context-count={}",
                context_support.len(),
                context_count,
            );
        }
        let cuda_profile = trace_configuration().mem6_cuda_profile;
        if cuda_profile {
            eprintln!(
                "mem6-cuda receiver_class_counts={:?} factors={} contexts={} restrictions={}",
                word.receiver_class_counts.as_deref().unwrap_or_default(),
                native_factors,
                context_count,
                restriction_count,
            );
        }
        let restriction_support = if let Some(restrictions) = direct_restrictions {
            if restrictions.iter().any(|restriction| {
                restriction.port as usize >= port_population
                    || !valid_current(&restriction.factor_current)
            }) || restrictions
                .iter()
                .map(|restriction| restriction.port)
                .collect::<BTreeSet<_>>()
                .len()
                != port_population
            {
                return Err(CudaRefineError::MembraneInteriorWordShape);
            }
            restrictions
                .iter()
                .flat_map(|restriction| {
                    restriction.factor_current.iter().map(|(factor, _)| *factor)
                })
                .collect::<BTreeSet<_>>()
        } else {
            let boundary = resident_boundary.ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let atlas = resident_atlas.ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            if materialize_moment_field
                || boundary.boundary_states.is_empty()
                || boundary.universal_ports.len() != port_population
                || boundary
                    .boundary_states
                    .windows(2)
                    .any(|pair| pair[0] >= pair[1])
                || boundary
                    .universal_ports
                    .iter()
                    .collect::<BTreeSet<_>>()
                    .len()
                    != port_population
                || boundary
                    .boundary_states
                    .iter()
                    .any(|state| *state >= atlas.state_count)
                || boundary
                    .universal_ports
                    .iter()
                    .any(|port| *port >= atlas.universal_port_count)
            {
                return Err(CudaRefineError::MembraneInteriorWordShape);
            }
            // The production contraction remains in the complete native factor chart.  This set
            // only reports the context aperture and never selects or rebuilds a restriction.
            context_support.clone()
        };
        if phase_trace {
            eprintln!(
                "mem6-front-admission restriction-support={} restrictions={}",
                restriction_support.len(),
                restriction_count,
            );
        }
        let active_factors = context_support
            .intersection(&restriction_support)
            .copied()
            .collect::<Vec<_>>();
        if active_factors.is_empty() {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        if phase_trace {
            eprintln!(
                "mem6-front-admission active-factors={}",
                active_factors.len()
            );
        }
        let active_lookup = active_factors
            .iter()
            .enumerate()
            .map(|(local, global)| (*global, local as u32))
            .collect::<BTreeMap<_, _>>();
        let factors = active_factors.len();
        let mut ordered_restrictions = direct_restrictions
            .unwrap_or_default()
            .iter()
            .collect::<Vec<_>>();
        ordered_restrictions.sort_by_key(|restriction| restriction.port);
        let mut port_restriction_offsets = Vec::with_capacity(port_population + 1);
        port_restriction_offsets.push(0_u64);
        let mut restriction_cursor = 0_usize;
        if resident_rectangular_restrictions {
            let boundary_state_count = resident_boundary
                .expect("the resident presentation was established")
                .boundary_states
                .len();
            for port in 1..=port_population {
                port_restriction_offsets.push(
                    u64::try_from(port.saturating_mul(boundary_state_count))
                        .map_err(|_| CudaRefineError::MembraneInteriorWordShape)?,
                );
            }
        } else {
            for port in 0..port_population as u32 {
                while restriction_cursor < ordered_restrictions.len()
                    && ordered_restrictions[restriction_cursor].port == port
                {
                    restriction_cursor += 1;
                }
                port_restriction_offsets.push(
                    u64::try_from(restriction_cursor)
                        .map_err(|_| CudaRefineError::MembraneInteriorWordShape)?,
                );
            }
            if restriction_cursor != ordered_restrictions.len() {
                return Err(CudaRefineError::MembraneInteriorWordShape);
            }
        }
        let (active_generator_targets, active_generator_local_targets) = if materialize_moment_field
        {
            let mut targets = Vec::with_capacity(generator_count * factors);
            let mut local_targets = Vec::with_capacity(generator_count * factors);
            for generator in 0..generator_count {
                for source in &active_factors {
                    let target =
                        front.generator_targets[generator * native_factors + *source as usize];
                    targets.push(target);
                    local_targets.push(active_lookup.get(&target).copied().unwrap_or(u32::MAX));
                }
            }
            (targets, local_targets)
        } else {
            (Vec::new(), Vec::new())
        };

        let context_limb_count = resident_context_state
            .as_ref()
            .map(|state| state.current_limb_count as usize)
            .unwrap_or_else(|| {
                front
                    .contexts
                    .iter()
                    .flat_map(|context| &context.factor_current)
                    .map(|(_, value)| value.to_u32_digits().len())
                    .max()
                    .unwrap_or(1)
                    .max(1)
            });
        let restriction_limb_count = if let Some(restrictions) = direct_restrictions {
            restrictions
                .iter()
                .flat_map(|restriction| &restriction.factor_current)
                .map(|(_, value)| value.to_u32_digits().len())
                .max()
                .unwrap_or(1)
                .max(1)
        } else {
            resident_atlas
                .expect("the resident presentation was established")
                .restriction_limb_count as usize
        };
        let weight_limb_count = resident_context_state
            .as_ref()
            .map(|state| state.weight_limb_count as usize)
            .unwrap_or_else(|| {
                front
                    .contexts
                    .iter()
                    .map(|context| context.quadratic_weight.to_u32_digits().len())
                    .max()
                    .unwrap_or(1)
                    .max(1)
            });
        if phase_trace {
            eprintln!(
                "mem6-front-admission limbs context={} restriction={} weight={}",
                context_limb_count, restriction_limb_count, weight_limb_count,
            );
        }
        let current_factor_population = if materialize_moment_field {
            factors
        } else {
            native_factors
        };
        let encode_dense = |population: usize,
                            limb_count: usize,
                            currents: Vec<&[(u32, BigUint)]>|
         -> Result<Vec<u32>, CudaRefineError> {
            let mut encoded = vec![
                0_u32;
                population
                    .checked_mul(current_factor_population)
                    .and_then(|extent| extent.checked_mul(limb_count))
                    .ok_or(CudaRefineError::MembraneInteriorWordShape)?
            ];
            for (section, current) in currents.into_iter().enumerate() {
                for (factor, value) in current {
                    let local_factor = if materialize_moment_field {
                        let Some(local_factor) = active_lookup.get(factor) else {
                            continue;
                        };
                        *local_factor as usize
                    } else {
                        *factor as usize
                    };
                    let mut limbs = value.to_u32_digits();
                    limbs.resize(limb_count, 0);
                    let begin = (section * current_factor_population + local_factor) * limb_count;
                    encoded[begin..begin + limb_count].copy_from_slice(&limbs);
                }
            }
            Ok(encoded)
        };
        let context_current_limbs = if resident_context_state.is_some() {
            Vec::new()
        } else {
            encode_dense(
                context_count,
                context_limb_count,
                front
                    .contexts
                    .iter()
                    .map(|context| context.factor_current.as_slice())
                    .collect(),
            )?
        };
        let restriction_current_limbs = if direct_restrictions.is_some() {
            encode_dense(
                restriction_count,
                restriction_limb_count,
                ordered_restrictions
                    .iter()
                    .map(|restriction| restriction.factor_current.as_slice())
                    .collect(),
            )?
        } else {
            Vec::new()
        };
        let mut context_weight_limbs = Vec::new();
        if resident_context_state.is_none() {
            context_weight_limbs.reserve(
                context_count
                    .checked_mul(weight_limb_count)
                    .ok_or(CudaRefineError::MembraneInteriorWordShape)?,
            );
            for context in &front.contexts {
                let mut limbs = context.quadratic_weight.to_u32_digits();
                limbs.resize(weight_limb_count, 0);
                context_weight_limbs.extend(limbs);
            }
        }
        let restriction_ports = if direct_restrictions.is_some() {
            ordered_restrictions
                .iter()
                .map(|restriction| restriction.port)
                .collect::<Vec<_>>()
        } else {
            Vec::new()
        };

        let maximal_context = if let Some(state) = resident_context_state.as_ref() {
            state.maximal_current.clone()
        } else {
            front
                .contexts
                .iter()
                .flat_map(|context| &context.factor_current)
                .map(|(_, value)| value)
                .max()
                .cloned()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?
        };
        let maximal_restriction = if let Some(restrictions) = direct_restrictions {
            restrictions
                .iter()
                .flat_map(|restriction| &restriction.factor_current)
                .map(|(_, value)| value)
                .max()
                .cloned()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?
        } else {
            resident_atlas
                .expect("the resident presentation was established")
                .maximal_current
                .clone()
        };
        let maximal_weight = if let Some(state) = resident_context_state.as_ref() {
            state.maximal_weight.clone()
        } else {
            front
                .contexts
                .iter()
                .map(|context| &context.quadratic_weight)
                .max()
                .cloned()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?
        };
        let product_limb_count = context_limb_count
            .checked_add(restriction_limb_count)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let quadratic_limb_count = product_limb_count
            .checked_mul(2)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let relational_current_aperture =
            if resident_rectangular_restrictions && !materialize_moment_field {
                word.sparse_relational_current.as_ref().map(|current| {
                    (
                        current.receipt.clone(),
                        current.state_present.pointer,
                        current.states.pointer,
                        current.state_count,
                        current.factor_real_sign.pointer,
                        current.factor_real_limbs.pointer,
                        current.factor_imaginary_sign.pointer,
                        current.factor_imaginary_limbs.pointer,
                        current.factor_limb_count,
                        current.returned_factor_bound.clone(),
                    )
                })
            } else {
                None
            };
        let moment_bound = (&maximal_context * &maximal_restriction).pow(2)
            * &maximal_weight
            * BigUint::from(context_count)
            * BigUint::from(restriction_count);
        let moment_limb_count = moment_bound.to_u32_digits().len().max(1).saturating_add(1);
        let family_bound = &moment_bound
            * BigUint::from(word.total_factor_capacity)
            * BigUint::from(generator_count)
            * BigUint::from(2_u8);
        let receiver_bound = &moment_bound
            * BigUint::from(generator_count)
            * BigUint::from(factors)
            * BigUint::from(factors)
            * BigUint::from(4_u8);
        let mut overlap_bound = family_bound.max(receiver_bound);
        if post_target_observer {
            let aperture = completed_step
                .as_ref()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let relational_bound = relational_current_aperture
                .as_ref()
                .map(|entry| entry.9.clone())
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let multiplicity = BigUint::from(aperture.candidate_count.max(1));
            let face_bound = &maximal_context * &multiplicity;
            let face_relational_bound = relational_bound * &multiplicity;
            let paired_relational_bound = &face_relational_bound * BigUint::from(2_u8);
            let direct_family_bound = BigUint::from(word.total_factor_capacity)
                * face_bound
                    .pow(2)
                    .max(&face_bound * &paired_relational_bound);
            let direct_receiver_bound = BigUint::from(native_factors).pow(3)
                * (&face_bound * &paired_relational_bound).max(paired_relational_bound.pow(2));
            overlap_bound = overlap_bound
                .max(direct_family_bound)
                .max(direct_receiver_bound);
        }
        let overlap_limb_count = overlap_bound.to_u32_digits().len().max(1).saturating_add(2);
        let contact_bound =
            word.maximal_family_numerator.abs() * BigInt::from(overlap_bound.clone());
        let (_, contact_digits) = contact_bound.to_u32_digits();
        let contact_limb_count = contact_digits
            .len()
            .max(1)
            .saturating_add(1)
            .max(overlap_limb_count);
        let radiation_bound =
            &contact_bound * BigInt::from(word.families) * BigInt::from(port_population);
        let (_, radiation_digits) = radiation_bound.to_u32_digits();
        let radiation_limb_count = radiation_digits.len().max(1).saturating_add(1);
        let incoming_denominator = lcm_positive(
            entering_current.real.denom().clone(),
            entering_current.imaginary.denom(),
        );
        let balance_denominator = lcm_positive(
            word.family_common_denominator.clone(),
            &incoming_denominator,
        );
        let joint_scale = (&balance_denominator / &word.family_common_denominator)
            .to_u64()
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let incoming_real_bound = (entering_current.real.numer()
            * (&balance_denominator / entering_current.real.denom()))
        .abs();
        let incoming_imaginary_bound = (entering_current.imaginary.numer()
            * (&balance_denominator / entering_current.imaginary.denom()))
        .abs();
        let situated_pairing_bound =
            radiation_bound.abs() * (&incoming_real_bound + &incoming_imaginary_bound);
        let (_, situated_pairing_digits) = situated_pairing_bound.to_u32_digits();
        let situated_pairing_limb_count = situated_pairing_digits.len().max(1).saturating_add(1);
        let stored_bound = incoming_real_bound.max(incoming_imaginary_bound)
            + radiation_bound.abs() * BigInt::from(joint_scale);
        let (_, stored_digits) = stored_bound.to_u32_digits();
        let stored_limb_count = stored_digits.len().max(2).saturating_add(1);
        let maximal_generator_preimage = front
            .generator_targets
            .chunks_exact(native_factors)
            .map(|generator| {
                let mut preimages = vec![0_usize; native_factors];
                for target in generator {
                    preimages[*target as usize] += 1;
                }
                preimages.into_iter().max().unwrap_or(0)
            })
            .max()
            .filter(|extent| *extent != 0)
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let relational_limb_count = relational_current_aperture.as_ref().map(
            |(_, _, _, source_relational_state_count, _, _, _, _, _, returned_factor_bound)| {
                if post_target_observer {
                    let multiplicity = BigUint::from(
                        completed_step
                            .as_ref()
                            .map(|aperture| aperture.candidate_count.max(1))
                            .unwrap_or(1),
                    );
                    let face_bound = &maximal_context * &multiplicity;
                    let relational_bound = returned_factor_bound * &multiplicity;
                    let dot_bound = BigUint::from(native_factors)
                        * &face_bound
                        * &relational_bound
                        * BigUint::from(2_u8);
                    let target_norm_bound = BigUint::from(native_factors) * face_bound.pow(2);
                    let relational_norm_bound = BigUint::from(native_factors)
                        * relational_bound.pow(2)
                        * BigUint::from(2_u8);
                    return dot_bound
                        .pow(2)
                        .max(&target_norm_bound * &relational_norm_bound)
                        .max(target_norm_bound)
                        .max(relational_norm_bound)
                        .to_u32_digits()
                        .len()
                        .max(1)
                        .saturating_add(2);
                }
                let transported_current_bound =
                    &maximal_context * BigUint::from(maximal_generator_preimage);
                let transported_relational_bound =
                    returned_factor_bound * BigUint::from(maximal_generator_preimage);
                let restricted_current_bound = &transported_current_bound * &maximal_restriction;
                let restricted_relational_bound =
                    &transported_relational_bound * &maximal_restriction;
                let dot_bound = BigUint::from(native_factors)
                    * BigUint::from(*source_relational_state_count)
                    * &restricted_current_bound
                    * &restricted_relational_bound;
                let overlap_bound = BigUint::from(2_u8)
                    * BigUint::from(context_count)
                    * &maximal_weight
                    * dot_bound.pow(2);
                let target_norm_bound = BigUint::from(context_count)
                    * &maximal_weight
                    * BigUint::from(native_factors)
                    * restricted_current_bound.pow(2);
                let relational_norm_bound = BigUint::from(*source_relational_state_count)
                    * BigUint::from(2_u8)
                    * BigUint::from(native_factors)
                    * restricted_relational_bound.pow(2);
                let denominator_square_bound = (&target_norm_bound * &relational_norm_bound).pow(2);
                overlap_bound
                    .max(target_norm_bound)
                    .max(relational_norm_bound)
                    .max(denominator_square_bound)
                    .to_u32_digits()
                    .len()
                    .max(1)
                    .saturating_add(2)
            },
        );
        let phase_component_bound = (&overlap_bound * &overlap_bound).max(overlap_bound.clone());
        let phase_component_limb_count = phase_component_bound
            .to_u32_digits()
            .len()
            .max(1)
            .saturating_add(2)
            .max(relational_limb_count.unwrap_or(0));
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
        let component_count = word
            .families
            .checked_add(word.receiver_count)
            .and_then(|count| count.checked_add(u32::from(relational_current_aperture.is_some())))
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        // A resident response is addressed by the complete
        // `(source boundary state, port, generator)` incidence.  Collapsing the source-state
        // coordinate here would sum distinct history fibres before either the phase receiver or
        // the returned generated-port passage had proved that future conduct factors through
        // that quotient.  The direct diagnostic presentation has no resident state axis.
        // `observe` consumes the complete `Site -> Carrier` section.  Once the target-site direct
        // sum is founded, the source-state coordinate is its reconstruction fibre rather than an
        // additional response population.  Direct diagnostic moments retain their existing chart;
        // production resident observation descends the state axis before receiver comparison.
        let descend_boundary_state_receiver =
            resident_rectangular_restrictions && !materialize_moment_field;
        let response_state_count = if descend_boundary_state_receiver
            || materialize_moment_field
            || !resident_rectangular_restrictions
        {
            1
        } else {
            resident_boundary
                .expect("the resident presentation was established")
                .boundary_states
                .len()
        };
        let local_response_population = if materialize_moment_field {
            port_population
        } else {
            port_population
                .checked_mul(generator_count)
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?
        };
        let response_population = response_state_count
            .checked_mul(local_response_population)
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let component_population = response_population
            .checked_mul(component_count as usize)
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        // Distinct source-state charts have not been identified by a complete future-history
        // quotient and therefore are incomparable here.  Pair only within each state chart;
        // this retains the full plural state front and avoids manufacturing cross-state order.
        let phase_pair_population = response_state_count
            .checked_mul(local_response_population)
            .and_then(|extent| extent.checked_mul(local_response_population))
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        if phase_trace {
            eprintln!(
                "mem6-front-admission response states={} local={} total={} phase-pairs={}",
                response_state_count,
                local_response_population,
                response_population,
                phase_pair_population,
            );
        }
        let (incoming_real_sign, incoming_real_limbs) = encode_component(
            &entering_current.real,
            &balance_denominator,
            stored_limb_count,
        )?;
        let (incoming_imaginary_sign, incoming_imaginary_limbs) = encode_component(
            &entering_current.imaginary,
            &balance_denominator,
            stored_limb_count,
        )?;

        let moment_population = if materialize_moment_field {
            port_population
                .checked_mul(factors)
                .and_then(|extent| extent.checked_mul(factors))
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?
        } else {
            0
        };
        let axis_count = word.families.max(word.receiver_count) as usize;
        let contraction_work = response_population
            .checked_mul(axis_count)
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        // One factorized contraction lane must not serialize the complete context population.
        // The card's discovered block width supplies an apparatus grain; the mathematical sum
        // remains exact because contiguous chunks are reduced in their original address order.
        let context_chunk_size = word.card.block_x as usize;
        let context_chunk_count = if materialize_moment_field {
            1
        } else {
            context_count.div_ceil(context_chunk_size)
        };
        // Factor incidences and receiver-class incidences are a second independent finite-sum
        // axis.  Cover them at the card's discovered grain and reduce the rectangular cover in
        // lexicographic address order.  This changes apparatus occupancy, not the exact moment.
        let incidence_chunk_size = word.card.block_x as usize;
        let maximal_receiver_class_count = word
            .receiver_class_counts
            .as_deref()
            .and_then(|counts| counts.iter().copied().max())
            .unwrap_or(0) as usize;
        let incidence_chunk_count = if materialize_moment_field {
            1
        } else {
            factors
                .div_ceil(incidence_chunk_size)
                .max(maximal_receiver_class_count.div_ceil(incidence_chunk_size))
                .max(1)
        };
        // One resident contribution section is reused across the ordered context/incidence cover.
        // The cover coordinates are chronology, not additional morphology, so retaining their
        // Cartesian product would duplicate a reconstructible partial field in device memory.
        // The completed target is observed through its retained sparse incidence below.  The
        // factorized restriction/contribution apparatus belongs to the source-side moment
        // passage and is never launched for that observation.  Keep one inert cell so the common
        // ownership/release path remains total without materializing a second, unused copy of the
        // source-side rectangular cover.
        let legacy_restriction_allocation_count = if post_target_observer {
            1
        } else {
            restriction_count
        };
        let contribution_work = if post_target_observer {
            1
        } else {
            restriction_count
                .checked_mul(if materialize_moment_field {
                    1
                } else {
                    generator_count
                })
                .and_then(|extent| extent.checked_mul(axis_count))
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?
        };
        let family_population = response_population
            .checked_mul(word.families as usize)
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let receiver_population = response_population
            .checked_mul(word.receiver_count as usize)
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        if phase_trace {
            eprintln!(
                "mem6-front-admission work contribution={} contraction={} components={} compatibility-limbs={} square-limbs={} cross-limbs={}",
                contribution_work,
                contraction_work,
                component_population,
                compatibility_limb_count,
                square_limb_count,
                cross_limb_count,
            );
        }

        Ok(MomentFrontPlan {
            post_target_observer,
            factored_receiver_history,
            resident_current,
            resident_boundary,
            resident_rectangular_restrictions,
            restriction_count,
            resident_context_state,
            native_factors,
            factors,
            port_population,
            generator_count,
            port_restriction_offsets,
            context_count,
            active_factors,
            active_generator_targets,
            active_generator_local_targets,
            context_limb_count,
            restriction_limb_count,
            weight_limb_count,
            current_factor_population,
            context_current_limbs,
            restriction_current_limbs,
            context_weight_limbs,
            restriction_ports,
            maximal_context,
            relational_current_aperture,
            moment_limb_count,
            overlap_limb_count,
            contact_limb_count,
            radiation_limb_count,
            compatibility_limb_count,
            norm_limb_count,
            square_limb_count,
            cross_limb_count,
            situated_pairing_limb_count,
            stored_limb_count,
            joint_scale,
            balance_denominator,
            incoming_real_sign,
            incoming_real_limbs,
            incoming_imaginary_sign,
            incoming_imaginary_limbs,
            product_limb_count,
            quadratic_limb_count,
            component_count,
            descend_boundary_state_receiver,
            local_response_population,
            response_population,
            component_population,
            moment_population,
            axis_count,
            contraction_work,
            context_chunk_size,
            context_chunk_count,
            incidence_chunk_size,
            incidence_chunk_count,
            legacy_restriction_allocation_count,
            contribution_work,
            family_population,
            receiver_population,
            maximal_generator_preimage,
        })
    }
}
