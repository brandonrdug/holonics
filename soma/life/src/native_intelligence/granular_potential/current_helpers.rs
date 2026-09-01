/// Return the canonical complete covariance section of one positive weighted rank-one family.
/// The pivot search is over the rational column span; positivity of every context weight makes
/// that span exactly the column span of the resulting Gram field. Consequently the selected pivot
/// rows and all of their cross moments determine the entire field, including every unselected
/// factor pair.
#[cfg(test)]
fn canonical_dynamic_moment(
    contexts: &[GranularCausalContext],
    factor_population: usize,
) -> Result<GranularDynamicMomentSection, NativeGranularPotentialError> {
    if contexts.is_empty()
        || factor_population == 0
        || factor_population > u32::MAX as usize
        || contexts
            .iter()
            .any(|context| context.quadratic_weight == BigUint::ZERO)
    {
        return Err(NativeGranularPotentialError::FineInvariant(
            "the dynamic moment received an empty native covariance family".to_owned(),
        ));
    }
    let mut dense = vec![vec![BigUint::ZERO; factor_population]; contexts.len()];
    for (context_at, context) in contexts.iter().enumerate() {
        if context.factor_current.is_empty()
            || context
                .factor_current
                .windows(2)
                .any(|pair| pair[0].factor >= pair[1].factor)
        {
            return Err(NativeGranularPotentialError::Wire);
        }
        for coordinate in &context.factor_current {
            let factor = coordinate.factor as usize;
            if factor >= factor_population || coordinate.incidence == BigUint::ZERO {
                return Err(NativeGranularPotentialError::FactorOutsideBase);
            }
            dense[context_at][factor] = coordinate.incidence.clone();
        }
    }

    let mut echelon = Vec::<(usize, Vec<BigInt>)>::new();
    let mut pivot_factors = Vec::new();
    for factor in 0..factor_population {
        let mut column = dense
            .iter()
            .map(|context| BigInt::from(context[factor].clone()))
            .collect::<Vec<_>>();
        for (pivot_row, basis) in &echelon {
            if column[*pivot_row] == BigInt::ZERO {
                continue;
            }
            let entering_pivot = column[*pivot_row].clone();
            let basis_pivot = basis[*pivot_row].clone();
            for row in *pivot_row..column.len() {
                column[row] = &basis_pivot * &column[row] - &entering_pivot * &basis[row];
            }
            let common = column
                .iter()
                .map(|value| value.magnitude().clone())
                .reduce(gcd_biguint)
                .filter(|value| *value != BigUint::ZERO)
                .unwrap_or_else(|| BigUint::from(1_u8));
            if common != BigUint::from(1_u8) {
                let common = BigInt::from(common);
                for value in &mut column {
                    *value /= &common;
                }
            }
        }
        let Some(pivot_row) = column.iter().position(|value| *value != BigInt::ZERO) else {
            continue;
        };
        let common = column
            .iter()
            .map(|value| value.magnitude().clone())
            .reduce(gcd_biguint)
            .filter(|value| *value != BigUint::ZERO)
            .unwrap_or_else(|| BigUint::from(1_u8));
        if common != BigUint::from(1_u8) {
            let common = BigInt::from(common);
            for value in &mut column {
                *value /= &common;
            }
        }
        if column[pivot_row] < BigInt::ZERO {
            for value in &mut column {
                *value = -std::mem::take(value);
            }
        }
        echelon.push((pivot_row, column));
        pivot_factors
            .push(u32::try_from(factor).map_err(|_| NativeGranularPotentialError::Extent)?);
    }
    if pivot_factors.is_empty() {
        return Err(NativeGranularPotentialError::FineInvariant(
            "the native covariance section had zero rank".to_owned(),
        ));
    }

    let mut pivot_cross_moments = Vec::with_capacity(
        pivot_factors
            .len()
            .checked_mul(factor_population)
            .ok_or(NativeGranularPotentialError::Extent)?,
    );
    for pivot in &pivot_factors {
        let pivot = *pivot as usize;
        for factor in 0..factor_population {
            let cross =
                contexts
                    .iter()
                    .enumerate()
                    .fold(BigUint::ZERO, |sum, (context_at, context)| {
                        sum + &context.quadratic_weight
                            * &dense[context_at][pivot]
                            * &dense[context_at][factor]
                    });
            pivot_cross_moments.push(cross);
        }
    }
    let rank =
        u32::try_from(pivot_factors.len()).map_err(|_| NativeGranularPotentialError::Extent)?;
    Ok(GranularDynamicMomentSection {
        factor_population: factor_population as u32,
        rank,
        pivot_factors,
        pivot_cross_moments,
    })
}

/// Quotient carried sections only after their complete future-consequence key has been formed.
/// The active quadratic masses are normalized by their exact common projective scale; every
/// removed divisor and every incoming addressed edge remains in the reconstruction DAG.
fn validate_resident_returned_face_boundary(
    states: &[NativeGranularState],
    factor_generators: &[NativeGranularFactorGenerator],
    returned: &[GranularHigherBoundaryFace],
) -> Result<(), NativeGranularPotentialError> {
    if returned.is_empty() || returned.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(NativeGranularPotentialError::FineInvariant(
            "the returned higher phase front is empty, repeated, or reordered".to_owned(),
        ));
    }
    let returned_generator_ids = returned
        .iter()
        .map(|face| face.generator)
        .collect::<BTreeSet<_>>();
    let admitted_generator_ids = factor_generators
        .iter()
        .map(|generator| generator.generator)
        .collect::<BTreeSet<_>>();
    if states.is_empty()
        || returned_generator_ids.is_empty()
        || !returned_generator_ids.is_subset(&admitted_generator_ids)
    {
        return Err(NativeGranularPotentialError::FineInvariant(
            "the resident phase front escaped the admitted generator boundary".to_owned(),
        ));
    }
    Ok(())
}

/// Recover the next boundary from the exact returned branch incidences. A port name is only an
/// exterior face: looking it up again at the root would discard the source-state leg of the
/// addressed span and silently reset every recurrent passage to a one-step receiver shadow.
fn returned_target_boundary(
    branches: &[GranularBoundaryBranch],
    returned: &[GranularHigherBoundaryFace],
) -> Result<Vec<u32>, NativeGranularPotentialError> {
    let mut boundary = BTreeSet::new();
    for face in returned {
        let mut matching = branches
            .iter()
            .filter(|branch| branch.port == face.port && branch.generator == face.generator);
        let branch = matching.next().ok_or_else(|| {
            NativeGranularPotentialError::FineInvariant(
                "a returned higher face had no addressed predecessor branch".to_owned(),
            )
        })?;
        if matching.next().is_some() || branch.target_states.is_empty() {
            return Err(NativeGranularPotentialError::FineInvariant(
                "a returned higher face did not determine one complete target-state fibre"
                    .to_owned(),
            ));
        }
        boundary.extend(branch.target_states.iter().copied());
    }
    if boundary.is_empty() {
        return Err(NativeGranularPotentialError::Wire);
    }
    Ok(boundary.into_iter().collect())
}

fn finalize_carried_current(
    mut reconstruction_nodes: Vec<GranularReconstructionNode>,
    candidates: GranularCarriedCandidates,
    boundary_front: Vec<u32>,
) -> Result<GranularPortCurrent, NativeGranularPotentialError> {
    type PendingNode = (
        u32,
        Vec<GranularFactorCurrent>,
        Vec<GranularReconstructionEdge>,
        u32,
        u32,
        BigUint,
        BigUint,
    );
    let mut pending_nodes = Vec::<PendingNode>::with_capacity(candidates.len());
    for ((state, factor_current), mut candidate) in candidates {
        let mut incoming = std::mem::take(&mut candidate.reconstruction_edges);
        incoming.sort_unstable();
        let mut shortest_extent = u32::MAX;
        let mut greatest_extent = 0_u32;
        let mut path_population = BigUint::from(0_u8);
        let mut quadratic_projective_mass = BigUint::from(0_u8);
        for edge in &incoming {
            let transport_square =
                &edge.transport_projective_scale * &edge.transport_projective_scale;
            if let Some(predecessor) = edge.predecessor {
                let predecessor = reconstruction_nodes
                    .get(predecessor as usize)
                    .filter(|node| node.node == predecessor)
                    .ok_or(NativeGranularPotentialError::Wire)?;
                shortest_extent = shortest_extent.min(
                    predecessor
                        .shortest_extent
                        .checked_add(1)
                        .ok_or(NativeGranularPotentialError::Extent)?,
                );
                greatest_extent = greatest_extent.max(
                    predecessor
                        .greatest_extent
                        .checked_add(1)
                        .ok_or(NativeGranularPotentialError::Extent)?,
                );
                path_population += &predecessor.path_population;
                quadratic_projective_mass +=
                    &predecessor.quadratic_projective_mass * &transport_square;
            } else {
                shortest_extent = shortest_extent.min(1);
                greatest_extent = greatest_extent.max(1);
                path_population += BigUint::from(1_u8);
                quadratic_projective_mass += transport_square;
            }
        }
        if shortest_extent == u32::MAX
            || path_population == BigUint::from(0_u8)
            || quadratic_projective_mass == BigUint::from(0_u8)
            || candidate.quadratic_weight != quadratic_projective_mass
        {
            return Err(NativeGranularPotentialError::FineInvariant(
                "a reconstruction node diverged from its native covariance weight".to_owned(),
            ));
        }
        pending_nodes.push((
            state,
            factor_current,
            incoming,
            shortest_extent,
            greatest_extent,
            path_population,
            quadratic_projective_mass,
        ));
    }
    let common_quadratic_scale = pending_nodes
        .iter()
        .map(|pending| pending.6.clone())
        .reduce(gcd_biguint)
        .filter(|scale| *scale != BigUint::from(0_u8))
        .unwrap_or_else(|| BigUint::from(1_u8));
    let mut context_nodes =
        BTreeMap::<(u32, Vec<GranularFactorCurrent>), (BigUint, Vec<u32>)>::new();
    for (
        state,
        factor_current,
        incoming,
        shortest_extent,
        greatest_extent,
        path_population,
        quadratic_projective_mass,
    ) in pending_nodes
    {
        let node = u32::try_from(reconstruction_nodes.len())
            .map_err(|_| NativeGranularPotentialError::Extent)?;
        let quadratic_weight = quadratic_projective_mass / &common_quadratic_scale;
        reconstruction_nodes.push(GranularReconstructionNode {
            node,
            quadratic_projective_mass: quadratic_weight.clone(),
            removed_common_quadratic_scale: common_quadratic_scale.clone(),
            shortest_extent,
            greatest_extent,
            path_population,
            incoming,
        });
        let context = context_nodes.entry((state, factor_current)).or_default();
        context.0 += quadratic_weight;
        context.1.push(node);
    }
    let contexts = context_nodes
        .into_iter()
        .map(
            |((state, factor_current), (quadratic_weight, node_ids))| GranularCausalContext {
                state,
                factor_current,
                quadratic_weight,
                reconstruction_nodes: node_ids,
            },
        )
        .collect::<Vec<_>>();
    Ok(GranularPortCurrent {
        contexts,
        resident_image: None,
        boundary_front,
        reconstruction_nodes,
    })
}

/// Rebuild only the cold reconstruction chart around an exact current already transported and
/// condensed by the resident apparatus.  Unlike exterior/projective ingress, this passage has no
/// authority to remove a new common scale: the resident row and weight are the continuing state.
fn finalize_resident_carried_current(
    mut reconstruction_nodes: Vec<GranularReconstructionNode>,
    candidates: Vec<(GranularConsequenceKey, GranularCarriedCandidate)>,
    boundary_front: Vec<u32>,
) -> Result<GranularPortCurrent, NativeGranularPotentialError> {
    let mut contexts = Vec::with_capacity(candidates.len());
    for ((state, factor_current), mut candidate) in candidates {
        let mut incoming = std::mem::take(&mut candidate.reconstruction_edges);
        incoming.sort_unstable();
        let mut shortest_extent = u32::MAX;
        let mut greatest_extent = 0_u32;
        let mut path_population = BigUint::from(0_u8);
        let mut reconstructed_mass = BigUint::from(0_u8);
        for edge in &incoming {
            let predecessor = edge
                .predecessor
                .and_then(|node| {
                    reconstruction_nodes
                        .get(node as usize)
                        .filter(|held| held.node == node)
                })
                .ok_or(NativeGranularPotentialError::Wire)?;
            shortest_extent = shortest_extent.min(
                predecessor
                    .shortest_extent
                    .checked_add(1)
                    .ok_or(NativeGranularPotentialError::Extent)?,
            );
            greatest_extent = greatest_extent.max(
                predecessor
                    .greatest_extent
                    .checked_add(1)
                    .ok_or(NativeGranularPotentialError::Extent)?,
            );
            path_population += &predecessor.path_population;
            reconstructed_mass += &predecessor.quadratic_projective_mass
                * &edge.transport_projective_scale
                * &edge.transport_projective_scale;
        }
        if shortest_extent == u32::MAX
            || path_population == BigUint::from(0_u8)
            || reconstructed_mass == BigUint::from(0_u8)
            || candidate.quadratic_weight != reconstructed_mass
        {
            return Err(NativeGranularPotentialError::FineInvariant(
                "the resident dynamic boundary map did not reconstruct its exact target weight"
                    .to_owned(),
            ));
        }
        let node = u32::try_from(reconstruction_nodes.len())
            .map_err(|_| NativeGranularPotentialError::Extent)?;
        reconstruction_nodes.push(GranularReconstructionNode {
            node,
            quadratic_projective_mass: candidate.quadratic_weight.clone(),
            removed_common_quadratic_scale: BigUint::from(1_u8),
            shortest_extent,
            greatest_extent,
            path_population,
            incoming,
        });
        contexts.push(GranularCausalContext {
            state,
            factor_current,
            quadratic_weight: candidate.quadratic_weight,
            reconstruction_nodes: vec![node],
        });
    }
    if contexts.is_empty() {
        return Err(NativeGranularPotentialError::Wire);
    }
    Ok(GranularPortCurrent {
        contexts,
        resident_image: None,
        boundary_front,
        reconstruction_nodes,
    })
}

/// Rebuild the cold lineage around an exact target-site sum.  Unlike the rank-one carrier above,
/// the target's unit quadratic weight is a later observer face: predecessor projective masses are
/// retained in the reconstruction node but do not author or scale the hot junction current.
fn finalize_resident_junction_current(
    mut reconstruction_nodes: Vec<GranularReconstructionNode>,
    candidates: Vec<(GranularConsequenceKey, GranularCarriedCandidate)>,
    boundary_front: Vec<u32>,
) -> Result<GranularPortCurrent, NativeGranularPotentialError> {
    let mut contexts = Vec::with_capacity(candidates.len());
    for ((state, factor_current), mut candidate) in candidates {
        let mut incoming = std::mem::take(&mut candidate.reconstruction_edges);
        incoming.sort_unstable();
        let mut shortest_extent = u32::MAX;
        let mut greatest_extent = 0_u32;
        let mut path_population = BigUint::from(0_u8);
        let mut retained_projective_mass = BigUint::from(0_u8);
        for edge in &incoming {
            let predecessor = edge
                .predecessor
                .and_then(|node| {
                    reconstruction_nodes
                        .get(node as usize)
                        .filter(|held| held.node == node)
                })
                .ok_or(NativeGranularPotentialError::Wire)?;
            shortest_extent = shortest_extent.min(
                predecessor
                    .shortest_extent
                    .checked_add(1)
                    .ok_or(NativeGranularPotentialError::Extent)?,
            );
            greatest_extent = greatest_extent.max(
                predecessor
                    .greatest_extent
                    .checked_add(1)
                    .ok_or(NativeGranularPotentialError::Extent)?,
            );
            path_population += &predecessor.path_population;
            retained_projective_mass += &predecessor.quadratic_projective_mass;
        }
        if shortest_extent == u32::MAX
            || path_population.is_zero()
            || retained_projective_mass.is_zero()
            || candidate.quadratic_weight != BigUint::from(1_u8)
        {
            return Err(NativeGranularPotentialError::FineInvariant(
                "the resident target-site junction lost its reconstruction fibre".to_owned(),
            ));
        }
        let node = u32::try_from(reconstruction_nodes.len())
            .map_err(|_| NativeGranularPotentialError::Extent)?;
        reconstruction_nodes.push(GranularReconstructionNode {
            node,
            quadratic_projective_mass: retained_projective_mass,
            removed_common_quadratic_scale: BigUint::from(1_u8),
            shortest_extent,
            greatest_extent,
            path_population,
            incoming,
        });
        contexts.push(GranularCausalContext {
            state,
            factor_current,
            quadratic_weight: candidate.quadratic_weight,
            reconstruction_nodes: vec![node],
        });
    }
    if contexts.is_empty() {
        return Err(NativeGranularPotentialError::Wire);
    }
    Ok(GranularPortCurrent {
        contexts,
        resident_image: None,
        boundary_front,
        reconstruction_nodes,
    })
}

fn primitive_factor_current(
    current: &[GranularFactorCurrent],
) -> Result<(Vec<GranularFactorCurrent>, BigUint), NativeGranularPotentialError> {
    if current.is_empty()
        || current
            .windows(2)
            .any(|pair| pair[0].factor >= pair[1].factor)
        || current
            .iter()
            .any(|coordinate| coordinate.incidence == BigUint::from(0_u8))
    {
        return Err(NativeGranularPotentialError::FineInvariant(
            "a factor current was not an addressed positive section".to_owned(),
        ));
    }
    let gcd = current
        .iter()
        .map(|coordinate| coordinate.incidence.clone())
        .reduce(gcd_biguint)
        .ok_or(NativeGranularPotentialError::CarrierExtent)?;
    Ok((
        current
            .iter()
            .map(|coordinate| GranularFactorCurrent {
                factor: coordinate.factor,
                incidence: &coordinate.incidence / &gcd,
            })
            .collect(),
        gcd,
    ))
}

/// Push a factor section through one exact descended generator. Repeated returned circulation
/// composes the checked squares while plural generator faces remain distinct until reception.
fn apply_generator_current(
    current: &[GranularFactorCurrent],
    generator: &NativeGranularFactorGenerator,
) -> Result<(Vec<GranularFactorCurrent>, BigUint), NativeGranularPotentialError> {
    if current.is_empty() {
        return Err(NativeGranularPotentialError::FineInvariant(
            "the higher current lost its factor section".to_owned(),
        ));
    }
    let mut transported = BTreeMap::<u32, BigUint>::new();
    for coordinate in current {
        let target = *generator
            .targets
            .get(coordinate.factor as usize)
            .ok_or(NativeGranularPotentialError::FactorOutsideBase)?;
        *transported.entry(target).or_default() += &coordinate.incidence;
    }
    primitive_factor_current(
        &transported
            .into_iter()
            .map(|(factor, incidence)| GranularFactorCurrent { factor, incidence })
            .collect::<Vec<_>>(),
    )
}

/// Form the oriented returned action difference `U_i J - J` on the complete native factor base.
/// The primitive section and removed common divisor are returned separately, preserving exact
/// projective reconstruction without turning the divisor into a behavioral aperture.
#[cfg(test)]
fn generator_action_difference(
    current: &[GranularFactorCurrent],
    generator: &NativeGranularFactorGenerator,
) -> Result<(Vec<GranularSignedFactorCurrent>, BigUint), NativeGranularPotentialError> {
    if current.is_empty() {
        return Err(NativeGranularPotentialError::FineInvariant(
            "the higher action difference lost its entering factor section".to_owned(),
        ));
    }
    let mut difference = BTreeMap::<u32, BigInt>::new();
    for coordinate in current {
        let target = *generator
            .targets
            .get(coordinate.factor as usize)
            .ok_or(NativeGranularPotentialError::FactorOutsideBase)?;
        *difference.entry(target).or_default() += BigInt::from(coordinate.incidence.clone());
        *difference.entry(coordinate.factor).or_default() -=
            BigInt::from(coordinate.incidence.clone());
    }
    difference.retain(|_, coefficient| coefficient != &BigInt::from(0_u8));
    if difference.is_empty() {
        return Ok((Vec::new(), BigUint::from(1_u8)));
    }
    let gcd = difference
        .values()
        .map(|coefficient| coefficient.magnitude().clone())
        .reduce(gcd_biguint)
        .ok_or(NativeGranularPotentialError::CarrierExtent)?;
    let divisor = BigInt::from(gcd.clone());
    Ok((
        difference
            .into_iter()
            .map(|(factor, coefficient)| GranularSignedFactorCurrent {
                factor,
                coefficient: coefficient / &divisor,
            })
            .collect(),
        gcd,
    ))
}

/// Push a native signed action section into the complete free receiver-face basis.  Only equality
/// of opaque `(receiver, observation)` faces is used; observation carrier values are never added,
/// ordered, or treated as magnitudes.
#[cfg(test)]
fn receiver_action_current(
    action: &[GranularSignedFactorCurrent],
    factor_faces: &[GranularFactorFace],
) -> Result<Vec<GranularReceiverActionCurrent>, NativeGranularPotentialError> {
    let mut receiver_current = BTreeMap::<(ReceiverId, Observation), BigInt>::new();
    for coordinate in action {
        let face = factor_faces
            .get(coordinate.factor as usize)
            .filter(|face| face.factor == coordinate.factor)
            .ok_or(NativeGranularPotentialError::FactorOutsideBase)?;
        for receiver in &face.receiver_factors {
            *receiver_current
                .entry((receiver.receiver, receiver.observation))
                .or_default() += &coordinate.coefficient;
        }
    }
    receiver_current.retain(|_, coefficient| coefficient != &BigInt::from(0_u8));
    Ok(receiver_current
        .into_iter()
        .map(
            |((receiver, observation), coefficient)| GranularReceiverActionCurrent {
                receiver,
                observation,
                coefficient,
            },
        )
        .collect())
}

/// Compose two local factor-current sections.  The common factor ray is the projective current;
/// the removed common divisor is returned as reconstruction testimony.  No coordinate is rounded,
/// scored, or converted through an exterior scalar chart.
fn transport_factor_current(
    left: &[GranularFactorCurrent],
    right: &[GranularFactorCurrent],
) -> Result<Option<(Vec<GranularFactorCurrent>, BigUint)>, NativeGranularPotentialError> {
    let mut products = Vec::<(u32, BigUint)>::new();
    let mut left_at = 0usize;
    let mut right_at = 0usize;
    while left_at < left.len() && right_at < right.len() {
        match left[left_at].factor.cmp(&right[right_at].factor) {
            std::cmp::Ordering::Less => left_at += 1,
            std::cmp::Ordering::Greater => right_at += 1,
            std::cmp::Ordering::Equal => {
                let product = &left[left_at].incidence * &right[right_at].incidence;
                products.push((left[left_at].factor, product));
                left_at += 1;
                right_at += 1;
            }
        }
    }
    if products.is_empty() {
        return Ok(None);
    }
    let gcd = products
        .iter()
        .map(|(_, incidence)| incidence.clone())
        .reduce(gcd_biguint)
        .ok_or(NativeGranularPotentialError::CarrierExtent)?;
    let primitive = products
        .into_iter()
        .map(|(factor, incidence)| {
            Ok(GranularFactorCurrent {
                factor,
                incidence: incidence / &gcd,
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Some((primitive, gcd)))
}

fn factor_currents_contact(
    left: &[GranularFactorCurrent],
    right: &[GranularFactorCurrent],
) -> bool {
    let mut left_at = 0_usize;
    let mut right_at = 0_usize;
    while left_at < left.len() && right_at < right.len() {
        match left[left_at].factor.cmp(&right[right_at].factor) {
            std::cmp::Ordering::Less => left_at += 1,
            std::cmp::Ordering::Greater => right_at += 1,
            std::cmp::Ordering::Equal => return true,
        }
    }
    false
}

fn gcd_biguint(mut left: BigUint, mut right: BigUint) -> BigUint {
    while right != BigUint::from(0_u8) {
        let remainder = &left % &right;
        left = right;
        right = remainder;
    }
    left
}

fn factor_current_matches(
    current: &[GranularFactorCurrent],
    support: &[u32],
    recurrence: u64,
    factor_population: usize,
) -> bool {
    current.len() == support.len()
        && !current.is_empty()
        && current.iter().zip(support).all(|(coordinate, factor)| {
            coordinate.factor == *factor
                && (coordinate.factor as usize) < factor_population
                && coordinate.incidence != BigUint::from(0_u8)
        })
        && current.iter().fold(BigUint::from(0_u8), |sum, coordinate| {
            sum + &coordinate.incidence
        }) == BigUint::from(recurrence)
}

fn factors_from_bits(
    bits: &[u64],
    factor_population: usize,
) -> Result<Vec<u32>, NativeGranularPotentialError> {
    let mut factors = Vec::new();
    for (word_at, word) in bits.iter().copied().enumerate() {
        let mut held = word;
        while held != 0 {
            let bit = held.trailing_zeros() as usize;
            let factor = word_at
                .checked_mul(u64::BITS as usize)
                .and_then(|base| base.checked_add(bit))
                .ok_or(NativeGranularPotentialError::Extent)?;
            if factor >= factor_population {
                return Err(NativeGranularPotentialError::FactorOutsideBase);
            }
            factors.push(u32::try_from(factor).map_err(|_| NativeGranularPotentialError::Extent)?);
            held &= held - 1;
        }
    }
    if factors.is_empty() {
        return Err(NativeGranularPotentialError::FineInvariant(
            "an observed boundary face lost all native factor support".to_owned(),
        ));
    }
    Ok(factors)
}

fn intern_support(
    factors: Vec<u32>,
    supports: &mut Vec<Vec<u32>>,
    lookup: &mut BTreeMap<Vec<u32>, u32>,
) -> Result<u32, NativeGranularPotentialError> {
    if let Some(support) = lookup.get(&factors) {
        return Ok(*support);
    }
    let support =
        u32::try_from(supports.len()).map_err(|_| NativeGranularPotentialError::Extent)?;
    lookup.insert(factors.clone(), support);
    supports.push(factors);
    Ok(support)
}

fn factor_identity(address: &str) -> ReceiverFiberIdentity {
    fiber_from_bytes(FACTOR_FACE_SCHEMA, address.as_bytes())
}

/// Derive the resident factor address from the complete native face rather than from the
/// predecessor's exterior address.  The index disambiguates equal receiver faces while the
/// native state and receiver family provide the address's future-consequence signature.
fn native_factor_address(
    factor: u32,
    native: NativeStateId,
    receiver_factors: &[GranularFactorReceiver],
) -> String {
    let mut digest = Sha256::new();
    digest.update(b"soma-life.native-future-consequence-factor.v1");
    digest.update(factor.to_le_bytes());
    digest.update(native.0.to_le_bytes());
    digest.update((receiver_factors.len() as u64).to_le_bytes());
    for receiver in receiver_factors {
        digest.update(receiver.receiver.0.to_le_bytes());
        digest.update(receiver.observation.0.to_le_bytes());
    }
    format!("native-factor/{}", render_hex(&digest.finalize()))
}

pub(super) fn factor_face_is_native(face: &GranularFactorFace) -> bool {
    face.factor_address == native_factor_address(face.factor, face.native, &face.receiver_factors)
}

fn native_factor_action_is_total(
    factor_faces: &[GranularFactorFace],
    generators: &[NativeGranularFactorGenerator],
) -> bool {
    let factor_population = factor_faces.len();
    factor_population != 0
        && factor_faces.iter().all(|face| {
            !face.receiver_factors.is_empty()
                && face
                    .receiver_factors
                    .windows(2)
                    .all(|pair| pair[0] < pair[1])
        })
        && factor_faces.first().is_some_and(|first| {
            let family = first
                .receiver_factors
                .iter()
                .map(|item| item.receiver)
                .collect::<BTreeSet<_>>();
            !family.is_empty()
                && factor_faces.iter().all(|face| {
                    face.receiver_factors
                        .iter()
                        .map(|item| item.receiver)
                        .collect::<BTreeSet<_>>()
                        == family
                })
        })
        && !generators.is_empty()
        && generators
            .windows(2)
            .all(|pair| pair[0].generator < pair[1].generator)
        && generators.iter().all(|generator| {
            generator.targets.len() == factor_population
                && generator
                    .targets
                    .iter()
                    .all(|target| (*target as usize) < factor_population)
        })
}

fn face_identity(face: &GranularFactorFace) -> ReceiverFiberIdentity {
    ReceiverFiberIdentity::new(face.receiver_schema, face.receiver_words.clone())
}

fn hex_sha256(bytes: &[u8]) -> String {
    render_hex(&Sha256::digest(bytes))
}

fn render_hex(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for octet in bytes {
        out.push(HEX[(octet >> 4) as usize] as char);
        out.push(HEX[(octet & 15) as usize] as char);
    }
    out
}
