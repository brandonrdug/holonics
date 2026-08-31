fn material_affine_transport_from_parts(
    rest_identity: &str,
    branch_population: usize,
    correspondences: &[LaboratoryFactorCycleCorrespondence],
    affine_cells: &[LaboratoryCellAffineSection],
    entering_section: &[i64],
) -> Result<Option<MaterialAffineTransportReceipt>, String> {
    if entering_section.len() != branch_population {
        return Err(format!(
            "the entering section has rank {}, but every affine landmark carries {} local fibres",
            entering_section.len(),
            branch_population
        ));
    }
    let mut cell_sections = Vec::with_capacity(affine_cells.len());
    for cell in affine_cells {
        if cell.landmark_factors.len() != cell.occurrence_multiplicities.len()
            || cell.landmark_factors.len() != cell.barycentric_weights.len()
        {
            return Err(format!(
                "affine cell {} lost its support population",
                cell.cell_address
            ));
        }
        let total_mass = cell
            .occurrence_multiplicities
            .iter()
            .try_fold(0u64, |sum, mass| sum.checked_add(*mass))
            .ok_or_else(|| "the affine cell mass overflowed".to_owned())?;
        let mut augmented = vec![Rat::from_integer(BigInt::from(0)); entering_section.len()];
        let mut exact_terms =
            Vec::with_capacity(cell.landmark_factors.len() * entering_section.len());
        for ((factor, multiplicity), weight) in cell
            .landmark_factors
            .iter()
            .zip(&cell.occurrence_multiplicities)
            .zip(&cell.barycentric_weights)
        {
            let correspondence = correspondences
                .get(*factor as usize)
                .ok_or_else(|| format!("affine landmark {factor} escaped the rest"))?;
            if correspondence.factor != *factor
                || correspondence.cycle_fibres.len() != entering_section.len()
            {
                return Err(format!(
                    "affine landmark {factor} lost its local rank-four fibre"
                ));
            }
            for ((coordinate, coefficient), fibre) in entering_section
                .iter()
                .enumerate()
                .zip(&correspondence.cycle_fibres)
            {
                if fibre.coordinate != coordinate {
                    return Err(format!("affine landmark {factor} changed its fibre chart"));
                }
                let transported = weight * Rat::from_integer(BigInt::from(*coefficient));
                augmented[coordinate] += &transported;
                exact_terms.push((
                    correspondence.factor_address.as_str(),
                    fibre.exact_fibre_address.as_str(),
                    *multiplicity,
                    weight,
                    *coefficient,
                    transported,
                ));
            }
        }
        let expected = entering_section
            .iter()
            .map(|coefficient| Rat::from_integer(BigInt::from(*coefficient)))
            .collect::<Vec<_>>();
        let augmentation_reconstructs_entering_section = augmented == expected;
        if !augmentation_reconstructs_entering_section {
            return Err(format!(
                "affine augmentation did not reconstruct the entering section at {}",
                cell.cell_address
            ));
        }
        let transported_field_identity_sha256 = digest_json(&(
            "soma-life.material-affine-cell-field.v1",
            rest_identity,
            &cell.cell_address,
            entering_section,
            &exact_terms,
        ))
        .map_err(|error| error.to_string())?;
        cell_sections.push(MaterialAffineCellTransportReceipt {
            cell_address: cell.cell_address.clone(),
            transported_field_identity_sha256,
            landmark_population: cell.landmark_factors.len(),
            local_fibre_term_population: exact_terms.len(),
            barycentric_total_mass: total_mass,
            augmentation_reconstructs_entering_section,
        });
    }
    MaterialAffineTransportReceipt::found(
        rest_identity.to_owned(),
        entering_section.to_vec(),
        correspondences.len(),
        cell_sections,
    )
    .map(Some)
    .map_err(|error| error.to_string())
}

fn factor_correspondences(
    body: &SituatedCultivatedAthenaRest,
    product: &ExchangeSituatedProduct,
) -> Result<Vec<LaboratoryFactorCycleCorrespondence>, LaboratoryCultivationError> {
    if product.native_covers.is_empty() || body.branches().len() != 4 {
        return Err(LaboratoryCultivationError::Correspondence(
            "the admitted base or its rank-four fibre is absent".to_owned(),
        ));
    }
    let exact = body.ecology().exact_reconstruction_fibres();
    product
        .native_covers
        .iter()
        .enumerate()
        .map(|(factor, cover)| {
            let mut cycle_fibres = Vec::with_capacity(body.branches().len());
            for branch in body.branches() {
                let matches = exact
                    .iter()
                    .filter(|fibre| {
                        fibre.thread == branch.thread_address
                            && fibre.dependent_receiver_fibre == BTreeSet::from([cover.native])
                    })
                    .collect::<Vec<_>>();
                if matches.len() != 1 {
                    return Err(LaboratoryCultivationError::Correspondence(format!(
                        "native landmark {} has {} fibres on cycle coordinate {}",
                        cover.native.0,
                        matches.len(),
                        branch.branch
                    )));
                }
                cycle_fibres.push(LaboratoryCycleFibreAddress {
                    coordinate: branch.branch,
                    thread_address: branch.thread_address.clone(),
                    exact_fibre_address: matches[0].address.clone(),
                });
            }
            let factor_address =
                digest_json(&(FACTOR_ADDRESS_DOMAIN, cover.native, &cycle_fibres))?;
            Ok(LaboratoryFactorCycleCorrespondence {
                factor: u32::try_from(factor).map_err(display_correspondence)?,
                factor_address,
                native: cover.native,
                cycle_fibres,
            })
        })
        .collect()
}

fn source_factor_map(
    product: &ExchangeSituatedProduct,
) -> Result<BTreeMap<ItemId, usize>, LaboratoryCultivationError> {
    let mut source_factors = BTreeMap::new();
    for (factor, cover) in product.native_covers.iter().enumerate() {
        for source in &cover.source_reconstruction_fibre {
            if source_factors.insert(*source, factor).is_some() {
                return Err(LaboratoryCultivationError::Correspondence(format!(
                    "source {} entered two affine landmarks",
                    source.0
                )));
            }
        }
    }
    let admitted = product
        .candidate_lineage
        .iter()
        .map(|lineage| lineage.source)
        .collect::<BTreeSet<_>>();
    if source_factors.keys().copied().collect::<BTreeSet<_>>() != admitted {
        return Err(LaboratoryCultivationError::Correspondence(
            "the affine landmark map does not cover the complete exchange source population"
                .to_owned(),
        ));
    }
    Ok(source_factors)
}

fn affine_cell_sections(
    potential: &NativeRelationalPotentialComplex,
) -> Result<Vec<LaboratoryCellAffineSection>, LaboratoryCultivationError> {
    potential
        .cells
        .iter()
        .map(|cell| {
            let mut multiplicities = BTreeMap::<u32, u64>::new();
            let mut source_occurrences = BTreeSet::new();
            for occurrence in &cell.occurrences {
                let held = multiplicities.entry(occurrence.factor).or_default();
                *held = held
                    .checked_add(occurrence.occurrence_population)
                    .ok_or_else(|| {
                        LaboratoryCultivationError::Correspondence(
                            "relational occurrence multiplicity overflow".to_owned(),
                        )
                    })?;
                source_occurrences.insert(occurrence.source_occurrence_identity_sha256.clone());
            }
            let total = multiplicities.values().try_fold(0u64, |sum, value| {
                sum.checked_add(*value).ok_or_else(|| {
                    LaboratoryCultivationError::Correspondence(
                        "relational affine mass overflow".to_owned(),
                    )
                })
            })?;
            if total == 0 {
                return Err(LaboratoryCultivationError::Correspondence(
                    "a relational cell has zero affine mass".to_owned(),
                ));
            }
            let landmark_factors = multiplicities.keys().copied().collect::<Vec<_>>();
            let occurrence_multiplicities = multiplicities.values().copied().collect::<Vec<_>>();
            let denominator = BigInt::from(total);
            let barycentric_weights = occurrence_multiplicities
                .iter()
                .map(|multiplicity| Rat::new(BigInt::from(*multiplicity), denominator.clone()))
                .collect::<Vec<_>>();
            let one = Rat::from_integer(BigInt::from(1));
            if landmark_factors != cell.factor_support
                || barycentric_weights.iter().cloned().sum::<Rat>() != one
            {
                return Err(LaboratoryCultivationError::Correspondence(
                    "a relational cell does not reconstruct its normalized affine support"
                        .to_owned(),
                ));
            }
            Ok(LaboratoryCellAffineSection {
                cell_address: cell.address.clone(),
                landmark_factors,
                occurrence_multiplicities,
                barycentric_weights,
                source_occurrence_identities_sha256: source_occurrences.into_iter().collect(),
            })
        })
        .collect()
}

fn validate_correspondences(
    body: &SituatedCultivatedAthenaRest,
    potential: &NativeRelationalPotentialComplex,
    correspondences: &[LaboratoryFactorCycleCorrespondence],
) -> Result<(), LaboratoryCultivationError> {
    if correspondences.len() != potential.factor_addresses.len()
        || correspondences.is_empty()
        || body.branches().len() != 4
    {
        return Err(LaboratoryCultivationError::Correspondence(
            "the affine landmark population does not equal the relational factor population"
                .to_owned(),
        ));
    }
    let exact = body.ecology().exact_reconstruction_fibres();
    let mut natives = BTreeSet::new();
    for (factor_at, correspondence) in correspondences.iter().enumerate() {
        if correspondence.factor as usize != factor_at
            || correspondence.factor_address != potential.factor_addresses[factor_at]
            || !natives.insert(correspondence.native)
            || correspondence.cycle_fibres.len() != body.branches().len()
        {
            return Err(LaboratoryCultivationError::Correspondence(
                "one affine landmark has malformed rank-four support".to_owned(),
            ));
        }
        for (coordinate, fibre) in correspondence.cycle_fibres.iter().enumerate() {
            let branch = &body.branches()[coordinate];
            if fibre.coordinate != branch.branch
                || fibre.thread_address != branch.thread_address
                || !exact.iter().any(|owned| {
                    owned.address == fibre.exact_fibre_address
                        && owned.thread == fibre.thread_address
                        && owned.dependent_receiver_fibre == BTreeSet::from([correspondence.native])
                })
            {
                return Err(LaboratoryCultivationError::Correspondence(
                    "one affine landmark lost an exact local cycle fibre".to_owned(),
                ));
            }
        }
    }
    Ok(())
}

fn validate_returned_correspondences(
    ecology: &holonic_engine::native_spool::NativeSituatedSpoolBundle,
    branches: &[SituatedCultivationBranch],
    potential: &NativeRelationalPotentialComplex,
    correspondences: &[LaboratoryFactorCycleCorrespondence],
) -> Result<(), LaboratoryCultivationError> {
    if correspondences.len() != potential.factor_addresses.len()
        || correspondences.is_empty()
        || branches.is_empty()
    {
        return Err(LaboratoryCultivationError::Correspondence(
            "the returned affine landmark population does not equal its retained factor population"
                .to_owned(),
        ));
    }
    let exact = ecology.exact_reconstruction_fibres();
    let base_threads = branches
        .iter()
        .map(|branch| branch.thread_address.as_str())
        .collect::<BTreeSet<_>>();
    let mut natives = BTreeSet::new();
    for (factor_at, correspondence) in correspondences.iter().enumerate() {
        if correspondence.factor as usize != factor_at
            || correspondence.factor_address != potential.factor_addresses[factor_at]
            || !natives.insert(correspondence.native)
            || correspondence.cycle_fibres.len() != branches.len()
        {
            return Err(LaboratoryCultivationError::Correspondence(
                "one returned affine landmark has malformed base-fibre support".to_owned(),
            ));
        }
        for (coordinate, fibre) in correspondence.cycle_fibres.iter().enumerate() {
            let branch = &branches[coordinate];
            if fibre.coordinate != branch.branch
                || fibre.thread_address != branch.thread_address
                || !base_threads.contains(fibre.thread_address.as_str())
                || !exact.iter().any(|owned| {
                    owned.address == fibre.exact_fibre_address
                        && owned.thread == fibre.thread_address
                        && owned.dependent_receiver_fibre == BTreeSet::from([correspondence.native])
                })
            {
                return Err(LaboratoryCultivationError::Correspondence(
                    "one returned affine landmark lost an exact inherited cycle fibre".to_owned(),
                ));
            }
        }
    }
    Ok(())
}

fn validate_exchange_projection(
    aperture: &ContinuationAperture,
    world: &VisibleMessageProjection,
) -> Result<(), LaboratoryCultivationError> {
    if aperture.source_occurrence_sha256 != world.source_occurrence_sha256
        || aperture.families.is_empty()
        || aperture.response_text_copied_into_atlas
        || aperture.provider_or_material_kind_routes_partition
    {
        return Err(LaboratoryCultivationError::Exchange(
            "the continuation aperture and visible projection are not one source occurrence"
                .to_owned(),
        ));
    }
    Ok(())
}

fn ordered_families(aperture: &ContinuationAperture) -> Vec<(usize, &ContinuationFamily)> {
    let mut families = aperture.families.iter().enumerate().collect::<Vec<_>>();
    families.sort_by_key(|(_, family)| {
        (
            family.prompt.container,
            family.prompt.record,
            family.prompt.visible_index,
        )
    });
    families
}

fn receive_message(
    builder: &mut NativeRelationalPotentialBuilder,
    factor: usize,
    phase: NativeDeliveryPhase,
    world: &VisibleMessageProjection,
    address: &MessageAddress,
    expected_speaker: &str,
) -> Result<(), LaboratoryCultivationError> {
    let message = world
        .messages
        .get(usize::try_from(address.visible_index).map_err(display_exchange)?)
        .ok_or_else(|| {
            LaboratoryCultivationError::Exchange(format!(
                "message {} escaped the visible projection",
                address.occurrence
            ))
        })?;
    if message.occurrence != address.occurrence
        || message.text_sha256 != address.content_sha256
        || message.container != address.container
        || message.record != address.record
        || message.speaker_face != expected_speaker
    {
        return Err(LaboratoryCultivationError::Exchange(format!(
            "message {} changed across the continuation/visible chart",
            address.occurrence
        )));
    }
    builder
        .receive(factor, phase, &message.occurrence, &message.text)
        .map_err(|error| LaboratoryCultivationError::Relational(error.to_string()))
}

fn digest_json(value: &impl Serialize) -> Result<String, LaboratoryCultivationError> {
    let bytes = serde_json::to_vec(value)
        .map_err(|error| LaboratoryCultivationError::Wire(error.to_string()))?;
    Ok(render_hex(&Sha256::digest(bytes)))
}

fn exterior_entity(surface: &str) -> RelationalEntity {
    let surface = vec![surface.to_owned()];
    RelationalEntity {
        identity: surface.iter().map(|word| word.to_lowercase()).collect(),
        surface,
    }
}

fn render_hex(value: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(value.len() * 2);
    for octet in value {
        out.push(HEX[(octet >> 4) as usize] as char);
        out.push(HEX[(octet & 15) as usize] as char);
    }
    out
}

fn display_correspondence(error: impl std::fmt::Display) -> LaboratoryCultivationError {
    LaboratoryCultivationError::Correspondence(error.to_string())
}

fn display_exchange(error: impl std::fmt::Display) -> LaboratoryCultivationError {
    LaboratoryCultivationError::Exchange(error.to_string())
}
