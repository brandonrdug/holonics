//! Local receiver realization and constitutive interaction helpers for the exchange product.
//!
//! These helpers are an owner-local implementation boundary; public product surfaces remain
//! explicitly defined and exported by the parent module.

use super::*;

#[allow(clippy::too_many_arguments)]
pub(super) fn situated_local(
    returned_native: &ExchangeReturnedNativeSection,
    branch: &K3PullbackBranch,
    constitutive: &NativeReceiverConstitutiveForm,
    basis: &BTreeMap<ExchangeDefectBasisFace, usize>,
    ambient_rows: usize,
    ambient_columns: usize,
    support_column: usize,
    native: &ReceiverHistoryCompression,
    seals: &BTreeMap<ItemId, String>,
) -> Result<(SituatedDifferenceSection, SupportedDefectSection), ExchangeSituatedProductError> {
    let mut local_faces = vec![returned_native.candidate_face.clone()];
    local_faces.extend(returned_native.returned_faces.iter().cloned());
    local_faces.sort();
    local_faces.dedup();
    let support_rows = local_faces
        .iter()
        .map(|face| basis[face])
        .collect::<Vec<_>>();
    let local_index = local_faces
        .iter()
        .enumerate()
        .map(|(at, face)| (face, at))
        .collect::<BTreeMap<_, _>>();
    let mut candidate_coordinates = vec![rat(0); local_faces.len()];
    candidate_coordinates[local_index[&returned_native.candidate_face]] = rat(1);
    let mut returned_coordinates = vec![rat(0); local_faces.len()];
    for face in &returned_native.returned_faces {
        returned_coordinates[local_index[face]] = rat(1);
    }
    let difference = returned_coordinates
        .iter()
        .zip(&candidate_coordinates)
        .map(|(returned, candidate)| returned - candidate)
        .collect::<Vec<_>>();
    let supported = ExactRatMatrix::new(
        difference
            .iter()
            .cloned()
            .map(|value| vec![value])
            .collect(),
    )
    .map_err(linear)?;
    let local_metric = constitutive.local_metric(returned_native.branch)?;
    let scalar_metric = ExactRatMatrix::new(vec![vec![local_metric.clone()]]).map_err(linear)?;
    let codomain_metric = ExactRatMatrix::new(
        (0..local_faces.len())
            .map(|row| {
                (0..local_faces.len())
                    .map(|column| {
                        if row == column {
                            local_metric.clone()
                        } else {
                            rat(0)
                        }
                    })
                    .collect()
            })
            .collect(),
    )
    .map_err(linear)?;
    let overlap_metric_value = branch.returned.entering_current.norm_square();
    if overlap_metric_value == rat(0) {
        return Err(ExchangeSituatedProductError::Constitutive(
            "the K3 overlap metric is degenerate".to_owned(),
        ));
    }
    let overlap_metric = ExactRatMatrix::new(vec![vec![overlap_metric_value]]).map_err(linear)?;
    let occurrence_fibre = NativeCollapsedFibre {
        native: branch.pullback.joining_native,
        occurrences: returned_native.event_reconstruction_fibre.clone(),
    };
    let candidate = readdress_section(
        &branch.candidate,
        returned_native.candidate_event,
        branch.candidate.predecessor,
        returned_native.event_reconstruction_fibre.clone(),
    );
    let returned = readdress_section(
        &branch.returned,
        returned_native.return_event,
        Some(returned_native.candidate_event),
        returned_native.event_reconstruction_fibre.clone(),
    );
    let identity_chart = ExactRatMatrix::identity(local_faces.len()).map_err(linear)?;
    let full = SituatedDifferenceSection::found(SituatedDifferenceInput {
        candidate,
        returned,
        carrying_occurrence: NativePullbackOccurrence {
            left: returned_native.candidate_event,
            right: returned_native.return_event,
            joining_native: branch.pullback.joining_native,
        },
        occurrence_fibres: vec![occurrence_fibre],
        source_transport: identity_chart.clone(),
        rebased_transport: identity_chart.clone(),
        source_chart: identity_chart.clone(),
        target_chart: identity_chart,
        candidate_coordinates,
        returned_coordinates,
        adjoint_steps: vec![
            CausalAdjointStepInput {
                name: format!("k3-candidate/{}", branch.candidate.address.occurrence.0),
                forward: ExactRatMatrix::new(vec![vec![rat(branch
                    .candidate
                    .incidence
                    .coefficient)]])
                .map_err(linear)?,
                domain_metric: scalar_metric.clone(),
                codomain_metric: overlap_metric.clone(),
            },
            CausalAdjointStepInput {
                name: format!("k3-return/{}", branch.returned.address.occurrence.0),
                forward: ExactRatMatrix::new(vec![vec![rat(branch
                    .returned
                    .incidence
                    .coefficient)]])
                .map_err(linear)?,
                domain_metric: overlap_metric,
                codomain_metric: scalar_metric.clone(),
            },
            CausalAdjointStepInput {
                name: format!(
                    "exchange-return/{}/{}",
                    returned_native.native.0, returned_native.branch
                ),
                forward: supported.clone(),
                domain_metric: scalar_metric.clone(),
                codomain_metric: codomain_metric.clone(),
            },
        ],
        terminal_covector: difference.clone(),
        native_obstructions: Vec::new(),
        open_deposition_boundary: "L2-coupled-morphology-deposition".to_owned(),
        open_exterior: vec![
            "receiver and successor histories outside this local product remain open".to_owned(),
        ],
    })?;
    let parent_candidate = digest_json(&(
        "exchange-native-candidate-fibre/v1",
        returned_native.native,
        returned_native.branch,
        returned_native
            .source_reconstruction_fibre
            .iter()
            .map(|source| (source, &seals[source]))
            .collect::<Vec<_>>(),
    ))?;
    let receiver = digest_json(&(
        "exchange-native-receiver-family/v1",
        returned_native.native,
        &returned_native.returned_faces,
    ))?;
    let mut successor_word = native
        .generators
        .iter()
        .map(|square| format!("exchange-generator/{}", square.generator.0))
        .collect::<Vec<_>>();
    successor_word.extend(
        branch
            .candidate
            .ordered_word
            .iter()
            .chain(&branch.returned.ordered_word)
            .map(|generator| format!("k3-generator/{}", generator.0)),
    );
    let section = SupportedDefectSection {
        address: local_address(&ExchangeProductAddress {
            native: returned_native.native,
            branch: returned_native.branch,
            k3_candidate: branch.candidate.address.clone(),
            k3_return: branch.returned.address.clone(),
            exchange_candidate: returned_native.candidate_event,
            exchange_return: returned_native.return_event,
        }),
        parent_candidate,
        receiver,
        successor_word,
        chart: "native-intelligence.exchange-dependent-free-module.v1".to_owned(),
        ambient_rows,
        ambient_columns,
        support_rows,
        support_columns: vec![support_column],
        supported,
        metrics: DefectMetrics {
            domain: scalar_metric,
            codomain: codomain_metric,
        },
    };
    Ok((full, section))
}

pub(super) fn generator_receipts(
    native_start: NativeStateId,
    branch: usize,
    k3: &K3PullbackBranch,
    compression: &ReceiverHistoryCompression,
    sources: &BTreeSet<ItemId>,
) -> Result<Vec<ExchangeGeneratorSquareReceipt>, ExchangeSituatedProductError> {
    let mut receipts = Vec::with_capacity(compression.generators.len());
    for square in &compression.generators {
        let native_end = square
            .native
            .iter()
            .find(|edge| edge.from == native_start)
            .map(|edge| edge.to)
            .ok_or_else(|| {
                ExchangeSituatedProductError::Exchange(
                    "a generator has no native successor on one fibre".to_owned(),
                )
            })?;
        let source_edges = square
            .source
            .iter()
            .filter(|edge| sources.contains(&edge.from))
            .cloned()
            .collect::<Vec<_>>();
        let exchange_square_commutes = source_edges.len() == sources.len()
            && source_edges
                .iter()
                .all(|edge| compression.encode(edge.to).ok() == Some(native_end));
        receipts.push(ExchangeGeneratorSquareReceipt {
            exchange_generator: square.generator,
            native_start,
            native_end,
            source_edges,
            k3_branch: branch,
            k3_word: k3
                .candidate
                .ordered_word
                .iter()
                .chain(&k3.returned.ordered_word)
                .copied()
                .collect(),
            exchange_square_commutes,
            k3_pullback_word_admitted: !k3.candidate.ordered_word.is_empty()
                && !k3.returned.ordered_word.is_empty(),
        });
    }
    if receipts
        .iter()
        .any(|receipt| !receipt.exchange_square_commutes || !receipt.k3_pullback_word_admitted)
    {
        return Err(ExchangeSituatedProductError::Exchange(
            "a dependent generator square does not commute".to_owned(),
        ));
    }
    Ok(receipts)
}

pub(super) fn mixed_interactions(
    branches: &[K3PullbackBranch],
    constitutive: &NativeReceiverConstitutiveForm,
    natives: &[NativeStateId],
    receiver_population: usize,
) -> Result<Vec<MixedConstitutiveInteractionFamily>, ExchangeSituatedProductError> {
    let receiver_population = i64::try_from(receiver_population).map_err(|_| {
        ExchangeSituatedProductError::Constitutive(
            "receiver population does not fit an exact incidence coefficient".to_owned(),
        )
    })?;
    let scale = rat(receiver_population);
    let mut interactions = Vec::new();
    for left in 0..branches.len() {
        for right in left..branches.len() {
            let storage = constitutive.form.get(left, right).map_err(linear)?.clone();
            if storage == rat(0) {
                continue;
            }
            let candidate_left = branches[left].candidate.emitting_current.clone();
            let candidate_right = branches[right].candidate.emitting_current.clone();
            let returned_left = branches[left].returned.emitting_current.scaled(&scale);
            let returned_right = branches[right].returned.emitting_current.scaled(&scale);
            let left_difference = returned_left.subtract(&candidate_left);
            let right_difference = returned_right.subtract(&candidate_right);
            let candidate_product = candidate_left.multiply(&candidate_right).scaled(&storage);
            let source_linear_terms = candidate_left
                .multiply(&right_difference)
                .add(&left_difference.multiply(&candidate_right))
                .scaled(&storage);
            let mixed_remainder = left_difference.multiply(&right_difference).scaled(&storage);
            let reconstructed_returned_product = candidate_product
                .add(&source_linear_terms)
                .add(&mixed_remainder);
            let returned_product = returned_left.multiply(&returned_right).scaled(&storage);
            if reconstructed_returned_product != returned_product {
                return Err(ExchangeSituatedProductError::Constitutive(
                    "the finite-Leibniz mixed interaction did not reconstruct".to_owned(),
                ));
            }
            interactions.push(MixedConstitutiveInteractionFamily {
                left_branch: left,
                right_branch: right,
                storage,
                candidate_left,
                candidate_right,
                returned_left,
                returned_right,
                left_difference,
                right_difference,
                candidate_product,
                source_linear_terms,
                mixed_remainder,
                reconstructed_returned_product,
                returned_product,
                native_support: natives.to_vec(),
                pair_population: pair_population(natives.len())?,
            });
        }
    }
    Ok(interactions)
}

pub(super) fn validate_mixed_interaction(
    interaction: &MixedConstitutiveInteractionFamily,
) -> Result<(), ExchangeSituatedProductError> {
    let left_difference = interaction
        .returned_left
        .subtract(&interaction.candidate_left);
    let right_difference = interaction
        .returned_right
        .subtract(&interaction.candidate_right);
    let candidate_product = interaction
        .candidate_left
        .multiply(&interaction.candidate_right)
        .scaled(&interaction.storage);
    let source_linear_terms = interaction
        .candidate_left
        .multiply(&right_difference)
        .add(&left_difference.multiply(&interaction.candidate_right))
        .scaled(&interaction.storage);
    let mixed = left_difference
        .multiply(&right_difference)
        .scaled(&interaction.storage);
    let returned = interaction
        .returned_left
        .multiply(&interaction.returned_right)
        .scaled(&interaction.storage);
    if interaction.left_difference != left_difference
        || interaction.right_difference != right_difference
        || interaction.candidate_product != candidate_product
        || interaction.source_linear_terms != source_linear_terms
        || interaction.mixed_remainder != mixed
        || interaction.reconstructed_returned_product
            != candidate_product.add(&source_linear_terms).add(&mixed)
        || interaction.returned_product != returned
        || interaction.reconstructed_returned_product != returned
        || interaction.native_support.is_empty()
        || interaction.pair_population != pair_population(interaction.native_support.len())?
    {
        return Err(ExchangeSituatedProductError::Constitutive(
            "a mixed interaction family fails exact finite-Leibniz reconstruction".to_owned(),
        ));
    }
    Ok(())
}
