use std::collections::BTreeSet;

use serde::Serialize;
use sha2::{Digest, Sha256};

use super::native_family::returned_section;
use super::native_family_types::{
    FactorizationStatus, NativeCarrierChart, NativeGeneratorRelation, NativeHexisRest,
    NativeNaturalityReceipt, NativeShortestSeparator, NativeSuccessorHistory,
    ReceiverHistoryFactorization,
};
use super::native_terrain_types::{
    NativeTerrainCultivation, NativeTerrainDecoder, NativeTerrainError, NativeTerrainInquiry,
    NativeTerrainReconstruction, NativeTerrainRest, NativeTerrainStanding,
    NativeTerrainWithdrawalReceipt, NativeTerrainWorldReturn,
};
use super::types::{ProductionInquiryPresentation, ProductionReceiver};
use super::wire::{decode_components, digest, encode_components, hex};

pub const NATIVE_TERRAIN_STANDING_SCHEMA: &str = "holonics.l3.native-terrain-standing.v1";
pub const NATIVE_TERRAIN_DECODER_SCHEMA: &str = "holonics.l3.native-terrain-decoder.v1";
pub const NATIVE_TERRAIN_FIBRES_SCHEMA: &str = "holonics.l3.native-terrain-fibres.v1";
pub const NATIVE_TERRAIN_INQUIRY_SCHEMA: &str = "holonics.l3.native-terrain-inquiry.v1";

const STANDING_MAGIC: &[u8; 8] = b"HLT3S001";
const DECODER_MAGIC: &[u8; 8] = b"HLT3D001";
const FIBRES_MAGIC: &[u8; 8] = b"HLT3F001";

use holonic_engine::is_sha256_digest as is_digest;

fn receivers() -> Vec<ProductionReceiver> {
    vec![
        ProductionReceiver::Language,
        ProductionReceiver::LeanProof,
        ProductionReceiver::ExactValue,
        ProductionReceiver::UnitDimension,
        ProductionReceiver::ExactVisual,
    ]
}

fn value_digest<T: Serialize>(value: &T) -> Result<String, NativeTerrainError> {
    serde_json::to_vec(value)
        .map(|bytes| digest(&bytes))
        .map_err(|error| NativeTerrainError::Wire(error.to_string()))
}

fn route(residual: i64) -> u32 {
    if residual == 0 {
        1
    } else {
        2
    }
}

fn added_histories(family: u32) -> Vec<NativeSuccessorHistory> {
    vec![
        NativeSuccessorHistory::LocalAblation { family },
        NativeSuccessorHistory::CarrierRebase {
            source: 0,
            target: family,
        },
        NativeSuccessorHistory::CarrierRebase {
            source: 1,
            target: family,
        },
    ]
}

fn chart_support(
    predecessor: &NativeHexisRest,
    occurrence: &str,
) -> Result<Vec<u32>, NativeTerrainError> {
    let occupied = predecessor
        .standing()
        .carrier_charts
        .iter()
        .flat_map(|chart| chart.support_coordinates.iter().copied())
        .collect::<BTreeSet<_>>();
    let material = Sha256::digest(occurrence.as_bytes());
    let dimension = predecessor.standing().generator.dimension as usize;
    let mut support = BTreeSet::new();
    for bytes in material.chunks_exact(4) {
        let coordinate = u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
        if !occupied.contains(&coordinate) {
            support.insert(coordinate);
        }
        if support.len() == dimension {
            break;
        }
    }
    if support.len() != dimension {
        return Err(NativeTerrainError::CarrierChart);
    }
    Ok(support.into_iter().collect())
}

fn generator_action(predecessor: &NativeHexisRest) -> Vec<i64> {
    let generator = &predecessor.standing().generator;
    let dimension = generator.dimension as usize;
    (0..dimension)
        .flat_map(|row| {
            (0..dimension).map(move |column| {
                i64::from(row == column)
                    + i64::from(generator.action_difference_orientation[row])
                        * i64::from(generator.constraint_orientation[column])
            })
        })
        .collect()
}

impl NativeTerrainRest {
    /// A genuine exterior return adds one carrier chart to the already-rested generator.  The L2
    /// predecessor is moved into this continuing owner; no source corpus or proof passage remains
    /// available to later current.
    pub fn cultivate(
        predecessor: NativeHexisRest,
        world_return: NativeTerrainWorldReturn,
        modulus: i64,
    ) -> Result<Self, NativeTerrainError> {
        predecessor
            .validate()
            .map_err(|error| NativeTerrainError::Predecessor(error.to_string()))?;
        if world_return.occurrence.is_empty()
            || !world_return.accepted
            || world_return.lean_exit_status != 0
            || world_return.exact_difference_octets == 0
            || !is_digest(&world_return.emitted_product_sha256)
            || !is_digest(&world_return.returned_lean_sha256)
            || modulus < 2
            || predecessor
                .standing()
                .carrier_charts
                .iter()
                .any(|chart| chart.modulus == modulus)
        {
            return Err(NativeTerrainError::WorldReturn);
        }
        let predecessor_identity = predecessor
            .canonical_identity()
            .map_err(|error| NativeTerrainError::Predecessor(error.to_string()))?;
        let chart_occurrence = format!(
            "l3/chart/{}",
            digest(
                format!(
                    "{}:{}:{}",
                    predecessor_identity, world_return.occurrence, modulus
                )
                .as_bytes()
            )
        );
        let support_coordinates = chart_support(&predecessor, &chart_occurrence)?;
        let chart = NativeCarrierChart {
            source_plate_occurrence: chart_occurrence.clone(),
            returned_occurrence: world_return.occurrence.clone(),
            cultivation_decision_occurrence: format!(
                "l3/decision/{}",
                digest(chart_occurrence.as_bytes())
            ),
            source_plate_sha256: value_digest(&world_return)?,
            modulus,
            support_coordinates,
        };
        let action = generator_action(&predecessor);
        let generator = &predecessor.standing().generator;
        let relation = NativeGeneratorRelation {
            occurrence: format!(
                "l3/relation/{}",
                digest(format!("{}:{}", generator.occurrence, chart_occurrence).as_bytes())
            ),
            source_action_sha256: value_digest(&action)?,
            source_constraint_sha256: value_digest(&generator.constraint_orientation)?,
            source_factor_sha256: value_digest(&generator.action_difference_orientation)?,
            identity_plus_oriented_outer_product: true,
            fixed_kernel_factors: true,
        };
        let family = predecessor.standing().carrier_charts.len() as u32;
        let histories = added_histories(family);
        let mut factors = Vec::new();
        for receiver in receivers() {
            for history in &histories {
                let consequence = match history {
                    NativeSuccessorHistory::LocalAblation { .. } => {
                        "the returned chart's local cultivation withdraws without moving the two inherited carrier charts"
                    }
                    NativeSuccessorHistory::CarrierRebase { source: 0, .. } => {
                        "integer generator transport commutes with reduction into the returned chart while kernel membership carries an exact defect"
                    }
                    NativeSuccessorHistory::CarrierRebase { source: 1, .. } => {
                        "the finite carrier contact returns the absence of a founded unital chart map instead of asserting naturality"
                    }
                    _ => return Err(NativeTerrainError::ReceiverHistory),
                };
                factors.push(ReceiverHistoryFactorization {
                    receiver,
                    history: history.clone(),
                    status: if matches!(history, NativeSuccessorHistory::LocalAblation { .. }) {
                        FactorizationStatus::Exact
                    } else {
                        FactorizationStatus::ExactDefect
                    },
                    consequence: consequence.to_owned(),
                });
            }
        }

        let integer_intervention = vec![1, modulus - 1, 0];
        let (integer_transport, integer_residual) = returned_section(
            &integer_intervention,
            &generator.constraint_orientation,
            &generator.action_difference_orientation,
            0,
        )
        .map_err(|_| NativeTerrainError::CarrierChart)?;
        let (returned_transport, returned_residual) = returned_section(
            &integer_intervention,
            &generator.constraint_orientation,
            &generator.action_difference_orientation,
            modulus,
        )
        .map_err(|_| NativeTerrainError::CarrierChart)?;
        let rebased = integer_transport
            .iter()
            .map(|value| value.rem_euclid(modulus))
            .collect::<Vec<_>>();
        let integer_contact = NativeNaturalityReceipt {
            source_chart: 0,
            target_chart: family,
            intervention_section: integer_intervention.clone(),
            source_transport: integer_transport,
            target_transport: returned_transport.clone(),
            rebased_source_transport: rebased.clone(),
            generator_square_commutes: rebased == returned_transport,
            source_route: route(integer_residual),
            target_route: route(returned_residual),
            cultivation_square_commutes: route(integer_residual) == route(returned_residual),
            exact_defect: format!(
                "integer residual {integer_residual} becomes {returned_residual} in the modulus-{modulus} chart"
            ),
        };
        let finite_intervention = vec![1, 1, 0];
        let (finite_transport, finite_residual) = returned_section(
            &finite_intervention,
            &generator.constraint_orientation,
            &generator.action_difference_orientation,
            predecessor.standing().carrier_charts[1].modulus,
        )
        .map_err(|_| NativeTerrainError::CarrierChart)?;
        let (finite_target_transport, finite_target_residual) = returned_section(
            &finite_intervention,
            &generator.constraint_orientation,
            &generator.action_difference_orientation,
            modulus,
        )
        .map_err(|_| NativeTerrainError::CarrierChart)?;
        let finite_contact = NativeNaturalityReceipt {
            source_chart: 1,
            target_chart: family,
            intervention_section: finite_intervention.clone(),
            source_transport: finite_transport,
            target_transport: finite_target_transport,
            rebased_source_transport: Vec::new(),
            generator_square_commutes: false,
            source_route: route(finite_residual),
            target_route: route(finite_target_residual),
            cultivation_square_commutes: false,
            exact_defect: format!(
                "no unital carrier chart is founded from modulus {} to modulus {modulus}",
                predecessor.standing().carrier_charts[1].modulus
            ),
        };
        let separators = vec![
            NativeShortestSeparator {
                proposed_quotient: format!(
                    "equal-present zero section across the integer and modulus-{modulus} charts"
                ),
                equal_present_sections: vec![vec![0, 0, 0], vec![0, 0, 0]],
                successor_sections: vec![
                    integer_intervention.clone(),
                    integer_intervention.clone(),
                ],
                returned_residuals: vec![integer_residual, returned_residual],
                returned_routes: vec![route(integer_residual), route(returned_residual)],
                shortest_word: vec![0],
            },
            NativeShortestSeparator {
                proposed_quotient: format!(
                    "unfounded finite-carrier identification from modulus {} to modulus {modulus}",
                    predecessor.standing().carrier_charts[1].modulus
                ),
                equal_present_sections: vec![vec![0, 0, 0], vec![0, 0, 0]],
                successor_sections: vec![finite_intervention.clone(), finite_intervention],
                returned_residuals: vec![finite_residual, finite_target_residual],
                returned_routes: vec![route(finite_residual), route(finite_target_residual)],
                shortest_word: vec![0],
            },
        ];
        let rest = Self {
            predecessor,
            standing: NativeTerrainStanding {
                schema: NATIVE_TERRAIN_STANDING_SCHEMA.to_owned(),
                cultivation: NativeTerrainCultivation {
                    decision_occurrence: chart.cultivation_decision_occurrence.clone(),
                    predecessor_identity,
                    world_return,
                    carrier_chart: chart.clone(),
                    generator_relation: relation,
                },
                open_exterior: vec![
                    "additional carrier charts require their own returned passage".to_owned(),
                    "nonlinear fixed varieties remain outside the oriented generator".to_owned(),
                    "finite-carrier contact remains obstructed without a founded chart map"
                        .to_owned(),
                ],
            },
            decoder: NativeTerrainDecoder {
                schema: NATIVE_TERRAIN_DECODER_SCHEMA.to_owned(),
                added_histories: histories,
                added_factorizations: factors,
                carrier_contacts: vec![integer_contact, finite_contact],
            },
            reconstruction: NativeTerrainReconstruction {
                schema: NATIVE_TERRAIN_FIBRES_SCHEMA.to_owned(),
                generator_fibre_addition: vec![
                    format!("{}/action", chart.source_plate_occurrence),
                    format!("{}/constraint", chart.source_plate_occurrence),
                    format!("{}/action-difference-factor", chart.source_plate_occurrence),
                ],
                complete_fibres: vec![
                    "returned-chart-lineage-fibre".to_owned(),
                    "shared-generator-incidence-fibre".to_owned(),
                    "integer-reduction-naturality-and-kernel-defect-fibre".to_owned(),
                    "finite-carrier-contact-obstruction-fibre".to_owned(),
                    "local-cultivation-ablation-fibre".to_owned(),
                    "exact-immediate-predecessor-withdrawal-fibre".to_owned(),
                ],
                shortest_separators: separators,
                unresolved_families: vec![
                    "unreturned carrier charts".to_owned(),
                    "nonlinear fixed varieties".to_owned(),
                    "unfounded finite-carrier maps".to_owned(),
                ],
            },
        };
        rest.validate()?;
        Ok(rest)
    }

    pub fn read(
        standing: &[u8],
        decoder: &[u8],
        fibres: &[u8],
    ) -> Result<Self, NativeTerrainError> {
        let standing = decode_components(STANDING_MAGIC, standing, 2)
            .map_err(|error| NativeTerrainError::Wire(error.to_string()))?;
        let decoder = decode_components(DECODER_MAGIC, decoder, 2)
            .map_err(|error| NativeTerrainError::Wire(error.to_string()))?;
        let fibres = decode_components(FIBRES_MAGIC, fibres, 2)
            .map_err(|error| NativeTerrainError::Wire(error.to_string()))?;
        let predecessor = NativeHexisRest::read(&standing[0], &decoder[0], &fibres[0])
            .map_err(|error| NativeTerrainError::Predecessor(error.to_string()))?;
        let rest = Self {
            predecessor,
            standing: serde_json::from_slice(&standing[1])
                .map_err(|error| NativeTerrainError::Wire(error.to_string()))?,
            decoder: serde_json::from_slice(&decoder[1])
                .map_err(|error| NativeTerrainError::Wire(error.to_string()))?,
            reconstruction: serde_json::from_slice(&fibres[1])
                .map_err(|error| NativeTerrainError::Wire(error.to_string()))?,
        };
        rest.validate()?;
        Ok(rest)
    }

    pub fn standing_bytes(&self) -> Result<Vec<u8>, NativeTerrainError> {
        self.validate()?;
        encode_components(
            STANDING_MAGIC,
            &[
                self.predecessor
                    .standing_bytes()
                    .map_err(|error| NativeTerrainError::Predecessor(error.to_string()))?,
                serde_json::to_vec(&self.standing)
                    .map_err(|error| NativeTerrainError::Wire(error.to_string()))?,
            ],
        )
        .map_err(|error| NativeTerrainError::Wire(error.to_string()))
    }

    pub fn decoder_bytes(&self) -> Result<Vec<u8>, NativeTerrainError> {
        self.validate()?;
        encode_components(
            DECODER_MAGIC,
            &[
                self.predecessor
                    .decoder_bytes()
                    .map_err(|error| NativeTerrainError::Predecessor(error.to_string()))?,
                serde_json::to_vec(&self.decoder)
                    .map_err(|error| NativeTerrainError::Wire(error.to_string()))?,
            ],
        )
        .map_err(|error| NativeTerrainError::Wire(error.to_string()))
    }

    pub fn fibre_bytes(&self) -> Result<Vec<u8>, NativeTerrainError> {
        self.validate()?;
        encode_components(
            FIBRES_MAGIC,
            &[
                self.predecessor
                    .fibre_bytes()
                    .map_err(|error| NativeTerrainError::Predecessor(error.to_string()))?,
                serde_json::to_vec(&self.reconstruction)
                    .map_err(|error| NativeTerrainError::Wire(error.to_string()))?,
            ],
        )
        .map_err(|error| NativeTerrainError::Wire(error.to_string()))
    }

    pub fn canonical_identity(&self) -> Result<String, NativeTerrainError> {
        self.validate()?;
        let predecessor = self
            .predecessor
            .canonical_identity()
            .map_err(|error| NativeTerrainError::Predecessor(error.to_string()))?;
        let standing = serde_json::to_vec(&self.standing)
            .map_err(|error| NativeTerrainError::Wire(error.to_string()))?;
        let decoder = serde_json::to_vec(&self.decoder)
            .map_err(|error| NativeTerrainError::Wire(error.to_string()))?;
        let reconstruction = serde_json::to_vec(&self.reconstruction)
            .map_err(|error| NativeTerrainError::Wire(error.to_string()))?;
        let mut hasher = Sha256::new();
        for bytes in [
            predecessor.as_bytes(),
            standing.as_slice(),
            decoder.as_slice(),
            reconstruction.as_slice(),
        ] {
            hasher.update((bytes.len() as u64).to_le_bytes());
            hasher.update(bytes);
        }
        Ok(hex(hasher.finalize()))
    }

    pub fn found_inquiry(
        &self,
        presentation: ProductionInquiryPresentation,
        receiver_family: Vec<ProductionReceiver>,
        sections: Vec<Vec<i64>>,
        revisited_histories: Vec<NativeSuccessorHistory>,
        prior_history_occurrences: Vec<String>,
        ablated_family: Option<u32>,
    ) -> Result<NativeTerrainInquiry, NativeTerrainError> {
        let mut inquiry = NativeTerrainInquiry {
            schema: NATIVE_TERRAIN_INQUIRY_SCHEMA.to_owned(),
            occurrence: String::new(),
            predecessor_rest_sha256: self.canonical_identity()?,
            presentation,
            receiver_family,
            sections,
            revisited_histories,
            prior_history_occurrences,
            ablated_family,
        };
        inquiry.occurrence = format!("l3/inquiry/{}", inquiry_body(&inquiry)?);
        self.admit_inquiry(&inquiry)?;
        Ok(inquiry)
    }

    pub fn admit_inquiry(&self, inquiry: &NativeTerrainInquiry) -> Result<(), NativeTerrainError> {
        let mut inquiry_receivers = inquiry.receiver_family.clone();
        inquiry_receivers.sort_by_key(|receiver| *receiver as u8);
        let mut declared_receivers = receivers();
        declared_receivers.sort_by_key(|receiver| *receiver as u8);
        let all_histories = self
            .predecessor
            .decoder()
            .declared_histories
            .iter()
            .chain(&self.decoder.added_histories)
            .collect::<Vec<_>>();
        if inquiry.schema != NATIVE_TERRAIN_INQUIRY_SCHEMA
            || inquiry.occurrence != format!("l3/inquiry/{}", inquiry_body(inquiry)?)
            || inquiry.predecessor_rest_sha256 != self.canonical_identity()?
            || inquiry_receivers != declared_receivers
            || inquiry.sections.len() != self.chart_count()
            || inquiry.sections.iter().any(|section| {
                section.len() != self.predecessor.standing().generator.dimension as usize
            })
            || inquiry.presentation.natural_language.is_empty()
            || inquiry.presentation.notation.is_empty()
            || !is_digest(&inquiry.presentation.vector_face_sha256)
            || !is_digest(&inquiry.presentation.raster_face_sha256)
            || inquiry.revisited_histories.is_empty()
            || inquiry
                .revisited_histories
                .iter()
                .any(|history| !all_histories.contains(&history))
            || inquiry.prior_history_occurrences.is_empty()
            || inquiry
                .ablated_family
                .is_some_and(|family| family as usize >= self.chart_count())
        {
            return Err(NativeTerrainError::Inquiry);
        }
        Ok(())
    }

    pub fn sections_wire(&self, inquiry: &NativeTerrainInquiry) -> Vec<i64> {
        inquiry.sections.iter().flatten().copied().collect()
    }

    pub fn constraint_orientation(&self) -> &[i8] {
        self.predecessor.constraint_orientation()
    }

    pub fn factor_orientation(&self) -> &[i8] {
        self.predecessor.factor_orientation()
    }

    pub fn moduli_wire(&self) -> Vec<i64> {
        self.predecessor
            .standing()
            .carrier_charts
            .iter()
            .map(|chart| chart.modulus)
            .chain(std::iter::once(
                self.standing.cultivation.carrier_chart.modulus,
            ))
            .collect()
    }

    pub fn cultivation_flags(&self, inquiry: &NativeTerrainInquiry) -> Vec<u32> {
        (0..self.chart_count())
            .map(|family| u32::from(inquiry.ablated_family != Some(family as u32)))
            .collect()
    }

    pub fn chart_count(&self) -> usize {
        self.predecessor.standing().carrier_charts.len() + 1
    }

    pub fn standing(&self) -> &NativeTerrainStanding {
        &self.standing
    }

    pub fn decoder(&self) -> &NativeTerrainDecoder {
        &self.decoder
    }

    pub fn reconstruction(&self) -> &NativeTerrainReconstruction {
        &self.reconstruction
    }

    pub fn predecessor(&self) -> &NativeHexisRest {
        &self.predecessor
    }

    pub fn factorization_population(&self) -> usize {
        self.predecessor.decoder().factorizations.len() + self.decoder.added_factorizations.len()
    }

    pub fn withdraw(
        self,
    ) -> Result<(NativeHexisRest, NativeTerrainWithdrawalReceipt), NativeTerrainError> {
        let cultivated_identity = self.canonical_identity()?;
        let restored_identity = self
            .predecessor
            .canonical_identity()
            .map_err(|error| NativeTerrainError::Predecessor(error.to_string()))?;
        let receipt = NativeTerrainWithdrawalReceipt {
            cultivated_identity,
            predecessor_identity: self.standing.cultivation.predecessor_identity.clone(),
            restored_identity: restored_identity.clone(),
            withdrawn_chart_occurrence: self
                .standing
                .cultivation
                .carrier_chart
                .source_plate_occurrence
                .clone(),
            exact_immediate_predecessor_restored: restored_identity
                == self.standing.cultivation.predecessor_identity,
        };
        if !receipt.exact_immediate_predecessor_restored {
            return Err(NativeTerrainError::Withdrawal);
        }
        Ok((self.predecessor, receipt))
    }

    pub fn validate(&self) -> Result<(), NativeTerrainError> {
        self.predecessor
            .validate()
            .map_err(|error| NativeTerrainError::Predecessor(error.to_string()))?;
        let predecessor_identity = self
            .predecessor
            .canonical_identity()
            .map_err(|error| NativeTerrainError::Predecessor(error.to_string()))?;
        let cultivation = &self.standing.cultivation;
        let chart = &cultivation.carrier_chart;
        let relation = &cultivation.generator_relation;
        let mut occupied = self
            .predecessor
            .standing()
            .carrier_charts
            .iter()
            .flat_map(|chart| chart.support_coordinates.iter().copied())
            .collect::<BTreeSet<_>>();
        if self.standing.schema != NATIVE_TERRAIN_STANDING_SCHEMA
            || cultivation.decision_occurrence.is_empty()
            || cultivation.predecessor_identity != predecessor_identity
            || cultivation.world_return.occurrence != chart.returned_occurrence
            || !cultivation.world_return.accepted
            || cultivation.world_return.lean_exit_status != 0
            || cultivation.world_return.exact_difference_octets == 0
            || !is_digest(&cultivation.world_return.emitted_product_sha256)
            || !is_digest(&cultivation.world_return.returned_lean_sha256)
            || chart.source_plate_occurrence.is_empty()
            || chart.cultivation_decision_occurrence != cultivation.decision_occurrence
            || !is_digest(&chart.source_plate_sha256)
            || chart.modulus < 2
            || self
                .predecessor
                .standing()
                .carrier_charts
                .iter()
                .any(|existing| existing.modulus == chart.modulus)
            || chart.support_coordinates.len()
                != self.predecessor.standing().generator.dimension as usize
            || chart
                .support_coordinates
                .windows(2)
                .any(|pair| pair[0] >= pair[1])
            || chart
                .support_coordinates
                .iter()
                .any(|coordinate| !occupied.insert(*coordinate))
            || relation.occurrence.is_empty()
            || !is_digest(&relation.source_action_sha256)
            || !is_digest(&relation.source_constraint_sha256)
            || !is_digest(&relation.source_factor_sha256)
            || !relation.identity_plus_oriented_outer_product
            || !relation.fixed_kernel_factors
            || self.standing.open_exterior.is_empty()
        {
            return Err(NativeTerrainError::CarrierChart);
        }
        let family = self.predecessor.standing().carrier_charts.len() as u32;
        if self.decoder.schema != NATIVE_TERRAIN_DECODER_SCHEMA
            || self.decoder.added_histories != added_histories(family)
            || self.decoder.added_factorizations.len()
                != receivers().len() * self.decoder.added_histories.len()
            || self.decoder.carrier_contacts.len() != 2
        {
            return Err(NativeTerrainError::ReceiverHistory);
        }
        for receiver in receivers() {
            for history in &self.decoder.added_histories {
                let receipts = self
                    .decoder
                    .added_factorizations
                    .iter()
                    .filter(|receipt| receipt.receiver == receiver && receipt.history == *history)
                    .collect::<Vec<_>>();
                if receipts.len() != 1
                    || receipts[0].consequence.is_empty()
                    || matches!(history, NativeSuccessorHistory::LocalAblation { .. })
                        != matches!(receipts[0].status, FactorizationStatus::Exact)
                {
                    return Err(NativeTerrainError::ReceiverHistory);
                }
            }
        }
        let integer = &self.decoder.carrier_contacts[0];
        let finite = &self.decoder.carrier_contacts[1];
        if integer.source_chart != 0
            || integer.target_chart != family
            || !integer.generator_square_commutes
            || integer.cultivation_square_commutes
            || integer.source_route == integer.target_route
            || finite.source_chart != 1
            || finite.target_chart != family
            || finite.generator_square_commutes
            || finite.rebased_source_transport.len() != 0
            || finite.exact_defect.is_empty()
        {
            return Err(NativeTerrainError::ReceiverHistory);
        }
        if self.reconstruction.schema != NATIVE_TERRAIN_FIBRES_SCHEMA
            || self.reconstruction.generator_fibre_addition.len() != 3
            || self.reconstruction.complete_fibres.len() < 6
            || self.reconstruction.shortest_separators.len() != 2
            || self.reconstruction.unresolved_families.is_empty()
        {
            return Err(NativeTerrainError::Reconstruction);
        }
        Ok(())
    }
}

fn inquiry_body(inquiry: &NativeTerrainInquiry) -> Result<String, NativeTerrainError> {
    #[derive(Serialize)]
    struct Body<'a> {
        schema: &'a str,
        predecessor_rest_sha256: &'a str,
        presentation: &'a ProductionInquiryPresentation,
        receiver_family: &'a [ProductionReceiver],
        sections: &'a [Vec<i64>],
        revisited_histories: &'a [NativeSuccessorHistory],
        prior_history_occurrences: &'a [String],
        ablated_family: Option<u32>,
    }
    serde_json::to_vec(&Body {
        schema: &inquiry.schema,
        predecessor_rest_sha256: &inquiry.predecessor_rest_sha256,
        presentation: &inquiry.presentation,
        receiver_family: &inquiry.receiver_family,
        sections: &inquiry.sections,
        revisited_histories: &inquiry.revisited_histories,
        prior_history_occurrences: &inquiry.prior_history_occurrences,
        ablated_family: inquiry.ablated_family,
    })
    .map(|bytes| digest(&bytes))
    .map_err(|error| NativeTerrainError::Wire(error.to_string()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn integer_reduction_commutes_while_mod_two_to_mod_three_stays_obstructed() {
        let section = [1, 2, 0];
        let constraint = [1, 1, -1];
        let factor = [-1, -1, 1];
        let (integer, integer_residual) =
            returned_section(&section, &constraint, &factor, 0).expect("integer");
        let (mod_three, mod_three_residual) =
            returned_section(&section, &constraint, &factor, 3).expect("mod three");
        assert_eq!(integer, vec![-2, -1, 3]);
        assert_eq!(integer_residual, 3);
        assert_eq!(mod_three, vec![1, 2, 0]);
        assert_eq!(mod_three_residual, 0);
        assert_eq!(
            integer
                .iter()
                .map(|value| value.rem_euclid(3))
                .collect::<Vec<_>>(),
            mod_three
        );
    }
}
