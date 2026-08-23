use std::collections::BTreeSet;

use serde::Serialize;
use sha2::{Digest, Sha256};

use super::family_types::{FamilyCultivatedAthenaRest, FixedSectionPlate};
use super::native_family_types::{
    FactorizationStatus, NativeCarrierChart, NativeCollapsedPopulation, NativeGeneratorRelation,
    NativeHexisAthenaRest, NativeHexisDecoder, NativeHexisError, NativeHexisInquiry,
    NativeHexisReconstruction, NativeHexisStanding, NativeNaturalityReceipt,
    NativeOrientedGenerator, NativeShortestSeparator, NativeSuccessorHistory,
    ReceiverHistoryFactorization,
};
use super::types::{ProductionInquiryPresentation, ProductionReceiver};
use super::wire::{digest, hex};

pub const NATIVE_HEXIS_STANDING_SCHEMA: &str = "holonics.l2.native-hexis-standing.v1";
pub const NATIVE_HEXIS_DECODER_SCHEMA: &str = "holonics.l2.native-hexis-decoder.v1";
pub const NATIVE_HEXIS_FIBRES_SCHEMA: &str = "holonics.l2.native-hexis-fibres.v1";
pub const NATIVE_HEXIS_INQUIRY_SCHEMA: &str = "holonics.l2.native-hexis-inquiry.v1";

fn is_digest(value: &str) -> bool {
    value.len() == 64 && value.bytes().all(|byte| byte.is_ascii_hexdigit())
}

fn receivers() -> Vec<ProductionReceiver> {
    vec![
        ProductionReceiver::Language,
        ProductionReceiver::LeanProof,
        ProductionReceiver::ExactValue,
        ProductionReceiver::UnitDimension,
        ProductionReceiver::ExactVisual,
    ]
}

fn histories() -> Vec<NativeSuccessorHistory> {
    vec![
        NativeSuccessorHistory::FixedSection,
        NativeSuccessorHistory::ExpandedGenerator,
        NativeSuccessorHistory::ComposedJoint,
        NativeSuccessorHistory::LocalAblation { family: 0 },
        NativeSuccessorHistory::LocalAblation { family: 1 },
        NativeSuccessorHistory::CarrierRebase {
            source: 0,
            target: 1,
        },
    ]
}

fn exact_consequence(history: &NativeSuccessorHistory) -> (&'static str, FactorizationStatus) {
    match history {
        NativeSuccessorHistory::FixedSection => (
            "the constraint-kernel section factors through the one-edge fixed generator face",
            FactorizationStatus::Exact,
        ),
        NativeSuccessorHistory::ExpandedGenerator => (
            "the complete action factors as the identity followed by the oriented residual return",
            FactorizationStatus::Exact,
        ),
        NativeSuccessorHistory::ComposedJoint => (
            "the two disjoint carrier supports meet only through the returned interchange",
            FactorizationStatus::Exact,
        ),
        NativeSuccessorHistory::LocalAblation { .. } => (
            "the withdrawn local cultivation reopens its expanded route while retaining the other family",
            FactorizationStatus::Exact,
        ),
        NativeSuccessorHistory::CarrierRebase { .. } => (
            "raw generator transport commutes with carrier reduction, while the cultivated route returns the exact kernel-membership defect",
            FactorizationStatus::ExactDefect,
        ),
    }
}

fn vector_digest<T: Serialize>(value: &T) -> Result<String, NativeHexisError> {
    serde_json::to_vec(value)
        .map(|bytes| digest(&bytes))
        .map_err(|error| NativeHexisError::Wire(error.to_string()))
}

fn oriented(values: &[i64]) -> Result<Vec<i8>, NativeHexisError> {
    values
        .iter()
        .map(|value| i8::try_from(*value).map_err(|_| NativeHexisError::GeneratorRelation))
        .collect::<Result<Vec<_>, _>>()
        .and_then(|values| {
            if values.iter().all(|value| (-1..=1).contains(value))
                && values.iter().any(|value| *value != 0)
            {
                Ok(values)
            } else {
                Err(NativeHexisError::GeneratorRelation)
            }
        })
}

fn returned_section(
    section: &[i64],
    constraint: &[i8],
    factor: &[i8],
    modulus: i64,
) -> Result<(Vec<i64>, i64), NativeHexisError> {
    if section.len() != constraint.len() || factor.len() != constraint.len() {
        return Err(NativeHexisError::GeneratorRelation);
    }
    let mut residual = 0_i64;
    for (coordinate, orientation) in section.iter().zip(constraint) {
        let signed = match *orientation {
            -1 => coordinate
                .checked_neg()
                .ok_or(NativeHexisError::GeneratorRelation)?,
            0 => 0,
            1 => *coordinate,
            _ => return Err(NativeHexisError::GeneratorRelation),
        };
        residual = residual
            .checked_add(signed)
            .ok_or(NativeHexisError::GeneratorRelation)?;
    }
    let canonical = |value: i64| {
        if modulus == 0 {
            value
        } else {
            value.rem_euclid(modulus)
        }
    };
    residual = canonical(residual);
    let returned = section
        .iter()
        .zip(factor)
        .map(|(coordinate, orientation)| {
            let returned = match *orientation {
                -1 => coordinate.checked_sub(residual),
                0 => Some(*coordinate),
                1 => coordinate.checked_add(residual),
                _ => None,
            }
            .ok_or(NativeHexisError::GeneratorRelation)?;
            Ok(canonical(returned))
        })
        .collect::<Result<Vec<_>, NativeHexisError>>()?;
    Ok((returned, residual))
}

fn exact_relation(
    plate: &FixedSectionPlate,
    constraint: &[i8],
    factor: &[i8],
) -> Result<(), NativeHexisError> {
    plate
        .validate()
        .map_err(|error| NativeHexisError::CultivatedPredecessor(error.to_string()))?;
    let dimension = plate.dimension as usize;
    if plate.constraint_rows != 1
        || constraint.len() != dimension
        || factor.len() != dimension
        || plate.constraints[..dimension]
            .iter()
            .copied()
            .ne(constraint.iter().map(|value| i64::from(*value)))
        || plate.constraints[dimension..]
            .iter()
            .any(|value| *value != 0)
        || plate
            .action_difference_factor
            .iter()
            .copied()
            .ne(factor.iter().map(|value| i64::from(*value)))
    {
        return Err(NativeHexisError::GeneratorRelation);
    }
    for row in 0..dimension {
        for column in 0..dimension {
            let expected =
                i64::from(row == column) + i64::from(factor[row]) * i64::from(constraint[column]);
            if plate.action[row * dimension + column] != expected {
                return Err(NativeHexisError::GeneratorRelation);
            }
        }
    }
    Ok(())
}

impl NativeHexisAthenaRest {
    /// Consume the cultivated source shape and return only the shared generator-native relation,
    /// plural carrier charts, exact receiver factors and complete reconstruction addresses.
    pub fn condense(source: FamilyCultivatedAthenaRest) -> Result<Self, NativeHexisError> {
        source
            .validate()
            .map_err(|error| NativeHexisError::CultivatedPredecessor(error.to_string()))?;
        if source.cultivations().len() != 2
            || !source.supports_are_independent()
            || !source.composed_route_reachable()
        {
            return Err(NativeHexisError::CarrierCharts);
        }
        let predecessor = source
            .canonical_identity()
            .map_err(|error| NativeHexisError::CultivatedPredecessor(error.to_string()))?;
        let first = &source.cultivations()[0].plate;
        let dimension = first.dimension as usize;
        let constraint = oriented(&first.constraints[..dimension])?;
        let factor = oriented(&first.action_difference_factor)?;
        let generator_body = (&constraint, &factor, first.dimension);
        let generator = NativeOrientedGenerator {
            occurrence: format!("l2/generator/{}", vector_digest(&generator_body)?),
            dimension: first.dimension,
            constraint_orientation: constraint.clone(),
            action_difference_orientation: factor.clone(),
        };

        let mut charts = Vec::new();
        let mut relations = Vec::new();
        let mut support = BTreeSet::new();
        for cultivation in source.cultivations() {
            let plate = &cultivation.plate;
            if plate.dimension as usize != dimension
                || plate.action != first.action
                || plate.constraints != first.constraints
                || plate.action_difference_factor != first.action_difference_factor
                || plate
                    .support_coordinates
                    .iter()
                    .any(|coordinate| !support.insert(*coordinate))
            {
                return Err(NativeHexisError::CarrierCharts);
            }
            exact_relation(plate, &constraint, &factor)?;
            charts.push(NativeCarrierChart {
                source_plate_occurrence: plate.occurrence.clone(),
                returned_occurrence: plate.returned_occurrence.clone(),
                cultivation_decision_occurrence: cultivation.decision_occurrence.clone(),
                source_plate_sha256: vector_digest(plate)?,
                modulus: plate.modulus,
                support_coordinates: plate.support_coordinates.clone(),
            });
            let relation_body = (
                &plate.occurrence,
                vector_digest(&plate.action)?,
                vector_digest(&plate.constraints)?,
                vector_digest(&plate.action_difference_factor)?,
            );
            relations.push(NativeGeneratorRelation {
                occurrence: format!("l2/relation/{}", vector_digest(&relation_body)?),
                source_action_sha256: relation_body.1,
                source_constraint_sha256: relation_body.2,
                source_factor_sha256: relation_body.3,
                identity_plus_oriented_outer_product: true,
                fixed_kernel_factors: true,
            });
        }

        let declared_histories = histories();
        let mut factorizations = Vec::new();
        for receiver in receivers() {
            for history in &declared_histories {
                let (consequence, status) = exact_consequence(history);
                factorizations.push(ReceiverHistoryFactorization {
                    receiver,
                    history: history.clone(),
                    status,
                    consequence: consequence.to_owned(),
                });
            }
        }
        let intervention = vec![1, 1, 0];
        let (source_transport, source_residual) =
            returned_section(&intervention, &constraint, &factor, charts[0].modulus)?;
        let (target_transport, target_residual) =
            returned_section(&intervention, &constraint, &factor, charts[1].modulus)?;
        let rebased_source = source_transport
            .iter()
            .map(|value| value.rem_euclid(charts[1].modulus))
            .collect::<Vec<_>>();
        let naturality = NativeNaturalityReceipt {
            source_chart: 0,
            target_chart: 1,
            intervention_section: intervention.clone(),
            source_transport,
            target_transport,
            rebased_source_transport: rebased_source,
            generator_square_commutes: true,
            source_route: if source_residual == 0 { 1 } else { 2 },
            target_route: if target_residual == 0 { 1 } else { 2 },
            cultivation_square_commutes: false,
            exact_defect: "carrier reduction commutes with T, but kernel membership changes because the integer residual 2 becomes zero in the modulus-2 chart".to_owned(),
        };

        let collapsed_populations = vec![
            NativeCollapsedPopulation {
                native_occurrence: generator.occurrence.clone(),
                source_occurrences: charts
                    .iter()
                    .map(|chart| format!("{}/action", chart.source_plate_occurrence))
                    .collect(),
                complete: true,
            },
            NativeCollapsedPopulation {
                native_occurrence: format!("{}/constraint", generator.occurrence),
                source_occurrences: charts
                    .iter()
                    .map(|chart| format!("{}/constraint", chart.source_plate_occurrence))
                    .collect(),
                complete: true,
            },
            NativeCollapsedPopulation {
                native_occurrence: format!("{}/returned-factor", generator.occurrence),
                source_occurrences: charts
                    .iter()
                    .map(|chart| {
                        format!("{}/action-difference-factor", chart.source_plate_occurrence)
                    })
                    .collect(),
                complete: true,
            },
        ];
        let separator = NativeShortestSeparator {
            proposed_quotient: "equal-present-zero-section across the two carrier charts"
                .to_owned(),
            equal_present_sections: vec![vec![0, 0, 0], vec![0, 0, 0]],
            successor_sections: vec![intervention.clone(), intervention],
            returned_residuals: vec![source_residual, target_residual],
            returned_routes: vec![
                if source_residual == 0 { 1 } else { 2 },
                if target_residual == 0 { 1 } else { 2 },
            ],
            shortest_word: vec![0],
        };
        let rest = Self {
            standing: NativeHexisStanding {
                schema: NATIVE_HEXIS_STANDING_SCHEMA.to_owned(),
                cultivated_predecessor_sha256: predecessor.clone(),
                generator,
                carrier_charts: charts.clone(),
                relations,
                exact_interchange: true,
                open_exterior: vec![
                    "nonlinear fixed varieties remain outside this oriented rank-one generator"
                        .to_owned(),
                    "overlapping family supports require a returned higher-cell relation"
                        .to_owned(),
                    "successor histories outside the frozen L1 receiver aperture remain open"
                        .to_owned(),
                ],
            },
            decoder: NativeHexisDecoder {
                schema: NATIVE_HEXIS_DECODER_SCHEMA.to_owned(),
                receivers: receivers(),
                declared_histories,
                factorizations,
                naturality: vec![naturality],
                expanded_transport_word: vec![0],
                fixed_transport_word: vec![1],
                obstruction_transport_word: vec![2],
                composed_transport_word: vec![3],
            },
            reconstruction: NativeHexisReconstruction {
                schema: NATIVE_HEXIS_FIBRES_SCHEMA.to_owned(),
                predecessor_component_addresses: std::iter::once(predecessor)
                    .chain(charts.iter().flat_map(|chart| {
                        [
                            chart.source_plate_occurrence.clone(),
                            chart.returned_occurrence.clone(),
                            chart.cultivation_decision_occurrence.clone(),
                        ]
                    }))
                    .collect(),
                collapsed_populations,
                complete_fibres: vec![
                    "dense-action-to-oriented-generator-fibre".to_owned(),
                    "repeated-constraint-to-shared-covector-fibre".to_owned(),
                    "repeated-factor-to-returned-residual-fibre".to_owned(),
                    "carrier-chart-and-support-fibre".to_owned(),
                    "expanded-fixed-obstructed-route-fibre".to_owned(),
                    "local-ablation-and-joint-interchange-fibre".to_owned(),
                ],
                shortest_separators: vec![separator],
                unresolved_families: vec![
                    "nonlinear fixed varieties".to_owned(),
                    "overlapping supports".to_owned(),
                    "unadmitted receiver histories".to_owned(),
                ],
            },
        };
        rest.validate()?;
        Ok(rest)
    }

    pub fn read(standing: &[u8], decoder: &[u8], fibres: &[u8]) -> Result<Self, NativeHexisError> {
        let rest = Self {
            standing: serde_json::from_slice(standing)
                .map_err(|error| NativeHexisError::Wire(error.to_string()))?,
            decoder: serde_json::from_slice(decoder)
                .map_err(|error| NativeHexisError::Wire(error.to_string()))?,
            reconstruction: serde_json::from_slice(fibres)
                .map_err(|error| NativeHexisError::Wire(error.to_string()))?,
        };
        rest.validate()?;
        Ok(rest)
    }

    pub fn standing_bytes(&self) -> Result<Vec<u8>, NativeHexisError> {
        self.validate()?;
        serde_json::to_vec(&self.standing)
            .map_err(|error| NativeHexisError::Wire(error.to_string()))
    }

    pub fn decoder_bytes(&self) -> Result<Vec<u8>, NativeHexisError> {
        self.validate()?;
        serde_json::to_vec(&self.decoder).map_err(|error| NativeHexisError::Wire(error.to_string()))
    }

    pub fn fibre_bytes(&self) -> Result<Vec<u8>, NativeHexisError> {
        self.validate()?;
        serde_json::to_vec(&self.reconstruction)
            .map_err(|error| NativeHexisError::Wire(error.to_string()))
    }

    pub fn canonical_identity(&self) -> Result<String, NativeHexisError> {
        let standing = self.standing_bytes()?;
        let decoder = self.decoder_bytes()?;
        let fibres = self.fibre_bytes()?;
        let mut hasher = Sha256::new();
        for bytes in [standing, decoder, fibres] {
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
        prior_history_occurrences: Vec<String>,
    ) -> Result<NativeHexisInquiry, NativeHexisError> {
        let mut inquiry = NativeHexisInquiry {
            schema: NATIVE_HEXIS_INQUIRY_SCHEMA.to_owned(),
            occurrence: String::new(),
            predecessor_rest_sha256: self.canonical_identity()?,
            presentation,
            receiver_family,
            sections,
            prior_history_occurrences,
        };
        #[derive(Serialize)]
        struct Body<'a> {
            schema: &'a str,
            predecessor_rest_sha256: &'a str,
            presentation: &'a ProductionInquiryPresentation,
            receiver_family: &'a [ProductionReceiver],
            sections: &'a [Vec<i64>],
            prior_history_occurrences: &'a [String],
        }
        let body = serde_json::to_vec(&Body {
            schema: &inquiry.schema,
            predecessor_rest_sha256: &inquiry.predecessor_rest_sha256,
            presentation: &inquiry.presentation,
            receiver_family: &inquiry.receiver_family,
            sections: &inquiry.sections,
            prior_history_occurrences: &inquiry.prior_history_occurrences,
        })
        .map_err(|error| NativeHexisError::Wire(error.to_string()))?;
        inquiry.occurrence = format!("l2/inquiry/{}", digest(&body));
        self.admit_inquiry(&inquiry)?;
        Ok(inquiry)
    }

    pub fn admit_inquiry(&self, inquiry: &NativeHexisInquiry) -> Result<(), NativeHexisError> {
        let mut inquiry_receivers = inquiry.receiver_family.clone();
        inquiry_receivers.sort_by_key(|receiver| *receiver as u8);
        let mut declared_receivers = self.decoder.receivers.clone();
        declared_receivers.sort_by_key(|receiver| *receiver as u8);
        if inquiry.schema != NATIVE_HEXIS_INQUIRY_SCHEMA
            || !inquiry.occurrence.starts_with("l2/inquiry/")
            || inquiry.predecessor_rest_sha256 != self.canonical_identity()?
            || inquiry_receivers != declared_receivers
            || inquiry.sections.len() != self.standing.carrier_charts.len()
            || inquiry
                .sections
                .iter()
                .any(|section| section.len() != self.standing.generator.dimension as usize)
            || inquiry.presentation.natural_language.is_empty()
            || inquiry.presentation.notation.is_empty()
            || !is_digest(&inquiry.presentation.vector_face_sha256)
            || !is_digest(&inquiry.presentation.raster_face_sha256)
            || inquiry.prior_history_occurrences.is_empty()
        {
            return Err(NativeHexisError::Inquiry);
        }
        Ok(())
    }

    pub fn sections_wire(&self, inquiry: &NativeHexisInquiry) -> Vec<i64> {
        inquiry.sections.iter().flatten().copied().collect()
    }

    pub fn constraint_orientation(&self) -> &[i8] {
        &self.standing.generator.constraint_orientation
    }

    pub fn factor_orientation(&self) -> &[i8] {
        &self.standing.generator.action_difference_orientation
    }

    pub fn moduli_wire(&self) -> Vec<i64> {
        self.standing
            .carrier_charts
            .iter()
            .map(|chart| chart.modulus)
            .collect()
    }

    pub fn cultivation_flags(&self) -> Vec<u32> {
        vec![1; self.standing.carrier_charts.len()]
    }

    pub fn standing(&self) -> &NativeHexisStanding {
        &self.standing
    }

    pub fn decoder(&self) -> &NativeHexisDecoder {
        &self.decoder
    }

    pub fn reconstruction(&self) -> &NativeHexisReconstruction {
        &self.reconstruction
    }

    pub fn validate(&self) -> Result<(), NativeHexisError> {
        let generator = &self.standing.generator;
        let dimension = generator.dimension as usize;
        if self.standing.schema != NATIVE_HEXIS_STANDING_SCHEMA
            || !is_digest(&self.standing.cultivated_predecessor_sha256)
            || generator.occurrence.is_empty()
            || dimension == 0
            || generator.constraint_orientation.len() != dimension
            || generator.action_difference_orientation.len() != dimension
            || generator
                .constraint_orientation
                .iter()
                .chain(&generator.action_difference_orientation)
                .any(|orientation| !(-1..=1).contains(orientation))
            || !generator
                .constraint_orientation
                .iter()
                .any(|orientation| *orientation != 0)
            || !generator
                .action_difference_orientation
                .iter()
                .any(|orientation| *orientation != 0)
            || self.standing.carrier_charts.len() != 2
            || self.standing.relations.len() != 2
            || !self.standing.exact_interchange
            || self.standing.open_exterior.is_empty()
        {
            return Err(NativeHexisError::GeneratorRelation);
        }
        let mut supports = BTreeSet::new();
        let mut plate_occurrences = BTreeSet::new();
        for chart in &self.standing.carrier_charts {
            if chart.source_plate_occurrence.is_empty()
                || chart.returned_occurrence.is_empty()
                || chart.cultivation_decision_occurrence.is_empty()
                || !is_digest(&chart.source_plate_sha256)
                || chart.modulus < 0
                || chart.modulus == 1
                || chart.support_coordinates.is_empty()
                || chart
                    .support_coordinates
                    .windows(2)
                    .any(|pair| pair[0] >= pair[1])
                || !plate_occurrences.insert(&chart.source_plate_occurrence)
                || chart
                    .support_coordinates
                    .iter()
                    .any(|coordinate| !supports.insert(*coordinate))
            {
                return Err(NativeHexisError::CarrierCharts);
            }
        }
        if self.standing.relations.iter().any(|relation| {
            relation.occurrence.is_empty()
                || !is_digest(&relation.source_action_sha256)
                || !is_digest(&relation.source_constraint_sha256)
                || !is_digest(&relation.source_factor_sha256)
                || !relation.identity_plus_oriented_outer_product
                || !relation.fixed_kernel_factors
        }) {
            return Err(NativeHexisError::GeneratorRelation);
        }

        let mut declared_receivers = self.decoder.receivers.clone();
        declared_receivers.sort_by_key(|receiver| *receiver as u8);
        declared_receivers.dedup();
        if self.decoder.schema != NATIVE_HEXIS_DECODER_SCHEMA
            || declared_receivers.len() != 5
            || self.decoder.declared_histories != histories()
            || self.decoder.factorizations.len()
                != self.decoder.receivers.len() * self.decoder.declared_histories.len()
            || self.decoder.naturality.len() != 1
            || self.decoder.expanded_transport_word.is_empty()
            || self.decoder.fixed_transport_word.is_empty()
            || self.decoder.obstruction_transport_word.is_empty()
            || self.decoder.composed_transport_word.is_empty()
        {
            return Err(NativeHexisError::ReceiverHistory);
        }
        for receiver in &self.decoder.receivers {
            for history in &self.decoder.declared_histories {
                let matches = self
                    .decoder
                    .factorizations
                    .iter()
                    .filter(|receipt| receipt.receiver == *receiver && receipt.history == *history)
                    .collect::<Vec<_>>();
                if matches.len() != 1 || matches[0].consequence.is_empty() {
                    return Err(NativeHexisError::ReceiverHistory);
                }
                let (_, expected) = exact_consequence(history);
                if matches[0].status != expected {
                    return Err(NativeHexisError::ReceiverHistory);
                }
            }
        }
        let naturality = &self.decoder.naturality[0];
        if naturality.source_chart != 0
            || naturality.target_chart != 1
            || naturality.intervention_section.len() != dimension
            || naturality.source_route == naturality.target_route
            || !naturality.generator_square_commutes
            || naturality.cultivation_square_commutes
            || naturality.exact_defect.is_empty()
        {
            return Err(NativeHexisError::ReceiverHistory);
        }
        let (source_transport, source_residual) = returned_section(
            &naturality.intervention_section,
            &generator.constraint_orientation,
            &generator.action_difference_orientation,
            self.standing.carrier_charts[0].modulus,
        )?;
        let (target_transport, target_residual) = returned_section(
            &naturality.intervention_section,
            &generator.constraint_orientation,
            &generator.action_difference_orientation,
            self.standing.carrier_charts[1].modulus,
        )?;
        let rebased = source_transport
            .iter()
            .map(|value| value.rem_euclid(self.standing.carrier_charts[1].modulus))
            .collect::<Vec<_>>();
        if naturality.source_transport != source_transport
            || naturality.target_transport != target_transport
            || naturality.rebased_source_transport != rebased
            || target_transport != rebased
            || naturality.source_route != if source_residual == 0 { 1 } else { 2 }
            || naturality.target_route != if target_residual == 0 { 1 } else { 2 }
        {
            return Err(NativeHexisError::ReceiverHistory);
        }

        if self.reconstruction.schema != NATIVE_HEXIS_FIBRES_SCHEMA
            || self.reconstruction.predecessor_component_addresses.len() < 7
            || self.reconstruction.collapsed_populations.len() < 3
            || self.reconstruction.complete_fibres.len() < 6
            || self.reconstruction.shortest_separators.len() != 1
            || self.reconstruction.unresolved_families.is_empty()
            || self
                .reconstruction
                .collapsed_populations
                .iter()
                .any(|population| {
                    population.native_occurrence.is_empty()
                        || population.source_occurrences.len() != 2
                        || !population.complete
                })
        {
            return Err(NativeHexisError::Reconstruction);
        }
        let separator = &self.reconstruction.shortest_separators[0];
        if separator.equal_present_sections != vec![vec![0, 0, 0], vec![0, 0, 0]]
            || separator.successor_sections
                != vec![
                    naturality.intervention_section.clone(),
                    naturality.intervention_section.clone(),
                ]
            || separator.returned_residuals != vec![source_residual, target_residual]
            || separator.returned_routes != vec![naturality.source_route, naturality.target_route]
            || separator.shortest_word != vec![0]
        {
            return Err(NativeHexisError::Reconstruction);
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn oriented_transport_commutes_with_mod_two_rebase_but_kernel_membership_reopens() {
        let section = [1, 1, 0];
        let constraint = [1, 1, -1];
        let factor = [-1, -1, 1];
        let (integer, integer_residual) =
            returned_section(&section, &constraint, &factor, 0).expect("integer");
        let (f2, f2_residual) = returned_section(&section, &constraint, &factor, 2).expect("F2");
        assert_eq!(integer, vec![-1, -1, 2]);
        assert_eq!(integer_residual, 2);
        assert_eq!(f2, vec![1, 1, 0]);
        assert_eq!(f2_residual, 0);
        assert_eq!(
            integer
                .iter()
                .map(|value| value.rem_euclid(2))
                .collect::<Vec<_>>(),
            f2
        );
    }
}
