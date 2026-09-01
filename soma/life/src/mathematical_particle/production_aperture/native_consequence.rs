//! N0's native mathematical application boundary.
//!
//! Source owners are [`NativeHexisRest`] and CUDA's fixed-section family passage. The
//! entering port is an addressed recovered operation/constraint/geometry occurrence; its
//! predecessor is the canonical generator-native rest. The constitutive law remains
//! `T = I + L*C`. The resident card returns transport, successor route, constraint, shared
//! contact, local withdrawals and exact reduction in one terminal deed. This owner only freezes
//! that return as `(C,D,F,L,X)` and offers borrowing projections afterward. Nonlinear varieties,
//! overlapping supports and unadmitted histories remain open. The construction grade is
//! `implemented-exact-with-measured-apparatus-testimony` when the real device receipt is present.

use std::collections::BTreeSet;

use holonic_engine::cuda_refine::{CudaRefineExecutor, DeviceNativeFixedSectionFamilies};
use serde::Serialize;
use sha2::{Digest, Sha256};

use super::native_consequence_types::{
    NativeAddressedConsequenceSpan, NativeApparatusReceipt, NativeCodec, NativeCodecProjection,
    NativeConsequenceExterior, NativeConsequenceLineage, NativeConsequenceReconstruction,
    NativeConstraintCell, NativeDerivationTransport, NativeDeviceRouteFibre,
    NativeExactConsequenceFace, NativeGeometryCell, NativeGeometryVertex,
    NativeMathematicalComplex, NativeMathematicalConsequence, NativeMathematicalConsequenceError,
    NativeMathematicalInquiry, NativeMathematicalPort, NativeMathematicalReceiver,
    NativeOperationCell, NativeReturnedObstruction,
};
use super::native_family_types::{NativeHexisRest, NativeSuccessorHistory};

pub const NATIVE_MATHEMATICAL_INQUIRY_SCHEMA: &str = "holonics.n0.native-mathematical-inquiry.v1";
pub const NATIVE_MATHEMATICAL_CONSEQUENCE_SCHEMA: &str =
    "holonics.n0.native-mathematical-consequence.v1";

fn digest(value: &impl Serialize) -> Result<String, NativeMathematicalConsequenceError> {
    let bytes = serde_json::to_vec(value)
        .map_err(|error| NativeMathematicalConsequenceError::Codec(error.to_string()))?;
    Ok(Sha256::digest(bytes)
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect())
}

fn receiver_family() -> Vec<NativeMathematicalReceiver> {
    vec![
        NativeMathematicalReceiver::OperationIncidence,
        NativeMathematicalReceiver::ConstraintReturn,
        NativeMathematicalReceiver::GeometryIncidence,
        NativeMathematicalReceiver::ExactConsequence,
        NativeMathematicalReceiver::DerivationalTransport,
        NativeMathematicalReceiver::ReconstructionFibre,
        NativeMathematicalReceiver::AddressedLineage,
        NativeMathematicalReceiver::ObstructionExterior,
    ]
}

impl NativeHexisRest {
    pub fn found_native_mathematical_inquiry(
        &self,
        source_occurrences: Vec<String>,
        sections: Vec<Vec<i64>>,
        requested_histories: Vec<NativeSuccessorHistory>,
        prior_history_occurrences: Vec<String>,
        open_exterior: Vec<String>,
    ) -> Result<NativeMathematicalInquiry, NativeMathematicalConsequenceError> {
        self.validate()
            .map_err(|error| NativeMathematicalConsequenceError::Predecessor(error.to_string()))?;
        let mut inquiry = NativeMathematicalInquiry {
            schema: NATIVE_MATHEMATICAL_INQUIRY_SCHEMA.to_owned(),
            occurrence: String::new(),
            predecessor_rest_sha256: self.canonical_identity().map_err(|error| {
                NativeMathematicalConsequenceError::Predecessor(error.to_string())
            })?,
            port: NativeMathematicalPort::RecoveredOperationConstraintGeometry,
            source_occurrences,
            receiver_family: receiver_family(),
            sections,
            requested_histories,
            prior_history_occurrences,
            open_exterior,
        };
        inquiry.occurrence = format!("n0/inquiry/{}", digest(&inquiry_body(&inquiry))?);
        self.admit_native_mathematical_inquiry(&inquiry)?;
        Ok(inquiry)
    }

    pub fn admit_native_mathematical_inquiry(
        &self,
        inquiry: &NativeMathematicalInquiry,
    ) -> Result<(), NativeMathematicalConsequenceError> {
        let dimension = self.standing.generator.dimension as usize;
        let source_population = inquiry.source_occurrences.iter().collect::<BTreeSet<_>>();
        let receiver_population = inquiry.receiver_family.iter().collect::<BTreeSet<_>>();
        let expected_occurrence = format!("n0/inquiry/{}", digest(&inquiry_body(inquiry))?);
        if inquiry.schema != NATIVE_MATHEMATICAL_INQUIRY_SCHEMA
            || inquiry.occurrence != expected_occurrence
            || inquiry.predecessor_rest_sha256
                != self.canonical_identity().map_err(|error| {
                    NativeMathematicalConsequenceError::Predecessor(error.to_string())
                })?
            || inquiry.port != NativeMathematicalPort::RecoveredOperationConstraintGeometry
            || inquiry.source_occurrences.len() != self.standing.carrier_charts.len()
            || source_population.len() != inquiry.source_occurrences.len()
            || inquiry.source_occurrences.iter().any(String::is_empty)
            || inquiry.receiver_family != receiver_family()
            || receiver_population.len() != inquiry.receiver_family.len()
            || inquiry.sections.len() != self.standing.carrier_charts.len()
            || inquiry
                .sections
                .iter()
                .any(|section| section.len() != dimension)
            || inquiry.requested_histories.is_empty()
            || inquiry
                .requested_histories
                .iter()
                .any(|history| !self.decoder.declared_histories.contains(history))
            || inquiry.prior_history_occurrences.is_empty()
            || inquiry
                .prior_history_occurrences
                .iter()
                .any(String::is_empty)
            || inquiry.open_exterior.is_empty()
        {
            return Err(NativeMathematicalConsequenceError::Inquiry);
        }
        Ok(())
    }

    /// Productive N0 entry: after admission the host launches one already-founded resident deed.
    /// No semantic result returns to the host between device fronts because the fixed-section
    /// transport and its typed reduction share the single terminal synchronization.
    pub fn conduct_native_mathematical_inquiry_on_card(
        &self,
        inquiry: &NativeMathematicalInquiry,
        card: &mut CudaRefineExecutor,
    ) -> Result<NativeMathematicalConsequence, NativeMathematicalConsequenceError> {
        self.admit_native_mathematical_inquiry(inquiry)?;
        let sections = inquiry
            .sections
            .iter()
            .flatten()
            .copied()
            .collect::<Vec<_>>();
        let moduli = self
            .standing
            .carrier_charts
            .iter()
            .map(|chart| chart.modulus)
            .collect::<Vec<_>>();
        let cultivated = vec![1; self.standing.carrier_charts.len()];
        let returned = card
            .conduct_native_fixed_section_families_on_device(
                &sections,
                &self.standing.generator.constraint_orientation,
                &self.standing.generator.action_difference_orientation,
                &moduli,
                &cultivated,
            )
            .map_err(|error| NativeMathematicalConsequenceError::Apparatus(error.to_string()))?;
        self.freeze_native_consequence(inquiry, returned, card.device_name().to_owned())
    }

    fn freeze_native_consequence(
        &self,
        inquiry: &NativeMathematicalInquiry,
        returned: DeviceNativeFixedSectionFamilies,
        device: String,
    ) -> Result<NativeMathematicalConsequence, NativeMathematicalConsequenceError> {
        let families = self.standing.carrier_charts.len();
        let dimension = self.standing.generator.dimension as usize;
        if returned.families != families
            || returned.dimension != dimension
            || returned.transported_sections.len() != families * dimension
            || returned.constraint_residuals.len() != families
            || returned.constraint_held.len() != families
            || returned.invariant.len() != families
            || returned.selected_route.len() != families
            || returned.ablated_route.len() != families
            || returned.local_ablated_joint.len() != families
            || returned.launches != 2
            || returned.synchronizations != 1
            || returned.typed_reductions != 1
            || returned.active_lanes != families as u32
            || returned.host_ingress_octets == 0
            || returned.host_egress_octets == 0
        {
            return Err(NativeMathematicalConsequenceError::IncompleteReturn);
        }

        let mut operation_cells = Vec::with_capacity(families);
        let mut constraint_cells = Vec::with_capacity(families);
        let mut geometry_cells = Vec::with_capacity(families);
        let mut exact_consequence_faces = Vec::with_capacity(families);
        let mut derivational_transport = Vec::with_capacity(families);
        let mut device_route_fibres = Vec::with_capacity(families);
        let mut addressed_spans = Vec::with_capacity(families);
        let mut returned_obstructions = Vec::new();

        for family in 0..families {
            let chart = &self.standing.carrier_charts[family];
            let entered = inquiry.sections[family].clone();
            let returned_section = returned.transported_sections
                [family * dimension..(family + 1) * dimension]
                .to_vec();
            let difference = returned_section
                .iter()
                .zip(&entered)
                .map(|(returned, entered)| returned - entered)
                .collect::<Vec<_>>();
            let word = word_for_route(self, returned.selected_route[family])?;
            let operation_occurrence = format!(
                "{}/operation/{family}/{}",
                inquiry.occurrence,
                digest(&(&entered, &returned_section, &word))?
            );
            let constraint_occurrence = format!(
                "{}/constraint/{family}/{}",
                inquiry.occurrence,
                digest(&(
                    returned.constraint_residuals[family],
                    returned.constraint_held[family]
                ))?
            );
            let geometry_occurrence = format!(
                "{}/geometry/{family}/{}",
                inquiry.occurrence,
                digest(&(&entered, &returned_section))?
            );
            let target_boundary = format!("{operation_occurrence}/returned-boundary");
            operation_cells.push(NativeOperationCell {
                occurrence: operation_occurrence.clone(),
                carrier_chart_occurrence: chart.source_plate_occurrence.clone(),
                generator_relation_occurrence: self.standing.relations[family].occurrence.clone(),
                source_boundary: inquiry.source_occurrences[family].clone(),
                target_boundary: target_boundary.clone(),
                entered_section: entered.clone(),
                returned_section: returned_section.clone(),
                exact_difference: difference.clone(),
                ordered_transport_word: word.clone(),
            });
            constraint_cells.push(NativeConstraintCell {
                occurrence: constraint_occurrence,
                carrier_chart_occurrence: chart.source_plate_occurrence.clone(),
                orientation: self.standing.generator.constraint_orientation.clone(),
                exact_residual: returned.constraint_residuals[family],
                held: returned.constraint_held[family] == 1,
            });
            geometry_cells.push(NativeGeometryCell {
                occurrence: geometry_occurrence,
                carrier_chart_occurrence: chart.source_plate_occurrence.clone(),
                vertices: entered
                    .iter()
                    .zip(&returned_section)
                    .enumerate()
                    .map(|(coordinate, (entered, returned))| NativeGeometryVertex {
                        coordinate: coordinate as u32,
                        entered: *entered,
                        returned: *returned,
                    })
                    .collect(),
                constraint_incidence: self.standing.generator.constraint_orientation.clone(),
                transport_incidence: self
                    .standing
                    .generator
                    .action_difference_orientation
                    .clone(),
            });
            exact_consequence_faces.push(NativeExactConsequenceFace {
                carrier_chart_occurrence: chart.source_plate_occurrence.clone(),
                returned_section: returned_section.clone(),
                exact_residual: returned.constraint_residuals[family],
                selected_route: returned.selected_route[family],
                fixed_section: returned.selected_route[family] == 1,
            });
            derivational_transport.push(NativeDerivationTransport {
                occurrence: format!("{}/derivation/{family}", inquiry.occurrence),
                predecessor_occurrence: inquiry.source_occurrences[family].clone(),
                successor_occurrence: target_boundary.clone(),
                ordered_word: word,
                prior_history_occurrences: inquiry.prior_history_occurrences.clone(),
                returned_difference: difference,
            });
            device_route_fibres.push(NativeDeviceRouteFibre {
                carrier_chart_occurrence: chart.source_plate_occurrence.clone(),
                selected_route: returned.selected_route[family],
                exact_ablation_route: returned.ablated_route[family],
                local_ablation_preserves_joint_contact: returned.local_ablated_joint[family] == 1,
                complete_route_population: vec![0, 1, 2],
            });
            addressed_spans.push(NativeAddressedConsequenceSpan {
                occurrence: format!("{}/span/{family}", inquiry.occurrence),
                left_boundary_map: inquiry.source_occurrences[family].clone(),
                right_boundary_map: target_boundary,
                joining_equality: chart.returned_occurrence.clone(),
            });
            if returned.selected_route[family] == 2 {
                returned_obstructions.push(NativeReturnedObstruction {
                    carrier_chart_occurrence: chart.source_plate_occurrence.clone(),
                    exact_residual: returned.constraint_residuals[family],
                    selected_route: 2,
                    reason: "the exact residual leaves this carrier's admitted fixed section"
                        .to_owned(),
                });
            }
        }

        let complex = NativeMathematicalComplex {
            operation_cells,
            constraint_cells,
            geometry_cells,
            exact_consequence_faces,
        };
        let reconstruction = NativeConsequenceReconstruction {
            inherited_collapsed_populations: self.reconstruction.collapsed_populations.clone(),
            complete_inherited_fibres: self.reconstruction.complete_fibres.clone(),
            device_route_fibres,
            shortest_available_separators: self.reconstruction.shortest_separators.clone(),
            unresolved_families: self.reconstruction.unresolved_families.clone(),
        };
        let lineage = NativeConsequenceLineage {
            predecessor_rest_sha256: inquiry.predecessor_rest_sha256.clone(),
            inquiry_occurrence: inquiry.occurrence.clone(),
            source_occurrences: inquiry.source_occurrences.clone(),
            addressed_spans,
        };
        let exterior = NativeConsequenceExterior {
            returned_obstructions,
            inquiry_open_exterior: inquiry.open_exterior.clone(),
            rested_open_exterior: self.standing.open_exterior.clone(),
            unresolved_families: self.reconstruction.unresolved_families.clone(),
        };
        let apparatus = NativeApparatusReceipt {
            device,
            launches: returned.launches,
            synchronizations: returned.synchronizations,
            typed_reductions: returned.typed_reductions,
            active_lanes: returned.active_lanes,
            semantic_work: returned.semantic_work.to_string(),
            semantic_span: returned.semantic_span,
            resident_octets: returned.resident_octets,
            transfer_octets: returned.host_ingress_octets + returned.host_egress_octets,
            host_semantic_callbacks: 0,
        };
        let receiver_family = receiver_family();
        let occurrence = format!(
            "n0/consequence/{}",
            digest(&(
                &inquiry.occurrence,
                &inquiry.predecessor_rest_sha256,
                &receiver_family,
                &complex,
                &derivational_transport,
                &reconstruction,
                &lineage,
                &exterior,
                &apparatus,
            ))?
        );
        Ok(NativeMathematicalConsequence {
            schema: NATIVE_MATHEMATICAL_CONSEQUENCE_SCHEMA.to_owned(),
            truth_status: "implemented-exact-with-measured-apparatus-testimony".to_owned(),
            occurrence,
            inquiry_occurrence: inquiry.occurrence.clone(),
            predecessor_rest_sha256: inquiry.predecessor_rest_sha256.clone(),
            receiver_family,
            complex,
            derivational_transport,
            reconstruction,
            lineage,
            exterior,
            apparatus,
        })
    }
}

impl NativeMathematicalConsequence {
    /// A projection borrows an already-frozen native consequence and cannot commit morphology or
    /// replace its identity.
    pub fn project(
        &self,
        codec: NativeCodec,
    ) -> Result<NativeCodecProjection, NativeMathematicalConsequenceError> {
        let (media_type, payload) = match codec {
            NativeCodec::ExactNotation => {
                let payload = self
                    .complex
                    .exact_consequence_faces
                    .iter()
                    .map(|face| {
                        format!(
                            "{}: {:?}; C(s)={}; route={}",
                            face.carrier_chart_occurrence,
                            face.returned_section,
                            face.exact_residual,
                            face.selected_route
                        )
                    })
                    .collect::<Vec<_>>()
                    .join("\n");
                ("text/plain; charset=utf-8", payload)
            }
            NativeCodec::Json => (
                "application/json",
                serde_json::to_string_pretty(self).map_err(|error| {
                    NativeMathematicalConsequenceError::Codec(error.to_string())
                })?,
            ),
        };
        Ok(NativeCodecProjection {
            schema: "holonics.n0.native-codec-projection.v1".to_owned(),
            truth_status: "implemented-exact".to_owned(),
            codec,
            native_consequence_occurrence: self.occurrence.clone(),
            media_type: media_type.to_owned(),
            payload,
        })
    }
}

#[derive(Serialize)]
struct InquiryBody<'a> {
    schema: &'a str,
    predecessor_rest_sha256: &'a str,
    port: NativeMathematicalPort,
    source_occurrences: &'a [String],
    receiver_family: &'a [NativeMathematicalReceiver],
    sections: &'a [Vec<i64>],
    requested_histories: &'a [NativeSuccessorHistory],
    prior_history_occurrences: &'a [String],
    open_exterior: &'a [String],
}

fn inquiry_body(inquiry: &NativeMathematicalInquiry) -> InquiryBody<'_> {
    InquiryBody {
        schema: &inquiry.schema,
        predecessor_rest_sha256: &inquiry.predecessor_rest_sha256,
        port: inquiry.port,
        source_occurrences: &inquiry.source_occurrences,
        receiver_family: &inquiry.receiver_family,
        sections: &inquiry.sections,
        requested_histories: &inquiry.requested_histories,
        prior_history_occurrences: &inquiry.prior_history_occurrences,
        open_exterior: &inquiry.open_exterior,
    }
}

fn word_for_route(
    rest: &NativeHexisRest,
    route: u32,
) -> Result<Vec<u32>, NativeMathematicalConsequenceError> {
    match route {
        0 => Ok(rest.decoder.expanded_transport_word.clone()),
        1 => Ok(rest.decoder.fixed_transport_word.clone()),
        2 => Ok(rest.decoder.obstruction_transport_word.clone()),
        _ => Err(NativeMathematicalConsequenceError::IncompleteReturn),
    }
}
