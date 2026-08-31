//! M1 particle construction — one addressed body, three co-present exact branches, and seven separate
//! sameness relations.
//!
//! Proposal spans are exterior testimony addressed only by authenticated artifact digest and
//! serial ordinal. Source spellings, atlas identifiers, and proposal names never route admission.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use holonic_engine::exact_linear::ExactRatMatrix;
use holonic_engine::exact_owner_testimony::ExactOwnerLicense;
use life::mathematical_particle::{
    AnalyticBranch, BinderId, BinderScope, BranchId, CarrierId, CarrierOccurrence, HypothesisId,
    HypothesisLicense, MathematicalParticle, MathematicalParticleInput, ParticleAdmissionInput,
    RelationWitness, TypedOperation, TypedPort,
};
use serde::Serialize;

use super::{particle_relations, particle_typing, resident_affine, source_material};

const AFFINE_ORDINALS: [usize; 8] = [35, 36, 37, 38, 39, 40, 41, 42];
const HEAT_POSITIVE_TIME_ORDINALS: [usize; 8] = [263, 264, 265, 266, 267, 268, 269, 270];
const HEAT_EUCLIDEAN_ORDINALS: [usize; 26] = [
    305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 320, 321, 322, 323,
    324, 325, 326, 327, 328, 329, 330,
];
const RIGIDITY_LINEAGE_ORDINAL: usize = 204;

#[derive(Clone, Debug, Serialize)]
pub struct ProposalReceipt {
    pub occurrence: String,
    pub passage: String,
    pub branches: Vec<u64>,
    pub attempt: String,
    pub owner_evidence: BTreeMap<u64, String>,
    pub obstruction: Option<String>,
}

#[derive(Clone, Debug)]
pub struct SamenessReceipt {
    pub left_occurrence: String,
    pub right_occurrence: String,
    pub source_mark_map: BTreeMap<String, String>,
    pub doctrine_forward: ExactRatMatrix,
    pub doctrine_reverse: ExactRatMatrix,
    pub receiver_indices: [usize; 2],
    pub classification_classes: BTreeMap<String, Vec<u8>>,
    pub similarity_characteristics: BTreeMap<String, BTreeMap<String, Vec<u8>>>,
    pub history_witness: RelationWitness,
    pub rendering_artifact_occurrence: String,
}

pub struct Construction {
    pub particle: MathematicalParticle,
    pub resident: resident_affine::ResidentReturn,
    pub licenses: Vec<ExactOwnerLicense>,
    pub proposals: Vec<ProposalReceipt>,
    pub rigidity_lineage: BTreeSet<String>,
    pub sameness: SamenessReceipt,
    pub proposal_source_spans: BTreeMap<String, BTreeSet<String>>,
}

fn source_marks(
    testimonies: &[&life::mathematical_source::SourceLayoutTestimony],
) -> BTreeSet<String> {
    testimonies
        .iter()
        .flat_map(|testimony| {
            testimony
                .occurrences
                .iter()
                .map(|occurrence| occurrence.address.clone())
        })
        .collect()
}

pub fn construct(root: &Path) -> Result<Construction, String> {
    let mut remounted = source_material::remount(root)?;
    if remounted.baseline_words.len() != remounted.reflow_words.len() {
        return Err("M0's harmless reflow lost a serial occurrence".to_owned());
    }
    for (baseline, reflow) in remounted
        .baseline
        .occurrences
        .iter()
        .zip(&remounted.reflow.occurrences)
    {
        if baseline.payload_sha256 != reflow.payload_sha256
            || baseline.serial_ordinal != reflow.serial_ordinal
        {
            return Err(
                "M0's harmless reflow changed the carrier word or serial ordinal".to_owned(),
            );
        }
    }
    if remounted.baseline_words != remounted.reflow_words {
        return Err("M0's harmless reflow changed a born-digital carrier word".to_owned());
    }
    let baseline_span = source_material::span_addresses(
        &remounted.baseline,
        source_material::baseline_sha256(),
        &AFFINE_ORDINALS,
    )?;
    let reflow_span = source_material::span_addresses(
        &remounted.reflow,
        source_material::reflow_sha256(),
        &AFFINE_ORDINALS,
    )?;
    let heat_time_span = source_material::span_addresses(
        &remounted.natural_page5,
        source_material::page5_sha256(),
        &HEAT_POSITIVE_TIME_ORDINALS,
    )?;
    let heat_euclidean_span = source_material::span_addresses(
        &remounted.natural_page5,
        source_material::page5_sha256(),
        &HEAT_EUCLIDEAN_ORDINALS,
    )?;
    let rigidity_lineage = source_material::span_addresses(
        &remounted.equation_atlas,
        source_material::atlas_sha256(),
        &[RIGIDITY_LINEAGE_ORDINAL],
    )?;
    let affine_sources = baseline_span
        .iter()
        .chain(&reflow_span)
        .cloned()
        .collect::<BTreeSet<_>>();
    let heat_sources = heat_time_span
        .iter()
        .chain(&heat_euclidean_span)
        .cloned()
        .collect::<BTreeSet<_>>();
    let passage_sources = affine_sources
        .iter()
        .chain(&heat_sources)
        .cloned()
        .collect::<BTreeSet<_>>();
    let all_sources = source_marks(&[
        &remounted.baseline,
        &remounted.reflow,
        &remounted.natural_page5,
        &remounted.equation_atlas,
    ]);
    let operation_assembly =
        particle_typing::construct(&all_sources, &affine_sources, &heat_sources)?;
    let relation_assembly = particle_relations::construct(
        root,
        &mut remounted,
        &all_sources,
        &affine_sources,
        &heat_sources,
        AFFINE_ORDINALS[0],
        &operation_assembly,
    )?;
    let particle_typing::OperationAssembly {
        operation,
        ports,
        laws,
        boundaries,
        passage,
        affine_standing: _,
        affine_return,
        heat_return,
        quantity_return,
        licenses,
        exact_owner,
        refused_attempt: _,
        resident,
    } = operation_assembly;
    let particle_relations::RelationAssembly {
        presentation_fibres,
        open_fibres,
        selection,
        proposals,
        proposal_receipts,
        refusal,
        value_receiver,
        rendering_receiver,
        classification_receiver,
        similarity_receiver,
        history_return,
        sameness,
        sameness_receipt,
    } = relation_assembly;
    let operation_typing = |law, hypotheses| TypedOperation {
        law,
        input_arity: usize::from(!operation.shape.laws[&law].inputs.is_empty()),
        output_arity: operation.shape.laws[&law].outputs.len(),
        hypotheses,
        branches: BTreeSet::from([BranchId(1)]),
    };
    let heat_hypotheses = BTreeSet::from([HypothesisId(1), HypothesisId(2), HypothesisId(3)]);
    let ordinary_hypothesis = BTreeSet::from([HypothesisId(1)]);
    let typed_operations = vec![
        operation_typing(laws.affine_enter, ordinary_hypothesis.clone()),
        operation_typing(laws.affine_contract, ordinary_hypothesis.clone()),
        operation_typing(laws.heat_enter, heat_hypotheses.clone()),
        operation_typing(laws.heat_contract, heat_hypotheses.clone()),
        operation_typing(laws.quantity_enter, ordinary_hypothesis.clone()),
        operation_typing(laws.quantity_contract, ordinary_hypothesis),
    ];
    let particle = MathematicalParticle::found(MathematicalParticleInput {
        occurrence: "m1-particle".to_owned(),
        source_testimonies: vec![
            remounted.baseline,
            remounted.reflow,
            remounted.natural_page5,
            remounted.equation_atlas,
        ],
        exterior_artifacts: vec![remounted.natural_page5_vector],
        presentation_fibres,
        operation,
        carriers: vec![CarrierOccurrence {
            id: CarrierId(1),
            source_occurrences: all_sources.clone(),
            owner_carrier: "Q".to_owned(),
            equality_law_lineage: "exact rational equality".to_owned(),
        }],
        binders: vec![
            BinderScope {
                id: BinderId(10),
                source_occurrences: heat_sources.clone(),
                ports: BTreeSet::from([ports.heat_in, ports.heat_out]),
                laws: BTreeSet::from([laws.heat_enter, laws.heat_contract]),
            },
            BinderScope {
                id: BinderId(11),
                source_occurrences: heat_sources.clone(),
                ports: BTreeSet::from([ports.heat_in, ports.heat_out]),
                laws: BTreeSet::from([laws.heat_enter, laws.heat_contract]),
            },
        ],
        ports: vec![
            TypedPort {
                boundary: boundaries.affine_input,
                carrier: CarrierId(1),
                unit_frame: Vec::new(),
                exposed: true,
            },
            TypedPort {
                boundary: boundaries.affine_output,
                carrier: CarrierId(1),
                unit_frame: Vec::new(),
                exposed: true,
            },
            TypedPort {
                boundary: boundaries.heat_input,
                carrier: CarrierId(1),
                unit_frame: Vec::new(),
                exposed: true,
            },
            TypedPort {
                boundary: boundaries.heat_output,
                carrier: CarrierId(1),
                unit_frame: Vec::new(),
                exposed: true,
            },
            TypedPort {
                boundary: boundaries.quantity_input,
                carrier: CarrierId(1),
                unit_frame: Vec::new(),
                exposed: true,
            },
            TypedPort {
                boundary: boundaries.quantity_output,
                carrier: CarrierId(1),
                unit_frame: Vec::new(),
                exposed: true,
            },
        ],
        operations: typed_operations,
        hypotheses: vec![
            HypothesisLicense {
                id: HypothesisId(1),
                source_occurrences: passage_sources.clone(),
                licenses: laws.all().into_iter().collect(),
                branches: BTreeSet::from([BranchId(1)]),
            },
            HypothesisLicense {
                id: HypothesisId(2),
                source_occurrences: heat_euclidean_span.clone(),
                licenses: BTreeSet::from([laws.heat_enter, laws.heat_contract]),
                branches: BTreeSet::from([BranchId(1)]),
            },
            HypothesisLicense {
                id: HypothesisId(3),
                source_occurrences: heat_time_span.clone(),
                licenses: BTreeSet::from([laws.heat_enter, laws.heat_contract]),
                branches: BTreeSet::from([BranchId(1)]),
            },
        ],
        passages: vec![passage],
        branches: vec![AnalyticBranch {
            id: BranchId(1),
            passage: selection,
            hypotheses: heat_hypotheses,
        }],
        linear_returns: vec![affine_return, heat_return],
        quantity_returns: vec![quantity_return],
        value_receivers: vec![value_receiver],
        rendering_receivers: vec![rendering_receiver],
        classification_receivers: vec![classification_receiver],
        similarity_receivers: vec![similarity_receiver],
        receiver_history_returns: vec![history_return],
        sameness: vec![sameness],
        proposals,
        refusals: vec![refusal],
        open_fibres,
        admission: ParticleAdmissionInput {
            proposal: "addressed-three-branch-proposal".to_owned(),
            typing_occurrence: "m1-shared-passage".to_owned(),
            exact_owner,
            passage_receipt: Some(resident.receipt),
        },
    })
    .map_err(|error| format!("{error:?}"))?;

    Ok(Construction {
        particle,
        resident: resident.returned,
        licenses,
        proposals: proposal_receipts,
        rigidity_lineage,
        sameness: sameness_receipt,
        proposal_source_spans: BTreeMap::from([
            ("affine-baseline".to_owned(), baseline_span.clone()),
            ("affine-reflow".to_owned(), reflow_span.clone()),
            ("heat-positive-time".to_owned(), heat_time_span.clone()),
            ("heat-euclidean".to_owned(), heat_euclidean_span.clone()),
        ]),
    })
}
