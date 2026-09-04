use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::Path;

use holonic_engine::interaction::OccurrencePort;
use holonic_engine::ported_operation::{OperationSpecies, PortedOperationComplex, SourceTestimony};
use holonic_engine::quantity::BaseUnits;
use life::exchange_world_tube::{
    mount_exchange_world_tube_on_device, ExchangeContainerSpec, ExchangeWorldTube,
};
use life::mathematical_particle::{
    BinderId, BinderScope, BranchId, CarrierId, CarrierOccurrence, HypothesisId, HypothesisLicense,
    MaterialOperationWorldTube, MaterialOperationWorldTubeInput, OperationWordStep,
    PassageBranchId, RecordFacePassage, TensorSlot, TensorSlotRole, TensorVariance,
    TypedConstructionStep, TypedMathematicalBoundary, TypedOperation, TypedOperationWord,
    TypedPassage, TypedPort,
};
use life::mathematical_source::{
    compare_presentations, correspond, correspondence_demand, derive_layout, layout_demand,
    ArtifactIdentity, ExactBox, ExactExtent, PlacedCarrier, Rat, SourceLayoutTestimony,
    SourceLayoutWorkCover, TestimonyChart,
};
use num_bigint::BigInt;
use sha2::{Digest, Sha256};

const FIXTURE_ROOT: &str = "research/fixtures/r0_rich_inquiry";

pub struct IntakeReturn {
    pub world_tube: MaterialOperationWorldTube,
    pub source_files: Vec<FileIdentity>,
    pub branch_source_occurrences: Vec<Vec<String>>,
}

#[derive(Clone, Debug, serde::Serialize)]
pub struct FileIdentity {
    pub path: String,
    pub sha256: String,
    pub octets: u64,
}

pub fn found(root: &Path) -> Result<IntakeReturn, String> {
    let json_relative = format!("{FIXTURE_ROOT}/inquiry.jsonl");
    let json_bytes = fs::read(root.join(&json_relative)).map_err(|error| error.to_string())?;
    let exchange = mount_exchange_world_tube_on_device(&[ExchangeContainerSpec {
        locator: root.join(&json_relative),
        provider_face: "operator".to_owned(),
        material_kind_face: "rich-inquiry-control-cohort".to_owned(),
    }])
    .map_err(|error| error.to_string())?;
    let json = record_layout(&json_relative, &json_bytes, &exchange)?;
    let language = line_layout(
        root,
        &format!("{FIXTURE_ROOT}/inquiry.md"),
        "r1/inquiry/language",
        TestimonyChart::BornDigital,
    )?;
    let lean = line_layout(
        root,
        &format!("{FIXTURE_ROOT}/inquiry.lean"),
        "r1/inquiry/lean",
        TestimonyChart::BornDigital,
    )?;
    let diagram_a = diagram_layout(
        root,
        &format!("{FIXTURE_ROOT}/support-route-a.svg"),
        "r1/inquiry/diagram-a",
        false,
    )?;
    let diagram_b = diagram_layout(
        root,
        &format!("{FIXTURE_ROOT}/support-route-b.svg"),
        "r1/inquiry/diagram-b",
        true,
    )?;

    let record_face_passages = exchange
        .records
        .iter()
        .enumerate()
        .map(|(at, record)| {
            let carrier = json
                .occurrences
                .get(at)
                .ok_or_else(|| "the JSON M0 face population left A1 chronology".to_owned())?;
            Ok(RecordFacePassage {
                record: at as u64,
                record_occurrence_sha256: exchange.record_occurrence(at as u64).render(),
                carrier_address: carrier.address.clone(),
                carried_payload_sha256: record.raw_sha256.render(),
            })
        })
        .collect::<Result<Vec<_>, String>>()?;
    let receiver_record_occurrences = record_face_passages
        .iter()
        .map(|passage| passage.record_occurrence_sha256.clone())
        .collect::<BTreeSet<_>>();

    let language_lean_demand =
        correspondence_demand(&language, &lean).map_err(|error| error.to_string())?;
    let language_lean = correspond(
        &language,
        &lean,
        &SourceLayoutWorkCover::exactly(&language_lean_demand),
    )
    .map_err(|error| error.to_string())?;
    let diagram_demand =
        correspondence_demand(&diagram_a, &diagram_b).map_err(|error| error.to_string())?;
    let diagram_fibre = correspond(
        &diagram_a,
        &diagram_b,
        &SourceLayoutWorkCover::exactly(&diagram_demand),
    )
    .map_err(|error| error.to_string())?;
    let diagram_control = compare_presentations(&diagram_a, &diagram_b);

    let source_testimonies = vec![json, language, lean, diagram_a, diagram_b];
    let branch_source_occurrences = source_testimonies
        .iter()
        .map(|testimony| {
            testimony
                .occurrences
                .iter()
                .map(|occurrence| occurrence.address.clone())
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let assembly = operation_boundary(&source_testimonies)?;
    let world_tube = MaterialOperationWorldTube::found(MaterialOperationWorldTubeInput {
        occurrence: "r1/material-operation-world-tube".to_owned(),
        exchange,
        source_testimonies,
        record_face_passages,
        operation: assembly.operation,
        passage: assembly.passage,
        carriers: assembly.carriers,
        binders: assembly.binders,
        ports: assembly.ports,
        operations: assembly.operations,
        hypotheses: assembly.hypotheses,
        branches: assembly.branches,
        receiver_record_occurrences,
        cross_codec_fibres: vec![language_lean, diagram_fibre],
        presentation_controls: vec![diagram_control],
        open_fibres: vec![
            "receiver factorization from the returned I5 passage remains R2".to_owned(),
            "variable-level mathematical binder identity remains a receiver fibre until a returned exact operation separates it".to_owned(),
            "raster and prior-history ports are absent from this selected source occurrence".to_owned(),
        ],
    })
    .map_err(|error| error.to_string())?;
    let source_files = [
        "inquiry.jsonl",
        "inquiry.md",
        "inquiry.lean",
        "support-route-a.svg",
        "support-route-b.svg",
    ]
    .into_iter()
    .map(|name| file_identity(root, &format!("{FIXTURE_ROOT}/{name}")))
    .collect::<Result<Vec<_>, String>>()?;
    Ok(IntakeReturn {
        world_tube,
        source_files,
        branch_source_occurrences,
    })
}

struct OperationBoundary {
    operation: PortedOperationComplex,
    passage: TypedPassage,
    carriers: Vec<CarrierOccurrence>,
    binders: Vec<BinderScope>,
    ports: Vec<TypedPort>,
    operations: Vec<TypedOperation>,
    hypotheses: Vec<HypothesisLicense>,
    branches: BTreeSet<BranchId>,
}

fn operation_boundary(testimonies: &[SourceLayoutTestimony]) -> Result<OperationBoundary, String> {
    let mut operation = PortedOperationComplex::new("r1-material-founded-operation-world-tube");
    let base = BaseUnits::declare(["material-incidence"]).map_err(|error| error.to_string())?;
    let dimensionless = base.dimensionless();
    let mut staging_sources = BTreeMap::new();
    let mut staging = BTreeMap::new();
    let mut words = BTreeMap::new();
    let mut carriers = Vec::new();
    let mut binders = Vec::new();
    let mut ports = Vec::new();
    let mut operations = Vec::new();
    let mut hypotheses = Vec::new();
    let mut branches = BTreeSet::new();
    let mut admitted_sources = BTreeSet::new();

    for (at, testimony) in testimonies.iter().enumerate() {
        let passage_branch = PassageBranchId((at + 1) as u64);
        let branch = BranchId((at + 1) as u64);
        let carrier = CarrierId((at + 1) as u64);
        let binder = BinderId((at + 1) as u64);
        let hypothesis = HypothesisId((at + 1) as u64);
        let branch_sources = testimony
            .occurrences
            .iter()
            .map(|occurrence| occurrence.address.clone())
            .collect::<BTreeSet<_>>();
        admitted_sources.extend(branch_sources.iter().cloned());
        branches.insert(branch);

        let input = operation.port(format!("branch-{at}-enter"));
        let output = operation.port(format!("branch-{at}-emit"));
        let deciding_testimony = vec![SourceTestimony::AuthoritativeDescription {
            statement: format!(
                "artifact occurrence {} carries {} situated faces into this branch",
                testimony.artifact.occurrence,
                testimony.occurrences.len()
            ),
        }];
        let stage_law = operation
            .bind_operation(
                format!("branch-{at}-stage"),
                OperationSpecies::Construction,
                Vec::new(),
                vec![input],
                None,
                deciding_testimony.clone(),
            )
            .map_err(|error| error.to_string())?;
        let carry_law = operation
            .bind_operation(
                format!("branch-{at}-carry"),
                OperationSpecies::Transport,
                vec![input],
                vec![output],
                Some("exact-addressed-incidence".to_owned()),
                deciding_testimony,
            )
            .map_err(|error| error.to_string())?;
        let stage_event = operation
            .occur(stage_law)
            .map_err(|error| error.to_string())?;
        let carry_event = operation
            .occur(carry_law)
            .map_err(|error| error.to_string())?;
        operation
            .carries_precedence(
                format!("branch-{at}-lineage"),
                input,
                OccurrencePort::output(stage_event, 0),
                OccurrencePort::input(carry_event, 0),
            )
            .map_err(|error| error.to_string())?;
        staging_sources.insert(passage_branch, branch_sources.clone());
        staging.insert(
            passage_branch,
            TypedConstructionStep {
                event: stage_event,
                law: stage_law,
                outputs: vec![input],
            },
        );
        words.insert(
            passage_branch,
            TypedOperationWord::found(
                format!("r1-branch-{at}-word"),
                vec![OperationWordStep {
                    event: carry_event,
                    law: carry_law,
                    inputs: vec![input],
                    outputs: vec![output],
                }],
                &operation,
            )
            .map_err(|error| error.to_string())?,
        );
        carriers.push(CarrierOccurrence {
            id: carrier,
            source_occurrences: branch_sources.clone(),
            owner_carrier: "exact-addressed-incidence".to_owned(),
            equality_law_lineage:
                "payload SHA-256 is one receiver equality; situated occurrence identity remains"
                    .to_owned(),
        });
        binders.push(BinderScope {
            id: binder,
            source_occurrences: branch_sources.clone(),
            ports: BTreeSet::from([input, output]),
            laws: BTreeSet::from([stage_law, carry_law]),
        });
        let slot = vec![TensorSlot {
            ordinal: 0,
            binder: binder.0,
            variance: TensorVariance::Covariant,
            role: TensorSlotRole::Free,
        }];
        for boundary in [input, output] {
            ports.push(TypedPort {
                boundary: TypedMathematicalBoundary::new(
                    boundary,
                    "exact-addressed-incidence",
                    Some(dimensionless.clone()),
                    slot.clone(),
                )
                .map_err(|error| error.to_string())?,
                carrier,
                unit_frame: Vec::new(),
                exposed: true,
            });
        }
        hypotheses.push(HypothesisLicense {
            id: hypothesis,
            source_occurrences: branch_sources,
            licenses: BTreeSet::from([stage_law, carry_law]),
            branches: BTreeSet::from([branch]),
        });
        for (law, input_arity, output_arity) in [(stage_law, 0, 1), (carry_law, 1, 1)] {
            operations.push(TypedOperation {
                law,
                input_arity,
                output_arity,
                hypotheses: BTreeSet::from([hypothesis]),
                branches: BTreeSet::from([branch]),
            });
        }
    }
    let passage = TypedPassage::found(
        "r1/material-founded-passage",
        staging_sources,
        staging,
        words,
        &operation,
        &admitted_sources,
    )
    .map_err(|error| error.to_string())?;
    Ok(OperationBoundary {
        operation,
        passage,
        carriers,
        binders,
        ports,
        operations,
        hypotheses,
        branches,
    })
}

fn record_layout(
    relative: &str,
    bytes: &[u8],
    exchange: &ExchangeWorldTube,
) -> Result<SourceLayoutTestimony, String> {
    let artifact = ArtifactIdentity::of_bytes("r1/inquiry/json-records", relative, bytes)
        .map_err(|error| error.to_string())?;
    let width = exchange
        .records
        .iter()
        .map(|record| (record.raw_range.end - record.raw_range.start) as usize)
        .max()
        .unwrap_or(1);
    let occurrences = exchange
        .records
        .iter()
        .enumerate()
        .map(|(at, record)| {
            let payload = bytes
                .get(record.raw_range.start as usize..record.raw_range.end as usize)
                .ok_or_else(|| "A1 record range left the captured JSON occurrence".to_owned())?
                .to_vec();
            PlacedCarrier::new(
                &artifact,
                at as u64,
                payload,
                Some(at as u64),
                ExactBox::new(
                    integer(0),
                    integer(at),
                    integer((record.raw_range.end - record.raw_range.start) as usize),
                    integer(at + 1),
                )
                .map_err(|error| error.to_string())?,
            )
            .map_err(|error| error.to_string())
        })
        .collect::<Result<Vec<_>, String>>()?;
    let extent = ExactExtent::new(integer(width), integer(exchange.records.len()))
        .map_err(|error| error.to_string())?;
    let demand = layout_demand(&occurrences).map_err(|error| error.to_string())?;
    derive_layout(
        TestimonyChart::BornDigital,
        artifact,
        extent,
        occurrences,
        &SourceLayoutWorkCover::exactly(&demand),
    )
    .map_err(|error| error.to_string())
}

fn line_layout(
    root: &Path,
    relative: &str,
    occurrence: &str,
    chart: TestimonyChart,
) -> Result<SourceLayoutTestimony, String> {
    let bytes = fs::read(root.join(relative)).map_err(|error| error.to_string())?;
    let artifact = ArtifactIdentity::of_bytes(occurrence, relative, &bytes)
        .map_err(|error| error.to_string())?;
    let lines = bytes
        .split(|octet| *octet == b'\n')
        .filter(|line| !line.is_empty())
        .collect::<Vec<_>>();
    let width = lines.iter().map(|line| line.len()).max().unwrap_or(1);
    let occurrences = lines
        .iter()
        .enumerate()
        .map(|(at, line)| {
            PlacedCarrier::new(
                &artifact,
                at as u64,
                line.to_vec(),
                Some(at as u64),
                ExactBox::new(
                    integer(0),
                    integer(at),
                    integer(line.len()),
                    integer(at + 1),
                )
                .map_err(|error| error.to_string())?,
            )
            .map_err(|error| error.to_string())
        })
        .collect::<Result<Vec<_>, String>>()?;
    let extent = ExactExtent::new(integer(width), integer(lines.len()))
        .map_err(|error| error.to_string())?;
    let demand = layout_demand(&occurrences).map_err(|error| error.to_string())?;
    derive_layout(
        chart,
        artifact,
        extent,
        occurrences,
        &SourceLayoutWorkCover::exactly(&demand),
    )
    .map_err(|error| error.to_string())
}

fn diagram_layout(
    root: &Path,
    relative: &str,
    occurrence: &str,
    reflow: bool,
) -> Result<SourceLayoutTestimony, String> {
    let bytes = fs::read(root.join(relative)).map_err(|error| error.to_string())?;
    let artifact = ArtifactIdentity::of_bytes(occurrence, relative, &bytes)
        .map_err(|error| error.to_string())?;
    let labels = ["E_n(Q)", "slots", "valuations", "squarefree", "support 2n"];
    let text = std::str::from_utf8(&bytes).map_err(|error| error.to_string())?;
    if labels.iter().any(|label| !text.contains(label)) {
        return Err(format!("{relative} lost one addressed diagram carrier"));
    }
    let boxes = if reflow {
        [
            (20, 40, 160, 140),
            (240, 40, 360, 140),
            (440, 160, 560, 260),
            (640, 280, 760, 380),
            (840, 280, 980, 380),
        ]
    } else {
        [
            (20, 70, 160, 170),
            (240, 70, 360, 170),
            (440, 70, 560, 170),
            (640, 70, 760, 170),
            (840, 70, 980, 170),
        ]
    };
    let occurrences = labels
        .iter()
        .zip(boxes)
        .enumerate()
        .map(|(at, (label, (left, top, right, bottom)))| {
            PlacedCarrier::new(
                &artifact,
                at as u64,
                label.as_bytes().to_vec(),
                Some(at as u64),
                ExactBox::new(integer(left), integer(top), integer(right), integer(bottom))
                    .map_err(|error| error.to_string())?,
            )
            .map_err(|error| error.to_string())
        })
        .collect::<Result<Vec<_>, String>>()?;
    let extent = ExactExtent::new(integer(1000), integer(if reflow { 420 } else { 240 }))
        .map_err(|error| error.to_string())?;
    let demand = layout_demand(&occurrences).map_err(|error| error.to_string())?;
    derive_layout(
        TestimonyChart::Vector,
        artifact,
        extent,
        occurrences,
        &SourceLayoutWorkCover::exactly(&demand),
    )
    .map_err(|error| error.to_string())
}

fn file_identity(root: &Path, relative: &str) -> Result<FileIdentity, String> {
    let bytes = fs::read(root.join(relative)).map_err(|error| error.to_string())?;
    Ok(FileIdentity {
        path: relative.to_owned(),
        sha256: digest(&bytes),
        octets: bytes.len() as u64,
    })
}

fn digest(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect()
}

fn integer(value: usize) -> Rat {
    Rat::from_integer(BigInt::from(value))
}
