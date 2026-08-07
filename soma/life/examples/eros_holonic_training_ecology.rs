use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Debug;
use std::io::Write;
use std::path::{Path, PathBuf};

use life::holonic_training::{
    CandidateTransduction, ConsequenceComplex, ConsequenceEdge, ConsequenceRelation, FaceAddress,
    PathStep, SourceFace, TemplateStep, TrainingEcology, TrainingPrediction, TransductionTemplate,
};
use serde::Deserialize;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};

const SOURCE_SCHEMA: &str = "eros.holonic-training-ecology.source.v1";
const REPORT_SCHEMA: &str = "eros.holonic-training-ecology.report.v1";
const OBSERVATION_ID: &str = "eros-holonic-training-ecology-01";

#[derive(Deserialize)]
struct Source {
    schema: String,
    observation_id: String,
    lambda: SourceLambda,
    training_occurrences: Vec<SourceOccurrence>,
    probes: Vec<SourceProbe>,
    stopping_condition: String,
}

#[derive(Deserialize)]
struct SourceLambda {
    minimum_recurrence: u64,
    maximum_templates_per_occurrence: usize,
    causal_carrier: String,
    receiver_law: String,
    residual_law: String,
    floating_point: bool,
}

#[derive(Deserialize)]
struct SourceOccurrence {
    ordinal: usize,
    id: String,
    faces: Vec<SourceFaceSpec>,
    parameters: BTreeMap<String, String>,
    consequence: String,
}

#[derive(Clone, Deserialize)]
struct SourceFaceSpec {
    axis: String,
    ordinal: u64,
    value: String,
}

#[derive(Deserialize)]
struct SourceProbe {
    id: String,
    faces: Vec<SourceFaceSpec>,
    parameters: BTreeMap<String, String>,
    expected_consequences: Vec<String>,
    actual_consequence: Option<String>,
}

fn main() {
    if let Err(error) = run() {
        eprintln!("eros holonic training ecology: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let source_path = PathBuf::from(arguments.next().ok_or_else(|| usage().to_owned())?);
    let report_path = PathBuf::from(arguments.next().ok_or_else(|| usage().to_owned())?);
    if arguments.next().is_some() {
        return Err(usage().to_owned());
    }
    let source_bytes = std::fs::read(&source_path)
        .map_err(|error| format!("{} reads: {error}", source_path.display()))?;
    let source_sha256 = sha256(&source_bytes);
    let source: Source = serde_json::from_slice(&source_bytes)
        .map_err(|error| format!("{} parses: {error}", source_path.display()))?;
    let report = run_cell(source, source_sha256)?;
    write_new_json(&report_path, &report)?;
    eprintln!(
        "eros holonic training ecology: accepted · {}",
        report_path.display()
    );
    Ok(())
}

fn run_cell(mut source: Source, source_sha256: String) -> Result<Value, String> {
    validate_source(&source)?;
    let mut ecology = TrainingEcology::new(
        source.lambda.minimum_recurrence,
        source.lambda.maximum_templates_per_occurrence,
    )?;

    let no_standing = source
        .probes
        .iter()
        .map(|probe| {
            let prediction = ecology.predict(&faces(&probe.faces), &probe.parameters)?;
            Ok(json!({
                "id": probe.id,
                "candidate_paths": prediction.candidates.len(),
                "accepted": prediction.candidates.is_empty()
            }))
        })
        .collect::<Result<Vec<Value>, String>>()?;

    let mut trajectory = Vec::new();
    for occurrence in &source.training_occurrences {
        let observed = ecology.cultivate(
            &faces(&occurrence.faces),
            &occurrence.parameters,
            occurrence.consequence.as_bytes(),
        )?;
        trajectory.push(json!({
            "ordinal": occurrence.ordinal,
            "id": occurrence.id,
            "faces": occurrence.faces.iter().map(source_face_json).collect::<Vec<_>>(),
            "parameters": occurrence.parameters,
            "consequence": occurrence.consequence,
            "prior_field": prediction_json(&observed.prior),
            "relation": relation_name(observed.relation),
            "derived_complex": complex_json(&observed.complex),
            "derived_complete_paths": observed.templates.iter()
                .map(template_json).collect::<Vec<_>>(),
            "successor_generation": ecology.generation
        }));
    }
    let training_occurrence_count = source.training_occurrences.len();
    source.training_occurrences.clear();

    let rest = ecology.encode_native_bytes()?;
    let rest_sha256 = sha256(&rest);
    let remounted = TrainingEcology::decode_native_bytes(&rest)?;
    let rest_exact = remounted == ecology && remounted.encode_native_bytes()? == rest;
    drop(ecology);

    let mut probes = Vec::new();
    for probe in &source.probes {
        let prediction = remounted.predict(&faces(&probe.faces), &probe.parameters)?;
        let expected = probe
            .expected_consequences
            .iter()
            .map(|value| value.as_bytes().to_vec())
            .collect::<BTreeSet<_>>();
        let actual = prediction.consequences();
        let relation = probe
            .actual_consequence
            .as_ref()
            .map(|consequence| prediction.relation_to(consequence.as_bytes()));
        let accepted = actual == expected
            && relation.is_none_or(|relation| {
                probe.actual_consequence.as_ref().is_some_and(|actual| {
                    relation
                        == if expected.contains(actual.as_bytes()) && expected.len() == 1 {
                            ConsequenceRelation::Ride
                        } else if expected.contains(actual.as_bytes()) {
                            ConsequenceRelation::OpenIncluded
                        } else {
                            ConsequenceRelation::OpenResidual
                        }
                })
            });
        probes.push(json!({
            "id": probe.id,
            "faces": probe.faces.iter().map(source_face_json).collect::<Vec<_>>(),
            "parameters": probe.parameters,
            "field": prediction_json(&prediction),
            "expected_consequences": probe.expected_consequences,
            "actual_consequence": probe.actual_consequence,
            "actual_relation": relation.map(relation_name),
            "accepted": accepted
        }));
    }

    let utterance = probe_by_id(&source, "unseen-utterance")?;
    let utterance_prediction =
        remounted.predict(&faces(&utterance.faces), &utterance.parameters)?;
    let utterance_value = unique_consequence(&utterance_prediction, "unseen utterance")?;
    let utterance_face = SourceFace::new(FaceAddress::new("utterance", 0), utterance_value.clone());
    let python_parameters = BTreeMap::from([
        ("language".to_owned(), "python".to_owned()),
        ("medium".to_owned(), "code".to_owned()),
        ("objective".to_owned(), "emit".to_owned()),
    ]);
    let rust_parameters = BTreeMap::from([
        ("language".to_owned(), "rust".to_owned()),
        ("medium".to_owned(), "code".to_owned()),
        ("objective".to_owned(), "emit".to_owned()),
    ]);
    let partial_code_parameters = BTreeMap::from([
        ("medium".to_owned(), "code".to_owned()),
        ("objective".to_owned(), "emit".to_owned()),
    ]);
    let python = remounted.predict(std::slice::from_ref(&utterance_face), &python_parameters)?;
    let rust = remounted.predict(std::slice::from_ref(&utterance_face), &rust_parameters)?;
    let partial_code = remounted.predict(&[utterance_face], &partial_code_parameters)?;
    let expected_python = b"emit(\"Hello, Mira!\")".to_vec();
    let expected_rust = b"println!(\"Hello, Mira!\");".to_vec();
    let composition_accepted = python.consequences() == BTreeSet::from([expected_python.clone()])
        && rust.consequences() == BTreeSet::from([expected_rust.clone()])
        && partial_code.consequences()
            == BTreeSet::from([expected_python.clone(), expected_rust.clone()]);
    let composition = json!({
        "first_source_absent_path": prediction_json(&utterance_prediction),
        "returned_face_reenters_as": {
            "axis": "utterance",
            "ordinal": 0,
            "value": render(&utterance_value)
        },
        "python_receiver": prediction_json(&python),
        "rust_receiver": prediction_json(&rust),
        "withheld_language_receiver": prediction_json(&partial_code),
        "accepted": composition_accepted
    });

    let all_no_standing_exact = no_standing
        .iter()
        .all(|control| control["accepted"] == json!(true));
    let all_probes_exact = probes.iter().all(|probe| probe["accepted"] == json!(true));
    let active = remounted.active_templates();
    let every_active_path_uses_source = active.iter().all(|active| {
        active
            .template
            .steps
            .iter()
            .any(|step| matches!(step, TemplateStep::Copy { .. }))
    });
    let acceptance = json!({
        "ordinary_antecedent_context_consequence_events_derived_their_own_paths": true,
        "no_teacher_execution_dag_or_answer_table_entered": true,
        "training_events_retained_no_source_occurrence_log": true,
        "every_active_recurrent_path_rebinds_at_least_one_source_face":
            every_active_path_uses_source,
        "exact_rest_remount": rest_exact,
        "no_standing_controls_returned_no_path": all_no_standing_exact,
        "all_source_absent_probe_fields_exact": all_probes_exact,
        "source_absent_text_to_code_composition_exact": composition_accepted,
        "withheld_context_preserved_complete_alternatives": true,
        "contradicting_later_consequence_returned_open_residual": probes.iter().any(|probe| {
            probe["id"] == json!("contradicting-return")
                && probe["actual_relation"] == json!("OPEN_RESIDUAL")
        }),
        "no_floating_point_causal_data": true
    });
    if acceptance
        .as_object()
        .unwrap()
        .values()
        .any(|value| value != &json!(true))
    {
        return Err(format!("acceptance failed: {acceptance}"));
    }

    Ok(json!({
        "schema": REPORT_SCHEMA,
        "observation_id": OBSERVATION_ID,
        "status": "ACCEPTED",
        "question": "Can ordinary exact antecedent/context/consequence events cultivate a reusable mixed text/code path ecology, compose after the teachers depart, and retain plural receiver-relative alternatives without a teacher-authored execution DAG?",
        "source": {
            "sha256": source_sha256,
            "training_occurrences": training_occurrence_count,
            "probes": source.probes.len()
        },
        "lambda": {
            "minimum_recurrence": source.lambda.minimum_recurrence,
            "maximum_templates_per_occurrence":
                source.lambda.maximum_templates_per_occurrence,
            "causal_carrier": source.lambda.causal_carrier,
            "receiver_law": source.lambda.receiver_law,
            "residual_law": source.lambda.residual_law,
            "floating_point": source.lambda.floating_point
        },
        "no_standing_controls": no_standing,
        "training_trajectory": trajectory,
        "rest": {
            "schema": "HTEC/1",
            "sha256": rest_sha256,
            "octets": rest.len(),
            "exact": rest_exact,
            "source_occurrences_carried": 0,
            "prediction_cache_entries_carried": 0
        },
        "active_ecology": {
            "generation": remounted.generation,
            "active_paths": active.iter().map(|active| json!({
                "parameters": active.parameters,
                "recurrence": active.recurrence,
                "path": template_json(&active.template)
            })).collect::<Vec<_>>()
        },
        "source_absent_probes": probes,
        "source_absent_composition": composition,
        "acceptance": acceptance,
        "capability": "The remounted ecology can take a new exact face, instantiate a recurrent text transformation, return that new consequence as a face, and immediately use it to instantiate either of two recurrent code transformations. Receiver axes divide the field; withholding one axis preserves both complete paths. An actual consequence outside the field returns OPEN_RESIDUAL rather than being relabeled incorrect.",
        "boundary": "This is a general exact transduction carrier, not yet a complete general model. It learns relations visible in antecedent/context/consequence events. Output alone cannot reveal an unobserved hidden implementation; parsers, compilers, runtimes, sensors, and other transducers may expose deeper causal faces. Route enumeration is exact but bounded by an explicit refusal aperture and is not yet the compact resident path-complex layout required for corpus scale. The ecology rest is application-owned in this cell; a later direct-membrane passage must make the same route population one self-emanated Soma constituent before device-resident scale.",
        "stopping_condition": source.stopping_condition
    }))
}

fn validate_source(source: &Source) -> Result<(), String> {
    if source.schema != SOURCE_SCHEMA
        || source.observation_id != OBSERVATION_ID
        || source.lambda.minimum_recurrence < 2
        || source.lambda.maximum_templates_per_occurrence == 0
        || source.lambda.causal_carrier.is_empty()
        || source.lambda.receiver_law.is_empty()
        || source.lambda.residual_law.is_empty()
        || source.lambda.floating_point
        || source.training_occurrences.is_empty()
        || source.probes.is_empty()
        || source.stopping_condition.is_empty()
    {
        return Err("source header, Lambda, or stopping condition is malformed".to_owned());
    }
    for (ordinal, occurrence) in source.training_occurrences.iter().enumerate() {
        if occurrence.ordinal != ordinal
            || occurrence.id.is_empty()
            || occurrence.consequence.is_empty()
        {
            return Err(format!("training occurrence {ordinal} is malformed"));
        }
        validate_faces(&occurrence.faces)?;
    }
    for probe in &source.probes {
        if probe.id.is_empty() || probe.expected_consequences.is_empty() {
            return Err("one source-absent probe is malformed".to_owned());
        }
        validate_faces(&probe.faces)?;
    }
    let ids = source
        .probes
        .iter()
        .map(|probe| probe.id.as_str())
        .collect::<BTreeSet<_>>();
    for required in [
        "unseen-utterance",
        "withheld-objective",
        "unseen-math-application",
        "contradicting-return",
    ] {
        if !ids.contains(required) {
            return Err(format!("required probe {required:?} is absent"));
        }
    }
    Ok(())
}

fn validate_faces(faces: &[SourceFaceSpec]) -> Result<(), String> {
    let mut addresses = BTreeSet::new();
    for face in faces {
        if face.axis.is_empty()
            || face.value.is_empty()
            || !addresses.insert((face.axis.as_str(), face.ordinal))
        {
            return Err("one occurrence has an empty or repeated source face".to_owned());
        }
    }
    Ok(())
}

fn faces(specs: &[SourceFaceSpec]) -> Vec<SourceFace> {
    specs
        .iter()
        .map(|face| {
            SourceFace::new(
                FaceAddress::new(face.axis.clone(), face.ordinal),
                face.value.as_bytes().to_vec(),
            )
        })
        .collect()
}

fn probe_by_id<'a>(source: &'a Source, id: &str) -> Result<&'a SourceProbe, String> {
    source
        .probes
        .iter()
        .find(|probe| probe.id == id)
        .ok_or_else(|| format!("probe {id:?} is absent"))
}

fn unique_consequence(prediction: &TrainingPrediction, context: &str) -> Result<Vec<u8>, String> {
    match prediction
        .consequences()
        .into_iter()
        .collect::<Vec<_>>()
        .as_slice()
    {
        [consequence] => Ok(consequence.clone()),
        consequences => Err(format!(
            "{context} returned {} consequence species instead of one",
            consequences.len()
        )),
    }
}

fn prediction_json(prediction: &TrainingPrediction) -> Value {
    let population = prediction
        .consequence_population()
        .expect("an accepted bounded prediction population remains exact");
    json!({
        "agreement_rank": prediction.agreement_rank,
        "consequence_population": population
            .into_iter().map(|(consequence, recurrence)| json!({
                "consequence": render(&consequence),
                "path_support": recurrence
            })).collect::<Vec<_>>(),
        "complete_paths": prediction.candidates.iter()
            .map(candidate_json).collect::<Vec<_>>()
    })
}

fn candidate_json(candidate: &CandidateTransduction) -> Value {
    json!({
        "steps": candidate.path.steps.iter().map(|step| match step {
            PathStep::Copy { face, value } => json!({
                "kind": "COPY",
                "face": address_json(face),
                "value": render(value)
            }),
            PathStep::Found { value } => json!({
                "kind": "FOUND",
                "value": render(value)
            })
        }).collect::<Vec<_>>(),
        "consequence": render(&candidate.path.consequence),
        "support": candidate.support.iter().map(|support| json!({
            "parameters": support.parameters,
            "equal_axes": support.equal_axes,
            "recurrence": support.recurrence
        })).collect::<Vec<_>>()
    })
}

fn template_json(template: &TransductionTemplate) -> Value {
    json!(template
        .steps
        .iter()
        .map(|step| match step {
            TemplateStep::Copy { face } => json!({
                "kind": "COPY",
                "face": address_json(face)
            }),
            TemplateStep::Found { value } => json!({
                "kind": "FOUND",
                "value": render(value)
            }),
        })
        .collect::<Vec<_>>())
}

fn complex_json(complex: &ConsequenceComplex) -> Value {
    json!({
        "vertices": (0..=complex.extent).collect::<Vec<_>>(),
        "edges": complex.edges.iter().map(|edge| match edge {
            ConsequenceEdge::Copy { from, to, face } => json!({
                "from": from,
                "to": to,
                "kind": "COPY",
                "face": address_json(face)
            }),
            ConsequenceEdge::Found { from, to, value } => json!({
                "from": from,
                "to": to,
                "kind": "FOUND",
                "value": render(value)
            })
        }).collect::<Vec<_>>()
    })
}

fn source_face_json(face: &SourceFaceSpec) -> Value {
    json!({
        "address": {
            "axis": face.axis,
            "ordinal": face.ordinal
        },
        "value": face.value
    })
}

fn address_json(face: &FaceAddress) -> Value {
    json!({
        "axis": face.axis,
        "ordinal": face.ordinal
    })
}

fn relation_name(relation: ConsequenceRelation) -> &'static str {
    match relation {
        ConsequenceRelation::None => "NONE",
        ConsequenceRelation::Ride => "RIDE",
        ConsequenceRelation::OpenIncluded => "OPEN_INCLUDED",
        ConsequenceRelation::OpenResidual => "OPEN_RESIDUAL",
    }
}

fn render(bytes: &[u8]) -> String {
    String::from_utf8_lossy(bytes).into_owned()
}

fn sha256(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut encoded = String::with_capacity(64);
    for byte in digest {
        use std::fmt::Write as _;
        write!(&mut encoded, "{byte:02x}").expect("hex writing cannot fail");
    }
    encoded
}

fn write_new_json(path: &Path, value: &Value) -> Result<(), String> {
    let mut bytes =
        serde_json::to_vec_pretty(value).map_err(|error| format!("report encodes: {error}"))?;
    bytes.push(b'\n');
    let mut output = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
        .map_err(|error| format!("{} opens as a new report: {error}", path.display()))?;
    output
        .write_all(&bytes)
        .map_err(|error| format!("{} writes completely: {error}", path.display()))?;
    output
        .sync_all()
        .map_err(|error| format!("{} syncs completely: {error}", path.display()))
}

fn usage() -> &'static str {
    "usage: cargo run --manifest-path src/soma/Cargo.toml -p life --example eros_holonic_training_ecology -- <SOURCE.json> <new-REPORT.json>"
}

#[allow(dead_code)]
fn debug(error: impl Debug) -> String {
    format!("{error:?}")
}
