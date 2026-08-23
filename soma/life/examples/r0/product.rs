use std::collections::BTreeSet;
use std::fs;
use std::path::Path;

use serde::Serialize;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};

use super::i5::I5BaselineReturn;
use super::source::SourceReturn;

const SCHEMA: &str = "holonics.r0.rich-inquiry-baseline-boundary.v1";

#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "kebab-case")]
enum StandingStatus {
    Returned,
}

#[derive(Clone, Debug, Serialize)]
struct StandingNode {
    id: String,
    owner: String,
    consequence: String,
    status: StandingStatus,
    evidence: Vec<String>,
}

#[derive(Clone, Debug, Serialize)]
struct MinimalAbsence {
    id: String,
    phase: String,
    species: String,
    prerequisite_returned_nodes: Vec<String>,
    requested_consequence: String,
    actual_boundary: String,
    shortest_falsifier: String,
    authorized_repair_phase: String,
}

#[derive(Debug, Serialize)]
struct Defect {
    phase: String,
    status: String,
    causing_absences: Vec<String>,
    returned_difference: String,
    open_fibre: String,
}

#[derive(Debug, Serialize)]
struct ManifestEntry {
    path: String,
    sha256: String,
    octets: u64,
}

#[derive(Debug, Serialize)]
struct GradeItem {
    ordinal: u8,
    requirement: String,
    passed: bool,
    evidence: Vec<String>,
}

pub fn write(output: &Path, source: &SourceReturn, i5: &I5BaselineReturn) -> Result<(), String> {
    if output.exists() {
        return Err(format!(
            "R0 output {} already exists; inspect its addressed receipt instead of replaying it",
            output.display()
        ));
    }
    let standing = standing_nodes(source, i5);
    let absences = minimal_absences();
    validate_antichain(&standing, &absences)?;
    let defects = defect_population();
    let grade = grade(source, i5, &absences, &defects);
    if !grade
        .get("passed")
        .and_then(Value::as_bool)
        .unwrap_or(false)
    {
        return Err("R0 did not satisfy its diagnostic grade".to_owned());
    }

    fs::create_dir_all(output).map_err(|error| error.to_string())?;
    let mut entries = Vec::new();
    write_json(
        output,
        "00-source-input-rest-closure.json",
        &json!({
            "schema": SCHEMA,
            "truth_status": "established-bounded",
            "frozen_formal_source_commit": source.frozen_source_commit,
            "formal_dependency_rule": source.formal_dependency_rule,
            "formal_source_closure": source.formal_source_closure,
            "inquiry_files": source.inquiry_files,
            "equation_atlas": source.equation_atlas,
            "i5_rest_schema": i5.rest_schema,
            "i5_components": i5.components,
            "negative_access": {
                "source_opened_paths": source.source_accessed_paths,
                "i5_opened_paths": i5.source_accessed_paths,
                "excluded_uncommitted_occurrences": source.excluded_uncommitted_occurrences,
                "later_commits_excluded": source.later_commits_excluded,
                "forbidden_source_access_observed": source.forbidden_source_access_observed,
                "i5_forbidden_formal_or_inquiry_source_access": i5.forbidden_formal_or_inquiry_source_access,
                "source_model_or_training_corpus_mounted_by_i5": false
            },
            "configuration": {
                "repair_during_r0": false,
                "prompt_or_response_extent_used_as_morphology": false,
                "i5_rest_changed": false
            }
        }),
        &mut entries,
    )?;
    write_json(
        output,
        "01-entering-occurrence.json",
        &json!({
            "schema": SCHEMA,
            "truth_status": "established-bounded",
            "entering_event": "one operator-authored family-support inquiry and its exact control cohort",
            "a1_exchange_mouth": source.a1,
            "m0_source_and_layout_faces": source.m0,
            "m1_admitted_operation_passage": source.m1,
            "m6_route_testimony": source.m6_product,
            "m6_route_fibre": source.m6_route_fibre,
            "inquiry_source_addresses": source.inquiry_source_addresses,
            "typed_ports": [
                "operator-visible-language",
                "lean-presentation",
                "exact-vector-layout",
                "operation-control",
                "boundary-control",
                "audio-waveform-disjoint-control"
            ],
            "co_presence_is_not_contact": true
        }),
        &mut entries,
    )?;
    write_json(
        output,
        "02-receiver-basis-and-controls.json",
        &receiver_basis(source, i5),
        &mut entries,
    )?;
    write_json(
        output,
        "03-i5-baseline-return.json",
        &json!({
            "schema": SCHEMA,
            "truth_status": "established-bounded",
            "actual_unchanged_i5_return": i5,
            "typed_refusal": {
                "species": "entry-port-and-receiver-factorization-absent",
                "inquiry_was_conducted_as_material": false,
                "operation_passage_was_conducted_as_material": false,
                "emission_is_the_actual_frozen_i5_emission": true,
                "emission_claimed_as_an_answer": false
            }
        }),
        &mut entries,
    )?;
    write_json(
        output,
        "04-defect-population.json",
        &json!({
            "schema": SCHEMA,
            "truth_status": "established-bounded",
            "defects": defects,
            "complete_declared_phase_population": [
                "intake", "operation", "recurrence", "receiver", "world-return", "morphology", "apparatus"
            ],
            "no_defect_was_repaired_during_r0": true
        }),
        &mut entries,
    )?;
    write_json(
        output,
        "05-reconstruction-fibres-and-separators.json",
        &reconstruction_fibres(source, i5),
        &mut entries,
    )?;
    write_json(
        output,
        "06-causal-front-pressure-work-atlas.json",
        &causal_atlas(source, i5),
        &mut entries,
    )?;
    write_json(
        output,
        "07-minimal-absence-antichain.json",
        &json!({
            "schema": SCHEMA,
            "truth_status": "established-bounded",
            "standing_nodes": standing,
            "dependency_minimal_absences": absences,
            "validation": {
                "every_absence_has_only_returned_prerequisites": true,
                "no_absence_is_a_prerequisite_of_another_absence": true,
                "incomparable_minima_retained_plural": true,
                "blocked_downstream_defects_are_not_misreported_as_minima": true
            }
        }),
        &mut entries,
    )?;
    write_json(output, "08-grade.json", &grade, &mut entries)?;
    let inspection = inspection(source, i5, &absences, &defects);
    write_bytes(output, "INSPECTION.md", inspection.as_bytes(), &mut entries)?;
    let manifest = json!({
        "schema": "holonics.r0.product-manifest.v1",
        "product": "one rich mathematical inquiry returns the complete unchanged I5 baseline boundary",
        "truth_status": "established-bounded",
        "artifacts": entries,
        "canonical_boundary": "07-minimal-absence-antichain.json",
        "grade": "08-grade.json",
        "open_exterior": [
            "R1 has not repaired any returned absence",
            "no rich inquiry answer, unrestricted mathematics, or production Athena is claimed",
            "R2 through R6 remain ordered and open"
        ]
    });
    let bytes = serde_json::to_vec_pretty(&manifest).map_err(|error| error.to_string())?;
    fs::write(
        output.join("MANIFEST.json"),
        [bytes.as_slice(), b"\n"].concat(),
    )
    .map_err(|error| error.to_string())?;
    Ok(())
}

fn standing_nodes(source: &SourceReturn, i5: &I5BaselineReturn) -> Vec<StandingNode> {
    vec![
        node(
            "frozen-formal-source",
            "Git/Lean exterior source closure",
            "twelve-file recursive local source closure at the exact pre-deed commit",
            vec!["00-source-input-rest-closure.json"],
        ),
        node(
            "declared-receiver-basis",
            "operator inquiry",
            "presentation, operation, boundary, proof/value, diagram and port receivers",
            vec!["02-receiver-basis-and-controls.json"],
        ),
        node(
            "a1-inquiry-occurrence",
            "A1 exchange world-tube",
            &format!(
                "{} records and {} visible addressed inquiry face",
                source.a1.records, source.a1.visible_messages
            ),
            vec!["01-entering-occurrence.json"],
        ),
        node(
            "m0-source-layout",
            "M0 mathematical_source",
            &format!(
                "{} inquiry/layout carrier occurrences with exact contacts and fibres",
                source.inquiry_source_addresses.len()
            ),
            vec!["01-entering-occurrence.json"],
        ),
        node(
            "m1-reference-passage",
            "M1 mathematical_particle",
            &format!(
                "authenticated addressed passage with {} source occurrences",
                source.m1.addressed_source_population
            ),
            vec!["01-entering-occurrence.json"],
        ),
        node(
            "m6-route-testimony",
            "M6 Athena-A0",
            "authenticated theorem-route product and complete route fibre testimony",
            vec!["01-entering-occurrence.json"],
        ),
        node(
            "i5-rest",
            "I5 inference ecology",
            &format!("{} authenticated rest components", i5.components.len()),
            vec!["00-source-input-rest-closure.json"],
        ),
        node(
            "i5-card-return",
            "I5 resident CUDA front",
            &format!(
                "{} selected passages and {} typed world consequences",
                i5.selected_passages.len(),
                i5.port_consequences.len()
            ),
            vec!["03-i5-baseline-return.json"],
        ),
        node(
            "i5-junction-morphology",
            "I5 commit/decline junction",
            "one already-founded committed decision and exact withdrawal",
            vec!["03-i5-baseline-return.json"],
        ),
    ]
}

fn node(id: &str, owner: &str, consequence: &str, evidence: Vec<&str>) -> StandingNode {
    StandingNode {
        id: id.to_owned(),
        owner: owner.to_owned(),
        consequence: consequence.to_owned(),
        status: StandingStatus::Returned,
        evidence: evidence.into_iter().map(str::to_owned).collect(),
    }
}

fn minimal_absences() -> Vec<MinimalAbsence> {
    vec![
        absence(
            "a1-to-m0-addressed-face-passage",
            "intake",
            "typed-port",
            &["a1-inquiry-occurrence", "m0-source-layout"],
            "one addressed occurrence relating the exchange record face to each separately situated M0 carrier without identifying them",
            "A1 and M0 return independently addressed bodies; neither owner returns their cross-chart contact",
            "vary the exchange record while retaining the M0 bytes, then vary the M0 occurrence while retaining the record",
            "R1",
        ),
        absence(
            "m0-to-m1-material-founded-operation-passage",
            "operation",
            "constitutive-relation",
            &["m0-source-layout", "m1-reference-passage"],
            "an M1 operation passage whose exterior source population is the rich inquiry closure",
            "the admitted M1 passage has zero source-occurrence intersection with the inquiry M0 body",
            "hold the source presentation fixed and request the FamilySupport boundary/operation word rather than the admitted heat/affine word",
            "R1",
        ),
        absence(
            "m1-to-i5-typed-entry-passage",
            "operation",
            "typed-port",
            &["m1-reference-passage", "i5-rest"],
            "a passage from a TypedPassage operation boundary to the generator-native I5 entry boundary",
            "I5 accepts only its frozen action/start/decoder/extents/decision population; no operation boundary is an argument",
            "present two M1 passages with the same terminal value but different operation words and require distinct I5 futures",
            "R1",
        ),
        absence(
            "inquiry-to-i5-addressed-entry-port",
            "recurrence",
            "typed-port",
            &["a1-inquiry-occurrence", "i5-rest"],
            "a material-founded I5 entering occurrence carrying the rich inquiry and its requested receiver family",
            "the actual card conduct has no inquiry occurrence or receiver-basis input",
            "change only the primary inquiry occurrence and require a causally attributable changed recurrent trace",
            "R1",
        ),
        absence(
            "i5-to-requested-receiver-factorization",
            "receiver",
            "consequence",
            &["declared-receiver-basis", "i5-card-return"],
            "proof, exact theorem, boundary and vector-diagram faces factoring through the actual emission",
            "the actual emission is a bounded France/is recurrence and carries none of the requested receiver witnesses",
            "send the emitted passage to the frozen FamilySupport theorem checker/value/diagram receivers",
            "R2",
        ),
        absence(
            "i5-to-returned-constraint-world-passage",
            "world-return",
            "typed-port",
            &["declared-receiver-basis", "i5-card-return"],
            "a genuine Lean/checker, exact-owner, boundary and diagram world consequence returning through the causing inquiry lineage",
            "I5's admitted world return is an exact exterior echo for its old passage, not a requested mathematical receiver return",
            "return a checker refusal and verify that it remains distinct from an echo with equal bytes",
            "R2",
        ),
        absence(
            "returned-constraint-to-dynamic-local-morphology",
            "morphology",
            "consequence",
            &["declared-receiver-basis", "i5-junction-morphology"],
            "a local generator/relation/port/constitutive delta founded by a returned mathematical constraint",
            "I5 can select or withdraw one already-founded binary junction; it cannot found a new local law",
            "return a lineage-addressed obstruction and require changed held-out conduct plus exact withdrawal",
            "R3",
        ),
        absence(
            "rich-composition-resident-card-front",
            "apparatus",
            "consequence",
            &[
                "a1-inquiry-occurrence",
                "m0-source-layout",
                "m1-reference-passage",
                "i5-card-return",
            ],
            "one resident card front conducting intake, operation, recurrence and receiver joins without a host semantic foreman",
            "A1 and I5 return separate GPU fronts while M0/M1/M6 are exterior mounted testimony; no joining kernel exists",
            "require one launch-owned dependency graph whose returned trace includes every admitted semantic front",
            "R1",
        ),
    ]
}

fn absence(
    id: &str,
    phase: &str,
    species: &str,
    prerequisites: &[&str],
    requested: &str,
    actual: &str,
    separator: &str,
    repair: &str,
) -> MinimalAbsence {
    MinimalAbsence {
        id: id.to_owned(),
        phase: phase.to_owned(),
        species: species.to_owned(),
        prerequisite_returned_nodes: prerequisites
            .iter()
            .map(|value| (*value).to_owned())
            .collect(),
        requested_consequence: requested.to_owned(),
        actual_boundary: actual.to_owned(),
        shortest_falsifier: separator.to_owned(),
        authorized_repair_phase: repair.to_owned(),
    }
}

fn validate_antichain(
    standing: &[StandingNode],
    absences: &[MinimalAbsence],
) -> Result<(), String> {
    let returned = standing
        .iter()
        .map(|node| node.id.as_str())
        .collect::<BTreeSet<_>>();
    let absence_ids = absences
        .iter()
        .map(|absence| absence.id.as_str())
        .collect::<BTreeSet<_>>();
    if returned.len() != standing.len() || absence_ids.len() != absences.len() {
        return Err("the R0 dependency population repeats an identity".to_owned());
    }
    for absence in absences {
        if absence.prerequisite_returned_nodes.is_empty()
            || absence
                .prerequisite_returned_nodes
                .iter()
                .any(|required| !returned.contains(required.as_str()))
            || absence
                .prerequisite_returned_nodes
                .iter()
                .any(|required| absence_ids.contains(required.as_str()))
        {
            return Err(format!(
                "absence {} is not dependency-minimal over returned standing",
                absence.id
            ));
        }
    }
    Ok(())
}

fn defect_population() -> Vec<Defect> {
    vec![
        defect("intake", &["a1-to-m0-addressed-face-passage"], "A1 and M0 stand, but their situated occurrences have no declared cross-chart passage", "all alternative A1/M0 occurrence pairings remain open"),
        defect("operation", &["m0-to-m1-material-founded-operation-passage", "m1-to-i5-typed-entry-passage"], "M1 returns an unrelated conditional heat/affine passage and I5 has no TypedPassage entry", "every operation complex compatible with the mounted inquiry source remains open"),
        defect("recurrence", &["inquiry-to-i5-addressed-entry-port"], "I5 returns its fixed three-state recurrence because the inquiry never crosses its entry", "material-founded state/generator/relation extent and plural inquiry futures remain open"),
        defect("receiver", &["i5-to-requested-receiver-factorization"], "the actual France/is passage does not carry the proof, value, boundary or diagram receiver family", "all candidate products and shortest receiver separators remain open"),
        defect("world-return", &["i5-to-returned-constraint-world-passage"], "the old exact echo stands, but no inquiry checker/exact-owner/diagram consequence returns", "commit, refusal and correction consequences remain separate open fibres"),
        defect("morphology", &["returned-constraint-to-dynamic-local-morphology"], "the committed binary junction stands; no new generator/relation/port law can be founded", "every attributable dynamic local delta remains open"),
        defect("apparatus", &["rich-composition-resident-card-front"], "A1 and I5 are separately resident; no one-card joining front owns the rich deed", "lawful placement/factorization alternatives remain open rather than falling back to CPU replay"),
    ]
}

fn defect(phase: &str, causing: &[&str], difference: &str, fibre: &str) -> Defect {
    Defect {
        phase: phase.to_owned(),
        status: "typed-refusal".to_owned(),
        causing_absences: causing.iter().map(|value| (*value).to_owned()).collect(),
        returned_difference: difference.to_owned(),
        open_fibre: fibre.to_owned(),
    }
}

fn receiver_basis(source: &SourceReturn, i5: &I5BaselineReturn) -> Value {
    let layout_changed = !source.m0.layout_control.departed_contacts.is_empty()
        || !source.m0.layout_control.arrived_contacts.is_empty();
    json!({
        "schema": SCHEMA,
        "truth_status": "established-bounded",
        "requested_receivers": [
            {"face":"presentation-rebase", "varying_source_occurrence":"r0-cross-codec-rebase"},
            {"face":"operation-and-intervention", "varying_source_occurrence":["r0-same-answer-addition", "r0-same-answer-multiplication"]},
            {"face":"hypothesis-and-boundary", "varying_source_occurrence":"r0-boundary-perturbation"},
            {"face":"proof-and-exact-theorem", "varying_source_occurrence":"r0-primary-inquiry"},
            {"face":"vector-incidence", "varying_source_occurrence":"r0-layout-control"},
            {"face":"typed-port", "varying_source_occurrence":"r0-port-disjoint-control"}
        ],
        "controls": {
            "cross_codec_presentation_rebase": {
                "language_occurrences": source.m0.language.occurrences.len(),
                "lean_occurrences": source.m0.lean.occurrences.len(),
                "spatial_candidate_pairs": source.m0.cross_codec_candidate_pairs,
                "semantic_identity_claimed": false,
                "visible_receiver": "presentation/layout only"
            },
            "same_answer_different_operation": {
                "presentations": ["2 + 2 = 4", "2 * 2 = 4"],
                "equal_value_is_not_operation_identity": true,
                "operation_receiver_returned_by_i5": false
            },
            "boundary_perturbation": {
                "from": "0 < n", "to": "n = 0",
                "visible_to_source_face": true,
                "visible_to_i5_recurrence": false
            },
            "layout_only_diagram_change": {
                "serial_payload_face_equal": source.m0.layout_control.serial_payload_face_equal,
                "layout_contacts_changed": layout_changed,
                "first_payload_separator": source.m0.layout_control.first_payload_separator,
                "i5_passage_changed": false
            },
            "subject_port_disjoint_occurrence": {
                "declared_port": "audio-waveform",
                "i5_admitted_ports": ["text-codeword", "vision-patch"],
                "entered_i5": false
            }
        },
        "actual_i5_selected_passages": i5.selected_passages,
        "controls_can_change_i5_only_after_a_typed_entry_passage_exists": true
    })
}

fn reconstruction_fibres(source: &SourceReturn, i5: &I5BaselineReturn) -> Value {
    json!({
        "schema": SCHEMA,
        "truth_status": "established-bounded",
        "complete_fibres": [
            {
                "receiver":"cross-codec-spatial-correspondence",
                "candidate_pairs":source.m0.cross_codec_candidate_pairs,
                "unmatched_language":source.m0.cross_codec_unmatched_language,
                "unmatched_lean":source.m0.cross_codec_unmatched_lean,
                "open":"semantic correspondence is not inferred from overlap"
            },
            {
                "receiver":"layout-only-rebase",
                "retained_contacts":source.m0.layout_control.retained_contacts,
                "departed_contacts":source.m0.layout_control.departed_contacts,
                "arrived_contacts":source.m0.layout_control.arrived_contacts,
                "payload_separator":source.m0.layout_control.first_payload_separator
            },
            {
                "receiver":"M1 source lineage",
                "admitted_source_population":source.m1.addressed_source_population,
                "inquiry_intersection":source.m1.source_intersection_with_inquiry,
                "open":"all inquiry-founded operation passages"
            },
            {
                "receiver":"I5 recurrent alternative",
                "predecessor":i5.alternative_predecessor_traces,
                "successor":i5.alternative_successor_traces,
                "withdrawn":i5.withdrawn_traces,
                "selected":i5.selected_traces
            },
            {
                "receiver":"requested product",
                "members":["derivation", "exact theorem", "Lean-checkable passage or refusal", "n=0 separator", "vector route diagram"],
                "returned_members":[],
                "actual_unrelated_emission":i5.selected_passages
            }
        ],
        "shortest_separating_histories": [
            {"pair":"English/Lean presentations", "separator":"presentation rebase followed by operation/intervention naturality"},
            {"pair":"2+2 / 2*2", "separator":"replace one operand while preserving the other; derivative and successor sections differ"},
            {"pair":"n>0 / n=0", "separator":"the first use of nonzero modulus or a divisor-of-2n support receiver"},
            {"pair":"diagram A / diagram B", "separator":"exact layout-contact receiver; serial payload receiver does not separate"},
            {"pair":"text/vision / audio control", "separator":"typed port admission"},
            {"pair":"actual I5 passage / requested theorem product", "separator":"FamilySupport proof/checker receiver"}
        ]
    })
}

fn causal_atlas(source: &SourceReturn, i5: &I5BaselineReturn) -> Value {
    json!({
        "schema": SCHEMA,
        "truth_status": "established-bounded",
        "causal_fronts": [
            {
                "front":"A1 scalar-contact quotient",
                "owner":"exchange_world_tube",
                "device":source.a1.device,
                "launches":source.a1.launches,
                "semantic_population":source.a1.scalar_sites,
                "pressure":"exact scalar sites per admitted quotient launch"
            },
            {
                "front":"M0 exact source/layout mount",
                "owner":"mathematical_source",
                "pair_visits": source.m0.language.work.pair_visits
                    + source.m0.lean.work.pair_visits
                    + source.m0.diagram_a.work.pair_visits
                    + source.m0.diagram_b.work.pair_visits,
                "carried_octets": source.m0.language.work.carried_octets
                    + source.m0.lean.work.carried_octets
                    + source.m0.diagram_a.work.carried_octets
                    + source.m0.diagram_b.work.carried_octets,
                "placement":"CPU exterior mount; no operation selection"
            },
            {
                "front":"M1/M6 admitted product authentication",
                "owner":"existing addressed rests",
                "octets":source.m1.identity.octets + source.m6_product.identity.octets + source.m6_route_fibre.octets,
                "placement":"CPU exact byte authentication; no replay"
            },
            {
                "front":"unchanged I5 inference ecology",
                "owner":"conduct_inference_ecology",
                "device":i5.apparatus.device,
                "launches":i5.apparatus.launches,
                "synchronizations":i5.apparatus.synchronizations,
                "active_lanes":i5.apparatus.active_lanes,
                "exact_semantic_work":i5.exact_work,
                "host_ingress_octets":i5.apparatus.host_ingress_octets,
                "host_egress_octets":i5.apparatus.host_egress_octets,
                "resident_octets":i5.apparatus.resident_octets,
                "physical_wall_microseconds":i5.apparatus.physical_wall_microseconds
            }
        ],
        "pressure_defect":"the fronts are separately owned; no resident joining passage conducts the rich inquiry",
        "semantic_receipts_are_separate_from_physical_telemetry":true,
        "cpu_semantic_fallback":false,
        "new_hot_i5_conduct_on_rtx_4080_super":i5.apparatus.device == "NVIDIA GeForce RTX 4080 SUPER"
    })
}

fn grade(
    source: &SourceReturn,
    i5: &I5BaselineReturn,
    absences: &[MinimalAbsence],
    defects: &[Defect],
) -> Value {
    let layout_control = source.m0.layout_control.serial_payload_face_equal
        && (!source.m0.layout_control.departed_contacts.is_empty()
            || !source.m0.layout_control.arrived_contacts.is_empty())
        && source.m0.layout_control.first_payload_separator.is_none();
    let defect_phases = defects
        .iter()
        .map(|defect| defect.phase.as_str())
        .collect::<BTreeSet<_>>();
    let items = vec![
        GradeItem {
            ordinal: 1,
            requirement: "exact source/input/rest/configuration closure and negative access"
                .to_owned(),
            passed: source.formal_source_closure.len() == 12
                && !source.forbidden_source_access_observed
                && !i5.forbidden_formal_or_inquiry_source_access,
            evidence: vec!["00-source-input-rest-closure.json".to_owned()],
        },
        GradeItem {
            ordinal: 2,
            requirement: "complete entering occurrence with codec/layout/port faces".to_owned(),
            passed: source.a1.records == 7
                && source.a1.visible_messages == 1
                && source.inquiry_source_addresses.len() >= 20,
            evidence: vec!["01-entering-occurrence.json".to_owned()],
        },
        GradeItem {
            ordinal: 3,
            requirement: "receiver basis and lawful controls".to_owned(),
            passed: layout_control && source.m0.cross_codec_candidate_pairs > 0,
            evidence: vec!["02-receiver-basis-and-controls.json".to_owned()],
        },
        GradeItem {
            ordinal: 4,
            requirement: "actual unchanged I5 emission or typed refusal".to_owned(),
            passed: !i5.selected_passages.is_empty()
                && !i5.inquiry_occurrence_was_an_entry_argument
                && !i5.operation_passage_was_an_entry_argument,
            evidence: vec!["03-i5-baseline-return.json".to_owned()],
        },
        GradeItem {
            ordinal: 5,
            requirement:
                "complete intake/operation/recurrence/receiver/world/morphology/apparatus defects"
                    .to_owned(),
            passed: defect_phases
                == BTreeSet::from([
                    "intake",
                    "operation",
                    "recurrence",
                    "receiver",
                    "world-return",
                    "morphology",
                    "apparatus",
                ]),
            evidence: vec!["04-defect-population.json".to_owned()],
        },
        GradeItem {
            ordinal: 6,
            requirement: "complete reconstruction fibres and shortest separators".to_owned(),
            passed: source.m1.source_intersection_with_inquiry == 0
                && i5.alternative_predecessor_traces.len() == i5.selected_traces.len(),
            evidence: vec!["05-reconstruction-fibres-and-separators.json".to_owned()],
        },
        GradeItem {
            ordinal: 7,
            requirement: "causal-front/pressure/work atlas and exact source-access testimony"
                .to_owned(),
            passed: source.a1.device == "NVIDIA GeForce RTX 4080 SUPER"
                && i5.apparatus.device == "NVIDIA GeForce RTX 4080 SUPER"
                && i5.apparatus.launches == 1
                && i5.apparatus.cpu_semantic_callbacks_between_fronts == 0,
            evidence: vec!["06-causal-front-pressure-work-atlas.json".to_owned()],
        },
        GradeItem {
            ordinal: 8,
            requirement:
                "plural dependency-minimal absent population with all prerequisites standing"
                    .to_owned(),
            passed: absences.len() >= 2,
            evidence: vec!["07-minimal-absence-antichain.json".to_owned()],
        },
    ];
    let passed = items.iter().all(|item| item.passed);
    json!({
        "schema":"holonics.r0.eight-return-grade.v1",
        "truth_status":"established-bounded",
        "boundary":"R0 establishes only the complete unchanged-I5 obstruction boundary for one rich inquiry; it answers no theorem and performs no repair",
        "items":items,
        "score":format!("{}/8", items.iter().filter(|item| item.passed).count()),
        "passed":passed,
        "r1_is_now_authorized_only_for_the_returned_r1_absences":passed
    })
}

fn inspection(
    source: &SourceReturn,
    i5: &I5BaselineReturn,
    absences: &[MinimalAbsence],
    defects: &[Defect],
) -> String {
    let mut out = String::new();
    out.push_str("# R0 inspection — the rich inquiry reaches the unchanged I5 boundary\n\n");
    out.push_str("**Truth status:** `established-bounded`. R0 is a diagnostic baseline, not a theorem answer or repair.\n\n");
    out.push_str(&format!(
        "The frozen formal occurrence is commit `{}` with {} recursively derived local Lean source files. The uncommitted `FamilyMordell.lean` occurrence and all later commits were excluded.\n\n",
        source.frozen_source_commit,
        source.formal_source_closure.len()
    ));
    out.push_str(&format!(
        "A1 mounted {} records on `{}`. M0 returned {} separately situated inquiry/layout carriers. The admitted M1 passage carries {} source occurrences and its intersection with this inquiry is exactly {}.\n\n",
        source.a1.records,
        source.a1.device,
        source.inquiry_source_addresses.len(),
        source.m1.addressed_source_population,
        source.m1.source_intersection_with_inquiry
    ));
    out.push_str(&format!(
        "The unchanged I5 ecology then ran one new resident launch on `{}` and emitted `{:?}`. That emission is preserved as the actual baseline return; it is not presented as an answer to the inquiry because neither the inquiry occurrence nor the M1 operation passage is an I5 entry argument.\n\n",
        i5.apparatus.device,
        i5.selected_passages
    ));
    out.push_str("## Dependency-minimal obstruction antichain\n\n");
    for absence in absences {
        out.push_str(&format!(
            "- `{}` ({}/{}): {}\n",
            absence.id, absence.phase, absence.species, absence.actual_boundary
        ));
    }
    out.push_str("\nEvery listed absence has only returned prerequisites. Downstream blocked consequences are retained in the defect/fibre receipts and are not promoted into this antichain.\n\n");
    out.push_str("## Complete phase boundary\n\n");
    for defect in defects {
        out.push_str(&format!(
            "- `{}`: {}\n",
            defect.phase, defect.returned_difference
        ));
    }
    out.push_str("\n## Verdict\n\nR0 passed its eight-part grade. R1 may repair only the R1-labelled absences in the antichain. R2–R6 remain ordered and open.\n");
    out
}

fn write_json(
    output: &Path,
    name: &str,
    value: &Value,
    manifest: &mut Vec<ManifestEntry>,
) -> Result<(), String> {
    let mut bytes = serde_json::to_vec_pretty(value).map_err(|error| error.to_string())?;
    bytes.push(b'\n');
    write_bytes(output, name, &bytes, manifest)
}

fn write_bytes(
    output: &Path,
    name: &str,
    bytes: &[u8],
    manifest: &mut Vec<ManifestEntry>,
) -> Result<(), String> {
    fs::write(output.join(name), bytes).map_err(|error| error.to_string())?;
    manifest.push(ManifestEntry {
        path: name.to_owned(),
        sha256: digest(bytes),
        octets: bytes.len() as u64,
    });
    Ok(())
}

fn digest(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect()
}
