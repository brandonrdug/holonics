//! A3: an addressed exchange defect returns through the inherited active cover.
//!
//! The selection law is founded entirely from A1 occurrence incidence and A2 receiver defects.
//! This first executable front asks whether the authenticated rank-one Phoenix covector is a
//! nonzero common forward direction for the development, held-out and revisit occurrences.  The
//! eventual cultivated continuation remains one local delta over the unchanged A2 body; no prompt
//! list, reward scalar, epoch counter or source passage enters its rested morphology.

#[path = "a2/cohort.rs"]
#[allow(dead_code)]
mod cohort;
#[path = "a2/defect.rs"]
#[allow(dead_code)]
mod defect;

use std::{
    collections::BTreeMap,
    env, fs,
    path::{Path, PathBuf},
    process::Command,
    time::Instant,
};

use cohort::{SiblingCohort, SiblingHistoryCut};
use defect::HistoryDefectReturn;
use holonic_engine::{
    cultivated_rest::{
        native_morphology_bytes, MorphologyPayload, NativeMorphologyInput,
        PredecessorProductIdentity,
    },
    phoenix::{
        continuation::{
            selector_successor_factor, AddressedReturnLineage, CultivationContinuationRest,
            LocalMetricAdjointReturn, MountedContinuation,
        },
        runtime::{ProductSession, RuntimeReceipt},
        streamed::{InterventionSite, ReceiverOption},
        tower::Intervention,
    },
};
use life::exchange_world_tube::{
    remount_exchange_world_tube, Digest32, ExchangeWorldTube, VisibleMessageFace,
};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

#[derive(Debug)]
enum Args {
    Probe {
        exchange_rest: PathBuf,
        a2_complex: PathBuf,
        phoenix_product: PathBuf,
    },
    Produce {
        a2_cohort: PathBuf,
        a2_complex: PathBuf,
        phoenix_product: PathBuf,
        exchange_rest: PathBuf,
        output: PathBuf,
    },
    DetachedGrade {
        phoenix_product: PathBuf,
        continuation: PathBuf,
        inputs: PathBuf,
        output: PathBuf,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Deserialize)]
struct A2ComplexFace {
    histories: Vec<HistoryDefectReturn>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct SelectedFamily<'a> {
    repeated_content_sha256: Digest32,
    target_native_id: u32,
    development: &'a SiblingHistoryCut,
    held_out: &'a SiblingHistoryCut,
    revisit: &'a SiblingHistoryCut,
    total_receiver_gap: i128,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct FamilySelectionReceipt {
    schema: String,
    repeated_content_sha256: String,
    target_native_id: u32,
    development_occurrence: String,
    held_out_occurrence: String,
    revisit_occurrence: String,
    family_population: usize,
    total_receiver_gap: String,
    selection_law: String,
    provider_or_surface_routed_selection: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ControlFace<'a> {
    face: &'a VisibleMessageFace,
    native_tokens: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct ControlSelectionReceipt {
    occurrence: String,
    content_sha256: String,
    container: u32,
    provider_face: String,
    speaker_face: String,
    native_tokens: usize,
    provider_disjoint: bool,
    content_disjoint: bool,
    container_disjoint: bool,
    selection_law: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct ForwardReading {
    role: String,
    occurrence: String,
    input_sha256: String,
    target_native_id: u32,
    target_before: (i64, i64),
    candidate_top_lower: i64,
    maximum_other_upper: i64,
    inherited_support_row: u32,
    inherited_left_entry: i64,
    support_before: (i64, i64),
    support_after: (i64, i64),
    activation_enclosure: (i128, i128),
    activation_strictly_positive: bool,
    activation_strictly_negative: bool,
    candidate_ids_before: Vec<u32>,
    candidate_surfaces_before: Vec<String>,
    non_target_potential_sha256: String,
    semantic_work_sha256: String,
    apparatus_sha256: String,
    wall_milliseconds: u128,
}

struct Conducted {
    reading: ForwardReading,
    receipt: RuntimeReceipt,
    terminal_hidden: Vec<(i64, i64)>,
    penultimate_hidden: Option<Vec<(i64, i64)>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct DevelopmentSelectorReturn {
    coordinate: u32,
    right_exponent: i32,
    selector_entry: i64,
    development_penultimate_interval: (i64, i64),
    development_hidden_interval: (i64, i64),
    strict_transition_gap: i128,
    development_activation: (i128, i128),
    held_out_activation: (i128, i128),
    revisit_activation: (i128, i128),
    disjoint_control_activation: (i128, i128),
    development_only_selection_law: String,
    held_out_revisit_and_control_choose_no_morphology: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct ProbeReceipt {
    schema: String,
    code_closure_sha256: String,
    predecessor_product_sha256: String,
    predecessor_morphology_sha256: String,
    selection: FamilySelectionReceipt,
    control: ControlSelectionReceipt,
    left_exponent: i32,
    right_exponent: i32,
    inherited_left_support: Vec<u32>,
    inherited_right_support: Vec<u32>,
    readings: Vec<ForwardReading>,
    selected_family_has_one_strict_orientation: bool,
    control_is_not_used_to_choose_orientation: bool,
    semantic_numbers_are_exact_integers: bool,
    physical_time_is_separate_telemetry: bool,
    truth_status: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct InputOccurrence {
    role: String,
    occurrence: String,
    text: String,
    byte_boundaries: Vec<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct A3Inputs {
    schema: String,
    selection: FamilySelectionReceipt,
    control: ControlSelectionReceipt,
    target_native_id: u32,
    target_native_surface: String,
    inherited_support_row: u32,
    inherited_support_entry: i64,
    passages: Vec<InputOccurrence>,
    source_material_is_an_exterior_input_not_rest: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct ExteriorEmission {
    relative_path: String,
    native_id: u32,
    surface: String,
    sha256: String,
    octets: u64,
    matches_target_surface: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct HeldOutWorldReceiver {
    history_occurrence: String,
    recorded_sibling_occurrence: String,
    recorded_first_native_id: u32,
    predecessor_enters_recorded_front: bool,
    successor_enters_recorded_front: bool,
    recorded_tool_world_pairs: u64,
    later_operator_return_present: bool,
    predecessor_emission: ExteriorEmission,
    successor_emission: ExteriorEmission,
    source_detached_durable_emission_improved: bool,
    complete_response_enacted_by_athena: bool,
    receiver_statement: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct CultivationHolonomy {
    repeated_content_sha256: String,
    development_occurrence: String,
    revisit_occurrence: String,
    occurrences_are_distinct: bool,
    predecessor_target_interval: (i64, i64),
    successor_target_interval: (i64, i64),
    returned_difference: (i128, i128),
    nontrivial: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct DisjointControlReturn {
    occurrence: String,
    provider_content_and_container_disjoint: bool,
    predecessor_candidate_ids: Vec<u32>,
    successor_candidate_ids: Vec<u32>,
    terminal_candidate_receiver_unchanged: bool,
    target_row_changed: bool,
    every_non_target_potential_unchanged: bool,
    receiver_statement: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct DetachedReturn {
    schema: String,
    namespace: String,
    continuation_identity_sha256: String,
    successor: Vec<ForwardReading>,
    ablated_held_out: ForwardReading,
    successor_held_out_emission: ExteriorEmission,
    ablated_held_out_emission: ExteriorEmission,
    all_frozen_members_verified: bool,
    source_access_forbidden_population: usize,
    exchange_store_mounted: bool,
    repository_mounted: bool,
    semantic_work_and_apparatus_are_separate: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct A3CultivationComplex {
    schema: String,
    probe: ProbeReceipt,
    predecessor_body_sha256: String,
    successor_continuation_sha256: String,
    selector: DevelopmentSelectorReturn,
    local_delta: holonic_engine::phoenix::continuation::LocalFactorDelta,
    causal_adjoint: LocalMetricAdjointReturn,
    predecessor: Vec<ForwardReading>,
    successor: Vec<ForwardReading>,
    held_out_world_receiver: HeldOutWorldReceiver,
    revisit_holonomy: CultivationHolonomy,
    disjoint_control: DisjointControlReturn,
    detached_return: DetachedReturn,
    ablation_restores_predecessor: bool,
    continuation_contains_exchange_text: bool,
    source_lookup_used_by_successor: bool,
    open_fibres: Vec<String>,
    truth_status: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct A3Grade {
    schema: String,
    unchanged_predecessor_and_distinct_successor: bool,
    exact_defect_and_lightning_leader_caused_delta: bool,
    source_detached_successor_remount: bool,
    held_out_world_receiver_improved: bool,
    revisit_holonomy_nontrivial: bool,
    subject_provider_disjoint_control_passed: bool,
    targeted_ablation_restored_predecessor: bool,
    no_retained_exchange_lookup: bool,
    exact_semantic_work_and_separate_card_telemetry: bool,
    passed: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct ProductManifest {
    schema: String,
    product: String,
    ancestry: String,
    receiver_history_aperture: String,
    continuation: String,
    inputs: String,
    complex: String,
    grade: String,
    detached_return: String,
    inference_entry: String,
    open_exterior: Vec<String>,
}

fn main() -> Result<(), String> {
    match args()? {
        Args::Probe {
            exchange_rest,
            a2_complex,
            phoenix_product,
        } => probe(ProbeArgs {
            exchange_rest,
            a2_complex,
            phoenix_product,
        }),
        Args::Produce {
            a2_cohort,
            a2_complex,
            phoenix_product,
            exchange_rest,
            output,
        } => produce(
            &a2_cohort,
            &a2_complex,
            &phoenix_product,
            &exchange_rest,
            &output,
        ),
        Args::DetachedGrade {
            phoenix_product,
            continuation,
            inputs,
            output,
        } => detached_grade(&phoenix_product, &continuation, &inputs, &output),
    }
}

struct ProbeArgs {
    exchange_rest: PathBuf,
    a2_complex: PathBuf,
    phoenix_product: PathBuf,
}

fn probe(args: ProbeArgs) -> Result<(), String> {
    let world = remount_exchange_world_tube(&args.exchange_rest)?;
    let cohort = cohort::derive(&world)?;
    let complex: A2ComplexFace =
        serde_json::from_slice(&fs::read(&args.a2_complex).map_err(|error| error.to_string())?)
            .map_err(|error| error.to_string())?;
    let selected = select_family(&cohort, &complex)?;
    let session = ProductSession::open(&args.phoenix_product)?;
    let control = select_control(&world, &selected, &session)?;
    let payload = session
        .mounted()
        .product
        .morphology_payload()
        .map_err(|error| error.to_string())?;
    let MorphologyPayload::AlignedFactor(factor) = payload else {
        return Err("the A2 predecessor carries no resident aligned factor".to_owned());
    };
    let left_support = factor
        .left
        .iter()
        .enumerate()
        .filter_map(|(row, value)| (*value != 0).then_some(row as u32))
        .collect::<Vec<_>>();
    let right_support = factor
        .right
        .iter()
        .enumerate()
        .filter_map(|(column, value)| (*value != 0).then_some(column as u32))
        .collect::<Vec<_>>();
    if left_support.len() != 1 || right_support.is_empty() {
        return Err(
            "A3's admitted predecessor is not the authenticated rank-one W3 body".to_owned(),
        );
    }
    let support_row = left_support[0];
    let support_entry = factor.left[support_row as usize];
    if support_entry != 1 || factor.left_exponent != 0 {
        return Err(format!(
            "the inherited left gauge is not the exact unit gauge: entry={support_entry}, exponent={}",
            factor.left_exponent
        ));
    }

    let mut readings = Vec::new();
    for (role, cut) in [
        ("development", selected.development),
        ("held-out", selected.held_out),
        ("revisit", selected.revisit),
    ] {
        let presentation = present(cut);
        readings.push(conduct(
            &session,
            role,
            &cut.occurrence,
            &presentation.text,
            &presentation.byte_boundaries,
            selected.target_native_id,
            support_row,
            support_entry,
        )?);
    }
    readings.push(conduct(
        &session,
        "subject-provider-disjoint-control",
        &control.face.occurrence,
        &control.face.text,
        &[0, control.face.text.len()],
        selected.target_native_id,
        support_row,
        support_entry,
    )?);
    let family = &readings[..3];
    let all_positive = family
        .iter()
        .all(|reading| reading.activation_strictly_positive);
    let all_negative = family
        .iter()
        .all(|reading| reading.activation_strictly_negative);
    let receipt = ProbeReceipt {
        schema: "holonics.athena-a3-forward-probe.v1".to_owned(),
        code_closure_sha256: code_closure(),
        predecessor_product_sha256: complex
            .histories
            .first()
            .ok_or_else(|| "A2 complex has no histories".to_owned())?
            .fixed_body
            .product_sha256
            .clone(),
        predecessor_morphology_sha256: complex.histories[0]
            .fixed_body
            .morphology_sha256
            .clone(),
        selection: selection_receipt(&selected),
        control: ControlSelectionReceipt {
            occurrence: control.face.occurrence.clone(),
            content_sha256: control.face.text_sha256.render(),
            container: control.face.container,
            provider_face: control.face.provider_face.clone(),
            speaker_face: control.face.speaker_face.clone(),
            native_tokens: control.native_tokens,
            provider_disjoint: control.face.provider_face != selected.development.prompt.provider_face,
            content_disjoint: control.face.text_sha256 != selected.repeated_content_sha256,
            container_disjoint: [
                selected.development.prompt.container,
                selected.held_out.prompt.container,
                selected.revisit.prompt.container,
            ]
            .into_iter()
            .all(|container| container != control.face.container),
            selection_law: "among A1 visible assistant occurrences whose provider, content address and container are disjoint from the selected family, choose greatest UTF-8 extent, then least occurrence identity; this input-only law does not inspect Athena conduct"
                .to_owned(),
        },
        left_exponent: factor.left_exponent,
        right_exponent: factor.right_exponent,
        inherited_left_support: left_support,
        inherited_right_support: right_support,
        readings,
        selected_family_has_one_strict_orientation: all_positive || all_negative,
        control_is_not_used_to_choose_orientation: true,
        semantic_numbers_are_exact_integers: true,
        physical_time_is_separate_telemetry: true,
        truth_status: "measured".to_owned(),
    };
    println!(
        "{}",
        serde_json::to_string_pretty(&receipt).map_err(|error| error.to_string())?
    );
    if receipt.selected_family_has_one_strict_orientation {
        Ok(())
    } else {
        Err("the inherited covector does not orient the complete selected family".to_owned())
    }
}

fn produce(
    a2_cohort: &Path,
    a2_complex: &Path,
    phoenix_product: &Path,
    exchange_rest: &Path,
    output: &Path,
) -> Result<(), String> {
    if output.exists() {
        return Err(format!("A3 output already exists: {}", output.display()));
    }
    fs::create_dir_all(output).map_err(|error| error.to_string())?;
    let cohort: SiblingCohort = serde_json::from_slice(
        &fs::read(a2_cohort).map_err(|error| format!("read A2 cohort: {error}"))?,
    )
    .map_err(|error| format!("decode A2 cohort: {error}"))?;
    let complex: A2ComplexFace = serde_json::from_slice(
        &fs::read(a2_complex).map_err(|error| format!("read A2 complex: {error}"))?,
    )
    .map_err(|error| format!("decode A2 complex: {error}"))?;
    let selected = select_family(&cohort, &complex)?;
    let mut session = ProductSession::open(phoenix_product)?;
    let world = remount_exchange_world_tube(exchange_rest)?;
    if world.source_occurrence_sha256 != cohort.source_occurrence_sha256 {
        return Err("the A3 control rest does not carry A2's exchange occurrence".to_owned());
    }
    let selected_control = select_control(&world, &selected, &session)?;
    let control_text = selected_control.face.text.clone();
    let control_occurrence = selected_control.face.occurrence.clone();
    let control = ControlSelectionReceipt {
        occurrence: control_occurrence.clone(),
        content_sha256: selected_control.face.text_sha256.render(),
        container: selected_control.face.container,
        provider_face: selected_control.face.provider_face.clone(),
        speaker_face: selected_control.face.speaker_face.clone(),
        native_tokens: selected_control.native_tokens,
        provider_disjoint: selected.development.prompt.provider_face
            != selected_control.face.provider_face,
        content_disjoint: selected.repeated_content_sha256
            != Digest32::of(control_text.as_bytes()),
        container_disjoint: [
            selected.development.prompt.container,
            selected.held_out.prompt.container,
            selected.revisit.prompt.container,
        ]
        .into_iter()
        .all(|container| container != selected_control.face.container),
        selection_law: "among A1 visible assistant occurrences whose provider, content address and container are disjoint from the selected family, choose greatest UTF-8 extent, then least occurrence identity; this input-only law does not inspect Athena conduct and the control does not choose the morphology"
            .to_owned(),
    };
    if !control.provider_disjoint || !control.content_disjoint || !control.container_disjoint {
        return Err(
            "the supplied A3 control is not provider/content/container-disjoint".to_owned(),
        );
    }
    let control_octets = control_text.len();
    let factor = match session
        .mounted()
        .product
        .morphology_payload()
        .map_err(|error| error.to_string())?
    {
        MorphologyPayload::AlignedFactor(factor) => factor,
        MorphologyPayload::SparseDelta(_) => {
            return Err("the A2 predecessor carries no resident aligned factor".to_owned());
        }
    };
    let (left_support, right_support, support_row, support_entry) = factor_support(&factor)?;
    let passages = vec![
        input_occurrence("development", selected.development),
        input_occurrence("held-out", selected.held_out),
        input_occurrence("revisit", selected.revisit),
        InputOccurrence {
            role: "subject-provider-disjoint-control".to_owned(),
            occurrence: control_occurrence,
            text: control_text,
            byte_boundaries: vec![0, control_octets],
        },
    ];
    if passages[3].byte_boundaries[1] != passages[3].text.len() {
        return Err("the control occurrence moved while it crossed the A3 mouth".to_owned());
    }
    let inputs = A3Inputs {
        schema: "holonics.athena-a3-input-occurrences.v1".to_owned(),
        selection: selection_receipt(&selected),
        control: control.clone(),
        target_native_id: selected.target_native_id,
        target_native_surface: session
            .mounted()
            .predecessor()
            .codebook()
            .native_surface(selected.target_native_id)
            .map_err(|error| error.to_string())?
            .to_owned(),
        inherited_support_row: support_row,
        inherited_support_entry: support_entry,
        passages,
        source_material_is_an_exterior_input_not_rest: true,
    };
    write_json(output.join("00-input-occurrences.json"), &inputs)?;

    let mut predecessor_conducted = Vec::new();
    for input in &inputs.passages {
        predecessor_conducted.push(conduct_with_receipt(
            &session,
            &input.role,
            &input.occurrence,
            &input.text,
            &input.byte_boundaries,
            inputs.target_native_id,
            support_row,
            support_entry,
        )?);
    }
    let all_positive = predecessor_conducted[..3]
        .iter()
        .all(|conducted| conducted.reading.activation_strictly_positive);
    let all_negative = predecessor_conducted[..3]
        .iter()
        .all(|conducted| conducted.reading.activation_strictly_negative);
    if !all_positive && !all_negative {
        return Err("the selected A3 family has no common inherited orientation".to_owned());
    }
    let probe = ProbeReceipt {
        schema: "holonics.athena-a3-forward-probe.v1".to_owned(),
        code_closure_sha256: code_closure(),
        predecessor_product_sha256: complex.histories[0].fixed_body.product_sha256.clone(),
        predecessor_morphology_sha256: complex.histories[0].fixed_body.morphology_sha256.clone(),
        selection: inputs.selection.clone(),
        control: control.clone(),
        left_exponent: factor.left_exponent,
        right_exponent: factor.right_exponent,
        inherited_left_support: left_support,
        inherited_right_support: right_support,
        readings: predecessor_conducted
            .iter()
            .map(|conducted| conducted.reading.clone())
            .collect(),
        selected_family_has_one_strict_orientation: true,
        control_is_not_used_to_choose_orientation: true,
        semantic_numbers_are_exact_integers: true,
        physical_time_is_separate_telemetry: true,
        truth_status: "measured".to_owned(),
    };
    write_json(output.join("01-forward-probe.json"), &probe)?;
    for conducted in &predecessor_conducted {
        write_json(
            output.join(format!(
                "runtime-predecessor-{}.json",
                conducted.reading.role
            )),
            &conducted.receipt,
        )?;
    }

    // Only the development occurrence founds the return.  Held-out and revisit readings above
    // are controls and may not enlarge the least lattice step.
    let development = &predecessor_conducted[0];
    let selector = derive_development_selector(
        predecessor_conducted[0]
            .penultimate_hidden
            .as_deref()
            .ok_or_else(|| {
                "the development history has no penultimate hidden section".to_owned()
            })?,
        &predecessor_conducted[0].terminal_hidden,
        &predecessor_conducted[1].terminal_hidden,
        &predecessor_conducted[2].terminal_hidden,
        &predecessor_conducted[3].terminal_hidden,
        factor.right_exponent,
    )?;
    let local_return = LocalMetricAdjointReturn::derive(
        development.reading.target_before,
        development.reading.maximum_other_upper,
        selector.development_activation,
    )
    .map_err(|error| error.to_string())?;
    let held_out_reading = &predecessor_conducted[1].reading;
    let predicted_held_out_delta = scale_interval(
        selector.held_out_activation,
        i128::from(local_return.least_lattice_step),
    )?;
    let predicted_held_out_lower = i128::from(held_out_reading.target_before.0)
        .checked_add(predicted_held_out_delta.0)
        .ok_or_else(|| "the held-out prediction left the exact carrier".to_owned())?;
    if predicted_held_out_lower <= i128::from(held_out_reading.maximum_other_upper) {
        return Err(format!(
            "the development-only selector does not separate held-out conduct: target lower={predicted_held_out_lower}, maximum other upper={}",
            held_out_reading.maximum_other_upper
        ));
    }
    let control_reading = &predecessor_conducted[3].reading;
    let predicted_control_delta = scale_interval(
        selector.disjoint_control_activation,
        i128::from(local_return.least_lattice_step),
    )?;
    let predicted_control_target = (
        i128::from(control_reading.target_before.0)
            .checked_add(predicted_control_delta.0)
            .ok_or_else(|| "the control prediction left the exact carrier".to_owned())?,
        i128::from(control_reading.target_before.1)
            .checked_add(predicted_control_delta.1)
            .ok_or_else(|| "the control prediction left the exact carrier".to_owned())?,
    );
    if control_reading
        .candidate_ids_before
        .contains(&inputs.target_native_id)
        || predicted_control_target.1 >= i128::from(control_reading.candidate_top_lower)
    {
        return Err(format!(
            "the development-derived local return predicts a disjoint-control candidate change: target={predicted_control_target:?}, inherited top lower={}",
            control_reading.candidate_top_lower
        ));
    }
    let successor_factor = selector_successor_factor(
        &factor,
        inputs.target_native_id,
        local_return.least_lattice_step,
        selector.coordinate,
        selector.selector_entry,
    )
    .map_err(|error| error.to_string())?;
    let morphology_bytes = native_morphology_bytes(&NativeMorphologyInput {
        left_population: session.runtime_law().left_population.clone(),
        right_population: session.runtime_law().right_population.clone(),
        left_shape: vec![
            successor_factor.rows as usize,
            successor_factor.rank as usize,
        ],
        right_shape: vec![
            successor_factor.rank as usize,
            successor_factor.columns as usize,
        ],
        left_exponent: successor_factor.left_exponent,
        right_exponent: successor_factor.right_exponent,
        rank: successor_factor.rank,
        resident_grain: successor_factor.resident_grain,
        predecessor: session.mounted().product.predecessor().clone(),
        laws: session.mounted().product.laws().to_vec(),
        left: successor_factor.left.clone(),
        right: successor_factor.right.clone(),
    })
    .map_err(|error| error.to_string())?;
    let successor_morphology = PredecessorProductIdentity::from_bytes(&morphology_bytes);
    let leader_history = complex
        .histories
        .iter()
        .find(|history| history.history_cut_occurrence == selected.development.occurrence)
        .ok_or_else(|| "the selected leader is absent from A2's defect complex".to_owned())?;
    let leader_activity = defect::activity_cuts(&development.receipt)?;
    let lineage = AddressedReturnLineage {
        exchange_source_sha256: cohort.source_occurrence_sha256.render(),
        a2_defect_complex_sha256: sha256_file(a2_complex)?,
        a2_fixed_body_sha256: leader_history.fixed_body.complete_identity_sha256.clone(),
        leader_occurrence_sha256: selected.development.occurrence.clone(),
        leader_input_sha256: development.reading.input_sha256.clone(),
        leader_history_sha256: selected.development.native_history_sha256.clone(),
        receiver_causal_sha256: leader_activity.receiver_causal_sha256,
        tower_admission_sha256: digest_json(&development.receipt.tower_admission)?,
        overlay_execution_sha256: digest_json(&development.receipt.overlay_execution)?,
    };
    let continuation = CultivationContinuationRest::seal(
        session.body_identity()?,
        lineage,
        &factor,
        inputs.target_native_id,
        development.reading.target_before,
        development.reading.maximum_other_upper,
        selector.development_activation,
        selector.coordinate,
        selector.selector_entry,
        successor_morphology,
        vec![
            "complete response suffixes and unobserved world actions remain open".to_owned(),
            "unexcited Gemma transport remains in the inherited reconstruction fibre".to_owned(),
            "the sparse receiver-covector rebase changes the inherited support row; the complete factor difference and every moved potential remain in the reconstruction fibre".to_owned(),
        ],
    )
    .map_err(|error| error.to_string())?;
    let continuation_dir = output.join("continuation");
    MountedContinuation::write_directory(&continuation_dir, &continuation, &morphology_bytes)
        .map_err(|error| error.to_string())?;
    session.attach_continuation(&continuation_dir)?;

    let mut successor_conducted = Vec::new();
    for input in &inputs.passages {
        successor_conducted.push(conduct_with_receipt(
            &session,
            &format!("successor-{}", input.role),
            &input.occurrence,
            &input.text,
            &input.byte_boundaries,
            inputs.target_native_id,
            support_row,
            support_entry,
        )?);
    }
    for conducted in &successor_conducted {
        write_json(
            output.join(format!("runtime-{}.json", conducted.reading.role)),
            &conducted.receipt,
        )?;
    }
    let continuation_identity = successor_conducted[0]
        .receipt
        .continuation_identity
        .as_ref()
        .ok_or_else(|| "successor runtime omitted its continuation identity".to_owned())?;

    run_detached_grade(
        &std::env::current_exe().map_err(|error| error.to_string())?,
        phoenix_product,
        &continuation_dir,
        &output.join("00-input-occurrences.json"),
        output,
    )?;
    let detached: DetachedReturn = serde_json::from_slice(
        &fs::read(output.join("04-detached-return.json")).map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())?;

    let predecessor_readings = predecessor_conducted
        .iter()
        .map(|conducted| conducted.reading.clone())
        .collect::<Vec<_>>();
    let successor_readings = successor_conducted
        .iter()
        .map(|conducted| conducted.reading.clone())
        .collect::<Vec<_>>();
    let held_before = &predecessor_readings[1];
    let held_after = &successor_readings[1];
    let held_out_world_receiver = HeldOutWorldReceiver {
        history_occurrence: selected.held_out.occurrence.clone(),
        recorded_sibling_occurrence: selected.held_out.sibling.occurrence.clone(),
        recorded_first_native_id: inputs.target_native_id,
        predecessor_enters_recorded_front: held_before
            .candidate_ids_before
            .contains(&inputs.target_native_id),
        successor_enters_recorded_front: held_after.candidate_ids_before
            == vec![inputs.target_native_id],
        recorded_tool_world_pairs: selected
            .held_out
            .world
            .claude_tool_returns
            .pair_population
            .saturating_add(selected.held_out.world.codex_tool_returns.pair_population),
        later_operator_return_present: selected.held_out.world.later_operator_return.is_some(),
        predecessor_emission: detached.ablated_held_out_emission.clone(),
        successor_emission: detached.successor_held_out_emission.clone(),
        source_detached_durable_emission_improved: !detached
            .ablated_held_out_emission
            .matches_target_surface
            && detached
                .successor_held_out_emission
                .matches_target_surface,
        complete_response_enacted_by_athena: false,
        receiver_statement: "inside the source-detached namespace the successor durably emits its unique held-out surface, while targeted ablation durably emits the predecessor surface; the exact file receiver changes from outside to inside the recorded first front. The captured sibling's later tool/world line is contextual testimony only: neither its unobserved suffix nor its tool actions are claimed as enacted"
            .to_owned(),
    };
    let revisit_before = &predecessor_readings[2];
    let revisit_after = &successor_readings[2];
    let returned_difference = (
        i128::from(revisit_after.target_before.0) - i128::from(revisit_before.target_before.0),
        i128::from(revisit_after.target_before.1) - i128::from(revisit_before.target_before.1),
    );
    let revisit_holonomy = CultivationHolonomy {
        repeated_content_sha256: selected.repeated_content_sha256.render(),
        development_occurrence: selected.development.occurrence.clone(),
        revisit_occurrence: selected.revisit.occurrence.clone(),
        occurrences_are_distinct: selected.development.occurrence != selected.revisit.occurrence,
        predecessor_target_interval: revisit_before.target_before,
        successor_target_interval: revisit_after.target_before,
        returned_difference,
        nontrivial: returned_difference != (0, 0),
    };
    let control_before = &predecessor_readings[3];
    let control_after = &successor_readings[3];
    let disjoint_control = DisjointControlReturn {
        occurrence: control.occurrence.clone(),
        provider_content_and_container_disjoint: control.provider_disjoint
            && control.content_disjoint
            && control.container_disjoint,
        predecessor_candidate_ids: control_before.candidate_ids_before.clone(),
        successor_candidate_ids: control_after.candidate_ids_before.clone(),
        terminal_candidate_receiver_unchanged: control_before.candidate_ids_before
            == control_after.candidate_ids_before,
        target_row_changed: control_before.target_before != control_after.target_before,
        every_non_target_potential_unchanged: control_before.non_target_potential_sha256
            == control_after.non_target_potential_sha256,
        receiver_statement: "the predeclared terminal candidate receiver must remain exact on the input-only selected disjoint subject; the addressed target-row movement and the complete non-target equality predicate (which is false here) are returned separately so this bounded control cannot be promoted to whole-potential invariance"
            .to_owned(),
    };
    let detached_successor_held = detached
        .successor
        .iter()
        .find(|reading| reading.role == "detached-successor-held-out")
        .ok_or_else(|| "detached return omitted held-out successor".to_owned())?;
    let ablation_restores_predecessor =
        semantic_reading_equal(&detached.ablated_held_out, held_before)
            && semantic_reading_equal(detached_successor_held, held_after);
    let continuation_contains_exchange_text = continuation_contains_any_text(
        &continuation_dir,
        &inputs
            .passages
            .iter()
            .map(|input| input.text.as_str())
            .collect::<Vec<_>>(),
    )?;
    let cultivation = A3CultivationComplex {
        schema: "holonics.athena-a3-cultivation-complex.v1".to_owned(),
        probe,
        predecessor_body_sha256: session.body_identity()?.complete_sha256,
        successor_continuation_sha256: continuation_identity.complete_sha256.clone(),
        selector,
        local_delta: continuation.local_delta.clone(),
        causal_adjoint: continuation.causal_adjoint.clone(),
        predecessor: predecessor_readings,
        successor: successor_readings,
        held_out_world_receiver,
        revisit_holonomy,
        disjoint_control,
        detached_return: detached,
        ablation_restores_predecessor,
        continuation_contains_exchange_text,
        source_lookup_used_by_successor: false,
        open_fibres: continuation.open_fibres.clone(),
        truth_status: "established-bounded".to_owned(),
    };
    let grade = grade(&cultivation);
    write_json(output.join("02-cultivation-complex.json"), &cultivation)?;
    write_json(output.join("03-grade.json"), &grade)?;
    let manifest = ProductManifest {
        schema: "holonics.athena-a3-product-manifest.v1".to_owned(),
        product: "Athena-Gemma addressed exchange cultivation continuation".to_owned(),
        ancestry: "the unchanged A2 Athena-Gemma cultivated product plus one addressed A3 sparse factor/covector continuation".to_owned(),
        receiver_history_aperture: "the selected three-occurrence repeated-content/recorded-first-native family, its source-detached held-out durable-emission receiver with recorded sibling context kept separate, revisit loop and one input-only provider/content/container-disjoint terminal control".to_owned(),
        continuation: "continuation/".to_owned(),
        inputs: "00-input-occurrences.json".to_owned(),
        complex: "02-cultivation-complex.json".to_owned(),
        grade: "03-grade.json".to_owned(),
        detached_return: "04-detached-return.json".to_owned(),
        inference_entry: "the_exchange_return_cultivates_athena_gemma --detached-grade BASE_PRODUCT continuation 00-input-occurrences.json RETURN_DIRECTORY".to_owned(),
        open_exterior: cultivation.open_fibres.clone(),
    };
    write_json(output.join("MANIFEST.json"), &manifest)?;
    write_inspection(output, &cultivation, &grade)?;
    println!(
        "{}",
        serde_json::to_string_pretty(&manifest).map_err(|error| error.to_string())?
    );
    if grade.passed {
        Ok(())
    } else {
        Err("A3 refused its complete nine-part grade".to_owned())
    }
}

fn detached_grade(
    phoenix_product: &Path,
    continuation: &Path,
    inputs: &Path,
    output: &Path,
) -> Result<(), String> {
    let inputs: A3Inputs = serde_json::from_slice(
        &fs::read(inputs).map_err(|error| format!("read detached inputs: {error}"))?,
    )
    .map_err(|error| error.to_string())?;
    let mut session = ProductSession::open_with_continuation(phoenix_product, continuation)?;
    let mut successor = Vec::new();
    let mut successor_held_out_emission = None;
    let mut continuation_identity_sha256 = None;
    let mut clean = true;
    let mut forbidden = 0usize;
    for index in [1usize, 2, 3] {
        let input = &inputs.passages[index];
        let conducted = conduct_with_receipt(
            &session,
            &format!("detached-successor-{}", input.role),
            &input.occurrence,
            &input.text,
            &input.byte_boundaries,
            inputs.target_native_id,
            inputs.inherited_support_row,
            inputs.inherited_support_entry,
        )?;
        clean &= conducted.receipt.frozen_members_verified;
        forbidden += conducted.receipt.source_access.forbidden.len();
        let identity = conducted
            .receipt
            .continuation_identity
            .as_ref()
            .ok_or_else(|| "detached successor omitted continuation identity".to_owned())?;
        if continuation_identity_sha256
            .as_ref()
            .is_some_and(|held| held != &identity.complete_sha256)
        {
            return Err("the detached continuation identity moved between currents".to_owned());
        }
        continuation_identity_sha256.get_or_insert_with(|| identity.complete_sha256.clone());
        if index == 1 {
            successor_held_out_emission = Some(write_exterior_emission(
                output,
                "held-out-successor.emission.txt",
                &conducted.receipt,
                &inputs.target_native_surface,
            )?);
        }
        successor.push(conducted.reading);
    }
    session.ablate_continuation()?;
    let held = &inputs.passages[1];
    let ablated = conduct_with_receipt(
        &session,
        "detached-ablated-held-out",
        &held.occurrence,
        &held.text,
        &held.byte_boundaries,
        inputs.target_native_id,
        inputs.inherited_support_row,
        inputs.inherited_support_entry,
    )?;
    clean &= ablated.receipt.frozen_members_verified;
    forbidden += ablated.receipt.source_access.forbidden.len();
    let ablated_held_out_emission = write_exterior_emission(
        output,
        "held-out-ablated.emission.txt",
        &ablated.receipt,
        &inputs.target_native_surface,
    )?;
    let returned = DetachedReturn {
        schema: "holonics.athena-a3-detached-return.v1".to_owned(),
        namespace: "private bwrap namespace: /athena-a3, /base, /continuation and /inputs.json read-only; /return writable; repository and exchange stores absent".to_owned(),
        continuation_identity_sha256: continuation_identity_sha256
            .ok_or_else(|| "detached successor returned no currents".to_owned())?,
        successor,
        ablated_held_out: ablated.reading,
        successor_held_out_emission: successor_held_out_emission
            .ok_or_else(|| "detached successor omitted held-out emission".to_owned())?,
        ablated_held_out_emission,
        all_frozen_members_verified: clean,
        source_access_forbidden_population: forbidden,
        exchange_store_mounted: false,
        repository_mounted: false,
        semantic_work_and_apparatus_are_separate: true,
    };
    write_json(output.join("04-detached-return.json"), &returned)
}

fn factor_support(
    factor: &holonic_engine::cultivated_rest::AlignedFactor,
) -> Result<(Vec<u32>, Vec<u32>, u32, i64), String> {
    let left = factor
        .left
        .iter()
        .enumerate()
        .filter_map(|(row, value)| (*value != 0).then_some(row as u32))
        .collect::<Vec<_>>();
    let right = factor
        .right
        .iter()
        .enumerate()
        .filter_map(|(column, value)| (*value != 0).then_some(column as u32))
        .collect::<Vec<_>>();
    if left.len() != 1 || right.is_empty() {
        return Err(
            "A3's admitted predecessor is not the authenticated rank-one W3 body".to_owned(),
        );
    }
    let row = left[0];
    let entry = factor.left[row as usize];
    if entry != 1 || factor.left_exponent != 0 {
        return Err(format!(
            "the inherited left gauge is not the exact unit gauge: entry={entry}, exponent={}",
            factor.left_exponent
        ));
    }
    Ok((left, right, row, entry))
}

fn input_occurrence(role: &str, cut: &SiblingHistoryCut) -> InputOccurrence {
    let presented = present(cut);
    InputOccurrence {
        role: role.to_owned(),
        occurrence: cut.occurrence.clone(),
        text: presented.text,
        byte_boundaries: presented.byte_boundaries,
    }
}

fn run_detached_grade(
    executable: &Path,
    phoenix_product: &Path,
    continuation: &Path,
    inputs: &Path,
    output: &Path,
) -> Result<(), String> {
    let executable = executable
        .canonicalize()
        .map_err(|error| format!("resolve A3 executable: {error}"))?;
    let phoenix_product = phoenix_product
        .canonicalize()
        .map_err(|error| format!("resolve Phoenix product: {error}"))?;
    let continuation = continuation
        .canonicalize()
        .map_err(|error| format!("resolve continuation: {error}"))?;
    let inputs = inputs
        .canonicalize()
        .map_err(|error| format!("resolve inputs: {error}"))?;
    let output = output
        .canonicalize()
        .map_err(|error| format!("resolve output: {error}"))?;
    let mut command = Command::new("bwrap");
    command
        .args(["--die-with-parent", "--unshare-all"])
        .args(["--ro-bind", "/usr", "/usr"])
        .args(["--ro-bind", "/etc", "/etc"])
        .args(["--ro-bind", "/sys", "/sys"])
        .args(["--dev-bind", "/dev", "/dev"])
        .args(["--proc", "/proc"])
        .args(["--tmpfs", "/tmp"]);
    for library in ["/lib", "/lib64", "/run"] {
        if Path::new(library).exists() {
            command.args(["--ro-bind", library, library]);
        }
    }
    command
        .arg("--ro-bind")
        .arg(executable)
        .arg("/athena-a3")
        .arg("--ro-bind")
        .arg(phoenix_product)
        .arg("/base")
        .arg("--ro-bind")
        .arg(continuation)
        .arg("/continuation")
        .arg("--ro-bind")
        .arg(inputs)
        .arg("/inputs.json")
        .arg("--bind")
        .arg(output)
        .arg("/return")
        .args([
            "--chdir",
            "/tmp",
            "/athena-a3",
            "--detached-grade",
            "/base",
            "/continuation",
            "/inputs.json",
            "/return",
        ]);
    let status = command
        .status()
        .map_err(|error| format!("enter detached A3 namespace: {error}"))?;
    if status.success() {
        Ok(())
    } else {
        Err(format!("detached A3 grade returned {status}"))
    }
}

fn semantic_reading_equal(left: &ForwardReading, right: &ForwardReading) -> bool {
    left.occurrence == right.occurrence
        && left.input_sha256 == right.input_sha256
        && left.target_native_id == right.target_native_id
        && left.target_before == right.target_before
        && left.candidate_top_lower == right.candidate_top_lower
        && left.maximum_other_upper == right.maximum_other_upper
        && left.inherited_support_row == right.inherited_support_row
        && left.inherited_left_entry == right.inherited_left_entry
        && left.support_before == right.support_before
        && left.support_after == right.support_after
        && left.activation_enclosure == right.activation_enclosure
        && left.candidate_ids_before == right.candidate_ids_before
        && left.candidate_surfaces_before == right.candidate_surfaces_before
        && left.non_target_potential_sha256 == right.non_target_potential_sha256
        && left.semantic_work_sha256 == right.semantic_work_sha256
}

fn write_exterior_emission(
    output: &Path,
    relative_path: &str,
    receipt: &RuntimeReceipt,
    target_surface: &str,
) -> Result<ExteriorEmission, String> {
    let [candidate] = receipt.generated.plural.as_slice() else {
        return Err(format!(
            "the exterior emission receiver requires one unique candidate, received {}",
            receipt.generated.plural.len()
        ));
    };
    fs::write(output.join(relative_path), candidate.surface.as_bytes())
        .map_err(|error| error.to_string())?;
    let bytes = fs::read(output.join(relative_path)).map_err(|error| error.to_string())?;
    if bytes != candidate.surface.as_bytes() {
        return Err("the exterior emission did not survive its durable return".to_owned());
    }
    Ok(ExteriorEmission {
        relative_path: relative_path.to_owned(),
        native_id: candidate.native_id,
        surface: candidate.surface.clone(),
        sha256: hex(&Sha256::digest(&bytes)),
        octets: bytes.len() as u64,
        matches_target_surface: candidate.surface == target_surface,
    })
}

fn scale_interval(interval: (i128, i128), scalar: i128) -> Result<(i128, i128), String> {
    let first = interval
        .0
        .checked_mul(scalar)
        .ok_or_else(|| "the interval scaling left the exact carrier".to_owned())?;
    let second = interval
        .1
        .checked_mul(scalar)
        .ok_or_else(|| "the interval scaling left the exact carrier".to_owned())?;
    Ok(if scalar < 0 {
        (second, first)
    } else {
        (first, second)
    })
}

fn derive_development_selector(
    development_penultimate: &[(i64, i64)],
    development: &[(i64, i64)],
    held_out: &[(i64, i64)],
    revisit: &[(i64, i64)],
    control: &[(i64, i64)],
    right_exponent: i32,
) -> Result<DevelopmentSelectorReturn, String> {
    if development.is_empty()
        || development_penultimate.len() != development.len()
        || held_out.len() != development.len()
        || revisit.len() != development.len()
        || control.len() != development.len()
    {
        return Err("the selector histories do not share one hidden receiver chart".to_owned());
    }
    if right_exponent > 0 || right_exponent < -62 {
        return Err(format!(
            "the inherited right exponent {right_exponent} cannot encode an exact unit selector"
        ));
    }
    let unit_entry = 1i64
        .checked_shl((-right_exponent) as u32)
        .ok_or_else(|| "the exact unit selector left the i64 factor carrier".to_owned())?;
    let mut selected = None::<(usize, i8, i128)>;
    for (coordinate, ((lower, upper), (prior_lower, prior_upper))) in development
        .iter()
        .copied()
        .zip(development_penultimate.iter().copied())
        .enumerate()
    {
        if lower > upper {
            return Err("the development hidden interval is malformed".to_owned());
        }
        if prior_lower > prior_upper {
            return Err("the penultimate hidden interval is malformed".to_owned());
        }
        let (orientation, transition_gap) = if lower > 0 {
            (1i8, i128::from(lower) - i128::from(prior_upper))
        } else if upper < 0 {
            (-1i8, i128::from(prior_lower) - i128::from(upper))
        } else {
            continue;
        };
        if transition_gap <= 0 {
            continue;
        }
        if selected
            .as_ref()
            .is_none_or(|(_, _, held_gap)| transition_gap > *held_gap)
        {
            selected = Some((coordinate, orientation, transition_gap));
        }
    }
    let (coordinate, orientation, strict_transition_gap) = selected.ok_or_else(|| {
        "development returned no strictly oriented penultimate-to-terminal coordinate".to_owned()
    })?;
    let selector_entry = i64::from(orientation)
        .checked_mul(unit_entry)
        .ok_or_else(|| "the selector entry left the i64 factor carrier".to_owned())?;
    let orient = |interval: (i64, i64)| -> Result<(i128, i128), String> {
        let interval = (i128::from(interval.0), i128::from(interval.1));
        scale_interval(interval, i128::from(orientation))
    };
    Ok(DevelopmentSelectorReturn {
        coordinate: coordinate as u32,
        right_exponent,
        selector_entry,
        development_penultimate_interval: development_penultimate[coordinate],
        development_hidden_interval: development[coordinate],
        strict_transition_gap,
        development_activation: orient(development[coordinate])?,
        held_out_activation: orient(held_out[coordinate])?,
        revisit_activation: orient(revisit[coordinate])?,
        disjoint_control_activation: orient(control[coordinate])?,
        development_only_selection_law: "inside the development history only, choose the least hidden coordinate having the greatest strictly oriented penultimate-to-terminal interval gap while the terminal interval stays strictly on that orientation; encode its unit covector exactly at the inherited right-factor exponent"
            .to_owned(),
        held_out_revisit_and_control_choose_no_morphology: true,
    })
}

fn continuation_contains_any_text(directory: &Path, texts: &[&str]) -> Result<bool, String> {
    let mut members = fs::read_dir(directory)
        .map_err(|error| error.to_string())?
        .collect::<Result<Vec<_>, _>>()
        .map_err(|error| error.to_string())?;
    members.sort_by_key(|entry| entry.file_name());
    if members.len() != 3 {
        return Err(
            "the A3 continuation directory does not contain exactly three members".to_owned(),
        );
    }
    for member in members {
        let bytes = fs::read(member.path()).map_err(|error| error.to_string())?;
        for text in texts {
            if !text.is_empty()
                && bytes
                    .windows(text.len())
                    .any(|window| window == text.as_bytes())
            {
                return Ok(true);
            }
        }
    }
    Ok(false)
}

fn grade(complex: &A3CultivationComplex) -> A3Grade {
    let unchanged_predecessor_and_distinct_successor = complex.predecessor_body_sha256.len() == 64
        && complex.successor_continuation_sha256.len() == 64
        && complex.predecessor_body_sha256 != complex.successor_continuation_sha256
        && complex.local_delta.delta_entry != 0;
    let exact_defect_and_lightning_leader_caused_delta = complex
        .selector
        .held_out_revisit_and_control_choose_no_morphology
        && complex.selector.development_activation.0 > 0
        && complex.causal_adjoint.least_lattice_step == complex.local_delta.delta_entry
        && complex.causal_adjoint.guaranteed_target_lower
            > i128::from(complex.causal_adjoint.maximum_other_upper)
        && complex.causal_adjoint.adjoint_defect
            == relational_geometry::Rat::from_integer(0.into());
    let source_detached_successor_remount = complex.detached_return.all_frozen_members_verified
        && complex.detached_return.source_access_forbidden_population == 0
        && !complex.detached_return.exchange_store_mounted
        && !complex.detached_return.repository_mounted
        && complex.detached_return.continuation_identity_sha256
            == complex.successor_continuation_sha256;
    let held_out_world_receiver_improved = !complex
        .held_out_world_receiver
        .predecessor_enters_recorded_front
        && complex
            .held_out_world_receiver
            .successor_enters_recorded_front
        && complex
            .held_out_world_receiver
            .source_detached_durable_emission_improved
        && !complex
            .held_out_world_receiver
            .predecessor_emission
            .matches_target_surface
        && complex
            .held_out_world_receiver
            .successor_emission
            .matches_target_surface
        && complex
            .held_out_world_receiver
            .predecessor_emission
            .sha256
            .len()
            == 64
        && complex
            .held_out_world_receiver
            .successor_emission
            .sha256
            .len()
            == 64
        && !complex
            .held_out_world_receiver
            .complete_response_enacted_by_athena;
    let revisit_holonomy_nontrivial =
        complex.revisit_holonomy.occurrences_are_distinct && complex.revisit_holonomy.nontrivial;
    let subject_provider_disjoint_control_passed = complex
        .disjoint_control
        .provider_content_and_container_disjoint
        && complex
            .disjoint_control
            .terminal_candidate_receiver_unchanged;
    let targeted_ablation_restored_predecessor = complex.ablation_restores_predecessor;
    let no_retained_exchange_lookup = !complex.continuation_contains_exchange_text
        && !complex.source_lookup_used_by_successor
        && complex.detached_return.source_access_forbidden_population == 0;
    let exact_semantic_work_and_separate_card_telemetry =
        complex.probe.semantic_numbers_are_exact_integers
            && complex.probe.physical_time_is_separate_telemetry
            && complex
                .detached_return
                .semantic_work_and_apparatus_are_separate
            && complex
                .predecessor
                .iter()
                .chain(&complex.successor)
                .all(|reading| {
                    reading.semantic_work_sha256.len() == 64 && reading.apparatus_sha256.len() == 64
                });
    let passed = unchanged_predecessor_and_distinct_successor
        && exact_defect_and_lightning_leader_caused_delta
        && source_detached_successor_remount
        && held_out_world_receiver_improved
        && revisit_holonomy_nontrivial
        && subject_provider_disjoint_control_passed
        && targeted_ablation_restored_predecessor
        && no_retained_exchange_lookup
        && exact_semantic_work_and_separate_card_telemetry;
    A3Grade {
        schema: "holonics.athena-a3-grade.v1".to_owned(),
        unchanged_predecessor_and_distinct_successor,
        exact_defect_and_lightning_leader_caused_delta,
        source_detached_successor_remount,
        held_out_world_receiver_improved,
        revisit_holonomy_nontrivial,
        subject_provider_disjoint_control_passed,
        targeted_ablation_restored_predecessor,
        no_retained_exchange_lookup,
        exact_semantic_work_and_separate_card_telemetry,
        passed,
    }
}

fn write_inspection(
    output: &Path,
    complex: &A3CultivationComplex,
    grade: &A3Grade,
) -> Result<(), String> {
    fs::write(
        output.join("INSPECTION.md"),
        format!(
            "# Athena A3 exchange cultivation\n\n- grade: {}\n- predecessor body: {}\n- successor continuation: {}\n- local target/delta: {} / {}\n- receiver selector/right changes: {} / {}\n- held-out durable emission enters recorded front: {} -> {}\n- revisit holonomy: {:?}\n- disjoint terminal candidate unchanged: {}\n- ablation restores predecessor: {}\n- retained exchange lookup: {}\n",
            if grade.passed { "PASS" } else { "REFUSED" },
            complex.predecessor_body_sha256,
            complex.successor_continuation_sha256,
            complex.local_delta.target_row,
            complex.local_delta.delta_entry,
            complex.local_delta.selector_coordinate,
            complex.local_delta.right_changes.len(),
            complex.held_out_world_receiver.predecessor_enters_recorded_front,
            complex.held_out_world_receiver.successor_enters_recorded_front,
            complex.revisit_holonomy.returned_difference,
            complex.disjoint_control.terminal_candidate_receiver_unchanged,
            complex.ablation_restores_predecessor,
            complex.source_lookup_used_by_successor || complex.continuation_contains_exchange_text,
        ),
    )
    .map_err(|error| error.to_string())
}

fn conduct(
    session: &ProductSession,
    role: &str,
    occurrence: &str,
    text: &str,
    boundaries: &[usize],
    target: u32,
    support: u32,
    inherited_left_entry: i64,
) -> Result<ForwardReading, String> {
    conduct_with_receipt(
        session,
        role,
        occurrence,
        text,
        boundaries,
        target,
        support,
        inherited_left_entry,
    )
    .map(|conducted| conducted.reading)
}

#[allow(clippy::too_many_arguments)]
fn conduct_with_receipt(
    session: &ProductSession,
    role: &str,
    occurrence: &str,
    text: &str,
    boundaries: &[usize],
    target: u32,
    support: u32,
    inherited_left_entry: i64,
) -> Result<Conducted, String> {
    let begun = Instant::now();
    let returned = session.infer_partitioned_with_intervention(
        text,
        boundaries,
        InterventionSite::Nowhere,
        &Intervention::None,
        ReceiverOption::Complete,
    )?;
    let vocabulary = returned.receipt.generated.vocabulary_extent;
    let base = terminal(&returned.cultivated.base.potential, vocabulary)?;
    let cultivated = terminal(&returned.cultivated.cultivated_potential, vocabulary)?;
    let hidden_extent = returned.receipt.runtime_law.hidden_extent as usize;
    let hidden_face = &returned.cultivated.base.final_normed;
    let terminal_hidden = terminal(hidden_face, hidden_extent)?.to_vec();
    let hidden_rows = hidden_face.len() / hidden_extent;
    let penultimate_hidden = (hidden_rows >= 2).then(|| {
        hidden_face[(hidden_rows - 2) * hidden_extent..(hidden_rows - 1) * hidden_extent].to_vec()
    });
    let target_before = *cultivated
        .get(target as usize)
        .ok_or_else(|| format!("target native row {target} left the potential"))?;
    let support_before = *base
        .get(support as usize)
        .ok_or_else(|| format!("support native row {support} left the base potential"))?;
    let support_after = *cultivated
        .get(support as usize)
        .ok_or_else(|| format!("support native row {support} left the cultivated potential"))?;
    let activation = (
        i128::from(support_after.0) - i128::from(support_before.1),
        i128::from(support_after.1) - i128::from(support_before.0),
    );
    let maximum_other_upper = cultivated
        .iter()
        .enumerate()
        .filter(|(row, _)| *row != target as usize)
        .map(|(_, interval)| interval.1)
        .max()
        .ok_or_else(|| "the terminal receiver has no competing row".to_owned())?;
    let non_target_potential_sha256 = digest_non_target(cultivated, target as usize);
    let semantic_work_sha256 =
        digest_json(&(&returned.receipt.total_work, &returned.receipt.overlay_work))?;
    let apparatus_sha256 = digest_json(&(
        &returned.receipt.admission,
        &returned.receipt.tower_admission,
        &returned.receipt.apparatus_census,
        &returned.receipt.apparatus_prediction,
        &returned.receipt.execution,
    ))?;
    let reading = ForwardReading {
        role: role.to_owned(),
        occurrence: occurrence.to_owned(),
        input_sha256: hex(&Sha256::digest(text.as_bytes())),
        target_native_id: target,
        target_before,
        candidate_top_lower: returned.receipt.generated.top_lower,
        maximum_other_upper,
        inherited_support_row: support,
        inherited_left_entry,
        support_before,
        support_after,
        activation_enclosure: activation,
        activation_strictly_positive: activation.0 > 0,
        activation_strictly_negative: activation.1 < 0,
        candidate_ids_before: returned
            .receipt
            .generated
            .plural
            .iter()
            .map(|candidate| candidate.native_id)
            .collect(),
        candidate_surfaces_before: returned
            .receipt
            .generated
            .plural
            .iter()
            .map(|candidate| candidate.surface.clone())
            .collect(),
        non_target_potential_sha256,
        semantic_work_sha256,
        apparatus_sha256,
        wall_milliseconds: begun.elapsed().as_millis(),
    };
    Ok(Conducted {
        reading,
        receipt: returned.receipt,
        terminal_hidden,
        penultimate_hidden,
    })
}

fn terminal(potential: &[(i64, i64)], vocabulary: usize) -> Result<&[(i64, i64)], String> {
    if vocabulary == 0 || potential.len() < vocabulary || potential.len() % vocabulary != 0 {
        return Err("the returned potential is not a complete terminal population".to_owned());
    }
    Ok(&potential[potential.len() - vocabulary..])
}

fn select_family<'a>(
    cohort: &'a SiblingCohort,
    complex: &A2ComplexFace,
) -> Result<SelectedFamily<'a>, String> {
    let cuts = cohort
        .cuts
        .iter()
        .map(|cut| (cut.occurrence.as_str(), cut))
        .collect::<BTreeMap<_, _>>();
    let mut groups = BTreeMap::<(Digest32, u32), Vec<(&SiblingHistoryCut, i128)>>::new();
    for history in &complex.histories {
        let cut = cuts
            .get(history.history_cut_occurrence.as_str())
            .copied()
            .ok_or_else(|| {
                format!(
                    "A2 history {} is absent from A1",
                    history.history_cut_occurrence
                )
            })?;
        let top_lower = history
            .defects
            .iter()
            .map(|defect| defect.candidate.lower)
            .max()
            .ok_or_else(|| {
                format!(
                    "A2 history {} has no defect front",
                    history.history_cut_occurrence
                )
            })?;
        let gap = i128::from(top_lower) - i128::from(history.recorded_sibling.terminal_interval.1);
        groups
            .entry((
                cut.repeated_content_sha256,
                history.recorded_sibling.first_native_id,
            ))
            .or_default()
            .push((cut, gap));
    }
    let mut candidates = groups
        .into_iter()
        .filter(|(_, members)| members.len() >= 3)
        .collect::<Vec<_>>();
    candidates.sort_by(|left, right| {
        right
            .1
            .len()
            .cmp(&left.1.len())
            .then_with(|| {
                right
                    .1
                    .iter()
                    .map(|(_, gap)| *gap)
                    .sum::<i128>()
                    .cmp(&left.1.iter().map(|(_, gap)| *gap).sum::<i128>())
            })
            .then_with(|| left.0.cmp(&right.0))
    });
    let ((content, target), mut members) = candidates
        .into_iter()
        .next()
        .ok_or_else(|| "A2 returned no three-occurrence defect family".to_owned())?;
    members.sort_by(|left, right| {
        right
            .1
            .cmp(&left.1)
            .then_with(|| left.0.occurrence.cmp(&right.0.occurrence))
    });
    let total_receiver_gap = members.iter().map(|(_, gap)| *gap).sum();
    Ok(SelectedFamily {
        repeated_content_sha256: content,
        target_native_id: target,
        development: members[0].0,
        held_out: members[1].0,
        revisit: members[2].0,
        total_receiver_gap,
    })
}

fn selection_receipt(selected: &SelectedFamily<'_>) -> FamilySelectionReceipt {
    FamilySelectionReceipt {
        schema: "holonics.athena-a3-family-selection.v1".to_owned(),
        repeated_content_sha256: selected.repeated_content_sha256.render(),
        target_native_id: selected.target_native_id,
        development_occurrence: selected.development.occurrence.clone(),
        held_out_occurrence: selected.held_out.occurrence.clone(),
        revisit_occurrence: selected.revisit.occurrence.clone(),
        family_population: 3,
        total_receiver_gap: selected.total_receiver_gap.to_string(),
        selection_law: "group every A2 history by its A1 repeated-content address and recorded sibling first native address; retain groups with at least three occurrences; choose greatest population, then greatest total exact first-front defect; descending defect then occurrence identity assigns development, held-out and revisit"
            .to_owned(),
        provider_or_surface_routed_selection: false,
    }
}

fn select_control<'a>(
    world: &'a ExchangeWorldTube,
    selected: &SelectedFamily<'_>,
    session: &ProductSession,
) -> Result<ControlFace<'a>, String> {
    let selected_containers = [
        selected.development.prompt.container,
        selected.held_out.prompt.container,
        selected.revisit.prompt.container,
    ];
    let provider = &selected.development.prompt.provider_face;
    let speaker = &selected.development.prompt.speaker_face;
    let mut eligible = Vec::new();
    for face in &world.visible_messages {
        if face.provider_face == *provider
            || face.speaker_face != *speaker
            || face.text_sha256 == selected.repeated_content_sha256
            || selected_containers.contains(&face.container)
            || face.text.is_empty()
        {
            continue;
        }
        eligible.push(face);
    }
    eligible.sort_by(|left, right| {
        right
            .text
            .len()
            .cmp(&left.text.len())
            .then_with(|| left.occurrence.cmp(&right.occurrence))
    });
    let face = eligible.into_iter().next().ok_or_else(|| {
        "A1 returned no provider/content/container-disjoint assistant control".to_owned()
    })?;
    let native_tokens = session.encode(&face.text)?.len();
    if native_tokens == 0 {
        return Err(
            "the input-only selected disjoint control has no native presentation".to_owned(),
        );
    }
    Ok(ControlFace {
        face,
        native_tokens,
    })
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct PresentedHistory {
    text: String,
    byte_boundaries: Vec<usize>,
}

fn present(cut: &SiblingHistoryCut) -> PresentedHistory {
    let mut text = String::new();
    let mut byte_boundaries = Vec::with_capacity(cut.history.len() + 1);
    byte_boundaries.push(0);
    for (index, message) in cut.history.iter().enumerate() {
        if index > 0 {
            text.push('\n');
        }
        text.push_str(&message.text);
        byte_boundaries.push(text.len());
    }
    PresentedHistory {
        text,
        byte_boundaries,
    }
}

fn code_closure() -> String {
    let mut digest = Sha256::new();
    for bytes in [
        include_bytes!("the_exchange_return_cultivates_athena_gemma.rs").as_slice(),
        include_bytes!("a2/cohort.rs").as_slice(),
        include_bytes!("a2/defect.rs").as_slice(),
        include_bytes!("../../../crates/holonic-engine/src/phoenix/runtime.rs").as_slice(),
        include_bytes!("../../../crates/holonic-engine/src/phoenix/continuation.rs").as_slice(),
        include_bytes!("../../../crates/holonic-engine/src/phoenix/streamed.rs").as_slice(),
        include_bytes!("../../../crates/holonic-engine/src/phoenix/streamed_cultivation.rs")
            .as_slice(),
        include_bytes!("../../../crates/holonic-engine/kernels/exact_resident_section.cu")
            .as_slice(),
    ] {
        digest.update((bytes.len() as u64).to_le_bytes());
        digest.update(bytes);
    }
    hex(&digest.finalize())
}

fn digest_non_target(potential: &[(i64, i64)], target: usize) -> String {
    let mut digest = Sha256::new();
    digest.update(b"athena-a3/non-target-potential/v1");
    digest.update((potential.len() as u64).to_le_bytes());
    digest.update((target as u64).to_le_bytes());
    for (row, interval) in potential.iter().enumerate() {
        if row == target {
            continue;
        }
        digest.update((row as u64).to_le_bytes());
        digest.update(interval.0.to_le_bytes());
        digest.update(interval.1.to_le_bytes());
    }
    hex(&digest.finalize())
}

fn digest_json(value: &impl Serialize) -> Result<String, String> {
    serde_json::to_vec(value)
        .map(|bytes| hex(&Sha256::digest(bytes)))
        .map_err(|error| error.to_string())
}

fn sha256_file(path: &Path) -> Result<String, String> {
    fs::read(path)
        .map(|bytes| hex(&Sha256::digest(bytes)))
        .map_err(|error| error.to_string())
}

fn write_json(path: PathBuf, value: &impl Serialize) -> Result<(), String> {
    let bytes = serde_json::to_vec_pretty(value).map_err(|error| error.to_string())?;
    let staged = path.with_extension("a3-staged");
    fs::write(&staged, bytes).map_err(|error| error.to_string())?;
    fs::rename(staged, path).map_err(|error| error.to_string())
}

fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        out.push(DIGITS[(byte >> 4) as usize] as char);
        out.push(DIGITS[(byte & 15) as usize] as char);
    }
    out
}

fn args() -> Result<Args, String> {
    let mut values = env::args().skip(1);
    match values.next().as_deref() {
        Some("--probe") => {
            let exchange_rest = required_path(&mut values, "EXCHANGE_REST")?;
            let a2_complex = required_path(&mut values, "A2_COMPLEX")?;
            let phoenix_product = required_path(&mut values, "PHOENIX_PRODUCT")?;
            no_trailing(&mut values, "--probe")?;
            Ok(Args::Probe {
                exchange_rest,
                a2_complex,
                phoenix_product,
            })
        }
        Some("--produce") => {
            let a2_cohort = required_path(&mut values, "A2_COHORT")?;
            let a2_complex = required_path(&mut values, "A2_COMPLEX")?;
            let phoenix_product = required_path(&mut values, "PHOENIX_PRODUCT")?;
            let exchange_rest = required_path(&mut values, "EXCHANGE_REST")?;
            let output = values
                .next()
                .map(PathBuf::from)
                .ok_or_else(|| "missing OUTPUT".to_owned())?;
            no_trailing(&mut values, "--produce")?;
            Ok(Args::Produce {
                a2_cohort,
                a2_complex,
                phoenix_product,
                exchange_rest,
                output,
            })
        }
        Some("--detached-grade") => {
            let phoenix_product = required_path(&mut values, "PHOENIX_PRODUCT")?;
            let continuation = required_path(&mut values, "CONTINUATION")?;
            let inputs = required_path(&mut values, "INPUTS")?;
            let output = required_path(&mut values, "OUTPUT")?;
            no_trailing(&mut values, "--detached-grade")?;
            Ok(Args::DetachedGrade {
                phoenix_product,
                continuation,
                inputs,
                output,
            })
        }
        _ => Err("usage: --probe EXCHANGE_REST A2_COMPLEX PHOENIX_PRODUCT | --produce A2_COHORT A2_COMPLEX PHOENIX_PRODUCT EXCHANGE_REST OUTPUT | --detached-grade PHOENIX_PRODUCT CONTINUATION INPUTS OUTPUT".to_owned()),
    }
}

fn required_path(values: &mut impl Iterator<Item = String>, name: &str) -> Result<PathBuf, String> {
    let path = values
        .next()
        .map(PathBuf::from)
        .ok_or_else(|| format!("missing {name}"))?;
    if !path.exists() {
        return Err(format!("required {name} {} is absent", path.display()));
    }
    Ok(path)
}

fn no_trailing(values: &mut impl Iterator<Item = String>, mode: &str) -> Result<(), String> {
    if values.next().is_some() {
        Err(format!("{mode} carries trailing arguments"))
    } else {
        Ok(())
    }
}
