use std::collections::BTreeMap;
use std::fmt::Debug;
use std::io::Write;
use std::path::{Path, PathBuf};

use body::incidence::IncidenceHand;
use body::manifold::FeltDeed;
use body::num::Cog;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use soma_abi::active::{ActionCurrent, RelationAtom};
use soma_membrane::{
    ContemporaryEvent, ContemporaryRadiation, CurrentBoundaryPort, CurrentEvent, CurrentGeometry,
    CurrentLineage, InterfaceCapability, LiveBoundaryTransition, LiveConstituent,
    LiveCurrentMachine, LiveMemory, RegionalRelationArc, RegionalRelationCell,
    SparseStandingSurface,
};

const SOURCE_COMPONENTS: [&str; 2] = ["informant", "current_inscription"];
const PRIMING_VALUES: [i64; 8] = [13, 29, 17, 31, -63_245, 47, 71, -89];
const FACES_PER_RELATION: usize = 3;

#[derive(Deserialize)]
struct Manifest {
    observation_id: String,
    architecture: Architecture,
    fixture: Fixture,
    model: Model,
}

#[derive(Deserialize)]
struct Architecture {
    attention_heads: usize,
    selected_layer: usize,
}

#[derive(Deserialize)]
struct Fixture {
    relation_id: String,
    source_current_id: String,
    target_current_id: String,
}

#[derive(Deserialize)]
struct Model {
    repository: String,
    revision: String,
}

#[derive(Clone, Deserialize)]
struct SpanChart {
    current_id: String,
    rendered_sha256: String,
    token_count: usize,
    roles: Vec<RoleSpan>,
    tokens: Vec<TokenSpan>,
}

#[derive(Clone, Deserialize)]
struct RoleSpan {
    role: String,
    byte_start: usize,
    byte_end: usize,
}

#[derive(Clone, Deserialize)]
struct TokenSpan {
    position: usize,
    token_id: u64,
    rendered_text: String,
    byte_start: usize,
    byte_end: usize,
}

#[derive(Clone, Deserialize)]
struct Leader {
    head: usize,
    receiver_position: usize,
    source_position: usize,
    source_token: TokenSpan,
    attention_ratio: String,
    unscaled_query_key_pairing: Pairing,
}

#[derive(Clone, Deserialize)]
struct Pairing {
    ratio: String,
}

#[derive(Clone)]
struct SelectedRelation {
    head: usize,
    component: String,
    token_id: u64,
    token_text: String,
    local_byte_start: usize,
    local_byte_end: usize,
    source_position: usize,
    target_position: usize,
    actual_target_position: usize,
    actual_target_token_id: u64,
    actual_target_text: String,
    receiver_position: usize,
    attention_ratio: String,
    unscaled_pairing: String,
}

#[derive(Clone, Copy)]
struct ActiveFaces {
    token_address: i64,
    component_local_address: i64,
    chronology_address: i64,
}

#[derive(Serialize)]
struct ArtifactRead {
    path: String,
    sha256: String,
}

#[derive(Serialize)]
struct TeacherRead {
    observation_id: String,
    model_repository: String,
    model_revision: String,
    layer: usize,
    attention_heads: usize,
    source_current_id: String,
    target_current_id: String,
    source_rendered_sha256: String,
    target_rendered_sha256: String,
    source_token_count: usize,
    target_token_count: usize,
    selection_law: &'static str,
    selected_relations: Vec<RelationRead>,
    artifacts: Vec<ArtifactRead>,
}

#[derive(Serialize)]
struct RelationRead {
    head: usize,
    component: String,
    source_token_id: u64,
    source_token_text: String,
    component_local_byte_interval: [usize; 2],
    source_position: usize,
    tokenizer_transported_target_position: usize,
    actual_target_leader_position: usize,
    actual_target_leader_token_id: u64,
    actual_target_leader_text: String,
    receiver_position: usize,
    source_attention_ratio: String,
    source_unscaled_query_key_pairing: String,
    seed_active_faces: ActiveFaceRead,
    later_active_faces: ActiveFaceRead,
}

#[derive(Serialize)]
struct ActiveFaceRead {
    token_address: i64,
    component_local_address: i64,
    chronology_address: i64,
    exact_encoding: &'static str,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
struct MachineRead {
    standing_sha256: [u8; 32],
    standing_rank: u64,
    standing_cells: usize,
    standing_constituents: usize,
    constituent_cells: usize,
    constituent_incidences: usize,
    constituent_pins: usize,
    constituent_paths: usize,
    constituent_transport_terms: usize,
    live_lineages: usize,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize)]
struct ContactRead {
    open: usize,
    ride: usize,
    found_this: usize,
    found_that: usize,
    dark: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct ConstituentRead {
    grain: u32,
    axes: u32,
    cells: usize,
    incidences: usize,
    pins: usize,
    boundaries: usize,
    paths: usize,
    folded_paths: usize,
    transport_terms: usize,
    exposed_pins: usize,
    open_boundaries: usize,
    ride_boundaries: usize,
    found_boundaries: usize,
    contacts: ContactRead,
}

#[derive(Serialize)]
struct SeedRead {
    canonical_capability_namespace: String,
    teacher_current_radiation_sha256: String,
    control_current_radiation_sha256: String,
    ordinary_current_radiation_exact: bool,
    teacher_regional: Vec<ConstituentRead>,
    teacher_after: MachineRead,
    control_after: MachineRead,
}

#[derive(Serialize)]
struct LaterBranchRead {
    role: &'static str,
    capability_namespace: String,
    current_radiation_sha256: String,
    regional_radiation_sha256: String,
    regional: Vec<ConstituentRead>,
    after: MachineRead,
}

#[derive(Serialize)]
struct ComparisonRead {
    source_and_target_text_are_nonidentical: bool,
    selected_token_addresses_recur: bool,
    selected_component_addresses_recur: bool,
    selected_chronology_addresses_change: bool,
    target_transformer_repoints_every_selected_relation: bool,
    rest_remount_exact_before_later_event: bool,
    same_later_currents_in_all_branches: bool,
    experienced_regions_advanced_one_grain: bool,
    unseeded_regions_remained_at_source_grain: bool,
    foreign_identity_did_not_rebase_prior_standing: bool,
    experienced_consumed_lower_constituents: bool,
    foreign_identity_preserved_prior_and_new_constituents: bool,
    later_model_interior_was_not_machine_input: bool,
}

#[derive(Serialize)]
struct Report {
    schema: &'static str,
    status: &'static str,
    question: &'static str,
    theory_to_structure: &'static str,
    stop_boundary: &'static str,
    teacher: TeacherRead,
    seed: SeedRead,
    later_experienced: LaterBranchRead,
    later_unseeded: LaterBranchRead,
    later_foreign_identity: LaterBranchRead,
    comparison: ComparisonRead,
    conclusion: &'static str,
}

struct BranchOutcome {
    radiation: ContemporaryRadiation,
    read: LaterBranchRead,
}

fn main() {
    if let Err(error) = run() {
        eprintln!("eros transformer-seeded ecology: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let artifacts = PathBuf::from(arguments.next().ok_or_else(|| {
        "usage: eros_transformer_seeded_ecology <block-atlas-result-dir> <new-report.json>"
            .to_owned()
    })?);
    let output = PathBuf::from(arguments.next().ok_or_else(|| {
        "usage: eros_transformer_seeded_ecology <block-atlas-result-dir> <new-report.json>"
            .to_owned()
    })?);
    if arguments.next().is_some() {
        return Err(
            "usage: eros_transformer_seeded_ecology <block-atlas-result-dir> <new-report.json>"
                .to_owned(),
        );
    }

    let report = run_host(&artifacts)?;
    let mut encoded = serde_json::to_vec_pretty(&report)
        .map_err(|error| format!("the report encodes exactly: {error}"))?;
    encoded.push(b'\n');
    let mut file = std::fs::OpenOptions::new()
        .create_new(true)
        .write(true)
        .open(&output)
        .map_err(|error| format!("{} opens once: {error}", output.display()))?;
    file.write_all(&encoded)
        .map_err(|error| format!("{} writes completely: {error}", output.display()))?;
    file.sync_all()
        .map_err(|error| format!("{} syncs completely: {error}", output.display()))?;
    eprintln!(
        "eros transformer-seeded ecology: {} · {} bytes · {}",
        report.status,
        encoded.len(),
        output.display()
    );
    Ok(())
}

fn run_host(artifacts: &Path) -> Result<Report, String> {
    let manifest_path = artifacts.join("manifest.json");
    let token_path = artifacts.join("token_spans.jsonl");
    let leaders_path = artifacts.join("receiver_leaders.json");
    let manifest: Manifest = read_json(&manifest_path)?;
    let charts = read_json_lines::<SpanChart>(&token_path)?;
    let leaders: BTreeMap<String, Vec<Leader>> = read_json(&leaders_path)?;
    let source = chart(&charts, &manifest.fixture.source_current_id)?;
    let target = chart(&charts, &manifest.fixture.target_current_id)?;
    let selected = select_relations(&manifest, source, target, &leaders)?;
    if selected.len() != 3
        || selected
            .iter()
            .map(|relation| relation.head)
            .collect::<Vec<_>>()
            != [2, 9, 13]
    {
        return Err(format!(
            "the fixed atlas exposes source-component leaders [2, 9, 13], got {:?}",
            selected
                .iter()
                .map(|relation| relation.head)
                .collect::<Vec<_>>()
        ));
    }

    let canonical_namespace = capability_namespace(&manifest, "source");
    let foreign_namespace = capability_namespace(&manifest, "foreign-source");
    if canonical_namespace == foreign_namespace {
        return Err("the canonical and foreign source identities remain distinct".to_owned());
    }
    let seed_faces: Vec<_> = selected.iter().map(seed_faces).collect();
    let later_faces: Vec<_> = selected.iter().map(later_faces).collect();
    let (base, lineages) = primed_machine(selected.len())?;
    let rest = base.rest_image().map_err(debug)?;
    let mut teacher = LiveCurrentMachine::from_rest_image(rest.clone()).map_err(debug)?;
    let mut control = LiveCurrentMachine::from_rest_image(rest).map_err(debug)?;

    let seed_currents = currents(&lineages, &seed_faces)?;
    let seed_arcs = arcs(&lineages, &selected, canonical_namespace);
    let seed_cells = regional_cells(&lineages, &seed_arcs);
    let teacher_seed = teacher
        .receive(ContemporaryEvent::with_regional(
            &seed_currents,
            &[],
            &seed_cells,
        ))
        .map_err(debug)?;
    let control_seed = control
        .receive(ContemporaryEvent::unrelated(&seed_currents))
        .map_err(debug)?;
    let seed_current_exact = teacher_seed.currents() == control_seed.currents();
    let teacher_seed_regions = regional_reads(&teacher_seed);
    let teacher_after_seed = machine_read(&teacher);
    let control_after_seed = machine_read(&control);

    let teacher_rest = teacher.rest_image().map_err(debug)?;
    let mut experienced =
        LiveCurrentMachine::from_rest_image(teacher_rest.clone()).map_err(debug)?;
    let mut foreign = LiveCurrentMachine::from_rest_image(teacher_rest.clone()).map_err(debug)?;
    let rest_remount_exact = experienced.rest_image().map_err(debug)? == teacher_rest
        && foreign.rest_image().map_err(debug)? == teacher_rest;
    let later_currents = currents(&lineages, &later_faces)?;

    let experienced_arcs = arcs(&lineages, &selected, canonical_namespace);
    let experienced_cells = regional_cells(&lineages, &experienced_arcs);
    let experienced_radiation = experienced
        .receive(ContemporaryEvent::with_regional(
            &later_currents,
            &[],
            &experienced_cells,
        ))
        .map_err(debug)?;
    let experienced_outcome = branch_outcome(
        "prior transformer relation standing",
        canonical_namespace,
        experienced_radiation,
        &experienced,
    );

    let control_arcs = arcs(&lineages, &selected, canonical_namespace);
    let control_cells = regional_cells(&lineages, &control_arcs);
    let control_radiation = control
        .receive(ContemporaryEvent::with_regional(
            &later_currents,
            &[],
            &control_cells,
        ))
        .map_err(debug)?;
    let control_outcome = branch_outcome(
        "same later current without regional seed",
        canonical_namespace,
        control_radiation,
        &control,
    );

    let foreign_arcs = arcs(&lineages, &selected, foreign_namespace);
    let foreign_cells = regional_cells(&lineages, &foreign_arcs);
    let foreign_radiation = foreign
        .receive(ContemporaryEvent::with_regional(
            &later_currents,
            &[],
            &foreign_cells,
        ))
        .map_err(debug)?;
    let foreign_outcome = branch_outcome(
        "same visible faces under a different source identity",
        foreign_namespace,
        foreign_radiation,
        &foreign,
    );

    let same_later_currents = experienced_outcome.radiation.currents()
        == control_outcome.radiation.currents()
        && experienced_outcome.radiation.currents() == foreign_outcome.radiation.currents();
    let experienced_advanced = experienced_outcome
        .radiation
        .regional()
        .iter()
        .all(|relation| relation.constituent().grain() == 3);
    let control_source_grain = control_outcome
        .radiation
        .regional()
        .iter()
        .all(|relation| relation.constituent().grain() == 2);
    let foreign_source_grain = foreign_outcome
        .radiation
        .regional()
        .iter()
        .all(|relation| relation.constituent().grain() == 2);
    let experienced_consumed = experienced.standing().constituents().len() == selected.len();
    let foreign_preserved = foreign.standing().constituents().len() == selected.len() * 2;
    let selected_tokens_recur = seed_faces
        .iter()
        .zip(&later_faces)
        .all(|(seed, later)| seed.token_address == later.token_address);
    let selected_components_recur = seed_faces
        .iter()
        .zip(&later_faces)
        .all(|(seed, later)| seed.component_local_address == later.component_local_address);
    let selected_chronology_changes = seed_faces
        .iter()
        .zip(&later_faces)
        .all(|(seed, later)| seed.chronology_address != later.chronology_address);
    let model_repoints = selected
        .iter()
        .all(|relation| relation.target_position != relation.actual_target_position);
    let comparison = ComparisonRead {
        source_and_target_text_are_nonidentical: source.rendered_sha256 != target.rendered_sha256,
        selected_token_addresses_recur: selected_tokens_recur,
        selected_component_addresses_recur: selected_components_recur,
        selected_chronology_addresses_change: selected_chronology_changes,
        target_transformer_repoints_every_selected_relation: model_repoints,
        rest_remount_exact_before_later_event: rest_remount_exact,
        same_later_currents_in_all_branches: same_later_currents,
        experienced_regions_advanced_one_grain: experienced_advanced,
        unseeded_regions_remained_at_source_grain: control_source_grain,
        foreign_identity_did_not_rebase_prior_standing: foreign_source_grain,
        experienced_consumed_lower_constituents: experienced_consumed,
        foreign_identity_preserved_prior_and_new_constituents: foreign_preserved,
        later_model_interior_was_not_machine_input: true,
    };
    let accepted = seed_current_exact
        && teacher_seed_regions.len() == selected.len()
        && comparison.source_and_target_text_are_nonidentical
        && comparison.selected_token_addresses_recur
        && comparison.selected_component_addresses_recur
        && comparison.selected_chronology_addresses_change
        && comparison.target_transformer_repoints_every_selected_relation
        && comparison.rest_remount_exact_before_later_event
        && comparison.same_later_currents_in_all_branches
        && comparison.experienced_regions_advanced_one_grain
        && comparison.unseeded_regions_remained_at_source_grain
        && comparison.foreign_identity_did_not_rebase_prior_standing
        && comparison.experienced_consumed_lower_constituents
        && comparison.foreign_identity_preserved_prior_and_new_constituents;
    if !accepted {
        return Err("the fixed transformer-seeded regional contrasts did not close".to_owned());
    }

    let teacher_read = TeacherRead {
        observation_id: manifest.observation_id.clone(),
        model_repository: manifest.model.repository.clone(),
        model_revision: manifest.model.revision.clone(),
        layer: manifest.architecture.selected_layer,
        attention_heads: manifest.architecture.attention_heads,
        source_current_id: source.current_id.clone(),
        target_current_id: target.current_id.clone(),
        source_rendered_sha256: source.rendered_sha256.clone(),
        target_rendered_sha256: target.rendered_sha256.clone(),
        source_token_count: source.token_count,
        target_token_count: target.token_count,
        selection_law: "all source-current final-receiver head leaders whose complete token occurrence lies inside the source-declared informant or current-inscription component",
        selected_relations: selected.iter().map(relation_read).collect(),
        artifacts: vec![
            artifact_read(&manifest_path)?,
            artifact_read(&token_path)?,
            artifact_read(&leaders_path)?,
        ],
    };
    Ok(Report {
        schema: "eros.transformer-seeded-regional-ecology.v1",
        status: "accepted",
        question: "can an exact relational cut inherited from one pretrained transformer block become Eros Standing and alter a later nonidentical text current after the model interior departs?",
        theory_to_structure: "one measured receiver-to-source occurrence relation -> one regional cell over token address, source-component address, and chronology; later tokenizer/source identity -> the same two invariant faces at changed chronology",
        stop_boundary: "this grades causal inheritance and later regional participation only; it does not grade autonomous recruitment, language competence, model equivalence, or transformer distillation",
        teacher: teacher_read,
        seed: SeedRead {
            canonical_capability_namespace: hex_u64(canonical_namespace),
            teacher_current_radiation_sha256: sha256_debug(&teacher_seed.currents()),
            control_current_radiation_sha256: sha256_debug(&control_seed.currents()),
            ordinary_current_radiation_exact: seed_current_exact,
            teacher_regional: teacher_seed_regions,
            teacher_after: teacher_after_seed,
            control_after: control_after_seed,
        },
        later_experienced: experienced_outcome.read,
        later_unseeded: control_outcome.read,
        later_foreign_identity: foreign_outcome.read,
        comparison,
        conclusion: "the transformer-selected relations became regional Standing and changed the same later tokenizer current without the block interior; a different source identity did not consume that Standing. The held-out transformer itself repointed all three leaders, so this is genuine inherited regional memory but not yet a distillation rule: contextual field formation still has to be learned or lawfully supplied.",
    })
}

fn select_relations(
    manifest: &Manifest,
    source: &SpanChart,
    target: &SpanChart,
    leaders: &BTreeMap<String, Vec<Leader>>,
) -> Result<Vec<SelectedRelation>, String> {
    let source_leaders = leaders
        .get(&manifest.fixture.source_current_id)
        .ok_or_else(|| "the teacher source has final-receiver leaders".to_owned())?;
    let target_leaders = leaders
        .get(&manifest.fixture.target_current_id)
        .ok_or_else(|| "the observer target has final-receiver leaders".to_owned())?;
    if source_leaders.len() != manifest.architecture.attention_heads
        || target_leaders.len() != manifest.architecture.attention_heads
    {
        return Err(
            "the leader population equals the declared attention-head population".to_owned(),
        );
    }
    let mut selected = Vec::new();
    for leader in source_leaders {
        let token = source
            .tokens
            .get(leader.source_position)
            .ok_or_else(|| format!("source leader head {} names one token", leader.head))?;
        if token.position != leader.source_position
            || token.token_id != leader.source_token.token_id
            || token.byte_start != leader.source_token.byte_start
            || token.byte_end != leader.source_token.byte_end
        {
            return Err(format!(
                "source leader head {} remains exact in the tokenizer chart",
                leader.head
            ));
        }
        let Some(component) = component_for(source, token)? else {
            continue;
        };
        let target_component = role(target, &component.role)?;
        if component.byte_end - component.byte_start
            != target_component.byte_end - target_component.byte_start
        {
            return Err(format!(
                "component {} retains one exact extent",
                component.role
            ));
        }
        let local_start = token.byte_start - component.byte_start;
        let local_end = token.byte_end - component.byte_start;
        let mapped: Vec<_> = target
            .tokens
            .iter()
            .filter(|candidate| {
                candidate.byte_start == target_component.byte_start + local_start
                    && candidate.byte_end == target_component.byte_start + local_end
                    && candidate.token_id == token.token_id
                    && candidate.rendered_text == token.rendered_text
            })
            .collect();
        if mapped.len() != 1 {
            return Err(format!(
                "head {} source occurrence has one exact component-relative target occurrence",
                leader.head
            ));
        }
        let actual = target_leaders
            .iter()
            .find(|candidate| candidate.head == leader.head)
            .ok_or_else(|| format!("target retains head {}", leader.head))?;
        selected.push(SelectedRelation {
            head: leader.head,
            component: component.role.clone(),
            token_id: token.token_id,
            token_text: token.rendered_text.clone(),
            local_byte_start: local_start,
            local_byte_end: local_end,
            source_position: token.position,
            target_position: mapped[0].position,
            actual_target_position: actual.source_position,
            actual_target_token_id: actual.source_token.token_id,
            actual_target_text: actual.source_token.rendered_text.clone(),
            receiver_position: leader.receiver_position,
            attention_ratio: leader.attention_ratio.clone(),
            unscaled_pairing: leader.unscaled_query_key_pairing.ratio.clone(),
        });
    }
    selected.sort_unstable_by_key(|relation| relation.head);
    Ok(selected)
}

fn component_for<'a>(
    chart: &'a SpanChart,
    token: &TokenSpan,
) -> Result<Option<&'a RoleSpan>, String> {
    let matches: Vec<_> = chart
        .roles
        .iter()
        .filter(|candidate| {
            SOURCE_COMPONENTS.contains(&candidate.role.as_str())
                && token.byte_start >= candidate.byte_start
                && token.byte_end <= candidate.byte_end
        })
        .collect();
    match matches.as_slice() {
        [] => Ok(None),
        [component] => Ok(Some(*component)),
        _ => Err(format!(
            "token {} belongs to at most one movable source component",
            token.position
        )),
    }
}

fn role<'a>(chart: &'a SpanChart, name: &str) -> Result<&'a RoleSpan, String> {
    let matches: Vec<_> = chart
        .roles
        .iter()
        .filter(|role| role.role == name)
        .collect();
    match matches.as_slice() {
        [role] => Ok(*role),
        _ => Err(format!("{} has one {name} component", chart.current_id)),
    }
}

fn seed_faces(relation: &SelectedRelation) -> ActiveFaces {
    ActiveFaces {
        token_address: relation.token_id as i64,
        component_local_address: relation.local_byte_start as i64 + 1,
        chronology_address: relation.source_position as i64 + 1,
    }
}

fn later_faces(relation: &SelectedRelation) -> ActiveFaces {
    ActiveFaces {
        token_address: relation.token_id as i64,
        component_local_address: relation.local_byte_start as i64 + 1,
        chronology_address: relation.target_position as i64 + 1,
    }
}

fn active_face_read(faces: ActiveFaces) -> ActiveFaceRead {
    ActiveFaceRead {
        token_address: faces.token_address,
        component_local_address: faces.component_local_address,
        chronology_address: faces.chronology_address,
        exact_encoding: "token id; component-local byte start + 1; zero-based token position + 1",
    }
}

fn relation_read(relation: &SelectedRelation) -> RelationRead {
    RelationRead {
        head: relation.head,
        component: relation.component.clone(),
        source_token_id: relation.token_id,
        source_token_text: relation.token_text.clone(),
        component_local_byte_interval: [relation.local_byte_start, relation.local_byte_end],
        source_position: relation.source_position,
        tokenizer_transported_target_position: relation.target_position,
        actual_target_leader_position: relation.actual_target_position,
        actual_target_leader_token_id: relation.actual_target_token_id,
        actual_target_leader_text: relation.actual_target_text.clone(),
        receiver_position: relation.receiver_position,
        source_attention_ratio: relation.attention_ratio.clone(),
        source_unscaled_query_key_pairing: relation.unscaled_pairing.clone(),
        seed_active_faces: active_face_read(seed_faces(relation)),
        later_active_faces: active_face_read(later_faces(relation)),
    }
}

fn primed_machine(
    relations: usize,
) -> Result<
    (
        LiveCurrentMachine,
        Vec<[CurrentLineage; FACES_PER_RELATION]>,
    ),
    String,
> {
    let mut machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).map_err(debug)?);
    let first = relation(13)?;
    let mut flat = Vec::new();
    for _ in 0..relations * FACES_PER_RELATION {
        flat.push(
            machine
                .attach(CurrentGeometry::Cell(first))
                .map_err(debug)?,
        );
    }
    let lineages: Vec<[CurrentLineage; FACES_PER_RELATION]> = flat
        .chunks_exact(FACES_PER_RELATION)
        .map(|chunk| [chunk[0], chunk[1], chunk[2]])
        .collect();
    for value in PRIMING_VALUES {
        let faces = vec![
            ActiveFaces {
                token_address: value,
                component_local_address: value,
                chronology_address: value,
            };
            relations
        ];
        let event = currents(&lineages, &faces)?;
        machine
            .receive(ContemporaryEvent::unrelated(&event))
            .map_err(debug)?;
    }
    Ok((machine, lineages))
}

fn currents(
    lineages: &[[CurrentLineage; FACES_PER_RELATION]],
    faces: &[ActiveFaces],
) -> Result<Vec<CurrentEvent<'static>>, String> {
    if lineages.len() != faces.len() {
        return Err("every selected relation supplies exactly three active faces".to_owned());
    }
    let mut currents = Vec::new();
    for (lineages, faces) in lineages.iter().zip(faces) {
        for (lineage, value) in lineages.iter().zip([
            faces.token_address,
            faces.component_local_address,
            faces.chronology_address,
        ]) {
            currents.push(CurrentEvent::continuing(
                *lineage,
                relation(value)?,
                action(),
            ));
        }
    }
    Ok(currents)
}

fn arcs(
    lineages: &[[CurrentLineage; FACES_PER_RELATION]],
    selected: &[SelectedRelation],
    namespace: u64,
) -> Vec<[RegionalRelationArc; FACES_PER_RELATION]> {
    lineages
        .iter()
        .zip(selected)
        .map(|(lineages, selected)| {
            std::array::from_fn(|edge| {
                let to = (edge + 1) % FACES_PER_RELATION;
                RegionalRelationArc::new(
                    lineages[edge],
                    CurrentBoundaryPort::Cell,
                    lineages[to],
                    CurrentBoundaryPort::Cell,
                    InterfaceCapability::new(namespace, selected.head as u64 * 4 + edge as u64),
                    edge as u32,
                    0,
                    IncidenceHand::Against,
                )
            })
        })
        .collect()
}

fn regional_cells<'a>(
    lineages: &[[CurrentLineage; FACES_PER_RELATION]],
    arcs: &'a [[RegionalRelationArc; FACES_PER_RELATION]],
) -> Vec<RegionalRelationCell<'a>> {
    lineages
        .iter()
        .zip(arcs)
        .map(|(lineages, arcs)| RegionalRelationCell::new(lineages[2], arcs))
        .collect()
}

fn branch_outcome(
    role: &'static str,
    namespace: u64,
    radiation: ContemporaryRadiation,
    machine: &LiveCurrentMachine,
) -> BranchOutcome {
    let read = LaterBranchRead {
        role,
        capability_namespace: hex_u64(namespace),
        current_radiation_sha256: sha256_debug(&radiation.currents()),
        regional_radiation_sha256: sha256_debug(&radiation.regional()),
        regional: regional_reads(&radiation),
        after: machine_read(machine),
    };
    BranchOutcome { radiation, read }
}

fn regional_reads(radiation: &ContemporaryRadiation) -> Vec<ConstituentRead> {
    radiation
        .regional()
        .iter()
        .map(|relation| constituent_read(relation.constituent()))
        .collect()
}

fn constituent_read(constituent: &LiveConstituent) -> ConstituentRead {
    let mut open_boundaries = 0;
    let mut ride_boundaries = 0;
    let mut found_boundaries = 0;
    for at in 0..constituent.boundaries().len() {
        match constituent.boundary_transition(at) {
            Some(LiveBoundaryTransition::Open) => open_boundaries += 1,
            Some(LiveBoundaryTransition::Ride) => ride_boundaries += 1,
            Some(LiveBoundaryTransition::Found) => found_boundaries += 1,
            None => {}
        }
    }
    let mut contacts = ContactRead::default();
    for pin in constituent.pins() {
        match pin.formed().map(|formed| formed.deed()) {
            None => contacts.open += 1,
            Some(FeltDeed::Ride) => contacts.ride += 1,
            Some(FeltDeed::FoundThis) => contacts.found_this += 1,
            Some(FeltDeed::FoundThat) => contacts.found_that += 1,
            Some(FeltDeed::Dark) => contacts.dark += 1,
        }
    }
    let paths = constituent
        .boundaries()
        .iter()
        .flat_map(|boundary| boundary.paths());
    let path_count = paths.clone().count();
    let folded_paths = paths.clone().filter(|path| path.interior_folded()).count();
    let transport_terms = paths.map(|path| path.transport().terms().len()).sum();
    ConstituentRead {
        grain: constituent.grain(),
        axes: constituent.axis_count(),
        cells: constituent.cells().len(),
        incidences: constituent.incidences().len(),
        pins: constituent.pins().len(),
        boundaries: constituent.boundaries().len(),
        paths: path_count,
        folded_paths,
        transport_terms,
        exposed_pins: constituent.exposed().len(),
        open_boundaries,
        ride_boundaries,
        found_boundaries,
        contacts,
    }
}

fn machine_read(machine: &LiveCurrentMachine) -> MachineRead {
    let LiveMemory {
        standing_cells,
        standing_constituents,
        constituent_cells,
        constituent_incidences,
        constituent_pins,
        constituent_paths,
        constituent_transport_terms,
        live_lineages,
        ..
    } = machine.memory();
    MachineRead {
        standing_sha256: sha256_bytes(format!("{:?}", machine.standing()).as_bytes()),
        standing_rank: machine.standing().rank(),
        standing_cells,
        standing_constituents,
        constituent_cells,
        constituent_incidences,
        constituent_pins,
        constituent_paths,
        constituent_transport_terms,
        live_lineages,
    }
}

fn capability_namespace(manifest: &Manifest, identity: &str) -> u64 {
    let mut hash = Sha256::new();
    for part in [
        "eros.transformer-seeded-regional-ecology.v1",
        identity,
        &manifest.model.repository,
        &manifest.model.revision,
        &manifest.fixture.relation_id,
    ] {
        hash.update(part.as_bytes());
        hash.update([0]);
    }
    let digest = hash.finalize();
    u64::from_be_bytes(digest[..8].try_into().expect("SHA-256 retains eight bytes"))
}

fn relation(value: i64) -> Result<RelationAtom, String> {
    RelationAtom::new(Cog::lit(value))
        .ok_or_else(|| format!("relation value {value} remains nonzero"))
}

fn action() -> ActionCurrent {
    ActionCurrent::new(Cog::lit(1)).expect("one is a resolving action")
}

fn chart<'a>(charts: &'a [SpanChart], current: &str) -> Result<&'a SpanChart, String> {
    let matches: Vec<_> = charts
        .iter()
        .filter(|chart| chart.current_id == current)
        .collect();
    match matches.as_slice() {
        [chart] => Ok(*chart),
        _ => Err(format!("the token atlas contains one chart for {current}")),
    }
}

fn read_json<T: for<'de> Deserialize<'de>>(path: &Path) -> Result<T, String> {
    let bytes = std::fs::read(path)
        .map_err(|error| format!("{} reads completely: {error}", path.display()))?;
    serde_json::from_slice(&bytes)
        .map_err(|error| format!("{} parses exactly: {error}", path.display()))
}

fn read_json_lines<T: for<'de> Deserialize<'de>>(path: &Path) -> Result<Vec<T>, String> {
    let text = std::fs::read_to_string(path)
        .map_err(|error| format!("{} reads completely: {error}", path.display()))?;
    text.lines()
        .enumerate()
        .map(|(at, line)| {
            serde_json::from_str(line).map_err(|error| {
                format!("{} line {} parses exactly: {error}", path.display(), at + 1)
            })
        })
        .collect()
}

fn artifact_read(path: &Path) -> Result<ArtifactRead, String> {
    let bytes = std::fs::read(path)
        .map_err(|error| format!("{} reads for hashing: {error}", path.display()))?;
    Ok(ArtifactRead {
        path: path.display().to_string(),
        sha256: hex_bytes(&sha256_bytes(&bytes)),
    })
}

fn sha256_debug(value: &impl Debug) -> String {
    hex_bytes(&sha256_bytes(format!("{value:?}").as_bytes()))
}

fn sha256_bytes(bytes: &[u8]) -> [u8; 32] {
    Sha256::digest(bytes).into()
}

fn hex_bytes(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut encoded = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        encoded.push(HEX[(byte >> 4) as usize] as char);
        encoded.push(HEX[(byte & 15) as usize] as char);
    }
    encoded
}

fn hex_u64(value: u64) -> String {
    format!("0x{value:016x}")
}

fn debug(error: impl Debug) -> String {
    format!("{error:?}")
}
