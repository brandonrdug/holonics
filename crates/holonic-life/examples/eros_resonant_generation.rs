//! Full-corpus generative passage through the conditioned resonance ecology.
//!
//! Training supplies ordered token paths and their actual adjacent transports. A later prefix
//! supplies no target token. Its terminal receiver opens the production continuation aperture,
//! which returns a plural family of successor germs. Every returned branch is then re-entered as
//! self-emanated material from the same trained rest so its complete context-conditioned topology
//! and its next continuation family can be inspected.

use std::{
    collections::{BTreeMap, BTreeSet},
    io::Write,
    path::{Path, PathBuf},
    time::Instant,
};

use body::num::Cog;
use life::form_mouth::deposit_form_or_message;
use life::resonance_ecology::{
    ResonanceConstituentRead, ResonanceEcology, ResonanceEcologyRestImage, ResonanceGerm,
    ResonanceOccurrence, ResonanceOccurrenceOrigin,
};
use life::suffix_ecology::{ExactSuffixEcology, SuffixBranchSupport};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use soma_abi::active::{ActionCurrent, RelationAtom};
use soma_membrane::{
    LiveBoundaryTransition, LiveConstituent, LiveCurrentMachine, ParallelCpuLiveCurrentExecutor,
    ReceiverFiberIdentity, SparseStandingSurface,
};

/// This driver's name at the plate mouth: `.local/artifacts/eros_resonant_generation/<name>-<sha256>.form`.
const FORM_DRIVER: &str = "eros_resonant_generation";
/// The four forms this driver seals. None is `ERST` or `HTEC`: the suffix ecology and the
/// resonance ecology carry their own native wires, which `holon-plate` does not hold.
const SUFFIX_REST_FORM: &str = "suffix-rest";
const RESONANCE_REST_FORM: &str = "resonance-rest";
const RESONANCE_REMOUNT_FORM: &str = "resonance-remount";
const RESONANCE_REVERSE_FORM: &str = "resonance-reverse-delivery";

const REPORT_SCHEMA: &str = "eros.resonant-generation.report.v2";
const PREFIX_CONTEXT_SCHEMA: u64 = 0x4552_4f53_5052_4546;
const TOKEN_GERM_SCHEMA: u64 = 0x4552_4f53_544f_4b4e;
const INFORMANT_SCHEMA: u64 = 0x4552_4f53_4c49_4e45;

#[derive(Deserialize)]
struct Source {
    schema: String,
    observation_id: String,
    tokenizer: TokenizerDeclaration,
    training_lines: Vec<SourceLine>,
    probes: Vec<SourceProbe>,
}

#[derive(Deserialize)]
struct TokenizerDeclaration {
    files: Vec<TokenizerFile>,
}

#[derive(Deserialize)]
struct TokenizerFile {
    path: String,
    sha256: String,
}

#[derive(Clone, Deserialize)]
struct SourceLine {
    line_ordinal: u32,
    #[serde(rename = "text")]
    _text: String,
    token_ids: Vec<u32>,
}

#[derive(Deserialize)]
struct SourceProbe {
    species: String,
    validation: ValidationLine,
    target_index: usize,
    prefix_token_ids: Vec<u32>,
    actual_token_id: u32,
    actual_piece: String,
    sibling_token_id: u32,
    sibling_piece: String,
}

#[derive(Deserialize)]
struct ValidationLine {
    line_ordinal: u32,
    text: String,
    token_ids: Vec<u32>,
}

#[derive(Serialize)]
struct Report {
    schema: &'static str,
    status: &'static str,
    source_schema: String,
    source_observation_id: String,
    source_sha256: String,
    tokenizer_sha256: String,
    tokenizer_matches_declared_source: bool,
    source_lines: usize,
    token_occurrences: usize,
    distinct_prefix_context_germs: usize,
    configuration_wall_millis: u128,
    reverse_configuration_wall_millis: u128,
    delivery_permutation_exact: bool,
    receptor_population: usize,
    rest_bytes: usize,
    rest_sha256: String,
    remount_exact: bool,
    suffix_state_population: usize,
    suffix_material_occurrence_population: u64,
    suffix_material_transition_population: usize,
    suffix_state_linear_bound: usize,
    suffix_state_linear_bound_respected: bool,
    suffix_configuration_wall_millis: u128,
    suffix_reverse_configuration_wall_millis: u128,
    suffix_rest_bytes: usize,
    suffix_rest_sha256: String,
    suffix_delivery_permutation_exact: bool,
    suffix_remount_exact: bool,
    generated_probe_population: usize,
    generation_wall_millis: u128,
    exposed_suffix_context_population: usize,
    emitted_branch_population: usize,
    self_emanated_branches_returned: usize,
    previously_unseen_prefix_branches: usize,
    distinct_branch_topologies: usize,
    species_grades: BTreeMap<String, SpeciesGrade>,
    probes: Vec<ProbeGenerationRead>,
    branch_tsv: String,
}

#[derive(Default, Serialize)]
struct SpeciesGrade {
    probe_population: usize,
    emitted_branch_population: usize,
    actual_present: usize,
    sibling_present: usize,
    both_present: usize,
    neither_present: usize,
}

#[derive(Serialize)]
struct ProbeGenerationRead {
    species: String,
    validation_line_ordinal: u32,
    validation_text: String,
    validation_token_ids: Vec<u32>,
    target_index: usize,
    prefix_token_ids: Vec<u32>,
    prefix_pieces: Vec<String>,
    actual_token_id: u32,
    actual_piece: String,
    sibling_token_id: u32,
    sibling_piece: String,
    candidate_population: usize,
    candidate_token_ids: Vec<u32>,
    candidate_pieces: Vec<String>,
    longest_recurrent_suffix_length: u32,
    suffix_context_population: usize,
    actual_present: bool,
    sibling_present: bool,
    question_returned_informants: usize,
    question_returned_germs: usize,
    question_origins: Vec<&'static str>,
    question_transitions: TransitionRead,
    question_constituent_sha256: String,
    branches: Vec<BranchRead>,
}

#[derive(Serialize)]
struct BranchRead {
    token_id: u32,
    piece: String,
    provenance: &'static str,
    supporting_contexts: Vec<SuffixSupportRead>,
    prefix_path_previously_observed: bool,
    returned_informants: usize,
    returned_germs: usize,
    returned_origins: Vec<&'static str>,
    transitions: TransitionRead,
    next_candidate_population: usize,
    next_candidate_token_ids: Vec<u32>,
    next_candidate_pieces: Vec<String>,
    constituent_sha256: String,
}

#[derive(Serialize)]
struct SuffixSupportRead {
    state: u32,
    matched_length: u32,
    target_state: u32,
    recurrence_multiplicity: u64,
    context_token_ids: Vec<u32>,
    context_pieces: Vec<String>,
}

#[derive(Default, Serialize)]
struct TransitionRead {
    open: usize,
    ride: usize,
    found: usize,
}

fn main() {
    if let Err(error) = run() {
        eprintln!("eros resonant generation: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let source_path = PathBuf::from(arguments.next().ok_or_else(usage)?);
    let tokenizer_path = PathBuf::from(arguments.next().ok_or_else(usage)?);
    let report_path = PathBuf::from(arguments.next().ok_or_else(usage)?);
    if arguments.next().is_some() {
        return Err(usage());
    }

    let source_bytes = std::fs::read(&source_path)
        .map_err(|error| format!("{} reads: {error}", source_path.display()))?;
    let source: Source = serde_json::from_slice(&source_bytes)
        .map_err(|error| format!("{} decodes: {error}", source_path.display()))?;
    if source.training_lines.is_empty()
        || source
            .training_lines
            .iter()
            .any(|line| line.token_ids.is_empty())
    {
        return Err("the source carries no complete training paths".to_owned());
    }
    let tokenizer_bytes = std::fs::read(&tokenizer_path)
        .map_err(|error| format!("{} reads: {error}", tokenizer_path.display()))?;
    let tokenizer_sha256 = sha256(&tokenizer_bytes);
    let declared_tokenizer_sha256 = source
        .tokenizer
        .files
        .iter()
        .find(|file| file.path == "tokenizer.json")
        .map(|file| file.sha256.as_str())
        .ok_or_else(|| "the source does not declare tokenizer.json".to_owned())?;
    let tokenizer_matches_declared_source = tokenizer_sha256 == declared_tokenizer_sha256;
    if !tokenizer_matches_declared_source {
        return Err("the supplied tokenizer does not match the frozen source".to_owned());
    }
    let token_pieces = token_pieces(&tokenizer_bytes)?;

    let mut token_occurrences = 0usize;
    let mut distinct_contexts = BTreeSet::new();
    let occurrences = source
        .training_lines
        .iter()
        .map(|line| {
            token_occurrences = token_occurrences
                .checked_add(line.token_ids.len())
                .ok_or_else(|| "token occurrence census overflowed".to_owned())?;
            let germs = context_germs(&line.token_ids)?;
            distinct_contexts.extend(germs.iter().map(|germ| germ.identity().clone()));
            ResonanceOccurrence::continuation_informant(
                informant_fiber(line)?,
                u64::from(line.line_ordinal),
                germs,
            )
            .map_err(debug)
        })
        .collect::<Result<Vec<_>, String>>()?;
    let token_paths = source
        .training_lines
        .iter()
        .map(|line| token_germs(&line.token_ids))
        .collect::<Result<Vec<_>, String>>()?;
    let suffix_configuration_started = Instant::now();
    let suffix_ecology = ExactSuffixEcology::condition(&token_paths).map_err(debug)?;
    let suffix_configuration_wall_millis = suffix_configuration_started.elapsed().as_millis();
    let suffix_rest_bytes = suffix_ecology.encode_native_bytes().map_err(debug)?;
    // THE_ASSEMBLY.md step 5, loop (d): *the signal is the octets*. Every hash here is untouched.
    // This is the exact-suffix ecology's own wire; no held plate schema reads it, which is a fact
    // about the reader's held set and is what the falsifier reports.
    let deposited = deposit_form_or_message(FORM_DRIVER, SUFFIX_REST_FORM, &suffix_rest_bytes)?;
    eprintln!("form deposited: {}", deposited.path.display());
    let suffix_rest_sha256 = sha256(&suffix_rest_bytes);
    let suffix_reopened =
        ExactSuffixEcology::from_native_bytes(&suffix_rest_bytes).map_err(debug)?;
    let suffix_remount_exact = suffix_reopened == suffix_ecology;
    let reversed_token_paths = token_paths.iter().rev().cloned().collect::<Vec<_>>();
    let suffix_reverse_started = Instant::now();
    let reversed_suffix = ExactSuffixEcology::condition(&reversed_token_paths).map_err(debug)?;
    let suffix_reverse_configuration_wall_millis = suffix_reverse_started.elapsed().as_millis();
    let suffix_delivery_permutation_exact = reversed_suffix == suffix_ecology;
    let conditioned_symbols = token_occurrences
        .checked_add(source.training_lines.len())
        .ok_or_else(|| "suffix symbol census overflowed".to_owned())?;
    let suffix_state_linear_bound = conditioned_symbols
        .checked_mul(2)
        .and_then(|extent| extent.checked_add(1))
        .ok_or_else(|| "suffix state bound overflowed".to_owned())?;
    let suffix_state_linear_bound_respected =
        suffix_ecology.state_count() <= suffix_state_linear_bound;
    if !suffix_state_linear_bound_respected {
        return Err("the factorized suffix ecology exceeded its linear state bound".to_owned());
    }
    if suffix_ecology.material_occurrence_count()
        != u64::try_from(token_occurrences)
            .map_err(|_| "token occurrence census exceeds u64".to_owned())?
    {
        return Err("the suffix ecology lost material occurrence testimony".to_owned());
    }

    let threads = std::thread::available_parallelism()
        .map(|extent| extent.get())
        .unwrap_or(1);
    let mut executor = ParallelCpuLiveCurrentExecutor::new(threads);
    let mut ecology = ResonanceEcology::new(LiveCurrentMachine::new(
        SparseStandingSurface::empty_rank(8).map_err(debug)?,
    ));
    let started = Instant::now();
    ecology
        .receive_configuration_with(&occurrences, action()?, &mut executor)
        .map_err(debug)?;
    let configuration_wall_millis = started.elapsed().as_millis();
    let rest = ecology.rest_image().map_err(debug)?;
    let rest_bytes = rest.encode_native_bytes().map_err(debug)?;
    // The resonance ecology's own rest wire. Same discipline; no held plate schema reads it either.
    let deposited = deposit_form_or_message(FORM_DRIVER, RESONANCE_REST_FORM, &rest_bytes)?;
    eprintln!("form deposited: {}", deposited.path.display());
    let rest_sha256 = sha256(&rest_bytes);
    let reopened = ResonanceEcologyRestImage::from_native_bytes(&rest_bytes).map_err(debug)?;
    let remounted = ResonanceEcology::from_rest_image(reopened).map_err(debug)?;
    let remounted_bytes = remounted
        .rest_image()
        .map_err(debug)?
        .encode_native_bytes()
        .map_err(debug)?;
    let deposited = deposit_form_or_message(FORM_DRIVER, RESONANCE_REMOUNT_FORM, &remounted_bytes)?;
    eprintln!("form deposited: {}", deposited.path.display());
    let remount_exact = remounted_bytes == rest_bytes;

    let reversed = occurrences.iter().rev().cloned().collect::<Vec<_>>();
    let mut reverse_executor = ParallelCpuLiveCurrentExecutor::new(threads);
    let mut reverse = ResonanceEcology::new(LiveCurrentMachine::new(
        SparseStandingSurface::empty_rank(8).map_err(debug)?,
    ));
    let reverse_started = Instant::now();
    reverse
        .receive_configuration_with(&reversed, action()?, &mut reverse_executor)
        .map_err(debug)?;
    let reverse_configuration_wall_millis = reverse_started.elapsed().as_millis();
    let reverse_bytes = reverse
        .rest_image()
        .map_err(debug)?
        .encode_native_bytes()
        .map_err(debug)?;
    let deposited = deposit_form_or_message(FORM_DRIVER, RESONANCE_REVERSE_FORM, &reverse_bytes)?;
    eprintln!("form deposited: {}", deposited.path.display());
    let delivery_permutation_exact = reverse_bytes == rest_bytes;
    eprintln!(
        "eros resonant generation: conditioned {} paths / {} prefix contexts · resonance rest {} bytes · suffix states {} / bound {} · suffix rest {} bytes · both delivery gauges {}",
        source.training_lines.len(),
        distinct_contexts.len(),
        rest_bytes.len(),
        suffix_ecology.state_count(),
        suffix_state_linear_bound,
        suffix_rest_bytes.len(),
        suffix_delivery_permutation_exact && delivery_permutation_exact,
    );
    drop(ecology);
    drop(remounted);
    drop(reverse);
    drop(reversed);
    drop(occurrences);
    drop(reversed_suffix);
    drop(reversed_token_paths);
    drop(token_paths);

    let mut probes = Vec::new();
    let mut species_grades = BTreeMap::<String, SpeciesGrade>::new();
    let mut emitted_branch_population = 0usize;
    let mut self_emanated_branches_returned = 0usize;
    let mut previously_unseen_prefix_branches = 0usize;
    let mut exposed_suffix_context_population = 0usize;
    let mut branch_topologies = BTreeSet::new();
    let mut tsv_rows = Vec::new();
    let generation_started = Instant::now();
    for probe in source.probes {
        let prefix = context_germs(&probe.prefix_token_ids)?;
        let question = ResonanceOccurrence::probe(u64::MAX - 4, prefix).map_err(debug)?;
        let mut question_ecology = ResonanceEcology::from_rest_image(
            ResonanceEcologyRestImage::from_native_bytes(&rest_bytes).map_err(debug)?,
        )
        .map_err(debug)?;
        let mut question_executor = ParallelCpuLiveCurrentExecutor::new(threads);
        let question_radiation = question_ecology
            .receive_with(&question, action()?, &mut question_executor)
            .map_err(debug)?;
        drop(question_ecology);
        drop(question_executor);
        let suffix_question = token_germs(&probe.prefix_token_ids)?;
        let emanation = suffix_ecology.emanate(&suffix_question).map_err(debug)?;
        exposed_suffix_context_population = exposed_suffix_context_population
            .checked_add(emanation.contexts().len())
            .ok_or_else(|| "suffix context census overflowed".to_owned())?;
        let candidate_token_ids = emanation
            .branches()
            .iter()
            .map(|branch| raw_token_id(branch.germ().identity()))
            .collect::<Result<Vec<_>, _>>()?;
        eprintln!(
            "eros resonant generation: {} / line {} reaches {} suffix scales and exposes {} branches",
            probe.species,
            probe.validation.line_ordinal,
            emanation.contexts().len(),
            candidate_token_ids.len(),
        );
        let candidate_set = candidate_token_ids.iter().copied().collect::<BTreeSet<_>>();
        let actual_present = candidate_set.contains(&probe.actual_token_id);
        let sibling_present = candidate_set.contains(&probe.sibling_token_id);
        let question_read = question_radiation.read();
        let question_constituent_sha256 =
            constituent_sha256(question_radiation.regional().constituent())?;
        let mut branches = Vec::new();
        for branch in emanation.branches() {
            let candidate = raw_token_id(branch.germ().identity())?;
            let mut branch_path = probe.prefix_token_ids.clone();
            branch_path.push(candidate);
            let branch_germs = context_germs(&branch_path)?;
            let occurrence =
                ResonanceOccurrence::self_emanated(u64::MAX - 2, branch_germs).map_err(debug)?;
            let prefix_path_previously_observed =
                contiguous_path_is_inherited(&branch_path, &source.training_lines);
            let mut branch_ecology = ResonanceEcology::from_rest_image(
                ResonanceEcologyRestImage::from_native_bytes(&rest_bytes).map_err(debug)?,
            )
            .map_err(debug)?;
            let mut branch_executor = ParallelCpuLiveCurrentExecutor::new(threads);
            let returned = branch_ecology
                .receive_with(&occurrence, action()?, &mut branch_executor)
                .map_err(debug)?;
            let returned_read = returned.read();
            let next_question = token_germs(&branch_path)?;
            let next_candidate_token_ids = suffix_ecology
                .emanate(&next_question)
                .map_err(debug)?
                .branches()
                .iter()
                .map(|next| raw_token_id(next.germ().identity()))
                .collect::<Result<Vec<_>, _>>()?;
            let constituent_sha256 = constituent_sha256(returned.regional().constituent())?;
            branch_topologies.insert(constituent_sha256.clone());
            if returned_read
                .origins()
                .contains(&ResonanceOccurrenceOrigin::SelfEmanated)
            {
                self_emanated_branches_returned += 1;
            }
            if !prefix_path_previously_observed {
                previously_unseen_prefix_branches += 1;
            }
            tsv_rows.push(format!(
                "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
                probe.species,
                probe.validation.line_ordinal,
                render_ids(&probe.prefix_token_ids),
                candidate,
                display_piece(candidate, &token_pieces),
                prefix_path_previously_observed,
                returned_read.open_pins(),
                returned_read.riding_pins(),
                next_candidate_token_ids.len(),
                constituent_sha256,
            ));
            branches.push(BranchRead {
                token_id: candidate,
                piece: display_piece(candidate, &token_pieces),
                provenance: "self-emanated",
                supporting_contexts: branch
                    .supports()
                    .iter()
                    .map(|support| {
                        suffix_support_read(*support, &probe.prefix_token_ids, &token_pieces)
                    })
                    .collect::<Result<Vec<_>, _>>()?,
                prefix_path_previously_observed,
                returned_informants: returned_read.informants().len(),
                returned_germs: returned_read.germs().len(),
                returned_origins: origins(returned_read),
                transitions: transition_read(returned.regional().support_transitions()),
                next_candidate_population: next_candidate_token_ids.len(),
                next_candidate_pieces: next_candidate_token_ids
                    .iter()
                    .map(|token| display_piece(*token, &token_pieces))
                    .collect(),
                next_candidate_token_ids,
                constituent_sha256,
            });
        }
        emitted_branch_population += branches.len();
        let grade = species_grades.entry(probe.species.clone()).or_default();
        grade.probe_population += 1;
        grade.emitted_branch_population += branches.len();
        grade.actual_present += usize::from(actual_present);
        grade.sibling_present += usize::from(sibling_present);
        grade.both_present += usize::from(actual_present && sibling_present);
        grade.neither_present += usize::from(!actual_present && !sibling_present);
        probes.push(ProbeGenerationRead {
            species: probe.species,
            validation_line_ordinal: probe.validation.line_ordinal,
            validation_text: probe.validation.text,
            validation_token_ids: probe.validation.token_ids,
            target_index: probe.target_index,
            prefix_token_ids: probe.prefix_token_ids.clone(),
            prefix_pieces: probe
                .prefix_token_ids
                .iter()
                .map(|token| display_piece(*token, &token_pieces))
                .collect(),
            actual_token_id: probe.actual_token_id,
            actual_piece: probe.actual_piece,
            sibling_token_id: probe.sibling_token_id,
            sibling_piece: probe.sibling_piece,
            candidate_population: candidate_token_ids.len(),
            candidate_pieces: candidate_token_ids
                .iter()
                .map(|token| display_piece(*token, &token_pieces))
                .collect(),
            candidate_token_ids,
            longest_recurrent_suffix_length: emanation.longest_matched_length(),
            suffix_context_population: emanation.contexts().len(),
            actual_present,
            sibling_present,
            question_returned_informants: question_read.informants().len(),
            question_returned_germs: question_read.germs().len(),
            question_origins: origins(question_read),
            question_transitions: transition_read(
                question_radiation.regional().support_transitions(),
            ),
            question_constituent_sha256,
            branches,
        });
    }
    let generation_wall_millis = generation_started.elapsed().as_millis();

    let report_parent = report_path
        .parent()
        .ok_or_else(|| format!("{} has no parent", report_path.display()))?;
    std::fs::create_dir_all(report_parent)
        .map_err(|error| format!("{} creates: {error}", report_parent.display()))?;
    let branch_path = report_parent.join("GENERATIVE_BRANCHES.tsv");
    let mut tsv = std::fs::File::create(&branch_path)
        .map_err(|error| format!("{} creates: {error}", branch_path.display()))?;
    writeln!(
        tsv,
        "species\tvalidation_line\tprefix_token_ids\tcandidate_token_id\tcandidate_piece\tpreviously_observed\topen_pins\triding_pins\tnext_candidate_population\tconstituent_sha256"
    )
    .map_err(|error| format!("{} writes: {error}", branch_path.display()))?;
    for row in tsv_rows {
        writeln!(tsv, "{row}")
            .map_err(|error| format!("{} writes: {error}", branch_path.display()))?;
    }

    let report = Report {
        schema: REPORT_SCHEMA,
        status: "full-corpus-generated",
        source_schema: source.schema,
        source_observation_id: source.observation_id,
        source_sha256: sha256(&source_bytes),
        tokenizer_sha256,
        tokenizer_matches_declared_source,
        source_lines: source.training_lines.len(),
        token_occurrences,
        distinct_prefix_context_germs: distinct_contexts.len(),
        configuration_wall_millis,
        reverse_configuration_wall_millis,
        delivery_permutation_exact,
        receptor_population: rest.receptor_count(),
        rest_bytes: rest_bytes.len(),
        rest_sha256,
        remount_exact,
        suffix_state_population: suffix_ecology.state_count(),
        suffix_material_occurrence_population: suffix_ecology.material_occurrence_count(),
        suffix_material_transition_population: suffix_ecology.material_transition_count(),
        suffix_state_linear_bound,
        suffix_state_linear_bound_respected,
        suffix_configuration_wall_millis,
        suffix_reverse_configuration_wall_millis,
        suffix_rest_bytes: suffix_rest_bytes.len(),
        suffix_rest_sha256,
        suffix_delivery_permutation_exact,
        suffix_remount_exact,
        generated_probe_population: probes.len(),
        generation_wall_millis,
        exposed_suffix_context_population,
        emitted_branch_population,
        self_emanated_branches_returned,
        previously_unseen_prefix_branches,
        distinct_branch_topologies: branch_topologies.len(),
        species_grades,
        probes,
        branch_tsv: branch_path.display().to_string(),
    };
    write_json(&report_path, &report)?;
    println!(
        "eros resonant generation: wrote {} probes / {} plural branches / {} previously unseen prefix branches to {}",
        report.generated_probe_population,
        report.emitted_branch_population,
        report.previously_unseen_prefix_branches,
        report_path.display(),
    );
    Ok(())
}

fn informant_fiber(line: &SourceLine) -> Result<ReceiverFiberIdentity, String> {
    let extent = u64::try_from(line.token_ids.len())
        .map_err(|_| "line extent does not fit the exact carrier".to_owned())?;
    let mut words = Vec::with_capacity(4 + line.token_ids.len());
    words.extend([line.line_ordinal, 0, extent as u32, (extent >> 32) as u32]);
    words.extend_from_slice(&line.token_ids);
    Ok(ReceiverFiberIdentity::new(INFORMANT_SCHEMA, words))
}

fn context_germs(tokens: &[u32]) -> Result<Vec<ResonanceGerm>, String> {
    let mut germs = Vec::new();
    germs
        .try_reserve_exact(tokens.len())
        .map_err(|error| format!("prefix context reserves: {error}"))?;
    for at in 0..tokens.len() {
        germs.push(context_germ(&tokens[..=at])?);
    }
    Ok(germs)
}

fn token_germs(tokens: &[u32]) -> Result<Vec<ResonanceGerm>, String> {
    let mut germs = Vec::new();
    germs
        .try_reserve_exact(tokens.len())
        .map_err(|error| format!("token germ path reserves: {error}"))?;
    for token in tokens {
        let phase = RelationAtom::new(Cog::lit(i64::from(*token) + 1))
            .ok_or_else(|| "token phase is dark".to_owned())?;
        germs.push(ResonanceGerm::new(
            ReceiverFiberIdentity::new(TOKEN_GERM_SCHEMA, [*token]),
            phase,
        ));
    }
    Ok(germs)
}

fn context_germ(context: &[u32]) -> Result<ResonanceGerm, String> {
    let token = context
        .last()
        .copied()
        .ok_or_else(|| "a context receiver cannot be empty".to_owned())?;
    let extent = u64::try_from(context.len())
        .map_err(|_| "prefix context exceeds the exact carrier".to_owned())?;
    let mut words = Vec::with_capacity(2 + context.len());
    words.extend([extent as u32, (extent >> 32) as u32]);
    words.extend_from_slice(context);
    let phase = RelationAtom::new(Cog::lit(i64::from(token) + 1))
        .ok_or_else(|| "token phase is dark".to_owned())?;
    Ok(ResonanceGerm::new(
        ReceiverFiberIdentity::new(PREFIX_CONTEXT_SCHEMA, words),
        phase,
    ))
}

fn raw_token_id(fiber: &ReceiverFiberIdentity) -> Result<u32, String> {
    if fiber.schema() != TOKEN_GERM_SCHEMA || fiber.words().len() != 1 {
        return Err("the suffix ecology returned a non-token germ".to_owned());
    }
    Ok(fiber.words()[0])
}

fn suffix_support_read(
    support: SuffixBranchSupport,
    prefix: &[u32],
    pieces: &BTreeMap<u32, String>,
) -> Result<SuffixSupportRead, String> {
    let matched_length = usize::try_from(support.matched_length())
        .map_err(|_| "a suffix context length exceeds the cpu".to_owned())?;
    let start = prefix
        .len()
        .checked_sub(matched_length)
        .ok_or_else(|| "a suffix support exceeds its question path".to_owned())?;
    let context_token_ids = prefix[start..].to_vec();
    Ok(SuffixSupportRead {
        state: support.state(),
        matched_length: support.matched_length(),
        target_state: support.target_state(),
        recurrence_multiplicity: support.recurrence_multiplicity(),
        context_pieces: context_token_ids
            .iter()
            .map(|token| display_piece(*token, pieces))
            .collect(),
        context_token_ids,
    })
}

fn contiguous_path_is_inherited(path: &[u32], lines: &[SourceLine]) -> bool {
    lines.iter().any(|line| {
        line.token_ids
            .windows(path.len())
            .any(|window| window == path)
    })
}

fn origins(read: &ResonanceConstituentRead) -> Vec<&'static str> {
    read.origins()
        .iter()
        .map(|origin| match origin {
            ResonanceOccurrenceOrigin::Inherited => "inherited",
            ResonanceOccurrenceOrigin::ReceiverQuestion => "receiver-question",
            ResonanceOccurrenceOrigin::SelfEmanated => "self-emanated",
        })
        .collect()
}

fn transition_read(transitions: &[Vec<LiveBoundaryTransition>]) -> TransitionRead {
    let mut read = TransitionRead::default();
    for transition in transitions.iter().flatten() {
        match transition {
            LiveBoundaryTransition::Open => read.open += 1,
            LiveBoundaryTransition::Ride => read.ride += 1,
            LiveBoundaryTransition::Found => read.found += 1,
        }
    }
    read
}

fn constituent_sha256(constituent: &LiveConstituent) -> Result<String, String> {
    let words = constituent.native_words().map_err(debug)?;
    let mut bytes = Vec::with_capacity(words.len() * core::mem::size_of::<u32>());
    for word in words {
        bytes.extend_from_slice(&word.to_le_bytes());
    }
    Ok(sha256(&bytes))
}

fn token_pieces(bytes: &[u8]) -> Result<BTreeMap<u32, String>, String> {
    let tokenizer: serde_json::Value =
        serde_json::from_slice(bytes).map_err(|error| format!("tokenizer decodes: {error}"))?;
    let vocabulary = tokenizer
        .get("model")
        .and_then(|model| model.get("vocab"))
        .and_then(serde_json::Value::as_object)
        .ok_or_else(|| "tokenizer.json has no model vocabulary".to_owned())?;
    vocabulary
        .iter()
        .map(|(piece, token)| {
            let token = token
                .as_u64()
                .and_then(|token| u32::try_from(token).ok())
                .ok_or_else(|| "tokenizer vocabulary id exceeds u32".to_owned())?;
            Ok((token, piece.clone()))
        })
        .collect()
}

fn display_piece(token: u32, pieces: &BTreeMap<u32, String>) -> String {
    pieces
        .get(&token)
        .map(|piece| piece.replace('Ġ', " ").replace('Ċ', "\\n"))
        .unwrap_or_else(|| format!("<token:{token}>"))
}

fn render_ids(ids: &[u32]) -> String {
    ids.iter().map(u32::to_string).collect::<Vec<_>>().join(",")
}

fn action() -> Result<ActionCurrent, String> {
    ActionCurrent::new(Cog::lit(1)).ok_or_else(|| "action current is dark".to_owned())
}

fn sha256(bytes: &[u8]) -> String {
    let mut digest = Sha256::new();
    digest.update(bytes);
    digest
        .finalize()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn write_json(path: &Path, report: &Report) -> Result<(), String> {
    let bytes = serde_json::to_vec_pretty(report).map_err(|error| error.to_string())?;
    std::fs::write(path, bytes).map_err(|error| format!("{} writes: {error}", path.display()))
}

fn debug(error: impl std::fmt::Debug) -> String {
    format!("{error:?}")
}

fn usage() -> String {
    "usage: eros_resonant_generation SOURCE.json tokenizer.json REPORT.json".to_owned()
}
