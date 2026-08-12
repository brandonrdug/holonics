//! Production as re-emission: the deposit licenses the continuation, and removing it removes it.
//!
//! ```text
//! flock /tmp/holonics-gpu.lock cargo run -p life --release \
//!   --example the_deposit_licenses_the_re_emission -- \
//!   --corpus-form output/the_material_mouth_seals_the_declared_body/declared-corpus-native-rest-<address>.form
//! ```
//!
//! **What this driver is for.**  `canon/TABLET_THE_RESONANCE.md` §6: *"enumerating every reachable
//! continuation is not generation at all. It is the complete candidate population, which is a
//! different object — and returning it is what a body does when nothing has been deposited to
//! conduct one way rather than another."*  The measured instance is
//! `research/records/2026-08-10_THE_MACHINE_RETURNS_EVERY_BRANCH_BECAUSE_NOTHING_ATTACHES.md`:
//! **14,018 response branches for one two-token prompt** on the declared document family below.
//!
//! The mandatory falsifier, in five receipts, all of which this driver returns or refuses:
//!
//! 1. the complete continuation fiber — the enumeration, as the control arm;
//! 2. the conducted sub-population, **strictly smaller**, every attached continuation naming the
//!    deposits that licensed it;
//! 3. the withheld fiber, retained and counted, never emitted;
//! 4. `ablate_target` against the generation: removing one named deposit removes **exactly** the
//!    continuations it licensed — this is the non-tautological ablation, and the one that measures
//!    `CLAUDE.md` §13 rule 1;
//! 5. full ablation restores the enumeration bit-exactly.
//!
//! **Receipt 5 is true by type-state and is reported as such.**  `ablate_all` consumes the conduct
//! morphology and hands back the plain ecology, so the complete arm cannot return anything else.
//! What it establishes is narrower than it sounds and still worth taking: the conducted pass did
//! not mutate the ecology it borrowed.  Receipt 4 is the one that can fail.
//!
//! **The material.**  The corpus is the sealed declared body, mounted by content address from a
//! path the caller supplies.  The family conditioned from it is the **same seventeen declared
//! documents** the 14,018 measurement ran on, so the two counts are comparable; the exterior source
//! of an occurrence is its declared repository-relative path and never its container, because a
//! container coordinate on this machine is an absolute host path
//! (`research/records/2026-08-11_THE_SEAL_CARRIED_THE_HOST_AND_THE_ORGANS_AWAIT_THEIR_CURRENT.md`
//! §2 conviction 1) and an absolute frame may not enter a lineage.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs::File,
    io::BufReader,
    path::{Path, PathBuf},
    time::Instant,
};

use body::num::Cog;
use holonic_engine::hardware_cover::HardwareCover;
use life::{
    form_mouth::deposit_form_or_message,
    morphological_language::{
        CudaMorphologicalConductExecutor, MorphologicalConductEdgeAddress, MorphologicalConductGenerationReceipt,
        MorphologicalConductPlurality, MorphologicalConductState, MorphologicalGeneratedCurrent,
        MorphologicalGenerationSpec, MorphologicalLanguageConductState,
        MorphologicalLanguageCurrentGeneration, MorphologicalLanguageEcology,
        MorphologicalLanguagePassage, MorphologicalResponseRest, MorphologicalSupportConduct,
    },
    text_material::{ExactTextMaterialAtlas, TextMaterialRole},
};
use serde::Serialize;
use soma_abi::active::ActionCurrent;

const DRIVER: &str = "the_deposit_licenses_the_re_emission";
const GRADE_FORM: &str = "re-emission-grade";
const REPORT_SCHEMA: &str = "soma-life.deposit-licenses-re-emission.v1";

/// **The declared document family of the 14,018-branch measurement**, verbatim from
/// `soma/life/driver-sources/eros-morphological-language-generation-bounded-01/SOURCE.json`.
///
/// This is a material declaration and not an aperture: it names *which corpus* the two arms are
/// compared on, so that the conducted count can be read against the enumerated one. A caller may
/// declare a different family with `--family`; a declared member the sealed corpus does not carry
/// is a refusal, never a silent skip.
const DECLARED_FAMILY: &[&str] = &[
    "CLAUDE.md",
    "CONSTRUCTION_STATE.md",
    "crates/holonic-engine/src/algebraic.rs",
    "papers/source/mathematics/definitions/contextual-tangle-compression.typ",
    "papers/source/mathematics/definitions/holonic-process-double-category.typ",
    "papers/source/mathematics/definitions/receiver-configuration-calculus.typ",
    "papers/source/mathematics/definitions/receiver-indexed-holonic-system.typ",
    "research/records/2026-07-26_THE_TUBE_CARRIES_THE_EXTERIOR_FACE_THE_DISTANT_FIELD_RETURNS_THROUGH_REBASE.md",
    "research/records/2026-07-27_THE_CURRENT_CROSSES_THE_LOCAL_FRONT_THE_FRAME_CANNOT_SCHEDULE_THE_EVENT.md",
    "research/records/2026-07-28_THE_PHASE_CARRIES_ACROSS_THE_CELL_THE_SCALAR_RECEIVER_IS_NOT_CLOSED_UNDER_PROPAGATION.md",
    "research/records/2026-07-29_THE_DELIVERY_WORD_IS_GAUGE_THE_CAUSAL_CONFIGURATION_CARRIES_THE_SOURCE_FIBER.md",
    "research/records/2026-07-29_THE_DIFFERENCE_EMITS_THE_PATH_CARRIES_THE_SPECTRUM_IS_THE_RECEIVER_PHASE_FACE.md",
    "research/records/2026-07-29_THE_INFORMANT_CHARGES_THE_GERM_THE_LEADER_RETURNS_THE_RESONANT_COMPONENT.md",
    "research/records/2026-07-29_THE_RECEIVER_IS_NOT_THE_FRAME_THE_PROJECTION_IS_ONLY_A_MEMBRANE.md",
    "research/records/2026-07-29_THE_SUFFIX_DILATES_THE_CONTEXT_THE_EMANATED_BRANCH_RETURNS_AS_CAUSE.md",
    "soma/life/src/synchronized_occurrence.rs",
    "standing/README.md",
];

/// The prompt and depth of the 14,018 measurement, verbatim from the same declared source.
const DECLARED_PROMPT: &str =
    "How does training condition morphology while unresolved uncertainty remains open?";
const DECLARED_TOKENS: usize = 2;

#[derive(Serialize)]
struct Report {
    schema: &'static str,
    corpus_form: String,
    corpus_address: String,
    corpus_occurrences: usize,
    declared_family: Vec<String>,
    family_occurrences: BTreeMap<String, usize>,
    conditioned_passages: usize,
    conditioned_sources: usize,
    prompt: String,
    maximum_observed_tokens: usize,
    conditioning_wall_millis: u128,
    /// **Conditioning's recruitment cost as WORK, not as a clock.** Membership tests attempted
    /// against incidences returned; their ratio is the overpayment.
    recruitment_membership_tests: u64,
    recruitment_incidences: u64,
    recruitment_overpayment_numerator: u64,

    atlas_rows: usize,
    atlas_plural_source_rows: usize,
    declared_minimum_distinct_sources: usize,
    plurality_declared_by: String,
    deposits: usize,
    /// The plurality's own orbit: the same atlas under a caller-declared `1`.
    deposits_under_declared_one: usize,

    complete_fiber_population: usize,
    complete_wall_millis: u128,
    conducted_population: usize,
    conducted_wall_millis: u128,
    conducted_is_strictly_smaller: bool,
    conducted_obstructed_population: usize,
    attached_continuation_population: usize,
    attached_continuations_naming_deposits: usize,

    evaluated_transitions: usize,
    attached_transitions: usize,
    withheld_transitions: usize,
    withheld_candidate_edges: usize,
    obstruction_rows: usize,
    obstructed_withheld_candidates: usize,

    device: String,
    device_launches: u64,
    device_host_parity_checked: bool,
    device_key_words: usize,
    device_deposit_search_comparison_bound: usize,
    host_linear_comparison_cost: usize,

    ablated_target: Option<String>,
    ablated_target_sources: Vec<String>,
    ablated_population: usize,
    /// Deposits that are the sole licence of at least one emitted continuation.
    sole_licence_deposits: usize,
    branches_naming_the_target: usize,
    /// How many of those the target licensed ALONE. Only these can be attributed to it.
    branches_solely_licensed: usize,
    branches_strictly_attributable: usize,
    branches_removed_by_the_ablation: usize,
    /// **Three states, not two.** A boolean here reported `true` when the target solely licensed
    /// nothing, because `0 removed == 0 expected` — a receipt that could not have come out
    /// otherwise, which is `CLAUDE.md` §8's tautology rule firing on this driver's own return. A
    /// vacuous arm says so instead of wearing a pass.
    ablation_receipt: &'static str,

    full_ablation_population: usize,
    full_ablation_restores_enumeration_bit_exactly: bool,
    full_ablation_is_type_state_true: bool,

    findings: Vec<String>,
}

fn main() {
    if let Err(error) = run() {
        eprintln!("REFUSED: {error}");
        std::process::exit(1);
    }
}

struct Arguments {
    corpus_form: PathBuf,
    prompt: String,
    tokens: usize,
    family: Vec<String>,
}

fn arguments() -> Result<Arguments, String> {
    let mut corpus_form = None;
    let mut prompt = DECLARED_PROMPT.to_owned();
    let mut tokens = DECLARED_TOKENS;
    let mut family = DECLARED_FAMILY
        .iter()
        .map(|path| (*path).to_owned())
        .collect::<Vec<_>>();
    let mut arguments = std::env::args().skip(1);
    while let Some(flag) = arguments.next() {
        let value = arguments
            .next()
            .ok_or_else(|| format!("{flag} carries no value"))?;
        match flag.as_str() {
            "--corpus-form" => corpus_form = Some(PathBuf::from(value)),
            "--prompt" => prompt = value,
            "--tokens" => {
                tokens = value
                    .parse()
                    .map_err(|_| format!("--tokens {value} is not a token depth"))?
            }
            "--family" => {
                family = value
                    .split(',')
                    .map(|path| path.trim().to_owned())
                    .filter(|path| !path.is_empty())
                    .collect()
            }
            other => return Err(format!("unknown argument {other}")),
        }
    }
    Ok(Arguments {
        corpus_form: corpus_form
            .ok_or_else(|| "--corpus-form <sealed corpus rest> is required".to_owned())?,
        prompt,
        tokens,
        family,
    })
}

fn run() -> Result<(), String> {
    let arguments = arguments()?;
    if arguments.tokens == 0 {
        return Err("a token depth of zero opens no observation aperture".to_owned());
    }
    let mut findings = Vec::new();

    // --- the sealed corpus, by content address, and the declared family selected from it --------
    let corpus_address = sha256_file(&arguments.corpus_form)?;
    eprintln!(
        "mounting sealed corpus {} ({corpus_address})",
        arguments.corpus_form.display()
    );
    let corpus_file = File::open(&arguments.corpus_form)
        .map_err(|error| format!("open sealed corpus: {error}"))?;
    let atlas = ExactTextMaterialAtlas::from_native_reader(BufReader::new(corpus_file))
        .map_err(|error| format!("mount sealed corpus: {error:?}"))?;
    let corpus_occurrences = atlas.corpus().occurrences().len();
    eprintln!("mounted {corpus_occurrences} occurrences");

    let mut family_occurrences = BTreeMap::new();
    let mut passages = Vec::new();
    for occurrence in atlas.corpus().occurrences() {
        if occurrence.role != TextMaterialRole::Document {
            continue;
        }
        let Some(declared) = arguments.family.iter().find(|declared| {
            occurrence.witnesses.iter().any(|witness| {
                witness.container == **declared || witness.container.ends_with(&format!("/{declared}"))
            })
        }) else {
            continue;
        };
        *family_occurrences.entry(declared.clone()).or_insert(0usize) += 1;
        // **The exterior source is the declared relative path.** The container carries this
        // machine's absolute home directory; folding it into a passage would re-found the
        // convicted absolute frame one organ downstream.
        passages.push(MorphologicalLanguagePassage::new(
            format!("{declared}#{}", occurrence.ordinal),
            declared.clone(),
            occurrence.receiver(),
            occurrence.text.clone(),
        ));
    }
    drop(atlas);
    let absent = arguments
        .family
        .iter()
        .filter(|declared| !family_occurrences.contains_key(*declared))
        .cloned()
        .collect::<Vec<_>>();
    if !absent.is_empty() {
        return Err(format!(
            "the sealed corpus carries no occurrence of {} declared family members: {absent:?}",
            absent.len()
        ));
    }
    let identities = passages
        .iter()
        .map(|passage| passage.identity.as_str())
        .collect::<BTreeSet<_>>();
    if identities.len() != passages.len() {
        return Err("two conditioned passages share one identity".to_owned());
    }
    let conditioned_sources = passages
        .iter()
        .map(|passage| passage.source.as_str())
        .collect::<BTreeSet<_>>()
        .len();
    eprintln!(
        "conditioning {} passages over {conditioned_sources} declared sources",
        passages.len()
    );

    // --- conditioning ---------------------------------------------------------------------------
    let action = ActionCurrent::new(Cog::lit(1)).ok_or_else(|| "action current is dark".to_owned())?;
    let workers = std::thread::available_parallelism()
        .map(|workers| workers.get())
        .unwrap_or(1);
    let conditioning_started = Instant::now();
    let ecology = MorphologicalLanguageEcology::condition(&passages, action, workers)
        .map_err(|error| format!("condition the declared family: {error:?}"))?;
    let conditioning_wall_millis = conditioning_started.elapsed().as_millis();
    let recruitment_membership_tests = ecology.census().recruitment_membership_tests;
    let recruitment_incidences = ecology.census().recruitment_incidences;
    eprintln!(
        "conditioned in {conditioning_wall_millis} ms; recruitment work: \
         {recruitment_membership_tests} membership tests, {recruitment_incidences} incidences"
    );

    // --- the deposits ---------------------------------------------------------------------------
    let atlas = ecology
        .conduct_atlas()
        .map_err(|error| format!("found the conduct atlas: {error:?}"))?;
    let atlas_rows = atlas.rows().len();
    let atlas_plural_source_rows = atlas
        .rows()
        .iter()
        .filter(|row| {
            row.target_sources()
                .iter()
                .map(|(_, source)| source.identity())
                .collect::<BTreeSet<_>>()
                .len()
                >= 2
        })
        .count();
    // THE PLURALITY'S OWN ORBIT. A declared condition that cannot move the deposited population is
    // a parameter in the code and absent from the evidence.
    let declared_one = MorphologicalConductPlurality::declared(
        1,
        "negative control: every material transport conducts, so whatever separates the two arms \
         is the plurality and nothing else",
    )
    .map_err(|error| format!("declare the control plurality: {error}"))?;
    let deposits_under_declared_one = match ecology
        .conduct_atlas()
        .map_err(|error| format!("re-found the conduct atlas: {error:?}"))?
        .into_state(&declared_one)
        .map_err(|error| format!("condense under the control plurality: {error}"))?
    {
        MorphologicalConductState::Conducting(morphology) => morphology.deposit_count(),
        MorphologicalConductState::Unconditioned(_) => 0,
    };

    let plurality = MorphologicalConductPlurality::recurrence_across_two_distinct_wholes();
    let declared_minimum_distinct_sources = plurality.minimum_distinct_sources();
    let plurality_declared_by = plurality.declared_by().to_owned();
    let MorphologicalConductState::Conducting(morphology) = atlas
        .into_state(&plurality)
        .map_err(|error| format!("condense the conduct atlas: {error}"))?
    else {
        return Err(format!(
            "no exact transport in this family returned through {declared_minimum_distinct_sources} \
             distinct sources: {atlas_rows} atlas rows, {atlas_plural_source_rows} plural-source. \
             That is a finding about the material and not a defect of the law; report the counts."
        ));
    };
    let deposits = morphology.deposit_count();
    eprintln!(
        "atlas {atlas_rows} rows, {atlas_plural_source_rows} plural-source, {deposits} deposits \
         (control plurality 1: {deposits_under_declared_one})"
    );

    // --- receipt (a): the complete continuation fiber -------------------------------------------
    let spec = MorphologicalGenerationSpec {
        maximum_observed_tokens: arguments.tokens,
    };
    let cover = HardwareCover::host_only();
    eprintln!("arm (a): the complete continuation fiber");
    let complete_started = Instant::now();
    let complete = ecology
        .generate_currents_over(&arguments.prompt, spec, &cover)
        .map_err(|error| format!("enumerate the complete fiber: {error:?}"))?;
    let complete_wall_millis = complete_started.elapsed().as_millis();
    let complete_fiber_population = complete.outputs.len();
    eprintln!("arm (a): {complete_fiber_population} branches in {complete_wall_millis} ms");

    // --- receipts (b) and (c): the conducted sub-population and the withheld fiber ---------------
    let MorphologicalLanguageConductState::Conducting(conducting) = ecology.receive_conduct(
        MorphologicalConductState::Conducting(morphology),
    ) else {
        return Err("a conducting morphology did not produce a conducting ecology".to_owned());
    };
    let mut executor = CudaMorphologicalConductExecutor::new(0)
        .map_err(|error| format!("mount the conduct card: {error}"))?;
    eprintln!("arm (b): the conducted sub-population on {}", executor.device_name());
    let conducted_started = Instant::now();
    let conducted = conducting
        .generate_currents_over(&arguments.prompt, spec, &cover, &mut executor)
        .map_err(|error| format!("conduct the generation: {error:?}"))?;
    let conducted_wall_millis = conducted_started.elapsed().as_millis();
    let conducted_population = conducted.generation.outputs.len();
    let semantic = conducted.semantic.clone();
    let device_launches = executor.launches();
    let device = executor.device_name().to_owned();
    let device_host_parity_checked = conducted
        .apparatus
        .iter()
        .all(|receipt| receipt.host_parity_checked);
    let device_key_words = conducted
        .apparatus
        .first()
        .map_or(0, |receipt| receipt.key_words);
    let device_deposit_search_comparison_bound = conducted
        .apparatus
        .iter()
        .map(|receipt| receipt.deposit_search_comparison_bound)
        .sum();
    let host_linear_comparison_cost = conducted
        .apparatus
        .iter()
        .map(|receipt| receipt.host_linear_comparison_cost)
        .sum();
    eprintln!(
        "arm (b): {conducted_population} branches in {conducted_wall_millis} ms over \
         {device_launches} launches"
    );

    let conducted_obstructed_population = conducted
        .generation
        .outputs
        .iter()
        .filter(|output| matches!(output.rest, MorphologicalResponseRest::Obstructed { .. }))
        .count();
    let attached_continuation_population = conducted
        .generation
        .outputs
        .iter()
        .filter(|output| output.tokens.iter().any(|token| !token.conducting_supports.is_empty()))
        .count();
    let attached_continuations_naming_deposits = conducted
        .generation
        .outputs
        .iter()
        .filter(|output| {
            output.support_conduct == MorphologicalSupportConduct::Recurred
                && output.supporting_sources >= declared_minimum_distinct_sources
        })
        .count();
    let withheld_candidate_edges = semantic
        .dispositions
        .iter()
        .filter(|disposition| disposition.attached_deposits.is_empty())
        .map(|disposition| disposition.candidate_edges.len())
        .sum::<usize>();
    let obstruction_rows = semantic.obstructions.len();
    let obstructed_withheld_candidates = semantic
        .obstructions
        .iter()
        .map(|obstruction| obstruction.withheld_candidates.len())
        .sum::<usize>();

    let conducted_is_strictly_smaller = conducted_population < complete_fiber_population;
    if !conducted_is_strictly_smaller {
        findings.push(format!(
            "the conducted population is NOT strictly smaller: complete {complete_fiber_population}, \
             conducted {conducted_population}. On this material nothing the deposits refused was \
             reachable, which is a finding about the material and is reported rather than \
             manufactured."
        ));
    }
    report_conduct(&semantic);

    // --- receipt (d): ablate one named deposit, the non-tautological arm ------------------------
    let emitted_by_deposit = deposit_incidence(&conducted.generation);
    // The target is a deposit that SOLELY licenses at least one continuation. Ablating one of
    // several licences removes nothing, which is the law working rather than the ablation failing,
    // so choosing such a target would make the receipt vacuous by construction.
    let mut target = emitted_by_deposit.solely.keys().next().cloned();
    let mut sole_licence_deposits = emitted_by_deposit.solely.len();
    if target.is_none() {
        findings.push(format!(
            "no deposit is the SOLE licence of any emitted continuation ({} deposits appear on some \
             token, none alone), so removing any one of them removes nothing and receipt (d) has no \
             non-vacuous target on this material. That is a finding about the material: every \
             attached transition here stands on plural deposits.",
            emitted_by_deposit.licensed.len()
        ));
        sole_licence_deposits = 0;
        target = emitted_by_deposit.licensed.keys().next().cloned();
    }
    let mut ablated_target = None;
    let mut ablated_target_sources = Vec::new();
    let mut ablated_population = 0usize;
    let mut branches_naming_the_target = 0usize;
    let mut branches_solely_licensed = 0usize;
    let mut branches_strictly_attributable = 0usize;
    let mut branches_removed_by_the_ablation = 0usize;
    let mut ablation_receipt = "the targeted ablation did not fire: no deposit licensed an emitted \
                                continuation";
    let conducted_texts = branch_paths(&conducted.generation);

    let state = if let Some(target) = target {
        branches_naming_the_target = emitted_by_deposit
            .licensed
            .get(&target)
            .map_or(0, multiset_extent);
        // Only the branches this deposit licences ALONE can be attributed to it. With multiplicity:
        // a branch whose twin carries a different licence is not removed by this ablation, and the
        // multiset says so where a set of surfaces cannot.
        let strictly_attributable = emitted_by_deposit
            .solely
            .get(&target)
            .cloned()
            .unwrap_or_default();
        branches_solely_licensed = multiset_extent(&strictly_attributable);
        branches_strictly_attributable = branches_solely_licensed;
        ablated_target = Some(format!("{target:?}"));
        ablated_target_sources = conducting
            .conduct()
            .deposit(&target)
            .map(|deposit| {
                deposit
                    .exterior_sources()
                    .iter()
                    .map(|source| source.identity().to_owned())
                    .collect()
            })
            .unwrap_or_default();
        eprintln!(
            "arm (d): ablating one deposit that licensed {branches_naming_the_target} branches, \
             {branches_solely_licensed} of them alone, {branches_strictly_attributable} strictly \
             attributable"
        );
        let ablation = conducting
            .ablate_target(&target)
            .map_err(|error| format!("ablate the target deposit: {error}"))?;
        match ablation.state {
            MorphologicalLanguageConductState::Conducting(remaining) => {
                let ablated = remaining
                    .generate_currents_over(&arguments.prompt, spec, &cover, &mut executor)
                    .map_err(|error| format!("conduct the ablated generation: {error:?}"))?;
                ablated_population = ablated.generation.outputs.len();
                let ablated_texts = branch_paths(&ablated.generation);
                let removed = multiset_difference(&conducted_texts, &ablated_texts);
                branches_removed_by_the_ablation = multiset_extent(&removed);
                ablation_receipt = if branches_solely_licensed == 0 {
                    "VACUOUS: the target solely licensed nothing, so nothing could be removed and \
                     the arm proves nothing about this material"
                } else if removed == strictly_attributable {
                    "the ablation removed exactly the continuations the target solely licensed"
                } else {
                    "DISAGREED: see findings"
                };
                if branches_solely_licensed > 0 && removed != strictly_attributable {
                    let unexpected = multiset_extent(&multiset_difference(
                        &removed,
                        &strictly_attributable,
                    ));
                    let unremoved = multiset_extent(&multiset_difference(
                        &strictly_attributable,
                        &removed,
                    ));
                    findings.push(format!(
                        "the targeted ablation removed {} branches where exactly {} were solely \
                         licensed by the removed deposit: {unexpected} removed that it did not \
                         solely license, {unremoved} solely licensed that survived",
                        multiset_extent(&removed),
                        multiset_extent(&strictly_attributable),
                    ));
                }
                remaining.ablate_all()
            }
            MorphologicalLanguageConductState::Unconditioned(_) => {
                return Err(
                    "the ablation of one deposit emptied a morphology that carried more".to_owned(),
                )
            }
        }
    } else {
        findings.push(
            "no deposit licensed an emitted continuation, so the targeted ablation had no named \
             target and receipt (d) did not fire"
                .to_owned(),
        );
        conducting.ablate_all()
    };

    // --- receipt (e): full ablation restores the enumeration -------------------------------------
    let restored = state.ecology;
    eprintln!("arm (e): the enumeration after full ablation");
    let full = restored
        .generate_currents_over(&arguments.prompt, spec, &cover)
        .map_err(|error| format!("re-enumerate after full ablation: {error:?}"))?;
    let full_ablation_population = full.outputs.len();
    let full_ablation_restores_enumeration_bit_exactly = full.outputs == complete.outputs;
    if !full_ablation_restores_enumeration_bit_exactly {
        findings.push(format!(
            "full ablation returned {full_ablation_population} branches against the control's \
             {complete_fiber_population}, and they are not bit-identical: the conducted pass \
             mutated the ecology it borrowed"
        ));
    }
    findings.push(
        "receipt (e) is true by type-state: `ablate_all` consumes the conduct morphology and \
         returns the plain ecology, so the complete arm could not have returned anything else. \
         What it establishes is that the conducted pass did not mutate the ecology it borrowed. \
         Receipt (d) is the ablation that can fail."
            .to_owned(),
    );

    let report = Report {
        schema: REPORT_SCHEMA,
        corpus_form: arguments.corpus_form.display().to_string(),
        corpus_address,
        corpus_occurrences,
        declared_family: arguments.family.clone(),
        family_occurrences,
        conditioned_passages: passages.len(),
        conditioned_sources,
        prompt: arguments.prompt.clone(),
        maximum_observed_tokens: arguments.tokens,
        conditioning_wall_millis,
        recruitment_membership_tests,
        recruitment_incidences,
        recruitment_overpayment_numerator: recruitment_membership_tests
            .saturating_sub(recruitment_incidences),
        atlas_rows,
        atlas_plural_source_rows,
        declared_minimum_distinct_sources,
        plurality_declared_by,
        deposits,
        deposits_under_declared_one,
        complete_fiber_population,
        complete_wall_millis,
        conducted_population,
        conducted_wall_millis,
        conducted_is_strictly_smaller,
        conducted_obstructed_population,
        attached_continuation_population,
        attached_continuations_naming_deposits,
        evaluated_transitions: semantic.evaluated_transitions,
        attached_transitions: semantic.attached_transitions,
        withheld_transitions: semantic.withheld_transitions,
        withheld_candidate_edges,
        obstruction_rows,
        obstructed_withheld_candidates,
        device,
        device_launches,
        device_host_parity_checked,
        device_key_words,
        device_deposit_search_comparison_bound,
        host_linear_comparison_cost,
        ablated_target,
        ablated_target_sources,
        ablated_population,
        sole_licence_deposits,
        branches_naming_the_target,
        branches_solely_licensed,
        branches_strictly_attributable,
        branches_removed_by_the_ablation,
        ablation_receipt,
        full_ablation_population,
        full_ablation_restores_enumeration_bit_exactly,
        full_ablation_is_type_state_true: true,
        findings,
    };
    let octets = serde_json::to_vec_pretty(&report)
        .map_err(|error| format!("encode the grade: {error}"))?;
    let deposited = deposit_form_or_message(DRIVER, GRADE_FORM, &octets)?;
    println!("{}", String::from_utf8_lossy(&octets));
    println!("grade deposited at {}", deposited.path.display());
    Ok(())
}

/// **Which branch paths each deposit licensed, and which it licensed ALONE.**
///
/// The distinction is the whole of receipt (d) and getting it wrong makes the receipt fail for the
/// wrong reason. A transition attaches when *any* deposited support attaches it, so a continuation
/// standing on three deposits survives the removal of one — correctly, and by the same law that
/// makes it conduct at all. The removal test therefore has to name the continuations for which the
/// target is the **sole** licence; those are the ones whose loss is attributable to it.
///
/// `licensed` is every path in which the deposit appears on some token. `solely` is every path with
/// a token whose complete attached set is exactly that one deposit.
struct DepositIncidence {
    licensed: BTreeMap<MorphologicalConductEdgeAddress, BranchPaths>,
    solely: BTreeMap<MorphologicalConductEdgeAddress, BranchPaths>,
}

fn deposit_incidence(generation: &MorphologicalLanguageCurrentGeneration) -> DepositIncidence {
    let mut licensed: BTreeMap<_, BranchPaths> = BTreeMap::new();
    let mut solely: BTreeMap<_, BranchPaths> = BTreeMap::new();
    for output in &generation.outputs {
        let path = branch_path(output);
        let named = output
            .tokens
            .iter()
            .flat_map(|token| token.conducting_supports.iter().cloned())
            .collect::<BTreeSet<_>>();
        let sole = output
            .tokens
            .iter()
            .filter(|token| token.conducting_supports.len() == 1)
            .flat_map(|token| token.conducting_supports.iter().cloned())
            .collect::<BTreeSet<_>>();
        for edge in named {
            *licensed
                .entry(edge)
                .or_default()
                .entry(path.clone())
                .or_insert(0) += 1;
        }
        for edge in sole {
            *solely
                .entry(edge)
                .or_default()
                .entry(path.clone())
                .or_insert(0) += 1;
        }
    }
    DepositIncidence { licensed, solely }
}

fn branch_path(output: &MorphologicalGeneratedCurrent) -> Vec<String> {
    output
        .tokens
        .iter()
        .map(|token| format!("{}|{:?}", token.token, token.transport))
        .collect()
}

/// **The returned branches as a MULTISET of emitted paths, because a path is not a branch.**
///
/// Two distinct currents can emit the same surface sequence, so comparing sets of paths hides a
/// removal: the first ablation measured a population falling 24 to 23 while reporting zero paths
/// removed, because the removed branch's twin was still there. Counting multiplicity is the exact
/// measure, and it is the one receipt (d) needs.
type BranchPaths = BTreeMap<Vec<String>, usize>;

fn branch_paths(generation: &MorphologicalLanguageCurrentGeneration) -> BranchPaths {
    let mut paths = BranchPaths::new();
    for output in &generation.outputs {
        *paths.entry(branch_path(output)).or_insert(0) += 1;
    }
    paths
}

/// What the left multiset carries that the right one does not, with multiplicity.
fn multiset_difference(left: &BranchPaths, right: &BranchPaths) -> BranchPaths {
    let mut difference = BranchPaths::new();
    for (path, carried) in left {
        let remaining = carried.saturating_sub(right.get(path).copied().unwrap_or(0));
        if remaining > 0 {
            difference.insert(path.clone(), remaining);
        }
    }
    difference
}

fn multiset_extent(paths: &BranchPaths) -> usize {
    paths.values().sum()
}

fn report_conduct(semantic: &MorphologicalConductGenerationReceipt) {
    eprintln!(
        "conduct: evaluated {} attached {} withheld {} obstructions {}",
        semantic.evaluated_transitions,
        semantic.attached_transitions,
        semantic.withheld_transitions,
        semantic.obstructions.len()
    );
}

fn sha256_file(path: &Path) -> Result<String, String> {
    use std::io::Read;

    use sha2::{Digest, Sha256};
    let mut reader =
        BufReader::new(File::open(path).map_err(|error| format!("open {}: {error}", path.display()))?);
    let mut hasher = Sha256::new();
    let mut window = vec![0u8; 1 << 20];
    loop {
        let read = reader
            .read(&mut window)
            .map_err(|error| format!("read {}: {error}", path.display()))?;
        if read == 0 {
            break;
        }
        hasher.update(&window[..read]);
    }
    Ok(hasher
        .finalize()
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect())
}
