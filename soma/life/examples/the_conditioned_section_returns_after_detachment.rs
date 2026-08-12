//! Record: research/records/2026-08-12_THE_RECURRENT_LAW_CROSSES_THE_CORPUS_DEPARTURE_THE_UNSEEN_SECTION_RIDES_ITS_DEPOSIT.md
//! Return 4: recurrent transformation conduct survives source detachment and answers unseen states.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs::File,
    io::BufReader,
    path::{Path, PathBuf},
};

use body::num::Cog;
use holonic_engine::cuda_refine::CudaRefineExecutor;
use life::{
    causal_section::{CausalSectionEcology, CausalSectionReading, SectionSeparator},
    form_mouth::deposit_form_or_message,
    morphological_language::{
        card_key, CudaMorphologicalConditioner, CudaMorphologicalConductExecutor,
        MorphologicalConditionSemanticReceipt, MorphologicalConductEdgeAddress,
        MorphologicalConductPlurality, MorphologicalLanguageEcology, MorphologicalLanguagePassage,
    },
    recurrent_section::{
        PresentedSectionState, RecurrentSectionFormationReceipt, RecurrentSectionMorphology,
        ReturnedTransformationLaw, SectionMorphologyWitness, SectionPresentation,
    },
    recurrent_section_cuda::{
        BiaffineSampleGrid, CudaRecurrentLawExecutor, RecurrentLawCudaReceipt,
    },
    text_material::{ExactTextMaterialAtlas, TextMaterialRole},
};
use serde::Serialize;
use soma_abi::active::ActionCurrent;

const DRIVER: &str = "the_conditioned_section_returns_after_detachment";
const REST_FORM: &str = "recurrent-section-native-rest";
const GRADE_FORM: &str = "recurrent-section-return-grade";
const SCHEMA: &str = "soma-life.conditioned-section-return.v2";

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
    "soma/life/src/morphological_language.rs",
];

#[derive(Clone, Copy)]
enum ExteriorLaw {
    Sum,
    Product,
    Difference,
    ReverseDifference,
}

impl ExteriorLaw {
    const fn enact(self, left: i64, right: i64) -> i64 {
        match self {
            Self::Sum => left + right,
            Self::Product => left * right,
            Self::Difference => left - right,
            Self::ReverseDifference => right - left,
        }
    }
}

#[derive(Clone)]
struct PresentationDeclaration {
    identity: &'static str,
    lineage: &'static str,
    incidence: [&'static str; 3],
    contact_faces: [&'static str; 2],
    exposure: &'static str,
    law: ExteriorLaw,
}

#[derive(Clone, Debug, Serialize)]
struct ConditioningApparatus {
    device: String,
    suffix_launches: u64,
    prefix_launches: u64,
    route_launches: u64,
    route_contact_launches: u64,
    resident_words: u64,
}

#[derive(Serialize)]
struct ConditioningReceipt {
    corpus_occurrences: usize,
    corpus_passages: usize,
    carrier_passages: usize,
    total_passages: usize,
    total_sources: usize,
    conduct_atlas_rows: usize,
    section_witness_rows: BTreeMap<String, usize>,
    founded_laws: usize,
    distinct_founded_laws: usize,
    semantic: MorphologicalConditionSemanticReceipt,
    conditioner_apparatus: ConditioningApparatus,
    law_foundation_apparatus: RecurrentLawCudaReceipt,
}

#[derive(Serialize)]
struct SourceAccessAudit {
    rest_octets: usize,
    corpus_octets: usize,
    schema_source_occurrence_fields: usize,
    schema_source_path_fields: usize,
    schema_section_identity_fields: usize,
    schema_sample_coordinate_fields: usize,
    schema_sample_answer_fields: usize,
    declared_paths_found_in_rest: Vec<String>,
    presentation_identities_found_in_rest: Vec<String>,
    complete_corpus_passages_found_in_rest: usize,
    founding_atlas_dropped_before_remount: bool,
    founding_morphology_dropped_before_remount: bool,
    founding_law_executor_dropped_before_remount: bool,
}

struct SealedReturn {
    rest: Vec<u8>,
    presentation_witnesses: BTreeMap<String, SectionMorphologyWitness>,
    conditioning: ConditioningReceipt,
    audit: SourceAccessAudit,
}

#[derive(Serialize)]
struct SeparatorReceipt {
    left: String,
    right: String,
    interventions: Vec<String>,
    receiver: Option<String>,
    left_observation: Option<String>,
    right_observation: Option<String>,
    separated_by_terminus: bool,
}

#[derive(Serialize)]
struct CausalProfile {
    label: &'static str,
    root_conduct_blocks: Vec<BTreeSet<String>>,
    reconstruction_fibers: Vec<BTreeSet<String>>,
    deposited_conducts: usize,
    active_conducts: usize,
    distinct_transformation_laws: usize,
    riding_state_laws: usize,
    causal_front_distribution: BTreeMap<usize, usize>,
    interaction_arity_distribution: BTreeMap<usize, usize>,
    phase_current_distribution: BTreeMap<usize, usize>,
    mixed_phase_distribution: BTreeMap<i64, usize>,
    reconvergent_diamonds: usize,
    flat_reconvergent_diamonds: usize,
    shortest_interventions: Vec<SeparatorReceipt>,
    open_state_population: usize,
}

#[derive(Serialize)]
struct ApparatusReceipt {
    conditioner: ConditioningApparatus,
    law_foundation_device: String,
    law_foundation_launches: u64,
    attachment_device: String,
    attachment_launches: u64,
    law_evaluation_device: String,
    law_evaluation_launches: u64,
    quotient_device: String,
    quotient_launches: u64,
    quotient_threads_per_block: u32,
    host_semantic_replay: bool,
}

#[derive(Serialize)]
struct GradeReceipt {
    schema: &'static str,
    corpus_form: String,
    rest_form: String,
    rest_address: String,
    rest_round_trip_exact: bool,
    conditioning: ConditioningReceipt,
    source_access_audit: SourceAccessAudit,
    founding_coordinates: Vec<[i64; 2]>,
    later_coordinates: Vec<[i64; 2]>,
    founding_later_coordinate_overlap: usize,
    unseen_consequences_exact: bool,
    before: CausalProfile,
    after: CausalProfile,
    value_receiver_ablated_blocks: Vec<BTreeSet<String>>,
    same_operation_cross_codec_fiber: BTreeSet<String>,
    same_value_different_law_separator: Vec<String>,
    reversed_port_separator: Vec<String>,
    targeted_ablation: String,
    target_became_open: bool,
    unrelated_sections_bit_identical: bool,
    attributable_fiber_before: BTreeSet<String>,
    attributable_fiber_after: BTreeSet<String>,
    scale_restriction: BTreeSet<String>,
    scale_rebased_blocks: Vec<BTreeSet<String>>,
    scale_rebase_agrees_with_full_intersection: bool,
    critical_receiver_was_value: bool,
    caustic_pair_population: usize,
    selected_reconstruction_representative: Option<String>,
    outside_declared_population: &'static str,
    apparatus: ApparatusReceipt,
}

fn main() {
    if let Err(error) = run() {
        eprintln!("REFUSED: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let corpus_form = argument()?;
    eprintln!("conditioning and sealing from {}", corpus_form.display());
    let sealed = condition_and_seal(&corpus_form)?;
    let rest_form = deposit_form_or_message(DRIVER, REST_FORM, &sealed.rest)?;

    // Detachment: no corpus atlas, conditioner, conduct atlas, sample coordinate, sample answer,
    // or founding-law executor crosses this point. The witness map is explicitly the later
    // presentation's anonymous contact face: it contains the exact material keys by which that
    // occurrence meets the deposit, but no source identity, coordinate, consequence, or law.
    let remounted = RecurrentSectionMorphology::decode_native_bytes(&sealed.rest)?;
    let rest_round_trip_exact = remounted.encode_native_bytes()? == sealed.rest;
    if !rest_round_trip_exact
        || !sealed.audit.declared_paths_found_in_rest.is_empty()
        || !sealed
            .audit
            .presentation_identities_found_in_rest
            .is_empty()
        || sealed.audit.complete_corpus_passages_found_in_rest != 0
    {
        return Err("the recurrent-law rest failed source detachment or exact remount".to_owned());
    }
    let declarations = declarations();
    let presentations = later_presentations(&declarations, &sealed.presentation_witnesses)?;

    let mut conduct_card = CudaMorphologicalConductExecutor::new(0)
        .map_err(|error| format!("mount recurrent-section conduct card: {error}"))?;
    let mut law_card = CudaRecurrentLawExecutor::new(0)?;
    let attachment_before = conduct_card.launches();
    let evaluation_before = law_card.launches();
    let before_formation =
        remounted.form_unconditioned_sections(&presentations, &mut conduct_card, &mut law_card)?;
    let after_formation =
        remounted.form_sections(&presentations, &mut conduct_card, &mut law_card)?;
    let target_witness = &presentations
        .iter()
        .find(|presentation| presentation.identity == "infix-sum")
        .ok_or_else(|| "the targeted presentation departed".to_owned())?
        .witness;
    let targeted_formation = remounted.form_without_witness(
        &presentations,
        target_witness,
        &mut conduct_card,
        &mut law_card,
    )?;
    let scale_restriction = BTreeSet::from([
        "infix-sum".to_owned(),
        "call-sum".to_owned(),
        "word-sum".to_owned(),
        "infix-product".to_owned(),
        "call-product".to_owned(),
    ]);
    let restricted_presentations = presentations
        .iter()
        .filter(|presentation| scale_restriction.contains(&presentation.identity))
        .cloned()
        .collect::<Vec<_>>();
    let restricted_formation =
        remounted.form_sections(&restricted_presentations, &mut conduct_card, &mut law_card)?;
    let attachment_launches = conduct_card.launches() - attachment_before;
    let law_evaluation_launches = law_card.launches() - evaluation_before;

    let mut quotient_card = CudaRefineExecutor::new().map_err(|error| error.to_string())?;
    let quotient_before = quotient_card.launches();
    let before_receipt = before_formation.receipt;
    let before_reading = CausalSectionEcology::found(before_formation.sections)
        .map_err(|error| error.to_string())?
        .read(&mut quotient_card)
        .map_err(|error| error.to_string())?;
    let after_receipt = after_formation.receipt;
    let unseen_consequences_exact = verify_later_return(&declarations, &after_receipt)?;
    let after_ecology =
        CausalSectionEcology::found(after_formation.sections).map_err(|error| error.to_string())?;
    let after_reading = after_ecology
        .read(&mut quotient_card)
        .map_err(|error| error.to_string())?;
    let value_ablated = after_ecology
        .read_without("value", &mut quotient_card)
        .map_err(|error| error.to_string())?;
    let targeted_receipt = targeted_formation.receipt;
    let targeted_reading = CausalSectionEcology::found(targeted_formation.sections)
        .map_err(|error| error.to_string())?
        .read(&mut quotient_card)
        .map_err(|error| error.to_string())?;
    let restricted_reading = CausalSectionEcology::found(restricted_formation.sections)
        .map_err(|error| error.to_string())?
        .read(&mut quotient_card)
        .map_err(|error| error.to_string())?;
    let quotient_launches = quotient_card.launches() - quotient_before;

    let sum_fiber = block_containing(
        &after_reading.root_conduct_blocks,
        &["infix-sum", "call-sum", "word-sum"],
    )?;
    let sum_product = separator_between(&after_reading, "infix-sum", "infix-product")?;
    let reversed = separator_between(&after_reading, "difference", "reverse-difference")?;
    if sum_product.interventions != ["raise-left"] || reversed.interventions != ["raise-left"] {
        return Err("an unseen same-value control lost its shortest intervention".to_owned());
    }
    let attributable_after = targeted_reading
        .root_conduct_blocks
        .iter()
        .find(|block| block.contains("call-sum") && block.contains("word-sum"))
        .cloned()
        .ok_or_else(|| "the ablated sum fiber lost unrelated presentations".to_owned())?;
    let target_became_open = targeted_receipt
        .readings
        .iter()
        .find(|reading| reading.identity == "infix-sum")
        .is_some_and(|reading| reading.states.iter().all(|state| state.open));
    let unrelated_sections_bit_identical = after_receipt
        .readings
        .iter()
        .filter(|reading| reading.identity != "infix-sum")
        .all(|reading| {
            targeted_receipt
                .readings
                .iter()
                .find(|candidate| candidate.identity == reading.identity)
                == Some(reading)
        });
    if !target_became_open || !unrelated_sections_bit_identical {
        return Err("the targeted recurrent-law ablation was not exact".to_owned());
    }
    let expected_restricted = after_reading
        .root_conduct_blocks
        .iter()
        .filter_map(|block| {
            let intersection = block
                .intersection(&scale_restriction)
                .cloned()
                .collect::<BTreeSet<_>>();
            (!intersection.is_empty()).then_some(intersection)
        })
        .collect::<Vec<_>>();
    let scale_rebase_agrees_with_full_intersection =
        canonical_blocks(&restricted_reading.root_conduct_blocks)
            == canonical_blocks(&expected_restricted);
    let critical_receiver_was_value = value_ablated.root_conduct_blocks.len() == 1;
    if !scale_rebase_agrees_with_full_intersection
        || !critical_receiver_was_value
        || !unseen_consequences_exact
    {
        return Err(
            "the unseen return, scale rebase, or critical receiver control fired".to_owned(),
        );
    }

    let caustic_pair_population = split_pair_population(
        &before_reading.root_conduct_blocks,
        &after_reading.root_conduct_blocks,
    );
    let before_profile = profile("before-conditioning", &before_reading, &before_receipt);
    let after_profile = profile("after-remount", &after_reading, &after_receipt);
    let apparatus = ApparatusReceipt {
        conditioner: sealed.conditioning.conditioner_apparatus.clone(),
        law_foundation_device: sealed.conditioning.law_foundation_apparatus.device.clone(),
        law_foundation_launches: sealed.conditioning.law_foundation_apparatus.launch_ordinal,
        attachment_device: after_receipt.attachment_apparatus.device.clone(),
        attachment_launches,
        law_evaluation_device: law_card.device_name().to_owned(),
        law_evaluation_launches,
        quotient_device: quotient_card.device_name().to_owned(),
        quotient_launches,
        quotient_threads_per_block: quotient_card.block_threads(),
        host_semantic_replay: false,
    };
    let founding_coordinates = vec![[2, 2], [3, 2], [2, 3], [3, 3]];
    let later_coordinates = vec![[0, 0], [1, 0], [0, 1], [1, 1]];
    let founding_later_coordinate_overlap = founding_coordinates
        .iter()
        .filter(|coordinate| later_coordinates.contains(coordinate))
        .count();
    let grade = GradeReceipt {
        schema: SCHEMA,
        corpus_form: corpus_form.display().to_string(),
        rest_form: rest_form.path.display().to_string(),
        rest_address: rest_form.address.clone(),
        rest_round_trip_exact,
        conditioning: sealed.conditioning,
        source_access_audit: sealed.audit,
        founding_coordinates,
        later_coordinates,
        founding_later_coordinate_overlap,
        unseen_consequences_exact,
        before: before_profile,
        after: after_profile,
        value_receiver_ablated_blocks: value_ablated.root_conduct_blocks,
        same_operation_cross_codec_fiber: sum_fiber.clone(),
        same_value_different_law_separator: sum_product.interventions.clone(),
        reversed_port_separator: reversed.interventions.clone(),
        targeted_ablation: "infix-sum".to_owned(),
        target_became_open,
        unrelated_sections_bit_identical,
        attributable_fiber_before: sum_fiber,
        attributable_fiber_after: attributable_after,
        scale_restriction,
        scale_rebased_blocks: restricted_reading.root_conduct_blocks,
        scale_rebase_agrees_with_full_intersection,
        critical_receiver_was_value,
        caustic_pair_population,
        selected_reconstruction_representative: None,
        outside_declared_population: "OPEN",
        apparatus,
    };
    let octets = serde_json::to_vec_pretty(&grade).map_err(|error| error.to_string())?;
    let grade_form = deposit_form_or_message(DRIVER, GRADE_FORM, &octets)?;

    println!("THE CONDITIONED SECTION RETURNS AFTER DETACHMENT");
    println!("  rest round trip       EXACT");
    println!("  source/sample access  NONE");
    println!("  unseen coordinates    4/4 exact");
    println!(
        "  before blocks         {:?}",
        block_shape(&grade.before.root_conduct_blocks)
    );
    println!(
        "  after blocks          {:?}",
        block_shape(&grade.after.root_conduct_blocks)
    );
    println!(
        "  sum fiber             {:?}",
        grade.same_operation_cross_codec_fiber
    );
    println!(
        "  sum/product           {:?}",
        grade.same_value_different_law_separator
    );
    println!(
        "  reverse hand          {:?}",
        grade.reversed_port_separator
    );
    println!(
        "  mixed phases          {:?}",
        grade.after.mixed_phase_distribution
    );
    println!("  caustic pairs         {}", grade.caustic_pair_population);
    println!(
        "  diamonds              {} flat",
        grade.after.flat_reconvergent_diamonds
    );
    println!("  target ablation       exact; unrelated bit-identical");
    println!("  scale rebase          exact intersection");
    println!("  selected representative NONE");
    println!("  outside               OPEN");
    println!(
        "  device attachment     {} launches",
        grade.apparatus.attachment_launches
    );
    println!(
        "  device law            {} + {} launches",
        grade.apparatus.law_foundation_launches, grade.apparatus.law_evaluation_launches
    );
    println!(
        "  device quotient       {} launches",
        grade.apparatus.quotient_launches
    );
    println!("  rest                   {}", rest_form.path.display());
    println!("  grade                  {}", grade_form.path.display());
    Ok(())
}

fn argument() -> Result<PathBuf, String> {
    let mut arguments = std::env::args().skip(1);
    let mut corpus_form = None;
    while let Some(flag) = arguments.next() {
        let value = arguments
            .next()
            .ok_or_else(|| format!("{flag} carries no value"))?;
        match flag.as_str() {
            "--corpus-form" => corpus_form = Some(PathBuf::from(value)),
            other => return Err(format!("unknown argument {other}")),
        }
    }
    corpus_form.ok_or_else(|| "--corpus-form <sealed native corpus rest> is required".to_owned())
}

fn condition_and_seal(path: &Path) -> Result<SealedReturn, String> {
    let file = File::open(path).map_err(|error| format!("open sealed corpus: {error}"))?;
    let atlas = ExactTextMaterialAtlas::from_native_reader(BufReader::new(file))
        .map_err(|error| format!("mount sealed corpus: {error:?}"))?;
    let corpus_occurrences = atlas.corpus().occurrences().len();
    let mut passages = Vec::new();
    let mut corpus_bodies = Vec::new();
    let mut found_family = BTreeSet::new();
    for occurrence in atlas.corpus().occurrences() {
        if occurrence.role != TextMaterialRole::Document {
            continue;
        }
        let Some(declared) = DECLARED_FAMILY.iter().find(|declared| {
            occurrence.witnesses.iter().any(|witness| {
                witness.container == **declared
                    || witness.container.ends_with(&format!("/{declared}"))
            })
        }) else {
            continue;
        };
        found_family.insert((*declared).to_owned());
        corpus_bodies.push(occurrence.text.as_bytes().to_vec());
        passages.push(MorphologicalLanguagePassage::new(
            format!("{declared}#{}", occurrence.ordinal),
            (*declared).to_owned(),
            occurrence.receiver(),
            occurrence.text.clone(),
        ));
    }
    drop(atlas);
    if found_family.len() != DECLARED_FAMILY.len() {
        return Err("the sealed corpus does not carry the complete declared family".to_owned());
    }
    let corpus_passages = passages.len();
    let corpus_octets = corpus_bodies.iter().map(Vec::len).sum();
    let declarations = declarations();
    let mut section_sources = BTreeMap::<String, BTreeSet<String>>::new();
    for declaration in &declarations {
        for delivery in ["alpha", "beta"] {
            let source = format!("return-4/{}/{delivery}", declaration.identity);
            section_sources
                .entry(declaration.identity.to_owned())
                .or_default()
                .insert(source.clone());
            passages.push(MorphologicalLanguagePassage::new(
                format!("{source}#0"),
                source,
                0,
                declaration.exposure,
            ));
        }
    }
    let carrier_passages = declarations.len() * 2;
    let total_sources = passages
        .iter()
        .map(|passage| passage.source.as_str())
        .collect::<BTreeSet<_>>()
        .len();
    let total_passages = passages.len();
    let action =
        ActionCurrent::new(Cog::lit(1)).ok_or_else(|| "action current is dark".to_owned())?;
    let mut conditioner = CudaMorphologicalConditioner::new(0)
        .map_err(|error| format!("mount resident conditioner: {error}"))?;
    let (ecology, semantic, device) =
        MorphologicalLanguageEcology::condition_with_cuda(&passages, action, &mut conditioner)
            .map_err(|error| format!("condition mixed corpus: {error:?}"))?;
    let conduct_atlas = ecology
        .conduct_atlas()
        .map_err(|error| format!("found conduct atlas: {error:?}"))?;
    let conduct_atlas_rows = conduct_atlas.rows().len();
    let mut section_edges = BTreeMap::<String, Vec<MorphologicalConductEdgeAddress>>::new();
    for declaration in &declarations {
        let sources = &section_sources[declaration.identity];
        let edges = conduct_atlas
            .rows()
            .iter()
            .filter(|row| {
                let row_sources = row
                    .target_sources()
                    .iter()
                    .map(|(_, source)| source.identity())
                    .collect::<BTreeSet<_>>();
                sources
                    .iter()
                    .all(|source| row_sources.contains(source.as_str()))
            })
            .map(|row| row.edge().clone())
            .collect::<Vec<_>>();
        if edges.is_empty() {
            return Err(format!(
                "section {} founded no recurring material transport",
                declaration.identity
            ));
        }
        section_edges.insert(declaration.identity.to_owned(), edges);
    }
    let identity_words = section_edges
        .values()
        .flatten()
        .map(MorphologicalConductEdgeAddress::identity_word_extent)
        .max()
        .ok_or_else(|| "the recurrent section has no device identity width".to_owned())?;
    let section_witness_rows = section_edges
        .iter()
        .map(|(identity, edges)| (identity.clone(), edges.len()))
        .collect();
    let plurality = MorphologicalConductPlurality::recurrence_across_two_distinct_wholes();
    let deposits = match conduct_atlas
        .into_state(&plurality)
        .map_err(|error| format!("condense device-founded conduct: {error}"))?
    {
        life::morphological_language::MorphologicalConductState::Conducting(morphology) => {
            morphology
        }
        life::morphological_language::MorphologicalConductState::Unconditioned(_) => {
            return Err("the mixed corpus founded no recurrent conduct".to_owned())
        }
    };
    for edges in section_edges.values() {
        if edges.iter().any(|edge| deposits.deposit(edge).is_none()) {
            return Err("a presentation witness did not survive the declared plurality".to_owned());
        }
    }
    let mut presentation_witnesses = BTreeMap::new();
    let mut returned = Vec::new();
    for declaration in &declarations {
        let mut keys = section_edges[declaration.identity]
            .iter()
            .map(|edge| {
                card_key(edge, identity_words)
                    .map(|key| key.as_ref().to_vec())
                    .map_err(|error| format!("encode section conduct witness: {error}"))
            })
            .collect::<Result<Vec<_>, _>>()?;
        keys.sort();
        keys.dedup();
        let key_words = keys.first().map(Vec::len).unwrap();
        let witness = SectionMorphologyWitness::new(key_words, keys, 2)?;
        presentation_witnesses.insert(declaration.identity.to_owned(), witness.clone());
        returned.push(ReturnedTransformationLaw {
            witness,
            samples: BiaffineSampleGrid {
                x0: 2,
                x1: 3,
                y0: 2,
                y1: 3,
                values: [
                    declaration.law.enact(2, 2),
                    declaration.law.enact(3, 2),
                    declaration.law.enact(2, 3),
                    declaration.law.enact(3, 3),
                ],
            },
        });
    }
    drop(deposits);
    drop(ecology);
    drop(passages);
    let mut law_executor = CudaRecurrentLawExecutor::new(0)?;
    let (recurrent, law_foundation_apparatus) =
        RecurrentSectionMorphology::found(returned, &mut law_executor)?;
    let founded_laws = recurrent.deposited_conducts();
    let distinct_founded_laws = recurrent.distinct_transformation_laws();
    let rest = recurrent.encode_native_bytes()?;
    drop(recurrent);
    drop(law_executor);
    let declared_paths_found_in_rest = DECLARED_FAMILY
        .iter()
        .filter(|path| contains(&rest, path.as_bytes()))
        .map(|path| (*path).to_owned())
        .collect::<Vec<_>>();
    let presentation_identities_found_in_rest = declarations
        .iter()
        .filter(|declaration| contains(&rest, declaration.identity.as_bytes()))
        .map(|declaration| declaration.identity.to_owned())
        .collect::<Vec<_>>();
    let complete_corpus_passages_found_in_rest = corpus_bodies
        .iter()
        .filter(|body| !body.is_empty() && contains(&rest, body))
        .count();
    let audit = SourceAccessAudit {
        rest_octets: rest.len(),
        corpus_octets,
        schema_source_occurrence_fields: 0,
        schema_source_path_fields: 0,
        schema_section_identity_fields: 0,
        schema_sample_coordinate_fields: 0,
        schema_sample_answer_fields: 0,
        declared_paths_found_in_rest,
        presentation_identities_found_in_rest,
        complete_corpus_passages_found_in_rest,
        founding_atlas_dropped_before_remount: true,
        founding_morphology_dropped_before_remount: true,
        founding_law_executor_dropped_before_remount: true,
    };
    Ok(SealedReturn {
        rest,
        presentation_witnesses,
        conditioning: ConditioningReceipt {
            corpus_occurrences,
            corpus_passages,
            carrier_passages,
            total_passages,
            total_sources,
            conduct_atlas_rows,
            section_witness_rows,
            founded_laws,
            distinct_founded_laws,
            semantic,
            conditioner_apparatus: ConditioningApparatus {
                device: device.device_name,
                suffix_launches: device.suffix_launches,
                prefix_launches: device.prefix_launches,
                route_launches: device.route_launches,
                route_contact_launches: device.route_contact_launches,
                resident_words: device.resident_words,
            },
            law_foundation_apparatus,
        },
        audit,
    })
}

fn declarations() -> Vec<PresentationDeclaration> {
    vec![
        PresentationDeclaration {
            identity: "infix-sum",
            lineage: "symbolic-infix",
            incidence: ["left", "plus", "right"],
            contact_faces: ["left-operand", "right-operand"],
            exposure: "2 + 2 ; 3 + 2 ; 2 + 3 ; 3 + 3",
            law: ExteriorLaw::Sum,
        },
        PresentationDeclaration {
            identity: "call-sum",
            lineage: "function-call",
            incidence: ["add", "left", "right"],
            contact_faces: ["callee-argument", "argument-order"],
            exposure: "add(2, 2); add(3, 2); add(2, 3); add(3, 3)",
            law: ExteriorLaw::Sum,
        },
        PresentationDeclaration {
            identity: "word-sum",
            lineage: "word-presentation",
            incidence: ["sum", "first", "second"],
            contact_faces: ["word-landmark", "word-landmark"],
            exposure: "two plus two ; three plus two ; two plus three ; three plus three",
            law: ExteriorLaw::Sum,
        },
        PresentationDeclaration {
            identity: "infix-product",
            lineage: "symbolic-infix",
            incidence: ["left", "times", "right"],
            contact_faces: ["factor", "factor"],
            exposure: "2 * 2 ; 3 * 2 ; 2 * 3 ; 3 * 3",
            law: ExteriorLaw::Product,
        },
        PresentationDeclaration {
            identity: "call-product",
            lineage: "function-call",
            incidence: ["multiply", "left", "right"],
            contact_faces: ["callee-argument", "argument-order"],
            exposure: "multiply(2, 2); multiply(3, 2); multiply(2, 3); multiply(3, 3)",
            law: ExteriorLaw::Product,
        },
        PresentationDeclaration {
            identity: "difference",
            lineage: "ordered-infix",
            incidence: ["left", "minus", "right"],
            contact_faces: ["minuend", "subtrahend"],
            exposure: "2 - 2 ; 3 - 2 ; 2 - 3 ; 3 - 3",
            law: ExteriorLaw::Difference,
        },
        PresentationDeclaration {
            identity: "reverse-difference",
            lineage: "reversed-port-control",
            incidence: ["right", "minus", "left"],
            contact_faces: ["subtrahend", "minuend"],
            exposure:
                "2 reverse-minus 2 ; 3 reverse-minus 2 ; 2 reverse-minus 3 ; 3 reverse-minus 3",
            law: ExteriorLaw::ReverseDifference,
        },
    ]
}

fn later_presentations(
    declarations: &[PresentationDeclaration],
    witnesses: &BTreeMap<String, SectionMorphologyWitness>,
) -> Result<Vec<SectionPresentation>, String> {
    let coordinates = [[0, 0], [1, 0], [0, 1], [1, 1]];
    declarations
        .iter()
        .map(|declaration| {
            Ok(SectionPresentation {
                identity: declaration.identity.to_owned(),
                lineage: declaration.lineage.to_owned(),
                incidence_text: declaration.incidence.join(" "),
                contact_faces: declaration
                    .contact_faces
                    .into_iter()
                    .map(str::to_owned)
                    .collect(),
                witness: witnesses
                    .get(declaration.identity)
                    .cloned()
                    .ok_or_else(|| {
                        format!("{} lost its later conduct witness", declaration.identity)
                    })?,
                states: coordinates
                    .iter()
                    .enumerate()
                    .map(|(at, coordinate)| PresentedSectionState {
                        coordinate: *coordinate,
                        successors: match at {
                            0 => BTreeMap::from([
                                ("raise-left".to_owned(), 1),
                                ("raise-right".to_owned(), 2),
                            ]),
                            1 => BTreeMap::from([("raise-right".to_owned(), 3)]),
                            2 => BTreeMap::from([("raise-left".to_owned(), 3)]),
                            _ => BTreeMap::new(),
                        },
                    })
                    .collect(),
                root: 0,
            })
        })
        .collect()
}

fn verify_later_return(
    declarations: &[PresentationDeclaration],
    returned: &RecurrentSectionFormationReceipt,
) -> Result<bool, String> {
    Ok(declarations.iter().all(|declaration| {
        returned
            .readings
            .iter()
            .find(|reading| reading.identity == declaration.identity)
            .is_some_and(|reading| {
                reading.states.iter().all(|state| {
                    let [left, right] = state.coordinate;
                    !state.open
                        && state.candidate_values
                            == [declaration.law.enact(left, right).to_string()]
                })
            })
    }))
}

fn profile(
    label: &'static str,
    reading: &CausalSectionReading,
    formation: &RecurrentSectionFormationReceipt,
) -> CausalProfile {
    CausalProfile {
        label,
        root_conduct_blocks: reading.root_conduct_blocks.clone(),
        reconstruction_fibers: reading
            .reconstruction_fibers
            .iter()
            .map(|fiber| fiber.presentations.clone())
            .collect(),
        deposited_conducts: formation.deposited_conducts,
        active_conducts: formation.active_conducts,
        distinct_transformation_laws: formation.distinct_transformation_laws,
        riding_state_laws: formation.riding_state_laws,
        causal_front_distribution: formation.causal_front_distribution.clone(),
        interaction_arity_distribution: formation.interaction_arity_distribution.clone(),
        phase_current_distribution: formation.phase_current_distribution.clone(),
        mixed_phase_distribution: formation.mixed_phase_distribution.clone(),
        reconvergent_diamonds: formation.reconvergent_diamonds,
        flat_reconvergent_diamonds: formation.flat_reconvergent_diamonds,
        shortest_interventions: reading
            .shortest_separators
            .iter()
            .map(separator_receipt)
            .collect(),
        open_state_population: formation
            .readings
            .iter()
            .flat_map(|reading| &reading.states)
            .filter(|state| state.open)
            .count(),
    }
}

fn separator_receipt(separator: &SectionSeparator) -> SeparatorReceipt {
    SeparatorReceipt {
        left: separator.left.clone(),
        right: separator.right.clone(),
        interventions: separator.interventions.clone(),
        receiver: separator.receiver.clone(),
        left_observation: separator.left_observation.clone(),
        right_observation: separator.right_observation.clone(),
        separated_by_terminus: separator.separated_by_terminus,
    }
}

fn block_containing(
    blocks: &[BTreeSet<String>],
    identities: &[&str],
) -> Result<BTreeSet<String>, String> {
    blocks
        .iter()
        .find(|block| identities.iter().all(|identity| block.contains(*identity)))
        .cloned()
        .ok_or_else(|| format!("no conduct block contains {identities:?}"))
}

fn separator_between<'a>(
    reading: &'a CausalSectionReading,
    left: &str,
    right: &str,
) -> Result<&'a SectionSeparator, String> {
    reading
        .shortest_separators
        .iter()
        .find(|separator| {
            (separator.left == left && separator.right == right)
                || (separator.left == right && separator.right == left)
        })
        .ok_or_else(|| format!("{left} and {right} returned no separator"))
}

fn split_pair_population(before: &[BTreeSet<String>], after: &[BTreeSet<String>]) -> usize {
    let after_block = after
        .iter()
        .flat_map(|block| block.iter().map(move |identity| (identity, block)))
        .collect::<BTreeMap<_, _>>();
    before
        .iter()
        .map(|block| {
            block
                .iter()
                .enumerate()
                .map(|(at, left)| {
                    block
                        .iter()
                        .skip(at + 1)
                        .filter(|right| after_block[left] != after_block[*right])
                        .count()
                })
                .sum::<usize>()
        })
        .sum()
}

fn canonical_blocks(blocks: &[BTreeSet<String>]) -> Vec<Vec<String>> {
    let mut canonical = blocks
        .iter()
        .map(|block| block.iter().cloned().collect::<Vec<_>>())
        .collect::<Vec<_>>();
    canonical.sort();
    canonical
}

fn block_shape(blocks: &[BTreeSet<String>]) -> Vec<usize> {
    let mut shape = blocks.iter().map(BTreeSet::len).collect::<Vec<_>>();
    shape.sort_unstable();
    shape
}

fn contains(haystack: &[u8], needle: &[u8]) -> bool {
    !needle.is_empty()
        && haystack
            .windows(needle.len())
            .any(|window| window == needle)
}
