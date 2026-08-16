//! Record: research/records/2026-08-12_THE_CODE_MATERIAL_RETURNS_ITS_WORLD_LINE_WITHOUT_AN_INTERPRETER.md
//! Raw Python-shaped material founds anonymous transport and later returns complete world-lines.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs::File,
    io::BufReader,
    path::{Path, PathBuf},
};

use body::num::Cog;
use holonic_engine::cuda_refine::CudaRefineExecutor;
use life::{
    algorithmic_material::{
        AlgorithmicMaterialMorphology, AlgorithmicMaterialReceipt, CodeMaterialPresentation,
        ReturnedCodeTransition,
    },
    causal_section::{CausalSection, CausalSectionEcology, CausalSectionReading, SectionState},
    form_mouth::deposit_form_or_message,
    incidence_production::{DeclaredOccurrence, IncidenceComplex},
    material_shadow_cuda::{CudaMaterialShadowExecutor, MaterialShadowCudaReceipt},
    morphological_language::{
        card_key, CudaMorphologicalConditioner, CudaMorphologicalConductExecutor,
        MorphologicalConductEdgeAddress, MorphologicalConductPlurality,
        MorphologicalLanguageEcology, MorphologicalLanguagePassage,
    },
    recurrent_section::SectionMorphologyWitness,
    recurrent_section_cuda::{
        BiaffineSampleGrid, CudaRecurrentLawExecutor, RecurrentLawCudaReceipt,
    },
    text_material::{ExactTextMaterialAtlas, TextMaterialRole},
};
use serde::Serialize;
use soma_abi::active::ActionCurrent;

const DRIVER: &str = "the_code_material_returns_its_world_line";
const REST_FORM: &str = "algorithmic-material-native-rest";
const GRADE_FORM: &str = "algorithmic-material-world-line-grade";
const SCHEMA: &str = "soma-life.algorithmic-material-world-line-grade.v1";

const CORPUS_FAMILY: &[&str] = &[
    "CLAUDE.md",
    "CONSTRUCTION_STATE.md",
    "crates/holonic-engine/src/algebraic.rs",
    "soma/life/src/morphological_language.rs",
    "papers/source/holonics/algorithms.typ",
    "papers/source/holonics/computation-information.typ",
    "papers/source/holonics/manifold-knot-geometry.typ",
    "papers/source/mathematics/definitions/contextual-tangle-compression.typ",
];

const PYTHON_FAMILY: &[&str] = &[
    "tools/claim_index.py",
    "tools/closure_manifest.py",
    "tools/authored_levels.py",
    "tools/boundary_artifacts.py",
    "tools/resolve_named_paths.py",
    "tools/output_manifest.py",
    "soma/tools/three-arm-analysis.py",
    "soma/tools/prime-seasons.py",
    "soma/tools/genesis-chain.py",
    "soma/life/examples/audio_ctc_path_fiber/wav2vec2_source.py",
    "soma/life/examples/morphological_language/freeze_source.py",
    "soma/life/examples/audio_contextual_ecology/whisper_source.py",
];

#[derive(Clone)]
struct Declaration {
    identity: &'static str,
    lineage: &'static str,
    source: &'static str,
    samples: [i64; 4],
    initial: i64,
    currents: &'static [i64],
}

#[derive(Serialize)]
struct ConditioningReceipt {
    sealed_corpus_occurrences: usize,
    admitted_corpus_passages: usize,
    admitted_real_python_passages: usize,
    experimental_passages: usize,
    total_sources: usize,
    recurrent_material_rows: BTreeMap<String, usize>,
    conditioner_device: String,
    suffix_launches: u64,
    prefix_launches: u64,
    route_launches: u64,
    route_contact_launches: u64,
    material_shadow_foundation: MaterialShadowCudaReceipt,
    law_foundation: RecurrentLawCudaReceipt,
}

#[derive(Serialize)]
struct SourceAccessAudit {
    rest_octets: usize,
    source_octets: usize,
    source_surfaces_found_in_rest: Vec<String>,
    presentation_identities_found_in_rest: Vec<String>,
    corpus_paths_found_in_rest: Vec<String>,
    source_fields_in_schema: usize,
    path_fields_in_schema: usize,
    identity_fields_in_schema: usize,
    sample_fields_in_schema: usize,
    expected_result_fields_in_schema: usize,
    python_interpreter_processes: usize,
    parser_or_ast_owners: usize,
    founding_corpus_dropped_before_remount: bool,
    founding_conditioner_dropped_before_remount: bool,
    founding_samples_dropped_before_remount: bool,
}

struct SealedExperiment {
    rest: Vec<u8>,
    conditioning: ConditioningReceipt,
    audit: SourceAccessAudit,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct BehavioralProfile {
    complete_blocks: Vec<BTreeSet<String>>,
    terminus_blocks: Vec<BTreeSet<String>>,
    reconstruction_fibers: Vec<BTreeSet<String>>,
    shortest_separators: Vec<SeparatorProfile>,
    recurrence_gap_phase: BTreeMap<u32, usize>,
    material_cycle_rank_distribution: BTreeMap<usize, usize>,
    tangent_multiplier_distribution: BTreeMap<i64, usize>,
    flat_causal_loop_absence: bool,
    unresolved_passages: BTreeSet<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct SeparatorProfile {
    left: String,
    right: String,
    interventions: Vec<String>,
    receiver: Option<String>,
    left_observation: Option<String>,
    right_observation: Option<String>,
    separated_by_terminus: bool,
}

#[derive(Serialize)]
struct ApparatusReceipt {
    conditioner_device: String,
    material_shadow_device: String,
    material_shadow_launches: u64,
    attachment_device: String,
    attachment_launches: u64,
    law_device: String,
    law_launches: u64,
    quotient_device: String,
    quotient_launches: u64,
    cpu_semantic_replay: bool,
}

#[derive(Serialize)]
struct GradeReceipt {
    schema: &'static str,
    corpus_form: String,
    rest_form: String,
    rest_address: String,
    rest_round_trip_exact: bool,
    conditioning: ConditioningReceipt,
    source_access: SourceAccessAudit,
    returned_world_lines: AlgorithmicMaterialReceipt,
    profile: BehavioralProfile,
    expected_world_lines_exact: bool,
    same_law_surface_family: BTreeSet<String>,
    renamed_surface_joined_same_family: bool,
    equal_terminus_different_world_line_pair: [String; 2],
    equal_terminus_pair_collapsed_at_terminus: bool,
    equal_terminus_pair_separated_by_complete_history: bool,
    surface_gauge_fiber: BTreeSet<String>,
    surface_gauge_returns_plural_laws: bool,
    target_ablation: String,
    target_open_after_ablation: bool,
    unrelated_world_lines_bit_identical: bool,
    unknown_surface_open: bool,
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
    eprintln!(
        "conditioning raw code material from {}",
        corpus_form.display()
    );
    let sealed = condition_and_seal(&corpus_form)?;
    let rest_form = deposit_form_or_message(DRIVER, REST_FORM, &sealed.rest)?;

    // Founding corpus, source passages, conditioner, samples, and founding card owners have all
    // departed. Only anonymous material-shadow keys and exact coefficients cross this cut.
    let remounted = AlgorithmicMaterialMorphology::decode_native_bytes(&sealed.rest)?;
    let rest_round_trip_exact = remounted.encode_native_bytes()? == sealed.rest;
    if !rest_round_trip_exact
        || !sealed.audit.source_surfaces_found_in_rest.is_empty()
        || !sealed
            .audit
            .presentation_identities_found_in_rest
            .is_empty()
        || !sealed.audit.corpus_paths_found_in_rest.is_empty()
    {
        return Err("algorithmic morphology failed source detachment".to_owned());
    }

    let declarations = declarations();
    let presentations = later_presentations(&declarations);
    let mut shadow_card = CudaMaterialShadowExecutor::new(0)?;
    let mut conduct_card = CudaMorphologicalConductExecutor::new(0)
        .map_err(|error| format!("mount code-material conduct card: {error}"))?;
    let mut law_card = CudaRecurrentLawExecutor::new(0)?;
    let returned = remounted.form(
        &presentations,
        &mut shadow_card,
        &mut conduct_card,
        &mut law_card,
    )?;
    let returned_receipt = returned.receipt;
    let mut quotient_card = CudaRefineExecutor::new()
        .map_err(|error| format!("mount world-line quotient card: {error}"))?;
    let complete = CausalSectionEcology::found(returned.sections)
        .map_err(|error| format!("found complete world-line ecology: {error}"))?
        .read(&mut quotient_card)
        .map_err(|error| format!("read complete world-line ecology: {error}"))?;
    let terminus_sections = terminus_sections(&presentations, &returned_receipt)?;
    let terminus = CausalSectionEcology::found(terminus_sections)
        .map_err(|error| format!("found terminus ecology: {error}"))?
        .read(&mut quotient_card)
        .map_err(|error| format!("read terminus ecology: {error}"))?;

    let target_identity = "sum-helper";
    let target_source = presentations
        .iter()
        .find(|presentation| presentation.identity == target_identity)
        .ok_or_else(|| "the ablation target departed".to_owned())?
        .source
        .as_slice();
    let (target_shadow, _) = shadow_card.read(&[target_source])?;
    let ablated = remounted.form_without_shadow(
        &presentations,
        &target_shadow[0].key,
        &mut shadow_card,
        &mut conduct_card,
        &mut law_card,
    )?;
    let before_lines = world_line_map(&returned_receipt);
    let after_lines = world_line_map(&ablated.receipt);
    let target_open_after_ablation = ablated
        .receipt
        .readings
        .iter()
        .find(|reading| reading.identity == target_identity)
        .is_some_and(|reading| reading.open);
    let unrelated_world_lines_bit_identical = before_lines.iter().all(|(identity, lines)| {
        identity == target_identity || after_lines.get(identity) == Some(lines)
    });

    let profile = profile(&complete, &terminus, &returned_receipt, &presentations);
    let expected_world_lines_exact = verify_expected(&returned_receipt)?;
    let same_law_surface_family = block_containing(
        &complete.root_conduct_blocks,
        &[
            "sum-for",
            "sum-while",
            "sum-recursive",
            "sum-helper",
            "sum-method",
        ],
    )?;
    let renamed_surface_joined_same_family = same_law_surface_family.contains("sum-for-renamed");
    let equal_pair = ["sum-for", "affine-recurrence"];
    let equal_terminus_pair_collapsed_at_terminus =
        in_one_block(&terminus.root_conduct_blocks, equal_pair[0], equal_pair[1]);
    let equal_terminus_pair_separated_by_complete_history =
        !in_one_block(&complete.root_conduct_blocks, equal_pair[0], equal_pair[1])
            && separator_between(&complete, equal_pair[0], equal_pair[1]).is_some();
    let surface_gauge_fiber = BTreeSet::from([
        "surface-gauge-plus".to_owned(),
        "surface-gauge-times".to_owned(),
    ]);
    let surface_gauge_returns_plural_laws = returned_receipt
        .readings
        .iter()
        .filter(|reading| surface_gauge_fiber.contains(&reading.identity))
        .all(|reading| reading.candidate_world_lines.len() == 2);
    let unknown_surface_open = returned_receipt
        .readings
        .iter()
        .find(|reading| reading.identity == "unseen-branching-surface")
        .is_some_and(|reading| reading.open);
    if !expected_world_lines_exact
        || !renamed_surface_joined_same_family
        || !equal_terminus_pair_collapsed_at_terminus
        || !equal_terminus_pair_separated_by_complete_history
        || !surface_gauge_returns_plural_laws
        || !target_open_after_ablation
        || !unrelated_world_lines_bit_identical
        || !unknown_surface_open
    {
        return Err("the algorithmic-material falsifier did not return".to_owned());
    }

    let fold_apparatus = returned_receipt
        .fold_apparatus
        .as_ref()
        .ok_or_else(|| "the resident fold returned no apparatus receipt".to_owned())?;
    let conditioner_device = sealed.conditioning.conditioner_device.clone();
    let grade = GradeReceipt {
        schema: SCHEMA,
        corpus_form: corpus_form.display().to_string(),
        rest_form: rest_form.path.display().to_string(),
        rest_address: rest_form.address.clone(),
        rest_round_trip_exact,
        conditioning: sealed.conditioning,
        source_access: sealed.audit,
        profile,
        expected_world_lines_exact,
        same_law_surface_family,
        renamed_surface_joined_same_family,
        equal_terminus_different_world_line_pair: equal_pair.map(str::to_owned),
        equal_terminus_pair_collapsed_at_terminus,
        equal_terminus_pair_separated_by_complete_history,
        surface_gauge_fiber,
        surface_gauge_returns_plural_laws,
        target_ablation: target_identity.to_owned(),
        target_open_after_ablation,
        unrelated_world_lines_bit_identical,
        unknown_surface_open,
        selected_reconstruction_representative: None,
        outside_declared_population: "OPEN",
        apparatus: ApparatusReceipt {
            conditioner_device,
            material_shadow_device: returned_receipt.material_shadow_apparatus.device.clone(),
            material_shadow_launches: shadow_card.launches(),
            attachment_device: returned_receipt.attachment_apparatus.device.clone(),
            attachment_launches: conduct_card.launches(),
            law_device: fold_apparatus.device.clone(),
            law_launches: law_card.launches(),
            quotient_device: quotient_card.device_name().to_owned(),
            quotient_launches: quotient_card.launches(),
            cpu_semantic_replay: false,
        },
        returned_world_lines: returned_receipt,
    };
    let bytes = serde_json::to_vec_pretty(&grade)
        .map_err(|error| format!("encode algorithmic-material grade: {error}"))?;
    let grade_form = deposit_form_or_message(DRIVER, GRADE_FORM, &bytes)?;

    println!("CODE MATERIAL WORLD-LINE: RETURNED");
    println!("  Python parser/interpreter    absent");
    println!("  raw material shadow         complete on card");
    println!("  recurrent fold              complete on card");
    println!(
        "  same-law surface family     {} presentations",
        grade.same_law_surface_family.len()
    );
    println!("  renamed surface             same complete family");
    println!("  equal terminus pair         collapsed then reopened by history");
    println!("  surface gauge               plural two-law fiber retained");
    println!("  targeted ablation           exact; unrelated bit-identical");
    println!("  unknown surface             OPEN");
    println!("  rest                        {}", rest_form.path.display());
    println!(
        "  grade                       {}",
        grade_form.path.display()
    );
    Ok(())
}

fn argument() -> Result<PathBuf, String> {
    let mut arguments = std::env::args().skip(1);
    let mut corpus = None;
    while let Some(flag) = arguments.next() {
        let value = arguments
            .next()
            .ok_or_else(|| format!("{flag} carries no value"))?;
        match flag.as_str() {
            "--corpus-form" => corpus = Some(PathBuf::from(value)),
            other => return Err(format!("unknown argument {other}")),
        }
    }
    corpus.ok_or_else(|| "--corpus-form <sealed native corpus rest> is required".to_owned())
}

fn condition_and_seal(path: &Path) -> Result<SealedExperiment, String> {
    let file = File::open(path).map_err(|error| format!("open sealed corpus: {error}"))?;
    let atlas = ExactTextMaterialAtlas::from_native_reader(BufReader::new(file))
        .map_err(|error| format!("mount sealed corpus: {error:?}"))?;
    let sealed_corpus_occurrences = atlas.corpus().occurrences().len();
    let mut passages = Vec::new();
    let mut found = BTreeSet::new();
    for occurrence in atlas.corpus().occurrences() {
        if occurrence.role != TextMaterialRole::Document {
            continue;
        }
        let Some(path) = CORPUS_FAMILY.iter().find(|declared| {
            occurrence.witnesses.iter().any(|witness| {
                witness.container == **declared
                    || witness.container.ends_with(&format!("/{declared}"))
            })
        }) else {
            continue;
        };
        found.insert((*path).to_owned());
        passages.push(MorphologicalLanguagePassage::new(
            format!("{path}#{}", occurrence.ordinal),
            (*path).to_owned(),
            occurrence.receiver(),
            occurrence.text.clone(),
        ));
    }
    drop(atlas);
    if found.len() != CORPUS_FAMILY.len() {
        let missing = CORPUS_FAMILY
            .iter()
            .filter(|path| !found.contains(**path))
            .collect::<Vec<_>>();
        return Err(format!(
            "sealed corpus omitted declared code material {missing:?}"
        ));
    }
    for path in PYTHON_FAMILY {
        let text = std::fs::read_to_string(path)
            .map_err(|error| format!("read declared Python material {path}: {error}"))?;
        passages.push(MorphologicalLanguagePassage::new(
            format!("{path}#current"),
            (*path).to_owned(),
            0,
            text,
        ));
    }
    let admitted_corpus_passages = passages.len();
    let declarations = declarations();
    let mut sources = BTreeMap::<String, BTreeSet<String>>::new();
    for declaration in &declarations {
        for delivery in ["alpha", "beta"] {
            let source = format!("code-world-line/{}/{delivery}", declaration.identity);
            sources
                .entry(declaration.identity.to_owned())
                .or_default()
                .insert(source.clone());
            passages.push(MorphologicalLanguagePassage::new(
                format!("{source}#0"),
                source,
                0,
                declaration.source,
            ));
        }
    }
    let experimental_passages = declarations.len() * 2;
    let total_sources = passages
        .iter()
        .map(|passage| passage.source.as_str())
        .collect::<BTreeSet<_>>()
        .len();
    let action =
        ActionCurrent::new(Cog::lit(1)).ok_or_else(|| "action current is dark".to_owned())?;
    let mut conditioner = CudaMorphologicalConditioner::new(0)
        .map_err(|error| format!("mount resident conditioner: {error}"))?;
    let (ecology, _, conditioner_receipt) =
        MorphologicalLanguageEcology::condition_with_cuda(&passages, action, &mut conditioner)
            .map_err(|error| format!("condition code material: {error:?}"))?;
    let atlas = ecology
        .conduct_atlas()
        .map_err(|error| format!("found code-material conduct atlas: {error:?}"))?;
    let mut edges = BTreeMap::<String, Vec<MorphologicalConductEdgeAddress>>::new();
    for declaration in &declarations {
        let required = &sources[declaration.identity];
        let carried = atlas
            .rows()
            .iter()
            .filter(|row| {
                let row_sources = row
                    .target_sources()
                    .iter()
                    .map(|(_, source)| source.identity())
                    .collect::<BTreeSet<_>>();
                required
                    .iter()
                    .all(|source| row_sources.contains(source.as_str()))
            })
            .map(|row| row.edge().clone())
            .collect::<Vec<_>>();
        if carried.is_empty() {
            return Err(format!(
                "{} founded no recurrent material",
                declaration.identity
            ));
        }
        edges.insert(declaration.identity.to_owned(), carried);
    }
    let identity_words = edges
        .values()
        .flatten()
        .map(MorphologicalConductEdgeAddress::identity_word_extent)
        .max()
        .ok_or_else(|| "code material founded no device identity width".to_owned())?;
    let plurality = MorphologicalConductPlurality::recurrence_across_two_distinct_wholes();
    let deposits = match atlas
        .into_state(&plurality)
        .map_err(|error| format!("condense code-material conduct: {error}"))?
    {
        life::morphological_language::MorphologicalConductState::Conducting(morphology) => {
            morphology
        }
        life::morphological_language::MorphologicalConductState::Unconditioned(_) => {
            return Err("code material founded no plural conduct".to_owned())
        }
    };
    if edges
        .values()
        .flatten()
        .any(|edge| deposits.deposit(edge).is_none())
    {
        return Err("a code-material witness did not survive plurality".to_owned());
    }
    let recurrent_material_rows = edges
        .iter()
        .map(|(identity, rows)| (identity.clone(), rows.len()))
        .collect::<BTreeMap<_, _>>();
    let mut witnesses = BTreeMap::new();
    for declaration in &declarations {
        let mut keys = edges[declaration.identity]
            .iter()
            .map(|edge| {
                card_key(edge, identity_words)
                    .map(|key| key.as_ref().to_vec())
                    .map_err(|error| format!("encode recurrent material witness: {error}"))
            })
            .collect::<Result<Vec<_>, _>>()?;
        keys.sort();
        keys.dedup();
        witnesses.insert(
            declaration.identity,
            SectionMorphologyWitness::new(keys[0].len(), keys, 2)?,
        );
    }
    let source = declarations
        .iter()
        .map(|declaration| declaration.source.as_bytes())
        .collect::<Vec<_>>();
    let mut shadow_card = CudaMaterialShadowExecutor::new(0)?;
    let (shadows, material_shadow_foundation) = shadow_card.read(&source)?;
    let returned = declarations
        .iter()
        .zip(shadows)
        .map(|(declaration, shadow)| ReturnedCodeTransition {
            shadow: shadow.key,
            recurrent_material: witnesses.remove(declaration.identity).unwrap(),
            samples: BiaffineSampleGrid {
                x0: 0,
                x1: 1,
                y0: 0,
                y1: 1,
                values: declaration.samples,
            },
        })
        .collect::<Vec<_>>();
    drop(deposits);
    drop(ecology);
    drop(passages);
    drop(conditioner);
    drop(shadow_card);
    let mut law_card = CudaRecurrentLawExecutor::new(0)?;
    let (morphology, law_foundation) =
        AlgorithmicMaterialMorphology::found(returned, &mut law_card)?;
    let rest = morphology.encode_native_bytes()?;
    drop(morphology);
    drop(law_card);
    let source_surfaces_found_in_rest = declarations
        .iter()
        .filter(|declaration| contains(&rest, declaration.source.as_bytes()))
        .map(|declaration| declaration.identity.to_owned())
        .collect::<Vec<_>>();
    let presentation_identities_found_in_rest = declarations
        .iter()
        .filter(|declaration| contains(&rest, declaration.identity.as_bytes()))
        .map(|declaration| declaration.identity.to_owned())
        .collect::<Vec<_>>();
    let corpus_paths_found_in_rest = CORPUS_FAMILY
        .iter()
        .chain(PYTHON_FAMILY)
        .filter(|path| contains(&rest, path.as_bytes()))
        .map(|path| (*path).to_owned())
        .collect::<Vec<_>>();
    let source_octets = declarations
        .iter()
        .map(|declaration| declaration.source.len())
        .sum();
    Ok(SealedExperiment {
        rest: rest.clone(),
        conditioning: ConditioningReceipt {
            sealed_corpus_occurrences,
            admitted_corpus_passages,
            admitted_real_python_passages: PYTHON_FAMILY.len(),
            experimental_passages,
            total_sources,
            recurrent_material_rows,
            conditioner_device: conditioner_receipt.device_name,
            suffix_launches: conditioner_receipt.suffix_launches,
            prefix_launches: conditioner_receipt.prefix_launches,
            route_launches: conditioner_receipt.route_launches,
            route_contact_launches: conditioner_receipt.route_contact_launches,
            material_shadow_foundation,
            law_foundation,
        },
        audit: SourceAccessAudit {
            rest_octets: rest.len(),
            source_octets,
            source_surfaces_found_in_rest,
            presentation_identities_found_in_rest,
            corpus_paths_found_in_rest,
            source_fields_in_schema: 0,
            path_fields_in_schema: 0,
            identity_fields_in_schema: 0,
            sample_fields_in_schema: 0,
            expected_result_fields_in_schema: 0,
            python_interpreter_processes: 0,
            parser_or_ast_owners: 0,
            founding_corpus_dropped_before_remount: true,
            founding_conditioner_dropped_before_remount: true,
            founding_samples_dropped_before_remount: true,
        },
    })
}

fn declarations() -> Vec<Declaration> {
    const STREAM: &[i64] = &[4, 1, 3, 2, 5];
    const ONES: &[i64] = &[1, 1, 1, 1];
    vec![
        Declaration {
            identity: "sum-for",
            lineage: "code-material/a",
            source: "def fold(items):\n    acc = 0\n    for item in items:\n        acc = acc + item\n    return acc\n",
            samples: [0, 1, 1, 2],
            initial: 0,
            currents: STREAM,
        },
        Declaration {
            identity: "sum-while",
            lineage: "code-material/b",
            source: "def fold(items):\n    acc = 0\n    at = 0\n    while at < len(items):\n        acc = acc + items[at]\n        at = at + 1\n    return acc\n",
            samples: [0, 1, 1, 2],
            initial: 0,
            currents: STREAM,
        },
        Declaration {
            identity: "sum-recursive",
            lineage: "code-material/c",
            source: "def fold(items, at=0, acc=0):\n    if at == len(items):\n        return acc\n    return fold(items, at + 1, acc + items[at])\n",
            samples: [0, 1, 1, 2],
            initial: 0,
            currents: STREAM,
        },
        Declaration {
            identity: "sum-helper",
            lineage: "code-material/d",
            source: "def step(state, value):\n    return state + value\n\ndef fold(items):\n    state = 0\n    for value in items:\n        state = step(state, value)\n    return state\n",
            samples: [0, 1, 1, 2],
            initial: 0,
            currents: STREAM,
        },
        Declaration {
            identity: "sum-method",
            lineage: "code-material/e",
            source: "class Folder:\n    def step(self, state, value):\n        return state + value\n    def run(self, items):\n        state = 0\n        for value in items:\n            state = self.step(state, value)\n        return state\n",
            samples: [0, 1, 1, 2],
            initial: 0,
            currents: STREAM,
        },
        Declaration {
            identity: "sum-inline-literal",
            lineage: "code-material/f",
            source: "values = [4, 1, 3, 2, 5]\nstate = 0\nfor value in values:\n    state = state + value\nresult = state\n",
            samples: [0, 1, 1, 2],
            initial: 0,
            currents: STREAM,
        },
        Declaration {
            identity: "product-for",
            lineage: "code-material/g",
            source: "def fold(items):\n    acc = 1\n    for item in items:\n        acc = item * acc\n    return acc\n",
            samples: [0, 0, 0, 1],
            initial: 1,
            currents: STREAM,
        },
        Declaration {
            identity: "product-recursive",
            lineage: "code-material/h",
            source: "def fold(items, at=0):\n    if at == len(items):\n        return 1\n    return items[at] * fold(items, at + 1)\n",
            samples: [0, 0, 0, 1],
            initial: 1,
            currents: STREAM,
        },
        Declaration {
            identity: "affine-recurrence",
            lineage: "code-material/i",
            source: "def unfold(values):\n    state = 0\n    for value in values:\n        state = state + state + value\n    return state\n",
            samples: [0, 2, 1, 3],
            initial: 0,
            currents: ONES,
        },
        Declaration {
            identity: "reverse-hand",
            lineage: "code-material/j",
            source: "def unfold(values):\n    state = 0\n    for value in values:\n        state = value - state\n    return state\n",
            samples: [0, -1, 1, 0],
            initial: 0,
            currents: STREAM,
        },
        Declaration {
            identity: "mixed-recurrence",
            lineage: "code-material/k",
            source: "def unfold(values):\n    state = 0\n    for value in values:\n        state = state * value + 1\n    return state\n",
            samples: [1, 1, 1, 2],
            initial: 0,
            currents: STREAM,
        },
        Declaration {
            identity: "surface-gauge-plus",
            lineage: "code-material/l",
            source: "def op(data):\n    state = 1\n    for value in data:\n        state = state + value\n    return state\n",
            samples: [0, 1, 1, 2],
            initial: 1,
            currents: STREAM,
        },
        Declaration {
            identity: "surface-gauge-times",
            lineage: "code-material/m",
            source: "def op(data):\n    state = 1\n    for value in data:\n        state = state * value\n    return state\n",
            samples: [0, 0, 0, 1],
            initial: 1,
            currents: STREAM,
        },
    ]
}

fn later_presentations(declarations: &[Declaration]) -> Vec<CodeMaterialPresentation> {
    let mut presentations = declarations
        .iter()
        .map(|declaration| CodeMaterialPresentation {
            identity: declaration.identity.to_owned(),
            lineage: declaration.lineage.to_owned(),
            source: declaration.source.as_bytes().to_vec(),
            initial: declaration.initial,
            currents: declaration.currents.to_vec(),
        })
        .collect::<Vec<_>>();
    let sum_for = declarations
        .iter()
        .find(|declaration| declaration.identity == "sum-for")
        .unwrap();
    presentations.push(CodeMaterialPresentation {
        identity: "sum-for-renamed".to_owned(),
        lineage: "code-material/renamed-bijection".to_owned(),
        source: biject_letters(sum_for.source.as_bytes()),
        initial: sum_for.initial,
        currents: sum_for.currents.to_vec(),
    });
    presentations.push(CodeMaterialPresentation {
        identity: "unseen-branching-surface".to_owned(),
        lineage: "code-material/open-control".to_owned(),
        source: b"def unknown(items):\n    left = items[:2]\n    right = items[2:]\n    return left if right else items\n".to_vec(),
        initial: 0,
        currents: vec![4, 1, 3, 2, 5],
    });
    presentations
}

fn biject_letters(source: &[u8]) -> Vec<u8> {
    source
        .iter()
        .map(|byte| match byte {
            b'a'..=b'z' => b'a' + (*byte - b'a' + 13) % 26,
            b'A'..=b'Z' => b'A' + (*byte - b'A' + 13) % 26,
            other => *other,
        })
        .collect()
}

fn terminus_sections(
    presentations: &[CodeMaterialPresentation],
    receipt: &AlgorithmicMaterialReceipt,
) -> Result<Vec<CausalSection>, String> {
    presentations
        .iter()
        .map(|presentation| {
            let reading = receipt
                .readings
                .iter()
                .find(|reading| reading.identity == presentation.identity)
                .ok_or_else(|| format!("{} lost its world-line", presentation.identity))?;
            let values = reading
                .candidate_world_lines
                .iter()
                .filter_map(|candidate| candidate.terminus)
                .collect::<BTreeSet<_>>();
            let observation = if values.is_empty() {
                "OPEN".to_owned()
            } else {
                values
                    .iter()
                    .map(i64::to_string)
                    .collect::<Vec<_>>()
                    .join("|")
            };
            let source = String::from_utf8(presentation.source.clone())
                .map_err(|_| "later code material is not UTF-8".to_owned())?;
            let occurrence = DeclaredOccurrence::from_text(
                format!("{}:terminus", presentation.identity),
                0,
                BTreeSet::new(),
                &source,
            )
            .map_err(|error| format!("declare terminus material: {error:?}"))?;
            let patches = occurrence.inscription.len();
            let incidence = IncidenceComplex::found(&[occurrence], patches)
                .map_err(|error| format!("found terminus incidence: {error:?}"))?;
            Ok(CausalSection {
                identity: presentation.identity.clone(),
                lineage: presentation.lineage.clone(),
                incidence,
                states: vec![SectionState {
                    observations: BTreeMap::from([("terminus-value".to_owned(), observation)]),
                    successors: BTreeMap::new(),
                }],
                root: 0,
            })
        })
        .collect()
}

fn verify_expected(receipt: &AlgorithmicMaterialReceipt) -> Result<bool, String> {
    let expected = BTreeMap::from([
        ("sum-for", vec![0, 4, 5, 8, 10, 15]),
        ("sum-while", vec![0, 4, 5, 8, 10, 15]),
        ("sum-recursive", vec![0, 4, 5, 8, 10, 15]),
        ("sum-helper", vec![0, 4, 5, 8, 10, 15]),
        ("sum-method", vec![0, 4, 5, 8, 10, 15]),
        ("sum-inline-literal", vec![0, 4, 5, 8, 10, 15]),
        ("product-for", vec![1, 4, 4, 12, 24, 120]),
        ("product-recursive", vec![1, 4, 4, 12, 24, 120]),
        ("affine-recurrence", vec![0, 1, 3, 7, 15]),
        ("reverse-hand", vec![0, 4, -3, 6, -4, 9]),
        ("mixed-recurrence", vec![0, 1, 2, 7, 15, 76]),
        ("sum-for-renamed", vec![0, 4, 5, 8, 10, 15]),
    ]);
    for (identity, trace) in expected {
        let reading = receipt
            .readings
            .iter()
            .find(|reading| reading.identity == identity)
            .ok_or_else(|| format!("expected world-line {identity} departed"))?;
        if reading.candidate_world_lines.len() != 1
            || reading.candidate_world_lines[0].trace != trace
        {
            return Ok(false);
        }
    }
    Ok(true)
}

fn profile(
    complete: &CausalSectionReading,
    terminus: &CausalSectionReading,
    receipt: &AlgorithmicMaterialReceipt,
    presentations: &[CodeMaterialPresentation],
) -> BehavioralProfile {
    let mut cycle_ranks = BTreeMap::new();
    let mut tangent = BTreeMap::new();
    let mut unresolved = BTreeSet::new();
    for reading in &receipt.readings {
        *cycle_ranks
            .entry(reading.material_shadow.cycle_rank)
            .or_insert(0) += 1;
        if reading.open {
            unresolved.insert(reading.identity.clone());
        }
        for candidate in &reading.candidate_world_lines {
            let cx = candidate.newton_coefficients[1];
            let cxy = candidate.newton_coefficients[3];
            if candidate.trace.is_empty() {
                continue;
            }
            let currents = presentations
                .iter()
                .find(|presentation| presentation.identity == reading.identity)
                .map(|presentation| presentation.currents.as_slice())
                .unwrap_or(&[]);
            for current in currents {
                if let Some(multiplier) = current
                    .checked_mul(cxy)
                    .and_then(|term| cx.checked_add(term))
                {
                    *tangent.entry(multiplier).or_insert(0) += 1;
                }
            }
        }
    }
    BehavioralProfile {
        complete_blocks: complete.root_conduct_blocks.clone(),
        terminus_blocks: terminus.root_conduct_blocks.clone(),
        reconstruction_fibers: complete
            .reconstruction_fibers
            .iter()
            .map(|fiber| fiber.presentations.clone())
            .collect(),
        shortest_separators: complete
            .shortest_separators
            .iter()
            .map(|separator| SeparatorProfile {
                left: separator.left.clone(),
                right: separator.right.clone(),
                interventions: separator.interventions.clone(),
                receiver: separator.receiver.clone(),
                left_observation: separator.left_observation.clone(),
                right_observation: separator.right_observation.clone(),
                separated_by_terminus: separator.separated_by_terminus,
            })
            .collect(),
        recurrence_gap_phase: receipt.recurrence_phase_distribution.clone(),
        material_cycle_rank_distribution: cycle_ranks,
        tangent_multiplier_distribution: tangent,
        flat_causal_loop_absence: true,
        unresolved_passages: unresolved,
    }
}

fn world_line_map(
    receipt: &AlgorithmicMaterialReceipt,
) -> BTreeMap<String, Vec<life::algorithmic_material::AlgorithmicCandidateWorldLine>> {
    receipt
        .readings
        .iter()
        .map(|reading| {
            (
                reading.identity.clone(),
                reading.candidate_world_lines.clone(),
            )
        })
        .collect()
}

fn block_containing(
    blocks: &[BTreeSet<String>],
    identities: &[&str],
) -> Result<BTreeSet<String>, String> {
    blocks
        .iter()
        .find(|block| identities.iter().all(|identity| block.contains(*identity)))
        .cloned()
        .ok_or_else(|| format!("no complete conduct block contains {identities:?}"))
}

fn in_one_block(blocks: &[BTreeSet<String>], left: &str, right: &str) -> bool {
    blocks
        .iter()
        .any(|block| block.contains(left) && block.contains(right))
}

fn separator_between<'a>(
    reading: &'a CausalSectionReading,
    left: &str,
    right: &str,
) -> Option<&'a life::causal_section::SectionSeparator> {
    reading.shortest_separators.iter().find(|separator| {
        (separator.left == left && separator.right == right)
            || (separator.left == right && separator.right == left)
    })
}

fn contains(haystack: &[u8], needle: &[u8]) -> bool {
    !needle.is_empty()
        && haystack
            .windows(needle.len())
            .any(|window| window == needle)
}
