//! Carry one conditioned production through the world, let its returned reading found reusable
//! conduct on CUDA, and produce again from the source-detached continuing rest.
//!
//! ```text
//! cargo run -p life --release --example the_conditioning_return_crosses_the_seal -- \
//!   --corpus-form output/the_material_mouth_seals_the_declared_body/<rest>.form \
//!   --workspace /home/b/Workspaces/holonics \
//!   --codex-root /home/b/.codex --claude-root /home/b/.claude
//! ```
//!
//! The production deed has two detached turns.  The first receives exactly CDER, CDPS, the
//! deposited `ReturnedReading`, and RTCF.  It rereads all four, groups the validated contact on
//! CUDA, deposits CRST, and proves exact target/all ablations.  The second receives only CRST and
//! produces again.  The declared source roots and the first turn's transit directory are absent.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs::File,
    io::{BufReader, Read},
    path::{Path, PathBuf},
    process::Command,
};

use holonic_engine::{
    conditioned_derivation::{
        found_conditioned_circuit, ConditionedBody, DerivationQuery, FoundedMorphology,
    },
    derivation_atlas::CircuitAperture,
    derivation_integral::AccumulationRule,
    rebase_invariants::PivotRule,
    returned_conduct::{
        canonical_incidences, cell_addresses, passages_founding_address, FirstProductionIdentity,
        PassageSite,
    },
    returned_reading::{condition_again, read_production, ReturnedReading},
};
use life::{
    conditioned_rest::{decode_derived_passages, render_derived_passages, ConditionedRest},
    form_mouth::{content_address, deposit_form_or_message, deposit_form_under, DepositedForm},
    laboratory_language::{LaboratoryResearchLeader, LaboratoryReturnedSection},
    returned_conduct::{
        conduct_returned_contact, return_reading_identity, return_source_lineage, AddressedForm,
        ContentAddress, NativeFormSchema, ReturnedCompositeRest, ReturnedConductBoundaryRefusal,
        ReturnedConductOutput, ReturnedContactForm,
    },
    returned_contact_cuda::CudaReturnedContactExecutor,
    text_material::ExactTextMaterialAtlas,
};
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};

const DRIVER: &str = "the_conditioning_return_crosses_the_seal";
const BODY_FORM: &str = "conditioned-body-native-rest";
const FIRST_FORM: &str = "deposited-first-production";
const READING_FORM: &str = "deposited-returned-reading";
const CONTACT_FORM: &str = "deposited-returned-contact";
const REST_FORM: &str = "source-free-returned-composite-rest";
const SECOND_FORM: &str = "source-free-second-production";
const GPU_SEMANTIC_FORM: &str = "corpus-cuda-semantic-return";
const GPU_APPARATUS_FORM: &str = "corpus-cuda-apparatus-receipt";
const CONTACT_SEMANTIC_FORM: &str = "returned-contact-semantic-receipt";
const CONTACT_APPARATUS_FORM: &str = "returned-contact-cuda-apparatus-receipt";
const ATTRIBUTION_FORM: &str = "source-free-causal-attribution";
const GRADE_FORM: &str = "conditioning-return-grade";

const BODY_OCCURRENCE: &str = "plan-2/predecessor/conditioned-body";
const FIRST_OCCURRENCE: &str = "plan-2/production/first";
const READING_OCCURRENCE: &str = "plan-2/reading/first-return";
const CONTACT_OCCURRENCE: &str = "plan-2/contact/typed-projection";
const REST_OCCURRENCE: &str = "plan-2/rest/returned-composite";

const STATEMENT: &str = "(h : P) : exactCarrier P";
const RULE: AccumulationRule = AccumulationRule::RecruitmentLoad;
const PIVOT: PivotRule = PivotRule::SmallestMagnitude;
const APERTURE: CircuitAperture = CircuitAperture::STATEMENT_INCIDENT;

#[derive(Clone, Debug, Serialize, Deserialize)]
struct ConductExpectation {
    body_address: String,
    first_address: String,
    reading_address: String,
    contact_address: String,
    body_occurrence: String,
    first_occurrence: String,
    reading_occurrence: String,
    contact_occurrence: String,
    source_roots: Vec<PathBuf>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct SuccessorExpectation {
    rest_address: String,
    rest_occurrence: String,
    first_address: String,
    reading_address: String,
    reading_occurrence: String,
    source_roots: Vec<PathBuf>,
}

#[derive(Clone, Debug)]
struct LightForm {
    path: PathBuf,
    address: String,
}

enum Mode {
    Build {
        corpus_form: PathBuf,
        source_roots: Vec<PathBuf>,
    },
    Conduct {
        body_form: PathBuf,
        first_form: PathBuf,
        reading_form: PathBuf,
        contact_form: PathBuf,
        expectation: ConductExpectation,
    },
    Successor {
        rest_form: PathBuf,
        expectation: SuccessorExpectation,
    },
}

fn main() {
    if let Err(error) = run() {
        eprintln!("REFUSED: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    match arguments()? {
        Mode::Build {
            corpus_form,
            source_roots,
        } => build(&corpus_form, source_roots),
        Mode::Conduct {
            body_form,
            first_form,
            reading_form,
            contact_form,
            expectation,
        } => conduct(
            &body_form,
            &first_form,
            &reading_form,
            &contact_form,
            &expectation,
        ),
        Mode::Successor {
            rest_form,
            expectation,
        } => successor(&rest_form, &expectation),
    }
}

fn arguments() -> Result<Mode, String> {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    match arguments.first().map(String::as_str) {
        Some("--conduct") => {
            if arguments.len() != 6 {
                return Err("--conduct requires BODY FIRST READING CONTACT EXPECTATION".to_owned());
            }
            return Ok(Mode::Conduct {
                body_form: PathBuf::from(&arguments[1]),
                first_form: PathBuf::from(&arguments[2]),
                reading_form: PathBuf::from(&arguments[3]),
                contact_form: PathBuf::from(&arguments[4]),
                expectation: serde_json::from_str(&arguments[5])
                    .map_err(|error| format!("read conduct expectation: {error}"))?,
            });
        }
        Some("--successor") => {
            if arguments.len() != 3 {
                return Err("--successor requires CRST EXPECTATION".to_owned());
            }
            return Ok(Mode::Successor {
                rest_form: PathBuf::from(&arguments[1]),
                expectation: serde_json::from_str(&arguments[2])
                    .map_err(|error| format!("read successor expectation: {error}"))?,
            });
        }
        _ => {}
    }

    let mut named = BTreeMap::new();
    let mut at = 0usize;
    while at < arguments.len() {
        let name = arguments
            .get(at)
            .ok_or_else(|| "an argument name is absent".to_owned())?;
        let value = arguments
            .get(at + 1)
            .ok_or_else(|| format!("{name} requires a path"))?;
        named.insert(name.to_owned(), PathBuf::from(value));
        at += 2;
    }
    let take = |name: &str| {
        named
            .get(name)
            .cloned()
            .ok_or_else(|| format!("missing {name} PATH"))
    };
    Ok(Mode::Build {
        corpus_form: take("--corpus-form")?,
        source_roots: vec![
            take("--workspace")?,
            take("--codex-root")?,
            take("--claude-root")?,
        ],
    })
}

fn build(corpus_form: &Path, source_roots: Vec<PathBuf>) -> Result<(), String> {
    let corpus_address = sha256_file(corpus_form)?;
    let corpus_file = File::open(corpus_form)
        .map_err(|error| format!("open admitted corpus {}: {error}", corpus_form.display()))?;
    let atlas = ExactTextMaterialAtlas::from_native_reader(BufReader::new(corpus_file))
        .map_err(|error| format!("mount admitted corpus: {error:?}"))?;
    let corpus_receipt = atlas.corpus().receipt().to_owned();

    let workspace = source_roots
        .first()
        .ok_or_else(|| "the declared workspace root is absent".to_owned())?;
    let standing = standing(&workspace.join("standing/output"))?;
    let standing_artifacts = standing.len();
    if standing_artifacts != 103 {
        return Err(format!(
            "the admitted mathematical standing moved: expected 103 artifacts, opened {standing_artifacts}"
        ));
    }
    let query = DerivationQuery::reaching(STATEMENT);
    let mut body = ConditionedBody::mount(standing)
        .map_err(|error| format!("mount mathematical standing: {error}"))?;
    if !body
        .derive(&query)
        .map_err(|error| format!("derive unconditioned mathematical control: {error}"))?
        .is_empty()
    {
        return Err("conditioning was not necessary for mathematical production".to_owned());
    }
    let recruited = body.recruited_population();
    let receiver_features = receiver_features(&recruited);
    if receiver_features.is_empty() {
        return Err("the mathematical standing founded no conditioning receiver family".to_owned());
    }

    let mut resident = atlas
        .mount_cuda(0)
        .map_err(|refusal| format!("mount admitted corpus on CUDA: {:?}", refusal.error()))?;
    let leader = LaboratoryResearchLeader {
        identity: "conditioning-return/corpus-receiver".to_owned(),
        question: STATEMENT.to_owned(),
        region: receiver_features.clone(),
        aperture: resident.receipt().conditioned_sections,
        generation: 0,
        caused_by_clauses: BTreeSet::new(),
    };
    let (gpu_semantic, gpu_apparatus) = resident
        .enact(&leader)
        .map_err(|error| format!("enact corpus CUDA reading: {error:?}"))?;
    if gpu_semantic.sections.is_empty()
        || gpu_semantic.omitted_population != 0
        || gpu_semantic.sections.len() != gpu_semantic.complete_population
        || gpu_apparatus.launch.is_none()
        || !gpu_apparatus.bounded_delta_equal
    {
        return Err("the corpus-linked CUDA deed returned no exact semantic population".to_owned());
    }
    let device = resident.device_name().to_owned();
    let corpus_launches = resident.launches();
    let atlas = resident.unmount_into_host();

    let returned_occurrences = gpu_semantic
        .sections
        .iter()
        .map(source_occurrence_identity)
        .collect::<Result<BTreeSet<_>, _>>()?;
    let selected_occurrences = atlas
        .corpus()
        .occurrences()
        .iter()
        .filter(|occurrence| returned_occurrences.contains(occurrence.identity.as_str()))
        .collect::<Vec<_>>();
    if selected_occurrences.len() != returned_occurrences.len() {
        return Err("a CUDA-returned section did not resolve to its source occurrence".to_owned());
    }
    let morphology = FoundedMorphology::condition_wholes(
        selected_occurrences
            .iter()
            .map(|occurrence| (occurrence.identity.as_str(), occurrence.text.as_str())),
    );
    let selected_occurrence_population = selected_occurrences.len();
    drop(selected_occurrences);
    if morphology.committed().is_empty() {
        return Err(
            "the complete CUDA-returned corpus projection committed no morphology".to_owned(),
        );
    }
    let full_morphology = FoundedMorphology::condition_wholes(
        atlas
            .corpus()
            .occurrences()
            .iter()
            .map(|occurrence| (occurrence.identity.as_str(), occurrence.text.as_str())),
    );
    for identifier in &recruited {
        let restricted = morphology
            .cover(identifier)
            .map_err(|error| format!("cover {identifier:?} through CUDA return: {error}"))?;
        let full = full_morphology
            .cover(identifier)
            .map_err(|error| format!("cover {identifier:?} through full corpus audit: {error}"))?;
        if restricted != full {
            return Err(format!(
                "the CUDA-returned receiver fiber does not factor the full corpus at {identifier:?}: \
                 restricted {} versus full {}",
                restricted.render(),
                full.render()
            ));
        }
    }
    drop(full_morphology);
    drop(atlas);

    let gpu_semantic_bytes = serde_json::to_vec_pretty(&gpu_semantic)
        .map_err(|error| format!("encode CUDA semantic return: {error}"))?;
    let gpu_semantic_form = deposit_light(GPU_SEMANTIC_FORM, &gpu_semantic_bytes)?;
    let gpu_apparatus_bytes = serde_json::to_vec_pretty(&gpu_apparatus)
        .map_err(|error| format!("encode CUDA apparatus receipt: {error}"))?;
    let gpu_apparatus_form = deposit_light(GPU_APPARATUS_FORM, &gpu_apparatus_bytes)?;

    body.carry_morphology(morphology);
    let body_bytes = ConditionedRest::seal(&body)
        .map_err(|error| format!("seal conditioned body: {error}"))?
        .encode_native_bytes()
        .map_err(|error| format!("encode conditioned body: {error}"))?;
    let body_form = deposit_light(BODY_FORM, &body_bytes)?;
    drop(body_bytes);

    let first = body
        .derive(&query)
        .map_err(|error| format!("first production: {error}"))?;
    let repeated = body
        .derive(&query)
        .map_err(|error| format!("unjoined control: {error}"))?;
    if first.is_empty() || first != repeated {
        return Err(
            "the unjoined control is empty or its repeated production is not bit-identical"
                .to_owned(),
        );
    }
    drop(repeated);
    let first_bytes = render_derived_passages(&first);
    let first_form = deposit_light(FIRST_FORM, &first_bytes)?;
    let reread_first = std::fs::read(&first_form.path)
        .map_err(|error| format!("reread first production: {error}"))?;
    let deposited_first = decode_derived_passages(&reread_first)
        .map_err(|error| format!("decode first production: {error}"))?;
    if deposited_first.as_ref() != first.as_slice()
        || render_derived_passages(&deposited_first) != reread_first
    {
        return Err("the deposited first production did not reopen exactly".to_owned());
    }
    drop(first_bytes);
    drop(reread_first);

    let before = found_conditioned_circuit(body.standing().to_vec(), APERTURE)
        .map_err(|error| format!("found standing circuit: {error}"))?;
    let after = body
        .circuit_from_production(&query, deposited_first.to_owned(), APERTURE)
        .map_err(|error| format!("found deposited production circuit: {error}"))?;
    let reading = read_production(&before, &after, RULE, PIVOT, STATEMENT)
        .map_err(|error| format!("read deposited production: {error}"))?;
    if reading.movement.moved().is_empty() || reading.returned.is_still() {
        return Err("the deposited first production returned no invariant movement".to_owned());
    }

    // This is the convicted private wire retained only as the negative control.  On the actual
    // Plan-1 morphology every returned word already stands, so it must not move production.
    let private = condition_again(
        &body.standing_derivations(),
        body.morphology(),
        &query,
        &reading.returned,
    )
    .map_err(|error| format!("run private-wire lexical control: {error}"))?;
    if private.the_production_moved() || private.first != private.second {
        return Err("the private in-memory conditioning edge moved production".to_owned());
    }
    if !private.committed_by_return.is_empty() {
        return Err("the private in-memory edge manufactured lexical novelty".to_owned());
    }
    drop(private);
    let still = condition_again(
        &body.standing_derivations(),
        body.morphology(),
        &query,
        &ReturnedReading::still(),
    )
    .map_err(|error| format!("run private-wire still control: {error}"))?;
    if still.the_production_moved()
        || still.first != still.second
        || &still.carried != body.morphology()
        || !still.committed_by_return.is_empty()
    {
        return Err("the private-wire still reading was not an exact no-op".to_owned());
    }
    drop(still);

    let initial_invariants = reading
        .movement
        .moved()
        .iter()
        .map(|moved| {
            json!({
                "grade": moved.grade,
                "fields": moved.fields_moved().into_iter()
                    .map(|field| format!("{field:?}"))
                    .collect::<Vec<_>>(),
            })
        })
        .collect::<Vec<_>>();
    let returned_population = reading.returned.returns().len();
    let reading_bytes = reading.returned.seal();
    let reading_form = deposit_light(READING_FORM, &reading_bytes)?;
    drop(reading_bytes);

    let body_addressed = addressed(
        &body_form,
        NativeFormSchema::ConditionedRest,
        BODY_OCCURRENCE,
    )?;
    let first_addressed = addressed(
        &first_form,
        NativeFormSchema::DerivedProduction,
        FIRST_OCCURRENCE,
    )?;
    let reading_addressed = addressed(
        &reading_form,
        NativeFormSchema::ReturnedReading,
        READING_OCCURRENCE,
    )?;
    let reading_identity = return_reading_identity(&reading_addressed.lineage());
    let source_lineage = return_source_lineage(&reading_addressed.lineage());
    let incidences = canonical_incidences(
        &before,
        &after,
        &FirstProductionIdentity {
            form: FIRST_OCCURRENCE.to_owned(),
        },
        &deposited_first,
        &reading.routes,
        &reading_identity,
        &source_lineage,
    )
    .map_err(|error| format!("found exact returned contact: {error}"))?;
    let contact_relations = incidences.len();
    if contact_relations == 0 {
        return Err("the returned reading founded no typed passage-cell contact".to_owned());
    }
    let contact = ReturnedContactForm::seal(
        body_addressed.lineage(),
        first_addressed.lineage(),
        reading_addressed.lineage(),
        RULE,
        PIVOT,
        query.to_owned(),
        APERTURE,
        incidences,
    )
    .map_err(|error| format!("seal exact returned contact: {error}"))?;
    let contact_bytes = contact
        .encode_native_bytes()
        .map_err(|error| format!("encode exact returned contact: {error}"))?;
    let contact_form = deposit_light(CONTACT_FORM, &contact_bytes)?;
    drop(contact_bytes);
    drop(contact);
    drop(reading);
    drop(before);
    drop(after);
    drop(first);
    drop(deposited_first);
    drop(body);

    let expectation = ConductExpectation {
        body_address: body_form.address.to_owned(),
        first_address: first_form.address.to_owned(),
        reading_address: reading_form.address.to_owned(),
        contact_address: contact_form.address.to_owned(),
        body_occurrence: BODY_OCCURRENCE.to_owned(),
        first_occurrence: FIRST_OCCURRENCE.to_owned(),
        reading_occurrence: READING_OCCURRENCE.to_owned(),
        contact_occurrence: CONTACT_OCCURRENCE.to_owned(),
        source_roots: source_roots.to_owned(),
    };
    let conduct_return = run_conduct_sandbox(
        workspace,
        &body_form,
        &first_form,
        &reading_form,
        &contact_form,
        &expectation,
    )?;
    inspect_conduct_return(&conduct_return)?;
    let rest_address = text_at(&conduct_return, "/rest/address")?;
    let rest_path = output_form_path(REST_FORM, rest_address);
    if sha256_file(&rest_path)? != rest_address {
        return Err("the detached CRST deposit is absent or moved".to_owned());
    }

    let successor_expectation = SuccessorExpectation {
        rest_address: rest_address.to_owned(),
        rest_occurrence: REST_OCCURRENCE.to_owned(),
        first_address: first_form.address.to_owned(),
        reading_address: reading_form.address.to_owned(),
        reading_occurrence: READING_OCCURRENCE.to_owned(),
        source_roots: source_roots.to_owned(),
    };
    let successor_return = run_successor_sandbox(workspace, &rest_path, &successor_expectation)?;
    inspect_successor_return(&successor_return)?;

    let attribution = json!({
        "schema": "soma-life.conditioning-return-attribution.v1",
        "conduct": conduct_return,
        "successor": successor_return,
    });
    let attribution_bytes = serde_json::to_vec_pretty(&attribution)
        .map_err(|error| format!("encode exact attribution: {error}"))?;
    let attribution_form = deposit_light(ATTRIBUTION_FORM, &attribution_bytes)?;
    let second_address = text_at(&attribution, "/successor/second/address")?;
    let second_path = output_form_path(SECOND_FORM, second_address);
    if sha256_file(&second_path)? != second_address {
        return Err("the source-free second production is absent or moved".to_owned());
    }
    let contact_semantic_address = text_at(&attribution, "/conduct/semantic/address")?;
    let contact_apparatus_address = text_at(&attribution, "/conduct/apparatus/address")?;
    let contact_semantic_path = output_form_path(CONTACT_SEMANTIC_FORM, contact_semantic_address);
    let contact_apparatus_path =
        output_form_path(CONTACT_APPARATUS_FORM, contact_apparatus_address);
    if sha256_file(&contact_semantic_path)? != contact_semantic_address
        || sha256_file(&contact_apparatus_path)? != contact_apparatus_address
    {
        return Err("a detached returned-contact receipt is absent or moved".to_owned());
    }

    let grade = json!({
        "truth_status": "established-bounded",
        "evidence_tags": ["implemented-exact", "computational-witness", "measured"],
        "predecessor": "28028c1",
        "owners": [
            "ConditionedBody",
            "ConditionedRest",
            "returned_reading",
            "ReturnedContactForm",
            "ReturnedContactMorphology",
            "ReturnedCompositeRest",
            "CudaReturnedContactExecutor",
            "form_mouth"
        ],
        "ports": ["CDER/v1", "CDPS/v2", "ReturnedReading/v1", "RTCF/v1", "CRST/v1"],
        "event_occurrence": READING_OCCURRENCE,
        "predecessor_identity": {"occurrence": BODY_OCCURRENCE, "address": body_form.address},
        "constitutive_law": "one exact founded route plus passage-cell provenance conducts one stable companion at the same local passage site",
        "receiver_question": STATEMENT,
        "returned_consequence": "a source-detached CRST remount emits one stable returned companion per contacted first-production site",
        "open_alternatives": [
            "this Plan-2 contact is intentionally nonselective at the declared statement aperture",
            "Plan 3 must found selective plural-source conduct and make generation attachment ride it"
        ],
        "corpus": {
            "path": corpus_form,
            "address": corpus_address,
            "receipt": corpus_receipt,
        },
        "mathematical_standing": {"artifacts": standing_artifacts},
        "conditioned_body": {"path": body_form.path, "address": body_form.address},
        "first_production": {
            "path": first_form.path,
            "address": first_form.address,
            "unjoined_repeat_bit_identical": true,
            "private_wire_lexical_control_bit_identical": true,
            "private_wire_still_control_bit_identical": true,
        },
        "earlier_return": {
            "path": reading_form.path,
            "address": reading_form.address,
            "occurrence": READING_OCCURRENCE,
            "returned_artifacts": returned_population,
            "initial_invariant_movement": initial_invariants,
        },
        "typed_contact": {
            "path": contact_form.path,
            "address": contact_form.address,
            "relations": contact_relations,
        },
        "continuing_rest": {"path": rest_path, "address": rest_address},
        "second_production": {"path": second_path, "address": second_address},
        "causal_attribution": {"path": attribution_form.path, "address": attribution_form.address},
        "returned_contact_semantic": {
            "path": contact_semantic_path,
            "address": contact_semantic_address,
        },
        "returned_contact_apparatus": {
            "path": contact_apparatus_path,
            "address": contact_apparatus_address,
        },
        "corpus_cuda": {
            "device": device,
            "launches": corpus_launches,
            "receiver_factorization": {
                "recruited_identifiers": recruited.len(),
                "declared_features": receiver_features.len(),
                "returned_sections": gpu_semantic.sections.len(),
                "returned_occurrences": selected_occurrence_population,
                "omitted_sections": gpu_semantic.omitted_population,
                "full_corpus_covers_equal": true,
            },
            "semantic": {"path": gpu_semantic_form.path, "address": gpu_semantic_form.address},
            "apparatus": {"path": gpu_apparatus_form.path, "address": gpu_apparatus_form.address},
        },
    });
    let grade_bytes = serde_json::to_vec_pretty(&grade)
        .map_err(|error| format!("encode passing grade: {error}"))?;
    let grade_form = deposit_light(GRADE_FORM, &grade_bytes)?;

    println!("CONDITIONED BODY    {}", body_form.path.display());
    println!("FIRST PRODUCTION   {}", first_form.path.display());
    println!("RETURNED READING   {}", reading_form.path.display());
    println!("TYPED CONTACT      {}", contact_form.path.display());
    println!("CONTINUING REST    {}", rest_path.display());
    println!("SECOND PRODUCTION  {}", second_path.display());
    println!("CAUSAL ATTRIBUTION {}", attribution_form.path.display());
    println!("CONTACT SEMANTICS  {}", contact_semantic_path.display());
    println!("CONTACT APPARATUS  {}", contact_apparatus_path.display());
    println!("CUDA SEMANTICS     {}", gpu_semantic_form.path.display());
    println!("CUDA APPARATUS     {}", gpu_apparatus_form.path.display());
    println!("PASSING GRADE      {}", grade_form.path.display());
    Ok(())
}

fn conduct(
    body_form: &Path,
    first_form: &Path,
    reading_form: &Path,
    contact_form: &Path,
    expectation: &ConductExpectation,
) -> Result<(), String> {
    let masked = masked_roots(&expectation.source_roots)?;
    let body = AddressedForm::new(
        body_form.to_owned(),
        &expectation.body_address,
        NativeFormSchema::ConditionedRest,
        expectation.body_occurrence.to_owned(),
    )
    .map_err(|error| error.to_string())?;
    let first = AddressedForm::new(
        first_form.to_owned(),
        &expectation.first_address,
        NativeFormSchema::DerivedProduction,
        expectation.first_occurrence.to_owned(),
    )
    .map_err(|error| error.to_string())?;
    let reading = AddressedForm::new(
        reading_form.to_owned(),
        &expectation.reading_address,
        NativeFormSchema::ReturnedReading,
        expectation.reading_occurrence.to_owned(),
    )
    .map_err(|error| error.to_string())?;
    let contact = AddressedForm::new(
        contact_form.to_owned(),
        &expectation.contact_address,
        NativeFormSchema::ReturnedContact,
        expectation.contact_occurrence.to_owned(),
    )
    .map_err(|error| error.to_string())?;

    let body_octets = read_exact(body_form, &expectation.body_address)?;
    let base = ConditionedRest::decode_native_bytes(&body_octets)
        .map_err(|error| format!("decode detached CDER: {error}"))?;
    let mounted = base
        .mount()
        .map_err(|error| format!("mount detached CDER: {error}"))?;
    let first_octets = read_exact(first_form, &expectation.first_address)?;
    let deposited_first = decode_derived_passages(&first_octets)
        .map_err(|error| format!("decode detached CDPS: {error}"))?;
    let query = DerivationQuery::reaching(STATEMENT);
    let unjoined_first = mounted
        .derive(&query)
        .map_err(|error| format!("derive detached unjoined control: {error}"))?;
    let unjoined_repeat = mounted
        .derive(&query)
        .map_err(|error| format!("repeat detached unjoined control: {error}"))?;
    if unjoined_first != unjoined_repeat || unjoined_first.as_slice() != deposited_first.as_ref() {
        return Err("the detached unjoined production moved".to_owned());
    }
    drop(mounted);
    drop(body_octets);
    drop(first_octets);
    drop(deposited_first);

    let mut executor = CudaReturnedContactExecutor::new(0)
        .map_err(|error| format!("mount returned-contact CUDA owner: {error}"))?;
    let full = conduct_returned_contact(&body, &first, &reading, &contact, &mut executor)
        .map_err(|error| format!("conduct full returned contact: {error}"))?;
    let targeted = conduct_returned_contact(&body, &first, &reading, &contact, &mut executor)
        .map_err(|error| format!("conduct targeted returned contact branch: {error}"))?;
    let all = conduct_returned_contact(&body, &first, &reading, &contact, &mut executor)
        .map_err(|error| format!("conduct all-ablated returned contact branch: {error}"))?;
    if executor.launches() != 3 {
        return Err("the three returned-contact branches did not each cross CUDA".to_owned());
    }

    let ReturnedConductOutput {
        rest: full_rest,
        semantic: full_semantic,
        apparatus: full_apparatus,
    } = full;
    let ReturnedConductOutput {
        rest: target_rest,
        semantic: target_semantic,
        apparatus: target_apparatus,
    } = targeted;
    let ReturnedConductOutput {
        rest: all_rest,
        semantic: all_semantic,
        apparatus: all_apparatus,
    } = all;
    if full_semantic != target_semantic || full_semantic != all_semantic {
        return Err("fresh conduct branches returned different semantic receipts".to_owned());
    }
    let full_rest_bytes = full_rest
        .encode_native_bytes()
        .map_err(|error| format!("encode full CRST: {error}"))?;
    let target_rest_bytes = target_rest
        .encode_native_bytes()
        .map_err(|error| format!("encode target CRST: {error}"))?;
    if target_rest_bytes != full_rest_bytes {
        return Err("the target branch did not begin from the exact full CRST".to_owned());
    }
    drop(target_rest_bytes);
    let all_rest_bytes = all_rest
        .encode_native_bytes()
        .map_err(|error| format!("encode all CRST: {error}"))?;
    if all_rest_bytes != full_rest_bytes {
        return Err("the all-ablation branch did not begin from the exact full CRST".to_owned());
    }
    drop(all_rest_bytes);
    let contact_records = full_rest.records().len();
    if contact_records < 2 {
        return Err(
            "the full CRST carries no unrelated returned-contact record for target ablation"
                .to_owned(),
        );
    }
    let rest_form = deposit_under_light(REST_FORM, &full_rest_bytes)?;

    let full_owner = full_rest
        .mount()
        .map_err(|error| format!("mount full returned owner: {error}"))?;
    let target_owner = target_rest
        .mount()
        .map_err(|error| format!("mount target returned owner: {error}"))?;
    let all_owner = all_rest
        .mount()
        .map_err(|error| format!("mount all returned owner: {error}"))?;

    let full_production = full_owner
        .produce(&query)
        .map_err(|error| format!("produce full returned branch: {error}"))?;
    let full_circuit = full_owner
        .found_circuit(&full_production, &query, APERTURE)
        .map_err(|error| format!("found full returned circuit: {error}"))?;
    let removed_site = target_owner
        .returned_records()
        .first()
        .ok_or_else(|| "the target branch carries no site to ablate".to_owned())?
        .site
        .to_owned();
    let removed_route = full_production
        .returned()
        .iter()
        .find(|route| route.site == removed_site)
        .ok_or_else(|| "the selected contact site emitted no companion".to_owned())?
        .passage
        .name
        .to_owned();
    let target_ablation = target_owner
        .ablate_site(&removed_site)
        .map_err(|error| format!("ablate one exact returned site: {error}"))?;
    let target_production = target_ablation
        .body
        .produce(&query)
        .map_err(|error| format!("produce target-ablated branch: {error}"))?;
    if target_production.returned().len() + 1 != full_production.returned().len()
        || target_production.returned().is_empty()
        || target_production
            .returned()
            .iter()
            .any(|route| route.site == removed_site)
        || target_production
            .returned()
            .iter()
            .any(|route| !full_production.returned().contains(route))
    {
        return Err("target ablation changed more than its one companion".to_owned());
    }
    let target_circuit = target_ablation
        .body
        .found_circuit(&target_production, &query, APERTURE)
        .map_err(|error| format!("found target-ablated circuit: {error}"))?;
    let full_cells: BTreeSet<_> = cell_addresses(&full_circuit)
        .map_err(|error| format!("address full returned circuit: {error}"))?
        .into_iter()
        .collect();
    let target_cells: BTreeSet<_> = cell_addresses(&target_circuit)
        .map_err(|error| format!("address target-ablated circuit: {error}"))?
        .into_iter()
        .collect();
    let removed_cells = full_cells
        .difference(&target_cells)
        .cloned()
        .collect::<Vec<_>>();
    let added_cells = target_cells
        .difference(&full_cells)
        .cloned()
        .collect::<Vec<_>>();
    if removed_cells.is_empty() || !added_cells.is_empty() {
        return Err("target ablation did not return one exact subtractive cell delta".to_owned());
    }
    let mut removed_cell_receipts = Vec::new();
    for cell in &removed_cells {
        let founders = passages_founding_address(&full_circuit, cell)
            .map_err(|error| format!("resolve target cell founder: {error}"))?;
        if !founders.contains(&removed_route) {
            return Err(
                "a target-removed cell was not founded by the removed companion".to_owned(),
            );
        }
        removed_cell_receipts.push(json!({"cell": cell, "founders": founders}));
    }

    let all_ablation = all_owner
        .ablate_all()
        .map_err(|error| format!("ablate complete returned fiber: {error}"))?;
    let all_production = all_ablation
        .body
        .produce(&query)
        .map_err(|error| format!("produce all-ablated branch: {error}"))?;
    if all_ablation.removed.len() != contact_records
        || !all_production.returned().is_empty()
        || content_address(&render_derived_passages(all_production.base()))
            != expectation.first_address
    {
        return Err(
            "complete returned-contact ablation did not restore the first production".to_owned(),
        );
    }

    std::fs::remove_file(reading_form)
        .map_err(|error| format!("delete sole mounted ReturnedReading: {error}"))?;
    match conduct_returned_contact(&body, &first, &reading, &contact, &mut executor) {
        Err(ReturnedConductBoundaryRefusal::AddressedReadFailed { path, .. })
            if path == reading_form => {}
        Err(error) => {
            return Err(format!(
                "deleting the ReturnedReading refused at the wrong boundary: {error}"
            ));
        }
        Ok(_) => return Err("conduct survived deletion of its sole ReturnedReading".to_owned()),
    }
    if executor.launches() != 3 {
        return Err("the deleted reading reached CUDA before refusal".to_owned());
    }

    let semantic_bytes = serde_json::to_vec_pretty(&full_semantic)
        .map_err(|error| format!("encode returned-contact semantic receipt: {error}"))?;
    let semantic_form = deposit_under_light(CONTACT_SEMANTIC_FORM, &semantic_bytes)?;
    let apparatus_bytes = serde_json::to_vec_pretty(&json!({
        "schema": "soma-life.returned-contact-apparatus-population.v1",
        "full": full_apparatus,
        "target_branch": target_apparatus,
        "all_branch": all_apparatus,
    }))
    .map_err(|error| format!("encode returned-contact apparatus receipt: {error}"))?;
    let apparatus_form = deposit_under_light(CONTACT_APPARATUS_FORM, &apparatus_bytes)?;

    let returned = json!({
        "schema": "soma-life.conditioning-return-conduct.v1",
        "source_roots_masked": masked,
        "unjoined_repeat_bit_identical": true,
        "four_forms_reread": true,
        "cuda_launches": 3,
        "rest": {
            "address": rest_form.address,
            "records": contact_records,
        },
        "semantic": {"address": semantic_form.address},
        "apparatus": {"address": apparatus_form.address},
        "deletion": {
            "removed_path": reading_form,
            "conduct_refused_before_cuda": true,
        },
        "target_ablation": {
            "site": removed_site,
            "companion": removed_route,
            "removed_cells": removed_cell_receipts,
            "target_only_cells": added_cells,
            "unrelated_companions_identical": true,
        },
        "all_ablation": {
            "removed_sites": all_ablation.removed.len(),
            "returned_routes_after": all_production.returned().len(),
            "restored_first_exactly": true,
        },
    });
    println!(
        "{}",
        serde_json::to_string(&returned)
            .map_err(|error| format!("encode detached conduct return: {error}"))?
    );
    Ok(())
}

fn successor(rest_form: &Path, expectation: &SuccessorExpectation) -> Result<(), String> {
    let masked = masked_roots(&expectation.source_roots)?;
    for departed in ["body.form", "first.form", "reading.form", "contact.form"] {
        if Path::new("/tmp/conditioning-return")
            .join(departed)
            .exists()
        {
            return Err(format!("the successor still sees departed {departed}"));
        }
    }
    if expectation.rest_occurrence != REST_OCCURRENCE {
        return Err("the addressed CRST occurrence moved".to_owned());
    }
    let addressed_rest = AddressedForm::new(
        rest_form.to_owned(),
        &expectation.rest_address,
        NativeFormSchema::ReturnedCompositeRest,
        expectation.rest_occurrence.to_owned(),
    )
    .map_err(|error| error.to_string())?;
    let rest_octets = read_exact(
        addressed_rest.path(),
        &addressed_rest.expected_content().render(),
    )?;
    let rest = ReturnedCompositeRest::decode_native_bytes(&rest_octets)
        .map_err(|error| format!("decode source-free CRST: {error}"))?;
    if rest
        .encode_native_bytes()
        .map_err(|error| format!("re-encode source-free CRST: {error}"))?
        .as_ref()
        != rest_octets.as_slice()
    {
        return Err("the source-free CRST did not reopen bit-identically".to_owned());
    }
    if rest.lineage().first_production().content().render() != expectation.first_address
        || rest.lineage().returned_reading().content().render() != expectation.reading_address
        || rest.lineage().returned_reading().occurrence().as_str() != expectation.reading_occurrence
    {
        return Err("the CRST lineage moved before source-free production".to_owned());
    }
    let reading_occurrence = rest
        .lineage()
        .returned_reading()
        .occurrence()
        .as_str()
        .to_owned();
    let repeated_owner = ReturnedCompositeRest::decode_native_bytes(&rest_octets)
        .map_err(|error| format!("decode independent CRST remount: {error}"))?
        .mount()
        .map_err(|error| format!("mount independent CRST remount: {error}"))?;
    let query = DerivationQuery::reaching(STATEMENT);
    let repeated = repeated_owner
        .produce(&query)
        .map_err(|error| format!("produce independent CRST remount: {error}"))?;
    let repeated_rest = repeated_owner
        .settle()
        .map_err(|error| format!("settle independent CRST remount: {error}"))?;
    if repeated_rest
        .encode_native_bytes()
        .map_err(|error| format!("encode independent settled CRST: {error}"))?
        .as_ref()
        != rest_octets.as_slice()
    {
        return Err("the independent CRST remount changed its continuing rest".to_owned());
    }
    drop(repeated_rest);
    let owner = rest
        .mount()
        .map_err(|error| format!("mount source-free returned body: {error}"))?;
    let production = owner
        .produce(&query)
        .map_err(|error| format!("produce source-free second turn: {error}"))?;
    if production != repeated || production.returned().is_empty() {
        return Err("the source-free returned production is empty or not a fixed point".to_owned());
    }
    if production
        .returned()
        .iter()
        .any(|route| route.passage.name.starts_with("returned_returned_"))
    {
        return Err("the returned conduct grew a route ladder".to_owned());
    }
    let base_bytes = render_derived_passages(production.base());
    if content_address(&base_bytes) != expectation.first_address {
        return Err("the fresh CRST base projection moved from the deposited first".to_owned());
    }

    let base_circuit = owner
        .base_circuit(&query, APERTURE)
        .map_err(|error| format!("found source-free base circuit: {error}"))?;
    let second_circuit = owner
        .found_circuit(&production, &query, APERTURE)
        .map_err(|error| format!("found source-free second circuit: {error}"))?;
    let movement = read_production(&base_circuit, &second_circuit, RULE, PIVOT, STATEMENT)
        .map_err(|error| format!("read source-free invariant movement: {error}"))?;
    if movement.movement.moved().is_empty() {
        return Err("the source-free second production moved no invariant".to_owned());
    }
    let base_cells: BTreeSet<_> = cell_addresses(&base_circuit)
        .map_err(|error| format!("address source-free base circuit: {error}"))?
        .into_iter()
        .collect();
    let second_cells: BTreeSet<_> = cell_addresses(&second_circuit)
        .map_err(|error| format!("address source-free second circuit: {error}"))?
        .into_iter()
        .collect();
    let withdrawn_cells = base_cells
        .difference(&second_cells)
        .cloned()
        .collect::<Vec<_>>();
    let founded_cells = second_cells
        .difference(&base_cells)
        .cloned()
        .collect::<Vec<_>>();
    if !withdrawn_cells.is_empty() || founded_cells.is_empty() {
        return Err(
            "the returned companions did not found one exact additive cell delta".to_owned(),
        );
    }

    let expected_source = format!(
        "{}@sha256:{}",
        expectation.reading_occurrence, expectation.reading_address
    );
    let mut movement_rows = Vec::new();
    let mut attributed_cells = BTreeSet::new();
    for moved in movement.movement.moved() {
        let mut cells = Vec::new();
        for cell in founded_cells
            .iter()
            .filter(|cell| cell.grade == moved.grade)
        {
            let founders = passages_founding_address(&second_circuit, cell)
                .map_err(|error| format!("resolve moved cell founder: {error}"))?;
            let mut causes = Vec::new();
            for founder in &founders {
                let Some(route) = production
                    .returned()
                    .iter()
                    .find(|route| &route.passage.name == founder)
                else {
                    continue;
                };
                let root = production
                    .base()
                    .iter()
                    .find(|root| PassageSite::of(root) == route.site)
                    .ok_or_else(|| {
                        "a returned companion no longer resolves its exact base site".to_owned()
                    })?;
                if route.causes.is_empty() {
                    return Err("a returned companion carries no exact cause".to_owned());
                }
                for cause in &route.causes {
                    if cause.occurrence.reading.form != reading_occurrence
                        || cause.source_lineage.source != expected_source
                        || cause.founded_route.as_ref().is_none_or(|address| {
                            address.statement != root.statement || address.passage != root.name
                        })
                    {
                        return Err(
                            "a moved cell names a cause outside the deposited return".to_owned()
                        );
                    }
                    causes.push(json!({
                        "companion": route.passage.name,
                        "occurrence": cause.occurrence,
                        "source_lineage": cause.source_lineage,
                        "founded_route": cause.founded_route,
                        "contact_cell": cause.cell,
                    }));
                }
            }
            if causes.is_empty() {
                return Err("a moved exact cell names no returned companion cause".to_owned());
            }
            if !attributed_cells.insert(cell.to_owned()) {
                return Err("one moved exact cell was attributed more than once".to_owned());
            }
            cells.push(json!({"cell": cell, "founders": founders, "caused_by": causes}));
        }
        if cells.is_empty() {
            return Err(format!(
                "invariant movement at grade {} names no moved exact cell",
                moved.grade
            ));
        }
        movement_rows.push(json!({
            "grade": moved.grade,
            "fields": moved.fields_moved().into_iter()
                .map(|field| format!("{field:?}"))
                .collect::<Vec<_>>(),
            "cells": cells,
        }));
    }
    let founded_population = founded_cells.iter().cloned().collect::<BTreeSet<_>>();
    if attributed_cells != founded_population {
        return Err("invariant attribution omitted or added an exact moved cell".to_owned());
    }
    let second_bytes = render_derived_passages(&production.passages());
    let second_form = deposit_under_light(SECOND_FORM, &second_bytes)?;
    let returned_routes = production.returned().len();
    let base_passages = production.base().len();
    let settled = owner
        .settle()
        .map_err(|error| format!("settle source-free returned body: {error}"))?;
    if settled
        .encode_native_bytes()
        .map_err(|error| format!("encode settled source-free CRST: {error}"))?
        .as_ref()
        != rest_octets.as_slice()
    {
        return Err("production changed the continuing CRST owner".to_owned());
    }

    let returned = json!({
        "schema": "soma-life.conditioning-return-successor.v1",
        "source_roots_masked": masked,
        "only_crst_mounted": true,
        "rest_occurrence": addressed_rest.occurrence(),
        "crst_reencoded_bit_identically": true,
        "independent_crst_remount_bit_identical": true,
        "no_returned_route_ladder": true,
        "base_projection_address": expectation.first_address,
        "base_passages": base_passages,
        "returned_routes": returned_routes,
        "founded_cells": founded_cells.len(),
        "withdrawn_cells": withdrawn_cells.len(),
        "invariant_movement": movement_rows,
        "second": {"address": second_form.address, "passages": base_passages + returned_routes},
        "continuing_rest_unchanged": true,
    });
    println!(
        "{}",
        serde_json::to_string(&returned)
            .map_err(|error| format!("encode successor return: {error}"))?
    );
    Ok(())
}

fn run_conduct_sandbox(
    workspace: &Path,
    body: &LightForm,
    first: &LightForm,
    reading: &LightForm,
    contact: &LightForm,
    expectation: &ConductExpectation,
) -> Result<Value, String> {
    let executable = std::env::current_exe()
        .and_then(|path| path.canonicalize())
        .map_err(|error| format!("resolve conditioning executable: {error}"))?;
    let transit = Transit::found(
        workspace,
        "conduct",
        &[
            ("deed", executable.as_path()),
            ("body.form", body.path.as_path()),
            ("first.form", first.path.as_path()),
            ("reading.form", reading.path.as_path()),
            ("contact.form", contact.path.as_path()),
        ],
    )?;
    let returns = ReturnDirectory::found(workspace, "conduct")?;
    let encoded = serde_json::to_string(expectation)
        .map_err(|error| format!("encode conduct expectation: {error}"))?;
    let output = sandbox_command(&transit, &returns, &expectation.source_roots, true)?
        .args([
            "--conduct",
            "/tmp/conditioning-return/body.form",
            "/tmp/conditioning-return/first.form",
            "/tmp/conditioning-return/reading.form",
            "/tmp/conditioning-return/contact.form",
        ])
        .arg(encoded)
        .output()
        .map_err(|error| format!("start detached returned conduct: {error}"))?;
    let returned = parse_sandbox_return(output, "detached returned conduct")?;
    for (name, path) in [
        (REST_FORM, "/rest/address"),
        (CONTACT_SEMANTIC_FORM, "/semantic/address"),
        (CONTACT_APPARATUS_FORM, "/apparatus/address"),
    ] {
        returns.admit(name, text_at(&returned, path)?)?;
    }
    returns.finish()?;
    transit.close()?;
    Ok(returned)
}

fn run_successor_sandbox(
    workspace: &Path,
    rest: &Path,
    expectation: &SuccessorExpectation,
) -> Result<Value, String> {
    let executable = std::env::current_exe()
        .and_then(|path| path.canonicalize())
        .map_err(|error| format!("resolve successor executable: {error}"))?;
    let transit = Transit::found(
        workspace,
        "successor",
        &[("deed", executable.as_path()), ("rest.form", rest)],
    )?;
    let returns = ReturnDirectory::found(workspace, "successor")?;
    let encoded = serde_json::to_string(expectation)
        .map_err(|error| format!("encode successor expectation: {error}"))?;
    let output = sandbox_command(&transit, &returns, &expectation.source_roots, false)?
        .args(["--successor", "/tmp/conditioning-return/rest.form"])
        .arg(encoded)
        .output()
        .map_err(|error| format!("start CRST-only successor: {error}"))?;
    let returned = parse_sandbox_return(output, "CRST-only successor")?;
    returns.admit(SECOND_FORM, text_at(&returned, "/second/address")?)?;
    returns.finish()?;
    transit.close()?;
    Ok(returned)
}

fn sandbox_command(
    transit: &Transit,
    returns: &ReturnDirectory,
    source_roots: &[PathBuf],
    writable_transit: bool,
) -> Result<Command, String> {
    let mut command = Command::new("bwrap");
    command
        .args(["--die-with-parent", "--new-session", "--unshare-net"])
        .args(["--ro-bind", "/", "/"])
        .args(["--dev-bind", "/dev", "/dev"])
        .args(["--proc", "/proc"])
        .args(["--tmpfs", "/tmp"])
        .args(["--dir", "/tmp/conditioning-return"])
        .args(["--dir", "/tmp/world"])
        .arg(if writable_transit {
            "--bind"
        } else {
            "--ro-bind"
        })
        .arg(&transit.root)
        .arg("/tmp/conditioning-return")
        .arg("--dir")
        .arg(format!("/tmp/world/{DRIVER}"))
        .arg("--bind")
        .arg(&returns.root)
        .arg(format!("/tmp/world/{DRIVER}"));
    for private_parent in [
        transit
            .root
            .parent()
            .expect("a transit child has its dedicated parent"),
        returns
            .root
            .parent()
            .expect("a return child has its dedicated parent"),
    ] {
        command.arg("--tmpfs").arg(private_parent);
    }
    for source in source_roots {
        command.arg("--tmpfs").arg(source);
    }
    command
        .args(["--chdir", "/tmp"])
        .arg("--")
        .arg("/tmp/conditioning-return/deed");
    Ok(command)
}

fn parse_sandbox_return(output: std::process::Output, deed: &str) -> Result<Value, String> {
    if !output.status.success() {
        return Err(format!(
            "{deed} failed: {}",
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    serde_json::from_slice(&output.stdout).map_err(|error| format!("read {deed} return: {error}"))
}

struct Transit {
    root: PathBuf,
    files: Vec<PathBuf>,
    closed: bool,
}

impl Transit {
    fn found(workspace: &Path, label: &str, sources: &[(&str, &Path)]) -> Result<Self, String> {
        let parent = workspace
            .parent()
            .ok_or_else(|| "the workspace has no exterior parent for transit".to_owned())?;
        let private_parent = parent.join(".holonics-plan2-transit");
        std::fs::create_dir_all(&private_parent).map_err(|error| {
            format!(
                "found dedicated transit parent {}: {error}",
                private_parent.display()
            )
        })?;
        let root = private_parent.join(format!("{}-{label}", std::process::id()));
        std::fs::create_dir(&root).map_err(|error| {
            format!("found exact transit directory {}: {error}", root.display())
        })?;
        let mut files = Vec::new();
        for (name, source) in sources {
            let destination = root.join(name);
            if let Err(error) = std::fs::hard_link(source, &destination) {
                for path in &files {
                    let _ = std::fs::remove_file(path);
                }
                let _ = std::fs::remove_dir(&root);
                return Err(format!(
                    "hardlink {} into exact transit: {error}",
                    source.display()
                ));
            }
            files.push(destination);
        }
        Ok(Self {
            root,
            files,
            closed: false,
        })
    }

    fn close(mut self) -> Result<(), String> {
        for path in &self.files {
            match std::fs::remove_file(path) {
                Ok(()) => {}
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
                Err(error) => {
                    return Err(format!(
                        "remove exact transit form {}: {error}",
                        path.display()
                    ));
                }
            }
        }
        std::fs::remove_dir(&self.root).map_err(|error| {
            format!(
                "close exact transit directory {}: {error}",
                self.root.display()
            )
        })?;
        if let Some(parent) = self.root.parent() {
            let _ = std::fs::remove_dir(parent);
        }
        self.closed = true;
        Ok(())
    }
}

impl Drop for Transit {
    fn drop(&mut self) {
        if self.closed {
            return;
        }
        for path in &self.files {
            match std::fs::remove_file(path) {
                Ok(()) => {}
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
                Err(_) => {}
            }
        }
        let _ = std::fs::remove_dir(&self.root);
    }
}

/// An initially empty exterior mouth.  The sandbox can write here, but it cannot see any earlier
/// output artifact through this mount.  The parent admits only the exact named/hash-checked forms.
struct ReturnDirectory {
    root: PathBuf,
    closed: bool,
}

impl ReturnDirectory {
    fn found(workspace: &Path, label: &str) -> Result<Self, String> {
        let parent = workspace
            .parent()
            .ok_or_else(|| "the workspace has no exterior parent for returned forms".to_owned())?;
        let private_parent = parent.join(".holonics-plan2-return");
        std::fs::create_dir_all(&private_parent).map_err(|error| {
            format!(
                "found dedicated return parent {}: {error}",
                private_parent.display()
            )
        })?;
        let root = private_parent.join(format!("{}-{label}", std::process::id()));
        std::fs::create_dir(&root)
            .map_err(|error| format!("found empty return directory {}: {error}", root.display()))?;
        Ok(Self {
            root,
            closed: false,
        })
    }

    fn admit(&self, name: &str, address: &str) -> Result<LightForm, String> {
        ContentAddress::parse(address).map_err(|error| error.to_string())?;
        let file_name = format!("{name}-{address}.form");
        let source = self.root.join(&file_name);
        if sha256_file(&source)? != address {
            return Err(format!(
                "the sandbox return {} does not carry its declared address",
                source.display()
            ));
        }
        let output = Path::new("output").join(DRIVER);
        std::fs::create_dir_all(&output)
            .map_err(|error| format!("found canonical output mouth: {error}"))?;
        let destination = output.join(file_name);
        if destination.exists() {
            if sha256_file(&destination)? != address {
                return Err(format!(
                    "the canonical destination {} carries different content",
                    destination.display()
                ));
            }
            std::fs::remove_file(&source).map_err(|error| {
                format!(
                    "remove redundant exact sandbox return {}: {error}",
                    source.display()
                )
            })?;
        } else {
            std::fs::rename(&source, &destination).map_err(|error| {
                format!(
                    "admit exact sandbox return {} as {}: {error}",
                    source.display(),
                    destination.display()
                )
            })?;
        }
        Ok(LightForm {
            path: destination,
            address: address.to_owned(),
        })
    }

    fn finish(mut self) -> Result<(), String> {
        if std::fs::read_dir(&self.root)
            .map_err(|error| format!("inspect exact return directory: {error}"))?
            .next()
            .is_some()
        {
            return Err("the sandbox returned an undeclared extra form".to_owned());
        }
        std::fs::remove_dir(&self.root)
            .map_err(|error| format!("close exact return directory: {error}"))?;
        if let Some(parent) = self.root.parent() {
            let _ = std::fs::remove_dir(parent);
        }
        self.closed = true;
        Ok(())
    }
}

impl Drop for ReturnDirectory {
    fn drop(&mut self) {
        if !self.closed {
            let _ = std::fs::remove_dir(&self.root);
        }
    }
}

fn masked_roots(roots: &[PathBuf]) -> Result<Vec<(String, bool)>, String> {
    let mut masked = Vec::new();
    for root in roots {
        let empty = std::fs::read_dir(root)
            .map_err(|error| format!("inspect masked source root {}: {error}", root.display()))?
            .next()
            .is_none();
        masked.push((root.display().to_string(), empty));
    }
    if masked.iter().any(|(_, empty)| !empty) {
        return Err("a declared source root remained reachable".to_owned());
    }
    Ok(masked)
}

fn inspect_conduct_return(returned: &Value) -> Result<(), String> {
    for path in [
        "/unjoined_repeat_bit_identical",
        "/four_forms_reread",
        "/deletion/conduct_refused_before_cuda",
        "/target_ablation/unrelated_companions_identical",
        "/all_ablation/restored_first_exactly",
    ] {
        if returned.pointer(path).and_then(Value::as_bool) != Some(true) {
            return Err(format!("detached conduct did not establish {path}"));
        }
    }
    if returned.pointer("/cuda_launches").and_then(Value::as_u64) != Some(3)
        || returned
            .pointer("/target_ablation/removed_cells")
            .and_then(Value::as_array)
            .is_none_or(Vec::is_empty)
        || returned
            .pointer("/all_ablation/returned_routes_after")
            .and_then(Value::as_u64)
            != Some(0)
    {
        return Err("the detached conduct omitted its exact GPU or ablation return".to_owned());
    }
    inspect_mask(returned, "/source_roots_masked")
}

fn inspect_successor_return(returned: &Value) -> Result<(), String> {
    for path in [
        "/only_crst_mounted",
        "/crst_reencoded_bit_identically",
        "/independent_crst_remount_bit_identical",
        "/no_returned_route_ladder",
        "/continuing_rest_unchanged",
    ] {
        if returned.pointer(path).and_then(Value::as_bool) != Some(true) {
            return Err(format!("source-free successor did not establish {path}"));
        }
    }
    if returned
        .pointer("/returned_routes")
        .and_then(Value::as_u64)
        .is_none_or(|count| count == 0)
        || returned
            .pointer("/invariant_movement")
            .and_then(Value::as_array)
            .is_none_or(Vec::is_empty)
    {
        return Err("the source-free successor returned no attributable movement".to_owned());
    }
    inspect_mask(returned, "/source_roots_masked")
}

fn inspect_mask(returned: &Value, path: &str) -> Result<(), String> {
    let masked = returned
        .pointer(path)
        .and_then(Value::as_array)
        .ok_or_else(|| format!("return omitted {path}"))?;
    if masked.is_empty()
        || masked
            .iter()
            .any(|entry| entry.get(1).and_then(Value::as_bool) != Some(true))
    {
        return Err("a declared source root was not masked".to_owned());
    }
    Ok(())
}

fn text_at<'a>(value: &'a Value, path: &str) -> Result<&'a str, String> {
    value
        .pointer(path)
        .and_then(Value::as_str)
        .ok_or_else(|| format!("return omitted text at {path}"))
}

fn addressed(
    form: &LightForm,
    schema: NativeFormSchema,
    occurrence: &str,
) -> Result<AddressedForm, String> {
    AddressedForm::new(
        form.path.to_owned(),
        &form.address,
        schema,
        occurrence.to_owned(),
    )
    .map_err(|error| error.to_string())
}

fn deposit_light(name: &str, octets: &[u8]) -> Result<LightForm, String> {
    let DepositedForm {
        path,
        address,
        octets,
    } = deposit_form_or_message(DRIVER, name, octets)?;
    drop(octets);
    Ok(LightForm { path, address })
}

fn deposit_under_light(name: &str, octets: &[u8]) -> Result<LightForm, String> {
    let DepositedForm {
        path,
        address,
        octets,
    } = deposit_form_under(Path::new("/tmp/world"), DRIVER, name, octets)
        .map_err(|error| error.to_string())?;
    drop(octets);
    Ok(LightForm { path, address })
}

fn output_form_path(name: &str, address: &str) -> PathBuf {
    Path::new("output")
        .join(DRIVER)
        .join(format!("{name}-{address}.form"))
}

fn read_exact(path: &Path, expected: &str) -> Result<Vec<u8>, String> {
    let octets = std::fs::read(path)
        .map_err(|error| format!("read addressed form {}: {error}", path.display()))?;
    if content_address(&octets) != expected {
        return Err(format!("the addressed form {} moved", path.display()));
    }
    Ok(octets)
}

/// Every exact ASCII word that could occur inside one identifier this standing recruits.
fn receiver_features(recruited: &BTreeSet<String>) -> BTreeSet<String> {
    let mut features = BTreeSet::new();
    for identifier in recruited {
        let mut run = Vec::new();
        let mut finish_run = |run: &mut Vec<u8>| {
            for start in 0..run.len() {
                for end in start + 1..=run.len() {
                    let feature = String::from_utf8(run[start..end].to_vec())
                        .expect("an ASCII alphabetic run is UTF-8");
                    features.insert(feature.to_ascii_lowercase());
                }
            }
            run.clear();
        };
        for octet in identifier.bytes() {
            if octet.is_ascii_alphabetic() {
                run.push(octet);
            } else if !run.is_empty() {
                finish_run(&mut run);
            }
        }
        if !run.is_empty() {
            finish_run(&mut run);
        }
    }
    features
}

fn source_occurrence_identity(section: &LaboratoryReturnedSection) -> Result<&str, String> {
    let (occurrence, local) = section
        .source_identity
        .rsplit_once("/surface-")
        .ok_or_else(|| {
            format!(
                "the resident section {:?} does not name its source occurrence",
                section.source_identity
            )
        })?;
    let local = local.parse::<usize>().map_err(|error| {
        format!(
            "the resident section {:?} has a malformed local address: {error}",
            section.source_identity
        )
    })?;
    if local != section.line {
        return Err(format!(
            "the resident section {:?} says line {} in its identity and {} in its chart",
            section.source_identity, local, section.line
        ));
    }
    Ok(occurrence)
}

fn standing(root: &Path) -> Result<Vec<(String, String)>, String> {
    fn lean_artifacts(root: &Path, found: &mut Vec<PathBuf>) -> Result<(), String> {
        let mut entries = std::fs::read_dir(root)
            .map_err(|error| format!("read mathematical standing {}: {error}", root.display()))?
            .collect::<Result<Vec<_>, _>>()
            .map_err(|error| format!("walk mathematical standing {}: {error}", root.display()))?;
        entries.sort_by_key(|entry| entry.path());
        for entry in entries {
            let path = entry.path();
            let kind = entry.file_type().map_err(|error| {
                format!("type mathematical artifact {}: {error}", path.display())
            })?;
            if kind.is_dir() {
                lean_artifacts(&path, found)?;
            } else if kind.is_file()
                && path
                    .extension()
                    .is_some_and(|extension| extension == "lean")
            {
                found.push(path);
            }
        }
        Ok(())
    }

    let mut artifacts = Vec::new();
    lean_artifacts(root, &mut artifacts)?;
    if artifacts.is_empty() {
        return Err(format!(
            "the declared mathematical standing {} contains no Lean artifacts",
            root.display()
        ));
    }
    artifacts
        .into_iter()
        .map(|path| {
            let text = std::fs::read_to_string(&path).map_err(|error| {
                format!("read mathematical artifact {}: {error}", path.display())
            })?;
            Ok((path.display().to_string(), text))
        })
        .collect()
}

fn sha256_file(path: &Path) -> Result<String, String> {
    let mut file = File::open(path)
        .map_err(|error| format!("open {} for its address: {error}", path.display()))?;
    let mut digest = Sha256::new();
    let mut buffer = vec![0u8; 1 << 20];
    loop {
        let read = file
            .read(&mut buffer)
            .map_err(|error| format!("read {} for its address: {error}", path.display()))?;
        if read == 0 {
            break;
        }
        digest.update(&buffer[..read]);
    }
    let mut address = String::new();
    for octet in digest.finalize() {
        use std::fmt::Write as _;
        write!(&mut address, "{octet:02x}").expect("writing into a string cannot fail");
    }
    Ok(address)
}
