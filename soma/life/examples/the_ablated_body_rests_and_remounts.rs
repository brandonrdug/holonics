//! **An ablated conditioned body rests, departs from its source, and remounts field for field** —
//! with the gap its ablation left in the identities still in it.
//!
//! ```text
//! cargo run --release -p life --example the_ablated_body_rests_and_remounts
//! ```
//!
//! ## The edge this closes
//!
//! `FoundedMorphology::without_stem` keeps the surviving stems' original `StemId`s, so an ablated
//! population is not numbered `0..n`. Until now the only constructor a foreign owner could come back
//! through was `from_founded_words`, which **derives** identity from arrival order — so an ablated
//! body could not be put back together, and `life::conditioned_rest` refused to seal one rather than
//! write a form that would mount as a different body. The refusal was right; the constructor was
//! missing.
//!
//! `FoundedMorphology::from_founded_stems` is that constructor. It carries identity and parent
//! verbatim and refuses a population no founding could have produced. The emitting half of the loop
//! now returns: an ablation goes out to disk and comes back.
//!
//! **Why the identities are worth keeping rather than renumbering.** The gap where the removed stem
//! stood *is* the record of the ablation. Renumbering closes it, and a body that has been ablated
//! then becomes indistinguishable from one that was founded on the smaller corpus. That is removing
//! chronology, and the whole of what an ablation is evidence of is the difference between those two
//! bodies.
//!
//! ## The four slots
//!
//! ```text
//!   source geometry   a founded morphology with one stem structurally removed
//!   receiver map      the CDER wire: identity, parent, named wholes, foreign lineage
//!   transport         seal -> octets -> disk -> chdir out of the repository -> decode -> mount
//!   returned residual the remounted body's own records and its production, compared whole
//! ```
//!
//! ## What each declared control can be wrong about
//!
//! - **The round trip could be vacuous.** If the ablated stem were the **last** one founded, the
//!   surviving identities would still be `0..n-1` and the founding seam would reproduce them, so the
//!   round trip would prove nothing about the resumption seam. The stem chosen here is required to
//!   be one the founding seam **does** renumber, and the founding seam is run alongside and required
//!   to return a different population. That control fails on exactly one material: ablating the
//!   last-founded stem.
//! - **The ablation could remove nothing.** A stem whose removal changes no production would make
//!   every equality below an equality between two identical bodies. The stem is chosen from the
//!   licensing population and `StemAblation::removes_structure` is required.
//! - **The remount could be a replay.** The wire has no field for a query or a derived passage, the
//!   corpus and the deposit are opened after the chdir and every open is required to fail, and the
//!   resumed body is asked a statement no body was asked before the seal.
//! - **The seal could have been weakened into a launder.** Four populations that no founding could
//!   have produced are written by a **foreign** writer of this module's wire and presented to the
//!   decoder; each must refuse by its own name. That foreign writer is first checked against the
//!   module's own encoder on the unchanged population, so "the forgery was refused" cannot mean "the
//!   forger is broken". A fifth defective body arrives through `serde`, having never been founded,
//!   and is refused at the seal.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use holonic_engine::conditioned_derivation::{
    ablate_stem, expose, ConditionedBody, DerivationQuery, DerivedPassage, Exposure,
    FoundedMorphology, FoundedMorphologyRefusal, FoundedStem, StemAblation, StemId, StemStanding,
};
use holonic_engine::derivation_atlas::CircuitAperture;
use life::conditioned_rest::{
    records, render_derived_passages, ConditionedRest, ConditionedRestRefusal, FoundedStemRecord,
    CONDITIONED_REST_PREFIX,
};
use life::form_mouth::{deposit_form, DepositedForm};

// -------------------------------------------------------------------------------------------------
// The declaration
// -------------------------------------------------------------------------------------------------

/// **The declared corpus.** Real deposited mathematics, named rather than globbed, each document
/// read as one whole so that a commitment is a recurrence across **distinct documents**.
const CORPUS: &[&str] = &[
    "papers/source/mathematics/theorems/weil-support-induction-reduction.typ",
    "papers/source/mathematics/theorems/conditioned-support-quotient-shorting.typ",
    "papers/source/mathematics/theorems/conditioned-effective-tension.typ",
    "papers/source/mathematics/theorems/prime-power-aperture-incidence.typ",
    "papers/source/mathematics/theorems/prime-power-hinge-cell-recurrence.typ",
    "papers/source/mathematics/theorems/archimedean-remainder-amplitude.typ",
    "papers/source/mathematics/theorems/causal-parity-kirchhoff-return.typ",
    "papers/source/mathematics/theorems/dyadic-character-filler-bound.typ",
    "papers/source/mathematics/lemmas/situated-mean-transport.typ",
    "papers/source/mathematics/lemmas/geometric-remainder-squeeze.typ",
    "papers/source/mathematics/lemmas/first-prime-capacitance-completion.typ",
    "papers/source/mathematics/corollaries/archimedean-carrier-prime-boundary.typ",
    "papers/source/mathematics/definitions/receiver-configuration-calculus.typ",
    "papers/source/mathematics/definitions/graded-arithmetic-accessibility-current.typ",
];

/// **The declared standing derivation deposit.**
const DEPOSIT: &str = "standing/output";

/// **The statement asked before the seal.**
const SEALED_QUERY: &str = "(h : P) : exactCarrier P";

/// **The statement asked only after the seal.**
const UNASKED_QUERY: &str = "(a b : Nat) : a = b";

const DRIVER: &str = "the_ablated_body_rests_and_remounts";
const FORM_SITE: &str = "ablated-conditioned-rest";

/// **The declared further whole**, presented to the resumed ablated rest. Written here, not read off
/// disk: after the rest, nothing is.
const FURTHER_WHOLE: (&str, &str) = (
    "document:presented-after-the-rest",
    "A receiver family founded after the rest carries the exact transport of a formal kernel.",
);

// -------------------------------------------------------------------------------------------------
// The exterior codecs
// -------------------------------------------------------------------------------------------------

/// Every `.lean` artifact under `root`, in a stable order.
fn deposit_artifacts(root: &Path) -> Vec<PathBuf> {
    let mut found = Vec::new();
    let Ok(entries) = std::fs::read_dir(root) else {
        return found;
    };
    let mut here: Vec<PathBuf> = entries.flatten().map(|entry| entry.path()).collect();
    here.sort();
    for path in here {
        if path.is_dir() {
            found.extend(deposit_artifacts(&path));
        } else if path.extension().is_some_and(|carried| carried == "lean") {
            found.push(path);
        }
    }
    found
}

/// **A foreign writer of the CDER wire**, written against the layout stated in
/// `life::conditioned_rest`'s header and not against that module's encoder.
///
/// It exists so that a population no founding could have produced can be presented to the decoder,
/// which is the only mouth that takes one.
fn forge(stems: &[FoundedStemRecord], standing: &[(String, String)]) -> Vec<u8> {
    fn run(octets: &mut Vec<u8>, text: &str) {
        octets.extend_from_slice(&(text.len() as u64).to_le_bytes());
        octets.extend_from_slice(text.as_bytes());
    }
    let mut octets = Vec::new();
    octets.extend_from_slice(&CONDITIONED_REST_PREFIX);
    octets.extend_from_slice(&(stems.len() as u64).to_le_bytes());
    for record in stems {
        octets.extend_from_slice(&record.id.to_le_bytes());
        run(&mut octets, &record.stem);
        match record.parent {
            None => octets.push(0),
            Some(parent) => {
                octets.push(1);
                octets.extend_from_slice(&parent.to_le_bytes());
            }
        }
        octets.extend_from_slice(&(record.wholes.len() as u64).to_le_bytes());
        for whole in &record.wholes {
            run(&mut octets, whole);
        }
        octets.extend_from_slice(&(record.foreign_lineage.len() as u64).to_le_bytes());
        for entry in &record.foreign_lineage {
            run(&mut octets, entry);
        }
    }
    octets.extend_from_slice(&(standing.len() as u64).to_le_bytes());
    for (source, text) in standing {
        run(&mut octets, source);
        run(&mut octets, text);
    }
    octets
}

// -------------------------------------------------------------------------------------------------
// Reading
// -------------------------------------------------------------------------------------------------

fn rule(title: &str) {
    println!("\n{}", "=".repeat(98));
    println!("{title}");
    println!("{}", "=".repeat(98));
}

struct Controls {
    failed: Vec<String>,
}

impl Controls {
    fn new() -> Self {
        Self { failed: Vec::new() }
    }

    fn check(&mut self, name: &str, holds: bool, saying: &str) {
        println!(
            "  [{}] {name}\n        {saying}",
            if holds { "holds" } else { "FAILS" }
        );
        if !holds {
            self.failed.push(name.to_owned());
        }
    }
}

/// Every stem record that differs across two populations, exhibited whole.
fn record_differences(before: &[FoundedStemRecord], after: &[FoundedStemRecord]) -> Vec<String> {
    let mut differing = Vec::new();
    for (at, earlier) in before.iter().enumerate() {
        match after.get(at) {
            None => differing.push(format!("position {at}: {} departed", earlier.render())),
            Some(later) if later == earlier => {}
            Some(later) => differing.push(format!(
                "position {at}:\n              before {}\n              after  {}",
                earlier.render(),
                later.render()
            )),
        }
    }
    for extra in after.iter().skip(before.len()) {
        differing.push(format!("appeared {}", extra.render()));
    }
    differing
}

fn exhibit(passage: &DerivedPassage) {
    println!("\n  {}", passage.name);
    println!(
        "      licensed by stem {:?}   brought {}   reaches {}",
        passage.stem, passage.brought, passage.reaches
    );
    for line in passage.text.lines() {
        println!("      | {line}");
    }
}

fn main() {
    let mut controls = Controls::new();

    rule("THE ABLATED BODY RESTS AND REMOUNTS -- an ablation goes to disk and comes back");

    let invocation = std::env::current_dir().expect("the invocation directory");
    println!("\n  invoked in {}", invocation.display());

    // ---------------------------------------------------------------------------------------------
    rule("[1]  THE CONDITIONING -- real deposited mathematics, one whole per document");

    let mut exposures: Vec<Exposure> = Vec::new();
    for path in CORPUS {
        match std::fs::read_to_string(path) {
            Ok(text) => exposures.push(expose(&format!("document:{path}"), &text)),
            Err(error) => {
                eprintln!("{path}: {error}");
                std::process::exit(2);
            }
        }
    }
    let artifacts = deposit_artifacts(Path::new(DEPOSIT));
    let deposit: Vec<(String, String)> = artifacts
        .iter()
        .filter_map(|path| {
            std::fs::read_to_string(path)
                .ok()
                .map(|text| (path.display().to_string(), text))
        })
        .collect();
    if deposit.is_empty() {
        eprintln!("the declared standing deposit {DEPOSIT} holds no readable Lean artifact");
        std::process::exit(2);
    }

    let mut whole = match ConditionedBody::mount(deposit.clone()) {
        Ok(body) => body,
        Err(refusal) => {
            eprintln!("the deposit was refused: {refusal}");
            std::process::exit(2);
        }
    };
    whole.condition(&exposures);
    let founded = whole.morphology().clone();

    println!(
        "\n  {} documents, {} standing artifacts",
        CORPUS.len(),
        deposit.len()
    );
    println!(
        "  founded {}   committed {}   provisional {}   recruited identifiers {}",
        founded.founded().len(),
        founded.committed().len(),
        founded.provisional().len(),
        whole.recruited_population().len()
    );

    let statements = whole.standing_statements();
    for declared in [SEALED_QUERY, UNASKED_QUERY] {
        if !statements.contains(declared) {
            eprintln!("the declared query is not a statement this deposit reaches: {declared}");
            std::process::exit(2);
        }
    }
    let sealed_query = DerivationQuery::reaching(SEALED_QUERY);
    let unasked_query = DerivationQuery::reaching(UNASKED_QUERY);

    let unablated = whole.derive(&sealed_query).expect("derives");
    println!(
        "  the unablated body returns {} passages on {SEALED_QUERY:?}",
        unablated.len()
    );

    // ---------------------------------------------------------------------------------------------
    rule("[2]  THE ABLATION -- a licensing stem removed, chosen so the identities really gap");

    let last_founded = founded
        .founded()
        .last()
        .map(|stem| stem.stem.clone())
        .expect("the corpus founded something");
    let licensing: BTreeSet<&str> = unablated
        .iter()
        .map(|passage| passage.stem.as_str())
        .collect();

    let mut chosen: Option<(String, StemAblation)> = None;
    let mut rejected_for_no_gap: Vec<String> = Vec::new();
    let mut rejected_for_no_structure: Vec<String> = Vec::new();
    for stem in &licensing {
        if *stem == last_founded {
            rejected_for_no_gap.push((*stem).to_owned());
            continue;
        }
        let ablation = match ablate_stem(
            &whole,
            stem,
            &sealed_query,
            CircuitAperture::STATEMENT_INCIDENT,
        ) {
            Ok(ablation) => ablation,
            Err(refusal) => {
                eprintln!("the ablation was refused: {refusal}");
                std::process::exit(2);
            }
        };
        if ablation.removes_structure() {
            chosen = Some(((*stem).to_owned(), ablation));
            break;
        }
        rejected_for_no_structure.push((*stem).to_owned());
    }
    let Some((removed, ablation)) = chosen else {
        eprintln!(
            "no licensing stem's removal removes structure; the material cannot exercise this driver"
        );
        std::process::exit(2);
    };

    println!(
        "\n  {} stems license the production. The stem removed is {removed:?}.",
        licensing.len()
    );
    if !rejected_for_no_structure.is_empty() {
        println!(
            "  passed over because their removal removes no structure: {rejected_for_no_structure:?}"
        );
    }
    if !rejected_for_no_gap.is_empty() {
        println!(
            "  passed over because they are the LAST founded stem, whose removal leaves no gap in \
             the identities: {rejected_for_no_gap:?}"
        );
    }
    println!(
        "\n  the removal took the production from {} passages to {}",
        ablation.passages_before.len(),
        ablation.passages_after.len()
    );
    println!(
        "    {} passages structurally absent, {} circuit cells absent, {} reopened, {} unaccounted",
        ablation.passages_absent.len(),
        ablation.cells_absent.len(),
        ablation.reopened.len(),
        ablation.unaccounted.len()
    );
    for passage in ablation.passages_absent.iter().take(2) {
        exhibit(passage);
    }

    let ablated = whole.without_stem(&removed).expect("the stem was founded");
    let ablated_records = records(ablated.morphology());
    let removed_identity = founded.stem(&removed).expect("founded").id;
    let ablated_before = ablated.derive(&sealed_query).expect("derives");

    println!(
        "\n  the removed stem carried identity {}. The surviving identities now run",
        removed_identity.0
    );
    let neighbourhood: Vec<u64> = ablated_records
        .iter()
        .map(|record| record.id)
        .filter(|id| id.saturating_add(3) >= removed_identity.0 && *id <= removed_identity.0 + 3)
        .collect();
    println!("    ... {neighbourhood:?} ...   with {} absent", removed_identity.0);

    // ---------------------------------------------------------------------------------------------
    rule("[3]  THE FOUNDING SEAM CANNOT CARRY IT -- and that is why this driver is not vacuous");

    let replayed = FoundedMorphology::from_founded_words(ablated_records.iter().map(|record| {
        (
            record.stem.clone(),
            record.wholes.clone(),
            record.foreign_lineage.clone(),
        )
    }));
    let replayed_records = records(&replayed);
    let replay_differences = record_differences(&ablated_records, &replayed_records);

    println!(
        "\n  `from_founded_words` replays the founding, so it derives identity from arrival order.\n  \
         Handed the ablated population it returns {} of {} stems differing:",
        replay_differences.len(),
        ablated_records.len()
    );
    for difference in replay_differences.iter().take(3) {
        println!("    {difference}");
    }
    let identities_are_contiguous = ablated_records
        .iter()
        .enumerate()
        .all(|(at, record)| record.id == at as u64);
    println!(
        "\n  The surviving identities are {} contiguous from zero. If the removed stem had been the\n  \
         LAST founded one they would be, this population would be identical, and every equality in\n  \
         [5] would hold for a body that was never renumbered. That is the exact material that makes\n  \
         the control below fail.",
        if identities_are_contiguous { "" } else { "NOT" }
    );

    // ---------------------------------------------------------------------------------------------
    rule("[4]  THE SEAL AND THE DEPARTURE -- the ablated body to octets, then out of the repository");

    let rest = match ConditionedRest::seal(&ablated) {
        Ok(rest) => rest,
        Err(refusal) => {
            eprintln!("{refusal}");
            std::process::exit(1);
        }
    };
    let octets = rest.encode_native_bytes().expect("the wire");
    let deposited: DepositedForm = match deposit_form(DRIVER, FORM_SITE, &octets) {
        Ok(deposited) => deposited,
        Err(refusal) => {
            eprintln!("{refusal}");
            std::process::exit(1);
        }
    };
    let sealed_path = std::fs::canonicalize(&deposited.path).expect("the form is on disk");

    println!("\n  the ablated body sealed:");
    println!("    founded stems      {}", rest.stems().len());
    println!("    standing artifacts {}", rest.standing().len());
    println!("    {} octets   address {}", octets.len(), deposited.address);
    println!("    {}", sealed_path.display());
    println!("\n  the census of the sealed form, recomputed by mounting it");
    for (field, value) in rest.census_rows().expect("a census") {
        println!("    {field:<24} {value}");
    }

    let elsewhere = std::env::temp_dir().join(format!("{DRIVER}-departed"));
    let _ = std::fs::remove_dir_all(&elsewhere);
    std::fs::create_dir_all(&elsewhere).expect("a working directory outside the repository");
    std::env::set_current_dir(&elsewhere).expect("depart");

    let mut reachable: Vec<String> = Vec::new();
    let mut refusals: BTreeMap<String, usize> = BTreeMap::new();
    let mut open_attempts = 0usize;
    for path in CORPUS.iter().copied() {
        open_attempts += 1;
        match std::fs::File::open(path) {
            Ok(_) => reachable.push(path.to_owned()),
            Err(error) => *refusals.entry(format!("{:?}", error.kind())).or_default() += 1,
        }
    }
    for artifact in &artifacts {
        open_attempts += 1;
        match std::fs::File::open(artifact) {
            Ok(_) => reachable.push(artifact.display().to_string()),
            Err(error) => *refusals.entry(format!("{:?}", error.kind())).or_default() += 1,
        }
    }
    open_attempts += 1;
    match std::fs::read_dir(DEPOSIT) {
        Ok(_) => reachable.push(DEPOSIT.to_owned()),
        Err(error) => *refusals.entry(format!("{:?}", error.kind())).or_default() += 1,
    }

    println!(
        "\n  the process working directory is now {}\n  {open_attempts} opens attempted against the \
         declared corpus, the deposited artifacts and the deposit root:",
        elsewhere.display()
    );
    for (kind, count) in &refusals {
        println!("    {count:>4} refused with ErrorKind::{kind}");
    }
    if reachable.is_empty() {
        println!("       0 opened");
    } else {
        println!("    {} OPENED, which fails this driver:", reachable.len());
        for path in &reachable {
            println!("         {path}");
        }
    }

    // ---------------------------------------------------------------------------------------------
    rule("[5]  THE REMOUNT -- field for field against the ablated body, identities included");

    let from_disk = std::fs::read(&sealed_path).expect("the sealed form");
    let reopened = match ConditionedRest::decode_native_bytes(&from_disk) {
        Ok(reopened) => reopened,
        Err(refusal) => {
            eprintln!("{refusal}");
            std::process::exit(1);
        }
    };
    let remounted = match reopened.mount() {
        Ok(body) => body,
        Err(refusal) => {
            eprintln!("{refusal}");
            std::process::exit(1);
        }
    };
    let remounted_records = records(remounted.morphology());
    let remount_differences = record_differences(&ablated_records, &remounted_records);

    println!(
        "\n  {} octets read back. {} founded stems, compared record for record against the ablated\n  \
         body -- identity, parent, named wholes, foreign lineage: {} differ.",
        from_disk.len(),
        remounted_records.len(),
        remount_differences.len()
    );
    for difference in remount_differences.iter().take(10) {
        println!("    {difference}");
    }

    let identities_before: Vec<u64> = ablated_records.iter().map(|record| record.id).collect();
    let identities_after: Vec<u64> = remounted_records.iter().map(|record| record.id).collect();
    let gap_survived = !identities_after.contains(&removed_identity.0);
    println!(
        "\n  the identity {} the removed stem carried is {} in the remounted population.",
        removed_identity.0,
        if gap_survived { "ABSENT" } else { "present" }
    );
    println!(
        "  the stem {removed:?} itself is {} in the remounted population.",
        if remounted.morphology().stem(&removed).is_none() {
            "absent"
        } else {
            "present"
        }
    );

    let ablated_after = remounted.derive(&sealed_query).expect("derives");
    let rendered_before = render_derived_passages(&ablated_before);
    let rendered_after = render_derived_passages(&ablated_after);
    println!(
        "\n  the production on {SEALED_QUERY:?}: {} passages before the rest, {} after;\n  \
         {} rendered octets against {}, over every field of every passage and every bridge.",
        ablated_before.len(),
        ablated_after.len(),
        rendered_before.len(),
        rendered_after.len()
    );

    let answered = remounted.derive(&unasked_query).expect("derives");
    let cross_check = ablated.derive(&unasked_query).expect("derives");
    println!(
        "\n  asked {UNASKED_QUERY:?}, which no body was asked before the seal: the remounted body\n  \
         returns {} passages and the pre-rest ablated body, asked now for the first time, returns {}.",
        answered.len(),
        cross_check.len()
    );

    // ---------------------------------------------------------------------------------------------
    rule("[6]  THE SEAL STILL REFUSES -- five populations no founding could have produced");

    let stems = reopened.stems().to_vec();
    let standing = reopened.standing().to_vec();

    // the positive control on the forger itself
    let forged_sound = forge(&stems, &standing);
    let reforged = ConditionedRest::decode_native_bytes(&forged_sound);
    let forger_is_faithful = forged_sound == from_disk && reforged.as_ref().ok() == Some(&reopened);
    println!(
        "\n  the foreign writer, on the UNCHANGED population: {} octets against the module's own {}\n  \
         -- {}",
        forged_sound.len(),
        from_disk.len(),
        if forger_is_faithful {
            "identical, and it reopens to the same rest"
        } else {
            "DIFFERENT, so nothing below is evidence"
        }
    );

    let mut forgeries: Vec<(String, Vec<u8>, &str)> = Vec::new();

    let provisional_slot = stems.iter().position(|record| record.wholes.len() == 1);
    let mut promoted: Option<(String, String)> = None;
    if let Some(slot) = provisional_slot {
        let mut repeated = stems.clone();
        let carried = repeated[slot].wholes[0].clone();
        repeated[slot].wholes.push(carried.clone());
        promoted = Some((repeated[slot].stem.clone(), carried));
        forgeries.push((
            format!(
                "one whole carried twice on the stem {:?}",
                repeated[slot].stem
            ),
            forge(&repeated, &standing),
            "WholeWitnessedTwice",
        ));
    }

    if stems.len() > 3 {
        let mut broken = stems.clone();
        broken[2].parent = Some(broken[0].id);
        forgeries.push((
            format!("the parent of {:?} is not its predecessor", broken[2].stem),
            forge(&broken, &standing),
            "ParentIsNotThePredecessor",
        ));

        let mut unwitnessed = stems.clone();
        unwitnessed[1].wholes.clear();
        forgeries.push((
            format!("no whole witnessed the stem {:?}", unwitnessed[1].stem),
            forge(&unwitnessed, &standing),
            "NoWholeWitnessedTheStem",
        ));

        let mut collided = stems.clone();
        collided[2].id = collided[1].id;
        collided[3].parent = Some(collided[1].id);
        forgeries.push((
            format!(
                "the stems {:?} and {:?} share one identity",
                collided[1].stem, collided[2].stem
            ),
            forge(&collided, &standing),
            "IdentityFoundedTwice",
        ));
    }

    let mut refused_by_name = 0usize;
    println!();
    for (named, wire, wanted) in &forgeries {
        let outcome = match ConditionedRest::decode_native_bytes(wire) {
            Err(ConditionedRestRefusal::NotAFoundedMorphology { refusal }) => {
                let carried = format!("{refusal:?}");
                if carried.starts_with(wanted) {
                    refused_by_name += 1;
                    format!("refused: {refusal}")
                } else {
                    format!("refused by the WRONG condition: {refusal}")
                }
            }
            Err(other) => format!("refused by another gate: {other}"),
            Ok(_) => "ADMITTED, which fails this driver".to_owned(),
        };
        println!("    {named}\n      {outcome}");
    }

    // what the repeated whole would have bought, taken lawfully so the consequence is exhibited
    if let Some((stem, carried)) = &promoted {
        let true_standing = FoundedStem {
            id: StemId(0),
            stem: stem.clone(),
            wholes: vec![carried.clone()],
            parent: None,
            foreign_lineage: Vec::new(),
        }
        .standing();
        let forged_standing = FoundedStem {
            id: StemId(0),
            stem: stem.clone(),
            wholes: vec![carried.clone(), carried.clone()],
            parent: None,
            foreign_lineage: Vec::new(),
        }
        .standing();
        println!(
            "\n  the repeated whole is not cosmetic: the stem {stem:?} stands {true_standing:?} on \
             the\n  true population and {forged_standing:?} on the forged one, so the forgery puts a \
             stem\n  one source witnessed onto the derivation path. {}",
            if true_standing == StemStanding::Provisional
                && forged_standing == StemStanding::Committed
            {
                "That is a frequency wearing a recurrence's name."
            } else {
                "-- and the fixture did not exhibit the flip, so this line carries nothing."
            }
        );
    }

    // the fifth: a body that arrived through serde having never been founded
    let sound_morphology = ablated.morphology().clone();
    let json = serde_json::to_string(&sound_morphology).expect("serialises");
    let second = sound_morphology.founded()[1].stem.clone();
    let lying = json.replace(
        &format!("\"{second}\":1,"),
        &format!("\"{second}\":{},", sound_morphology.founded().len() + 4),
    );
    let mut serde_refusal = "the index entry to corrupt was not found".to_owned();
    let mut serde_refused = false;
    if lying != json {
        let carried: FoundedMorphology = serde_json::from_str(&lying).expect("reopens");
        let records_agree = records(&carried) == records(&sound_morphology);
        let mut lying_body = ConditionedBody::mount(deposit.clone()).expect("mounts");
        lying_body.carry_morphology(carried);
        serde_refusal = match ConditionedRest::seal(&lying_body) {
            Err(ConditionedRestRefusal::NotAFoundedMorphology {
                refusal: refusal @ FoundedMorphologyRefusal::IndexNamesAnotherSlot { .. },
            }) => {
                serde_refused = records_agree;
                format!(
                    "refused at the seal: {refusal}\n      and its RECORDS are identical to the \
                     sound body's ({records_agree}), which is why the seal cannot rely on them alone"
                )
            }
            Err(other) => format!("refused by another gate: {other}"),
            Ok(_) => "SEALED, which fails this driver".to_owned(),
        };
    }
    println!(
        "\n    a morphology deserialized with a lookup index that lies about one slot\n      \
         {serde_refusal}"
    );

    // ---------------------------------------------------------------------------------------------
    rule("[7]  THE RESUMED ABLATED BODY GOES ON RECEIVING -- without closing its gap");

    let mut receiving = reopened.clone();
    let moved = receiving.receive_whole(FURTHER_WHOLE.0, FURTHER_WHOLE.1);
    let moved_records = receiving.stems().to_vec();
    let gap_still_absent = !moved_records
        .iter()
        .any(|record| record.id == removed_identity.0);
    let carried_forward = moved_records
        .iter()
        .take(ablated_records.len())
        .zip(ablated_records.iter())
        .filter(|(now, was)| now.id != was.id)
        .count();
    let moved_octets = receiving.encode_native_bytes().expect("the wire");

    println!(
        "\n  {} stems moved: {:?}",
        moved.len(),
        moved.iter().take(10).collect::<Vec<&String>>()
    );
    println!(
        "  the form went from {} octets to {}.",
        from_disk.len(),
        moved_octets.len()
    );
    println!(
        "  the identity {} is {} after the further whole, and {} of the {} identities already\n  \
         standing were renumbered by it.",
        removed_identity.0,
        if gap_still_absent {
            "still ABSENT"
        } else {
            "now present, which fails this driver"
        },
        carried_forward,
        ablated_records.len()
    );

    // ---------------------------------------------------------------------------------------------
    rule("CONTROLS");

    controls.check(
        "the ablation removes structure rather than changing a number",
        ablation.removes_structure(),
        &format!(
            "{} passages structurally absent and {} circuit cells absent on removing {removed:?}, \
             with {} reopened and {} unaccounted",
            ablation.passages_absent.len(),
            ablation.cells_absent.len(),
            ablation.reopened.len(),
            ablation.unaccounted.len()
        ),
    );
    controls.check(
        "the ablated population is one the FOUNDING seam cannot carry",
        !replay_differences.is_empty() && !identities_are_contiguous,
        &format!(
            "`from_founded_words` returns {} of {} stems differing; had the LAST founded stem been \
             removed it would return the same population and this driver would prove nothing",
            replay_differences.len(),
            ablated_records.len()
        ),
    );
    controls.check(
        "the corpus and the deposit are provably unreachable at the remount",
        reachable.is_empty() && open_attempts == CORPUS.len() + artifacts.len() + 1,
        &format!(
            "{open_attempts} opens were attempted from {} and every one was refused",
            elsewhere.display()
        ),
    );
    controls.check(
        "the ablated body remounts field for field, identities included",
        remount_differences.is_empty()
            && ablated.morphology() == remounted.morphology()
            && identities_before == identities_after,
        &format!(
            "{} stems, every record equal on identity, parent, named wholes and foreign lineage",
            remounted_records.len()
        ),
    );
    controls.check(
        "the gap the ablation left survived the wire",
        gap_survived
            && remounted.morphology().stem(&removed).is_none()
            && identities_after.len() + 1 == founded.founded().len(),
        &format!(
            "identity {} is absent from {} surviving identities, and the founded population had {}",
            removed_identity.0,
            identities_after.len(),
            founded.founded().len()
        ),
    );
    controls.check(
        "the remounted ablated body's production is bit-identical",
        rendered_before == rendered_after && ablated_before == ablated_after,
        &format!(
            "{} rendered octets on both sides over {} passages",
            rendered_before.len(),
            ablated_after.len()
        ),
    );
    controls.check(
        "the remounted body answers a statement no body was asked before the seal",
        !answered.is_empty() && answered == cross_check,
        &format!(
            "{} passages on {UNASKED_QUERY:?}, agreeing artifact for artifact with the body still \
             in memory",
            answered.len()
        ),
    );
    controls.check(
        "the foreign wire writer is faithful on the unchanged population",
        forger_is_faithful,
        &format!(
            "{} octets, identical to the module's own encoding and reopening to the same rest; \
             without this, a refused forgery would only mean a broken forger",
            forged_sound.len()
        ),
    );
    controls.check(
        "every population no founding could have produced is refused by its own name",
        refused_by_name == forgeries.len() && !forgeries.is_empty() && serde_refused,
        &format!(
            "{refused_by_name} of {} forged wires refused by the named condition, and the \
             deserialized body with a lying index refused at the seal",
            forgeries.len()
        ),
    );
    controls.check(
        "the resumed ablated body goes on receiving without closing its gap",
        !moved.is_empty() && gap_still_absent && carried_forward == 0,
        &format!(
            "{} stems moved, identity {} still absent, and {carried_forward} of the {} identities \
             already standing were renumbered",
            moved.len(),
            removed_identity.0,
            ablated_records.len()
        ),
    );
    controls.check(
        "the pre-ablation production is non-empty, so every equality above carries evidence",
        !unablated.is_empty() && !ablated_before.is_empty() && !founded.committed().is_empty(),
        &format!(
            "{} passages before the ablation, {} after, over {} committed stems",
            unablated.len(),
            ablated_before.len(),
            founded.committed().len()
        ),
    );

    if controls.failed.is_empty() {
        println!("\n  every declared control holds.");
    } else {
        println!("\n  FAILED: {:?}", controls.failed);
        std::process::exit(1);
    }
}
