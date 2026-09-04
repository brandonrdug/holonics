//! The conditioned instance **rests, departs from its source, and resumes** — and the resumed body
//! answers a statement it was never asked before the seal.
//!
//! ```text
//! cargo run --release -p life --example eros_mathematics_instance_rest
//! ```
//!
//! ## The seam this driver closes
//!
//! `eros_mathematics_conditioning` is a **run**: it reads fourteen declared documents through
//! `life::text_material`, founds a morphology, derives, prints and exits. Every later run re-reads
//! the corpus, so nothing it establishes distinguishes a conditioned body from a lookup over a
//! corpus that is still open. `CLAUDE.md` §13 rule 1 asks a training claim for *source-detached
//! remount*, and a body with no wire cannot be detached from anything.
//!
//! This driver is the wire, driven. The conditioning is identical — the same fourteen declared
//! documents, the same intake, the same 103-artifact standing — and then:
//!
//! ```text
//!   condition ─▶ FoundedMorphology ─┐
//!                                   ├─ ConditionedRest::seal ─▶ CDER octets ─▶ form_mouth
//!   standing/output ─▶ Vec<Passage> ┘                                             │
//!                                                                                 │
//!   chdir out of the repository; every corpus path and every deposited artifact    │
//!   is opened and REQUIRED TO FAIL ─────────────────────────────────────────────── │ ─┐
//!                                                                                 │  │
//!   a fresh ConditionedBody ◀── ConditionedRest::mount ◀── decode ◀── the octets ◀─┘  │
//!                    │                                                               │
//!                    └── derives, with the corpus and the deposit provably unreachable ┘
//! ```
//!
//! ## The four slots
//!
//! ```text
//!   source geometry   the founded morphology and the deposited standing, as sealed octets
//!   receiver map      a fresh body mounted from those octets and nothing else
//!   transport         character succession through a recruited identifier, as before the rest
//!   returned residual the passages the resumed body derives -- on the statement it was asked
//!                     before the seal, and on one it was not
//! ```
//!
//! ## What each declared control can be wrong about
//!
//! - **Departure.** A remount that could still read the corpus proves nothing at all, so departure
//!   is not narrated here: the process working directory is moved out of the repository and every
//!   one of the fourteen declared documents and every one of the deposited artifacts is *opened*,
//!   with the resulting `ErrorKind` population printed. A single successful open fails the driver.
//! - **Resumption.** Comparing counts would leave a body free to return the same number of passages
//!   carrying different bridges. The comparison is over
//!   `conditioned_rest::render_derived_passages`, which carries every field of every passage and
//!   every bridge, and any difference is exhibited as a population of artifacts.
//! - **Replay.** A body that could only return its last answer would satisfy both of the above. So
//!   the sealed form has no field for a query or a derived passage, the resumed body is asked a
//!   *different* statement, and every artifact it returns is checked to be absent from the octets it
//!   was resumed from.
//! - **The morphology.** Committed set, provisional set, every stem's own record, and every cover
//!   over the recruited population, compared as populations.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use holonic_engine::conditioned_derivation::{
    expose, ConditionedBody, DerivationQuery, DerivedPassage, Exposure, FoundedMorphology,
};
use life::conditioned_rest::{
    records, render_derived_passages, ConditionedRest, FoundedStemRecord,
};
use life::form_mouth::{deposit_form, DepositedForm};
use life::text_material::{ExactTextMaterialAtlas, ExactTextMaterialCorpus, ParsedTextDocument};

// -------------------------------------------------------------------------------------------------
// The declaration
// -------------------------------------------------------------------------------------------------

/// **The declared corpus.** The same fourteen documents `eros_mathematics_conditioning` declares,
/// named rather than globbed so that opening exactly this population after the rest is a well-posed
/// operation.
const CORPUS: &[&str] = &[
    "research/papers/source/mathematics/theorems/weil-support-induction-reduction.typ",
    "research/papers/source/mathematics/theorems/conditioned-support-quotient-shorting.typ",
    "research/papers/source/mathematics/theorems/conditioned-effective-tension.typ",
    "research/papers/source/mathematics/theorems/prime-power-aperture-incidence.typ",
    "research/papers/source/mathematics/theorems/prime-power-hinge-cell-recurrence.typ",
    "research/papers/source/mathematics/theorems/archimedean-remainder-amplitude.typ",
    "research/papers/source/mathematics/theorems/causal-parity-kirchhoff-return.typ",
    "research/papers/source/mathematics/theorems/dyadic-character-filler-bound.typ",
    "research/papers/source/mathematics/lemmas/situated-mean-transport.typ",
    "research/papers/source/mathematics/lemmas/geometric-remainder-squeeze.typ",
    "research/papers/source/mathematics/lemmas/first-prime-capacitance-completion.typ",
    "research/papers/source/mathematics/corollaries/archimedean-carrier-prime-boundary.typ",
    "research/papers/source/mathematics/definitions/receiver-configuration-calculus.typ",
    "research/papers/source/mathematics/definitions/graded-arithmetic-accessibility-current.typ",
];

/// **The declared standing derivation deposit.** Sealed into the rest, so the resumed body carries
/// it rather than re-reading it.
const DEPOSIT: &str = "standing/output";

/// **The statement asked before the seal.** The same one `eros_mathematics_conditioning` declares.
const SEALED_QUERY: &str = "(h : P) : exactCarrier P";

/// **The statement asked only after the seal.** A different statement the deposit reaches, put to
/// no body until the octets were on disk. A body that can only replay its last answer returns
/// nothing here.
const UNASKED_QUERY: &str = "(a b : Nat) : a = b";

/// The driver name the form is deposited under, and the site within it that sealed the form.
const DRIVER: &str = "eros_mathematics_instance_rest";
const FORM_SITE: &str = "conditioned-rest";

/// **The declared further whole.** Presented to the resumed body after it has derived, so that the
/// resumption is shown to be a body that goes on receiving rather than an image that answers once.
/// Its surface is written here and is not read off disk: after the rest, nothing is.
const FURTHER_WHOLE: (&str, &str) = (
    "document:presented-after-the-rest",
    "A receiver family founded after the rest carries the exact transport of a formal kernel.",
);

// -------------------------------------------------------------------------------------------------
// The exterior codecs — reading files is not a claim, so both are stated here in full
// -------------------------------------------------------------------------------------------------

/// **The declared section codec.** A section is a maximal run of non-blank lines. Nothing is
/// stripped, lowercased, or normalized.
fn sections(text: &str) -> Vec<String> {
    let mut sections = Vec::new();
    let mut open: Vec<&str> = Vec::new();
    for line in text.lines() {
        if line.trim().is_empty() {
            if !open.is_empty() {
                sections.push(open.join("\n"));
                open.clear();
            }
        } else {
            open.push(line);
        }
    }
    if !open.is_empty() {
        sections.push(open.join("\n"));
    }
    sections
}

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

/// Read the declared corpus through `life::text_material`, exactly as the conditioning driver does.
fn intake() -> Result<(Vec<Exposure>, ExactTextMaterialAtlas), String> {
    let mut parsed = Vec::new();
    for path in CORPUS {
        let text = std::fs::read_to_string(path).map_err(|error| format!("{path}: {error}"))?;
        let sections = sections(&text);
        if sections.is_empty() {
            return Err(format!("{path}: the section codec returned nothing"));
        }
        parsed.push(ParsedTextDocument {
            identity: (*path).to_owned(),
            source: (*path).to_owned(),
            sections,
        });
    }
    let corpus = ExactTextMaterialCorpus::import(Vec::new(), &parsed, 1)
        .map_err(|error| format!("life's intake refused the corpus: {error:?}"))?;
    let atlas = ExactTextMaterialAtlas::condition(corpus)
        .map_err(|error| format!("life refused to condition the atlas: {error:?}"))?;
    let exposures = atlas
        .corpus()
        .passages()
        .iter()
        .map(|passage| expose(&passage.identity, &passage.text))
        .collect();
    Ok((exposures, atlas))
}

/// The declared corpus document an intake occurrence identity names.
///
/// A parse of `life`'s own occurrence key `document:{identity}:{ordinal}:{sha256}`, and after the
/// rest this resolves from the **sealed lineage alone** — the named document is carried on the stem,
/// with the document itself unreadable.
fn document_of(whole: &str) -> Option<&'static str> {
    let body = whole.strip_prefix("document:")?;
    CORPUS
        .iter()
        .copied()
        .find(|path| body.starts_with(&format!("{path}:")))
}

fn documents_witnessing(morphology: &FoundedMorphology, stem: &str) -> BTreeSet<&'static str> {
    morphology
        .stem(stem)
        .map(|founded| {
            founded
                .wholes
                .iter()
                .filter_map(|whole| document_of(whole))
                .collect()
        })
        .unwrap_or_default()
}

fn file_name(path: &str) -> &str {
    Path::new(path)
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or(path)
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

/// One passage, exhibited as the artifact it is.
fn exhibit(passage: &DerivedPassage, morphology: &FoundedMorphology) {
    let witnessing: Vec<&str> = documents_witnessing(morphology, &passage.stem)
        .into_iter()
        .map(file_name)
        .collect();
    println!("\n  {}", passage.name);
    println!(
        "      licensed by stem {:?}   brought {}   reaches {}",
        passage.stem, passage.brought, passage.reaches
    );
    println!(
        "      stem founded by corpus documents: {}",
        witnessing.join(" ")
    );
    for bridge in passage.licensing() {
        let routes = if bridge.routes.len() <= 3 {
            bridge.routes.join(" ")
        } else {
            format!(
                "{} ... {}   [{} routes]",
                bridge.routes[0],
                bridge.routes[bridge.routes.len() - 1],
                bridge.routes.len()
            )
        };
        println!(
            "      bridge   {} @{}  <-{:?}->  {} @{}   licensed by {routes}",
            bridge.held, bridge.held_at, bridge.stem, bridge.brought, bridge.brought_at
        );
    }
    for line in passage.text.lines() {
        println!("      | {line}");
    }
}

/// The population of artifacts that differ across two productions, exhibited field by field. Never
/// a count, and never a hash standing in for the artifacts.
fn passage_differences(before: &[DerivedPassage], after: &[DerivedPassage]) -> Vec<String> {
    let mut differing = Vec::new();
    for (at, earlier) in before.iter().enumerate() {
        match after.get(at) {
            None => differing.push(format!("position {at}: {} departed entirely", earlier.name)),
            Some(later) if later == earlier => {}
            Some(later) => {
                for (field, was, now) in [
                    ("name", &earlier.name, &later.name),
                    ("statement", &earlier.statement, &later.statement),
                    ("reaches", &earlier.reaches, &later.reaches),
                    ("brought", &earlier.brought, &later.brought),
                    ("stem", &earlier.stem, &later.stem),
                    ("text", &earlier.text, &later.text),
                ] {
                    if was != now {
                        differing
                            .push(format!("position {at}: {field} was {was:?} and is {now:?}"));
                    }
                }
                if earlier.bridges != later.bridges {
                    for bridge in &earlier.bridges {
                        if !later.bridges.contains(bridge) {
                            differing.push(format!("position {at}: bridge departed {bridge:?}"));
                        }
                    }
                    for bridge in &later.bridges {
                        if !earlier.bridges.contains(bridge) {
                            differing.push(format!("position {at}: bridge appeared {bridge:?}"));
                        }
                    }
                }
            }
        }
    }
    for extra in after.iter().skip(before.len()) {
        differing.push(format!("{} appeared with no counterpart", extra.name));
    }
    differing
}

/// Every stem record that differs across the rest, exhibited whole.
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

/// Whether a run of octets carries a given text anywhere. Used to prove the sealed form does not
/// carry an answer.
fn octets_carry(octets: &[u8], text: &str) -> bool {
    let needle = text.as_bytes();
    !needle.is_empty() && octets.windows(needle.len()).any(|window| window == needle)
}

fn main() {
    let mut controls = Controls::new();

    // ---------------------------------------------------------------------------------------------
    rule("EROS MATHEMATICS INSTANCE REST -- the conditioned body rests, departs, and resumes");

    let invocation = std::env::current_dir().expect("the invocation directory");
    println!("\n  invoked in {}", invocation.display());

    let (exposures, atlas) = match intake() {
        Ok(taken) => taken,
        Err(refusal) => {
            eprintln!("{refusal}");
            std::process::exit(2);
        }
    };

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

    let corpus_receipt = atlas.corpus().receipt();
    println!(
        "  declared corpus  {} documents   {} witnessed occurrences   raw container sha256 {}",
        CORPUS.len(),
        corpus_receipt.witnessed_occurrences,
        corpus_receipt.raw_container_sha256
    );
    println!(
        "  declared standing  {DEPOSIT}   {} artifacts",
        deposit.len()
    );

    // ---------------------------------------------------------------------------------------------
    rule(
        "[1]  THE CONDITIONING -- identical to the run, and the last thing the corpus is read for",
    );

    let mut conditioned = match ConditionedBody::mount(deposit.clone()) {
        Ok(body) => body,
        Err(refusal) => {
            eprintln!("the deposit was refused: {refusal}");
            std::process::exit(2);
        }
    };
    conditioned.condition(&exposures);
    let morphology_before = conditioned.morphology().clone();
    let records_before = records(&morphology_before);
    let recruited = conditioned.recruited_population();
    let statements = conditioned.standing_statements();

    println!(
        "\n  {} exposures handed across the seam, one per admitted occurrence",
        exposures.len()
    );
    println!(
        "  founded {}   committed {}   provisional {}   recruited identifiers {}",
        morphology_before.founded().len(),
        morphology_before.committed().len(),
        morphology_before.provisional().len(),
        recruited.len()
    );

    for declared in [SEALED_QUERY, UNASKED_QUERY] {
        if !statements.contains(declared) {
            eprintln!("the declared query is not a statement this deposit reaches: {declared}");
            eprintln!("the deposit reaches: {statements:?}");
            std::process::exit(2);
        }
    }
    let sealed_query = DerivationQuery::reaching(SEALED_QUERY);
    let unasked_query = DerivationQuery::reaching(UNASKED_QUERY);

    let before = conditioned.derive(&sealed_query).expect("derives");
    println!(
        "\n  the body is asked {SEALED_QUERY:?} BEFORE the seal and returns {} passages",
        before.len()
    );
    println!("  it is not asked {UNASKED_QUERY:?}, and will not be until the octets are on disk.");

    // ---------------------------------------------------------------------------------------------
    rule("[2]  THE SEAL -- the founded morphology and the standing, to content-addressed octets");

    let rest = match ConditionedRest::seal(&conditioned) {
        Ok(rest) => rest,
        Err(refusal) => {
            eprintln!("{refusal}");
            std::process::exit(2);
        }
    };
    let octets = match rest.encode_native_bytes() {
        Ok(octets) => octets,
        Err(refusal) => {
            eprintln!("{refusal}");
            std::process::exit(2);
        }
    };
    let deposited: DepositedForm = match deposit_form(DRIVER, FORM_SITE, &octets) {
        Ok(deposited) => deposited,
        Err(refusal) => {
            eprintln!("{refusal}");
            std::process::exit(2);
        }
    };
    let sealed_path = std::fs::canonicalize(&deposited.path).expect("the form is on disk");

    println!("\n  the rest carries");
    println!("    founded stems      {}", rest.stems().len());
    println!("    standing artifacts {}", rest.standing().len());
    println!("    queries            0   (the wire has no field for one)");
    println!("    derived passages   0   (the wire has no field for one)");
    println!("\n  the census of the sealed form, recomputed by mounting it");
    for (field, value) in rest.census_rows().expect("a census") {
        println!("    {field:<24} {value}");
    }
    println!("\n  the form, at the plate mouth");
    println!("    {} octets", octets.len());
    println!("    address {}", deposited.address);
    println!("    {}", sealed_path.display());
    println!(
        "\n  read back by holon-plate with\n    cargo run -p holon-plate -- deposit --from CDER:{} --to instance.holon\n    \
         cargo run -p holon-plate -- resume --plate instance.holon",
        deposited.path.display()
    );

    // ---------------------------------------------------------------------------------------------
    rule("[3]  SOURCE DEPARTURE -- every declared path is OPENED, and every open must fail");

    let elsewhere = std::env::temp_dir().join(format!("{DRIVER}-departed"));
    let _ = std::fs::remove_dir_all(&elsewhere);
    std::fs::create_dir_all(&elsewhere).expect("a working directory outside the repository");
    std::env::set_current_dir(&elsewhere).expect("depart");
    println!(
        "\n  the process working directory is now {}\n  \
         Every declared corpus path and every deposited artifact path is relative, so none of them\n  \
         resolves here. That is not asserted: each one is opened below and the refusal is reported.\n",
        elsewhere.display()
    );

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
    // and the deposit root itself, which is what a body that wanted to re-read its standing would open
    open_attempts += 1;
    match std::fs::read_dir(DEPOSIT) {
        Ok(_) => reachable.push(DEPOSIT.to_owned()),
        Err(error) => *refusals.entry(format!("{:?}", error.kind())).or_default() += 1,
    }

    println!(
        "    {open_attempts} opens attempted: {} declared corpus documents, {} deposited artifacts, \
         and the deposit root",
        CORPUS.len(),
        artifacts.len()
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
    rule("[4]  THE REMOUNT -- a fresh body, from the sealed octets and nothing else");

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
    let morphology_after = remounted.morphology().clone();
    let records_after = records(&morphology_after);

    println!(
        "\n  {} octets read from {}",
        from_disk.len(),
        sealed_path.display()
    );
    println!(
        "  the fresh body carries {} standing passages, {} founded stems, {} committed, {} provisional",
        remounted.standing().len(),
        morphology_after.founded().len(),
        morphology_after.committed().len(),
        morphology_after.provisional().len()
    );

    // ---------------------------------------------------------------------------------------------
    rule("[5]  BIT-IDENTICAL RESUMPTION -- the same statement, the artifacts compared whole");

    let after = remounted.derive(&sealed_query).expect("derives");
    let rendered_before = render_derived_passages(&before);
    let rendered_after = render_derived_passages(&after);
    let differences = passage_differences(&before, &after);

    println!(
        "\n  before the rest  {} passages, {} rendered octets",
        before.len(),
        rendered_before.len()
    );
    println!(
        "  after the rest   {} passages, {} rendered octets",
        after.len(),
        rendered_after.len()
    );
    println!(
        "  the rendering carries every field of every passage and every bridge -- name, statement,\n  \
         reaches, brought, stem, text, and each bridge's stem, held, held offset, brought, brought\n  \
         offset and route."
    );
    if differences.is_empty() {
        println!(
            "\n  the two populations differ in nothing. The whole difference population is empty."
        );
    } else {
        println!("\n  the difference population, whole:");
        for difference in &differences {
            println!("    {difference}");
        }
    }
    println!("\n  three passages of the resumed production, exhibited whole:");
    for passage in after.iter().take(3) {
        exhibit(passage, &morphology_after);
    }

    // ---------------------------------------------------------------------------------------------
    rule("[6]  THE UNASKED STATEMENT -- put to no body until the octets were on disk");

    let answered = remounted.derive(&unasked_query).expect("derives");
    // The cross-check is taken on the body still in memory, and taken NOW: it was not asked this
    // statement before the seal either, so the sealed octets cannot carry its answer.
    let cross_check = conditioned.derive(&unasked_query).expect("derives");
    let unasked_differences = passage_differences(&cross_check, &answered);

    println!(
        "\n  {UNASKED_QUERY:?}\n\n  the resumed body returns {} passages. The pre-rest body, asked \
         the same statement now\n  for the first time, returns {}.",
        answered.len(),
        cross_check.len()
    );
    if unasked_differences.is_empty() {
        println!("  The two populations differ in nothing.");
    } else {
        println!("  the difference population, whole:");
        for difference in &unasked_differences {
            println!("    {difference}");
        }
    }

    let replayed: Vec<&DerivedPassage> = answered
        .iter()
        .filter(|passage| before.iter().any(|earlier| earlier.name == passage.name))
        .collect();
    let carried_in_octets: Vec<&str> = before
        .iter()
        .chain(answered.iter())
        .map(|passage| passage.name.as_str())
        .filter(|name| octets_carry(&from_disk, name))
        .collect();

    println!(
        "\n  none of these artifacts is in the sealed octets: {} of the {} names across both\n  \
         productions occur anywhere in the {} form octets.",
        carried_in_octets.len(),
        before.len() + answered.len(),
        from_disk.len()
    );
    println!(
        "  {} of the {} returned here also appeared in the pre-seal production.",
        replayed.len(),
        answered.len()
    );

    println!("\n  every passage the resumed body returned on the unasked statement, whole:");
    for passage in &answered {
        exhibit(passage, &morphology_after);
    }

    // ---------------------------------------------------------------------------------------------
    rule("[7]  THE MORPHOLOGY -- committed set, provisional set, and every cover, as populations");

    let committed_before: BTreeSet<&str> =
        morphology_before.committed_stems().into_iter().collect();
    let committed_after: BTreeSet<&str> = morphology_after.committed_stems().into_iter().collect();
    let provisional_before: BTreeSet<&str> = morphology_before
        .provisional()
        .iter()
        .map(|stem| stem.stem.as_str())
        .collect();
    let provisional_after: BTreeSet<&str> = morphology_after
        .provisional()
        .iter()
        .map(|stem| stem.stem.as_str())
        .collect();

    let committed_left: Vec<&&str> = committed_before.difference(&committed_after).collect();
    let committed_entered: Vec<&&str> = committed_after.difference(&committed_before).collect();
    let provisional_left: Vec<&&str> = provisional_before.difference(&provisional_after).collect();
    let provisional_entered: Vec<&&str> =
        provisional_after.difference(&provisional_before).collect();

    println!(
        "\n    committed    before {:>5}   after {:>5}   left {:?}   entered {:?}",
        committed_before.len(),
        committed_after.len(),
        committed_left,
        committed_entered
    );
    println!(
        "    provisional  before {:>5}   after {:>5}   left {:?}   entered {:?}",
        provisional_before.len(),
        provisional_after.len(),
        provisional_left,
        provisional_entered
    );

    let stem_differences = record_differences(&records_before, &records_after);
    println!(
        "\n    every stem's own record -- identity, parent, named wholes, foreign lineage -- \
         compared\n    across the rest: {} of {} differ.",
        stem_differences.len(),
        records_before.len()
    );
    for difference in stem_differences.iter().take(20) {
        println!("      {difference}");
    }

    let mut cover_differences: Vec<String> = Vec::new();
    for identifier in &recruited {
        let (Ok(was), Ok(now)) = (
            morphology_before.cover(identifier),
            morphology_after.cover(identifier),
        ) else {
            cover_differences.push(format!("{identifier}: a cover was refused on one side"));
            continue;
        };
        if was.render() != now.render() {
            cover_differences.push(format!(
                "{identifier}: before {}   after {}",
                was.render(),
                now.render()
            ));
        }
    }
    let mut stem_cover_differences: Vec<String> = Vec::new();
    for record in &records_before {
        let (Ok(was), Ok(now)) = (
            morphology_before.cover(&record.stem),
            morphology_after.cover(&record.stem),
        ) else {
            stem_cover_differences
                .push(format!("{}: a cover was refused on one side", record.stem));
            continue;
        };
        if was.render() != now.render() {
            stem_cover_differences.push(format!(
                "{}: before {}   after {}",
                record.stem,
                was.render(),
                now.render()
            ));
        }
    }
    println!(
        "\n    the cover of every one of the {} recruited identifiers: {} differ.",
        recruited.len(),
        cover_differences.len()
    );
    for difference in cover_differences.iter().take(20) {
        println!("      {difference}");
    }
    println!(
        "    the cover of every one of the {} founded stems: {} differ.",
        records_before.len(),
        stem_cover_differences.len()
    );
    for difference in stem_cover_differences.iter().take(20) {
        println!("      {difference}");
    }

    println!(
        "\n    three licensing stems, traced back to the NAMED documents that founded them -- from \
         the\n    sealed lineage alone, with those documents unreadable:\n"
    );
    let licensing: BTreeSet<&str> = after.iter().map(|passage| passage.stem.as_str()).collect();
    for stem in licensing.iter().take(3) {
        let documents = documents_witnessing(&morphology_after, stem);
        println!("      stem {stem:?}");
        for path in &documents {
            println!(
                "        founded by  {path}   [reachable: {}]",
                Path::new(path).exists()
            );
        }
    }

    // ---------------------------------------------------------------------------------------------
    rule("[8]  THE RESUMED BODY GOES ON RECEIVING -- one further whole, after the rest");

    let mut receiving = reopened.clone();
    let moved = receiving.receive_whole(FURTHER_WHOLE.0, FURTHER_WHOLE.1);
    let moved_octets = receiving.encode_native_bytes().expect("the wire");
    let after_further = receiving
        .mount()
        .expect("mounts")
        .derive(&sealed_query)
        .expect("derives");

    println!(
        "\n  the further whole, presented to the resumed rest:\n    {} : {:?}",
        FURTHER_WHOLE.0, FURTHER_WHOLE.1
    );
    println!(
        "\n  {} stems moved: {:?}",
        moved.len(),
        moved.iter().take(12).collect::<Vec<&String>>()
    );
    println!(
        "  the form moved from {} octets to {}.",
        from_disk.len(),
        moved_octets.len()
    );
    println!(
        "  the production on {SEALED_QUERY:?} went from {} passages to {}.",
        after.len(),
        after_further.len()
    );

    // ---------------------------------------------------------------------------------------------
    rule("CONTROLS");

    controls.check(
        "the corpus and the deposit are provably unreachable at the remount",
        reachable.is_empty() && open_attempts == CORPUS.len() + artifacts.len() + 1,
        &format!(
            "{open_attempts} opens were attempted from {} and every one was refused; \
             a remount that could still read its source proves nothing",
            elsewhere.display()
        ),
    );
    controls.check(
        "the remounted production is bit-identical on the statement asked before the seal",
        rendered_before == rendered_after && before == after && differences.is_empty(),
        &format!(
            "{} rendered octets on both sides, over every field of every passage and every bridge",
            rendered_before.len()
        ),
    );
    controls.check(
        "the resumed body answered a statement it was not asked before the seal",
        !answered.is_empty() && unasked_differences.is_empty(),
        &format!(
            "{} passages on {UNASKED_QUERY:?}, agreeing artifact for artifact with the body still \
             in memory",
            answered.len()
        ),
    );
    controls.check(
        "the sealed octets carry no answer, so the resumption is a derivation and not a cache",
        carried_in_octets.is_empty(),
        &format!(
            "none of the {} artifact names across both productions occurs in the {} form octets",
            before.len() + answered.len(),
            from_disk.len()
        ),
    );
    controls.check(
        "the founded morphology survived exactly",
        morphology_before == morphology_after
            && stem_differences.is_empty()
            && committed_before == committed_after
            && provisional_before == provisional_after,
        &format!(
            "{} stems, {} committed and {} provisional, every record equal field for field",
            records_before.len(),
            committed_before.len(),
            provisional_before.len()
        ),
    );
    controls.check(
        "every cover is unchanged across the rest",
        cover_differences.is_empty() && stem_cover_differences.is_empty(),
        &format!(
            "{} recruited identifiers and {} founded stems, decomposed under both morphologies",
            recruited.len(),
            records_before.len()
        ),
    );
    controls.check(
        "the sealed form is on disk at its content address and reopens to the same rest",
        sealed_path.is_file()
            && from_disk == octets
            && sealed_path
                .file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| name.contains(&deposited.address))
            && reopened == rest,
        &format!("{} octets at {}", from_disk.len(), sealed_path.display()),
    );
    controls.check(
        "the resumed body goes on receiving: a further whole moves the form",
        !moved.is_empty() && moved_octets != from_disk,
        &format!(
            "{} stems moved and the form went from {} octets to {}; a body that resumed inert \
             would satisfy every check above",
            moved.len(),
            from_disk.len(),
            moved_octets.len()
        ),
    );
    controls.check(
        "the pre-rest production is non-empty, so every equality above carries evidence",
        !before.is_empty() && !morphology_before.committed().is_empty(),
        &format!(
            "{} passages over {} committed stems; two empty populations agree trivially",
            before.len(),
            morphology_before.committed().len()
        ),
    );

    if controls.failed.is_empty() {
        println!("\n  every declared control holds.");
    } else {
        println!("\n  FAILED: {:?}", controls.failed);
        std::process::exit(1);
    }
}
