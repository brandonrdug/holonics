//! The atmosphere and the ground: statement founding at corpus scale, on a doubling ladder.
//!
//! ```text
//! cargo run --release --example the_atmosphere_and_the_ground
//! cargo run --release --example the_atmosphere_and_the_ground -- <rung-cap>
//! ```
//!
//! ## What this is
//!
//! `the_statement_is_founded` conditions on **three** documents and founds statements against a
//! small formal deposit. Brandon, 2026-08-09: *"Right, scale. An actual atmosphere and ground."*
//!
//! ```text
//!   THE ATMOSPHERE   research/papers/source/mathematics/*.typ   +  docs/canon/*.md  +  research/records/*.md
//!                    the charge distribution: what the corpus committed, by recurrence
//!
//!   THE GROUND       standing/output/**/*.lean
//!                    the standing formal deposit the composition founds against
//! ```
//!
//! The question is not whether it runs. It is **whether more atmosphere produces more, or better,
//! statements** — and that is a measurement, not an expectation. A corpus that founds more stems can
//! license more bridges *and* can refuse more candidates, and which one happens is the finding.
//!
//! ## The aperture, and why there is one
//!
//! `docs/plans/THE_ROADMAP.md` forbids an aperture-less organ in the corpus path, and names the two
//! precedents: `eros_resonant_corpus_current` SIGKILLs at 10,963 MB on 1,556 lines, while
//! `the_iron_tokens_carry_the_field` returns a **typed obstruction naming the required width** and
//! answers a narrower question whole, at 12.3M tokens in 2 GB.
//!
//! So this driver climbs a **doubling ladder** — 1, 2, 4, 8 … documents — reporting the full return
//! at every rung, and stops at the first rung that refuses. A ladder that stops has still returned
//! every rung below it, and the rung it stopped at is named. Nothing here is authored: the rungs are
//! read off the declared population by doubling, and the caller may cap them from `argv[1]`.
//!
//! ## What is returned
//!
//! Per rung: documents, committed stems, candidates composed, statements **admitted in full**, and
//! the refusal population by species. `CLAUDE.md` §9 — the artifact is returned and inspected;
//! counts are supporting receipts and never substitutes.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use std::time::Instant;

use holonic_engine::conditioned_derivation::{
    ConditionedBody, ContactSpecies, Exposure, FoundedMorphology, expose,
};
use holonic_engine::contact_gluing::{LeaderCochain, glue_at_contact, integrate_leader};
use holonic_engine::rebase_invariants::PivotRule;
use holonic_engine::statement_composition::{StatementAdmission, found_statements};

/// The declared atmosphere. Roots and extensions only — every file under each is read whole, and
/// the population is whatever is there. `corpus_census::DECLARED_STRATA` declares the same three
/// for the census; this driver names them again rather than importing, because the census measures
/// tokens and this conditions on wholes, and one root list serving two questions would hide which.
const ATMOSPHERE: [(&str, &str); 3] = [
    ("research/papers/source/mathematics", "typ"),
    ("canon", "md"),
    ("research/records", "md"),
];

/// The declared ground: the standing formal deposit the composition founds against.
const GROUND: &str = "standing/output";

fn gather(root: &Path, extension: &str) -> Vec<(String, String)> {
    let mut found = Vec::new();
    let mut frontier = vec![root.to_path_buf()];
    while let Some(at) = frontier.pop() {
        let Ok(entries) = std::fs::read_dir(&at) else {
            continue;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                frontier.push(path);
            } else if path.extension().and_then(|e| e.to_str()) == Some(extension)
                && let Ok(text) = std::fs::read_to_string(&path)
            {
                found.push((path.display().to_string(), text));
            }
        }
    }
    found.sort();
    found
}

fn rule(title: &str) {
    println!("\n{}", "=".repeat(96));
    println!("{title}");
    println!("{}", "=".repeat(96));
}

/// Resident set size in MB, read from the kernel rather than guessed.
fn resident_mb() -> u64 {
    std::fs::read_to_string("/proc/self/statm")
        .ok()
        .and_then(|statm| statm.split_whitespace().nth(1)?.parse::<u64>().ok())
        .map_or(0, |pages| pages * 4 / 1024)
}

struct Rung {
    documents: usize,
    committed: usize,
    composed: usize,
    admitted: Vec<String>,
    refused: BTreeMap<&'static str, usize>,
    /// The contact species of every licence carrying an admitted statement. This is the crossings
    /// and faces measured on real material rather than merely carried.
    contacts: BTreeMap<&'static str, usize>,
    seconds: f64,
    resident: u64,
}

fn main() {
    let cap: usize = std::env::args()
        .nth(1)
        .and_then(|read| read.parse().ok())
        .unwrap_or(usize::MAX);

    rule("THE ATMOSPHERE AND THE GROUND");

    let mut atmosphere: Vec<(String, String)> = Vec::new();
    for (root, extension) in ATMOSPHERE {
        let stratum = gather(Path::new(root), extension);
        println!(
            "  {:<30} {:>4} documents  {:>9} octets",
            format!("{root}/**/*.{extension}"),
            stratum.len(),
            stratum.iter().map(|(_, text)| text.len()).sum::<usize>()
        );
        atmosphere.extend(stratum);
    }
    let ground = gather(Path::new(GROUND), "lean");
    println!(
        "  {:<30} {:>4} artifacts  {:>9} octets",
        format!("{GROUND}/**/*.lean"),
        ground.len(),
        ground.iter().map(|(_, text)| text.len()).sum::<usize>()
    );

    if atmosphere.is_empty() || ground.is_empty() {
        eprintln!("\n  REFUSED: the atmosphere or the ground is empty at these declared roots.");
        std::process::exit(1);
    }

    // The rungs are read off the population by doubling. Nothing is authored: the ladder is
    // whatever powers of two fit under the declared count, plus the count itself.
    let mut rungs: Vec<usize> = Vec::new();
    let mut at = 1usize;
    while at < atmosphere.len() {
        rungs.push(at);
        at *= 2;
    }
    rungs.push(atmosphere.len());
    rungs.retain(|rung| *rung <= cap);
    println!("\n  the ladder, by doubling over the declared population: {rungs:?}");
    if cap != usize::MAX {
        println!("  capped by the caller at {cap}");
    }

    // ---------------------------------------------------------------------------------------------

    rule("THE LADDER");

    let mut climbed: Vec<Rung> = Vec::new();
    for documents in &rungs {
        let began = Instant::now();
        let exposures: Vec<Exposure> = atmosphere
            .iter()
            .take(*documents)
            .map(|(name, text)| expose(name, text))
            .collect();
        let morphology = FoundedMorphology::condition(&exposures);
        let committed = morphology.committed_stems().len();

        let mut body = match ConditionedBody::mount(ground.clone()) {
            Ok(body) => body,
            Err(refusal) => {
                println!("\n  rung {documents}: the ground refused the mount — {refusal}");
                break;
            }
        };
        body.carry_morphology(morphology);

        let founded = match found_statements(&body) {
            Ok(founded) => founded,
            Err(refusal) => {
                println!("\n  rung {documents}: the composition refused — {refusal}");
                println!("  every rung below it stands and is reported above.");
                break;
            }
        };

        let mut admitted = Vec::new();
        let mut refused: BTreeMap<&'static str, usize> = BTreeMap::new();
        let mut contacts: BTreeMap<&'static str, usize> = BTreeMap::new();
        for candidate in &founded.adjudicated {
            match &candidate.admission {
                StatementAdmission::Admitted { licences, .. } => {
                    admitted.push(candidate.candidate.statement.clone());
                    for licence in licences {
                        let species = match licence.contact {
                            ContactSpecies::Simple => "simple",
                            ContactSpecies::Superposed => "superposed",
                            ContactSpecies::Crossed => "crossed",
                        };
                        *contacts.entry(species).or_default() += 1;
                    }
                }
                StatementAdmission::Refused(obstruction) => {
                    *refused.entry(obstruction.species()).or_default() += 1;
                }
            }
        }
        admitted.sort();
        admitted.dedup();

        let rung = Rung {
            documents: *documents,
            committed,
            composed: founded.adjudicated.len(),
            admitted,
            refused,
            contacts,
            seconds: began.elapsed().as_secs_f64(),
            resident: resident_mb(),
        };
        println!(
            "  {:>4} docs   {:>6} stems   {:>7} composed   {:>4} admitted   {:>7.1}s   {:>5} MB",
            rung.documents,
            rung.committed,
            rung.composed,
            rung.admitted.len(),
            rung.seconds,
            rung.resident
        );
        climbed.push(rung);
    }

    if climbed.is_empty() {
        eprintln!("\n  REFUSED at the first rung. Nothing was returned.");
        std::process::exit(1);
    }

    // ---------------------------------------------------------------------------------------------

    rule("THE COST LAW");

    println!("  A cost law is a law (`CLAUDE.md` §8), and it is stated against the rung below.\n");
    println!(
        "    {:>6}  {:>8}  {:>9}  {:>8}  {:>8}",
        "docs", "stems x", "composed x", "time x", "MB"
    );
    for pair in climbed.windows(2) {
        let (below, here) = (&pair[0], &pair[1]);
        let ratio = |now: f64, was: f64| if was > 0.0 { now / was } else { f64::NAN };
        println!(
            "    {:>6}  {:>8.2}  {:>9.2}  {:>8.2}  {:>8}",
            here.documents,
            ratio(here.committed as f64, below.committed as f64),
            ratio(here.composed as f64, below.composed as f64),
            ratio(here.seconds, below.seconds),
            here.resident
        );
    }

    // ---------------------------------------------------------------------------------------------

    rule("THE ARTIFACT — every statement the largest returned rung founded");

    let top = climbed.last().expect("a rung climbed");
    println!(
        "  {} documents, {} committed stems, {} candidates composed, {} admitted.\n",
        top.documents,
        top.committed,
        top.composed,
        top.admitted.len()
    );
    for statement in &top.admitted {
        println!("    |- {statement}");
    }
    if top.admitted.is_empty() {
        println!("    (none: at this scale every candidate was refused)");
    }

    println!("\n  THE CONTACTS carrying those admissions, by species:");
    println!("      simple      one carrier at the site on both sides, crossing nothing");
    println!("      superposed  several occurrences co-present at the site — they superpose there");
    println!(
        "      crossed     the bridging stem overlaps another without containment, so the two"
    );
    println!("                  share letters neither can give up: taking one engages the other");
    for (species, count) in &top.contacts {
        println!("    {species:<44} {count:>7}");
    }
    if top.contacts.is_empty() {
        println!("    (none: no statement was admitted at this rung)");
    }

    println!("\n  and how the contact population moved up the ladder:");
    println!(
        "    {:>6}  {:>9}  {:>12}  {:>9}",
        "docs", "simple", "superposed", "crossed"
    );
    for rung in &climbed {
        println!(
            "    {:>6}  {:>9}  {:>12}  {:>9}",
            rung.documents,
            rung.contacts.get("simple").copied().unwrap_or(0),
            rung.contacts.get("superposed").copied().unwrap_or(0),
            rung.contacts.get("crossed").copied().unwrap_or(0),
        );
    }

    println!("\n  the refusal population, by species — every one retained:");
    for (species, count) in &top.refused {
        println!("    {species:<44} {count:>7}");
    }

    // ---------------------------------------------------------------------------------------------

    rule("WHAT MOVED WITH THE ATMOSPHERE");

    let first = climbed.first().expect("a rung climbed");
    let gained: BTreeSet<&String> = top
        .admitted
        .iter()
        .filter(|statement| !first.admitted.contains(statement))
        .collect();
    let lost: BTreeSet<&String> = first
        .admitted
        .iter()
        .filter(|statement| !top.admitted.contains(statement))
        .collect();
    println!(
        "  from {} document(s) to {}: {} statements appeared, {} departed.",
        first.documents,
        top.documents,
        gained.len(),
        lost.len()
    );
    println!("\n  appeared:");
    for statement in &gained {
        println!("    |- {statement}");
    }
    println!("\n  departed:");
    for statement in &lost {
        println!("    |- {statement}");
    }
    println!(
        "\n  A departure at greater scale is not a loss: a corpus that founds more stems refuses\n  \
         more candidates as well as licensing more, and which of the two dominates is the finding\n  \
         rather than the expectation. Both populations are exhibited by name."
    );

    // ---------------------------------------------------------------------------------------------
    // The gluing, and the return stroke
    // ---------------------------------------------------------------------------------------------

    rule("THE GLUING — what the union carries that neither stem carries alone");

    println!("  Every contact site is a COVER: the word's offsets are 0-cells, its founded stem");
    println!(
        "  occurrences are 1-cells, and two occurrences meet exactly when they share an offset."
    );
    println!(
        "  `gluing::read_cover` returns the rank of the connecting map per grade — the classes"
    );
    println!("  `A∪B` carries that neither `A` nor `B` does.\n");

    let exposures: Vec<Exposure> = atmosphere
        .iter()
        .take(top.documents)
        .map(|(name, text)| expose(name, text))
        .collect();
    let morphology = FoundedMorphology::condition(&exposures);
    let mut body = ConditionedBody::mount(ground.clone()).expect("the ground mounts");
    body.carry_morphology(morphology.clone());

    let mut glued = 0usize;
    let mut connecting = 0usize;
    let mut shown = 0usize;
    for word in body.recruited_population() {
        let Ok(cover) = morphology.cover(&word) else {
            continue;
        };
        let crossings = cover.crossings();
        let Some((left, right)) = crossings.first() else {
            continue;
        };
        let Ok((_, reading)) = glue_at_contact(
            &cover,
            &left.stem,
            &right.stem,
            PivotRule::SmallestMagnitude,
        ) else {
            continue;
        };
        glued += 1;
        let carries: i64 = reading.obstruction.iter().sum();
        if reading.exhibits_obstruction() {
            connecting += 1;
        }
        if shown < 6 {
            println!(
                "    {word:<22} `{}` x `{}`   beta0 {}/{} -> union {}   overlap beta0 {}   delta {carries}",
                left.stem,
                right.stem,
                reading.left.grades[0].betti,
                reading.right.grades[0].betti,
                reading.union.grades[0].betti,
                reading.overlap.grades[0].betti,
            );
            shown += 1;
        }
    }
    println!("\n  {glued} crossing contacts glued; {connecting} carry a non-zero connecting map.");

    rule("THE RETURN STROKE — the leader integrated, absorbed as a causal string");

    println!(
        "  A leader is a walk along founded occurrences; integrating it is an exact running sum"
    );
    println!(
        "  over `BigInt` with no tolerance. The stroke is that walk READ BACK AS A STRING — the"
    );
    println!(
        "  ordered stems it rode — with the series retained term by term rather than collapsed.\n"
    );

    let mut strokes = 0usize;
    for word in body.recruited_population().into_iter().take(400) {
        let Ok(cover) = morphology.cover(&word) else {
            continue;
        };
        let Some(first) = cover.occurrences.first() else {
            continue;
        };
        let Ok((_, stroke)) =
            integrate_leader(&cover, &morphology, &first.stem, LeaderCochain::SpanLength)
        else {
            continue;
        };
        if stroke.string.len() < 2 || strokes >= 6 {
            continue;
        }
        println!(
            "    {word:<22} rode {:?}\n{:<26} word `{}`   integral {}   series {:?}",
            stroke.string, "", stroke.word, stroke.integral, stroke.series
        );
        strokes += 1;
    }
    if strokes == 0 {
        println!("    (no leader rode more than one occurrence at this scale)");
    }

    rule("BOUNDS");
    println!(
        "  - The ladder stopped at {} of {} documents.",
        top.documents,
        atmosphere.len()
    );
    println!("  - Every figure has one frame and no timing here is falsifiable (`CLAUDE.md` §8).");
    println!("  - Nothing is submitted to a kernel. A founded statement is production read as");
    println!("    structure; whether it type-checks is a separate receiver and is not claimed.");
}
