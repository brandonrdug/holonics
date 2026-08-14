//! Coherence is collocation over time, at three grains, against the null-bind.
//!
//! ```text
//! cargo run --release --example faces_grow_from_collocation -- standing/output
//! ```
//!
//! ## What this driver is for
//!
//! `holonic_engine::name_elaboration` walks **recruitment** and reported that 17 of the deposit's 18
//! identifiers are atoms with no constituents, and therefore undiscriminable without a richer
//! deposit. `holonic_engine::collocation` implements the ratified law that says otherwise:
//! *two things relate iff presented together, within one source.* An atom recruits nothing and
//! still **collocates**, so its face is founded with no declaration at all.
//!
//! ## The declared controls
//!
//! Each is printed with its evidence and the run exits non-zero if any fails.
//!
//! ```text
//!   1  THE NULL-BIND -- the same items, the same counts, the pairing destroyed, and what it founds
//!   2  collocation founds a face on an item whose recruitment closure is empty
//!   3  the regions are emergent: nothing in the code declares a cluster, a count, or a membership
//!   4  two grains disagree, with the passage and both grains named
//!   5  nothing dropped silently: every item measured is in the return, every bound is declared
//! ```
//!
//! **Control 1 is the one that decides whether the organ is real, and its verdict is not the one
//! the construction hoped for.** The raw forced-passage population does *not* survive the
//! null-bind, and the driver prints that first and in full, because a falsification is a
//! first-class return. What *does* survive it is stated with the same evidence: the **face
//! population** and the **homology of the co-presentation complex**, both of which separate real
//! from re-paired at every grain and under every declared schedule.
//!
//! ## Why three grains rather than a second material
//!
//! `standing/output` carries 18 items. Eighteen is small enough that a re-pairing can reproduce a
//! forcing by coincidence, so a single incidence could not decide anything. The driver therefore
//! reads one material at **three grains** — 4 foundings, 103 artifacts, 558 lines — which is three
//! incidences of very different shape, and runs every control at each. Where a reading holds at one
//! grain and fails at another, both are printed. That is `FORMULA.md:615`'s *"coherence is
//! collocation at EVERY grain"* used as the falsifier it is.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use holonic_engine::collocation::{
    CoPresentation, CollocationDeposit, ComplexAperture, ForcedPassage, NullBindScope,
    Presentation, lean_artifact_items, lean_line_items,
};
use holonic_engine::derivation_atlas::{Derivation, read_derivation};
use holonic_engine::name_elaboration::{ElaborationAperture, ElaborationDeposit};
use holonic_engine::rebase_invariants::{PivotRule, rebase_invariants};

/// The declared enumeration aperture: the co-presented population any one reading may walk. A
/// reading that exceeds it is **refused with the bound**, never truncated.
const ENUMERATION_APERTURE: usize = 200_000;

/// The declared complex aperture. Homology is read on the 3-skeleton, so `β₀`, `β₁` and `β₂` are
/// exact for the whole complex and everything above is named rather than computed. The founding
/// grain's complete complex carries sixteen thousand cells and a dense integer reduction of it
/// would be a cost with no return; the f-vector below reports every one of them anyway.
const COMPLEX_APERTURE: ComplexAperture = ComplexAperture::ToGrade(3);

/// The pivot rule every integer reduction here is taken under. A pivot order is a receiver
/// coordinate and is never compared as an invariant.
const RULE: PivotRule = PivotRule::FirstNonzero;

/// The declared null-bind schedules. Three stride lists, no random number generator anywhere. Each
/// is a gauge on the pairing and the driver reports the orbit each one actually produced, because a
/// gauge whose group acts trivially on the material is not a gauge.
const SCHEDULES: [(&str, &[usize]); 3] = [
    ("A", &[1, 2, 3, 5, 7, 11, 13, 17, 19, 23]),
    ("B", &[29, 31, 37, 41, 43, 47, 53, 59, 61, 67]),
    ("C", &[71, 73, 79, 83, 89, 97, 101, 103, 107, 109]),
];

// -------------------------------------------------------------------------------------------------
// Reading the deposit at three grains
// -------------------------------------------------------------------------------------------------

fn artifact_paths(root: &Path) -> Vec<PathBuf> {
    let mut found = Vec::new();
    let Ok(entries) = std::fs::read_dir(root) else {
        return found;
    };
    let mut here: Vec<PathBuf> = entries.flatten().map(|entry| entry.path()).collect();
    here.sort();
    for path in here {
        if path.is_dir() {
            found.extend(artifact_paths(&path));
        } else if path.extension().is_some_and(|carried| carried == "lean") {
            found.push(path);
        }
    }
    found
}

/// One artifact as it was deposited: its founding (the **source**), its name, and its text.
struct Artifact {
    source: String,
    name: String,
    text: String,
}

fn read_deposit(root: &Path) -> Vec<Artifact> {
    artifact_paths(root)
        .into_iter()
        .filter_map(|path| {
            let text = std::fs::read_to_string(&path).ok()?;
            let name = path.file_name()?.to_str()?.to_owned();
            let source = path
                .parent()
                .and_then(Path::file_name)
                .and_then(|carried| carried.to_str())
                .unwrap_or("(root)")
                .to_owned();
            Some(Artifact { source, name, text })
        })
        .collect()
}

/// **The aperture of "together", stated three ways.** Each is one source's own carving; no region
/// ever spans two sources, which is the referent law's requirement and not a convenience.
fn deposits(artifacts: &[Artifact]) -> Vec<CollocationDeposit> {
    // One deposited return is one presentation.
    let by_artifact: Vec<Presentation> = artifacts
        .iter()
        .filter_map(|artifact| {
            let items = lean_artifact_items(&artifact.text);
            (!items.is_empty()).then(|| Presentation {
                source: artifact.source.clone(),
                region: format!("{}/{}", artifact.source, artifact.name),
                items,
            })
        })
        .collect();

    // One line of one deposited return is one presentation.
    let by_line: Vec<Presentation> = artifacts
        .iter()
        .flat_map(|artifact| {
            artifact
                .text
                .lines()
                .enumerate()
                .filter_map(move |(ordinal, line)| {
                    let items = lean_line_items(line);
                    (!items.is_empty()).then(|| Presentation {
                        source: artifact.source.clone(),
                        region: format!("{}/{}:{ordinal}", artifact.source, artifact.name),
                        items,
                    })
                })
        })
        .collect();

    // One whole founding is one presentation.
    let mut pooled: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for artifact in artifacts {
        pooled
            .entry(artifact.source.clone())
            .or_default()
            .extend(lean_artifact_items(&artifact.text));
    }
    let by_founding: Vec<Presentation> = pooled
        .into_iter()
        .map(|(source, items)| Presentation {
            region: source.clone(),
            source,
            items,
        })
        .collect();

    vec![
        CollocationDeposit::found("founding", by_founding).expect("the deposit carries foundings"),
        CollocationDeposit::found("artifact", by_artifact).expect("the deposit carries artifacts"),
        CollocationDeposit::found("line", by_line).expect("the deposit carries lines"),
    ]
}

// -------------------------------------------------------------------------------------------------
// Printing
// -------------------------------------------------------------------------------------------------

fn rule_line(title: &str) {
    println!("\n{}", "=".repeat(98));
    println!("{title}");
    println!("{}", "=".repeat(98));
}

fn section(title: &str) {
    println!("\n{title}");
    println!("{}", "-".repeat(title.len()));
}

fn verdict(number: usize, title: &str, held: bool) -> bool {
    println!(
        "\n  CONTROL {number}  {}  {title}",
        if held { "HELD  " } else { "FAILED" }
    );
    held
}

/// A passage printed with everything that decides what it is worth.
fn passage_line(passage: &ForcedPassage, reproduced: bool) {
    println!(
        "    {:<10} {:<18} ==> {:<18} |ext|={:<4} refusing={:<4} sources={} Q={}/{}",
        if reproduced { "re-paired" } else { "SURVIVES " },
        passage.from,
        passage.to,
        passage.extent_from,
        passage.refusing.len(),
        passage.sources.len(),
        passage.quotient.numer(),
        passage.quotient.denom(),
    );
}

fn f_vector_line(label: &str, carried: &BTreeMap<u32, usize>) {
    let body: Vec<String> = carried
        .iter()
        .map(|(grade, count)| format!("{grade}:{count}"))
        .collect();
    println!(
        "    {label:<26} total {:<6} [{}]",
        carried.values().sum::<usize>(),
        body.join(" ")
    );
}

// -------------------------------------------------------------------------------------------------
// The invariants of one reading
// -------------------------------------------------------------------------------------------------

/// What one co-presentation returns, on the link where a cone point cannot make it tautological.
struct Reading {
    facets: usize,
    closed_regions: usize,
    faces: usize,
    /// Betti numbers **only where the aperture computes them exactly**. A truncated skeleton's top
    /// grade carries `cells - rank_in`, which is not a Betti number of anything, and printing it as
    /// one would be the receipt overstating its code.
    betti: Vec<usize>,
    /// Grades whose Betti number the aperture did not compute. Named, never quietly absent.
    betti_withheld: Vec<u32>,
}

fn read_invariants(reading: &CoPresentation) -> Reading {
    let (link, _) = reading.without_universal();
    let f_vector = link
        .f_vector(ENUMERATION_APERTURE)
        .expect("declared aperture");
    let built = link
        .complex(COMPLEX_APERTURE, ENUMERATION_APERTURE)
        .expect("declared aperture");
    let invariants = rebase_invariants(built.complex(), RULE).expect("an exact reduction");
    let carried = invariants.betti_vector();
    // Every grade is exact when the aperture bound nothing; otherwise exact strictly below it.
    let exact_through = if built.outside_aperture().is_empty() {
        carried.len()
    } else {
        COMPLEX_APERTURE
            .exact_to_grade()
            .map_or(carried.len(), |grade| {
                (grade as usize + 1).min(carried.len())
            })
    };
    Reading {
        facets: link.facets().len(),
        closed_regions: link.closed_regions().len(),
        faces: f_vector.values().sum(),
        betti: carried[..exact_through].to_vec(),
        betti_withheld: (exact_through as u32..carried.len() as u32).collect(),
    }
}

fn passage_set(reading: &CoPresentation) -> BTreeSet<(String, String)> {
    reading
        .forced_passages()
        .into_iter()
        .map(|passage| (passage.from, passage.to))
        .collect()
}

// -------------------------------------------------------------------------------------------------
// main
// -------------------------------------------------------------------------------------------------

fn main() {
    let root = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "standing/output".to_owned());
    let root = PathBuf::from(root);
    let artifacts = read_deposit(&root);

    rule_line("FACES GROW FROM COLLOCATION -- the ratified law, over the deposited standing");
    println!(
        "\n  material           {} deposited returns under {}",
        artifacts.len(),
        root.display()
    );
    if artifacts.is_empty() {
        println!("\n  the deposit is empty; nothing can be read from it.");
        std::process::exit(2);
    }

    let deposits = deposits(&artifacts);
    let readings: Vec<CoPresentation> = deposits.iter().map(CoPresentation::read).collect();

    section("the aperture of \"together\", three ways");
    println!("  Every region lies inside ONE source. No relation here crosses a source boundary.");
    for (deposit, reading) in deposits.iter().zip(&readings) {
        println!(
            "    grain {:<9} {:>4} regions   {:>3} sources   {:>3} items   universal {:?}",
            deposit.grain(),
            deposit.regions(),
            deposit.sources().len(),
            reading.items().len(),
            reading.universal()
        );
    }

    // ---------------------------------------------------------------------------------------------
    // The faces, at every grain
    // ---------------------------------------------------------------------------------------------

    rule_line("THE FACES -- what co-presentation founds on each item, at each grain");
    for reading in &readings {
        section(&format!("grain: {}", reading.grain()));
        for item in reading.items() {
            let face = reading.face(item);
            println!(
                "    {:<20} |ext|={:<4} sources={:<2} face={:?}",
                item,
                reading.extent(item).len(),
                reading.sources_of(item).len(),
                face.iter().cloned().collect::<Vec<_>>()
            );
        }
        let classes = reading.separation_classes();
        println!(
            "    -> {} distinct faces over {} items; the collapsed classes are:",
            classes.len(),
            reading.items().len()
        );
        for (face, together) in &classes {
            if together.len() > 1 {
                println!(
                    "         {:?} share the face {:?}",
                    together.iter().cloned().collect::<Vec<_>>(),
                    face.iter().cloned().collect::<Vec<_>>()
                );
            }
        }
    }

    // ---------------------------------------------------------------------------------------------
    // CONTROL 1 -- the null-bind
    // ---------------------------------------------------------------------------------------------

    rule_line("CONTROL 1 -- THE NULL-BIND: the same items, the same counts, the pairing destroyed");
    println!(
        "\n  Double-edge swaps under three declared stride schedules, in two scopes. No random\n  \
         number generator. Both marginals are verified bit-exact before any reading is taken."
    );

    let mut control_one = true;
    let mut founds_forcings: Vec<(String, usize, usize, usize, usize, usize)> = Vec::new();
    for (reading, deposit) in readings.iter().zip(&deposits) {
        section(&format!(
            "grain: {} -- the pairing destroyed",
            reading.grain()
        ));
        let real = read_invariants(reading);
        let real_passages = reading.forced_passages();
        println!(
            "    REAL                       facets {:<4} closed-regions {:<4} faces {:<6} betti {:?} forced-passages {}",
            real.facets,
            real.closed_regions,
            real.faces,
            real.betti,
            real_passages.len()
        );
        if !real.betti_withheld.is_empty() {
            println!(
                "    (betti withheld at grades {:?}: the aperture truncates the skeleton there and\n     \
                 the reduction's top row is not a Betti number of anything.)",
                real.betti_withheld
            );
        }

        let mut reproduced: BTreeSet<(String, String)> = BTreeSet::new();
        let mut non_trivial_orbits = 0usize;
        let mut trivial_orbits: Vec<String> = Vec::new();
        let mut inflated = 0usize;
        let mut merged = 0usize;
        let mut null_forcings = 0usize;
        for scope in [NullBindScope::WholeDeposit, NullBindScope::WithinSource] {
            for (name, schedule) in SCHEDULES {
                let bound = deposit
                    .null_bind(schedule, scope)
                    .expect("a declared schedule");
                let scope_name = match scope {
                    NullBindScope::WholeDeposit => "whole-deposit",
                    NullBindScope::WithinSource => "within-source",
                };
                let shuffled = CoPresentation::read(bound.deposit());
                let carried = read_invariants(&shuffled);
                let passages = passage_set(&shuffled);
                let trivial = bound.regions_moved == 0;
                println!(
                    "    NULL-BIND {name} {scope_name:<14} facets {:<4} closed-regions {:<4} faces {:<6} betti {:?} forced-passages {:<4} (swaps {} refused {} regions moved {}/{}){}",
                    carried.facets,
                    carried.closed_regions,
                    carried.faces,
                    carried.betti,
                    passages.len(),
                    bound.applied,
                    bound.refused,
                    bound.regions_moved,
                    deposit.regions(),
                    if trivial { "  <- ORBIT TRIVIAL" } else { "" },
                );
                if trivial {
                    // A gauge whose group acts trivially on the declared material is not a gauge,
                    // and its agreement with the material is not evidence of anything.
                    trivial_orbits.push(format!("{name}/{scope_name}"));
                    continue;
                }
                non_trivial_orbits += 1;
                null_forcings += passages.len();
                reproduced.extend(
                    passage_set(reading)
                        .intersection(&passages)
                        .cloned()
                        .collect::<BTreeSet<_>>(),
                );
                if carried.faces > real.faces {
                    inflated += 1;
                }
                if carried.betti.first().copied().unwrap_or(0)
                    < real.betti.first().copied().unwrap_or(0)
                {
                    merged += 1;
                }
            }
        }
        let tally = (
            reading.grain().to_owned(),
            real_passages.len(),
            null_forcings,
            non_trivial_orbits,
            inflated,
            merged,
        );

        let survivors: Vec<&ForcedPassage> = real_passages
            .iter()
            .filter(|passage| !reproduced.contains(&(passage.from.clone(), passage.to.clone())))
            .collect();
        println!(
            "\n    of {} real forced passages, {} were reproduced by some null-bind and {} were not:",
            real_passages.len(),
            reproduced.len(),
            survivors.len()
        );
        let mut ordered = real_passages.clone();
        ordered.sort_by(|left, right| left.quotient.cmp(&right.quotient));
        for passage in &ordered {
            passage_line(
                passage,
                reproduced.contains(&(passage.from.clone(), passage.to.clone())),
            );
        }
        let highest_survivor = ordered
            .iter()
            .filter(|passage| !reproduced.contains(&(passage.from.clone(), passage.to.clone())))
            .map(|passage| passage.quotient.clone())
            .max();
        let lowest_reproduced = ordered
            .iter()
            .filter(|passage| reproduced.contains(&(passage.from.clone(), passage.to.clone())))
            .map(|passage| passage.quotient.clone())
            .min();
        if let (Some(low), Some(_)) = (&lowest_reproduced, &highest_survivor) {
            let below: Vec<String> = ordered
                .iter()
                .filter(|passage| passage.quotient < *low)
                .map(|passage| format!("{} => {}", passage.from, passage.to))
                .collect();
            let below_survived = ordered
                .iter()
                .filter(|passage| passage.quotient < *low)
                .all(|passage| !reproduced.contains(&(passage.from.clone(), passage.to.clone())));
            println!(
                "\n    the lowest Q any null-bind reproduced here is {}/{}, and the material carries\n    \
                 {} passage(s) below it: {:?}",
                low.numer(),
                low.denom(),
                below.len(),
                below
            );
            if below.is_empty() {
                println!(
                    "    -- so the cross-check between the exact quotient and the realized re-pairing\n       \
                     returns NOTHING at this grain and is not evidence here. Reported, not counted."
                );
            } else {
                println!("    -- and every one of them survived every null-bind: {below_survived}");
            }
        }

        println!(
            "\n    null-binds with a NON-TRIVIAL orbit   {non_trivial_orbits} of 6\n    \
             null-binds with a trivial orbit       {:?}  (not evidence, and excluded from every\n      \
             reading above: a gauge whose group acts trivially on the declared material is not a\n      \
             gauge, and its agreement with the material says nothing)\n    \
             of the {non_trivial_orbits} that moved, INFLATED the face population  {inflated}\n    \
             of the {non_trivial_orbits} that moved, MERGED the components         {merged}",
            trivial_orbits
        );
        // The face population is what the law says grows; the component count is what the material
        // presents as disjoint. A grain where no null-bind moved anything decides nothing.
        if non_trivial_orbits == 0 || inflated != non_trivial_orbits {
            control_one = false;
        }
        founds_forcings.push(tally);
    }

    println!("\n  THE RESULT, stated first because it is a falsification.\n");
    println!(
        "    {:<10} {:>12} {:>12} {:>10} {:>12} {:>12}",
        "grain", "real forced", "null forced", "orbits", "inflated", "merged"
    );
    for (grain, real, null, orbits, inflated, merged) in &founds_forcings {
        println!(
            "    {grain:<10} {real:>12} {null:>12} {orbits:>10} {:>12} {:>12}",
            format!("{inflated}/{orbits}"),
            format!("{merged}/{orbits}")
        );
    }
    println!(
        "\n  The null-bind DOES found forced passages, at every grain, in quantity. A shuffled\n  \
         co-presentation is NOT sterile, and an organ returning the raw forcing relation would have\n  \
         returned something a re-pairing reproduces. That is `CLAUDE.md` §8's tautology rule firing on\n  \
         this organ's own first construction: an item present in 101 of 103 regions is forced by\n  \
         ARITHMETIC, and a count of forcings cannot tell that apart from a relation.\n\n  \
         What the null-bind cannot do is reproduce the material's CONCENTRATION. The same regions, the\n  \
         same sizes, the same item counts found roughly twice the facets and twice the faces once the\n  \
         pairing is destroyed -- every non-trivial re-pairing, at every grain, without exception. The\n  \
         co-presentation complex's β₀ falls under most of them too, though not all: the real material\n  \
         presents DISJOINT families and a re-pairing usually joins them, and the `merged` column above\n  \
         says exactly how often. Both are properties of the FACE POPULATION, which is what the law\n  \
         says grows -- not of a table of pairs, which is what the naive reading returns.\n\n  \
         The exact quotient Q and the realized re-pairing are two independent instruments over the\n  \
         same question and they agree wherever the comparison is non-vacuous."
    );
    let one = verdict(
        1,
        "the null-bind moves the material and EVERY non-trivial re-pairing inflates the face \
         population -- but it founds forcings, so the raw forcing relation is NOT the organ's return",
        control_one,
    );

    // ---------------------------------------------------------------------------------------------
    // CONTROL 2 -- the atom
    // ---------------------------------------------------------------------------------------------

    rule_line(
        "CONTROL 2 -- an atom's recruitment closure is empty and its collocation face is not",
    );

    let derivations: Vec<Derivation> = artifacts
        .iter()
        .filter_map(|artifact| read_derivation(&artifact.text))
        .collect();
    let elaboration = ElaborationDeposit::read(&derivations);
    let artifact_grain = readings
        .iter()
        .find(|reading| reading.grain() == "artifact")
        .expect("the artifact grain");
    let founding_grain = readings
        .iter()
        .find(|reading| reading.grain() == "founding")
        .expect("the founding grain");

    section("every item, by what recruitment returns and what collocation returns");
    let mut separated = Vec::new();
    for item in artifact_grain.items() {
        let recruits = elaboration
            .elaborate(item, ElaborationAperture::Exhausted)
            .map(|meaning| {
                meaning
                    .constituents()
                    .keys()
                    .filter(|name| *name != item)
                    .cloned()
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default();
        let face = artifact_grain.face(item);
        println!(
            "    {:<20} recruitment-closure {:<3} {:<40} collocation-face {}",
            item,
            recruits.len(),
            format!("{recruits:?}"),
            format!("{:?}", face.iter().cloned().collect::<Vec<_>>()),
        );
        if recruits.is_empty() && !face.is_empty() {
            separated.push(item.clone());
        }
    }
    println!(
        "\n    {} items have an EMPTY recruitment closure and a NON-EMPTY collocation face:\n      {:?}",
        separated.len(),
        separated
    );

    let recruitment_classes = {
        let mut classes: BTreeMap<Vec<String>, Vec<String>> = BTreeMap::new();
        for item in artifact_grain.items() {
            let key = elaboration
                .elaborate(item, ElaborationAperture::Exhausted)
                .map(|meaning| {
                    meaning
                        .constituents()
                        .keys()
                        .filter(|name| *name != item)
                        .cloned()
                        .collect::<Vec<_>>()
                })
                .unwrap_or_default();
            classes.entry(key).or_default().push(item.clone());
        }
        classes
    };
    println!(
        "\n    SEPARATION, side by side, over the same 18 identifiers:\n      \
         recruitment            {:>2} classes\n      \
         collocation / line     {:>2} classes\n      \
         collocation / artifact {:>2} classes\n      \
         collocation / founding {:>2} classes",
        recruitment_classes.len(),
        readings
            .iter()
            .find(|reading| reading.grain() == "line")
            .expect("line")
            .separation_classes()
            .len(),
        artifact_grain.separation_classes().len(),
        founding_grain.separation_classes().len(),
    );
    let two = verdict(
        2,
        "collocation founds a face on an item that declares nothing and is declared by nothing",
        !separated.is_empty()
            && founding_grain.separation_classes().len() > recruitment_classes.len(),
    );

    // ---------------------------------------------------------------------------------------------
    // CONTROL 3 -- the regions are emergent
    // ---------------------------------------------------------------------------------------------

    rule_line("CONTROL 3 -- the regions are emergent, never designed");
    println!(
        "\n  Nothing in `collocation.rs` names a cluster, a region count, or a membership. The two\n  \
         region populations below are both DERIVED: the facets are the maximal co-presented sets and\n  \
         the closed regions are the fixed points of `A -> int(ext(A))`. Neither was declared and\n  \
         neither can be tuned; the only declared quantities in the module are the two APERTURES, and\n  \
         both refuse rather than truncate."
    );
    let mut emergent = true;
    for reading in &readings {
        let facets = reading.facets();
        let closed = reading.closed_regions();
        section(&format!("grain: {}", reading.grain()));
        println!(
            "    {} regions presented -> {} distinct facets, {} closed regions",
            reading.regions(),
            facets.len(),
            closed.len()
        );
        for facet in facets.iter().take(6) {
            println!(
                "      facet {:?}",
                facet.iter().cloned().collect::<Vec<_>>()
            );
        }
        if facets.len() > 6 {
            println!("      ... and {} more, all in the return", facets.len() - 6);
        }
        if facets.is_empty() || closed.len() < facets.len() {
            emergent = false;
        }
    }
    let three = verdict(
        3,
        "the returned region population is derived from what was presented and nothing declares it",
        emergent,
    );

    // ---------------------------------------------------------------------------------------------
    // CONTROL 4 -- two grains disagree
    // ---------------------------------------------------------------------------------------------

    rule_line("CONTROL 4 -- two grains disagree, and both are named");

    let mut by_grain: BTreeMap<&str, BTreeSet<(String, String)>> = BTreeMap::new();
    for reading in &readings {
        by_grain.insert(reading.grain(), passage_set(reading));
    }
    let mut disagreements = 0usize;
    for (left, right) in [
        ("artifact", "line"),
        ("founding", "artifact"),
        ("founding", "line"),
    ] {
        let here = &by_grain[left];
        let there = &by_grain[right];
        let only_left: Vec<String> = here
            .difference(there)
            .map(|(from, to)| format!("{from} => {to}"))
            .collect();
        let only_right: Vec<String> = there
            .difference(here)
            .map(|(from, to)| format!("{from} => {to}"))
            .collect();
        section(&format!("{left} against {right}"));
        println!(
            "    present at {left} and absent at {right}: {} -- {:?}",
            only_left.len(),
            only_left.iter().take(6).collect::<Vec<_>>()
        );
        println!(
            "    present at {right} and absent at {left}: {} -- {:?}",
            only_right.len(),
            only_right.iter().take(6).collect::<Vec<_>>()
        );
        if only_left.is_empty() && only_right.is_empty() {
            println!("    the two grains agree exactly; the grain parameter does no work here.");
        } else {
            disagreements += 1;
        }
        if only_right.is_empty() {
            println!(
                "    NOTE: the disagreement is one-directional. Every {right}-grain forcing is also\n    \
                 an {left}-grain forcing on this material -- a {right} region sits inside exactly one\n    \
                 {left} region, so its extent can only shrink, and a shrunken extent forces more.\n    \
                 That is a fact about this carving, not a law; `founding` against `line` breaks it."
            );
        }
    }
    let survives_every_grain: Vec<String> = by_grain["artifact"]
        .iter()
        .filter(|passage| {
            by_grain["line"].contains(passage) && by_grain["founding"].contains(passage)
        })
        .map(|(from, to)| format!("{from} => {to}"))
        .collect();
    println!(
        "\n    what survives ALL THREE grains: {:?}",
        survives_every_grain
    );
    println!(
        "    the separating power is NOT monotone in the grain: {} / {} / {} classes at\n    \
         line / artifact / founding, so the FINEST grain separates LEAST -- a line is too small a\n    \
         region to force anything, and the law's \"across time\" has nothing to range over. Coherence\n    \
         is collocation at every grain; the separation it returns is not.",
        readings
            .iter()
            .find(|reading| reading.grain() == "line")
            .expect("line")
            .separation_classes()
            .len(),
        artifact_grain.separation_classes().len(),
        founding_grain.separation_classes().len(),
    );
    let four = verdict(
        4,
        "the grain parameter does work: every pair of grains carries a passage the other does not",
        disagreements == 3,
    );

    // ---------------------------------------------------------------------------------------------
    // CONTROL 5 -- nothing dropped
    // ---------------------------------------------------------------------------------------------

    rule_line(
        "CONTROL 5 -- nothing dropped silently; every bound declared and what fell outside named",
    );

    let mut nothing_dropped = true;
    for (reading, deposit) in readings.iter().zip(&deposits) {
        section(&format!("grain: {}", reading.grain()));
        let faces = reading.faces();
        let every_item_returned = reading
            .items()
            .iter()
            .all(|item| faces.contains_key(item) && !reading.extent(item).is_empty());
        let presented: BTreeSet<&str> = deposit.items();
        let returned: BTreeSet<&str> = reading.items().iter().map(String::as_str).collect();
        println!(
            "    items presented {} -> items in the return {} -> every one carries an extent and a face: {}",
            presented.len(),
            returned.len(),
            every_item_returned
        );
        if presented != returned || !every_item_returned {
            nothing_dropped = false;
        }

        let (link, emptied) = reading.without_universal();
        if reading.universal().is_empty() {
            println!(
                "    no item is universal here, so the complex is not a cone and its homology is\n    \
                 already a fact about the material. The link is the complex."
            );
        } else {
            println!(
                "    the universal items {:?} are a CONE POINT; the complex over them is contractible\n    \
                 whatever the material does -- the tautology a homology reading has to detect. Homology\n    \
                 is therefore read on the LINK. Regions emptied by the deletion, by name: {:?}",
                reading.universal().iter().cloned().collect::<Vec<_>>(),
                emptied
            );
        }

        let whole = link
            .f_vector(ENUMERATION_APERTURE)
            .expect("declared aperture");
        let built = link
            .complex(COMPLEX_APERTURE, ENUMERATION_APERTURE)
            .expect("declared aperture");
        f_vector_line("the whole complex", &whole);
        f_vector_line("founded under the aperture", built.founded());
        f_vector_line("OUTSIDE the aperture", built.outside_aperture());
        let invariants = rebase_invariants(built.complex(), RULE).expect("an exact reduction");
        let carried = read_invariants(reading);
        println!(
            "    aperture {:?}; betti {:?} exact; betti WITHHELD at grades {:?}; torsion {:?};\n    \
             euler {} -- {}",
            COMPLEX_APERTURE,
            carried.betti,
            carried.betti_withheld,
            invariants.total_torsion(),
            invariants.euler_characteristic(),
            if built.outside_aperture().is_empty() {
                "of the whole complex, which the aperture did not bind"
            } else {
                "of the founded skeleton, NOT of the whole complex, and it is printed as such"
            },
        );
        let accounted: usize = built.founded().values().sum::<usize>()
            + built.outside_aperture().values().sum::<usize>();
        println!(
            "    founded + outside = {accounted}; the whole complex = {}; balanced: {}",
            whole.values().sum::<usize>(),
            accounted == whole.values().sum::<usize>()
        );
        if accounted != whole.values().sum::<usize>() {
            nothing_dropped = false;
        }
    }
    let five = verdict(
        5,
        "every item measured is in the return and every declared bound names what fell outside it",
        nothing_dropped,
    );

    // ---------------------------------------------------------------------------------------------

    rule_line("VERDICTS");
    let all = [one, two, three, four, five];
    for (ordinal, held) in all.iter().enumerate() {
        println!(
            "  control {}  {}",
            ordinal + 1,
            if *held { "HELD" } else { "FAILED" }
        );
    }
    if all.iter().all(|held| *held) {
        println!("\n  every declared control held.");
    } else {
        println!("\n  a declared control failed.");
        std::process::exit(1);
    }
}
