//! **The material hands over its own atlas.**
//!
//! `research/records/2026-07-19_…THE_INCIDENCE_REACTS…md` §I: *"The source therefore owes more than
//! a sequence of relation words and less than an authored meaning. It supplies a bounded oriented
//! incidence atlas."* `incidence_production::IncidenceComplex::found` takes inscription patches, so
//! until now every material entered through one byte chart. Lean, Rust and arithmetic each already
//! carry an oriented incidence atlas; this driver hands each one over and measures whether the four
//! then **conduct differently**.
//!
//! ```text
//! cargo run --release -p life --example the_material_hands_over_its_own_atlas
//! ```
//!
//! # The two falsifiers, both of which can fail
//!
//! 1. **The four material kinds must conduct differently.** The same readings — constituents,
//!    contacts, closed boundaries, cancellations, holonomy flat/curved, grain reached, successors
//!    with residuals — are taken identically across Lean, Rust, arithmetic and prose at comparable
//!    extents. **If the shapes are indistinguishable the intake is still orthographic**, and this
//!    driver says so rather than tuning until they differ.
//! 2. **`2+2`, `4`, `2·2`, `2²` are one denoted value and four constructions.** The complex must
//!    separate them; a declared denoted-value receiver must collapse them; and the collapse must be
//!    exhibited as the quotient it is — every collapsed pair with the word that separates it.
//!
//! Scale is reported in **counted work** and never in elapsed time (`CLAUDE.md` §8).

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};

use holonic_engine::lean_development::{join, read_development, DeclarationGrain};
use life::{
    incidence_production::{IncidenceComplex, PhaseChart},
    laboratory_language::{LaboratorySourceAtlas, LaboratorySourceKind, LaboratorySourceRoots},
    material_incidence::{
        arithmetic_atlas, arithmetic_family, denoted_value_quotient, lean_atlas, prose_atlas,
        read_conduct, rust_atlas, rust_items_of_section, ArithConstruction, ConductReading,
        MaterialAtlas, MaterialIncidenceError, MaterialKind, RankRepresentative, RustItem,
    },
};

/// The declared Lean extents, in containers admitted. The corpus carries 8,625.
const LEAN_EXTENTS: &[usize] = &[64, 256, 1024, 4096, 8625];

/// The declared Rust extents, in brace-balanced source sections admitted. The atlas carries 29,482.
const RUST_EXTENTS: &[usize] = &[256, 1024, 4096, 16_384, 29_482];

/// The declared prose extents, in theory sections admitted.
const PROSE_EXTENTS: &[usize] = &[8, 32, 128, 512, 2048];

/// The declared prose patch extent per section.
const PROSE_PATCH_EXTENT: usize = 96;

/// The declared route source aperture. Its outside is returned.
const SOURCE_APERTURE: usize = 48;

/// The declared route depth, before the route budget cuts it against the material's own degree.
const ROUTE_DEPTH: usize = 3;

/// The declared route budget. It bounds `max_incident_degree ^ depth`, the per-source predicted
/// work, and the total route population — every route carries an exact composition of rational
/// rotations, so the population is the cost. Its outside is returned.
const ROUTE_BUDGET: u128 = 120_000;

/// The declared interference aperture: arrivals at one constituent that will be scanned pairwise.
/// `IncidenceComplex::interfere` is quadratic in what it is handed.
const INTERFERENCE_ARRIVALS: usize = 96;

/// The declared closure budget. It bounds `hand_up`'s `Σ cycle length · contacts` and
/// `next_grain`'s `compounds² · contacts` — the two counted costs of closing and handing up.
const CLOSURE_BUDGET: u128 = 500_000_000;

/// The declared budget on `body::incidence::EventComplex`'s **unsorted** validation, in
/// `cells × incidences`. Handing the slices over in a reversed order sets `cells_indexed = false`
/// and the validator falls back to a linear scan per cell and per incidence.
const UNSORTED_VALIDATION_BUDGET: u128 = 30_000_000;

/// The constituent population the four materials are compared at.
const COMPARABLE_CONSTITUENTS: usize = 1_500;

/// The generated arithmetic family's operand range: every `a ∘ b` for `a, b` in `1..=n`.
const ARITHMETIC_OPERANDS: u32 = 12;

/// Above this declared contact population the rank-representative gauge orbit is not taken, since
/// it founds the complex twice more. The extents it was not taken at are reported.
const GAUGE_ORBIT_BUDGET: u64 = 60_000;

/// How many emitted successors to print per material.
const PRINTED_EMISSIONS: usize = 8;

fn main() {
    if let Err(error) = run() {
        eprintln!("REFUSED: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let workspace = workspace_root()?;
    println!("THE MATERIAL HANDS OVER ITS OWN ATLAS");
    println!("  workspace {}", workspace.display());
    println!(
        "  the seam: one DeclaredOccurrence per contact, two patches, `caused_by` carrying the \
         material's own dependency rank."
    );
    println!(
        "  nothing in `soma/life/src/incidence_production.rs` is edited; the constructor lives \
         beside `found`, in `material_incidence`."
    );
    println!();

    // -- the four atlases, swept ---------------------------------------------------------------
    let lean = lean_sweep(&workspace)?;
    let rust = rust_sweep(&workspace)?;
    let arithmetic = arithmetic_sweep()?;
    let prose = prose_sweep(&workspace)?;

    // -- FALSIFIER 1 — do the four conduct differently? ----------------------------------------
    println!();
    println!("FALSIFIER 1 — THE FOUR MATERIAL KINDS MUST CONDUCT DIFFERENTLY");
    println!(
        "  each row is the SAME reading, taken by the SAME function, on a complex founded through \
         the SAME seam. The comparison extent is the one whose constituent population is nearest \
         {COMPARABLE_CONSTITUENTS}."
    );
    let mut comparable = Vec::new();
    for swept in [&lean, &rust, &arithmetic, &prose] {
        if let Some(chosen) = nearest(swept, COMPARABLE_CONSTITUENTS) {
            comparable.push(chosen);
        }
    }
    print_conduct_table(&comparable);

    println!();
    let distinct = comparable
        .iter()
        .map(|entry| shape_word(&entry.reading))
        .collect::<BTreeSet<_>>();
    println!(
        "  distinct conduct shapes among {} materials: {}",
        comparable.len(),
        distinct.len()
    );
    for entry in &comparable {
        println!(
            "    {:>11}  {}",
            entry.reading.kind.name(),
            shape_word(&entry.reading)
        );
    }
    println!(
        "  {}",
        if distinct.len() == comparable.len() {
            "EVERY MATERIAL CONDUCTS ON ITS OWN SHAPE — the intake is not orthographic at this \
             extent"
        } else {
            "TWO OR MORE MATERIALS CONDUCT IDENTICALLY — the intake is still reading surfaces and \
             that is the finding, not a tuning target"
        }
    );

    // -- the full sweep, and where cost stops the run ------------------------------------------
    println!();
    println!("THE SWEEP — counted work, never a clock");
    for swept in [&lean, &rust, &arithmetic, &prose] {
        print_sweep(swept);
    }

    // -- the artifact: emitted successors, per material ----------------------------------------
    println!();
    println!("THE ARTIFACT — EMITTED SUCCESSORS AND THEIR RESIDUALS, PER MATERIAL");
    println!(
        "  `complete_(F,Q,0)(C_0) → (n_1, ρ_0)`. Counts alone are the failure that occasioned this \
         line, so the text is returned."
    );
    for swept in [&lean, &rust, &arithmetic, &prose] {
        // The comparison extent is where the four are compared; the artifact is returned at the
        // widest extent whose closure the declared budget admitted, so a material refused at the
        // comparison extent still returns its successors rather than a blank.
        let widest = swept
            .entries
            .iter()
            .rev()
            .find(|entry| !entry.reading.emissions.is_empty());
        match widest {
            Some(entry) => print_emissions(entry),
            None => {
                if let Some(entry) = swept.entries.last() {
                    print_emissions(entry);
                }
            }
        }
    }

    // -- FALSIFIER 2 — the four constructions of one value -------------------------------------
    println!();
    println!("FALSIFIER 2 — ONE DENOTED VALUE, FOUR CONSTRUCTIONS");
    arithmetic_soul()?;

    // -- the orthographic residue, measured ----------------------------------------------------
    println!();
    println!("THE ORTHOGRAPHIC RESIDUE THAT REMAINS, MEASURED RATHER THAN ASSERTED");
    orthographic_residue()?;

    Ok(())
}

// ---------------------------------------------------------------------------------------------
// One swept material
// ---------------------------------------------------------------------------------------------

struct Swept {
    kind: MaterialKind,
    provenance: String,
    entries: Vec<Entry>,
}

struct Entry {
    extent: usize,
    containers: u64,
    atlas_constituents: u64,
    atlas_contacts: u64,
    cyclic_contacts: u64,
    cores: u64,
    open_joins: u64,
    ranks: u64,
    faithful: bool,
    body_admits: bool,
    /// `None` where the declared budget refused the quadratic unsorted validation.
    body_admits_reordered: Option<bool>,
    unsorted_work: u128,
    /// `None` where the declared gauge-orbit budget refused to found the complex twice more.
    rank_gauge: Option<bool>,
    reading: ConductReading,
}

fn found_entry(
    extent: usize,
    atlas: &MaterialAtlas,
) -> Result<Entry, MaterialIncidenceError> {
    let work = atlas.intake_work();
    stage(atlas.kind(), extent, "atlas read");
    let complex = atlas.found(RankRepresentative::Least)?;
    stage(atlas.kind(), extent, "complex founded");
    let faithfulness = atlas.faithfulness(&complex);
    let body_admits = complex.validate_with_body(true).is_ok();
    stage(atlas.kind(), extent, "body admits (indexed)");
    // The storage-order gauge control hands the same complex over in a reversed order, which sets
    // `EventComplex::cells_indexed = false` and makes its validator fall back to a LINEAR scan per
    // cell and per incidence — quadratic. At 72 constituents that is invisible; here it is the
    // wall, so it is taken under a declared budget in counted work and its outside is reported.
    let cells =
        (complex.sites().len() + complex.bonds().len() + complex.compounds().len()) as u128;
    let incidences = (2 * complex.bonds().len() + complex.dependencies().len()) as u128
        + complex
            .compounds()
            .iter()
            .map(|compound| compound.bonds.len() as u128)
            .sum::<u128>();
    let unsorted_work = cells.saturating_mul(incidences);
    let body_admits_reordered = if unsorted_work <= UNSORTED_VALIDATION_BUDGET {
        Some(complex.validate_with_body(false).is_ok())
    } else {
        None
    };
    stage(atlas.kind(), extent, "body admits (reordered)");
    // The gauge orbit founds the complex twice more. Above the declared budget it is not taken,
    // and the entry says so rather than reporting a check that never ran.
    let orbit = if work.contacts <= GAUGE_ORBIT_BUDGET {
        Some(atlas.rank_gauge_orbit()?)
    } else {
        None
    };
    stage(atlas.kind(), extent, "gauge orbit");
    let reading = read_conduct(
        atlas.kind(),
        &complex,
        PhaseChart::WindingAdjacent,
        SOURCE_APERTURE,
        ROUTE_DEPTH,
        ROUTE_BUDGET,
        INTERFERENCE_ARRIVALS,
        CLOSURE_BUDGET,
    )?;
    stage(atlas.kind(), extent, "conduct read");
    Ok(Entry {
        extent,
        containers: work.containers,
        atlas_constituents: work.constituents,
        atlas_contacts: work.contacts,
        cyclic_contacts: work.cyclic_contacts,
        cores: work.strongly_connected_cores,
        open_joins: work.open_joins,
        ranks: work.ranks,
        faithful: faithfulness.is_faithful(),
        body_admits,
        body_admits_reordered,
        unsorted_work,
        rank_gauge: orbit.map(|orbit| orbit.ranks_unmoved),
        reading,
    })
}

/// A stage marker on stderr, so a long sweep says where it is. It is a progress line and it is
/// never evidence.
fn stage(kind: MaterialKind, extent: usize, what: &str) {
    eprintln!("      · {} {extent}: {what}", kind.name());
}

fn nearest(swept: &Swept, target: usize) -> Option<&Entry> {
    swept.entries.iter().min_by_key(|entry| {
        entry
            .reading
            .constituents
            .abs_diff(target)
    })
}

/// The complex's own conduct shape as one word, so "do they differ" is checkable rather than eyed.
fn shape_word(reading: &ConductReading) -> String {
    format!(
        "closures/contact {}‰ · dependency/contact {}‰ · curved {} · plural arrivals {} · \
         grain {} · greatest multiplicity {} · greatest degree {}",
        per_mille(reading.closed_boundaries, reading.contacts),
        per_mille(reading.dependency_edges, reading.contacts),
        if reading.curved_boundaries == 0 {
            "none".to_owned()
        } else if reading.flat_boundaries == 0 {
            "every".to_owned()
        } else {
            "mixed".to_owned()
        },
        if reading.plural_arrivals == 0 { "none" } else { "some" },
        reading.grain_reached,
        reading.greatest_multiplicity,
        if reading.greatest_incident_degree > 1000 {
            "hub"
        } else if reading.greatest_incident_degree > 32 {
            "wide"
        } else {
            "narrow"
        }
    )
}

/// Parts per thousand, in integers. No float enters this driver at any point.
fn per_mille(part: usize, whole: usize) -> u128 {
    if whole == 0 {
        return 0;
    }
    (part as u128 * 1000) / whole as u128
}

fn print_conduct_table(entries: &[&Entry]) {
    println!(
        "  {:>11} {:>8} {:>9} {:>9} {:>8} {:>7} {:>7} {:>7} {:>8} {:>8} {:>6} {:>6} {:>6}",
        "material",
        "extent",
        "constit",
        "contacts",
        "⪯ edges",
        "closed",
        "flat",
        "curved",
        "routes",
        "plural",
        "annih",
        "grain",
        "degree"
    );
    for entry in entries {
        let reading = &entry.reading;
        println!(
            "  {:>11} {:>8} {:>9} {:>9} {:>8} {:>7} {:>7} {:>7} {:>8} {:>8} {:>6} {:>6} {:>6}",
            reading.kind.name(),
            entry.extent,
            reading.constituents,
            reading.contacts,
            reading.dependency_edges,
            reading.closed_boundaries,
            reading.flat_boundaries,
            reading.curved_boundaries,
            reading.routes,
            reading.plural_arrivals,
            reading.annihilating_pairs,
            reading.grain_reached,
            reading.greatest_incident_degree
        );
    }
    println!(
        "  every row: route source aperture {SOURCE_APERTURE}, declared route depth {ROUTE_DEPTH} \
         cut per material by the route budget {ROUTE_BUDGET}."
    );
    for entry in entries {
        println!(
            "    {:>11}  effective route depth {}  ·  sources outside the aperture {}  ·  arrival \
             fibers outside the interference budget {}",
            entry.reading.kind.name(),
            entry.reading.effective_route_depth,
            entry.reading.sources_outside_aperture,
            entry.reading.arrivals_outside_interference_budget
        );
        println!("                 closure: {}", entry.reading.grain_stop);
    }
}

fn print_sweep(swept: &Swept) {
    println!();
    println!("  {} — {}", swept.kind.name(), swept.provenance);
    println!(
        "  {:>9} {:>7} {:>9} {:>9} {:>8} {:>7} {:>9} {:>6} {:>9} {:>8} {:>6} {:>6}",
        "extent",
        "cont'rs",
        "K (atlas)",
        "∂ (atlas)",
        "cyclic ∂",
        "cores",
        "OPEN join",
        "ranks",
        "sites",
        "closed",
        "faith",
        "body"
    );
    for entry in &swept.entries {
        println!(
            "  {:>9} {:>7} {:>9} {:>9} {:>8} {:>7} {:>9} {:>6} {:>9} {:>8} {:>6} {:>6}",
            entry.extent,
            entry.containers,
            entry.atlas_constituents,
            entry.atlas_contacts,
            entry.cyclic_contacts,
            entry.cores,
            entry.open_joins,
            entry.ranks,
            entry.reading.constituents,
            entry.reading.closed_boundaries,
            if entry.faithful { "yes" } else { "NO" },
            match (entry.body_admits, entry.body_admits_reordered) {
                (true, Some(true)) => "both",
                (true, Some(false)) => "SORTED",
                (true, None) => "idx",
                _ => "NO",
            },
        );
    }
    if let Some(widest) = swept.entries.last() {
        if widest.body_admits_reordered.is_none() {
            println!(
                "    the storage-order gauge (`validate_with_body(false)`) was NOT taken at the \
                 widest extent: counted work {} above the declared budget \
                 {UNSORTED_VALIDATION_BUDGET}. `EventComplex` falls back to a linear scan per cell \
                 and per incidence when the slices are not in indexed order, so that control is \
                 quadratic and it is the first thing scale takes away.",
                widest.unsorted_work
            );
        }
    }
    if let Some(last) = swept.entries.last() {
        let taken = swept
            .entries
            .iter()
            .filter(|entry| entry.rank_gauge.is_some())
            .count();
        let unmoved = swept
            .entries
            .iter()
            .filter(|entry| entry.rank_gauge == Some(true))
            .count();
        println!(
            "    the rank representative is a gauge: taken at {taken} of {} extents (budget \
             {GAUGE_ORBIT_BUDGET} contacts), ranks unmoved at {unmoved}{}",
            swept.entries.len(),
            if taken == unmoved {
                ""
            } else {
                " — A RANK MOVED, so the intake is reading its own bookkeeping"
            }
        );
        println!("    at the widest admitted extent: {}", last.reading.grain_stop);
    }
}

fn print_emissions(entry: &Entry) {
    let reading = &entry.reading;
    println!();
    println!(
        "  ── {} at extent {} — {} closed boundaries, {} emitted successors at grain 1",
        reading.kind.name(),
        entry.extent,
        reading.closed_boundaries,
        reading.emissions.len()
    );
    if reading.emissions.is_empty() {
        println!("     NOTHING CLOSED, SO NOTHING HANDED UP. {}", reading.grain_stop);
        return;
    }
    for (at, emission) in reading.emissions.iter().take(PRINTED_EMISSIONS).enumerate() {
        println!();
        println!(
            "     [{at:>2}] grain {} · causal rank {} · holonomy {} · {} · chain gauge {:+}",
            emission.grain,
            emission.causal_rank,
            emission.holonomy,
            if emission.flat { "flat" } else { "CURVED" },
            emission.chain_gauge
        );
        println!("          surface  {}", elide(&emission.surface, 150));
        println!(
            "          residual {} internal contacts departed, carrying multiplicity {}",
            emission.internal_contacts, emission.carried_multiplicity
        );
        for contact in emission.departed.iter().take(4) {
            println!("                   departed {}", elide(contact, 140));
        }
        if emission.exposed.is_empty() {
            println!("                   exposed  NONE — this compound is saturated");
        } else {
            for exposed in emission.exposed.iter().take(4) {
                println!("                   exposed  {}", elide(exposed, 140));
            }
            if emission.exposed.len() > 4 {
                println!(
                    "                   exposed  … {} further",
                    emission.exposed.len() - 4
                );
            }
        }
    }
    if reading.emissions.len() > PRINTED_EMISSIONS {
        println!(
            "     … {} further successors not printed",
            reading.emissions.len() - PRINTED_EMISSIONS
        );
    }
}

// ---------------------------------------------------------------------------------------------
// Lean
// ---------------------------------------------------------------------------------------------

fn lean_sweep(workspace: &Path) -> Result<Swept, String> {
    let root = workspace.join("soma/formal");
    let mut paths = Vec::new();
    collect(&root, "lean", &mut paths)?;
    paths.sort();
    println!("LEAN — {} containers under soma/formal", paths.len());

    let mut entries = Vec::new();
    let mut carried: Vec<holonic_engine::lean_development::DevelopmentReading> = Vec::new();
    let mut read_at = 0usize;
    for extent in LEAN_EXTENTS {
        let extent = (*extent).min(paths.len());
        while read_at < extent {
            let text = std::fs::read_to_string(&paths[read_at])
                .map_err(|error| format!("read {}: {error}", paths[read_at].display()))?;
            carried.push(read_development(
                &text,
                DeclarationGrain::EveryTopLevelDeclaration,
            ));
            read_at += 1;
        }
        let reading = join(carried.clone());
        let recruitment = reading.declared_recruitment_qualified();
        let order = reading
            .declarations
            .iter()
            .filter(|form| !form.anonymous)
            .map(|form| form.qualified())
            .collect::<Vec<_>>();
        let open = reading
            .open_recruitment()
            .values()
            .map(|symbols| symbols.len() as u64)
            .sum::<u64>();
        // Tactic position is deliberately NOT joined. `lean_development::tactic_position_declared`
        // is documented as a *bounding instrument*: a declared name in tactic position is probably
        // a step-head misread, so joining it would manufacture edges the reading refuses.
        let atlas = lean_atlas(
            &recruitment,
            &BTreeMap::new(),
            &order,
            open,
            extent as u64,
        )
        .map_err(|error| format!("lean atlas at {extent}: {error:?}"))?;
        match found_entry(extent, &atlas) {
            Ok(entry) => {
                println!(
                    "  {extent:>6} containers → {} declarations · {} recruitment edges · {} OPEN",
                    order.len(),
                    atlas.contacts().len(),
                    open
                );
                entries.push(entry);
            }
            Err(error) => println!("  {extent:>6} containers refused: {error:?}"),
        }
        if extent == paths.len() {
            break;
        }
    }
    Ok(Swept {
        kind: MaterialKind::Lean,
        provenance: format!(
            "soma/formal, {} .lean containers; ∂ is \
             `lean_development::declared_recruitment_qualified` — the resolved term-position join, \
             which returns an ambiguous landing OPEN rather than choosing",
            paths.len()
        ),
        entries,
    })
}

// ---------------------------------------------------------------------------------------------
// Rust
// ---------------------------------------------------------------------------------------------

fn rust_sweep(workspace: &Path) -> Result<Swept, String> {
    let roots = LaboratorySourceRoots {
        theory: Vec::new(),
        code: vec![PathBuf::from("crates"), PathBuf::from("soma")],
    };
    let atlas = LaboratorySourceAtlas::mount_repository_roots(workspace, &roots, &BTreeSet::new())
        .map_err(|error| format!("mount the Rust atlas: {error:?}"))?;
    let sections = atlas
        .source_readings()
        .filter(|reading| reading.kind == LaboratorySourceKind::RustSource)
        .map(|reading| (reading.source.to_owned(), reading.text.to_owned()))
        .collect::<Vec<_>>();
    println!();
    println!(
        "RUST — {} brace-balanced source sections under crates/ and soma/ \
         (`LaboratorySourceAtlas`, reused not rebuilt)",
        sections.len()
    );

    let mut entries = Vec::new();
    let mut items: Vec<RustItem> = Vec::new();
    let mut read_at = 0usize;
    for extent in RUST_EXTENTS {
        let extent = (*extent).min(sections.len());
        while read_at < extent {
            let (source, text) = &sections[read_at];
            items.extend(rust_items_of_section(
                &module_of(source),
                read_at as u64,
                text,
            ));
            read_at += 1;
        }
        let atlas = rust_atlas(&items, extent as u64)
            .map_err(|error| format!("rust atlas at {extent}: {error:?}"))?;
        match found_entry(extent, &atlas) {
            Ok(entry) => {
                println!(
                    "  {extent:>6} sections → {} items · {} call edges · {} OPEN short names",
                    items.len(),
                    atlas.contacts().len(),
                    atlas.intake_work().open_joins
                );
                entries.push(entry);
            }
            Err(error) => println!("  {extent:>6} sections refused: {error:?}"),
        }
        if extent == sections.len() {
            break;
        }
    }
    Ok(Swept {
        kind: MaterialKind::Rust,
        provenance: format!(
            "crates/ and soma/, {} sections; ∂ is call and type incidence joined on the item's \
             short name, with an ambiguous name returned OPEN — `declared_recruitment`'s own \
             measured discipline",
            sections.len()
        ),
        entries,
    })
}

fn module_of(source: &str) -> String {
    source
        .trim_end_matches(".rs")
        .replace(['/', '-'], "·")
}

// ---------------------------------------------------------------------------------------------
// Arithmetic
// ---------------------------------------------------------------------------------------------

/// The declared family. Three denoted-value blocks, so the quotient is not vacuous, and every
/// construction of each value differing in **construction** rather than in presentation alone.
fn declared_family() -> Result<Vec<ArithConstruction>, String> {
    let presentations = [
        // denoting 4
        "4", "2+2", "2*2", "2^2", "6-2", "8/2", "1+1+2", "2*(1+1)", "(3-1)*2", "16/(2^2)", "-(-4)",
        "1+3", "3+1", "12/3",
        // denoting 5
        "5", "2+3", "3+2", "10/2", "7-2", "1+4", "(2+3)*1",
        // denoting 6
        "6", "2*3", "3*2", "2+4", "12/2", "8-2", "2^3-2", "(1+2)*2",
    ];
    arithmetic_family(&presentations).map_err(|error| format!("the family: {error:?}"))
}

/// The generated family, so arithmetic reaches the other three materials' extent.
///
/// The enumeration is the material: every `a ∘ b` for `a, b` in `1..=ARITHMETIC_OPERANDS` and every
/// binary operation, less the ones the exact arithmetic refuses. Nothing here is hand-picked, so
/// the denoted-value blocks are whatever the arithmetic makes them.
fn generated_family() -> Result<Vec<ArithConstruction>, String> {
    let mut presentations = Vec::new();
    for left in 1..=ARITHMETIC_OPERANDS {
        for right in 1..=ARITHMETIC_OPERANDS {
            for glyph in ['+', '-', '*', '/', '^'] {
                presentations.push(format!("{left}{glyph}{right}"));
            }
        }
    }
    let borrowed = presentations
        .iter()
        .map(String::as_str)
        .collect::<Vec<_>>();
    let family = arithmetic_family(&borrowed).map_err(|error| format!("{error:?}"))?;
    // The exact evaluator refuses what it must; a refused construction is not admitted.
    Ok(family
        .into_iter()
        .filter(|construction| construction.node.denoted_value().is_ok())
        .collect())
}

fn arithmetic_sweep() -> Result<Swept, String> {
    let family = generated_family()?;
    println!();
    println!(
        "ARITHMETIC — {} generated constructions `a ∘ b`, a,b ∈ 1..={ARITHMETIC_OPERANDS}, five \
         operations, exact over BigRational",
        family.len()
    );
    let mut entries = Vec::new();
    for extent in [16usize, 64, 256, family.len()] {
        let extent = extent.min(family.len());
        let cut = &family[..extent];
        let atlas =
            arithmetic_atlas(cut).map_err(|error| format!("arithmetic atlas: {error:?}"))?;
        match found_entry(extent, &atlas) {
            Ok(entry) => {
                println!(
                    "  {extent:>6} constructions → {} nodes · {} operand/hand contacts",
                    atlas.constituents().len(),
                    atlas.contacts().len()
                );
                entries.push(entry);
            }
            Err(error) => println!("  {extent:>6} constructions refused: {error:?}"),
        }
        if extent == family.len() {
            break;
        }
    }
    Ok(Swept {
        kind: MaterialKind::Arithmetic,
        provenance: format!(
            "{} generated constructions; ∂ is the operand incidence and, on a NON-COMMUTATIVE node \
             only, the left-before-right contact that is `o_t` written as a cell",
            family.len()
        ),
        entries,
    })
}

// ---------------------------------------------------------------------------------------------
// Prose
// ---------------------------------------------------------------------------------------------

fn prose_sweep(workspace: &Path) -> Result<Swept, String> {
    let roots = LaboratorySourceRoots {
        theory: vec![PathBuf::from("research/records"), PathBuf::from("canon")],
        code: Vec::new(),
    };
    let atlas = LaboratorySourceAtlas::mount_repository_roots(workspace, &roots, &BTreeSet::new())
        .map_err(|error| format!("mount the prose atlas: {error:?}"))?;
    let sections = atlas
        .source_readings()
        .filter(|reading| reading.kind == LaboratorySourceKind::Theory)
        .map(|reading| (reading.identity.to_owned(), reading.text.to_owned()))
        .collect::<Vec<_>>();
    println!();
    println!(
        "PROSE — {} theory sections under research/records and canon (the declared control: §III's \
         lawful byte-serialization chart, written as an atlas so it is strictly comparable)",
        sections.len()
    );

    let mut entries = Vec::new();
    for extent in PROSE_EXTENTS {
        let extent = (*extent).min(sections.len());
        let atlas = prose_atlas(&sections[..extent], PROSE_PATCH_EXTENT)
            .map_err(|error| format!("prose atlas at {extent}: {error:?}"))?;
        match found_entry(extent, &atlas) {
            Ok(entry) => {
                println!(
                    "  {extent:>6} sections → {} patches · {} adjacency contacts",
                    atlas.constituents().len(),
                    atlas.contacts().len()
                );
                entries.push(entry);
            }
            Err(error) => println!("  {extent:>6} sections refused: {error:?}"),
        }
        if extent == sections.len() {
            break;
        }
    }
    Ok(Swept {
        kind: MaterialKind::Prose,
        provenance: format!(
            "research/records and canon, {} sections at patch extent {PROSE_PATCH_EXTENT}",
            sections.len()
        ),
        entries,
    })
}

// ---------------------------------------------------------------------------------------------
// The soul: one denoted value, four constructions
// ---------------------------------------------------------------------------------------------

fn arithmetic_soul() -> Result<(), String> {
    let family = declared_family()?;
    let atlas = arithmetic_atlas(&family).map_err(|error| format!("{error:?}"))?;
    let complex = atlas
        .found(RankRepresentative::Least)
        .map_err(|error| format!("{error:?}"))?;
    let quotient = denoted_value_quotient(&family, &complex, PhaseChart::WindingAdjacent, 4)
        .map_err(|error| format!("{error:?}"))?;

    println!(
        "  the corpus's own retained law: presentation equality, denoted-value equality, receiver \
         equality and occurrence identity are FOUR separate relations."
    );
    println!(
        "    occurrence identity     {} constructions",
        quotient.occurrences
    );
    println!(
        "    presentation equality   {} distinct presentation strings",
        quotient.distinct_presentations
    );
    println!(
        "    denoted-value equality  {} blocks — the quotient",
        quotient.blocks.len()
    );
    println!(
        "    receiver equality       the founded complex, read per construction"
    );
    println!();
    println!("  THE CONSTRUCTIONS, PER DENOTED VALUE, AS THE COMPLEX FOUNDS THEM");
    println!(
        "  {:>12} {:>14} {:>9} {:>9} {:>8} {:>7} {:>28}",
        "value", "presentation", "nodes", "contacts", "closed", "depth", "holonomy at grain 1"
    );
    let per_construction = construction_readings(&family, &complex)?;
    for (value, block) in &quotient.blocks {
        for presentation in block {
            let reading = &per_construction[presentation];
            println!(
                "  {:>12} {:>14} {:>9} {:>9} {:>8} {:>7} {:>28}",
                format!("{value}"),
                presentation,
                reading.0,
                reading.1,
                reading.2,
                reading.3,
                reading.4
            );
        }
    }
    println!();
    println!(
        "  the commutative operations `+` and `*` emit no left-before-right contact, so their \
         constructions are TREES and close nothing. `-`, `/` and `^` do, so each closes exactly \
         one boundary per non-commutative node. THE HAND IS WHAT CLOSES."
    );

    println!();
    println!("  THE QUOTIENT, EXHIBITED AS THE QUOTIENT IT IS");
    println!(
        "  the denoted-value receiver identifies {} pairs; each is a collapsed pair and each \
         carries the word that separates it under the construction receiver (`H.0016`: the loss is \
         the collapsed population, family-relative).",
        quotient.separating_words.len() + quotient.indistinguishable.len()
    );
    for (left, right, word) in quotient.separating_words.iter().take(14) {
        println!("    {left:>10}  ≡ᵥ  {right:<10}   separated by {word}");
    }
    if quotient.separating_words.len() > 14 {
        println!(
            "    … {} further separated pairs",
            quotient.separating_words.len() - 14
        );
    }
    println!();
    if quotient.indistinguishable.is_empty() {
        println!(
            "  the construction receiver separated EVERY collapsed pair: the quotient's loss is \
             total and exhibitable."
        );
    } else {
        println!(
            "  {} collapsed pairs the construction receiver could NOT separate — the quotient's \
             own blind spot, returned rather than hidden:",
            quotient.indistinguishable.len()
        );
        for (left, right) in quotient.indistinguishable.iter().take(10) {
            println!("    {left:>10}  ≡  {right:<10}   indistinguishable at this receiver");
        }
    }
    Ok(())
}

type ConstructionRow = (usize, usize, usize, u32, String);

fn construction_readings(
    family: &[ArithConstruction],
    complex: &IncidenceComplex,
) -> Result<BTreeMap<String, ConstructionRow>, String> {
    let emissions = complex
        .hand_up(PhaseChart::WindingAdjacent)
        .map_err(|error| format!("{error:?}"))?;
    let mut found = BTreeMap::new();
    for construction in family {
        let owned = complex
            .sites()
            .iter()
            .enumerate()
            .filter(|(_, site)| {
                site.surface
                    .rsplit_once('#')
                    .is_some_and(|(_, label)| label == construction.label)
            })
            .map(|(at, _)| at)
            .collect::<BTreeSet<_>>();
        let contacts = complex
            .bonds()
            .iter()
            .filter(|bond| owned.contains(&bond.from) && owned.contains(&bond.to))
            .count();
        let closed = complex
            .compounds()
            .iter()
            .filter(|compound| compound.sites.iter().all(|site| owned.contains(site)))
            .count();
        let depth = owned
            .iter()
            .map(|at| complex.sites()[*at].causal_rank)
            .max()
            .unwrap_or(0);
        let holonomy = emissions
            .iter()
            .find(|emission| emission.surface.contains(&format!("#{}", construction.label)))
            .map(|emission| {
                format!(
                    "{} {}",
                    emission.holonomy_text(),
                    if emission.terrain_is_flat() { "flat" } else { "CURVED" }
                )
            })
            .unwrap_or_else(|| "— nothing closed".to_owned());
        found.insert(
            construction.presentation.clone(),
            (owned.len(), contacts, closed, depth, holonomy),
        );
    }
    Ok(found)
}

// ---------------------------------------------------------------------------------------------
// The residue
// ---------------------------------------------------------------------------------------------

/// Rename every constituent through a declared bijection and re-found.
///
/// The **structure** must be identical — same constituents, contacts, closed boundaries — because a
/// bijection on names changes no incidence. The **transport** moves, because
/// `incidence_production`'s phase chart reads `popcount` off the surface's own octets. That is the
/// exact residue this construction did not remove, and it is where a change to
/// `incidence_production.rs` would be needed: a `species` field on `Bond`, so `∂` carries the
/// contact's kind and the transport can be taken from the material's relation rather than from its
/// spelling.
fn orthographic_residue() -> Result<(), String> {
    let family = declared_family()?;
    let atlas = arithmetic_atlas(&family).map_err(|error| format!("{error:?}"))?;
    let complex = atlas
        .found(RankRepresentative::Least)
        .map_err(|error| format!("{error:?}"))?;

    let renamed_constituents = atlas
        .constituents()
        .iter()
        .enumerate()
        .map(|(at, _)| format!("q{at:05}"))
        .collect::<Vec<_>>();
    let renamed = MaterialAtlas::new(
        atlas.kind(),
        renamed_constituents,
        (0..atlas.constituents().len() as u64).collect(),
        atlas.contacts().to_vec(),
        0,
        0,
    )
    .map_err(|error| format!("{error:?}"))?;
    let renamed_complex = renamed
        .found(RankRepresentative::Least)
        .map_err(|error| format!("{error:?}"))?;

    println!(
        "  a declared BIJECTION on constituent names — every surface replaced by `q<index>` — \
         changes no incidence whatsoever."
    );
    println!(
        "    constituents {} → {}   contacts {} → {}   closed boundaries {} → {}",
        complex.sites().len(),
        renamed_complex.sites().len(),
        complex.bonds().len(),
        renamed_complex.bonds().len(),
        complex.compounds().len(),
        renamed_complex.compounds().len()
    );
    let structure_held = complex.sites().len() == renamed_complex.sites().len()
        && complex.bonds().len() == renamed_complex.bonds().len()
        && complex.compounds().len() == renamed_complex.compounds().len();
    println!(
        "    the structure {}",
        if structure_held {
            "HELD — ∂, o and ⪯ came from the material"
        } else {
            "MOVED — the intake is reading names as structure, which is a defect"
        }
    );

    let before = complex
        .hand_up(PhaseChart::WindingAdjacent)
        .map_err(|error| format!("{error:?}"))?;
    let after = renamed_complex
        .hand_up(PhaseChart::WindingAdjacent)
        .map_err(|error| format!("{error:?}"))?;
    let moved = before
        .iter()
        .zip(after.iter())
        .filter(|(left, right)| left.holonomy != right.holonomy)
        .count();
    let flat_before = before.iter().filter(|e| e.terrain_is_flat()).count();
    let flat_after = after.iter().filter(|e| e.terrain_is_flat()).count();
    println!(
        "    the TRANSPORT moved at {moved} of {} closed boundaries; flat {flat_before} → \
         {flat_after}",
        before.len()
    );
    println!(
        "    {}",
        if moved > 0 {
            "so holonomy is still read off the constituent's OCTETS. `incidence_production`'s \
             `contact_winding`/`sheet_of` take popcounts of the surface bytes, which is §III's \
             lawful chart — but it means the transport does not yet consult ContactSpecies, and \
             `2+2` against `2*2` is separated by the operator's SPELLING and not by ∂."
        } else {
            "the transport did not move under a renaming, so it is not reading the octets"
        }
    );
    println!(
        "    THE ONE CHANGE THIS WORK WOULD ASK OF `incidence_production.rs`: a `species` field on \
         `Bond`, carried into `PhaseChart::contact_transport`, so the turn a contact carries comes \
         from the relation's kind rather than from the name's bytes. It was not made: that owner \
         belongs to another agent this wave."
    );
    Ok(())
}

// ---------------------------------------------------------------------------------------------

fn workspace_root() -> Result<PathBuf, String> {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    manifest
        .parent()
        .and_then(Path::parent)
        .map(Path::to_path_buf)
        .ok_or_else(|| "the workspace root is not above soma/life".to_owned())
}

fn collect(root: &Path, extension: &str, found: &mut Vec<PathBuf>) -> Result<(), String> {
    let entries = match std::fs::read_dir(root) {
        Ok(entries) => entries,
        Err(error) => return Err(format!("read {}: {error}", root.display())),
    };
    for entry in entries {
        let entry = entry.map_err(|error| format!("read {}: {error}", root.display()))?;
        let path = entry.path();
        if path.is_dir() {
            collect(&path, extension, found)?;
        } else if path.extension().and_then(|value| value.to_str()) == Some(extension) {
            found.push(path);
        }
    }
    Ok(())
}

fn elide(text: &str, extent: usize) -> String {
    let flattened = text.split_whitespace().collect::<Vec<_>>().join(" ");
    if flattened.chars().count() <= extent {
        return flattened;
    }
    format!("{}…", flattened.chars().take(extent).collect::<String>())
}
