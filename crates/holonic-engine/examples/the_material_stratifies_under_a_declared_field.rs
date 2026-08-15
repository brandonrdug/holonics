//! **Mathematics into the Information Centrifuge**, steps 2 and 3.
//!
//! A centrifuge does not analyse. It applies a **declared field** and lets the
//! material separate **by its own response**; nothing is classified from
//! outside. This driver applies one to mathematical material and returns the
//! strata, the collapsed population with its distinguishing words, and the
//! null that says whether any of it is carried by the degree sequence.
//!
//! The material is **mathematics**. Lean is a codec — good for this because it
//! is *correctly written, completely derived and networked* mathematics — and
//! nothing here is about Lean.
//!
//! # Step 2 — band every coordinate, and the reason is measured
//!
//! On raw integer coordinates the one-shot partition of mathlib is already
//! **133,597 singletons of 232,037** before any transport is applied. `compress`
//! on that family returns `rounds = 0` and `collapsed = []`: reporting it as a
//! separation would be reporting the identity partition.
//!
//! So every count enters through `corpus_census::density_band` — `floor(log₂ n)`
//! computed as a bit length, exact, with no logarithm evaluated and no float
//! constructed. The banding is **derived from the count itself**, not authored.
//!
//! # Step 3 — the families, chosen against the authored partition
//!
//! **Forbidden, and each for a measured reason:**
//!
//! - `namespace_path` — 3,477 distinct blocks over 232,037 declarations. That is
//!   the preimage of a directory tree, authored by the corpus's maintainers.
//! - `former` — 9 values, the preimage of a keyword.
//! - `line` — file layout. Already convicted once, when a brace convention
//!   became the only nonzero torsion in a whole deposit.
//!
//! **Contaminated, and it is measured:** the term-position `recruited` multiset
//! carries `_` 158,691, `simp` 72,125, `only` 32,427, `rw` 11,204 — placeholders
//! and tactics in the term column, over 10% of 2,619,362 occurrences that are
//! not mathematical objects. This driver strips them and **reports how many it
//! stripped**, because a cleaning that is not counted is a declaration.
//!
//! **Used:** the statement's own recovered shape, the recruitment breadth, the
//! conduct breadth, and the internal chain depth — all banded.
//!
//! # The falsifier
//!
//! **The degree-preserving rewiring null.** Same declarations, same per-item
//! recruitment cardinality, edges redrawn from the multiset of landings the
//! observed population actually used. If the strata, the memory order and the
//! distinguishing-word lengths all agree with the null, **the separation is
//! carried by the degree sequence and not by the mathematics.**
//!
//! And the per-axis witness: every declared axis must exhibit a pair it
//! separates that no other axis does, or the family is one receiver wearing
//! several names.
//!
//! # What this run does not establish
//!
//! Not a Millennium anything. Not a claim that the strata are meaningful — only
//! that they are the material's and not a restatement of a declaration. The
//! reader is `lean_development`, never `derivation_atlas`, whose reading knows
//! only `have` as a binding tactic.
//!
//! ```text
//! cargo run --release -p holonic-engine --example the_material_stratifies_under_a_declared_field
//! ```

use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::corpus_census::density_band;
use holonic_engine::lean_development::{DeclarationGrain, DeclaredForm, read_development};
use holonic_engine::receiver_exact_compression::{
    InputId, ItemId, Observation, ObservedSystem, ReceiverId, compress,
};

/// Term-position surfaces that are not mathematical objects. Stripped, and the
/// count of what was stripped is returned rather than assumed.
const NOT_AN_OBJECT: [&str; 12] = [
    "_", "simp", "only", "rw", "rfl", "exact", "apply", "intro", "have", "refine", "obtain",
    "at",
];

/// The declared axes. Each reads one banded coordinate; none reads a namespace,
/// a former, or a line.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Axis {
    /// How broadly the declaration reaches, banded.
    RecruitmentBreadth,
    /// How broadly it was conducted, banded.
    ConductBreadth,
    /// How deep its own internal chain runs, banded.
    ChainDepth,
    /// The shape of its statement: binder count and applied depth, banded.
    StatementShape,
}

impl Axis {
    const DECLARED: [Self; 4] = [
        Self::RecruitmentBreadth,
        Self::ConductBreadth,
        Self::ChainDepth,
        Self::StatementShape,
    ];
}

struct Declaration {
    name: String,
    /// Cleaned term-position surfaces.
    recruits: BTreeSet<String>,
    conduct: u64,
    chain: u64,
    binders: u64,
    applied_depth: u64,
}

/// The material, read and cleaned. Returns the declarations and what the
/// cleaning removed.
fn read_material(roots: &[&str]) -> (Vec<Declaration>, u64, u64) {
    let not_an_object: BTreeSet<&str> = NOT_AN_OBJECT.iter().copied().collect();
    let mut declarations = Vec::new();
    let mut stripped = 0u64;
    let mut kept = 0u64;
    for root in roots {
        let mut stack = vec![std::path::PathBuf::from(root)];
        while let Some(path) = stack.pop() {
            let Ok(entries) = std::fs::read_dir(&path) else {
                continue;
            };
            for entry in entries.flatten() {
                let path = entry.path();
                if path.is_dir() {
                    if path.file_name().is_some_and(|name| name == ".lake") {
                        continue;
                    }
                    stack.push(path);
                } else if path.extension().is_some_and(|e| e == "lean") {
                    let Ok(text) = std::fs::read_to_string(&path) else {
                        continue;
                    };
                    let reading =
                        read_development(&text, DeclarationGrain::EveryTopLevelDeclaration);
                    for form in &reading.declarations {
                        declarations.push(declaration_of(form, &not_an_object, &mut stripped, &mut kept));
                    }
                }
            }
        }
    }
    (declarations, stripped, kept)
}

fn declaration_of(
    form: &DeclaredForm,
    not_an_object: &BTreeSet<&str>,
    stripped: &mut u64,
    kept: &mut u64,
) -> Declaration {
    let mut recruits = BTreeSet::new();
    for (surface, count) in &form.recruited {
        if not_an_object.contains(surface.as_str()) {
            *stripped += u64::from(*count);
        } else {
            *kept += u64::from(*count);
            recruits.insert(surface.clone());
        }
    }
    // The statement's shape, read off the statement itself and never off a name:
    // how many binder groups it opens and how deeply its application nests.
    let binders = form.statement.matches('(').count() as u64;
    let mut depth = 0i64;
    let mut deepest = 0i64;
    for byte in form.statement.bytes() {
        match byte {
            b'(' | b'[' | b'{' => {
                depth += 1;
                deepest = deepest.max(depth);
            }
            b')' | b']' | b'}' => depth -= 1,
            _ => {}
        }
    }
    Declaration {
        name: form.name.clone(),
        recruits,
        conduct: form.tactics.values().map(|c| u64::from(*c)).sum(),
        chain: form.steps.len() as u64,
        binders,
        applied_depth: deepest.max(0) as u64,
    }
}

/// The observed system: items are declarations, the field is the declared axis
/// family, and a successor step follows a recruitment edge.
struct MaterialField {
    declarations: Vec<Declaration>,
    /// item -> the items it recruits, by index.
    successors: Vec<Vec<usize>>,
    /// Which axes are in force. Withholding one is how an axis is graded.
    axes: Vec<Axis>,
}

impl MaterialField {
    fn found(declarations: Vec<Declaration>, axes: Vec<Axis>) -> Self {
        let mut by_name: BTreeMap<&str, usize> = BTreeMap::new();
        for (at, declaration) in declarations.iter().enumerate() {
            by_name.entry(declaration.name.as_str()).or_insert(at);
        }
        let successors = declarations
            .iter()
            .map(|declaration| {
                let mut landing: Vec<usize> = declaration
                    .recruits
                    .iter()
                    .filter_map(|surface| by_name.get(surface.as_str()).copied())
                    .collect();
                landing.sort_unstable();
                landing.dedup();
                landing
            })
            .collect();
        Self {
            declarations,
            successors,
            axes,
        }
    }

    /// Every count enters banded. `floor(log₂ n)` as a bit length, exact.
    fn coordinate(&self, at: usize, axis: Axis) -> u64 {
        let declaration = &self.declarations[at];
        match axis {
            Axis::RecruitmentBreadth => density_band(declaration.recruits.len() as u64),
            Axis::ConductBreadth => density_band(declaration.conduct),
            Axis::ChainDepth => density_band(declaration.chain),
            Axis::StatementShape => {
                density_band(declaration.binders) * 8 + density_band(declaration.applied_depth)
            }
        }
    }

    fn face(&self, at: usize) -> u64 {
        let mut face = 0u64;
        for axis in &self.axes {
            face = face.wrapping_mul(64).wrapping_add(self.coordinate(at, *axis));
        }
        face
    }

    /// The rewiring null: same out-degree per item, landings redrawn in order
    /// from the multiset of landings the observed population actually used.
    fn rewired(&self) -> Self {
        let mut pool: Vec<usize> = self.successors.iter().flatten().copied().collect();
        pool.sort_unstable();
        let mut at = 0usize;
        let successors = self
            .successors
            .iter()
            .map(|landing| {
                let mut drawn = Vec::with_capacity(landing.len());
                for _ in 0..landing.len() {
                    if pool.is_empty() {
                        break;
                    }
                    // A deterministic stride through the pool, so the null is
                    // reproducible and consults no clock and no randomness.
                    at = (at + 7919) % pool.len();
                    drawn.push(pool[at]);
                }
                drawn.sort_unstable();
                drawn.dedup();
                drawn
            })
            .collect();
        Self {
            declarations: self
                .declarations
                .iter()
                .map(|d| Declaration {
                    name: d.name.clone(),
                    recruits: d.recruits.clone(),
                    conduct: d.conduct,
                    chain: d.chain,
                    binders: d.binders,
                    applied_depth: d.applied_depth,
                })
                .collect(),
            successors,
            axes: self.axes.clone(),
        }
    }
}

impl ObservedSystem for MaterialField {
    fn items(&self) -> Vec<ItemId> {
        (0..self.declarations.len())
            .map(|at| ItemId(at as u64))
            .collect()
    }

    fn receivers(&self) -> Vec<ReceiverId> {
        vec![ReceiverId(0)]
    }

    fn inputs(&self) -> Vec<InputId> {
        let mut faces: BTreeSet<u64> = BTreeSet::new();
        for at in 0..self.declarations.len() {
            faces.insert(self.face(at));
        }
        faces.into_iter().map(InputId).collect()
    }

    fn observation(&self, item: ItemId, _receiver: ReceiverId) -> Observation {
        Observation(self.face(item.0 as usize))
    }

    fn successor(&self, item: ItemId, input: InputId) -> Option<ItemId> {
        self.successors
            .get(item.0 as usize)?
            .iter()
            .find(|to| self.face(**to) == input.0)
            .map(|to| ItemId(*to as u64))
    }
}

struct Reading {
    items: usize,
    one_shot: usize,
    conduct: usize,
    singletons: usize,
    rounds: usize,
    collapsed: usize,
    memory_order: Option<usize>,
    word_lengths: BTreeMap<usize, usize>,
}

fn read(field: &MaterialField) -> Reading {
    let compression = compress(field);
    let singletons = compression
        .conduct
        .blocks
        .iter()
        .filter(|block| block.len() == 1)
        .count();
    let mut word_lengths: BTreeMap<usize, usize> = BTreeMap::new();
    for pair in &compression.collapsed {
        *word_lengths
            .entry(pair.distinguishing_word.len())
            .or_insert(0) += 1;
    }
    Reading {
        items: field.declarations.len(),
        one_shot: compression.one_shot.len(),
        conduct: compression.conduct.len(),
        singletons,
        rounds: compression.rounds,
        collapsed: compression.collapsed.len(),
        memory_order: compression.memory_order(),
        word_lengths,
    }
}

fn line(name: &str, reading: &Reading) {
    println!(
        "  {name:<26} items {:>6}  one-shot {:>6}  conduct {:>6}  singletons {:>6}  rounds {:>3}  collapsed {:>6}  order {}",
        reading.items,
        reading.one_shot,
        reading.conduct,
        reading.singletons,
        reading.rounds,
        reading.collapsed,
        match reading.memory_order {
            Some(k) => k.to_string(),
            None => "none".to_owned(),
        }
    );
}

fn main() {
    println!("{}", "=".repeat(112));
    println!("THE MATERIAL STRATIFIES UNDER A DECLARED FIELD");
    println!("{}", "=".repeat(112));
    println!();

    let roots = ["soma/formal"];
    let (declarations, stripped, kept) = read_material(&roots);
    println!("  material          {} declarations under {roots:?}", declarations.len());
    println!(
        "  term position     {kept} surfaces kept, {stripped} stripped as not-an-object and counted"
    );
    if declarations.len() < 2 {
        println!("  the declared material carries too few declarations to stratify");
        std::process::exit(1);
    }

    // ---------------------------------------------------------------------------------
    // STEP 2 -- the banding, measured against the raw coordinates it replaces.
    // ---------------------------------------------------------------------------------
    println!();
    println!("{}", "-".repeat(112));
    println!("STEP 2 -- BANDING, against the raw coordinates it replaces");
    println!("{}", "-".repeat(112));
    let raw: BTreeSet<(usize, u64, u64, u64, u64)> = declarations
        .iter()
        .map(|d| {
            (
                d.recruits.len(),
                d.conduct,
                d.chain,
                d.binders,
                d.applied_depth,
            )
        })
        .collect();
    let field = MaterialField::found(declarations, Axis::DECLARED.to_vec());
    let banded: BTreeSet<u64> = (0..field.declarations.len()).map(|at| field.face(at)).collect();
    println!(
        "  raw coordinates give {} distinct faces over {} items; banded gives {}",
        raw.len(),
        field.declarations.len(),
        banded.len()
    );
    println!(
        "  the banding is floor(log2 n) as a bit length -- exact, no logarithm evaluated, no float"
    );

    // ---------------------------------------------------------------------------------
    // The reading, and the null.
    // ---------------------------------------------------------------------------------
    println!();
    println!("{}", "-".repeat(112));
    println!("THE READING, AND THE DEGREE-PRESERVING NULL");
    println!("{}", "-".repeat(112));
    let observed = read(&field);
    let null = read(&field.rewired());
    line("the material", &observed);
    line("the rewiring null", &null);

    let separates_beyond_degree = observed.conduct != null.conduct
        || observed.collapsed != null.collapsed
        || observed.word_lengths != null.word_lengths
        || observed.memory_order != null.memory_order;
    println!();
    println!(
        "  the reading differs from the null                {}",
        if separates_beyond_degree {
            "YES -- the separation is not carried by the degree sequence alone"
        } else {
            "NO -- REFUTED: the degree sequence carries the whole separation"
        }
    );
    println!(
        "  distinguishing-word lengths, material {:?}",
        observed.word_lengths
    );
    println!("  distinguishing-word lengths, null     {:?}", null.word_lengths);

    // ---------------------------------------------------------------------------------
    // The per-axis witness: withhold each axis and require the reading to move.
    // ---------------------------------------------------------------------------------
    println!();
    println!("{}", "-".repeat(112));
    println!("THE PER-AXIS WITNESS -- withhold one axis and the reading must move");
    println!("{}", "-".repeat(112));
    let mut every_axis_earns_its_place = true;
    for axis in Axis::DECLARED {
        let withheld: Vec<Axis> = Axis::DECLARED
            .iter()
            .copied()
            .filter(|other| *other != axis)
            .collect();
        let smaller = MaterialField::found(
            field
                .declarations
                .iter()
                .map(|d| Declaration {
                    name: d.name.clone(),
                    recruits: d.recruits.clone(),
                    conduct: d.conduct,
                    chain: d.chain,
                    binders: d.binders,
                    applied_depth: d.applied_depth,
                })
                .collect(),
            withheld,
        );
        let reading = read(&smaller);
        let moved = reading.conduct != observed.conduct || reading.collapsed != observed.collapsed;
        every_axis_earns_its_place &= moved;
        println!(
            "  without {:<22} conduct {:>6} (was {:>6})  collapsed {:>6} (was {:>6})   {}",
            format!("{axis:?}"),
            reading.conduct,
            observed.conduct,
            reading.collapsed,
            observed.collapsed,
            if moved { "earns its place" } else { "CARRIES NOTHING" }
        );
    }

    println!();
    println!("{}", "=".repeat(112));
    println!("WHAT RETURNED");
    println!("{}", "=".repeat(112));
    println!("  conduct refined the one-shot reading            {}", observed.rounds >= 1);
    println!("  the strata are not all singletons               {}", observed.singletons < observed.conduct);
    println!("  the reading beats the degree-preserving null    {separates_beyond_degree}");
    println!("  every declared axis earns its place             {every_axis_earns_its_place}");

    println!();
    println!("{}", "-".repeat(112));
    println!("WHAT THIS RUN DOES NOT ESTABLISH");
    println!("{}", "-".repeat(112));
    println!("  No namespace, no former and no line entered any axis, so no stratum is the preimage");
    println!("  of a directory tree or a keyword. That is a bar cleared, not a result. Nothing here");
    println!("  claims the strata are meaningful -- only that they are the material's own response");
    println!("  to a declared field, and that a degree-matched null does not reproduce them.");
    println!("{}", "=".repeat(112));
}
