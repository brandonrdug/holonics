//! The panel grows at the junctions it is blind to, and two founding orders do not commute.
//!
//! `receiver_exact_compression` calls `receivers()` once and never again: the partition refines and
//! the receiver population is **locked**. A locked panel returns exactly one decomposition, which
//! cannot hold competing readings of the same material as live alternatives.
//!
//! A `CollapsedPair` with `witness: None` is the junction — conduct separates it and no declared
//! receiver saw. This driver founds a receiver there, re-refines, and repeats to exhaustion; then it
//! runs the founding under two junction orders and returns the gyration.
//!
//! **The material is the development itself.** Items are the 66 top-level declarations of
//! `soma/formal`; an input is *"take the k-th declared name this declaration recruits"*, so conduct
//! is the recruitment chain the intake recovered; the declared panel is three faces a reader has
//! before opening anything — the former that founded it, its namespace depth, and whether it carries
//! a statement. Nothing here is authored about *which* declarations differ; the panel is coarse on
//! purpose, and what it cannot see is what gets founded.
//!
//! ## Controls
//!
//! 1. **The junction is real on this material.** Unwitnessed pairs must exist before founding, or
//!    every control below is vacuous.
//! 2. **Founding closes them.** Exhaustion, or the remainder refused by name.
//! 3. **The Nerode congruence does not move.** Founding sharpens what is *seen*; conduct is an
//!    invariant of the material and must be bit-identical before and after.
//! 4. **The one-shot reading strictly refines.** The panel grew, so it must see more.
//! 5. **The null.** Under a panel that already witnesses everything — one receiver per item — the
//!    founding must found **nothing**. A law that founds on any input is unfalsifiable.
//! 6. **The orbit.** Two founding orders are run. If they coincide the gauge measured nothing and
//!    the driver says so rather than reporting agreement as evidence — `CLAUDE.md` §8. If they
//!    diverge, `gyr[a,b]` is returned: same endpoint, different path.
//! 7. **The bound.** Foundings ≤ `|items| − 1`, structurally.
//!
//! Run: `the_receiver_is_founded_at_the_junction [development-root]`

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use holonic_engine::founded_receiver::{found_to_exhaustion, gyration, FoundedPanel};
use holonic_engine::lean_development::{
    join, read_development, ConductGrain, DeclarationGrain, DevelopmentReading,
};
use holonic_engine::receiver_exact_compression::{
    compress, InputId, ItemId, ObservedSystem, Observation, ReceiverId,
};

/// The development as a system under observation.
///
/// - **items** — one per top-level declaration, in canonical order.
/// - **inputs** — `take the k-th declared name this declaration recruits`, `k` up to the widest
///   declared recruitment in the development. The alphabet is the material's, not a choice.
/// - **receivers** — three coarse faces: the former, the namespace depth, whether a statement is
///   carried. A reader has these before opening anything.
struct Development {
    names: Vec<String>,
    ordinal: BTreeMap<String, usize>,
    /// Per declaration, the declared names it recruits, in canonical order.
    recruits: Vec<Vec<usize>>,
    formers: Vec<u64>,
    depths: Vec<u64>,
    stated: Vec<u64>,
    width: usize,
}

impl Development {
    fn read(reading: &DevelopmentReading) -> Self {
        let mut names: Vec<String> = reading
            .declarations
            .iter()
            .map(|form| form.name.clone())
            .collect();
        names.sort();
        names.dedup();
        let ordinal: BTreeMap<String, usize> = names
            .iter()
            .enumerate()
            .map(|(index, name)| (name.clone(), index))
            .collect();

        let mut recruits = vec![Vec::new(); names.len()];
        let mut formers = vec![0u64; names.len()];
        let mut depths = vec![0u64; names.len()];
        let mut stated = vec![0u64; names.len()];
        let declared = reading.declared_names();

        for form in &reading.declarations {
            let Some(index) = ordinal.get(&form.name).copied() else {
                continue;
            };
            let mut reached: Vec<usize> = form
                .recruited
                .keys()
                .filter(|symbol| declared.contains(symbol.as_str()))
                .filter_map(|symbol| ordinal.get(symbol).copied())
                .filter(|other| *other != index)
                .collect();
            reached.sort_unstable();
            reached.dedup();
            recruits[index] = reached;
            // The former, as an exact token. Never ordered, never compared by magnitude.
            formers[index] = form.former.bytes().fold(0u64, |acc, byte| {
                acc.wrapping_mul(131).wrapping_add(u64::from(byte))
            });
            depths[index] = form.namespace_path.len() as u64;
            stated[index] = u64::from(!form.statement.is_empty());
        }

        let width = recruits.iter().map(Vec::len).max().unwrap_or(0);
        Self {
            names,
            ordinal,
            recruits,
            formers,
            depths,
            stated,
            width,
        }
    }

    fn name_of(&self, item: ItemId) -> &str {
        &self.names[item.0 as usize]
    }
}

impl ObservedSystem for Development {
    fn items(&self) -> Vec<ItemId> {
        (0..self.names.len() as u64).map(ItemId).collect()
    }
    fn receivers(&self) -> Vec<ReceiverId> {
        vec![ReceiverId(0), ReceiverId(1), ReceiverId(2)]
    }
    fn inputs(&self) -> Vec<InputId> {
        (0..self.width as u64).map(InputId).collect()
    }
    fn observation(&self, item: ItemId, receiver: ReceiverId) -> Observation {
        let index = item.0 as usize;
        Observation(match receiver.0 {
            0 => self.formers[index],
            1 => self.depths[index],
            _ => self.stated[index],
        })
    }
    fn successor(&self, item: ItemId, input: InputId) -> Option<ItemId> {
        self.recruits[item.0 as usize]
            .get(input.0 as usize)
            .map(|next| ItemId(*next as u64))
    }
}

/// The null: a panel with one receiver per item sees everything and must found nothing.
struct SeeingPanel<'a>(&'a Development);

impl ObservedSystem for SeeingPanel<'_> {
    fn items(&self) -> Vec<ItemId> {
        self.0.items()
    }
    fn receivers(&self) -> Vec<ReceiverId> {
        vec![ReceiverId(0)]
    }
    fn inputs(&self) -> Vec<InputId> {
        self.0.inputs()
    }
    fn observation(&self, item: ItemId, _receiver: ReceiverId) -> Observation {
        Observation(item.0)
    }
    fn successor(&self, item: ItemId, input: InputId) -> Option<ItemId> {
        self.0.successor(item, input)
    }
}

fn section(title: &str) {
    println!("\n{}", "=".repeat(96));
    println!("{title}");
    println!("{}", "=".repeat(96));
}

fn lean_paths(root: &Path) -> Vec<PathBuf> {
    let mut found = Vec::new();
    let Ok(entries) = std::fs::read_dir(root) else {
        return found;
    };
    let mut here: Vec<PathBuf> = entries.flatten().map(|entry| entry.path()).collect();
    here.sort();
    for path in here {
        if path.is_dir() {
            found.extend(lean_paths(&path));
        } else if path.extension().is_some_and(|carried| carried == "lean") {
            found.push(path);
        }
    }
    found
}

fn main() {
    let root = PathBuf::from(
        std::env::args()
            .nth(1)
            .unwrap_or_else(|| "soma/formal".to_owned()),
    );
    let paths = lean_paths(&root);
    if paths.is_empty() {
        eprintln!("no .lean under {}", root.display());
        std::process::exit(2);
    }
    let reading = join(
        paths
            .iter()
            .filter_map(|path| std::fs::read_to_string(path).ok())
            .map(|text| read_development(&text, DeclarationGrain::EveryTopLevelDeclaration))
            .collect(),
    );
    let system = Development::read(&reading);

    println!("truth_status=established-bounded");
    println!("evidence=computational-witness");
    println!("law=a junction is where the declared panel is exhausted, and exhaustion FOUNDS");
    println!("material={}", root.display());

    let mut controls: Vec<(bool, String, String)> = Vec::new();

    // ------------------------------------------------------------------ the material and the panel
    section("THE SYSTEM UNDER OBSERVATION");
    println!("\n  items      {} declarations", system.names.len());
    println!("  inputs     {} (widest declared recruitment)", system.width);
    println!("  receivers  3 declared -- former, namespace depth, carries-a-statement");
    println!(
        "  conduct    the recruitment chain: {} declarations recruit at least one other",
        system.recruits.iter().filter(|r| !r.is_empty()).count()
    );
    let _ = reading.derivations(ConductGrain::TermsOnly);

    let before = compress(&system);
    let unwitnessed: Vec<_> = before
        .collapsed
        .iter()
        .filter(|pair| pair.witness.is_none())
        .collect();
    println!(
        "\n  one-shot blocks {}   conduct blocks {}   collapsed {}   UNWITNESSED {}",
        before.one_shot.len(),
        before.conduct.len(),
        before.collapsed.len(),
        unwitnessed.len()
    );

    section("CONTROL 1 -- THE JUNCTION IS REAL ON THIS MATERIAL");
    println!("\n  A junction is a pair conduct separates that NO declared receiver witnesses.");
    println!("  If none exists here, every control below is vacuous and this one says so.\n");
    for pair in unwitnessed.iter().take(10) {
        println!(
            "    {:<38} | {:<38} after {} input(s)",
            system.name_of(pair.left),
            system.name_of(pair.right),
            pair.distinguishing_word.len()
        );
    }
    if unwitnessed.len() > 10 {
        println!("    … and {} more", unwitnessed.len() - 10);
    }
    controls.push((
        !unwitnessed.is_empty(),
        "control 1 -- the declared panel is blind somewhere conduct is not".to_owned(),
        format!("{} unwitnessed pairs before founding", unwitnessed.len()),
    ));

    // ------------------------------------------------------------------ the founding
    section("CONTROLS 2, 3, 4, 7 -- THE PANEL GROWS AT ITS OWN BLINDNESS");
    let panel = found_to_exhaustion(&system, &[]);
    report(&system, &panel);

    controls.push((
        panel.exhausted() || !panel.refused.is_empty(),
        "control 2 -- founding reaches exhaustion, or refuses by name".to_owned(),
        format!(
            "{} founded, {} unwitnessed remain, {} refusals",
            panel.rounds,
            panel.unwitnessed_remaining,
            panel.refused.len()
        ),
    ));
    controls.push((
        before.conduct == panel.conduct,
        "control 3 -- founding does not move the Nerode congruence".to_owned(),
        format!(
            "conduct blocks {} before, {} after",
            before.conduct.len(),
            panel.conduct.len()
        ),
    ));
    controls.push((
        panel.rounds == 0 || panel.one_shot_after.len() > panel.one_shot_before.len(),
        "control 4 -- a grown panel reads strictly finer".to_owned(),
        format!(
            "one-shot {} -> {}",
            panel.one_shot_before.len(),
            panel.one_shot_after.len()
        ),
    ));
    controls.push((
        panel.rounds <= panel.bound,
        "control 7 -- foundings are bounded by |items| - 1".to_owned(),
        format!("{} foundings against bound {}", panel.rounds, panel.bound),
    ));

    // ------------------------------------------------------------------ the null
    section("CONTROL 5 (NULL) -- A PANEL THAT SEES EVERYTHING FOUNDS NOTHING");
    let seeing = SeeingPanel(&system);
    let seeing_reading = compress(&seeing);
    let seeing_panel = found_to_exhaustion(&seeing, &[]);
    println!(
        "\n  one receiver per item: {} one-shot blocks over {} items, {} unwitnessed",
        seeing_reading.one_shot.len(),
        system.names.len(),
        seeing_reading
            .collapsed
            .iter()
            .filter(|pair| pair.witness.is_none())
            .count()
    );
    println!("  foundings: {}", seeing_panel.rounds);
    println!("\n  A law that founds on ANY input cannot fail. This is the input on which it must not.");
    controls.push((
        seeing_panel.rounds == 0,
        "control 5 (NULL) -- nothing is founded where nothing is blind".to_owned(),
        format!("{} foundings on a fully witnessing panel", seeing_panel.rounds),
    ));

    // ------------------------------------------------------------------ the gyration
    section("CONTROL 6 -- THE GYRATION: TWO FOUNDING ORDERS");
    let gyr = gyration(&system);
    println!("\n  Partition joins commute, so refinement order cannot matter. FOUNDING order can:");
    println!("  a junction exists only relative to the panel standing when it is reached.\n");
    println!("  left  order  {} foundings", gyr.left_order.len());
    println!("  right order  {} foundings", gyr.right_order.len());
    println!("  conduct agrees      {}", gyr.conduct_agrees);
    println!("  partitions agree    {}", gyr.partitions_agree);
    println!("  founded agree       {}", gyr.founded_agree);

    if gyr.orbit_is_trivial() {
        println!("\n  ORBIT TRIVIAL -- the two orders are one order. `CLAUDE.md` §8: a gauge whose");
        println!("  group acts trivially on the declared material is not a gauge, so the agreement");
        println!("  below is NOT evidence and is reported rather than claimed.");
    } else {
        println!("\n  ORBIT NON-TRIVIAL. gyr[a,b], exhibited:");
        if let Some((step, left, right)) = &gyr.divergence {
            println!(
                "    first divergence at founding {step}:  {}  against  {}",
                system.name_of(left.0),
                system.name_of(right.0)
            );
            println!(
                "                                  |{}  against  |{}",
                system.name_of(left.1),
                system.name_of(right.1)
            );
        }
        for (left, right) in &gyr.only_left {
            println!(
                "    only the left order founded   {} | {}",
                system.name_of(*left),
                system.name_of(*right)
            );
        }
        for (left, right) in &gyr.only_right {
            println!(
                "    only the right order founded  {} | {}",
                system.name_of(*left),
                system.name_of(*right)
            );
        }
        if gyr.is_holonomy() {
            println!("\n  AND IT IS A HOLONOMY: both orders reach the SAME partition by DIFFERENT");
            println!("  paths. Equal endpoints do not identify ordered paths -- the project's own law,");
            println!("  and here the transport under it is real: the founding order is the path and");
            println!("  the panel is what is carried along it.");
        }
    }
    controls.push((
        gyr.conduct_agrees,
        format!(
            "control 6 -- the gyration is returned, and the orbit is {}",
            if gyr.orbit_is_trivial() { "TRIVIAL (reported, not claimed)" } else { "non-trivial" }
        ),
        format!(
            "left {} / right {} foundings, holonomy {}",
            gyr.left_order.len(),
            gyr.right_order.len(),
            gyr.is_holonomy()
        ),
    ));

    // ------------------------------------------------------------------
    section("THE CONTROLS");
    let mut failed = 0usize;
    for (held, name, detail) in &controls {
        println!("  [{}] {name}", if *held { "HELD" } else { "FAIL" });
        println!("         {detail}");
        if !held {
            failed += 1;
        }
    }
    println!("\n  {} of {} controls held", controls.len() - failed, controls.len());
    if failed > 0 {
        std::process::exit(1);
    }
}

fn report(system: &Development, panel: &FoundedPanel) {
    println!("\n  declared panel   {} receivers", panel.declared.len());
    println!("  founded          {} receivers", panel.rounds);
    println!("  bound            {}", panel.bound);
    println!(
        "  one-shot         {} -> {} blocks",
        panel.one_shot_before.len(),
        panel.one_shot_after.len()
    );
    println!("  conduct          {} blocks (invariant)", panel.conduct.len());
    println!("  unwitnessed      {}", panel.unwitnessed_remaining);

    if !panel.founded.is_empty() {
        println!("\n  every founded receiver, with the junction that provoked it");
        println!("  ---------------------------------------------------------");
        for found in &panel.founded {
            println!(
                "    #{:<3} at  {:<34} | {:<34}  after {} input(s), +{} blocks",
                found.id.0,
                system.name_of(found.junction.0),
                system.name_of(found.junction.1),
                found.after.len(),
                found.blocks_gained
            );
        }
    }
    if !panel.refused.is_empty() {
        println!("\n  refusals, by name");
        println!("  -----------------");
        for refusal in &panel.refused {
            println!("    {refusal:?}");
        }
    }
}
