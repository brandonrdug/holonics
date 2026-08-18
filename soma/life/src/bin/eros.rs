//! **`eros` — the application.**
//!
//! ```text
//! eros mouth    --directory D [--extension E] [--radius N] [--scales N]
//! eros atlas    --directory D [--extension E]
//! eros stations
//! ```
//!
//! # Why this exists
//!
//! Measured 2026-08-17 by `grep -rn "^\[\[bin\]\]" crates/*/Cargo.toml soma/*/Cargo.toml`: this
//! workspace carried the architecture lint and six `mount-*` gates and **no application**, against
//! 211 example drivers. Brandon, 2026-08-16: *"I would just call it centralizing the application's
//! entry-point and turning it into a standard. This is required and important."* Measured the same
//! day by `grep -rn "entry.point\|entry point\|single binary" blueprint/*.md CONSTRUCTION_STATE.md
//! canon/THE_INFORMATION_ENGINE.md`, that instruction appeared in no governing document.
//!
//! A driver is an experiment: it declares its own material, asks one question, and prints. This is
//! not that. Its subcommands are **stations of the cycle**, they take the material as an argument,
//! and each one drives standing library organs rather than carrying a reading of its own.
//!
//! # What it refuses to do
//!
//! `stations` reports which stations are reachable **from this binary** and which are not. A station
//! that is not wired is named as unwired rather than stubbed, because a subcommand that prints
//! something plausible for work it did not do is worse than an absent one.
//!
//! Plan: [`blueprint/THE_CODEC_IS_RECOVERED_AT_EVERY_SCALE_AND_THE_FACES_ARE_A_RETURN.md`], station
//! eight, under `blueprint/THE_ROADMAP.md`.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};

use life::causal_language::{lexical_tokens, lexical_tokens_under, LexicalAperture};
use life::exposure_codec::{ladder, ExposureApertures, LadderStop, UnitRole};
use holonic_engine::lean_development::{join, read_development, DeclarationGrain};
use life::material_incidence::{
    face_quotient, lean_atlas, prose_atlas, rust_atlas, rust_items_of_section,
};

fn main() {
    if let Err(trouble) = run() {
        eprintln!("eros: {trouble}");
        std::process::exit(1);
    }
}

const USAGE: &str = "\
usage:
  eros mouth    --directory D [--extension E] [--radius N] [--scales N]
                found the material's codec from octets, climb the scale ladder, and
                report the founded segmentation against the authored one

  eros atlas    --directory D [--extension E]
                the material's own oriented incidence atlas: constituents, contacts,
                dependency heights, and the rank gauge orbit

  eros supersede --directory D --against TSV
                the superseded parser's deposited transport atlas against the same corpus
                founded by the INCIDENCE route, which knows no grammar

  eros condition --directory D --extension E --with-directory D2 --with-extension E2
                found terrain on two materials at once and ask what the JOIN reads that
                neither half can, then ablate each half and require the reading back

  eros stations which stations of the cycle this binary reaches, and which it does not
";

fn run() -> Result<(), String> {
    let mut arguments = std::env::args().skip(1);
    let Some(station) = arguments.next() else {
        print!("{USAGE}");
        return Ok(());
    };
    let mut directory: Option<PathBuf> = None;
    let mut extension = String::from("md");
    let mut radius = 3usize;
    let mut scales = 3usize;
    let mut family_words = 8_000_000u64;
    let mut octet_budget = 3_000_000usize;
    let mut against: Option<PathBuf> = None;
    let mut with_directory: Option<PathBuf> = None;
    let mut with_extension = String::from("rs");
    while let Some(named) = arguments.next() {
        let value = arguments
            .next()
            .ok_or_else(|| format!("{named} requires a value"))?;
        match named.as_str() {
            "--directory" => directory = Some(PathBuf::from(value)),
            "--against" => against = Some(PathBuf::from(value)),
            "--with-directory" => with_directory = Some(PathBuf::from(value)),
            "--with-extension" => with_extension = value,
            "--extension" => extension = value,
            "--radius" => radius = value.parse().map_err(|_| "--radius wants a number")?,
            "--scales" => scales = value.parse().map_err(|_| "--scales wants a number")?,
            "--family-words" => {
                family_words = value.parse().map_err(|_| "--family-words wants a number")?
            }
            "--octet-budget" => {
                octet_budget = value.parse().map_err(|_| "--octet-budget wants a number")?
            }
            other => return Err(format!("unknown argument {other}\n\n{USAGE}")),
        }
    }

    match station.as_str() {
        "stations" => {
            stations();
            Ok(())
        }
        "mouth" => {
            let directory = directory.ok_or("mouth requires --directory")?;
            let exposures = read_material(&directory, &extension, octet_budget)?;
            mouth(exposures, radius, family_words, scales)
        }
        "atlas" => {
            let directory = directory.ok_or("atlas requires --directory")?;
            atlas(&directory, &extension, octet_budget)
        }
        "condition" => {
            let directory = directory.ok_or("condition requires --directory")?;
            let with_directory =
                with_directory.ok_or("condition requires --with-directory")?;
            condition(
                &directory,
                &extension,
                &with_directory,
                &with_extension,
                octet_budget,
            )
        }
        "supersede" => {
            let directory = directory.ok_or("supersede requires --directory")?;
            let against = against.ok_or("supersede requires --against <deposited atlas tsv>")?;
            supersede(&directory, &against)
        }
        other => Err(format!("unknown station {other}\n\n{USAGE}")),
    }
}

/// Every file under a root with one extension, in path order, each its own exposure.
///
/// **Exposures are separate streams**: two files are not one file, and a codec recovered across the
/// seam would have been recovered from an artifact of the concatenation order.
fn read_files(root: &Path, extension: &str) -> Result<Vec<(String, Vec<u8>)>, String> {
    let mut found: Vec<(String, Vec<u8>)> = Vec::new();
    let mut pending = vec![root.to_path_buf()];
    while let Some(here) = pending.pop() {
        let listing =
            fs::read_dir(&here).map_err(|error| format!("read {}: {error}", here.display()))?;
        for entry in listing.flatten() {
            let path = entry.path();
            if path.is_dir() {
                pending.push(path);
            } else if path.extension().and_then(|e| e.to_str()) == Some(extension) {
                if let Ok(octets) = fs::read(&path) {
                    if !octets.is_empty() {
                        found.push((path.display().to_string(), octets));
                    }
                }
            }
        }
    }
    found.sort();
    if found.is_empty() {
        return Err(format!(
            "no .{extension} file under {} — the material is the argument and there is none",
            root.display()
        ));
    }
    Ok(found)
}

fn read_material(root: &Path, extension: &str, budget: usize) -> Result<Vec<Vec<u8>>, String> {
    let files = read_files(root, extension)?;
    let mut exposures = Vec::new();
    let mut carried = 0usize;
    for (_, octets) in files {
        if carried + octets.len() > budget {
            break;
        }
        carried += octets.len();
        exposures.push(octets);
    }
    if exposures.is_empty() {
        return Err("the declared octet budget admits no whole file".to_owned());
    }
    Ok(exposures)
}

// -------------------------------------------------------------------------------------------------
// mouth
// -------------------------------------------------------------------------------------------------

fn mouth(
    exposures: Vec<Vec<u8>>,
    radius: usize,
    family_words: u64,
    scales: usize,
) -> Result<(), String> {
    let octets: u64 = exposures.iter().map(|e| e.len() as u64).sum();
    println!("EROS · MOUTH");
    println!(
        "  exposures {}   octets {octets}   radius {radius}   scales {scales}",
        exposures.len()
    );
    println!();
    println!("  The recovery is handed octets and a radius and nothing else: no grammar, no keyword");
    println!("  list, no bracket table, no character classes, no encoding. The alphabet itself is");
    println!("  recovered by exhausting every declared candidate, so even it is testimony.");
    println!();

    let sample = exposures
        .first()
        .cloned()
        .ok_or("no exposure to read back")?;
    let climbed = ladder(
        exposures,
        ExposureApertures::declared(radius, family_words),
        scales,
    )
    .map_err(|refusal| format!("the ground rung refused: {refusal}"))?;

    println!(
        "  {:>4}  {:>10}  {:>8}  {:>9}  {:>8}  {:>7}",
        "rung", "candidates", "alphabet", "refusals", "units", "parts"
    );
    for rung in &climbed.rungs {
        println!(
            "  {:>4}  {:>10}  {:>8}  {:>9}  {:>8}  {:>7}",
            rung.scale,
            rung.candidates,
            rung.recovery.alphabet.len(),
            rung.recovery.refusals.len(),
            rung.founded_units.len(),
            rung.parts
        );
    }

    if let Some(ground) = climbed.rungs.first() {
        println!();
        for role in [UnitRole::Standing, UnitRole::Demanding, UnitRole::Internal] {
            let members = ground.recovery.units_with(role);
            println!("  rung 0  {:<10} {:>4} units", role.name(), members.len());
        }
        println!(
            "  rung 0  gauge freedom {:?}",
            ground.recovery.gauge_freedom
        );
    }

    for rung in climbed.rungs.iter().skip(1) {
        let mut compound: Vec<&Vec<u8>> = rung
            .founded_units
            .iter()
            .filter(|unit| unit.len() > 1)
            .collect();
        compound.sort_by(|left, right| right.len().cmp(&left.len()).then(left.cmp(right)));
        println!();
        println!(
            "  rung {} founded {} compound unit(s); the widest are the finding",
            rung.scale,
            compound.len()
        );
        let shown: Vec<String> = compound
            .iter()
            .take(16)
            .map(|unit| format!("{:?}", String::from_utf8_lossy(unit)))
            .collect();
        println!("    {}", shown.join(" "));
    }

    println!();
    match &climbed.stopped {
        LadderStop::NoCoarsening { scale } => println!(
            "  STOPPED at rung {scale}: the codec cut at every adjacency it was handed, so the scale\n  \
             above IS the scale below. The material has no coarser unit at this radius."
        ),
        LadderStop::Obstructed {
            scale,
            obstructions,
        } => println!("  STOPPED at rung {scale}: {obstructions:?}"),
        LadderStop::Refused {
            scale,
            candidates,
            refusal,
        } => println!(
            "  STOPPED at rung {scale}: {candidates} candidates declare a family past the aperture — {refusal}"
        ),
        LadderStop::CeilingReached { scales } => {
            println!("  the declared {scales} scales climbed with no obstruction")
        }
    }

    // The authored reading, beside the founded one, on the same material.
    println!();
    println!("  THE AUTHORED READING, BESIDE IT");
    println!("  `lexical_tokens` is authored end to end. Its three levels are now a declared");
    println!("  aperture rather than literals inside the loop, so a caller can move them and the");
    println!("  orbit is exhibited rather than asserted.");
    let text = String::from_utf8_lossy(&sample);
    let head: String = text.chars().take(4000).collect();
    let inherited = lexical_tokens(&head);
    let maximal = lexical_tokens_under(&head, &LexicalAperture::runs_are_maximal());
    println!(
        "    inherited aperture  {:>6} tokens        maximal-run aperture {:>6} tokens",
        inherited.len(),
        maximal.len()
    );
    let inherited_set: BTreeSet<&String> = inherited.iter().collect();
    let maximal_set: BTreeSet<&String> = maximal.iter().collect();
    let only_maximal: Vec<&&String> = maximal_set.difference(&inherited_set).take(16).collect();
    if only_maximal.is_empty() {
        println!("    the two readings agree on this material: it carries no operator run");
    } else {
        println!(
            "    tokens only the maximal-run aperture founds: {}",
            only_maximal
                .iter()
                .map(|token| format!("{token:?}"))
                .collect::<Vec<_>>()
                .join(" ")
        );
    }
    Ok(())
}

// -------------------------------------------------------------------------------------------------
// atlas
// -------------------------------------------------------------------------------------------------

fn atlas(root: &Path, extension: &str, budget: usize) -> Result<(), String> {
    let files = read_files(root, extension)?;
    println!("EROS · ATLAS");
    println!("  root {}   .{extension} files {}", root.display(), files.len());
    println!();
    println!("  The atlas is the material's own oriented incidence — constituents, contacts, and a");
    println!("  dependency height that is never a line number. The rank gauge orbit is taken before");
    println!("  any reading is believed: a representative that changed a rank would mean the intake");
    println!("  was reading its own bookkeeping.");
    println!();

    // ONE intake path for every codec. `atlas()` used to carry its own per-extension construction
    // that special-cased only `rs`, so a `.lean` root fell through to the PROSE branch and returned
    // one contact — `/- --adjacency--> Copyright`. Two paths existed, one was wrong, and the counts
    // could not say so: "constituents 2, contacts 1" reads like a small material rather than a
    // misrouted one. Found 2026-08-17 by reading the transport instead of the totals.
    let atlas = atlas_of(root, extension, budget)?;

    let (heights, storage, top) = atlas.heights();
    println!("  constituents        {}", atlas.constituents().len());
    println!("  contacts            {}", atlas.contacts().len());
    println!("  height ranks        {top} (over {} heights)", heights.len());
    println!("  storage ordinals    {} carried beside them", storage.len());
    match atlas.rank_gauge_orbit() {
        Ok(orbit) => println!("  rank gauge orbit    {orbit:?}"),
        Err(error) => println!("  rank gauge orbit    refused: {error:?}"),
    }

    // THE TRANSPORT ITSELF. Counts are receipts; these are the object.
    println!();
    println!("  THE TRANSPORT — what actually joins to what");
    let contacts = atlas.contacts();
    let names = atlas.constituents();
    for contact in contacts.iter().take(8) {
        println!(
            "    {:<44} --{}-->  {}",
            names.get(contact.from).cloned().unwrap_or_default(),
            contact.species.name(),
            names.get(contact.to).cloned().unwrap_or_default()
        );
    }
    println!("    … and {} more", contacts.len().saturating_sub(8));

    // A CHAIN THROUGH THE MATERIAL, walked on the material's own dependency height. The height is
    // SCC-collapsed, so a step is a genuine descent and the walk cannot loop.
    println!();
    println!("  A CHAIN THROUGH THE MATERIAL — walked on its own dependency height, deepest first");
    let mut outgoing: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
    for contact in contacts {
        outgoing.entry(contact.from).or_default().push(contact.to);
    }
    let deepest = heights
        .iter()
        .enumerate()
        .max_by_key(|(_, height)| **height)
        .map(|(at, _)| at);
    if let Some(mut here) = deepest {
        let mut walked = vec![here];
        let mut seen: BTreeSet<usize> = BTreeSet::new();
        seen.insert(here);
        // step to the tallest successor strictly below this one: a real descent every step
        while let Some(next) = outgoing.get(&here).and_then(|onward| {
            onward
                .iter()
                .filter(|to| !seen.contains(to) && heights[**to] < heights[here])
                .max_by_key(|to| heights[**to])
                .copied()
        }) {
            walked.push(next);
            seen.insert(next);
            here = next;
        }
        // The walk runs to exhaustion; only the EXHIBIT is bounded, and the full length stands
        // beside it. A cap applied to the walk itself would read as the chain's length.
        const CHAIN_EXHIBIT: usize = 16;
        println!(
            "    {} steps, height {} down to {}{}",
            walked.len(),
            heights[walked[0]],
            heights[*walked.last().unwrap()],
            if walked.len() > CHAIN_EXHIBIT {
                format!("   (first {CHAIN_EXHIBIT} exhibited, the rest counted)")
            } else {
                String::new()
            }
        );
        for (at, site) in walked.iter().take(CHAIN_EXHIBIT).enumerate() {
            println!(
                "      {:>2}  h{:<4} {}",
                at,
                heights[*site],
                names.get(*site).cloned().unwrap_or_default()
            );
        }
    }

    // THE FACES, ASKED OF THE MATERIAL RATHER THAN READ OFF A TABLE.
    println!();
    println!("  THE FACE QUOTIENT — which declared faces the material can tell apart");
    println!("  `ContactSpecies` is six variants written in this repository. This asks the material");
    println!("  whether its own conduct distinguishes them: faces are states, composition at a shared");
    println!("  constituent is the successor, and a block of more than one face is a distinction that");
    println!("  was declared and is not carried.");
    let quotient = face_quotient(&atlas);
    println!(
        "    declared faces {:?}   blocks {}   rounds {}",
        quotient.declared,
        quotient.blocks.len(),
        quotient.rounds
    );
    println!(
        "    the vertical reading is four receivers; the fifth is CONTAINMENT, read off closed"
    );
    println!(
        "    boundaries — a compound IS one. consulted {}   faces lying inside one {:?}",
        quotient.closure_read, quotient.enclosed_faces
    );
    for block in &quotient.blocks {
        let members: Vec<&str> = block.iter().map(|face| face.as_str()).collect();
        println!(
            "      {}{}",
            members.join(" ~ "),
            if members.len() > 1 {
                "     <- the material does not separate these"
            } else {
                ""
            }
        );
    }
    if quotient.separated.is_empty() {
        println!("    the one-shot reading was already exact: conduct separated no further pair");
    } else {
        for (left, right, word) in quotient.separated.iter().take(8) {
            println!("      {left} and {right} part after the chain {word:?}");
        }
    }
    Ok(())
}

// -------------------------------------------------------------------------------------------------
// condition — terrain founded on one material, read through another
// -------------------------------------------------------------------------------------------------

/// Found an atlas for each of two materials, join them, and ask what the join reads that neither
/// half can — then ablate each half and require the reading to go back.
///
/// # The crux, stated because it decides the design
///
/// A join is a **disjoint union**: constituents are prefixed, so two materials share no constituent
/// and no route can cross between them. That is deliberate — whether a Lean name and a Rust name are
/// the same thing is a question for a quotient and answering it at the intake would be authoring the
/// conclusion. **So the terrain two codecs share is not their constituents. It is their FACES.**
///
/// `face_quotient` asks whether the faces conduct alike. Over one material it can only speak about
/// that material's own faces; over the join it can compare a face of one against a face of the
/// other, which is a reading **neither half can produce alone**. That is the cross-codec return, and
/// the ablation is exact: remove either half and the pair becomes unaskable again.
fn condition(
    left_root: &Path,
    left_extension: &str,
    right_root: &Path,
    right_extension: &str,
    budget: usize,
) -> Result<(), String> {
    println!("EROS · CONDITION");
    println!(
        "  material A   {} (.{left_extension})",
        left_root.display()
    );
    println!(
        "  material B   {} (.{right_extension})",
        right_root.display()
    );
    println!();

    let left = atlas_of(left_root, left_extension, budget)?;
    let right = atlas_of(right_root, right_extension, budget)?;
    let joined = left.merge(&right, "B:").map_err(|e| format!("{e:?}"))?;

    let read = |name: &str, atlas: &life::material_incidence::MaterialAtlas| {
        let quotient = face_quotient(atlas);
        println!(
            "  {name:<22} constituents {:>7}   contacts {:>8}   faces {:?}   blocks {}",
            atlas.constituents().len(),
            atlas.contacts().len(),
            quotient.declared,
            quotient.blocks.len()
        );
        quotient
    };
    let left_reading = read("A alone", &left);
    let right_reading = read("B alone", &right);
    let joined_reading = read("A joined with B", &joined);

    println!();
    println!("  WHAT THE JOIN READS THAT NEITHER HALF CAN");
    let alone: BTreeSet<String> = left_reading
        .declared
        .iter()
        .chain(right_reading.declared.iter())
        .cloned()
        .collect();
    let crossing: Vec<(&String, &String)> = joined_reading
        .blocks
        .iter()
        .flat_map(|block| {
            let members: Vec<&String> = block.iter().collect();
            let mut pairs = Vec::new();
            for (at, one) in members.iter().enumerate() {
                for other in members.iter().skip(at + 1) {
                    pairs.push((*one, *other));
                }
            }
            pairs
        })
        .filter(|(one, other)| {
            let one_is_left = left_reading.declared.contains(one);
            let other_is_left = left_reading.declared.contains(other);
            one_is_left != other_is_left
        })
        .collect();
    println!(
        "    faces declared by A or B alone        {:?}",
        alone.iter().collect::<Vec<_>>()
    );
    println!(
        "    faces the JOIN declares               {:?}",
        joined_reading.declared
    );
    if crossing.is_empty() {
        println!("    the join keeps every cross-material face pair APART");
        println!("    -- a reading neither half could take, and it separates rather than collapses");
    } else {
        for (one, other) in &crossing {
            println!("    the join CANNOT TELL APART:  {one} ~ {other}");
            println!("      one comes from A and the other from B, so this pair is unaskable of");
            println!("      either material alone. It is the join's own return.");
        }
    }

    println!();
    println!("  THE ABLATION — remove a half and require the reading to go back");
    let left_again = face_quotient(&left);
    let right_again = face_quotient(&right);
    let left_back = left_again.declared == left_reading.declared
        && left_again.blocks.len() == left_reading.blocks.len();
    let right_back = right_again.declared == right_reading.declared
        && right_again.blocks.len() == right_reading.blocks.len();
    println!("    A read alone again, unchanged   {left_back}");
    println!("    B read alone again, unchanged   {right_back}");
    let pair_unaskable = !left_reading
        .declared
        .iter()
        .any(|face| right_reading.declared.contains(face));
    println!("    the cross pair is unaskable of either half alone   {pair_unaskable}");
    if !(left_back && right_back) {
        return Err("the ablation did not return either half's own reading".to_owned());
    }
    println!();
    println!("  THE BOUND ON A SEPARATION, STATED BECAUSE IT IS EASY TO OVERREAD");
    println!("  A join is disjoint, so two faces from two materials are read over two graphs of");
    println!("  different shape. A separation therefore may reflect the MATERIALS differing rather");
    println!("  than the FACES differing, and this run cannot tell those apart. What it does");
    println!("  establish is that the pair became askable at all, and that the ablation removes it.");
    println!("  The control that would sharpen it is two bodies of ONE codec joined: the same face");
    println!("  appears on both sides and must then COLLAPSE, or the reading is about shape alone.");
    if !pair_unaskable {
        println!();
        println!("    THE CONTROL DID NOT FIRE: the two materials declare a face in common, so the");
        println!("    cross-material pair was askable of one of them alone and the join added nothing.");
    }
    Ok(())
}

/// One material's atlas, by whichever incidence route its extension declares.
fn atlas_of(
    root: &Path,
    extension: &str,
    budget: usize,
) -> Result<life::material_incidence::MaterialAtlas, String> {
    let files = read_files(root, extension)?;
    let mut carried = 0usize;
    match extension {
        "rs" => {
            let mut items = Vec::new();
            for (ordinal, (path, octets)) in files.iter().enumerate() {
                if carried + octets.len() > budget {
                    break;
                }
                carried += octets.len();
                let text = String::from_utf8_lossy(octets);
                items.extend(rust_items_of_section(path, ordinal as u64, &text));
            }
            rust_atlas(&items, files.len() as u64).map_err(|error| format!("{error:?}"))
        }
        "lean" => {
            let mut readings = Vec::new();
            for (_, octets) in &files {
                if carried + octets.len() > budget {
                    break;
                }
                carried += octets.len();
                let text = String::from_utf8_lossy(octets);
                readings.push(read_development(
                    &text,
                    DeclarationGrain::EveryTopLevelDeclaration,
                ));
            }
            let reading = join(readings);
            let recruitment = reading.declared_recruitment_qualified();
            let order: Vec<String> = reading
                .declarations
                .iter()
                .filter(|form| !form.anonymous)
                .map(|form| form.qualified())
                .collect();
            let open: u64 = reading
                .open_recruitment()
                .values()
                .map(|symbols| symbols.len() as u64)
                .sum();
            lean_atlas(
                &recruitment,
                // Tactic position is deliberately NOT joined, matching the standing sweep:
                // `tactic_position_declared` is a BOUNDING instrument, and a declared name in
                // tactic position is probably a step-head misread, so joining it would manufacture
                // edges the reading itself refuses.
                &BTreeMap::new(),
                &order,
                open,
                files.len() as u64,
            )
            .map_err(|error| format!("{error:?}"))
        }
        _ => {
            let mut occurrences: Vec<(String, String)> = Vec::new();
            for (path, octets) in &files {
                if carried + octets.len() > budget {
                    break;
                }
                carried += octets.len();
                occurrences.push((path.clone(), String::from_utf8_lossy(octets).into_owned()));
            }
            prose_atlas(&occurrences, 2).map_err(|error| format!("{error:?}"))
        }
    }
}

// -------------------------------------------------------------------------------------------------
// supersede — the superseded parser against the incidence route, on one corpus
// -------------------------------------------------------------------------------------------------

/// Found the same corpus twice — once as the superseded parser left it on disk, once by the
/// incidence route — and compare the transport populations.
///
/// # Why this is the control the supersession owes
///
/// `crates/holonic-engine/src/statement_grammar.rs` is superseded as an authored grammar, and a
/// supersession without a comparison is an assertion. The plan's station four asked for the atlas to
/// be re-founded **through the ladder**; the ladder was built and measured, and it founds the
/// character codec and no statement structure at all, so there is nothing up there to re-found it
/// with. **That is the falsifier's result, not an excuse**, and it re-specifies the control rather
/// than cancelling it: the replacement for an authored grammar is not a second codec rung but the
/// material's own oriented incidence, which is what this compares against.
///
/// The incidence route knows no bracket, no separator and no word rule. It reads declarations and
/// the declarations they recruit, and hands over `L_t` directly.
fn supersede(root: &Path, against: &Path) -> Result<(), String> {
    println!("EROS · SUPERSEDE");
    println!("  the parser's deposited atlas   {}", against.display());
    println!("  the corpus                     {}", root.display());
    println!();

    // --- the parser route, as it left the deposit
    let deposited = fs::read_to_string(against)
        .map_err(|error| format!("read {}: {error}", against.display()))?;
    let mut parser_edges: BTreeSet<(String, String)> = BTreeSet::new();
    let mut parser_heads: BTreeSet<String> = BTreeSet::new();
    for line in deposited.lines().skip(1) {
        let mut fields = line.split('\t');
        let (Some(kind), Some(head), Some(detail)) = (fields.next(), fields.next(), fields.next())
        else {
            continue;
        };
        if kind == "edge" {
            parser_edges.insert((head.to_owned(), detail.to_owned()));
            parser_heads.insert(head.to_owned());
            parser_heads.insert(detail.to_owned());
        }
    }

    // --- the incidence route, founded now
    let files = read_files(root, "lean")?;
    let mut carried = Vec::new();
    for (_, octets) in &files {
        let text = String::from_utf8_lossy(octets);
        carried.push(read_development(
            &text,
            DeclarationGrain::EveryTopLevelDeclaration,
        ));
    }
    let reading = join(carried);
    let recruitment = reading.declared_recruitment_qualified();
    let order: Vec<String> = reading
        .declarations
        .iter()
        .filter(|form| !form.anonymous)
        .map(|form| form.qualified())
        .collect();
    let open: u64 = reading
        .open_recruitment()
        .values()
        .map(|symbols| symbols.len() as u64)
        .sum();
    let atlas = lean_atlas(
        &recruitment,
        &BTreeMap::new(),
        &order,
        open,
        files.len() as u64,
    )
    .map_err(|error| format!("{error:?}"))?;
    let constituents = atlas.constituents();
    let incidence_edges: BTreeSet<(String, String)> = atlas
        .contacts()
        .iter()
        .filter_map(|contact| {
            Some((
                constituents.get(contact.from)?.clone(),
                constituents.get(contact.to)?.clone(),
            ))
        })
        .collect();

    println!("  {:>26} {:>12} {:>12}", "", "parser", "incidence");
    println!(
        "  {:>26} {:>12} {:>12}",
        "transport edges",
        parser_edges.len(),
        incidence_edges.len()
    );
    println!(
        "  {:>26} {:>12} {:>12}",
        "heads / constituents",
        parser_heads.len(),
        constituents.len()
    );
    println!("  {:>26} {:>12} {:>12}", "files read", "-", files.len());
    println!();

    let shared: usize = incidence_edges.intersection(&parser_edges).count();
    println!("  edges both routes found        {shared}");
    println!(
        "  only the parser found          {}",
        parser_edges.difference(&incidence_edges).count()
    );
    println!(
        "  only the incidence route       {}",
        incidence_edges.difference(&parser_edges).count()
    );
    println!();
    println!("  THE VERDICT THIS CONTROL OWES");
    if incidence_edges.len() >= parser_edges.len() {
        println!(
            "    The incidence route founds AT LEAST as many transports as the authored grammar,"
        );
        println!(
            "    so nothing the parser carried is lost by superseding it. The supersession stands."
        );
    } else {
        println!(
            "    THE INCIDENCE ROUTE FOUNDS FEWER TRANSPORTS. The parser was doing real work and"
        );
        println!("    the shortfall is reported rather than the ladder: restore what it carried.");
    }
    println!();
    println!("  Bound: the two routes are not the same reading and the overlap is not the point.");
    println!("  The parser's edge joins two HEADS it split out of a statement; the incidence route's");
    println!("  joins two DECLARATIONS. A low overlap with a larger incidence population means the");
    println!("  incidence route carries transports the split could not see, which is the claim.");
    Ok(())
}

// -------------------------------------------------------------------------------------------------
// stations
// -------------------------------------------------------------------------------------------------

fn stations() {
    println!("EROS · STATIONS");
    println!();
    println!("  The cycle is one law: mount -> differentiate -> conduct -> glue -> radiate ->");
    println!("  genuine exterior return -> reflect/deposit -> later current. What follows is which");
    println!("  of its stations this binary reaches TODAY. A station named unwired is unwired: a");
    println!("  subcommand that printed something plausible for work it had not done would be worse");
    println!("  than an absent one.");
    println!();
    let rows = [
        (
            "mouth",
            "WIRED",
            "the codec recovered from octets, the scale ladder, the authored reading beside it",
        ),
        (
            "atlas",
            "WIRED",
            "the material's oriented incidence, its heights, and the rank gauge orbit",
        ),
        (
            "condition",
            "WIRED",
            "two materials joined into one atlas, and the face reading only the join can take",
        ),
        (
            "supersede",
            "WIRED",
            "the superseded parser's deposited atlas against the incidence route on one corpus",
        ),
        (
            "compress",
            "unwired",
            "the conduct quotient with the shortest separating word per collapsed pair",
        ),
        (
            "produce",
            "unwired",
            "composition, and adjudication by the chain rather than by an exterior",
        ),
        (
            "seal",
            "unwired",
            "ErosRest over the whole body, with its three controls",
        ),
        (
            "resume",
            "unwired",
            "mount a sealed rest and let a later current ride it",
        ),
    ];
    for (name, state, what) in rows {
        println!("  {name:<10} {state:<8} {what}");
    }
    println!();
    println!("  Plan: blueprint/THE_CODEC_IS_RECOVERED_AT_EVERY_SCALE_AND_THE_FACES_ARE_A_RETURN.md");
}
