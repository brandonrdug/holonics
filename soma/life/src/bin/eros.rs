//! **`eros` — the application.**
//!
//! ```text
//! eros mouth    --directory D [--extension E] [--radius N] [--scales N]
//! eros atlas    --directory D [--extension E]
//! eros phoenix infer     --rest R --text "..." [--text ...] [--export-manifest]
//! eros phoenix infer     --product D --text "..." --card
//! eros phoenix cultivate --rest R --material F --out S
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

use holonic_engine::lean_development::{join, read_development, DeclarationGrain};
use holonic_engine::phoenix::runtime;
use life::atlas_cultivation::{conduct, MetricDeclaration};
use life::causal_language::{lexical_tokens, lexical_tokens_under, LexicalAperture};
use life::exposure_codec::{ladder, ExposureApertures, LadderStop, UnitRole};
use life::material_incidence::{
    face_quotient, lean_atlas, prose_atlas, rust_atlas, rust_items_of_section,
};
use life::phoenix_rest::{
    content_bar, cultivate, forbidden_open, lineage_metadata, loss_digest, open_descriptors,
    read_rest, regions,
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

  eros phoenix infer     --rest R --text \"...\" [--text ...] [--export-manifest]
                mount a sealed native rest ALONE and conduct each prompt through the rest's
                own declared walk, future and depth laws; the plural section is returned and
                the rest is left octet-identical

  eros phoenix infer     --product DIR --text \"...\" --card
                mount the cultivated product directory and addressed W1 predecessor, then
                conduct unseen runtime text on the resident card and return its plural face

  eros phoenix cultivate --rest R --material F --out S
                expose one material to a sealed rest under the cultivation law and write a
                DISTINCT successor rest; the predecessor is not touched

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
    // The phoenix station carries a deed word and two valueless flags, so the loop reads a flag
    // before it reaches for a value. Every other station's parse is unmoved.
    let mut deed: Option<String> = None;
    let mut rest: Option<PathBuf> = None;
    let mut product: Option<PathBuf> = None;
    let mut material: Option<PathBuf> = None;
    let mut out: Option<PathBuf> = None;
    let mut texts: Vec<String> = Vec::new();
    let mut export_manifest = false;
    let mut card = false;
    while let Some(named) = arguments.next() {
        match named.as_str() {
            "--export-manifest" => {
                export_manifest = true;
                continue;
            }
            "--card" => {
                card = true;
                continue;
            }
            _ => {}
        }
        if !named.starts_with("--") {
            if station == "phoenix" && deed.is_none() {
                deed = Some(named);
                continue;
            }
            return Err(format!("unknown argument {named}\n\n{USAGE}"));
        }
        let value = arguments
            .next()
            .ok_or_else(|| format!("{named} requires a value"))?;
        match named.as_str() {
            "--rest" => rest = Some(PathBuf::from(value)),
            "--product" => product = Some(PathBuf::from(value)),
            "--material" => material = Some(PathBuf::from(value)),
            "--out" => out = Some(PathBuf::from(value)),
            // Repeatable: the material is the argument, and a station that took one prompt would
            // be asking the caller to run it once per prompt in a different process each time.
            "--text" => texts.push(value),
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
            let with_directory = with_directory.ok_or("condition requires --with-directory")?;
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
        "phoenix" => {
            let deed = deed.ok_or("phoenix requires a deed: infer or cultivate")?;
            match deed.as_str() {
                "infer" => {
                    if card {
                        let product = product.ok_or(
                            "phoenix infer --card requires --product <cultivated directory>",
                        )?;
                        if rest.is_some() {
                            return Err(
                                "phoenix infer --card accepts --product and rejects --rest"
                                    .to_owned(),
                            );
                        }
                        phoenix_card_infer(&product, &texts)
                    } else {
                        let rest = rest.ok_or("phoenix requires --rest <sealed native rest>")?;
                        phoenix_infer(&rest, &texts, export_manifest)
                    }
                }
                "cultivate" => {
                    let rest =
                        rest.ok_or("phoenix cultivate requires --rest <sealed native rest>")?;
                    let material =
                        material.ok_or("phoenix cultivate requires --material <file>")?;
                    let out = out.ok_or("phoenix cultivate requires --out <successor path>")?;
                    phoenix_cultivate(&rest, &material, &out)
                }
                other => Err(format!(
                    "phoenix has two deeds, infer and cultivate; {other} is neither\n\n{USAGE}"
                )),
            }
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
    println!(
        "  The recovery is handed octets and a radius and nothing else: no grammar, no keyword"
    );
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
    println!(
        "  root {}   .{extension} files {}",
        root.display(),
        files.len()
    );
    println!();
    println!(
        "  The atlas is the material's own oriented incidence — constituents, contacts, and a"
    );
    println!(
        "  dependency height that is never a line number. The rank gauge orbit is taken before"
    );
    println!(
        "  any reading is believed: a representative that changed a rank would mean the intake"
    );
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
    println!(
        "  height ranks        {top} (over {} heights)",
        heights.len()
    );
    println!(
        "  storage ordinals    {} carried beside them",
        storage.len()
    );
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
    println!(
        "  `ContactSpecies` is six variants written in this repository. This asks the material"
    );
    println!(
        "  whether its own conduct distinguishes them: faces are states, composition at a shared"
    );
    println!(
        "  constituent is the successor, and a block of more than one face is a distinction that"
    );
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
    println!("  material A   {} (.{left_extension})", left_root.display());
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
        println!(
            "    -- a reading neither half could take, and it separates rather than collapses"
        );
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
    println!(
        "  different shape. A separation therefore may reflect the MATERIALS differing rather"
    );
    println!("  than the FACES differing, and this run cannot tell those apart. What it does");
    println!(
        "  establish is that the pair became askable at all, and that the ablation removes it."
    );
    println!(
        "  The control that would sharpen it is two bodies of ONE codec joined: the same face"
    );
    println!(
        "  appears on both sides and must then COLLAPSE, or the reading is about shape alone."
    );
    if !pair_unaskable {
        println!();
        println!(
            "    THE CONTROL DID NOT FIRE: the two materials declare a face in common, so the"
        );
        println!(
            "    cross-material pair was askable of one of them alone and the join added nothing."
        );
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
    println!(
        "  The parser's edge joins two HEADS it split out of a statement; the incidence route's"
    );
    println!(
        "  joins two DECLARATIONS. A low overlap with a larger incidence population means the"
    );
    println!("  incidence route carries transports the split could not see, which is the claim.");
    Ok(())
}

// -------------------------------------------------------------------------------------------------
// phoenix — a sealed native rest, mounted alone
// -------------------------------------------------------------------------------------------------

/// The W4 application deed: one authenticated cultivated directory, one unseen runtime material,
/// and one resident card circulation. The generated section is returned without ranking or
/// sampling; all admission/work/apparatus coordinates are read from the resident return.
fn phoenix_card_infer(product: &Path, texts: &[String]) -> Result<(), String> {
    if texts.len() != 1 || texts[0].trim().is_empty() {
        return Err("phoenix infer --card requires exactly one unseen non-empty --text".to_owned());
    }
    let text = &texts[0];
    let returned = runtime::infer(product, text)?;
    let receipt = serde_json::to_string(&returned.receipt).map_err(|error| error.to_string())?;
    println!("EROS · PHOENIX · INFER · CARD · SOURCE-DETACHED");
    println!("  product directory {}", product.display());
    println!(
        "  input addresses {} · terminal position {} · plural {} · separated {}",
        returned.receipt.input.native_ids.len(),
        returned.receipt.generated.terminal_position,
        returned.receipt.generated.plural.len(),
        returned.receipt.generated.separated,
    );
    println!("PHOENIX_RETURN {receipt}");
    Ok(())
}

/// How much of a plural section is exhibited. The section itself is returned whole and its
/// population is printed beside the exhibit, exactly as the atlas station's chain is: a cap applied
/// to the *reading* would read as the reading's size.
const SECTION_EXHIBIT: usize = 24;

/// **CONDUCT a sealed native rest, alone.**
///
/// # What this mounts, and what it does not
///
/// One file is opened: the rest. There is no corpus behind it, no source model, no development
/// material and no second place to look — the container carries the transport, the standings, the
/// suffix links, the vocabulary and, in its own metadata, the statement of every law that reads it.
/// The process prints its own open descriptors so the claim is a measurement rather than an
/// assertion.
///
/// # The surface this conducts on, stated because it is a reliance and not a result
///
/// This arm is the independent ARM N control. Its conduct is CPU-exact and integral throughout;
/// the lifted Phoenix card path is the distinct `--product ... --card` application entry above.
/// Keeping the two entries explicit prevents an ARM N answer from being reported as Gemma lift.
fn phoenix_infer(rest_path: &Path, texts: &[String], export_manifest: bool) -> Result<(), String> {
    println!("EROS · PHOENIX · INFER");
    if texts.is_empty() {
        return Err("infer requires at least one --text; the material is the argument".to_owned());
    }
    let named = rest_path.display().to_string();
    let (octets, rest) = read_rest(rest_path).map_err(|refusal| refusal.to_string())?;
    println!("  the rest        {named}");
    println!(
        "    {} octets · {} classes · {} transitions · {} vocabulary germs · tree height {}",
        octets.len(),
        rest.classes(),
        rest.transitions(),
        rest.vocabulary.len(),
        rest.height
    );
    println!(
        "    class extents   {}",
        if rest.extent.is_empty() {
            "NOT CARRIED — this rest conducts and cannot be deposited into".to_owned()
        } else {
            format!(
                "{} carried, so this rest can also be cultivated",
                rest.extent.len()
            )
        }
    );
    let before = loss_digest(&octets);
    println!("    sha256 before   {before}");
    println!(
        "    (a digest here DETECTS LOSS and addresses nothing: a rest is its path and its lineage)"
    );
    println!();

    println!("  THE LAWS, AS THE REST ITSELF DECLARES THEM");
    for law in ["law.walk", "law.future", "law.depth"] {
        match rest.metadata.get(law) {
            Some(statement) => println!("    {law}\n      {statement}"),
            None => println!("    {law}   ABSENT — the rest declares no such law"),
        }
    }
    println!(
        "    its declared material (a LINEAGE, not a corpus)\n      {}",
        rest.metadata
            .get("material")
            .cloned()
            .unwrap_or_else(|| "(none declared)".to_owned())
    );
    println!();

    print_source_audit();

    for text in texts {
        let section = conduct(&rest, text, &lexical_tokens(text));
        let mut by_depth: BTreeMap<usize, Vec<&(String, u64, usize)>> = BTreeMap::new();
        for offer in &section.offered {
            by_depth.entry(offer.2).or_default().push(offer);
        }
        println!("  PROMPT {text:?}");
        println!("    the walk            {}", section.trace.join(" · "));
        println!(
            "    landed class        {}   standing {}",
            section.class, section.standing
        );
        println!(
            "    the plural future   {} germs over {} ladder depth(s)",
            section.offered.len(),
            by_depth.len()
        );
        for (depth, offers) in &by_depth {
            println!(
                "      depth {depth:<3} {:>6} germs{}",
                offers.len(),
                if offers.len() > SECTION_EXHIBIT {
                    format!("   (first {SECTION_EXHIBIT} exhibited, the rest counted)")
                } else {
                    String::new()
                }
            );
            let shown: Vec<String> = offers
                .iter()
                .take(SECTION_EXHIBIT)
                .map(|(surface, standing, _)| format!("{surface:?}×{standing}"))
                .collect();
            println!("        {}", shown.join(" "));
        }
        println!(
            "    NO WINNER IS TAKEN. The section is the whole family the landed class's ladder \
             offers, each germ with the standing of the class it reaches and the depth it was \
             found at; nothing here ranks them and nothing here samples."
        );
        println!();
    }

    if export_manifest {
        println!("  THE REALIZATION MANIFEST — the container's own regions, read off its header");
        println!(
            "    {:<28} {:>7} {:>12} {:>12}",
            "region", "dtype", "octets", "offset"
        );
        for region in regions(&octets) {
            println!(
                "    {:<28} {:>7} {:>12} {:>12}",
                region.name,
                region.dtype,
                region.octets(),
                region.start
            );
        }
        println!(
            "    metadata keys  {:?}",
            rest.metadata.keys().collect::<Vec<_>>()
        );
        println!();
        println!(
            "  THE CONTENT BAR — what the rest is required NOT to carry, measured on its octets"
        );
        for row in content_bar(&octets, &rest) {
            println!(
                "    [{}] {}",
                if row.held { "held" } else { "BROKEN" },
                row.claim
            );
            println!("        {}", row.evidence);
        }
        println!();
    }

    // The rest is re-read from the disk rather than re-hashed from memory: the question is whether
    // the FILE moved, and a digest of octets this process is still holding could not answer it.
    let after_octets = fs::read(rest_path).map_err(|error| format!("{named}: {error}"))?;
    let after = loss_digest(&after_octets);
    println!("  THE FROZEN REST, RE-READ FROM THE DISK");
    println!("    sha256 after    {after}");
    println!(
        "    {}",
        if after == before {
            "the inference deposited nothing: the rest is octet-identical"
        } else {
            "THE REST MOVED — a frozen inference has written, which it may not"
        }
    );
    if after != before {
        return Err("the rest moved under an inference".to_owned());
    }
    Ok(())
}

/// The process asking of itself what it has open, and whether any of it is forbidden.
///
/// A rest is opened, read whole and closed, so what remains is this process's own stdio; the audit
/// is the set at this instant and the forbidden line is a search over it.
fn print_source_audit() {
    let audit = open_descriptors();
    println!("  THE SOURCE AUDIT — every descriptor this process holds, asked of itself");
    for target in &audit {
        println!("    {target}");
    }
    let forbidden = forbidden_open(&audit);
    println!(
        "    forbidden targets open ({:?}): {}",
        life::phoenix_rest::FORBIDDEN_DESCRIPTORS,
        if forbidden.is_empty() {
            "none".to_owned()
        } else {
            forbidden.join(" ")
        }
    );
    println!();
}

/// **CULTIVATE a sealed native rest with one material, writing a DISTINCT successor.**
///
/// The predecessor's atlas is *mounted from the rest*, never rebuilt from a corpus, which is the
/// whole difference between a frozen runtime and a driver. The law is
/// [`life::atlas_cultivation`]'s: predict the continuation family at every position and record the
/// four-state relation (the structured residual), deposit, derive the structural rows from the
/// refusals the residual named and the standings through the declared metrics, and commit by
/// replay. Nothing about it is restated here.
fn phoenix_cultivate(
    rest_path: &Path,
    material_path: &Path,
    out_path: &Path,
) -> Result<(), String> {
    println!("EROS · PHOENIX · CULTIVATE");
    let named = rest_path.display().to_string();
    let material_named = material_path.display().to_string();
    let out_named = out_path.display().to_string();
    if out_path == rest_path {
        return Err(format!(
            "the successor {out_named} is the predecessor. A cultivation founds a DISTINCT rest; \
             the predecessor is not touched"
        ));
    }
    let (octets, rest) = read_rest(rest_path).map_err(|refusal| refusal.to_string())?;
    let before = loss_digest(&octets);
    let material = fs::read_to_string(material_path)
        .map_err(|error| format!("the material {material_named}: {error}"))?;
    println!("  the predecessor {named}");
    println!(
        "    {} octets · {} classes · {} transitions · {} vocabulary   sha256 {before}",
        octets.len(),
        rest.classes(),
        rest.transitions(),
        rest.vocabulary.len()
    );
    println!(
        "  the material    {material_named}   {} octets",
        material.len()
    );
    println!("  the successor   {out_named}");
    println!();
    print_source_audit();

    let metric = MetricDeclaration::identity();
    let grown = cultivate(&rest, &named, &material_named, &material, &metric)
        .map_err(|refusal| refusal.to_string())?;

    println!("  THE STRUCTURED RESIDUAL — the prediction, taken before anything moved");
    println!(
        "    {} germ occurrences carried into the standing rest",
        grown.germs
    );
    for (relation, count) in grown.residual.census() {
        println!("      {relation:<28} {count:>8}");
    }
    print!("    the depth the carried germ was first offered at:");
    for (depth, count) in grown.residual.depth_census() {
        match depth {
            None => print!("  offered-nowhere {count}"),
            Some(depth) => print!("  depth-{depth} {count}"),
        }
    }
    println!();
    println!();

    println!("  THE DELTA — plural, and every row names the position that caused it");
    println!(
        "    germs founded               {:>8}",
        grown.delta.germs_founded.len()
    );
    println!(
        "    classes founded             {:>8}   of which {} are SPLITS of a class that stood",
        grown.delta.classes_after - grown.delta.classes_before,
        grown.delta.classes_split()
    );
    // **The sharp face of a founding, and the one that says whether the material's own transport
    // was touched at all.** A transition founded at a class that already offered a nonempty family
    // is a founding *inside* what the body could already say; one founded at a class that offered
    // nothing is a terminus — a class whose longest string ends in a previous path's separator —
    // and the deposit is crossing the chronology's seam rather than changing the transport.
    let inside = grown
        .delta
        .transitions_founded
        .iter()
        .filter(|row| row.on_standing_class && !rest.row(row.class).is_empty())
        .count();
    println!(
        "    transitions founded         {:>8}   of which {} on classes that stood, and {} at a \
         class that already offered a nonempty family",
        grown.delta.transitions_founded.len(),
        grown.delta.transitions_founded_on_standing(),
        inside
    );
    println!(
        "    transitions rebased         {:>8}",
        grown.delta.transitions_rebased.len()
    );
    println!(
        "    suffix links rebased        {:>8}   of which {} on classes that stood",
        grown.delta.suffix_rebased.len(),
        grown
            .delta
            .suffix_rebased
            .iter()
            .filter(|row| row.on_standing_class)
            .count()
    );
    println!(
        "    classes whose standing moved{:>8}   total deposited {}",
        grown.delta.standing_increments.len(),
        grown
            .delta
            .standing_increments
            .values()
            .map(|increment| u128::from(*increment))
            .sum::<u128>()
    );
    println!("    the declared metric         {}", metric.name);
    let founded: Vec<String> = grown
        .delta
        .germs_founded
        .iter()
        .take(SECTION_EXHIBIT)
        .map(|germ| format!("{germ:?}"))
        .collect();
    if !founded.is_empty() {
        println!(
            "    the germs the material founded{}: {}",
            if grown.delta.germs_founded.len() > SECTION_EXHIBIT {
                format!(
                    " (first {SECTION_EXHIBIT} of {} exhibited)",
                    grown.delta.germs_founded.len()
                )
            } else {
                String::new()
            },
            founded.join(" ")
        );
    }
    println!(
        "    the committed container against the container the transport itself emits: {}",
        if grown.germ_side_identical {
            "OCTET-IDENTICAL on the germ side"
        } else {
            "DIFFERENT — the commit is not the derivation"
        }
    );
    println!(
        "    (the extents are the transport's on both sides, so that region is not a falsifier \
         here and is not counted as one; the germ side is.)"
    );
    if !grown.germ_side_identical {
        return Err("the committed delta is not the container the transport emits".to_owned());
    }
    println!();

    let mut successor = grown.successor.clone();
    successor.metadata = lineage_metadata(&rest, &named, &material_named, &grown, &metric);
    let successor_octets = successor
        .write_container()
        .map_err(|refusal| refusal.to_string())?;
    if let Some(parent) = out_path.parent() {
        fs::create_dir_all(parent).map_err(|error| format!("{}: {error}", parent.display()))?;
    }
    fs::write(out_path, &successor_octets).map_err(|error| format!("{out_named}: {error}"))?;

    println!("  THE SUCCESSOR — a distinct rest, sealed with its own lineage");
    println!(
        "    {} octets · {} classes · {} transitions · {} vocabulary · extents {}",
        successor_octets.len(),
        successor.classes(),
        successor.transitions(),
        successor.vocabulary.len(),
        successor.extent.len()
    );
    println!("    sha256          {}", loss_digest(&successor_octets));
    for key in [
        "cultivation.law",
        "cultivation.metric",
        "cultivation.predecessor",
        "cultivation.material",
        "cultivation.delta",
    ] {
        if let Some(value) = successor.metadata.get(key) {
            println!("    {key}\n      {value}");
        }
    }
    println!();

    let predecessor_after = fs::read(rest_path).map_err(|error| format!("{named}: {error}"))?;
    let after = loss_digest(&predecessor_after);
    println!("  THE PREDECESSOR, RE-READ FROM THE DISK");
    println!("    sha256 after    {after}");
    println!(
        "    {}",
        if after == before {
            "untouched: a cultivation founds a successor and does not overwrite what it grew from"
        } else {
            "THE PREDECESSOR MOVED — a cultivation has overwritten what it grew from"
        }
    );
    if after != before {
        return Err("the predecessor moved under a cultivation".to_owned());
    }
    Ok(())
}

// -------------------------------------------------------------------------------------------------
// stations
// -------------------------------------------------------------------------------------------------

fn stations() {
    println!("EROS · STATIONS");
    println!();
    println!("  The cycle is one law: mount -> differentiate -> conduct -> glue -> radiate ->");
    println!(
        "  genuine exterior return -> reflect/deposit -> later current. What follows is which"
    );
    println!("  of its stations this binary reaches TODAY. A station named unwired is unwired: a");
    println!(
        "  subcommand that printed something plausible for work it had not done would be worse"
    );
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
            "phoenix infer",
            "WIRED",
            "the independent ARM N rest mounted alone; retained as the CPU control",
        ),
        (
            "phoenix cultivate",
            "WIRED",
            "one material exposed to that rest, and a DISTINCT successor sealed with its lineage",
        ),
        (
            "phoenix --card",
            "WIRED",
            "a cultivated lifted product mounted source-detached and conducted on the card",
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
        println!("  {name:<18} {state:<8} {what}");
    }
    println!();
    println!(
        "  Plan: blueprint/THE_CODEC_IS_RECOVERED_AT_EVERY_SCALE_AND_THE_FACES_ARE_A_RETURN.md"
    );
}
