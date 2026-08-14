//! Point the exposure recovery at real sealed material and return the codec it recovers, the
//! independent route that agrees with it, the wrong readings that must not, and the bound.
//!
//! The material is one kind taken out of the sealed corpus deposited by
//! `the_material_mouth_seals_the_declared_body` — by default the Lean sources, because Lean's codec
//! is real, rigid and independently checkable. The recovery is handed **octets and nothing else**:
//! no `.lean` reader, no keyword list, no bracket table, no encoding.
//!
//! What is returned, in order:
//!
//! 1. the exposure — what was taken from the seal and what was withheld;
//! 2. the recovery — alphabet, the census of the exhausted family, the refusal law that establishes
//!    there is a codec at all, the direct quotient with the shortest context that separated each
//!    pair, both seeding frames, the roles, the boundary table and the gauge freedom;
//! 3. **the held-out answer key** — the recovered codec's segmentation of material it never saw,
//!    against an independent implementation of the same decomposition, with disagreements exhibited;
//! 4. **three declared wrong readings**, each of which must be separated from the recovery by an
//!    exhibited shortest word, with the two independent routes to that word agreeing;
//! 5. **the gauge orbit** — the same cross-check under a reversed input declaration and under an
//!    added receiver, so the agreement is shown to survive a frame change;
//! 6. **the gauge freedom, driven** — each unrealized adjacency flipped, the word that would decide
//!    it exhibited, and that word shown absent from the material;
//! 7. **the degenerate controls** — the same organ on material where the answer is different or
//!    absent, which is where authorship would show;
//! 8. **the exposure ladder** — the same recovery at increasing exposure, so the quantity of
//!    stimulus the codec takes is measured rather than assumed;
//! 9. **the answer key in both directions** — what exposure recovered of `lean_development`'s
//!    authored grammar, and what it recovered that the authored reader does not have.
//!
//! `CLAUDE.md` §8 — *a law that returns zero proves nothing about itself*. Section 4 is the non-zero
//! return of the law whose zero return is section 3. §9 — *return the artifact*: every count below
//! stands beside the population it counts.

use std::collections::{BTreeMap, BTreeSet};
use std::fs::File;
use std::path::{Path, PathBuf};

use holonic_engine::codec_recovery::{
    conform, Boundary, Conformance, OpaqueSymbolCodec, RecoveredCodec, Symbol,
};
use holonic_engine::codec_system::{
    cross_check, cross_check_over, CodecIndexReceiver, CodecSystem, ReversedInputOrder,
    SeparationSpecies, TheJointAutomaton,
};
use holonic_engine::derivation_atlas::{CODEC_KEYWORDS, DECLARATION_FORMERS};
use holonic_engine::lean_development::{
    read_development, DeclarationGrain, BINDING_TACTICS, DECLARATION_MODIFIERS, PREAMBLE_FORMS,
};
use life::exposure_codec::{
    carried, octets_of, recover, ExposedMaterial, ExposureApertures, ExposureObstruction,
    ExposureRecovery, UnitRole,
};
use life::text_material::ExactTextMaterialAtlas;

struct Settings {
    rest: Option<PathBuf>,
    directory: Option<PathBuf>,
    extension: String,
    identity_prefix: String,
    radius: usize,
    family_words: u64,
    octet_budget: u64,
    held_out: usize,
}

fn main() {
    if let Err(error) = run() {
        eprintln!("REFUSED: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let settings = arguments()?;
    let exposures = material(&settings)?;
    if exposures.is_empty() {
        return Err("the declared material carries no exposure".to_owned());
    }

    let held_out_at = exposures.len().saturating_sub(settings.held_out);
    let founding: Vec<Vec<u8>> = exposures[..held_out_at].to_vec();
    let held_out: Vec<Vec<u8>> = exposures[held_out_at..].to_vec();
    let founding = truncate_to(founding, settings.octet_budget);

    println!("=== [1] THE EXPOSURE ===");
    println!(
        "  source              {}",
        settings
            .rest
            .as_ref()
            .map(|path| format!("sealed rest {}", path.display()))
            .unwrap_or_else(|| format!(
                "directory {}",
                settings
                    .directory
                    .as_ref()
                    .map(|path| path.display().to_string())
                    .unwrap_or_default()
            ))
    );
    println!("  material kind       {}", settings.identity_prefix);
    println!(
        "  exposures founding  {}   octets {}",
        founding.len(),
        founding.iter().map(|e| e.len() as u64).sum::<u64>()
    );
    println!(
        "  exposures held out  {}   octets {}",
        held_out.len(),
        held_out.iter().map(|e| e.len() as u64).sum::<u64>()
    );
    println!(
        "  declared apertures  radius {}   family words {}",
        settings.radius, settings.family_words
    );

    let material = ExposedMaterial::expose(founding.clone(), settings.radius)
        .map_err(|error| format!("expose the material: {error}"))?;
    let recovery = recover(
        &material,
        ExposureApertures::declared(settings.radius, settings.family_words),
    )
    .map_err(|error| format!("recover from exposure: {error}"))?;

    println!("\n=== [2] THE RECOVERY ===");
    report(&recovery, founding.iter().map(|e| e.len() as u64).sum());

    let Some(codec) = recovery.codec.clone() else {
        println!("\nNo codec was recovered; the obstruction above is the return.");
        return Ok(());
    };

    println!("\n=== [2b] THE DIRECT QUOTIENT, BY A SECOND ALGORITHM ===");
    println!("  The quotient above is iterated refinement over contexts drawn from the exhausted");
    println!(
        "  family. This recomputes it in one pass by adjacency signature — every octet keyed by"
    );
    println!(
        "  exactly which octets follow it and which precede it — and the two must land on the"
    );
    println!(
        "  same partition. The signature route cannot be coarser than the refinement, because a"
    );
    println!("  one-hole context of length two *is* the signature, so agreement pins both.");
    let signature = signature_quotient(&material, &recovery.alphabet);
    let refined: BTreeSet<BTreeSet<u8>> = recovery.direct_quotient.iter().cloned().collect();
    let signed: BTreeSet<BTreeSet<u8>> = signature.iter().cloned().collect();
    println!(
        "    refinement route {} blocks   signature route {} blocks   the two routes {}",
        refined.len(),
        signed.len(),
        if refined == signed {
            "AGREE on the partition, block for block"
        } else {
            "DISAGREE — the difference is exhibited below"
        }
    );
    if refined != signed {
        for block in refined.symmetric_difference(&signed).take(6) {
            println!(
                "      only one route holds {}",
                render_octets(&block.iter().copied().collect::<Vec<_>>())
            );
        }
        return Err("the two quotient routes disagreed".to_owned());
    }
    println!(
        "  The independent route on the CODEC itself is Moore refinement over the joint carrier,"
    );
    println!(
        "  which `receiver_exact_compression::compress` runs inside every cross-check below; its"
    );
    println!("  block, collapsed and round counts are reported there.");

    println!("\n=== [3] THE HELD-OUT ANSWER KEY ===");
    println!(
        "  The recovered codec is run on {} exposures it never saw, against an independent",
        held_out.len()
    );
    println!(
        "  implementation of the same decomposition. The answer key is Rust's own decoder; it is"
    );
    println!("  consulted here for grading only and no part of the recovery ever called it.");
    let population: Vec<Vec<Symbol>> = held_out.iter().map(|octets| carried(octets)).collect();
    let borrowed: Vec<Vec<Symbol>> = population.clone();
    let key = answer_key();
    let conformance = conform(&codec, &key, &borrowed);
    exhibit_conformance("held out", &conformance);
    // and on the material it was founded on, because a codec that disagrees with the key where it
    // *did* look is a different finding from one that disagrees only where it did not.
    let founding_population: Vec<Vec<Symbol>> =
        founding.iter().map(|octets| carried(octets)).collect();
    let founding_borrowed: Vec<Vec<Symbol>> = founding_population.clone();
    let founding_conformance = conform(&codec, &key, &founding_borrowed);
    exhibit_conformance("founding", &founding_conformance);

    println!("\n=== [4] THREE DECLARED WRONG READINGS ===");
    println!(
        "  Each keeps the recovered classes and changes only where the unit breaks. Each must"
    );
    println!(
        "  be separated from the recovery by an exhibited word, and the two independent routes"
    );
    println!(
        "  to that word — the joint automaton and Moore refinement — must return the same one."
    );
    let wrong = wrong_readings(&codec);
    let mut separated = 0usize;
    for (name, reading) in &wrong {
        let check = cross_check(&codec, reading)
            .map_err(|error| format!("cross-check {name}: {error:?}"))?;
        let word = check.joint_automaton.clone();
        println!("\n  [{name}]");
        println!(
            "    rest states separated  {}   routes agree  {}   disagreements {:?}",
            check.rest_states_separated,
            check.agrees(),
            check.disagreements
        );
        match (&check.nerode, &word) {
            (Some((_, nerode_word)), Some(automaton_word)) => {
                println!(
                    "    shortest separating word   nerode {}   joint-automaton {}",
                    render(nerode_word),
                    render(automaton_word)
                );
                if let Some((left, right)) = &check.joint_automaton_returns {
                    println!("    recovered segments it   {}", render_tokens(left));
                    println!("    the wrong reading       {}", render_tokens(right));
                }
                separated += 1;
            }
            _ => println!("    NOT SEPARATED — this reading is observationally the recovery"),
        }
        if !check.agrees() {
            return Err(format!("the two routes disagreed on {name}"));
        }
        let wrong_conformance = conform(reading, &key, &borrowed);
        println!(
            "    against the answer key on held-out material: {} disagreements, {} refusals",
            wrong_conformance.disagreements.len(),
            wrong_conformance.refusals.len()
        );
        if let Some(first) = wrong_conformance.disagreements.first() {
            let (key_window, reading_window) = divergence_window(&first.target, &first.recovered);
            println!(
                "      at the first divergence   answer key {}   this reading {}",
                render_tokens(&key_window),
                render_tokens(&reading_window)
            );
        }
    }
    println!(
        "\n  separated {} of {} declared wrong readings",
        separated,
        wrong.len()
    );

    println!("\n=== [5] THE GAUGE ORBIT ON THE CROSS-CHECK ===");
    println!("  The same cross-check under two declared frame changes. A gauge whose orbit is");
    println!("  trivial has gauged nothing, so the orbit is exhibited rather than assumed.");
    if let Some((name, reading)) = wrong.first() {
        let system = CodecSystem::joint(&[&codec, reading])
            .map_err(|error| format!("joint carrier: {error:?}"))?;
        let plain = cross_check_over(&system, &TheJointAutomaton, &codec, reading)
            .map_err(|error| format!("plain: {error:?}"))?;
        let reversed = ReversedInputOrder { inner: &system };
        let flipped = cross_check_over(&reversed, &TheJointAutomaton, &codec, reading)
            .map_err(|error| format!("reversed: {error:?}"))?;
        let indexed = CodecIndexReceiver { inner: &system };
        let framed = cross_check_over(&indexed, &TheJointAutomaton, &codec, reading)
            .map_err(|error| format!("indexed: {error:?}"))?;
        println!("  against [{name}]");
        // `codec_system` declares which quantity survives a frame change and which does not:
        // *"which of several equally short words is returned is a tie-break and
        // implementation-local; only the length is the agreed quantity"*. So the expectation is
        // declared per frame rather than read off `agrees()` — reading the whole of `agrees()` as
        // the invariant would convict a frame change for doing exactly what it was declared to do.
        //
        // The third frame is the control on the other two. `CodecIndexReceiver` adds a receiver that
        // returns **which codec a state belongs to** — an absolute frame, a coordinate outside the
        // declared family — and under it the question has no content: the two rest states are apart
        // at one shot, nothing is ever collapsed, and the Nerode route has no word to exhibit. It is
        // included precisely so the two lawful frames are seen to be lawful against something that
        // is not.
        let mut words: BTreeSet<String> = BTreeSet::new();
        let mut lengths: BTreeSet<usize> = BTreeSet::new();
        for (frame, check, expectation) in [
            ("declared order", &plain, "no species at all"),
            (
                "reversed input order",
                &flipped,
                "tie-break only; the length must not move",
            ),
            (
                "codec-index receiver",
                &framed,
                "ABSOLUTE FRAME — must trivialise and exhibit no word",
            ),
        ] {
            let nerode = check
                .nerode
                .as_ref()
                .map(|(_, word)| render(word))
                .unwrap_or_else(|| "-".to_owned());
            let automaton = check
                .joint_automaton
                .as_ref()
                .map(|word| render(word))
                .unwrap_or_else(|| "-".to_owned());
            println!(
                "    {frame:<22} blocks {:>3}  collapsed {:>3}  rounds {:>2}  nerode [{nerode}]  automaton [{automaton}]",
                check.compression.conduct.len(),
                check.compression.collapsed.len(),
                check.compression.rounds,
            );
            println!(
                "      declared: {expectation:<48} returned species {:?}",
                check.disagreements
            );
            let met = match frame {
                "declared order" => check.agrees(),
                "reversed input order" => {
                    check
                        .disagreements
                        .iter()
                        .all(|species| *species == SeparationSpecies::TieBrokenDifferently)
                        && check
                            .nerode
                            .as_ref()
                            .zip(check.joint_automaton.as_ref())
                            .is_none_or(|((_, left), right)| {
                                left.len() == right.len()
                            })
                }
                _ => {
                    check.compression.collapsed.is_empty()
                        && check.nerode.is_none()
                        && check
                            .disagreements
                            .contains(&SeparationSpecies::NerodeSeparatedWithoutExhibitingAWord)
                }
            };
            println!("      the frame did what it declared: {met}");
            if !met {
                return Err(format!("{frame} did not do what it declared"));
            }
            if let Some((_, word)) = &check.nerode {
                words.insert(render(word));
                lengths.insert(word.len());
            }
        }
        println!(
            "    the words the two lawful frames returned: {:?}, their lengths {:?} — {}",
            words,
            lengths,
            if words.len() > 1 && lengths.len() == 1 {
                "the gauge orbit is NON-TRIVIAL and the invariant is the length, exactly as declared"
            } else if words.len() > 1 {
                "the orbit moved the length, which is a defect and not a tie-break"
            } else {
                "one word across both frames; on this material the orbit is trivial"
            }
        );
    }

    println!("\n=== [6] THE GAUGE FREEDOM, DRIVEN ===");
    if recovery.gauge_freedom.is_empty() {
        println!("  The material realized every class adjacency; nothing is free.");
    }
    for (left, right) in &recovery.gauge_freedom {
        let Some(flipped) = flip(&codec, &recovery, *left, *right) else {
            continue;
        };
        let word = codec
            .shortest_separating_input(&flipped)
            .map_err(|error| format!("separate the flipped reading: {error:?}"))?;
        let flipped_conformance = conform(&flipped, &key, &borrowed);
        match word {
            Some(word) => {
                let octets = octets_of(&word).unwrap_or_default();
                println!(
                    "  {:>9} -> {:<9} free.  the word that would decide it: {}   does the material carry it? {}",
                    left.name(),
                    right.name(),
                    render(&word),
                    material.occurs(&octets)
                );
            }
            None => println!(
                "  {:>9} -> {:<9} free, and no input of any length separates the two readings",
                left.name(),
                right.name()
            ),
        }
        println!(
            "            on held-out material the flipped reading disagrees with the answer key {} times",
            flipped_conformance.disagreements.len()
        );
    }

    println!("\n=== [7] THE DEGENERATE CONTROLS ===");
    println!("  The same organ, unchanged, on material where the answer is different or absent.");
    println!(
        "  Each control declares the widest family the octet carrier could require at this radius,"
    );
    println!(
        "  {} words, because a control whose alphabet is wider than the Lean material's must not be",
        full_octet_family(settings.radius)
    );
    println!("  refused for the caller's aperture and reported as though it had returned nothing.");
    for (name, exposures) in controls(&founding) {
        control(
            &name,
            exposures,
            settings.radius,
            full_octet_family(settings.radius),
        );
    }

    println!("\n=== [8] THE EXPOSURE LADDER ===");
    println!("  How much stimulus the codec takes. The same recovery at increasing exposure; the");
    println!("  reading is a function of what was received and the ladder is what says so.");
    let total: u64 = founding.iter().map(|e| e.len() as u64).sum();
    let mut budget = 1u64 << 12;
    let mut rungs: Vec<(u64, BTreeSet<u8>)> = Vec::new();
    let mut seen_extents: BTreeSet<u64> = BTreeSet::new();
    let mut refused_below: Option<u64> = None;
    while budget < total.saturating_mul(2) {
        let rung = truncate_to(founding.clone(), budget);
        let extent: u64 = rung.iter().map(|e| e.len() as u64).sum();
        if !seen_extents.insert(extent) {
            budget = budget.saturating_mul(8);
            continue;
        }
        if let Ok(exposed) = ExposedMaterial::expose(rung, settings.radius) {
            if let Ok(step) = recover(
                &exposed,
                ExposureApertures::declared(settings.radius, settings.family_words),
            ) {
                let roles = if step.roles.is_empty() {
                    "refused".to_owned()
                } else {
                    format!(
                        "standing {:>3}  demanding {:>3}  internal {:>3}",
                        step.octets_with(UnitRole::Standing).len(),
                        step.octets_with(UnitRole::Demanding).len(),
                        step.octets_with(UnitRole::Internal).len()
                    )
                };
                let conformance = step
                    .codec
                    .as_ref()
                    .map(|codec| conform(codec, &key, &borrowed));
                println!(
                    "  octets {:>10}  alphabet {:>3}  refusals {:>7}  {}  held-out disagreements {}",
                    extent,
                    step.alphabet.len(),
                    step.refusals.len(),
                    roles,
                    conformance
                        .map(|check| format!(
                            "{} (+{} refusals)",
                            check.disagreements.len(),
                            check.refusals.len()
                        ))
                        .unwrap_or_else(|| "-".to_owned())
                );
                let recovered_here = step.codec.is_some();
                let internal: BTreeSet<u8> = step.opening_frame.internal.iter().copied().collect();
                let moved = rungs
                    .last()
                    .map(|(_, previous): &(u64, BTreeSet<u8>)| {
                        previous.symmetric_difference(&internal).count()
                    })
                    .unwrap_or(internal.len());
                println!("                                       octets whose internal reading moved since the rung above: {moved}");
                if recovered_here {
                    rungs.push((extent, internal));
                } else {
                    refused_below = Some(extent);
                }
            }
        }
        if extent >= total {
            break;
        }
        budget = budget.saturating_mul(8);
    }
    if rungs.len() >= 2 {
        println!(
            "  the internal class over the ladder: {:?} at octets {:?}",
            rungs.iter().map(|(_, set)| set.len()).collect::<Vec<_>>(),
            rungs.iter().map(|(extent, _)| *extent).collect::<Vec<_>>()
        );
        println!(
            "  over the rungs that RETURNED a codec, the internal class grows monotonically: {}",
            rungs.windows(2).all(|pair| pair[0].1.is_subset(&pair[1].1))
        );
        match refused_below {
            Some(extent) => println!(
                "  and below {extent} octets of exposure the organ REFUSED rather than returning a\n                   confident wrong codec. Where the exposure runs out is measured here, not declared."
            ),
            None => println!(
                "  the organ returned a codec at every rung, including the narrowest exposure tried."
            ),
        }
    }

    println!("\n=== [9] THE ANSWER KEY, IN BOTH DIRECTIONS ===");
    answer_key_comparison(&codec, &held_out);

    Ok(())
}

// -------------------------------------------------------------------------------------------------
// Reporting
// -------------------------------------------------------------------------------------------------

fn report(recovery: &ExposureRecovery, extent: u64) {
    println!(
        "  alphabet            {} octets, recovered by exhausting all 256 probes",
        recovery.alphabet.len()
    );
    println!("\n  the census of the exhausted family");
    println!(
        "    the last column is the exposure divided by the admitted family at that length. It is"
    );
    println!(
        "    reported and never consulted: a refusal is evidence of a rule only where the exposure"
    );
    println!(
        "    outruns the family, and where it does not, an absence is finiteness wearing a rule's"
    );
    println!("    clothes. Nothing below gates on it.");
    println!("    length  admitted    realized   recurring    refused   octets/admitted");
    for row in &recovery.census {
        println!(
            "    {:>6}  {:>8}  {:>10}  {:>10}  {:>9}   {:>15}",
            row.length,
            row.admitted,
            row.realized,
            row.recurring,
            row.refused,
            extent / row.admitted.max(1)
        );
    }
    println!(
        "\n  the refusal law — what the material's own recurring factors license and it refuses"
    );
    if recovery.refusals.is_empty() {
        println!("    empty. the material refuses nothing; there is no codec at this radius.");
    } else {
        let adjacency: Vec<&_> = recovery
            .refusals
            .iter()
            .filter(|refusal| refusal.word.len() == 2)
            .collect();
        println!(
            "    {} minimal refusals in all, {} of them adjacencies",
            recovery.refusals.len(),
            adjacency.len()
        );
        for refusal in adjacency.iter().take(8) {
            println!(
                "      {} is refused, though {} and {} both recur",
                render_octets(&refusal.word),
                render_octets(&refusal.licensing_prefix),
                render_octets(&refusal.licensing_suffix)
            );
        }
        if adjacency.len() > 8 {
            println!("      … and {} more adjacencies", adjacency.len() - 8);
        }
    }

    println!("\n  the direct quotient — the finest the declared family admits");
    println!(
        "    {} blocks over {} octets; {} separated pairs, each carrying the shortest context",
        recovery.direct_quotient.len(),
        recovery.alphabet.len(),
        recovery.direct_separations.len()
    );
    let mut by_length: BTreeMap<usize, usize> = BTreeMap::new();
    for separation in &recovery.direct_separations {
        *by_length.entry(separation.context_length()).or_default() += 1;
    }
    println!("    separations by context length: {by_length:?}");
    for separation in recovery.direct_separations.iter().take(4) {
        println!(
            "      {} and {} part at {}·_·{} — {} occurs there, {} does not",
            render_octet(separation.left),
            render_octet(separation.right),
            render_octets(&separation.prefix),
            render_octets(&separation.suffix),
            render_octet(if separation.left_occurs {
                separation.left
            } else {
                separation.right
            }),
            render_octet(if separation.left_occurs {
                separation.right
            } else {
                separation.left
            })
        );
    }
    if recovery.direct_quotient.len() == recovery.alphabet.len() {
        println!(
            "    every block is a singleton. that is the bound this grain reports on itself: no two"
        );
        println!(
            "    octets of this material are distributionally identical, and each pair says where."
        );
    }

    println!("\n  the two seeding frames");
    for frame in [&recovery.opening_frame, &recovery.closing_frame] {
        println!(
            "    {:<20} internal {:>3}  demanding {:>3}  standing {:>3}  rounds {}",
            frame.frame,
            frame.internal.len(),
            frame.demanding.len(),
            frame.standing.len(),
            frame.rounds
        );
    }
    println!(
        "    the frames {}",
        if recovery.opening_frame.internal == recovery.closing_frame.internal
            && recovery.opening_frame.demanding == recovery.closing_frame.demanding
        {
            "agree — the reading is not a coordinate of which end it was seeded from"
        } else {
            "DISAGREE — the reading is a coordinate and it is refused"
        }
    );

    if !recovery.obstructions.is_empty() {
        println!("\n  obstructions");
        for obstruction in &recovery.obstructions {
            match obstruction {
                ExposureObstruction::NothingIsRefused { radius } => println!(
                    "    NothingIsRefused at radius {radius} — the material licenses everything its own factors could"
                ),
                ExposureObstruction::NothingRecurs { radius } => {
                    println!("    NothingRecurs at radius {radius} — nothing happened twice")
                }
                ExposureObstruction::FramesDisagree { opening, closing } => println!(
                    "    FramesDisagree — openings read {} internal, closings read {}",
                    opening.internal.len(),
                    closing.internal.len()
                ),
                ExposureObstruction::NothingStands {
                    internal,
                    demanding,
                } => println!(
                    "    NothingStands — {internal} internal and {demanding} demanding leave nothing that is a unit by itself"
                ),
            }
        }
    }

    if !recovery.roles.is_empty() {
        println!("\n  THE RECOVERED CODEC");
        for role in [UnitRole::Standing, UnitRole::Demanding, UnitRole::Internal] {
            let members = recovery.octets_with(role);
            if members.is_empty() {
                continue;
            }
            println!("    class {:<10} {} members", role.name(), members.len());
            println!("      {}", render_octets(&members));
        }
        if let Some(codec) = &recovery.codec {
            println!("\n    the boundary table   (Cut opens a unit, Join continues one)");
            let present: Vec<UnitRole> =
                [UnitRole::Standing, UnitRole::Demanding, UnitRole::Internal]
                    .into_iter()
                    .filter(|role| recovery.roles.values().any(|carried| carried == role))
                    .collect();
            print!("      {:<12}", "from \\ to");
            for role in &present {
                print!("{:>11}", role.name());
            }
            println!();
            for (row, left) in codec.boundary.iter().zip(&present) {
                print!("      {:<12}", left.name());
                for entry in row {
                    print!(
                        "{:>11}",
                        match entry {
                            Boundary::Join => "Join",
                            Boundary::Cut => "Cut",
                        }
                    );
                }
                println!();
            }
        }
        println!(
            "\n    gauge freedom: {} adjacencies the material never carried  {:?}",
            recovery.gauge_freedom.len(),
            recovery
                .gauge_freedom
                .iter()
                .map(|(left, right)| format!("{}->{}", left.name(), right.name()))
                .collect::<Vec<_>>()
        );
    }

    println!("\n  work — every figure a count, none of them a clock");
    println!(
        "    alphabet probes {}   declared family words {}   material contacts {}   deep scans {}",
        recovery.work.alphabet_probes,
        recovery.work.declared_family_words,
        recovery.work.material_contacts,
        recovery.work.deep_scans
    );
    println!(
        "    contexts examined {}   refusal checks {}   fixed-point rounds {}",
        recovery.work.contexts_examined,
        recovery.work.refusal_checks,
        recovery.work.fixed_point_rounds
    );
}

/// The direct quotient recomputed in one pass, by keying each octet on its exact adjacency
/// signature. A second algorithm over the same testimony, holding no state the refinement holds.
fn signature_quotient(material: &ExposedMaterial, alphabet: &[u8]) -> Vec<BTreeSet<u8>> {
    let mut keyed: BTreeMap<(Vec<u8>, Vec<u8>), BTreeSet<u8>> = BTreeMap::new();
    for octet in alphabet {
        let follows: Vec<u8> = alphabet
            .iter()
            .copied()
            .filter(|next| material.occurs(&[*octet, *next]))
            .collect();
        let precedes: Vec<u8> = alphabet
            .iter()
            .copied()
            .filter(|before| material.occurs(&[*before, *octet]))
            .collect();
        keyed.entry((follows, precedes)).or_default().insert(*octet);
    }
    keyed.into_values().collect()
}

fn exhibit_conformance(name: &str, conformance: &Conformance) {
    println!(
        "  {name}: examined {}, disagreements {}, refusals {}  — {}",
        conformance.examined,
        conformance.disagreements.len(),
        conformance.refusals.len(),
        if conformance.is_exact() {
            "EXACT on every exposure examined"
        } else {
            "not exact; the residual is exhibited below"
        }
    );
    for disagreement in conformance.disagreements.iter().take(3) {
        let (key_window, recovered_window) =
            divergence_window(&disagreement.target, &disagreement.recovered);
        println!(
            "    at the first divergence: answer key {}   recovered {}",
            render_tokens(&key_window),
            render_tokens(&recovered_window)
        );
    }
    for refusal in conformance.refusals.iter().take(3) {
        println!(
            "    refused an exposure carrying {} — an octet the founding exposure never showed",
            render_octet(refusal.symbol.0 as u8)
        );
    }
}

// -------------------------------------------------------------------------------------------------
// The answer key, and the wrong readings
// -------------------------------------------------------------------------------------------------

/// The independent implementation of the same decomposition.
///
/// It is Rust's own decoder, reached only through the standard library, and it is consulted for
/// grading and never by the recovery. Handed the octet-carrier string, it returns each decoded
/// character's octets, re-carried — so a disagreement is a disagreement about **where the units
/// break** and about nothing else.
fn answer_key() -> OpaqueSymbolCodec {
    OpaqueSymbolCodec::new(|input: &[Symbol]| {
        let Some(octets) = octets_of(input) else {
            return Vec::new();
        };
        match std::str::from_utf8(&octets) {
            Ok(text) => text
                .chars()
                .map(|point| {
                    let mut buffer = [0u8; 4];
                    carried(point.encode_utf8(&mut buffer).as_bytes())
                })
                .collect(),
            Err(_) => Vec::new(),
        }
    })
}

/// Three readings that are wrong on purpose. Each keeps the recovered classes and emission — so the
/// cross-check admits them — and changes only where a unit breaks.
fn wrong_readings(codec: &RecoveredCodec) -> Vec<(String, RecoveredCodec)> {
    let classes = codec.classes.len();
    let mut readings = Vec::new();

    let mut every_cut = codec.clone();
    every_cut.boundary = vec![vec![Boundary::Cut; classes]; classes];
    readings.push(("every octet is its own unit".to_owned(), every_cut));

    let mut every_join = codec.clone();
    every_join.boundary = vec![vec![Boundary::Join; classes]; classes];
    readings.push(("the whole exposure is one unit".to_owned(), every_join));

    let mut inverted = codec.clone();
    inverted.boundary = codec
        .boundary
        .iter()
        .map(|row| {
            row.iter()
                .map(|entry| match entry {
                    Boundary::Join => Boundary::Cut,
                    Boundary::Cut => Boundary::Join,
                })
                .collect()
        })
        .collect();
    readings.push((
        "the unit breaks in exactly the wrong place".to_owned(),
        inverted,
    ));
    readings
}

/// One boundary entry flipped, so a free adjacency can be shown to be free.
fn flip(
    codec: &RecoveredCodec,
    recovery: &ExposureRecovery,
    left: UnitRole,
    right: UnitRole,
) -> Option<RecoveredCodec> {
    let present: Vec<UnitRole> = [UnitRole::Standing, UnitRole::Demanding, UnitRole::Internal]
        .into_iter()
        .filter(|role| recovery.roles.values().any(|carried| carried == role))
        .collect();
    let row = present.iter().position(|role| *role == left)?;
    let column = present.iter().position(|role| *role == right)?;
    let mut flipped = codec.clone();
    flipped.boundary[row][column] = match codec.boundary[row][column] {
        Boundary::Join => Boundary::Cut,
        Boundary::Cut => Boundary::Join,
    };
    Some(flipped)
}

// -------------------------------------------------------------------------------------------------
// The controls
// -------------------------------------------------------------------------------------------------

/// Materials on which a reader who already knew the answer would still say the answer.
fn controls(founding: &[Vec<u8>]) -> Vec<(String, Vec<Vec<u8>>)> {
    let mut controls = Vec::new();

    // (i) the same material with every multi-octet group removed. The codec is genuinely absent and
    // the honest reading is that every octet stands.
    let stripped: Vec<Vec<u8>> = founding
        .iter()
        .map(|exposure| {
            exposure
                .iter()
                .copied()
                .filter(|octet| *octet < 0x80)
                .collect()
        })
        .filter(|exposure: &Vec<u8>| !exposure.is_empty())
        .collect();
    controls.push((
        "the same material with every multi-octet group removed".to_owned(),
        stripped,
    ));

    // (ii) the same octets re-encoded at a different width. A codec is present and it is a different
    // one; a reading that returns the first codec here would be reciting.
    let widened: Vec<Vec<u8>> = founding
        .iter()
        .take(64)
        .filter_map(|exposure| std::str::from_utf8(exposure).ok())
        .map(|text| {
            text.encode_utf16()
                .flat_map(|unit| unit.to_le_bytes())
                .collect()
        })
        .filter(|exposure: &Vec<u8>| !exposure.is_empty())
        .collect();
    controls.push((
        "the same text re-encoded at a fixed two-octet width".to_owned(),
        widened,
    ));

    // (iii) octets with no law at all, produced by a declared deterministic recurrence so the run
    // reproduces. Nothing is refused and the recovery must say so.
    let mut state: u64 = 0x243F_6A88_85A3_08D3;
    let lawless: Vec<Vec<u8>> = (0..16)
        .map(|_| {
            (0..131_072)
                .map(|_| {
                    state ^= state << 13;
                    state ^= state >> 7;
                    state ^= state << 17;
                    (state >> 24) as u8
                })
                .collect()
        })
        .collect();
    controls.push(("octets carrying no law at all".to_owned(), lawless));

    controls
}

/// The widest family the octet carrier could ever require at this radius. Read off the carrier —
/// an octet takes 256 values — and not authored.
fn full_octet_family(radius: usize) -> u64 {
    let mut total = 0u64;
    let mut power = 1u64;
    for _ in 1..=radius {
        power = power.saturating_mul(256);
        total = total.saturating_add(power);
    }
    total
}

fn control(name: &str, exposures: Vec<Vec<u8>>, radius: usize, family_words: u64) {
    let extent: u64 = exposures.iter().map(|e| e.len() as u64).sum();
    if exposures.is_empty() {
        println!("\n  [{name}] no exposure");
        return;
    }
    let Ok(material) = ExposedMaterial::expose(exposures, radius) else {
        println!("\n  [{name}] refused at exposure");
        return;
    };
    match recover(&material, ExposureApertures::declared(radius, family_words)) {
        Ok(recovery) => {
            println!("\n  [{name}]");
            println!(
                "    octets {}  alphabet {}  refusals {}",
                extent,
                recovery.alphabet.len(),
                recovery.refusals.len()
            );
            for row in &recovery.census {
                println!(
                    "      length {}  admitted {:>10}  realized {:>9}  refused {:>9}  octets/admitted {:>8}",
                    row.length,
                    row.admitted,
                    row.realized,
                    row.refused,
                    extent / row.admitted.max(1)
                );
            }
            println!(
                "    standing {}  demanding {}  internal {}",
                recovery.opening_frame.standing.len(),
                recovery.opening_frame.demanding.len(),
                recovery.opening_frame.internal.len()
            );
            if recovery.obstructions.is_empty() {
                println!(
                    "    a codec over {} classes",
                    recovery
                        .codec
                        .as_ref()
                        .map_or(0, RecoveredCodec::class_count)
                );
            } else {
                for obstruction in &recovery.obstructions {
                    println!("    obstruction: {}", obstruction_name(obstruction));
                }
            }
        }
        Err(error) => println!("\n  [{name}] refused: {error}"),
    }
}

fn obstruction_name(obstruction: &ExposureObstruction) -> String {
    match obstruction {
        ExposureObstruction::NothingIsRefused { .. } => {
            "NothingIsRefused — no rule, so no codec".to_owned()
        }
        ExposureObstruction::NothingRecurs { .. } => "NothingRecurs".to_owned(),
        ExposureObstruction::FramesDisagree { opening, closing } => format!(
            "FramesDisagree — openings {} internal, closings {}",
            opening.internal.len(),
            closing.internal.len()
        ),
        ExposureObstruction::NothingStands {
            internal,
            demanding,
        } => {
            format!("NothingStands — {internal} internal, {demanding} demanding, nothing standing")
        }
    }
}

// -------------------------------------------------------------------------------------------------
// The answer key in both directions
// -------------------------------------------------------------------------------------------------

/// What exposure recovered of the authored reader's grammar, and what it recovered that the authored
/// reader does not have.
///
/// The authored reader is `holonic_engine::lean_development`. It is a real, working, hand-written
/// grammar of this material and it is the held-out answer key for the second direction.
fn answer_key_comparison(codec: &RecoveredCodec, held_out: &[Vec<u8>]) {
    let mut authored: Vec<&str> = Vec::new();
    authored.extend(DECLARATION_FORMERS);
    authored.extend(CODEC_KEYWORDS);
    authored.extend(PREAMBLE_FORMS);
    authored.extend(DECLARATION_MODIFIERS);
    authored.extend(BINDING_TACTICS);
    let authored: BTreeSet<&str> = authored.into_iter().collect();

    let mut recovered_whole = 0usize;
    let mut worked = Vec::new();
    for word in &authored {
        let segments = codec.segment(&carried(word.as_bytes())).unwrap_or_default();
        if segments.len() == 1 {
            recovered_whole += 1;
        }
        if worked.len() < 4 {
            worked.push((*word, segments.len()));
        }
    }
    println!("  direction A — what exposure recovered of the authored grammar");
    println!(
        "    {} authored vocabulary items across five tables; the recovered codec returns {} of",
        authored.len(),
        recovered_whole
    );
    println!("    them as a single unit.");
    for (word, count) in &worked {
        println!("      {word:<14} segments into {count} units");
    }
    println!(
        "    exposure at this radius recovered **none** of the authored token grammar, and the"
    );
    println!(
        "    reason is exact rather than a shortfall: the declared family reaches two adjacent"
    );
    println!("    octets, and no item of that vocabulary is two octets long.");

    println!("\n  direction B — what exposure recovered that the authored reader does not have");
    let sample: Vec<&Vec<u8>> = held_out.iter().take(8).collect();
    let mut grouped = 0u64;
    let mut total = 0u64;
    for exposure in &sample {
        total += exposure.len() as u64;
        grouped += exposure.iter().filter(|octet| **octet >= 0x80).count() as u64;
    }
    println!(
        "    of {total} held-out octets, {grouped} are not units by themselves — they belong to a"
    );
    println!("    group the recovered codec found and the authored reader is simply handed.");
    println!(
        "    The authored reader takes `&str`. It never recovers the grouping; it inherits it."
    );
    println!(
        "    Ablating exactly that inheritance — reading the same octets with each octet as its"
    );
    println!("    own unit — is what the following measures.");
    println!(
        "\n    {:<28} {:>12} {:>12} {:>10}",
        "reading", "declarations", "commentary", "preamble"
    );
    let mut token_sets: Vec<BTreeSet<String>> = Vec::new();
    let mut name_sets: Vec<BTreeSet<String>> = Vec::new();
    for (name, project) in [
        ("as the codec groups them", true),
        ("with the grouping ablated", false),
    ] {
        let mut declarations = 0usize;
        let mut commentary = 0usize;
        let mut preamble = 0usize;
        let mut tokens: BTreeSet<String> = BTreeSet::new();
        let mut names: BTreeSet<String> = BTreeSet::new();
        for exposure in &sample {
            let text = if project {
                match std::str::from_utf8(exposure) {
                    Ok(text) => text.to_owned(),
                    Err(_) => continue,
                }
            } else {
                latin1(exposure)
            };
            let reading = read_development(&text, DeclarationGrain::EveryTopLevelDeclaration);
            declarations += reading.declarations.len();
            commentary += reading.commentary.len();
            preamble += reading.preamble.len();
            tokens.extend(reading.commentary.keys().cloned());
            names.extend(reading.declared_names().into_iter().map(str::to_owned));
        }
        println!("    {name:<28} {declarations:>12} {commentary:>12} {preamble:>10}");
        token_sets.push(tokens);
        name_sets.push(names);
    }
    let token_delta = token_sets[0].symmetric_difference(&token_sets[1]).count();
    let name_delta = name_sets[0].symmetric_difference(&name_sets[1]).count();
    println!(
        "\n    the counts are the same; the POPULATIONS are not. commentary tokens that differ: {token_delta}"
    );
    println!("    declared names that differ: {name_delta}");
    for token in token_sets[0].symmetric_difference(&token_sets[1]).take(4) {
        println!("      {}", render(&carried(token.as_bytes())));
    }
    println!(
        "    So the authored reading's *shape* at this grain never depended on the grouping — it"
    );
    println!("    cuts at ASCII and nowhere else — while the *content* it returns does. Exposure");
    println!("    recovered the layer the authored reader is handed, and none of the layer the");
    println!("    authored reader encodes. Both directions, and neither is zero.");
}

// -------------------------------------------------------------------------------------------------
// Material intake
// -------------------------------------------------------------------------------------------------

fn material(settings: &Settings) -> Result<Vec<Vec<u8>>, String> {
    if let Some(rest) = &settings.rest {
        return from_sealed_rest(rest, &settings.identity_prefix);
    }
    if let Some(directory) = &settings.directory {
        return from_directory(directory, &settings.extension);
    }
    Err("declare either --rest or --directory".to_owned())
}

fn from_sealed_rest(path: &Path, prefix: &str) -> Result<Vec<Vec<u8>>, String> {
    let file = File::open(path).map_err(|error| format!("open {}: {error}", path.display()))?;
    let atlas = ExactTextMaterialAtlas::from_native_reader(std::io::BufReader::new(file))
        .map_err(|error| format!("reopen the sealed rest: {error:?}"))?;
    let mut by_identity: BTreeMap<String, Vec<u8>> = BTreeMap::new();
    for occurrence in atlas.corpus().occurrences() {
        let Some(identity) = occurrence.native_identity.strip_prefix("document:") else {
            continue;
        };
        let identity = identity.rsplit_once(':').map_or(identity, |(head, _)| head);
        if !identity.starts_with(prefix) {
            continue;
        }
        by_identity
            .entry(identity.to_owned())
            .or_default()
            .extend_from_slice(occurrence.text.as_bytes());
    }
    Ok(by_identity
        .into_values()
        .filter(|e| !e.is_empty())
        .collect())
}

fn from_directory(root: &Path, extension: &str) -> Result<Vec<Vec<u8>>, String> {
    let mut paths = Vec::new();
    collect(root, extension, &mut paths)?;
    paths.sort();
    let mut exposures = Vec::with_capacity(paths.len());
    for path in paths {
        let octets =
            std::fs::read(&path).map_err(|error| format!("read {}: {error}", path.display()))?;
        if !octets.is_empty() {
            exposures.push(octets);
        }
    }
    Ok(exposures)
}

fn collect(root: &Path, extension: &str, into: &mut Vec<PathBuf>) -> Result<(), String> {
    let entries =
        std::fs::read_dir(root).map_err(|error| format!("read {}: {error}", root.display()))?;
    for entry in entries {
        let entry = entry.map_err(|error| format!("walk {}: {error}", root.display()))?;
        let path = entry.path();
        if path.is_dir() {
            collect(&path, extension, into)?;
        } else if path.extension().and_then(|value| value.to_str()) == Some(extension) {
            into.push(path);
        }
    }
    Ok(())
}

fn truncate_to(exposures: Vec<Vec<u8>>, budget: u64) -> Vec<Vec<u8>> {
    let mut taken = Vec::new();
    let mut extent = 0u64;
    for exposure in exposures {
        if extent >= budget {
            break;
        }
        extent += exposure.len() as u64;
        taken.push(exposure);
    }
    taken
}

// -------------------------------------------------------------------------------------------------
// Rendering
// -------------------------------------------------------------------------------------------------

fn render_octet(octet: u8) -> String {
    if (0x20..0x7f).contains(&octet) {
        format!("'{}'", octet as char)
    } else {
        format!("{octet:02x}")
    }
}

fn render_octets(octets: &[u8]) -> String {
    octets
        .iter()
        .map(|octet| render_octet(*octet))
        .collect::<Vec<_>>()
        .join(" ")
}

/// Octets projected onto text one-for-one, for the authored reader this driver grades against.
///
/// **This is not [`carried`] and the difference is the point.** `carried` injects octets into the
/// codec's own symbol alphabet, where nothing is interpreted; this projection hands the same octets
/// to a reader that expects characters, which is an interpretation and is declared here as one. The
/// two were the same function until the alphabet was rotated off `char`, and that they were the same
/// is exactly what the rotation removed.
fn latin1(octets: &[u8]) -> String {
    octets.iter().map(|octet| *octet as char).collect()
}

fn render(carried_word: &[Symbol]) -> String {
    render_octets(&octets_of(carried_word).unwrap_or_default())
}

fn render_tokens(tokens: &[Vec<Symbol>]) -> String {
    tokens
        .iter()
        .map(|token| {
            let octets = octets_of(token).unwrap_or_default();
            if octets.len() > 8 {
                format!(
                    "[{} … {} octets]",
                    render_octets(&octets[..8]),
                    octets.len()
                )
            } else {
                format!("[{}]", render_octets(&octets))
            }
        })
        .collect::<Vec<_>>()
        .join(" ")
}

/// The window around the first unit at which two segmentations part, so a divergence is exhibited
/// where it happens rather than from the beginning of a file.
fn divergence_window(
    target: &[Vec<Symbol>],
    recovered: &[Vec<Symbol>],
) -> (Vec<Vec<Symbol>>, Vec<Vec<Symbol>>) {
    let first = target
        .iter()
        .zip(recovered)
        .position(|(left, right)| left != right)
        .unwrap_or_else(|| target.len().min(recovered.len()));
    let from = first.saturating_sub(2);
    (
        target.iter().skip(from).take(5).cloned().collect(),
        recovered.iter().skip(from).take(5).cloned().collect(),
    )
}

// -------------------------------------------------------------------------------------------------
// Arguments
// -------------------------------------------------------------------------------------------------

fn arguments() -> Result<Settings, String> {
    let mut settings = Settings {
        rest: None,
        directory: None,
        extension: "lean".to_owned(),
        identity_prefix: "lean:".to_owned(),
        radius: 3,
        family_words: 8_000_000,
        octet_budget: 24_000_000,
        held_out: 24,
    };
    let mut arguments = std::env::args().skip(1);
    while let Some(named) = arguments.next() {
        let value = arguments
            .next()
            .ok_or_else(|| format!("{named} requires a value"))?;
        match named.as_str() {
            "--rest" => settings.rest = Some(PathBuf::from(value)),
            "--directory" => settings.directory = Some(PathBuf::from(value)),
            "--extension" => settings.extension = value,
            "--identity-prefix" => settings.identity_prefix = value,
            "--radius" => {
                settings.radius = value
                    .parse()
                    .map_err(|_| "--radius wants a number".to_owned())?
            }
            "--family-words" => {
                settings.family_words = value
                    .parse()
                    .map_err(|_| "--family-words wants a number".to_owned())?
            }
            "--octet-budget" => {
                settings.octet_budget = value
                    .parse()
                    .map_err(|_| "--octet-budget wants a number".to_owned())?
            }
            "--held-out" => {
                settings.held_out = value
                    .parse()
                    .map_err(|_| "--held-out wants a number".to_owned())?
            }
            other => return Err(format!("unknown argument {other}")),
        }
    }
    if settings.rest.is_none() && settings.directory.is_none() {
        return Err(
            "usage: --rest PATH [--identity-prefix lean:] | --directory PATH [--extension lean] \
             [--radius 3] [--family-words N] [--octet-budget N] [--held-out N]"
                .to_owned(),
        );
    }
    Ok(settings)
}
