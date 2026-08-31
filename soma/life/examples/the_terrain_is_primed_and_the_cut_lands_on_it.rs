//! THE TERRAIN IS PRIMED AND THE CUT LANDS ON IT — the segmentation, over standing it can touch.
//!
//! ```text
//! cargo run --release -p life --example the_terrain_is_primed_and_the_cut_lands_on_it -- \
//!   --priming <file> --foreign <file> --prime-words 200000 --read-words 1200
//! ```
//!
//! # The occasion, and it is a withdrawal
//!
//! `the_thoughts_are_returned_as_text` returned the body's segmentation of prose and it was
//! useless: cuts mid-word at every entry, `faces_founded` **zero** across 59,734 crossings, and at a
//! fixed span every thought a multiple of the span. The record written from it concluded that
//! `thought_completed` *"is not the founding cut"*.
//!
//! **That conclusion is withdrawn here, and the cut organ is exonerated.** `perceive_grain` is
//! byte-identical between this tree and the frozen laboratory at `a07ff376` — measured, whole
//! function, character for character. Nothing about the cut regressed. What regressed is the
//! driver, and it is one line:
//!
//! ```text
//!   let standing = vec![0u32; cells()];
//! ```
//!
//! The laboratory's reading driver primed that pool with a corpus first and delivered **one word
//! per arrival**; its cuts then landed on the material's own joints. Every live driver that runs the
//! body over text hands it an all-zero standing chart — `the_thoughts_are_returned_as_text`,
//! `the_worldline_coheres_or_it_does_not`, `the_orbit_closes_or_the_grain_admits_a_stroke`,
//! `the_rest_advances_or_the_model_is_frozen`. **A cut that lands on terrain touches has nothing to
//! land on when there is no terrain**, and the zero foundings were saying exactly that.
//!
//! # What this driver does
//!
//! One priming corpus is delivered word by word into a body's own region. That region — the
//! deposited terrain, not a copy of anything emitted — becomes the **standing** chart of a second
//! body, which then reads a lane it did not prime on. The same lane is read twice, over bare
//! standing and over primed standing, and the two segmentations are printed as text beside each
//! other.
//!
//! Two lanes, because the interesting comparison is not primed-vs-bare alone:
//!
//! ```text
//!   KNOWN     a stretch of the priming corpus itself — terrain the body stood
//!   FOREIGN   prose the priming corpus never carried
//! ```
//!
//! # The falsifier, stated before the run
//!
//! **If priming moves no cut position on either lane, the terrain does not condition the cut and
//! this whole reading is refuted.** A driver whose control cannot fail is the defect this repository
//! convicts by name, so the bare-terrain flight is run on the identical lane with an identical body
//! and differs in the standing chart alone.
//!
//! # Bars
//!
//! No count here gates anything. Nothing is scored, ranked, or thresholded. The word grain splits on
//! whitespace and keeps every non-empty run — **no length filter**, because a length filter is an
//! authored level and the laboratory's own `words_of` carried one. The priming and reading extents
//! are caller-declared apertures with no default authored inside an organ; they bound how much
//! material is delivered and decide nothing about what the body does with it.

use std::path::PathBuf;

use body::channel::LineageChannel;
use body::manifold::{ErosBody, ENCLOSURE_WORDS};
use body::num::Cog;
use life::eros_rest::{ErosRest, MediumBlock, OrganRest};

const AXIS: i64 = 1 << 8;
const SEED: &[u8] = b"the terrain is primed and the cut lands on it";
const DRIVE: u32 = 100;

fn cells() -> usize {
    (AXIS * AXIS) as usize * 16
}

/// Split on whitespace, keep every non-empty run. Nothing else — a length filter here would be an
/// authored level deciding what the body is allowed to receive.
fn words_of(octets: &[u8]) -> Vec<Vec<u8>> {
    octets
        .split(|byte| byte.is_ascii_whitespace())
        .filter(|word| !word.is_empty())
        .map(<[u8]>::to_vec)
        .collect()
}

/// Project Gutenberg sources carry a header the material did not author. Where the marker is
/// present the header is skipped; where it is absent nothing is skipped and the whole file stands.
fn corpus_words(octets: Vec<u8>) -> Vec<Vec<u8>> {
    let start = octets
        .windows(9)
        .position(|window| window == b"*** START")
        .map(|at| at + 600)
        .unwrap_or(0);
    words_of(&octets[start.min(octets.len())..])
}

/// What one flight returned: where it cut, and what it founded while doing so.
struct Flight {
    cuts: Vec<bool>,
    faces: u64,
    founded: u64,
    thoughts: usize,
}

/// Deliver `lane` word by word to a body standing on `standing`, and return where it cut.
fn fly(standing: &[u32], lane: &[Vec<u8>]) -> Flight {
    let mut own = vec![0u32; cells()];
    let mut carrier = vec![0u32; 64 * ENCLOSURE_WORDS];
    let mut eyes = ErosBody::over(standing, &mut own, AXIS, SEED, 1 << 20, &mut carrier);
    let mut flight = Flight {
        cuts: Vec::with_capacity(lane.len()),
        faces: 0,
        founded: 0,
        thoughts: 0,
    };
    for word in lane {
        let perception = eyes.perceive(word, DRIVE);
        flight.faces += u64::from(perception.faces);
        flight.founded += u64::from(perception.faces_founded);
        flight.cuts.push(perception.thought_completed);
        if perception.thought_completed {
            flight.thoughts += 1;
        }
        if eyes.resource_refused() {
            break;
        }
    }
    flight
}

/// Deliver the priming corpus and RETURN THE TERRAIN IT DEPOSITED. This is the whole repair: the
/// own region a body wrote is the standing chart the next body reads.
fn prime(words: &[Vec<u8>]) -> (Vec<u32>, u64, u64) {
    let bare = vec![0u32; cells()];
    let mut own = vec![0u32; cells()];
    let mut carrier = vec![0u32; 64 * ENCLOSURE_WORDS];
    let (mut faces, mut founded) = (0u64, 0u64);
    {
        let mut eyes = ErosBody::over(&bare, &mut own, AXIS, SEED, 1 << 20, &mut carrier);
        for word in words {
            let perception = eyes.perceive(word, DRIVE);
            faces += u64::from(perception.faces);
            founded += u64::from(perception.faces_founded);
            if eyes.resource_refused() {
                break;
            }
        }
    }
    (own, faces, founded)
}

/// Render a cut pattern over its words as `[segment] [segment] …` — the artifact itself.
fn bracket(words: &[Vec<u8>], cuts: &[bool], from: usize, upto: usize) -> String {
    let upto = upto.min(words.len()).min(cuts.len());
    let mut out = String::from("[");
    for at in from..upto {
        if cuts[at] && at > from {
            out.push_str("] [");
        }
        if !out.ends_with('[') {
            out.push(' ');
        }
        out.push_str(&String::from_utf8_lossy(&words[at]));
    }
    out.push(']');
    out
}

struct Settings {
    priming: PathBuf,
    foreign: PathBuf,
    prime_words: usize,
    read_words: usize,
    known_at: usize,
    /// Seal the primed terrain to this path and stop. The next process resumes from it.
    deposit: Option<PathBuf>,
    /// Resume from a sealed terrain instead of priming. **This is the later current across a
    /// process boundary**: the terrain this run stands on was deposited by a run that has exited.
    resume: Option<PathBuf>,
}

fn arguments() -> Result<Settings, String> {
    let mut settings = Settings {
        priming: PathBuf::from("/home/b/Workspaces/laboratory/src/soma/diet/websters1913.txt"),
        foreign: PathBuf::from("/home/b/Workspaces/laboratory/src/soma/diet/alice.txt"),
        prime_words: 200_000,
        read_words: 1_200,
        known_at: 800_000,
        deposit: None,
        resume: None,
    };
    let mut arguments = std::env::args().skip(1);
    while let Some(named) = arguments.next() {
        let value = arguments
            .next()
            .ok_or_else(|| format!("{named} requires a value"))?;
        let number = |what: &str| {
            value
                .parse::<usize>()
                .map_err(|_| format!("{what} wants a number"))
        };
        match named.as_str() {
            "--priming" => settings.priming = PathBuf::from(&value),
            "--foreign" => settings.foreign = PathBuf::from(&value),
            "--prime-words" => settings.prime_words = number("--prime-words")?,
            "--read-words" => settings.read_words = number("--read-words")?,
            "--known-at" => settings.known_at = number("--known-at")?,
            "--deposit" => settings.deposit = Some(PathBuf::from(&value)),
            "--resume" => settings.resume = Some(PathBuf::from(&value)),
            other => return Err(format!("unknown argument {other}")),
        }
    }
    Ok(settings)
}

fn rule(title: &str) {
    println!("\n{}", "=".repeat(98));
    println!("{title}");
    println!("{}", "=".repeat(98));
}

fn main() {
    if let Err(error) = run() {
        eprintln!("REFUSED: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let settings = arguments()?;

    let priming_octets = std::fs::read(&settings.priming)
        .map_err(|error| format!("priming corpus {}: {error}", settings.priming.display()))?;
    let foreign_octets = std::fs::read(&settings.foreign)
        .map_err(|error| format!("foreign corpus {}: {error}", settings.foreign.display()))?;

    let priming_all = corpus_words(priming_octets);
    let foreign_all = corpus_words(foreign_octets);
    if priming_all.is_empty() || foreign_all.is_empty() {
        return Err("a declared corpus carries no word".to_owned());
    }

    let priming: Vec<Vec<u8>> = priming_all
        .iter()
        .take(settings.prime_words)
        .cloned()
        .collect();

    // KNOWN is a stretch of the priming corpus the body actually stood on — inside the delivered
    // prefix, never past it, or it would not be known and the label would be a lie.
    let known_at = settings
        .known_at
        .min(priming.len().saturating_sub(settings.read_words));
    let known: Vec<Vec<u8>> = priming
        .iter()
        .skip(known_at)
        .take(settings.read_words)
        .cloned()
        .collect();
    let foreign: Vec<Vec<u8>> = foreign_all
        .iter()
        .take(settings.read_words)
        .cloned()
        .collect();

    rule("THE TERRAIN IS PRIMED AND THE CUT LANDS ON IT");
    println!(
        "  priming corpus   {}   {} words delivered of {} carried",
        settings.priming.display(),
        priming.len(),
        priming_all.len()
    );
    println!(
        "  foreign corpus   {}   {} words carried",
        settings.foreign.display(),
        foreign_all.len()
    );
    println!(
        "  KNOWN lane       {} words from the delivered priming, beginning at word {known_at}",
        known.len()
    );
    println!(
        "  FOREIGN lane     {} words the priming never carried",
        foreign.len()
    );
    println!("  axis {AXIS}   one arrival = ONE WORD   drive {DRIVE}");

    // ★ THE LATER CURRENT, ACROSS A PROCESS. With `--resume` the terrain this run stands on was
    // deposited by a run that has already exited: the sealed carriers cross through `ErosRest`'s
    // wire as exact words, come back through `seal`'s own refusals, and are handed straight back as
    // `standing`. A run that begins here did not start at an origin.
    let (terrain, prime_faces, prime_founded) = if let Some(from) = settings.resume.as_ref() {
        let octets = std::fs::read(from)
            .map_err(|error| format!("resume from {}: {error}", from.display()))?;
        let resumed = ErosRest::from_native_bytes(&octets)
            .map_err(|refusal| format!("the sealed terrain refused to mount: {refusal:?}"))?
            .resume()
            .map_err(|refusal| format!("the mounted body refused to resume: {refusal:?}"))?;
        let carried = resumed
            .carrier("own")
            .ok_or_else(|| "the sealed body carries no region named `own`".to_owned())?
            .to_vec();
        println!(
            "  RESUMED from {} — {} octets, {} standing words, and this run primed NOTHING",
            from.display(),
            octets.len(),
            carried.iter().filter(|word| **word != 0).count()
        );
        (carried, 0, 0)
    } else {
        prime(&priming)
    };

    if let Some(to) = settings.deposit.as_ref() {
        // Seal and stop. The frame is the body's own genesis channel; the terrain crosses as exact
        // words, never a digest, because a digest cannot exhibit which word moved.
        let sealed = ErosRest::seal(
            LineageChannel::from_located_first_difference((Cog::lit(3), Cog::lit(1))),
            vec![MediumBlock {
                carrier: "own".to_owned(),
                words: terrain.clone(),
            }],
            vec![OrganRest {
                organ: "terrain".to_owned(),
                bytes: SEED.to_vec(),
            }],
        )
        .map_err(|refusal| format!("the terrain refused to seal: {refusal:?}"))?;
        let octets = sealed
            .encode_native_bytes()
            .map_err(|refusal| format!("the sealed terrain refused to encode: {refusal:?}"))?;
        std::fs::write(to, &octets)
            .map_err(|error| format!("deposit to {}: {error}", to.display()))?;
        println!(
            "  DEPOSITED {} octets to {} — {} standing words non-zero.",
            octets.len(),
            to.display(),
            terrain.iter().filter(|word| **word != 0).count()
        );
        println!("  This process now exits. Run again with --resume to stand on it.");
        return Ok(());
    }
    let standing_places = terrain.iter().filter(|word| **word != 0).count();
    rule("THE PRIMING");
    println!(
        "  faces crossed {prime_faces} · faces FOUNDED {prime_founded} · standing words non-zero \
         {standing_places} of {}",
        terrain.len()
    );
    if standing_places == 0 {
        return Err(
            "the priming deposited nothing — the terrain is still bare and the comparison below \
             would be two identical flights"
                .to_owned(),
        );
    }

    let bare = vec![0u32; cells()];
    let mut any_moved = false;

    for (name, lane) in [("KNOWN", &known), ("FOREIGN", &foreign)] {
        let over_bare = fly(&bare, lane);
        let over_primed = fly(&terrain, lane);
        let common = over_bare.cuts.len().min(over_primed.cuts.len());
        let moved = (0..common)
            .filter(|at| over_bare.cuts[*at] != over_primed.cuts[*at])
            .count();
        if moved > 0 {
            any_moved = true;
        }

        rule(&format!(
            "{name} — the same lane, read over bare standing and over primed standing"
        ));
        println!(
            "  bare      cuts {:>5}   faces {:>8}   founded {:>8}",
            over_bare.thoughts, over_bare.faces, over_bare.founded
        );
        println!(
            "  primed    cuts {:>5}   faces {:>8}   founded {:>8}",
            over_primed.thoughts, over_primed.faces, over_primed.founded
        );
        println!("  positions the priming MOVED: {moved} of {common}");

        for from in [40usize, 400, 900] {
            if from + 28 > common {
                continue;
            }
            println!("\n  ── words {from}..{} ──", from + 28);
            println!(
                "    bare    {}",
                bracket(lane, &over_bare.cuts, from, from + 28)
            );
            println!(
                "    primed  {}",
                bracket(lane, &over_primed.cuts, from, from + 28)
            );
        }
    }

    rule("THE FALSIFIER");
    if !any_moved {
        // **A falsifier that prints and exits zero is a check that cannot fail.** The first form of
        // this driver printed `REFUTED` and returned `Ok(())`, so a refuted run and a confirmed run
        // were indistinguishable to anything reading the exit status — which is the defect
        // the universal owner catalog names as the one to avoid, committed in the driver
        // written to demonstrate a falsifier. The refusal now leaves through the same door the
        // driver's other refusals do.
        return Err(
            "REFUTED. The priming moved no cut position on either lane. The standing terrain does \
             not condition the cut, and the reading this driver was built to take does not exist. \
             Nothing here may be cited as conditioning."
                .to_owned(),
        );
    }
    println!("  The priming moved cut positions. The standing terrain conditions the cut, and");
    println!("  the segmentation is a reading of what the body has stood on — not of how the");
    println!("  arrivals were chunked.");
    Ok(())
}
