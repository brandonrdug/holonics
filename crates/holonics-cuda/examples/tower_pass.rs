//! **The gated tower's training pass on the card** (`holonics_cuda::hnn::tower`; #404, #76).
//!
//! - `tower_pass parity CLASSES CLASSES_SHA KEYS KEYS_SHA WIDTH MODES CONTACTS LEVELS STREAMS
//!   SECTION SECTIONS RATE_BITS [NEWS_BITS NEWS_RADIX [FIRST]] [participating | mutual | passage]`:
//!   founds the gated tower (rectifying, on both turn ladders) on the keys, its levels on the news
//!   clock `NewsClock::above(NEWS_BITS, NEWS_RADIX, FIRST)` when one is named (`FIRST` 1 when it is
//!   not; the passage needs a clock, the mutual contact none), with participation over `SECTION`
//!   joined after it (`Tower::founded_participation`, one head a rung) when `participating` is, or with the
//!   mutual contact joined at `β = 2^(−2)` (`Tower::join_mutual_contact`) when `mutual` is, or with
//!   the passage joined last (`Tower::join_passage`) when `passage` is, and runs
//!   `SECTIONS` sections of the class passage (two bytes a class, big-endian,
//!   alphabet 257) host against card in lockstep. Each section's opening read is compared face by
//!   face and the whole summed covector entry by entry, then both learners take the section (the
//!   host's through `HostPass`, the card's through `TowerCard`) and their texts and continuing
//!   states are compared. Prints one `TOWER_PARITY` line a section and `TOWER_PARITY_DONE`.
//! - `tower_pass parity-state STATE STATE_SHA CLASSES CLASSES_SHA OCTETS STREAMS SECTION [SECTIONS]`:
//!   the same lockstep from a saved learner (`TowerLearner::to_text`, any face the card carries,
//!   the pair face among them) over a class passage of `OCTETS` (1 or 2, big-endian) bytes a class,
//!   every stream from rest; without `SECTIONS`, the whole passage. Prints, beside the lines above,
//!   `TOWER_PARITY_SHA` with both learners' SHA-256 after the last section.
//! - `tower_pass parity-units STATE STATE_SHA UNITS UNITS_SHA TEXT TEXT_SHA STREAMS SECTION [SECTIONS]`:
//!   the same from a learner trained on founded units (`train-unit-tower`,
//!   `train-unit-pumped-tower`, `train-unit-pair-pumped-tower`), its passage the text read in those units (`Units::parse`), as the
//!   trainer reads it.
//! - `tower_pass train complete-language ARGS…`: a `complete-language` tower training command
//!   (`train-gated-tower-classes`, `train-scaled-tower-classes`, `train-two-ladder-tower-classes`,
//!   `train-two-ladder-news-tower-classes`, `train-two-ladder-participating-tower-classes`, `train-two-ladder-news-participating-tower-classes`, `train-two-ladder-mutual-tower-classes`, `train-two-ladder-news-passage-tower-classes`, `train-two-ladder-stacked-news-passage-tower-classes`, or `train-unit-tower`, `train-unit-pumped-tower` or
//!   `train-unit-pair-pumped-tower` on the founded units) with every section's forward and reverse on the
//!   card; its saved learner is the host's (`TOWER_STATE`'s digest names it). A tower the card
//!   does not carry is refused at its first section (`TowerCard::admits`), never read on the host.
//! - `tower_pass release complete-language release-tower-classes ARGS…`: the class release with
//!   every prompt's read and every drawn class's step on the card, the prompts drawing together.
//! - `tower_pass read complete-language read-tower-race ARGS…`: the race's readings of a rested
//!   learner, its covector and codes read on the card.
#![allow(dead_code, clippy::disallowed_methods, clippy::disallowed_types, reason = "explicit exterior CLI file/process boundary")]

#[path = "../../holonics/examples/solenoidal_alpha.rs"]
mod exterior;

use holonics::hnn::tower::realization::{HostPass, PassRealization, Slot};
use holonics::hnn::tower::{face_code, ContactLaw, NewsClock, Tower, TowerDeclaration, TowerLearner, TowerState, TurnLadder};
use holonics::hnn::units::Units;
use holonics_cuda::hnn::{Card, TowerCard};
use std::error::Error;
use std::io::Write;
use std::process::{Command, Stdio};
use std::time::Instant;

type Result<T> = std::result::Result<T, Box<dyn Error>>;

/// A file read whole, refused unless its SHA-256 is the declared one (`sha256sum`, the exterior's).
fn pinned(path: &str, sha: &str) -> Result<Vec<u8>> {
    let output = Command::new("sha256sum").arg(path).output()?;
    let digest = std::str::from_utf8(&output.stdout)?.split_whitespace().next().unwrap_or("").to_owned();
    if !output.status.success() || digest != sha {
        return Err(format!("{path}: sha256 {digest} is not the declared {sha}").into());
    }
    Ok(std::fs::read(path)?)
}

fn count(s: &str) -> Result<usize> {
    Ok(s.parse::<usize>()?)
}

/// The SHA-256 of `bytes` (`sha256sum`, the exterior's).
fn digest(bytes: &[u8]) -> Result<String> {
    let mut process = Command::new("sha256sum").stdin(Stdio::piped()).stdout(Stdio::piped()).spawn()?;
    process.stdin.take().ok_or("sha256sum's input")?.write_all(bytes)?;
    let output = process.wait_with_output()?;
    let digest = std::str::from_utf8(&output.stdout)?.split_whitespace().next().unwrap_or("").to_owned();
    if !output.status.success() || digest.len() != 64 {
        return Err("sha256sum failed".into());
    }
    Ok(digest)
}

fn parity(args: &[String]) -> Result<()> {
    const USAGE: &str = "parity CLASSES CLASSES_SHA KEYS KEYS_SHA WIDTH MODES CONTACTS LEVELS STREAMS SECTION SECTIONS RATE_BITS [NEWS_BITS NEWS_RADIX [FIRST]] [participating | mutual | passage]";
    if args.len() < 12 {
        return Err(USAGE.into());
    }
    let word = args.last().filter(|w| w.parse::<u32>().is_err()).map(String::as_str);
    let numbers = &args[12..args.len() - usize::from(word.is_some())];
    let clock = match numbers {
        [] => None,
        [bits, radix] => Some(NewsClock::new(bits.parse()?, radix.parse()?)?),
        [bits, radix, first] => Some(NewsClock::above(bits.parse()?, radix.parse()?, first.parse()?)?),
        _ => return Err(USAGE.into()),
    };
    let (participating, mutual, passage) = (word == Some("participating"), word == Some("mutual"), word == Some("passage"));
    if (word.is_some() && !(participating || mutual || passage)) || (mutual && clock.is_some()) || (passage && clock.is_none()) {
        return Err(USAGE.into());
    }
    let bytes = pinned(&args[0], &args[1])?;
    let keys = pinned(&args[2], &args[3])?;
    if bytes.len() % 2 != 0 {
        return Err("a class file holds two bytes a class".into());
    }
    let classes: Vec<usize> = bytes.chunks(2).map(|b| u16::from_be_bytes([b[0], b[1]]) as usize).collect();
    let alphabet = 257;
    if classes.iter().any(|&c| c >= alphabet) {
        return Err("a class outside the declared alphabet".into());
    }
    let declaration = TowerDeclaration {
        alphabet,
        width: count(&args[4])?,
        modes: count(&args[5])?,
        contacts: count(&args[6])?,
        levels: count(&args[7])?,
        gated: true,
        turned: false,
        pumped: false,
        contact: ContactLaw::Rectifying,
    };
    let (streams, section, sections) = (count(&args[8])?, count(&args[9])?, count(&args[10])?);
    let rate_bits: u32 = args[11].parse()?;
    let chunk = classes.len() / streams;
    if streams == 0 || section == 0 || sections == 0 || (chunk - 1) / section < sections {
        return Err("the passage must hold the declared sections in every stream".into());
    }
    let mut tower = Tower::found_on(declaration, &keys, TurnLadder::Both)?;
    if let Some(clock) = clock {
        tower.join_news(clock)?;
    }
    if participating {
        let founded = tower.founded_participation(section)?;
        println!("TOWER_PARTICIPATION section={} beta_shift={} heads={:?}", founded.section, founded.beta_shift, founded.heads);
        tower.join_participation(founded)?;
    }
    if mutual {
        tower.join_mutual_contact(2)?;
        println!("TOWER_MUTUAL_CONTACT shift=2");
    }
    if passage {
        tower.join_passage()?;
        println!("TOWER_PASSAGE first_clocked_level={}", tower.news().map_or(0, |c| c.first()));
    }
    let mut host = TowerLearner::new(tower.clone(), rate_bits);
    let mut carded = TowerLearner::new(tower, rate_bits);
    lockstep(&mut host, &mut carded, &classes, streams, section, sections)
}

fn parity_state(args: &[String]) -> Result<()> {
    if args.len() != 7 && args.len() != 8 {
        return Err("parity-state STATE STATE_SHA CLASSES CLASSES_SHA OCTETS STREAMS SECTION [SECTIONS]".into());
    }
    let state = pinned(&args[0], &args[1])?;
    let bytes = pinned(&args[2], &args[3])?;
    let classes: Vec<usize> = match count(&args[4])? {
        1 => bytes.iter().map(|&b| b as usize).collect(),
        2 if bytes.len() % 2 == 0 => bytes.chunks(2).map(|b| u16::from_be_bytes([b[0], b[1]]) as usize).collect(),
        _ => return Err("a class passage holds one or two bytes a class".into()),
    };
    parity_from(&state, &classes, &args[5..])
}

fn parity_units(args: &[String]) -> Result<()> {
    if args.len() != 8 && args.len() != 9 {
        return Err("parity-units STATE STATE_SHA UNITS UNITS_SHA TEXT TEXT_SHA STREAMS SECTION [SECTIONS]".into());
    }
    let state = pinned(&args[0], &args[1])?;
    let units = Units::from_text(std::str::from_utf8(&pinned(&args[2], &args[3])?)?).map_err(|e| e.to_string())?;
    let classes: Vec<usize> = units.parse(&pinned(&args[4], &args[5])?).map_err(|e| e.to_string())?.into_iter().map(|u| u as usize).collect();
    println!("TOWER_PARITY_UNITS units={} classes={}", units.len(), classes.len());
    parity_from(&state, &classes, &args[6..])
}

/// The lockstep from the saved learner `state` over `classes`, `args` being `STREAMS SECTION
/// [SECTIONS]`, and both learners' SHA-256 after the last section.
fn parity_from(state: &[u8], classes: &[usize], args: &[String]) -> Result<()> {
    let host = TowerLearner::from_text(std::str::from_utf8(state)?)?;
    if classes.iter().any(|&c| c >= host.tower.declaration.alphabet) {
        return Err("a class outside the learner's alphabet".into());
    }
    let (streams, section) = (count(&args[0])?, count(&args[1])?);
    if streams == 0 || section == 0 || classes.len() / streams < section + 1 {
        return Err("the passage must hold a section in every stream".into());
    }
    let whole = (classes.len() / streams - 1) / section;
    let sections = match args.get(2) {
        Some(n) => count(n)?,
        None => whole,
    };
    let mut host = host;
    let mut carded = TowerLearner::from_text(std::str::from_utf8(state)?)?;
    lockstep(&mut host, &mut carded, classes, streams, section, sections)?;
    println!("TOWER_PARITY_SHA sections={sections} whole_pass={} host={} card={}", sections == whole, digest(host.to_text().as_bytes())?, digest(carded.to_text().as_bytes())?);
    Ok(())
}

/// Host against card in lockstep over `sections` sections of the passage split into `streams`
/// streams, every stream from rest.
fn lockstep(host: &mut TowerLearner, carded: &mut TowerLearner, classes: &[usize], streams: usize, section: usize, sections: usize) -> Result<()> {
    let chunk = classes.len() / streams;
    if streams == 0 || section == 0 || sections == 0 || (chunk - 1) / section < sections {
        return Err("the passage must hold the declared sections in every stream".into());
    }
    let opened = Card::open(0)?;
    let mut card = TowerCard::open(&opened)?;
    if std::env::var_os("TOWER_PROFILE").is_some() {
        card.profile();
    }
    let mut states_h: Vec<TowerState> = (0..streams).map(|_| host.tower.rest()).collect();
    let mut states_c = states_h.clone();
    let started = Instant::now();
    let (mut faces_all, mut faces_unequal, mut entries_all, mut entries_unequal, mut learners_unequal) = (0usize, 0usize, 0usize, 0usize, 0usize);
    let (mut host_ns, mut card_ns) = (0u128, 0u128);
    println!("TOWER_PARITY_OPEN material={} streams={streams} section={section} sections={sections} card={}", host.tower.theta.len(), opened.census().name);
    for k in 0..sections {
        let parts: Vec<&[usize]> = (0..streams).map(|s| &classes[s * chunk + k * section..s * chunk + (k + 1) * section + 1]).collect();
        let targets: Vec<Vec<Option<usize>>> = parts.iter().map(|p| p[1..].iter().map(|&c| Some(c)).collect()).collect();
        // The opening read and the summed covector, host against card on the same material.
        let mut reference = HostPass::default();
        let t0 = Instant::now();
        let read_h = reference.forward(&host.tower, &states_h, &parts, &targets, Slot::Opened)?;
        let g_h = reference.reverse(&host.tower, &states_h, &parts, None)?;
        // The reference's kept read is not the learner's: free it before the learners take the
        // section.
        drop(reference);
        let t1 = Instant::now();
        let read_c = card.forward(&host.tower, &states_h, &parts, &targets, Slot::Opened)?;
        let g_c = card.reverse(&host.tower, &states_h, &parts, None)?;
        let t2 = Instant::now();
        let faces_h: Vec<(u128, u128)> = read_h.faces.iter().flatten().flatten().copied().collect();
        let faces_c: Vec<(u128, u128)> = read_c.faces.iter().flatten().flatten().copied().collect();
        let codes_unequal = faces_h.iter().zip(&faces_c).filter(|(a, b)| face_code(a.0, a.1) != face_code(b.0, b.1)).count() + faces_h.len().abs_diff(faces_c.len());
        let unequal = faces_h.iter().zip(&faces_c).filter(|(a, b)| a != b).count() + faces_h.len().abs_diff(faces_c.len());
        let g_unequal = g_h.iter().zip(&g_c).filter(|(a, b)| a != b).count() + g_h.len().abs_diff(g_c.len());
        let first = g_h.iter().zip(&g_c).position(|(a, b)| a != b);
        let swell_equal = read_h.swell == read_c.swell;
        faces_all += faces_h.len();
        faces_unequal += unequal;
        entries_all += g_h.len();
        entries_unequal += g_unequal;
        // Both learners take the section.
        let t3 = Instant::now();
        let receipt_h = host.section_realized(&mut states_h, &parts, None, &mut HostPass::default())?;
        let t4 = Instant::now();
        let receipt_c = carded.section_realized(&mut states_c, &parts, None, &mut card)?;
        let t5 = Instant::now();
        let learner_equal = receipt_h == receipt_c && host.to_text() == carded.to_text() && states_h == states_c;
        learners_unequal += usize::from(!learner_equal);
        host_ns += (t1 - t0).as_nanos() + (t4 - t3).as_nanos();
        card_ns += (t2 - t1).as_nanos() + (t5 - t4).as_nanos();
        println!(
            "TOWER_PARITY section={} faces={} faces_unequal={unequal} codes_unequal={codes_unequal} swell_equal={swell_equal} gradient_entries={} gradient_unequal={g_unequal} first_unequal={first:?} deposited={} halvings={} learner_equal={learner_equal} host_pass_ms={} card_pass_ms={} host_section_ms={} card_section_ms={}",
            k + 1,
            faces_h.len(),
            g_h.len(),
            receipt_h.deposited,
            receipt_h.halvings,
            (t1 - t0).as_millis(),
            (t2 - t1).as_millis(),
            (t4 - t3).as_millis(),
            (t5 - t4).as_millis()
        );
        if let Some(i) = first {
            println!("TOWER_PARITY_FIRST section={} index={i} host={} card={}", k + 1, g_h[i], g_c[i]);
        }
    }
    let times = card.times();
    println!(
        "TOWER_PARITY_DONE sections={sections} faces={faces_all} faces_unequal={faces_unequal} gradient_entries={entries_all} gradient_unequal={entries_unequal} learners_unequal={learners_unequal} host_ms={} card_ms={} card_forwards={} card_forward_ms={} card_reverses={} card_reverse_ms={} elapsed_ms={}",
        host_ns / 1_000_000,
        card_ns / 1_000_000,
        times.forwards,
        times.forward_ns / 1_000_000,
        times.reverses,
        times.reverse_ns / 1_000_000,
        started.elapsed().as_millis()
    );
    println!("TOWER_REALIZATION {}", card.realization());
    for (entry, calls, ns) in card.profiled() {
        println!("TOWER_PROFILE entry={entry} launches={calls} ms={}", ns / 1_000_000);
    }
    if faces_unequal + entries_unequal + learners_unequal > 0 {
        return Err("the card's pass is not the host's".into());
    }
    Ok(())
}

fn train(args: &[String]) -> Result<()> {
    if args.first().map(String::as_str) != Some("complete-language") {
        return Err("train complete-language COMMAND ARGS…".into());
    }
    // The command as run, so a host parity reference can name the card run it checks.
    println!("TOWER_COMMAND {}", args[1..].join(" "));
    let opened = Card::open(0)?;
    let mut card = TowerCard::open(&opened)?;
    let started = Instant::now();
    let result = exterior::run_tower_classes_with_realization(&args[1..], &mut card);
    let times = card.times();
    println!(
        "TOWER_CARD forwards={} forward_ms={} reverses={} reverse_ms={} elapsed_ms={}",
        times.forwards,
        times.forward_ns / 1_000_000,
        times.reverses,
        times.reverse_ns / 1_000_000,
        started.elapsed().as_millis()
    );
    result
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let result = match args.first().map(String::as_str) {
        Some("parity") => parity(&args[1..]),
        Some("parity-state") => parity_state(&args[1..]),
        Some("parity-units") => parity_units(&args[1..]),
        Some("train") | Some("release") | Some("read") => train(&args[1..]),
        _ => Err("tower_pass parity …|parity-state …|parity-units …|train complete-language …|release complete-language …|read complete-language …".into()),
    };
    if let Err(error) = result {
        eprintln!("tower_pass: {error}");
        std::process::exit(1);
    }
}
