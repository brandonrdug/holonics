//! [definition; theory, November 12 (the record of the opening's room, §4)] **`train-store`, the store's trainer**: a learner continued on a
//! store of whole documents (`tools/corpus_passage.py`), read by keyed stretches, one keyed state a stretch, in sections declared to fill one
//! batch of the card. Its cut is the reference port's (`store_stretch_census.py`, the passage record's receipts), draw for draw, and its lines
//! are held to the port's. Its law is in code and in the learner's state: the rate held at the state's `rate_bits`, every step standing at its
//! size, no growth but the letters' at the crossing, the step's transfer and external price printed and never acted on. It reads no
//! environment variable for its law: a run where any variable named `FIELD_…` is set is refused, but for the readings the card's driver
//! reads before any command (`FIELD_PROFILE`, `FIELD_PHASES`, `FIELD_TRACE`), which leave every bit of the state as it is.
//!
//! Why no room and no opening (the record §2 and §4): a document has no question and no answer; the code line's openings computed 0.704 of a
//! lap's sites for 0.018 of its compared places. Why one state a stretch (§4 item 2): a pass over fresh text meets a new stretch at every draw,
//! and a second state of the same bytes buys less than the next stretch does. Why a declared section (§4 item 3): a section is the unit a
//! deposit consumes, so its extent is law and is carried in the state; a section read from the device's free memory would let the bits follow
//! the schedule. Why the letters at a crossing (§4 item 4, [`holonics_engine::field::Constitution::lettered`]): the codec held only the code
//! passage's bytes and refused every other.

use holonics_engine::codec::Codec;
use holonics_engine::passage::held_out;
use holonics_engine::region::{views_of, OwnedRegion};
use crate::exterior::*;
use holonics_engine::codec::count;
use std::io::Read;
use std::path::Path;
use holonics_engine::field::{Learner, Realization, MaterialMean, PassSlice, StorePass};
use std::collections::HashMap;
use std::io::{BufRead, Seek, SeekFrom};
use holonics_engine::passage::{Cut, Piece, PieceBytes, Slice, Stretch, held_set};

/// The store's slices in its own order: `tools/corpus_passage.py`'s `SLICES` (Common Corpus's five), then the arithmetic world
/// (`tools/arithmetic_world.py`) and the word problems (`tools/words_passage.py`), joined on November 16 ([`join_store`]).
const SLICES: [&str; 7] = ["code", "web", "science", "books", "wikidata", "arithmetic", "words"];
/// [definition; Build B] The most places the world's reaction takes: a signed value of 128 bits (39 digits and its sign) and a line feed, or
/// `?` between two line feeds.
const REACTION_BOUND: u64 = 41;

/// [definition; Build B] Whether the stretch of count `d` is an act of the world joined to its slice: one in `every`, keyed by the key
/// file's seed and the stretch's count (the mixer of [`holonics_engine::passage`]'s draws, SplitMix64).
fn acts_here(seed: u64, d: u64, every: u64) -> bool {
    let mut z = seed.wrapping_add(d.wrapping_mul(0x9E37_79B9_7F4A_7C15)) ^ 0x776F_726C_6400_0000;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    (z ^ (z >> 31)) % every == 0
}

/// [definition; theory, November 16 20:39Z] A draft's own places, the ones its refine redraws: its expression before its first `= `, or the
/// places before its first line feed, or every place it wrote. The `= `, the predicted value and what follows stay written.
fn draft_places(draft: &[u8]) -> usize {
    let eq = draft.windows(2).position(|w| w == b"= ");
    let feed = draft.iter().position(|&b| b == b'\n');
    match (eq, feed) {
        (Some(e), f) if f.is_none_or(|f| e < f) => e,
        (_, Some(f)) => f,
        _ => draft.len(),
    }
}

/// [definition; Build B] An act's prompt from its stretch's bytes: the last `records` whole lines of the stretch (each ending with its line
/// feed), or none where the stretch holds no whole line.
fn world_prompt(bytes: &[u8], records: usize) -> Option<Vec<u8>> {
    let last = bytes.iter().rposition(|&b| b == b'\n')?;
    let body = &bytes[..=last];
    let starts: Vec<usize> = std::iter::once(0).chain(body.iter().enumerate().filter(|(_, b)| **b == b'\n').map(|(k, _)| k + 1)).filter(|&k| k <= last).collect();
    // A line begins at the stretch's start only where the stretch begins a record; the first partial line is never a record.
    let whole: Vec<usize> = starts.iter().copied().filter(|&k| k > 0).collect();
    let from = *whole.iter().rev().nth(records.saturating_sub(1)).or(whole.first())?;
    Some(body[from..].to_vec())
}

/// The head of a slice's index of pieces (`tools/corpus_passage.py`'s `INDEX_HEAD`).
const INDEX_HEAD: &str = "document\ttitle_octets\ttext_octets\topens\tcloses";
/// The head of a store's counts (`tools/corpus_passage.py`'s `STORE_HEAD`).
const STORE_HEAD: &str = "role\tslice\tshare\tline_floor\tdocuments\tpieces\ttext_octets\tstore_octets\tsha256";
/// [definition; the record §4 item 1] **A stretch's two draws**: a context and a run, each on an octave uniform over `[4, 8)` to `[256, 512)`
/// and uniform within it, so a stretch is 8 to 1,022 places, 217 on the mean. The least stands under the near field (`NEAR`, 6 places) and the
/// longest stretch near twice the code line's mean mask region (458) and well inside the declared reach (3,771), so no ring is asked a distance
/// the code line never gave it. Written into the pass at the crossing; a wider range is a crossing with its own guess.
const LEAST: u64 = 4;
const OCTAVES: u64 = 7;
/// [definition; the record §4 item 3] **The section's first bounds**: 15,606,223 pairs of sites and 41,490 sites, which reserve nine tenths of
/// te7's one-batch peak store (8,440,325,846 octets) at 280 octets a pair and at the octets a site that 257 classes take (77,766), split at the
/// cut's own mean of 376.1 pairs of sites a site (`store_stretch_draw.txt`). Written into the pass at the crossing and changed only at a
/// declared crossing (a growth of the constitution).
const PAIRS_BOUND: u64 = 15_606_223;
const SITES_BOUND: u64 = 41_490;
/// The readings the card's driver reads before any command, which leave the state's bytes as they are; `FIELD_BLANK_LIVE` (with the profile)
/// reads a blank's face covector back at each return (November 16).
const READINGS: [&str; 4] = ["FIELD_PROFILE", "FIELD_PHASES", "FIELD_TRACE", "FIELD_BLANK_LIVE"];

/// A slice's file as its source of bytes.
struct SliceFile(std::fs::File);

impl PieceBytes for SliceFile {
    fn read_at(&mut self, at: u64, out: &mut [u8]) -> Result<()> {
        self.0.seek(SeekFrom::Start(at))?;
        self.0.read_exact(out)?;
        Ok(())
    }
}

/// [measurement; the port's `Tally`] A section's counts by the port's fields (the two pairs fields left to the port).
#[derive(Clone, Copy, Debug, Default)]
struct Tally {
    regions: u64,
    sites: u64,
    domain: u64,
    squared: u64,
    open: u64,
}

impl Tally {
    fn take(&mut self, region: &OwnedRegion, counted: usize) {
        // [the lead, November 18] A passage read by two streams stands on the card as its known stream's sites and as many open places, and
        // compares every place past its first.
        let n = region.classes.len() as u64 * if region.strand { 2 } else { 1 };
        self.regions += 1;
        self.sites += n;
        self.domain += counted as u64;
        self.squared += n * n;
        self.open += if region.strand { region.classes.len().saturating_sub(1) as u64 } else { region.unresolved.iter().filter(|&&u| u).count() as u64 };
    }

    fn text(&self) -> String {
        format!("regions={} sites={} domain={} squared={} open={}", self.regions, self.sites, self.domain, self.squared, self.open)
    }
}

/// The store's counts, `(role, slice) → (pieces, store octets)`, from its `STORE.tsv`.
pub(crate) fn store_counts(text: &str) -> Result<HashMap<(String, String), (u64, u128)>> {
    let mut lines = text.lines();
    if lines.next() != Some(STORE_HEAD) {
        return Err("a STORE.tsv that does not open with its head".into());
    }
    let mut out = HashMap::new();
    for line in lines {
        let w: Vec<&str> = line.split('\t').collect();
        if w.len() != 9 {
            return Err("a STORE.tsv row that is not nine fields".into());
        }
        out.insert((w[0].to_string(), w[1].to_string()), (count(w[5])? as u64, w[7].parse::<u128>()?));
    }
    Ok(out)
}

/// A slice's first `count` pieces from its index, each with its offset in the slice's file (the bytes of every piece before it).
fn pieces_of(path: &Path, count: u64) -> Result<Vec<Piece>> {
    let mut lines = std::io::BufReader::new(std::fs::File::open(path)?).lines();
    if lines.next().transpose()?.as_deref() != Some(INDEX_HEAD) {
        return Err("a slice's index that does not open with its head".into());
    }
    let mut out = Vec::with_capacity(count as usize);
    let mut offset = 0u64;
    for line in lines {
        if out.len() as u64 == count {
            break;
        }
        let line = line?;
        let w: Vec<u64> = line.split('\t').map(|v| v.parse::<u64>()).collect::<std::result::Result<_, _>>()?;
        let [document, title, text, opens, closes] = w[..] else { return Err("a slice's index row that is not five counts".into()) };
        let piece = Piece { document, offset, title, text, opens: opens == 1, closes: closes == 1 };
        // [theory, November 12, P49] A piece of no places would wrap the cut's `rest − 1`; `tools/corpus_passage.py` writes none.
        if piece.places() == 0 {
            return Err("a piece of zero places (tools/corpus_passage.py writes none)".into());
        }
        out.push(piece);
        offset += title + text;
    }
    if out.len() as u64 != count {
        return Err("a slice's index shorter than its role's pieces".into());
    }
    Ok(out)
}

/// [measurement; the record §4 item 4] Which byte values the store's documents hold, over every slice's training and held files (the line feed
/// counted as held: a piece that opens with a title is read with one), read a block at a time.
fn bytes_held(store: &Path) -> Result<[bool; 256]> {
    let mut held = [false; 256];
    held[b'\n' as usize] = true;
    let mut block = vec![0u8; READ_BUDGET as usize];
    for name in SLICES {
        for stem in ["DOCS", "HELD"] {
            let path = store.join(format!("{stem}_{name}.bin"));
            if !path.exists() {
                continue;
            }
            let mut file = std::fs::File::open(path)?;
            loop {
                let n = file.read(&mut block)?;
                if n == 0 {
                    break;
                }
                for &b in &block[..n] {
                    held[b as usize] = true;
                }
            }
        }
    }
    Ok(held)
}

/// A count of codes on `2^(−20)` bits over `sites` in millionths of a bit a site (toward zero, as `train-field`'s section line).
fn micro(code: i64, sites: usize) -> i128 {
    if sites == 0 {
        return 0;
    }
    (code as i128 * 1_000_000) / ((sites as i128) << 20)
}

/// The realization's counters as a line's words (`-` where it keeps none).
fn counters_text(realization: &dyn Realization) -> String {
    match realization.counters() {
        Some(c) => format!("reads={} returns={} pairs={} batches={} peak_store={}", c.reads, c.returns, c.pairs, c.batches, c.peak_store),
        None => "counters=-".to_string(),
    }
}

/// `train-store UNITS UNITS_SHA STORE STORE_SHA ROLE KEYS KEYS_SHA CODEC CODEC_SHA HELD HELD_SHA SECTIONS SAVE STOP_MS OUT FROM FROM_SHA`:
/// the learner `FROM` continued over the store `STORE` (`STORE_SHA` its `STORE.tsv`'s) in the role `ROLE` (`prefix`, `train` or `held`), for
/// `SECTIONS` sections, saving `OUT/STATE.k` and `OUT/MEAN.k` every `SAVE` sections and at the last (`k` the sections done in this run, and
/// `MEAN.k` the mean of the states after each section since the save before); a section ending past `STOP_MS` from the run's start saves
/// `OUT/STATE.stopped` and ends. `CODEC` is the learner's codec; `HELD` is the code line's held passage, the yardstick read at the crossing.
///
/// [definition; the record §4 item 4] **The crossing** (a learner with no pass): the held passage read at the code line's codec and printed
/// as `STORE_YARDSTICK at=before` (`train-field`'s `FIELD_HELD` read, [`held_out`]); the byte values the store's documents hold counted, the
/// codec extended by the fresh ones in byte order (`field-codec-v3`, written as `OUT/CODEC`), the learner grown by as many letters
/// ([`Learner::lettered`]), the yardstick read again (`at=after`), the pass set at the store's start with its law (the octaves of a
/// stretch's draws, the section's bounds) and `OUT/STATE.0` saved. A continued learner (with its pass) reads on from its place.
pub fn train(args: &[String], realization: &mut dyn Realization) -> Result<()> {
    if args.len() != 18 {
        return Err("train-store UNITS UNITS_SHA STORE STORE_SHA ROLE KEYS KEYS_SHA CODEC CODEC_SHA HELD HELD_SHA SECTIONS SAVE STOP_MS OUT FROM FROM_SHA".into());
    }
    let started = std::time::Instant::now();
    // [definition; the record §5, R5] The store's law reads no variable: every one named `FIELD_…` is refused, but for the card driver's two
    // readings.
    let set: Vec<String> = std::env::vars_os().filter_map(|(k, _)| k.into_string().ok()).filter(|k| k.starts_with("FIELD_") && !READINGS.contains(&k.as_str())).collect();
    if !set.is_empty() {
        return Err(format!("train-store reads no variable for its law, and {} set", set.join(", ")).into());
    }
    let units = units_of(&args[1], &args[2])?;
    if !units.merges().is_empty() {
        return Err("the store's cut is on bytes: a units file of merges is refused".into());
    }
    let store = Path::new(&args[3]);
    let counts = store_counts(std::str::from_utf8(&pinned_read(&store.join("STORE.tsv").to_string_lossy(), &args[4], READ_BUDGET as usize)?)?)?;
    let role = args[5].as_str();
    let keys = pinned_read(&args[6], &args[7], READ_BUDGET as usize)?;
    let seed = u64::from_be_bytes(keys.get(keys.len().saturating_sub(8)..).filter(|w| w.len() == 8).ok_or("a key file of fewer than eight bytes")?.try_into()?);
    let codec_text = String::from_utf8(pinned_read(&args[8], &args[9], READ_BUDGET as usize)?)?;
    let held_text_bytes = pinned_read(&args[10], &args[11], READ_BUDGET as usize)?;
    let (sections, save, stop_ms) = (positive(&args[12])?, positive(&args[13])?, positive(&args[14])? as u128);
    let out = Path::new(&args[15]);
    let from_text = pinned_read(&args[16], &args[17], STATE_BUDGET)?;
    let mut learner = Learner::from_text(std::str::from_utf8(&from_text)?).map_err(|e| e.to_string())?;
    // A state's text read and written back: every code line state reads and writes byte for byte (the pass line only where present).
    println!("STORE_STATE_TEXT bytes={} roundtrip={} pass={}", from_text.len(), if learner.to_text().as_bytes() == from_text.as_slice() { "equal" } else { "differs" }, if learner.pass.is_some() { "present" } else { "none" });
    if learner.to_text().as_bytes() != from_text.as_slice() {
        return Err("a state that does not read and write back byte for byte".into());
    }
    let names: Vec<&str> = SLICES.iter().copied().filter(|n| counts.contains_key(&(role.to_string(), n.to_string()))).collect();
    if names.is_empty() {
        return Err(format!("a store with no slice of the role {role}").into());
    }
    std::fs::create_dir(out)?;
    let mut codec = Codec::from_text(&codec_text, units)?;
    if learner.pass.is_none() {
        // The crossing.
        if learner.field.declaration.alphabet != codec.alphabet() {
            return Err("a crossing learner whose alphabet is not its codec's".into());
        }
        let before = held_out(&learner.field, &codec, &held_set(&codec, &held_text_bytes)?, realization)?;
        println!("STORE_YARDSTICK at=before {} ms={}", held_text(&before), started.elapsed().as_millis());
        let held = bytes_held(store)?;
        let standing: Vec<bool> = (0..256usize).map(|b| codec.encode(&[b as u8]).is_ok()).collect();
        let fresh: Vec<u32> = (0..256u32).filter(|&b| held[b as usize] && !standing[b as usize]).collect();
        let (n_held, n_standing) = (held.iter().filter(|&&h| h).count(), standing.iter().filter(|&&s| s).count());
        let standing_held = (0..256).filter(|&b| held[b] && standing[b]).count();
        println!("STORE_BYTES held={n_held} standing={n_standing} standing_held={standing_held} fresh={} held_by_none={} ms={}", fresh.len(), 256 - n_held, started.elapsed().as_millis());
        codec = codec.extended(&fresh)?;
        learner = learner.lettered(fresh.len()).map_err(|e| e.to_string())?;
        println!("STORE_LETTERS fresh={} alphabet={} void={} material={} ms={}", fresh.len(), codec.alphabet(), codec.void(), learner.field.material_len(), started.elapsed().as_millis());
        let after = held_out(&learner.field, &codec, &held_set(&codec, &held_text_bytes)?, realization)?;
        println!("STORE_YARDSTICK at=after {} ms={}", held_text(&after), started.elapsed().as_millis());
        learner.pass = Some(StorePass { role: role.to_string(), store: args[4].clone(), stretches: 0, least: LEAST, octaves: OCTAVES, pairs: PAIRS_BOUND, sites: SITES_BOUND, own: false, slices: names.iter().map(|n| PassSlice { name: n.to_string(), piece: 0, cursor: 0, taken: 0 }).collect(), world: None, frontier: 0, before: false, strand: false, past: false, second: false });
        write_new(&out.join("STATE.0"), learner.to_text().as_bytes())?;
        println!("STORE_CROSSING role={role} saved=STATE.0 ms={}", started.elapsed().as_millis());
    }
    write_new(&out.join("CODEC"), codec.to_text().as_bytes())?;
    let pass = learner.pass.clone().ok_or("a learner with no pass past its crossing")?;
    if pass.role != role || pass.store != args[4] || pass.slices.iter().map(|s| s.name.as_str()).ne(names.iter().copied()) {
        return Err("a learner whose pass is of another role, store or slices".into());
    }
    if learner.field.declaration.alphabet != codec.alphabet() {
        return Err("a learner whose alphabet is not its codec's".into());
    }
    // [the record §5, R3] The declaration by part, and the pass's law.
    let d = learner.field.declaration;
    let l = learner.field.layout();
    println!(
        "STORE_DECLARATION alphabet={} void={} lanes={} lane_width={} heads={} still={} modes={} contacts={} carry={} triads={} ticks={} frames={} reach={} rate_bits={} material={} enc={} before={} after={} read_bias={} moment_before={} moment_after={} pace={} least={} octaves={} pairs_bound={} sites_bound={}",
        d.alphabet,
        codec.void(),
        d.lanes,
        d.lane_width(),
        d.heads,
        d.still,
        d.modes,
        d.contacts,
        d.carry,
        d.triads,
        d.ticks,
        d.frames,
        d.reach,
        learner.rate_bits,
        learner.field.material_len(),
        l.before - l.enc,
        l.after - l.before,
        l.q - l.after,
        l.moment_before - l.read_bias,
        l.moment_after - l.moment_before,
        l.temper - l.moment_after,
        l.moment_face - l.pace,
        pass.least,
        pass.octaves,
        pass.pairs,
        pass.sites
    );
    let stem = if role == "held" { "HELD" } else { "DOCS" };
    let mut slices = Vec::with_capacity(names.len());
    for &name in &names {
        let (count, quota) = counts[&(role.to_string(), name.to_string())];
        slices.push(Slice { name: name.to_string(), quota, pieces: pieces_of(&store.join(format!("{stem}_{name}.tsv")), count)?, source: Box::new(SliceFile(std::fs::File::open(store.join(format!("{stem}_{name}.bin")))?)) });
    }
    println!("STORE_PASS_AT stretches={} {} {} ms={}", pass.stretches, pass.slices.iter().map(|s| format!("{}_piece={} {}_cursor={} {}_taken={}", s.name, s.piece, s.name, s.cursor, s.name, s.taken)).collect::<Vec<_>>().join(" "), counters_text(realization), started.elapsed().as_millis());
    let mut cut = Cut { seed, slices, pass };
    let mut mean = MaterialMean::new(learner.field.material_len());
    // The step's price since the last save ([`Receipt::transfer`] and [`Receipt::external`]), printed and never acted on.
    let (mut transfers, mut externals, mut curvatures, mut priced, mut since) = (0i128, 0i128, 0i128, 0usize, 0usize);
    let mut prior: Option<i128> = None;
    let mut done = 0usize;
    let mut ended = false;
    // [measurement; theory, November 13, P56 item 4] The host's part of a section by phase, summed, printed where a reading is set (`FIELD_PROFILE`,
    // `FIELD_PHASES`): the cut, the views, the realized section (the card's run and the deposit on the host), the mean of states, the lines, the pass
    // line and the saves (ns).
    let host_phases = std::env::var_os("FIELD_PROFILE").is_some() || std::env::var_os("FIELD_PHASES").is_some();
    let mut host = [0u128; 7];
    while done < sections {
        let section_start = std::time::Instant::now();
        let mut regions: Vec<OwnedRegion> = Vec::new();
        let (mut tally, mut by_slice) = (Tally::default(), vec![0u64; cut.slices.len()]);
        let (mut in_pairs, mut in_sites) = (0u64, 0u64);
        // The section's stretches read at the frontier (the pass's share, [`holonics_engine::field::StorePass::frontier`]).
        let mut at_frontier = 0u64;
        // [definition; Build B] The section's acts: the prompt's classes and the slice of each stretch the world answers.
        let mut acts: Vec<(Vec<usize>, usize)> = Vec::new();
        while let Some(drawn) = cut.next() {
            let act = cut.pass.world.as_ref().filter(|w| !drawn.frontier && cut.slices[drawn.slice].name == w.slice && acts_here(seed, drawn.d, w.every)).map(|w| w.run);
            let n = drawn.sites() + act.map_or(0, |run| run + REACTION_BOUND);
            // A stretch read by two streams is staged as its known stream's sites and as many open places: the section's bounds are the card's.
            let n = if drawn.frontier && cut.pass.strand { 2 * n } else { n };
            if in_sites > 0 && (in_pairs + n * n > cut.pass.pairs || in_sites + n > cut.pass.sites) {
                break;
            }
            let prompt = match act {
                Some(_) => {
                    let at = cut.pass.slices[drawn.slice].clone();
                    let bytes = cut.slices[drawn.slice].bytes(at.piece as usize, at.cursor, drawn.q + drawn.a)?;
                    cut.pass.world.as_ref().and_then(|w| world_prompt(&bytes, w.records as usize))
                }
                None => None,
            };
            let slice = drawn.slice;
            at_frontier += u64::from(drawn.frontier);
            let Stretch { region, counted, .. } = cut.take(drawn, &codec)?;
            by_slice[slice] += 1;
            (in_pairs, in_sites) = (in_pairs + n * n, in_sites + n);
            match prompt {
                Some(p) => acts.push((codec.encode(&p)?, slice)),
                None => {
                    tally.take(&region, counted);
                    regions.push(region);
                }
            }
        }
        if regions.is_empty() && acts.is_empty() {
            ended = true;
            break;
        }
        // [definition; Build B] The field acts and the world answers: each act's prompt released `run` places on the field as it stands
        // (the writer `write-store` runs, keyed by the pass's count of stretches), the world's reaction to each draft appended, and the
        // reaction alone open. The prompt and the draft are known context, never a target.
        let mut world_line = String::new();
        if let (Some(w), false) = (cut.pass.world.clone(), acts.is_empty()) {
            let run = w.run as usize;
            let release: Vec<(&[usize], usize)> = acts.iter().map(|(p, _)| (p.as_slice(), run)).collect();
            let act_seed = seed ^ cut.pass.stretches.wrapping_mul(0x9E37_79B9_7F4A_7C15);
            let mut drafts = learner.field.sample_runs(&release, run, 0, codec.void(), act_seed, 0, true, false, None, false, realization, &mut |_, _| true, &mut |_| {}).map_err(|e| e.to_string())?;
            if w.refine > 0 {
                // [definition; theory, November 16 20:39Z] Each draft redrawn once, place by place in landmark order, its predicted reaction known.
                let lens: Vec<usize> = drafts.iter().map(|d| draft_places(&codec.decode(&d[..d.iter().position(|&c| c == codec.void()).unwrap_or(d.len())]))).collect();
                let prompts: Vec<&[usize]> = acts.iter().map(|(p, _)| p.as_slice()).collect();
                drafts = learner.field.refine_drafts(&prompts, &drafts, &lens, codec.void(), act_seed ^ 0x7265_6669_6E65, realization).map_err(|e| e.to_string())?;
            }
            let (mut read_ok, mut draft_places, mut world_places) = (0usize, 0usize, 0usize);
            let first = regions.len();
            for ((prompt, _), draft) in acts.iter().zip(&drafts) {
                let written = &draft[..draft.iter().position(|&c| c == codec.void()).unwrap_or(draft.len())];
                let reaction = crate::world::react(&codec.decode(written));
                if reaction.appended != b"?\n" && reaction.appended != b"\n?\n" {
                    read_ok += 1;
                }
                let answered = codec.encode(&reaction.appended)?;
                let mut classes = prompt.clone();
                classes.extend_from_slice(&written[..reaction.read.min(written.len())]);
                let known = classes.len();
                classes.extend_from_slice(&answered);
                let mut open = vec![false; known];
                open.extend(std::iter::repeat_n(true, answered.len()));
                let region = OwnedRegion::plain(classes, open);
                tally.take(&region, answered.len());
                (draft_places, world_places) = (draft_places + reaction.read.min(written.len()), world_places + answered.len());
                regions.push(region);
            }
            world_line = format!("acts={} read={read_ok} draft_places={draft_places} world_places={world_places} first={first}", acts.len());
        }
        let regions_ms = section_start.elapsed().as_millis();
        host[0] += section_start.elapsed().as_nanos();
        let views_start = std::time::Instant::now();
        let views = views_of(&regions);
        host[1] += views_start.elapsed().as_nanos();
        let deposit_start = std::time::Instant::now();
        let receipt = learner.section_realized(&views, realization).map_err(|e| e.to_string())?;
        let deposit_ms = deposit_start.elapsed().as_millis();
        host[2] += deposit_start.elapsed().as_nanos();
        let mean_start = std::time::Instant::now();
        mean.take(&learner.field).map_err(|e| e.to_string())?;
        host[3] += mean_start.elapsed().as_nanos();
        let lines_start = std::time::Instant::now();
        if receipt.sites as u64 != tally.domain {
            return Err(format!("a section whose receipt counts {} sites against the cut's domain of {}", receipt.sites, tally.domain).into());
        }
        let opt = |v: Option<i64>| v.map_or("-".to_string(), |c| micro(c, receipt.sites).to_string());
        // [P60 item 6] The opening's code over the section's compared places, in millionths of a bit a place, where the field has the lift; a
        // line of a field without it is the line as before.
        let opening = if receipt.opening.is_empty() {
            String::new()
        } else {
            let (code, places) = receipt.opening.iter().fold((0i128, 0usize), |(c, n), &(rc, rn)| (c + rc as i128, n + rn));
            format!(" opening={} opening_places={places}", if places == 0 { 0 } else { (code * 1_000_000) / ((places as i128) << 20) })
        };
        // The count of the section's regions read at the frontier, on the line only where the pass declares a share, so a line without one
        // is the line as before.
        let frontier = if cut.pass.frontier > 0 { format!(" frontier={at_frontier}") } else { String::new() };
        println!(
            "STORE_SECTION n={done} {} {} stretches={} before={} after={} deposited={} transfer={} external={} rate={}{opening}{frontier} regions_ms={regions_ms} deposit_ms={deposit_ms} ms={}",
            tally.text(),
            cut.slices.iter().zip(&by_slice).map(|(s, n)| format!("{}={n}", s.name)).collect::<Vec<_>>().join(" "),
            cut.pass.stretches,
            micro(receipt.code_before, receipt.sites),
            opt(receipt.code_after),
            receipt.deposited,
            opt(receipt.transfer),
            opt(receipt.external),
            learner.rate_bits,
            section_start.elapsed().as_millis()
        );
        if !world_line.is_empty() {
            // [measurement; Build B] The world's places' code at the section's comparison (the opening's, before the deposit), in millionths of a
            // bit a place, beside the section's own line.
            let first: usize = world_line.rsplit("first=").next().and_then(|v| v.parse().ok()).unwrap_or(regions.len());
            let (code, places) = receipt.opening.iter().skip(first).fold((0i128, 0usize), |(c, n), &(rc, rn)| (c + rc as i128, n + rn));
            println!("STORE_WORLD n={done} {world_line} world_code={}", if places == 0 { 0 } else { (code * 1_000_000) / ((places as i128) << 20) });
        }
        if let (Some(t), Some(e)) = (receipt.transfer, prior) {
            (transfers, externals, curvatures, priced) = (transfers + t as i128, externals + e, curvatures + (t as i128 - e), priced + 1);
        }
        prior = receipt.external.filter(|_| receipt.deposited && receipt.halvings == 0).map(i128::from);
        host[4] += lines_start.elapsed().as_nanos();
        let pass_start = std::time::Instant::now();
        learner.pass = Some(cut.pass.clone());
        host[5] += pass_start.elapsed().as_nanos();
        done += 1;
        since += 1;
        let saves_start = std::time::Instant::now();
        if done % save == 0 || done == sections {
            write_new(&out.join(format!("STATE.{done}")), learner.to_text().as_bytes())?;
            let (rest, moved, square) = mean.released(&learner.field).map_err(|e| e.to_string())?;
            let mut resting = learner.clone();
            resting.field = rest;
            write_new(&out.join(format!("MEAN.{done}")), resting.to_text().as_bytes())?;
            println!(
                "STORE_SAVE k={done} sections={since} states={} moved={moved} square={square} priced={priced} transfer={transfers} external={externals} curvature={curvatures} octave={} rate={} {} ms={}",
                mean.states(),
                step_transfer(2 * transfers, curvatures),
                learner.rate_bits,
                counters_text(realization),
                started.elapsed().as_millis()
            );
            mean = MaterialMean::new(learner.field.material_len());
            (transfers, externals, curvatures, priced, since) = (0, 0, 0, 0, 0);
        }
        host[6] += saves_start.elapsed().as_nanos();
        if started.elapsed().as_millis() > stop_ms {
            write_new(&out.join("STATE.stopped"), learner.to_text().as_bytes())?;
            println!("STORE_STOPPED sections={done}/{sections} stretches={} {} ms={}", cut.pass.stretches, counters_text(realization), started.elapsed().as_millis());
            return Ok(());
        }
    }
    if ended && since > 0 {
        write_new(&out.join(format!("STATE.{done}")), learner.to_text().as_bytes())?;
        let (rest, moved, square) = mean.released(&learner.field).map_err(|e| e.to_string())?;
        let mut resting = learner.clone();
        resting.field = rest;
        write_new(&out.join(format!("MEAN.{done}")), resting.to_text().as_bytes())?;
        println!("STORE_SAVE k={done} sections={since} states={} moved={moved} square={square} priced={priced} transfer={transfers} external={externals} curvature={curvatures} octave={} rate={} {} ms={}", mean.states(), step_transfer(2 * transfers, curvatures), learner.rate_bits, counters_text(realization), started.elapsed().as_millis());
    }
    if host_phases {
        // A reading's milliseconds to one decimal from its nanoseconds, nearest (integers: the guard lints bar floats in this crate).
        let ms = |ns: u128| {
            let tenths = (ns + 50_000) / 100_000;
            format!("{}.{}", tenths / 10, tenths % 10)
        };
        // [measurement; theory, November 13, P58 item 4] The deposit's parts (`SECTION_PARTS`).
        let parts: Vec<String> = holonics_engine::field::SECTION_PARTS
            .iter()
            .zip(holonics_engine::field::SECTION_PART_NAMES)
            .map(|(p, name)| format!("{name}_ms={}", ms(u128::from(p.load(std::sync::atomic::Ordering::Relaxed)))))
            .collect();
        println!("STORE_DEPOSIT_PARTS sections={done} {}", parts.join(" "));
        println!(
            "STORE_HOST sections={done} cut_ms={} views_ms={} realized_ms={} mean_ms={} lines_ms={} pass_ms={} saves_ms={} elapsed_ms={}",
            ms(host[0]),
            ms(host[1]),
            ms(host[2]),
            ms(host[3]),
            ms(host[4]),
            ms(host[5]),
            ms(host[6]),
            started.elapsed().as_millis()
        );
    }
    println!(
        "STORE_PASS role={role} sections={done} stretches_read={} ended={ended} {} ms={}",
        cut.pass.stretches,
        cut.pass.slices.iter().map(|s| format!("{}_pieces={}", s.name, s.piece)).collect::<Vec<_>>().join(" "),
        started.elapsed().as_millis()
    );
    Ok(())
}

/// The variables a store command refuses: every one named `FIELD_…` but the card driver's two readings ([`READINGS`]).
pub(crate) fn refuse_variables(command: &str) -> Result<()> {
    let set: Vec<String> = std::env::vars_os().filter_map(|(k, _)| k.into_string().ok()).filter(|k| k.starts_with("FIELD_") && !READINGS.contains(&k.as_str())).collect();
    if !set.is_empty() {
        return Err(format!("{command} reads no variable for its law, and {} set", set.join(", ")).into());
    }
    Ok(())
}

/// The slices of `role` the store holds, in the store's order.
pub(crate) fn role_names(counts: &HashMap<(String, String), (u64, u128)>, role: &str) -> Vec<&'static str> {
    SLICES.iter().copied().filter(|n| counts.contains_key(&(role.to_string(), n.to_string()))).collect()
}

/// A slice of `role` opened: its index's pieces and its file.
pub(crate) fn open_slice(store: &Path, role: &str, name: &str, counts: &HashMap<(String, String), (u64, u128)>) -> Result<Slice> {
    let stem = if role == "held" { "HELD" } else { "DOCS" };
    let (count, quota) = counts[&(role.to_string(), name.to_string())];
    Ok(Slice { name: name.to_string(), quota, pieces: pieces_of(&store.join(format!("{stem}_{name}.tsv")), count)?, source: Box::new(SliceFile(std::fs::File::open(store.join(format!("{stem}_{name}.bin")))?)) })
}

/// The sections the held forward reads at, `σ = 2^(−e)` bits.
const HELD_SIGMAS: [u32; 2] = [6, 4];

/// [definition; agent-inferred, November 14] **`found-lane STATE STATE_SHA KEYS KEYS_SHA OUT`**: the learner `STATE` with one more lane on its
/// fine field ([`Learner::laned`]: every read from the lane and every write into it at zero, a tower's level kept and the glue's reads and
/// writes of the lane at zero), its draws read from `KEYS` past the learner's count, written to `OUT`. Before it writes, every line is judged
/// (`FOUND_LANE_LINE`): the learner's head may change only its count of key draws; the fine field's declaration only its width and its lanes;
/// the fine field's material, the glue and the two moment lines keep every standing word at the place the founding's map gives it (a moment
/// line's lane words at zero in the first and at their family's mean in the second); every other line (the level's line, its field's
/// declaration and material, the parts, the pass) is equal. Anything else is refused and nothing is written (November 11: a state tool that
/// left a line behind). Reads no realization: that every face is kept is read on the card by the line's own held read of the founded state.
/// [measurement; November 15, T6 of the theory thread's #841] `read-open-rows UNITS UNITS_SHA STORE STORE_SHA ROLE KEYS KEYS_SHA CODEC CODEC_SHA
/// SECTIONS STATE STATE_SHA`: the sections the line would train next from `STATE` (a lap's mean: its pass line places the cut), each region's
/// forward on the host's threads, and its open rows' shares by where they lie ([`holonics_engine::field::OpenRows`]), summed by slice, head
/// and tick: the near field's share, the far sources' by octave of distance, split by whether the receiver probes the source's class, with
/// each octave's Rényi-2 count and largest share. A reading on the host beside the card's runs: the state is read, never written.
#[allow(clippy::float_arithmetic, reason = "a reading written at the exterior: printed fractions and counts (the precision law governs what the machinery stores and computes, not how a reading is written; October 18)")]
pub fn read_open_rows(args: &[String]) -> Result<()> {
    use holonics_engine::field::{OpenCrowds, OpenRows, OPEN_OCTAVES};
    use rayon::prelude::*;
    // [measurement; theory, November 15 21:16Z] `ticks` and `held` read with OTHER's field where given (the sections stay STATE's pass's).
    let mode = args.get(13).map(String::as_str);
    let fits = match (args.len(), mode) {
        (13, None) | (14, Some("crowds" | "ticks" | "held" | "halves" | "bytick" | "carried")) => true,
        (16, Some("jitter" | "ticks" | "held")) => true,
        _ => false,
    };
    if !fits {
        return Err("read-open-rows UNITS UNITS_SHA STORE STORE_SHA ROLE KEYS KEYS_SHA CODEC CODEC_SHA SECTIONS STATE STATE_SHA [crowds | ticks [OTHER OTHER_SHA] | held [OTHER OTHER_SHA] | jitter OTHER OTHER_SHA]".into());
    }
    let with_crowds = mode == Some("crowds");
    let with_ticks = mode == Some("ticks");
    let with_held = mode == Some("held");
    let with_halves = mode == Some("halves");
    let with_bytick = mode == Some("bytick");
    let with_carried = mode == Some("carried");
    let loaded = if args.len() == 16 { Some(Learner::from_text(std::str::from_utf8(&pinned_read(&args[14], &args[15], STATE_BUDGET)?)?).map_err(|e| e.to_string())?) } else { None };
    let (other, reader) = if mode == Some("jitter") { (loaded, None) } else { (None, loaded) };
    let started = std::time::Instant::now();
    refuse_variables("read-open-rows")?;
    let units = units_of(&args[1], &args[2])?;
    let store = Path::new(&args[3]);
    let counts = store_counts(std::str::from_utf8(&pinned_read(&store.join("STORE.tsv").to_string_lossy(), &args[4], READ_BUDGET as usize)?)?)?;
    let role = args[5].as_str();
    let keys = pinned_read(&args[6], &args[7], READ_BUDGET as usize)?;
    let seed = u64::from_be_bytes(keys.get(keys.len().saturating_sub(8)..).filter(|w| w.len() == 8).ok_or("a key file of fewer than eight bytes")?.try_into()?);
    let codec = Codec::from_text(&String::from_utf8(pinned_read(&args[8], &args[9], READ_BUDGET as usize)?)?, units)?;
    let sections = positive(&args[10])?;
    let learner = Learner::from_text(std::str::from_utf8(&pinned_read(&args[11], &args[12], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let pass = learner.pass.clone().ok_or("a state with no pass line: read-open-rows reads a state of the store's line")?;
    if learner.field.declaration.alphabet != codec.alphabet() {
        return Err("a state whose alphabet is not its codec's".into());
    }
    let names: Vec<&str> = SLICES.iter().copied().filter(|n| counts.contains_key(&(role.to_string(), n.to_string()))).collect();
    if pass.role != role || pass.slices.iter().map(|s| s.name.as_str()).ne(names.iter().copied()) {
        return Err("a state whose pass is of another role or slices".into());
    }
    let stem = if role == "held" { "HELD" } else { "DOCS" };
    let mut slices = Vec::with_capacity(names.len());
    for &name in &names {
        let (count, quota) = counts[&(role.to_string(), name.to_string())];
        slices.push(Slice { name: name.to_string(), quota, pieces: pieces_of(&store.join(format!("{stem}_{name}.tsv")), count)?, source: Box::new(SliceFile(std::fs::File::open(store.join(format!("{stem}_{name}.bin")))?)) });
    }
    let d = learner.field.declaration;
    let (heads, ticks) = (d.heads, d.ticks);
    let mut cut = Cut { seed, slices, pass };
    let mut acc: Vec<Vec<OpenRows>> = vec![vec![OpenRows::default(); ticks * heads]; names.len()];
    let mut crowds: Vec<Vec<OpenCrowds>> = vec![vec![OpenCrowds::default(); ticks * heads]; names.len()];
    let mut jitter: Vec<[[u64; 40]; OPEN_OCTAVES]> = vec![[[0u64; 40]; OPEN_OCTAVES]; ticks * heads];
    let mut news: Vec<Vec<holonics_engine::field::TickNews>> = vec![vec![holonics_engine::field::TickNews::default(); ticks]; names.len()];
    let mut held: Vec<holonics_engine::field::HeldRead> = vec![holonics_engine::field::HeldRead::default(); names.len()];
    let mut halves: Vec<[i128; 5]> = vec![[0; 5]; names.len()];
    let mut bytick: Vec<Vec<i128>> = vec![Vec::new(); names.len()];
    let mut carried_acc: Vec<Vec<[i128; 3]>> = vec![Vec::new(); names.len()];
    let mut carried_compared: Vec<u64> = vec![0; names.len()];
    let (mut done, mut regions_read) = (0usize, 0usize);
    while done < sections {
        let mut regions: Vec<(usize, OwnedRegion)> = Vec::new();
        let (mut in_pairs, mut in_sites) = (0u64, 0u64);
        while let Some(drawn) = cut.next() {
            let n = drawn.sites();
            if in_sites > 0 && (in_pairs + n * n > cut.pass.pairs || in_sites + n > cut.pass.sites) {
                break;
            }
            let slice = drawn.slice;
            let Stretch { region, .. } = cut.take(drawn, &codec)?;
            (in_pairs, in_sites) = (in_pairs + n * n, in_sites + n);
            regions.push((slice, region));
        }
        if regions.is_empty() {
            break;
        }
        let owned: Vec<OwnedRegion> = regions.iter().map(|(_, r)| r.clone()).collect();
        let views = views_of(&owned);
        let field = reader.as_ref().map_or(&learner.field, |r| &r.field);
        if with_carried {
            // [measurement; theory, November 15 22:29Z] The held set dropped and carried one tick, at 1/64 and 1/16 bit, by slice.
            let read: Vec<std::result::Result<Vec<[i128; 3]>, String>> = views.par_iter().map(|v| field.held_carried(v, &HELD_SIGMAS).map_err(|e| e.to_string())).collect();
            for ((slice, r), cell) in regions.iter().zip(read) {
                let c = cell?;
                carried_acc[*slice].resize(c.len(), [0; 3]);
                for (acc, row) in carried_acc[*slice].iter_mut().zip(&c) {
                    for i in 0..3 {
                        acc[i] += row[i];
                    }
                }
                carried_compared[*slice] += r.unresolved.iter().filter(|&&u| u).count() as u64;
            }
            regions_read += regions.len();
            done += 1;
            println!("CARRIED_SECTION n={done} regions={} sites={in_sites} ms={}", regions.len(), started.elapsed().as_millis());
            continue;
        }
        if with_bytick {
            // [measurement; theory, November 15 22:04Z] The held set at 1/16 bit a tick at a time, by slice.
            let read: Vec<std::result::Result<Vec<i128>, String>> = views.par_iter().map(|v| field.held_by_tick(v, 4).map_err(|e| e.to_string())).collect();
            for ((slice, _), cell) in regions.iter().zip(read) {
                let c = cell?;
                bytick[*slice].resize(c.len(), 0);
                bytick[*slice].iter_mut().zip(&c).for_each(|(a, b)| *a += b);
            }
            regions_read += regions.len();
            done += 1;
            println!("BYTICK_SECTION n={done} regions={} sites={in_sites} ms={}", regions.len(), started.elapsed().as_millis());
            continue;
        }
        if with_halves {
            // [measurement; theory, November 15 21:45Z] The held set at 1/16 bit and its two complementary halves, by slice.
            let read: Vec<std::result::Result<[i128; 4], String>> = views.par_iter().map(|v| field.held_halves(v, 4).map_err(|e| e.to_string())).collect();
            for ((slice, r), cell) in regions.iter().zip(read) {
                let c = cell?;
                for i in 0..4 {
                    halves[*slice][i] += c[i];
                }
                halves[*slice][4] += r.classes.len() as i128;
            }
            regions_read += regions.len();
            done += 1;
            println!("HALVES_SECTION n={done} regions={} sites={in_sites} ms={}", regions.len(), started.elapsed().as_millis());
            continue;
        }
        if with_held {
            // [measurement; theory, November 15 21:16Z] The forward with its quiet written site-ticks held, at 1/64 and 1/16 bit, by slice.
            let read: Vec<std::result::Result<holonics_engine::field::HeldRead, String>> = views.par_iter().map(|v| field.held_forward(v, &HELD_SIGMAS).map_err(|e| e.to_string())).collect();
            for ((slice, _), cell) in regions.iter().zip(read) {
                held[*slice].add(&cell?);
            }
            regions_read += regions.len();
            done += 1;
            println!("HELD_SECTION n={done} regions={} sites={in_sites} ms={}", regions.len(), started.elapsed().as_millis());
            continue;
        }
        if with_ticks {
            // [measurement; theory, November 15 20:38Z] What each site's tick moves and what reaches it, by slice and tick.
            let read: Vec<std::result::Result<Vec<holonics_engine::field::TickNews>, String>> = views.par_iter().map(|v| field.tick_news(v).map_err(|e| e.to_string())).collect();
            for ((slice, _), cells) in regions.iter().zip(read) {
                for (k, c) in cells?.iter().enumerate() {
                    news[*slice][k].add(c);
                }
            }
            regions_read += regions.len();
            done += 1;
            println!("TICK_NEWS_SECTION n={done} regions={} sites={in_sites} ms={}", regions.len(), started.elapsed().as_millis());
            continue;
        }
        if let Some(other) = other.as_ref() {
            let read: Vec<std::result::Result<Vec<[[u64; 40]; OPEN_OCTAVES]>, String>> = views.par_iter().map(|v| learner.field.far_jitter(&other.field, v).map_err(|e| e.to_string())).collect();
            for cells in read {
                for (a, c) in jitter.iter_mut().zip(cells?) {
                    for o in 0..OPEN_OCTAVES {
                        for b in 0..40 {
                            a[o][b] += c[o][b];
                        }
                    }
                }
            }
            regions_read += regions.len();
            done += 1;
            println!("OPEN_ROWS_SECTION n={done} regions={} sites={in_sites} ms={}", regions.len(), started.elapsed().as_millis());
            continue;
        }
        let read: Vec<std::result::Result<(Vec<OpenRows>, Vec<OpenCrowds>), String>> = views
            .par_iter()
            .map(|v| {
                let rows = learner.field.open_rows(v).map_err(|e| e.to_string())?;
                let cr = if with_crowds { learner.field.open_crowds(v).map_err(|e| e.to_string())? } else { Vec::new() };
                Ok((rows, cr))
            })
            .collect();
        for ((slice, _), cells) in regions.iter().zip(read) {
            let (rows, cr) = cells?;
            for (a, c) in acc[*slice].iter_mut().zip(rows) {
                a.add(&c);
            }
            for (a, c) in crowds[*slice].iter_mut().zip(cr) {
                a.add(&c);
            }
        }
        regions_read += regions.len();
        done += 1;
        println!("OPEN_ROWS_SECTION n={done} regions={} sites={in_sites} ms={}", regions.len(), started.elapsed().as_millis());
    }
    let kind = |h: usize| if !d.carries_moment(h) { "still" } else if d.is_depth(h) { "depth" } else { "paced" };
    if with_carried {
        let nats = std::f64::consts::LN_2 / (1u64 << 20) as f64;
        for (s, name) in names.iter().enumerate() {
            let n = carried_compared[s].max(1) as f64;
            for (i, e) in HELD_SIGMAS.iter().enumerate() {
                let Some(&[whole, dropped, carried]) = carried_acc[s].get(i) else { continue };
                println!("CARRIED slice={name} sigma=2^-{e} compared={} rise_nats_a_compared dropped={:.5} carried={:.5} carried_over_dropped={:.3}", carried_compared[s], (dropped - whole) as f64 * nats / n, (carried - whole) as f64 * nats / n, (carried - whole) as f64 / (dropped - whole).max(1) as f64);
            }
        }
        println!("CARRIED_DONE sections={done} regions={regions_read} ms={}", started.elapsed().as_millis());
        return Ok(());
    }
    if with_bytick {
        for (s, name) in names.iter().enumerate() {
            let c = &bytick[s];
            let Some(&full) = c.first() else { continue };
            let rises: Vec<String> = c[1..].iter().enumerate().map(|(k, &v)| format!("t{k}={:.3}", (v - full) as f64 / (1u64 << 20) as f64)).collect();
            println!("BYTICK slice={name} sigma=2^-4 rise_bits {}", rises.join(" "));
        }
        println!("BYTICK_DONE sections={done} regions={regions_read} ms={}", started.elapsed().as_millis());
        return Ok(());
    }
    if with_halves {
        for (s, name) in names.iter().enumerate() {
            let [full, all, a, b, sites] = halves[s];
            let rise = |v: i128| (v - full) as f64 / (1u64 << 20) as f64;
            let (ra, rb, rf) = (rise(a), rise(b), rise(all));
            println!("HALVES slice={name} sigma=2^-4 sites={sites} rise_bits all={rf:.3} half_a={ra:.3} half_b={rb:.3} half_over_all a={:.3} b={:.3} sum_over_all={:.3}", ra / rf, rb / rf, (ra + rb) / rf);
        }
        println!("HALVES_DONE sections={done} regions={regions_read} ms={}", started.elapsed().as_millis());
        return Ok(());
    }
    if with_held {
        let bits = |v: i128| v as f64 / (1u64 << 20) as f64;
        let abits = |v: i128| v as f64 / (1u64 << 40) as f64;
        for (s, name) in names.iter().enumerate() {
            let c = &held[s];
            let (nc, nw) = (c.compared.max(1) as f64, c.written.max(1) as f64);
            for (i, e) in HELD_SIGMAS.iter().enumerate() {
                let (Some(&o), Some(&ch)) = (c.code_oracle.get(i), c.code_chart.get(i)) else { continue };
                let ticks_text: Vec<String> = (0..c.a_all.len())
                    .map(|k| {
                        let (n, ah, abh, abc) = (c.held[i][k], c.a_held[i][k], c.abs_held[i][k], c.abs_chart[i][k]);
                        format!("t{k}:held={:.3} sum_a/abs={:+.3} held_sum_a/abs={:+.3} held_abs_share={:.4} chart_abs_over_oracle={:.2}", n as f64 / nw, c.a_all[k] as f64 / c.abs_all[k].max(1) as f64, ah as f64 / abh.max(1) as f64, abh as f64 / c.abs_all[k].max(1) as f64, abc as f64 / abh.max(1) as f64)
                    })
                    .collect();
                println!(
                    "HELD slice={name} sigma=2^-{e} compared={} written={} code_bits_a_compared full={:.5} oracle={:+.5} chart={:+.5} rise_bits_a_written oracle={:+.5} chart={:+.5} {}",
                    c.compared, c.written, bits(c.code_full) / nc, bits(o - c.code_full) / nc, bits(ch - c.code_full) / nc, bits(o - c.code_full) / nw, bits(ch - c.code_full) / nw, ticks_text.join(" ")
                );
                let _ = abits;
            }
        }
        println!("HELD_DONE sections={done} regions={regions_read} ms={}", started.elapsed().as_millis());
        return Ok(());
    }
    if with_ticks {
        // `a` on `2^(−40)` bits; a share under `σ = 2^(−e)` bits counts the octaves `b ≤ 40 − e` (`|a| < 2^(40 − e)`).
        for (s, name) in names.iter().enumerate() {
            for k in 0..ticks {
                let c = &news[s][k];
                for (kind, label) in ["written", "open"].iter().enumerate() {
                    let n = c.sites[kind].max(1) as f64;
                    let total = c.cost_abs[kind].max(1) as f64;
                    let under = |e: usize| -> (f64, f64) {
                        let top = 40 - e;
                        (c.cost[kind][..=top].iter().sum::<u64>() as f64 / n, c.cost_mass[kind][..=top].iter().sum::<u128>() as f64 / total)
                    };
                    let shares: Vec<String> = [6usize, 5, 4, 3, 2].iter().map(|&e| { let (a, b) = under(e); format!("s2^-{e}:{a:.3}/{b:.4}") }).collect();
                    let hist = |h: &[u64]| -> String { h.iter().enumerate().filter(|&(_, &v)| v > 0).map(|(b, v)| format!("{b}:{v}")).collect::<Vec<_>>().join(",") };
                    println!("TICK_NEWS slice={name} tick={k} kind={label} sites={} unread_current={:.4} rule_misses={}/{} mean_abs_bits={:.6} under_sigma(sites/mass) {}", c.sites[kind], c.unread[kind] as f64 / n, c.rule_misses[0], c.rule_misses[1], c.cost_abs[kind] as f64 / n / (1u64 << 40) as f64, shares.join(" "));
                    println!("TICK_NEWS_OCTAVES slice={name} tick={k} kind={label} cost {} update(80+) {} covector {}", hist(&c.cost[kind]), hist(&c.update[kind]), hist(&c.covector[kind]));
                }
            }
        }
        println!("TICK_NEWS_DONE sections={done} regions={regions_read} ms={}", started.elapsed().as_millis());
        return Ok(());
    }
    if other.is_some() {
        // The median and quartiles of |Δz| by head, tick and octave, in bits (the bin's upper edge, 2^(b+1) on the face's 2^(−16) grain).
        let quantile = |hist: &[u64; 40], q: f64| -> f64 {
            let total: u64 = hist.iter().sum();
            let mut run = 0u64;
            for (b, &c) in hist.iter().enumerate() {
                run += c;
                if run as f64 >= q * total as f64 {
                    return (1u64 << (b + 1)) as f64 / 65536.0;
                }
            }
            f64::NAN
        };
        for h in 0..heads {
            for k in 0..ticks {
                let cell = &jitter[k * heads + h];
                let mut all = [0u64; 40];
                for o in 0..OPEN_OCTAVES {
                    for b in 0..40 {
                        all[b] += cell[o][b];
                    }
                }
                let by: Vec<String> = (0..OPEN_OCTAVES).filter(|&o| cell[o].iter().sum::<u64>() > 0).map(|o| format!("o{o}:{:.4}/{:.4}/{:.4}", quantile(&cell[o], 0.25), quantile(&cell[o], 0.5), quantile(&cell[o], 0.75))).collect();
                println!("FAR_JITTER head={h} kind={} tick={k} pairs={} q25_bits={:.4} median_bits={:.4} q75_bits={:.4} by_octave(q25/median/q75) {}", kind(h), all.iter().sum::<u64>(), quantile(&all, 0.25), quantile(&all, 0.5), quantile(&all, 0.75), by.join(" "));
            }
        }
        println!("OPEN_ROWS_DONE sections={done} regions={regions_read} ms={}", started.elapsed().as_millis());
        return Ok(());
    }
    let frac = |x: u128, total: u128| if total == 0 { 0.0 } else { x as f64 / total as f64 };
    for (s, name) in names.iter().enumerate() {
        for h in 0..heads {
            for k in 0..ticks {
                let c = &acc[s][k * heads + h];
                let total = c.near + c.crowd + c.far.iter().flatten().sum::<u128>();
                let (probed, other): (u128, u128) = (c.far.iter().map(|f| f[1]).sum(), c.far.iter().map(|f| f[0]).sum());
                println!("OPEN_ROWS slice={name} head={h} kind={} tick={k} rows={} near={:.4} crowd={:.4} far_probed={:.4} far_other={:.4}", kind(h), c.rows, frac(c.near, total), frac(c.crowd, total), frac(probed, total), frac(other, total));
                let octaves: Vec<String> = (0..OPEN_OCTAVES)
                    .filter(|&o| c.counted[o][0] + c.counted[o][1] > 0)
                    .map(|o| {
                        let part = |k: usize| {
                            let n = c.counted[o][k].max(1) as f64;
                            format!("{:.4}/{:.1}/{:.3}", frac(c.far[o][k], total), c.effective[o][k] as f64 / 256.0 / n, c.peak[o][k] as f64 / 65536.0 / n)
                        };
                        format!("o{o}:probed={},other={}", part(1), part(0))
                    })
                    .collect();
                println!("OPEN_ROWS_OCTAVES slice={name} head={h} tick={k} (share/renyi2_count/peak) {}", octaves.join(" "));
                if with_crowds {
                    let c = &crowds[s][k * heads + h];
                    let (pairs, band, lock): (u64, u64, u64) = (c.pairs.iter().sum(), c.band_terms.iter().sum(), c.lock_terms.iter().sum());
                    println!("OPEN_CROWDS slice={name} head={h} kind={} tick={k} rows={} far_pairs={pairs} band_terms={band} band_ratio={:.4} lock_terms={lock} lock_ratio={:.4}", kind(h), c.rows, band as f64 / pairs.max(1) as f64, lock as f64 / pairs.max(1) as f64);
                    let by: Vec<String> = (0..OPEN_OCTAVES)
                        .filter(|&o| c.pairs[o] > 0)
                        .map(|o| format!("o{o}:pairs={},band={:.3},lock={:.3},whole_band={:.3},whole_lock={:.3}", c.pairs[o], c.band_terms[o] as f64 / c.pairs[o] as f64, c.lock_terms[o] as f64 / c.pairs[o] as f64, c.band_whole[o] as f64 / c.crowds[o].max(1) as f64, c.lock_whole[o] as f64 / c.crowds[o].max(1) as f64))
                        .collect();
                    println!("OPEN_CROWDS_OCTAVES slice={name} head={h} tick={k} {}", by.join(" "));
                    let wider: Vec<String> = ["quarter_bit", "one_bit", "four_bits"]
                        .iter()
                        .enumerate()
                        .map(|(t, label)| format!("{label}:band={:.4},lock={:.4}", c.band_at[t].iter().sum::<u64>() as f64 / pairs.max(1) as f64, c.lock_at[t].iter().sum::<u64>() as f64 / pairs.max(1) as f64))
                        .collect();
                    println!("OPEN_CROWDS_WIDER slice={name} head={h} tick={k} {}", wider.join(" "));
                    let cover: Vec<String> = ["sixteenth_bit", "quarter_bit", "one_bit", "four_bits"]
                        .iter()
                        .enumerate()
                        .map(|(t, label)| format!("{label}={:.4}", c.cover[t].iter().sum::<u64>() as f64 / pairs.max(1) as f64))
                        .collect();
                    println!("OPEN_CROWDS_COVER slice={name} head={h} kind={} tick={k} (the floor of any grouping by lock, over the far pairs) {}", kind(h), cover.join(" "));
                    let by_octave: Vec<String> = (0..OPEN_OCTAVES).filter(|&o| c.pairs[o] > 0).map(|o| format!("o{o}:{:.3}/{:.3}/{:.3}/{:.3}", c.cover[0][o] as f64 / c.pairs[o] as f64, c.cover[1][o] as f64 / c.pairs[o] as f64, c.cover[2][o] as f64 / c.pairs[o] as f64, c.cover[3][o] as f64 / c.pairs[o] as f64)).collect();
                    println!("OPEN_CROWDS_COVER_OCTAVES slice={name} head={h} tick={k} {}", by_octave.join(" "));
                }
            }
        }
    }
    println!("OPEN_ROWS_DONE sections={done} regions={regions_read} ms={}", started.elapsed().as_millis());
    Ok(())
}

pub fn found_lane(args: &[String]) -> Result<()> {
    if args.len() != 6 {
        return Err("found-lane STATE STATE_SHA KEYS KEYS_SHA OUT".into());
    }
    let started = std::time::Instant::now();
    let text = pinned_read(&args[1], &args[2], STATE_BUDGET)?;
    let learner = Learner::from_text(std::str::from_utf8(&text)?).map_err(|e| e.to_string())?;
    if learner.to_text().as_bytes() != text.as_slice() {
        return Err("a state that does not read and write back byte for byte".into());
    }
    let keys = pinned_read(&args[3], &args[4], STATE_BUDGET)?;
    let out = Path::new(&args[5]);
    if out.exists() {
        return Err("a founded state's path that exists".into());
    }
    let founded = learner.laned(&keys).map_err(|e| e.to_string())?;
    let rest = keys.get(learner.drawn..).ok_or("fewer key bytes than the learner has drawn")?;
    let (field, from) = learner.field.laned(rest).map_err(|e| e.to_string())?;
    if field != founded.field {
        return Err("the learner's founding and the field's differ".into());
    }
    let (old_d, new_d) = (learner.field.declaration, founded.field.declaration);
    let (old_m, new_m) = (learner.field.material_len(), founded.field.material_len());
    let (old_fine, new_fine) = (learner.field.theta.len(), founded.field.theta.len());
    let glue_lens = (learner.field.scale.as_ref().map(|s| s.glue.len()), founded.field.scale.as_ref().map(|s| s.glue.len()));
    let glue_at = (old_m - glue_lens.0.unwrap_or(0), new_m - glue_lens.1.unwrap_or(0));
    let (a, b) = (learner.to_text(), founded.to_text());
    let (la, lb): (Vec<&str>, Vec<&str>) = (a.lines().collect(), b.lines().collect());
    if la.len() != lb.len() {
        return Err(format!("a founding that wrote {} lines for {}", lb.len(), la.len()).into());
    }
    // A line of words over the material's indices `[lo, hi)` (old) and `[nlo, nhi)` (new): every standing word at its mapped place.
    let mapped = |wx: &[&str], wy: &[&str], lo: usize, nlo: usize| -> bool {
        wy.iter().enumerate().all(|(n, w)| match from[nlo + n] {
            Some(o) if (lo..lo + wx.len()).contains(&o) => *w == wx[o - lo],
            Some(_) => false,
            None => true,
        })
    };
    let mut judged = [0usize; 6];
    for (k, (x, y)) in la.iter().zip(&lb).enumerate() {
        let (wx, wy): (Vec<&str>, Vec<&str>) = (x.split(' ').collect(), y.split(' ').collect());
        if x.is_empty() || y.is_empty() {
            return Err(format!("line {k} is empty in the source or the founded state").into());
        }
        let verdict = if x == y {
            judged[0] += 1;
            "equal".to_string()
        } else if k == 0 && wx.len() == wy.len() && wx.iter().zip(&wy).enumerate().all(|(i, (p, q))| i == 2 || p == q) {
            judged[1] += 1;
            format!("head draws {} to {}", wx[2], wy[2])
        } else if k == 1 && wx.len() == wy.len() && wx.iter().zip(&wy).enumerate().all(|(i, (p, q))| i == 2 || i == 10 || p == q) && wy[2] == new_d.width.to_string() && wy[10] == new_d.lanes.to_string() {
            judged[2] += 1;
            format!("declaration width {} to {} lanes {} to {}", old_d.width, new_d.width, old_d.lanes, new_d.lanes)
        } else if wx.len() == old_fine && wy.len() == new_fine && mapped(&wx, &wy, 0, 0) {
            judged[3] += 1;
            format!("fine material {} words to {}", old_fine, new_fine)
        } else if Some(wx.len()) == glue_lens.0 && Some(wy.len()) == glue_lens.1 && mapped(&wx, &wy, glue_at.0, glue_at.1) {
            judged[4] += 1;
            format!("glue {} words to {}", wx.len(), wy.len())
        } else if wx.len() == old_m && wy.len() == new_m && mapped(&wx, &wy, 0, 0) {
            judged[5] += 1;
            format!("moments {} words to {}", old_m, new_m)
        } else {
            return Err(format!("line {k}: a change the founding of a lane does not make").into());
        };
        println!("FOUND_LANE_LINE k={k} {verdict}");
    }
    if judged[2] != 1 || judged[3] != 1 || judged[5] != 2 || (glue_lens.0.is_some() && judged[4] != 1) {
        return Err(format!("a founding whose lines were judged {judged:?}").into());
    }
    std::fs::write(out, b.as_bytes())?;
    println!("FOUND_LANE lines={} equal={} width={} lanes={} material={} founded_material={} lane_entries={} ms={}", la.len(), judged[0], new_d.width, new_d.lanes, old_m, new_m, from.iter().filter(|o| o.is_none()).count(), started.elapsed().as_millis());
    Ok(())
}

/// [definition; Brandon, November 15 02:06Z] **`found-loud STATE STATE_SHA OUT`**: the learner `STATE` whose face reads its sites' loudness
/// ([`Learner::with_loud`]: `κ` and `b` appended at zero, so every face is the source's), written to `OUT`. Before it writes, every line is
/// judged (`FOUND_LOUD_LINE`): the fine field's declaration only its head line's loudness (read back as the source's with the loudness on); the
/// fine field's material and the two moment lines keep every standing word at the place the founding's map gives it, the new words zero; the
/// parts line only one more octave, zero; every other line equal. Anything else is refused and nothing is written. Reads no realization: that
/// every face is kept is read on the card by the line's own held read of the founded state.
pub fn found_loud(args: &[String]) -> Result<()> {
    if args.len() != 4 {
        return Err("found-loud STATE STATE_SHA OUT".into());
    }
    let started = std::time::Instant::now();
    let text = pinned_read(&args[1], &args[2], STATE_BUDGET)?;
    let learner = Learner::from_text(std::str::from_utf8(&text)?).map_err(|e| e.to_string())?;
    if learner.to_text().as_bytes() != text.as_slice() {
        return Err("a state that does not read and write back byte for byte".into());
    }
    let out = Path::new(&args[3]);
    if out.exists() {
        return Err("a founded state's path that exists".into());
    }
    let founded = learner.with_loud().map_err(|e| e.to_string())?;
    let (field, from) = learner.field.with_loud().map_err(|e| e.to_string())?;
    if field != founded.field {
        return Err("the learner's founding and the field's differ".into());
    }
    let old_d = learner.field.declaration;
    let (old_m, new_m) = (learner.field.material_len(), founded.field.material_len());
    let (old_fine, new_fine) = (learner.field.theta.len(), founded.field.theta.len());
    let (a, b) = (learner.to_text(), founded.to_text());
    let (la, lb): (Vec<&str>, Vec<&str>) = (a.lines().collect(), b.lines().collect());
    if la.len() != lb.len() {
        return Err(format!("a founding that wrote {} lines for {}", lb.len(), la.len()).into());
    }
    let mapped = |wx: &[&str], wy: &[&str]| -> bool {
        wy.iter().enumerate().all(|(n, w)| match from[n] {
            Some(o) => o < wx.len() && *w == wx[o],
            None => *w == "0",
        })
    };
    let mut judged = [0usize; 5];
    for (k, (x, y)) in la.iter().zip(&lb).enumerate() {
        let (wx, wy): (Vec<&str>, Vec<&str>) = (x.split(' ').collect(), y.split(' ').collect());
        let verdict = if x == y {
            judged[0] += 1;
            "equal".to_string()
        } else if k == 1 && wy[0] == "hnn-field-v14l" && wx.len() >= 12 && wy.len() == 18 && wx[1..12] == wy[1..12] && wy[17] == "1" && founded.field.declaration == (holonics_engine::field::Declaration { loud: true, ..old_d }) {
            judged[1] += 1;
            format!("declaration {} to {}", wx[0], wy[0])
        } else if wx.len() == old_fine && wy.len() == new_fine && mapped(&wx, &wy) {
            judged[2] += 1;
            format!("fine material {old_fine} words to {new_fine}")
        } else if wx.len() == old_m && wy.len() == new_m && mapped(&wx, &wy) {
            judged[3] += 1;
            format!("moments {old_m} words to {new_m}")
        } else if x.starts_with("parts ") && *y == format!("{x} 0") {
            judged[4] += 1;
            "parts one more octave, zero".to_string()
        } else {
            return Err(format!("line {k}: a change the loudness's founding does not make").into());
        };
        println!("FOUND_LOUD_LINE k={k} {verdict}");
    }
    if judged[1] != 1 || judged[2] != 1 || judged[3] != 2 || (learner.rate_parts.is_some() && judged[4] != 1) {
        return Err(format!("a founding whose lines were judged {judged:?}").into());
    }
    std::fs::write(out, b.as_bytes())?;
    println!("FOUND_LOUD lines={} equal={} material={old_m} founded_material={new_m} loud_entries={} ms={}", la.len(), judged[0], from.iter().filter(|o| o.is_none()).count(), started.elapsed().as_millis());
    Ok(())
}

/// [definition; the lead, November 19 (G-1119-7)] **`found-pump STATE STATE_SHA OUT`**: the learner `STATE` whose carry circles are pumped
/// ([`Learner::with_pump`]: the pump's chart `P` and `p_b` appended at zero, so every face is the source's), written to `OUT`. Before it
/// writes, every line is judged (`FOUND_PUMP_LINE`): the fine field's declaration only its head line's pump (read back as the source's with
/// the pump on, the eleven counts kept); the fine field's material and the first moments keep every standing word at the place the founding's
/// map gives it, the new words zero; the second moments the same, the new words at most two values (the means the chart's rows and its bias
/// open at); every other line equal (the parts line among them: the chart is the `carry` part's). Anything else is refused and nothing is
/// written. Reads no realization: that every face is kept is read on the card by the line's own held read of the founded state.
pub fn found_pump(args: &[String]) -> Result<()> {
    if args.len() != 4 {
        return Err("found-pump STATE STATE_SHA OUT".into());
    }
    let started = std::time::Instant::now();
    let text = pinned_read(&args[1], &args[2], STATE_BUDGET)?;
    let learner = Learner::from_text(std::str::from_utf8(&text)?).map_err(|e| e.to_string())?;
    if learner.to_text().as_bytes() != text.as_slice() {
        return Err("a state that does not read and write back byte for byte".into());
    }
    let out = Path::new(&args[3]);
    if out.exists() {
        return Err("a founded state's path that exists".into());
    }
    let founded = learner.with_pump().map_err(|e| e.to_string())?;
    let (field, from) = learner.field.with_pump().map_err(|e| e.to_string())?;
    if field != founded.field {
        return Err("the learner's founding and the field's differ".into());
    }
    let old_d = learner.field.declaration;
    let (old_m, new_m) = (learner.field.material_len(), founded.field.material_len());
    let (old_fine, new_fine) = (learner.field.theta.len(), founded.field.theta.len());
    let (a, b) = (learner.to_text(), founded.to_text());
    let (la, lb): (Vec<&str>, Vec<&str>) = (a.lines().collect(), b.lines().collect());
    if la.len() != lb.len() {
        return Err(format!("a founding that wrote {} lines for {}", lb.len(), la.len()).into());
    }
    // Every standing word at its mapped place; the new words zero, or (`opened`) at most two values.
    let mapped = |wx: &[&str], wy: &[&str], opened: bool| -> bool {
        let mut fresh = std::collections::BTreeSet::new();
        let kept = wy.iter().enumerate().all(|(n, w)| match from[n] {
            Some(o) => o < wx.len() && *w == wx[o],
            None => {
                fresh.insert(*w);
                opened || *w == "0"
            }
        });
        kept && fresh.len() <= 2
    };
    let mut judged = [0usize; 4];
    for (k, (x, y)) in la.iter().zip(&lb).enumerate() {
        let (wx, wy): (Vec<&str>, Vec<&str>) = (x.split(' ').collect(), y.split(' ').collect());
        let verdict = if x == y {
            judged[0] += 1;
            "equal".to_string()
        } else if k == 1 && wy[0] == "hnn-field-v14p" && wx.len() >= 12 && wy.len() == 21 && wx[1..12] == wy[1..12] && wy[20] == "1" && founded.field.declaration == (holonics_engine::field::Declaration { pump: true, ..old_d }) {
            judged[1] += 1;
            format!("declaration {} to {}", wx[0], wy[0])
        } else if wx.len() == old_fine && wy.len() == new_fine && mapped(&wx, &wy, false) {
            judged[2] += 1;
            format!("fine material {old_fine} words to {new_fine}")
        } else if wx.len() == old_m && wy.len() == new_m && mapped(&wx, &wy, true) {
            judged[3] += 1;
            format!("moments {old_m} words to {new_m}")
        } else {
            return Err(format!("line {k}: a change the pump's founding does not make").into());
        };
        println!("FOUND_PUMP_LINE k={k} {verdict}");
    }
    if judged[1] != 1 || judged[2] != 1 || judged[3] != 2 {
        return Err(format!("a founding whose lines were judged {judged:?}").into());
    }
    std::fs::write(out, b.as_bytes())?;
    println!("FOUND_PUMP lines={} equal={} material={old_m} founded_material={new_m} pump_entries={} ms={}", la.len(), judged[0], from.iter().filter(|o| o.is_none()).count(), started.elapsed().as_millis());
    Ok(())
}

/// A state's text with its pass line replaced by `pass`'s, every other line byte for byte: the written text, its count of lines and the one
/// line that differs (counted from 1), read back and checked (its field the source's, its count of stretches kept). Refused where any other
/// line would differ. The one tool under [`next_pass`] and [`own_states`].
fn with_pass(text: &str, learner: &Learner, pass: StorePass) -> Result<(String, usize, usize)> {
    let stretches = pass.stretches;
    let mut next = learner.clone();
    next.pass = Some(pass);
    let written = next.to_text();
    let (old_lines, new_lines): (Vec<&str>, Vec<&str>) = (text.lines().collect(), written.lines().collect());
    if old_lines.len() != new_lines.len() {
        return Err("a written pass whose state has a different count of lines".into());
    }
    let differing: Vec<usize> = (0..old_lines.len()).filter(|&i| old_lines[i] != new_lines[i]).collect();
    if differing.len() != 1 || !old_lines[differing[0]].starts_with("pass ") {
        return Err(format!("a written pass that changes lines other than the pass line ({:?})", differing).into());
    }
    let back = Learner::from_text(&written).map_err(|e| e.to_string())?;
    if back.pass.as_ref().map(|p| p.stretches) != Some(stretches) || back.field != learner.field || back.pass != next.pass {
        return Err("a written pass whose state does not read back as the source's field, count and pass".into());
    }
    Ok((written, old_lines.len(), differing[0] + 1))
}

/// A pass's slices as `NAME:PIECE:TAKEN`, joined by commas.
fn slices_text(pass: &StorePass) -> String {
    pass.slices.iter().map(|s| format!("{}:{}:{}", s.name, s.piece, s.taken)).collect::<Vec<_>>().join(",")
}

/// [definition; agent-inferred, November 13] `next-pass STATE STATE_SHA OUT`: **a state's next pass over its role**: the state with its pass line's
/// slices set back to their first piece (piece, cursor and places taken zero), its count of stretches kept, so the next pass's cuts and masks
/// are drawn afresh from the key stream (a stretch's length and mask are keyed by that count, [`Cut::next`]) over the same documents, and
/// every other line of the state byte for byte. Refused where the state's pass has not ended (a slice short of its last piece). The written state
/// is read back and checked: its every line but the pass line equal to the source's. Why: the line's first pass over the store's training
/// documents ended at lap 6 (November 13), and a second pass is the same law over the same passage at new states.
pub fn next_pass(args: &[String]) -> Result<()> {
    if args.len() != 4 {
        return Err("next-pass STATE STATE_SHA OUT".into());
    }
    let text = String::from_utf8(pinned_read(&args[1], &args[2], STATE_BUDGET)?)?;
    let out = Path::new(&args[3]);
    if out.exists() {
        return Err(format!("{} exists", out.display()).into());
    }
    let learner = Learner::from_text(&text).map_err(|e| e.to_string())?;
    let before = learner.pass.clone().ok_or("a state with no pass line")?;
    let mut pass = before.clone();
    for slice in &mut pass.slices {
        (slice.piece, slice.cursor, slice.taken) = (0, 0, 0);
    }
    let after = slices_text(&pass);
    let (written, lines, differing) = with_pass(&text, &learner, pass)?;
    std::fs::write(out, &written)?;
    println!("NEXT_PASS stretches={} before={} after={after} lines={lines} differing_line={differing}", before.stretches, slices_text(&before));
    Ok(())
}

/// [definition; agent-inferred, November 16, the theory thread's Build A] `join-store STATE STATE_SHA STORE STORE_SHA OUT`: **a state's pass
/// joined to a grown store**: the state with its pass line set to the store `STORE` (`STORE_SHA` its `STORE.tsv`'s), its slices those of the
/// store's role in the store's order, every slice at its first piece (piece, cursor and places taken zero), its count of stretches kept, and every
/// other line of the state byte for byte (read back and checked, as [`next_pass`]). Refused where the state's slices are not the first of the
/// grown store's, in order, or where the store adds no slice. Why at a new pass: the cut draws the slice whose places taken stand least against its
/// quota ([`holonics_engine::passage::Cut::next`]), so a slice joined in the middle of a pass is drawn alone until it reaches the others' share,
/// or, set to their share, is drawn alone once theirs end: on November 16 the line stood at 0.609 of its pass, and either join would have run
/// some five laps on the joined slices alone. Joined at a new pass, every slice is drawn at its quota from the first section, and the pass ends
/// for all of them together. What the old slices had left of their pass is read on the next one, the same law over the same passage.
pub fn join_store(args: &[String]) -> Result<()> {
    if args.len() != 6 {
        return Err("join-store STATE STATE_SHA STORE STORE_SHA OUT".into());
    }
    let text = String::from_utf8(pinned_read(&args[1], &args[2], STATE_BUDGET)?)?;
    let store = Path::new(&args[3]);
    let counts = store_counts(std::str::from_utf8(&pinned_read(&store.join("STORE.tsv").to_string_lossy(), &args[4], READ_BUDGET as usize)?)?)?;
    let out = Path::new(&args[5]);
    if out.exists() {
        return Err(format!("{} exists", out.display()).into());
    }
    let learner = Learner::from_text(&text).map_err(|e| e.to_string())?;
    let before = learner.pass.clone().ok_or("a state with no pass line")?;
    let names = role_names(&counts, &before.role);
    let held: Vec<&str> = before.slices.iter().map(|s| s.name.as_str()).collect();
    if names.len() <= held.len() || names[..held.len()] != held[..] {
        return Err(format!("a store whose {} slices ({}) do not extend the state's ({})", before.role, names.join(","), held.join(",")).into());
    }
    let mut pass = before.clone();
    pass.store = args[4].clone();
    pass.slices = names.iter().map(|n| PassSlice { name: n.to_string(), piece: 0, cursor: 0, taken: 0 }).collect();
    let after = slices_text(&pass);
    let (written, lines, differing) = with_pass(&text, &learner, pass)?;
    std::fs::write(out, &written)?;
    println!(
        "JOIN_STORE stretches={} store_before={} store_after={} before={} after={after} lines={lines} differing_line={differing}",
        before.stretches,
        before.store,
        args[4],
        slices_text(&before)
    );
    Ok(())
}

/// [definition; agent-inferred, the lead, November 16] `move-store STATE STATE_SHA STORE STORE_SHA SLICE OUT`: **a state's pass moved to a
/// store whose slice `SLICE` was redrawn**: the state with its pass line's store set to `STORE` (`STORE_SHA` its `STORE.tsv`'s), the same
/// slices in the same order, every other slice's place kept, and `SLICE` set to the start of the first piece that begins at or past the
/// places the pass has taken of it (its cursor zero, its places taken kept), so the slice goes on at the share of its octets it stood at
/// and ends its pass with the others; every other line of the state byte for byte (read back and checked, as [`next_pass`]). Refused where
/// the store's slices of the role are not the state's. Why not [`join_store`]: it adds slices at a new pass and sets every slice back to
/// its first piece; a slice redrawn at the same octets changes no quota, and its pieces' lengths alone change, so a kept cursor could
/// stand past its piece's places. Where the pass has taken more than the redrawn slice holds, the slice stands at its end.
pub fn move_store(args: &[String]) -> Result<()> {
    if args.len() != 7 {
        return Err("move-store STATE STATE_SHA STORE STORE_SHA SLICE OUT".into());
    }
    let text = String::from_utf8(pinned_read(&args[1], &args[2], STATE_BUDGET)?)?;
    let store = Path::new(&args[3]);
    let counts = store_counts(std::str::from_utf8(&pinned_read(&store.join("STORE.tsv").to_string_lossy(), &args[4], READ_BUDGET as usize)?)?)?;
    let out = Path::new(&args[6]);
    if out.exists() {
        return Err(format!("{} exists", out.display()).into());
    }
    let learner = Learner::from_text(&text).map_err(|e| e.to_string())?;
    let before = learner.pass.clone().ok_or("a state with no pass line")?;
    let names = role_names(&counts, &before.role);
    if before.slices.iter().map(|s| s.name.as_str()).ne(names.iter().copied()) {
        return Err(format!("a store whose {} slices ({}) are not the state's", before.role, names.join(",")).into());
    }
    let at = before.slices.iter().position(|s| s.name == args[5]).ok_or_else(|| format!("a pass with no slice {}", args[5]))?;
    let pieces = open_slice(store, &before.role, &args[5], &counts)?.pieces;
    let taken = before.slices[at].taken;
    let piece = pieces.partition_point(|p| p.offset < taken);
    let mut pass = before.clone();
    pass.store = args[4].clone();
    (pass.slices[at].piece, pass.slices[at].cursor) = (piece as u64, 0);
    let (written, lines, differing) = with_pass(&text, &learner, pass)?;
    std::fs::write(out, &written)?;
    println!(
        "MOVE_STORE stretches={} store_before={} store_after={} slice={} pieces={} taken={taken} piece_before={} cursor_before={} piece_after={piece} piece_offset={} lines={lines} differing_line={differing}",
        before.stretches,
        before.store,
        args[4],
        args[5],
        pieces.len(),
        before.slices[at].piece,
        before.slices[at].cursor,
        pieces.get(piece).map_or("end".to_string(), |p| p.offset.to_string())
    );
    Ok(())
}

/// [definition; agent-inferred, November 16, the theory thread's Build B] `set-world STATE STATE_SHA SLICE EVERY RECORDS RUN OUT`: **a world
/// joined to a state's pass** ([`holonics_engine::field::PassWorld`]): the state with its pass line's world clause set (one stretch in
/// `EVERY` of `SLICE` an act, its last `RECORDS` whole lines the prompt, `RUN` places released), its place in the pass kept, and every
/// other line byte for byte (read back and checked, as [`next_pass`]). Refused where the pass holds no slice `SLICE`.
pub fn set_world(args: &[String]) -> Result<()> {
    if args.len() != 8 && args.len() != 9 {
        return Err("set-world STATE STATE_SHA SLICE EVERY RECORDS RUN OUT [REFINE]".into());
    }
    let text = String::from_utf8(pinned_read(&args[1], &args[2], STATE_BUDGET)?)?;
    let out = Path::new(&args[7]);
    if out.exists() {
        return Err(format!("{} exists", out.display()).into());
    }
    let learner = Learner::from_text(&text).map_err(|e| e.to_string())?;
    let before = learner.pass.clone().ok_or("a state with no pass line")?;
    if !before.slices.iter().any(|s| s.name == args[3]) {
        return Err(format!("a pass with no slice {}", args[3]).into());
    }
    let refine = match args.get(8) { Some(r) => r.parse::<u64>().map_err(|_| "REFINE is zero or one")?, None => 0 };
    if refine > 1 {
        return Err("REFINE is zero or one".into());
    }
    let world = holonics_engine::field::PassWorld { slice: args[3].clone(), every: positive(&args[4])? as u64, records: positive(&args[5])? as u64, run: positive(&args[6])? as u64, refine };
    let pass = StorePass { world: Some(world), ..before.clone() };
    let line = pass.to_line();
    let (written, lines, differing) = with_pass(&text, &learner, pass)?;
    std::fs::write(out, &written)?;
    println!("SET_WORLD stretches={} lines={lines} differing_line={differing} pass_tail={}", before.stretches, line.rsplit(" world ").next().map_or(String::new(), |w| format!("world {w}")));
    Ok(())
}

/// [definition; theory, November 16 19:10Z, the crossing triad] `grow-crossings STATE STATE_SHA KEYS KEYS_SHA TRIADS OUT`: **the learner with crossing
/// triads** ([`holonics_engine::field::Learner::with_crossings`]): `TRIADS` triads whose legs stand at the site, their charts drawn from the key
/// stream past the learner's draws, their return `W_T` at zero, so every face the grown field reads is the field's before it, bit for bit; every
/// standing entry keeps its value, its moments and its rate at its new index, and the pass is kept. Refused on a learner that has triads.
pub fn grow_crossings(args: &[String]) -> Result<()> {
    if args.len() != 7 {
        return Err("grow-crossings STATE STATE_SHA KEYS KEYS_SHA TRIADS OUT".into());
    }
    let text = String::from_utf8(pinned_read(&args[1], &args[2], STATE_BUDGET)?)?;
    let keys = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let triads = positive(&args[5])?;
    let out = Path::new(&args[6]);
    if out.exists() {
        return Err(format!("{} exists", out.display()).into());
    }
    let learner = Learner::from_text(&text).map_err(|e| e.to_string())?;
    let grown = learner.with_crossings(triads, &keys).map_err(|e| e.to_string())?;
    let written = grown.to_text();
    let back = Learner::from_text(&written).map_err(|e| e.to_string())?;
    if back.to_text() != written || back.field != grown.field || back.pass != learner.pass {
        return Err("a grown learner that does not read back as itself with its pass".into());
    }
    std::fs::write(out, &written)?;
    let (old, new) = (learner.field.material_len(), grown.field.material_len());
    let d = grown.field.declaration;
    println!("GROW_CROSSINGS triads={} crossing={} material_before={old} material_after={new} drawn_before={} drawn_after={}", d.triads, d.crossing, learner.drawn, grown.drawn);
    Ok(())
}

/// [measurement; theory, November 16 19:10Z, G-tr2] `zero-triad-return STATE STATE_SHA OUT`: **a control for the triads**: the state with its
/// triads' return `W_T` set to zero (every other entry, moment and line as it stands), so a reading of it is the field's faces with the
/// triads' products unread. A ruler's state: never trained from. Refused on a state with no triads.
pub fn zero_triad_return(args: &[String]) -> Result<()> {
    if args.len() != 4 {
        return Err("zero-triad-return STATE STATE_SHA OUT".into());
    }
    let text = String::from_utf8(pinned_read(&args[1], &args[2], STATE_BUDGET)?)?;
    let out = Path::new(&args[3]);
    if out.exists() {
        return Err(format!("{} exists", out.display()).into());
    }
    let mut learner = Learner::from_text(&text).map_err(|e| e.to_string())?;
    let d = learner.field.declaration;
    if d.triads == 0 {
        return Err("a state with no triads".into());
    }
    let l = learner.field.layout().clone();
    let span = l.w_triad..l.w_triad + d.width * 2 * d.triads;
    let moved = learner.field.theta[span.clone()].iter().filter(|&&v| v != 0).count();
    learner.field.theta[span].fill(0);
    std::fs::write(out, learner.to_text())?;
    println!("ZERO_TRIAD_RETURN triads={} crossing={} entries={} nonzero_before={moved}", d.triads, d.crossing, d.width * 2 * d.triads);
    Ok(())
}

/// [measurement; the lead, November 17 01:26Z] `read-pace UNITS UNITS_SHA CODEC CODEC_SHA STATE STATE_SHA`: **the turned heads' located rates,
/// by symbol**: for each paced head, its clock's rate `κ = 1 + c_h[u]` (`Loci::pace`, on the material's grain) at the ten digits, the
/// space, the signs `+ - * =`, the line feed and the letters `a e t`, in thousandths. A ruler: it names symbols by their bytes, outside the
/// machine, and reads a state. Why: a digit that advanced a ring by its own value would show rates rising with the digit, and a clock in
/// a number's own frame would stand still on digits and step at separators; this reads where deposition has put them.
pub fn read_pace(args: &[String]) -> Result<()> {
    if args.len() != 7 {
        return Err("read-pace UNITS UNITS_SHA CODEC CODEC_SHA STATE STATE_SHA".into());
    }
    let units = units_of(&args[1], &args[2])?;
    let codec = Codec::from_text(&String::from_utf8(pinned_read(&args[3], &args[4], READ_BUDGET as usize)?)?, units)?;
    let learner = Learner::from_text(std::str::from_utf8(&pinned_read(&args[5], &args[6], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let d = learner.field.declaration;
    let (at, rows) = (learner.field.layout().pace, d.alphabet + 1);
    let named: Vec<(String, u8)> = (b'0'..=b'9').map(|b| ((b as char).to_string(), b)).chain([("space".to_string(), b' '), ("+".to_string(), b'+'), ("-".to_string(), b'-'), ("*".to_string(), b'*'), ("=".to_string(), b'='), ("feed".to_string(), b'\n'), ("a".to_string(), b'a'), ("e".to_string(), b'e'), ("t".to_string(), b't')]).collect();
    // The rings a turned head's modes stand on: slot `l (frames − still) + (head − still)` of the solenoid's periods, mode `l` of the head.
    let periods = holonics_engine::field::ring_periods(d.turned_slots(), d.reach);
    println!("PACE_RINGS slots={} reach={} periods={}", d.turned_slots(), d.reach, periods.iter().map(usize::to_string).collect::<Vec<_>>().join(","));
    for p in 0..d.paced_heads() {
        let mine: Vec<String> = (0..d.modes).map(|l| periods[l * (d.frames - d.still) + p].to_string()).collect();
        println!("PACE_HEAD paced_head={p} modes_on_rings={}", mine.join(","));
    }
    for p in 0..d.paced_heads() {
        let mut line = format!("PACE paced_head={p}");
        for (name, byte) in &named {
            let class = codec.encode(&[*byte])?[0];
            let c = learner.field.theta[at + p * rows + class] as i128;
            let kappa = (1i128 << holonics_engine::field::MATERIAL_BITS) + c;
            line.push_str(&format!(" {name}={}", (kappa * 1000) >> holonics_engine::field::MATERIAL_BITS));
        }
        println!("{line}");
    }
    Ok(())
}

/// [measurement; the lead, November 17 09:50Z] `read-triads STATE STATE_SHA`: **the triads' material as it stands, by triad**: for each of the
/// `J` triads the root mean square of its return's two columns of `W_T` (`Loci::w_triad`, the real and the imaginary product's) and of its
/// three legs' rows of the charts `A`, `B` and `G` (`Loci::triad`), in millionths of the material's unit, with its legs' biases in thousandths
/// of the face's; and beside them the root mean square of the pairs' return `W`. A ruler reading a state. Why: a founding that sets a triad's
/// legs where the tension leads releases what that triad's return holds, so what each standing triad carries is read before any is founded
/// again.
pub fn read_triads(args: &[String]) -> Result<()> {
    if args.len() != 3 {
        return Err("read-triads STATE STATE_SHA".into());
    }
    let learner = Learner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let d = learner.field.declaration;
    let l = learner.field.layout();
    let (dw, f, j, j2) = (d.width, d.contacts, d.triads, 2 * d.triads);
    let theta = &learner.field.theta;
    // The root mean square of a list of entries on the material's grain, in millionths of its unit.
    let rms = |values: &mut dyn Iterator<Item = i64>| -> u128 {
        let (mut sum, mut n) = (0u128, 0u128);
        for v in values {
            sum += (v as i128 * v as i128) as u128;
            n += 1;
        }
        if n == 0 {
            return 0;
        }
        ((sum / n).isqrt() * 1_000_000) >> holonics_engine::field::MATERIAL_BITS
    };
    println!("TRIADS triads={j} width={dw} crossing={} pairs_return_rms_millionths={}", d.crossing, rms(&mut theta[l.w..l.w + dw * f].iter().map(|&v| v as i64)));
    for k in 0..j {
        let ret = rms(&mut (0..dw).flat_map(|o| [theta[l.w_triad + o * j2 + k] as i64, theta[l.w_triad + o * j2 + j + k] as i64]));
        let leg = |chart: usize| rms(&mut [k, j + k].into_iter().flat_map(|row| theta[l.triad + (chart * j2 + row) * dw..l.triad + (chart * j2 + row + 1) * dw].iter().map(|&v| v as i64)));
        let bias = |chart: usize| -> String { [k, j + k].iter().map(|row| ((theta[l.triad_bias + chart * j2 + row] as i128 * 1000) >> holonics_engine::field::FACE_BITS).to_string()).collect::<Vec<_>>().join(",") };
        println!("TRIAD k={k} return_rms={ret} leg_a_rms={} leg_b_rms={} leg_g_rms={} bias_a={} bias_b={} bias_g={}", leg(0), leg(1), leg(2), bias(0), bias(1), bias(2));
    }
    Ok(())
}

/// [measurement; the lead, November 16 23:58Z; atlas `contact.row-heat-keys-short`] `ruler-temper STATE STATE_SHA HEAD MILLI OUT`: **a ruler's
/// state with one head's listener cooled**: the state with `MILLI` thousandths of an octave added to head `HEAD`'s listener temperature
/// (`Loci::temper`, `[h][1]`, the logarithm of the row's gain on the material's grain), every other entry, moment and line kept. A ruler's
/// state for a reading of what a row would gather at another gain with its present keys; never trained from, and no law reads it. Why a state
/// and not a reading's argument: a temperature is a store's state (CLAUDE.md), so the ruler moves the store and the reads stay the engine's own.
pub fn ruler_temper(args: &[String]) -> Result<()> {
    if args.len() != 6 {
        return Err("ruler-temper STATE STATE_SHA HEAD MILLI OUT".into());
    }
    let text = String::from_utf8(pinned_read(&args[1], &args[2], STATE_BUDGET)?)?;
    let out = Path::new(&args[5]);
    if out.exists() {
        return Err(format!("{} exists", out.display()).into());
    }
    let mut learner = Learner::from_text(&text).map_err(|e| e.to_string())?;
    let d = learner.field.declaration;
    let head: usize = args[3].parse().map_err(|_| "HEAD is a head's count")?;
    if head >= d.heads {
        return Err(format!("a state of {} heads", d.heads).into());
    }
    let milli: i64 = args[4].parse().map_err(|_| "MILLI is thousandths of an octave")?;
    let at = learner.field.layout().temper + 2 * head + 1;
    let before = learner.field.theta[at];
    let delta = (milli as i128 * (1i128 << holonics_engine::field::MATERIAL_BITS)) / 1000;
    let after = i32::try_from(before as i128 + delta).map_err(|_| "a temperature past its entry")?;
    learner.field.theta[at] = after;
    std::fs::write(out, learner.to_text())?;
    println!("RULER_TEMPER head={head} milli={milli} before={before} after={after} grain_bits={}", holonics_engine::field::MATERIAL_BITS);
    Ok(())
}

/// [definition; the lead, November 16 21:40Z; atlas `contact.pool-founding`] `found-crossing STATE STATE_SHA LEGS LEGS_SHA OUT [RETURN RETURN_SHA]`:
/// **the triads' legs founded where the tension leads** ([`holonics_engine::field::Learner::with_located_legs`]). `LEGS` holds the charts `A`, `B`
/// and `G` and then their biases as the state lays them (`6J × D + 6J` entries, little-endian 32-bit integers on the material's grain), read by
/// a ruler on the host from `read-tension`'s rows (`tools/tension_ruler.py`). Without `RETURN` the triads' return `W_T` is set to zero, so every
/// face reads bit for bit as the state's before it: a founding, and a lap may train from it. With `RETURN` (`D × 2J` entries, the same form) the
/// return is the ruler's regression too: a ruler's state for a capacity read, never trained from. Every other entry, moment, rate and line is
/// kept; the triads' moments open as a growth opens them.
pub fn found_crossing(args: &[String]) -> Result<()> {
    if args.len() != 6 && args.len() != 8 {
        return Err("found-crossing STATE STATE_SHA LEGS LEGS_SHA OUT [RETURN RETURN_SHA]".into());
    }
    let text = String::from_utf8(pinned_read(&args[1], &args[2], STATE_BUDGET)?)?;
    let words = |bytes: Vec<u8>| -> Result<Vec<i32>> {
        if bytes.len() % 4 != 0 {
            return Err("a material file that is not whole 32-bit words".into());
        }
        Ok(bytes.chunks_exact(4).map(|w| i32::from_le_bytes([w[0], w[1], w[2], w[3]])).collect())
    };
    let legs = words(pinned_read(&args[3], &args[4], READ_BUDGET as usize)?)?;
    let out = Path::new(&args[5]);
    if out.exists() {
        return Err(format!("{} exists", out.display()).into());
    }
    let ret = match args.get(6) {
        Some(path) => Some(words(pinned_read(path, &args[7], READ_BUDGET as usize)?)?),
        None => None,
    };
    let learner = Learner::from_text(&text).map_err(|e| e.to_string())?;
    let founded = learner.with_located_legs(&legs, ret.as_deref()).map_err(|e| e.to_string())?;
    let written = founded.to_text();
    let back = Learner::from_text(&written).map_err(|e| e.to_string())?;
    if back.to_text() != written || back.field != founded.field || back.pass != learner.pass {
        return Err("a founded learner that does not read back as itself with its pass".into());
    }
    std::fs::write(out, &written)?;
    let d = founded.field.declaration;
    let l = founded.field.layout().clone();
    let moved = learner.field.theta[l.triad..l.triad + 6 * d.triads * d.width].iter().zip(&founded.field.theta[l.triad..l.triad + 6 * d.triads * d.width]).filter(|(a, b)| a != b).count();
    let standing = founded.field.theta[l.w_triad..l.w_triad + d.width * 2 * d.triads].iter().filter(|&&v| v != 0).count();
    println!("FOUND_CROSSING triads={} crossing={} legs_entries={} legs_moved={moved} return={} return_nonzero={standing}", d.triads, d.crossing, legs.len(), if ret.is_some() { "ruler" } else { "zero" });
    Ok(())
}

/// [measurement; the lead, November 17, the record of the step back §7] `hold-families STATE STATE_SHA OUT FAMILY…`: **a learner whose
/// deposit moves the named families alone**: every entry outside them takes its own rate of 100 bits, at which a step releases to zero,
/// and every entry inside them the learner's rate (each entry's own rate, [`Learner::own_rates`], written as the state's `rates` line).
/// The families are named as the layout names them (`q`, `q_bias`, `probe`, `probe_bias`, `temper`, `read`, `read_bias`, `lift_bias`,
/// `v`, `v_bias`, `out`, `out_bias`, `closed_odds`, `closed_odds_bias`, `enc`). Why: the lap law finishes a block's bridge with the rest
/// of the constitution held (the staircase record of October 25, §1: a block pass that held every family but the readouts kept what was
/// founded, and a full stepped pass eroded it). A study's tool: it writes a new state and changes no law.
pub fn hold_families(args: &[String]) -> Result<()> {
    if args.len() < 5 {
        return Err("hold-families STATE STATE_SHA OUT FAMILY…".into());
    }
    let text = String::from_utf8(pinned_read(&args[1], &args[2], STATE_BUDGET)?)?;
    let out = Path::new(&args[3]);
    if out.exists() {
        return Err(format!("{} exists", out.display()).into());
    }
    let mut learner = Learner::from_text(&text).map_err(|e| e.to_string())?;
    let d = learner.field.declaration;
    let l = learner.field.layout().clone();
    let (dw, m2, a, h) = (d.width, 2 * d.heads * d.modes, d.alphabet, d.heads);
    let mut rates = vec![100u32; learner.field.material_len()];
    let mut moved = 0usize;
    for name in &args[4..] {
        let (start, len) = match name.as_str() {
            "enc" => (l.enc, (a + 1) * dw),
            "q" => (l.q, m2 * dw),
            "q_bias" => (l.q_bias, m2),
            "v" => (l.v, m2 * dw),
            "v_bias" => (l.v_bias, m2),
            "out" => (l.out, dw * m2),
            "out_bias" => (l.out_bias, dw),
            "probe" => (l.probe, m2 * dw),
            "probe_bias" => (l.probe_bias, m2),
            "temper" => (l.temper, 2 * h),
            "read" => (l.read, dw * dw),
            "read_bias" => (l.read_bias, a),
            "lift_bias" => (l.lift_bias, dw),
            "closed_odds" => (l.closed_odds, usize::from(d.closed > 0) * h * dw),
            "closed_odds_bias" => (l.closed_odds_bias, usize::from(d.closed > 0) * h),
            _ => return Err(format!("hold-families knows no family {name}").into()),
        };
        rates[start..start + len].fill(learner.rate_bits);
        moved += len;
    }
    learner.own_rates = Some(rates);
    let written = learner.to_text();
    if Learner::from_text(&written).map_err(|e| e.to_string())?.to_text() != written {
        return Err("a held learner that does not read back as itself".into());
    }
    std::fs::write(out, &written)?;
    println!("HOLD_FAMILIES moving={} entries_moving={moved} entries_held={} rate_bits={}", args[4..].join(","), learner.field.material_len() - moved, learner.rate_bits);
    Ok(())
}

/// [definition; the lead, November 17, the step back's record §11] `set-leak STATE STATE_SHA BITS OUT`: **a learner with the store's leak
/// set** ([`Learner::leak`]): every material entry relaxes by `2^(−BITS)` of itself after each section's step; `BITS` of zero clears it.
/// The leak is law and is carried in the learner's state, never in a run's switch. It writes a new state.
pub fn set_leak(args: &[String]) -> Result<()> {
    if args.len() != 5 {
        return Err("set-leak STATE STATE_SHA BITS OUT".into());
    }
    let text = String::from_utf8(pinned_read(&args[1], &args[2], STATE_BUDGET)?)?;
    let bits: u32 = args[3].parse()?;
    let out = Path::new(&args[4]);
    if out.exists() {
        return Err(format!("{} exists", out.display()).into());
    }
    let mut learner = Learner::from_text(&text).map_err(|e| e.to_string())?;
    learner.leak = (bits > 0).then_some(bits);
    let written = learner.to_text();
    if Learner::from_text(&written).map_err(|e| e.to_string())?.to_text() != written {
        return Err("a leaking learner that does not read back as itself".into());
    }
    std::fs::write(out, &written)?;
    println!("SET_LEAK bits={bits} rate_bits={} entries={}", learner.rate_bits, learner.field.material_len());
    Ok(())
}

/// [definition; the lead, November 18, the audit of that day §1.1 and §1.8] `set-rate STATE STATE_SHA BITS OUT [remainder]`: **a learner
/// with the deposit's rate set** to `2^(−BITS)` (every moment, entry and line as it stands; the moments are the covector's and do not
/// read the rate), and with the word `remainder` its steps' remainders carried from zero ([`Learner::remainder`]), without which a cooler
/// rate's step truncates to nothing on the face-grain entries. The rate and the remainder are law and are carried in the learner's state.
/// It writes a new state.
pub fn set_rate(args: &[String]) -> Result<()> {
    if args.len() != 5 && !(args.len() == 6 && args[5] == "remainder") {
        return Err("set-rate STATE STATE_SHA BITS OUT [remainder]".into());
    }
    let text = String::from_utf8(pinned_read(&args[1], &args[2], STATE_BUDGET)?)?;
    let bits: u32 = args[3].parse()?;
    let out = Path::new(&args[4]);
    if out.exists() {
        return Err(format!("{} exists", out.display()).into());
    }
    let mut learner = Learner::from_text(&text).map_err(|e| e.to_string())?;
    if bits == 0 || bits >= 32 {
        return Err("a rate under one bit or past thirty-one".into());
    }
    let before = learner.rate_bits;
    learner.rate_bits = bits;
    if args.len() == 6 && learner.remainder.is_none() {
        learner.remainder = Some(vec![0; learner.field.material_len()]);
    }
    let written = learner.to_text();
    if Learner::from_text(&written).map_err(|e| e.to_string())?.to_text() != written {
        return Err("a learner that does not read back as itself".into());
    }
    std::fs::write(out, &written)?;
    println!("SET_RATE rate_bits={bits} before={before} remainder={} entries={}", learner.remainder.is_some(), learner.field.material_len());
    Ok(())
}

/// [definition; the lead, November 18, the audit of that day §1.4] `set-frontier STATE STATE_SHA EIGHTHS OUT`: **a learner whose pass reads
/// a share of its stretches at the frontier** ([`holonics_engine::field::StorePass::frontier`]): `EIGHTHS` of every eight stretches, keyed by
/// the stretch's count, are the context known and the next place alone open ([`holonics_engine::passage::frontier_state_of`]), the state
/// a writer in place order meets; zero takes the share off. Every other line byte for byte, read back and checked. The share is law and
/// is carried in the learner's state. It writes a new state.
pub fn set_frontier(args: &[String]) -> Result<()> {
    // [the lead, November 18, the frontier record §6] With the word `before` last, the frontier's stretches are read as known streams
    // ([`holonics_engine::field::StorePass::before`]); without it they are read as the law reads any region.
    // With the word `strand` last they are read by two streams ([`holonics_engine::field::StorePass::strand`]): every place compared.
    // A last word `past` after either: their odd strand contacts face the past ([`holonics_engine::field::StorePass::past`]).
    // [the record of the two streams §15] A last word `second` after either, or after `past`: their row of the site after reads the second
    // site before ([`holonics_engine::field::StorePass::second`]).
    let second = (args.len() == 7 || args.len() == 8) && args[args.len() - 1] == "second";
    let words = args.len() - usize::from(second);
    let past = words == 7 && args[6] == "past";
    let reading = if words == 6 || past { args.get(5).map(String::as_str) } else { None };
    let (known, strand) = (reading == Some("before"), reading == Some("strand"));
    if words != 5 && !known && !strand {
        return Err("set-frontier STATE STATE_SHA EIGHTHS OUT [before | strand [past] [second]]".into());
    }
    let text = String::from_utf8(pinned_read(&args[1], &args[2], STATE_BUDGET)?)?;
    let share: u64 = args[3].parse()?;
    let out = Path::new(&args[4]);
    if out.exists() {
        return Err(format!("{} exists", out.display()).into());
    }
    if share > 8 {
        return Err("a frontier's share past eight of every eight stretches".into());
    }
    let learner = Learner::from_text(&text).map_err(|e| e.to_string())?;
    let before = learner.pass.clone().ok_or("a state with no pass line")?;
    if before.frontier == share && before.before == known && before.strand == strand && before.past == past && before.second == second {
        return Err("a state whose frontier share and reading are already those".into());
    }
    if (known || strand) && share == 0 {
        return Err("known streams and two streams read the frontier's stretches: a share of zero has none".into());
    }
    let (written, lines, differing) = with_pass(&text, &learner, StorePass { frontier: share, before: known, strand, past, second, ..before.clone() })?;
    std::fs::write(out, &written)?;
    println!("SET_FRONTIER share={share} known_streams={known} two_streams={strand} past={past} second={second} before={} before_known_streams={} before_two_streams={} stretches={} slices={} lines={lines} differing_line={differing}", before.frontier, before.before, before.strand, before.stretches, slices_text(&before));
    Ok(())
}

/// [definition; the lead, November 18, the record of the two streams §11] `open-level STATE STATE_SHA OUT`: **the learner whose level is
/// opened to one-sided streams** ([`Learner::level_before`]): the block a passage read by two streams takes the epoch before each place
/// through, at zero, so every face reads as before. Before it writes, the founded text is read back as itself, and its lines are judged:
/// the glue's line and the lines that hold a word an entry (the two moments', and where the state carries them the entries' rates and the
/// step's remainder) each keep every standing word and end in the block's zeros (the rates' in the base rate); every other line is
/// equal. Anything else is refused and nothing is written. The block is law and is carried in the learner's state.
pub fn open_level(args: &[String]) -> Result<()> {
    if args.len() != 4 {
        return Err("open-level STATE STATE_SHA OUT".into());
    }
    let text = String::from_utf8(pinned_read(&args[1], &args[2], STATE_BUDGET)?)?;
    let out = Path::new(&args[3]);
    if out.exists() {
        return Err(format!("{} exists", out.display()).into());
    }
    let learner = Learner::from_text(&text).map_err(|e| e.to_string())?;
    if learner.to_text() != text {
        return Err("a state that does not read and write back byte for byte".into());
    }
    let founded = learner.level_before().map_err(|e| e.to_string())?;
    let written = founded.to_text();
    if Learner::from_text(&written).map_err(|e| e.to_string())?.to_text() != written {
        return Err("a founded learner that does not read back as itself".into());
    }
    let (old_m, new_m) = (learner.field.material_len(), founded.field.material_len());
    let block = new_m - old_m;
    let (la, lb): (Vec<&str>, Vec<&str>) = (text.lines().collect(), written.lines().collect());
    if la.len() != lb.len() {
        return Err(format!("a founding that wrote {} lines for {}", lb.len(), la.len()).into());
    }
    let (mut grown, mut equal) = (0usize, 0usize);
    for (n, (x, y)) in la.iter().zip(&lb).enumerate() {
        if x == y {
            equal += 1;
            continue;
        }
        // A grown line: the standing words, then the block's words, each the same (zero, or the base rate on the rates' line).
        let rest = y.strip_prefix(x).ok_or_else(|| format!("line {}: a founded line that does not keep its standing words", n + 1))?;
        let added: Vec<&str> = rest.split(' ').filter(|w| !w.is_empty()).collect();
        let rate = learner.rate_bits.to_string();
        if added.len() != block || !(added.iter().all(|w| *w == "0") || added.iter().all(|w| *w == rate)) {
            return Err(format!("line {}: a founded line that grew by {} words where the block holds {block}, or by words that are not its opening", n + 1, added.len()).into());
        }
        grown += 1;
    }
    if grown < 3 {
        return Err(format!("a founding that grew {grown} lines: the glue's and the two moments' are three").into());
    }
    std::fs::write(out, &written)?;
    println!("OPEN_LEVEL entries_before={old_m} entries={new_m} block={block} lines={} grown={grown} equal={equal}", la.len());
    Ok(())
}

/// [measurement; the lead, November 18, the audit of that day (decide the level)] `zero-level-return STATE STATE_SHA OUT`: **a control for
/// the level**: the state with its level's prolongation, `B` and `b_B`, set to zero (every other entry, moment and line as it stands), so a
/// reading of it is the field's faces with the level unheard. A ruler's state: never trained from. Refused on a state with no level.
pub fn zero_level_return(args: &[String]) -> Result<()> {
    if args.len() != 4 {
        return Err("zero-level-return STATE STATE_SHA OUT".into());
    }
    let text = String::from_utf8(pinned_read(&args[1], &args[2], STATE_BUDGET)?)?;
    let out = Path::new(&args[3]);
    if out.exists() {
        return Err(format!("{} exists", out.display()).into());
    }
    let mut learner = Learner::from_text(&text).map_err(|e| e.to_string())?;
    let width = learner.field.declaration.width;
    let scale = learner.field.scale.as_deref_mut().ok_or("a state with no level")?;
    let (_, _, b, _, len) = scale.glue_offsets(width);
    let moved = scale.glue[b..len].iter().filter(|&&v| v != 0).count();
    scale.glue[b..len].fill(0);
    std::fs::write(out, learner.to_text())?;
    println!("ZERO_LEVEL_RETURN entries={} nonzero_before={moved}", len - b);
    Ok(())
}

/// [definition; the lead, November 17, the founding records] `found-closed STATE STATE_SHA CLOSED CLOSED_SHA OUT`: **the closed characters
/// founded from a ruler's words** ([`Learner::with_closed`]). `CLOSED` is little-endian 32-bit words: `E`, then the keys (`A × 2E` on
/// `2^(−16)`: a class's `E` real parts, then its `E` imaginary parts), then the odds (`heads` rows of `D` on `2^(−24)`, then a bias a head
/// on `2^(−16)`). The card refuses the founded state until the closed face's realization is built.
pub fn found_closed(args: &[String]) -> Result<()> {
    if args.len() != 6 {
        return Err("found-closed STATE STATE_SHA CLOSED CLOSED_SHA OUT".into());
    }
    let text = String::from_utf8(pinned_read(&args[1], &args[2], STATE_BUDGET)?)?;
    let bytes = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    if bytes.len() % 4 != 0 || bytes.len() < 4 {
        return Err("a closed characters' file that is not whole 32-bit words".into());
    }
    let words: Vec<i32> = bytes.chunks_exact(4).map(|w| i32::from_le_bytes([w[0], w[1], w[2], w[3]])).collect();
    let out = Path::new(&args[5]);
    if out.exists() {
        return Err(format!("{} exists", out.display()).into());
    }
    let learner = Learner::from_text(&text).map_err(|e| e.to_string())?;
    let d = learner.field.declaration;
    let closed = usize::try_from(words[0]).map_err(|_| "a count of closed characters below zero")?;
    let keys_len = d.alphabet * 2 * closed;
    if words.len() != 1 + keys_len + d.heads * (d.width + 1) {
        return Err("a closed characters' file that is not its count, its keys and its odds".into());
    }
    let founded = learner.with_closed(closed, &words[1..1 + keys_len], &words[1 + keys_len..]).map_err(|e| e.to_string())?;
    let written = founded.to_text();
    let back = Learner::from_text(&written).map_err(|e| e.to_string())?;
    if back.to_text() != written || back.field != founded.field || back.pass != learner.pass {
        return Err("a founded learner that does not read back as itself with its pass".into());
    }
    std::fs::write(out, &written)?;
    let l = founded.field.layout().clone();
    let on_ring = (0..d.alphabet).filter(|a| founded.field.theta[l.closed_key + a * 2 * closed..l.closed_key + (a + 1) * 2 * closed].iter().any(|&v| v != 0)).count();
    let standing = founded.field.theta[l.closed_odds..l.closed_odds + d.heads * d.width].iter().filter(|&&v| v != 0).count();
    println!("FOUND_CLOSED closed={closed} classes_on_ring={on_ring} odds_rows_nonzero={standing} odds_biases={:?} material_before={} material_after={}", &founded.field.theta[l.closed_odds_bias..l.closed_odds_bias + d.heads], learner.field.material_len(), founded.field.material_len());
    Ok(())
}

/// [definition; the lead, November 18, the record of the two streams §19] `grow-carry STATE STATE_SHA KEYS KEYS_SHA CIRCLES OUT`: **a state
/// with `CIRCLES` more carry circles** ([`holonics_engine::field::Learner::more_carry`]), founded as its first were, the draws read from
/// the key stream past every draw the learner has read. The state is read and must write back byte for byte; the founded learner must read
/// back as itself with the passage's place, the parts' rates, the laps and the rate it stood at; every standing entry of the material is
/// carried once with its value (checked here against the field's own founding). Its line `GROW_CARRY` gives the circles, the contacts, the
/// material's entries and the drawn key bytes before and after. On the host: it opens no card and trains nothing. That the founding keeps
/// every face is the engine's test's (`more_carry_circles_keep_every_face_every_standing_circle_and_a_towers_level`) and, on a line's
/// state, a held read of the founded state set against the same state's read before it.
pub fn grow_carry(args: &[String]) -> Result<()> {
    if args.len() != 7 {
        return Err("grow-carry STATE STATE_SHA KEYS KEYS_SHA CIRCLES OUT".into());
    }
    let text = pinned_read(&args[1], &args[2], STATE_BUDGET)?;
    let learner = Learner::from_text(std::str::from_utf8(&text)?).map_err(|e| e.to_string())?;
    if learner.to_text().as_bytes() != text.as_slice() {
        return Err("a state that does not read and write back byte for byte".into());
    }
    let keys = pinned_read(&args[3], &args[4], STATE_BUDGET)?;
    let circles: usize = args[5].parse().map_err(|_| "a count of carry circles that is no number")?;
    let out = Path::new(&args[6]);
    if out.exists() {
        return Err("a founded state's path that exists".into());
    }
    let founded = learner.more_carry(circles, &keys).map_err(|e| e.to_string())?;
    let rest = keys.get(learner.drawn..).ok_or("fewer key bytes than the learner has drawn")?;
    let (field, from) = learner.field.more_carry(circles, rest).map_err(|e| e.to_string())?;
    if field != founded.field {
        return Err("the learner's founding and the field's differ".into());
    }
    let (old_all, new_all): (Vec<i32>, Vec<i32>) = (learner.field.material().copied().collect(), founded.field.material().copied().collect());
    let mut carried = vec![0u8; old_all.len()];
    for (k, o) in from.iter().enumerate() {
        if let Some(i) = *o {
            if new_all[k] != old_all[i] {
                return Err("a standing entry that the founding did not carry with its value".into());
            }
            carried[i] = carried[i].saturating_add(1);
        }
    }
    if from.len() != new_all.len() || carried.iter().any(|&n| n != 1) {
        return Err("a founding that did not carry every standing entry once".into());
    }
    let written = founded.to_text();
    let back = Learner::from_text(&written).map_err(|e| e.to_string())?;
    if back.to_text() != written || back.field != founded.field || back.pass != learner.pass || back.rate_parts != learner.rate_parts || back.laps != learner.laps || back.rate_bits != learner.rate_bits {
        return Err("a founded learner that does not read back as itself with its pass, its parts' rates, its laps and its rate".into());
    }
    std::fs::write(out, &written)?;
    let (od, nd) = (learner.field.declaration, founded.field.declaration);
    println!(
        "GROW_CARRY circles_before={} circles_after={} contacts_before={} contacts_after={} material_before={} material_after={} fine_before={} fine_after={} drawn_before={} drawn_after={} new_entries={}",
        od.carry,
        nd.carry,
        od.contacts,
        nd.contacts,
        old_all.len(),
        new_all.len(),
        learner.field.theta.len(),
        founded.field.theta.len(),
        learner.drawn,
        founded.drawn,
        from.iter().filter(|o| o.is_none()).count()
    );
    Ok(())
}

/// [definition; agent-inferred, November 16, Athena alpha's cold-restart box (#404)] `restore-store STATE STATE_SHA`: **a saved state restored
/// cold**: the state read into a learner in a fresh process and written back as text, its bytes compared with the file's. A reading: it writes
/// nothing. Its line `STORE_RESTORE` gives the state's octets, its learner's laps, drawn keys and material entries, and whether the restored
/// state writes the same bytes. With gate 3's reproduction (a cold process from a saved state codes the line's sections and reads the
/// line's cavity table byte for byte), it is the engine's receipt that a restart keeps what the line learned.
pub fn restore(args: &[String]) -> Result<()> {
    if args.len() != 3 {
        return Err("restore-store STATE STATE_SHA".into());
    }
    let started = std::time::Instant::now();
    let bytes = pinned_read(&args[1], &args[2], STATE_BUDGET)?;
    let text = std::str::from_utf8(&bytes)?;
    let learner = Learner::from_text(text).map_err(|e| e.to_string())?;
    let written = learner.to_text();
    let equal = written.as_bytes() == bytes.as_slice();
    let first = written.as_bytes().iter().zip(bytes.iter()).position(|(a, b)| a != b).map_or("-".to_string(), |k| k.to_string());
    println!(
        "STORE_RESTORE octets={} written_octets={} laps={} drawn={} entries={} equal={equal} first_unequal_octet={first} ms={}",
        bytes.len(),
        written.len(),
        learner.laps,
        learner.drawn,
        learner.field.material_len(),
        started.elapsed().as_millis()
    );
    if !equal {
        return Err("the restored state does not write the saved bytes".into());
    }
    Ok(())
}

/// [definition; agent-inferred, November 15, the record of the states a field trains on, §5 item 1] `own-states STATE STATE_SHA OUT`: **a
/// state whose training states are the field's own**: the state with its pass line's word `own` set ([`StorePass`]), its place in the pass
/// kept, so the cut goes on over the same stretches and each stretch's state is the release's own at a crossing of its octaves
/// ([`holonics_engine::passage::own_state_of`]); every other line byte for byte, read back and checked. Refused where the state's states
/// are already its own.
pub fn own_states(args: &[String]) -> Result<()> {
    if args.len() != 4 {
        return Err("own-states STATE STATE_SHA OUT".into());
    }
    let text = String::from_utf8(pinned_read(&args[1], &args[2], STATE_BUDGET)?)?;
    let out = Path::new(&args[3]);
    if out.exists() {
        return Err(format!("{} exists", out.display()).into());
    }
    let learner = Learner::from_text(&text).map_err(|e| e.to_string())?;
    let before = learner.pass.clone().ok_or("a state with no pass line")?;
    if before.own {
        return Err("a state whose training states are already its own".into());
    }
    let (written, lines, differing) = with_pass(&text, &learner, StorePass { own: true, ..before.clone() })?;
    std::fs::write(out, &written)?;
    println!("OWN_STATES stretches={} slices={} lines={lines} differing_line={differing}", before.stretches, slices_text(&before));
    Ok(())
}

/// [measurement; theory, November 12, P49 item 4] `write-store UNITS UNITS_SHA STORE STORE_SHA KEYS KEYS_SHA CODEC CODEC_SHA DOCUMENTS PROMPT RUN
/// OUT STATE STATE_SHA`: **the release from held prompts**. On the store's held role, for each slice in the store's order, its first
/// `DOCUMENTS` pieces that open their document and hold at least `PROMPT + RUN` places; a problem is the piece's first `PROMPT` places and
/// `RUN` open places. The release is the tower's as it stands, its law fixed here: [`holonics_engine::field::Constitution::sample_runs`] over
/// every problem at once with `sweeps = RUN` (one place a read), `refine = REFINE` (0 where none is given), the codec's void, the key file's seed, `run_bound = 0`, the
/// near tail, the keyed order within an octave, no given lengths, no one-end draw, a sweep that always goes on and no observer: the store's
/// writer state run from `k = 0` upward, by octaves of distance from the prompt. `OUT` is created new; each problem writes three files of
/// raw bytes (`SLICE_NN.prompt`, `SLICE_NN.written`, the codec's decode up to the first void, and `SLICE_NN.reference`, the piece's next
/// `RUN` places), and one line (`STORE_WRITE`: its slice, its document, the places written before a void and the release's reads); a closing
/// line holds the card's counters and the time. A reading: the state is not touched.
/// The held problems the writer and the prompt's reading meet: `DOCUMENTS` held pieces a slice that open and hold `PROMPT + RUN` places, each
/// its slice, its document, its prompt's classes, its prompt's bytes and its reference continuation's bytes.
#[allow(clippy::type_complexity, reason = "a problem's five parts, named at the one place they are built")]
fn held_problems<'n>(store: &Path, counts: &HashMap<(String, String), (u64, u128)>, names: &[&'n str], codec: &Codec, documents: usize, prompt: usize, run: usize) -> Result<Vec<(&'n str, u64, Vec<usize>, Vec<u8>, Vec<u8>)>> {
    let mut problems: Vec<(&str, u64, Vec<usize>, Vec<u8>, Vec<u8>)> = Vec::new();
    for &name in names {
        let mut slice = open_slice(store, "held", name, counts)?;
        let chosen: Vec<usize> = (0..slice.pieces.len()).filter(|&k| slice.pieces[k].opens && slice.pieces[k].places() >= (prompt + run) as u64).take(documents).collect();
        for k in chosen {
            let bytes = slice.bytes(k, 0, (prompt + run) as u64)?;
            let classes = codec.encode(&bytes[..prompt])?;
            if classes.len() != prompt {
                return Err("a prompt whose bytes are not one class each".into());
            }
            problems.push((name, slice.pieces[k].document, classes, bytes[..prompt].to_vec(), bytes[prompt..].to_vec()));
        }
    }
    if problems.is_empty() {
        return Err("no held piece holds the prompt and the run".into());
    }
    Ok(problems)
}

/// [measurement; agent-inferred, November 16, Athena alpha's answer box (#404) and the theory thread's acceptance (d) of 16:02 UTC]
/// `read-prompt UNITS UNITS_SHA STORE STORE_SHA KEYS KEYS_SHA CODEC CODEC_SHA DOCUMENTS PROMPT RUN STATE STATE_SHA`: **whether a continuation
/// is read from its own prompt.** For each of the writer's held problems the reference continuation is coded with every one of its places
/// open, beside its own prompt and beside a foil, the next problem's prompt of the same slice (the last takes the first's), the region the
/// writer's first read meets (the prompt resolved, the run open). A continuation that depends on its prompt codes lower beside its own. Each
/// problem's line gives both codes over the run in millionths of a bit a place and their difference, and by octave of the place's distance
/// from the prompt (`1`, `2–3`, `4–7`, … places in), so the nearest places, where a prompt can reach first, stand beside the far ones; each
/// slice's line sums its problems. A reading: the state is read, never written; the texts stay unprinted (the held documents are private).
pub fn read_prompt(args: &[String], realization: &mut dyn Realization) -> Result<()> {
    if args.len() != 14 {
        return Err("read-prompt UNITS UNITS_SHA STORE STORE_SHA KEYS KEYS_SHA CODEC CODEC_SHA DOCUMENTS PROMPT RUN STATE STATE_SHA".into());
    }
    let started = std::time::Instant::now();
    refuse_variables("read-prompt")?;
    let units = units_of(&args[1], &args[2])?;
    if !units.merges().is_empty() {
        return Err("the store's cut is on bytes: a units file of merges is refused".into());
    }
    let store = Path::new(&args[3]);
    let counts = store_counts(std::str::from_utf8(&pinned_read(&store.join("STORE.tsv").to_string_lossy(), &args[4], READ_BUDGET as usize)?)?)?;
    let _keys = pinned_read(&args[5], &args[6], READ_BUDGET as usize)?;
    let codec = Codec::from_text(&String::from_utf8(pinned_read(&args[7], &args[8], READ_BUDGET as usize)?)?, units)?;
    let (documents, prompt, run) = (positive(&args[9])?, positive(&args[10])?, positive(&args[11])?);
    let learner = Learner::from_text(std::str::from_utf8(&pinned_read(&args[12], &args[13], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    if learner.field.declaration.alphabet != codec.alphabet() {
        return Err("a state whose alphabet is not its codec's".into());
    }
    let law = learner.pass.clone().ok_or("a state with no pass line: read-prompt reads a state of the store's line")?;
    let names = role_names(&counts, "held");
    let problems = held_problems(store, &counts, &names, &codec, documents, prompt, run)?;
    // The continuation's classes (a byte a class, as the prompt's).
    let runs: Vec<Vec<usize>> = problems.iter().map(|p| codec.encode(&p.4)).collect::<std::result::Result<Vec<_>, _>>()?;
    if runs.iter().any(|r| r.len() != run) {
        return Err("a continuation whose bytes are not one class each".into());
    }
    // Each problem's foil: the next problem of its slice, the slice's last taking its first.
    let foil_of: Vec<usize> = (0..problems.len())
        .map(|k| {
            let name = problems[k].0;
            let same: Vec<usize> = (0..problems.len()).filter(|&j| problems[j].0 == name).collect();
            let at = same.iter().position(|&j| j == k).unwrap_or(0);
            same[(at + 1) % same.len()]
        })
        .collect();
    println!("PROMPT_LAW problems={} documents={documents} prompt={prompt} run={run} alphabet={} pairs_bound={} sites_bound={} ms={}", problems.len(), codec.alphabet(), law.pairs, law.sites, started.elapsed().as_millis());
    // The regions: for problem `k`, its own (`2k`) and its foil's (`2k + 1`) prompt with its continuation open.
    let regions: Vec<OwnedRegion> = (0..problems.len())
        .flat_map(|k| {
            [k, foil_of[k]].into_iter().map(move |p| (k, p))
        })
        .map(|(k, p)| {
            let mut classes = problems[p].2.clone();
            classes.extend_from_slice(&runs[k]);
            let mut open = vec![false; prompt];
            open.extend(std::iter::repeat_n(true, run));
            OwnedRegion::plain(classes, open)
        })
        .collect();
    const OCTAVES: usize = 9;
    let octave = |d: usize| -> usize { ((usize::BITS - 1 - d.leading_zeros()) as usize).min(OCTAVES - 1) };
    // Per problem: [own, foil] codes summed by octave, on `2^(−20)` bits, and the places in each octave.
    let mut sums: Vec<[[i128; OCTAVES]; 2]> = vec![[[0; OCTAVES]; 2]; problems.len()];
    let mut in_octave = [0usize; OCTAVES];
    for d in 1..=run {
        in_octave[octave(d)] += 1;
    }
    let mut at = 0usize;
    let mut batches = 0usize;
    while at < regions.len() {
        let (mut in_pairs, mut in_sites, mut end) = (0u64, 0u64, at);
        while end < regions.len() {
            let s = regions[end].classes.len() as u64;
            if in_sites > 0 && (in_pairs + s * s > law.pairs || in_sites + s > law.sites) {
                break;
            }
            (in_pairs, in_sites, end) = (in_pairs + s * s, in_sites + s, end + 1);
        }
        let faces = realization.read_faces(&learner.field, &views_of(&regions[at..end])).map_err(|e| e.to_string())?;
        for (r, faces) in (at..end).zip(faces) {
            let (k, side) = (r / 2, r % 2);
            for (t, face) in faces.iter().enumerate().skip(prompt) {
                let face = face.as_ref().ok_or("an open place without a face")?;
                sums[k][side][octave(t - prompt + 1)] += face.code(runs[k][t - prompt]) as i128;
            }
        }
        batches += 1;
        at = end;
    }
    let micro = |code: i128, places: usize| -> i128 { if places == 0 { 0 } else { code * 1_000_000 / ((places as i128) << 20) } };
    let mut index: HashMap<&str, usize> = HashMap::new();
    let mut by_slice: Vec<(&str, [[i128; OCTAVES]; 2], usize)> = Vec::new();
    for (k, p) in problems.iter().enumerate() {
        let i = index.entry(p.0).or_insert(0);
        let stem = format!("{}_{:02}", p.0, *i);
        *i += 1;
        let total = |side: usize| sums[k][side].iter().sum::<i128>();
        let octaves: Vec<String> = (0..OCTAVES).filter(|&o| in_octave[o] > 0).map(|o| format!("{}", micro(sums[k][1][o] - sums[k][0][o], in_octave[o]))).collect();
        println!("PROMPT problem={stem} document={} foil={} own={} foil_code={} foil_less_own={} by_octave_foil_less_own={}", p.1, foil_of[k], micro(total(0), run), micro(total(1), run), micro(total(1) - total(0), run), octaves.join(","));
        match by_slice.iter_mut().find(|e| e.0 == p.0) {
            Some(e) => {
                for side in 0..2 {
                    for o in 0..OCTAVES {
                        e.1[side][o] += sums[k][side][o];
                    }
                }
                e.2 += 1;
            }
            None => by_slice.push((p.0, sums[k], 1)),
        }
    }
    for (name, s, n) in &by_slice {
        let total = |side: usize| s[side].iter().sum::<i128>();
        let octaves: Vec<String> = (0..OCTAVES).filter(|&o| in_octave[o] > 0).map(|o| format!("{}", micro(s[1][o] - s[0][o], in_octave[o] * n))).collect();
        println!("PROMPT_SLICE slice={name} problems={n} own={} foil_code={} foil_less_own={} by_octave_foil_less_own={}", micro(total(0), run * n), micro(total(1), run * n), micro(total(1) - total(0), run * n), octaves.join(","));
    }
    println!("PROMPT_DONE problems={} batches={batches} {} ms={}", problems.len(), counters_text(realization), started.elapsed().as_millis());
    Ok(())
}

/// [measurement; agent-inferred, November 16, the theory thread's writer guesses W1 of 16:37 UTC] `read-writes UNITS UNITS_SHA STORE STORE_SHA
/// KEYS KEYS_SHA CODEC CODEC_SHA DOCUMENTS PROMPT RUN WRITES STATE STATE_SHA`: **a write's code beside its reference's.** For each of the
/// writer's held problems (the same choice as `write-store`'s), the written run read from `WRITES/{problem}.written` and the reference
/// continuation are each coded after the problem's prompt two ways: every place of the run open alone among the run's other places (the
/// one-place receiver, both sides known), and every place of the run open at once (the receiver of the writer's first read). A write that
/// the field reads as its own codes lower than the reference under the first; how the two receivers part says where the writer's draft
/// stands. Codes in millionths of a bit a place, over the written places before the first void (a write that voids early is coded on what
/// it wrote), the reference over its whole run; each slice's line sums its problems. A reading: nothing is written, the texts unprinted.
pub fn read_writes(args: &[String], realization: &mut dyn Realization) -> Result<()> {
    if args.len() != 15 {
        return Err("read-writes UNITS UNITS_SHA STORE STORE_SHA KEYS KEYS_SHA CODEC CODEC_SHA DOCUMENTS PROMPT RUN WRITES STATE STATE_SHA".into());
    }
    let started = std::time::Instant::now();
    refuse_variables("read-writes")?;
    let units = units_of(&args[1], &args[2])?;
    if !units.merges().is_empty() {
        return Err("the store's cut is on bytes: a units file of merges is refused".into());
    }
    let store = Path::new(&args[3]);
    let counts = store_counts(std::str::from_utf8(&pinned_read(&store.join("STORE.tsv").to_string_lossy(), &args[4], READ_BUDGET as usize)?)?)?;
    let _keys = pinned_read(&args[5], &args[6], READ_BUDGET as usize)?;
    let codec = Codec::from_text(&String::from_utf8(pinned_read(&args[7], &args[8], READ_BUDGET as usize)?)?, units)?;
    let (documents, prompt, run) = (positive(&args[9])?, positive(&args[10])?, positive(&args[11])?);
    let writes = Path::new(&args[12]);
    let learner = Learner::from_text(std::str::from_utf8(&pinned_read(&args[13], &args[14], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    if learner.field.declaration.alphabet != codec.alphabet() {
        return Err("a state whose alphabet is not its codec's".into());
    }
    let law = learner.pass.clone().ok_or("a state with no pass line: read-writes reads a state of the store's line")?;
    let names = role_names(&counts, "held");
    let problems = held_problems(store, &counts, &names, &codec, documents, prompt, run)?;
    let mut index: HashMap<&str, usize> = HashMap::new();
    // Each problem: its stem, its write's classes and its reference's classes.
    let mut runs: Vec<(String, Vec<usize>, Vec<usize>)> = Vec::new();
    for p in &problems {
        let i = index.entry(p.0).or_insert(0);
        let stem = format!("{}_{:02}", p.0, *i);
        *i += 1;
        let written = std::fs::read(writes.join(format!("{stem}.written")))?;
        let w = codec.encode(&written)?;
        let r = codec.encode(&p.4)?;
        if r.len() != run {
            return Err("a reference whose bytes are not one class each".into());
        }
        runs.push((stem, w.into_iter().take(run).collect(), r));
    }
    println!("WRITES_LAW problems={} documents={documents} prompt={prompt} run={run} alphabet={} ms={}", problems.len(), codec.alphabet(), started.elapsed().as_millis());
    // The regions: for problem `k` and side `s` (0 the write, 1 the reference), the whole-open region, then one region a place.
    let mut jobs: Vec<(usize, usize, Option<usize>)> = Vec::new();
    for (k, (_, w, r)) in runs.iter().enumerate() {
        for (s, len) in [(0usize, w.len()), (1usize, r.len())] {
            if len == 0 {
                continue;
            }
            jobs.push((k, s, None));
            jobs.extend((0..len).map(|t| (k, s, Some(t))));
        }
    }
    let region_of = |&(k, s, at): &(usize, usize, Option<usize>)| -> OwnedRegion {
        let body = if s == 0 { &runs[k].1 } else { &runs[k].2 };
        let mut classes = problems[k].2.clone();
        classes.extend_from_slice(body);
        let mut open = vec![false; prompt];
        match at {
            None => open.extend(std::iter::repeat_n(true, body.len())),
            Some(t) => open.extend((0..body.len()).map(|u| u == t)),
        }
        OwnedRegion::plain(classes, open)
    };
    // Per problem and side: [one-place, all-open] codes on `2^(−20)` bits.
    let mut sums: Vec<[[i128; 2]; 2]> = vec![[[0; 2]; 2]; runs.len()];
    let mut at = 0usize;
    let mut batches = 0usize;
    while at < jobs.len() {
        let (mut in_pairs, mut in_sites, mut end) = (0u64, 0u64, at);
        while end < jobs.len() {
            let (k, s, _) = jobs[end];
            let n = (prompt + if s == 0 { runs[k].1.len() } else { runs[k].2.len() }) as u64;
            if in_sites > 0 && (in_pairs + n * n > law.pairs || in_sites + n > law.sites) {
                break;
            }
            (in_pairs, in_sites, end) = (in_pairs + n * n, in_sites + n, end + 1);
        }
        let regions: Vec<OwnedRegion> = jobs[at..end].iter().map(region_of).collect();
        let faces = realization.read_faces(&learner.field, &views_of(&regions)).map_err(|e| e.to_string())?;
        for (&(k, s, place), (faces, region)) in jobs[at..end].iter().zip(faces.iter().zip(&regions)) {
            for (t, face) in faces.iter().enumerate().skip(prompt) {
                if !region.unresolved[t] {
                    continue;
                }
                let face = face.as_ref().ok_or("an open place without a face")?;
                sums[k][s][usize::from(place.is_none())] += face.code(region.classes[t]) as i128;
            }
        }
        batches += 1;
        at = end;
    }
    let micro = |code: i128, places: usize| -> i128 { if places == 0 { 0 } else { code * 1_000_000 / ((places as i128) << 20) } };
    let mut by_slice: Vec<(&str, [[i128; 2]; 2], usize, usize)> = Vec::new();
    for (k, (stem, w, r)) in runs.iter().enumerate() {
        println!(
            "WRITES problem={stem} written_places={} write_one={} reference_one={} write_open={} reference_open={}",
            w.len(),
            micro(sums[k][0][0], w.len()),
            micro(sums[k][1][0], r.len()),
            micro(sums[k][0][1], w.len()),
            micro(sums[k][1][1], r.len())
        );
        let name = problems[k].0;
        match by_slice.iter_mut().find(|e| e.0 == name) {
            Some(e) => {
                for s in 0..2 {
                    for m in 0..2 {
                        e.1[s][m] += sums[k][s][m];
                    }
                }
                e.2 += w.len();
                e.3 += r.len();
            }
            None => by_slice.push((name, sums[k], w.len(), r.len())),
        }
    }
    for (name, s, wp, rp) in &by_slice {
        println!("WRITES_SLICE slice={name} written_places={wp} write_one={} reference_one={} write_open={} reference_open={}", micro(s[0][0], *wp), micro(s[1][0], *rp), micro(s[0][1], *wp), micro(s[1][1], *rp));
    }
    println!("WRITES_DONE problems={} regions={} batches={batches} {} ms={}", runs.len(), jobs.len(), counters_text(realization), started.elapsed().as_millis());
    Ok(())
}

/// [measurement; agent-inferred, November 16, the theory thread's anchor and answer reads of Build A] `read-forms UNITS UNITS_SHA KEYS
/// KEYS_SHA CODEC CODEC_SHA FORMS FORMS_SHA STATE STATE_SHA`: **a continuation coded after its own prompt.** `FORMS` is a table of rows
/// `label<TAB>prompt<TAB>run` (a line feed in a prompt or a run written `\n`), made by a ruler on the host from the arithmetic world's held
/// files (`tools/forms_table.py`): the same sum after `a + b = `, `a plus b equals ` and the foil `a plux b eqvals `, or a held record cut
/// after its `= `. Each row's region is its prompt resolved and its run open, the region the writer's first read meets, and each open place
/// is coded under its written byte. Each row's line gives the run's code in millionths of a bit a place and each place's code in order, so a
/// ruler sums them by form, by the operands' lengths, by the digit's place and by whether a carry entered it. A reading: the state is read,
/// never written. It runs on the card (`train`) or on the host's threads (`host`, beside the card's runs: it opens no card).
pub fn read_forms(args: &[String], realization: &mut dyn Realization) -> Result<()> {
    // [measurement; the theory thread's R1 of 19:12 UTC] With `one`, each place of the run is coded open alone, the rest of the run known
    // (the one-place receiver: the state a training mask meets where a digit's neighbours are known).
    // [measurement; the lead, November 16 23:00Z] With `carry=MILLI`, every open row carries its lock along the ticks at `γ = MILLI/1000`
    // ([`holonics_engine::field::Constitution::lock_carry`]), on the host's realization: a ruler's forward, read before the stage is a law.
    let (one, carry) = match (args.len(), args.get(11).map(String::as_str), args.get(12).and_then(|w| w.strip_prefix("carry="))) {
        (11, None, None) => (false, None),
        (12, Some("one"), None) => (true, None),
        (13, Some("one"), Some(m)) => (true, Some(crate::ruler::tension::carry_of(m)?)),
        _ => return Err("read-forms UNITS UNITS_SHA KEYS KEYS_SHA CODEC CODEC_SHA FORMS FORMS_SHA STATE STATE_SHA [one [carry=MILLI]]".into()),
    };
    let started = std::time::Instant::now();
    refuse_variables("read-forms")?;
    let units = units_of(&args[1], &args[2])?;
    if !units.merges().is_empty() {
        return Err("the store's cut is on bytes: a units file of merges is refused".into());
    }
    let _keys = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let codec = Codec::from_text(&String::from_utf8(pinned_read(&args[5], &args[6], READ_BUDGET as usize)?)?, units)?;
    let table = String::from_utf8(pinned_read(&args[7], &args[8], READ_BUDGET as usize)?)?;
    let mut learner = Learner::from_text(std::str::from_utf8(&pinned_read(&args[9], &args[10], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    if learner.field.declaration.alphabet != codec.alphabet() {
        return Err("a state whose alphabet is not its codec's".into());
    }
    learner.field.lock_carry = carry;
    let law = learner.pass.clone().ok_or("a state with no pass line: read-forms reads a state of the store's line")?;
    let unescape = |t: &str| t.replace("\\n", "\n");
    let mut rows: Vec<(String, usize, Vec<usize>)> = Vec::new();
    let mut regions: Vec<OwnedRegion> = Vec::new();
    for line in table.lines() {
        let w: Vec<&str> = line.split('\t').collect();
        let [label, prompt, run] = w[..] else { return Err("a forms row that is not three fields".into()) };
        let (p, r) = (codec.encode(unescape(prompt).as_bytes())?, codec.encode(unescape(run).as_bytes())?);
        if p.is_empty() || r.is_empty() {
            return Err("a forms row with an empty prompt or run".into());
        }
        let mut classes = p.clone();
        classes.extend_from_slice(&r);
        if one {
            for j in 0..r.len() {
                let mut open = vec![false; classes.len()];
                open[p.len() + j] = true;
                regions.push(OwnedRegion::plain(classes.clone(), open));
            }
        } else {
            let mut open = vec![false; p.len()];
            open.extend(std::iter::repeat_n(true, r.len()));
            regions.push(OwnedRegion::plain(classes, open));
        }
        rows.push((label.to_string(), p.len(), r));
    }
    if rows.is_empty() {
        return Err("a forms table of no rows".into());
    }
    println!("FORMS_LAW rows={} receiver={} alphabet={} pairs_bound={} sites_bound={} ms={}", rows.len(), if one { "one" } else { "open" }, codec.alphabet(), law.pairs, law.sites, started.elapsed().as_millis());
    let micro = |code: i128, places: usize| -> i128 { if places == 0 { 0 } else { code * 1_000_000 / ((places as i128) << 20) } };
    let (mut at, mut batches) = (0usize, 0usize);
    // Each region's row and its first open place: a row's places in order, one region a place under `one`.
    let owner: Vec<(usize, usize)> = rows.iter().enumerate().flat_map(|(k, r)| if one { (0..r.2.len()).map(|j| (k, j)).collect::<Vec<_>>() } else { vec![(k, 0)] }).collect();
    let mut codes_of: Vec<Vec<i128>> = rows.iter().map(|r| vec![0; r.2.len()]).collect();
    while at < regions.len() {
        let (mut in_pairs, mut in_sites, mut end) = (0u64, 0u64, at);
        while end < regions.len() {
            let s = regions[end].classes.len() as u64;
            if in_sites > 0 && (in_pairs + s * s > law.pairs || in_sites + s > law.sites) {
                break;
            }
            (in_pairs, in_sites, end) = (in_pairs + s * s, in_sites + s, end + 1);
        }
        let faces = realization.read_faces(&learner.field, &views_of(&regions[at..end])).map_err(|e| e.to_string())?;
        for (r, faces) in (at..end).zip(faces) {
            let (k, j0) = owner[r];
            let (_, prompt, run) = &rows[k];
            let places: Vec<usize> = if one { vec![j0] } else { (0..run.len()).collect() };
            for j in places {
                codes_of[k][j] = faces[prompt + j].as_ref().map(|f| f.code(run[j]) as i128).ok_or("an open place without a face")?;
            }
        }
        batches += 1;
        at = end;
    }
    for ((label, _, run), codes) in rows.iter().zip(&codes_of) {
        let total: i128 = codes.iter().sum();
        println!("FORMS_ROW label={label} prompt_places={} run_places={} code={} by_place={}", rows.iter().find(|r| &r.0 == label).map_or(0, |r| r.1), run.len(), micro(total, run.len()), codes.iter().map(|&c| micro(c, 1).to_string()).collect::<Vec<_>>().join(","));
    }
    println!("FORMS_DONE rows={} batches={batches} {} ms={}", rows.len(), counters_text(realization), started.elapsed().as_millis());
    Ok(())
}

/// [measurement; agent-inferred, November 16, Brandon's 17:06Z: how the words warp around the problems] `write-forms UNITS UNITS_SHA KEYS
/// KEYS_SHA CODEC CODEC_SHA FORMS FORMS_SHA RUN OUT STATE STATE_SHA [REFINE]`: **the writer after each prompt of a forms table** (the table
/// `read-forms` reads: `label<TAB>prompt<TAB>run`, a line feed written `\n`). Each row's prompt is released with `RUN` places open, by the
/// writer `write-store` runs (`sample_runs`: as many sweeps as places, `REFINE` passes after them, zero by default), the key file's seed.
/// `OUT/forms.written` holds a row a problem, `label<TAB>prompt<TAB>written<TAB>reference` with line feeds written `\n`, the written run
/// decoded up to its first void. A writing: the state is read, never written. It runs on the card (`train`) or on the host's threads
/// (`host`). The arithmetic world's tables are synthetic and GSM8K's test split is public, so `OUT` may be shown; a table made from a
/// private passage keeps its `OUT` private.
pub fn write_forms(args: &[String], realization: &mut dyn Realization) -> Result<()> {
    // [measurement; the lead, November 17] With `place` after `REFINE`, each octave's places are drawn in place order (the run written
    // left to right, each place on a read whose every earlier place is resolved), where the law draws them in a keyed order: a ruler's
    // comparison of what the order within an octave costs a write, read before any change of the release's law.
    let place_order = args.len() == 15 && args[14] == "place";
    if args.len() != 13 && args.len() != 14 && !place_order {
        return Err("write-forms UNITS UNITS_SHA KEYS KEYS_SHA CODEC CODEC_SHA FORMS FORMS_SHA RUN OUT STATE STATE_SHA [REFINE [place]]".into());
    }
    let started = std::time::Instant::now();
    refuse_variables("write-forms")?;
    let units = units_of(&args[1], &args[2])?;
    if !units.merges().is_empty() {
        return Err("the store's cut is on bytes: a units file of merges is refused".into());
    }
    let keys = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let seed = u64::from_be_bytes(keys.get(keys.len().saturating_sub(8)..).filter(|w| w.len() == 8).ok_or("a key file of fewer than eight bytes")?.try_into()?);
    let codec = Codec::from_text(&String::from_utf8(pinned_read(&args[5], &args[6], READ_BUDGET as usize)?)?, units)?;
    let table = String::from_utf8(pinned_read(&args[7], &args[8], READ_BUDGET as usize)?)?;
    let run = positive(&args[9])?;
    let out = Path::new(&args[10]);
    let learner = Learner::from_text(std::str::from_utf8(&pinned_read(&args[11], &args[12], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let refine = match args.get(13) { Some(r) => r.parse::<usize>().map_err(|_| "REFINE is a count")?, None => 0 };
    if learner.field.declaration.alphabet != codec.alphabet() {
        return Err("a state whose alphabet is not its codec's".into());
    }
    let unescape = |t: &str| t.replace("\\n", "\n");
    let escape = |b: &[u8]| String::from_utf8_lossy(b).replace('\n', "\\n").replace('\t', "\\t");
    let mut rows: Vec<(String, Vec<u8>, Vec<usize>, Vec<u8>)> = Vec::new();
    for line in table.lines() {
        let w: Vec<&str> = line.split('\t').collect();
        let [label, prompt, reference] = w[..] else { return Err("a forms row that is not three fields".into()) };
        let bytes = unescape(prompt).into_bytes();
        let classes = codec.encode(&bytes)?;
        if classes.is_empty() {
            return Err("a forms row with an empty prompt".into());
        }
        rows.push((label.to_string(), bytes, classes, unescape(reference).into_bytes()));
    }
    std::fs::create_dir(out)?;
    println!("FORMS_WRITE_LAW rows={} run={run} sweeps={run} refine={refine} alphabet={} void={} ms={}", rows.len(), codec.alphabet(), codec.void(), started.elapsed().as_millis());
    let release: Vec<(&[usize], usize)> = rows.iter().map(|r| (r.2.as_slice(), run)).collect();
    let written = learner
        .field
        .sample_runs(&release, run, refine, codec.void(), seed, 0, true, place_order, None, false, realization, &mut |_, _| true, &mut |_| {})
        .map_err(|e| e.to_string())?;
    let mut text = String::new();
    for ((label, prompt, _, reference), w) in rows.iter().zip(&written) {
        let before_void = w.iter().position(|&c| c == codec.void()).unwrap_or(w.len());
        let decoded = codec.decode(&w[..before_void]);
        text.push_str(&format!("{label}\t{}\t{}\t{}\n", escape(prompt), escape(&decoded), escape(reference)));
    }
    write_new(&out.join("forms.written"), text.as_bytes())?;
    println!("FORMS_WRITE_DONE rows={} {} ms={}", rows.len(), counters_text(realization), started.elapsed().as_millis());
    Ok(())
}

/// [measurement; agent-inferred, November 16, the theory thread's R2 of 19:12 UTC] `read-junction UNITS UNITS_SHA KEYS KEYS_SHA CODEC
/// CODEC_SHA FORMS FORMS_SHA STATE STATE_SHA`: **where an answer digit's contact weight goes.** For each held sum or difference of two
/// operands in its symbols form (`anchor:LENGTHS:OP:symbols:N` rows of the forms table: `a OP b = ` and the value), each digit of the value
/// is opened alone, the rest of the record known (R1's receiver), and each tick and head's row at that digit is read for the shares of its
/// contact weight on the operands' digits: the aligned ones (`a_k` and `b_k`, the digits at the same place counted from each number's
/// last digit) and the others. Each line gives, by the operands' lengths, tick and head, the mean share an aligned digit takes and the mean
/// share another operand digit takes, in millionths of the row's weight, and their ratio in thousandths. A reading on the host's threads
/// (it opens no card): the state is read, never written. A ruler: it names places by the world's own layout, outside the machine.
pub fn read_junction(args: &[String]) -> Result<()> {
    use rayon::prelude::*;
    if args.len() != 11 {
        return Err("read-junction UNITS UNITS_SHA KEYS KEYS_SHA CODEC CODEC_SHA FORMS FORMS_SHA STATE STATE_SHA".into());
    }
    let started = std::time::Instant::now();
    refuse_variables("read-junction")?;
    let units = units_of(&args[1], &args[2])?;
    let _keys = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let codec = Codec::from_text(&String::from_utf8(pinned_read(&args[5], &args[6], READ_BUDGET as usize)?)?, units)?;
    let table = String::from_utf8(pinned_read(&args[7], &args[8], READ_BUDGET as usize)?)?;
    let learner = Learner::from_text(std::str::from_utf8(&pinned_read(&args[9], &args[10], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    if learner.field.declaration.alphabet != codec.alphabet() {
        return Err("a state whose alphabet is not its codec's".into());
    }
    // (lengths, region, aligned places, other operand places, the first operand's aligned place, the second's)
    let mut work: Vec<(String, OwnedRegion, Vec<usize>, Vec<usize>, Vec<usize>, Vec<usize>)> = Vec::new();
    for line in table.lines() {
        let w: Vec<&str> = line.split('\t').collect();
        let [label, prompt, run] = w[..] else { return Err("a forms row that is not three fields".into()) };
        let parts: Vec<&str> = label.split(':').collect();
        if parts.len() != 5 || parts[0] != "anchor" || parts[3] != "symbols" || !(parts[2] == "+" || parts[2] == "-") {
            continue;
        }
        let toks: Vec<&str> = prompt.split(' ').collect();
        let (a, b) = (toks[0], toks[2]);
        let (a_at, b_at) = (0usize, a.len() + 3);
        let value = run.replace("\\n", "\n");
        let bytes = format!("{prompt}{value}").into_bytes();
        let classes = codec.encode(&bytes)?;
        let digits = value.trim_end_matches('\n').trim_start_matches('-');
        let v_at = prompt.len() + value.len() - 1 - digits.len();
        for k in 0..digits.len() {
            let place = v_at + digits.len() - 1 - k;
            let mut aligned = Vec::new();
            let (mut a_k, mut b_k) = (Vec::new(), Vec::new());
            if k < a.len() {
                aligned.push(a_at + a.len() - 1 - k);
                a_k.push(a_at + a.len() - 1 - k);
            }
            if k < b.len() {
                aligned.push(b_at + b.len() - 1 - k);
                b_k.push(b_at + b.len() - 1 - k);
            }
            let others: Vec<usize> = (a_at..a_at + a.len()).chain(b_at..b_at + b.len()).filter(|j| !aligned.contains(j)).collect();
            if aligned.is_empty() || others.is_empty() {
                continue;
            }
            let mut open = vec![false; classes.len()];
            open[place] = true;
            work.push((parts[1].to_string(), OwnedRegion::plain(classes.clone(), open), aligned, others, a_k, b_k));
        }
    }
    let (ticks, heads) = (learner.field.declaration.ticks, learner.field.declaration.heads);
    println!("JUNCTION_LAW digits={} ticks={ticks} heads={heads} ms={}", work.len(), started.elapsed().as_millis());
    let micro = |p: u128| -> u128 { (p * 1_000_000) >> holonics_engine::width::SHARE_BITS };
    // Per digit and tick and head: the aligned digits' mean share, the others' mean share, and the first and second operand's aligned digit's
    // share apart (the second's aligned digit stands at a fixed offset from the answer digit, `len(" = ") + len(value) − len(b)`, so its share
    // alone cannot tell an address from a fixed reach; the first's offset moves with the second operand's length).
    type Cell = (usize, usize, u128, u128, Option<u128>, Option<u128>);
    let read: Vec<std::result::Result<(String, Vec<Cell>), String>> = work
        .par_iter()
        .map(|(lengths, region, aligned, others, a_k, b_k)| {
            let rows = learner.field.open_sources(&holonics_engine::region::view_of(region)).map_err(|e| e.to_string())?;
            Ok((lengths.clone(), rows.into_iter().map(|(t, h, _, srcs)| {
                let on = |set: &[usize]| srcs.iter().filter(|(j, _)| set.contains(j)).map(|&(_, p)| micro(p)).sum::<u128>() / set.len().max(1) as u128;
                (t, h, on(aligned), on(others), (!a_k.is_empty()).then(|| on(a_k)), (!b_k.is_empty()).then(|| on(b_k)))
            }).collect()))
        })
        .collect();
    let mut acc: std::collections::BTreeMap<(String, usize, usize), [u128; 7]> = std::collections::BTreeMap::new();
    for r in read {
        let (lengths, cells) = r?;
        for (t, h, al, ot, a, b) in cells {
            let e = acc.entry((lengths.clone(), t, h)).or_insert([0; 7]);
            e[0] += 1;
            e[1] += al;
            e[2] += ot;
            if let Some(a) = a {
                (e[3], e[4]) = (e[3] + 1, e[4] + a);
            }
            if let Some(b) = b {
                (e[5], e[6]) = (e[5] + 1, e[6] + b);
            }
        }
    }
    for ((lengths, t, h), e) in &acc {
        let (am, om) = (e[1] / e[0], e[2] / e[0]);
        let (a, b) = (e[4] / e[3].max(1), e[6] / e[5].max(1));
        let milli = |x: u128| if om == 0 { 0 } else { x * 1000 / om };
        println!("JUNCTION_HEAD lengths={lengths} tick={t} head={h} digits={} aligned_share={am} other_share={om} ratio_milli={} first_share={a} first_milli={} second_share={b} second_milli={}", e[0], milli(am), milli(a), milli(b));
    }
    println!("JUNCTION_DONE ms={}", started.elapsed().as_millis());
    Ok(())
}

/// [measurement; theory, November 16 20:39Z, G-B3a] `write-acts UNITS UNITS_SHA KEYS KEYS_SHA CODEC CODEC_SHA FORMS FORMS_SHA RUN REFINE SEED STATE
/// STATE_SHA`: **the trainer's acts, off the line**: each row's prompt of a forms table (`forms_table.py acts`) released `RUN` places as the
/// trainer's act path releases them, its draft redrawn once where `REFINE` is one ([`holonics_engine::field::Constitution::refine_drafts`]),
/// and the world's reaction (`crate::world::react`). Prints each act's draft and reaction (`ACT`; the world is synthetic) and the share of
/// drafts the world read (`ACTS_DONE`). `SEED` keys the release as the trainer's count of stretches does. A writing: the state is read,
/// never written. On the card (`train`) or the host's threads (`host`).
pub fn write_acts(args: &[String], realization: &mut dyn Realization) -> Result<()> {
    if args.len() != 14 {
        return Err("write-acts UNITS UNITS_SHA KEYS KEYS_SHA CODEC CODEC_SHA FORMS FORMS_SHA RUN REFINE SEED STATE STATE_SHA".into());
    }
    let started = std::time::Instant::now();
    refuse_variables("write-acts")?;
    let units = units_of(&args[1], &args[2])?;
    let keys = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let seed = u64::from_be_bytes(keys.get(keys.len().saturating_sub(8)..).filter(|w| w.len() == 8).ok_or("a key file of fewer than eight bytes")?.try_into()?);
    let codec = Codec::from_text(&String::from_utf8(pinned_read(&args[5], &args[6], READ_BUDGET as usize)?)?, units)?;
    let table = String::from_utf8(pinned_read(&args[7], &args[8], READ_BUDGET as usize)?)?;
    let (run, refine, count) = (positive(&args[9])?, args[10].parse::<u64>().map_err(|_| "REFINE is zero or one")?, args[11].parse::<u64>().map_err(|_| "SEED is a count")?);
    let learner = Learner::from_text(std::str::from_utf8(&pinned_read(&args[12], &args[13], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let mut prompts: Vec<Vec<usize>> = Vec::new();
    for line in table.lines() {
        let w: Vec<&str> = line.split('\t').collect();
        let [_, prompt, _] = w[..] else { return Err("a forms row that is not three fields".into()) };
        prompts.push(codec.encode(prompt.replace("\\n", "\n").as_bytes())?);
    }
    let act_seed = seed ^ count.wrapping_mul(0x9E37_79B9_7F4A_7C15);
    let release: Vec<(&[usize], usize)> = prompts.iter().map(|p| (p.as_slice(), run)).collect();
    let mut drafts = learner.field.sample_runs(&release, run, 0, codec.void(), act_seed, 0, true, false, None, false, realization, &mut |_, _| true, &mut |_| {}).map_err(|e| e.to_string())?;
    if refine > 0 {
        let lens: Vec<usize> = drafts.iter().map(|d| draft_places(&codec.decode(&d[..d.iter().position(|&c| c == codec.void()).unwrap_or(d.len())]))).collect();
        let views: Vec<&[usize]> = prompts.iter().map(Vec::as_slice).collect();
        drafts = learner.field.refine_drafts(&views, &drafts, &lens, codec.void(), act_seed ^ 0x7265_6669_6E65, realization).map_err(|e| e.to_string())?;
    }
    let escape = |b: &[u8]| String::from_utf8_lossy(b).replace('\n', "\\n");
    let mut read_ok = 0usize;
    for (k, d) in drafts.iter().enumerate() {
        let written = codec.decode(&d[..d.iter().position(|&c| c == codec.void()).unwrap_or(d.len())]);
        let reaction = crate::world::react(&written);
        let ok = reaction.appended != b"?\n" && reaction.appended != b"\n?\n";
        read_ok += usize::from(ok);
        println!("ACT k={k} read={} draft={} world={}", u8::from(ok), escape(&written[..reaction.read.min(written.len())]), escape(&reaction.appended));
    }
    println!("ACTS_DONE acts={} read={read_ok} refine={refine} run={run} {} ms={}", drafts.len(), counters_text(realization), started.elapsed().as_millis());
    Ok(())
}

pub fn write(args: &[String], realization: &mut dyn Realization) -> Result<()> {
    if args.len() != 15 && args.len() != 16 {
        return Err("write-store UNITS UNITS_SHA STORE STORE_SHA KEYS KEYS_SHA CODEC CODEC_SHA DOCUMENTS PROMPT RUN OUT STATE STATE_SHA [REFINE]".into());
    }
    let started = std::time::Instant::now();
    refuse_variables("write-store")?;
    let units = units_of(&args[1], &args[2])?;
    if !units.merges().is_empty() {
        return Err("the store's cut is on bytes: a units file of merges is refused".into());
    }
    let store = Path::new(&args[3]);
    let counts = store_counts(std::str::from_utf8(&pinned_read(&store.join("STORE.tsv").to_string_lossy(), &args[4], READ_BUDGET as usize)?)?)?;
    let keys = pinned_read(&args[5], &args[6], READ_BUDGET as usize)?;
    let seed = u64::from_be_bytes(keys.get(keys.len().saturating_sub(8)..).filter(|w| w.len() == 8).ok_or("a key file of fewer than eight bytes")?.try_into()?);
    let codec = Codec::from_text(&String::from_utf8(pinned_read(&args[7], &args[8], READ_BUDGET as usize)?)?, units)?;
    let (documents, prompt, run) = (positive(&args[9])?, positive(&args[10])?, positive(&args[11])?);
    // [agent-inferred, November 14, the mark's record §3] `REFINE` passes after the sweeps, each revisiting the written run one place a read in
    // the writer's order and drawing each place again on the region as it stands (a place reopened is silent, so on a field that reads twice
    // its first read marks it): the draft reheard as the field's own. A pass costs as many reads as the run has places. Zero, the default, is
    // the writer as it stood. (Read first as a count of reads: 256 passes passed a 300 s deadline on November 14.)
    let refine = match args.get(15) { Some(r) => r.parse::<usize>().map_err(|_| "REFINE is a count")?, None => 0 };
    let out = Path::new(&args[12]);
    let learner = Learner::from_text(std::str::from_utf8(&pinned_read(&args[13], &args[14], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    if learner.field.declaration.alphabet != codec.alphabet() {
        return Err("a state whose alphabet is not its codec's".into());
    }
    let names = role_names(&counts, "held");
    let problems = held_problems(store, &counts, &names, &codec, documents, prompt, run)?;
    std::fs::create_dir(out)?;
    println!("STORE_WRITE_LAW problems={} documents={documents} prompt={prompt} run={run} sweeps={run} refine={refine} run_bound=0 near_tail=true place_order=false lengths=none one_end=false alphabet={} void={} ms={}", problems.len(), codec.alphabet(), codec.void(), started.elapsed().as_millis());
    let release: Vec<(&[usize], usize)> = problems.iter().map(|p| (p.2.as_slice(), run)).collect();
    // The release's reads, from the realization's own count (the sweep is not asked on the release's last read, so its calls fall one short).
    let reads_before = realization.counters().map(|c| c.reads);
    let mut asked = 0usize;
    let written = learner
        .field
        .sample_runs(&release, run, refine, codec.void(), seed, 0, true, false, None, false, realization, &mut |_, _| {
            asked += 1;
            true
        }, &mut |_| {})
        .map_err(|e| e.to_string())?;
    let reads = match (reads_before, realization.counters()) {
        (Some(b), Some(a)) => (a.reads - b) as usize,
        _ => asked + 1,
    };
    let mut index: HashMap<&str, usize> = HashMap::new();
    for ((name, document, _, prompt_bytes, reference), written) in problems.iter().zip(&written) {
        let i = index.entry(name).or_insert(0);
        let stem = format!("{name}_{:02}", *i);
        *i += 1;
        let before_void = written.iter().position(|&c| c == codec.void()).unwrap_or(written.len());
        let text = codec.decode(written);
        write_new(&out.join(format!("{stem}.prompt")), prompt_bytes)?;
        write_new(&out.join(format!("{stem}.written")), &text)?;
        write_new(&out.join(format!("{stem}.reference")), reference)?;
        println!("STORE_WRITE slice={name} problem={stem} document={document} written_places={before_void} written_octets={} reads={reads}", text.len());
    }
    println!("STORE_WRITE_DONE problems={} reads={reads} {} ms={}", problems.len(), counters_text(realization), started.elapsed().as_millis());
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use holonics_engine::field::NEAR;

    /// [definition; Build B] An act's prompt is the stretch's last whole lines, never its first partial line; and one stretch in `every` acts.
    #[test]
    fn an_acts_prompt_is_its_stretchs_last_whole_lines() {
        assert_eq!(world_prompt(b"7 = 9\n1 + 1 = 2\n2 * 3 = 6\n4 - ", 3), Some(b"1 + 1 = 2\n2 * 3 = 6\n".to_vec()), "the partial first line is no record");
        assert_eq!(world_prompt(b"7 = 9\n1 + 1 = 2\n2 * 3 = 6\n4 - ", 1), Some(b"2 * 3 = 6\n".to_vec()));
        assert_eq!(world_prompt(b"x\na\nb\nc\nd\n", 2), Some(b"c\nd\n".to_vec()));
        assert_eq!(world_prompt(b"half a record", 3), None);
        assert_eq!(world_prompt(b"half\nno whole line", 3), None, "a line feed with no whole line after it");
        for every in [1u64, 4, 8] {
            let hits = (1..80_001u64).filter(|&d| acts_here(0x5EED, d, every)).count() as u64;
            assert!(hits * every > 76_000 && hits * every < 84_000, "every={every} hits={hits}");
        }
    }
    use holonics_engine::passage::{cut_of, lengths_of, state_of, Kind};

    /// [definition; the record §4 item 1] **A stretch's draws and cut are the port's**: the draws stand on the octaves `[4, 8)` to `[256, 512)`,
    /// a stretch that would leave fewer than the least context takes the rest with its context under the rest, a true end follows only a piece
    /// that closes, and a piece's places are its title, one line feed where it opens with a title, and its text.
    #[test]
    fn a_stretchs_draws_and_cut_are_the_ports() {
        for d in 1..2000u64 {
            let (q, a) = lengths_of(0x5EED, d, LEAST, OCTAVES);
            assert!((4..512).contains(&q) && (4..512).contains(&a));
            let (q2, a2, ends, done) = cut_of(0x5EED, d, 1 << 40, true, LEAST, OCTAVES);
            assert_eq!((q2, a2, ends, done), (q, a, false, false), "a piece with no end goes on");
            let rest = q + a + 3;
            let (q3, a3, ends, done) = cut_of(0x5EED, d, rest, true, LEAST, OCTAVES);
            assert_eq!((q3 + a3, ends, done, q3 < rest), (rest, true, true, true), "fewer than the least context left: the rest taken");
            let (_, _, ends, _) = cut_of(0x5EED, d, rest, false, LEAST, OCTAVES);
            assert!(!ends, "no true end past a piece that does not close");
            let (q4, a4, _, done) = cut_of(0x5EED, d, 1, true, LEAST, OCTAVES);
            assert_eq!((q4, a4, done), (0, 1, true), "a piece of one place");
        }
        let p = Piece { document: 0, offset: 0, title: 5, text: 9, opens: true, closes: true };
        assert_eq!(p.places(), 15);
        assert_eq!(Piece { opens: false, title: 0, ..p }.places(), 9);
        assert_eq!(Piece { title: 0, ..p }.places(), 9, "a piece that opens with no title has no line feed");
    }

    /// [definition; the record §4 item 2] **A stretch's state is the port's**: the writer's state resolves its context, the first `k` of its run in
    /// the octave order and the near tail, and counts its open places; a mask state's domain is `⌊2√(mK)⌋` over the whole stretch or past the
    /// context; both kinds are met.
    #[test]
    fn a_stretchs_state_is_the_ports() {
        let (mut writers, mut masks) = (0, 0);
        for d in 1..400u64 {
            let (q, a) = (7usize, 30usize);
            let classes: Vec<usize> = (0..q + a + NEAR).map(|t| t % 5).collect();
            let Stretch { region, kind, counted, .. } = state_of(0xABCD, d, classes, q, a);
            let open = region.unresolved.iter().filter(|&&u| u).count();
            match kind {
                Kind::Writer => {
                    writers += 1;
                    assert!((0..q).all(|t| !region.unresolved[t]) && (q + a..q + a + NEAR).all(|t| !region.unresolved[t]));
                    assert_eq!((counted, region.domain), (open, None));
                    assert!(open >= 1 && open <= a);
                }
                Kind::MaskWhole | Kind::MaskRun => {
                    masks += 1;
                    let from = if kind == Kind::MaskWhole { 0 } else { q };
                    assert!((0..from).all(|t| !region.unresolved[t]));
                    assert_eq!(region.domain, Some(((4 * (q + a + NEAR - from) * open) as u128).isqrt() as usize));
                    assert_eq!(Some(counted), region.domain);
                }
                Kind::Frontier => panic!("a keyed state is never the frontier's: the cut draws that one"),
            }
        }
        assert!(writers > 100 && masks > 100, "{writers} {masks}");
    }

    /// [definition; the record of the states a field trains on, §5 item 2] **A stretch's own state is the release's at a crossing of its
    /// octaves**: its context and near tail resolved, the run's places at distances under `2^o` resolved and every farther place open, `o` the
    /// stretch's count modulo the run's crossings, its code a code of its open places with no domain; every crossing is met in turn, and
    /// the state is the line's writer state wherever that state stands at a crossing (its order within an octave does not reach it).
    #[test]
    fn a_stretchs_own_state_is_the_releases_at_a_crossing_of_its_octaves() {
        use holonics_engine::passage::own_state_of;
        for a in [4usize, 5, 7, 8, 30, 64, 255, 256, 511] {
            let q = 7usize;
            let classes: Vec<usize> = (0..q + a + NEAR).map(|t| t % 5).collect();
            let crossings = (usize::BITS - a.leading_zeros()) as u64;
            let mut met = vec![0u32; crossings as usize];
            for d in 1..3 * crossings + 1 {
                let Stretch { region, kind, counted, .. } = own_state_of(d, classes.clone(), q, a);
                let o = (d % crossings) as u32;
                met[o as usize] += 1;
                assert_eq!((kind, region.domain, counted), (Kind::Writer, None, a + 1 - (1 << o)));
                for (t, &u) in region.unresolved.iter().enumerate() {
                    assert_eq!(u, t >= q && t < q + a && t + 1 - q >= 1 << o, "a={a} d={d} t={t}");
                }
                assert_eq!(region.unresolved.iter().filter(|&&u| u).count(), counted, "the code is a code of the open places");
            }
            assert!(met.iter().all(|&m| m == 3), "a={a}: every crossing met in turn ({met:?})");
        }
        // Where the line's keyed writer state stands at a crossing (`k = 2^o − 1`), it is the own state at that crossing.
        let (q, a) = (7usize, 30usize);
        let classes: Vec<usize> = (0..q + a + NEAR).map(|t| t % 5).collect();
        let mut seen = 0;
        for d in 1..4000u64 {
            let keyed = state_of(0xABCD, d, classes.clone(), q, a);
            if keyed.kind != Kind::Writer || !(keyed.counted == a || (a + 1 - keyed.counted).is_power_of_two()) {
                continue;
            }
            let k = a - keyed.counted;
            let o = (usize::BITS - (k + 1).leading_zeros() - 1) as u64;
            let own = own_state_of(o, classes.clone(), q, a);
            assert_eq!(own.region.unresolved, keyed.region.unresolved, "d={d} k={k}");
            seen += 1;
        }
        assert!(seen > 20, "{seen}");
    }
}
