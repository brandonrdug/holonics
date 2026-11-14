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
//! the schedule. Why the letters at a crossing (§4 item 4, [`holonics_engine::field::Field::lettered`]): the codec held only the code
//! passage's bytes and refused every other.

use holonics_engine::codec::FieldCodec;
use holonics_engine::passage::held_out;
use holonics_engine::region::{views_of, TrainRegion};
use crate::exterior::*;
use holonics_engine::codec::count;
use std::io::Read;
use std::path::Path;
use holonics_engine::field::{FieldLearner, FieldRealization, MaterialMean, PassSlice, StorePass, NEAR};
use std::collections::HashMap;
use std::io::{BufRead, Seek, SeekFrom};
use holonics_engine::passage::{Cut, Kind, Piece, PieceBytes, Slice, Stretch, held_set};

/// The store's slices in its own order (`tools/corpus_passage.py`'s `SLICES`).
const SLICES: [&str; 5] = ["code", "web", "science", "books", "wikidata"];
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
/// The readings the card's driver reads before any command, which leave the state's bytes as they are.
const READINGS: [&str; 3] = ["FIELD_PROFILE", "FIELD_PHASES", "FIELD_TRACE"];

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
    fn take(&mut self, region: &TrainRegion, counted: usize) {
        let n = region.classes.len() as u64;
        self.regions += 1;
        self.sites += n;
        self.domain += counted as u64;
        self.squared += n * n;
        self.open += region.unresolved.iter().filter(|&&u| u).count() as u64;
    }

    fn text(&self) -> String {
        format!("regions={} sites={} domain={} squared={} open={}", self.regions, self.sites, self.domain, self.squared, self.open)
    }
}

/// The store's counts, `(role, slice) → (pieces, store octets)`, from its `STORE.tsv`.
fn store_counts(text: &str) -> Result<HashMap<(String, String), (u64, u128)>> {
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
fn counters_text(realization: &dyn FieldRealization) -> String {
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
/// ([`FieldLearner::lettered`]), the yardstick read again (`at=after`), the pass set at the store's start with its law (the octaves of a
/// stretch's draws, the section's bounds) and `OUT/STATE.0` saved. A continued learner (with its pass) reads on from its place.
pub fn train(args: &[String], realization: &mut dyn FieldRealization) -> Result<()> {
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
    let mut learner = FieldLearner::from_text(std::str::from_utf8(&from_text)?).map_err(|e| e.to_string())?;
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
    let mut codec = FieldCodec::from_text(&codec_text, units)?;
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
        learner.pass = Some(StorePass { role: role.to_string(), store: args[4].clone(), stretches: 0, least: LEAST, octaves: OCTAVES, pairs: PAIRS_BOUND, sites: SITES_BOUND, slices: names.iter().map(|n| PassSlice { name: n.to_string(), piece: 0, cursor: 0, taken: 0 }).collect() });
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
    // The step's price since the last save ([`FieldReceipt::transfer`] and [`FieldReceipt::external`]), printed and never acted on.
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
        let mut regions: Vec<TrainRegion> = Vec::new();
        let (mut tally, mut by_slice) = (Tally::default(), vec![0u64; cut.slices.len()]);
        let (mut in_pairs, mut in_sites) = (0u64, 0u64);
        while let Some(drawn) = cut.next() {
            let n = drawn.sites();
            if in_sites > 0 && (in_pairs + n * n > cut.pass.pairs || in_sites + n > cut.pass.sites) {
                break;
            }
            let Stretch { region, counted, .. } = cut.take(drawn, &codec)?;
            tally.take(&region, counted);
            by_slice[drawn.slice] += 1;
            (in_pairs, in_sites) = (in_pairs + n * n, in_sites + n);
            regions.push(region);
        }
        if regions.is_empty() {
            ended = true;
            break;
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
        println!(
            "STORE_SECTION n={done} {} {} stretches={} before={} after={} deposited={} transfer={} external={} rate={}{opening} regions_ms={regions_ms} deposit_ms={deposit_ms} ms={}",
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
fn refuse_variables(command: &str) -> Result<()> {
    let set: Vec<String> = std::env::vars_os().filter_map(|(k, _)| k.into_string().ok()).filter(|k| k.starts_with("FIELD_") && !READINGS.contains(&k.as_str())).collect();
    if !set.is_empty() {
        return Err(format!("{command} reads no variable for its law, and {} set", set.join(", ")).into());
    }
    Ok(())
}

/// The slices of `role` the store holds, in the store's order.
fn role_names(counts: &HashMap<(String, String), (u64, u128)>, role: &str) -> Vec<&'static str> {
    SLICES.iter().copied().filter(|n| counts.contains_key(&(role.to_string(), n.to_string()))).collect()
}

/// A slice of `role` opened: its index's pieces and its file.
fn open_slice(store: &Path, role: &str, name: &str, counts: &HashMap<(String, String), (u64, u128)>) -> Result<Slice> {
    let stem = if role == "held" { "HELD" } else { "DOCS" };
    let (count, quota) = counts[&(role.to_string(), name.to_string())];
    Ok(Slice { name: name.to_string(), quota, pieces: pieces_of(&store.join(format!("{stem}_{name}.tsv")), count)?, source: Box::new(SliceFile(std::fs::File::open(store.join(format!("{stem}_{name}.bin")))?)) })
}

/// [definition; agent-inferred, November 14] **`found-lane STATE STATE_SHA KEYS KEYS_SHA OUT`**: the learner `STATE` with one more lane on its
/// fine field ([`FieldLearner::laned`]: every read from the lane and every write into it at zero, a tower's level kept and the glue's reads and
/// writes of the lane at zero), its draws read from `KEYS` past the learner's count, written to `OUT`. Before it writes, every line is judged
/// (`FOUND_LANE_LINE`): the learner's head may change only its count of key draws; the fine field's declaration only its width and its lanes;
/// the fine field's material, the glue and the two moment lines keep every standing word at the place the founding's map gives it (a moment
/// line's lane words at zero in the first and at their family's mean in the second); every other line (the level's line, its field's
/// declaration and material, the parts, the pass) is equal. Anything else is refused and nothing is written (November 11: a state tool that
/// left a line behind). Reads no realization: that every face is kept is read on the card by the line's own held read of the founded state.
pub fn found_lane(args: &[String]) -> Result<()> {
    if args.len() != 6 {
        return Err("found-lane STATE STATE_SHA KEYS KEYS_SHA OUT".into());
    }
    let started = std::time::Instant::now();
    let text = pinned_read(&args[1], &args[2], STATE_BUDGET)?;
    let learner = FieldLearner::from_text(std::str::from_utf8(&text)?).map_err(|e| e.to_string())?;
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
    let learner = FieldLearner::from_text(&text).map_err(|e| e.to_string())?;
    let mut pass = learner.pass.clone().ok_or("a state with no pass line")?;
    let before = pass.clone();
    for slice in &mut pass.slices {
        (slice.piece, slice.cursor, slice.taken) = (0, 0, 0);
    }
    let mut next = learner.clone();
    next.pass = Some(pass);
    let written = next.to_text();
    let (old_lines, new_lines): (Vec<&str>, Vec<&str>) = (text.lines().collect(), written.lines().collect());
    if old_lines.len() != new_lines.len() {
        return Err("a next pass whose state has a different count of lines".into());
    }
    let differing: Vec<usize> = (0..old_lines.len()).filter(|&i| old_lines[i] != new_lines[i]).collect();
    if differing.len() != 1 || !old_lines[differing[0]].starts_with("pass ") {
        return Err(format!("a next pass that changes lines other than the pass line ({:?})", differing).into());
    }
    let back = FieldLearner::from_text(&written).map_err(|e| e.to_string())?;
    if back.pass.as_ref().map(|p| p.stretches) != Some(before.stretches) || back.field != learner.field {
        return Err("a next pass whose state does not read back as the source's field and count".into());
    }
    std::fs::write(out, &written)?;
    println!("NEXT_PASS stretches={} before={} after={} lines={} differing_line={}", before.stretches, before.slices.iter().map(|s| format!("{}:{}:{}", s.name, s.piece, s.taken)).collect::<Vec<_>>().join(","), back.pass.as_ref().map_or(String::new(), |p| p.slices.iter().map(|s| format!("{}:{}:{}", s.name, s.piece, s.taken)).collect::<Vec<_>>().join(",")), old_lines.len(), differing[0] + 1);
    Ok(())
}

/// [measurement; theory, November 13, P55 part B; the design record of November 13, §4.4] `read-cavity UNITS UNITS_SHA STORE STORE_SHA KEYS KEYS_SHA
/// CODEC CODEC_SHA PLACES STATE STATE_SHA OUT [ROLE]`: **a held place's news at its cavity opening**, a reading (with `ROLE` = `prefix`, the
/// same reading on the documents the line trains on, G187). Each slice of the held role, alone and in the
/// store's order, is cut afresh from stretch 1 with the key file's seed (as `read-store`, retired by C6 of #603, cut it), whole stretches until at least `PLACES` places.
/// For each place `t` of a stretch: the stretch as a region with every place written but `t`; `c0`, the face at the built opening with no tick
/// ([`holonics_engine::field::Field::opening_face`], on the host) at `t`'s written class; `cK`, the face after the declared ticks by the
/// realization's read (`read_faces`, the regions batched under the pass's two bounds) at the same class. On the code slice each stretch is also
/// read with the leading spaces of each line that begins inside it doubled (the copy cut at the stretch's bound of 1,022 places), `c0` at every
/// place of the copy. Codes are on `2^(−20)` bits. One line a place to `OUT/cavity.tsv` (numbers only); a line a slice with the devices' times.
///
/// [measurement; theory, November 13, P57 item 2 (G132)] With the faces, the realization reads each open place's chart `r̂` (64 words on
/// `2^(−16)`) at the opening, after ticks 1, 2 and 3 (each tick's opening) and after the last tick ([`FieldRealization::read_tick_charts`]); the
/// trained readout's code at each stage, `c0` to `c3` and `cK`, is the face of that chart at the written class (`c0` checked against the host's
/// opening face, `cK` against the realization's face). The charts go to `OUT/words.bin` (the place rows' order, five stages of 64 little-endian
/// 32-bit words a place). The same is read at the open places of each slice's whole masks, as `read-store` cut them (rows `W`,
/// `OUT/words_whole.bin`). The output directory is private: it holds no text, but it is the held passage's places.
pub fn read_cavity(args: &[String], realization: &mut dyn FieldRealization) -> Result<()> {
    if args.len() != 13 && args.len() != 14 {
        return Err("read-cavity UNITS UNITS_SHA STORE STORE_SHA KEYS KEYS_SHA CODEC CODEC_SHA PLACES STATE STATE_SHA OUT [ROLE]".into());
    }
    let started = std::time::Instant::now();
    refuse_variables("read-cavity")?;
    let units = units_of(&args[1], &args[2])?;
    if !units.merges().is_empty() {
        return Err("the store's cut is on bytes: a units file of merges is refused".into());
    }
    let store = Path::new(&args[3]);
    let counts = store_counts(std::str::from_utf8(&pinned_read(&store.join("STORE.tsv").to_string_lossy(), &args[4], READ_BUDGET as usize)?)?)?;
    let keys = pinned_read(&args[5], &args[6], READ_BUDGET as usize)?;
    let seed = u64::from_be_bytes(keys.get(keys.len().saturating_sub(8)..).filter(|w| w.len() == 8).ok_or("a key file of fewer than eight bytes")?.try_into()?);
    let codec = FieldCodec::from_text(&String::from_utf8(pinned_read(&args[7], &args[8], READ_BUDGET as usize)?)?, units)?;
    let places = positive(&args[9])?;
    let learner = FieldLearner::from_text(std::str::from_utf8(&pinned_read(&args[10], &args[11], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let law = learner.pass.clone().ok_or("a state with no pass line: read-cavity reads a state of the store's line")?;
    if learner.field.declaration.alphabet != codec.alphabet() {
        return Err("a state whose alphabet is not its codec's".into());
    }
    let out = Path::new(&args[12]);
    if out.exists() {
        return Err(format!("{} exists", out.display()).into());
    }
    std::fs::create_dir_all(out)?;
    let mut tsv = std::io::BufWriter::new(std::fs::File::create(out.join("cavity.tsv"))?);
    use std::io::Write as _;
    writeln!(tsv, "row\tslice\tstretch\tt\tclass\tc0\tcK\tsource\tc1\tc2\tc3\tcO")?;
    let mut words = std::io::BufWriter::new(std::fs::File::create(out.join("words.bin"))?);
    let mut words_whole = std::io::BufWriter::new(std::fs::File::create(out.join("words_whole.bin"))?);
    let dw = learner.field.declaration.width;
    let stages_expected = learner.field.declaration.ticks + 1;
    // [P60 item 7] The opening's code through its lift at every place of a region (cavity openings only, no tick), where the field has the lift;
    // `-` where it has not. At a written place it is the place's code with it alone open among the others (the cavity opening is the opening of
    // the region masked there, §4.4a's check), so one region of every place written gives the one-place masks' codes.
    let opened = learner.field.declaration.opening;
    let opening_of = |classes: &[usize], unresolved: &[bool]| -> std::result::Result<Vec<Option<i64>>, String> {
        if !opened {
            return Ok(vec![None; classes.len()]);
        }
        let region = [TrainRegion::plain(classes.to_vec(), unresolved.to_vec())];
        let views = views_of(&region);
        learner.field.opening_codes(&views[0]).map_err(|e| e.to_string())
    };
    let cell = |v: Option<i64>| v.map_or("-".to_string(), |c| c.to_string());
    let code_of_read = |r: &[i32], class: usize| -> std::result::Result<i64, String> { Ok(learner.field.face_of_read(r).map_err(|e| e.to_string())?.code(class)) };
    let put_words = |w: &mut std::io::BufWriter<std::fs::File>, rows: &[Vec<i32>], at: usize| -> std::io::Result<()> {
        for stage in rows {
            for &v in &stage[at * dw..(at + 1) * dw] {
                w.write_all(&v.to_le_bytes())?;
            }
        }
        Ok(())
    };
    // [measurement; G187] The role read: the held documents by default (the line's reads, every line kept), or `prefix`, the documents the line
    // trains on, cut and read the same way, so the codes on text the field has met stand beside the codes on text it has not.
    let role = match args.get(13).map(String::as_str) {
        None | Some("held") => "held",
        Some("prefix") => "prefix",
        Some(other) => return Err(format!("read-cavity reads the held or the prefix role, not {other}").into()),
    };
    let names = role_names(&counts, role);
    println!("CAVITY_LAW role={role} places={places} least={} octaves={} pairs_bound={} sites_bound={} ticks={} alphabet={} ms={}", law.least, law.octaves, law.pairs, law.sites, learner.field.declaration.ticks, codec.alphabet(), started.elapsed().as_millis());
    const COPY_BOUND: usize = 1022;
    for &name in &names {
        let slice = open_slice(store, role, name, &counts)?;
        let pass = StorePass { role: role.to_string(), store: args[4].clone(), stretches: 0, least: law.least, octaves: law.octaves, pairs: law.pairs, sites: law.sites, slices: vec![PassSlice { name: name.to_string(), piece: 0, cursor: 0, taken: 0 }] };
        let mut cut = Cut { seed, slices: vec![slice], pass };
        let mut stretches: Vec<(Vec<usize>, Vec<u8>, bool)> = Vec::new();
        let mut wholes: Vec<(usize, TrainRegion)> = Vec::new();
        let mut taken = 0usize;
        while taken < places as usize {
            let Some(drawn) = cut.next() else { break };
            let at = cut.pass.slices[drawn.slice].clone();
            let bytes = cut.slices[drawn.slice].bytes(at.piece as usize, at.cursor, drawn.q + drawn.a)?;
            let ends = drawn.ends;
            let stretch = cut.take(drawn, &codec)?;
            taken += stretch.region.classes.len();
            if stretch.kind == Kind::MaskWhole {
                wholes.push((stretches.len(), stretch.region.clone()));
            }
            stretches.push((stretch.region.classes.clone(), bytes, ends));
        }
        // c0 on the host, a region a place; the first stretch's places checked against the whole opening.
        // [the ring record §4] On a field that reads twice the opening a place's chart begins from is the second read's, marked by the first
        // read's face, so c0 is read from the realization's chart at that opening (its parity with the host's charts is on record, the card's
        // `the_field_that_reads_twice_on_the_card_reads_the_hosts_bits`), and the host reads no opening of its own.
        let marked = learner.field.declaration.mark;
        let host_start = std::time::Instant::now();
        let mut c0: Vec<Vec<i64>> = Vec::with_capacity(stretches.len());
        // (the places of a stretch read on the host's threads: a reading, each place's region its own)
        use rayon::prelude::*;
        for (k, (classes, _, _)) in stretches.iter().enumerate().filter(|_| !marked) {
            let codes: Vec<std::result::Result<i64, String>> = (0..classes.len())
                .into_par_iter()
                .map(|t| {
                    let mut mask = vec![false; classes.len()];
                    mask[t] = true;
                    let region = [TrainRegion::plain(classes.clone(), mask)];
                    let views = views_of(&region);
                    let face = learner.field.opening_face(&views[0], t).map_err(|e| e.to_string())?;
                    if k == 0 {
                        let whole = learner.field.opening_face_whole(&views[0], t).map_err(|e| e.to_string())?;
                        if whole.code(classes[t]) != face.code(classes[t]) {
                            return Err(format!("the opening's face at a place differs from the whole opening's (stretch 1, place {t})"));
                        }
                    }
                    Ok(face.code(classes[t]))
                })
                .collect();
            c0.push(codes.into_iter().collect::<std::result::Result<Vec<i64>, String>>()?);
        }
        let host_ms = host_start.elapsed().as_millis();
        // cK on the realization, the regions batched under the pass's two bounds.
        let card_start = std::time::Instant::now();
        let mut ck: Vec<Vec<i64>> = stretches.iter().map(|(c, _, _)| vec![0i64; c.len()]).collect();
        // [P57 item 2] Each place's charts by stage (its one open row at each stage) and the trained readout's codes c1 to c3.
        let mut charts: Vec<Vec<Vec<Vec<i32>>>> = stretches.iter().map(|(c, _, _)| vec![Vec::new(); c.len()]).collect();
        let mut mid: Vec<Vec<[i64; 3]>> = stretches.iter().map(|(c, _, _)| vec![[0i64; 3]; c.len()]).collect();
        let jobs: Vec<(usize, usize)> = stretches.iter().enumerate().flat_map(|(k, (c, _, _))| (0..c.len()).map(move |t| (k, t))).collect();
        let mut at = 0usize;
        let mut batches = 0usize;
        while at < jobs.len() {
            let (mut in_pairs, mut in_sites, mut end) = (0u64, 0u64, at);
            while end < jobs.len() {
                let s = stretches[jobs[end].0].0.len() as u64;
                if in_sites > 0 && (in_pairs + s * s > law.pairs || in_sites + s > law.sites) {
                    break;
                }
                (in_pairs, in_sites, end) = (in_pairs + s * s, in_sites + s, end + 1);
            }
            let regions: Vec<TrainRegion> = jobs[at..end]
                .iter()
                .map(|&(k, t)| {
                    let classes = &stretches[k].0;
                    let mut mask = vec![false; classes.len()];
                    mask[t] = true;
                    TrainRegion::plain(classes.clone(), mask)
                })
                .collect();
            let (faces, stages) = realization.read_tick_charts(&learner.field, &views_of(&regions)).map_err(|e| e.to_string())?;
            for ((&(k, t), f), st) in jobs[at..end].iter().zip(&faces).zip(stages) {
                let class = stretches[k].0[t];
                ck[k][t] = f[t].as_ref().ok_or("an open place without a face")?.code(class);
                if st.len() != stages_expected || st.iter().any(|s| s.len() != dw) {
                    return Err("a place's charts by stage that are not one row of each stage".into());
                }
                if code_of_read(&st[stages_expected - 1], class)? != ck[k][t] {
                    return Err(format!("the face of the last chart differs from the realization's face (stretch {k}, place {t})").into());
                }
                mid[k][t] = [code_of_read(&st[1], class)?, code_of_read(&st[2], class)?, code_of_read(&st[3], class)?];
                charts[k][t] = st;
            }
            batches += 1;
            at = end;
        }
        let card_ms = card_start.elapsed().as_millis();
        if marked {
            for (k, (classes, _, _)) in stretches.iter().enumerate() {
                c0.push((0..classes.len()).map(|t| code_of_read(&charts[k][t][0], classes[t])).collect::<std::result::Result<Vec<i64>, _>>()?);
            }
        }
        let opening_start = std::time::Instant::now();
        let co: Vec<Vec<Option<i64>>> = stretches.par_iter().map(|(classes, _, _)| opening_of(classes, &vec![false; classes.len()])).collect::<std::result::Result<_, String>>()?;
        let opening_ms = opening_start.elapsed().as_millis();
        for (k, (classes, _, _)) in stretches.iter().enumerate() {
            for t in 0..classes.len() {
                if code_of_read(&charts[k][t][0], classes[t])? != c0[k][t] {
                    return Err(format!("the face of the opening's chart differs from the host's opening face (stretch {k}, place {t})").into());
                }
                let [c1, c2, c3] = mid[k][t];
                writeln!(tsv, "P\t{name}\t{k}\t{t}\t{}\t{}\t{}\t-\t{c1}\t{c2}\t{c3}\t{}", classes[t], c0[k][t], ck[k][t], cell(co[k][t]))?;
                put_words(&mut words, &charts[k][t], 0)?;
            }
        }
        // [P57 item 2] The slice's whole masks as the cut gives them, their open places' charts by stage and codes.
        let whole_start = std::time::Instant::now();
        let mut whole_places = 0usize;
        let mut w_at = 0usize;
        while w_at < wholes.len() {
            let (mut in_pairs, mut in_sites, mut end) = (0u64, 0u64, w_at);
            while end < wholes.len() {
                let s = wholes[end].1.classes.len() as u64;
                if in_sites > 0 && (in_pairs + s * s > law.pairs || in_sites + s > law.sites) {
                    break;
                }
                (in_pairs, in_sites, end) = (in_pairs + s * s, in_sites + s, end + 1);
            }
            let regions: Vec<TrainRegion> = wholes[w_at..end].iter().map(|(_, r)| r.clone()).collect();
            let (faces, stages) = realization.read_tick_charts(&learner.field, &views_of(&regions)).map_err(|e| e.to_string())?;
            for ((k, region), (f, st)) in wholes[w_at..end].iter().zip(faces.iter().zip(&stages)) {
                let wo = opening_of(&region.classes, &region.unresolved)?;
                if st.len() != stages_expected {
                    return Err("a whole mask's charts by stage that are not one of each stage".into());
                }
                for (row, t) in (0..region.classes.len()).filter(|&t| region.unresolved[t]).enumerate() {
                    let class = region.classes[t];
                    let cw = f[t].as_ref().ok_or("an open place without a face")?.code(class);
                    let at_row = |s: usize| &st[s][row * dw..(row + 1) * dw];
                    if code_of_read(at_row(stages_expected - 1), class)? != cw {
                        return Err(format!("a whole mask's last chart's face differs from the realization's face (stretch {k}, place {t})").into());
                    }
                    let (w0, w1, w2, w3) = (code_of_read(at_row(0), class)?, code_of_read(at_row(1), class)?, code_of_read(at_row(2), class)?, code_of_read(at_row(3), class)?);
                    writeln!(tsv, "W\t{name}\t{k}\t{t}\t{class}\t{w0}\t{cw}\t-\t{w1}\t{w2}\t{w3}\t{}", cell(wo[t]))?;
                    put_words(&mut words_whole, st, row)?;
                    whole_places += 1;
                }
            }
            w_at = end;
        }
        let whole_ms = whole_start.elapsed().as_millis();
        // The code slice's copies: each line's leading spaces doubled, c0 on the host at every place of the copy.
        let mut copy_places = 0usize;
        let copy_start = std::time::Instant::now();
        if name == "code" {
            for (k, (_, bytes, ends)) in stretches.iter().enumerate() {
                let (mut copy, mut source) = (Vec::with_capacity(2 * bytes.len()), Vec::with_capacity(2 * bytes.len()));
                let mut leading = false;
                for (t, &b) in bytes.iter().enumerate() {
                    if b == b'\n' {
                        leading = true;
                    } else if b != b' ' {
                        leading = false;
                    }
                    copy.push(b);
                    source.push(t);
                    if leading && b == b' ' {
                        copy.push(b);
                        source.push(t);
                    }
                }
                let mut classes = codec.encode(&copy)?;
                if *ends {
                    let first_void = bytes.len();
                    classes.resize(classes.len() + NEAR, codec.void());
                    source.extend((0..NEAR).map(|v| first_void + v));
                }
                classes.truncate(COPY_BOUND);
                source.truncate(COPY_BOUND);
                let codes: Vec<std::result::Result<i64, String>> = (0..classes.len())
                    .into_par_iter()
                    .map(|t| {
                        let mut mask = vec![false; classes.len()];
                        mask[t] = true;
                        let region = [TrainRegion::plain(classes.clone(), mask)];
                        let views = views_of(&region);
                        Ok(learner.field.opening_face(&views[0], t).map_err(|e| e.to_string())?.code(classes[t]))
                    })
                    .collect();
                let cc = opening_of(&classes, &vec![false; classes.len()])?;
                for (t, code) in codes.into_iter().enumerate() {
                    writeln!(tsv, "C\t{name}\t{k}\t{t}\t{}\t{}\t-\t{}\t-\t-\t-\t{}", classes[t], code?, source[t], cell(cc[t]))?;
                }
                copy_places += classes.len();
            }
        }
        // [P60 item 7c] Each stretch begun seven places later (its bytes from the eighth on, a true end's voids kept), the opening's code at every
        // place of the copy, `source` the place of the stretch it stands at; where the field has the lift.
        let mut later_places = 0usize;
        if opened {
            const LATER: usize = 7;
            let later: Vec<(usize, Vec<usize>, Vec<Option<i64>>)> = stretches
                .par_iter()
                .enumerate()
                .filter(|(_, (_, bytes, _))| bytes.len() > LATER)
                .map(|(k, (_, bytes, ends))| -> std::result::Result<_, String> {
                    let mut classes = codec.encode(&bytes[LATER..]).map_err(|e| e.to_string())?;
                    if *ends {
                        classes.resize(classes.len() + NEAR, codec.void());
                    }
                    let codes = opening_of(&classes, &vec![false; classes.len()])?;
                    Ok((k, classes, codes))
                })
                .collect::<std::result::Result<_, String>>()?;
            for (k, classes, codes) in later {
                for (t, (class, code)) in classes.iter().zip(codes).enumerate() {
                    writeln!(tsv, "S\t{name}\t{k}\t{t}\t{class}\t-\t-\t{}\t-\t-\t-\t{}", t + LATER, cell(code))?;
                }
                later_places += classes.len();
            }
        }
        println!(
            "CAVITY_SLICE slice={name} stretches={} places={taken} host_c0_ms={host_ms} card_cK_ms={card_ms} card_batches={batches} host_opening_ms={opening_ms} whole_masks={} whole_places={whole_places} whole_ms={} copy_places={copy_places} later_places={later_places} host_copy_ms={} elapsed_ms={}",
            stretches.len(),
            wholes.len(),
            whole_ms,
            copy_start.elapsed().as_millis(),
            started.elapsed().as_millis()
        );
    }
    tsv.flush()?;
    words.flush()?;
    words_whole.flush()?;
    println!("CAVITY_DONE ms={}", started.elapsed().as_millis());
    Ok(())
}

/// [measurement; theory, November 12, P49 item 4] `write-store UNITS UNITS_SHA STORE STORE_SHA KEYS KEYS_SHA CODEC CODEC_SHA DOCUMENTS PROMPT RUN
/// OUT STATE STATE_SHA`: **the release from held prompts**. On the store's held role, for each slice in the store's order, its first
/// `DOCUMENTS` pieces that open their document and hold at least `PROMPT + RUN` places; a problem is the piece's first `PROMPT` places and
/// `RUN` open places. The release is the tower's as it stands, its law fixed here: [`holonics_engine::field::Field::sample_runs`] over
/// every problem at once with `sweeps = RUN` (one place a read), `refine = REFINE` (0 where none is given), the codec's void, the key file's seed, `run_bound = 0`, the
/// near tail, the keyed order within an octave, no given lengths, no one-end draw, a sweep that always goes on and no observer: the store's
/// writer state run from `k = 0` upward, by octaves of distance from the prompt. `OUT` is created new; each problem writes three files of
/// raw bytes (`SLICE_NN.prompt`, `SLICE_NN.written`, the codec's decode up to the first void, and `SLICE_NN.reference`, the piece's next
/// `RUN` places), and one line (`STORE_WRITE`: its slice, its document, the places written before a void and the release's reads); a closing
/// line holds the card's counters and the time. A reading: the state is not touched.
pub fn write(args: &[String], realization: &mut dyn FieldRealization) -> Result<()> {
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
    let codec = FieldCodec::from_text(&String::from_utf8(pinned_read(&args[7], &args[8], READ_BUDGET as usize)?)?, units)?;
    let (documents, prompt, run) = (positive(&args[9])?, positive(&args[10])?, positive(&args[11])?);
    // [agent-inferred, November 14, the mark's record §3] `REFINE` passes after the sweeps, each revisiting the written run one place a read in
    // the writer's order and drawing each place again on the region as it stands (a place reopened is silent, so on a field that reads twice
    // its first read marks it): the draft reheard as the field's own. A pass costs as many reads as the run has places. Zero, the default, is
    // the writer as it stood. (Read first as a count of reads: 256 passes passed a 300 s deadline on November 14.)
    let refine = match args.get(15) { Some(r) => r.parse::<usize>().map_err(|_| "REFINE is a count")?, None => 0 };
    let out = Path::new(&args[12]);
    let learner = FieldLearner::from_text(std::str::from_utf8(&pinned_read(&args[13], &args[14], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    if learner.field.declaration.alphabet != codec.alphabet() {
        return Err("a state whose alphabet is not its codec's".into());
    }
    let role = "held";
    let names = role_names(&counts, role);
    // Each problem: its slice, its document, its prompt's classes, its prompt's bytes and its reference continuation's bytes.
    let mut problems: Vec<(&str, u64, Vec<usize>, Vec<u8>, Vec<u8>)> = Vec::new();
    for &name in &names {
        let mut slice = open_slice(store, role, name, &counts)?;
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
    use holonics_engine::passage::{cut_of, lengths_of, state_of};

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
            }
        }
        assert!(writers > 100 && masks > 100, "{writers} {masks}");
    }
}
