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
    fn take(&mut self, region: &OwnedRegion, counted: usize) {
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
        learner.pass = Some(StorePass { role: role.to_string(), store: args[4].clone(), stretches: 0, least: LEAST, octaves: OCTAVES, pairs: PAIRS_BOUND, sites: SITES_BOUND, own: false, slices: names.iter().map(|n| PassSlice { name: n.to_string(), piece: 0, cursor: 0, taken: 0 }).collect() });
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
/// The sections the held forward reads at, `σ = 2^(−e)` bits.
const HELD_SIGMAS: [u32; 2] = [6, 4];

pub fn read_open_rows(args: &[String]) -> Result<()> {
    use holonics_engine::field::{OpenCrowds, OpenRows, OPEN_OCTAVES};
    use rayon::prelude::*;
    // [measurement; theory, November 15 21:16Z] `ticks` and `held` read with OTHER's field where given (the sections stay STATE's pass's).
    let mode = args.get(13).map(String::as_str);
    let fits = match (args.len(), mode) {
        (13, None) | (14, Some("crowds" | "ticks" | "held" | "halves" | "bytick")) => true,
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
                    println!("TICK_NEWS slice={name} tick={k} kind={label} sites={} unread_current={:.4} mean_abs_bits={:.6} under_sigma(sites/mass) {}", c.sites[kind], c.unread[kind] as f64 / n, c.cost_abs[kind] as f64 / n / (1u64 << 40) as f64, shares.join(" "));
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
    use holonics_engine::field::NEAR;
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
