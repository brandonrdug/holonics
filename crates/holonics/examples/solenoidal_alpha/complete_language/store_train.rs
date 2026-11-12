//! [definition; theory, November 12 (the record of the opening's room, §4)] **`train-store`, the store's trainer**: a learner continued on a
//! store of whole documents (`tools/corpus_passage.py`), read by keyed stretches, one keyed state a stretch, in sections declared to fill one
//! batch of the card. Its cut is the reference port's (`store_stretch_census.py`, the passage record's receipts), draw for draw, and its lines
//! are held to the port's. Its law is in code and in the learner's state: the rate held at the state's `rate_bits`, every step standing at its
//! size, no growth but the letters' at the crossing, the step's transfer and external price printed and never acted on. It reads no
//! environment variable for its law: a run where any variable named `FIELD_…` is set is refused, but for the two readings the card's driver
//! reads before any command (`FIELD_PROFILE`, `FIELD_PHASES`), which leave every bit of the state as it is.
//!
//! Why no room and no opening (the record §2 and §4): a document has no question and no answer; the code line's openings computed 0.704 of a
//! lap's sites for 0.018 of its compared places. Why one state a stretch (§4 item 2): a pass over fresh text meets a new stretch at every draw,
//! and a second state of the same bytes buys less than the next stretch does. Why a declared section (§4 item 3): a section is the unit a
//! deposit consumes, so its extent is law and is carried in the state; a section read from the device's free memory would let the bits follow
//! the schedule. Why the letters at a crossing (§4 item 4, [`holonics::hnn::tower::field::Field::lettered`]): the codec held only the code
//! passage's bytes and refused every other.

use super::field_train::{held_out, held_text, mix, problems_of, question_text, shape, step_transfer, units_of, views_of, weighed_domain, FieldCodec, Problems, Shape, TrainRegion};
use super::tower_train::{count, positive, STATE_BUDGET};
use super::*;
use holonics::hnn::tower::field::{octave_of, FieldLearner, FieldRealization, MaterialMean, PassSlice, StorePass, NEAR};
use std::collections::HashMap;
use std::io::{BufRead, Seek, SeekFrom};

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
const READINGS: [&str; 2] = ["FIELD_PROFILE", "FIELD_PHASES"];

/// A piece of a slice's index: its offset in the slice's file, its title's and its text's octets, and whether it opens and closes its document.
#[derive(Clone, Copy, Debug)]
struct Piece {
    offset: u64,
    title: u64,
    text: u64,
    opens: bool,
    closes: bool,
}

impl Piece {
    /// Whether a line feed stands between the title and the text (a piece that opens with a title; the store keeps no separator).
    fn line_feed(&self) -> bool {
        self.opens && self.title > 0
    }

    /// The piece's places: its title's bytes, one line feed where it opens with a title, and its text's bytes.
    fn places(&self) -> u64 {
        self.title + u64::from(self.line_feed()) + self.text
    }
}

/// A slice of the role read: its name, its quota (the role's store octets), its pieces in order and its file.
struct Slice {
    name: String,
    quota: u128,
    pieces: Vec<Piece>,
    file: std::fs::File,
}

impl Slice {
    /// The places `[from, from + len)` of piece `k`, read from the slice's file at the piece's offset (never the slice in memory).
    fn bytes(&mut self, k: usize, from: u64, len: u64) -> Result<Vec<u8>> {
        let p = self.pieces[k];
        let end = from + len;
        if end > p.places() {
            return Err("a stretch past its piece's places".into());
        }
        let mut out = Vec::with_capacity(len as usize);
        let read = |file: &mut std::fs::File, at: u64, n: u64, out: &mut Vec<u8>| -> Result<()> {
            if n == 0 {
                return Ok(());
            }
            file.seek(SeekFrom::Start(at))?;
            let start = out.len();
            out.resize(start + n as usize, 0);
            file.read_exact(&mut out[start..])?;
            Ok(())
        };
        if !p.line_feed() {
            read(&mut self.file, p.offset + from, len, &mut out)?;
            return Ok(out);
        }
        // The title's places, the line feed at place `title`, then the text's places one past their bytes.
        let t = p.title;
        if from < t {
            read(&mut self.file, p.offset + from, end.min(t) - from, &mut out)?;
        }
        if from <= t && t < end {
            out.push(b'\n');
        }
        let text_from = from.max(t + 1);
        if text_from < end {
            read(&mut self.file, p.offset + text_from - 1, end - text_from, &mut out)?;
        }
        Ok(out)
    }
}

/// A stretch drawn at the pass's place and not yet taken: its slice, its draw, its context and run, whether a true end follows it, and whether
/// it finishes its piece.
#[derive(Clone, Copy, Debug)]
struct Drawn {
    slice: usize,
    d: u64,
    q: u64,
    a: u64,
    ends: bool,
    done: bool,
}

impl Drawn {
    /// The stretch's sites: its context, its run and the near tail where a true end follows.
    fn sites(&self) -> u64 {
        self.q + self.a + if self.ends { NEAR as u64 } else { 0 }
    }
}

/// [definition; the record §4 item 1; the port's `lengths_of`] A stretch's two draws, the `d`th of the pass.
fn lengths_of(seed: u64, d: u64, least: u64, octaves: u64) -> (u64, u64) {
    let oq = mix(seed, d | 1 << 60) % octaves;
    let q = (least << oq) + mix(seed, d | 3 << 60) % (least << oq);
    let oa = mix(seed, d | 1 << 62) % octaves;
    let a = (least << oa) + mix(seed, d | 5 << 60) % (least << oa);
    (q, a)
}

/// [definition; the record §4 item 1; the port's `cut_of`] The stretch at a cursor with `rest` places left: its context and run, whether a
/// true end follows (the piece closes its document), and whether the piece is done. Where the next `q + a` places would leave at least the
/// least context, the stretch is those places and the piece goes on; else it takes the rest, its context `min(q, rest − 1)`.
fn cut_of(seed: u64, d: u64, rest: u64, closes: bool, least: u64, octaves: u64) -> (u64, u64, bool, bool) {
    let (q, a) = lengths_of(seed, d, least, octaves);
    if rest >= q + a + least {
        return (q, a, false, false);
    }
    let q = q.min(rest - 1);
    (q, rest - q, closes, true)
}

/// The kind of a stretch's one keyed state, as the port names it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Kind {
    MaskWhole,
    MaskRun,
    Writer,
}

/// [definition; the record §4 item 2; the port's `state_of`] **A stretch's one keyed state**, from `head = mix(seed, d)`: bit 17 set, the
/// writer's state (the context known, the run's places in the writer's octave order of their distance from the context, keyed within an
/// octave, its first `k` resolved, `k` by octaves of reads, `k = 0` among them, and a true end's voids given); clear, a mask state (`shape`'s
/// law over the whole stretch or past the context, the density `τ = u²`, weighed back by its domain `⌊2√(mK)⌋`). Regions are plain: no port.
/// Returns the region, its kind, and the sites its code is a code of (its weighed domain, or its open places for the writer's state).
fn state_of(seed: u64, d: u64, classes: Vec<usize>, q: usize, a: usize) -> (TrainRegion, Kind, usize) {
    let n = classes.len();
    let head = mix(seed, d);
    if (head >> 17) & 1 == 1 {
        let key = mix(seed, d | 7 << 61);
        let most = a - 1;
        let o = (key % (u64::from(usize::BITS - most.leading_zeros()) + 1)) as u32;
        let k = if o == 0 {
            0
        } else {
            let low = 1usize << (o - 1);
            let high = ((1usize << o) - 1).min(most);
            low + (mix(seed, d | 15 << 60) as usize) % (high - low + 1)
        };
        let mut unresolved: Vec<bool> = (0..n).map(|t| t >= q && t < q + a).collect();
        let mut order: Vec<usize> = (q..q + a).collect();
        order.sort_by_key(|&t| (octave_of(t + 1 - q), mix(key, t as u64), t));
        for &t in &order[..k] {
            unresolved[t] = false;
        }
        return (TrainRegion::plain(classes, unresolved), Kind::Writer, a - k);
    }
    let (mask, kind, from) = match shape(seed, d, q, n) {
        Shape::Masked(mask) => (mask, Kind::MaskWhole, 0),
        Shape::Answer(mask) => (mask, Kind::MaskRun, q),
    };
    let domain = weighed_domain(n - from, &mask);
    (TrainRegion { domain: Some(domain), ..TrainRegion::plain(classes, mask) }, kind, domain)
}

/// [definition; the record §4 items 1 and 5; the port's `store`] **The cut over a role of the store**: the slices interleaved by least progress
/// against their quotas (the role's store octets; the earlier slice at a tie), each slice's pieces read in order from their cursors, the pass's
/// place carried in the learner's state ([`StorePass`]).
struct Cut {
    seed: u64,
    slices: Vec<Slice>,
    pass: StorePass,
}

impl Cut {
    /// The next stretch at the pass's place, drawn and not taken (none where every slice's pieces are read).
    fn next(&self) -> Option<Drawn> {
        let live: Vec<usize> = (0..self.slices.len()).filter(|&s| (self.pass.slices[s].piece as usize) < self.slices[s].pieces.len()).collect();
        let mut slice = *live.first()?;
        for &other in &live[1..] {
            let (t_o, t_n) = (self.pass.slices[other].taken as u128, self.pass.slices[slice].taken as u128);
            if t_o * self.slices[slice].quota < t_n * self.slices[other].quota {
                slice = other;
            }
        }
        let at = &self.pass.slices[slice];
        let piece = self.slices[slice].pieces[at.piece as usize];
        let d = self.pass.stretches + 1;
        let (q, a, ends, done) = cut_of(self.seed, d, piece.places() - at.cursor, piece.closes, self.pass.least, self.pass.octaves);
        Some(Drawn { slice, d, q, a, ends, done })
    }

    /// The drawn stretch taken: its region read from its slice's file, and the pass moved past it.
    fn take(&mut self, drawn: Drawn, codec: &FieldCodec) -> Result<(TrainRegion, Kind, usize)> {
        let at = self.pass.slices[drawn.slice].clone();
        let bytes = self.slices[drawn.slice].bytes(at.piece as usize, at.cursor, drawn.q + drawn.a)?;
        let mut classes = codec.encode(&bytes)?;
        if classes.len() != bytes.len() {
            return Err("a stretch whose bytes are not one class each".into());
        }
        if drawn.ends {
            classes.resize(classes.len() + NEAR, codec.void());
        }
        let region = state_of(self.seed, drawn.d, classes, drawn.q as usize, drawn.a as usize);
        let place = &mut self.pass.slices[drawn.slice];
        place.taken += drawn.q + drawn.a;
        if drawn.done {
            (place.piece, place.cursor) = (place.piece + 1, 0);
        } else {
            place.cursor += drawn.q + drawn.a;
        }
        self.pass.stretches = drawn.d;
        Ok(region)
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
        let [_, title, text, opens, closes] = w[..] else { return Err("a slice's index row that is not five counts".into()) };
        out.push(Piece { offset, title, text, opens: opens == 1, closes: closes == 1 });
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

/// The code line's held passage (te7's lap script's `DEV`) as `train-field` reads it: its problems at the codec, those whose answer stands
/// within the codec's extent.
fn held_set(codec: &FieldCodec, text: &[u8]) -> Result<Problems> {
    let mut out = Vec::new();
    for (q, a) in problems_of(text) {
        let (qc, ac) = (codec.encode(&question_text(&q))?, codec.encode(&a)?);
        if ac.len() < codec.answer {
            out.push((qc, ac, a.len()));
        }
    }
    Ok(out)
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
pub(super) fn train(args: &[String], realization: &mut dyn FieldRealization) -> Result<()> {
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
        slices.push(Slice { name: name.to_string(), quota, pieces: pieces_of(&store.join(format!("{stem}_{name}.tsv")), count)?, file: std::fs::File::open(store.join(format!("{stem}_{name}.bin")))? });
    }
    println!("STORE_PASS_AT stretches={} {} {} ms={}", pass.stretches, pass.slices.iter().map(|s| format!("{}_piece={} {}_cursor={} {}_taken={}", s.name, s.piece, s.name, s.cursor, s.name, s.taken)).collect::<Vec<_>>().join(" "), counters_text(realization), started.elapsed().as_millis());
    let mut cut = Cut { seed, slices, pass };
    let mut mean = MaterialMean::new(learner.field.material_len());
    // The step's price since the last save ([`FieldReceipt::transfer`] and [`FieldReceipt::external`]), printed and never acted on.
    let (mut transfers, mut externals, mut curvatures, mut priced, mut since) = (0i128, 0i128, 0i128, 0usize, 0usize);
    let mut prior: Option<i128> = None;
    let mut done = 0usize;
    let mut ended = false;
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
            let (region, _, counted) = cut.take(drawn, &codec)?;
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
        let views = views_of(&regions);
        let deposit_start = std::time::Instant::now();
        let receipt = learner.section_realized(&views, realization).map_err(|e| e.to_string())?;
        let deposit_ms = deposit_start.elapsed().as_millis();
        mean.take(&learner.field).map_err(|e| e.to_string())?;
        if receipt.sites as u64 != tally.domain {
            return Err(format!("a section whose receipt counts {} sites against the cut's domain of {}", receipt.sites, tally.domain).into());
        }
        let opt = |v: Option<i64>| v.map_or("-".to_string(), |c| micro(c, receipt.sites).to_string());
        println!(
            "STORE_SECTION n={done} {} {} stretches={} before={} after={} deposited={} transfer={} external={} rate={} regions_ms={regions_ms} deposit_ms={deposit_ms} ms={}",
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
        learner.pass = Some(cut.pass.clone());
        done += 1;
        since += 1;
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
    println!(
        "STORE_PASS role={role} sections={done} stretches_read={} ended={ended} {} ms={}",
        cut.pass.stretches,
        cut.pass.slices.iter().map(|s| format!("{}_pieces={}", s.name, s.piece)).collect::<Vec<_>>().join(" "),
        started.elapsed().as_millis()
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

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
        let p = Piece { offset: 0, title: 5, text: 9, opens: true, closes: true };
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
            let (region, kind, counted) = state_of(0xABCD, d, classes, q, a);
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
