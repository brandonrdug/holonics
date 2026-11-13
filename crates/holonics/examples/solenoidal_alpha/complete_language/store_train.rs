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
//! the schedule. Why the letters at a crossing (§4 item 4, [`holonics::hnn::tower::field::Field::lettered`]): the codec held only the code
//! passage's bytes and refused every other.

use super::field_train::{held_out, held_text, mix, problems_of, question_text, shape, step_transfer, units_of, views_of, weighed_domain, FieldCodec, Problems, Shape, TrainRegion};
use super::tower_train::{count, positive, STATE_BUDGET};
use super::*;
use holonics::hnn::tower::field::{level_declaration, level_split, octave_of, FieldLearner, FieldRealization, MaterialMean, PassSlice, StorePass, LEVEL_HARMONICS, NEAR};
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
const READINGS: [&str; 3] = ["FIELD_PROFILE", "FIELD_PHASES", "FIELD_TRACE"];

/// A piece of a slice's index: its offset in the slice's file, its title's and its text's octets, and whether it opens and closes its document.
#[derive(Clone, Copy, Debug)]
struct Piece {
    document: u64,
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
/// Returns the region, its kind, the sites its code is a code of (its weighed domain, or its open places for the writer's state), and
/// for the writer's state its `k` and its front (the first open place of its order, the place the release draws next).
fn state_of(seed: u64, d: u64, classes: Vec<usize>, q: usize, a: usize) -> Stretch {
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
        return Stretch { region: TrainRegion::plain(classes, unresolved), kind: Kind::Writer, counted: a - k, q, writer: Some((k, order[k])) };
    }
    let (mask, kind, from) = match shape(seed, d, q, n) {
        Shape::Masked(mask) => (mask, Kind::MaskWhole, 0),
        Shape::Answer(mask) => (mask, Kind::MaskRun, q),
    };
    let domain = weighed_domain(n - from, &mask);
    Stretch { region: TrainRegion { domain: Some(domain), ..TrainRegion::plain(classes, mask) }, kind, counted: domain, q, writer: None }
}

/// A stretch's one keyed state ([`state_of`]): its region, its kind, the sites its code is a code of, its context, and for the writer's
/// state its `k` and its front place.
struct Stretch {
    region: TrainRegion,
    kind: Kind,
    counted: usize,
    q: usize,
    writer: Option<(usize, usize)>,
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
    fn take(&mut self, drawn: Drawn, codec: &FieldCodec) -> Result<Stretch> {
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
        let parts: Vec<String> = holonics::hnn::tower::field::SECTION_PARTS
            .iter()
            .zip(holonics::hnn::tower::field::SECTION_PART_NAMES)
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
    Ok(Slice { name: name.to_string(), quota, pieces: pieces_of(&store.join(format!("{stem}_{name}.tsv")), count)?, file: std::fs::File::open(store.join(format!("{stem}_{name}.bin")))? })
}

/// A region's code over its unresolved places on the codes' own grain (`2^(−20)` bits), beside the count of those places: the sum of
/// `face.code(class)`, as [`held_out`] reads a face.
fn region_code(faces: &[Option<holonics::hnn::tower::TowerFace>], region: &TrainRegion) -> Result<(i64, usize)> {
    let (mut code, mut places) = (0i64, 0usize);
    for (t, &open) in region.unresolved.iter().enumerate() {
        if open {
            let face = faces.get(t).and_then(Option::as_ref).ok_or("an unresolved place without a face")?;
            code += face.code(region.classes[t]);
            places += 1;
        }
    }
    Ok((code, places))
}

/// The four kinds a read gathers by: a mask over the whole stretch, a mask past the context, the writer's state at `k = 0`, at `k > 0`.
const READ_KINDS: [&str; 4] = ["mask_whole", "mask_run", "writer_k0", "writer_k"];

fn read_kind(stretch: &Stretch) -> usize {
    match (stretch.kind, stretch.writer) {
        (Kind::MaskWhole, _) => 0,
        (Kind::MaskRun, _) => 1,
        (Kind::Writer, Some((0, _))) => 2,
        (Kind::Writer, _) => 3,
    }
}

/// The octaves the surprise census reads: a place's code on the codes' `2^(−20)` bits has bit length `b`, so it codes `[2^(b−21), 2^(b−20))`
/// bits (`b = 0`: a code of zero); 40 lengths hold every code a face of `2^(−16)` shares can give.
const SURPRISE_OCTAVES: usize = 40;

/// The octaves the writer's partitions read (octave 8 holds the farthest place a run of at most 511 places draws; a run that ends a piece
/// may reach one octave more).
const READ_OCTAVES: usize = 10;

/// [definition; theory, November 13, the design record §4.4a; P60 item 3] **`found-opening STATE STATE_SHA OUT`**: the learner `STATE` with the
/// opening's lift founded at zero ([`FieldLearner::with_opening`]), written to the file `OUT`. Before it writes, every line of the state that the
/// law reads is printed for the source and the founded state (`FOUND_OPENING_LINE`) and judged: a line is equal, or it is the declaration's line
/// (its head `hnn-field-v14g`, the source's words kept and the opening's word appended), the parts line (the source's octaves and the opening's at
/// 0), or one of the material's three lines (the source's words kept, the block's `D × D + D` words appended: the material and the first moments
/// at 0, the second at the means the growth opens them at). Any other changed line, an empty line, or a different count of lines is refused and
/// nothing is written: a state tool that leaves a line behind trains every part at a rate the law never set (November 11). Reads no realization.
pub(super) fn found_opening(args: &[String]) -> Result<()> {
    if args.len() != 4 {
        return Err("found-opening STATE STATE_SHA OUT".into());
    }
    let started = std::time::Instant::now();
    let text = pinned_read(&args[1], &args[2], STATE_BUDGET)?;
    let learner = FieldLearner::from_text(std::str::from_utf8(&text)?).map_err(|e| e.to_string())?;
    if learner.to_text().as_bytes() != text.as_slice() {
        return Err("a state that does not read and write back byte for byte".into());
    }
    let out = Path::new(&args[3]);
    if out.exists() {
        return Err("a founded state's path that exists".into());
    }
    let founded = learner.with_opening().map_err(|e| e.to_string())?;
    let (dw, block) = (founded.field.declaration.width, founded.field.material_len() - learner.field.material_len());
    if block != dw * dw + dw {
        return Err(format!("a founding that appended {block} entries, where the lift holds {}", dw * dw + dw).into());
    }
    let (a, b) = (learner.to_text(), founded.to_text());
    let (la, lb): (Vec<&str>, Vec<&str>) = (a.lines().collect(), b.lines().collect());
    if la.len() != lb.len() {
        return Err(format!("a founding that wrote {} lines for {}", lb.len(), la.len()).into());
    }
    let material = learner.field.material_len();
    let mut judged = (0usize, 0usize, 0usize, 0usize);
    for (k, (x, y)) in la.iter().zip(&lb).enumerate() {
        let (wx, wy): (Vec<&str>, Vec<&str>) = (x.split(' ').collect(), y.split(' ').collect());
        if x.is_empty() || y.is_empty() {
            return Err(format!("line {k} is empty in the source or the founded state").into());
        }
        let kept = wy.len() >= wx.len() && wy[..wx.len()] == wx[..];
        let head = |w: &[&str]| w[0].chars().take(24).collect::<String>();
        let verdict = if x == y {
            judged.0 += 1;
            "equal".to_string()
        } else if k == 1 && wy[0] == "hnn-field-v14g" && wy.len() == wx.len() + 2 && wy[1..wx.len()] == wx[1..] && wy.last() == Some(&"1") {
            judged.1 += 1;
            format!("declaration source={x} founded={y}")
        } else if wx[0] == "parts" && kept && wy.len() == wx.len() + 1 && wy.last() == Some(&"0") {
            judged.2 += 1;
            format!("parts appended={}", wy[wx.len()])
        } else if kept && wx.len() == material && wy.len() == material + block {
            judged.3 += 1;
            let tail = &wy[material..];
            let zeros = tail.iter().filter(|&&w| w == "0").count();
            let mut distinct: Vec<&str> = tail.to_vec();
            distinct.sort_unstable();
            distinct.dedup();
            format!("block appended={} zero={zeros} distinct={}", tail.len(), distinct.join(","))
        } else {
            return Err(format!("line {k} ({}) changed beyond the opening's lift: {} words for {}", head(&wx), wy.len(), wx.len()).into());
        };
        println!("FOUND_OPENING_LINE line={k} head={} words_source={} words_founded={} {verdict}", head(&wx), wx.len(), wy.len());
    }
    if judged.1 != 1 || judged.3 != 3 || (learner.rate_parts.is_some() && judged.2 != 1) {
        return Err(format!("a founding whose changed lines are {} declaration, {} parts and {} material lines", judged.1, judged.2, judged.3).into());
    }
    write_new(out, b.as_bytes())?;
    println!("FOUND_OPENING lines={} equal={} declaration={} parts={} material_lines={} material={} block={block} founded_material={} ms={}", la.len(), judged.0, judged.1, judged.2, judged.3, material, founded.field.material_len(), started.elapsed().as_millis());
    Ok(())
}

/// [definition; theory, November 13, the design record §4.9; G145] **`found-level STATE STATE_SHA KEYS KEYS_SHA OUT`**: the learner `STATE` (with
/// the opening's block, whose news the level reads) grown by a level above ([`FieldLearner::scaled_up`] at [`LEVEL_HARMONICS`], after
/// [`level_split`] of its ticks, its field declared by [`level_declaration`]), its founding drawn from the key file past the learner's draws,
/// written to the file `OUT`. Before it writes, every line is judged (`FOUND_LEVEL_LINE`): the learner's head may change only its count of
/// key draws; the field's declaration and material lines are equal; four lines follow them (the level's line, its field's declaration and
/// material, the glue); the two moment lines keep the source's words and append the level's entries at zero; every other line (the parts,
/// the rates, the pass) is equal. Anything else is refused and nothing is written (November 11: a state tool that left a line behind).
/// Reads no realization.
pub(super) fn found_level(args: &[String]) -> Result<()> {
    if args.len() != 6 {
        return Err("found-level STATE STATE_SHA KEYS KEYS_SHA OUT".into());
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
    let d = learner.field.declaration;
    let founded = learner.scaled_up(LEVEL_HARMONICS, level_split(&d), level_declaration(&d), &keys).map_err(|e| e.to_string())?;
    let block = founded.field.material_len() - learner.field.material_len();
    let (a, b) = (learner.to_text(), founded.to_text());
    let (la, lb): (Vec<&str>, Vec<&str>) = (a.lines().collect(), b.lines().collect());
    if lb.len() != la.len() + 4 {
        return Err(format!("a founding that wrote {} lines for {}", lb.len(), la.len()).into());
    }
    let material = learner.field.material_len();
    let s = founded.field.scale.as_deref().ok_or("a founding without its level")?;
    let mut judged = 0usize;
    for (k, y) in lb.iter().enumerate() {
        let (x, verdict) = match k {
            0 => {
                let (wx, wy): (Vec<&str>, Vec<&str>) = (la[0].split(' ').collect(), y.split(' ').collect());
                let ok = wx.len() == wy.len() && wx.iter().zip(&wy).enumerate().all(|(i, (p, q))| i == 2 || p == q);
                if !ok {
                    return Err("the learner's head changed beyond its count of key draws".into());
                }
                (la[0], format!("head draws {} to {}", wx[2], wy[2]))
            }
            1 | 2 if *y == la[k] => (la[k], "equal".to_string()),
            3 if *y == format!("level {} {}", s.harmonics, s.split) => ("", format!("level harmonics={} split={}", s.harmonics, s.split)),
            4 if Some(*y) == s.coarse.to_text().lines().next() => ("", format!("the level's field's declaration {y}")),
            5 if y.split(' ').count() == s.coarse.theta.len() => ("", format!("the level's field's material {} words", s.coarse.theta.len())),
            6 if y.split(' ').count() == s.glue.len() => ("", format!("the glue {} words, {} drawn", s.glue.len(), s.glue.iter().filter(|&&v| v != 0).count())),
            7 | 8 => {
                let (wx, wy): (Vec<&str>, Vec<&str>) = (la[k - 4].split(' ').collect(), y.split(' ').collect());
                if wx.len() != material || wy.len() != material + block || wy[..material] != wx[..] || wy[material..].iter().any(|&w| w != "0") {
                    return Err(format!("line {k}: a moment line that does not keep the source's words and append the level's at zero").into());
                }
                (la[k - 4], format!("moments kept={material} appended={block} at zero"))
            }
            _ if k > 8 && *y == la[k - 4] => (la[k - 4], "equal".to_string()),
            _ => return Err(format!("line {k} changed beyond the level's founding").into()),
        };
        judged += 1;
        let head: String = y.chars().take(24).collect();
        println!("FOUND_LEVEL_LINE line={k} head={head} words_source={} words_founded={} {verdict}", if x.is_empty() { 0 } else { x.split(' ').count() }, y.split(' ').count());
    }
    write_new(out, b.as_bytes())?;
    println!("FOUND_LEVEL lines={} judged={judged} material={material} block={block} founded_material={} draws={} ms={}", lb.len(), founded.field.material_len(), founded.drawn - learner.drawn, started.elapsed().as_millis());
    Ok(())
}

/// [measurement; theory, November 13, Brandon's self-induction (that day, 18:05Z) and an outside read's depth sweep; G149] `read-depth UNITS
/// UNITS_SHA STORE STORE_SHA KEYS KEYS_SHA CODEC CODEC_SHA PLACES TICKS STATE STATE_SHA OUT`: **what the field's recurrence does past the depth
/// it was trained at**, a reading. The state's field is read with its declared ticks replaced by `TICKS` (its material, its level's split and
/// every law the same; a tick reads only the ticks before it, so the stage after tick `k` of one run is the face a run of `k` ticks gives).
/// Each slice of the held role is cut as `read-cavity` cuts it, whole stretches until `PLACES` places, each place open alone among its
/// stretch's written places, read by the realization's charts by stage (each tick's opening and after the last). `OUT/depth.tsv` holds a line
/// a place (numbers only): the slice, the place's class, and for every stage the code of its class and the face's expected code, both on
/// `2^(−20)` bits; `OUT/charts.bin` its charts by stage (`TICKS + 1` rows of `D` little-endian 32-bit words a place, in the rows' order). The
/// output directory is private.
pub(super) fn read_depth(args: &[String], realization: &mut dyn FieldRealization) -> Result<()> {
    if args.len() != 14 {
        return Err("read-depth UNITS UNITS_SHA STORE STORE_SHA KEYS KEYS_SHA CODEC CODEC_SHA PLACES TICKS STATE STATE_SHA OUT".into());
    }
    let started = std::time::Instant::now();
    refuse_variables("read-depth")?;
    let units = units_of(&args[1], &args[2])?;
    if !units.merges().is_empty() {
        return Err("the store's cut is on bytes: a units file of merges is refused".into());
    }
    let store = Path::new(&args[3]);
    let counts = store_counts(std::str::from_utf8(&pinned_read(&store.join("STORE.tsv").to_string_lossy(), &args[4], READ_BUDGET as usize)?)?)?;
    let keys = pinned_read(&args[5], &args[6], READ_BUDGET as usize)?;
    let seed = u64::from_be_bytes(keys.get(keys.len().saturating_sub(8)..).filter(|w| w.len() == 8).ok_or("a key file of fewer than eight bytes")?.try_into()?);
    let codec = FieldCodec::from_text(&String::from_utf8(pinned_read(&args[7], &args[8], READ_BUDGET as usize)?)?, units)?;
    let places = positive(&args[9])? as usize;
    let ticks = positive(&args[10])? as usize;
    let learner = FieldLearner::from_text(std::str::from_utf8(&pinned_read(&args[11], &args[12], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let law = learner.pass.clone().ok_or("a state with no pass line: read-depth reads a state of the store's line")?;
    if learner.field.declaration.alphabet != codec.alphabet() {
        return Err("a state whose alphabet is not its codec's".into());
    }
    if learner.field.scale.as_ref().is_some_and(|s| ticks <= s.split) {
        return Err("a depth at or under the level's split".into());
    }
    let mut field = learner.field.clone();
    field.declaration.ticks = ticks;
    let out = Path::new(&args[13]);
    if out.exists() {
        return Err(format!("{} exists", out.display()).into());
    }
    std::fs::create_dir_all(out)?;
    use std::io::Write as _;
    let mut tsv = std::io::BufWriter::new(std::fs::File::create(out.join("depth.tsv"))?);
    let mut charts_bin = std::io::BufWriter::new(std::fs::File::create(out.join("charts.bin"))?);
    let stages = ticks + 1;
    writeln!(tsv, "slice\tclass{}", (0..stages).map(|k| format!("\tcode{k}\tentropy{k}")).collect::<String>())?;
    println!("DEPTH_LAW role=held places={places} ticks={ticks} declared_ticks={} level={} ms={}", learner.field.declaration.ticks, field.scale.is_some(), started.elapsed().as_millis());
    let expected = |f: &holonics::hnn::tower::TowerFace| -> i64 {
        let sum: i128 = f.masses.iter().map(|&m| m as i128 * holonics::hnn::tower::face_code(m, f.total) as i128).sum();
        let total = (f.total as i128).max(1);
        ((2 * sum + total) / (2 * total)) as i64
    };
    for &name in &role_names(&counts, "held") {
        let slice = open_slice(store, "held", name, &counts)?;
        let pass = StorePass { role: "held".to_string(), store: args[4].clone(), stretches: 0, least: law.least, octaves: law.octaves, pairs: law.pairs, sites: law.sites, slices: vec![PassSlice { name: name.to_string(), piece: 0, cursor: 0, taken: 0 }] };
        let mut cut = Cut { seed, slices: vec![slice], pass };
        let mut stretches: Vec<Vec<usize>> = Vec::new();
        let mut taken = 0usize;
        while taken < places {
            let Some(drawn) = cut.next() else { break };
            let stretch = cut.take(drawn, &codec)?;
            taken += stretch.region.classes.len();
            stretches.push(stretch.region.classes.clone());
        }
        let jobs: Vec<(usize, usize)> = stretches.iter().enumerate().flat_map(|(k, c)| (0..c.len()).map(move |t| (k, t))).collect();
        let card_start = std::time::Instant::now();
        let mut at = 0usize;
        while at < jobs.len() {
            let (mut in_pairs, mut in_sites, mut end) = (0u64, 0u64, at);
            while end < jobs.len() {
                let s = stretches[jobs[end].0].len() as u64;
                if in_sites > 0 && (in_pairs + s * s > law.pairs || in_sites + s > law.sites) {
                    break;
                }
                (in_pairs, in_sites, end) = (in_pairs + s * s, in_sites + s, end + 1);
            }
            let regions: Vec<TrainRegion> = jobs[at..end]
                .iter()
                .map(|&(k, t)| {
                    let mut mask = vec![false; stretches[k].len()];
                    mask[t] = true;
                    TrainRegion::plain(stretches[k].clone(), mask)
                })
                .collect();
            let (_, charts) = realization.read_tick_charts(&field, &views_of(&regions)).map_err(|e| e.to_string())?;
            for (&(k, t), st) in jobs[at..end].iter().zip(&charts) {
                if st.len() != stages || st.iter().any(|c| c.len() != field.declaration.width) {
                    return Err("a place's charts by stage that are not one row of each stage".into());
                }
                let class = stretches[k][t];
                let mut line = format!("{name}\t{class}");
                for chart in st {
                    let face = field.face_of_read(chart).map_err(|e| e.to_string())?;
                    line.push_str(&format!("\t{}\t{}", face.code(class), expected(&face)));
                    for &v in chart {
                        charts_bin.write_all(&v.to_le_bytes())?;
                    }
                }
                writeln!(tsv, "{line}")?;
            }
            at = end;
        }
        println!("DEPTH_SLICE slice={name} stretches={} places={} card_ms={} ms={}", stretches.len(), jobs.len(), card_start.elapsed().as_millis(), started.elapsed().as_millis());
    }
    println!("DEPTH_DONE {} ms={}", counters_text(realization), started.elapsed().as_millis());
    Ok(())
}

/// [measurement; theory, November 13, an outside read of that day (its claim 1); G148] `read-influence UNITS UNITS_SHA STORE STORE_SHA KEYS
/// KEYS_SHA CODEC CODEC_SHA PAIRS STATE STATE_SHA OUT`: **whether one place's influence on another follows the news between them or their
/// distance**, a reading. Each slice of the held role is cut as `read-cavity` cuts it, whole stretches until four times `PAIRS` places, every
/// place written. `PAIRS` pairs a slice are drawn by the key file's seed: a receiving place `b` (uniform over the slice's places), a distance
/// `d` log-uniform over the stretch, the source `a = b − d` (or `b + d` where that leaves the stretch), and a class drawn from another place of
/// the slice, unequal to `a`'s. Each pair is read twice by the realization at the last tick with `b` alone open: as the stretch holds it, and
/// with `a`'s class replaced. `OUT/influence.tsv` holds a line a pair (numbers only): the slice, `d`, the news strictly between `a` and `b`
/// (the opening's codes, the level's news law at a written place, on `2^(−20)` bits), `b`'s code both ways. The output directory is private.
pub(super) fn read_influence(args: &[String], realization: &mut dyn FieldRealization) -> Result<()> {
    if args.len() != 13 {
        return Err("read-influence UNITS UNITS_SHA STORE STORE_SHA KEYS KEYS_SHA CODEC CODEC_SHA PAIRS STATE STATE_SHA OUT".into());
    }
    let started = std::time::Instant::now();
    refuse_variables("read-influence")?;
    let units = units_of(&args[1], &args[2])?;
    if !units.merges().is_empty() {
        return Err("the store's cut is on bytes: a units file of merges is refused".into());
    }
    let store = Path::new(&args[3]);
    let counts = store_counts(std::str::from_utf8(&pinned_read(&store.join("STORE.tsv").to_string_lossy(), &args[4], READ_BUDGET as usize)?)?)?;
    let keys = pinned_read(&args[5], &args[6], READ_BUDGET as usize)?;
    let seed = u64::from_be_bytes(keys.get(keys.len().saturating_sub(8)..).filter(|w| w.len() == 8).ok_or("a key file of fewer than eight bytes")?.try_into()?);
    let codec = FieldCodec::from_text(&String::from_utf8(pinned_read(&args[7], &args[8], READ_BUDGET as usize)?)?, units)?;
    let pairs = positive(&args[9])? as usize;
    let learner = FieldLearner::from_text(std::str::from_utf8(&pinned_read(&args[10], &args[11], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let law = learner.pass.clone().ok_or("a state with no pass line: read-influence reads a state of the store's line")?;
    if learner.field.declaration.alphabet != codec.alphabet() || !learner.field.declaration.opening {
        return Err("a state whose alphabet is not its codec's, or without the opening's block".into());
    }
    let out = Path::new(&args[12]);
    if out.exists() {
        return Err(format!("{} exists", out.display()).into());
    }
    std::fs::create_dir_all(out)?;
    use std::io::Write as _;
    let mut tsv = std::io::BufWriter::new(std::fs::File::create(out.join("influence.tsv"))?);
    writeln!(tsv, "slice\td\tnews_between\tcode\tcode_moved\tclocks_between")?;
    println!("INFLUENCE_LAW role=held pairs={pairs} level={} ms={}", learner.field.scale.is_some(), started.elapsed().as_millis());
    use rayon::prelude::*;
    let mut state = seed ^ 0x9E37_79B9_7F4A_7C15;
    let mut draw = move || {
        state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    };
    for &name in &role_names(&counts, "held") {
        let slice = open_slice(store, "held", name, &counts)?;
        let pass = StorePass { role: "held".to_string(), store: args[4].clone(), stretches: 0, least: law.least, octaves: law.octaves, pairs: law.pairs, sites: law.sites, slices: vec![PassSlice { name: name.to_string(), piece: 0, cursor: 0, taken: 0 }] };
        let mut cut = Cut { seed, slices: vec![slice], pass };
        let mut stretches: Vec<Vec<usize>> = Vec::new();
        let mut taken = 0usize;
        while taken < 4 * pairs {
            let Some(drawn) = cut.next() else { break };
            let stretch = cut.take(drawn, &codec)?;
            taken += stretch.region.classes.len();
            stretches.push(stretch.region.classes.clone());
        }
        let news: Vec<Vec<i64>> = stretches
            .par_iter()
            .map(|classes| {
                let region = [TrainRegion::plain(classes.clone(), vec![false; classes.len()])];
                let views = views_of(&region);
                learner.field.opening_codes(&views[0]).map_err(|e| e.to_string())?.into_iter().map(|c| c.ok_or_else(|| "a place the opening does not compare".to_string())).collect::<std::result::Result<Vec<i64>, String>>()
            })
            .collect::<std::result::Result<_, String>>()?;
        // [G150's premise] Each turned head's clock (its variation) over each stretch as it is written.
        let clocks: Vec<Vec<Vec<i64>>> = stretches
            .par_iter()
            .map(|classes| {
                let region = [TrainRegion::plain(classes.clone(), vec![false; classes.len()])];
                let views = views_of(&region);
                learner.field.head_variations(&views[0]).map_err(|e| e.to_string())
            })
            .collect::<std::result::Result<_, String>>()?;
        let places: Vec<(usize, usize)> = stretches.iter().enumerate().flat_map(|(k, c)| (0..c.len()).map(move |t| (k, t))).collect();
        // (stretch, b, a, moved class)
        let mut drawn_pairs: Vec<(usize, usize, usize, usize)> = Vec::with_capacity(pairs);
        let mut tries = 0usize;
        while drawn_pairs.len() < pairs && tries < 64 * pairs {
            tries += 1;
            let (k, b) = places[(draw() % places.len() as u64) as usize];
            let n = stretches[k].len();
            if n < 2 {
                continue;
            }
            // A distance log-uniform over the stretch: an octave `o` with `2^o ≤ n − 1`, then a distance within it.
            let octaves = (64 - ((n - 1) as u64).leading_zeros()) as u64;
            let o = (draw() % octaves) as u32;
            let (lo, hi) = (1usize << o, ((1usize << (o + 1)) - 1).min(n - 1));
            let d = lo + (draw() % (hi - lo + 1) as u64) as usize;
            let a = if b >= d { b - d } else if b + d < n { b + d } else { continue };
            let (k2, t2) = places[(draw() % places.len() as u64) as usize];
            let moved = stretches[k2][t2];
            if moved == stretches[k][a] {
                continue;
            }
            drawn_pairs.push((k, b, a, moved));
        }
        // Each pair's two regions, batched under the pass's bounds.
        let mut regions: Vec<TrainRegion> = Vec::with_capacity(2 * drawn_pairs.len());
        for &(k, b, a, moved) in &drawn_pairs {
            let mut mask = vec![false; stretches[k].len()];
            mask[b] = true;
            regions.push(TrainRegion::plain(stretches[k].clone(), mask.clone()));
            let mut c = stretches[k].clone();
            c[a] = moved;
            regions.push(TrainRegion::plain(c, mask));
        }
        let card_start = std::time::Instant::now();
        let mut codes: Vec<i64> = Vec::with_capacity(regions.len());
        let mut at = 0usize;
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
            for (j, f) in faces.iter().enumerate() {
                let r = &regions[at + j];
                let b = r.unresolved.iter().position(|&u| u).ok_or("a region without its open place")?;
                codes.push(f[b].as_ref().ok_or("an open place without a face")?.code(r.classes[b]));
            }
            at = end;
        }
        for (i, &(k, b, a, _)) in drawn_pairs.iter().enumerate() {
            let (lo, hi) = (a.min(b), a.max(b));
            let between: i64 = news[k][lo + 1..hi].iter().sum();
            let gaps: Vec<String> = clocks[k].iter().map(|sigma| (sigma[hi] - sigma[lo]).unsigned_abs().to_string()).collect();
            writeln!(tsv, "{name}\t{}\t{between}\t{}\t{}\t{}", hi - lo, codes[2 * i], codes[2 * i + 1], gaps.join(","))?;
        }
        println!("INFLUENCE_SLICE slice={name} stretches={} pairs={} reads={} card_ms={} ms={}", stretches.len(), drawn_pairs.len(), regions.len(), card_start.elapsed().as_millis(), started.elapsed().as_millis());
    }
    println!("INFLUENCE_DONE {} ms={}", counters_text(realization), started.elapsed().as_millis());
    Ok(())
}

/// [measurement; theory, November 13, the design record §4.9; G146, from the outside read of that day's points 1 and 3] `read-news UNITS
/// UNITS_SHA STORE STORE_SHA KEYS KEYS_SHA CODEC CODEC_SHA PLACES STATE STATE_SHA`: **how far a place's news at its two-sided cavity falls
/// short of a block's**, a reading on the host. Each slice of the held role is cut as `read-cavity` cuts it, whole stretches until `PLACES`
/// places, every place written. `c1_t` is the opening's code of place `t` with it alone open (its cavity face); for blocks of `b = 2` and
/// `3` places at every offset, `cb_t` is the code of `t` with its block open and every other place written, and a block's news is the sum
/// of its places' `cb`. Read by slice: the sums of `cb` over the sums of `c1` on the same places (a pseudo-likelihood's shortfall: one
/// over it is the share of a block's news the single places carry), the share of places dark at their cavity (`c1` under a bit) that carry
/// four bits or more in a pair, and the level's cut on `c1` and on `c2` (offset 0) at the flat face's section: the sites' share, the mean
/// epoch, the strides of three sections or more with their share of the news, and the sites the two cuts share. Numbers only.
pub(super) fn read_news(args: &[String]) -> Result<()> {
    if args.len() != 12 {
        return Err("read-news UNITS UNITS_SHA STORE STORE_SHA KEYS KEYS_SHA CODEC CODEC_SHA PLACES STATE STATE_SHA".into());
    }
    let started = std::time::Instant::now();
    refuse_variables("read-news")?;
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
    let law = learner.pass.clone().ok_or("a state with no pass line: read-news reads a state of the store's line")?;
    if learner.field.declaration.alphabet != codec.alphabet() || !learner.field.declaration.opening {
        return Err("a state whose alphabet is not its codec's, or without the opening's block".into());
    }
    let section = holonics::hnn::tower::field::level_section(codec.alphabet());
    let bit = 1i64 << 20;
    println!("NEWS_LAW role=held places={places} section={section} ms={}", started.elapsed().as_millis());
    use rayon::prelude::*;
    // Every place's opening code through the opening's lift (the level's news law at a written place) with the places `open` open and the
    // rest written, at its written class.
    let codes_at = |classes: &[usize], open: std::ops::Range<usize>| -> std::result::Result<Vec<i64>, String> {
        let mut mask = vec![false; classes.len()];
        mask[open].fill(true);
        let region = [TrainRegion::plain(classes.to_vec(), mask)];
        let views = views_of(&region);
        learner.field.opening_codes(&views[0]).map_err(|e| e.to_string())?.into_iter().map(|c| c.ok_or_else(|| "a place the opening does not compare".to_string())).collect()
    };
    // The cut's readings on one stretch's news: (sites, strides of three sections or more, their news, the news).
    let cut_of = |news: &[i64]| -> (Vec<usize>, usize, i128, i128) {
        let anchors = holonics::hnn::tower::field::level_anchors(news, section);
        let mut sum = vec![0i128; news.len() + 1];
        for (t, &c) in news.iter().enumerate() {
            sum[t + 1] = sum[t] + c as i128;
        }
        let (mut long, mut long_news) = (0usize, 0i128);
        for w in anchors.windows(2) {
            let l = sum[w[1] + 1] - sum[w[0] + 1];
            if l >= 3 * section as i128 {
                (long, long_news) = (long + 1, long_news + l);
            }
        }
        (anchors, long, long_news, sum[news.len()])
    };
    for &name in &role_names(&counts, "held") {
        let slice = open_slice(store, "held", name, &counts)?;
        let pass = StorePass { role: "held".to_string(), store: args[4].clone(), stretches: 0, least: law.least, octaves: law.octaves, pairs: law.pairs, sites: law.sites, slices: vec![PassSlice { name: name.to_string(), piece: 0, cursor: 0, taken: 0 }] };
        let mut cut = Cut { seed, slices: vec![slice], pass };
        let mut stretches: Vec<Vec<usize>> = Vec::new();
        let mut taken = 0usize;
        while taken < places as usize {
            let Some(drawn) = cut.next() else { break };
            let stretch = cut.take(drawn, &codec)?;
            taken += stretch.region.classes.len();
            stretches.push(stretch.region.classes.clone());
        }
        let slice_start = std::time::Instant::now();
        // Per stretch: c1 at every place, and for b in 2, 3 and each offset, every full block's places' codes.
        type Read = (Vec<i64>, [Vec<Option<i64>>; 5]);
        let reads: Vec<std::result::Result<Read, String>> = stretches
            .par_iter()
            .map(|classes| {
                let n = classes.len();
                let c1 = codes_at(classes, 0..0)?;
                let mut blocks: [Vec<Option<i64>>; 5] = Default::default();
                for (slot, (b, o)) in [(2usize, 0usize), (2, 1), (3, 0), (3, 1), (3, 2)].into_iter().enumerate() {
                    let mut out = vec![None; n];
                    let mut start = o;
                    while start + b <= n {
                        let codes = codes_at(classes, start..start + b)?;
                        for t in start..start + b {
                            out[t] = Some(codes[t]);
                        }
                        start += b;
                    }
                    blocks[slot] = out;
                }
                Ok((c1, blocks))
            })
            .collect();
        let reads: Vec<Read> = reads.into_iter().collect::<std::result::Result<_, _>>()?;
        let n_places: usize = reads.iter().map(|(c, _)| c.len()).sum();
        for (slot, (b, o)) in [(2usize, 0usize), (2, 1), (3, 0), (3, 1), (3, 2)].into_iter().enumerate() {
            let (mut sb, mut s1, mut covered) = (0i128, 0i128, 0usize);
            for (c1, blocks) in &reads {
                for (t, v) in blocks[slot].iter().enumerate() {
                    if let Some(v) = v {
                        (sb, s1, covered) = (sb + *v as i128, s1 + c1[t] as i128, covered + 1);
                    }
                }
            }
            let millibits = |sum: i128| sum * 1000 / (covered.max(1) as i128 * bit as i128);
            println!("NEWS_BLOCKS slice={name} b={b} offset={o} places={covered} block_millibits={} single_millibits={} ratio_milli={}", millibits(sb), millibits(s1), if s1 > 0 { sb * 1000 / s1 } else { 0 });
        }
        let (mut dark, mut dark_bright) = (0usize, 0usize);
        for (c1, blocks) in &reads {
            for (t, &c) in c1.iter().enumerate() {
                if c < bit {
                    dark += 1;
                    if blocks[0][t].or(blocks[1][t]).is_some_and(|v| v >= 4 * bit) {
                        dark_bright += 1;
                    }
                }
            }
        }
        println!("NEWS_DARK slice={name} places={n_places} dark_single={dark} of_them_four_bits_in_a_pair={dark_bright}");
        for (label, pick) in [("c1", 0usize), ("c2", 1)] {
            let (mut sites, mut epochs, mut long, mut long_news, mut news, mut shared, mut cut_places) = (0usize, 0usize, 0usize, 0i128, 0i128, 0usize, 0usize);
            for (c1, blocks) in &reads {
                let series: Vec<i64> = if pick == 0 { c1.clone() } else { blocks[0].iter().zip(c1).map(|(v, &c)| v.unwrap_or(c)).collect() };
                let (anchors, l, ln, total) = cut_of(&series);
                let (other, ..) = cut_of(c1);
                sites += anchors.len();
                epochs += anchors.len();
                long += l;
                long_news += ln;
                news += total;
                shared += anchors.iter().filter(|a| other.contains(a)).count();
                cut_places += series.len();
            }
            println!("NEWS_CUT slice={name} news={label} places={cut_places} sites={sites} share_milli={} mean_epoch_milli={} long_strides={long} long_news_milli={} shared_with_c1={shared} millibits_a_place={}", sites * 1000 / cut_places.max(1), cut_places * 1000 / epochs.max(1), if news > 0 { long_news * 1000 / news } else { 0 }, news * 1000 / (cut_places.max(1) as i128 * bit as i128));
        }
        println!("NEWS_SLICE slice={name} stretches={} places={n_places} host_ms={} threads={}", stretches.len(), slice_start.elapsed().as_millis(), rayon::current_num_threads());
    }
    println!("NEWS_DONE ms={}", started.elapsed().as_millis());
    Ok(())
}

/// [measurement; theory, November 13, P55 part B; the design record of November 13, §4.4] `read-cavity UNITS UNITS_SHA STORE STORE_SHA KEYS KEYS_SHA
/// CODEC CODEC_SHA PLACES STATE STATE_SHA OUT`: **a held place's news at its cavity opening**, a reading. Each slice of the held role, alone and in the
/// store's order, is cut afresh from stretch 1 with the key file's seed (as `read-store` cuts it), whole stretches until at least `PLACES` places.
/// For each place `t` of a stretch: the stretch as a region with every place written but `t`; `c0`, the face at the built opening with no tick
/// ([`holonics::hnn::tower::field::Field::opening_face`], on the host) at `t`'s written class; `cK`, the face after the declared ticks by the
/// realization's read (`read_faces`, the regions batched under the pass's two bounds) at the same class. On the code slice each stretch is also
/// read with the leading spaces of each line that begins inside it doubled (the copy cut at the stretch's bound of 1,022 places), `c0` at every
/// place of the copy. Codes are on `2^(−20)` bits. One line a place to `OUT/cavity.tsv` (numbers only); a line a slice with the devices' times.
///
/// [measurement; theory, November 13, P57 item 2 (G132)] With the faces, the realization reads each open place's chart `r̂` (64 words on
/// `2^(−16)`) at the opening, after ticks 1, 2 and 3 (each tick's opening) and after the last tick ([`FieldRealization::read_tick_charts`]); the
/// trained readout's code at each stage, `c0` to `c3` and `cK`, is the face of that chart at the written class (`c0` checked against the host's
/// opening face, `cK` against the realization's face). The charts go to `OUT/words.bin` (the place rows' order, five stages of 64 little-endian
/// 32-bit words a place). The same is read at the open places of each slice's whole masks, as `read-store` cuts them (rows `W`,
/// `OUT/words_whole.bin`). The output directory is private: it holds no text, but it is the held passage's places.
pub(super) fn read_cavity(args: &[String], realization: &mut dyn FieldRealization) -> Result<()> {
    if args.len() != 13 {
        return Err("read-cavity UNITS UNITS_SHA STORE STORE_SHA KEYS KEYS_SHA CODEC CODEC_SHA PLACES STATE STATE_SHA OUT".into());
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
    let mut put_words = |w: &mut std::io::BufWriter<std::fs::File>, rows: &[Vec<i32>], at: usize| -> std::io::Result<()> {
        for stage in rows {
            for &v in &stage[at * dw..(at + 1) * dw] {
                w.write_all(&v.to_le_bytes())?;
            }
        }
        Ok(())
    };
    let role = "held";
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
        let host_start = std::time::Instant::now();
        let mut c0: Vec<Vec<i64>> = Vec::with_capacity(stretches.len());
        // (the places of a stretch read on the host's threads: a reading, each place's region its own)
        use rayon::prelude::*;
        for (k, (classes, _, _)) in stretches.iter().enumerate() {
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

/// A share `n/d` to four decimals, nearest, as a reading prints it (integers: the guard lints bar floats in this crate).
fn share4(n: u128, d: u128) -> String {
    let v = (n * 10_000 + d.max(1) / 2) / d.max(1);
    format!("{}.{:04}", v / 10_000, v % 10_000)
}

/// [measurement; theory, November 13, P56 item 2 (G128 b)] `read-ticks UNITS UNITS_SHA STORE STORE_SHA ROLE KEYS KEYS_SHA CODEC CODEC_SHA SECTIONS STATE
/// STATE_SHA`: **a site's chart from tick to tick**, a reading. The pass's next `SECTIONS` sections, cut from the state's pass line as `train-store`
/// cuts them, each read on the realization by `read_ticks` from the one state, which nothing deposits into. For each site and each tick `k ≥ 1`:
/// `m_k` the largest magnitude of the site's chart at tick `k`'s opening, `d_k` the largest magnitude of its difference from tick `k − 1`'s; the
/// histogram of `bit_length(m_k) − bit_length(d_k)` (`d_k = 0` in its own bin) by tick and by the site's kind (open, definite), for the chart and
/// for the pair contact's chart.
pub(super) fn read_ticks(args: &[String], realization: &mut dyn FieldRealization) -> Result<()> {
    if args.len() != 13 {
        return Err("read-ticks UNITS UNITS_SHA STORE STORE_SHA ROLE KEYS KEYS_SHA CODEC CODEC_SHA SECTIONS STATE STATE_SHA".into());
    }
    let started = std::time::Instant::now();
    refuse_variables("read-ticks")?;
    let units = units_of(&args[1], &args[2])?;
    if !units.merges().is_empty() {
        return Err("the store's cut is on bytes: a units file of merges is refused".into());
    }
    let store = Path::new(&args[3]);
    let counts = store_counts(std::str::from_utf8(&pinned_read(&store.join("STORE.tsv").to_string_lossy(), &args[4], READ_BUDGET as usize)?)?)?;
    let role = args[5].as_str();
    let keys = pinned_read(&args[6], &args[7], READ_BUDGET as usize)?;
    let seed = u64::from_be_bytes(keys.get(keys.len().saturating_sub(8)..).filter(|w| w.len() == 8).ok_or("a key file of fewer than eight bytes")?.try_into()?);
    let codec = FieldCodec::from_text(&String::from_utf8(pinned_read(&args[8], &args[9], READ_BUDGET as usize)?)?, units)?;
    let sections = positive(&args[10])? as usize;
    let learner = FieldLearner::from_text(std::str::from_utf8(&pinned_read(&args[11], &args[12], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let pass = learner.pass.clone().ok_or("a state with no pass line: read-ticks reads a state of the store's line")?;
    let names: Vec<&str> = SLICES.iter().copied().filter(|n| counts.contains_key(&(role.to_string(), n.to_string()))).collect();
    if pass.role != role || pass.store != args[4] || pass.slices.iter().map(|s| s.name.as_str()).ne(names.iter().copied()) {
        return Err("a state whose pass is of another role, store or slices".into());
    }
    if learner.field.declaration.alphabet != codec.alphabet() {
        return Err("a state whose alphabet is not its codec's".into());
    }
    let stem = if role == "held" { "HELD" } else { "DOCS" };
    let mut slices = Vec::with_capacity(names.len());
    for &name in &names {
        let (count, quota) = counts[&(role.to_string(), name.to_string())];
        slices.push(Slice { name: name.to_string(), quota, pieces: pieces_of(&store.join(format!("{stem}_{name}.tsv")), count)?, file: std::fs::File::open(store.join(format!("{stem}_{name}.bin")))? });
    }
    let mut cut = Cut { seed, slices, pass };
    let ticks = learner.field.declaration.ticks;
    // [chart 2][kind 2][tick][bin]: bin 0 a zero difference, bin 65 + (bit_length(m) − bit_length(d)) otherwise.
    const BINS: usize = 130;
    let mut hist = vec![0u64; 2 * 2 * ticks * BINS];
    let bits = |v: u64| 64 - v.leading_zeros() as i64;
    let mut read_sections = 0usize;
    for n in 0..sections {
        let section_start = std::time::Instant::now();
        let mut regions: Vec<TrainRegion> = Vec::new();
        let (mut in_pairs, mut in_sites) = (0u64, 0u64);
        while let Some(drawn) = cut.next() {
            let s = drawn.sites();
            if in_sites > 0 && (in_pairs + s * s > cut.pass.pairs || in_sites + s > cut.pass.sites) {
                break;
            }
            let Stretch { region, .. } = cut.take(drawn, &codec)?;
            (in_pairs, in_sites) = (in_pairs + s * s, in_sites + s);
            regions.push(region);
        }
        if regions.is_empty() {
            break;
        }
        let reads = realization.read_ticks(&learner.field, &views_of(&regions)).map_err(|e| e.to_string())?;
        for (region, per_tick) in regions.iter().zip(&reads) {
            let sites = region.classes.len();
            for k in 1..per_tick.len().min(ticks) {
                for (c, (cur, prev)) in [(&per_tick[k].read, &per_tick[k - 1].read), (&per_tick[k].pair_read, &per_tick[k - 1].pair_read)].into_iter().enumerate() {
                    if cur.len() != prev.len() || cur.is_empty() || !cur.len().is_multiple_of(sites) {
                        continue;
                    }
                    let dw = cur.len() / sites;
                    for t in 0..sites {
                        let (a, b) = (&cur[t * dw..(t + 1) * dw], &prev[t * dw..(t + 1) * dw]);
                        let m = a.iter().map(|&v| u64::from(v.unsigned_abs())).max().unwrap_or(0);
                        let d = a.iter().zip(b).map(|(&x, &y)| (i64::from(x) - i64::from(y)).unsigned_abs()).max().unwrap_or(0);
                        let bin = if d == 0 { 0 } else { (65 + bits(m) - bits(d)).clamp(1, BINS as i64 - 1) as usize };
                        let kind = usize::from(region.unresolved[t]);
                        hist[((c * 2 + kind) * ticks + k) * BINS + bin] += 1;
                    }
                }
            }
        }
        read_sections += 1;
        println!("TICKS_SECTION n={n} regions={} sites={in_sites} ms={} elapsed_ms={}", regions.len(), section_start.elapsed().as_millis(), started.elapsed().as_millis());
    }
    for c in 0..2 {
        for kind in 0..2 {
            for k in 1..ticks {
                let h = &hist[((c * 2 + kind) * ticks + k) * BINS..((c * 2 + kind) * ticks + k + 1) * BINS];
                let total: u64 = h.iter().sum();
                if total == 0 {
                    continue;
                }
                let ge8: u64 = h[(65 + 8)..].iter().sum();
                // The median of the difference in bits, the zero bin read as the largest difference of all.
                let mut order: Vec<(i64, u64)> = (1..BINS).map(|b| (b as i64 - 65, h[b])).collect();
                order.push((i64::MAX, h[0]));
                let (mut acc, mut median) = (0u64, i64::MAX);
                for &(v, cnt) in &order {
                    acc += cnt;
                    if 2 * acc >= total {
                        median = v;
                        break;
                    }
                }
                println!(
                    "TICKS_HIST chart={} kind={} tick={k} sites={total} zero_share={} ge8_share={} median_bits={} counts={}",
                    ["read", "pair_read"][c],
                    ["definite", "open"][kind],
                    share4(h[0] as u128, total as u128),
                    share4(ge8 as u128, total as u128),
                    if median == i64::MAX { "zero".to_string() } else { median.to_string() },
                    (1..BINS).filter(|&b| h[b] > 0).map(|b| format!("{}:{}", b as i64 - 65, h[b])).collect::<Vec<_>>().join(",")
                );
            }
        }
    }
    println!("TICKS_DONE sections={read_sections} ms={}", started.elapsed().as_millis());
    Ok(())
}

/// [measurement; theory, November 12, P49 item 3] `read-store UNITS UNITS_SHA STORE STORE_SHA ROLE KEYS KEYS_SHA CODEC CODEC_SHA HELD HELD_SHA
/// SECTIONS STATE STATE_SHA`: **the pass's cut over a role, read and never deposited**. `STATE` is a state or a mean of the line; the read takes
/// the law of its pass line (the least context, the octaves, the section's two bounds) and none of its place, and writes nothing. Each slice
/// of the role, in the store's order and alone, is cut afresh from stretch 1 with the key file's seed, so every slice meets the same draws,
/// for `SECTIONS` sections under the bounds (fewer where the slice ends), its regions training's own ([`state_of`]); each section's regions
/// are read on the realization by `read_faces`, as [`held_out`] reads, and a region's code is the sum of `face.code(class)` over its
/// unresolved places beside their count. One line a section (`STORE_READ`: the port's fields, then each kind's regions, places and code);
/// a closing line a slice (`STORE_READ_WRITER`) with two partitions of its writer's states: at `k = 0` the places and code by the octave of
/// an open place's distance from the context, and over every writer's state the code at its front place (the first open place of its
/// order, the place the release draws next) and the count, by that place's octave. Last, once, the code line's yardstick on `HELD`
/// (`STORE_YARDSTICK at=read`). A reading: the state's bytes are not touched.
pub(super) fn read(args: &[String], realization: &mut dyn FieldRealization) -> Result<()> {
    if args.len() != 15 {
        return Err("read-store UNITS UNITS_SHA STORE STORE_SHA ROLE KEYS KEYS_SHA CODEC CODEC_SHA HELD HELD_SHA SECTIONS STATE STATE_SHA".into());
    }
    let started = std::time::Instant::now();
    refuse_variables("read-store")?;
    let units = units_of(&args[1], &args[2])?;
    if !units.merges().is_empty() {
        return Err("the store's cut is on bytes: a units file of merges is refused".into());
    }
    let store = Path::new(&args[3]);
    let counts = store_counts(std::str::from_utf8(&pinned_read(&store.join("STORE.tsv").to_string_lossy(), &args[4], READ_BUDGET as usize)?)?)?;
    let role = args[5].as_str();
    let keys = pinned_read(&args[6], &args[7], READ_BUDGET as usize)?;
    let seed = u64::from_be_bytes(keys.get(keys.len().saturating_sub(8)..).filter(|w| w.len() == 8).ok_or("a key file of fewer than eight bytes")?.try_into()?);
    let codec = FieldCodec::from_text(&String::from_utf8(pinned_read(&args[8], &args[9], READ_BUDGET as usize)?)?, units)?;
    let held_bytes = pinned_read(&args[10], &args[11], READ_BUDGET as usize)?;
    let sections = positive(&args[12])?;
    let learner = FieldLearner::from_text(std::str::from_utf8(&pinned_read(&args[13], &args[14], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let law = learner.pass.clone().ok_or("a state with no pass line: read-store reads a state of the store's line")?;
    if learner.field.declaration.alphabet != codec.alphabet() {
        return Err("a state whose alphabet is not its codec's".into());
    }
    let names = role_names(&counts, role);
    if names.is_empty() {
        return Err(format!("a store with no slice of the role {role}").into());
    }
    println!("STORE_READ_LAW role={role} least={} octaves={} pairs_bound={} sites_bound={} sections={sections} alphabet={} void={} ms={}", law.least, law.octaves, law.pairs, law.sites, codec.alphabet(), codec.void(), started.elapsed().as_millis());
    for &name in &names {
        let slice = open_slice(store, role, name, &counts)?;
        let pass = StorePass { role: role.to_string(), store: args[4].clone(), stretches: 0, least: law.least, octaves: law.octaves, pairs: law.pairs, sites: law.sites, slices: vec![PassSlice { name: name.to_string(), piece: 0, cursor: 0, taken: 0 }] };
        let mut cut = Cut { seed, slices: vec![slice], pass };
        let (mut k0, mut front) = (vec![(0u64, 0i64); READ_OCTAVES], vec![(0u64, 0i64); READ_OCTAVES]);
        // [measurement; theory, the counts of counts of surprise (CLAUDE.md's structural measures; Brandon's lens of November 12, 20:31Z, on
        // information the line already predicts)] Every compared place's code by its octave: the bit length of its code on the codes' grain.
        let mut surprise = vec![(0u64, 0i64); SURPRISE_OCTAVES];
        // [measurement; theory, November 12, P53 item 4; the store record's §11, first item] The partition the held read owes: a release's compared
        // places by their distance to the nearest known place of the region (1, 2, 3, 4 to 7, 8 to 15, 16 and more, or none) and by the region's count of
        // known places (0, 1 to 15, 16 to 63, 64 and more), a mask's by how many of its two neighbours are known (0, 1, 2); a count and a code sum each.
        let (mut by_distance, mut by_known, mut by_neighbours) = ([(0u64, 0i64); 7], [(0u64, 0i64); 4], [(0u64, 0i64); 3]);
        let mut read_sections = 0usize;
        for n in 0..sections {
            let section_start = std::time::Instant::now();
            let mut stretches: Vec<Stretch> = Vec::new();
            let (mut tally, mut in_pairs, mut in_sites) = (Tally::default(), 0u64, 0u64);
            while let Some(drawn) = cut.next() {
                let s = drawn.sites();
                if in_sites > 0 && (in_pairs + s * s > cut.pass.pairs || in_sites + s > cut.pass.sites) {
                    break;
                }
                let stretch = cut.take(drawn, &codec)?;
                tally.take(&stretch.region, stretch.counted);
                (in_pairs, in_sites) = (in_pairs + s * s, in_sites + s);
                stretches.push(stretch);
            }
            if stretches.is_empty() {
                break;
            }
            let regions: Vec<TrainRegion> = stretches.iter().map(|s| s.region.clone()).collect();
            let faces = realization.read_faces(&learner.field, &views_of(&regions)).map_err(|e| e.to_string())?;
            let mut by_kind = [(0u64, 0u64, 0i64); 4];
            for (stretch, faces) in stretches.iter().zip(&faces) {
                let (code, places) = region_code(faces, &stretch.region)?;
                for (t, _) in stretch.region.unresolved.iter().enumerate().filter(|&(_, &u)| u) {
                    let c = faces[t].as_ref().ok_or("an unresolved place without a face")?.code(stretch.region.classes[t]);
                    let b = ((i64::BITS - c.max(0).leading_zeros()) as usize).min(SURPRISE_OCTAVES - 1);
                    (surprise[b].0, surprise[b].1) = (surprise[b].0 + 1, surprise[b].1 + c);
                }
                let k = read_kind(stretch);
                by_kind[k] = (by_kind[k].0 + 1, by_kind[k].1 + places as u64, by_kind[k].2 + code);
                {
                    let u = &stretch.region.unresolved;
                    let n = u.len();
                    let known = u.iter().filter(|&&open| !open).count();
                    if stretch.writer.is_some() {
                        // The nearest known place on each side, in one pass each way.
                        let (mut before, mut after) = (vec![usize::MAX; n], vec![usize::MAX; n]);
                        let mut last = usize::MAX;
                        for t in 0..n {
                            if !u[t] {
                                last = t;
                            }
                            before[t] = if last == usize::MAX { usize::MAX } else { t - last };
                        }
                        last = usize::MAX;
                        for t in (0..n).rev() {
                            if !u[t] {
                                last = t;
                            }
                            after[t] = if last == usize::MAX { usize::MAX } else { last - t };
                        }
                        let kb = match known {
                            0 => 0,
                            1..=15 => 1,
                            16..=63 => 2,
                            _ => 3,
                        };
                        for t in (0..n).filter(|&t| u[t]) {
                            let c = faces[t].as_ref().ok_or("an unresolved place without a face")?.code(stretch.region.classes[t]);
                            let db = match before[t].min(after[t]) {
                                1 => 0,
                                2 => 1,
                                3 => 2,
                                4..=7 => 3,
                                8..=15 => 4,
                                usize::MAX => 6,
                                _ => 5,
                            };
                            (by_distance[db].0, by_distance[db].1) = (by_distance[db].0 + 1, by_distance[db].1 + c);
                            (by_known[kb].0, by_known[kb].1) = (by_known[kb].0 + 1, by_known[kb].1 + c);
                        }
                    } else {
                        for t in (0..n).filter(|&t| u[t]) {
                            let c = faces[t].as_ref().ok_or("an unresolved place without a face")?.code(stretch.region.classes[t]);
                            let nb = usize::from(t > 0 && !u[t - 1]) + usize::from(t + 1 < n && !u[t + 1]);
                            (by_neighbours[nb].0, by_neighbours[nb].1) = (by_neighbours[nb].0 + 1, by_neighbours[nb].1 + c);
                        }
                    }
                }
                if let Some((k, at)) = stretch.writer {
                    let q = stretch.q;
                    if k == 0 {
                        for (t, &open) in stretch.region.unresolved.iter().enumerate().filter(|&(_, &u)| u) {
                            let _ = open;
                            let o = (octave_of(t + 1 - q) as usize).min(READ_OCTAVES - 1);
                            let face = faces[t].as_ref().ok_or("an unresolved place without a face")?;
                            (k0[o].0, k0[o].1) = (k0[o].0 + 1, k0[o].1 + face.code(stretch.region.classes[t]));
                        }
                    }
                    let o = (octave_of(at + 1 - q) as usize).min(READ_OCTAVES - 1);
                    let face = faces[at].as_ref().ok_or("a writer's front without a face")?;
                    (front[o].0, front[o].1) = (front[o].0 + 1, front[o].1 + face.code(stretch.region.classes[at]));
                }
            }
            let kinds: Vec<String> = READ_KINDS.iter().zip(&by_kind).map(|(name, (r, p, c))| format!("{name}_regions={r} {name}_places={p} {name}_code={c}")).collect();
            println!("STORE_READ slice={name} n={n} {} stretches={} {} ms={}", tally.text(), cut.pass.stretches, kinds.join(" "), section_start.elapsed().as_millis());
            read_sections += 1;
        }
        let shown = if k0[READ_OCTAVES - 1].0 + front[READ_OCTAVES - 1].0 > 0 { READ_OCTAVES } else { READ_OCTAVES - 1 };
        let list = |v: &[(u64, i64)], what: &str| (0..shown).map(|o| format!("{what}{o}={}/{}", v[o].0, v[o].1)).collect::<Vec<_>>().join(" ");
        println!("STORE_READ_SURPRISE slice={name} places={} by_bit_length(count/code) {} ms={}", surprise.iter().map(|v| v.0).sum::<u64>(), (0..SURPRISE_OCTAVES).filter(|&b| surprise[b].0 > 0).map(|b| format!("b{b}={}/{}", surprise[b].0, surprise[b].1)).collect::<Vec<_>>().join(" "), started.elapsed().as_millis());
        println!("STORE_READ_WRITER slice={name} sections={read_sections} stretches={} k0_by_octave(places/code) {} front_by_octave(count/code) {} ms={}", cut.pass.stretches, list(&k0, "o"), list(&front, "o"), started.elapsed().as_millis());
        let cells = |v: &[(u64, i64)], names: &[&str]| v.iter().zip(names).map(|((c, s), n)| format!("{n}={c}/{s}")).collect::<Vec<_>>().join(" ");
        println!(
            "STORE_READ_PARTITION slice={name} release_by_distance(count/code) {} release_by_known(count/code) {} mask_by_neighbours(count/code) {}",
            cells(&by_distance, &["d1", "d2", "d3", "d4_7", "d8_15", "d16_", "none"]),
            cells(&by_known, &["k0", "k1_15", "k16_63", "k64_"]),
            cells(&by_neighbours, &["n0", "n1", "n2"])
        );
    }
    let held = held_out(&learner.field, &codec, &held_set(&codec, &held_bytes)?, realization)?;
    println!("STORE_YARDSTICK at=read {} ms={}", held_text(&held), started.elapsed().as_millis());
    println!("STORE_READ_DONE {} ms={}", counters_text(realization), started.elapsed().as_millis());
    Ok(())
}

/// [measurement; theory, November 12, P49 item 4] `write-store UNITS UNITS_SHA STORE STORE_SHA KEYS KEYS_SHA CODEC CODEC_SHA DOCUMENTS PROMPT RUN
/// OUT STATE STATE_SHA`: **the release from held prompts**. On the store's held role, for each slice in the store's order, its first
/// `DOCUMENTS` pieces that open their document and hold at least `PROMPT + RUN` places; a problem is the piece's first `PROMPT` places and
/// `RUN` open places. The release is the tower's as it stands, its law fixed here: [`holonics::hnn::tower::field::Field::sample_runs`] over
/// every problem at once with `sweeps = RUN` (one place a read), `refine = 0`, the codec's void, the key file's seed, `run_bound = 0`, the
/// near tail, the keyed order within an octave, no given lengths, no one-end draw, a sweep that always goes on and no observer: the store's
/// writer state run from `k = 0` upward, by octaves of distance from the prompt. `OUT` is created new; each problem writes three files of
/// raw bytes (`SLICE_NN.prompt`, `SLICE_NN.written`, the codec's decode up to the first void, and `SLICE_NN.reference`, the piece's next
/// `RUN` places), and one line (`STORE_WRITE`: its slice, its document, the places written before a void and the release's reads); a closing
/// line holds the card's counters and the time. A reading: the state is not touched.
pub(super) fn write(args: &[String], realization: &mut dyn FieldRealization) -> Result<()> {
    if args.len() != 15 {
        return Err("write-store UNITS UNITS_SHA STORE STORE_SHA KEYS KEYS_SHA CODEC CODEC_SHA DOCUMENTS PROMPT RUN OUT STATE STATE_SHA".into());
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
    println!("STORE_WRITE_LAW problems={} documents={documents} prompt={prompt} run={run} sweeps={run} refine=0 run_bound=0 near_tail=true place_order=false lengths=none one_end=false alphabet={} void={} ms={}", problems.len(), codec.alphabet(), codec.void(), started.elapsed().as_millis());
    let release: Vec<(&[usize], usize)> = problems.iter().map(|p| (p.2.as_slice(), run)).collect();
    // The release's reads, from the realization's own count (the sweep is not asked on the release's last read, so its calls fall one short).
    let reads_before = realization.counters().map(|c| c.reads);
    let mut asked = 0usize;
    let written = learner
        .field
        .sample_runs(&release, run, 0, codec.void(), seed, 0, true, false, None, false, realization, &mut |_, _| {
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

    /// [measurement; theory, November 12, P49 item 3g] **A region's code from the read's sum is the field's code**: on a small store written to a
    /// scratch directory (pieces that open with a title and close, and one that opens with none), the cut's stretches read through the host
    /// realization give, region by region, the same code and count from [`region_code`] as [`holonics::hnn::tower::field::Field::code`] reads
    /// for the same plain region, and both kinds of state are met.
    #[test]
    fn a_regions_code_from_the_reads_sum_is_the_fields_code() {
        use holonics::hnn::tower::field::{Field, FieldDeclaration, HostField};
        use holonics::hnn::units::Units;
        let dir = std::env::temp_dir().join(format!("store_read_test_{}_{}", std::process::id(), line!()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let docs: Vec<(Vec<u8>, Vec<u8>)> = (0..12u8)
            .map(|k| (if k % 4 == 3 { Vec::new() } else { format!("Title {k}").into_bytes() }, (0..40 + 7 * k as usize).map(|t| b"abcdefghij klmnop,."[(t * 7 + k as usize) % 19]).collect()))
            .collect();
        let (mut bin, mut tsv) = (Vec::new(), String::from(INDEX_HEAD) + "\n");
        for (k, (title, text)) in docs.iter().enumerate() {
            bin.extend_from_slice(title);
            bin.extend_from_slice(text);
            tsv.push_str(&format!("{k}\t{}\t{}\t1\t1\n", title.len(), text.len()));
        }
        std::fs::write(dir.join("DOCS_code.bin"), &bin).unwrap();
        std::fs::write(dir.join("DOCS_code.tsv"), &tsv).unwrap();
        let counts: HashMap<(String, String), (u64, u128)> = [(("prefix".to_string(), "code".to_string()), (docs.len() as u64, bin.len() as u128))].into_iter().collect();
        let slice = open_slice(&dir, "prefix", "code", &counts).unwrap();
        let every: Vec<u8> = docs.iter().flat_map(|(a, b)| a.iter().chain(b).copied()).collect();
        let codec = FieldCodec::found(Units::bytes(), &[(b"q".to_vec(), every)]).unwrap();
        let d = FieldDeclaration { alphabet: codec.alphabet(), width: 8, heads: 2, modes: 3, still: 1, contacts: 4, ticks: 2, frames: 2, reach: 160, lanes: 1, depth: 0, carry: 0, triads: 0 };
        let keys: Vec<u8> = (0..1u64 << 14).flat_map(|i| (i.wrapping_add(1).wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ (i << 17)).to_be_bytes()).collect();
        let field = Field::found(d, &keys).unwrap();
        let pass = StorePass { role: "prefix".into(), store: "ab".repeat(32), stretches: 0, least: LEAST, octaves: OCTAVES, pairs: PAIRS_BOUND, sites: SITES_BOUND, slices: vec![PassSlice { name: "code".into(), piece: 0, cursor: 0, taken: 0 }] };
        let mut cut = Cut { seed: 0x5EED, slices: vec![slice], pass };
        let mut stretches = Vec::new();
        while let Some(drawn) = cut.next() {
            stretches.push(cut.take(drawn, &codec).unwrap());
        }
        assert!(stretches.len() >= 12, "{}", stretches.len());
        assert!(stretches.iter().any(|s| s.writer.is_some()) && stretches.iter().any(|s| s.writer.is_none()), "both kinds of state");
        let regions: Vec<TrainRegion> = stretches.iter().map(|s| s.region.clone()).collect();
        let views = views_of(&regions);
        let faces = HostField.read_faces(&field, &views).unwrap();
        for ((region, view), faces) in regions.iter().zip(&views).zip(&faces) {
            let (code, places) = region_code(faces, region).unwrap();
            assert_eq!((code, places), field.code(view).unwrap());
        }
        let _ = std::fs::remove_dir_all(&dir);
    }
}
