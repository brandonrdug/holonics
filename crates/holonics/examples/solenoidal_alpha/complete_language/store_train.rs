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
    let mut reads = 0usize;
    let written = learner
        .field
        .sample_runs(&release, run, 0, codec.void(), seed, 0, true, false, None, false, realization, &mut |_, _| {
            reads += 1;
            true
        }, &mut |_| {})
        .map_err(|e| e.to_string())?;
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
