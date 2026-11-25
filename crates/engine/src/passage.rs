//! **The passage's cut and a pass's place.**
//!
//! stretch `d` of a pass draws its context `q = least·2^(o_q) + u_q` and its run `a = least·2^(o_a) + u_a`, each `o` keyed on the pass's
//! octaves and each `u` within its octave (`mix(seed, d | …)`), and takes the rest of its piece where `rest < q + a + least`; its one
//! keyed state is a mask (density `τ = u²`, `u` on `2^(−16)`, weighed back by its domain `⌊2√(mK)⌋`), the writer's (the run's first `k`
//! places resolved, by octaves of their distance from the context) or, at the frontier, every place known but the last (weight `m` over
//! one); its own state resolves `k = 2^o − 1`, `o = d mod (⌊log₂ a⌋ + 1)`; the cut takes the slice with least `taken_s/quota_s` (weighed by each slice's tension where the pass holds it; the
//! earlier at a tie), its pieces in order from a cursor
//!
//! Kind: chain over a pass's stretches, its place carried in the learner's state (`StorePass`); gate, a site, inside a stretch. Kernels:
//! none; the cut is drawn on the host before any forward. A slice reads its bytes through [`PieceBytes`], and the store's file is the
//! commands' source (`athena::store`).
//! Lean: none yet.
//! Atlas: `passage.cut-reads-each-stretch-once`, `tower.field-own-states`, `tower.field-states-name-their-receivers`,
//! `tower.store-frontier-state`, `tower.store-stretch-cut`; with owners in other modules, `tower.field-growth-by-copies`.
//! Records: `2026-11-12_A_LAPS_CARD_TIME_STANDS…` (§4: the cut, the keyed state), `2026-11-15_THE_STATES_A_FIELD_TRAINS_ON…`,
//! `2026-11-18_THE_WRITERS_FRONTIER_IS…`, `2026-11-18_THE_CODEC_THE_REGION…` (the first lines this header replaced). The derivations'
//! history is in the records; the items below keep their reasons.

use crate::codec::{question_text, Codec, RECORD, UNIT};
use crate::field::{octave_of, Constitution, Realization, Region, StorePass, NEAR, SHARE_BITS};
use crate::region::{region_classes, OwnedRegion};

type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;

/// The encoded problems: each question's classes, its answer's and the answer's bytes.
pub type Problems = Vec<(Vec<usize>, Vec<usize>, usize)>;

/// [definition; agent-inferred, November 3, §16.27] **A region's shape**: a keyed completion mask over the whole region
/// (`Masked`), or over the answer and its void tail with the question known (`Answer`), the state the writer meets
/// ([`Constitution::sample_realized`]: the question known, a uniform state of a random reading order of the answer's places).
pub enum Shape {
    Masked(Vec<bool>),
    Answer(Vec<bool>),
}

/// The problems of a passage: `question \n answer` blocks separated by a blank line; or, where the passage carries the
/// record separator, records `question US answer` separated by it, each part's bytes exact. [agent-inferred, November 5]
/// Why the records: the code passage (Brandon, November 5: python-codes-25k in place of GSM8K) has answers that hold
/// blank lines and questions of several lines, which the blank-line blocks would cut; neither separator stands in it.
pub fn problems_of(text: &[u8]) -> Vec<(Vec<u8>, Vec<u8>)> {
    if text.contains(&RECORD) {
        return text
            .split(|&b| b == RECORD)
            .filter_map(|record| {
                let cut = record.iter().position(|&b| b == UNIT)?;
                let (q, a) = (&record[..cut], &record[cut + 1..]);
                (!q.is_empty() && !a.is_empty()).then(|| (q.to_vec(), a.to_vec()))
            })
            .collect();
    }
    let mut out = Vec::new();
    for block in text.split(|&b| b == b'\n').collect::<Vec<_>>().split(|line| line.is_empty()) {
        if block.len() < 2 {
            continue;
        }
        let q = block[0].to_vec();
        let a = block[1..].join(&b'\n');
        out.push((q, a));
    }
    out
}

/// The exterior mask stream: an integer mixer of the key file's first word and a counter.
pub fn mix(seed: u64, counter: u64) -> u64 {
    let mut z = seed.wrapping_add(counter.wrapping_mul(0x9E37_79B9_7F4A_7C15));
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

/// [definition; agent-inferred, November 3, §16.27; §16.32] **A region's shape**, drawn: `τ = u²`, `u` uniform on `(0, 1]` on
/// `2^(−16)`, and each site open where its keyed draw falls below `τ`; with even odds over the whole region (the question's and the
/// answer's language alike) or over the answer's sites and its void tail alone, the question known, so the field meets
/// the writer's every state (`K` of the answer's places open, uniform given `K`); at least one site open in the domain.
///
/// Why the front regions are retired (the field's code read end to end, November 3): they were the states of the release
/// that locked a place where one class held a majority and moved its front only past locked places; that writer could
/// not write text, whose places are uncertain even under a perfect model, so it committed the bytes it was surest of
/// (runs of `0`, `<<`, `=`, `####`) and left the rest open. The writer now draws every place from its own face in the
/// training clock run backwards, whose states are these masks; the fronts' two reads (read 2 carrying faces at a pump
/// rung) and their ports took half of every lap for states no writer meets.
pub fn shape(seed: u64, draw: u64, question: usize, sites: usize) -> Shape {
    let head = mix(seed, draw);
    let u = ((head >> 1) & 0xFFFF) + 1;
    // [definition; agent-inferred, November 3, §16.32] The density is drawn at `τ = u²`, so the states where most of a site's
    // neighbours are known come more often; each region is weighed back by its importance ratio ([`weighed_domain`]).
    let tau = ((u * u) >> 16).max(1);
    let whole = head & 1 == 1;
    let from = if whole { 0 } else { question };
    let mut out: Vec<bool> = (0..sites).map(|t| t >= from && (mix(seed, draw ^ ((t as u64 + 1) << 32)) & 0xFFFF) < tau).collect();
    if !out.iter().any(|&u| u) {
        out[from + mix(seed, draw.wrapping_add(1)) as usize % (sites - from)] = true;
    }
    if whole {
        Shape::Masked(out)
    } else {
        Shape::Answer(out)
    }
}

/// [definition; agent-inferred, November 3, §16.32] **A state's domain weighed back to the joint code**: a region whose `K`
/// open sites among `m` were drawn at `τ = u²` (density `q(τ) = 1/(2√τ)`) against the joint code's uniform `τ`, so its
/// importance ratio `p/q = 2√τ`, read at `τ ≈ K/m`, multiplies its weight `m/K` ([`Region::weight`]): the domain is read as
/// `⌊2√(mK)⌋`, its weight `2√(m/K)`. The estimate of the order-averaged joint code stays unbiased (to `τ`'s reading
/// through `K`), and its variance is spent where a site's neighbours are known.
pub fn weighed_domain(m: usize, mask: &[bool]) -> usize {
    let k = mask.iter().filter(|&&u| u).count().max(1) as u128;
    (4 * m as u128 * k).isqrt() as usize
}

/// The held-out read: at the release's own opening (the region the question and the codec's
/// answer extent, every answer site unresolved at once), with each site's neighbours resolved
/// ([`context_regions`], the region the question, the answer and its first void), and the same
/// beside another problem's question (the foil, [`held_regions`]), the field's code over the
/// answer's classes and its first void, on `2^(−20)` bits, beside each one's count: `[opening,
/// context, foil]`. A reading of completion only (§16.23): no decision of the run reads it.
/// [retired, November 2, §16.19] The split of each into its digits and its text: a class sorted by
/// the codec's own byte kind was the numeral matcher's partition, read beside the field's own.
pub fn held_out(field: &Constitution, codec: &Codec, problems: &Problems, realization: &mut dyn Realization) -> Result<[(i64, usize); 3]> {
    let regions = held_regions(codec, problems);
    let views: Vec<Region> = regions.iter().map(|(c, u, _)| Region { classes: c, unresolved: u, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None }).collect();
    let mut out = [(0i64, 0usize); 3];
    let mut opening = 0usize;
    for (chunk, parts) in views.chunks(64).zip(regions.chunks(64)) {
        let faces = realization.read_faces(field, chunk).map_err(|e| e.to_string())?;
        for ((region, faces), &(_, _, base)) in chunk.iter().zip(faces).zip(parts) {
            if base == 0 {
                // [agent-inferred, November 3, §16.27] The opening is read at its places, as the writer meets it: the answer's
                // cells and its first void, each at its own place, every answer place open.
                let (q, a, _) = &problems[opening];
                opening += 1;
                for (t, face) in faces.iter().enumerate().skip(q.len()).take(a.len() + 1) {
                    let face = face.as_ref().ok_or("an opening place without a face")?;
                    out[0].0 += face.code(region.classes[t]);
                }
                out[0].1 += a.len() + 1;
                continue;
            }
            for (face, &class) in faces.iter().zip(region.classes) {
                if let Some(face) = face {
                    let code = face.code(class);
                    out[base].0 += code;
                    out[base].1 += 1;
                }
            }
        }
    }
    Ok(out)
}

/// The held-out read's regions ([`held_out`]): each problem's opening (base 0), its [`CONTEXT`]
/// parts read with their neighbours (base 1), and the same parts beside the next problem's
/// question (base 2; the last problem beside the first's).
///
/// [agent-inferred, November 1] Why the foil: the sixth reading's answers beside their neighbours
/// coded their digits below the bytes' own table (2.776 bits against 3.46), while the release
/// wrote the commonest numbers and the answers read from the question alone did not fall (5.16 to
/// 5.70). A neighbour inside the answer carries much of a digit (the result after `>>` repeats
/// the one before it), so the context read cannot say whether the question is read at all. The
/// same answer read beside another problem's question codes no more bits than beside its own
/// unless the field reads its own question: the difference, foil minus context, is what the
/// question tells the answer beyond its neighbours.
pub fn held_regions(codec: &Codec, problems: &Problems) -> Vec<(Vec<usize>, Vec<bool>, usize)> {
    let mut regions: Vec<(Vec<usize>, Vec<bool>, usize)> = problems
        .iter()
        .map(|(q, a, _)| {
            let classes = region_classes(codec, q, a, q.len() + codec.answer);
            let open = (0..classes.len()).map(|t| t >= q.len()).collect();
            (classes, open, 0)
        })
        .collect();
    regions.extend(problems.iter().flat_map(|(q, a, _)| context_regions(codec.void(), q, a, q.len() + a.len() + 1).into_iter().map(|(c, u)| (c, u, 1))));
    let n = problems.len();
    regions.extend((0..n).flat_map(|i| {
        let ((_, a, _), (q, _, _)) = (&problems[i], &problems[(i + 1) % n]);
        context_regions(codec.void(), q, a, q.len() + a.len() + 1).into_iter().map(|(c, u)| (c, u, 2))
    }));
    regions
}

/// [agent-inferred, November 1] **An answer read with its neighbours**: one problem's region (its
/// question, answer and `length − |q| − |a|` voids) read in [`CONTEXT`] parts, the answer's sites
/// and its first void at `t ≡ r (mod CONTEXT)` (counted from the answer's first site) unresolved in
/// part `r` and every other site resolved, so each is read once with the three sites before it and
/// after it resolved. Why (the third reading, November 1): the opening read, every answer site
/// unresolved at once, reads what the question and the place tell a site, whose floor sits near
/// the bytes' own table (the held answers coded at 5.34 bits a byte after a lap; the training
/// answers' byte table codes them at 5.05), so it could not show what the field learned from an
/// answer's own bytes (four bytes before a site code it at 1.98 bits on the same terms), which is
/// what a release that commits only what the field resolves runs on.
pub fn context_regions(void: usize, q: &[usize], a: &[usize], length: usize) -> Vec<(Vec<usize>, Vec<bool>)> {
    let mut classes: Vec<usize> = q.iter().chain(a).copied().collect();
    classes.resize(length, void);
    let end = q.len() + a.len() + 1;
    (0..CONTEXT).map(|r| (classes.clone(), (0..length).map(|t| t >= q.len() && t < end && (t - q.len()) % CONTEXT == r).collect())).collect()
}

/// The parts of [`context_regions`]: a site read with the `CONTEXT − 1` sites on each side of it
/// resolved (agent-inferred: the reach the bytes' own table needs to code a site at its
/// four-byte-context rate, from either side).
pub const CONTEXT: usize = 4;

/// A piece of a slice's index: its offset in the slice's file, its title's and its text's octets, and whether it opens and closes its document.
#[derive(Clone, Copy, Debug)]
pub struct Piece {
    pub document: u64,
    pub offset: u64,
    pub title: u64,
    pub text: u64,
    pub opens: bool,
    pub closes: bool,
}

impl Piece {
    /// Whether a line feed stands between the title and the text (a piece that opens with a title; the store keeps no separator).
    pub fn line_feed(&self) -> bool {
        self.opens && self.title > 0
    }

    /// The piece's places: its title's bytes, one line feed where it opens with a title, and its text's bytes.
    pub fn places(&self) -> u64 {
        self.title + u64::from(self.line_feed()) + self.text
    }
}

/// [realization; November 14, C4 of #603] **Where a slice's bytes come from**: `out.len()` bytes from `at`. The cut reads its slices
/// through it, so the passage's law (pieces, places, draws, stretches) holds no file: the store's file is one source (`SliceFile` in `athena::store`).
pub trait PieceBytes {
    fn read_at(&mut self, at: u64, out: &mut [u8]) -> Result<()>;
}

/// A slice of the role read: its name, its quota (the role's store octets), its pieces in order and its source of bytes.
pub struct Slice {
    pub name: String,
    pub quota: u128,
    pub pieces: Vec<Piece>,
    pub source: Box<dyn PieceBytes>,
}

impl Slice {
    /// The places `[from, from + len)` of piece `k`, read from the slice's source at the piece's offset (never the slice in memory).
    pub fn bytes(&mut self, k: usize, from: u64, len: u64) -> Result<Vec<u8>> {
        let p = self.pieces[k];
        let end = from + len;
        if end > p.places() {
            return Err("a stretch past its piece's places".into());
        }
        let mut out = Vec::with_capacity(len as usize);
        let read = |source: &mut Box<dyn PieceBytes>, at: u64, n: u64, out: &mut Vec<u8>| -> Result<()> {
            if n == 0 {
                return Ok(());
            }
            let start = out.len();
            out.resize(start + n as usize, 0);
            source.read_at(at, &mut out[start..])
        };
        if !p.line_feed() {
            read(&mut self.source, p.offset + from, len, &mut out)?;
            return Ok(out);
        }
        // The title's places, the line feed at place `title`, then the text's places one past their bytes.
        let t = p.title;
        if from < t {
            read(&mut self.source, p.offset + from, end.min(t) - from, &mut out)?;
        }
        if from <= t && t < end {
            out.push(b'\n');
        }
        let text_from = from.max(t + 1);
        if text_from < end {
            read(&mut self.source, p.offset + text_from - 1, end - text_from, &mut out)?;
        }
        Ok(out)
    }
}

/// A stretch drawn at the pass's place and not yet taken: its slice, its draw, its context and run, whether a true end follows it, and whether
/// it finishes its piece.
#[derive(Clone, Copy, Debug)]
pub struct Drawn {
    pub slice: usize,
    pub d: u64,
    pub q: u64,
    pub a: u64,
    pub ends: bool,
    pub done: bool,
    /// Read at the frontier ([`frontier_cut_of`]): its context and the one place after it, a true end's first void where one follows.
    pub frontier: bool,
}

impl Drawn {
    /// The stretch's sites: its context, its run and the near tail where a true end follows; at the frontier, its context and one place.
    pub fn sites(&self) -> u64 {
        if self.frontier {
            return self.q + 1;
        }
        self.q + self.a + if self.ends { NEAR as u64 } else { 0 }
    }
}

/// [definition; the record §4 item 1; the port's `lengths_of`] A stretch's two draws, the `d`th of the pass.
pub fn lengths_of(seed: u64, d: u64, least: u64, octaves: u64) -> (u64, u64) {
    let oq = mix(seed, d | 1 << 60) % octaves;
    let q = (least << oq) + mix(seed, d | 3 << 60) % (least << oq);
    let oa = mix(seed, d | 1 << 62) % octaves;
    let a = (least << oa) + mix(seed, d | 5 << 60) % (least << oa);
    (q, a)
}

/// [definition; the record §4 item 1; the port's `cut_of`] The stretch at a cursor with `rest` places left: its context and run, whether a
/// true end follows (the piece closes its document), and whether the piece is done. Where the next `q + a` places would leave at least the
/// least context, the stretch is those places and the piece goes on; else it takes the rest, its context `min(q, rest − 1)`.
pub fn cut_of(seed: u64, d: u64, rest: u64, closes: bool, least: u64, octaves: u64) -> (u64, u64, bool, bool) {
    let (q, a) = lengths_of(seed, d, least, octaves);
    if rest >= q + a + least {
        return (q, a, false, false);
    }
    let q = q.min(rest - 1);
    (q, rest - q, closes, true)
}

/// [definition; agent-inferred, the lead, November 18, the audit of that day §1.4] **The frontier's cut**: the stretch at a cursor with
/// `rest` places left, read at the frontier. Its context is the stretch's own draw of one ([`lengths_of`], so a context's length keeps the
/// pass's octaves and no scale of it is privileged), and its run is the one place after it: `(q, 1)` where the piece goes on past it by
/// the least context or more. Else it takes the rest of the piece: where the piece closes its document, every place left is known and the
/// one open place is the true end's first void (`(rest, 0)`, an end follows), so the field is compared on where a document stops as a
/// writer must place it; where the piece does not close, the last place left is the open one (`(rest − 1, 1)`). Returns the context, the
/// places of the run that are the passage's (one or none), whether a true end follows, and whether the piece is done.
pub fn frontier_cut_of(seed: u64, d: u64, rest: u64, closes: bool, least: u64, octaves: u64) -> (u64, u64, bool, bool) {
    let (q, _) = lengths_of(seed, d, least, octaves);
    if rest > q + least {
        return (q, 1, false, false);
    }
    if closes {
        (rest, 0, true, true)
    } else {
        (rest - 1, 1, false, true)
    }
}

/// Whether the pass's `d`th stretch is read at the frontier: a keyed draw of eight against the pass's share ([`StorePass::frontier`]).
pub fn frontier_here(seed: u64, d: u64, share: u64) -> bool {
    share > 0 && mix(seed, d | 9 << 60) % 8 < share
}

/// [definition; agent-inferred, the lead, November 18, the audit of that day §1.4] **A stretch's frontier state**: every place known but
/// the last, which alone is open, and the region ends there (`classes` is the context and the open place; a true end's void is given as
/// `void` and stands as the open place). It is the state a writer in place order meets at each place it writes: everything before the
/// place bound, nothing after it. One place is compared for the region's `m` sites, so its weight in the code is `m` over one
/// ([`crate::field::Region::weight`]): its domain is the region, which keeps a section's comparison weight following the sites it reads
/// across its kinds of state. Why a region that ends at its open place and not a run left open behind it: an open place is no source
/// to the contact (`field.rs`'s first lines, §16.20), so a tail of open places would cost their sites and bring the compared place
/// nothing the contact gathers; and it is the state the night's text run of November 17 compared and wrote from.
pub fn frontier_state_of(mut classes: Vec<usize>, void: Option<usize>) -> Stretch {
    if let Some(v) = void {
        classes.push(v);
    }
    let n = classes.len();
    let unresolved: Vec<bool> = (0..n).map(|t| t + 1 == n).collect();
    Stretch { region: OwnedRegion { domain: Some(n), ..OwnedRegion::plain(classes, unresolved) }, kind: Kind::Frontier, counted: n, q: n - 1 }
}

/// The kind of a stretch's one keyed state, as the port names it; `Frontier` is the lead's of November 18 ([`frontier_state_of`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    MaskWhole,
    MaskRun,
    Writer,
    Frontier,
}

/// [definition; the record §4 item 2; the port's `state_of`] **A stretch's one keyed state**, from `head = mix(seed, d)`: bit 17 set, the
/// writer's state (the context known, the run's places in the writer's octave order of their distance from the context, keyed within an
/// octave, its first `k` resolved, `k` by octaves of reads, `k = 0` among them, and a true end's voids given); clear, a mask state (`shape`'s
/// law over the whole stretch or past the context, the density `τ = u²`, weighed back by its domain `⌊2√(mK)⌋`). Regions are plain: no port.
/// Returns the region, its kind, the sites its code is a code of (its weighed domain, or its open places for the writer's state) and its
/// context.
pub fn state_of(seed: u64, d: u64, classes: Vec<usize>, q: usize, a: usize) -> Stretch {
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
        return Stretch { region: OwnedRegion::plain(classes, unresolved), kind: Kind::Writer, counted: a - k, q };
    }
    let (mask, kind, from) = match shape(seed, d, q, n) {
        Shape::Masked(mask) => (mask, Kind::MaskWhole, 0),
        Shape::Answer(mask) => (mask, Kind::MaskRun, q),
    };
    let domain = weighed_domain(n - from, &mask);
    Stretch { region: OwnedRegion { domain: Some(domain), ..OwnedRegion::plain(classes, mask) }, kind, counted: domain, q }
}

/// [definition; agent-inferred, November 15, the record of the states a field trains on, §3 and §5 item 2] **A stretch's own state**: the
/// release's own state at the `o`th crossing of its octaves, its context known, the run's places at distances `1` to `2^o − 1` from the
/// context resolved (its first `o` octaves whole, `k = 2^o − 1`), every farther place open, and a true end's voids given; weighed as one
/// link of the release's chain, its code a code of its open places (no importance weight). The crossing is the passage's own clock, the
/// stretch's count `d` in the pass modulo the run's crossings `⌊log₂ a⌋ + 1` (the `o` with `2^o ≤ a`): no key is drawn. Why these states:
/// the writer releases places by octaves of distance from its prompt ([`crate::field::Constitution::sample_runs`]), so at each crossing of an
/// octave every place nearer stands resolved and every farther place open, whatever order it keeps within an octave; these are the states
/// the field meets when it writes, read at octaves of `k`, so no scale of `k` is privileged. The record's step 2 ordered the run's places by
/// the field's news, one extra read a stretch; at a crossing the order within an octave does not reach the state, so no read is needed.
pub fn own_state_of(d: u64, classes: Vec<usize>, q: usize, a: usize) -> Stretch {
    let crossings = u64::from(octave_of(a)) + 1;
    let o = (d % crossings) as u32;
    let unresolved: Vec<bool> = (0..classes.len()).map(|t| t >= q && t < q + a && octave_of(t + 1 - q) >= o).collect();
    let k = (1usize << o) - 1;
    Stretch { region: OwnedRegion::plain(classes, unresolved), kind: Kind::Writer, counted: a - k, q }
}

/// A stretch's one state ([`state_of`], [`own_state_of`]): its region, its kind, the sites its code is a code of and its context.
pub struct Stretch {
    pub region: OwnedRegion,
    pub kind: Kind,
    pub counted: usize,
    pub q: usize,
}

/// [definition; the record §4 items 1 and 5; the port's `store`] **The cut over a role of the store**: the slices interleaved by least progress
/// against their quotas (the role's store octets; the earlier slice at a tie), each slice's pieces read in order from their cursors, the pass's
/// place carried in the learner's state ([`StorePass`]).
pub struct Cut {
    pub seed: u64,
    pub slices: Vec<Slice>,
    pub pass: StorePass,
}

impl Cut {
    /// The next stretch at the pass's place, drawn and not taken (none where every slice's pieces are read).
    /// [definition; the lead, November 24] Each slice's weight where the pass holds the slices by their tensions
    /// ([`StorePass::slice_tension`]): its tension, a slice with no reading at the mean of those with one, one each where none has.
    pub fn slice_weights(&self) -> Option<Vec<u128>> {
        let t = self.pass.slice_tension.as_ref()?;
        let read: Vec<u128> = t.iter().filter(|&&v| v > 0).map(|&v| u128::from(v)).collect();
        let mean = if read.is_empty() { 1 } else { (read.iter().sum::<u128>() / read.len() as u128).max(1) };
        Some(t.iter().map(|&v| if v > 0 { u128::from(v) } else { mean }).collect())
    }

    pub fn next(&self) -> Option<Drawn> {
        let live: Vec<usize> = (0..self.slices.len()).filter(|&s| (self.pass.slices[s].piece as usize) < self.slices[s].pieces.len()).collect();
        let mut slice = *live.first()?;
        // [definition; the lead, November 25] Where the pass holds its slices by their tensions, the slice whose own clock stands furthest
        // behind ([`StorePass::slice_clock`], every clock at zero where none is written); otherwise the quotas' interleave as before.
        if self.pass.slice_tension.is_some() {
            let clock = |s: usize| self.pass.slice_clock.as_ref().map_or(0, |c| c[s]);
            for &other in &live[1..] {
                if clock(other) < clock(slice) {
                    slice = other;
                }
            }
        } else {
            for &other in &live[1..] {
                let (t_o, t_n) = (self.pass.slices[other].taken as u128, self.pass.slices[slice].taken as u128);
                if t_o * self.slices[slice].quota < t_n * self.slices[other].quota {
                    slice = other;
                }
            }
        }
        let at = &self.pass.slices[slice];
        let piece = self.slices[slice].pieces[at.piece as usize];
        let d = self.pass.stretches + 1;
        let rest = piece.places() - at.cursor;
        let frontier = frontier_here(self.seed, d, self.pass.frontier);
        let (q, a, ends, done) = if frontier {
            frontier_cut_of(self.seed, d, rest, piece.closes, self.pass.least, self.pass.octaves)
        } else {
            cut_of(self.seed, d, rest, piece.closes, self.pass.least, self.pass.octaves)
        };
        Some(Drawn { slice, d, q, a, ends, done, frontier })
    }

    /// The drawn stretch taken: its region read from its slice's file, and the pass moved past it.
    pub fn take(&mut self, drawn: Drawn, codec: &Codec) -> Result<Stretch> {
        let at = self.pass.slices[drawn.slice].clone();
        let bytes = self.slices[drawn.slice].bytes(at.piece as usize, at.cursor, drawn.q + drawn.a)?;
        let mut classes = codec.encode(&bytes)?;
        if classes.len() != bytes.len() {
            return Err("a stretch whose bytes are not one class each".into());
        }
        if drawn.ends && !drawn.frontier {
            classes.resize(classes.len() + NEAR, codec.void());
        }
        let (q, a) = (drawn.q as usize, drawn.a as usize);
        let region = if drawn.frontier {
            // The pass's word: the stretch at the frontier is read as a known stream ([`StorePass::before`]).
            let mut state = frontier_state_of(classes, drawn.ends.then(|| codec.void()));
            (state.region.before, state.region.past, state.region.second) = (self.pass.before, self.pass.past, self.pass.second);
            if self.pass.strand {
                // The pass's word: the stretch is read by two streams ([`StorePass::strand`]): every site known, every place past the
                // first compared at weight one, so it declares no domain.
                state.region.unresolved.fill(false);
                (state.region.domain, state.region.strand) = (None, true);
                state.counted -= 1;
            }
            state
        } else if self.pass.own {
            own_state_of(drawn.d, classes, q, a)
        } else {
            state_of(self.seed, drawn.d, classes, q, a)
        };
        if let Some(weight) = self.slice_weights() {
            // [definition; the lead, November 25] The slice's own clock moves by the places it gave over its quota times its tension now
            // ([`StorePass::slice_clock`]).
            let n = self.slices.len();
            let step = clock_step(drawn.q + drawn.a, self.slices[drawn.slice].quota, weight[drawn.slice]);
            self.pass.slice_clock.get_or_insert_with(|| vec![0; n])[drawn.slice] += step;
        }
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

/// [definition; the lead, November 25] **A slice's clock step** ([`StorePass::slice_clock`]): `places` over the slice's quota times its
/// tension, on `2^(−SHARE_BITS)` of a place, released once a step.
pub fn clock_step(places: u64, quota: u128, weight: u128) -> u128 {
    (u128::from(places) << SHARE_BITS) / (quota * weight).max(1)
}

/// The code line's held passage (te7's lap script's `DEV`) as `train-field` reads it: its problems at the codec, those whose answer stands
/// within the codec's extent.
pub fn held_set(codec: &Codec, text: &[u8]) -> Result<Problems> {
    let mut out = Vec::new();
    for (q, a) in problems_of(text) {
        let (qc, ac) = (codec.encode(&question_text(&q))?, codec.encode(&a)?);
        if ac.len() < codec.answer {
            out.push((qc, ac, a.len()));
        }
    }
    Ok(out)
}
