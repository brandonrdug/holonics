//! The field's exterior commands (`holonics::hnn::tower::field`): the GSM8K boundary codec, the
//! training of the field on completed regions, its held-out read and its release by refinement.
//!
//! [definition; agent-inferred, November 1] **The codec is the founded units, or the bytes.** A
//! region's classes are the units the passage's own code founded (`hnn::units`), compacted to those
//! the training passage uses, with the void class past an answer's end; a founding of no merges
//! (`founded-units-v1 0`) is the bytes. No unit is chosen by hand: a chart that kept
//! digits apart and read them with their place was the recorded failure of October 27 (a
//! hand-written tokenizer standing in for learning) and is refused. The run reads bytes because the
//! founded units weld digits: only 552 of 2,287 operands (24.1%) were the same unit in the question
//! and in its calculation, so the field would meet one number as other words; a byte is the same
//! class wherever it is written. The codec is exterior: the field meets only classes.
//!
//! The mask and tail draws are an exterior keyed stream (the key file's last word seeds an integer
//! mixer, apart from every founding and growth draw read from its front): they choose which sites
//! a section compares and how far its region runs past the answer, never what the field deposits.
//!
//! [agent-inferred, November 1] **A region carries no word of where its answer ends.** The release
//! opens the answer at the training passage's longest extent and the region shrinks as voids are
//! released, so a training region runs past its answer by a keyed tail (see [`tail`]) and the
//! held-out read opens at the release's own extent. A region whose length ended one site past its
//! answer, as the first draft's did, told the field the answer's end, and the release could never
//! meet that region (the review of November 1).

use super::tower_train::{count, positive, STATE_BUDGET};
use super::*;
use holonics::hnn::tower::field::{Echo, Field, FieldDeclaration, FieldLearner, FieldNext, FieldRealization, FieldReceipt, HeldRows, HostField, Port, Region, Shares};
use holonics::hnn::units::Units;
use rayon::prelude::*;
use std::collections::HashMap;

/// A codec's text ceiling, `2^24` bytes.
const CODEC_BUDGET: usize = 1 << 24;

/// The GSM8K boundary codec: the founded units, the units the passage uses (each one class, in
/// unit order) and the answer's longest extent in classes.
pub(super) struct FieldCodec {
    units: Units,
    used: Vec<u32>,
    class_of_unit: HashMap<u32, usize>,
    /// The longest training answer in classes, plus its void: the answer sites a release opens.
    pub answer: usize,
}

/// A units file (`founded-units-v1 0`, a founding of no merges, is the bytes).
pub(super) fn units_of(path: &str, sha: &str) -> Result<Units> {
    Units::from_text(std::str::from_utf8(&pinned_read(path, sha, READ_BUDGET as usize)?)?).map_err(|e| e.to_string().into())
}

impl FieldCodec {
    /// The codec of a training passage's problems.
    pub(super) fn found(units: Units, problems: &[(Vec<u8>, Vec<u8>)]) -> Result<Self> {
        let mut used: Vec<u32> = Vec::new();
        for (q, a) in problems {
            used.extend(units.parse(&question_text(q)).map_err(|e| e.to_string())?);
            used.extend(units.parse(a).map_err(|e| e.to_string())?);
        }
        used.sort_unstable();
        used.dedup();
        let mut codec = Self::with(units, used, 0);
        codec.answer = problems.iter().map(|(_, a)| codec.encode(a).map(|c| c.len())).collect::<Result<Vec<_>>>()?.into_iter().max().unwrap_or(0) + 1;
        Ok(codec)
    }

    fn with(units: Units, used: Vec<u32>, answer: usize) -> Self {
        let class_of_unit = used.iter().enumerate().map(|(c, &u)| (u, c)).collect();
        Self { units, used, class_of_unit, answer }
    }

    /// The void class, the last.
    pub(super) fn void(&self) -> usize {
        self.used.len()
    }

    pub(super) fn alphabet(&self) -> usize {
        self.void() + 1
    }

    /// A text's classes; a unit the training passage never used is refused.
    pub(super) fn encode(&self, text: &[u8]) -> Result<Vec<usize>> {
        self.units.parse(text).map_err(|e| e.to_string())?.into_iter().map(|u| self.class_of_unit.get(&u).copied().ok_or_else(|| format!("unit {u} is not in the codec").into())).collect()
    }

    /// Classes back to bytes, up to the first void.
    pub(super) fn decode(&self, classes: &[usize]) -> Vec<u8> {
        let mut out = Vec::new();
        for &c in classes.iter().take_while(|&&c| c < self.void()) {
            out.extend_from_slice(self.units.piece(self.used[c] as usize));
        }
        out
    }

    /// The codec as text: its head line, then the used units on one line.
    pub(super) fn to_text(&self) -> String {
        let used: Vec<String> = self.used.iter().map(u32::to_string).collect();
        format!("field-codec-v2 {}\n{}\n", self.answer, used.join(" "))
    }

    pub(super) fn from_text(text: &str, units: Units) -> Result<Self> {
        let mut lines = text.lines();
        let head: Vec<&str> = lines.next().unwrap_or("").split(' ').collect();
        if head.len() != 2 || head[0] != "field-codec-v2" {
            return Err("a codec that is not field-codec-v2".into());
        }
        let used = lines.next().unwrap_or("").split(' ').map(|w| w.parse::<u32>()).collect::<std::result::Result<Vec<_>, _>>()?;
        if used.iter().any(|&u| u as usize >= units.len()) {
            return Err("a codec's unit outside the units".into());
        }
        Ok(Self::with(units, used, count(head[1])?))
    }
}

/// A problem's question as its region opens it: the question, then the line it ends on.
pub(super) fn question_text(q: &[u8]) -> Vec<u8> {
    let mut out = q.to_vec();
    out.push(b'\n');
    out
}

/// The record separator and the unit separator of a passage of records (ASCII `RS` and `US`).
pub(super) const RECORD: u8 = 0x1E;
pub(super) const UNIT: u8 = 0x1F;

/// The problems of a passage: `question \n answer` blocks separated by a blank line; or, where the passage carries the
/// record separator, records `question US answer` separated by it, each part's bytes kept whole. [agent-inferred, November 5]
/// Why the records: the code passage (Brandon, November 5: python-codes-25k in place of GSM8K) has answers that hold
/// blank lines and questions of several lines, which the blank-line blocks would cut; neither separator stands in it.
pub(super) fn problems_of(text: &[u8]) -> Vec<(Vec<u8>, Vec<u8>)> {
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
pub(super) fn mix(seed: u64, counter: u64) -> u64 {
    let mut z = seed.wrapping_add(counter.wrapping_mul(0x9E37_79B9_7F4A_7C15));
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

/// The encoded problems: each question's classes, its answer's and the answer's bytes.
pub(super) type Problems = Vec<(Vec<usize>, Vec<usize>, usize)>;

/// [definition; agent-inferred, November 3, §16.27] **A region's shape**: a keyed completion mask over the whole region
/// (`Masked`), or over the answer and its void tail with the question known (`Answer`), the state the writer meets
/// ([`Field::sample_realized`]: the question known, a uniform state of a random reading order of the answer's places).
pub(super) enum Shape {
    Masked(Vec<bool>),
    Answer(Vec<bool>),
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
pub(super) fn shape(seed: u64, draw: u64, question: usize, sites: usize) -> Shape {
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
pub(super) fn weighed_domain(m: usize, mask: &[bool]) -> usize {
    let k = mask.iter().filter(|&&u| u).count().max(1) as u128;
    (4 * m as u128 * k).isqrt() as usize
}

/// [definition; agent-inferred, November 5, the unified-theory reading of 19:32, part 2 of 18:53] **A region ends five places
/// past its lowest void**, the law since code85 stood against the keyed tail at equal laps (held context 2.124 against 2.181
/// at lap 1, sections 166 ms against 382); `FIELD_TAIL_KEYED` declares the keyed tail over the room it replaced, for
/// comparison. A training region's tail
/// is the void and the five places past it (`NEAR` places), a path state past a resolved void ends five places past it, and
/// the withheld read's tail is cut the same way, so every place before the end keeps its near field and the problem never
/// hears the codec's room (its longest answer and one). Why: the room's voids are no problem's; the content heard its length
/// through them, in void crowds and the backward strand's void sum, over as many as 1,700 places.
pub(super) fn near_tail() -> bool {
    static NEAR_TAIL: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *NEAR_TAIL.get_or_init(|| std::env::var_os("FIELD_TAIL_KEYED").is_none())
}

/// [definition; agent-inferred, November 5, the unified-theory reading of 21:19] **A path state with no resolved void keeps
/// the whole room**: its far open places are compared at the boundary again, the comparisons that taught the opening its
/// length (code84's segment 2: with them cut the opening's void mass fell to 0.02–0.04 at every distance), now on the clock
/// that runs a silent stretch past the last arrival at one rate (`Field::silent_stretch`). `FIELD_PATH_FRONT_CUT` declares
/// the cut it replaced (`NEAR − 1` places past the front octave's end, the margin read and not compared), for comparison.
pub(super) fn path_front_cut() -> bool {
    static CUT: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *CUT.get_or_init(|| std::env::var_os("FIELD_PATH_FRONT_CUT").is_some())
}

/// [definition; agent-inferred, November 5, the unified-theory reading of 23:26] **b2's far share, on the whole room**
/// (`FIELD_PATH_FAR_KEYED`, declared against b1's every place): a path state with no resolved void compares its front octave
/// whole and, past it, one place an octave through the codec's extent, the place the state's keyed order opens first there
/// (the writer's first read in it), at the boundary (letter or void) with weight one; the places between are read on the
/// one-rate clock past the last arrival and not compared (the port's `heard`). Why: the end is one variable, 9.57 bits an
/// answer, and the whole room compared it once a place, 638 bits a state on the truth's own curve, as much as an answer's
/// content (430 to 620), so length took about half the step; the keyed places code about 3 bits a state, the end's octave,
/// and the front octave codes its place within it. Keyed, not at fixed distances: the clock turns the rings, and fixed
/// distances meet them at a few phases. It keeps b1's geometry, so it reads the far share alone; b2 proper also drops the
/// places between (regions with explicit positions).
pub(super) fn path_far_keyed() -> bool {
    static KEYED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *KEYED.get_or_init(|| std::env::var_os("FIELD_PATH_FAR_KEYED").is_some())
}

/// [agent-inferred, November 1] A region's void tail past its answer, in `[1, room]`, `room` the
/// codec's answer extent less the answer's: an octave `k` of the room drawn uniform, then a length
/// uniform in `[2^k, min(2^(k+1) − 1, room)]`. Every octave of tail is met alike, so the field
/// meets the long void regions of a release's first sweeps and the short ones of its last; on the
/// GSM8K training passage this reads 1.86 times the sites² of a one-void tail (a uniform length
/// would read 3.42 times).
pub(super) fn tail(seed: u64, draw: u64, room: usize) -> usize {
    let room = room.max(1);
    if near_tail() {
        return holonics::hnn::tower::field::NEAR.min(room);
    }
    let octaves = u64::from(usize::BITS - room.leading_zeros());
    let k = (mix(seed, draw | 1 << 63) % octaves) as u32;
    let low = 1usize << k;
    let high = ((1usize << (k + 1)) - 1).min(room);
    low + (mix(seed, draw | 3 << 62) as usize) % (high - low + 1)
}

/// A problem's region classes: the question and its line, the answer, then `void` to `length`.
pub(super) fn region_classes(codec: &FieldCodec, q: &[usize], a: &[usize], length: usize) -> Vec<usize> {
    let mut out: Vec<usize> = q.iter().chain(a).copied().collect();
    out.resize(length, codec.void());
    out
}

/// The lengths of the regions `members` would form from `draw` on (each draw counted as
/// [`section_regions`] counts it): one region a member, then each of `paths`' path states ([`opening_region`]).
pub(super) fn region_lengths(codec: &FieldCodec, problems: &Problems, members: &[usize], paths: &[usize], seed: u64, draw: &mut u64) -> Vec<usize> {
    let mut draws = Vec::with_capacity(members.len());
    let mut out: Vec<usize> = members
        .iter()
        .map(|&i| {
            let (q, a, _) = &problems[i];
            *draw += 1;
            draws.push(*draw);
            q.len() + a.len() + tail(seed, *draw, codec.answer - a.len())
        })
        .collect();
    out.extend(paths.iter().zip(&draws).filter_map(|(&i, &d)| opening_region(codec, &problems[i].0, &problems[i].1, seed, d).map(|r| r.classes.len())));
    if path_writer() {
        out.extend(paths.iter().zip(&draws).filter_map(|(&i, &d)| writer_region(codec, &problems[i].0, &problems[i].1, seed, d).map(|r| r.classes.len())));
    }
    if path_squares() {
        // Four states a square, each the truth cut NEAR places past the end (a square whose face holds no runner-up is fewer).
        out.extend(paths.iter().filter(|&&i| problems[i].1.len().min(codec.answer) >= 2).flat_map(|&i| std::iter::repeat_n((problems[i].0.len() + problems[i].1.len().min(codec.answer) + holonics::hnn::tower::field::NEAR).min(problems[i].0.len() + codec.answer), 4)));
    }
    if path_drafts() {
        out.extend(paths.iter().filter(|&&i| !problems[i].1.is_empty()).map(|&i| (problems[i].0.len() + problems[i].1.len().min(codec.answer) + holonics::hnn::tower::field::NEAR).min(problems[i].0.len() + codec.answer)));
    }
    out
}

/// [definition; agent-inferred, November 5, §16.47] **A problem's writer's path, compared at its boundary**: the question
/// resolved and the codec's whole extent past it, as the writer opens ([`opening`]), then one state of the writer's own
/// reading order run on the truth: the extent's places by octaves of their distance from the question, keyed within an
/// octave and fresh each draw, as the writer releases them ([`holonics::hnn::tower::field::Field::sample_realized`];
/// the unified-theory reading of November 5, 15:04: read on a state the path trained in one keyed order, the octave
/// writer wrote 1.49 times held, its end's faces never having met these states), its first `k` places resolved
/// from the truth and every place past the lowest resolved void resolved as the void (the writer's closing law), `k`
/// drawn so every octave of reads is met alike (`k = 0`, the opening, the first; then `[2^(o−1), 2^o)` within the extent,
/// uniform). Every open place is an answer port compared at its boundary
/// ([`holonics::hnn::tower::field::Port::boundary`]) at weight one: the answer's places with whether a letter stands
/// there, never which, the places past it with the void. Why (the unified-theory readings of November 5, 08:09 and
/// 10:51; §16.46 and §16.47): the writer fixes its length in its first reads and never undoes a letter past the true
/// end; compared at the opening alone, the opening met the length law (byte mass past the end 63 places against 222) but
/// the writer still overran, 95% of the drift of its expected length made in its reads 1 to 64, the sparse states
/// training meets about as rarely as it met the opening; each octave of reads carries an equal share of where the
/// length is decided. The boundary's minimizer is the answer's length given the question and what the path has resolved.
///
/// [definition; agent-inferred, November 5, the unified-theory readings of 18:53 and 21:19] Before a void is resolved the
/// path state keeps the whole room, its far open places compared at the boundary (`path_front_cut`); under
/// `FIELD_PATH_FRONT_CUT` it ends five places past its front, the cut of 18:53 (every place past the front octave is open
/// and silent and heard by the front only through the near field, so the region is cut `NEAR − 1` places past the front
/// octave's end, the faces at and before it the whole room's bit for bit, the margin read and not compared at the port's
/// stop), which kept the faces and dropped the far comparisons that taught the length. Past a resolved void the region ends
/// `NEAR` places past it (`near_tail`). A state with nothing open is no state (none).
pub(super) fn opening_region(codec: &FieldCodec, q: &[usize], a: &[usize], seed: u64, draw: u64) -> Option<TrainRegion> {
    if path_prefix() {
        return Some(prefix_region(codec, q, a, seed, draw));
    }
    opening_region_with(codec, q, a, seed, draw, path_far_keyed())
}

/// [definition; agent-inferred, November 6, the unified-theory reading of 00:58] **The writer's path in place order**
/// (`FIELD_PATH_PREFIX`, declared against the octave path): a path state is a prefix, the question and the answer's first `k`
/// places resolved, compared at its frontier on the frontier's own class (its byte, or the void where the answer ends: content
/// and boundary at once), the room past it silent and not compared. `k` is uniform in `[0, len]` (`len` the answer's places,
/// its end the void at `len`) and the state stands for the `len + 1` places its draw samples (`domain`, weight
/// `(len + 1)/1`, [`Region::weight`]), so each place counts once, the taught hazard is the truth's, and a prefix state weighs an
/// answer's chain code as a mask state weighs its averaged code (the unified-theory reading of 01:21: at weight one an
/// octave-uniform `k` drew a 250-place answer's place 130 in 1 of 1,107 states, and the taught hazard wrote 0.34 of held,
/// 56% of the ends in an octave's first eighth against the truth's 17%). The region is cut
/// `NEAR − 1` places past the frontier, the same bits for the frontier's face (the silent room past it is heard only through the near
/// field, `the_room_past_the_front_is_heard_only_through_the_near_field`); its places past the frontier stand in a port that
/// hears none of them. Why: one place a read in one order draws exactly the joint its faces make by the chain rule, and a
/// prefix state compared at its frontier is that joint's own code, the end coded once an answer where the writer meets it; the
/// content masks code the order-averaged joint and the octave path states compared only the boundary, so neither order was
/// trained at its own states. Place order, because keyed octaves draw early bytes beside blank neighbours (common bytes only,
/// Brandon's read of 23:12).
pub(super) fn prefix_region(codec: &FieldCodec, q: &[usize], a: &[usize], seed: u64, draw: u64) -> TrainRegion {
    let room = codec.answer;
    let last = a.len().min(room - 1);
    let k = (mix(seed, draw | 5 << 61) % (last as u64 + 1)) as usize;
    let frontier = q.len() + k;
    let cut = (frontier + holonics::hnn::tower::field::NEAR).min(q.len() + room);
    let classes = region_classes(codec, q, a, cut);
    let unresolved: Vec<bool> = (0..cut).map(|t| t >= frontier).collect();
    let heard = vec![false; cut];
    TrainRegion { domain: Some(last + 1), port: Some((frontier + 1, codec.void(), Vec::new(), true, None, Some(heard))), ..TrainRegion::plain(classes, unresolved) }
}

/// [definition; agent-inferred, November 6, the unified-theory reading of 04:03] **Length lives at one state**
/// (`FIELD_PATH_OPENING`, with the far share): the only path state is the fully masked one, the release's first read, where
/// the void mass at each place is the length's distribution; it keeps the room and compares one keyed place an octave of
/// distance from the question (b2's far places on the one-rate clock), at the boundary with weight one, keyed by distance and
/// never by the end. Every other state keeps the near tail.
pub(super) fn path_opening() -> bool {
    static OPENING: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *OPENING.get_or_init(|| std::env::var_os("FIELD_PATH_OPENING").is_some())
}

/// [definition; agent-inferred, November 6, the unified-theory reading of 06:50] **The writer's own state, given its end**
/// (`FIELD_PATH_WRITER`, beside the opening): the one-end writer fixes its length at the release's first read and then
/// sweeps given it, so every state it meets past that read is the question, the answer's places to its end with the first
/// `k` of them in its order resolved, and the end's `NEAR` voids resolved, its region cut there ([`Field::sample_runs`] with
/// `lengths`: the near tail of the read's region). This is that state on the truth: the answer's places ordered by octaves of
/// their distance from the question, keyed within an octave and fresh each draw, as the writer releases them; `k` drawn so
/// every octave of reads is met alike (`k = 0`, the state just past the end's draw, the first; then `[2^(o−1), 2^o)` within
/// the answer, at least one place left open); every open place compared on its own class at weight one (no port: the
/// region's `K` open places of `K`, [`holonics::hnn::tower::field::Region::weight`]), the end's voids given and not compared.
/// Why (the unified-theory reading of 06:50): with the opening as the only path state (code91) the writer's states past its
/// first read left training, and the writer's own order code rose from 3.316 to 4.06 bits a place while the other orders'
/// fell; the opening keeps the length and these keep the states the writer writes in. [the unified-theory reading of 09:50]
/// Not at the boundary: once the end's voids are given, a boundary codes a letter place only as `−log₂(1 − p̂_∅)`, its letters
/// renormalized off the void, so it compared no letter (long109's seg1 moved the writer's order code and the space, not its
/// fences or openings); compared on their classes, these are the masks' comparison under the writer's own mask.
/// [the unified-theory readings of 11:49 and 12:23] `FIELD_WRITER_LETTERS` declares each open place compared on its letters
/// off the void instead ([`holonics::hnn::tower::field::Port::letters`], the release's own draw given the end). It is built and
/// its card parity passed, but it is held: lap 12 read off the void equalled the read with it to three places, and lap 14
/// brought the length back on the whole-class law. It joins only if the expected length less held passes +40 again and the
/// off-void given-end read comes in at least 0.01 bits a letter under the with-void read. An answer with no place is no state.
///
/// [`holonics::hnn::tower::field::Field::sample_runs`]: the writer whose states these are.
pub(super) fn writer_region(codec: &FieldCodec, q: &[usize], a: &[usize], seed: u64, draw: u64) -> Option<TrainRegion> {
    let len = a.len().min(codec.answer);
    if len == 0 {
        return None;
    }
    let near = holonics::hnn::tower::field::NEAR;
    let cut = (q.len() + len + near).min(q.len() + codec.answer);
    let classes = region_classes(codec, q, &a[..len], cut);
    let mut unresolved: Vec<bool> = (0..cut).map(|t| t >= q.len() && t < q.len() + len).collect();
    let key = mix(seed, draw | 7 << 61);
    // The places `k` may resolve and leave one open: `[0, len − 1]`, met by its octaves.
    let most = len - 1;
    let octaves = u64::from(usize::BITS - most.leading_zeros()) + 1;
    let o = (key % octaves) as u32;
    let k = if o == 0 {
        0
    } else {
        let low = 1usize << (o - 1);
        let high = ((1usize << o) - 1).min(most);
        low + (mix(seed, draw | 15 << 60) as usize) % (high - low + 1)
    };
    let mut order: Vec<usize> = (q.len()..q.len() + len).collect();
    order.sort_by_key(|&t| (holonics::hnn::tower::field::octave_of(t + 1 - q.len()), mix(key, t as u64), t));
    for &t in &order[..k] {
        unresolved[t] = false;
    }
    if writer_letters() {
        // Declared: each open place on its letters off the void, the release's own draw given the end.
        return Some(TrainRegion { port: Some((q.len(), codec.void(), a[..len].to_vec(), false, None, None)), letters: true, ..TrainRegion::plain(classes, unresolved) });
    }
    Some(TrainRegion::plain(classes, unresolved))
}

/// Whether the writer's states are compared on their letters off the void (`FIELD_WRITER_LETTERS`, [`writer_region`]).
pub(super) fn writer_letters() -> bool {
    static LETTERS: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *LETTERS.get_or_init(|| std::env::var_os("FIELD_WRITER_LETTERS").is_some())
}

/// [definition; agent-inferred, November 6, the unified-theory reading of 06:50, E] **The opening's room is cut to its windows**
/// (`FIELD_ROOM_CUT`): the fully masked path state computes the question, the stretch's first place and each heard place
/// with `(NEAR − 1)·ticks` places on either side ([`holonics::hnn::tower::field::Region::window`]); its heard faces and its
/// covector are the whole room's bit for bit (`a_cut_room_reads_and_returns_the_whole_rooms_bits`). The masks and the writer's
/// states keep their room whole: their blanks sit between arrivals.
pub(super) fn room_cut() -> bool {
    static CUT: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *CUT.get_or_init(|| std::env::var_os("FIELD_ROOM_CUT").is_some())
}

/// [definition; agent-inferred, November 6, the unified-theory reading of 17:08] **The field meets its own release**
/// (`FIELD_PATH_DRAFTS`, beside the opening and the writer's state): for each path problem a draw `ρ` uniform on `(0, 1]` (on
/// `2^(−16)`) opens a keyed `ρ` share of the answer's places (at least one) in the truth's region given its end (the answer,
/// its end's `NEAR` voids given, the region cut there), and the field as it stands reads it once; each open place is drawn
/// from its face over the letters (temperature one, keyed, the release's own draw given the end). The draft region holds those
/// draws and the truth elsewhere, and opens a masks' state over the answer's places (`τ = u²`, [`shape`]'s law, weighed back by
/// [`weighed_domain`]), each open place compared with the truth's class. Why (the unified-theory reading of 17:08): the
/// writer places each letter once beside open neighbours, and a written non-word is a context no training comparison met;
/// here every comparison reads the truth beside the field's own drafts. The read is one card read a section of short regions.
pub(super) fn draft_regions(codec: &FieldCodec, problems: &Problems, paths: &[usize], draws: &[u64], seed: u64, field: &Field, realization: &mut dyn FieldRealization) -> Result<Vec<TrainRegion>> {
    let near = holonics::hnn::tower::field::NEAR;
    let void = codec.void();
    // Each draft's truth, its open places and its draw.
    let mut reads: Vec<(Vec<usize>, Vec<bool>, usize, usize, u64)> = Vec::new();
    for (&i, &d) in paths.iter().zip(draws) {
        let (q, a, _) = &problems[i];
        let len = a.len().min(codec.answer);
        if len == 0 {
            continue;
        }
        let cut = (q.len() + len + near).min(q.len() + codec.answer);
        let classes = region_classes(codec, q, &a[..len], cut);
        // The draft's own key stream, apart from every draw-tagged stream of the section's other regions.
        let key = mix(seed ^ 0x0D2A_F7ED_0000_0000, d);
        let rho = ((mix(key, 1) >> 1) & 0xFFFF) + 1;
        let mut open: Vec<bool> = (0..cut).map(|t| t >= q.len() && t < q.len() + len && (mix(key, (t as u64 + 1) << 8 | 2) & 0xFFFF) < rho).collect();
        if !open.iter().any(|&u| u) {
            open[q.len() + (mix(key, 3) as usize) % len] = true;
        }
        reads.push((classes, open, q.len(), len, d));
    }
    if reads.is_empty() {
        return Ok(Vec::new());
    }
    let views: Vec<Region> = reads.iter().map(|(classes, open, _, _, _)| Region { classes, unresolved: open, faces: &[], locked: &[], echo: &[], domain: None, port: None }).collect();
    let faces = realization.read_faces(field, &views).map_err(|e| e.to_string())?;
    let mut out = Vec::with_capacity(reads.len());
    for ((classes, open, start, len, d), f) in reads.iter().zip(&faces) {
        // The draft: each open place drawn from its face over the letters, the truth elsewhere.
        let mut drafted = classes.clone();
        for t in (0..classes.len()).filter(|&t| open[t]) {
            let face = f[t].as_ref().ok_or("a draft's open place with no face")?;
            let letters = face.total - face.masses[void];
            if letters == 0 {
                continue;
            }
            let key = mix(seed ^ 0x0D2A_F7ED_0000_0000, *d);
            let u = (((mix(key, (t as u64 + 1) << 8 | 4) as u128) << 64) | mix(key, (t as u64 + 1) << 8 | 5) as u128) % letters;
            let mut acc = 0u128;
            if let Some(c) = (0..face.masses.len()).filter(|&c| c != void).find(|&c| {
                acc += face.masses[c];
                acc > u
            }) {
                drafted[t] = c;
            }
        }
        // The masks' state over the answer's places, compared on the truth's classes.
        // `τ = u²` over the answer's places ([`shape`]'s law), at least one open.
        let key = mix(seed ^ 0x0D2A_F7ED_0000_0000, *d);
        let u = ((mix(key, 6) >> 1) & 0xFFFF) + 1;
        let tau = ((u * u) >> 16).max(1);
        let mut unresolved: Vec<bool> = (0..classes.len()).map(|t| t >= *start && t < start + len && (mix(key, (t as u64 + 1) << 8 | 7) & 0xFFFF) < tau).collect();
        if !unresolved.iter().any(|&o| o) {
            unresolved[start + (mix(key, 8) as usize) % len] = true;
        }
        let row: Vec<usize> = (0..classes.len()).map(|t| if unresolved[t] { classes[t] } else { drafted[t] }).collect();
        let answer_mask: Vec<bool> = unresolved[*start..start + len].to_vec();
        out.push(TrainRegion { domain: Some(weighed_domain(*len, &answer_mask)), ..TrainRegion::plain(row, unresolved) });
    }
    Ok(out)
}

/// Whether each path problem also trains on its own draft ([`draft_regions`], `FIELD_PATH_DRAFTS`).
pub(super) fn path_drafts() -> bool {
    static DRAFTS: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *DRAFTS.get_or_init(|| std::env::var_os("FIELD_PATH_DRAFTS").is_some())
}

/// Whether each path problem also trains the writer's own state given its end ([`writer_region`]).
pub(super) fn path_writer() -> bool {
    static WRITER: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *WRITER.get_or_init(|| std::env::var_os("FIELD_PATH_WRITER").is_some())
}

/// Whether the path states are prefixes in place order ([`prefix_region`]).
pub(super) fn path_prefix() -> bool {
    static PREFIX: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *PREFIX.get_or_init(|| std::env::var_os("FIELD_PATH_PREFIX").is_some())
}

/// [`opening_region`] with b2's far share declared or not ([`path_far_keyed`]).
pub(super) fn opening_region_with(codec: &FieldCodec, q: &[usize], a: &[usize], seed: u64, draw: u64, far_keyed: bool) -> Option<TrainRegion> {
    let room = codec.answer;
    let classes = region_classes(codec, q, a, q.len() + room);
    let mut unresolved: Vec<bool> = (0..classes.len()).map(|t| t >= q.len()).collect();
    let key = mix(seed, draw | 5 << 61);
    let octaves = u64::from(usize::BITS - room.leading_zeros()) + 1;
    let o = (key % octaves) as u32;
    let k = if o == 0 || path_opening() {
        0
    } else {
        let low = 1usize << (o - 1);
        let high = ((1usize << o) - 1).min(room);
        low + (mix(seed, draw | 6 << 61) as usize) % (high - low + 1)
    };
    let mut order: Vec<usize> = (q.len()..classes.len()).collect();
    order.sort_by_key(|&t| (holonics::hnn::tower::field::octave_of(t + 1 - q.len()), mix(key, t as u64), t));
    for &t in &order[..k] {
        unresolved[t] = false;
    }
    let voided = (q.len()..classes.len()).find(|&t| !unresolved[t] && classes[t] == codec.void());
    if let Some(end) = voided {
        for slot in &mut unresolved[end + 1..] {
            *slot = false;
        }
    }
    if !unresolved.iter().any(|&u| u) {
        return None;
    }
    let (mut classes, mut unresolved, mut stop) = (classes, unresolved, None);
    if let Some(end) = voided.filter(|_| near_tail()) {
        let cut = (end + holonics::hnn::tower::field::NEAR).min(classes.len());
        classes.truncate(cut);
        unresolved.truncate(cut);
    }
    let mut heard = None;
    if voided.is_none() && !path_front_cut() && far_keyed {
        let front = holonics::hnn::tower::field::octave_of(order[k] + 1 - q.len());
        let mut mask: Vec<bool> = (0..classes.len()).map(|t| t >= q.len() && holonics::hnn::tower::field::octave_of(t + 1 - q.len()) <= front).collect();
        let mut last = front;
        for &t in &order[k..] {
            let o = holonics::hnn::tower::field::octave_of(t + 1 - q.len());
            if o > last {
                mask[t] = true;
                last = o;
            }
        }
        heard = Some(mask);
    }
    if voided.is_none() && path_front_cut() {
        let front = holonics::hnn::tower::field::octave_of(order[k] + 1 - q.len());
        let front_end = (q.len() + (1usize << (front + 1)) - 1).min(classes.len());
        let cut = (front_end + holonics::hnn::tower::field::NEAR - 1).min(classes.len());
        classes.truncate(cut);
        unresolved.truncate(cut);
        stop = Some(front_end).filter(|&e| e < cut);
    }
    // The answer's cells the region holds: past a cut region the answer goes on, so every place it holds is a letter's.
    let target = a[..a.len().min(classes.len() - q.len())].to_vec();
    // [E] The opening (no void resolved, every answer place silent) cuts its room to its heard places' windows, declared.
    let window = room_cut() && voided.is_none() && heard.is_some() && k == 0;
    Some(TrainRegion { port: Some((q.len(), codec.void(), target, true, stop, heard)), window, ..TrainRegion::plain(classes, unresolved) })
}

/// A training region: its classes, its unresolved sites, its carried faces and its locks (each
/// empty where none).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct TrainRegion {
    pub classes: Vec<usize>,
    pub unresolved: Vec<bool>,
    pub faces: Vec<Option<Shares>>,
    pub locked: Vec<bool>,
    /// Each carried site's echo (§15.3), empty where none.
    pub echo: Vec<Option<Echo>>,
    /// The sites its open ones were drawn from (§16.23, [`Region::domain`]).
    pub domain: Option<usize>,
    /// Its answer port (§16.24, [`Region::port`]): the first place, the void, the cells, and whether it is compared at
    /// its boundary (§16.47) rather than through its coupling.
    pub port: Option<(usize, usize, Vec<usize>, bool, Option<usize>, Option<Vec<bool>>)>,
    /// Whether its port cuts the room to its windows ([`holonics::hnn::tower::field::Port::window`]).
    pub window: bool,
    /// Whether its port compares its open places on their letters off the void ([`holonics::hnn::tower::field::Port::letters`]).
    pub letters: bool,
    /// Its port's declared pull ([`holonics::hnn::tower::field::Port::pull`]).
    pub pull: Option<(usize, usize, i64)>,
}

impl TrainRegion {
    /// A region carrying no face and no lock.
    pub(super) fn plain(classes: Vec<usize>, unresolved: Vec<bool>) -> Self {
        Self { classes, unresolved, faces: Vec::new(), locked: Vec::new(), echo: Vec::new(), domain: None, port: None, window: false, letters: false, pull: None }
    }
}

/// A region as the field reads it.
fn view_of(region: &TrainRegion) -> Region<'_> {
    Region { classes: &region.classes, unresolved: &region.unresolved, faces: &region.faces, locked: &region.locked, echo: &region.echo, domain: region.domain, port: region.port.as_ref().map(|(start, void, target, boundary, stop, heard)| Port { start: *start, void: *void, target, boundary: *boundary, stop: *stop, heard: heard.as_deref(), window: region.window, letters: region.letters, pull: region.pull }) }
}

/// The regions as the field reads them.
pub(super) fn views_of(regions: &[TrainRegion]) -> Vec<Region<'_>> {
    regions.iter().map(view_of).collect()
}

/// **A section's regions as `train-field` forms them**: each member's classes (its question, its answer and a keyed
/// void tail) and its shape ([`shape`]), one region a member, weighed in the joint code over the sites its open ones were
/// drawn from ([`Region::weight`]: the whole region, or the answer and its tail); then a state of the writer's path of
/// each of `paths`, the section's share of the lap's keyed passage ([`paths_of`]), compared at its boundary
/// ([`opening_region`], §16.47), the `n`th on the `n`th member's draw. The step the learner holds is read first on these
/// regions, which it was not fit on, and the held step's read is returned.
pub(super) fn section_regions(codec: &FieldCodec, problems: &Problems, members: &[usize], paths: &[usize], seed: u64, draw: &mut u64, learner: &mut FieldLearner, realization: &mut dyn FieldRealization) -> Result<(Vec<TrainRegion>, Option<FieldNext>)> {
    if paths.len() != members.len() {
        return Err(format!("a section of {} members and {} paths", members.len(), paths.len()).into());
    }
    let mut regions: Vec<TrainRegion> = Vec::with_capacity(3 * members.len());
    let mut draws = Vec::with_capacity(members.len());
    for &i in members {
        let (q, a, _) = &problems[i];
        *draw += 1;
        draws.push(*draw);
        let length = q.len() + a.len() + tail(seed, *draw, codec.answer - a.len());
        let classes = region_classes(codec, q, a, length);
        regions.push(match shape(seed, *draw, q.len(), length) {
            Shape::Masked(mask) => TrainRegion { domain: Some(weighed_domain(length, &mask)), ..TrainRegion::plain(classes, mask) },
            Shape::Answer(mask) => TrainRegion { domain: Some(weighed_domain(length - q.len(), &mask)), ..TrainRegion::plain(classes, mask) },
        });
    }
    // [§16.47] Beside the members' regions, a state of each path problem's writer's path, compared at its boundary.
    regions.extend(paths.iter().zip(&draws).filter_map(|(&i, &d)| opening_region(codec, &problems[i].0, &problems[i].1, seed, d)));
    // [the unified-theory reading of November 6, 06:50] Then, declared, the writer's own state of each path problem given its end.
    if path_writer() {
        regions.extend(paths.iter().zip(&draws).filter_map(|(&i, &d)| writer_region(codec, &problems[i].0, &problems[i].1, seed, d)));
    }
    // [the unified-theory reading of November 6, 17:08] Then, declared, each path problem's own draft: the field meets its release.
    if path_drafts() {
        let drafts = draft_regions(codec, problems, paths, &draws, seed, &learner.field, realization)?;
        regions.extend(drafts);
    }
    // [the unified-theory reading of November 6, 19:04] Then, declared, each path problem's square: the faces' two readings agree.
    if path_squares() {
        let (squares, met, curl) = square_regions(codec, problems, paths, &draws, seed, &learner.field, realization)?;
        regions.extend(squares);
        println!("FIELD_SQUARES squares={met} curl_bits={}", bits(curl, met.max(1)));
    }
    let next = if learner.holds_step() { learner.read_step_on(&views_of(&regions), realization).map_err(|e| e.to_string())?.1 } else { None };
    Ok((regions, next))
}

/// [agent-inferred, November 1] **The training passage's sections and its withheld problems**:
/// `withheld` problems, the first in a keyed order, are never trained on; their code at the
/// release's opening is the run's own unseen read ([`unseen_regions`]), the step a lap's last
/// section holds is read on them, and the body grows on it ([`train`]). The rest are sorted by length and cut into sections of `section`.
/// Why: the first reading's growth read the passage's own code, read before each deposit, which
/// fell every lap while the held answer's rose, so the body never grew; and the held problems are
/// the reading's, which no decision of the run may read.
pub(super) fn sections_of(problems: &Problems, section: usize, withheld: usize, seed: u64) -> (Vec<Vec<usize>>, Vec<usize>) {
    let mut keyed: Vec<usize> = (0..problems.len()).collect();
    keyed.sort_by_key(|&i| (mix(seed, 1 << 61 | i as u64), i));
    let mut unseen = keyed[..withheld.min(keyed.len())].to_vec();
    unseen.sort_unstable();
    let mut order: Vec<usize> = keyed[withheld.min(keyed.len())..].to_vec();
    order.sort_by_key(|&i| (problems[i].0.len() + problems[i].1.len(), i));
    (order.chunks(section).map(|c| c.to_vec()).collect(), unseen)
}

/// The keyed order a learner that has read `read` laps walks the sections in.
pub(super) fn walk(seed: u64, read: u64, sections: usize) -> Vec<usize> {
    let mut walk: Vec<usize> = (0..sections).collect();
    walk.sort_by_key(|&s| (mix(seed, (read << 40) ^ s as u64), s));
    walk
}

/// [definition; agent-inferred, November 5, §16.47] **A lap's path problems, by section**: the problems whose writer's
/// path a section compares at its boundary ([`section_regions`]), cut from one keyed order of the whole passage, fresh
/// each lap, in the sizes of the sections in the lap's walk, so each problem's path is met once a lap. Why (the
/// unified-theory reading of November 5, 12:31): the sections are cut from problems sorted by length, so a section's own
/// members' boundary covectors were of one length class and one sign (their void entries sum to the members' answer
/// length less the opening's expected length), and the opening's void bias followed the last sections walked: segment 2's
/// last lap walked sections 15 to 57 bytes shorter than the passage at every depth from 2 to 128 sections and its opening
/// sat 34 places short of the length law, where segments 1 and 3, whose last laps did not, sat on it. The masked regions
/// stay with their sections, so a section's packing changes only by its path problems' questions.
pub(super) fn paths_of(seed: u64, read: u64, sections: &[Vec<usize>]) -> Vec<Vec<usize>> {
    let mut keyed: Vec<usize> = sections.iter().flatten().copied().collect();
    keyed.sort_by_key(|&i| (mix(seed, 7 << 60 | read << 40 | i as u64), i));
    let mut out = vec![Vec::new(); sections.len()];
    let mut rest = keyed.as_slice();
    for s in walk(seed, read, sections.len()) {
        let (now, later) = rest.split_at(sections[s].len());
        out[s] = now.to_vec();
        rest = later;
    }
    out
}

/// The first draw of the withheld problems' regions, the same every lap (apart from every
/// training draw, a lap's count times the passage's).
pub(super) const UNSEEN_DRAW: u64 = 1 << 61;

/// The held-out read: at the release's own opening (the region the question and the codec's
/// answer extent, every answer site unresolved at once), with each site's neighbours resolved
/// ([`context_regions`], the region the question, the answer and its first void), and the same
/// beside another problem's question (the foil, [`held_regions`]), the field's code over the
/// answer's classes and its first void, on `2^(−20)` bits, beside each one's count: `[opening,
/// context, foil]`. A reading of completion only (§16.23): no decision of the run reads it.
/// [retired, November 2, §16.19] The split of each into its digits and its text: a class sorted by
/// the codec's own byte kind was the numeral matcher's partition, read beside the field's own.
fn held_out(field: &Field, codec: &FieldCodec, problems: &Problems, realization: &mut dyn FieldRealization) -> Result<[(i64, usize); 3]> {
    let regions = held_regions(codec, problems);
    let views: Vec<Region> = regions.iter().map(|(c, u, _)| Region { classes: c, unresolved: u, faces: &[], locked: &[], echo: &[], domain: None, port: None }).collect();
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

/// [measurement; agent-inferred, November 2] **The held answer sites' rows by where their mass lies**
/// ([`FieldRealization::read_row_shares`]), on two sets of the held problems' regions: `opening`, the release's first
/// read (base 0 of [`held_regions`]: the question definite and every answer site open), and `context`, the held
/// read's (base 1: one answer site in [`CONTEXT`] open, its neighbours resolved). For each head and tick, over the
/// unresolved answer sites, the millionths of a row's mass on the question past the near field (`question_far`),
/// on the question within it (`question_near`), on the soft near field and on the rest; the current's part from the
/// question per row (on the value's grain); and the far question's mean effective count of sources over the rows
/// that hear it, `(Σ p)² / Σ p²` (§16.19's far-contact review). Region-level groups only. A reading only: nothing
/// in the run reads it.
fn held_rows_text(field: &Field, codec: &FieldCodec, problems: &Problems, realization: &mut dyn FieldRealization, lap: i64) -> Result<()> {
    let regions = held_regions(codec, problems);
    let n = problems.len();
    let d = field.declaration;
    let sets: [(&str, usize, usize, usize); 2] = [("opening", 0, n, 1), ("context", n, n * CONTEXT, CONTEXT)];
    for (set, skip, take, parts) in sets {
        let started = std::time::Instant::now();
        let views: Vec<Region> = regions.iter().skip(skip).take(take).map(|(c, u, _)| Region { classes: c, unresolved: u, faces: &[], locked: &[], echo: &[], domain: None, port: None }).collect();
        let questions: Vec<usize> = problems.iter().flat_map(|(q, _, _)| std::iter::repeat_n(q.len(), parts)).collect();
        let mut total = vec![HeldRows::default(); d.ticks * d.heads];
        for (chunk, asks) in views.chunks(64).zip(questions.chunks(64)) {
            for (acc, one) in total.iter_mut().zip(realization.read_row_shares(field, chunk, asks).map_err(|e| e.to_string())?) {
                acc.rows += one.rows;
                acc.question += one.question;
                acc.soft_near += one.soft_near;
                acc.other += one.other;
                acc.question_current += one.question_current;
                acc.question_far += one.question_far;
                acc.far_effective += one.far_effective;
                acc.far_rows += one.far_rows;
                acc.near_definite += one.near_definite;
            }
        }
        let share = |v: u128, rows: u64| (v * 1_000_000 >> 63) / rows.max(1) as u128;
        println!("FIELD_ROWS_HELD_READ lap={lap} set={set} regions={} ms={}", views.len(), started.elapsed().as_millis());
        for tick in 0..d.ticks {
            for head in 0..d.heads {
                let r = total[tick * d.heads + head];
                // The mean effective count on 2^(−8), to hundredths.
                let effective = (r.far_effective * 100 / 256) / r.far_rows.max(1) as u128;
                println!(
                    "FIELD_ROWS_HELD lap={lap} set={set} head={head} tick={tick} rows={} question_far_share={} question_near_share={} soft_near_share={} near_definite_share={} other_share={} question_current={} far_rows={} far_effective_sources={}.{:02}",
                    r.rows,
                    share(r.question_far, r.rows),
                    share(r.question - r.question_far, r.rows),
                    share(r.soft_near, r.rows),
                    share(r.near_definite, r.rows),
                    share(r.other, r.rows),
                    r.question_current / r.rows.max(1) as i128,
                    r.far_rows,
                    effective / 100,
                    effective % 100
                );
            }
        }
    }
    Ok(())
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
pub(super) fn context_regions(void: usize, q: &[usize], a: &[usize], length: usize) -> Vec<(Vec<usize>, Vec<bool>)> {
    let mut classes: Vec<usize> = q.iter().chain(a).copied().collect();
    classes.resize(length, void);
    let end = q.len() + a.len() + 1;
    (0..CONTEXT).map(|r| (classes.clone(), (0..length).map(|t| t >= q.len() && t < end && (t - q.len()) % CONTEXT == r).collect())).collect()
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
pub(super) fn held_regions(codec: &FieldCodec, problems: &Problems) -> Vec<(Vec<usize>, Vec<bool>, usize)> {
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

/// [definition; agent-inferred, November 2, §16.23] **One held problem's states for the joint read**: its answer (and
/// its first void, `m = |A| + 1` sites) read beside a question, the question resolved, at one state a stratum: `K_s`
/// uniform in the stratum `S_s = [1 + ⌊s m/D⌋, 1 + ⌊(s+1) m/D⌋)` of `1..m` (`D` = [`CONTEXT`] strata, empty strata
/// skipped), and `K_s` open sites uniform among the `m` (the keyed `K_s` least of a keyed rank). The weight of stratum
/// `s` is `|S_s|/K_s`, so `Σ_s (|S_s|/K_s) Σ_(open) −log₂ p̂` is the stratified reading of
/// `E_(K~U{1..m}) (m/K) Σ_(open) −log₂ p̂ = E_σ L_σ(A | Q)`, the order-averaged joint code (the comparison record, §3.2).
/// Returns each state's classes, open sites and `(|S_s|, K_s)`; the foil's states are the same draws beside the next
/// problem's question.
pub(super) fn joint_states(void: usize, q: &[usize], a: &[usize], seed: u64, key: u64) -> Vec<(Vec<usize>, Vec<bool>, (u64, u64))> {
    let mut classes: Vec<usize> = q.iter().chain(a).copied().collect();
    classes.push(void);
    let m = a.len() + 1;
    let mut rank: Vec<usize> = (0..m).collect();
    rank.sort_by_key(|&j| (mix(seed, JOINT_KEY ^ key ^ ((j as u64 + 1) << 20)), j));
    (0..CONTEXT)
        .filter_map(|s| {
            let (lo, hi) = (1 + s * m / CONTEXT, 1 + (s + 1) * m / CONTEXT);
            (hi > lo).then(|| {
                let k = lo + (mix(seed, JOINT_KEY ^ key ^ (s as u64 + 1)) % (hi - lo) as u64) as usize;
                let mut open = vec![false; classes.len()];
                for &j in &rank[..k] {
                    open[q.len() + j] = true;
                }
                (classes.clone(), open, ((hi - lo) as u64, k as u64))
            })
        })
        .collect()
}

/// The joint read's key space (§16.23), apart from every other draw of the run.
const JOINT_KEY: u64 = 9 << 58;

/// [measurement; agent-inferred, November 2, §16.23] **The question's information, read by the joint code** (#602): for
/// each held problem, its answer's order-averaged joint code beside its own question and beside the next problem's
/// (the same states, [`joint_states`]), each state's code weighed `|S_s|/K_s`, every term released at the code's grain
/// `2^(−20)` (to the nearest, half away from zero) a site; the information is the foil's code less the own. Printed as
/// bits a byte over every held answer site (`FIELD_JOINT`), its series by the answer's quarters (`FIELD_JOINT_SERIES`,
/// a site in the quarter its place falls in), and the quartiles over the problems of each one's information a byte;
/// each problem's series by site, in millibits, goes to `rows` (the run's private `JOINT.tsv`). A reading only: no
/// decision of the run reads it. It is not screened by the answer's own restatements, so it contains the question's
/// information about the plan of a solution as well as about its names.
fn joint_read(field: &Field, codec: &FieldCodec, problems: &Problems, seed: u64, realization: &mut dyn FieldRealization, lap: i64, rows: &mut std::fs::File) -> Result<()> {
    let started = std::time::Instant::now();
    let n = problems.len();
    // (problem, foil, weight, classes, open)
    let mut states: Vec<(usize, bool, (u64, u64), Vec<usize>, Vec<bool>)> = Vec::new();
    for i in 0..n {
        let ((q, a, _), (fq, _, _)) = (&problems[i], &problems[(i + 1) % n]);
        for (foil, question) in [(false, q), (true, fq)] {
            for (c, u, w) in joint_states(codec.void(), question, a, seed, i as u64) {
                states.push((i, foil, w, c, u));
            }
        }
    }
    // Each held problem's per-site terms, own and foil, on 2^(−20) bits.
    let mut own: Vec<Vec<i64>> = problems.iter().map(|(_, a, _)| vec![0i64; a.len() + 1]).collect();
    let mut foil: Vec<Vec<i64>> = own.clone();
    // [measurement; theory, November 9 23:30] The own code by the share of the answer already written when a place is coded,
    // `(m − K)/m` of a state with `K` of its `m` places open, in tenths: each tenth's code on 2^(−20) bits and its places
    // (each state's `|S_s|/K_s` a coded place).
    let mut tenths = [(0i128, 0i128); 10];
    for chunk in states.chunks(64) {
        let views: Vec<Region> = chunk.iter().map(|(_, _, _, c, u)| Region { classes: c, unresolved: u, faces: &[], locked: &[], echo: &[], domain: None, port: None }).collect();
        let faces = realization.read_faces(field, &views).map_err(|e| e.to_string())?;
        for ((i, is_foil, (size, k), c, _), faces) in chunk.iter().zip(faces) {
            let q_len = c.len() - problems[*i].1.len() - 1;
            let terms = if *is_foil { &mut foil[*i] } else { &mut own[*i] };
            let m = (c.len() - q_len) as u64;
            let tenth = &mut tenths[(10 * (m - k) / m).min(9) as usize];
            let mut coded = 0i128;
            for (t, face) in faces.iter().enumerate() {
                if let Some(face) = face {
                    let x = face.code(c[t]) as i128 * *size as i128;
                    let k = *k as i128;
                    let term = (if x >= 0 { (x + k / 2) / k } else { -((-x + k / 2) / k) }) as i64;
                    terms[t - q_len] += term;
                    if !is_foil {
                        tenth.0 += term as i128;
                    }
                    coded += 1;
                }
            }
            if !is_foil {
                tenth.1 += (coded * *size as i128 + *k as i128 / 2) / *k as i128;
            }
        }
    }
    let (mut own_sum, mut foil_sum, mut sites) = (0i128, 0i128, 0i128);
    let mut quarters = [(0i128, 0i128); 4];
    let mut per: Vec<i64> = Vec::with_capacity(n);
    for i in 0..n {
        let m = own[i].len();
        let (o, f): (i64, i64) = (own[i].iter().sum(), foil[i].iter().sum());
        own_sum += o as i128;
        foil_sum += f as i128;
        sites += m as i128;
        for j in 0..m {
            let quarter = &mut quarters[4 * j / m];
            quarter.0 += (foil[i][j] - own[i][j]) as i128;
            quarter.1 += 1;
        }
        // The problem's information a byte, on 2^(−20) bits.
        per.push(((f - o) as i128 / m as i128) as i64);
        let series: Vec<String> = (0..m).map(|j| ((foil[i][j] - own[i][j]) as i128 * 1000 / (1 << 20)).to_string()).collect();
        row(rows, &format!("{lap}\t{i}\t{m}\t{}\t{}\t{}\t{}\n", micro_bits(o as i128, 1), micro_bits(f as i128, 1), micro_bits((f - o) as i128, 1), series.join(",")))?;
    }
    println!(
        "FIELD_JOINT lap={lap} answers={n} sites={sites} own_bits_a_byte={} foil_bits_a_byte={} information_bits_a_byte={} ms={}",
        micro_bits(own_sum, sites),
        micro_bits(foil_sum, sites),
        micro_bits(foil_sum - own_sum, sites),
        started.elapsed().as_millis()
    );
    // [measurement; agent-inferred, November 4, the tower record's D5] The same code in nats (the comparison's natural unit,
    // `ln 2` its navigator's face on `2^(−30)`), as a density on two partitions: a place, and a word crossing (a word's first
    // byte, the receiver's packet of content: a word's first letter carries most of its information and its spelling little).
    let words: i128 = problems.iter().map(|(_, a, _)| word_crossings(&codec.decode(a)) as i128).sum();
    let ln2 = field.ln2();
    println!(
        "FIELD_JOINT_NATS lap={lap} places={sites} words={words} own_nats_a_place={} foil_nats_a_place={} information_nats_a_place={} own_nats_a_word={} information_nats_a_word={}",
        micro_nats(own_sum * ln2, sites),
        micro_nats(foil_sum * ln2, sites),
        micro_nats((foil_sum - own_sum) * ln2, sites),
        micro_nats(own_sum * ln2, words),
        micro_nats((foil_sum - own_sum) * ln2, words)
    );
    for (b, &(code, places)) in tenths.iter().enumerate() {
        println!("FIELD_JOINT_WRITTEN lap={lap} written=0.{b}-{} places={places} own_nats_a_place={}", if b == 9 { "1".to_string() } else { format!("0.{}", b + 1) }, micro_nats(code * ln2, places));
    }
    per.sort_unstable();
    let q = |f: usize| per.get((f * per.len()) / 4).copied().unwrap_or(0) as i128;
    println!(
        "FIELD_JOINT_SERIES lap={lap} by_quarter_bits_a_byte={} problems_quartiles_bits_a_byte={}/{}/{}",
        quarters.iter().map(|&(s, c)| micro_bits(s, c)).collect::<Vec<_>>().join("/"),
        micro_bits(q(1), 1),
        micro_bits(q(2), 1),
        micro_bits(q(3), 1)
    );
    Ok(())
}

/// The parts of [`context_regions`]: a site read with the `CONTEXT − 1` sites on each side of it
/// resolved (agent-inferred: the reach the bytes' own table needs to code a site at its
/// four-byte-context rate, from either side).
pub(super) const CONTEXT: usize = 4;

/// [agent-inferred, November 1] **The withheld problems' regions, read with their neighbours**
/// ([`context_regions`]): each problem's question, its answer and a keyed void tail (the draws from
/// [`UNSEEN_DRAW`] on), so every lap reads the same regions over the same sites. Why not the
/// release's states at `ρ`: their resolved sites are the first in the field's own news order, so as
/// the field learns a site it leaves the compared set, and a growth that compares code a site
/// across laps would read a different set of sites each lap. Why not the release's opening (the
/// third reading): its code sits near the bytes' table whatever the field learns of an answer's
/// bytes, so the growth compared readings that could not fall.
pub(super) fn unseen_regions(codec: &FieldCodec, problems: &Problems, unseen: &[usize], seed: u64) -> Vec<(Vec<usize>, Vec<bool>)> {
    unseen_regions_with(codec.answer, codec.void(), problems, unseen, seed)
}

fn unseen_regions_with(answer: usize, void: usize, problems: &Problems, unseen: &[usize], seed: u64) -> Vec<(Vec<usize>, Vec<bool>)> {
    let mut draw = UNSEEN_DRAW;
    unseen
        .iter()
        .flat_map(|&i| {
            let (q, a, _) = &problems[i];
            draw += 1;
            let length = q.len() + a.len() + tail(seed, draw, answer - a.len());
            context_regions(void, q, a, length)
        })
        .collect()
}

/// The withheld problems read with their neighbours ([`unseen_regions`]): the step the learner
/// holds is read on them, and their code under the material that stands is returned with its
/// sites and the step's read.
fn unseen_read(learner: &mut FieldLearner, codec: &FieldCodec, problems: &Problems, unseen: &[usize], seed: u64, realization: &mut dyn FieldRealization) -> Result<(i64, usize, Option<FieldNext>)> {
    let regions = unseen_regions(codec, problems, unseen, seed);
    let views: Vec<Region> = regions.iter().map(|(c, u)| Region { classes: c, unresolved: u, faces: &[], locked: &[], echo: &[], domain: None, port: None }).collect();
    let (faces, next) = learner.read_step_on(&views, realization).map_err(|e| e.to_string())?;
    let (mut code, mut sites) = (0i64, 0usize);
    for (faces, region) in faces.iter().zip(&views) {
        for (face, &class) in faces.iter().zip(region.classes) {
            if let Some(face) = face {
                code += face.code(class);
                sites += 1;
            }
        }
    }
    Ok((code, sites, next))
}

/// [agent-inferred, November 1] **The held-out read on `2^(−20)` bits to six decimals**
/// (millionths): `[opening, context, foil]`, each a code over its sites ([`held_out`]), and the question's
/// effect, the foil's rate less the context's (signed), beside the context's. Why six decimals
/// (reading 9): the held answer coded 5.629 bits a byte beside its own question and 5.629 beside a
/// foil's, equal at the printed thousandth, so a question effect below a thousandth of a bit could
/// not be seen; the effect is the difference of the two rates and is printed as such, not left to
/// the reader's subtraction of two rounded numbers. One formatter for every `FIELD_HELD` line.
fn held_text(held: &[(i64, usize); 3]) -> String {
    let rate = |k: usize| micro_bits(held[k].0 as i128, held[k].1 as i128);
    let effect = match (held[2], held[1]) {
        ((_, 0), _) | (_, (_, 0)) => "-".to_string(),
        ((a, na), (b, nb)) => micro_bits(a as i128 * nb as i128 - b as i128 * na as i128, na as i128 * nb as i128),
    };
    format!("answer={} classes={} context={} context_classes={} foil={} question={effect}", rate(0), held[0].1, rate(1), held[1].1, rate(2))
}

fn bits(code: i64, n: usize) -> String {
    if n == 0 {
        return "-".into();
    }
    // The reading on 2^(−20) bits as a decimal to three places.
    let thousandths = (code as i128 * 1000 + ((n as i128) << 19)) / ((n as i128) << 20);
    format!("{}.{:03}", thousandths / 1000, thousandths % 1000)
}

/// A rate `num / (sites · 2^20)` bits as a signed decimal to six places, to the nearest millionth
/// (`-` where no site).
/// A count of nats on `2^(−50)` (a code on `2^(−20)` bits times `ln 2` on `2^(−30)`) over `n`, as a decimal to six places.
fn micro_nats(num: i128, n: i128) -> String {
    micro_bits(num >> 30, n)
}

/// The word crossings of a text: its bytes that begin a word (a byte past a space or a line's end, or the first).
fn word_crossings(text: &[u8]) -> usize {
    (0..text.len()).filter(|&i| !text[i].is_ascii_whitespace() && (i == 0 || text[i - 1].is_ascii_whitespace())).count()
}

fn micro_bits(num: i128, sites: i128) -> String {
    if sites == 0 {
        return "-".into();
    }
    let den = sites << 20;
    let scaled = num * 1_000_000;
    let millionths = if scaled >= 0 { (scaled + den / 2) / den } else { -((-scaled + den / 2) / den) };
    format!("{}{}.{:06}", if millionths < 0 { "-" } else { "" }, millionths.abs() / 1_000_000, millionths.abs() % 1_000_000)
}

fn next_text(next: Option<FieldNext>) -> String {
    match next {
        Some(n) => format!("next_change={} next_halvings={} next_refused={}", n.change, n.halvings, n.refused),
        None => "next=-".into(),
    }
}

/// `train-field UNITS UNITS_SHA TRAIN TRAIN_SHA DEV DEV_SHA KEYS KEYS_SHA D H n STILL f K SECTION
/// LAPS RATE LAP_MS GROWN_LAP_MS STOP_MS OUT [FROM FROM_SHA]`: the field founded on the keys (or continued from a rested
/// learner), trained over `LAPS` laps of the training problems in sections of `SECTION` regions,
/// each lap's sections in a keyed order. As many training problems as `DEV` holds are withheld
/// ([`sections_of`]); after each lap the step the lap's last section deposited is read on them, the
/// learner rests as `OUT/STATE.lap`, and the held-out problems are read (a reading only). The
/// codec is founded on the training passage and written as `OUT/CODEC`. After a lap whose withheld
/// problems code no fewer bits a site than they did after the lap before, the body grows by copies
/// (`FieldLearner::widened`) before the next.
///
/// [agent-inferred, November 1] **The run's bounds are its own.** `LAP_MS` bounds a lap before any
/// growth and `GROWN_LAP_MS` one after (the projections' upper ends), `STOP_MS` the run from its
/// start. At the first section that ends past either, the learner rests as `OUT/STATE.stopped`
/// and the run stops, its partial evidence reported as incomplete (`FIELD_STOPPED`). Why: the
/// second reading's bound was an outside watcher that stopped the trainer inside its first lap,
/// so 336 sections of learning left no state and nothing could be released or read.
///
/// [agent-inferred, November 1] **A lap starts only while the time left holds its bound.** `LAPS`
/// is a count bound; before each lap after the first, the run continues only if the elapsed time
/// plus that lap's projected bound stays within `STOP_MS`, and otherwise it ends at the last
/// rested lap (`FIELD_LAPS_HELD`). The body grows at most once in a run, because the run carries
/// only the two projections (before and after one growth); a second growth is held and the laps
/// go on at that width (`FIELD_GROW_HELD`, [`growth`]), and the keys are checked to cover that one growth before any
/// lap runs. Why: the fifth reading sized its laps from its time, so `LAPS` and the time bound
/// were the same number read twice, and a lap that could not finish would only have stopped the run
/// with its partial step.
/// [agent-inferred, November 6] **The declared clocks**, read alike by training, its parity and every reading of a state, so a
/// state is read under the clock it was trained on: `FIELD_CLOCK_PER_BLANK` (`Field::per_blank_clock`) and `FIELD_CLOCK_BARE`
/// (`Field::bare_stretch`, the unified-theory reading of 10:31: past the last arrival a silent place runs at the bare rate).
pub(super) fn declared_clocks(field: &mut Field) {
    field.per_blank_clock = std::env::var_os("FIELD_CLOCK_PER_BLANK").is_some();
    field.bare_stretch = std::env::var_os("FIELD_CLOCK_BARE").is_some();
}

pub(super) fn train(args: &[String], realization: &mut dyn FieldRealization) -> Result<()> {
    if !(args.len() == 22 || args.len() == 24) {
        return Err("train-field UNITS UNITS_SHA TRAIN TRAIN_SHA DEV DEV_SHA KEYS KEYS_SHA D H n STILL f K SECTION LAPS RATE LAP_MS GROWN_LAP_MS STOP_MS OUT [FROM FROM_SHA]".into());
    }
    let started = std::time::Instant::now();
    let units = units_of(&args[1], &args[2])?;
    let train_text = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let dev_text = pinned_read(&args[5], &args[6], READ_BUDGET as usize)?;
    let keys = pinned_read(&args[7], &args[8], READ_BUDGET as usize)?;
    let (width, heads, modes, still, contacts, ticks) = (positive(&args[9])?, positive(&args[10])?, positive(&args[11])?, count(&args[12])?, positive(&args[13])?, positive(&args[14])?);
    let (section, laps, rate) = (positive(&args[15])?, count(&args[16])?, count(&args[17])? as u32);
    let (lap_ms, grown_lap_ms, stop_ms) = (positive(&args[18])? as u128, positive(&args[19])? as u128, positive(&args[20])? as u128);
    let out = Path::new(&args[21]);
    std::fs::create_dir(out)?;
    let train_problems = problems_of(&train_text);
    let dev_problems = problems_of(&dev_text);
    let codec = FieldCodec::found(units, &train_problems)?;
    write_new(&out.join("CODEC"), codec.to_text().as_bytes())?;
    let encode = |problems: &[(Vec<u8>, Vec<u8>)]| -> Result<Problems> {
        problems.par_iter().map(|(q, a)| Ok((codec.encode(&question_text(q)).map_err(|e| e.to_string())?, codec.encode(a).map_err(|e| e.to_string())?, a.len()))).collect::<std::result::Result<Vec<_>, String>>().map_err(|e| e.into())
    };
    let train_set = encode(&train_problems)?;
    let dev_set: Problems = encode(&dev_problems)?.into_iter().filter(|(_, a, _)| a.len() < codec.answer).collect();
    // The reach: the longest region the run reads, a question and the codec's answer extent (a
    // training region's tail never runs past it, and the release opens there).
    let reach = train_set.iter().chain(&dev_set).map(|(q, _, _)| q.len() + codec.answer).max().unwrap_or(codec.answer);
    let mut learner = match args.get(22..24) {
        Some([path, sha]) => FieldLearner::from_text(std::str::from_utf8(&pinned_read(path, sha, STATE_BUDGET)?)?).map_err(|e| e.to_string())?,
        _ => {
            // The founding's heads are its ring sets; the reach is the passages'.
            let declaration = FieldDeclaration { alphabet: codec.alphabet(), width, heads, modes, still, contacts, ticks, frames: heads, reach, lanes: 1, depth: 0, energy: false };
            let mut field = Field::found(declaration, &keys).map_err(|e| e.to_string())?;
            // [measurement; agent-inferred, November 3, §16.31] `FIELD_FOUND_RETURNS` (`returns`, or `lift` for the readout's
            // lift as well): the founding's zero families drawn instead, uniform on `±√(3/fan-in)` from a block of the key
            // file before its last word, a declared read of whether their zero founding slows the field's first laps.
            if let Ok(which) = std::env::var("FIELD_FOUND_RETURNS") {
                let l = field.layout().clone();
                let (dw, m2, f) = (declaration.width, 2 * declaration.complex(), declaration.contacts);
                let mut families = vec![(l.out, dw * m2, m2), (l.w, dw * f, f)];
                if which == "lift" {
                    families.push((l.read, dw * dw, dw));
                }
                let total: usize = families.iter().map(|&(_, len, _)| len).sum();
                let block = keys.len().checked_sub(8 + 4 * total).ok_or("a key file too short for the returns' draws")?;
                let mut cursor = block;
                for (start, len, fan) in families {
                    let (num, den) = (((3u128) << 32).isqrt(), ((fan as u128) << 32).isqrt());
                    for k in 0..len {
                        let word = &keys[cursor..cursor + 4];
                        cursor += 4;
                        let draw = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) as i128;
                        field.theta[start + k] = ((draw * ((num << holonics::hnn::tower::MATERIAL_BITS) / den) as i128) >> 31) as i32;
                    }
                }
                println!("FIELD_FOUND_RETURNS which={which} entries={total}");
            }
            FieldLearner::new(field, rate)
        }
    };
    // [measurement; agent-inferred, November 6, the unified-theory reading of 02:38] `FIELD_CLOCK_PER_BLANK`: every silent place
    // runs its own per-blank rate past the last arrival too (`Field::per_blank_clock`), the clock alone set against §16.47's
    // one-rate stretch, a declared comparison.
    declared_clocks(&mut learner.field);
    if learner.field.declaration.alphabet != codec.alphabet() {
        return Err("a continued learner whose alphabet is not the codec's".into());
    }
    if learner.field.declaration.reach < reach {
        return Err(format!("a continued learner whose reach ({}) is shorter than the passages' regions ({reach})", learner.field.declaration.reach).into());
    }
    // The masks and tails read the key file's last word; the one growth this run can make (its
    // projections are of the declaration and of it grown once) reads the key file's front past
    // the founding, and must not reach it.
    let seed = u64::from_be_bytes(keys.get(keys.len().saturating_sub(8)..).filter(|w| w.len() == 8).ok_or("a key file of fewer than eight bytes")?.try_into()?);
    if laps > 1 {
        let drawn = learner.drawn + 4 * learner.field.declaration.growth_draws(2);
        if drawn + 8 > keys.len() {
            return Err(format!("a key file of {} bytes, and a growth would read {drawn} before its last word", keys.len()).into());
        }
    }
    // Sections of problems of like length, and the withheld problems (as many as the held read's).
    let (sections, unseen) = sections_of(&train_set, section, dev_set.len(), seed);
    println!(
        "FIELD_DECLARATION alphabet={} width={width} heads={heads} modes={modes} still={still} contacts={contacts} ticks={ticks} frames={} reach={} section={section} rate={} answer={} train={} withheld={} dev={} sections={} laps_read={} material={}",
        codec.alphabet(),
        learner.field.declaration.frames,
        learner.field.declaration.reach,
        learner.rate_bits,
        codec.answer,
        train_set.len() - unseen.len(),
        unseen.len(),
        dev_set.len(),
        sections.len(),
        learner.laps,
        learner.field.theta.len()
    );
    // [measurement; agent-inferred, November 3, §16.28] `FIELD_WIDEN_FIRST` (a factor past one, two where none is given): a
    // continued learner widened by copies before its first lap (the growth law's operation, read here without its trigger),
    // so a run reads whether the trained body's width bounds its fall; the run then makes no further growth.
    let widen_factor = std::env::var("FIELD_WIDEN_FIRST").ok().map(|v| v.parse::<usize>().ok().filter(|&f| f > 1).unwrap_or(2));
    let widened_first = widen_factor.is_some() && args.len() == 24;
    // [agent-inferred, November 3, the tower record, D3] `FIELD_SCALE_FIRST=P`: a continued learner grown in scale before its
    // first lap (packets of `P` sites after half its ticks; the packets' field as wide as the fine one, twice its heads, half
    // of them still, as many contacts and ticks, on the packets' reach), so a run reads the tower against the field alone.
    let scaled_first = std::env::var("FIELD_SCALE_FIRST").ok().and_then(|v| v.parse::<usize>().ok()).filter(|&p| p > 1 && args.len() == 24);
    if let Some(period) = scaled_first {
        let d = learner.field.declaration;
        let coarse = FieldDeclaration { alphabet: 2, heads: 2 * d.heads, frames: 2 * d.heads, still: d.heads, reach: d.reach.div_ceil(period), ..d };
        learner = learner.scaled_up(period, (d.ticks / 2).max(1), coarse, &keys).map_err(|e| e.to_string())?;
        println!("FIELD_SCALE lap=-1 period={period} split={} coarse_width={} coarse_heads={} material={} ms={}", (d.ticks / 2).max(1), coarse.width, coarse.heads, learner.field.material_len(), started.elapsed().as_millis());
    }
    // [measurement; agent-inferred, November 3, §16.28] `FIELD_RATE_BITS`: a continued learner's step rate `2^(−k)` read at
    // `k` for this run, so a run reads whether the step's size bounds the trained field's fall.
    if let Some(k) = std::env::var("FIELD_RATE_BITS").ok().and_then(|v| v.parse::<u32>().ok()).filter(|_| args.len() == 24) {
        learner.rate_bits = k;
        println!("FIELD_RATE rate={k}");
    }
    // [measurement; agent-inferred, November 3, §16.30] `FIELD_HELD_READ`: each step held and read on the next section before
    // it stands (the tower's acceptance 77, [`FieldLearner::read_held`]), a declared comparison with the field's law.
    if std::env::var_os("FIELD_HELD_READ").is_some() {
        learner.read_held = true;
        println!("FIELD_HELD_READ");
    }
    // [agent-inferred, November 4, §16.41] `FIELD_STEP_TRANSFER`: the step's size follows its price on the sections it was not
    // fit on ([`step_transfer`]), one octave a lap at most; a declared comparison with the fixed rate.
    let transfer_law = std::env::var_os("FIELD_STEP_TRANSFER").is_some();
    if transfer_law {
        println!("FIELD_STEP_TRANSFER rate={}", learner.rate_bits);
    }
    if let Some(factor) = widen_factor.filter(|_| widened_first) {
        learner = learner.widened(factor, &keys).map_err(|e| e.to_string())?;
        let d = learner.field.declaration;
        println!("FIELD_GROW lap=-1 width={} heads={} contacts={} rate={} material={} ms={}", d.width, d.heads, d.contacts, learner.rate_bits, learner.field.theta.len(), started.elapsed().as_millis());
    }
    // [agent-inferred, November 4, §16.40] `FIELD_LANE_FIRST`: a continued learner grown by one fresh lane before its first
    // lap ([`FieldLearner::laned`]), so a run reads a lane against the same state continued alone; the run then makes no
    // growth by copies.
    let laned_first = std::env::var_os("FIELD_LANE_FIRST").is_some() && args.len() == 24;
    if laned_first {
        learner = learner.laned(&keys).map_err(|e| e.to_string())?;
        let d = learner.field.declaration;
        println!("FIELD_LANE lap=-1 width={} lanes={} rate={} material={} ms={}", d.width, d.lanes, learner.rate_bits, learner.field.theta.len(), started.elapsed().as_millis());
    }
    let held = held_out(&learner.field, &codec, &dev_set, realization)?;
    println!("FIELD_HELD lap=-1 {} ms={}", held_text(&held), started.elapsed().as_millis());
    held_rows_text(&learner.field, &codec, &dev_set, realization, -1)?;
    let mut joint_rows = rows_file(&out.join("JOINT.tsv"), "lap\tproblem\tanswer_sites\town_bits\tfoil_bits\tinformation_bits\tinformation_millibits_by_site\n")?;
    joint_read(&learner.field, &codec, &dev_set, seed, realization, -1, &mut joint_rows)?;
    // The withheld problems' code after the lap before (at the opening, before any lap).
    let (code, sites, next) = unseen_read(&mut learner, &codec, &train_set, &unseen, seed, realization)?;
    println!("FIELD_UNSEEN lap=-1 code={} sites={sites} {} ms={}", bits(code, sites), next_text(next), started.elapsed().as_millis());
    let mut previous = (code, sites);
    let mut grown = widened_first || laned_first;
    let mut fallen = false;
    // [the unified-theory reading of November 6, 08:54] The external price `p_ext` of the step the last section stood at full
    // size, which the next section's transfer pairs with.
    let mut prior: Option<i128> = None;
    for lap in 0..laps {
        // A lap starts only where the time left holds its bound: no lap is begun that its own
        // projection says could pass the run's deadline.
        let bound = if grown { grown_lap_ms } else { lap_ms };
        let elapsed = started.elapsed().as_millis();
        if lap > 0 && elapsed + bound > stop_ms {
            println!("FIELD_LAPS_HELD lap={lap} reason=time left={} bound={bound} ms={elapsed}", stop_ms.saturating_sub(elapsed));
            break;
        }
        // The learner's own lap count keys the walk and the draws: a continued run moves on.
        let read = learner.laps;
        let mut draw = read * train_set.len() as u64;
        let mut read_after = 0usize;
        let (mut code_before, mut code_after, mut sites, mut deposited, mut halvings, mut held_down, mut refused) = (0i64, 0i64, 0usize, 0usize, 0u64, 0usize, 0usize);
        // The lap's transfers `Σ t`, the external prices `Σ p_ext` they pair with and the curvatures `Σ (t − p_ext)`, over the
        // steps that stood at full size.
        let (mut transfers, mut externals, mut curvatures, mut priced) = (0i128, 0i128, 0i128, 0usize);
        let lap_start = std::time::Instant::now();
        let paths = paths_of(seed, read, &sections);
        for (n, &s) in walk(seed, read, sections.len()).iter().enumerate() {
            let section_start = std::time::Instant::now();
            let (regions, next) = section_regions(&codec, &train_set, &sections[s], &paths[s], seed, &mut draw, &mut learner, realization)?;
            // [measurement; agent-inferred, November 5] The section's time by phase (Brandon, November 5: where the time goes):
            // its regions formed with the held step read on them, then its deposit (with any halving's rereads).
            let regions_ms = section_start.elapsed().as_millis();
            let length = regions.iter().map(|r| r.classes.len()).max().unwrap_or(0);
            let views = views_of(&regions);
            // [measurement; agent-inferred, November 2] **The far pairs' share of the contact covector** (§16.20): on the
            // section's own regions before its step, at the run's sections 1, 2, 4, 8 and 16 and at each lap's first,
            // `Σ |δs|` near and far per head (`Field::covector_shares`, through the realization). Zero at the founding,
            // where the readout and the current's return stand at zero.
            let run_section = lap * sections.len() + n + 1;
            if n == 0 || (run_section <= 16 && run_section.is_power_of_two()) {
                let read_start = std::time::Instant::now();
                let shares = realization.read_covector_shares(&learner.field, &views).map_err(|e| e.to_string())?;
                for (head, [near, far]) in shares.iter().enumerate() {
                    let far_share = if near + far == 0 { 0 } else { far * 1_000_000 / (near + far) };
                    println!("FIELD_COVECTOR_SHARE lap={lap} section={run_section} head={head} near={near} far={far} far_share={far_share} ms={}", read_start.elapsed().as_millis());
                }
            }
            let deposit_start = std::time::Instant::now();
            let receipt = learner.section_realized(&views, realization).map_err(|e| e.to_string())?;
            let deposit_ms = deposit_start.elapsed().as_millis();
            let receipt = FieldReceipt { next: next.or(receipt.next), ..receipt };
            code_before += receipt.code_before;
            if let Some(after) = receipt.code_after {
                (code_after, read_after) = (code_after + after, read_after + receipt.sites);
            }
            sites += receipt.sites;
            deposited += usize::from(receipt.deposited);
            halvings += receipt.halvings as u64;
            if let Some(next) = receipt.next {
                held_down += usize::from(next.halvings > 0 && !next.refused);
                refused += usize::from(next.refused);
            }
            // [measurement; §16.41] The step's parabola: its first-order change and the change read at its full size; the step
            // before priced on this section ([`FieldReceipt::transfer`]); in millionths of a bit a site (signed), and the rate
            // the step was taken at.
            let micro = |c: i64| if receipt.sites == 0 { 0 } else { (c as i128 * 1_000_000) / ((receipt.sites as i128) << 20) };
            let rate_taken = learner.rate_bits;
            println!(
                "FIELD_SECTION lap={lap} n={n} sites={} before={} after={} halvings={} deposited={} {} predicted_micro={} change_micro={} transfer_micro={} external_micro={} curvature_micro={} rate={rate_taken} length={length} regions_ms={regions_ms} deposit_ms={deposit_ms} ms={}",
                receipt.sites,
                bits(receipt.code_before, receipt.sites),
                receipt.code_after.map_or("-".to_string(), |a| bits(a, receipt.sites)),
                receipt.halvings,
                receipt.deposited,
                next_text(receipt.next),
                receipt.predicted.map_or("-".to_string(), |p| micro(p).to_string()),
                receipt.change.map_or("-".to_string(), |c| micro(c).to_string()),
                receipt.transfer.map_or("-".to_string(), |t| micro(t).to_string()),
                receipt.external.map_or("-".to_string(), |e| micro(e).to_string()),
                receipt.transfer.zip(prior).map_or("-".to_string(), |(t, e)| if receipt.sites == 0 { "0".to_string() } else { ((t as i128 - e) * 1_000_000 / ((receipt.sites as i128) << 20)).to_string() }),
                section_start.elapsed().as_millis()
            );
            if let (Some(t), Some(e)) = (receipt.transfer, prior) {
                (transfers, externals, curvatures, priced) = (transfers + t as i128, externals + e, curvatures + (t as i128 - e), priced + 1);
            }
            prior = receipt.external.filter(|_| receipt.deposited && receipt.halvings == 0).map(i128::from);
            let (over_lap, over_run) = (lap_start.elapsed().as_millis() > if grown { grown_lap_ms } else { lap_ms }, started.elapsed().as_millis() > stop_ms);
            if over_lap || over_run {
                // The pending step is judged on the withheld problems as a lap's last step is, so
                // the stopped state carries no step its next regions have not read.
                let (code, unseen_sites, next) = unseen_read(&mut learner, &codec, &train_set, &unseen, seed, realization)?;
                write_new(&out.join("STATE.stopped"), learner.to_text().as_bytes())?;
                println!(
                    "FIELD_STOPPED lap={lap} sections={}/{} reason={} sites={sites} before={} after={} deposited={deposited} halvings={halvings} next_halved={held_down} next_refused={refused} lap_ms={} ms={}",
                    n + 1,
                    sections.len(),
                    if over_lap { "lap" } else { "run" },
                    bits(code_before, sites),
                    if read_after == 0 { "-".to_string() } else { bits(code_after, read_after) },
                    lap_start.elapsed().as_millis(),
                    started.elapsed().as_millis()
                );
                println!("FIELD_UNSEEN lap={lap} stopped code={} sites={unseen_sites} {} ms={}", bits(code, unseen_sites), next_text(next), started.elapsed().as_millis());
                return Ok(());
            }
        }
        learner.laps += 1;
        // The lap's last step is read on the withheld problems, which it was not fit on.
        let (code, unseen_sites, next) = unseen_read(&mut learner, &codec, &train_set, &unseen, seed, realization)?;
        // [measurement; §16.41; the unified-theory reading of November 6, 08:54] **The lap's line search**: along the lap's steps
        // the joint code's slope at the step is `Σ t` and its curvature `Σ (t − p_ext)`, so its least is `μ* = −Σp_ext / Σ(t −
        // p_ext)`, exactly `step_transfer(2Σt, Σ(t − p_ext))`; in thousandths of the step where `Σ(t − p_ext) > 0`, and the octave
        // it reads. The rate moves before the state is written, so a segment's cut keeps the move.
        let octave = step_transfer(2 * transfers, curvatures);
        let least = if curvatures > 0 { -externals * 1000 / curvatures } else { 0 };
        println!("FIELD_STEP_PRICE lap={lap} priced={priced} transfer={transfers} external={externals} curvature={curvatures} least_milli={least} octave={octave} rate={}", learner.rate_bits);
        // [agent-inferred, November 6, 10:10] `FIELD_STEP_HELD` holds the rate (the price is printed, never acted on): the
        // external price `p_ext` is the step before priced after it stood (`deposit_step(m_(s−1), v_(s−1))` is that step), so
        // `Σ(t − p_ext)` telescopes to the lap's last transfer less its first and no curvature is read from the pass (seg2's
        // lap 7: 13,426,496 against `Σt` 45,000,785,396); acting on it is the transfer's sign alone.
        if transfer_law && priced > 0 && std::env::var_os("FIELD_STEP_HELD").is_none() {
            learner.rate_bits = learner.rate_bits.saturating_add_signed(-octave).max(1);
        }
        write_new(&out.join(format!("STATE.{lap}")), learner.to_text().as_bytes())?;
        println!(
            "FIELD_LAP lap={lap} read={} sites={sites} before={} after={} deposited={deposited}/{} halvings={halvings} next_halved={held_down} next_refused={refused} ms={}",
            learner.laps,
            bits(code_before, sites),
            if read_after == 0 { "-".to_string() } else { bits(code_after, read_after) },
            sections.len(),
            lap_start.elapsed().as_millis()
        );
        println!("FIELD_UNSEEN lap={lap} code={} sites={unseen_sites} {} ms={}", bits(code, unseen_sites), next_text(next), started.elapsed().as_millis());
        // [measurement; agent-inferred, November 3, §16.31] `FIELD_STEP_COHERENCE`: each family's `Σ|m| / Σ√v` in millionths
        // ([`FieldLearner::step_coherence`]) after the lap, which families' steps are driven and which are noise.
        if std::env::var_os("FIELD_STEP_COHERENCE").is_some() {
            const NAMES: [&str; 26] = ["enc", "before", "after", "q", "q_bias", "v", "v_bias", "out", "out_bias", "a", "a_bias", "b", "b_bias", "w", "w_bias", "read", "read_bias", "moment_before", "moment_after", "temper", "probe", "probe_bias", "pace", "moment_face", "moment_face_bias", "lift_bias"];
            let text: Vec<String> = learner.step_coherence().iter().enumerate().map(|(k, &(_, m, v))| format!("{}={}", NAMES.get(k).copied().unwrap_or("?"), if v == 0 { 0 } else { m * 1_000_000 / v })).collect();
            println!("FIELD_STEP_COHERENCE lap={lap} {}", text.join(" "));
        }
        let held = held_out(&learner.field, &codec, &dev_set, realization)?;
        println!("FIELD_HELD lap={lap} {} ms={}", held_text(&held), started.elapsed().as_millis());
        held_rows_text(&learner.field, &codec, &dev_set, realization, lap as i64)?;
        joint_read(&learner.field, &codec, &dev_set, seed, realization, lap as i64, &mut joint_rows)?;
        // [retired, November 2, §16.23] The early stop on the context read's question effect: that read sees the question
        // only where the answer does not restate itself (a ceiling near 0.18 bits a byte on GSM8K, nearly all of it
        // names), so it read the copier's channel (the comparison record, §2.2). The context read stays as a reading of
        // completion; the question's information is the joint read's.
        // [agent-inferred, November 1] The width is the trained body's (growth by copies, the
        // tower's law): when a lap leaves the withheld problems coding no fewer bits a site than
        // the lap before left them, the body has spent its width and grows by two before the next.
        // [agent-inferred, November 2] Only once the withheld code has fallen at this width: a lap
        // that raises it from where the width began has not spent the width but harmed it, and
        // growing then copies the harm (the crib run of November 2 grew at lap 0 after its first lap
        // raised the code from 5.459 to 5.912 bits, and its grown body refused 240 of 248 steps).
        let fell = (code as i128) * (previous.1 as i128) < (previous.0 as i128) * (unseen_sites as i128);
        fallen |= fell;
        // [measurement; agent-inferred, November 3] `FIELD_GROWTH_HELD`: every growth held, a declared comparison at one width
        // (a tower's growth by copies is always held: it grows by its levels' lanes).
        let held = std::env::var_os("FIELD_GROWTH_HELD").is_some() || learner.field.scale.is_some();
        match growth(fell, fallen, grown || held, lap, laps) {
            Growth::Widen => {
                learner = learner.widened(2, &keys).map_err(|e| e.to_string())?;
                grown = true;
                fallen = false;
                let d = learner.field.declaration;
                println!("FIELD_GROW lap={lap} width={} heads={} contacts={} rate={} material={} ms={}", d.width, d.heads, d.contacts, learner.rate_bits, learner.field.theta.len(), started.elapsed().as_millis());
            }
            Growth::Held => println!("FIELD_GROW_HELD lap={lap} reason=a second growth has no projection; the laps go on at this width ms={}", started.elapsed().as_millis()),
            Growth::None => {}
        }
        previous = (code, unseen_sites);
    }
    Ok(())
}


/// [agent-inferred, November 4, §16.41] **The octave a lap's transfers read**: `+1` (the step doubles), `−1` (it halves) or
/// `0`. Each step's transfer `t` is the first-order change of the next section's code were the step taken once more, so along
/// the lap's steps the joint code is `F(μ) = cμ + b′μ²` with `F′(1) = Σ t`; `b′` is read from the own curvatures `Σ b` of the
/// steps priced (a section's own parabola, the receipt's `change − predicted`), so the joint parabola's least is
/// `μ* = 1 − Σt / 2Σb`. The step halves where `μ* < 1/√2` and doubles where `μ* > √2`, the octave nearest `μ*` on the rate's
/// own carrier, compared exactly (`u = 2Σb − Σt = 2Σb μ*`: halve where `u < 0` or `u² < 2(Σb)²`, double where `u² > 8(Σb)²`).
/// Where no curvature is read (`Σ b ≤ 0`) the transfer's sign alone moves it. [the unified-theory reading of November 6, 08:54]
/// Since the step fluxes (no reread, so no `change`), the trainer reads it as the lap's line search, `step_transfer(2Σt,
/// Σ(t − p_ext))`: `μ* = −Σp_ext / Σ(t − p_ext)`, the curvature `t − p_ext` read from the pass alone ([`FieldReceipt::external`]).
/// Why the next sections and not the step's own:
/// a step's own parabola read its least near five times the step at rate `2^(−11)` and its law drove the step to `2^(−7)`,
/// where the joint code rose from 1.127 to 1.59 nats a place (`_receipts/law50/`): a step's own fall is mostly the fit to its
/// own section, and only the next sections price what it generalizes.
pub(super) fn step_transfer(transfers: i128, curvatures: i128) -> i32 {
    if curvatures <= 0 {
        return -(transfers.signum() as i32);
    }
    let u = 2 * curvatures - transfers;
    let b2 = curvatures * curvatures;
    if u < 0 || u.saturating_mul(u) < 2 * b2 {
        -1
    } else if u.saturating_mul(u) > 8 * b2 {
        1
    } else {
        0
    }
}

/// What a lap's withheld read decides of the body's width ([`growth`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Growth {
    Widen,
    Held,
    None,
}

/// [agent-inferred, November 2] **A lap's growth**: after a lap whose withheld code did not fall, once it has
/// fallen at this width and a lap remains, the body widens if it has not grown in this run, and otherwise the
/// growth is held and the laps go on at this width. Why: the run carries the projections of its declaration and
/// of one growth, so a second has no projection; crib13 ended at lap 9 of 27 when its second growth came due,
/// which cut the workload the design fixed (the run's laps) for a growth the run could not project.
pub(super) fn growth(fell: bool, fallen: bool, grown: bool, lap: usize, laps: usize) -> Growth {
    match (!fell && fallen && lap + 1 < laps, grown) {
        (false, _) => Growth::None,
        (true, false) => Growth::Widen,
        (true, true) => Growth::Held,
    }
}

/// The bytes a release writes, escaped: `|`, tab, line ends, quotes, the backslash and every byte outside
/// printable ASCII as `\xNN`, the rest as themselves (as `written_coupling`'s `unescape` reads them).
fn escaped(bytes: &[u8]) -> String {
    let mut out = String::new();
    for &c in bytes {
        match c {
            0x7c => out.push_str("\\x7c"),
            9 => out.push_str("\\t"),
            10 => out.push_str("\\n"),
            13 => out.push_str("\\r"),
            0x27 => out.push_str("\\'"),
            0x22 => out.push_str("\\\""),
            0x5c => out.push_str("\\\\"),
            0x20..0x7f => out.push(c as char),
            _ => out.push_str(&format!("\\x{c:02x}")),
        }
    }
    out
}

/// A file opened create-new, written a row at a time so a stopped run keeps what it read.
fn rows_file(path: &Path, head: &str) -> Result<std::fs::File> {
    use std::io::Write;
    let mut file = std::fs::OpenOptions::new().write(true).create_new(true).open(path)?;
    file.write_all(head.as_bytes())?;
    Ok(file)
}

fn row(file: &mut std::fs::File, text: &str) -> Result<()> {
    use std::io::Write;
    file.write_all(text.as_bytes())?;
    Ok(())
}

/// A writer's opening: the question's classes and its written prefix, and the answer sites left
/// open (the codec's extent less the prefix, at least one); refused where a unit is not the codec's
/// or the region passes the field's reach.
fn opening(codec: &FieldCodec, field: &Field, question: &[u8], prefix: &[u8]) -> std::result::Result<(Vec<usize>, usize), String> {
    let mut q = codec.encode(&question_text(question)).map_err(|e| e.to_string())?;
    let written = codec.encode(prefix).map_err(|e| e.to_string())?;
    let open = codec.answer.saturating_sub(written.len()).max(1);
    q.extend(&written);
    if q.len() + open > field.declaration.reach {
        return Err(format!("a region of {} sites passes the field's reach of {}", q.len() + open, field.declaration.reach));
    }
    Ok((q, open))
}

/// [measurement; agent-inferred, November 3, §16.27, §16.36] **`sample-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA
/// HELD HELD_SHA COUNT SWEEPS REFINE STOP_MS OUT`**: the first `COUNT` held questions, each answer released by the training
/// clock run backwards ([`Field::sample_realized`]): every answer place drawn from its own face in a keyed random order over
/// `SWEEPS` sweeps, then `REFINE` passes revisiting the written answer, the draws keyed by the state's own hash. Writes `SAMPLE.tsv` (each answer's places before its first void,
/// private), `PLACES.tsv` (every place, the void as `|`; private) and `COUPLING.tsv` (each answer's `λ` and `F*` against its own and the next problem's target).
pub(super) fn sample(args: &[String], realization: &mut dyn FieldRealization) -> Result<()> {
    if args.len() != 14 {
        return Err("sample-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD HELD_SHA COUNT SWEEPS REFINE STOP_MS OUT".into());
    }
    let started = std::time::Instant::now();
    let mut learner = FieldLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    declared_clocks(&mut learner.field);
    let units = units_of(&args[5], &args[6])?;
    let codec = FieldCodec::from_text(std::str::from_utf8(&pinned_read(&args[3], &args[4], CODEC_BUDGET)?)?, units)?;
    let held = problems_of(&pinned_read(&args[7], &args[8], READ_BUDGET as usize)?);
    let (limit, sweeps, refine, stop_ms) = (count(&args[9])?, positive(&args[10])?, count(&args[11])?, positive(&args[12])? as u128);
    let out = Path::new(&args[13]);
    std::fs::create_dir(out)?;
    let field = &learner.field;
    let held = &held[..limit.min(held.len())];
    let seed = u64::from_str_radix(&args[2][..16], 16).map_err(|_| "a state hash that is not hexadecimal")?;
    let requests: Vec<(Vec<usize>, usize)> = held.iter().map(|(question, _)| opening(&codec, field, question, b"")).collect::<std::result::Result<_, String>>()?;
    let problems: Vec<(&[usize], usize)> = requests.iter().map(|(q, n)| (q.as_slice(), *n)).collect();
    let mut stopped = None;
    let answers = field
        .sample_realized(&problems, sweeps, refine, codec.void(), seed, realization, &mut |done, all| {
            if done % 16 == 0 {
                println!("FIELD_SAMPLE_SWEEP done={done} of={all} ms={}", started.elapsed().as_millis());
            }
            if started.elapsed().as_millis() > stop_ms {
                stopped = Some(done);
                return false;
            }
            true
        })
        .map_err(|e| e.to_string())?;
    let mut file = rows_file(&out.join("SAMPLE.tsv"), "")?;
    let mut place_rows = rows_file(&out.join("PLACES.tsv"), "")?;
    let mut couplings = rows_file(&out.join("COUPLING.tsv"), "problem\twritten\theld\tlambda\tfriction\tfoil_lambda\tfoil_friction\n")?;
    let (mut sum_h, mut sum_t, mut sum_l, mut sum_f, mut sum_fl, mut sum_ff, mut wins, mut losses) = (0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize);
    for (i, places) in answers.iter().enumerate() {
        // [agent-inferred, November 3, §16.35] The written answer is its places before the first void, as the codec reads
        // classes (`FieldCodec::decode`): the void is the class past an answer's end, so a place past it is past the end.
        let h: Vec<usize> = places.iter().copied().take_while(|&c| c != codec.void()).collect();
        let past = places.iter().skip(h.len()).filter(|&&c| c != codec.void()).count();
        println!("FIELD_SAMPLE_PLACES problem={i} first_void={} past_first_void={past} places={}", h.len(), places.len());
        let text = codec.decode(&h);
        row(&mut file, &format!("{i}\t{}\n", escaped(&text)))?;
        // Every place in order, the void as `|` (an escaped text writes a `|` byte as `\x7c`).
        let marked: String = places.iter().map(|&c| if c == codec.void() { "|".to_string() } else { escaped(&codec.decode(&[c])) }).collect();
        row(&mut place_rows, &format!("{i}\t{marked}\n"))?;
        let t = codec.encode(&held[i].1).unwrap_or_default();
        let foil = codec.encode(&held[(i + 1) % held.len()].1).unwrap_or_default();
        let c = holonics::receiver::coupling::coupling(&h, &t).map_err(|e| e.to_string())?;
        let f = holonics::receiver::coupling::coupling(&h, &foil).map_err(|e| e.to_string())?;
        row(&mut couplings, &format!("{i}\t{}\t{}\t{}\t{}\t{}\t{}\n", h.len(), t.len(), c.lambda, c.least_friction, f.lambda, f.least_friction))?;
        (sum_h, sum_t, sum_l, sum_f, sum_fl, sum_ff) = (sum_h + h.len(), sum_t + t.len(), sum_l + c.lambda, sum_f + c.least_friction, sum_fl + f.lambda, sum_ff + f.least_friction);
        wins += usize::from(c.lambda > f.lambda);
        losses += usize::from(c.lambda < f.lambda);
    }
    println!(
        "FIELD_SAMPLE problems={} sweeps={sweeps} stopped={} written={sum_h} held={sum_t} lambda={sum_l} friction={sum_f} foil_lambda={sum_fl} foil_friction={sum_ff} own_wins={wins} foil_wins={losses} ms={}",
        held.len(),
        stopped.map_or("-".to_string(), |s| s.to_string()),
        started.elapsed().as_millis()
    );
    Ok(())
}

/// The restated results of a held answer, `<<E=C>>D` with `D = C` (the boundary codec's bytes, every site one byte): each
/// one's answer site of its first `>` and its length `|C|`. D's `k`-th site reads C's `k`-th at offset `|C| + 2`.
pub(super) fn restatements_of(pieces: &[Vec<u8>]) -> Vec<(usize, usize)> {
    let byte = |t: usize| pieces.get(t).filter(|p| p.len() == 1).map(|p| p[0]);
    let mut out = Vec::new();
    for s in 1..pieces.len() {
        if byte(s) != Some(b'>') || byte(s + 1) != Some(b'>') {
            continue;
        }
        let Some(c0) = (0..s).rev().find(|&t| byte(t) == Some(b'=')).map(|t| t + 1) else { continue };
        let length = s - c0;
        let inside = (c0..s).all(|t| byte(t).is_some_and(|b| b != b'<' && b != b'>' && b != b'='));
        let opened = (0..c0).rev().take_while(|&t| byte(t) != Some(b'>')).any(|t| t > 0 && byte(t) == Some(b'<') && byte(t - 1) == Some(b'<'));
        if length > 0 && inside && opened && (0..length).all(|k| byte(s + 2 + k).is_some() && byte(s + 2 + k) == byte(c0 + k)) {
            out.push((s, length));
        }
    }
    out
}

/// [measurement; agent-inferred, November 4, §16.42] **`restate-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD
/// HELD_SHA COUNT OUT`**: whether the field writes a restated result's ends (the unified-theory reading of November 4,
/// §5: in `<<E=C>>D` the result C is written again as D, and D's `k`-th site must read C's `k`-th at offset `|C| + 2`,
/// inside the near field for `|C| ≤ 3`, where the fine rings' skin leaves almost nothing; the written answers miss
/// mostly at D's ends). For each restatement in the first `COUNT` held answers, three sites are read: D's first place,
/// its last, and the place after it (where the source at the restatement's offset is the `>` that ends it). Each is
/// read in five of the writer's states, beside its question and the rest of its answer: alone open (`alone`); with D
/// and the place after it open (`restated_open`: the result written, its restatement not); with C, D and the place
/// after it open (`both_open`; the `>>` between them written); with the `>>`, D and the place after it open
/// (`between_open`: the result written, the places between it and its restatement not); and with every answer site but
/// C's open (`answer_open`). The turned heads read a source across their learned clock, whose gaps are the sites'
/// paces, so an open site between a source and its receiver changes the gap they meet across. Each read is the realization's near field by offset
/// ([`FieldRealization::read_near_offsets`]): every tick and head's shares of the sources 1 to 5 sites before, and the
/// face at the site, whose share of the answer's class is the code the place costs. Writes `RESTATEMENTS.tsv` (each read;
/// private, of the held answers) and prints the counts, and (§16.44) the writer's first state's code: every answer place
/// and the first void open beside the question, the truth's code a class. A reading only.
pub(super) fn restate_field(args: &[String], realization: &mut dyn FieldRealization) -> Result<()> {
    use holonics::hnn::tower::field::NEAR;
    if args.len() != 11 {
        return Err("restate-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD HELD_SHA COUNT OUT".into());
    }
    let started = std::time::Instant::now();
    let learner = FieldLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let field = &learner.field;
    let d = field.declaration;
    let units = units_of(&args[5], &args[6])?;
    let codec = FieldCodec::from_text(std::str::from_utf8(&pinned_read(&args[3], &args[4], CODEC_BUDGET)?)?, units)?;
    let held = problems_of(&pinned_read(&args[7], &args[8], READ_BUDGET as usize)?);
    let limit = count(&args[9])?;
    let out = Path::new(&args[10]);
    std::fs::create_dir(out)?;
    let kinds: Vec<&str> = (0..d.heads).map(|h| if h % d.frames < d.still { "still" } else { "turned" }).collect();
    println!("FIELD_RESTATE_DECLARATION heads={} ticks={} still={} frames={} kinds={}", d.heads, d.ticks, d.still, d.frames, kinds.join(","));
    let cells: Vec<String> = (0..d.ticks).flat_map(|k| (0..d.heads).flat_map(move |h| (1..NEAR).map(move |o| format!("t{k}h{h}d{o}")))).collect();
    let mut rows = rows_file(&out.join("RESTATEMENTS.tsv"), &format!("problem\trestatement\tstate\tat\tlength\toffset\tp_true\tp_total\t{}\n", cells.join("\t")))?;
    // [§16.44] The `>>` places' clocks by tick with every answer place but C open: each paced head's rate there, its written
    // rate, and the face's code of the `>` against its entropy (on `2^(−20)` bits).
    let mut clocks = rows_file(&out.join("CLOCKS.tsv"), "problem\trestatement\tlength\ttick\thead\tkappa_first\tkappa_second\tkappa_written\tcode_first\tentropy_first\tcode_second\tentropy_second\n")?;
    let entropy = |f: &holonics::hnn::tower::TowerFace| -> i64 { if f.total == 0 { 0 } else { (f.masses.iter().map(|&m| (m as i128) * holonics::hnn::tower::face_code(m.max(1), f.total) as i128).sum::<i128>() / f.total as i128) as i64 } };
    let (mut restatements, mut reads) = (0usize, 0usize);
    // [§16.44] The writer's first state: every answer place and the first void open beside the question, the truth's code.
    let (mut first_code, mut first_places) = (0i64, 0usize);
    let problems = limit.min(held.len());
    for (k, (question, answer)) in held.iter().take(limit).enumerate() {
        let (q, a) = (codec.encode(&question_text(question))?, codec.encode(answer)?);
        let mut classes: Vec<usize> = q.iter().chain(&a).copied().collect();
        classes.push(codec.void());
        if classes.len() > d.reach {
            continue;
        }
        let first: Vec<bool> = (0..classes.len()).map(|t| t >= q.len()).collect();
        let region = Region { classes: &classes, unresolved: &first, faces: &[], locked: &[], echo: &[], domain: None, port: None };
        let faces = realization.read_faces(field, std::slice::from_ref(&region)).map_err(|e| e.to_string())?.remove(0);
        for (t, face) in faces.iter().enumerate().filter(|&(t, _)| first[t]) {
            let face = face.as_ref().ok_or("an open place with no face")?;
            first_code += holonics::hnn::tower::face_code(face.masses[classes[t]], face.total);
            first_places += 1;
        }
        let pieces: Vec<Vec<u8>> = a.iter().map(|&c| codec.decode(&[c])).collect();
        for (c, (s, length)) in restatements_of(&pieces).into_iter().enumerate() {
            restatements += 1;
            // The answer's sites: C before the close at `s`, the `>>` at `s` and `s + 1`, then D and the place after it.
            let (result, restated) = (q.len() + s - length..q.len() + s, q.len() + s + 2..q.len() + s + 3 + length);
            let between = q.len() + s..q.len() + s + 2;
            let answer_rest: Vec<usize> = (q.len()..classes.len()).filter(|t| !result.contains(t)).collect();
            let states: [(&str, Vec<usize>); 5] = [
                ("alone", Vec::new()),
                ("restated_open", restated.clone().collect()),
                ("both_open", result.clone().chain(restated.clone()).collect()),
                ("between_open", between.chain(restated.clone()).collect()),
                ("answer_open", answer_rest),
            ];
            {
                let (gt, open) = (q.len() + s, &states[4].1);
                let mut unresolved = vec![false; classes.len()];
                for &t in open {
                    unresolved[t] = true;
                }
                let region = Region { classes: &classes, unresolved: &unresolved, faces: &[], locked: &[], echo: &[], domain: None, port: None };
                let read = realization.read_blank_clocks(field, &region, &[gt, gt + 1]).map_err(|e| e.to_string())?;
                let width = d.alphabet + 1;
                for tick in 0..d.ticks {
                    let (Some((k1, f1)), Some((k2, f2))) = (&read[0].ticks[tick], &read[1].ticks[tick]) else { continue };
                    for (p, (&a, &b)) in k1.iter().zip(k2).enumerate() {
                        let written = (1i64 << holonics::hnn::tower::field::PACE_BITS) + field.theta[field.layout().pace + p * width + classes[gt]] as i64;
                        let (c1, c2) = (holonics::hnn::tower::face_code(f1.masses[classes[gt]], f1.total), holonics::hnn::tower::face_code(f2.masses[classes[gt + 1]], f2.total));
                        row(&mut clocks, &format!("{k}\t{c}\t{length}\t{tick}\t{p}\t{a}\t{b}\t{written}\t{c1}\t{}\t{c2}\t{}\n", entropy(f1), entropy(f2)))?;
                    }
                }
            }
            for (state, open) in &states {
                for (at, place) in [("first", s + 2), ("last", s + 1 + length), ("stop", s + 2 + length)] {
                    let i = q.len() + place;
                    let mut unresolved = vec![false; classes.len()];
                    for &t in open.iter().chain(std::iter::once(&i)) {
                        unresolved[t] = true;
                    }
                    let region = Region { classes: &classes, unresolved: &unresolved, faces: &[], locked: &[], echo: &[], domain: None, port: None };
                    let near = realization.read_near_offsets(field, &region, &[i]).map_err(|e| e.to_string())?.remove(0);
                    let logits = near.logits.as_ref().ok_or("a near-field read with no face at its open site")?;
                    let face = field.tempered(logits, 1);
                    reads += 1;
                    let shares: Vec<String> = near.before.iter().flat_map(|b| b.iter().map(u64::to_string)).collect();
                    row(&mut rows, &format!("{k}\t{c}\t{state}\t{at}\t{length}\t{}\t{}\t{}\t{}\n", length + 2, face.masses[classes[i]], face.total, shares.join("\t")))?;
                }
            }
        }
        if (k + 1) % 16 == 0 {
            println!("FIELD_RESTATE_PROGRESS problems={} restatements={restatements} reads={reads} ms={}", k + 1, started.elapsed().as_millis());
        }
    }
    println!("FIELD_RESTATE problems={problems} restatements={restatements} reads={reads} ms={}", started.elapsed().as_millis());
    println!("FIELD_RESTATE_FIRST places={first_places} code_bits_a_class={}", bits(first_code, first_places));
    Ok(())
}

/// The bands of distance a square's two places stand at (§ the curl on two-place squares): 1, 2–3, 4–7, 8–15, 16 and past.
const SQUARE_BANDS: [(usize, usize); 5] = [(1, 1), (2, 3), (4, 7), (8, 15), (16, usize::MAX)];

/// A square's reading: each place's runner-up letter on its face beside the truth, and the log odds ratio through each
/// place's faces across the other's standing and runner-up letters, `λ_i`, `λ_j` on the codes' `2^(−20)` bits, with the four
/// faces on their letters (`[i | j standing, i | j runner-up, j | i standing, j | i runner-up]`).
struct Square {
    runners: (usize, usize),
    lambda_i: i64,
    lambda_j: i64,
    faces: [holonics::hnn::tower::TowerFace; 4],
}

struct SquareReads {
    squares: Vec<Option<Square>>,
    regions: usize,
}

/// [measurement; agent-inferred, November 6, the unified-theory reading of 18:28] **A square's four reads** on a state of the
/// truth (`truth`: the question, the answer and its near tail, every place resolved): for each `(band, i, j)`, the faces at
/// `i` and at `j` with only that place open, each face's runner-up letter (the most mass after the standing letter's, on its
/// letters off the void), then each place's face with the other's letter set to its runner-up. `λ_i = c_i(a'|b) + c_i(a|b')
/// − c_i(a|b) − c_i(a'|b')` (`a`, `a'` the standing and runner-up letters at `i`, `b`, `b'` at `j`), `λ_j` alike; a square
/// whose face holds no runner-up is none.
fn square_reads(field: &Field, void: usize, truth: &[usize], picked: &[(usize, usize, usize)], realization: &mut dyn FieldRealization) -> Result<SquareReads> {
    let letters = |f: &holonics::hnn::tower::TowerFace| holonics::hnn::tower::field::letters_face(f, void);
    let runner_up = |f: &holonics::hnn::tower::TowerFace, standing: usize| (0..f.masses.len()).filter(|&c| c != standing && f.masses[c] > 0).max_by_key(|&c| (f.masses[c], std::cmp::Reverse(c)));
    let state = |open_at: usize, set: Option<(usize, usize)>| -> (Vec<usize>, Vec<bool>) {
        let mut classes = truth.to_vec();
        if let Some((t, c)) = set {
            classes[t] = c;
        }
        let open = (0..classes.len()).map(|t| t == open_at).collect();
        (classes, open)
    };
    let read = |states: &[(Vec<usize>, Vec<bool>)], at: &[usize], realization: &mut dyn FieldRealization| -> Result<Vec<holonics::hnn::tower::TowerFace>> {
        let mut faces = Vec::with_capacity(states.len());
        for (chunk, sites) in states.chunks(32).zip(at.chunks(32)) {
            let regions: Vec<Region> = chunk.iter().map(|(c, o)| Region { classes: c, unresolved: o, faces: &[], locked: &[], echo: &[], domain: None, port: None }).collect();
            for (f, &t) in realization.read_faces(field, &regions).map_err(|e| e.to_string())?.into_iter().zip(sites) {
                let face = f[t].as_ref().ok_or("a square's open place with no face")?;
                faces.push(letters(face).ok_or("a square's face with no letter")?);
            }
        }
        Ok(faces)
    };
    let base_states: Vec<_> = picked.iter().flat_map(|&(_, i, j)| [state(i, None), state(j, None)]).collect();
    let base_at: Vec<usize> = picked.iter().flat_map(|&(_, i, j)| [i, j]).collect();
    let base = read(&base_states, &base_at, realization)?;
    let mut cross_states = Vec::with_capacity(base_states.len());
    let mut runners = Vec::with_capacity(picked.len());
    for (s, &(_, i, j)) in picked.iter().enumerate() {
        let (Some(bi), Some(bj)) = (runner_up(&base[2 * s], truth[i]), runner_up(&base[2 * s + 1], truth[j])) else {
            runners.push(None);
            continue;
        };
        runners.push(Some((bi, bj)));
        cross_states.push(state(i, Some((j, bj))));
        cross_states.push(state(j, Some((i, bi))));
    }
    let cross_at: Vec<usize> = picked.iter().zip(&runners).filter(|(_, r)| r.is_some()).flat_map(|(&(_, i, j), _)| [i, j]).collect();
    let cross = read(&cross_states, &cross_at, realization)?;
    let regions = base_states.len() + cross_states.len();
    let mut squares = Vec::with_capacity(picked.len());
    let mut c = 0usize;
    for (s, (&(_, i, j), r)) in picked.iter().zip(&runners).enumerate() {
        let Some((bi, bj)) = *r else {
            squares.push(None);
            continue;
        };
        let (ai, aj) = (truth[i], truth[j]);
        let faces = [base[2 * s].clone(), cross[2 * c].clone(), base[2 * s + 1].clone(), cross[2 * c + 1].clone()];
        c += 1;
        let lambda_i = faces[0].code(bi) + faces[1].code(ai) - faces[0].code(ai) - faces[1].code(bi);
        let lambda_j = faces[2].code(bj) + faces[3].code(aj) - faces[2].code(aj) - faces[3].code(bj);
        squares.push(Some(Square { runners: (bi, bj), lambda_i, lambda_j, faces }));
    }
    Ok(SquareReads { squares, regions })
}

/// [definition; the unified-theory reading of November 6, 19:04] **The squares agree**: each path problem's square at a keyed
/// band ([`SQUARE_BANDS`], among those its answer reaches), its places keyed within the answer, on the truth given its end
/// (the question, the answer and its `NEAR` voids, cut there), read through [`square_reads`] on the learner's field; with
/// `l = λ_i − λ_j` the loss is `l²/4`, and four states each open at one place carry its covector as a declared pull
/// ([`holonics::hnn::tower::field::Port::pull`]): `i` beside `j`'s standing letter pulls `(a, a', w_i)` (its code
/// `w_i (c(a') − c(a))`), `i` beside `j`'s runner-up `(a', a, w_i)`, `j` beside `i`'s standing letter `(b, b', w_j)` and `j`
/// beside `i`'s runner-up `(b', b, w_j)`, so the four codes sum to `w_i λ_i + w_j λ_j` at the read. [definition; the
/// unified-theory reading of November 6, 20:33] **The turn law**: the pull compares the two readings' ratio, not their
/// difference. With `v = (λ_i, λ_j)` and `σ` the swap, `κ = 1 − ⟨v, σv⟩/⟨v, v⟩ = l²/r²` (`r² = λ_i² + λ_j²`), and the pull is
/// `l²/4`'s covector with its radial part removed, `w_i = (l/2) λ_j (λ_i + λ_j)/r²`, `w_j = −(l/2) λ_i (λ_i + λ_j)/r²` (zero
/// where `r = 0`), so `w_i λ_i + w_j λ_j = 0`: no common scale of the two readings is pulled, and a one-way square
/// (`λ_j = 0`) moves only the missing reading. [agent-inferred, November 6, squares125] Each state's factor `w/(n_p/4)` is
/// bounded by one, as a compared place's covector entry is (`|p − e| ≤ 1`), the two scaled alike so the pull keeps no radial
/// part. Why: a runner-up of almost no mass on a cross face read `|l|` in the tens of bits, and squares125's pull outgrew the
/// card's 128-bit sum at its 249th section. Why (squares123): `l²/4` is homogeneous in the readings' scale, so its
/// steepest path shrank both (λ's spread at d = 1 3.54 → 2.99) and held context paid. [definition; the unified-theory reading of November 6, 20:18] **A square stands for its answer**: its four
/// states together weigh as many places as its problem compares in the section (its opening's and its writer state's
/// compared answer places, `n_p`), `w = (l/2)(n_p/4)`, so prediction and agreement stand equal a problem, local to its
/// answer. Why (squares121): at `w = l/2` the trained squares' `|l|` ran flat (1.163 to 1.210 bits by quarter) beside about
/// a thousand compared places a section. Why (truth120): the curl's spread exceeded the odds ratio's at every band on lap 4 and lap 24 alike, and the masked
/// comparison never sets the two readings of a pair against each other; the law keeps handedness, an oriented interaction
/// must only read the same from both ends. Returns the states and the squares' `Σ|l|` on `2^(−20)` bits.
pub(super) fn square_regions(codec: &FieldCodec, problems: &Problems, paths: &[usize], draws: &[u64], seed: u64, field: &Field, realization: &mut dyn FieldRealization) -> Result<(Vec<TrainRegion>, usize, i64)> {
    let near = holonics::hnn::tower::field::NEAR;
    let void = codec.void();
    let mut out = Vec::new();
    let (mut squares, mut curl) = (0usize, 0i64);
    for (&p, &d) in paths.iter().zip(draws) {
        let (q, a, _) = &problems[p];
        let len = a.len().min(codec.answer);
        if len < 2 {
            continue;
        }
        let truth = region_classes(codec, q, &a[..len], (q.len() + len + near).min(q.len() + codec.answer));
        let key = mix(seed ^ 0x5C0A_4E00_0000_0000, d);
        let bands: Vec<(usize, usize)> = SQUARE_BANDS.iter().map(|&(lo, hi)| (lo, hi.min(len - 1))).filter(|&(lo, top)| lo <= top).collect();
        let (lo, top) = bands[(mix(key, 1) % bands.len() as u64) as usize];
        let dist = lo + (mix(key, 2) % (top - lo + 1) as u64) as usize;
        let i = q.len() + (mix(key, 3) % (len - dist) as u64) as usize;
        let j = i + dist;
        let read = square_reads(field, void, &truth, &[(0, i, j)], realization)?;
        let Some(Some(sq)) = read.squares.into_iter().next() else { continue };
        let l = sq.lambda_i - sq.lambda_j;
        let compared = opening_region(codec, q, a, seed, d).map_or(0, |r| compared_answer_places(&r, q.len(), len)) + if path_writer() { writer_region(codec, q, a, seed, d).map_or(0, |r| compared_answer_places(&r, q.len(), len)) } else { 0 };
        let (li, lj) = (sq.lambda_i as i128, sq.lambda_j as i128);
        let r2 = li * li + lj * lj;
        let n = compared.max(1) as i128;
        // Each state's factor (on 2^(−20)), bounded by one: the two scaled alike, so the pull keeps no radial part.
        let (mut fi, mut fj) = if r2 == 0 { (0, 0) } else { (div_nearest_i128(l as i128 * lj * (li + lj), 2 * r2), div_nearest_i128(-(l as i128) * li * (li + lj), 2 * r2)) };
        let most = fi.abs().max(fj.abs());
        if most > 1 << 20 {
            (fi, fj) = (div_nearest_i128(fi << 20, most), div_nearest_i128(fj << 20, most));
        }
        let (wi, wj) = (fit_i64(div_nearest_i128(fi * n, 4))?, fit_i64(div_nearest_i128(fj * n, 4))?);
        let (ai, aj, (bi, bj)) = (truth[i], truth[j], sq.runners);
        let state = |open_at: usize, set: Option<(usize, usize)>, pull: (usize, usize, i64)| {
            let mut classes = truth.clone();
            if let Some((t, c)) = set {
                classes[t] = c;
            }
            let unresolved = (0..classes.len()).map(|t| t == open_at).collect();
            TrainRegion { port: Some((open_at, void, Vec::new(), false, Some(open_at + 1), None)), pull: Some(pull), ..TrainRegion::plain(classes, unresolved) }
        };
        out.push(state(i, None, (ai, bi, wi)));
        out.push(state(i, Some((j, bj)), (bi, ai, wi)));
        out.push(state(j, None, (aj, bj, wj)));
        out.push(state(j, Some((i, bi)), (bj, aj, wj)));
        squares += 1;
        curl += l.abs();
    }
    Ok((out, squares, curl))
}

/// A state's compared answer places: its open places within the answer, before its port's stop and among the places its
/// port hears where it declares them.
fn compared_answer_places(region: &TrainRegion, q: usize, len: usize) -> usize {
    (q..q + len)
        .filter(|&t| t < region.unresolved.len() && region.unresolved[t])
        .filter(|&t| match &region.port {
            Some((start, _, _, _, stop, heard)) => t < *start || (stop.is_none_or(|s| t < s) && heard.as_ref().is_none_or(|h| h[t])),
            None => true,
        })
        .count()
}

/// The nearest integer to `n / d` (`d > 0`), half away from zero.
fn div_nearest_i128(n: i128, d: i128) -> i128 {
    if n >= 0 { (n + d / 2) / d } else { -((-n + d / 2) / d) }
}

fn fit_i64(v: i128) -> std::result::Result<i64, String> {
    i64::try_from(v).map_err(|_| "a square's pull past 64 bits".to_string())
}

/// Whether each path problem's square also trains the faces' agreement ([`square_regions`], `FIELD_PATH_SQUARES`).
pub(super) fn path_squares() -> bool {
    static SQUARES: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *SQUARES.get_or_init(|| std::env::var_os("FIELD_PATH_SQUARES").is_some())
}

/// [measurement; agent-inferred, November 6, the unified-theory reading of 18:28] **The curl on two-place squares**: on each
/// of `COUNT` held answers, as the writer reads it given its length (the question, the truth, its near tail), `SQUARES` keyed
/// pairs of answer places `(i, j = i + d)` in each band of distance (`d` = 1, 2–3, 4–7, 8–15, 16 and past): the standing
/// letters `a_i`, `a_j`, each face's runner-up letter `b_i`, `b_j` (read with only that place open), then each place's face
/// with the other's letter set to its runner-up; `λ_i` is the log odds ratio `ln p_i(a|a) p_i(b|b) / p_i(b|a) p_i(a|b)` read
/// through `i`'s faces across `j`'s two letters, `λ_j` the same through `j`'s, both on the codes' `2^(−20)` bits. The faces are
/// one joint's conditionals on a square only where `λ_i = λ_j` (Kolmogorov's cycle condition); `λ_i − λ_j` is its curl.
/// Writes `CURL.tsv` (private positions and classes of held answers) and prints the run's size. A reading only.
pub(super) fn curl_field(args: &[String], realization: &mut dyn FieldRealization) -> Result<()> {
    if args.len() != 12 {
        return Err("curl-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD HELD_SHA COUNT SQUARES OUT".into());
    }
    let started = std::time::Instant::now();
    let learner = FieldLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let field = &learner.field;
    let units = units_of(&args[5], &args[6])?;
    let codec = FieldCodec::from_text(std::str::from_utf8(&pinned_read(&args[3], &args[4], CODEC_BUDGET)?)?, units)?;
    let held = problems_of(&pinned_read(&args[7], &args[8], READ_BUDGET as usize)?);
    let (n, squares) = (count(&args[9])?.min(held.len()), positive(&args[10])?);
    let out = Path::new(&args[11]);
    std::fs::create_dir(out)?;
    let void = codec.void();
    let near = holonics::hnn::tower::field::NEAR;
    // [measurement; the unified-theory reading of November 7, 04:20] `FIELD_ENERGY_SHIFTS` (comma-separated `k`): the central
    // squares' steps, a letter's weight over `2^k` (4, 3 and 2 where none is given); `FIELD_ENERGY_SQUARES`: a TSV whose rows
    // `problem band i j` (answer places) are the only squares read, the settling read of chosen squares.
    let shifts: Vec<u32> = match std::env::var("FIELD_ENERGY_SHIFTS") {
        Ok(v) => v.split(',').map(|k| k.trim().parse::<u32>().map_err(|_| format!("FIELD_ENERGY_SHIFTS {v}: shifts are counts"))).collect::<std::result::Result<_, _>>()?,
        Err(_) => vec![4, 3, 2],
    };
    let chosen: Option<std::collections::BTreeSet<(usize, usize, usize, usize)>> = match std::env::var("FIELD_ENERGY_SQUARES") {
        Ok(path) => Some(
            std::fs::read_to_string(&path)?
                .lines()
                .filter_map(|l| {
                    let c: Vec<usize> = l.split('\t').take(4).filter_map(|v| v.parse().ok()).collect();
                    (c.len() == 4).then(|| (c[0], c[1], c[2], c[3]))
                })
                .collect(),
        ),
        Err(_) => None,
    };
    let header = if std::env::var_os("FIELD_ENERGY_CENTRAL").is_some() {
        let cells: Vec<String> = shifts.iter().flat_map(|&k| [format!("c{}_i", 1u32 << k), format!("c{}_j", 1u32 << k)]).collect();
        format!("problem\tband\ti\tj\t{}\n", cells.join("\t"))
    } else {
        "problem\tband\ti\tj\tlambda_i\tlambda_j\tsmall_i\tsmall_j\twide_i\twide_j\tzlambda_i\tzlambda_j\tglambda\tfloors\n".to_string()
    };
    let mut rows = rows_file(&out.join("CURL.tsv"), &header)?;
    let (mut read_regions, mut written) = (0usize, 0usize);
    for k in 0..n {
        let (q, room) = opening(&codec, field, &held[k].0, b"")?;
        let mut a = codec.encode(&held[k].1)?;
        a.truncate(room);
        if a.len() < 2 {
            continue;
        }
        let mut truth: Vec<usize> = q.iter().chain(&a).copied().collect();
        truth.extend(std::iter::repeat_n(void, near.min(room - a.len())));
        // The keyed squares of each band within the answer.
        let mut picked: Vec<(usize, usize, usize)> = Vec::new();
        for (b, &(lo, hi)) in SQUARE_BANDS.iter().enumerate() {
            let top = hi.min(a.len() - 1);
            if lo > top {
                continue;
            }
            for s in 0..squares {
                let key = mix(0xC0_41 << 40 | (k as u64) << 20, (b as u64) << 16 | s as u64);
                let d = lo + (key as usize >> 8) % (top - lo + 1);
                let i = q.len() + (key >> 32) as usize % (a.len() - d);
                picked.push((b, i, i + d));
            }
        }
        if let Some(chosen) = &chosen {
            picked.retain(|&(b, i, j)| chosen.contains(&(k, b, i - q.len(), j - q.len())));
            picked.dedup();
            if picked.is_empty() {
                continue;
            }
        }
        // [measurement; the unified-theory reading of November 7, 01:37] An energy field's square is read at one base, its four
        // corners replayed at the base's halvings under its supports (`Field::energy_square_corners`), with the attribution
        // read at ε and 4ε beside it, through the realization (the card's or the host's).
        // [measurement; the unified-theory reading of November 7, 03:22] `FIELD_ENERGY_CENTRAL`: each square's central readings at
        // one base at a letter's weight over 16, 8 and 4 (`Field::energy_central_square`), through the realization (the card's
        // since November 7, 04:20, or the host's).
        if field.declaration.energy && std::env::var_os("FIELD_ENERGY_CENTRAL").is_some() {
            let letter = (1u32 << 16) / field.declaration.alphabet as u32;
            let steps: Vec<u32> = shifts.iter().map(|&k| letter >> k).collect();
            let asked: Vec<(&[usize], (usize, usize))> = picked.iter().map(|&(_, i, j)| (truth.as_slice(), (i, j))).collect();
            let reads = realization.read_energy_central_squares(field, &asked, void, &steps).map_err(|e| e.to_string())?;
            read_regions += (3 + 4 * steps.len()) * picked.len();
            for (&(b, i, j), square) in picked.iter().zip(&reads) {
                let Some(r) = square else { continue };
                let cells: Vec<String> = r.iter().flat_map(|&(x, y)| [(x << 4).to_string(), (y << 4).to_string()]).collect();
                row(&mut rows, &format!("{k}\t{b}\t{}\t{}\t{}\n", i - q.len(), j - q.len(), cells.join("\t")))?;
                written += 1;
            }
            continue;
        }
        if field.declaration.energy {
            // The step is read on a letter's own weight in the uniform mixture, `ε = 2^(−4)/A` of a mixture's weight (four
            // times that wide), so every moved mixture stays a mixture at any alphabet. [agent-inferred, November 7: theory's
            // 2^(−6) and 2^(−4) of the five-letter tiny field are 0.08 and 0.31 of a letter's weight there.]
            let eps = ((1u32 << 16) / field.declaration.alphabet as u32) >> ENERGY_EPS_SHIFT;
            let asked: Vec<(&[usize], (usize, usize))> = picked.iter().map(|&(_, i, j)| (truth.as_slice(), (i, j))).collect();
            let reads = realization.read_energy_squares(field, &asked, void, eps).map_err(|e| e.to_string())?;
            read_regions += 13 * picked.len();
            for (&(b, i, j), square) in picked.iter().zip(&reads) {
                let Some(sq) = square else { continue };
                // The attribution read on the faces' logits (2^(−16) bits), written on the curl's 2^(−20) bits.
                row(&mut rows, &format!("{k}\t{b}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n", i - q.len(), j - q.len(), sq.lambda_i, sq.lambda_j, sq.small_i << 4, sq.small_j << 4, sq.wide_i << 4, sq.wide_j << 4, sq.zlambda_i, sq.zlambda_j, sq.glambda, sq.floors))?;
                written += 1;
            }
            continue;
        }
        let read = square_reads(field, void, &truth, &picked, realization)?;
        read_regions += read.regions;
        for (&(b, i, j), square) in picked.iter().zip(&read.squares) {
            let Some(sq) = square else { continue };
            row(&mut rows, &format!("{k}\t{b}\t{}\t{}\t{}\t{}\t-\t-\t-\t-\t-\t-\t-\t-\n", i - q.len(), j - q.len(), sq.lambda_i, sq.lambda_j))?;
            written += 1;
        }
    }
    println!("FIELD_CURL problems={n} squares={written} regions={read_regions} ms={}", started.elapsed().as_millis());
    Ok(())
}

/// [measurement; agent-inferred, November 5, §16.45] **`reach-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD
/// HELD_SHA COUNT OUT`**: how far the question reaches into a blank answer (the unified-theory reading of November 5: a
/// turned head's skin is `e^(−2π|σ_i − σ_j|/n)`, `σ` its clock's variation, so a blank run at its expected duration
/// stretches the answer away from its question, and the writer's first state, every answer place blank, pays it most). In
/// that state (every answer place and the first void open beside the question), for each of the first `COUNT` held
/// problems and each open place: its duration on each paced head at the last tick (the clock that tick ran), its variation
/// from the question's last site (those durations summed up to it), and its truth's code beside its own question and
/// beside the next problem's (the foil, whose difference is the question's reach). Writes `REACH.tsv` (private, of the
/// held answers) and prints the codes by place. A reading only.
pub(super) fn reach_field(args: &[String], realization: &mut dyn FieldRealization) -> Result<()> {
    if args.len() != 11 {
        return Err("reach-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD HELD_SHA COUNT OUT".into());
    }
    let started = std::time::Instant::now();
    let learner = FieldLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let field = &learner.field;
    let d = field.declaration;
    let units = units_of(&args[5], &args[6])?;
    let codec = FieldCodec::from_text(std::str::from_utf8(&pinned_read(&args[3], &args[4], CODEC_BUDGET)?)?, units)?;
    let held = problems_of(&pinned_read(&args[7], &args[8], READ_BUDGET as usize)?);
    let n = count(&args[9])?.min(held.len());
    let out = Path::new(&args[10]);
    std::fs::create_dir(out)?;
    let paced = d.paced_heads();
    let one = 1i64 << holonics::hnn::tower::field::PACE_BITS;
    let heads: Vec<String> = (0..paced).flat_map(|p| [format!("kappa{p}"), format!("variation{p}")]).collect();
    let mut rows = rows_file(&out.join("REACH.tsv"), &format!("problem\tplace\tplaces\tcode_own\tcode_foil\t{}\n", heads.join("\t")))?;
    let questions: Vec<Vec<usize>> = held.iter().take(n).map(|(q, _)| codec.encode(&question_text(q))).collect::<std::result::Result<_, _>>()?;
    // By place from the question, on doubling spans `[0, 1), [1, 2), [2, 4), …`: places, own code, foil code.
    let mut spans = vec![(0usize, 0i64, 0i64); (usize::BITS - d.reach.leading_zeros()) as usize + 1];
    for k in 0..n {
        let a = codec.encode(&held[k].1)?;
        let (q, fq) = (&questions[k], &questions[(k + 1) % n]);
        let region_of = |q: &[usize]| -> (Vec<usize>, Vec<bool>) {
            let mut classes: Vec<usize> = q.iter().chain(&a).copied().collect();
            classes.push(codec.void());
            let open = (0..classes.len()).map(|t| t >= q.len()).collect();
            (classes, open)
        };
        let ((own, own_open), (foil, foil_open)) = (region_of(q), region_of(fq));
        if own.len() > d.reach || foil.len() > d.reach {
            continue;
        }
        let own_region = Region { classes: &own, unresolved: &own_open, faces: &[], locked: &[], echo: &[], domain: None, port: None };
        let foil_region = Region { classes: &foil, unresolved: &foil_open, faces: &[], locked: &[], echo: &[], domain: None, port: None };
        let faces_own = realization.read_faces(field, std::slice::from_ref(&own_region)).map_err(|e| e.to_string())?.remove(0);
        let faces_foil = realization.read_faces(field, std::slice::from_ref(&foil_region)).map_err(|e| e.to_string())?.remove(0);
        let places = a.len() + 1;
        let sites: Vec<usize> = (q.len()..own.len()).collect();
        let clocks = realization.read_blank_clocks(field, &own_region, &sites).map_err(|e| e.to_string())?;
        let mut variation = vec![0i64; paced];
        for j in 0..places {
            let code = |faces: &[Option<holonics::hnn::tower::TowerFace>], at: usize| -> std::result::Result<i64, String> {
                let face = faces[at].as_ref().ok_or("an open place with no face")?;
                Ok(holonics::hnn::tower::face_code(face.masses[own[q.len() + j]], face.total))
            };
            let (c_own, c_foil) = (code(&faces_own, q.len() + j)?, code(&faces_foil, fq.len() + j)?);
            // The clock the last tick ran at this place; one on a head whose last tick reads no blank clock there.
            let kappa: Vec<i64> = match clocks[j].ticks.last().and_then(Option::as_ref) {
                Some((rates, _)) => rates.clone(),
                None => vec![one; paced],
            };
            let mut cells = Vec::with_capacity(2 * paced);
            for (p, &rate) in kappa.iter().enumerate() {
                variation[p] += rate;
                cells.push(format!("{rate}\t{}", variation[p]));
            }
            row(&mut rows, &format!("{k}\t{j}\t{places}\t{c_own}\t{c_foil}\t{}\n", cells.join("\t")))?;
            let s = &mut spans[(usize::BITS - j.leading_zeros()) as usize];
            s.0 += 1;
            s.1 += c_own;
            s.2 += c_foil;
        }
    }
    for (span, &(count, own, foil)) in spans.iter().enumerate().filter(|(_, s)| s.0 > 0) {
        let from = if span == 0 { 0 } else { 1usize << (span - 1) };
        println!("FIELD_REACH from={from} places={count} own_bits_a_class={} foil_bits_a_class={} question_bits_a_class={}", bits(own, count), bits(foil, count), bits(foil - own, count));
    }
    let (count, own, foil) = spans.iter().fold((0, 0, 0), |t, s| (t.0 + s.0, t.1 + s.1, t.2 + s.2));
    println!("FIELD_REACH_DONE problems={n} places={count} own_bits_a_class={} foil_bits_a_class={} ms={}", bits(own, count), bits(foil, count), started.elapsed().as_millis());
    Ok(())
}

/// [measurement; agent-inferred, November 6, the unified-theory reading of 00:58] **`order-field STATE STATE_SHA CODEC
/// CODEC_SHA UNITS UNITS_SHA HELD HELD_SHA COUNT OUT`**: each order's writer's code of the first `COUNT` held answers, the
/// truth's surprise summed over the states that order meets, each place read with what the order resolved before it (its
/// excess over the truth's entropy is that joint's divergence, so the lower code marks the closer joint, no write drawn). In
/// place order a state is the question and the answer's first `k` places, read at its frontier on the frontier's own class
/// (the void where the answer ends), `k` from 0 to the end; in the writer's keyed octave order (its key the state's hash, as
/// `length-field` draws) each place is read beside every place the order resolved before it, a void closing the places past
/// it. Each region is cut `NEAR` places past its last resolved or read place (the silent room past it is heard only through the
/// near field). [the unified-theory reading of 01:40] And the masks' own order: the answer and its near tail (the region cut at
/// `q + L + NEAR`, `L` the answer's places) coded in a keyed uniform order of its places, each read beside what that order
/// resolved before it, plus the length's code from the opening's faces: the opening's void mass at `t` read as `P(L ≤ t)`, so
/// `P(L = len)` is its difference at `len` and `len − 1` (an answer where that difference is not positive is counted, its
/// length code left out: the faces are no one joint's there). For one joint every order codes the same, so the orders'
/// differences also read how far the faces are from one joint. [01:47] Place order's code splits on its own faces into a length
/// part (`−log₂(1 − v)` at each place before the end, `−log₂ v` at it) and a content part (the rest: each byte's code given that
/// the answer goes on). Writes `ORDER.tsv` (problem, places, place-order code, its length part, keyed-order code, masks'-order
/// code, its length code or `-`; on `2^(−20)` bits; private, of the held answers). A reading only.
pub(super) fn order_field(args: &[String], realization: &mut dyn FieldRealization) -> Result<()> {
    if args.len() != 11 {
        return Err("order-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD HELD_SHA COUNT OUT".into());
    }
    let started = std::time::Instant::now();
    let mut learner = FieldLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    declared_clocks(&mut learner.field);
    let field = &learner.field;
    let units = units_of(&args[5], &args[6])?;
    let codec = FieldCodec::from_text(std::str::from_utf8(&pinned_read(&args[3], &args[4], CODEC_BUDGET)?)?, units)?;
    let held = problems_of(&pinned_read(&args[7], &args[8], READ_BUDGET as usize)?);
    let n = count(&args[9])?.min(held.len());
    let out = Path::new(&args[10]);
    std::fs::create_dir(out)?;
    let seed = u64::from_str_radix(&args[2][..16], 16).map_err(|_| "a state hash that is not hexadecimal")?;
    // The release's own key mix (`Field::release`), so the keyed order is the writer's.
    let mix_key = |counter: u64| -> u64 {
        let mut z = seed.wrapping_add(counter.wrapping_mul(0x9E37_79B9_7F4A_7C15));
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    };
    let void = codec.void();
    let near = holonics::hnn::tower::field::NEAR;
    let mut rows = rows_file(&out.join("ORDER.tsv"), "problem\tplaces\tplace_code\tplace_length\tkeyed_code\tmasks_code\tlength_code\n")?;
    let mut place_length_total = 0i64;
    let (mut keyed_length_total, mut given_total, mut letters_total) = (0i64, 0i64, 0usize);
    let mut given_letters_total = 0i64;
    let (mut place_total, mut keyed_total, mut places_total) = (0i64, 0i64, 0usize);
    let (mut masks_total, mut length_total, mut lengths_unread) = (0i64, 0i64, 0usize);
    for (k, (question, answer)) in held.iter().take(n).enumerate() {
        let (q, room) = opening(&codec, field, question, b"")?;
        let a = codec.encode(answer)?;
        let end = a.len().min(room - 1);
        let truth = |t: usize| -> usize { if t - q.len() < a.len() { a[t - q.len()] } else { void } };
        // Each state: its classes, its open places, the place read and its true class.
        let mut states: Vec<(Vec<usize>, Vec<bool>, usize, usize)> = Vec::new();
        for j in 0..=end {
            let frontier = q.len() + j;
            let cut = (frontier + near).min(q.len() + room);
            let classes: Vec<usize> = (0..cut).map(|t| if t < frontier { if t < q.len() { q[t] } else { a[t - q.len()] } } else { void }).collect();
            let open: Vec<bool> = (0..cut).map(|t| t >= frontier).collect();
            states.push((classes, open, frontier, truth(frontier)));
        }
        let place_states = states.len();
        let mut order: Vec<usize> = (q.len()..q.len() + room).collect();
        order.sort_by_key(|&t| (holonics::hnn::tower::field::octave_of(t + 1 - q.len()), mix_key(((k as u64) << 32) ^ t as u64 ^ (1 << 62)), t));
        let mut resolved = vec![false; q.len() + room];
        let mut last = q.len();
        for &t in &order {
            if resolved[t] {
                continue;
            }
            let cut = (t.max(last) + near).min(q.len() + room);
            let classes: Vec<usize> = (0..cut).map(|s| if s < q.len() { q[s] } else if resolved[s] { truth(s) } else { void }).collect();
            let open: Vec<bool> = (0..cut).map(|s| s >= q.len() && !resolved[s]).collect();
            states.push((classes, open, t, truth(t)));
            resolved[t] = true;
            last = last.max(t + 1);
            if truth(t) == void {
                for slot in &mut resolved[t + 1..] {
                    *slot = true;
                }
            }
        }
        let keyed_states = states.len();
        // [measurement; the unified-theory reading of November 6, 11:07] **The keyed order given its end**, the one-end writer's
        // own states: the answer's places in the same octave order, its end's `NEAR` voids given and the region cut there, each
        // place read on its own class (a letter).
        let len = a.len().min(room);
        let given_cut = (q.len() + len + near).min(q.len() + room);
        let mut given_order: Vec<usize> = (q.len()..q.len() + len).collect();
        given_order.sort_by_key(|&t| (holonics::hnn::tower::field::octave_of(t + 1 - q.len()), mix_key(((k as u64) << 32) ^ t as u64 ^ (1 << 62)), t));
        let mut given_known = vec![false; given_cut];
        for &t in &given_order {
            let classes: Vec<usize> = (0..given_cut).map(|s| if s < q.len() { q[s] } else if given_known[s] { truth(s) } else { void }).collect();
            let open: Vec<bool> = (0..given_cut).map(|s| s >= q.len() && s < q.len() + len && !given_known[s]).collect();
            states.push((classes, open, t, truth(t)));
            given_known[t] = true;
        }
        let given_states = states.len();
        // The masks' order: the answer and its near tail in a keyed uniform order.
        let span = (a.len() + near).min(room);
        let mut masks: Vec<usize> = (q.len()..q.len() + span).collect();
        masks.sort_by_key(|&t| (mix_key(((k as u64) << 32) ^ t as u64 ^ (3 << 61)), t));
        let mut known = vec![false; q.len() + span];
        for &t in &masks {
            let classes: Vec<usize> = (0..q.len() + span).map(|s| if s < q.len() { q[s] } else if known[s] { truth(s) } else { void }).collect();
            let open: Vec<bool> = (0..q.len() + span).map(|s| s >= q.len() && !known[s]).collect();
            states.push((classes, open, t, truth(t)));
            known[t] = true;
        }
        let mut codes = (0i64, 0i64, 0i64);
        let (mut place_length, mut keyed_length, mut given, mut given_letters) = (0i64, 0i64, 0i64, 0i64);
        for (c, chunk) in states.chunks(256).enumerate() {
            let regions: Vec<Region> = chunk.iter().map(|(classes, open, _, _)| Region { classes, unresolved: open, faces: &[], locked: &[], echo: &[], domain: None, port: None }).collect();
            let faces = realization.read_faces(field, &regions).map_err(|e| e.to_string())?;
            for (i, ((_, _, at, class), f)) in chunk.iter().zip(&faces).enumerate() {
                let face = f[*at].as_ref().ok_or("a read place with no face")?;
                let code = face.code(*class);
                match c * 256 + i {
                    s if s < place_states => {
                        codes.0 += code;
                        place_length += if *class == void { code } else { holonics::hnn::tower::face_code(face.total - face.masses[void], face.total) };
                    }
                    s if s < keyed_states => {
                        codes.1 += code;
                        // [the unified-theory reading of 11:07] The keyed order's length part: void or letter at each read.
                        keyed_length += if *class == void { code } else { holonics::hnn::tower::face_code(face.total - face.masses[void], face.total) };
                    }
                    s if s < given_states => {
                        given += code;
                        given_letters += holonics::hnn::tower::face_code(face.masses[*class], face.total - face.masses[void]);
                    }
                    _ => codes.2 += code,
                }
            }
        }
        // The length's code from the opening's faces: `P(L = len) = P(L ≤ len) − P(L ≤ len − 1)` on their void masses.
        let opening_classes: Vec<usize> = q.iter().copied().chain(std::iter::repeat_n(void, room)).collect();
        let opening_open: Vec<bool> = (0..opening_classes.len()).map(|t| t >= q.len()).collect();
        let opening = realization.read_faces(field, &[Region { classes: &opening_classes, unresolved: &opening_open, faces: &[], locked: &[], echo: &[], domain: None, port: None }]).map_err(|e| e.to_string())?.remove(0);
        let void_at = |t: usize| -> std::result::Result<(u128, u128), String> { let f = opening[t].as_ref().ok_or("an opening place with no face")?; Ok((f.masses[void], f.total)) };
        let (vn, tn) = void_at(q.len() + end)?;
        let length = if end == 0 {
            Some(holonics::hnn::tower::face_code(vn, tn))
        } else {
            let (vp, tp) = void_at(q.len() + end - 1)?;
            // `vn/tn − vp/tp` on the faces' own `2^(−62)` grain (a class's mass is at most `2^62`).
            let unit = 1u128 << 62;
            ((vn << 62) / tn).checked_sub((vp << 62) / tp).filter(|&p| p > 0).map(|p| holonics::hnn::tower::face_code(p, unit))
        };
        match length {
            Some(l) => length_total += l,
            None => lengths_unread += 1,
        }
        masks_total += codes.2;
        place_length_total += place_length;
        (keyed_length_total, given_total, letters_total) = (keyed_length_total + keyed_length, given_total + given, letters_total + len);
        given_letters_total += given_letters;
        row(&mut rows, &format!("{k}\t{}\t{}\t{place_length}\t{}\t{}\t{}\n", end + 1, codes.0, codes.1, codes.2, length.map_or("-".to_string(), |l| l.to_string())))?;
        (place_total, keyed_total, places_total) = (place_total + codes.0, keyed_total + codes.1, places_total + end + 1);
    }
    println!(
        "FIELD_ORDER problems={n} places={places_total} place_bits_a_place={} place_length_bits_a_place={} place_content_bits_a_place={} keyed_bits_a_place={} keyed_length_bits_a_place={} keyed_content_bits_a_place={} keyed_given_bits_a_letter={} keyed_given_off_void_bits_a_letter={} letters={letters_total} masks_bits_a_place={} masks_length_bits_a_place={} lengths_unread={lengths_unread} ms={}",
        bits(place_total, places_total),
        bits(place_length_total, places_total),
        bits(place_total - place_length_total, places_total),
        bits(keyed_total, places_total),
        bits(keyed_length_total, places_total),
        bits(keyed_total - keyed_length_total, places_total),
        bits(given_total, letters_total),
        bits(given_letters_total, letters_total),
        bits(masks_total, places_total),
        bits(length_total, places_total),
        started.elapsed().as_millis()
    );
    Ok(())
}

/// [measurement; agent-inferred, November 6, the unified-theory reading of 02:38] **`masks-field STATE STATE_SHA CODEC CODEC_SHA
/// UNITS UNITS_SHA HELD HELD_SHA COUNT ENDS OUT`**: the masks' own order as a writer, given each answer's length. For each of the
/// first `COUNT` held problems, its length `L` is the `written` places of a write's `ENDS.tsv` (a place-order write's lengths,
/// drawn from its hazard); the region is the question and `L + NEAR` places (the answer and its near tail, as the masks met
/// them), drawn one place a read in a keyed uniform order of those places (keyed by the state's hash): an answer place from its
/// face restricted to the letters (an integer draw against their masses), a near-tail place the void. Writes `SAMPLE.tsv`
/// (each answer, private, of the held answers). A reading only.
pub(super) fn masks_field(args: &[String], realization: &mut dyn FieldRealization) -> Result<()> {
    if args.len() != 12 {
        return Err("masks-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD HELD_SHA COUNT ENDS OUT".into());
    }
    let started = std::time::Instant::now();
    let mut learner = FieldLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    declared_clocks(&mut learner.field);
    let field = &learner.field;
    let units = units_of(&args[5], &args[6])?;
    let codec = FieldCodec::from_text(std::str::from_utf8(&pinned_read(&args[3], &args[4], CODEC_BUDGET)?)?, units)?;
    let held = problems_of(&pinned_read(&args[7], &args[8], READ_BUDGET as usize)?);
    let n = count(&args[9])?.min(held.len());
    let ends = std::fs::read_to_string(&args[10])?;
    let lengths: std::collections::BTreeMap<usize, usize> = ends
        .lines()
        .skip(1)
        .filter_map(|l| {
            let mut c = l.split('\t');
            Some((c.next()?.parse().ok()?, c.nth(1)?.parse().ok()?))
        })
        .collect();
    let out = Path::new(&args[11]);
    std::fs::create_dir(out)?;
    let seed = u64::from_str_radix(&args[2][..16], 16).map_err(|_| "a state hash that is not hexadecimal")?;
    let mix_key = |counter: u64| -> u64 {
        let mut z = seed.wrapping_add(counter.wrapping_mul(0x9E37_79B9_7F4A_7C15));
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    };
    let void = codec.void();
    let near = holonics::hnn::tower::field::NEAR;
    let (mut classes, mut open, mut orders, mut starts, mut spans) = (Vec::new(), Vec::new(), Vec::new(), Vec::new(), Vec::new());
    for (k, (question, _)) in held.iter().take(n).enumerate() {
        let (q, room) = opening(&codec, field, question, b"")?;
        let length = *lengths.get(&k).ok_or("a problem with no length in ENDS")?;
        let span = (length + near).min(room);
        let mut order: Vec<usize> = (q.len()..q.len() + span).collect();
        order.sort_by_key(|&t| (mix_key(((k as u64) << 32) ^ t as u64 ^ (5 << 60)), t));
        classes.push(q.iter().copied().chain(std::iter::repeat_n(void, span)).collect::<Vec<usize>>());
        open.push((0..q.len() + span).map(|t| t >= q.len()).collect::<Vec<bool>>());
        starts.push(q.len());
        spans.push(length.min(span));
        orders.push(order);
    }
    let steps = orders.iter().map(Vec::len).max().unwrap_or(0);
    for step in 0..steps {
        let active: Vec<usize> = (0..orders.len()).filter(|&k| step < orders[k].len()).collect();
        let regions: Vec<Region> = active.iter().map(|&k| Region { classes: &classes[k], unresolved: &open[k], faces: &[], locked: &[], echo: &[], domain: None, port: None }).collect();
        let faces = realization.read_faces(field, &regions).map_err(|e| e.to_string())?;
        let mut draws = Vec::with_capacity(active.len());
        for (&k, f) in active.iter().zip(&faces) {
            let t = orders[k][step];
            let c = if t - starts[k] >= spans[k] {
                void
            } else {
                let face = f[t].as_ref().ok_or("a drawn place with no face")?;
                let letters = face.total - face.masses[void];
                let u = (((mix_key(((k as u64) << 40) ^ ((t as u64) << 8) ^ 0xD) as u128) << 64) | mix_key(((k as u64) << 40) ^ ((t as u64) << 8) ^ 0xE) as u128) % letters.max(1);
                let mut acc = 0u128;
                (0..face.masses.len()).filter(|&c| c != void).find(|&c| {
                    acc += face.masses[c];
                    acc > u
                }).unwrap_or(0)
            };
            draws.push((k, t, c));
        }
        for (k, t, c) in draws {
            classes[k][t] = c;
            open[k][t] = false;
        }
    }
    let mut file = rows_file(&out.join("SAMPLE.tsv"), "")?;
    for k in 0..classes.len() {
        let places = &classes[k][starts[k]..starts[k] + spans[k]];
        row(&mut file, &format!("{k}\t{}\n", escaped(&codec.decode(places))))?;
    }
    println!("FIELD_MASKS problems={} reads={steps} ms={}", classes.len(), started.elapsed().as_millis());
    Ok(())
}

/// [definition; agent-inferred, November 6] **`ring-field STATE STATE_SHA DEPTH OUT`**: the state with its last `DEPTH` turned
/// ring sets made depth rings ([`Field::with_depth`]), their increments founded at zero, written to `OUT`.
/// [measurement; agent-inferred, November 6, the unified-theory reading of 06:50, D] **`depth-field STATE STATE_SHA CODEC CODEC_SHA
/// UNITS UNITS_SHA`**: each depth ring's located increment `r_h[u]` (its pace row on the class sheet, base zero) at the
/// brackets `( ) [ ] { }`, beside the quotes, the newline, the space and a letter, with the row's largest magnitude over every
/// class; `r` on its stored grain, the state's own integers. A reading of the constitution only: no face is read.
pub(super) fn depth_field(args: &[String]) -> Result<()> {
    if args.len() != 7 {
        return Err("depth-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA".into());
    }
    let learner = FieldLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let units = units_of(&args[5], &args[6])?;
    let codec = FieldCodec::from_text(std::str::from_utf8(&pinned_read(&args[3], &args[4], CODEC_BUDGET)?)?, units)?;
    let (field, d) = (&learner.field, learner.field.declaration);
    let width = d.alphabet + 1;
    let bytes: &[u8] = b"()[]{}\"'\n a";
    for (p, h) in (0..d.heads).filter(|&h| d.carries_moment(h)).enumerate() {
        if !d.is_depth(h) {
            continue;
        }
        let row = &field.theta[field.layout().pace + p * width..field.layout().pace + (p + 1) * width];
        let read: Vec<String> = bytes
            .iter()
            .map(|&b| match codec.encode(&[b]) {
                Ok(c) if c.len() == 1 => format!("{}={}", escaped(&[b]), row[c[0]]),
                _ => format!("{}=-", escaped(&[b])),
            })
            .collect();
        println!("FIELD_DEPTH head={h} {} largest={}", read.join(" "), row.iter().map(|v| v.unsigned_abs()).max().unwrap_or(0));
    }
    Ok(())
}

/// **`census-field FROM FROM_SHA TO TO_SHA`** (the width census's read (a), theory November 8): for each material family of
/// the later state, its declared grain, the top place its largest `|θ|` occupies beside the 31 an `i32` holds, the bottom place
/// any entry moved by between the two states (the trailing zeros of the least-moved difference), how many entries moved, how
/// many sit at zero, how many were released to zero and how many founded from it; and the averaged constitution's top place
/// beside its 39 (an `i64` eight places finer than `θ`'s `i32`). A reading of the constitution only: no face is read and nothing runs.
/// [definition; theory, November 9 00:08] **A state's averaged constitution opened at its live θ** (`average-open STATE STATE_SHA
/// OUT`): a crossing between laws, so a resumed passage averages its own θ and not another passage's (the forks from 179
/// carried law D's average). Recorded where it is done, in the run's record with its crossing; the state carries only the
/// average it now has.
pub(super) fn average_open(args: &[String]) -> Result<()> {
    if args.len() != 4 {
        return Err("average-open STATE STATE_SHA OUT".into());
    }
    let mut learner = FieldLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    learner.average = None;
    learner.average_section();
    write_new(std::path::Path::new(&args[3]), learner.to_text().as_bytes())?;
    println!("FIELD_AVERAGE_OPEN state={} out={}", &args[2][..16.min(args[2].len())], args[3]);
    Ok(())
}

/// [definition; theory, November 9 05:51] **A state of the scaled contrast moved to the one deposit** (`deposit-fold STATE
/// STATE_SHA OUT`, [`FieldLearner::deposit_folded`]): the scaled law's length `λ`, read from the state's last step against its
/// moments (the law kept its lengths in the trainer, never in a state), is folded into every family, `ρ_f ← ρ_f − log₂ λ`,
/// so the first carried step is the scaled one in every moving family. A state with no family-lengths line opens them at the
/// one rate first (its own, or the rate below it its run stepped at, `rate_shift` bits under). A crossing between laws,
/// reading-free: no face is read, and the family-lengths line is the only change, checked against the state as this source
/// writes it (a state saved before the carried deposit gains its `carried` line of zeros on any rewrite, which
/// `rewritten_as_read` reports). Prints `FIELD_DEPOSIT_FOLD` (`λ` on `2^(−32)` with the
/// partition of lengths that form the last step, `log₂ λ` on `2^(−24)` bits, in thousandths beside) and one
/// `FIELD_DEPOSIT_FOLD_FAMILY` line a family: its length before and after in thousandths of a bit, and at the state's own
/// moments the entries the scaled step moved, the entries where the folded released step is that step, one grain from it and
/// further, and those the fold forms a sub-grain step for and carries. Recorded where it is done, in the run's record with
/// its crossing.
pub(super) fn deposit_fold(args: &[String]) -> Result<()> {
    if args.len() != 4 {
        return Err("deposit-fold STATE STATE_SHA OUT".into());
    }
    let text = String::from_utf8(pinned_read(&args[1], &args[2], STATE_BUDGET)?)?;
    let learner = FieldLearner::from_text(&text).map_err(|e| e.to_string())?;
    let (folded, read) = learner.deposit_folded().map_err(|e| e.to_string())?;
    let (as_read, moved) = (learner.to_text(), folded.to_text());
    // The family lengths only: the moved text less its family-lengths line is the state's, as this source writes it.
    let rest = |t: &str| -> Vec<String> { t.lines().filter(|l| !l.starts_with("family-lengths ")).map(str::to_string).collect() };
    if rest(&moved) != rest(&as_read) || moved.lines().count() != as_read.lines().count() + usize::from(read.opened) {
        return Err("deposit-fold: the fold would change more than the family lengths".into());
    }
    write_new(std::path::Path::new(&args[3]), moved.as_bytes())?;
    let bits = holonics::hnn::tower::MATERIAL_BITS;
    let milli = |v: i128, places: u32| -> i128 { (v * 1000 + (1i128 << (places - 1))) >> places };
    println!(
        "FIELD_DEPOSIT_FOLD state={} out={} opened={} rate_shift={} lambda_q32={} lambda_low_q32={} lambda_high_q32={} lambda_milli={} log2_lambda_q24={} log2_lambda_milli={} entries={} rewritten_as_read={}",
        &args[2][..16.min(args[2].len())],
        args[3],
        u8::from(read.opened),
        read.shift,
        read.length,
        read.low,
        read.high,
        milli(read.length, 32),
        read.log2_lambda,
        milli(read.log2_lambda, bits),
        read.entries,
        u8::from(as_read == text)
    );
    let names = family_names(&folded.field);
    for (k, (fam, &(_, len, grain))) in read.families.iter().zip(&folded.field.families_all()).enumerate() {
        if len == 0 {
            continue;
        }
        let name = names.get(k).map_or_else(|| format!("family{k}"), |(n, _)| n.to_string());
        println!(
            "FIELD_DEPOSIT_FOLD_FAMILY family={name} entries={len} grain={grain} rho_milli={}->{} moving={} equal={} one={} further={} carrying={}",
            milli(fam.before, bits),
            milli(fam.after, bits),
            fam.moving,
            fam.equal,
            fam.one,
            fam.further,
            fam.carrying
        );
    }
    Ok(())
}

pub(super) fn census_field(args: &[String]) -> Result<()> {
    if args.len() != 5 {
        return Err("census-field FROM FROM_SHA TO TO_SHA".into());
    }
    let from = FieldLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let to = FieldLearner::from_text(std::str::from_utf8(&pinned_read(&args[3], &args[4], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    if from.field.theta.len() != to.field.theta.len() || from.field.families() != to.field.families() {
        return Err("census-field: the two states lay out different materials".into());
    }
    // The layout's families in the order `FieldLayout::new` pushes them.
    const NAMES: [&str; 28] = [
        "enc", "before", "after", "q", "q_bias", "v", "v_bias", "out", "out_bias", "a", "a_bias", "b", "b_bias", "w", "w_bias", "read", "read_bias",
        "moment_before", "moment_after", "temper", "probe", "probe_bias", "pace", "moment_face", "moment_face_bias", "lift_bias", "pair_c", "face_temper",
    ];
    let top = |v: &[i32]| v.iter().map(|x| 32 - x.unsigned_abs().leading_zeros()).max().unwrap_or(0);
    for (i, &(start, len, grain)) in to.field.families().iter().enumerate() {
        let (a, b) = (&from.field.theta[start..start + len], &to.field.theta[start..start + len]);
        let moved: Vec<u32> = a.iter().zip(b).filter(|(x, y)| x != y).map(|(x, y)| (i64::from(*y) - i64::from(*x)).trailing_zeros()).collect();
        let bottom = moved.iter().min().map_or("-".to_string(), u32::to_string);
        // The lowest set bit of each moved entry's change, places 0 to 7 and 8 or more, and the change's largest top place.
        let mut hist = [0usize; 9];
        moved.iter().for_each(|&z| hist[(z as usize).min(8)] += 1);
        let step_top = a.iter().zip(b).map(|(x, y)| 64 - (i64::from(*y) - i64::from(*x)).unsigned_abs().leading_zeros()).max().unwrap_or(0);
        let name = NAMES.get(i).copied().unwrap_or("?");
        let zeros = b.iter().filter(|&&x| x == 0).count();
        let released = a.iter().zip(b).filter(|(x, y)| **x != 0 && **y == 0).count();
        let founded = a.iter().zip(b).filter(|(x, y)| **x == 0 && **y != 0).count();
        let avg = to.average.as_ref().map_or("-".to_string(), |v| {
            let t = v[start..start + len].iter().map(|x| 64 - x.unsigned_abs().leading_zeros()).max().unwrap_or(0);
            format!("{t}/39")
        });
        let hist: Vec<String> = hist.iter().map(usize::to_string).collect();
        println!(
            "FIELD_CENSUS family={i}:{name} len={len} grain={grain} top={}/31 moved={} bottom_moved={bottom} lowest_bit_hist={} change_top={step_top} zeros={zeros} released={released} founded={founded} average_top={avg}",
            top(b),
            moved.len(),
            hist.join(",")
        );
    }
    Ok(())
}

pub(super) fn ring_field(args: &[String]) -> Result<()> {
    if args.len() != 5 {
        return Err("ring-field STATE STATE_SHA DEPTH OUT".into());
    }
    let mut learner = FieldLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    learner.field = learner.field.with_depth(count(&args[3])?).map_err(|e| e.to_string())?;
    std::fs::write(&args[4], learner.to_text())?;
    println!("FIELD_RING depth={} heads={} frames={} still={}", learner.field.declaration.depth, learner.field.declaration.heads, learner.field.declaration.frames, learner.field.declaration.still);
    Ok(())
}

/// [measurement; agent-inferred, November 5, §16.46] **`opening-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD
/// HELD_SHA TRAIN TRAIN_SHA COUNT OUT`**: the void's mass across the writer's opening (the unified-theory reading of November
/// 5, 07:16: the writer overruns its answers, and a byte drawn far out pins the answer at least that long). For each of the
/// first `COUNT` held problems, the region is the writer's own opening ([`opening`]: the question resolved and the codec's
/// whole extent open), and each open place's face is read through the realization: its void mass on `2^(−20)` beside the
/// held answer's length in places, and the face's leading class (its bytes in hex, `void` for the void; the lowest class on a
/// tie) with its mass, which dates a write's seed (the unified-theory reading of November 5, 22:02: a sweep's first draws all
/// come from this opening). Writes `OPENING.tsv` (problem, held length, place, void mass, lead, lead mass; private, of the held
/// answers) and `LENGTHS.tsv` (the training answers' lengths in places, as training draws them, under the extent). A
/// reading only.
/// [measurement; agent-inferred, November 6, the unified-theory reading of 09:56] **`stretch-field STATE STATE_SHA CODEC CODEC_SHA
/// UNITS UNITS_SHA HELD HELD_SHA COUNT OUT`**: each held question's opening (the question and the room, every answer place open,
/// as `opening-field` reads it), and at the silent stretch's first place, the place whose rate every place past it runs at, each
/// paced head's rate `κ₁` on `2^(−24)` at each tick whose clock the blanks set ([`Field::blank_clocks`], through the
/// realization), written to `OUT/STRETCH.tsv` (`problem head tick kappa`). A forward reading only.
pub(super) fn stretch_field(args: &[String], realization: &mut dyn FieldRealization) -> Result<()> {
    if args.len() != 11 {
        return Err("stretch-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD HELD_SHA COUNT OUT".into());
    }
    let started = std::time::Instant::now();
    let mut learner = FieldLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    declared_clocks(&mut learner.field);
    let field = &learner.field;
    let units = units_of(&args[5], &args[6])?;
    let codec = FieldCodec::from_text(std::str::from_utf8(&pinned_read(&args[3], &args[4], CODEC_BUDGET)?)?, units)?;
    let held = problems_of(&pinned_read(&args[7], &args[8], READ_BUDGET as usize)?);
    let n = count(&args[9])?.min(held.len());
    let out = Path::new(&args[10]);
    std::fs::create_dir(out)?;
    let void = codec.void();
    let mut rows = rows_file(&out.join("STRETCH.tsv"), "problem\thead\ttick\tkappa\n")?;
    let mut read = 0usize;
    for (k, (question, _)) in held.iter().take(n).enumerate() {
        let (q, open) = opening(&codec, field, question, b"")?;
        let mut classes = q.clone();
        classes.extend(std::iter::repeat_n(void, open));
        let unresolved: Vec<bool> = (0..classes.len()).map(|t| t >= q.len()).collect();
        let region = Region { classes: &classes, unresolved: &unresolved, faces: &[], locked: &[], echo: &[], domain: None, port: None };
        let clocks = realization.read_blank_clocks(field, &region, &[q.len()]).map_err(|e| e.to_string())?;
        for (tick, slot) in clocks[0].ticks.iter().enumerate() {
            let Some((kappa, _)) = slot else { continue };
            for (head, kv) in kappa.iter().enumerate() {
                row(&mut rows, &format!("{k}\t{head}\t{tick}\t{kv}\n"))?;
            }
        }
        read += 1;
    }
    println!("FIELD_STRETCH problems={read} ms={}", started.elapsed().as_millis());
    Ok(())
}

pub(super) fn opening_field(args: &[String], realization: &mut dyn FieldRealization) -> Result<()> {
    if args.len() != 13 {
        return Err("opening-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD HELD_SHA TRAIN TRAIN_SHA COUNT OUT".into());
    }
    let started = std::time::Instant::now();
    let mut learner = FieldLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    declared_clocks(&mut learner.field);
    let field = &learner.field;
    let units = units_of(&args[5], &args[6])?;
    let codec = FieldCodec::from_text(std::str::from_utf8(&pinned_read(&args[3], &args[4], CODEC_BUDGET)?)?, units)?;
    let held = problems_of(&pinned_read(&args[7], &args[8], READ_BUDGET as usize)?);
    let train = problems_of(&pinned_read(&args[9], &args[10], READ_BUDGET as usize)?);
    let n = count(&args[11])?.min(held.len());
    let out = Path::new(&args[12]);
    std::fs::create_dir(out)?;
    let mut lengths = rows_file(&out.join("LENGTHS.tsv"), "length\tanswers\n")?;
    let mut by_length: std::collections::BTreeMap<usize, usize> = std::collections::BTreeMap::new();
    for (_, a) in &train {
        let a = codec.encode(a)?;
        if a.len() < codec.answer {
            *by_length.entry(a.len()).or_default() += 1;
        }
    }
    for (length, answers) in &by_length {
        row(&mut lengths, &format!("{length}\t{answers}\n"))?;
    }
    let void = codec.void();
    let mut rows = rows_file(&out.join("OPENING.tsv"), "problem\theld\tplace\tvoid\tlead\tlead_mass\n")?;
    let mut places = 0usize;
    for (k, (question, answer)) in held.iter().take(n).enumerate() {
        let (q, open) = opening(&codec, field, question, b"")?;
        let held_length = codec.encode(answer)?.len();
        let mut classes = q.clone();
        classes.extend(std::iter::repeat_n(void, open));
        let unresolved: Vec<bool> = (0..classes.len()).map(|t| t >= q.len()).collect();
        let region = Region { classes: &classes, unresolved: &unresolved, faces: &[], locked: &[], echo: &[], domain: None, port: None };
        let faces = realization.read_faces(field, std::slice::from_ref(&region)).map_err(|e| e.to_string())?.remove(0);
        for j in 0..open {
            let face = faces[q.len() + j].as_ref().ok_or("an open place with no face")?;
            let mass = ((face.masses[void] << 20) + face.total / 2) / face.total;
            let lead = (0..face.masses.len()).rev().max_by_key(|&c| face.masses[c]).ok_or("a face with no class")?;
            let lead_mass = ((face.masses[lead] << 20) + face.total / 2) / face.total;
            let name = if lead == void { "void".to_string() } else { codec.decode(&[lead]).iter().map(|b| format!("{b:02x}")).collect() };
            row(&mut rows, &format!("{k}\t{held_length}\t{j}\t{mass}\t{name}\t{lead_mass}\n"))?;
            places += 1;
        }
    }
    println!("FIELD_OPENING problems={n} places={places} training_answers={} ms={}", by_length.values().sum::<usize>(), started.elapsed().as_millis());
    Ok(())
}

/// [measurement; agent-inferred, November 5, §16.47] **`length-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD
/// HELD_SHA COUNT SWEEPS REFINE STOP_MS OUT [READS KEY]`**: the answer's length as the writer writes it (the unified-theory reading of
/// November 5, 09:45: if the field's conditionals were one joint law, its expected length would be a martingale along the
/// writer's path). The writer of `sample-field`, draw for draw ([`Field::sample_observed`]), and at every read each
/// problem's expected length `L` = the answer places resolved as letters + `Σ (1 − p̂_∅)` over its open places, on `2^(−20)`
/// places; at the release's end its written length. Writes `LENGTH.tsv` (problem, read, pass, `L`, letters, open; one row
/// a problem a read), `ENDS.tsv` (each problem's held and written length, the read and place of its first void, and the
/// place of its last letter and the read that last drew it) and `SAMPLE.tsv` (each answer as `sample-field` writes it),
/// private, of the held answers. With `READS` and `KEY` (the unified-theory reading of November 5, 13:26): the writer is
/// keyed by `KEY` (sixteen hex digits) in place of the state's hash, so two states are read on the same keys and their
/// drifts are paired, and it stops at its sweep `READS` (`0`, never), so reads `0` to `READS` are the whole writer's, its
/// last sweep then drawing every place left and its ends not the written answer's. A reading only.
pub(super) fn length_field(args: &[String], realization: &mut dyn FieldRealization) -> Result<()> {
    if args.len() != 14 && args.len() != 16 {
        return Err("length-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD HELD_SHA COUNT SWEEPS REFINE STOP_MS OUT [READS KEY]".into());
    }
    let started = std::time::Instant::now();
    let mut learner = FieldLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    declared_clocks(&mut learner.field);
    let units = units_of(&args[5], &args[6])?;
    let codec = FieldCodec::from_text(std::str::from_utf8(&pinned_read(&args[3], &args[4], CODEC_BUDGET)?)?, units)?;
    let held = problems_of(&pinned_read(&args[7], &args[8], READ_BUDGET as usize)?);
    let (limit, sweeps, refine, stop_ms) = (count(&args[9])?, positive(&args[10])?, count(&args[11])?, positive(&args[12])? as u128);
    let out = Path::new(&args[13]);
    std::fs::create_dir(out)?;
    let field = &learner.field;
    let held = &held[..limit.min(held.len())];
    let (reads, key) = match args.get(14..16) {
        Some([reads, key]) => (count(reads)?, key.as_str()),
        _ => (0, &args[2][..]),
    };
    let seed = u64::from_str_radix(key.get(..16).ok_or("a writer's key of fewer than sixteen hex digits")?, 16).map_err(|_| "a writer's key that is not hexadecimal")?;
    let requests: Vec<(Vec<usize>, usize)> = held.iter().map(|(question, _)| opening(&codec, field, question, b"")).collect::<std::result::Result<_, String>>()?;
    let problems: Vec<(&[usize], usize)> = requests.iter().map(|(q, n)| (q.as_slice(), *n)).collect();
    let void = codec.void();
    let mut rows = rows_file(&out.join("LENGTH.tsv"), "problem\tread\tpass\tlength\tletters\topen\n")?;
    // Each problem's first void (read, place) and each place's last letter draw (the read whose draws set it).
    let mut first_void: Vec<Option<(usize, usize)>> = vec![None; problems.len()];
    let mut drawn: Vec<Vec<Option<usize>>> = problems.iter().map(|&(q, n)| vec![None; q.len() + n]).collect();
    let mut before: Option<(Vec<Vec<usize>>, Vec<Vec<bool>>, usize)> = None;
    let mut failed: Option<String> = None;
    let mut stopped = None;
    let WriterLaw { run_bits, near_tail, place_order, one_end, rest, spans, refine_order } = WriterLaw::from_env()?;
    // [measurement; agent-inferred, November 6] `FIELD_WRITER_LENGTHS`: a write's `ENDS.tsv` whose `written` places fix each
    // answer's length ([`Field::sample_runs`]'s `lengths`), the writer then writing content given its length.
    let given: Option<Vec<usize>> = match std::env::var("FIELD_WRITER_LENGTHS") {
        Ok(path) => {
            let text = std::fs::read_to_string(path)?;
            let mut by: std::collections::BTreeMap<usize, usize> = std::collections::BTreeMap::new();
            for l in text.lines().skip(1) {
                let mut c = l.split('\t');
                if let (Some(k), Some(w)) = (c.next().and_then(|v| v.parse().ok()), c.nth(1).and_then(|v| v.parse().ok())) {
                    by.insert(k, w);
                }
            }
            Some((0..problems.len()).map(|k| by.get(&k).copied().ok_or("a problem with no length in FIELD_WRITER_LENGTHS")).collect::<std::result::Result<Vec<usize>, _>>()?.into_iter().zip(&problems).map(|(l, &(_, n))| l.min(n)).collect())
        }
        Err(_) => None,
    };
    // [measurement; agent-inferred, November 6, the unified-theory reading of 18:28] `FIELD_WRITER_FROM_TRUTH`: the walk starts
    // from held's answers (within the room), their lengths given, its first pass read without drawing
    // ([`holonics::hnn::tower::field::Field::sample_runs`]'s `from`): the field's calibration on the truth, then the walk from it.
    let truth: Option<Vec<Vec<usize>>> = match std::env::var_os("FIELD_WRITER_FROM_TRUTH") {
        Some(_) => Some(held.iter().zip(&problems).map(|((_, a), &(_, n))| codec.encode(a).map(|mut c| {
            c.truncate(n);
            c
        })).collect::<std::result::Result<Vec<_>, _>>()?),
        None => None,
    };
    let given = match &truth {
        Some(t) => Some(t.iter().map(Vec::len).collect()),
        None => given,
    };
    let (mut reads_made, mut bound_sum, mut passed_sum) = (0usize, 0i128, 0usize);
    // [measurement; agent-inferred, November 5] Each refine pass's redraws and their code, `Σ −log₂ p(c)` of the class each
    // drew on the face it was drawn from, a problem a pass (`PASSES.tsv`): whether the answer's own code falls, then holds;
    // beside it the pass's drive ([`holonics::hnn::tower::field::PassDrive`]: the standing letters' code, the faces'
    // entropy, the drive, the varentropy on `2^(−40)` bits², the changes and the changes equilibrium keeps), the rest's
    // own reading.
    let mut pending: Option<(usize, Vec<Vec<(usize, holonics::hnn::tower::TowerFace)>>)> = None;
    let mut passes: std::collections::BTreeMap<(usize, usize), (usize, i64)> = std::collections::BTreeMap::new();
    let mut drives: Vec<Vec<holonics::hnn::tower::field::PassDrive>> = Vec::new();
    let answers = field
        .sample_runs(
            &problems,
            sweeps,
            refine,
            void,
            seed,
            run_bits << 20,
            near_tail,
            place_order,
            given.as_deref(),
            one_end,
            rest,
            spans,
            truth.as_deref(),
            refine_order,
            realization,
            &mut |done, _| {
                if started.elapsed().as_millis() > stop_ms || (reads > 0 && done == reads) {
                    stopped = Some(done);
                    return false;
                }
                true
            },
            &mut |r| {
                if let Some((pass, drawn)) = pending.take() {
                    for (k, list) in drawn.iter().enumerate() {
                        for (t, face) in list.iter().filter(|(t, _)| !r.open[k][*t]) {
                            let slot = passes.entry((k, pass)).or_default();
                            *slot = (slot.0 + 1, slot.1 + face.code(r.classes[k][*t]));
                        }
                    }
                }
                if r.faces.is_none() {
                    drives = r.drives.to_vec();
                }
                if let (true, Some(faces)) = (r.pass >= 1, r.faces) {
                    pending = Some((r.pass, (0..problems.len()).map(|k| (0..r.classes[k].len()).filter(|&t| r.open[k][t]).filter_map(|t| faces[k][t].clone().map(|f| (t, f))).collect()).collect()));
                }
                for (k, &(q, _)) in problems.iter().enumerate() {
                    if let Some((classes, open, read)) = &before {
                        for t in q.len()..r.classes[k].len() {
                            let changed = open[k][t] != r.open[k][t] || classes[k][t] != r.classes[k][t];
                            if changed && !r.open[k][t] && r.classes[k][t] != void {
                                drawn[k][t] = Some(*read);
                            }
                        }
                    }
                    if first_void[k].is_none() {
                        if let Some(t) = (q.len()..r.classes[k].len()).find(|&t| !r.open[k][t] && r.classes[k][t] == void) {
                            first_void[k] = Some((r.read, t - q.len()));
                        }
                    }
                    let (mut length, mut letters, mut opened) = (0i128, 0usize, 0usize);
                    for t in q.len()..r.classes[k].len() {
                        if !r.open[k][t] {
                            if r.classes[k][t] != void {
                                letters += 1;
                                length += 1 << 20;
                            }
                        } else {
                            opened += 1;
                            match r.faces.map(|f| f[k][t].as_ref()) {
                                Some(Some(face)) => length += (((face.total - face.masses[void]) << 20) / face.total) as i128,
                                Some(None) => failed = Some("an open place with no face".into()),
                                None => {}
                            }
                        }
                    }
                    if row(&mut rows, &format!("{k}\t{}\t{}\t{length}\t{letters}\t{opened}\n", r.read, r.pass)).is_err() {
                        failed = Some("LENGTH.tsv could not be written".into());
                    }
                }
                before = Some((r.classes.to_vec(), r.open.to_vec(), r.read));
                if r.faces.is_some() {
                    (reads_made, bound_sum, passed_sum) = (reads_made + 1, bound_sum + r.bound, passed_sum + r.passed);
                }
            },
        )
        .map_err(|e| e.to_string())?;
    if let Some(why) = failed {
        return Err(why.into());
    }
    let mut pass_rows = rows_file(&out.join("PASSES.tsv"), "problem\tpass\tredrawn\tcode\tstanding\tentropy\tdrive\tvarentropy\tchanges\tequilibrium\theat\n")?;
    for ((k, pass), (redrawn, code)) in &passes {
        let d = drives.get(*k).and_then(|d| d.get(pass - 1)).copied().unwrap_or_default();
        row(&mut pass_rows, &format!("{k}\t{pass}\t{redrawn}\t{code}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n", d.standing, d.entropy, d.drive(), d.varentropy, d.changes, d.equilibrium, d.heat))?;
    }
    heat_lines(&drives);
    let mut ends = rows_file(&out.join("ENDS.tsv"), "problem\theld\twritten\tfirst_void_read\tfirst_void_place\tlast_letter_place\tlast_letter_read\n")?;
    let mut file = rows_file(&out.join("SAMPLE.tsv"), "")?;
    for (k, places) in answers.iter().enumerate() {
        let q = problems[k].0.len();
        let written = places.iter().take_while(|&&c| c != void).count();
        row(&mut file, &format!("{k}\t{}\n", escaped(&codec.decode(&places[..written]))))?;
        let held_length = codec.encode(&held[k].1)?.len();
        let (fv_read, fv_place) = first_void[k].map_or(("-".to_string(), "-".to_string()), |(r, t)| (r.to_string(), t.to_string()));
        let last = if written == 0 { "-".to_string() } else { (written - 1).to_string() };
        let last_read = if written == 0 { "-".to_string() } else { drawn[k][q + written - 1].map_or("-".to_string(), |r| r.to_string()) };
        row(&mut ends, &format!("{k}\t{held_length}\t{written}\t{fv_read}\t{fv_place}\t{last}\t{last_read}\n"))?;
    }
    println!(
        "FIELD_LENGTH problems={} sweeps={sweeps} refine={}{} stopped={} run_bits={run_bits} reads={reads_made} certified_bits={} passed={passed_sum} ms={}",
        problems.len(),
        refine,
        format!("{}{}{}{}", if rest { "_rest" } else { "" }, if spans { "_spans" } else { "" }, if truth.is_some() { "_from_truth" } else { "" }, match refine_order { holonics::hnn::tower::field::RefineOrder::Keyed => "", holonics::hnn::tower::field::RefineOrder::Place => "_place", holonics::hnn::tower::field::RefineOrder::Reversed => "_reversed" }),
        stopped.map_or("-".to_string(), |s| s.to_string()),
        bits(bound_sum as i64, 1),
        started.elapsed().as_millis()
    );
    Ok(())
}

/// [definition; theory, November 7 22:08 and November 8 14:22] **A contrast read's seed**: `FIELD_CONTRAST_SEED=HEX` where it
/// is declared (so laws read from different states pair section by section), else the state's carried key, else the hash of
/// the state it opened from (`state_sha`).
fn contrast_seed(learner: &FieldLearner, state_sha: &str) -> Result<u64> {
    Ok(match (std::env::var("FIELD_CONTRAST_SEED"), learner.key) {
        (Ok(v), _) => u64::from_str_radix(&v, 16).map_err(|_| "FIELD_CONTRAST_SEED is hexadecimal")?,
        (Err(_), Some(k)) => k,
        (Err(_), None) => u64::from_str_radix(state_sha.get(..16).ok_or("a state's hash of fewer than sixteen hex digits")?, 16).map_err(|_| "a state's hash that is not hexadecimal")?,
    })
}

/// The fresh writes' key at the lap count `read` and the section `n` (its releases and sweeps).
fn writes_key(seed: u64, read: u64, n: usize) -> u64 {
    mix(seed ^ 0x9E85_15 << 40, read << 32 | n as u64)
}

/// [definition; the unified-theory readings of November 7, 05:20 and 09:36] **A member's residue class**: the first answer place
/// `r` of the class `t ≡ r (mod spacing)` that member `member` of section `n` opens at the lap count `read`, keyed by the seed, for
/// an answer of `len` places. The kernel's blocks ([`kernel_blocks`]) take their class from it.
fn residue_start(seed: u64, read: u64, n: usize, member: usize, spacing: usize, len: usize) -> usize {
    (mix(seed ^ 0xB10C << 44, read << 40 | (n as u64) << 16 | member as u64) as usize) % spacing.min(len).max(1)
}

/// [definition; the unified-theory reading of November 7, 08:13] **The kernel's two block lengths**: `k₊ = ⌈k*·2^¼⌉` and
/// `k₋ = max(1, ⌊k*·2^(−¼)⌋)`, read on `log₂ k*` (`log2_k_star`, on `2^(−16)`), or `k*` (`block_places`) twice where the length
/// is held (`FIELD_CONTRAST_BLOCK_PIN`, `FIELD_CONTRAST_WHOLE_BLOCKS`).
fn kernel_lengths(held: bool, block_places: usize, log2_k_star: i128) -> (usize, usize) {
    if held {
        return (block_places.max(1), block_places.max(1));
    }
    let up = (1..=1usize << 13).find(|&k| log2_q16(k as u64) as i128 >= log2_k_star + (1 << 14)).unwrap_or(1 << 13);
    let down = (1..=1usize << 13).rev().find(|&k| log2_q16(k as u64) as i128 <= log2_k_star - (1 << 14)).unwrap_or(1).max(1);
    (up, down)
}

/// [definition; the unified-theory readings of November 7, 07:24 and 08:13] **The kernel's blocks**: each member's answer places
/// `t ≡ r (mod spacing)` from its answer's start ([`residue_start`]), cut into blocks alternating the lengths `k₊` and `k₋`
/// ([`kernel_lengths`]; `k₊` first on even sections, `k₋` on odd), or one block a member where `whole`
/// (`FIELD_CONTRAST_WHOLE_BLOCKS`, laps 4 to 9). Returns the blocks (places of the member's region), each block's member, and
/// each block's length class (`Some(true)` k₊, `Some(false)` k₋) where it is whole, `None` where it closes short.
#[allow(clippy::too_many_arguments)]
fn kernel_blocks(set: &Problems, members: &[usize], seed: u64, read: u64, n: usize, spacing: usize, (k_up, k_down): (usize, usize), whole: bool) -> (Vec<Vec<usize>>, Vec<usize>, Vec<Option<bool>>) {
    let (mut blocks, mut owners, mut classes_of): (Vec<Vec<usize>>, Vec<usize>, Vec<Option<bool>>) = (Vec::new(), Vec::new(), Vec::new());
    for (m, &i) in members.iter().enumerate() {
        let (q, a, _) = &set[i];
        let r = residue_start(seed, read, n, m, spacing, a.len());
        let residue: Vec<usize> = (r..a.len()).step_by(spacing).map(|j| q.len() + j).collect();
        if whole {
            blocks.push(residue);
            owners.push(m);
            classes_of.push(None);
            continue;
        }
        let mut at = 0usize;
        let mut up = n % 2 == 0;
        while at < residue.len() {
            let len = if up { k_up } else { k_down };
            let end = (at + len).min(residue.len());
            blocks.push(residue[at..end].to_vec());
            owners.push(m);
            classes_of.push((end - at == len).then_some(up));
            at = end;
            up = !up;
        }
    }
    (blocks, owners, classes_of)
}

/// [definition; theory, November 9 11:39] **The sites one read of a problem's region holds**: its question, its answer and the
/// near tail of voids its room leaves, `Q + L + v` with `v = min(NEAR, room − L)`.
fn region_sites((q, a, room): &(Vec<usize>, Vec<usize>, usize)) -> u128 {
    (q.len() + a.len() + holonics::hnn::tower::field::NEAR.min(room.saturating_sub(a.len()))) as u128
}

/// [definition; theory, November 9 11:39 and 12:18] **A sweep's site reads**: the sites a whole sweep of a section's answers at
/// their true lengths reads at most, `Σ_k (L_k + 1)(Q_k + L_k + v_k)`: its opening read of every answer's region, then the
/// longest answer's steps, each proposing answer reading its whole region ([`Field::energy_sweep_at`]: a taken move's proposal
/// read is the next place's current read, so a place costs one read). `walk-field` prints it before a run, and the save law
/// projects a section of fresh writes from it ([`section_work`]), so the two count the same reads.
fn sweep_site_reads(set: &Problems, members: &[usize]) -> u128 {
    members.iter().map(|&i| (set[i].1.len() as u128 + 1) * region_sites(&set[i])).sum()
}

/// [definition; theory, November 9 11:48] **A section's law, as the save law reads its declared work** ([`section_work`]).
enum SectionLaw<'a> {
    /// Fresh writes swept whole `sweeps` times (`FIELD_CONTRAST_FRESH=SWEEPS`, the declared count), from sweep `from` (zero but
    /// in a section resumed at a sweep), opened by a release of `release_reads` reads (none from the truths or resumed).
    Fresh { sweeps: u64, from: u64, release_reads: usize },
    /// The kernel: one Metropolis–Hastings step a block from the truth, the blocks' members `owners`.
    Kernel { owners: &'a [usize] },
    /// Law D (`FIELD_CONTRAST_CONDITIONAL`, its beat and its coin): each block place against its whole conditional.
    Conditional { blocks: &'a [Vec<usize>], owners: &'a [usize], alphabet: usize },
    /// The joint release (`FIELD_CONTRAST_JOINT=READS`), at most `reads` reads.
    Joint { reads: usize },
    /// The writer as it writes (`FIELD_CONTRAST_WRITER`).
    Writer,
}

/// [definition; theory, November 9 11:48; each law's unit agent-inferred from what its section reads] **A section's declared
/// work**, the save law's projection operand, and its unit: `site_reads`, the sites of the regions its reads hold (each region
/// `Q + L + v`, [`region_sites`]), or `places`, its answer places.
/// - Fresh writes: their release, their declared sweeps (those left, in a section resumed at a sweep) times
///   [`sweep_site_reads`], and their deposit ([`FreshStops`]; since theory, November 9 13:29, whose stops fall between them).
/// - The kernel: two reads a member and two a block (the faces and the material at the truth, and at each block's proposal),
///   `2 Σ_k region_k + 2 Σ_b region_(owner b)`.
/// - Law D: one faces read a member and one material read a letter at each block place, `Σ_k region_k + alphabet·Σ_b |b|
///   region_(owner b)`; its beat and its coin read at most this.
/// - The joint release: its declared reads of every region at most, `reads·Σ_k region_k`.
/// - The writer: its answer places `Σ_k L_k`, since its reads follow its runs' entropies and no count of them is declared
///   before the section.
///
/// What a section reads beside its declared work (on the other paths, a release before its sweeps or a deposit's material
/// reads) is carried in the measured rate ([`SaveRate`]).
fn section_work(law: &SectionLaw, set: &Problems, members: &[usize]) -> (u128, &'static str) {
    let region = |m: usize| region_sites(&set[members[m]]);
    let regions: u128 = (0..members.len()).map(region).sum();
    match *law {
        SectionLaw::Fresh { sweeps, from, release_reads } => (FreshStops::of(set, members, release_reads).section(from, sweeps), "site_reads"),
        SectionLaw::Kernel { owners } => (2 * regions + 2 * owners.iter().map(|&o| region(o)).sum::<u128>(), "site_reads"),
        SectionLaw::Conditional { blocks, owners, alphabet } => (regions + alphabet as u128 * blocks.iter().zip(owners).map(|(b, &o)| b.len() as u128 * region(o)).sum::<u128>(), "site_reads"),
        SectionLaw::Joint { reads } => (reads as u128 * regions, "site_reads"),
        SectionLaw::Writer => (members.iter().map(|&i| set[i].1.len() as u128).sum(), "places"),
    }
}

/// [definition; theory, November 9 11:48] **The run's largest measured rate**: of the sections measured so far in this run, the
/// one whose measured time over its declared work is the largest, kept as its pair `(ms, work)` undivided (two rates compared by
/// their cross products). A section of `w` units projects `⌈w·ms/work⌉` ms.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct SaveRate {
    ms: u128,
    work: u128,
}

impl SaveRate {
    /// The larger of `rate` and a section's `ms` over its `work`; a section of no declared work measures no rate.
    fn larger(rate: Option<SaveRate>, ms: u128, work: u128) -> Option<SaveRate> {
        match rate {
            _ if work == 0 => rate,
            Some(r) if r.ms.saturating_mul(work) >= ms.saturating_mul(r.work) => Some(r),
            _ => Some(SaveRate { ms, work }),
        }
    }

    /// The projected milliseconds of a section of `work` units, rounded up.
    fn project(self, work: u128) -> u128 {
        work.saturating_mul(self.ms).div_ceil(self.work)
    }
}

/// [definition; theory, November 9 11:48] **The save law's test at a section's start**: save when the time since the last saved
/// state, `since_ms`, plus the section's projected time would pass the hour, `since + projected > hour` (a section that would
/// end on the hour does not pass it). Before the run has measured a section there is no projection (`None`), and the
/// test is the plain hour, `since ≥ hour`.
fn save_due(since_ms: u128, projected_ms: Option<u128>, hour_ms: u128) -> bool {
    match projected_ms {
        Some(p) => since_ms.saturating_add(p) > hour_ms,
        None => since_ms >= hour_ms,
    }
}

/// [definition; theory, November 9 11:48, 12:18 and the unit rule after] **The save law's clock**, in milliseconds from the
/// run's start: when the last saved state was written, the run's largest measured rate, the run's largest measured held read,
/// and the section now open. A section opens after any save at its start and closes at its last print, or before a held read
/// it makes (a lap's tenth on the kernel and law D paths), so its measured time holds its sweeps, its deposit and its prints,
/// and every rate is per unit of its declared work. A held read is its own row: its time is kept as the largest held read
/// (the opening read, each save's, each tenth's and each lap end's feed it), and a section in which a tenth's read falls
/// projects its work at the rate plus that largest held read. A save's held read is counted once, from the state's write, in
/// the time since the last save.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct SaveClock {
    saved_ms: u128,
    rate: Option<SaveRate>,
    held: Option<u128>,
    open: Option<(u128, u128)>,
}

impl SaveClock {
    /// The time since the last saved state, at `now_ms`.
    fn since(&self, now_ms: u128) -> u128 {
        now_ms.saturating_sub(self.saved_ms)
    }

    /// A section of `work` units projected at the measured rate, plus the largest held read where a tenth's read falls in it
    /// (none before the run has measured a section).
    fn projected(&self, work: u128, tenth_read: bool) -> Option<u128> {
        self.rate.map(|r| r.project(work) + if tenth_read { self.held.unwrap_or(0) } else { 0 })
    }

    /// A state written at `now_ms`.
    fn saved(&mut self, now_ms: u128) {
        self.saved_ms = now_ms;
    }

    /// A held read that took `ms`: the largest so far is kept.
    fn held_read(&mut self, ms: u128) {
        self.held = Some(self.held.map_or(ms, |h| h.max(ms)));
    }

    /// A section of `work` units opens at `now_ms`; a section left open (one skipped unread) is dropped unmeasured.
    fn open(&mut self, work: u128, now_ms: u128) {
        self.open = Some((work, now_ms));
    }

    /// The open section closes at `now_ms`, its last print or the start of its own held read: its time over its declared work
    /// meets the rate. A closed clock closes nothing.
    fn close(&mut self, now_ms: u128) {
        if let Some((work, at)) = self.open.take() {
            self.rate = SaveRate::larger(self.rate, now_ms.saturating_sub(at), work);
        }
    }
}

/// [definition; theory, November 7 19:50] **A tenth's held read falls at section `n`** (from zero) of a lap of `sections`, the
/// lap's tenths printed so far `tenths_printed`: the tenth `⌊(n + 1)·10/sections⌋` passes the last printed, and the section is
/// not the lap's last (whose read is the lap's end). The kernel and law D paths read the held places there without HostHeld,
/// and the save law projects that read at the section's start.
fn tenth_read_falls(n: usize, sections: usize, tenths_printed: usize) -> bool {
    (n + 1) * 10 / sections.max(1) > tenths_printed && n + 1 < sections
}

/// [definition; theory, November 8 14:46 and 22:04, November 9 13:29] **The fresh writes' sweeps**: whole sweeps of the energy's
/// own kernel over `active` at the field's own `T` ([`holonics::hnn::tower::field::Field::energy_sweep_at`], cool 0), from sweep
/// `from` to sweep `sweeps` (from zero), sweep `s` keyed `mix(key, 100 + s)`. `at_start` hears each sweep's index (from zero)
/// and the writes as that sweep meets them, before it runs (the save law's sweep stop); `each` hears each sweep's number (from
/// one), the places moved and proposed, each write's energy a place, the writes and the sweep's milliseconds. The sweeps only
/// read the field, and each opens with a read of every write's region and keys its coins by its own number, so the writes'
/// letters are the whole state between two sweeps: sweeps `from..sweeps` from the writes after `from` sweeps are the
/// uninterrupted sweeps' tail.
#[allow(clippy::too_many_arguments)]
fn fresh_sweeps_at(field: &Field, problems: &[(&[usize], usize)], active: &mut [Vec<usize>], from: u64, sweeps: u64, key: u64, void: usize, realization: &mut dyn FieldRealization, at_start: &mut dyn FnMut(u64, &[Vec<usize>]) -> Result<()>, each: &mut dyn FnMut(u64, usize, usize, &[i128], &[Vec<usize>], u128)) -> Result<()> {
    for sweep in from..sweeps {
        at_start(sweep, active)?;
        let t0 = std::time::Instant::now();
        let (mv, pr, en) = field.energy_sweep_at(problems, active, None, void, 0, mix(key, 100 + sweep), realization, &mut |_, _| {}).map_err(|e| e.to_string())?;
        each(sweep + 1, mv, pr, &en, active, t0.elapsed().as_millis());
    }
    Ok(())
}

/// [measurement; theory, November 8 22:04] **The writes' retention**: the share of their places at their truth's letter, in
/// thousandths (`FIELD_FRESH_RETAIN`), read afresh from the writes and the truths' answers at each sweep.
fn retention_milli(active: &[Vec<usize>], answers: &[&[usize]]) -> usize {
    let places: usize = active.iter().map(|a| a.len()).sum::<usize>().max(1);
    let agree: usize = active.iter().zip(answers).map(|(a, t)| a.iter().zip(t.iter()).filter(|(x, y)| x == y).count()).sum();
    agree * 1000 / places
}

/// The joint release's reads that open the fresh writes (`FieldLearner`'s field, [`Field::energy_release`]).
const WRITES_RELEASE_READS: usize = 64;

/// [definition; theory, November 9 13:29] **A fresh section's stops**: the declared work, in site reads, between the save law's
/// stops on the fresh-writes path. The section's start stops before its release (`release`, at most
/// [`WRITES_RELEASE_READS`] reads of every region, none where the writes start at the truths or are resumed), each sweep's
/// start stops before it (`sweep`, [`sweep_site_reads`]), and the last sweep runs on into the deposit (`deposit`, the two
/// material reads of each write's region and its truth's) and the next section's start.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct FreshStops {
    release: u128,
    sweep: u128,
    deposit: u128,
}

impl FreshStops {
    fn of(set: &Problems, members: &[usize], release_reads: usize) -> Self {
        let regions: u128 = members.iter().map(|&i| region_sites(&set[i])).sum();
        FreshStops { release: release_reads as u128 * regions, sweep: sweep_site_reads(set, members), deposit: 2 * regions }
    }

    /// The section's declared work from sweep `from` of `sweeps`: its release, its sweeps left and its deposit.
    fn section(&self, from: u64, sweeps: u64) -> u128 {
        self.release + u128::from(sweeps.saturating_sub(from)) * self.sweep + self.deposit
    }

    /// The work from sweep `s`'s start to the next stop: the sweep, and after the last the deposit.
    fn at_sweep(&self, s: u64, sweeps: u64) -> u128 {
        self.sweep + if s + 1 == sweeps { self.deposit } else { 0 }
    }
}

/// [definition; theory, November 9 13:29] **A sweep save's writes** (`STATE.<lap>.<section>.<done>.writes`). Between two sweeps
/// of a fresh section the learner is the section's opening state (its sweeps only read the field; only the deposit and the
/// averaged constitution move it), each sweep opens with its own read of every region and keys its coins by its own number, and
/// the retention reading is formed afresh from the writes and their truths; so the learner (`STATE.<lap>.<section>`, named by
/// its hash) and the writes' letters are the whole state, and nothing else is carried. Text, one field a line:
/// `field-sweep-writes v1`, then `read R section N done S sweeps K key HEX start truth|release state SHA256`, then one line a
/// write, `write J LEN C,C,…` (its classes in the codec's alphabet; private, the field's own letters for private questions).
#[derive(Clone, Debug, PartialEq, Eq)]
struct SweepWrites {
    read: u64,
    section: usize,
    done: u64,
    sweeps: u64,
    key: u64,
    from_truth: bool,
    state: String,
    writes: Vec<Vec<usize>>,
}

impl SweepWrites {
    fn to_text(&self) -> String {
        let mut text = format!(
            "field-sweep-writes v1\nread {} section {} done {} sweeps {} key {:016x} start {} state {}\n",
            self.read,
            self.section,
            self.done,
            self.sweeps,
            self.key,
            if self.from_truth { "truth" } else { "release" },
            self.state
        );
        for (j, w) in self.writes.iter().enumerate() {
            text.push_str(&format!("write {j} {} {}\n", w.len(), w.iter().map(|c| c.to_string()).collect::<Vec<_>>().join(",")));
        }
        text
    }

    fn from_text(text: &str) -> Result<Self> {
        let mut lines = text.lines();
        if lines.next() != Some("field-sweep-writes v1") {
            return Err("a sweep save's writes open with field-sweep-writes v1".into());
        }
        let head: Vec<&str> = lines.next().ok_or("a sweep save's writes without their index")?.split(' ').collect();
        let named = ["read", "section", "done", "sweeps", "key", "start", "state"];
        if head.len() != 2 * named.len() || head.iter().step_by(2).zip(named).any(|(a, b)| *a != b) {
            return Err("a sweep save's index is read R section N done S sweeps K key HEX start truth|release state SHA256".into());
        }
        let number = |k: usize| -> Result<u64> { head[2 * k + 1].parse().map_err(|_| format!("a sweep save's {} is a count", named[k]).into()) };
        let (read, section, done, sweeps) = (number(0)?, number(1)? as usize, number(2)?, number(3)?);
        let key = u64::from_str_radix(head[9], 16).map_err(|_| "a sweep save's key is hexadecimal")?;
        let from_truth = match head[11] {
            "truth" => true,
            "release" => false,
            _ => return Err("a sweep save's start is truth or release".into()),
        };
        let state = head[13].to_string();
        if state.len() != 64 || !state.bytes().all(|c| c.is_ascii_hexdigit()) || done >= sweeps {
            return Err("a sweep save names its state's SHA-256 and a sweep before its last".into());
        }
        let mut writes = Vec::new();
        for (j, line) in lines.enumerate() {
            let parts: Vec<&str> = line.split(' ').collect();
            if parts.len() != 4 || parts[0] != "write" || parts[1].parse::<usize>().ok() != Some(j) {
                return Err(format!("a sweep save's write {j} is write J LEN C,C,…").into());
            }
            let classes: Vec<usize> = parts[3].split(',').map(|c| c.parse::<usize>()).collect::<std::result::Result<_, _>>().map_err(|_| format!("a sweep save's write {j} holds classes"))?;
            if parts[2].parse::<usize>().ok() != Some(classes.len()) || classes.is_empty() {
                return Err(format!("a sweep save's write {j} is not its length").into());
            }
            writes.push(classes);
        }
        Ok(SweepWrites { read, section, done, sweeps, key, from_truth, state, writes })
    }
}

/// [definition; the unified-theory reading of November 7, 09:36; theory, November 9 05:51] **The writes' deposit**: each write
/// `active[j]` read as its region (its question, the write and the near tail of voids its room leaves) against its truth
/// `truths[j]`, every site resolved, deposited through the one deposit ([`FieldLearner::section_contrast`]). The fresh
/// writes' sections deposit through it, and the sweep resume's acceptance reads it.
fn writes_deposit(learner: &mut FieldLearner, problems: &[(&[usize], usize)], truths: &[Vec<usize>], active: &[Vec<usize>], void: usize, realization: &mut dyn FieldRealization) -> Result<holonics::hnn::tower::field::ContrastReceipt> {
    let m = active.len();
    let writes_now = writes_regions(problems, active, void);
    let resolved: Vec<Vec<bool>> = truths.iter().map(|t| vec![false; t.len()]).collect();
    let truth_views: Vec<Region> = truths[..m].iter().zip(&resolved).map(|(c, u)| Region { classes: c, unresolved: u, faces: &[], locked: &[], echo: &[], domain: None, port: None }).collect();
    let write_views: Vec<Region> = writes_now.iter().zip(&resolved).map(|(c, u)| Region { classes: c, unresolved: u, faces: &[], locked: &[], echo: &[], domain: None, port: None }).collect();
    Ok(learner.section_contrast(&truth_views, &write_views, realization).map_err(|e| e.to_string())?)
}

/// Each write's region: its question, the write and the near tail of voids its room leaves.
fn writes_regions(problems: &[(&[usize], usize)], active: &[Vec<usize>], void: usize) -> Vec<Vec<usize>> {
    let near = holonics::hnn::tower::field::NEAR;
    active
        .iter()
        .enumerate()
        .map(|(j, w)| {
            let (q, room) = problems[j];
            let mut c: Vec<usize> = q.iter().chain(w).copied().collect();
            c.extend(std::iter::repeat_n(void, near.min(room - w.len())));
            c
        })
        .collect()
}

/// [measurement; theory, November 9 14:30] **The writes' contrast covector by problem**, a reading before the deposit: each
/// write against its truth, read as [`writes_deposit`] reads them, through
/// [`holonics::hnn::tower::field::contrast_pair_covectors`] (one material read of every truth and write, each pair's
/// `(1/T)(∂G/∂θ(truth) − ∂G/∂θ(write))` released to the deposit's chart). It reads the field and changes nothing.
fn writes_pairs(field: &Field, problems: &[(&[usize], usize)], truths: &[Vec<usize>], active: &[Vec<usize>], void: usize, realization: &mut dyn FieldRealization) -> Result<Vec<Vec<i128>>> {
    let m = active.len();
    let writes_now = writes_regions(problems, active, void);
    let resolved: Vec<Vec<bool>> = truths.iter().map(|t| vec![false; t.len()]).collect();
    let truth_views: Vec<Region> = truths[..m].iter().zip(&resolved).map(|(c, u)| Region { classes: c, unresolved: u, faces: &[], locked: &[], echo: &[], domain: None, port: None }).collect();
    let write_views: Vec<Region> = writes_now.iter().zip(&resolved).map(|(c, u)| Region { classes: c, unresolved: u, faces: &[], locked: &[], echo: &[], domain: None, port: None }).collect();
    let pairs = holonics::hnn::tower::field::contrast_pair_covectors(field, &truth_views, &write_views, realization).map_err(|e| e.to_string())?;
    Ok(pairs.into_iter().map(|p| p.covector).collect())
}

/// `Σ v²` over `v`, in an unbounded carrier.
fn square_sum<'a>(v: impl Iterator<Item = &'a i128>) -> num_bigint::BigUint {
    v.map(|x| num_bigint::BigUint::from(x.unsigned_abs()).pow(2)).sum()
}

/// `⟨a, b⟩`, in an unbounded carrier.
fn dot_sum(a: &[i128], b: &[i128]) -> num_bigint::BigInt {
    a.iter().zip(b).map(|(&x, &y)| num_bigint::BigInt::from(x) * num_bigint::BigInt::from(y)).sum()
}

/// The cosine of two vectors with squared norms `aa` and `bb` and product `ab`, in signed thousandths: `⌊1000·ab /
/// ⌊√(aa·bb)⌋⌋` toward zero, held to `±1000`; none where either vector is zero.
fn cosine_milli(ab: &num_bigint::BigInt, aa: &num_bigint::BigUint, bb: &num_bigint::BigUint) -> Option<i64> {
    let root = (aa * bb).sqrt();
    if root == num_bigint::BigUint::from(0u8) {
        return None;
    }
    let c = ab * num_bigint::BigInt::from(1000) / num_bigint::BigInt::from(root);
    num_traits::ToPrimitive::to_i64(&c.clamp(num_bigint::BigInt::from(-1000), num_bigint::BigInt::from(1000)))
}

/// [measurement; theory, November 9 14:30] **The delete-one jackknife SE** of a reading from its leave-one-out values
/// `x_(−p)` over `n` problems: `√((n − 1)/n · Σ_p (x_(−p) − x̄)²) = √((n − 1)·Σ_p (n·x_(−p) − S)² / n³)`, `S = Σ_p x_(−p)`,
/// floored; none under two problems.
fn jackknife_se(loo: &[num_bigint::BigUint]) -> Option<num_bigint::BigUint> {
    let n = loo.len();
    if n < 2 {
        return None;
    }
    let total: num_bigint::BigInt = loo.iter().map(|x| num_bigint::BigInt::from(x.clone())).sum();
    let spread: num_bigint::BigInt = loo.iter().map(|x| (num_bigint::BigInt::from(x.clone()) * num_bigint::BigInt::from(n) - &total).pow(2)).sum();
    let variance = spread * num_bigint::BigInt::from(n - 1) / num_bigint::BigInt::from(n).pow(3);
    variance.to_biguint().map(|v| v.sqrt())
}

/// [measurement; theory, November 9 14:30] **A section's covector by family** (`FIELD_COVECTOR_SECTION`), a reading. The
/// section's contrast covector is `g = Σ_p g(p)` over its problems' covectors (`pairs`, [`writes_pairs`]), in the deposit's
/// chart (`(1/T)·∂G/∂θ` released to `2^(−24)` of the material on a family at the material's grain and `40 − 24` places further
/// on any other, the unit the family's moments take; it stands within `⌊(n + 1)/2⌋` units of the covector the deposit takes,
/// entry by entry, which releases the pairs' sum once). For every family with entries, one line:
/// - `norm`: `‖g_f‖ = ⌊√Σ g²⌋`, in that unit;
/// - `norm_se`: the delete-one jackknife SE of `‖g_f‖` over the section's problems ([`jackknife_se`] of `‖g_f − g_f(p)‖`);
/// - `cos_prev_milli`: the cosine of `g_f` with the previous section's (`prev`), signed thousandths, `-` where none;
/// - `step_norm`, `step_cos_milli`: the norm of the step `s_f` the deposit took on the family (`step`, `θ` moving by `−s_f`:
///   as formed on `2^(−24)` of the family's grain, `step_unit=formed`, or as moved on the grain, `θ` before less `θ` after,
///   `step_unit=moved`), and the cosine of `θ`'s move `−s_f` with `−g_f`, signed thousandths: positive where `θ` moved down
///   the covector.
///
/// Returns the lines (after `lap` and `n`) and `g`. Sums are checked on `i128`, squares and products unbounded.
fn covector_section_lines(field: &Field, pairs: &[Vec<i128>], prev: Option<&[i128]>, step: &[i128], step_unit: &str) -> Result<(Vec<String>, Vec<i128>)> {
    const OVER: &str = "a section covector past its 128-bit carrier";
    let material = field.material_len();
    if pairs.iter().any(|p| p.len() != material) || step.len() != material || prev.is_some_and(|p| p.len() != material) {
        return Err("a section covector of another length than the field's material".into());
    }
    let mut g = vec![0i128; material];
    for pair in pairs {
        for (v, &x) in g.iter_mut().zip(pair) {
            *v = v.checked_add(x).ok_or(OVER)?;
        }
    }
    let names = family_names(field);
    let mut lines = Vec::new();
    for &(start, len, _) in field.families_all().iter().filter(|fam| fam.1 > 0) {
        let range = start..start + len;
        let gf = &g[range.clone()];
        let gg = square_sum(gf.iter());
        let loo: Vec<num_bigint::BigUint> = pairs
            .iter()
            .map(|pair| -> Result<num_bigint::BigUint> {
                let rest: Vec<i128> = gf.iter().zip(&pair[range.clone()]).map(|(&a, &b)| a.checked_sub(b).ok_or(OVER)).collect::<std::result::Result<_, _>>()?;
                Ok(square_sum(rest.iter()).sqrt())
            })
            .collect::<Result<_>>()?;
        let cos_prev = prev.and_then(|p| cosine_milli(&dot_sum(gf, &p[range.clone()]), &gg, &square_sum(p[range.clone()].iter())));
        let sf = &step[range.clone()];
        let ss = square_sum(sf.iter());
        // `−s_f` against `−g_f` is `s_f` against `g_f`.
        let step_cos = cosine_milli(&dot_sum(sf, gf), &ss, &gg);
        let shown = |v: Option<i64>| v.map_or("-".to_string(), |c| c.to_string());
        lines.push(format!(
            "family={} norm={} norm_se={} cos_prev_milli={} step_norm={} step_cos_milli={} step_unit={step_unit}",
            names.iter().find(|&&(_, at)| at == start).map_or("?", |&(name, _)| name),
            gg.sqrt(),
            jackknife_se(&loo).map_or("-".to_string(), |se| se.to_string()),
            shown(cos_prev),
            ss.sqrt(),
            shown(step_cos)
        ));
    }
    Ok((lines, g))
}

/// [definition; the unified-theory readings of November 7, 04:05 and 05:20, route (b)] **`contrast-field STATE STATE_SHA CODEC
/// CODEC_SHA UNITS UNITS_SHA TRAIN TRAIN_SHA HELD HELD_SHA SECTION LAPS PLACES LAP_MS STOP_MS OUT`**: an energy field trained by
/// meeting its own invariant kernel (a step that leaves `P ∝ 2^(−G/T)` invariant). Each training problem is a state: its question, its answer (cut to the room) and its near
/// voids, every site resolved. Each state opens one block, its answer places `t ≡ r (mod s)` from the answer's start, `s`
/// [`FieldLearner::kernel_spacing`] and `r` keyed by the lap, the section and the member, and the
/// section deposits one Metropolis–Hastings step from the truth weighed by its accept probability
/// ([`FieldLearner::section_kernel`]). Declared comparisons: `FIELD_CONTRAST_JOINT=READS`, the joint release as the
/// negative ([`holonics::hnn::tower::field::Field::energy_release`], [`FieldLearner::section_contrast`]), and
/// `FIELD_CONTRAST_WRITER=SWEEPS,REFINE`, the writer as it writes ([`WriterLaw`]). Before the first lap and after each, the
/// enumerated conditional is read at `PLACES` held places ([`enumerated_read`]). A lap starts only where `LAP_MS` fits before
/// `STOP_MS`; past `STOP_MS` the run writes `STATE.stopped` and stops. Writes `STATE.<lap>`, `STATE.<lap>.<sections done>` under
/// the save law (at most an hour apart where its projection holds; [`save_due`]) and `ENUMERATED.tsv` (private: held answers'
/// letters).
pub(super) fn contrast_field(args: &[String], realization: &mut dyn FieldRealization) -> Result<()> {
    if std::env::var("FIELD_CENSUS").is_ok_and(|v| v == "1") {
        holonics::number::census::enable();
    }
    if args.len() != 17 {
        return Err("contrast-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA TRAIN TRAIN_SHA HELD HELD_SHA SECTION LAPS PLACES LAP_MS STOP_MS OUT".into());
    }
    let started = std::time::Instant::now();
    let mut learner = FieldLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    declared_clocks(&mut learner.field);
    if !learner.field.declaration.energy {
        return Err("contrast-field trains a field whose faces are one energy's forces".into());
    }
    let units = units_of(&args[5], &args[6])?;
    let codec = FieldCodec::from_text(std::str::from_utf8(&pinned_read(&args[3], &args[4], CODEC_BUDGET)?)?, units)?;
    let train_text = problems_of(&pinned_read(&args[7], &args[8], READ_BUDGET as usize)?);
    let held_text = problems_of(&pinned_read(&args[9], &args[10], READ_BUDGET as usize)?);
    let (section, laps, places) = (positive(&args[11])?, count(&args[12])?, count(&args[13])?);
    let (lap_ms, stop_ms) = (positive(&args[14])? as u128, positive(&args[15])? as u128);
    let out = Path::new(&args[16]);
    // The declared comparison: the joint release, at most `READS` reads.
    let joint: Option<usize> = match std::env::var("FIELD_CONTRAST_JOINT") {
        Ok(v) => Some(v.trim().parse::<usize>().ok().filter(|&r| r > 0).ok_or(format!("FIELD_CONTRAST_JOINT {v}: READS"))?),
        Err(_) => None,
    };
    let spacing = FieldLearner::kernel_spacing();
    // [definition; theory, November 8 14:46] `FIELD_CONTRAST_FRESH=SWEEPS`: the section deposits against writes instead of a
    // kernel step from the truth: each section releases its problems' writes afresh from the faces at their true lengths and
    // sweeps them whole SWEEPS times at T, so nothing persists between sections (each sweep's energy printed, the last two read
    // as the lag). [theory, November 9 14:00] The carried writes of lap 13's law (`FIELD_CONTRAST_PERSISTENT`: one residue class
    // a section, sunk by eight whole sweeps where they opened) are retired; git history is their archive.
    let fresh_sweeps: Option<u64> = std::env::var("FIELD_CONTRAST_FRESH").ok().and_then(|v| v.parse().ok()).filter(|&k| k > 0);
    // [definition; theory, November 8 22:04] `FIELD_FRESH_FROM_TRUTH`: the fresh writes' chain starts at each problem's truth
    // instead of the field's release, so its SWEEPS whole sweeps at T carry the negative phase from the long chain the truth
    // melts into; each sweep's share of places still at the truth letter prints as `FIELD_FRESH_RETAIN`.
    let fresh_from_truth = std::env::var_os("FIELD_FRESH_FROM_TRUTH").is_some();
    // [measurement; theory, November 8 16:49] `FIELD_MELT=SWEEPS`: a melt from the truth, which separates learning from release.
    // At the loaded state, the first section read starts twice, from its truths and from the field's own release at their true
    // lengths (the fork's key), and each start is swept whole SWEEPS times at the field's `T` (cool 0), with no deposition.
    // `FIELD_MELT=0` gives the sweep-0 reads alone.
    let melt_sweeps: Option<u64> = std::env::var("FIELD_MELT").ok().and_then(|v| v.parse().ok());
    // [measurement; theory, November 8 20:48] `FIELD_MELT_ALL=N,M,…`: the melt reads each listed section of the walk (from
    // `FIELD_CONTRAST_FROM_SECTION`, at most the first listed) in one load, passing the others unread, none deposited, and ends after
    // the last, so a bulk read over many answers (each answer's length printed beside its energies) costs one load.
    let melt_all: Vec<usize> = std::env::var("FIELD_MELT_ALL").map(|v| v.split(',').filter_map(|x| x.trim().parse().ok()).collect()).unwrap_or_default();
    let on_writes = fresh_sweeps.is_some() || melt_sweeps.is_some();
    let conditional = std::env::var_os("FIELD_CONTRAST_CONDITIONAL").is_some();
    // [measurement; theory, November 8 11:10] `FIELD_CONTRAST_READ_ONLY`: each section is read and its learner put back as it
    // opened, so every section's code is read at the opening state and nothing is deposited (the family split's reads).
    let read_only = std::env::var_os("FIELD_CONTRAST_READ_ONLY").is_some();
    // [measurement; theory, November 8 11:35] `FIELD_SECTION_LETTERS`: each section's trained places counted by their true
    // letter, printed, and the section skipped (no read, no deposit), so the walk's letter counts cost no field time.
    let section_letters = std::env::var_os("FIELD_SECTION_LETTERS").is_some();
    // [measurement; theory, November 8 15:11] `FIELD_SAVE_AT=N`: also save at section N, so a resume from that save has an
    // unbroken twin in the same run (the resume fix's check at scale); several, comma-separated, save at each (theory, November
    // 8 17:38: the fork's continuation rests and melts at 219 and 239 without breaking its run). [theory, November 9 13:29] An
    // entry `N.S` saves at section N's sweep S instead (the sweeps done, from zero; fresh writes only), so a sweep resume has its
    // unbroken twin in the same run.
    let (save_at, save_at_sweep): (Vec<usize>, Vec<(usize, u64)>) = {
        let declared = std::env::var("FIELD_SAVE_AT").unwrap_or_default();
        let mut at = (Vec::new(), Vec::new());
        for x in declared.split(',').map(str::trim).filter(|x| !x.is_empty()) {
            match x.split_once('.') {
                Some((n, s)) => at.1.push((n.parse().map_err(|_| format!("FIELD_SAVE_AT {x}: N.S"))?, s.parse().map_err(|_| format!("FIELD_SAVE_AT {x}: N.S"))?)),
                None => {
                    if let Ok(n) = x.parse() {
                        at.0.push(n);
                    }
                }
            }
        }
        at
    };
    // [measurement; theory, November 8 17:38] `FIELD_CONDITIONAL_ROWS`: each conditional read's per-place code (micro-nats) is
    // also written to `CONDITIONAL_ROWS.txt`, one line a section, so two reads of one section pair place by place for their SE.
    let conditional_rows = std::env::var_os("FIELD_CONDITIONAL_ROWS").is_some();
    // [definition; the unified-theory reading of November 7, 21:58] `FIELD_CONTRAST_AVERAGE`: the averaged constitution moves
    // each section (`FieldLearner::average_section`) and every held read reads it; the live field keeps stepping.
    let averaging = std::env::var_os("FIELD_CONTRAST_AVERAGE").is_some();
    let coherence_every: usize = match std::env::var("FIELD_COHERENCE_EVERY") {
        Ok(v) => v.parse().map_err(|_| "FIELD_COHERENCE_EVERY is a section count".to_string())?,
        Err(_) => 0,
    };
    learner.coin_measure = std::env::var_os("FIELD_COIN_MEASURE").is_some();
    // [definition; theory, November 9 05:00] The deposit is the carried release (`FieldLearner::carried`): a state that carries
    // a `carried` line keeps its remainders, one without opens them at zero; no switch selects it.
    // [definition; theory, November 8 13:44] `FIELD_UNIGRAM=shadow|apply`: the unigram law's carried sums
    // (`FieldLearner::unigram`); a state that carries a `unigram` line keeps them, one without opens them at zero. `shadow`
    // carries them with θ untouched; `apply` also steps the bias.
    if let Ok(mode) = std::env::var("FIELD_UNIGRAM") {
        let applied = match mode.as_str() {
            "shadow" => false,
            "apply" => true,
            _ => return Err("FIELD_UNIGRAM is shadow or apply".into()),
        };
        let alphabet = learner.field.declaration.alphabet;
        learner.unigram.get_or_insert_with(|| holonics::hnn::tower::field::UnigramCarry::new(alphabet, applied)).applied = applied;
    }
    let coin_tau: Option<u32> = match std::env::var("FIELD_CONTRAST_COIN") {
        Ok(v) => Some(v.parse().map_err(|_| "FIELD_CONTRAST_COIN is the tolerance's bits".to_string())?),
        Err(_) => None,
    };
    let beat_top: Option<u32> = match std::env::var("FIELD_CONTRAST_BEAT") {
        Ok(v) => Some(v.parse().map_err(|_| "FIELD_CONTRAST_BEAT is the top band".to_string())?),
        Err(_) => None,
    };
    // `FIELD_CONTRAST_SECTIONS=N`: a declared read of the first lap's next `N` sections (theory, November 7 20:29: "the first 40
    // sections decide"), after which the learner rests as `STATE.stopped`, as at a deadline.
    let read_sections: usize = match std::env::var("FIELD_CONTRAST_SECTIONS") {
        Ok(v) => v.parse().map_err(|_| "FIELD_CONTRAST_SECTIONS is a section count".to_string())?,
        Err(_) => 0,
    };
    // `FIELD_CONTRAST_FROM_SECTION=N`: the first lap resumes a lap that was killed after its saved state `STATE.<lap>.<N>`
    // (an exterior kill, November 7 18:14): STATE is that saved state, and the lap's walk goes on from its `N`-th section
    // with the same keys; later laps walk whole.
    // [definition; theory, November 9 13:29] `FIELD_CONTRAST_FROM_WRITES=PATH`: the first lap resumes a fresh section at a sweep,
    // from a sweep save's writes (`STATE.<lap>.<N>.<S>.writes`, [`SweepWrites`]): STATE is the state the file names by its hash
    // (`STATE.<lap>.<N>`), the walk goes on from the file's section (`FIELD_CONTRAST_FROM_SECTION`, where declared, must be it),
    // and that section skips its release and runs its sweeps from the file's `S` on the file's writes, with the same keys.
    let mut from_writes: Option<SweepWrites> = match std::env::var("FIELD_CONTRAST_FROM_WRITES") {
        Ok(path) => Some(SweepWrites::from_text(std::str::from_utf8(&std::fs::read(&path)?)?)?),
        Err(_) => None,
    };
    let from_section: usize = match (std::env::var("FIELD_CONTRAST_FROM_SECTION"), &from_writes) {
        (Ok(v), w) => {
            let n: usize = v.parse().map_err(|_| "FIELD_CONTRAST_FROM_SECTION is a section count".to_string())?;
            if w.as_ref().is_some_and(|w| w.section != n) {
                return Err("FIELD_CONTRAST_FROM_SECTION is not the sweep save's section".into());
            }
            n
        }
        (Err(_), Some(w)) => w.section,
        (Err(_), None) => 0,
    };
    let whole_blocks = std::env::var_os("FIELD_CONTRAST_WHOLE_BLOCKS").is_some();
    // [the unified-theory reading of November 7, 07:24] The first section's `k*`: lap 8's acceptance of 0.234 fell between its
    // fourth and fifth block-size tenths (16.4 and 20.2 places), `FIELD_CONTRAST_BLOCK_PLACES` where declared.
    let mut block_places: usize = match std::env::var("FIELD_CONTRAST_BLOCK_PLACES") {
        Ok(v) => v.trim().parse().map_err(|_| format!("FIELD_CONTRAST_BLOCK_PLACES {v}: a count"))?,
        Err(_) => 18,
    };
    let mut log2_k_star = log2_q16(block_places as u64) as i128;
    // `FIELD_CONTRAST_BLOCK_PIN`: `k*` held at its opening (`FIELD_CONTRAST_BLOCK_PLACES`), a declared comparison with its read.
    let pinned_blocks = std::env::var_os("FIELD_CONTRAST_BLOCK_PIN").is_some();
    // The declared comparison: the writer as it writes, `SWEEPS,REFINE`.
    let writer: Option<(usize, usize)> = match std::env::var("FIELD_CONTRAST_WRITER") {
        Ok(v) => match v.split_once(',').map(|(a, b)| (a.trim().parse::<usize>(), b.trim().parse::<usize>())) {
            Some((Ok(sw), Ok(rf))) if sw > 0 => Some((sw, rf)),
            _ => return Err(format!("FIELD_CONTRAST_WRITER {v}: SWEEPS,REFINE").into()),
        },
        Err(_) => None,
    };
    // [the unified-theory reading of November 7, 06:26] The kernel steps by the moments (the evidence-shrunk Newton step it took
    // instead ran lap 6 away as its curvature fell), and the Newton terms are read beside the moments' step. [definition;
    // theory, November 9 05:51] There is one deposit: the Newton step's switch (`FIELD_CONTRAST_NEWTON`) retired with it.
    let kernel = writer.is_none() && joint.is_none();
    learner.newton_read = kernel;
    // [definition; the unified-theory reading of November 7, 06:26] **More evidence a step**: a section of `n = 16·4^k` states
    // steps at the state's rate less `k` bits (the step's relative noise falls as `√n`), and the moments count states, moving
    // `2k` bits faster. Sixteen states a section keep the state's rates.
    // The state is written at its own rate, so a later run's sections set the step from it again.
    let mut base_rate = learner.rate_bits;
    if kernel {
        let mut k = 0u32;
        while 16usize << (2 * k) < section {
            k += 1;
        }
        if 16usize << (2 * k) != section {
            return Err(format!("contrast-field's kernel steps on sections of 16·4^k states, not {section}").into());
        }
        base_rate = learner.rate_bits;
        learner.rate_bits = learner.rate_bits.checked_sub(k).ok_or("a rate below its states' evidence")?;
        learner.first_rate = holonics::hnn::tower::FIRST_RATE.saturating_sub(2 * k);
        learner.second_rate = holonics::hnn::tower::SECOND_RATE.saturating_sub(2 * k);
        // [definition; the unified-theory reading of November 7, 06:57] Each family reads its length from its own transfer,
        // and the letters' temperature joins the deposit; `FIELD_CONTRAST_ONE_RATE` keeps one rate for every family and the
        // temperature held (laps 4 and 5's law), a declared comparison.
        if std::env::var_os("FIELD_CONTRAST_ONE_RATE").is_none() {
            // A continued learner keeps the lengths its families read (carried in its text since November 7, 07:24).
            if learner.family_rates.is_none() {
                learner.open_family_rates();
            }
            // [the unified-theory reading of November 7, 09:55] Against writes the letters' temperature is held: at writes not
            // relaxed at the current `T` its covector falls toward zero as `T` grows wherever the writes sit below their truths
            // (lap 13 ran `log₂ T` from 9.7 to 24.2 bits in 150 sections until a read refused its carrier).
            learner.temper_learns = !on_writes && std::env::var_os("FIELD_CONTRAST_HOLD_T").is_none();
        } else {
            learner.family_rates = None;
        }
    }
    // [measurement; the unified-theory reading of November 7, 06:57] `FIELD_CONTRAST_LOG2T_SHIFT_MILLI`: the letters' temperature
    // moved by that many thousandths of a bit before the run (the held code read at a sharper `T`, untrained).
    if let Ok(v) = std::env::var("FIELD_CONTRAST_LOG2T_SHIFT_MILLI") {
        let milli: i64 = v.trim().parse().map_err(|_| format!("FIELD_CONTRAST_LOG2T_SHIFT_MILLI {v}: thousandths of a bit"))?;
        let at = learner.field.layout().face_temper;
        let moved = learner.field.theta[at] as i64 + milli * (1i64 << holonics::hnn::tower::MATERIAL_BITS) / 1000;
        learner.field.theta[at] = i32::try_from(moved).map_err(|_| "a temperature past its carrier")?;
        println!("FIELD_CONTRAST_LOG2T_SHIFT milli={milli} log2_t={}", learner.field.theta[at]);
    }
    std::fs::create_dir(out)?;
    let void = codec.void();
    // [definition; theory, November 7 22:08] `FIELD_CONTRAST_SEED=HEX`: a read keyed by a declared seed, so laws read from
    // different states pair section by section; laps keep the state-keyed walk.
    // [definition; theory, November 8 14:22] An undeclared seed is the state's carried key, or, for a state without one, its
    // opening state's hash; the learner carries it so every save keeps it and a resume re-keys nothing.
    let seed = contrast_seed(&learner, &args[2])?;
    learner.key = Some(seed);
    // A sweep resume continues the section its writes were saved in: the same state, lap count, key, sweeps and start.
    if let Some(w) = &from_writes {
        if !w.state.eq_ignore_ascii_case(&args[2]) || w.read != learner.laps || w.key != writes_key(seed, learner.laps, w.section) || fresh_sweeps != Some(w.sweeps) || w.from_truth != fresh_from_truth {
            return Err("a sweep resume needs the state its writes name, its lap count and key, the same FIELD_CONTRAST_FRESH and FIELD_FRESH_FROM_TRUTH".into());
        }
    }
    let law = WriterLaw::from_env()?;
    let train_set = encoded_problems(&codec, &train_text, &learner.field)?;
    let held_set = encoded_problems(&codec, &held_text, &learner.field)?;
    let (sections, _) = sections_of(&train_set, section, 0, seed);
    let truth_of = |p: &(Vec<usize>, Vec<usize>, usize), letters: &[usize]| -> Vec<usize> { truth_with_voids(void, p, letters) };
    // [measurement; theory, November 7 23:05] `FIELD_PAIR_KINDS=N`: the pairs by kind of the `N` longest training problems and
    // the median one, each at its truth, resolved (the material read's state), read on the host (`Field::energy_pair_kinds`).
    if let Ok(v) = std::env::var("FIELD_PAIR_KINDS") {
        let count: usize = v.parse().map_err(|_| "FIELD_PAIR_KINDS is a count of problems".to_string())?;
        let mut order: Vec<usize> = (0..train_set.len()).collect();
        order.sort_by_key(|&i| std::cmp::Reverse(train_set[i].0.len() + train_set[i].1.len()));
        let mut chosen: Vec<usize> = order.iter().take(count).copied().collect();
        chosen.push(order[order.len() / 2]);
        for i in chosen {
            let truth = truth_of(&train_set[i], &train_set[i].1);
            let none = vec![false; truth.len()];
            let region = Region { classes: &truth, unresolved: &none, faces: &[], locked: &[], echo: &[], domain: None, port: None };
            let t = std::time::Instant::now();
            let k = learner.field.energy_pair_kinds(&region).map_err(|e| e.to_string())?;
            let heads = k.largest.len().max(1) as u64;
            println!(
                "FIELD_PAIR_KINDS problem={i} sites={} heads={heads} near={} sharp={} listened={} pairs_a_site_a_head={} reach_over_classes={} largest_classes={:?} ms={}",
                k.sites, k.near, k.sharp, k.listened, (k.near + k.sharp + k.listened) / (heads * k.sites.max(1) as u64), learner.field.declaration.reach / k.classes.max(1), k.largest, t.elapsed().as_millis()
            );
        }
    }
    // [measurement; theory, November 8, the width census's §5] `FIELD_CENSUS_RELAX=N`: the energy's material read (the
    // relaxation and its reverse, as a conditional section reads each configuration) of the `N` longest training problems and
    // the median one, each at its truth, resolved, on the host reference with the census on: reads (c), (d), (e) and (g). A read only: it
    // returns before any section.
    if let Ok(v) = std::env::var("FIELD_CENSUS_RELAX") {
        let count: usize = v.parse().map_err(|_| "FIELD_CENSUS_RELAX is a count of problems".to_string())?;
        holonics::number::census::enable();
        let mut order: Vec<usize> = (0..train_set.len()).collect();
        order.sort_by_key(|&i| std::cmp::Reverse(train_set[i].0.len() + train_set[i].1.len()));
        let mut chosen: Vec<usize> = order.iter().take(count).copied().collect();
        chosen.push(order[order.len() / 2]);
        // `FIELD_CENSUS_PICK=k`: only the k-th of those problems, so a serial read runs one problem a process.
        if let Ok(k) = std::env::var("FIELD_CENSUS_PICK") {
            let k: usize = k.parse().map_err(|_| "FIELD_CENSUS_PICK is an index".to_string())?;
            chosen = vec![*chosen.get(k).ok_or("FIELD_CENSUS_PICK is past the chosen problems")?];
        }
        for i in chosen {
            let truth = truth_of(&train_set[i], &train_set[i].1);
            let none = vec![false; truth.len()];
            let region = Region { classes: &truth, unresolved: &none, faces: &[], locked: &[], echo: &[], domain: None, port: None };
            let t = std::time::Instant::now();
            // `FIELD_CENSUS_REST=MOST` (theory, November 8 02:56): the descent read to rest instead, at most MOST ticks, each
            // tick's halvings, fall and slack on 2^(−32).
            if let Ok(most) = std::env::var("FIELD_CENSUS_REST") {
                let most: usize = most.parse().map_err(|_| "FIELD_CENSUS_REST is a count of ticks".to_string())?;
                // `FIELD_CENSUS_REST_REBASE`: each lane re-based to its opening scale after each tick (theory, 03:32).
                // `FIELD_CENSUS_REST_FLOW`: the certified flow step (theory, 04:21), re-based inside the candidate.
                let mode = if std::env::var_os("FIELD_CENSUS_REST_SWING_PERLANE").is_some() {
                    holonics::hnn::tower::field::RestMode::SwingPerLane
                } else if std::env::var_os("FIELD_CENSUS_REST_SWING").is_some() {
                    holonics::hnn::tower::field::RestMode::SwingProjected
                } else if std::env::var_os("FIELD_CENSUS_REST_PERLANE").is_some() {
                    holonics::hnn::tower::field::RestMode::PerLane
                } else if std::env::var_os("FIELD_CENSUS_REST_PROJECTED").is_some() {
                    holonics::hnn::tower::field::RestMode::Projected
                } else if std::env::var_os("FIELD_CENSUS_REST_LINE").is_some() {
                    holonics::hnn::tower::field::RestMode::Line
                } else if std::env::var_os("FIELD_CENSUS_REST_FLOW").is_some() {
                    holonics::hnn::tower::field::RestMode::Flow
                } else if std::env::var_os("FIELD_CENSUS_REST_REBASE").is_some() {
                    holonics::hnn::tower::field::RestMode::Rebase
                } else {
                    holonics::hnn::tower::field::RestMode::Law
                };
                let rebase = format!("{mode:?}");
                let rest = learner.field.energy_rest_read(&region, most, mode).map_err(|e| e.to_string())?;
                for (k, tick) in rest.ticks.iter().enumerate() {
                    println!(
                        "FIELD_REST_TICK problem={i} mode={rebase} tick={k} halvings={} fall={} fall_bits={} slack={} fall_over_slack_milli={} scale_top={} rebase_change={} claim={} rho_nonpositive={} rho_bits={}/{}/{} radial_milli={}/{}/{} gap_phi={} gap_force={} gap_rescale={} gap_kinetic={} swing={}",
                        tick.halvings,
                        tick.fall,
                        128 - tick.fall.unsigned_abs().leading_zeros(),
                        tick.slack,
                        tick.fall * 1000 / tick.slack.max(1),
                        tick.scale_top,
                        tick.rebase_change,
                        tick.claim,
                        tick.rho_nonpositive,
                        tick.rho_least,
                        tick.rho_median,
                        tick.rho_top,
                        tick.radial_least,
                        tick.radial_median,
                        tick.radial_top,
                        tick.gaps[0],
                        tick.gaps[1],
                        tick.gaps[2],
                        tick.gaps[3],
                        tick.swing
                    );
                }
                for t in &rest.tries {
                    println!("FIELD_REST_TRY problem={i} mode={rebase} tick={} halvings={} fall={} claim={} slack={} note={} guard_milli={} radial_rose={} radial_rest={} tangential={} residual={} lanes_rose={} lanes_fell={} lanes_rebased={} moved={} second={} unmirrored={}", t.tick, t.halvings, t.fall, t.claim, t.slack, t.note, t.guard_milli, t.split[0], t.split[1], t.split[2], t.split[3], t.split[4], t.split[5], t.split[6], t.split[7], t.split[8], t.split[9]);
                }
                for m in &rest.mirror {
                    let even = m.rise_plus + m.rise_minus;
                    let odd = (m.rise_plus - m.rise_minus) / 2 + m.work;
                    println!("FIELD_REST_MIRROR problem={i} halvings={} moved={} rise_plus={} rise_minus={} work={} even={even} odd={odd}", m.halvings, m.moved, m.rise_plus, m.rise_minus, m.work);
                }
                for e in &rest.entries {
                    println!("FIELD_REST_ENTRY problem={i} index={} d1={} d2={} force={} ratio_milli={} rise_up={} rise_down={}", e.index, e.d1, e.d2, e.force, if e.d1 != 0 { e.d2 * 1000 / e.d1 } else { 0 }, e.rise_up, e.rise_down);
                }
                println!(
                    "FIELD_REST problem={i} mode={rebase} sites={} ticks={} ended={:?} opening={} last={} fall={} opening_scale_top={} ms={}",
                    truth.len(),
                    rest.ticks.len(),
                    rest.ended,
                    rest.opening,
                    rest.last,
                    rest.opening - rest.last,
                    rest.opening_scale_top,
                    t.elapsed().as_millis()
                );
                continue;
            }
            let (_, g) = learner.field.energy_material(&region).map_err(|e| e.to_string())?;
            println!("FIELD_CENSUS_RELAX problem={i} sites={} g={g} ms={}", truth.len(), t.elapsed().as_millis());
        }
        for r in holonics::number::census::report() {
            println!("FIELD_CENSUS_SITE phase=relax most_bits={} met={} site={}", r.most_bits, r.met, r.site);
        }
        // A read only: nothing is deposited and no section runs.
        return Ok(());
    }
    let d = learner.field.declaration;
    println!(
        "FIELD_CONTRAST_DECLARATION alphabet={} width={} heads={} modes={} ticks={} reach={} rate={} log2_t={} section={section} sections={} train={} held={} places={places} release={} moments={},{} run_bits={} rest={} spans={} laps_read={}",
        d.alphabet,
        d.width,
        d.heads,
        d.modes,
        d.ticks,
        d.reach,
        learner.rate_bits,
        learner.field.theta[learner.field.layout().face_temper],
        sections.len(),
        train_set.len(),
        held_set.len(),
        match (writer, joint) {
            (Some((sw, rf)), _) => format!("writer_{sw}_{rf}"),
            (None, Some(reads)) => format!("joint_{reads}"),
            (None, None) => format!("kernel_spacing_{spacing}"),
        },
        learner.first_rate,
        learner.second_rate,
        law.run_bits,
        law.rest,
        law.spans,
        learner.laps
    );
    let mut enumerated_rows = rows_file(&out.join("ENUMERATED.tsv"), "lap\tproblem\tplace\ttruth\tlog2_t\tface_masses\tface_total\tenergies\ttruth_face_masses\ttruth_face_total\n")?;
    // [definition; theory, November 7 22:41] `FIELD_HOST_HELD=K`: every held read on the host's lanes (`HostHeld`), at `θ` and
    // `θ̄`, at the lap's start, its `K` crossings, its saves and its stop; the card reads none.
    let host_crossings: usize = match std::env::var("FIELD_HOST_HELD") {
        Ok(v) => v.parse().map_err(|_| "FIELD_HOST_HELD is a count of crossings a lap".to_string())?,
        Err(_) => 0,
    };
    let host_held = if host_crossings > 0 {
        Some(HostHeld::start(enumerated_places(&held_set, places, &truth_of), &out, "lap\tproblem\tplace\ttruth\tlog2_t\tface_masses\tface_total\tenergies\ttruth_face_masses\ttruth_face_total\n")?)
    } else {
        None
    };
    let opening_read = std::time::Instant::now();
    match &host_held {
        Some(h) => h.read(-1, &learner),
        None => enumerated_read(&held_field(&learner, averaging), &held_set, places, &truth_of, realization, -1, &mut enumerated_rows)?,
    }
    let opening_read_ms = opening_read.elapsed().as_millis();
    println!("FIELD_ENUMERATED_READ lap=-1 ms={}", started.elapsed().as_millis());
    // [definition; Brandon, November 6 17:11; theory, November 7 16:56, November 9 11:48, 12:18 and the unit rule after] **The
    // save law.** A card run holds at most one hour (`SAVE_MS`) between saved states. At a section's start the learner rests as
    // `STATE.<lap>.<sections done>`, the held places are read from it (`ENUMERATED.tsv` rows marked `10000·(lap + 1) + sections
    // done`) and the run goes on, when the time since the last saved state plus the section's projected time would pass the hour
    // ([`save_due`]). The projection is the section's declared work ([`section_work`]) times the run's largest measured time per
    // unit of work so far ([`SaveRate`]), plus the run's largest held read where a lap's tenth read falls in the section
    // ([`tenth_read_falls`]). Each section is measured from its start, after any save there, to its last print or to the start
    // of its tenth's held read ([`SaveClock`]): its deposit, its prints and its reads beside the declared work are inside the
    // measured rate, every held read is outside it as its own row (the largest kept: the opening read, each save's, each tenth's
    // and each lap end's), and a save's held read is counted once, from the state's write, in the time since the save. The hour
    // is guaranteed only where the projection holds: a save can fall only at a section's start, so this per-section stop holds
    // the gap to the projection, and a section that runs past its projection carries the gap past the hour by its excess, after
    // which the next start saves and the measured rate rises to that section's. Before the run has measured any section there
    // is no rate, and the first section meets the plain hour test (an hour since the last saved state). The run's opening state
    // stands from the run's start, a lap's end state from its write, and no hour save falls at the section a lap or a resumed
    // run opens at (its state is the one already saved). `FIELD_SAVE_AT` adds declared saves. Each `FIELD_SAVED` line prints its
    // reason (`hour`, the projected crossing, ahead of `declared`) and the projection it used. [theory, November 9 13:29] On the
    // fresh-writes path the stops are the sweeps ([`FreshStops`]): the section's start projects its release, up to its first
    // sweep's start, and each sweep's start is tested in the same way with the work to the next stop (the sweep, and after the
    // last the deposit); a sweep save writes the writes' letters (`STATE.<lap>.<sections done>.<sweeps done>.writes`,
    // [`SweepWrites`]) and the learner only where this run has not written it for the section, reads no held places, and is
    // resumed by `FIELD_CONTRAST_FROM_WRITES`. Its `FIELD_SAVED` line names its sweep (`sweep=-` on a section's).
    const SAVE_MS: u128 = 3_600_000;
    let mut clock = SaveClock::default();
    clock.held_read(opening_read_ms);
    // [measurement; theory, November 9 14:30] The previous fresh section's covector, held in memory for the covector line's cosine.
    let mut prev_covector: Option<Vec<i128>> = None;
    for lap in 0..laps {
        let elapsed = started.elapsed().as_millis();
        if lap > 0 && elapsed + lap_ms > stop_ms {
            println!("FIELD_LAPS_HELD lap={lap} reason=time left={} bound={lap_ms} ms={elapsed}", stop_ms.saturating_sub(elapsed));
            break;
        }
        let read = learner.laps;
        let lap_start = std::time::Instant::now();
        let (mut states, mut same, mut gap, mut deposited) = (0usize, 0usize, 0i128, 0usize);
        // The kernel's lap: its block places, moved places, and the weights' sum and squares' sum on 2^(−24).
        let (mut places_lap, mut moved_lap, mut weight_lap, mut square_lap, mut whole_lap) = (0usize, 0usize, 0i128, 0i128, 0usize);
        // Σ_b k_b min(1, A_b) on 2^(−24): the places the lap's kernel moves in expectation.
        let mut accepted_places = 0i128;
        // Each state's (block places, weight), and each section's (α, shrink) in thousandths, for the lap's tenths.
        let mut by_state: Vec<(usize, i128)> = Vec::new();
        let mut by_section: Vec<(i128, i128)> = Vec::new();
        // Each family's transfer and predicted change summed over the lap (on 2^(−20) bits).
        let mut by_family: Vec<(i128, i128)> = Vec::new();
        let (mut tenth_family, mut tenths_printed): (Vec<(i128, i128)>, usize) = (Vec::new(), 0);
        // The sections' coherence over each hundred sections and over the lap (theory, November 7 19:50).
        let (mut coherence_block, mut coherence_lap) = (Coherence::new(&learner.field), Coherence::new(&learner.field));
        let mut leg = Leg::new(&learner.field);
        let mut coherence_from = 0usize;
        for (n, &s) in walk(seed, read, sections.len()).iter().enumerate().skip(if lap == 0 { from_section } else { 0 }) {
            let now = started.elapsed().as_millis();
            let opening = if lap == 0 { from_section } else { 0 };
            // A fresh section resumed at a sweep: the sweep save's writes, taken at the section the run opens at.
            let resumed = if lap == 0 && n == from_section { from_writes.take() } else { None };
            let resumed_sweep = resumed.as_ref().map(|w| w.done);
            if (n > 0 || resumed.is_some()) && n == from_section && lap == 0 {
                println!("FIELD_RESUMED lap={lap} sections={n}/{} sweep={} ms={now}", sections.len(), resumed_sweep.map_or("-".to_string(), |d| d.to_string()));
            }
            let members = &sections[s];
            // [definition; theory, November 9 13:29] On the fresh-writes path the save law stops at the section's start (before its
            // release) and at each sweep's start ([`FreshStops`]); a resumed section opens at its sweep, with no release.
            let release_reads = if resumed.is_some() || fresh_from_truth { 0 } else { WRITES_RELEASE_READS };
            let stops = fresh_sweeps.map(|_| FreshStops::of(&train_set, members, release_reads));
            // The kernel's blocks are cut before the save law reads the section, so its declared work is that of the blocks it
            // steps.
            let kernel_cut = (!on_writes && kernel).then(|| {
                let lengths = kernel_lengths(pinned_blocks || whole_blocks, block_places, log2_k_star);
                (lengths, kernel_blocks(&train_set, members, seed, read, n, spacing, lengths, whole_blocks))
            });
            let section_law = if on_writes {
                // A melt (`FIELD_MELT` without `FIELD_CONTRAST_FRESH`) reads its first section and ends the run before any rate is
                // measured, so its declared sweeps stand in for the fresh writes' only as a projection operand.
                SectionLaw::Fresh { sweeps: fresh_sweeps.or(melt_sweeps).unwrap_or(0), from: resumed_sweep.unwrap_or(0), release_reads }
            } else {
                match (&kernel_cut, writer) {
                    (Some((_, (blocks, owners, _))), _) if conditional => SectionLaw::Conditional { blocks, owners, alphabet: learner.field.declaration.alphabet },
                    (Some((_, (_, owners, _))), _) => SectionLaw::Kernel { owners },
                    (None, Some(_)) => SectionLaw::Writer,
                    (None, None) => SectionLaw::Joint { reads: joint.unwrap_or(1) },
                }
            };
            let (work, unit) = section_work(&section_law, &train_set, members);
            // A lap's tenth read falls in this section where the kernel or law D reads it without HostHeld (the receipt's family
            // lengths are the learner's, so they are known here).
            let tenth_read = kernel_cut.is_some() && !section_letters && host_held.is_none() && learner.family_rates.as_ref().is_some_and(|r| !r.is_empty()) && tenth_read_falls(n, sections.len(), tenths_printed);
            // The work to the next stop: the section's, or on the fresh-writes path its release, up to its first sweep's start.
            let to_stop = stops.map_or(work, |st| st.release);
            let (projected, since) = (clock.projected(to_stop, tenth_read), clock.since(now));
            let hour = n != opening && save_due(since, projected, SAVE_MS);
            // Whether this section's learner is written in this run (a sweep save writes it only where it is not).
            let mut state_written = false;
            if hour || (n > 0 && save_at.contains(&n)) {
                write_new(&out.join(format!("STATE.{lap}.{n}")), at_rate(&learner, base_rate).as_bytes())?;
                state_written = true;
                clock.saved(now);
                let held_read = std::time::Instant::now();
                match &host_held {
                    Some(h) => h.read(10_000 * (lap as i64 + 1) + n as i64, &learner),
                    None => enumerated_read(&held_field(&learner, averaging), &held_set, places, &truth_of, realization, 10_000 * (lap as i64 + 1) + n as i64, &mut enumerated_rows)?,
                }
                let held_ms = clock.held;
                clock.held_read(held_read.elapsed().as_millis());
                println!(
                    "FIELD_SAVED lap={lap} sections={n}/{} sweep=- ms={now} read_ms={} reason={} since_ms={since} projected_ms={} work={to_stop} unit={unit} rate_ms={} rate_work={} tenth_read={} held_ms={} hour_ms={SAVE_MS}",
                    sections.len(),
                    started.elapsed().as_millis() - now,
                    if hour { "hour" } else { "declared" },
                    projected.map_or("-".to_string(), |p| p.to_string()),
                    clock.rate.map_or("-".to_string(), |r| r.ms.to_string()),
                    clock.rate.map_or("-".to_string(), |r| r.work.to_string()),
                    u8::from(tenth_read),
                    held_ms.map_or("-".to_string(), |h| h.to_string())
                );
                leg.print(&learner.field, lap, n, "leg");
                leg = Leg::new(&learner.field);
            }
            let section_start = std::time::Instant::now();
            clock.open(work, started.elapsed().as_millis());
            let truths: Vec<Vec<usize>> = members.iter().map(|&i| truth_of(&train_set[i], &train_set[i].1)).collect();
            if on_writes {
                // [definition; the unified-theory reading of November 7, 09:36; theory, November 8 14:46] **The field meets its
                // writes**: each section, write `j` of the section's `j`-th question is released afresh at its true length (from
                // the faces, or from its truth) and swept whole SWEEPS times at the energy's `T`, and the section deposits
                // `(1/T) Σ_j [∂G/∂θ(truth_j) − ∂G/∂θ(write_j)]` ([`FieldLearner::section_contrast`]): the loss is the closing read
                // `(G(write) − G(truth))/T`, which rests at the answers' likelihood given their questions.
                let problems: Vec<(&[usize], usize)> = members.iter().map(|&i| (train_set[i].0.as_slice(), train_set[i].2)).collect();
                let lengths: Vec<usize> = members.iter().map(|&i| train_set[i].1.len()).collect();
                let key = writes_key(seed, read, n);
                // The melt (`FIELD_MELT`): each sweep prints the share of answer places at their truth letter, each answer's energy a
                // place (milli-nats), the places moved and proposed, the answers whose first ten letters are their truth's, and those
                // with a backtick in their first three places (sweep 0 is the start, before any sweep); after the last sweep the
                // answers are written whole (private), and the run ends.
                if melt_sweeps.is_some() && !melt_all.is_empty() && !melt_all.contains(&n) {
                    continue;
                }
                if let Some(k) = melt_sweeps {
                    let m = members.len();
                    let truth_answers: Vec<Vec<usize>> = members.iter().map(|&i| train_set[i].1.clone()).collect();
                    let released = learner.field.energy_release(&problems, &lengths, void, 64, key, realization, &mut |_, _, _| {}).map_err(|e| e.to_string())?;
                    // [measurement; theory, November 8 17:18] The soup's advantage placed by reads at sweep 0: `G/T` a place (nats, the
                    // closing read's chart) of the truths, the truths with their letters shuffled within each answer (keyed), and the
                    // release; order = truth − shuffle, mix = shuffle − release, each answer's in milli-nats a place. [theory, 17:54]
                    // The release start after its fourth sweep (the fresh writer's own count) is read in the same chart, the
                    // equilibrium writes, beside truth and shuffle, so no reading crosses charts; FIELD_MELT=0 sweeps it four times.
                    let list = |v: &[i128]| v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",");
                    let average = |v: &[i128]| v.iter().sum::<i128>() / v.len().max(1) as i128;
                    let mean = average;
                    let (truth_e, shuffle_e) = {
                        let shuffled: Vec<Vec<usize>> = truth_answers
                            .iter()
                            .enumerate()
                            .map(|(j, t)| {
                                let mut a = t.clone();
                                for i in (1..a.len()).rev() {
                                    let r = (mix(key, 300 << 32 | (j as u64) << 16 | i as u64) % (i as u64 + 1)) as usize;
                                    a.swap(i, r);
                                }
                                a
                            })
                            .collect();
                        let truth_e = closing_per_place(&learner.field, realization, &problems, &truth_answers, void)?;
                        let shuffle_e = closing_per_place(&learner.field, realization, &problems, &shuffled, void)?;
                        let release_e = closing_per_place(&learner.field, realization, &problems, &released, void)?;
                        let lens: Vec<String> = truth_answers.iter().map(|a| a.len().to_string()).collect();
                        println!("FIELD_MELT_READ n={n} lengths={}", lens.join(","));
                        for (kind, v) in [("truth", &truth_e), ("shuffle", &shuffle_e), ("release", &release_e)] {
                            println!("FIELD_MELT_READ n={n} kind={kind} energy_milli={} energies_milli={}", mean(v), list(v));
                        }
                        let order: Vec<i128> = truth_e.iter().zip(&shuffle_e).map(|(a, b)| a - b).collect();
                        let mixd: Vec<i128> = shuffle_e.iter().zip(&release_e).map(|(a, b)| a - b).collect();
                        println!("FIELD_MELT_READ n={n} order_milli={} orders_milli={} mix_milli={} mixes_milli={}", mean(&order), list(&order), mean(&mixd), list(&mixd));
                        (truth_e, shuffle_e)
                    };
                    use std::io::Write;
                    let mut f = std::fs::OpenOptions::new().create(true).append(true).open(out.join("MELT_WRITES.txt"))?;
                    for (start, mut active) in [("truth", truth_answers.clone()), ("release", released)] {
                        let last = if start == "release" { k.max(4) } else { k };
                        for sweep in 0..=last {
                            let t0 = std::time::Instant::now();
                            let (mv, pr, en) = if sweep == 0 {
                                (0usize, 0usize, Vec::new())
                            } else {
                                learner.field.energy_sweep_at(&problems, &mut active, None, void, 0, mix(key, 200 + sweep), realization, &mut |_, _| {}).map_err(|e| e.to_string())?
                            };
                            let places: usize = active.iter().map(|a| a.len()).sum::<usize>().max(1);
                            let agree: usize = active.iter().zip(&truth_answers).map(|(a, t)| a.iter().zip(t).filter(|(x, y)| x == y).count()).sum();
                            let opening = active.iter().zip(&truth_answers).filter(|(a, t)| { let l = t.len().min(10); a.len() >= l && a[..l] == t[..l] }).count();
                            let tick = active.iter().filter(|a| codec.decode(&a[..a.len().min(3)]).contains(&b'`')).count();
                            let energies: Vec<String> = en.iter().map(|e| (e * 1000 >> 32).to_string()).collect();
                            let mean = if en.is_empty() { "-".to_string() } else { ((en.iter().sum::<i128>() / m.max(1) as i128) * 1000 >> 32).to_string() };
                            println!(
                                "FIELD_MELT start={start} n={n} sweep={sweep} retention_milli={} energy_milli={mean} energies_milli={} moved={mv} proposed={pr} opening_intact={opening} backtick_first3={tick} ms={}",
                                agree * 1000 / places,
                                if energies.is_empty() { "-".to_string() } else { energies.join(",") },
                                t0.elapsed().as_millis()
                            );
                            if start == "release" && sweep == 4 {
                                let eq = closing_per_place(&learner.field, realization, &problems, &active, void)?;
                                let less = |v: &[i128]| v.iter().zip(&eq).map(|(a, b)| a - b).collect::<Vec<i128>>();
                                let (t, sh) = (less(&truth_e), less(&shuffle_e));
                                println!("FIELD_MELT_READ n={n} kind=equilibrium4 energy_milli={} energies_milli={}", average(&eq), list(&eq));
                                println!("FIELD_MELT_READ n={n} truth_less_equilibrium_milli={} truths_less_milli={} shuffle_less_equilibrium_milli={} shuffles_less_milli={}", average(&t), list(&t), average(&sh), list(&sh));
                            }
                        }
                        for (j, w) in active.iter().enumerate() {
                            writeln!(f, "=== melt {start} section {n} answer {j} ===")?;
                            f.write_all(&codec.decode(w))?;
                            writeln!(f)?;
                        }
                    }
                    println!("FIELD_MELT_DONE n={n} ms={}", started.elapsed().as_millis());
                    if melt_all.iter().any(|&x| x > n) {
                        continue;
                    }
                    return Ok(());
                }
                // A melt without `FIELD_CONTRAST_FRESH` has ended the run above.
                let (Some(k), Some(stops)) = (fresh_sweeps, stops) else { return Err("a section of writes needs FIELD_CONTRAST_FRESH".into()) };
                let writes: Vec<Vec<usize>> = if let Some(w) = &resumed {
                    if w.writes.len() != members.len() || w.writes.iter().zip(&lengths).any(|(w, &l)| w.len() != l) {
                        return Err("a sweep save's writes are not its section's answers at their lengths".into());
                    }
                    w.writes.clone()
                } else if fresh_from_truth {
                    members.iter().map(|&i| train_set[i].1.clone()).collect()
                } else {
                    learner.field.energy_release(&problems, &lengths, void, WRITES_RELEASE_READS, key, realization, &mut |_, _, _| {}).map_err(|e| e.to_string())?
                };
                let m = members.len().min(writes.len());
                let mut active: Vec<Vec<usize>> = (0..m).map(|j| writes[j][..lengths[j].min(writes[j].len())].to_vec()).collect();
                // [definition; theory, November 9 13:29] **The sweep stop**: each sweep's start is tested as a section's start, with
                // the work to the next stop (the sweep, and after the last the deposit) at the run's largest measured rate; a save
                // there writes the writes' letters ([`SweepWrites`]) and the learner only where this run has not written it for this
                // section, and reads no held places. No hour save falls at the sweep a resumed section opens at.
                let at_sweep = &mut |sweep: u64, active: &[Vec<usize>]| -> Result<()> {
                    let now = started.elapsed().as_millis();
                    let to_stop = stops.at_sweep(sweep, k);
                    let (projected, since) = (clock.projected(to_stop, false), clock.since(now));
                    let hour = resumed_sweep != Some(sweep) && save_due(since, projected, SAVE_MS);
                    if hour || save_at_sweep.contains(&(n, sweep)) {
                        let text = at_rate(&learner, base_rate);
                        let state = if state_written {
                            "kept"
                        } else {
                            write_new(&out.join(format!("STATE.{lap}.{n}")), text.as_bytes())?;
                            state_written = true;
                            "written"
                        };
                        let saved = SweepWrites { read, section: n, done: sweep, sweeps: k, key, from_truth: fresh_from_truth, state: sha256(text.as_bytes())?, writes: active.to_vec() };
                        write_new(&out.join(format!("STATE.{lap}.{n}.{sweep}.writes")), saved.to_text().as_bytes())?;
                        clock.saved(now);
                        println!(
                            "FIELD_SAVED lap={lap} sections={n}/{} sweep={sweep}/{k} ms={now} read_ms=- reason={} since_ms={since} projected_ms={} work={to_stop} unit=site_reads rate_ms={} rate_work={} tenth_read=0 held_ms=- state={state} write_ms={} hour_ms={SAVE_MS}",
                            sections.len(),
                            if hour { "hour" } else { "declared" },
                            projected.map_or("-".to_string(), |p| p.to_string()),
                            clock.rate.map_or("-".to_string(), |r| r.ms.to_string()),
                            clock.rate.map_or("-".to_string(), |r| r.work.to_string()),
                            started.elapsed().as_millis() - now
                        );
                    }
                    Ok(())
                };
                fresh_sweeps_at(&learner.field, &problems[..m], &mut active, resumed_sweep.unwrap_or(0), k, key, void, realization, at_sweep, &mut |sweep, mv, pr, en, active, ms| {
                    println!("FIELD_FRESH_SWEEP lap={lap} n={n} sweep={sweep} moved={mv} proposed={pr} accept_milli={} write_energy_milli={} ms={ms}", mv * 1000 / pr.max(1), (en.iter().sum::<i128>() / m.max(1) as i128) * 1000 >> 32);
                    if fresh_from_truth {
                        let answers: Vec<&[usize]> = members.iter().map(|&i| train_set[i].1.as_slice()).collect();
                        println!("FIELD_FRESH_RETAIN lap={lap} n={n} sweep={sweep} retention_milli={}", retention_milli(active, &answers));
                    }
                })?;
                // [measurement; theory, November 8 14:59] Each section's writes decoded beside their truths (private).
                use std::io::Write;
                let mut f = std::fs::OpenOptions::new().create(true).append(true).open(out.join("FRESH_WRITES.txt"))?;
                for (j, w) in active.iter().enumerate() {
                    writeln!(f, "=== section {n} write {j} ===")?;
                    f.write_all(&codec.decode(w))?;
                    writeln!(f, "\n=== section {n} truth {j} ===")?;
                    f.write_all(&codec.decode(&train_set[members[j]].1))?;
                    writeln!(f)?;
                }
                let release_ms = section_start.elapsed().as_millis();
                let theta_before = learner.field.theta.clone();
                // [measurement; theory, November 9 14:30] The section's covector by problem, read before the deposit on the field it
                // deposits on (`FIELD_COVECTOR_SECTION`; a reading).
                let pairs = writes_pairs(&learner.field, &problems[..m], &truths, &active, void, realization)?;
                let deposit_start = std::time::Instant::now();
                // [definition; theory, November 9 05:51] The writes' contrast deposits through the one deposit, as every contrast
                // does (`FieldLearner::section_contrast`): each entry's step carries its remainder and each family's length moves by
                // its own transfer. The scaled contrast's Newton length and its harmonic mean of eleven are retired; a state saved
                // under them moves to this law by `deposit-fold`.
                let receipt = writes_deposit(&mut learner, &problems[..m], &truths, &active, void, realization)?;
                let deposit_ms = deposit_start.elapsed().as_millis();
                let places: i128 = lengths[..m].iter().map(|&l| l as i128).sum::<i128>().max(1);
                // The closing read `(G(write) − G(truth))/T` a place in thousandths of a nat (`gap` is `Σ (G(truth) − G(write))/T` on 2^(−32) bits).
                let closing_milli = -(receipt.gap * LN2_Q30 >> 30) * 1000 / places >> 32;
                (states, deposited) = (states + receipt.states, deposited + usize::from(receipt.deposited));
                (gap, same) = (gap + receipt.gap, same + receipt.same);
                // [definition; theory, November 9 00:08] The averaged constitution moves at every deposit, this path's as the
                // kernel's: until then the fresh writes' held reads read an average frozen at their starting state (law D's, for
                // the forks from 179).
                if averaging {
                    learner.average_section();
                }
                let micro = |v: Option<i64>| v.map_or("-".to_string(), |c| ((c as i128 * 1_000_000) / ((receipt.states as i128) << 20)).to_string());
                println!(
                    "FIELD_PERSISTENT lap={lap} n={n} writes={m} closing_milli={closing_milli} deposited={} predicted_micro={} transfer_micro={} external_micro={} log2_t={} sweep_ms={release_ms} deposit_ms={deposit_ms} ms={}",
                    receipt.deposited,
                    micro(receipt.predicted),
                    micro(receipt.transfer),
                    micro(receipt.external),
                    learner.field.theta[learner.field.layout().face_temper],
                    started.elapsed().as_millis()
                );
                // [measurement; theory, November 9 05:04] Each family's moved grains and its length, as the kernel's path prints them.
                println!("FIELD_STEP lap={lap} n={n} {}", step_text(&learner.field, &theta_before));
                println!("FIELD_LENGTHS lap={lap} n={n} {}", lengths_text(&learner));
                // [measurement; theory, November 9 14:30] The covector line, a family a line: the step as the deposit formed it where
                // the learner keeps it, else as it moved (`θ` before less `θ` after).
                let (step, step_unit): (Vec<i128>, &str) = match learner.last_formed_step() {
                    Some(formed) => (formed.to_vec(), "formed"),
                    None => (theta_before.iter().zip(&learner.field.theta).map(|(&b, &a)| b as i128 - a as i128).collect(), "moved"),
                };
                let (lines, g) = covector_section_lines(&learner.field, &pairs, prev_covector.as_deref(), &step, step_unit)?;
                for line in lines {
                    println!("FIELD_COVECTOR_SECTION lap={lap} n={n} {line}");
                }
                prev_covector = Some(g);
                // The section closes at its last print, before the next start's save (the save law's clock).
                clock.close(started.elapsed().as_millis());
                // The declared read ends this path as it ends the kernel's (`FIELD_CONTRAST_SECTIONS`); without it the fresh-writes
                // fork of November 8 ran past its 20 sections to the deadline and was stopped at section 204 with no state.
                let read_done = read_sections > 0 && lap == 0 && n + 1 >= from_section + read_sections;
                if started.elapsed().as_millis() > stop_ms || read_done {
                    write_new(&out.join("STATE.stopped"), at_rate(&learner, base_rate).as_bytes())?;
                    println!("FIELD_STOPPED lap={lap} sections={}/{} states={states} ms={}", n + 1, sections.len(), started.elapsed().as_millis());
                    return Ok(());
                }
                continue;
            }
            // The kernel (the writer and the joint release undeclared): each state's answer places `t ≡ r (mod s)`, cut into blocks
            // of at most `k*` places, each block its own kernel step from the truth ([the unified-theory reading of November 7,
            // 07:24]: a block of `k` places moves `k·2Φ(−σ√k/2)` places, most at `σ²k ≈ 5.7`); `FIELD_CONTRAST_WHOLE_BLOCKS`
            // keeps one block a state (laps 4 to 9). [definition; the unified-theory reading of November 7, 08:13] Two lengths a
            // section ([`kernel_lengths`]), each residue class cut into blocks alternating them ([`kernel_blocks`], cut at the
            // section's start for the save law); a closing block shorter than its length runs but is not read.
            if let Some(((k_up, k_down), (blocks, owners, classes_of))) = kernel_cut {
                if section_letters {
                    let mut count = std::collections::BTreeMap::<usize, usize>::new();
                    for (b, &o) in blocks.iter().zip(&owners) {
                        for &t in b {
                            *count.entry(truths[o][t]).or_default() += 1;
                        }
                    }
                    let places: usize = count.values().sum();
                    let text: Vec<String> = count.iter().map(|(&c, &k)| format!("{}:{k}", if c < 256 { escaped(&[c as u8]) } else { format!("#{c}") })).collect();
                    let longest = members.iter().map(|&i| (train_set[i].0.len() + train_set[i].1.len(), i)).max().unwrap_or((0, 0));
                    println!("FIELD_SECTION_LETTERS lap={lap} n={n} places={places} longest={} longest_problem={} {}", longest.0, longest.1, text.join(" "));
                    continue;
                }
                let resolved: Vec<Vec<bool>> = truths.iter().map(|t| vec![false; t.len()]).collect();
                let truth_views: Vec<Region> = truths.iter().zip(&resolved).map(|(c, u)| Region { classes: c, unresolved: u, faces: &[], locked: &[], echo: &[], domain: None, port: None }).collect();
                let key = mix(seed ^ 0xC0_7A57 << 40, read << 32 | n as u64);
                // [measurement; theory, November 7 21:44] The section's step, `Σ |Δθ|` a family on its grain over its entries.
                let theta_before = learner.field.theta.clone();
                let frozen = read_only.then(|| learner.clone());
                // [the unified-theory reading of November 7, 07:40] Each problem's truth formed once for all its blocks.
                // [definition; the unified-theory reading of November 7, 20:29, law (D)] `FIELD_CONTRAST_CONDITIONAL`: each block place
                // deposits against its whole conditional (`FieldLearner::section_conditional`), no proposal and no coin; its
                // pseudo-likelihood code on the trained places is the `FIELD_CONDITIONAL` line.
                let receipt = if conditional {
                    // [definition; the unified-theory reading of November 7, 21:08] `FIELD_CONTRAST_BEAT=TOP`: each place spent on
                    // its beat `2^k` by what is left of its news (`FieldLearner::section_conditional_beat`), bands held to
                    // `0..=TOP`; the counts of counts are the `FIELD_BANDS` line.
                    let r = match beat_top {
                        Some(top) => {
                            let ids: Vec<u64> = members.iter().map(|&i| i as u64).collect();
                            let r = learner.section_conditional_beat(&truth_views, &owners, &blocks, &ids, read, top, realization).map_err(|e| e.to_string())?;
                            println!("FIELD_BANDS lap={lap} n={n} {}", r.bands.iter().enumerate().map(|(k, &(seen, spent))| format!("k{k}={seen}/{spent}")).collect::<Vec<_>>().join(" "));
                            r
                        }
                        // [definition; the unified-theory reading of November 7, 22:08] `FIELD_CONTRAST_COIN=TAU_BITS`: the letters'
                        // reverses kept by a coin at `τ = 2^(−TAU_BITS)` (`FieldLearner::section_conditional_coin`).
                        None => match coin_tau {
                            Some(tau) => learner.section_conditional_coin(&truth_views, &owners, &blocks, tau, mix(seed ^ 0xC01A << 40, read << 32 | n as u64), realization).map_err(|e| e.to_string())?,
                            None => learner.section_conditional(&truth_views, &owners, &blocks, realization).map_err(|e| e.to_string())?,
                        },
                    };
                    let nats: i128 = -r.log2_a.iter().map(|&l| l * LN2_Q30 >> 30).sum::<i128>();
                    println!(
                        "FIELD_CONDITIONAL lap={lap} n={n} places={} pl_code_milli={} truth_p_milli={} mode_milli={} ms={}",
                        r.places,
                        nats * 1000 / (r.places.max(1) as i128) >> 32,
                        r.weight * 1000 / ((r.places.max(1) as i128) << holonics::hnn::tower::MATERIAL_BITS),
                        r.whole * 1000 / r.places.max(1),
                        section_start.elapsed().as_millis()
                    );
                    if conditional_rows {
                        use std::io::Write;
                        let mut f = std::fs::OpenOptions::new().create(true).append(true).open(out.join("CONDITIONAL_ROWS.txt"))?;
                        let row: Vec<String> = r.log2_a.iter().map(|&l| (-(l * LN2_Q30 >> 30) * 1_000_000 >> 32).to_string()).collect();
                        writeln!(f, "lap={lap} n={n} places={} micro_nats={}", r.log2_a.len(), row.join(","))?;
                    }
                    // [measurement; theory, November 7 23:47] The coin's measure: each tolerance's cost a place and added variance,
                    // and the tolerance that minimizes `cost × (1 + V_coin/V_D)` (a tie to the larger, cheaper `τ`), written to
                    // `COIN_TAU`.
                    if let Some(m) = &r.coin_measure {
                        let alphabet = learner.field.declaration.alphabet as u128;
                        let places = m.places.max(1) as u128;
                        let (cf, cm) = (m.forward_us.max(1) * 1000 / m.regions.max(1) as u128, m.material_us.max(1) * 1000 / m.regions.max(1) as u128);
                        let full = alphabet * cm;
                        let mut best: Option<(u128, u32)> = None;
                        let mut cells = Vec::new();
                        for b in 1..=m.kept.len() as u32 {
                            let kept_milli = (m.kept[b as usize - 1].max(0) as u128) * 1000 / (places << holonics::hnn::tower::MATERIAL_BITS);
                            let cost = alphabet * cf + (1000 + kept_milli) * cm / 1000;
                            let ratio_milli = m.v_coin[b as usize - 1].saturating_mul(1000) / m.v_deposit.max(1);
                            let work = cost.saturating_mul(1000 + ratio_milli);
                            if best.is_none_or(|(w, _)| work < w) {
                                best = Some((work, b));
                            }
                            cells.push(format!("b{b}:kept_milli={kept_milli},vratio_milli={ratio_milli},cost_milli={}", cost * 1000 / full.max(1)));
                        }
                        let chosen = best.map_or(0, |(_, b)| b);
                        println!("FIELD_COIN_MEASURE lap={lap} n={n} places={} forward_ns_a_region={cf} material_ns_a_region={cm} {} chosen_tau_bits={chosen}", m.places, cells.join(" "));
                        std::fs::write(out.join("COIN_TAU"), format!("{chosen}\n"))?;
                    }
                    if !r.outside.is_empty() {
                        let unit = 1i128 << holonics::hnn::tower::MATERIAL_BITS;
                        let stat = |j: usize| -> String {
                            let mut v: Vec<i128> = r.outside.iter().map(|o| o[j]).collect();
                            let mean = v.iter().sum::<i128>() * 1_000_000 / (unit * v.len() as i128);
                            v.sort_unstable();
                            format!("{mean}/{}/{}", v[v.len() * 9 / 10] * 1_000_000 / unit, v[v.len() - 1] * 1_000_000 / unit)
                        };
                        println!("FIELD_LETTERS lap={lap} n={n} outside_top4_micro={} outside_top8_micro={} outside_top16_micro={} (mean/q90/max)", stat(0), stat(1), stat(2));
                    }
                    r
                } else {
                    learner.section_kernel_grouped(&truth_views, &owners, &blocks, key, realization).map_err(|e| e.to_string())?
                };
                // [definition; the unified-theory reading of November 7, 07:40] **The block size from the acceptance's own slope**:
                // moved places `k·α(k)` peak where `d ln α/d ln k = −1`, so `log₂ k* += ¼(1 + slope)`, the slope of `log₂ min(1, A)`
                // on `log₂ k` across the section's blocks (no Gaussian assumed); a section whose blocks share one size moves nothing.
                // The elasticity of the mean acceptance, `ln(ᾱ₊/ᾱ₋)/ln(k₊/k₋)`, ᾱ the mean of `min(1, A)` over each length's whole
                // blocks (never the mean of logs); `log₂ k* += ¼(1 + slope)`.
                let (mut slope_milli, mut alpha_up, mut alpha_down) = (None, 0i128, 0i128);
                if !whole_blocks && !pinned_blocks && k_up > k_down {
                    let mean = |want: bool| -> Option<i128> {
                        let w: Vec<i128> = classes_of.iter().zip(&receipt.per_state).filter(|(c, _)| **c == Some(want)).map(|(_, &(_, w))| w).collect();
                        (!w.is_empty()).then(|| w.iter().sum::<i128>() / w.len() as i128)
                    };
                    if let (Some(au), Some(ad)) = (mean(true), mean(false)) {
                        (alpha_up, alpha_down) = (au, ad);
                        if au > 0 && ad > 0 {
                            let num = log2_q16(au as u64) as i128 - log2_q16(ad as u64) as i128;
                            let den = log2_q16(k_up as u64) as i128 - log2_q16(k_down as u64) as i128;
                            let slope_q16 = (num << 16) / den;
                            slope_milli = Some(slope_q16 * 1000 >> 16);
                            log2_k_star = (log2_k_star + ((1i128 << 16) + slope_q16) / 4).clamp(0, 12 << 16);
                            block_places = (1..=1usize << 12).min_by_key(|&k| (log2_q16(k as u64) as i128 - log2_k_star).abs()).unwrap_or(1);
                        }
                    }
                }
                accepted_places += receipt.per_state.iter().map(|&(k, w)| k as i128 * w).sum::<i128>();
                // [measurement; the unified-theory reading of November 7, 08:25] The kernel's entropy production, `ℓ = ln A`: its
                // per-place spread `s₁ = −2 Σℓ/Σk` and `s₂ = Σ(ℓ + k s₁/2)²/Σk` (normality: `s₁ = s₂` at equilibrium), and `⟨A⟩ − 1`
                // (zero at equilibrium; from the truth, the data's distance from it); thousandths of a nat.
                let entropy_text = {
                    let nats: Vec<i128> = receipt.log2_a.iter().map(|&l| l * LN2_Q30 >> 30).collect();
                    let k_sum: i128 = blocks.iter().map(|b| b.len() as i128).sum::<i128>().max(1);
                    let s1 = -2 * nats.iter().sum::<i128>() / k_sum;
                    let s2 = nats.iter().zip(&blocks).map(|(&l, b)| {
                        let d = l + b.len() as i128 * s1 / 2;
                        (d >> 16) * (d >> 16)
                    }).sum::<i128>() / k_sum;
                    let mean_a = receipt.log2_a.iter().map(|&l| exp2_q32(l)).sum::<i128>() / receipt.log2_a.len().max(1) as i128;
                    format!(" s1_milli={} s2_milli={} mean_a_less_one_milli={}", (s1 * 1000) >> 32, (s2 * 1000) >> 32, ((mean_a - (1i128 << 32)) * 1000) >> 32)
                };
                (states, deposited) = (states + receipt.states, deposited + usize::from(receipt.deposited));
                (places_lap, moved_lap, weight_lap, square_lap, whole_lap) = (places_lap + receipt.places, moved_lap + receipt.moved, weight_lap + receipt.weight, square_lap + receipt.weight_square, whole_lap + receipt.whole);
                let unit = 1i128 << holonics::hnn::tower::MATERIAL_BITS;
                let micro = |v: Option<i64>| v.map_or("-".to_string(), |c| ((c as i128 * 1_000_000) / ((receipt.states as i128) << 20)).to_string());
                by_state.extend(receipt.per_state.iter().copied());
                if by_family.len() < receipt.by_family.len() {
                    by_family.resize(receipt.by_family.len(), (0, 0));
                }
                for (slot, &(t, p)) in by_family.iter_mut().zip(&receipt.by_family) {
                    *slot = (slot.0 + t.unwrap_or(0), slot.1 + p.unwrap_or(0));
                }
                let newton_text = match receipt.newton {
                    Some(r) => {
                        let alpha = if r.alpha.1 > 0 { r.alpha.0 * 1000 / r.alpha.1 } else { 0 };
                        let shrink = if r.shrink.1 > 0 { r.shrink.0 * 1000 / r.shrink.1 } else { 0 };
                        by_section.push((alpha, shrink));
                        format!(" alpha_milli={alpha} shrink_milli={shrink} slope_micro={} curvature={} variance={}", (r.slope * 1_000_000) / ((receipt.states as i128) << 20), r.curvature, r.variance)
                    }
                    None => String::new(),
                };
                println!(
                    "FIELD_KERNEL lap={lap} n={n} states={} places={} moved={} accept_milli={} least_milli={} most_milli={} whole={} deposited={} predicted_micro={} transfer_micro={} external_micro={}{newton_text}{entropy_text} log2_t={} blocks={} k_star={block_places} k_up={k_up} k_down={k_down} alpha_up_milli={} alpha_down_milli={} slope_milli={} g_agree={}/{} g_gap={} ms_section={} ms={}",
                    receipt.states,
                    receipt.places,
                    receipt.moved,
                    receipt.weight * 1000 / (unit * receipt.states as i128),
                    receipt.least * 1000 / unit,
                    receipt.most * 1000 / unit,
                    receipt.whole,
                    receipt.deposited,
                    micro(receipt.predicted),
                    micro(receipt.transfer),
                    micro(receipt.external),
                    learner.field.theta[learner.field.layout().face_temper],
                    blocks.len(),
                    alpha_up * 1000 >> holonics::hnn::tower::MATERIAL_BITS,
                    alpha_down * 1000 >> holonics::hnn::tower::MATERIAL_BITS,
                    slope_milli.map_or("-".to_string(), |v| v.to_string()),
                    receipt.g_agree.0,
                    receipt.g_agree.1,
                    receipt.g_gap,
                    section_start.elapsed().as_millis(),
                    started.elapsed().as_millis()
                );
                println!("FIELD_STEP lap={lap} n={n} {}", step_text(&learner.field, &theta_before));
                println!("FIELD_LENGTHS lap={lap} n={n} {}", lengths_text(&learner));
                leg.add(&learner.field, &receipt, &theta_before);
                if let Some(opening) = &frozen {
                    learner.clone_from(opening);
                }
                if averaging && frozen.is_none() {
                    learner.average_section();
                }
                if let Some(h) = &host_held {
                    let len = sections.len();
                    if (n + 1) * host_crossings / len > n * host_crossings / len {
                        h.read(10_000 * (lap as i64 + 1) + (n + 1) as i64, &learner);
                    }
                }
                coherence_block.add(&receipt.covector);
                coherence_lap.add(&receipt.covector);
                // `FIELD_COHERENCE_EVERY=K`: the lap's coherence so far each `K` sections, so a run stopped from outside still
                // leaves it (November 7: the 40-section read of law (D) was killed inside a 15-minute section).
                if coherence_every > 0 && (n + 1 - from_section.min(n + 1)) % coherence_every == 0 {
                    println!("FIELD_COHERENCE_SO_FAR lap={lap} sections={} n={} {}", n + 1, coherence_lap.n, coherence_lap.text(&learner.field));
                }
                if (n + 1) % 100 == 0 {
                    println!("FIELD_COHERENCE lap={lap} sections={coherence_from}..{} n={} {}", n + 1, coherence_block.n, coherence_block.text(&learner.field));
                    (coherence_block, coherence_from) = (Coherence::new(&learner.field), n + 1);
                }
                // [measurement; the unified-theory reading of November 7, 06:57] At each tenth of the lap: `log₂ T`, and each family's
                // length (milli-bits) and its share (transfer over own-section price, thousandths) over the tenth.
                if !receipt.rates.is_empty() {
                    if tenth_family.len() < receipt.by_family.len() {
                        tenth_family.resize(receipt.by_family.len(), (0, 0));
                    }
                    for (slot, &(t, p)) in tenth_family.iter_mut().zip(&receipt.by_family) {
                        *slot = (slot.0 + t.unwrap_or(0), slot.1 + p.unwrap_or(0));
                    }
                    let tenth = (n + 1) * 10 / sections.len();
                    if tenth_read_falls(n, sections.len(), tenths_printed) {
                        // [measurement; theory, November 7 19:50] The held places read at each tenth, beside the tenth's acceptance and
                        // the sections' coherence (rows marked `10000·(lap + 1) + sections done`).
                        match &host_held {
                            // The host's crossings carry the tenths.
                            Some(_) => {}
                            None => {
                                // The section closes before its tenth's read, which is the save law's own row (`SaveClock`).
                                clock.close(started.elapsed().as_millis());
                                let held_read = std::time::Instant::now();
                                enumerated_read(&held_field(&learner, averaging), &held_set, places, &truth_of, realization, 10_000 * (lap as i64 + 1) + (n + 1) as i64, &mut enumerated_rows)?;
                                clock.held_read(held_read.elapsed().as_millis());
                            }
                        }
                    }
                    if tenth > tenths_printed || n + 1 == sections.len() {
                        tenths_printed = tenth;
                        println!("FIELD_KERNEL_TENTH lap={lap} tenth={tenth} log2_t={} {}", learner.field.theta[learner.field.layout().face_temper], rates_text(&learner.field, &receipt.rates, &tenth_family));
                        tenth_family.iter_mut().for_each(|x| *x = (0, 0));
                    }
                }
                // The section closes at its last print (where no tenth's read closed it), before the next start's save.
                clock.close(started.elapsed().as_millis());
                let read_done = read_sections > 0 && lap == 0 && n + 1 >= from_section + read_sections;
                if started.elapsed().as_millis() > stop_ms || read_done {
                    write_new(&out.join("STATE.stopped"), at_rate(&learner, base_rate).as_bytes())?;
                    // [theory, November 7 21:44] Every stopped read ends with the held read (rows marked `lap`).
                    match &host_held {
                        Some(h) => h.read(lap as i64, &learner),
                        None => enumerated_read(&held_field(&learner, averaging), &held_set, places, &truth_of, realization, lap as i64, &mut enumerated_rows)?,
                    }
                    println!("FIELD_STOPPED lap={lap} sections={}/{} states={states} ms={}", n + 1, sections.len(), started.elapsed().as_millis());
                    if coherence_block.n > 0 {
                        println!("FIELD_COHERENCE lap={lap} sections={coherence_from}..{} n={} {}", n + 1, coherence_block.n, coherence_block.text(&learner.field));
                    }
                    println!("FIELD_COHERENCE_LAP lap={lap} stopped n={} {}", coherence_lap.n, coherence_lap.text(&learner.field));
                    leg.print(&learner.field, lap, n + 1, "stop");
                    if states > 0 {
                        println!("FIELD_KERNEL_FAMILIES lap={lap} stopped {}", family_text(&learner.field, &by_family, states));
                        let mean = weight_lap * 1000 / (unit * states as i128);
                        let var = (square_lap * 1_000_000 / (unit * states as i128)) - mean * mean;
                        println!("FIELD_KERNEL_ACCEPT lap={lap} stopped states={states} places={places_lap} moved={moved_lap} accept_milli={mean} sd_milli={} whole={whole_lap}", (var.max(0) as u128).isqrt());
                    }
                    return Ok(());
                }
                continue;
            }
            let problems: Vec<(&[usize], usize)> = members.iter().map(|&i| (train_set[i].0.as_slice(), train_set[i].2)).collect();
            let lengths: Vec<usize> = members.iter().map(|&i| train_set[i].1.len()).collect();
            let key = mix(seed ^ 0xC0_7A57 << 40, read << 32 | n as u64);
            // The release's progress, one line every 256 reads with its elapsed milliseconds, and its cut where the run passes
            // `STOP_MS` (a cut release deposits nothing: the run stops there, incomplete).
            let mut cut = false;
            let mut reads_made = 0usize;
            let answers = match writer {
                None => learner
                    .field
                    .energy_release(&problems, &lengths, void, joint.unwrap_or(1), key, realization, &mut |read, moving, moved| {
                        reads_made = read + 1;
                        if read % 8 == 0 {
                            println!("FIELD_RELEASE_READ lap={lap} n={n} read={read} moving={moving} moved={moved} ms={}", section_start.elapsed().as_millis());
                        }
                    })
                    .map_err(|e| e.to_string())?,
                Some((sweeps, refine)) => learner
                .field
                .sample_runs(
                    &problems,
                    sweeps,
                    refine,
                    void,
                    key,
                    law.run_bits << 20,
                    law.near_tail,
                    law.place_order,
                    Some(&lengths),
                    false,
                    law.rest,
                    law.spans,
                    None,
                    law.refine_order,
                    realization,
                    &mut |done, total| {
                        reads_made = reads_made.max(done + 1);
                        if done % 256 == 0 {
                            println!("FIELD_RELEASE_READ lap={lap} n={n} read={done} of={total} ms={}", section_start.elapsed().as_millis());
                        }
                        if started.elapsed().as_millis() > stop_ms {
                            cut = true;
                            return false;
                        }
                        true
                    },
                    &mut |_| {},
                )
                .map_err(|e| e.to_string())?,
            };
            let release_ms = section_start.elapsed().as_millis();
            if cut {
                println!("FIELD_STOPPED lap={lap} sections={n}/{} reason=release_cut release_reads={reads_made} release_ms={release_ms} ms={}", sections.len(), started.elapsed().as_millis());
                return Ok(());
            }
            let releases: Vec<Vec<usize>> = members
                .iter()
                .zip(&answers)
                .map(|(&i, written)| written.get(..train_set[i].1.len()).map(|w| truth_of(&train_set[i], w)).ok_or("a release shorter than its given length"))
                .collect::<std::result::Result<_, _>>()?;
            let resolved: Vec<Vec<bool>> = truths.iter().map(|t| vec![false; t.len()]).collect();
            let truth_views: Vec<Region> = truths.iter().zip(&resolved).map(|(c, u)| Region { classes: c, unresolved: u, faces: &[], locked: &[], echo: &[], domain: None, port: None }).collect();
            let release_views: Vec<Region> = releases.iter().zip(&resolved).map(|(c, u)| Region { classes: c, unresolved: u, faces: &[], locked: &[], echo: &[], domain: None, port: None }).collect();
            let theta_before = learner.field.theta.clone();
            let deposit_start = std::time::Instant::now();
            let receipt = learner.section_contrast(&truth_views, &release_views, realization).map_err(|e| e.to_string())?;
            let deposit_ms = deposit_start.elapsed().as_millis();
            (states, same, gap, deposited) = (states + receipt.states, same + receipt.same, gap + receipt.gap, deposited + usize::from(receipt.deposited));
            let micro = |v: Option<i64>| v.map_or("-".to_string(), |c| ((c as i128 * 1_000_000) / ((receipt.states as i128) << 20)).to_string());
            println!(
                "FIELD_CONTRAST lap={lap} n={n} states={} same={} gap_micro={} deposited={} predicted_micro={} transfer_micro={} external_micro={} release_reads={reads_made} release_ms={release_ms} deposit_ms={deposit_ms} ms={}",
                receipt.states,
                receipt.same,
                (receipt.gap * 1_000_000) / ((receipt.states as i128) << 32),
                receipt.deposited,
                micro(receipt.predicted),
                micro(receipt.transfer),
                micro(receipt.external),
                started.elapsed().as_millis()
            );
            // [measurement; theory, November 9 05:04] Each family's moved grains and its length, as the kernel's path prints them.
            println!("FIELD_STEP lap={lap} n={n} {}", step_text(&learner.field, &theta_before));
            println!("FIELD_LENGTHS lap={lap} n={n} {}", lengths_text(&learner));
            // The section closes at its last print, before the next start's save.
            clock.close(started.elapsed().as_millis());
            if started.elapsed().as_millis() > stop_ms {
                write_new(&out.join("STATE.stopped"), at_rate(&learner, base_rate).as_bytes())?;
                println!("FIELD_STOPPED lap={lap} sections={}/{} states={states} ms={}", n + 1, sections.len(), started.elapsed().as_millis());
                return Ok(());
            }
        }
        learner.laps += 1;
        write_new(&out.join(format!("STATE.{lap}")), at_rate(&learner, base_rate).as_bytes())?;
        clock.saved(started.elapsed().as_millis());
        if on_writes {
            println!("FIELD_PERSISTENT_LAP lap={lap} states={states} closing_milli={} ms={}", if states == 0 { 0 } else { -(gap * LN2_Q30 >> 30) * 1000 / (states as i128) >> 32 }, started.elapsed().as_millis());
        }
        if states > 0 && writer.is_none() && joint.is_none() && !on_writes {
            let unit = 1i128 << holonics::hnn::tower::MATERIAL_BITS;
            let mean = weight_lap * 1000 / (unit * states as i128);
            let var = (square_lap * 1_000_000 / (unit * states as i128)) - mean * mean;
            println!("FIELD_KERNEL_ACCEPT lap={lap} states={states} places={places_lap} moved={moved_lap} accept_milli={mean} sd_milli={} whole={whole_lap} accepted_places={} accepted_places_a_second={}", (var.max(0) as u128).isqrt(), accepted_places >> holonics::hnn::tower::MATERIAL_BITS, (accepted_places >> holonics::hnn::tower::MATERIAL_BITS) * 1000 / lap_start.elapsed().as_millis().max(1) as i128);
            if coherence_block.n > 0 {
                println!("FIELD_COHERENCE lap={lap} sections={coherence_from}..{} n={} {}", sections.len(), coherence_block.n, coherence_block.text(&learner.field));
            }
            println!("FIELD_COHERENCE_LAP lap={lap} n={} {}", coherence_lap.n, coherence_lap.text(&learner.field));
            leg.print(&learner.field, lap, sections.len(), "lap");
            // [measurement; the unified-theory reading of November 7, 05:55] The acceptance by tenths of the states' block size,
            // and α and the shrink by tenths of the lap (their medians).
            let mut sized = by_state.clone();
            sized.sort_by_key(|&(p, _)| p);
            let tenths: Vec<String> = (0..10)
                .map(|k| {
                    let part = &sized[k * sized.len() / 10..(k + 1) * sized.len() / 10];
                    let (places, weight) = part.iter().fold((0usize, 0i128), |(p, w), &(q, x)| (p + q, w + x));
                    format!("{}:{}", places * 10 / part.len().max(1), weight * 1000 / (unit * part.len().max(1) as i128))
                })
                .collect();
            println!("FIELD_KERNEL_BLOCKS lap={lap} by_block_tenth(places_tenths:accept_milli)={}", tenths.join(","));
            println!("FIELD_KERNEL_FAMILIES lap={lap} {}", family_text(&learner.field, &by_family, states));
            if !by_section.is_empty() {
                let median = |v: &mut Vec<i128>| -> i128 {
                    v.sort_unstable();
                    v[v.len() / 2]
                };
                let tenths: Vec<String> = (0..10)
                    .map(|k| {
                        let part = &by_section[k * by_section.len() / 10..((k + 1) * by_section.len() / 10).max(k * by_section.len() / 10 + 1).min(by_section.len())];
                        let (mut a, mut sh): (Vec<i128>, Vec<i128>) = part.iter().copied().unzip();
                        format!("{}:{}", median(&mut a), median(&mut sh))
                    })
                    .collect();
                println!("FIELD_KERNEL_NEWTON lap={lap} by_lap_tenth(alpha_milli:shrink_milli medians)={}", tenths.join(","));
            }
        }
        println!(
            "FIELD_CONTRAST_LAP lap={lap} read={} states={states} same={same} gap_micro={} deposited={deposited}/{} lap_ms={} ms={}",
            learner.laps,
            if states == 0 { 0 } else { (gap * 1_000_000) / ((states as i128) << 32) },
            sections.len(),
            lap_start.elapsed().as_millis(),
            started.elapsed().as_millis()
        );
        let held_read = std::time::Instant::now();
        match &host_held {
            Some(h) => h.read(lap as i64, &learner),
            None => enumerated_read(&held_field(&learner, averaging), &held_set, places, &truth_of, realization, lap as i64, &mut enumerated_rows)?,
        }
        clock.held_read(held_read.elapsed().as_millis());
        println!("FIELD_ENUMERATED_READ lap={lap} ms={}", started.elapsed().as_millis());
    }
    Ok(())
}

/// [measurement; November 7, lap 7] Each family's transfer and predicted change over a lap, named by the layout, in
/// micro-bits a state: `name=transfer/predicted`. Since November 9 05:00 both are the length law's own operands, the step as
/// the deposit carries it priced on `2^(−44)` bits ([`holonics::hnn::tower::field::PRICE_BITS`]).
fn family_text(field: &Field, sums: &[(i128, i128)], states: usize) -> String {
    let names = family_names(field);
    field
        .families_all()
        .iter()
        .zip(sums)
        .filter(|(fam, _)| fam.1 > 0)
        .map(|(&(start, _, _), &(t, p))| {
            let name = names.iter().find(|&&(_, at)| at == start).map_or("?", |&(n, _)| n);
            let micro = |v: i128| v * 1_000_000 / ((states.max(1) as i128) << holonics::hnn::tower::field::PRICE_BITS);
            format!("{name}={}/{}", micro(t), micro(p))
        })
        .collect::<Vec<_>>()
        .join(" ")
}

/// [measurement] Each family's moved grains in a section, `name=Σ|Δθ|/entries`, the families that moved alone (the
/// `FIELD_STEP` line).
fn step_text(field: &Field, before: &[i32]) -> String {
    let names = family_names(field);
    field
        .families_all()
        .iter()
        .filter(|fam| fam.1 > 0)
        .filter_map(|&(start, len, _)| {
            let total: i128 = (start..start + len).map(|i| (field.theta[i] as i128 - before[i] as i128).abs()).sum();
            (total > 0).then(|| format!("{}={}/{len}", names.iter().find(|&&(_, at)| at == start).map_or("?", |&(n, _)| n), total))
        })
        .collect::<Vec<_>>()
        .join(" ")
}

/// [measurement; theory, November 9 05:04] **Each family's length after the section**, `name=ρ_f` in milli-bits (the step is
/// `2^(−ρ_f)` of the moments' unit), every family with entries in the layout's order, read after the section's length update
/// (the `FIELD_LENGTHS` line beside `FIELD_STEP`, so a family's wake rate reads beside its moved grains); where the learner
/// reads no family lengths each family's is the learner's one rate. A reading: it changes nothing.
fn lengths_text(learner: &FieldLearner) -> String {
    let names = family_names(&learner.field);
    learner
        .field
        .families_all()
        .iter()
        .enumerate()
        .filter(|(_, fam)| fam.1 > 0)
        .map(|(k, _)| {
            let name = names.get(k).map_or_else(|| format!("family{k}"), |(n, _)| n.to_string());
            let rho = learner.family_rates.as_ref().map_or(i128::from(learner.rate_bits) << holonics::hnn::tower::MATERIAL_BITS, |r| r.get(k).copied().unwrap_or(0));
            format!("{name}={}", rho * 1000 >> holonics::hnn::tower::MATERIAL_BITS)
        })
        .collect::<Vec<_>>()
        .join(" ")
}

/// [measurement; November 7] Each family's length `ρ_f` in milli-bits and its share (transfer over own-section price, in
/// thousandths) over a span of sections: `name=ρ/share`.
fn rates_text(field: &Field, rates: &[i128], sums: &[(i128, i128)]) -> String {
    let names = family_names(field);
    field
        .families_all()
        .iter()
        .enumerate()
        .filter(|&(_, fam)| fam.1 > 0)
        .map(|(k, &(start, _, _))| {
            let name = names.iter().find(|&&(_, at)| at == start).map_or("?", |&(n, _)| n);
            let rho = rates.get(k).copied().unwrap_or(0) * 1000 >> holonics::hnn::tower::MATERIAL_BITS;
            let (t, p) = sums.get(k).copied().unwrap_or((0, 0));
            let share = if p == 0 { 0 } else { t * 1000 / p.abs() };
            format!("{name}={rho}/{share}")
        })
        .collect::<Vec<_>>()
        .join(" ")
}

/// The layout's families by name and start.
/// [measurement; theory, November 7 19:50, from Brandon's 19:44 lens: efficiency is learning more from the same passage]
/// **The sections' coherence**, family by family over a stretch of sections: `n`, `Σ_s |g_s|²` and `|Σ_s g_s|²` of the
/// deposits before their length on the family's natural grain (each entry read `2^16` coarser so the squares keep their
/// carrier), and `|Σg|²/(n Σ|g|²)` in thousandths: near 1000 where the sections share dynamics, near `1000/n` where each
/// section teaches only itself. Its trend across a lap is the grokking read. Kept entry by entry as well (theory, 20:10): each
/// entry's own `α_i = (Σ_s g_i)²/(n Σ_s g_i²)`, the share of a family's moving entries with `α_i > 1/4` (a noise entry passes
/// it at `n = 40` with chance 0.0016) and the share of the family's `Σ_i (Σ_s g_i)²` those entries carry.
struct Coherence {
    n: usize,
    sum: Vec<i128>,
    squares: Vec<i128>,
}

impl Coherence {
    fn new(field: &Field) -> Self {
        Self { n: 0, sum: vec![0; field.material_len()], squares: vec![0; field.material_len()] }
    }
    fn add(&mut self, g: &[i128]) {
        if g.len() != self.sum.len() {
            return;
        }
        self.n += 1;
        for (i, &x) in g.iter().enumerate() {
            let q = x >> 16;
            self.squares[i] = self.squares[i].saturating_add(q.saturating_mul(q));
            self.sum[i] = self.sum[i].saturating_add(x);
        }
    }
    fn text(&self, field: &Field) -> String {
        let names = family_names(field);
        let n = self.n.max(1) as i128;
        field
            .families_all()
            .iter()
            .filter(|fam| fam.1 > 0)
            .filter_map(|&(start, len, _)| {
                let range = start..start + len;
                let squares: i128 = range.clone().map(|i| self.squares[i]).fold(0, i128::saturating_add);
                if squares == 0 {
                    return None;
                }
                let name = names.iter().find(|&&(_, at)| at == start).map_or("?", |&(n, _)| n);
                let pull = |i: usize| -> i128 {
                    let q = self.sum[i] >> 16;
                    q.saturating_mul(q)
                };
                let whole: i128 = range.clone().map(pull).fold(0, i128::saturating_add);
                let coherence = whole.checked_mul(1000).map_or(-1, |w| w / n.saturating_mul(squares).max(1));
                let moving = range.clone().filter(|&i| self.squares[i] > 0).count();
                let above: Vec<usize> = range.filter(|&i| self.squares[i] > 0 && pull(i).saturating_mul(4) > n.saturating_mul(self.squares[i])).collect();
                let carried: i128 = above.iter().map(|&i| pull(i)).fold(0, i128::saturating_add);
                let carried_milli = carried.checked_mul(1000).map_or(-1, |c| c / whole.max(1));
                Some(format!("{name}={squares}:{whole}:{coherence}:{}/{moving}:{carried_milli}", above.len()))
            })
            .collect::<Vec<_>>()
            .join(" ")
    }
}

/// [measurement; theory, November 7 22:55] **A leg's readings** (from one saved state to the next): the sections' coherence,
/// each letter's truth count less its conditional mass, the places' surprise bands, `KL(p ‖ face)` and `p(truth)` a place, and
/// each family's step, printed at each save as `FIELD_LEG` lines.
struct Leg {
    coherence: Coherence,
    letters: Vec<i128>,
    bands: Vec<usize>,
    kl: i128,
    moments: [i128; 8],
    truth_p: i128,
    places: usize,
    steps: Vec<i128>,
    sections: usize,
}

impl Leg {
    fn new(field: &Field) -> Self {
        Self { coherence: Coherence::new(field), letters: Vec::new(), bands: Vec::new(), kl: 0, moments: [0; 8], truth_p: 0, places: 0, steps: vec![0; field.families_all().len()], sections: 0 }
    }
    fn add(&mut self, field: &Field, r: &holonics::hnn::tower::field::KernelReceipt, before: &[i32]) {
        self.coherence.add(&r.covector);
        self.sections += 1;
        if self.letters.len() < r.letter_counts.len() {
            self.letters.resize(r.letter_counts.len(), 0);
        }
        for (a, &c) in self.letters.iter_mut().zip(&r.letter_counts) {
            *a += c;
        }
        if self.bands.len() < r.surprise_bands.len() {
            self.bands.resize(r.surprise_bands.len(), 0);
        }
        for (a, &c) in self.bands.iter_mut().zip(&r.surprise_bands) {
            *a += c;
        }
        (self.kl, self.truth_p, self.places) = (self.kl + r.kl_face, self.truth_p + r.weight, self.places + r.places);
        for (a, &b) in self.moments.iter_mut().zip(&r.moments) {
            *a += b;
        }
        for (slot, &(start, len, _)) in self.steps.iter_mut().zip(field.families_all().iter()) {
            *slot += (start..start + len).map(|i| (field.theta[i] as i128 - before[i] as i128).abs()).sum::<i128>();
        }
    }
    fn print(&self, field: &Field, lap: usize, at: usize, what: &str) {
        let unit = 1i128 << holonics::hnn::tower::MATERIAL_BITS;
        let places = self.places.max(1) as i128;
        let mut letters: Vec<(usize, i128)> = self.letters.iter().copied().enumerate().collect();
        letters.sort_by_key(|&(a, c)| (std::cmp::Reverse(c.abs()), a));
        let top: Vec<String> = letters.iter().take(8).map(|&(a, c)| format!("{a}:{}", c * 1000 / unit)).collect();
        let bands: Vec<String> = self.bands.iter().enumerate().filter(|&(_, &c)| c > 0).map(|(k, c)| format!("k{k}={c}")).collect();
        let names = family_names(field);
        let steps: Vec<String> = field
            .families_all()
            .iter()
            .zip(&self.steps)
            .filter(|&(f, &s)| f.1 > 0 && s > 0)
            .map(|(&(start, len, _), &s)| format!("{}={}", names.iter().find(|&&(_, at)| at == start).map_or("?", |&(n, _)| n), s * 1000 / (len as i128 * self.sections.max(1) as i128)))
            .collect();
        println!("FIELD_LEG lap={lap} {what} sections={at} legsections={} places={} truth_p_milli={} kl_face_milli_nats={}", self.sections, self.places, self.truth_p * 1000 / (unit * places), self.kl * LN2_Q30 / places * 1000 >> 62);
        // [measurement; theory, November 8 13:11] The read places' seven moments in milli-nats (milli-nats² for the variances)
        // over their beat weights, and the stream's own Newton steps toward sharper (s) and toward the face (w).
        let w = self.moments[7].max(1);
        let nats = |x: i128| -> i128 { x * LN2_Q30 / w * 1000 >> 62 };
        let nats2 = |x: i128| -> i128 { (x * LN2_Q30 >> 30) * LN2_Q30 / w * 1000 >> 62 };
        let m: Vec<i128> = (0..4).map(|i| nats(self.moments[i])).chain((4..7).map(|i| nats2(self.moments[i]))).collect();
        let s_step = if m[4] != 0 { 1000 - (m[0] - m[1]) * 1000 / m[4] } else { 0 };
        let w_step = if m[5] != 0 { 1000 - (m[3] - m[2]) * 1000 / m[5] } else { 0 };
        // [theory, November 8 15:33] The f terms are read against the face carried at the truth (built from the truth letter, so
        // they leak it); w's calibration is read on held rows against the open face. code, h, var_lnp and s stand.
        println!("FIELD_LEG_MOMENTS lap={lap} {what} sections={at} weight={} code={} h={} f_carried_truth={} kl_carried={} var_lnp={} var_f_carried={} cov_carried={} s_milli={s_step} w_carried_milli={w_step}", self.moments[7], m[0], m[1], m[2], m[3], m[4], m[5], m[6]);
        println!("FIELD_LEG_COHERENCE lap={lap} {what} n={} {}", self.coherence.n, self.coherence.text(field));
        println!("FIELD_LEG_LETTERS lap={lap} {what} truth_count_less_mass_milli {}", top.join(" "));
        println!("FIELD_LEG_BANDS lap={lap} {what} {}", bands.join(" "));
        println!("FIELD_LEG_STEPS lap={lap} {what} milli_grains_an_entry_a_section {}", steps.join(" "));
        // The width census's sites (FIELD_CENSUS=1, theory November 8): each site's largest bit length and how often it was
        // met, cumulative over the run.
        for r in holonics::number::census::report() {
            println!("FIELD_CENSUS_SITE lap={lap} {what} most_bits={} met={} site={}", r.most_bits, r.met, r.site);
        }
    }
}

/// The field a held read reads: the averaged constitution where it is kept and declared, the live field otherwise.
fn held_field(learner: &FieldLearner, averaging: bool) -> Field {
    if averaging { learner.averaged_field() } else { learner.field.clone() }
}

fn family_names(field: &Field) -> Vec<(&'static str, usize)> {
    let l = field.layout();
    vec![("enc", l.enc), ("before", l.before), ("after", l.after), ("q", l.q), ("q_bias", l.q_bias), ("v", l.v), ("v_bias", l.v_bias), ("out", l.out), ("out_bias", l.out_bias), ("a", l.a), ("a_bias", l.a_bias), ("b", l.b), ("b_bias", l.b_bias), ("w", l.w), ("w_bias", l.w_bias), ("read", l.read), ("read_bias", l.read_bias), ("moment_before", l.moment_before), ("moment_after", l.moment_after), ("temper", l.temper), ("probe", l.probe), ("probe_bias", l.probe_bias), ("pace", l.pace), ("moment_face", l.moment_face), ("moment_face_bias", l.moment_face_bias), ("lift_bias", l.lift_bias), ("pair_c", l.pair_c), ("face_temper", l.face_temper)]
}

/// `ln 2` on `2^(−30)` (`⌊ln 2 · 2^30⌉`), the readings' carrier from bits to nats.
const LN2_Q30: i128 = 744_261_118;

/// `2^x` on `2^(−32)` for `x` on `2^(−32)` (a reading's face, read at its declared width): the whole part as a shift, the
/// fraction as the product of `2^(2^(−i))` over its set bits, each the root of the one before by integer square roots.
/// [measurement; theory, November 8 17:18] The closing read's chart: each answer's `G/T` a place in milli-nats, its question,
/// answer and near tail read at the field's own `T` (`read_energies`, as `FIELD_WRITE_ENERGY` reads it).
fn closing_per_place(field: &Field, realization: &mut dyn FieldRealization, problems: &[(&[usize], usize)], answers: &[Vec<usize>], void: usize) -> Result<Vec<i128>> {
    let configurations: Vec<Vec<usize>> = problems
        .iter()
        .zip(answers)
        .map(|(&(q, room), a)| {
            let mut c: Vec<usize> = q.iter().chain(a).copied().collect();
            c.extend(std::iter::repeat_n(void, holonics::hnn::tower::field::NEAR.min(room - a.len())));
            c
        })
        .collect();
    let asked: Vec<&[usize]> = configurations.iter().map(Vec::as_slice).collect();
    let g = realization.read_energies(field, &asked).map_err(|e| e.to_string())?;
    let inverse = exp2_q32(-((field.theta[field.layout().face_temper] as i128) << 8));
    Ok(g.iter().zip(answers).map(|(&g, a)| (((g * inverse >> 32) * LN2_Q30 >> 30) / a.len().max(1) as i128) * 1000 >> 32).collect())
}

fn exp2_q32(x: i128) -> i128 {
    let whole = x >> 32;
    let frac = x & ((1i128 << 32) - 1);
    let mut root: u128 = 2u128 << 32;
    let mut out: u128 = 1u128 << 32;
    for i in 1..=32 {
        root = (root << 32).isqrt();
        if frac >> (32 - i) & 1 == 1 {
            out = (out * root) >> 32;
        }
    }
    let out = out as i128;
    if whole >= 0 {
        if whole > 60 { i128::MAX >> 2 } else { out << whole }
    } else if whole < -100 {
        0
    } else {
        out >> (-whole)
    }
}

/// `log₂ x` on `2^(−16)` for `x ≥ 1`: the leading bit's place, then sixteen fraction bits by repeated squaring of the mantissa.
fn log2_q16(x: u64) -> i64 {
    if x == 0 {
        return 0;
    }
    let whole = 63 - x.leading_zeros() as i64;
    // The mantissa in [1, 2) on 2^(−62).
    let mut m: u128 = (x as u128) << (62 - whole);
    let mut frac = 0i64;
    for bit in (0..16).rev() {
        m = (m * m) >> 62;
        if m >= 2u128 << 62 {
            m >>= 1;
            frac |= 1 << bit;
        }
    }
    (whole << 16) | frac
}

/// The learner's text at the rate `rate`, the state's own (a section's evidence sets the step from it; [`contrast_field`]).
fn at_rate(learner: &FieldLearner, rate: u32) -> String {
    let mut written = learner.clone();
    written.rate_bits = rate;
    written.to_text()
}

/// [measurement; the unified-theory reading of November 7, 04:05] **The enumerated conditional at held places** (lap 4's score):
/// for the first `places` held problems, one keyed answer place `t` each, the rest at the truth. The face at `t` (`t` open,
/// [`FieldRealization::read_faces`]) beside every letter's energy `G(rest, e_t = c)` at its own certified halvings
/// ([`FieldRealization::read_energies`]), so `P(c | rest) ∝ 2^(−G_c/T)` is the enumerated conditional (every letter's `G` read) and the face only proposes.
/// Each place's row goes to `rows`: the open face's masses and total (the place open, carrying the uniform mixture as an
/// energy field's open sites do), `log₂ T` on `2^(−24)`, the energies on `2^(−32)` bits, and the face at the truth (the
/// place carrying its truth letter whole, as a kernel block opens it).
/// The codes and `KL(enumerated ‖ face)` are read from the rows at the receipt (a reading only: nothing in the run reads it).
fn enumerated_read(field: &Field, held: &Problems, places: usize, truth_of: &dyn Fn(&(Vec<usize>, Vec<usize>, usize), &[usize]) -> Vec<usize>, realization: &mut dyn FieldRealization, lap: i64, rows: &mut std::fs::File) -> Result<()> {
    let chosen = enumerated_places(held, places, truth_of);
    for line in enumerated_rows(field, &chosen, realization, lap)? {
        row(rows, &line)?;
    }
    Ok(())
}

/// The held places an enumerated read takes: each of the first `places` held problems' keyed answer place, its truth and its
/// question's length.
type HeldPlaces = Vec<(usize, Vec<usize>, usize, usize)>;

/// [definition; theory, November 8 13:13] Past one place a held problem, the rest of `places` are drawn per letter: every held
/// answer place but the problems' own keyed ones, in a keyed order, without replacement, so they weigh the held problems by
/// answer length as the stream does. The first `held.len()` places of a read stay one a problem, continuous with every read
/// before; the rows keep that order.
fn enumerated_places(held: &Problems, places: usize, truth_of: &dyn Fn(&(Vec<usize>, Vec<usize>, usize), &[usize]) -> Vec<usize>) -> HeldPlaces {
    // [measurement; theory, November 8 14:22] `FIELD_HELD_ALL_OF=K`: every answer place of the first K held problems (the
    // writer's own answers), so the enumerated conditional reads the places the writer's joint code is read on.
    if let Some(k) = std::env::var("FIELD_HELD_ALL_OF").ok().and_then(|v| v.parse::<usize>().ok()) {
        return held.iter().take(k).enumerate().flat_map(|(i, p)| (0..p.1.len()).map(move |j| (i, truth_of(p, &p.1), p.0.len() + j, p.0.len()))).collect();
    }
    let mut chosen: HeldPlaces = held
        .iter()
        .take(places)
        .enumerate()
        .map(|(k, p)| {
            let t = p.0.len() + (mix(ENUMERATED_KEY, k as u64) as usize) % p.1.len();
            (k, truth_of(p, &p.1), t, p.0.len())
        })
        .collect();
    if places > chosen.len() {
        let first: std::collections::BTreeSet<(usize, usize)> = chosen.iter().map(|(k, _, t, _)| (*k, *t)).collect();
        let mut letters: Vec<(u64, usize, usize)> = held
            .iter()
            .enumerate()
            .flat_map(|(k, p)| (0..p.1.len()).map(move |j| (k, p.0.len() + j)))
            .filter(|key| !first.contains(key))
            .map(|(k, t)| (mix(ENUMERATED_KEY ^ 0x1E77_E5, ((k as u64) << 32) | t as u64), k, t))
            .collect();
        letters.sort_unstable();
        for &(_, k, t) in letters.iter().take(places - chosen.len()) {
            let p = &held[k];
            chosen.push((k, truth_of(p, &p.1), t, p.0.len()));
        }
    }
    chosen
}

/// Each problem's question, its answer cut to the room, and the room (`Problems`' third place), as the held reads encode them.
fn encoded_problems(codec: &FieldCodec, problems: &[(Vec<u8>, Vec<u8>)], field: &Field) -> Result<Problems> {
    let mut set = Vec::with_capacity(problems.len());
    for (question, answer) in problems {
        let (q, room) = opening(codec, field, question, b"")?;
        let mut a = codec.encode(answer)?;
        a.truncate(room);
        if !a.is_empty() {
            set.push((q, a, room));
        }
    }
    Ok(set)
}

/// A problem's truth at `letters`: its question, the letters, and the near field's voids its room leaves past them.
fn truth_with_voids(void: usize, (q, a, room): &(Vec<usize>, Vec<usize>, usize), letters: &[usize]) -> Vec<usize> {
    let mut t: Vec<usize> = q.iter().chain(letters).copied().collect();
    t.extend(std::iter::repeat_n(void, holonics::hnn::tower::field::NEAR.min(room - a.len())));
    t
}

/// [measurement; theory, November 8, the lead reading] **`lead-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD
/// HELD_SHA PLACES OUT`**: whether a letter leads its own state, at the held places the enumerated conditional reads
/// ([`enumerated_places`]: the first `PLACES`, `FIELD_HELD_ALL_OF` as there), each place's configuration its truth with every
/// site resolved (the enumerated read's configuration at the truth letter: one relaxation a place). Each place's lead
/// ([`holonics::hnn::tower::field::EnergyLead`], read through the realization's own buffers) gives per lane (a)
/// `cos(r̂_t, Rᵀ E(u_t))` at the relaxed state and (b) `‖E(u_t) + E₋(u_(t−1)) + E₊(u_(t+1))‖ / ‖C s_t + b‖` at the opening, and
/// beside them (theory, November 9) `c_open = cos(x⁰_t, Rᵀ E(u_t))` (the opening state) and `c_EE = cos(E(u_t), Rᵀ E(u_t))`
/// (the opening's own term), in thousandths, nearest. Prints a `FIELD_LEAD` line a lane with the quartiles and median of each over the places (nearest
/// rank, `⌈p n⌉`-th smallest), one with `lane=all` (each place's whole site: every lane's sums added) and one with
/// `lane=pooled` (every lane of every place); writes each place's lane sums and readings to `LEAD.tsv` (the series the
/// readings are formed from; no letter). `FIELD_CONTRAST_AVERAGE` reads the averaged constitution, as the held read does.
/// A reading only: nothing is deposited and no state is written.
pub(super) fn lead_field(args: &[String], realization: &mut dyn FieldRealization) -> Result<()> {
    if args.len() != 11 {
        return Err("lead-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD HELD_SHA PLACES OUT".into());
    }
    let started = std::time::Instant::now();
    let mut learner = FieldLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    declared_clocks(&mut learner.field);
    if !learner.field.declaration.energy {
        return Err("lead-field reads a field whose faces are one energy's forces".into());
    }
    let units = units_of(&args[5], &args[6])?;
    let codec = FieldCodec::from_text(std::str::from_utf8(&pinned_read(&args[3], &args[4], CODEC_BUDGET)?)?, units)?;
    let held_text = problems_of(&pinned_read(&args[7], &args[8], READ_BUDGET as usize)?);
    let places = positive(&args[9])?;
    let out = Path::new(&args[10]);
    std::fs::create_dir(out)?;
    let averaging = std::env::var_os("FIELD_CONTRAST_AVERAGE").is_some();
    let field = held_field(&learner, averaging);
    let held_set = encoded_problems(&codec, &held_text, &learner.field)?;
    let void = codec.void();
    let truth_of = |p: &(Vec<usize>, Vec<usize>, usize), letters: &[usize]| -> Vec<usize> { truth_with_voids(void, p, letters) };
    let chosen = enumerated_places(&held_set, places, &truth_of);
    let asked: Vec<(&[usize], usize)> = chosen.iter().map(|(_, truth, t, _)| (truth.as_slice(), *t)).collect();
    let sites: usize = asked.iter().map(|(c, _)| c.len()).sum();
    let reading = std::time::Instant::now();
    let leads = realization.read_energy_leads(&field, &asked).map_err(|e| e.to_string())?;
    let read_ms = reading.elapsed().as_millis();
    let lanes = field.declaration.lanes;
    let cos_text = |c: Option<i64>| c.map_or("none".to_string(), |v| v.to_string());
    let ratio_text = |r: Option<u128>| r.map_or("inf".to_string(), |v| v.to_string());
    let mut rows = rows_file(
        &out.join("LEAD.tsv"),
        "problem\tplace\tlane\tread_own\tread_read\town_own\tletters_letters\tmoment_moment\tcos_milli\tratio_milli\topen_own\topen_open\tenc_own\tenc_enc\tc_open_milli\tc_ee_milli\n",
    )?;
    for ((k, _, t, q), lead) in chosen.iter().zip(&leads) {
        for lane in 0..lanes {
            let ((dot, rr, oo), (ll, mm), (xo, xx), (eo, ee)) = (lead.own[lane], lead.opening[lane], lead.open[lane], lead.enc[lane]);
            let at = Some(lane);
            let (cos, ratio, c_open, c_ee) = (cos_text(lead.cos_milli(at)), ratio_text(lead.ratio_milli(at)), cos_text(lead.cos_open_milli(at)), cos_text(lead.cos_ee_milli(at)));
            row(&mut rows, &format!("{k}\t{}\t{lane}\t{dot}\t{rr}\t{oo}\t{ll}\t{mm}\t{cos}\t{ratio}\t{xo}\t{xx}\t{eo}\t{ee}\t{c_open}\t{c_ee}\n", t - q))?;
        }
    }
    // Each reading of a lead on a lane (the whole site with `None`): the relaxed cosine, the ratio, `c_open` and `c_EE`.
    type Readings = (Option<i64>, Option<u128>, Option<i64>, Option<i64>);
    let readings = |l: &holonics::hnn::tower::field::EnergyLead, lane: Option<usize>| -> Readings { (l.cos_milli(lane), l.ratio_milli(lane), l.cos_open_milli(lane), l.cos_ee_milli(lane)) };
    let quartiles = |values: Vec<Option<i64>>| -> [String; 3] {
        rank_quartiles(values.into_iter().flatten().collect()).map_or(["none".to_string(), "none".to_string(), "none".to_string()], |(a, b, d)| [a.to_string(), b.to_string(), d.to_string()])
    };
    // A ratio with no bounded value (the moment's term zero) stands above every bounded one.
    let line = |lane: &str, reads: Vec<Readings>| {
        let n = reads.len();
        let unread = |pick: &dyn Fn(&Readings) -> bool| reads.iter().filter(|r| pick(r)).count();
        let (cos_unread, unbounded, open_unread, ee_unread) = (unread(&|r| r.0.is_none()), unread(&|r| r.1.is_none()), unread(&|r| r.2.is_none()), unread(&|r| r.3.is_none()));
        let c = quartiles(reads.iter().map(|r| r.0).collect());
        let r = rank_quartiles(reads.iter().map(|r| r.1.unwrap_or(u128::MAX)).collect())
            .map_or(["none".to_string(), "none".to_string(), "none".to_string()], |(a, b, d)| [a, b, d].map(|v| if v == u128::MAX { "inf".to_string() } else { v.to_string() }));
        let (o, e) = (quartiles(reads.iter().map(|r| r.2).collect()), quartiles(reads.iter().map(|r| r.3).collect()));
        println!(
            "FIELD_LEAD lane={lane} cos_q25={} cos_median={} cos_q75={} ratio_q25={} ratio_median={} ratio_q75={} c_open_q25={} c_open_median={} c_open_q75={} c_ee_q25={} c_ee_median={} c_ee_q75={} reads={n} cos_unread={cos_unread} ratio_unbounded={unbounded} c_open_unread={open_unread} c_ee_unread={ee_unread}",
            c[0], c[1], c[2], r[0], r[1], r[2], o[0], o[1], o[2], e[0], e[1], e[2]
        );
    };
    for lane in 0..lanes {
        line(&lane.to_string(), leads.iter().map(|l| readings(l, Some(lane))).collect());
    }
    line("all", leads.iter().map(|l| readings(l, None)).collect());
    line("pooled", leads.iter().flat_map(|l| (0..lanes).map(move |k| readings(l, Some(k)))).collect());
    println!(
        "FIELD_LEAD_READ places={} sites={sites} lanes={lanes} width={} ticks={} averaged={} read_ms={read_ms} host_threads={} ms={}",
        leads.len(),
        field.declaration.width,
        field.declaration.ticks,
        u8::from(averaging),
        rayon::current_num_threads(),
        started.elapsed().as_millis()
    );
    Ok(())
}

/// [definition; theory, November 9, the class reading] A support's receipt word: FNV-1a over 64 bits (offset basis
/// `0xcbf2_9ce4_8422_2325`, prime `0x100_0000_01b3`) of its sorted offsets, each as its eight little-endian octets, so two
/// places' supports are compared by the word and their sizes without carrying either list. A reading's name, never a key the
/// machine reads.
fn support_word(offsets: &[i64]) -> u64 {
    offsets.iter().flat_map(|o| o.to_le_bytes()).fold(0xcbf2_9ce4_8422_2325u64, |h, b| (h ^ u64::from(b)).wrapping_mul(0x100_0000_01b3))
}

/// [measurement; theory, November 9, the class reading] **`class-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD
/// HELD_SHA PLACES OUT`**: whether a letter redraws the classes its place's opening is held at, or the halvings its descent
/// stands at, the two discrete maps the covector is taken across without seeing. At the held places the enumerated
/// conditional reads ([`enumerated_places`]: the first `PLACES`, `FIELD_HELD_ALL_OF` as there), at the state's live `θ` (not
/// the averaged constitution), each letter `c` of the alphabet at the place with the rest at the truth (the enumerated read's
/// configurations) is relaxed as `G` is ([`FieldRealization::read_energy_held_classes`]:
/// [`holonics::hnn::tower::field::Field::energy_held_classes`] on the host, the card's own lists and relaxation on the card),
/// and at the place `t` and at `t ± 1` (the letter at `t` enters its neighbours' opening through their before and after rows)
/// each head's key class, probe class and lock support are read.
///
/// Writes `CLASSES.tsv`, a row a configuration, site and head: `problem`, `place` (in the answer), `letter` (its codec
/// index; no letter text), `site_offset` (−1, 0, +1), `head`, `class`, `probe_class` (the trits' numbers), `support_size`,
/// `support_word` ([`support_word`] of the support's sorted offsets from `t`, in hexadecimal) and `far` (the offsets from `t`
/// of the sources past the row's near field, comma-separated, `-` for none; the near field is every site within `NEAR − 1`
/// of the row, all keyed, and moves with no letter). Writes `HALVINGS.tsv`, a row a configuration: `problem`, `place`, `letter`, `stood` (the ticks that stood),
/// `rested` (1 where a tick rested and ended the descent), `halvings` (each standing tick's halvings in order, `-` for none)
/// and `g` (`G` on `2^(−32)` bits). Prints one `FIELD_CLASS_READ` line: the places, configurations and rows; against each
/// place's truth letter, the (letter, site, head) rows whose classes moved, whose support moved, and the letters whose
/// halvings moved; the read's time and the host's threads. A reading only: nothing is deposited and no state is written.
pub(super) fn class_field(args: &[String], realization: &mut dyn FieldRealization) -> Result<()> {
    use holonics::hnn::tower::field::NEAR;
    if args.len() != 11 {
        return Err("class-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD HELD_SHA PLACES OUT".into());
    }
    let started = std::time::Instant::now();
    let mut learner = FieldLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    declared_clocks(&mut learner.field);
    if !learner.field.declaration.energy {
        return Err("class-field reads a field whose faces are one energy's forces".into());
    }
    let units = units_of(&args[5], &args[6])?;
    let codec = FieldCodec::from_text(std::str::from_utf8(&pinned_read(&args[3], &args[4], CODEC_BUDGET)?)?, units)?;
    let held_text = problems_of(&pinned_read(&args[7], &args[8], READ_BUDGET as usize)?);
    let places = positive(&args[9])?;
    let out = Path::new(&args[10]);
    std::fs::create_dir(out)?;
    let field = learner.field;
    let held_set = encoded_problems(&codec, &held_text, &field)?;
    let void = codec.void();
    let truth_of = |p: &(Vec<usize>, Vec<usize>, usize), letters: &[usize]| -> Vec<usize> { truth_with_voids(void, p, letters) };
    let chosen = enumerated_places(&held_set, places, &truth_of);
    let alphabet = field.declaration.alphabet;
    let configurations: Vec<Vec<usize>> = chosen
        .iter()
        .flat_map(|(_, truth, t, _)| {
            (0..alphabet).map(move |c| {
                let mut x = truth.clone();
                x[*t] = c;
                x
            })
        })
        .collect();
    let asked: Vec<(&[usize], usize)> = configurations.iter().zip(chosen.iter().flat_map(|(_, _, t, _)| std::iter::repeat_n(*t, alphabet))).map(|(c, t)| (c.as_slice(), t)).collect();
    let reading = std::time::Instant::now();
    let reads = realization.read_energy_held_classes(&field, &asked).map_err(|e| e.to_string())?;
    let read_ms = reading.elapsed().as_millis();
    if reads.len() != asked.len() {
        return Err("class-field: a read that is not one a configuration".into());
    }
    let heads = field.declaration.heads;
    let mut classes = rows_file(&out.join("CLASSES.tsv"), "problem\tplace\tletter\tsite_offset\thead\tclass\tprobe_class\tsupport_size\tsupport_word\tfar\n")?;
    let mut halvings = rows_file(&out.join("HALVINGS.tsv"), "problem\tplace\tletter\tstood\trested\thalvings\tg\n")?;
    let (mut rows, mut compared, mut class_moved, mut support_moved, mut letters_compared, mut halvings_moved) = (0u64, 0u64, 0u64, 0u64, 0u64, 0u64);
    for (n, (k, truth, t, q)) in chosen.iter().enumerate() {
        let place = &reads[n * alphabet..(n + 1) * alphabet];
        let truth_read = &place[truth[*t]];
        let (mut class_text, mut halving_text) = (String::new(), String::new());
        for (c, read) in place.iter().enumerate() {
            if read.site != *t || read.heads.len() != heads {
                return Err("class-field: a read at another place or of other heads".into());
            }
            for (i, &s) in read.sites.iter().enumerate() {
                let offset = s as i64 - *t as i64;
                for (h, lists) in read.heads.iter().enumerate() {
                    let at = &lists[i];
                    let offsets: Vec<i64> = at.support.iter().map(|&j| j as i64 - *t as i64).collect();
                    let far: Vec<String> = at.support.iter().filter(|&&j| (j as usize).abs_diff(s) >= NEAR).map(|&j| (j as i64 - *t as i64).to_string()).collect();
                    let far = if far.is_empty() { "-".to_string() } else { far.join(",") };
                    class_text.push_str(&format!("{k}\t{}\t{c}\t{offset}\t{h}\t{}\t{}\t{}\t{:016x}\t{far}\n", t - q, at.class, at.probe_class, offsets.len(), support_word(&offsets)));
                    rows += 1;
                    if c != truth[*t] {
                        let base = truth_read.heads.get(h).and_then(|l| truth_read.sites.iter().position(|&x| x == s).map(|p| &l[p])).ok_or("class-field: the truth's read misses a site")?;
                        compared += 1;
                        class_moved += u64::from((at.class, at.probe_class) != (base.class, base.probe_class));
                        support_moved += u64::from(at.support != base.support);
                    }
                }
            }
            let stood: Vec<String> = read.read.halvings.iter().flatten().map(u32::to_string).collect();
            let rested = u8::from(read.read.halvings.iter().any(Option::is_none));
            let list = if stood.is_empty() { "-".to_string() } else { stood.join(",") };
            halving_text.push_str(&format!("{k}\t{}\t{c}\t{}\t{rested}\t{list}\t{}\n", t - q, stood.len(), read.read.last));
            if c != truth[*t] {
                letters_compared += 1;
                halvings_moved += u64::from(read.read.halvings != truth_read.read.halvings);
            }
        }
        row(&mut classes, &class_text)?;
        row(&mut halvings, &halving_text)?;
    }
    println!(
        "FIELD_CLASS_READ places={} configurations={} rows={rows} heads={heads} ticks={} class_moved={class_moved}/{compared} support_moved={support_moved}/{compared} halvings_moved={halvings_moved}/{letters_compared} read_ms={read_ms} host_threads={} ms={}",
        chosen.len(),
        reads.len(),
        field.declaration.ticks,
        rayon::current_num_threads(),
        started.elapsed().as_millis()
    );
    Ok(())
}

/// [definition; theory, November 9 09:34, the word reading] `arcsin(2^(−k))` on `2^(−100)`, `k ≥ 1`, by its series
/// `Σ_n t_n` with `t_0 = x` and `t_n = t_(n−1) x² (2n − 1)² / (2n (2n + 1))`, summed until a term releases to zero (each term
/// at most a quarter of the one before, so the sum's floor error is under one unit a term). A reading's navigator, never a
/// law's: it names the cone band's width in phase.
fn arcsin_power(k: u32) -> u128 {
    const ONE: u32 = 100;
    let mut term: u128 = 1u128 << (ONE - k);
    let (mut sum, mut n) = (term, 1u128);
    while term > 0 {
        term = (term >> (2 * k)) * (2 * n - 1) * (2 * n - 1) / ((2 * n) * (2 * n + 1));
        sum += term;
        n += 1;
    }
    sum
}

/// [measurement; theory, November 9 09:34, the word reading] **The cone band's half-width in phase** for `ε = 2^(−k)`: a mode
/// `w = r e^(iφ)` has `λ = |re² − im²|/(re² + im²) = |cos 2φ|`, and the cone `|re| = |im|` lies at `cos 2φ = 0`, so `λ < ε`
/// exactly where `φ` lies within `½ arcsin ε` of the cone. Returned in micro-radians and milli-degrees, nearest, with
/// `π = 6 arcsin ½` from the same series (`arcsin 1 = 3 arcsin ½` where `k = 0`).
fn band_half_width(k: u32) -> (u128, u128) {
    let half_pi_third = arcsin_power(1);
    let arcsin = if k == 0 { 3 * half_pi_third } else { arcsin_power(k) };
    let pi = 6 * half_pi_third;
    let micro = (arcsin * 1_000_000 / 2 + (1u128 << 99)) >> 100;
    let milli_degrees = (arcsin * 180_000 + pi) / (2 * pi);
    (micro, milli_degrees)
}

/// [measurement; theory, November 9 11:10] **`walk-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA TRAIN TRAIN_SHA SECTION
/// FROM COUNT`**: the declared workload of a run's sections before it is launched. The training passage's sections as
/// `contrast-field` forms them ([`sections_of`] at the state's seed, [`contrast_seed`]) in the keyed order its learner walks them
/// at its lap count ([`walk`]), and for each walked section from `FROM`, `COUNT` of them, one `FIELD_WALK` line: the walk index,
/// the section, its problems (and their indices in the encoded passage, `members`; the summary prints the passage's and the
/// encoded set's counts, equal where no answer encoded empty), the summed answer places `P` (the places a fresh write sweeps, at true lengths), `Σ L²` and the
/// longest answer, and `site_reads`, the sites a sweep reads at most (`Σ_k (L_k + 1)(Q_k + L_k + v_k)`, [`sweep_site_reads`]:
/// its opening read of every answer's region, and each proposing answer reading its whole region with its near tail of voids;
/// since theory, November 9 12:18, the opening read is counted); the save law projects a section of fresh writes as its
/// declared sweeps times these site reads times the run's largest measured time per site read ([`section_work`],
/// [`SaveRate`]), from the same function. A reading only: it opens nothing on the realization.
pub(super) fn walk_field(args: &[String]) -> Result<()> {
    if args.len() != 12 {
        return Err("walk-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA TRAIN TRAIN_SHA SECTION FROM COUNT".into());
    }
    let learner = FieldLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let units = units_of(&args[5], &args[6])?;
    let codec = FieldCodec::from_text(std::str::from_utf8(&pinned_read(&args[3], &args[4], CODEC_BUDGET)?)?, units)?;
    let train_text = problems_of(&pinned_read(&args[7], &args[8], READ_BUDGET as usize)?);
    let (section, from, count) = (positive(&args[9])?, self::count(&args[10])?, positive(&args[11])?);
    let seed = contrast_seed(&learner, &args[2])?;
    let train_set = encoded_problems(&codec, &train_text, &learner.field)?;
    let (sections, _) = sections_of(&train_set, section, 0, seed);
    let order = walk(seed, learner.laps, sections.len());
    let (mut total_p, mut total_sq, mut total_reads) = (0u128, 0u128, 0u128);
    for (n, &s) in order.iter().enumerate().skip(from).take(count) {
        let lengths: Vec<u128> = sections[s].iter().map(|&i| train_set[i].1.len() as u128).collect();
        let p: u128 = lengths.iter().sum();
        let sq: u128 = lengths.iter().map(|l| l * l).sum();
        let site_reads = sweep_site_reads(&train_set, &sections[s]);
        (total_p, total_sq, total_reads) = (total_p + p * p, total_sq + sq, total_reads + site_reads);
        let members: Vec<String> = sections[s].iter().map(usize::to_string).collect();
        println!("FIELD_WALK n={n} section={s} problems={} places={p} places_squared={} sum_l_squared={sq} site_reads={site_reads} longest={} members={}", lengths.len(), p * p, lengths.iter().max().unwrap_or(&0), members.join(","));
    }
    println!("FIELD_WALK_READ seed={seed:016x} laps={} sections={} from={from} count={count} sum_places_squared={total_p} sum_l_squared={total_sq} site_reads={total_reads} problems={} encoded={}", learner.laps, sections.len(), train_text.len(), train_set.len());
    Ok(())
}

/// [measurement; theory, November 9 09:34 and 09:42, the word reading] **`word-field STATE STATE_SHA CODEC CODEC_SHA UNITS
/// UNITS_SHA HELD HELD_SHA PLACES OUT`**: the address words a held place's classes and lock supports are read from, written so
/// a changed support between two states can be told apart as the receiver's own probe word moving or a far source's key
/// moving. At the held places the trainer's held read takes ([`enumerated_places`], `FIELD_HELD_ALL_OF` as there), at live
/// `θ`, each place's truth configuration is opened as the energy opens it ([`FieldRealization::read_energy_opening_words`]:
/// on the card from its own `qkv` and `pr` carriers, [`holonics::hnn::tower::field::Field::energy_opening_words`] on the
/// host); every site of a truth is resolved, so definite.
///
/// - `WORDS.tsv`, at `t` and `t ± 1`, a row a site, head, mode and kind: `problem`, `place` (in the answer), `site_offset`
///   (−1, 0, +1), `head`, `mode`, `kind` (`key`, the unframed `q`; `probe`, `p` with its moment added), `re`, `im` (the
///   realization's integers), `trit` ([`holonics::hnn::tower::field::shell`]: 2 where `re > |im|`, 0 where `re < −|im|`, 1
///   otherwise), `band_milli` (`λ = |re² − im²|/(re² + im²)` in thousandths, nearest; `-` for the zero word), `inside` (1 where
///   `λ < ε`, the code's own near-cone test, [`holonics::hnn::tower::field::probes`]), `base` (1 for the class's own `b` modes,
///   [`holonics::hnn::tower::field::FieldDeclaration::class_trits`]) and `eps_bits` (`ε = 2^(−eps_bits)`, `band_bits(b)`: the
///   band the code reads on a probe; it reads none on a key, so a key row's `inside` is the geometry at the same `ε`).
/// - `KEYS.tsv`, every site's key word (each a definite source): `problem`, `place`, `site` (its index in the region), `head`,
///   `mode`, `re`, `im`, `trit`, `band_milli`.
///
/// No letter. Prints one `FIELD_WORD_READ` line: the places and rows of each file, the declaration's heads, modes and `b`,
/// `ε = 2^(−band_bits(b))` and its half-width in phase ([`band_half_width`]: `½ arcsin ε`, the code's geometry), the base
/// modes inside their band by kind, the read's time and the host's threads. A reading only: nothing is deposited and no state
/// is written.
pub(super) fn word_field(args: &[String], realization: &mut dyn FieldRealization) -> Result<()> {
    use holonics::hnn::tower::field::{band_bits, probes, shell};
    if args.len() != 11 {
        return Err("word-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD HELD_SHA PLACES OUT".into());
    }
    let started = std::time::Instant::now();
    let mut learner = FieldLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    declared_clocks(&mut learner.field);
    if !learner.field.declaration.energy {
        return Err("word-field reads a field whose faces are one energy's forces".into());
    }
    let units = units_of(&args[5], &args[6])?;
    let codec = FieldCodec::from_text(std::str::from_utf8(&pinned_read(&args[3], &args[4], CODEC_BUDGET)?)?, units)?;
    let held_text = problems_of(&pinned_read(&args[7], &args[8], READ_BUDGET as usize)?);
    let places = positive(&args[9])?;
    let out = Path::new(&args[10]);
    std::fs::create_dir(out)?;
    let field = learner.field;
    let held_set = encoded_problems(&codec, &held_text, &field)?;
    let void = codec.void();
    let truth_of = |p: &(Vec<usize>, Vec<usize>, usize), letters: &[usize]| -> Vec<usize> { truth_with_voids(void, p, letters) };
    let chosen = enumerated_places(&held_set, places, &truth_of);
    let asked: Vec<(&[usize], usize)> = chosen.iter().map(|(_, truth, t, _)| (truth.as_slice(), *t)).collect();
    let reading = std::time::Instant::now();
    let reads = realization.read_energy_opening_words(&field, &asked).map_err(|e| e.to_string())?;
    let read_ms = reading.elapsed().as_millis();
    if reads.len() != chosen.len() {
        return Err("word-field: a read that is not one a place".into());
    }
    let d = field.declaration;
    let (heads, n, m, b) = (d.heads, d.modes, d.complex(), d.class_trits());
    let k = band_bits(b);
    // `λ` nearest in thousandths, `⌊(2000 |re² − im²| + s) / 2s⌋` with `s = re² + im²`, in a 128-bit carrier.
    let band_milli = |re: i64, im: i64| -> Result<String> {
        const PAST: &str = "word-field: a word past its 128-bit carrier";
        let (rr, ii) = (re as i128 * re as i128, im as i128 * im as i128);
        let total = rr.checked_add(ii).ok_or(PAST)?;
        if total == 0 {
            return Ok("-".to_string());
        }
        let twice = (rr - ii).abs().checked_mul(2000).and_then(|v| v.checked_add(total)).ok_or(PAST)?;
        Ok((twice / (2 * total)).to_string())
    };
    let inside = |re: i64, im: i64, bits: u32| !probes(std::iter::once((re, im)), bits).is_empty();
    let mut words = rows_file(&out.join("WORDS.tsv"), "problem\tplace\tsite_offset\thead\tmode\tkind\tre\tim\ttrit\tband_milli\tinside\tbase\teps_bits\n")?;
    let mut keys_file = rows_file(&out.join("KEYS.tsv"), "problem\tplace\tsite\thead\tmode\tre\tim\ttrit\tband_milli\n")?;
    let (mut word_rows, mut key_rows) = (0u64, 0u64);
    let (mut key_inside, mut probe_inside, mut base_words) = (0u64, 0u64, 0u64);
    for ((problem, truth, t, q), read) in chosen.iter().zip(&reads) {
        if read.site != *t || read.keys.len() != truth.len() || read.probes.len() != read.sites.len() {
            return Err("word-field: a read at another place".into());
        }
        let place = t - q;
        let mut text = String::new();
        for (i, &s) in read.sites.iter().enumerate() {
            let offset = s as i64 - *t as i64;
            for h in 0..heads {
                for l in 0..n {
                    for (kind, word) in [("key", &read.keys[s]), ("probe", &read.probes[i])] {
                        let (re, im) = (word[h * n + l], word[m + h * n + l]);
                        let within = inside(re, im, k);
                        if l < b {
                            base_words += 1;
                            match kind {
                                "key" => key_inside += u64::from(within),
                                _ => probe_inside += u64::from(within),
                            }
                        }
                        text.push_str(&format!("{problem}\t{place}\t{offset}\t{h}\t{l}\t{kind}\t{re}\t{im}\t{}\t{}\t{}\t{}\t{k}\n", shell(re, im), band_milli(re, im)?, u8::from(within), u8::from(l < b)));
                        word_rows += 1;
                    }
                }
            }
        }
        row(&mut words, &text)?;
        let mut text = String::new();
        for (s, word) in read.keys.iter().enumerate() {
            for h in 0..heads {
                for l in 0..n {
                    let (re, im) = (word[h * n + l], word[m + h * n + l]);
                    text.push_str(&format!("{problem}\t{place}\t{s}\t{h}\t{l}\t{re}\t{im}\t{}\t{}\n", shell(re, im), band_milli(re, im)?));
                    key_rows += 1;
                }
            }
        }
        row(&mut keys_file, &text)?;
    }
    let (micro, milli_degrees) = band_half_width(k);
    println!(
        "FIELD_WORD_READ places={} word_rows={word_rows} key_rows={key_rows} heads={heads} modes={n} class_trits={b} band_bits={k} epsilon=2^-{k} half_width_micro_rad={micro} half_width_milli_deg={milli_degrees} key_inside={key_inside}/{} probe_inside={probe_inside}/{} read_ms={read_ms} host_threads={} ms={}",
        reads.len(),
        base_words / 2,
        base_words / 2,
        rayon::current_num_threads(),
        started.elapsed().as_millis()
    );
    Ok(())
}

/// [measurement; theory, November 9 08:13 and 08:15, the held-under reading] **`held-under BASE BASE_SHA STATE STATE_SHA CODEC
/// CODEC_SHA UNITS UNITS_SHA HELD HELD_SHA PLACES OUT HOLD`**: the trainer's held enumerated read at `STATE`'s live `θ` with
/// each configuration's discrete maps held at `BASE`'s live `θ`. At the held places the trainer's held read takes
/// ([`enumerated_places`], `FIELD_HELD_ALL_OF` as there), every letter at each with the rest at the truth, each `G` is read
/// ([`FieldRealization::read_energies_under`], [`holonics::hnn::tower::field::Field::energy_g_under`]) with `HOLD` declaring
/// what `BASE` gives: `classes` its classes, lock lists and supports (`G(θ_S; C_B, h_S)`, the halvings `STATE`'s own) and
/// `classes+halvings` those and its halvings and stood ticks (`G(θ_S; C_B, h_B)`, replayed uncertified); the plain held read is
/// `G(θ_S; C_S, h_S)`. `BASE` and `STATE` share their declaration (else refused); with `BASE` = `STATE` either hold reads the
/// plain held read's bits.
///
/// Writes `ENUMERATED.tsv` in the trainer's held read's format with `lap` −1: the energies held under `BASE`, the open face and
/// the face at the truth `STATE`'s own (the face only proposes; it is not read under `BASE`). Prints one `FIELD_HELD_UNDER`
/// line: the hold, the places and configurations, the held code (each place's `−ln p(truth | rest)` in the conditional
/// section's chart, [`holonics::hnn::tower::field::conditional_code`] at `STATE`'s `T`) in milli- and micro-nats a place, floor,
/// whether `BASE`'s `θ` is `STATE`'s, the read's time and the host's threads. A reading only: nothing is deposited and no
/// state is written.
pub(super) fn held_under(args: &[String], realization: &mut dyn FieldRealization) -> Result<()> {
    use holonics::hnn::tower::field::{conditional_code, BaseHold};
    const USAGE: &str = "held-under BASE BASE_SHA STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD HELD_SHA PLACES OUT classes|classes+halvings";
    if args.len() != 14 {
        return Err(USAGE.into());
    }
    let hold = BaseHold::of(&args[13]).ok_or(USAGE)?;
    let started = std::time::Instant::now();
    let read_learner = |path: &str, sha: &str| -> Result<FieldLearner> {
        let mut learner = FieldLearner::from_text(std::str::from_utf8(&pinned_read(path, sha, STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
        declared_clocks(&mut learner.field);
        Ok(learner)
    };
    let (base, state) = (read_learner(&args[1], &args[2])?.field, read_learner(&args[3], &args[4])?.field);
    if !state.declaration.energy || !base.declaration.energy {
        return Err("held-under reads fields whose faces are one energy's forces".into());
    }
    if base.declaration != state.declaration {
        return Err("held-under: BASE and STATE of another declaration".into());
    }
    let units = units_of(&args[7], &args[8])?;
    let codec = FieldCodec::from_text(std::str::from_utf8(&pinned_read(&args[5], &args[6], CODEC_BUDGET)?)?, units)?;
    let held_text = problems_of(&pinned_read(&args[9], &args[10], READ_BUDGET as usize)?);
    let places = positive(&args[11])?;
    let out = Path::new(&args[12]);
    std::fs::create_dir(out)?;
    let held_set = encoded_problems(&codec, &held_text, &state)?;
    let void = codec.void();
    let truth_of = |p: &(Vec<usize>, Vec<usize>, usize), letters: &[usize]| -> Vec<usize> { truth_with_voids(void, p, letters) };
    let chosen = enumerated_places(&held_set, places, &truth_of);
    let alphabet = state.declaration.alphabet;
    let mut rows = rows_file(&out.join("ENUMERATED.tsv"), "lap\tproblem\tplace\ttruth\tlog2_t\tface_masses\tface_total\tenergies\ttruth_face_masses\ttruth_face_total\n")?;
    let reading = std::time::Instant::now();
    let (lines, energies) = enumerated_reads(&state, &chosen, realization, -1, Some((&base, hold)))?;
    let read_ms = reading.elapsed().as_millis();
    for line in &lines {
        row(&mut rows, line)?;
    }
    let codes = chosen
        .iter()
        .enumerate()
        .map(|(n, (_, truth, t, _))| conditional_code(&state, &energies[n * alphabet..(n + 1) * alphabet], truth[*t]).map(|code| code * LN2_Q30 >> 30).map_err(|e| e.to_string()))
        .collect::<std::result::Result<Vec<i128>, String>>()?;
    let (nats, n) = (codes.iter().sum::<i128>(), chosen.len().max(1) as i128);
    println!(
        "FIELD_HELD_UNDER hold={} places={} configurations={} held_code_milli={} held_code_micro={} same_theta={} read_ms={read_ms} host_threads={} ms={}",
        hold.word(),
        chosen.len(),
        energies.len(),
        nats * 1000 / n >> 32,
        nats * 1_000_000 / n >> 32,
        u8::from(base.theta == state.theta),
        rayon::current_num_threads(),
        started.elapsed().as_millis()
    );
    Ok(())
}

/// [declared read; theory, November 8, the line reading] The line's lengths, `η = 4^k` for `k = 0..=4`, in one section's step.
const LINE_ETAS: [u32; 5] = [1, 4, 16, 64, 256];

/// [measurement; theory, November 8, the line reading] **`line-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD
/// HELD_SHA PLACES OUT`**: whether the deposit has stalled on a descent it does not take. The held code, the enumerated
/// conditional at the held places the trainer's held read takes ([`enumerated_places`], `FIELD_HELD_ALL_OF` as there; its
/// reads [`enumerated_reads`]), each place's `−ln p(truth | rest)` in the conditional section's chart
/// ([`holonics::hnn::tower::field::conditional_code`], read at each point's own `T`), is read at the state's live `θ` (the
/// baseline, `direction=none eta=0`; not the averaged constitution) and at `θ − η u` for each `η` of [`LINE_ETAS`] along two
/// directions ([`FieldLearner::line_directions`], each of length one section's step): `mv`, the deposit's next step from the
/// state's moments with each family at its own length (`η = 1` is that step), and `m`, the first moment scaled to its norm.
/// Each point keeps every entry at `θ`'s grain and 32-bit carrier ([`holonics::hnn::tower::field::line_point`]).
///
/// Prints `FIELD_LINE_STEP` (the step's norm and what moves at `η = 1`), a `FIELD_LINE_FAMILY` line a family (its share of
/// each direction's squared norm in thousandths, its entries moved at `η = 1`, its length), then a `FIELD_LINE` line a point
/// as it is read (the held code a place in milli-nats and micro-nats, floor, its entries moved, the realized step's norm in
/// millionths of `θ`'s unit) and a `FIELD_LINE_READ` line. Writes each point's place codes to `LINE.<direction>.<eta>.tsv`
/// (micro-nats, floor; no letter), and the held read's rows to `ENUMERATED.tsv` marked by the point (0 the baseline, 1 to 5
/// `m`, 6 to 10 `mv`). `FIELD_LINE_STEP_ONLY` prints the step's lines and reads nothing. A reading only: nothing is
/// deposited and no state is written.
///
/// [measurement; theory, November 9 04:20 (a)] With `FAMILIES ETAS` (comma lists: family names as `FIELD_LINE_FAMILY` prints
/// them, and lengths in one section's step), the points are instead the `mv` step restricted to those families (every other
/// entry held at `θ`), one a length (`direction=mv_families`, marked 1 on): the families the deposit's grain truncates, each
/// along its own `m/√v` at its own length, read where the grain first lets them move and past it. No baseline is read then.
pub(super) fn line_field(args: &[String], realization: &mut dyn FieldRealization) -> Result<()> {
    use holonics::hnn::tower::field::{conditional_code, line_norm, line_point, LINE_BITS};
    if args.len() != 11 && args.len() != 13 {
        return Err("line-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD HELD_SHA PLACES OUT [FAMILIES ETAS]".into());
    }
    let started = std::time::Instant::now();
    let mut learner = FieldLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    declared_clocks(&mut learner.field);
    if !learner.field.declaration.energy {
        return Err("line-field reads a field whose faces are one energy's forces".into());
    }
    let units = units_of(&args[5], &args[6])?;
    let codec = FieldCodec::from_text(std::str::from_utf8(&pinned_read(&args[3], &args[4], CODEC_BUDGET)?)?, units)?;
    let held_text = problems_of(&pinned_read(&args[7], &args[8], READ_BUDGET as usize)?);
    let places = positive(&args[9])?;
    let out = Path::new(&args[10]);
    std::fs::create_dir(out)?;
    let held_set = encoded_problems(&codec, &held_text, &learner.field)?;
    let void = codec.void();
    let truth_of = |p: &(Vec<usize>, Vec<usize>, usize), letters: &[usize]| -> Vec<usize> { truth_with_voids(void, p, letters) };
    let chosen = enumerated_places(&held_set, places, &truth_of);
    let directions = learner.line_directions().map_err(|e| e.to_string())?;
    let families = learner.field.families_all();
    let mut grains = vec![0u32; learner.field.material_len()];
    for &(start, n, grain) in &families {
        grains[start..start + n].fill(grain);
    }
    // The moved entries of `u` at `η = 1`, and a change on each family's grain carried to the line's.
    let moved_at_one = |u: &[i128], range: std::ops::Range<usize>| range.filter(|&i| u[i].unsigned_abs() >= 1u128 << (LINE_BITS - grains[i] - 1)).count();
    let on_line = |d: &[i128]| -> Vec<i128> { d.iter().zip(&grains).map(|(&x, &g)| x << (LINE_BITS - g)).collect() };
    let micro = |norm: u128, bits: u32| norm * 1_000_000 >> bits;
    let all = 0..learner.field.material_len();
    let released_norm = line_norm(&on_line(&directions.released)).map_err(|e| e.to_string())?;
    println!(
        "FIELD_LINE_STEP lengths={} rate_bits={} entries={} norm_micro={} first_norm_micro={} moved_mv={} moved_m={} released_moved={} released_norm_micro={} log2_t={}",
        if learner.family_rates.is_some() { "family" } else { "rate" },
        learner.rate_bits,
        all.len(),
        micro(directions.step_norm, LINE_BITS),
        micro(directions.first_norm, holonics::hnn::tower::STEP_BITS),
        moved_at_one(&directions.step, all.clone()),
        moved_at_one(&directions.first, all.clone()),
        directions.released.iter().filter(|&&r| r != 0).count(),
        micro(released_norm, LINE_BITS),
        learner.field.theta[learner.field.layout().face_temper]
    );
    let square = |u: &[i128], range: std::ops::Range<usize>| -> u128 { u[range].iter().map(|v| v.unsigned_abs().saturating_mul(v.unsigned_abs())).fold(0u128, u128::saturating_add) };
    let (step_total, first_total) = (square(&directions.step, all.clone()).max(1), square(&directions.first, all.clone()).max(1));
    let names = family_names(&learner.field);
    for (k, &(start, n, grain)) in families.iter().enumerate() {
        if n == 0 {
            continue;
        }
        let name = names.get(k).map_or_else(|| format!("family{k}"), |(name, _)| name.to_string());
        let length = learner.family_rates.as_ref().map_or_else(|| "-".to_string(), |r| (r[k] * 1000 >> holonics::hnn::tower::MATERIAL_BITS).to_string());
        println!(
            "FIELD_LINE_FAMILY family={name} entries={n} grain={grain} length_millibits={length} mv_share_milli={} m_share_milli={} moved_mv={} moved_m={} released_moved={}",
            square(&directions.step, start..start + n).saturating_mul(1000) / step_total,
            square(&directions.first, start..start + n).saturating_mul(1000) / first_total,
            moved_at_one(&directions.step, start..start + n),
            moved_at_one(&directions.first, start..start + n),
            directions.released[start..start + n].iter().filter(|&&r| r != 0).count()
        );
    }
    // [measurement; agent-inferred, November 8] `FIELD_LINE_STEP_ONLY`: the step's lines alone, no held read (the moments read
    // on any host, with no card).
    if std::env::var_os("FIELD_LINE_STEP_ONLY").is_some() {
        println!("FIELD_LINE_READ points=0 places={} host_threads={} ms={}", chosen.len(), rayon::current_num_threads(), started.elapsed().as_millis());
        return Ok(());
    }
    // The `mv` step on the named families alone (theory, November 9 04:20 (a)), and its lengths.
    let restricted: Option<(Vec<i128>, Vec<u32>)> = if args.len() == 13 {
        let mut keep = vec![false; learner.field.material_len()];
        for name in args[11].split(',') {
            let k = names.iter().position(|&(n, _)| n == name).ok_or_else(|| format!("line-field: no family named {name}"))?;
            let &(start, n, _) = families.get(k).ok_or_else(|| format!("line-field: family {name} past the field's families"))?;
            if n == 0 {
                return Err(format!("line-field: family {name} has no entries").into());
            }
            keep[start..start + n].fill(true);
        }
        let etas = args[12].split(',').map(positive).map(|e| e.and_then(|e| u32::try_from(e).map_err(|_| "line-field: a length past 32 bits".into()))).collect::<Result<Vec<u32>>>()?;
        let step: Vec<i128> = directions.step.iter().zip(&keep).map(|(&u, &k)| if k { u } else { 0 }).collect();
        // Each named family's first length: the least `η` at which one of its entries moves (`|η u_i|` reaching half its grain
        // on the line), `-` for a family whose step is zero.
        for name in args[11].split(',') {
            let k = names.iter().position(|&(n, _)| n == name).ok_or_else(|| format!("line-field: no family named {name}"))?;
            let (start, n, grain) = families[k];
            let most = step[start..start + n].iter().map(|v| v.unsigned_abs()).max().unwrap_or(0);
            let half = 1u128 << (LINE_BITS - grain - 1);
            let first = if most == 0 { "-".to_string() } else { half.div_ceil(most).to_string() };
            println!("FIELD_LINE_FIRST family={name} entries={n} grain={grain} first_eta={first}");
        }
        println!(
            "FIELD_LINE_FAMILIES families={} entries={} norm_micro={} moved_at_one={} etas={}",
            args[11],
            keep.iter().filter(|&&k| k).count(),
            micro(line_norm(&step).map_err(|e| e.to_string())?, LINE_BITS),
            moved_at_one(&step, all.clone()),
            args[12]
        );
        Some((step, etas))
    } else {
        None
    };
    let mut rows = rows_file(&out.join("ENUMERATED.tsv"), "lap\tproblem\tplace\ttruth\tlog2_t\tface_masses\tface_total\tenergies\ttruth_face_masses\ttruth_face_total\n")?;
    let alphabet = learner.field.declaration.alphabet;
    let points: Vec<(&str, u32)> = match &restricted {
        Some((_, etas)) => std::iter::once(("skip", 0)).chain(etas.iter().map(|&e| ("mv_families", e))).collect(),
        None => std::iter::once(("none", 0)).chain(LINE_ETAS.iter().map(|&e| ("m", e))).chain(LINE_ETAS.iter().map(|&e| ("mv", e))).collect(),
    };
    for (marker, &(direction, eta)) in points.iter().enumerate() {
        if direction == "skip" {
            continue;
        }
        let at = std::time::Instant::now();
        // A point the field's laws refuse (a carrier passed along the line) is its own line, and the next point is read.
        let mut read_point = || -> Result<(Vec<i128>, usize, u128, i32)> {
            let (point, moved) = match direction {
                "m" => line_point(&learner.field, &directions.first, eta).map_err(|e| e.to_string())?,
                "mv" => line_point(&learner.field, &directions.step, eta).map_err(|e| e.to_string())?,
                "mv_families" => line_point(&learner.field, &restricted.as_ref().ok_or("line-field: no families")?.0, eta).map_err(|e| e.to_string())?,
                _ => (learner.field.clone(), 0),
            };
            let change: Vec<i128> = point.theta.iter().zip(&learner.field.theta).map(|(&a, &b)| a as i128 - b as i128).collect();
            let realized = line_norm(&on_line(&change)).map_err(|e| e.to_string())?;
            let (lines, energies) = enumerated_reads(&point, &chosen, realization, marker as i64, None)?;
            let codes = chosen
                .iter()
                .enumerate()
                .map(|(n, (_, truth, t, _))| conditional_code(&point, &energies[n * alphabet..(n + 1) * alphabet], truth[*t]).map(|code| code * LN2_Q30 >> 30).map_err(|e| e.to_string()))
                .collect::<std::result::Result<Vec<i128>, String>>()?;
            for line in &lines {
                row(&mut rows, line)?;
            }
            Ok((codes, moved, realized, point.theta[point.layout().face_temper]))
        };
        match read_point() {
            Ok((codes, moved, realized, log2_t)) => {
                let mut file = rows_file(&out.join(format!("LINE.{direction}.{eta}.tsv")), "problem\tplace\tcode_micro_nats\n")?;
                for ((k, _, t, q), &place) in chosen.iter().zip(&codes) {
                    row(&mut file, &format!("{k}\t{}\t{}\n", t - q, place * 1_000_000 >> 32))?;
                }
                let (nats, n) = (codes.iter().sum::<i128>(), chosen.len().max(1) as i128);
                println!(
                    "FIELD_LINE direction={direction} eta={eta} held_code_milli={} places={} ms={} held_code_micro={} moved={moved} step_micro={} log2_t={log2_t}",
                    nats * 1000 / n >> 32,
                    chosen.len(),
                    at.elapsed().as_millis(),
                    nats * 1_000_000 / n >> 32,
                    micro(realized, LINE_BITS)
                );
            }
            Err(e) => println!("FIELD_LINE direction={direction} eta={eta} refused=\"{e}\" places={} ms={}", chosen.len(), at.elapsed().as_millis()),
        }
    }
    println!("FIELD_LINE_READ points={} places={} host_threads={} ms={}", points.len(), chosen.len(), rayon::current_num_threads(), started.elapsed().as_millis());
    Ok(())
}

/// [agent-inferred, November 9] **A sum of products of two covector entries, in two limbs**: `hi·2^128 + lo`, the high limb
/// signed. Each product of two 128-bit entries (at most `2^254` in magnitude) is carried whole, and a sum past `2^255` is
/// refused, never wrapped or released.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct ProductSum {
    hi: i128,
    lo: u128,
}

impl ProductSum {
    /// `self + x·y`.
    fn add_product(&mut self, x: i128, y: i128) -> Result<()> {
        const PAST: &str = "covector-field: a sum of products past its 256-bit carrier";
        const LOW: u128 = u64::MAX as u128;
        let (a, b) = (x.unsigned_abs(), y.unsigned_abs());
        let (a1, a0, b1, b0) = (a >> 64, a & LOW, b >> 64, b & LOW);
        let (mid, mid_carry) = (a1 * b0).overflowing_add(a0 * b1);
        let (lo, lo_carry) = (a0 * b0).overflowing_add(mid << 64);
        // `a, b ≤ 2^127`, so `a·b ≤ 2^254` and its high limb is below `2^127`.
        let hi = i128::try_from(a1 * b1 + (mid >> 64) + (u128::from(mid_carry) << 64) + u128::from(lo_carry)).map_err(|_| PAST)?;
        if (x < 0) != (y < 0) {
            let (l, borrow) = self.lo.overflowing_sub(lo);
            self.hi = self.hi.checked_sub(hi).and_then(|h| h.checked_sub(i128::from(borrow))).ok_or(PAST)?;
            self.lo = l;
        } else {
            let (l, carry) = self.lo.overflowing_add(lo);
            self.hi = self.hi.checked_add(hi).and_then(|h| h.checked_add(i128::from(carry))).ok_or(PAST)?;
            self.lo = l;
        }
        Ok(())
    }

    fn big(self) -> num_bigint::BigInt {
        (num_bigint::BigInt::from(self.hi) << 128) + num_bigint::BigInt::from(self.lo)
    }
}

/// [measurement; theory, November 9 04:36 and 04:40] **One half's test of first-order stationarity in one family**, from the
/// problem sums `D_p = Σ_(i ∈ p) ⟨g_f(i), Σ_(a ∈ other) g_f(a)⟩` over the half's problems, the half's place count `n` and the
/// other half's `n_o`, in the family's covector unit squared: `S = Σ_p D_p / (n_o n)` (nearest), `SE = √((m Σ D_p² − (Σ
/// D_p)²)/(m − 1)) / (n_o n)` (floor; the SD across the half's `m` problems of their sums of `b_i`, times `√m / n`), and `z =
/// S/SE` in thousandths toward zero, read from `z² = (Σ D_p)²(m − 1)/(m Σ D_p² − (Σ D_p)²)`, a ratio of integer sums in
/// which a power of two on the family's unit cancels (its `2^(4k)` above and below), so `z` is the same bits at any grain of
/// `f`. `none` for fewer than two problems, `inf` where the problems' sums agree.
fn stationarity(sums: &[num_bigint::BigInt], n: usize, n_other: usize) -> (String, String, String) {
    use num_bigint::BigInt;
    use num_traits::{Signed, Zero};
    let m = BigInt::from(sums.len());
    let total: BigInt = sums.iter().sum();
    let squares: BigInt = sums.iter().map(|d| d * d).sum();
    let scale = BigInt::from(n) * BigInt::from(n_other);
    let s = if scale.is_zero() {
        "none".to_string()
    } else {
        let q = (total.abs() * 2u32 + &scale) / (&scale * 2u32);
        (if total.is_negative() { -q } else { q }).to_string()
    };
    if sums.len() < 2 || scale.is_zero() {
        return (s, "none".to_string(), "none".to_string());
    }
    let spread = &m * &squares - &total * &total;
    let one_less = &m - 1u32;
    let se = (&spread / (&one_less * &scale * &scale)).sqrt().to_string();
    let z = if spread.is_zero() {
        if total.is_zero() { "none".to_string() } else if total.is_negative() { "-inf".to_string() } else { "inf".to_string() }
    } else {
        let z = (&total * &total * &one_less * 1_000_000u32 / &spread).sqrt();
        (if total.is_negative() { -z } else { z }).to_string()
    };
    (s, se, z)
}

/// [measurement; theory, November 9 04:36 and 04:40] **`covector-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD
/// HELD_SHA PLACES OUT`**: whether law (D) stands where its covector is stationary in each family, or a descent in a family
/// remains that law (D) does not take. At the state's own averaged constitution `θ̄` ([`held_field`] with averaging; a state
/// that carries no average is refused), at the held places the enumerated conditional reads ([`enumerated_places`],
/// `FIELD_HELD_ALL_OF` as there), each place's covector `g(i)` is the one [`FieldLearner::section_conditional`] adds for that
/// place, read through the realization as the section reads it
/// ([`holonics::hnn::tower::field::conditional_place_covectors`]: every letter at the place with the rest at the truth, the
/// deposit's chart, sign and units; the letters' temperature's entry the face of the place's own operand where it learns, as
/// the trainer declares it: held under `FIELD_CONTRAST_ONE_RATE` or `FIELD_CONTRAST_HOLD_T`, since a state does not carry it).
///
/// [agent-inferred, November 9] **The halves are halves of the problems**: the problems in the order their first place is
/// chosen, those at even positions half A and at odd positions half B, a problem's places together. A place's covector reads
/// its whole passage, so two places of one problem are not independent; two halves of problems are.
///
/// Per family `f` (the `FIELD_LINE_FAMILY` names and order): for each place `i` in B, `b_i = ⟨g_f(i), mean_A g_f⟩`;
/// `S_ab = Σ_B b_i / n_B` with `SE_ab` the SD of B's per-problem sums of `b_i` times `√m_B / n_B` (theory, 04:40: a problem's
/// places share its passage, so their `b_i` are correlated and a spread across places reads too small), and `z_ab = S/SE`;
/// then A and B swapped. With the halves independent `E S_f = |E g_f|²`, zero where `f` is stationary, and `z` does not
/// depend on `f`'s grain ([`stationarity`]); `z > 2` in both halves is a descent in `f` that law (D) does not take. `S_ab`
/// and `S_ba` are one number, `⟨mean_A g_f, mean_B g_f⟩`: the swap changes only whose spread sets the SE. On held places
/// `E g_f` is the held code's gradient, which is law (D)'s own expectation only where held and trained places share it (a
/// training passage given as `HELD` reads law (D)'s own objective). `S`, `SE` and
/// `mean_sq` are in `f`'s covector unit squared (each entry on its family's grain, as the deposit sums it); `mean_sq_a` is the
/// mean over A's places of `‖g_f(i)‖²`, the per-place size beside the shared part `S`. The `family=all` line adds the
/// families in their grain units, so it is a null test that leans on the finest grains; the per-family lines decide.
///
/// **The carrier**: the entries are the deposit's own 128-bit integers; the halves' sums are checked at 128 bits; each
/// product of two entries and their sum over a family is carried in two limbs ([`ProductSum`], refused past `2^255`); the
/// problems' sums and the statistics are unbounded integers. No entry is released before a product, so the reading rounds
/// nothing before `S`, `SE` and `z` are formed, and a grain change of `f` multiplies every sum by its power of two with no
/// remainder.
///
/// Prints `FIELD_COVECTOR_FIELD` (which field it read), a `FIELD_COVECTOR_HALF` line a half (its problems and places), a
/// `FIELD_COVECTOR_CHUNK` line a chunk of [`holonics::hnn::tower::field::CONDITIONAL_CHUNK`] places with its elapsed
/// milliseconds, a `FIELD_COVECTOR` line a family and one for `all`, and `FIELD_COVECTOR_READ`. Writes `COVECTOR.tsv`: a
/// row a place and family, its problem and answer place, its half, `dot = ⟨g_f(i), Σ_other g_f⟩` (so `b_i = dot /
/// other_places`) and `square = ‖g_f(i)‖²`, in `f`'s unit squared; no letter. A reading only: nothing is deposited and no
/// state is written. The places' covectors stand together (`places × entries × 16` bytes, printed), the letters' materials
/// one chunk at a time.
pub(super) fn covector_field(args: &[String], realization: &mut dyn FieldRealization) -> Result<()> {
    use holonics::hnn::tower::field::{conditional_place_covectors, CONDITIONAL_CHUNK};
    use num_bigint::BigInt;
    if args.len() != 11 {
        return Err("covector-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD HELD_SHA PLACES OUT".into());
    }
    let started = std::time::Instant::now();
    let mut learner = FieldLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    declared_clocks(&mut learner.field);
    if !learner.field.declaration.energy {
        return Err("covector-field reads a field whose faces are one energy's forces".into());
    }
    if !learner.average.as_ref().is_some_and(|a| a.len() == learner.field.theta.len()) {
        return Err("covector-field reads law (D)'s averaged constitution, and this state carries no average".into());
    }
    let units = units_of(&args[5], &args[6])?;
    let codec = FieldCodec::from_text(std::str::from_utf8(&pinned_read(&args[3], &args[4], CODEC_BUDGET)?)?, units)?;
    let held_text = problems_of(&pinned_read(&args[7], &args[8], READ_BUDGET as usize)?);
    let places = positive(&args[9])?;
    let out = Path::new(&args[10]);
    std::fs::create_dir(out)?;
    let field = held_field(&learner, true);
    // A state does not carry whether the letters' temperature learns: law (D)'s covector carries it as the trainer declares it
    // (held under `FIELD_CONTRAST_ONE_RATE` or `FIELD_CONTRAST_HOLD_T`; law (D) is not against writes).
    let temper_learns = std::env::var_os("FIELD_CONTRAST_ONE_RATE").is_none() && std::env::var_os("FIELD_CONTRAST_HOLD_T").is_none();
    let temper = field.layout().face_temper;
    let material = field.material_len();
    println!(
        "FIELD_COVECTOR_FIELD field=averaged entries={material} averaged_moved={} temper_learns={} log2_t={} live_log2_t={}",
        field.theta.iter().zip(&learner.field.theta).filter(|(a, b)| a != b).count(),
        u8::from(temper_learns),
        field.theta[temper],
        learner.field.theta[temper]
    );
    let held_set = encoded_problems(&codec, &held_text, &learner.field)?;
    let void = codec.void();
    let truth_of = |p: &(Vec<usize>, Vec<usize>, usize), letters: &[usize]| -> Vec<usize> { truth_with_voids(void, p, letters) };
    let chosen = enumerated_places(&held_set, places, &truth_of);
    // The problems in the order their first place is chosen, each read once; a place is `(problem's position, site)`.
    let mut order: Vec<usize> = Vec::new();
    let mut position: HashMap<usize, usize> = HashMap::new();
    for (k, _, _, _) in &chosen {
        if !position.contains_key(k) {
            position.insert(*k, order.len());
            order.push(*k);
        }
    }
    let truths: Vec<&Vec<usize>> = order.iter().map(|k| chosen.iter().find(|c| c.0 == *k).map(|c| &c.1).ok_or("covector-field: a problem with no place")).collect::<std::result::Result<_, _>>()?;
    let resolved: Vec<Vec<bool>> = truths.iter().map(|t| vec![false; t.len()]).collect();
    let views: Vec<Region> = truths.iter().zip(&resolved).map(|(c, u)| Region { classes: c, unresolved: u, faces: &[], locked: &[], echo: &[], domain: None, port: None }).collect();
    let asked: Vec<(usize, usize)> = chosen.iter().map(|(k, _, t, _)| (position[k], *t)).collect();
    // Half B is the problems at odd positions.
    let in_b: Vec<bool> = asked.iter().map(|&(p, _)| p % 2 == 1).collect();
    let (places_b, problems_b) = (in_b.iter().filter(|&&b| b).count(), order.len() / 2);
    let (places_a, problems_a) = (asked.len() - places_b, order.len() - problems_b);
    println!("FIELD_COVECTOR_HALF half=A problems={problems_a} places={places_a} positions=even");
    println!("FIELD_COVECTOR_HALF half=B problems={problems_b} places={places_b} positions=odd");
    if places_a == 0 || places_b == 0 {
        return Err("covector-field needs two problems or more, one a half".into());
    }
    println!("FIELD_COVECTOR_MEMORY covector_bytes={} chunk_places={CONDITIONAL_CHUNK}", asked.len() * material * 16);
    let chunks = asked.len().div_ceil(CONDITIONAL_CHUNK);
    let reading = std::time::Instant::now();
    let mut realization_us = 0u128;
    let read = conditional_place_covectors(&field, temper_learns, &views, &asked, realization, &mut |c, n, read_us| {
        realization_us = read_us;
        println!("FIELD_COVECTOR_CHUNK chunk={}/{chunks} places={n}/{} realization_ms={} ms={}", c + 1, asked.len(), read_us / 1000, reading.elapsed().as_millis());
    })
    .map_err(|e| e.to_string())?;
    let read_ms = reading.elapsed().as_millis();
    // Each half's sum, entry by entry, at 128 bits.
    let (mut sum_a, mut sum_b) = (vec![0i128; material], vec![0i128; material]);
    for (r, &b) in read.iter().zip(&in_b) {
        let sum = if b { &mut sum_b } else { &mut sum_a };
        for (s, &x) in sum.iter_mut().zip(&r.covector) {
            *s = s.checked_add(x).ok_or("covector-field: a half's sum past its 128-bit carrier")?;
        }
    }
    let families = field.families_all();
    let names = family_names(&field);
    // Each place's and family's `⟨g_f(i), Σ_other g_f⟩` and `‖g_f(i)‖²`.
    let mut dots: Vec<Vec<(BigInt, BigInt)>> = Vec::with_capacity(read.len());
    for (r, &b) in read.iter().zip(&in_b) {
        let other = if b { &sum_a } else { &sum_b };
        let mut per_family = Vec::with_capacity(families.len());
        for &(start, n, _) in &families {
            let (mut dot, mut square) = (ProductSum::default(), ProductSum::default());
            for j in start..start + n {
                dot.add_product(r.covector[j], other[j])?;
                square.add_product(r.covector[j], r.covector[j])?;
            }
            per_family.push((dot.big(), square.big()));
        }
        dots.push(per_family);
    }
    let mut rows = rows_file(&out.join("COVECTOR.tsv"), "problem\tplace\thalf\tfamily\tdot\tother_places\tsquare\n")?;
    let name_of = |k: usize| names.get(k).map_or_else(|| format!("family{k}"), |(name, _)| name.to_string());
    for (i, (k, _, t, q)) in chosen.iter().enumerate() {
        let (half, other) = if in_b[i] { ("b", places_a) } else { ("a", places_b) };
        for (f, &(_, n, _)) in families.iter().enumerate() {
            if n > 0 {
                row(&mut rows, &format!("{k}\t{}\t{half}\t{}\t{}\t{other}\t{}\n", t - q, name_of(f), dots[i][f].0, dots[i][f].1))?;
            }
        }
    }
    // One half's problem sums of `pick`'s dot, and its mean square, over its places.
    let half_read = |b: bool, pick: &dyn Fn(usize) -> (BigInt, BigInt)| -> (Vec<BigInt>, BigInt) {
        let mut sums = vec![BigInt::from(0); order.len()];
        let mut square = BigInt::from(0);
        for (i, &(p, _)) in asked.iter().enumerate().filter(|&(i, _)| in_b[i] == b) {
            let (d, s) = pick(i);
            sums[p] += d;
            square += s;
        }
        let sums: Vec<BigInt> = sums.into_iter().enumerate().filter(|&(p, _)| (p % 2 == 1) == b).map(|(_, s)| s).collect();
        let n = BigInt::from(if b { places_b } else { places_a });
        (sums, (square * 2u32 + &n) / (&n * 2u32))
    };
    let line = |family: &str, entries: usize, grain: &str, pick: &dyn Fn(usize) -> (BigInt, BigInt)| {
        let (sums_b, mean_sq_b) = half_read(true, pick);
        let (sums_a, mean_sq_a) = half_read(false, pick);
        let (s_ab, se_ab, z_ab) = stationarity(&sums_b, places_b, places_a);
        let (s_ba, se_ba, z_ba) = stationarity(&sums_a, places_a, places_b);
        println!(
            "FIELD_COVECTOR family={family} entries={entries} grain={grain} places_b={places_b} problems_b={problems_b} s_ab={s_ab} se_ab={se_ab} z_ab_milli={z_ab} places_a={places_a} problems_a={problems_a} s_ba={s_ba} se_ba={se_ba} z_ba_milli={z_ba} mean_sq_a={mean_sq_a} mean_sq_b={mean_sq_b}"
        );
    };
    for (f, &(_, n, grain)) in families.iter().enumerate() {
        if n > 0 {
            line(&name_of(f), n, &grain.to_string(), &|i| dots[i][f].clone());
        }
    }
    line("all", material, "-", &|i| dots[i].iter().fold((BigInt::from(0), BigInt::from(0)), |(d, s), (x, y)| (d + x, s + y)));
    println!(
        "FIELD_COVECTOR_READ places={} problems={} families={} entries={material} averaged=1 read_ms={read_ms} realization_ms={} host_threads={} ms={}",
        asked.len(),
        order.len(),
        families.iter().filter(|f| f.1 > 0).count(),
        realization_us / 1000,
        rayon::current_num_threads(),
        started.elapsed().as_millis()
    );
    Ok(())
}

/// [measurement; theory, November 9 05:31] The `z` at the larger SE: both halves share one `S`, so the larger SE is the `z` of
/// smaller magnitude (`none` where either is unread).
fn z_at_larger_se(a: &str, b: &str) -> String {
    // An unbounded `z` (its SE zero) stands above every bounded one.
    let size = |z: &str| -> Option<(bool, num_bigint::BigUint)> {
        match z {
            "inf" | "-inf" => Some((true, num_bigint::BigUint::default())),
            v => v.parse::<num_bigint::BigInt>().ok().map(|x| (false, x.magnitude().clone())),
        }
    };
    match (size(a), size(b)) {
        (Some(x), Some(y)) => if x <= y { a } else { b }.to_string(),
        _ => "none".to_string(),
    }
}

/// [agent-inferred, November 9] The fresh writes' problems a batch: the fork's section (fork3b's sixteen), so its measured
/// sweep rates project a batch.
const CONTRAST_BATCH: usize = 16;

/// [measurement; theory, November 9 05:31] **`contrast-covector-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA PROBLEMS
/// PROBLEMS_SHA COUNT SWEEPS OUT`**: whether the fresh-writes contrast law (fork3b's: `FIELD_CONTRAST_FRESH=SWEEPS`,
/// `FIELD_FRESH_FROM_TRUTH`) stands where its covector is stationary in each family, at the state's live `θ` (the law deposits
/// at `θ`, so this is its own point; the averaged constitution is not read).
///
/// [agent-inferred, November 9] **The problems**: of the `N` problems the codec encodes from `PROBLEMS` (in the file's
/// order), the `COUNT` at `⌊(2c + 1)N / (2·COUNT)⌋` for `c = 0..COUNT`, the middles of `COUNT` equal parts of the file:
/// deterministic, spread across it, each whole (its answer cut to the room, as the trainer reads it). Their indices are
/// printed, never their letters.
///
/// **The writes** are the trainer's fresh writes from the truth: each answer's write starts at its truth at its true length
/// and is swept whole `SWEEPS` times at the field's `T` ([`fresh_sweeps_at`], keyed as the trainer keys a section's,
/// [`writes_key`] with the seed [`contrast_seed`] and the lap count the state carries). [agent-inferred] The problems are
/// swept [`CONTRAST_BATCH`] at a time, in order of answer length, batch `b` keyed as section `b` would be: a write's chain is
/// its own (its coins keyed by its place in the batch), so a batch shares only its walk, set by its longest answer.
///
/// **Each problem's covector** `g(p) = (1/T)(∂G/∂θ(truth_p) − ∂G/∂θ(write_p))` is the pair's term of the covector
/// [`FieldLearner::section_contrast`] deposits ([`holonics::hnn::tower::field::contrast_pair_covectors`], the deposit's chart,
/// sign and units, released pair by pair where the section releases the sum once; `T` held, as the law holds it).
///
/// **The test** (as `covector-field`'s, with a problem the unit): the problems at even positions of the chosen order are half
/// A and at odd positions half B; per family `f`, for each problem `p` in B, `b_p = ⟨g_f(p), mean_A g_f⟩`, `S_ab = Σ_B b_p /
/// m_B`, `SE_ab = SD_B(b_p)/√m_B` ([`stationarity`]), `z_ab = S/SE`; then A and B swapped. `S_ab` and `S_ba` are one
/// estimate, so the bar is `z > 2` at the larger SE (`z_bar_milli`). `S`, `SE` and `mean_sq` are in `f`'s covector unit squared;
/// the carrier is `covector-field`'s ([`ProductSum`], unbounded statistics), so `z` is the same bits at any grain of `f`. The
/// `family=all` line adds the families in their grain units: a null test that leans on the finest grains.
///
/// Prints `FIELD_CONTRAST_COVECTOR_CHOICE` (the rule and the indices), `FIELD_CONTRAST_COVECTOR_FIELD` (which field it read),
/// a `FIELD_CONTRAST_COVECTOR_HALF` line a half, a `FIELD_CONTRAST_COVECTOR_SWEEP` line a batch's sweep and a
/// `FIELD_CONTRAST_COVECTOR_BATCH` line a batch (its answers' places and longest, its sweep and covector milliseconds, its
/// writes' share at their truth letters), a `FIELD_CONTRAST_COVECTOR` line a family and one for `all`, and
/// `FIELD_CONTRAST_COVECTOR_READ`. Writes `CONTRAST_COVECTOR.tsv`: a row a problem and family, its index, position, half, batch
/// and answer length, `dot = ⟨g_f(p), Σ_other g_f⟩` (so `b_p = dot / other_problems`) and `square = ‖g_f(p)‖²`; no letter.
/// A reading only: nothing is deposited, no state is written and no write is kept.
pub(super) fn contrast_covector_field(args: &[String], realization: &mut dyn FieldRealization) -> Result<()> {
    use holonics::hnn::tower::field::contrast_pair_covectors;
    use num_bigint::BigInt;
    if args.len() != 12 {
        return Err("contrast-covector-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA PROBLEMS PROBLEMS_SHA COUNT SWEEPS OUT".into());
    }
    let started = std::time::Instant::now();
    let mut learner = FieldLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    declared_clocks(&mut learner.field);
    if !learner.field.declaration.energy || learner.field.scale.is_some() {
        return Err("contrast-covector-field reads a field whose faces are one energy's forces".into());
    }
    let units = units_of(&args[5], &args[6])?;
    let codec = FieldCodec::from_text(std::str::from_utf8(&pinned_read(&args[3], &args[4], CODEC_BUDGET)?)?, units)?;
    let text = problems_of(&pinned_read(&args[7], &args[8], READ_BUDGET as usize)?);
    let (wanted, sweeps) = (positive(&args[9])?, positive(&args[10])? as u64);
    let out = Path::new(&args[11]);
    let seed = contrast_seed(&learner, &args[2])?;
    let field = &learner.field;
    let set = encoded_problems(&codec, &text, field)?;
    if wanted < 2 || wanted > set.len() {
        return Err(format!("contrast-covector-field: COUNT {wanted} of {} problems (two or more, at most all)", set.len()).into());
    }
    std::fs::create_dir(out)?;
    let chosen: Vec<usize> = (0..wanted).map(|c| (2 * c + 1) * set.len() / (2 * wanted)).collect();
    println!(
        "FIELD_CONTRAST_COVECTOR_CHOICE problems={} count={wanted} rule=middles_of_equal_parts indices={}",
        set.len(),
        chosen.iter().map(usize::to_string).collect::<Vec<_>>().join(",")
    );
    let read = learner.laps;
    println!(
        "FIELD_CONTRAST_COVECTOR_FIELD field=live entries={} log2_t={} laps={read} seed={seed:016x} sweeps={sweeps} average_carried={} temper=held",
        field.material_len(),
        field.theta[field.layout().face_temper],
        u8::from(learner.average.is_some())
    );
    let in_b: Vec<bool> = (0..wanted).map(|c| c % 2 == 1).collect();
    let problems_b = in_b.iter().filter(|&&b| b).count();
    let problems_a = wanted - problems_b;
    println!("FIELD_CONTRAST_COVECTOR_HALF half=A problems={problems_a} positions=even");
    println!("FIELD_CONTRAST_COVECTOR_HALF half=B problems={problems_b} positions=odd");
    // The batches: the chosen positions in order of answer length (then position), sixteen at a time.
    let mut by_length: Vec<usize> = (0..wanted).collect();
    by_length.sort_by_key(|&c| (set[chosen[c]].1.len(), c));
    let batches: Vec<&[usize]> = by_length.chunks(CONTRAST_BATCH).collect();
    let void = codec.void();
    let mut covectors: Vec<Option<Vec<i128>>> = vec![None; wanted];
    let mut batch_of = vec![0usize; wanted];
    let (mut sweep_ms, mut covector_ms) = (0u128, 0u128);
    for (b, members) in batches.iter().enumerate() {
        let problems: Vec<(&[usize], usize)> = members.iter().map(|&c| (set[chosen[c]].0.as_slice(), set[chosen[c]].2)).collect();
        let mut active: Vec<Vec<usize>> = members.iter().map(|&c| set[chosen[c]].1.clone()).collect();
        let places: usize = active.iter().map(Vec::len).sum();
        let longest = active.iter().map(Vec::len).max().unwrap_or(0);
        let key = writes_key(seed, read, b);
        let at = std::time::Instant::now();
        fresh_sweeps_at(field, &problems, &mut active, 0, sweeps, key, void, realization, &mut |_, _| Ok(()), &mut |sweep, mv, pr, en, _, ms| {
            println!(
                "FIELD_CONTRAST_COVECTOR_SWEEP batch={}/{} sweep={sweep} moved={mv} proposed={pr} write_energy_milli={} ms={ms} elapsed_ms={}",
                b + 1,
                batches.len(),
                (en.iter().sum::<i128>() / members.len().max(1) as i128) * 1000 >> 32,
                started.elapsed().as_millis()
            );
        })?;
        let swept = at.elapsed().as_millis();
        let agree: usize = active.iter().zip(members.iter()).map(|(w, &c)| w.iter().zip(&set[chosen[c]].1).filter(|(x, y)| x == y).count()).sum();
        let truths: Vec<Vec<usize>> = members.iter().map(|&c| truth_with_voids(void, &set[chosen[c]], &set[chosen[c]].1)).collect();
        let writes: Vec<Vec<usize>> = members.iter().zip(&active).map(|(&c, w)| truth_with_voids(void, &set[chosen[c]], w)).collect();
        let resolved: Vec<Vec<bool>> = truths.iter().map(|t| vec![false; t.len()]).collect();
        let truth_views: Vec<Region> = truths.iter().zip(&resolved).map(|(c, u)| Region { classes: c, unresolved: u, faces: &[], locked: &[], echo: &[], domain: None, port: None }).collect();
        let write_views: Vec<Region> = writes.iter().zip(&resolved).map(|(c, u)| Region { classes: c, unresolved: u, faces: &[], locked: &[], echo: &[], domain: None, port: None }).collect();
        let at = std::time::Instant::now();
        let pairs = contrast_pair_covectors(field, &truth_views, &write_views, realization).map_err(|e| e.to_string())?;
        let formed = at.elapsed().as_millis();
        for (&c, pair) in members.iter().zip(pairs) {
            covectors[c] = Some(pair.covector);
            batch_of[c] = b;
        }
        (sweep_ms, covector_ms) = (sweep_ms + swept, covector_ms + formed);
        println!(
            "FIELD_CONTRAST_COVECTOR_BATCH batch={}/{} problems={} places={places} longest={longest} sweep_ms={swept} covector_ms={formed} retention_milli={} ms={}",
            b + 1,
            batches.len(),
            members.len(),
            agree * 1000 / places.max(1),
            started.elapsed().as_millis()
        );
    }
    let covectors: Vec<Vec<i128>> = covectors.into_iter().map(|g| g.ok_or("contrast-covector-field: a problem with no covector")).collect::<std::result::Result<_, _>>()?;
    let material = field.material_len();
    let (mut sum_a, mut sum_b) = (vec![0i128; material], vec![0i128; material]);
    for (g, &b) in covectors.iter().zip(&in_b) {
        let sum = if b { &mut sum_b } else { &mut sum_a };
        for (s, &x) in sum.iter_mut().zip(g) {
            *s = s.checked_add(x).ok_or("contrast-covector-field: a half's sum past its 128-bit carrier")?;
        }
    }
    let families = field.families_all();
    let names = family_names(field);
    let name_of = |k: usize| names.get(k).map_or_else(|| format!("family{k}"), |(name, _)| name.to_string());
    // Each problem's and family's `⟨g_f(p), Σ_other g_f⟩` and `‖g_f(p)‖²`.
    let mut dots: Vec<Vec<(BigInt, BigInt)>> = Vec::with_capacity(wanted);
    for (g, &b) in covectors.iter().zip(&in_b) {
        let other = if b { &sum_a } else { &sum_b };
        let mut per_family = Vec::with_capacity(families.len());
        for &(start, n, _) in &families {
            let (mut dot, mut square) = (ProductSum::default(), ProductSum::default());
            for j in start..start + n {
                dot.add_product(g[j], other[j])?;
                square.add_product(g[j], g[j])?;
            }
            per_family.push((dot.big(), square.big()));
        }
        dots.push(per_family);
    }
    let mut rows = rows_file(&out.join("CONTRAST_COVECTOR.tsv"), "problem\tposition\thalf\tbatch\tanswer_length\tfamily\tdot\tother_problems\tsquare\n")?;
    for c in 0..wanted {
        let (half, other) = if in_b[c] { ("b", problems_a) } else { ("a", problems_b) };
        for (f, &(_, n, _)) in families.iter().enumerate() {
            if n > 0 {
                row(&mut rows, &format!("{}\t{c}\t{half}\t{}\t{}\t{}\t{}\t{other}\t{}\n", chosen[c], batch_of[c], set[chosen[c]].1.len(), name_of(f), dots[c][f].0, dots[c][f].1))?;
            }
        }
    }
    // One half's problems' dots of `pick`, and its mean square.
    let half_read = |b: bool, pick: &dyn Fn(usize) -> (BigInt, BigInt)| -> (Vec<BigInt>, BigInt) {
        let mut sums = Vec::new();
        let mut square = BigInt::from(0);
        for c in (0..wanted).filter(|&c| in_b[c] == b) {
            let (d, s) = pick(c);
            sums.push(d);
            square += s;
        }
        let m = BigInt::from(sums.len().max(1));
        (sums, (square * 2u32 + &m) / (&m * 2u32))
    };
    let line = |family: &str, entries: usize, grain: &str, pick: &dyn Fn(usize) -> (BigInt, BigInt)| {
        let (sums_b, mean_sq_b) = half_read(true, pick);
        let (sums_a, mean_sq_a) = half_read(false, pick);
        let (s_ab, se_ab, z_ab) = stationarity(&sums_b, problems_b, problems_a);
        let (s_ba, se_ba, z_ba) = stationarity(&sums_a, problems_a, problems_b);
        let z_bar = z_at_larger_se(&z_ab, &z_ba);
        println!(
            "FIELD_CONTRAST_COVECTOR family={family} entries={entries} grain={grain} problems_b={problems_b} s_ab={s_ab} se_ab={se_ab} z_ab_milli={z_ab} problems_a={problems_a} s_ba={s_ba} se_ba={se_ba} z_ba_milli={z_ba} z_bar_milli={z_bar} mean_sq_a={mean_sq_a} mean_sq_b={mean_sq_b}"
        );
    };
    for (f, &(_, n, grain)) in families.iter().enumerate() {
        if n > 0 {
            line(&name_of(f), n, &grain.to_string(), &|c| dots[c][f].clone());
        }
    }
    line("all", material, "-", &|c| dots[c].iter().fold((BigInt::from(0), BigInt::from(0)), |(d, s), (x, y)| (d + x, s + y)));
    println!(
        "FIELD_CONTRAST_COVECTOR_READ problems={wanted} batches={} sweeps={sweeps} families={} entries={material} sweep_ms={sweep_ms} covector_ms={covector_ms} host_threads={} ms={}",
        batches.len(),
        families.iter().filter(|f| f.1 > 0).count(),
        rayon::current_num_threads(),
        started.elapsed().as_millis()
    );
    Ok(())
}

/// The nearest-rank quartiles `(q25, median, q75)` of `values` (each the `⌈p n⌉`-th smallest), none for no values.
fn rank_quartiles<T: Ord + Copy>(mut values: Vec<T>) -> Option<(T, T, T)> {
    if values.is_empty() {
        return None;
    }
    values.sort_unstable();
    let n = values.len();
    let at = |quarters: usize| values[(quarters * n).div_ceil(4) - 1];
    Some((at(1), at(2), at(3)))
}

/// [`enumerated_read`]'s rows at `chosen` (each line `lap`-marked), read through `realization`.
fn enumerated_rows(field: &Field, chosen: &HeldPlaces, realization: &mut dyn FieldRealization, lap: i64) -> Result<Vec<String>> {
    Ok(enumerated_reads(field, chosen, realization, lap, None)?.0)
}

/// [`enumerated_rows`]'s rows beside the energies they carry: `alphabet` a place, its letters in order, the places in
/// `chosen`'s order. [measurement; theory, November 9 08:13, the held-under reading] With `under`, each configuration's `G` is
/// read at `field`'s `θ` under the base's discrete maps ([`FieldRealization::read_energies_under`]); the faces are `field`'s own.
fn enumerated_reads(field: &Field, chosen: &HeldPlaces, realization: &mut dyn FieldRealization, lap: i64, under: Option<(&Field, holonics::hnn::tower::field::BaseHold)>) -> Result<(Vec<String>, Vec<i128>)> {
    let alphabet = field.declaration.alphabet;
    let chosen: Vec<(usize, &Vec<usize>, usize, usize)> = chosen.iter().map(|(k, truth, t, q)| (*k, truth, *t, *q)).collect();
    if chosen.is_empty() {
        return Ok((Vec::new(), Vec::new()));
    }
    let opens: Vec<Vec<bool>> = chosen.iter().map(|(_, truth, t, _)| (0..truth.len()).map(|s| s == *t).collect()).collect();
    let views: Vec<Region> = chosen.iter().zip(&opens).map(|((_, truth, _, _), open)| Region { classes: truth, unresolved: open, faces: &[], locked: &[], echo: &[], domain: None, port: None }).collect();
    let faces = realization.read_faces(field, &views).map_err(|e| e.to_string())?;
    // [measurement; the unified-theory reading of November 7, 08:25] The face at the truth beside the open face: the place
    // carrying its truth letter whole (as a kernel block opens it), whose slope keeps the place's own curvature.
    let carried: Vec<Vec<Option<Shares>>> = chosen.iter().map(|(_, truth, t, _)| (0..truth.len()).map(|s| (s == *t).then(|| vec![(truth[s] as u32, 1u32 << 16)])).collect()).collect();
    let truth_views: Vec<Region> = chosen.iter().zip(&opens).zip(&carried).map(|(((_, truth, _, _), open), c)| Region { classes: truth, unresolved: open, faces: c, locked: open, echo: &[], domain: None, port: None }).collect();
    let truth_faces = realization.read_faces(field, &truth_views).map_err(|e| e.to_string())?;
    let configurations: Vec<Vec<usize>> = chosen
        .iter()
        .flat_map(|(_, truth, t, _)| {
            (0..alphabet).map(move |c| {
                let mut x = truth.to_vec();
                x[*t] = c;
                x
            })
        })
        .collect();
    let asked: Vec<&[usize]> = configurations.iter().map(Vec::as_slice).collect();
    let energies = match under {
        None => realization.read_energies(field, &asked),
        Some((base, hold)) => realization.read_energies_under(field, base, &asked, hold),
    }
    .map_err(|e| e.to_string())?;
    let log2_t = field.theta[field.layout().face_temper];
    let mut lines = Vec::with_capacity(chosen.len());
    for (n, (k, truth, t, q)) in chosen.iter().enumerate() {
        let face = faces[n][*t].as_ref().ok_or("an enumerated read's open place with no face")?;
        let masses: Vec<String> = face.masses.iter().map(u128::to_string).collect();
        let at_truth = truth_faces[n][*t].as_ref().ok_or("an enumerated read's carried place with no face")?;
        let truth_masses: Vec<String> = at_truth.masses.iter().map(u128::to_string).collect();
        let g: Vec<String> = energies[n * alphabet..(n + 1) * alphabet].iter().map(i128::to_string).collect();
        lines.push(format!("{lap}\t{k}\t{}\t{}\t{log2_t}\t{}\t{}\t{}\t{}\t{}\n", t - q, truth[*t], masses.join(","), face.total, g.join(","), truth_masses.join(","), at_truth.total));
    }
    Ok((lines, energies))
}

/// [definition; theory, November 7 22:41, from Brandon's 22:29 lens: the host is a surface too] **The held reader on the host's
/// lanes**: readings never deposit, so the held reads at every crossing run on the host (the field's own realization,
/// [`holonics::hnn::tower::field::HostField`]) on a thread of their own while the card keeps learning. Each request is the
/// field at a crossing, the live `θ` and the averaged `θ̄`, read in order; their rows go to `HELD_LIVE.tsv` and
/// `HELD_AVERAGE.tsv`, marked as the card's held rows are, with a `FIELD_HOST_HELD` line a read.
struct HostHeld {
    send: Option<std::sync::mpsc::Sender<(i64, &'static str, Field)>>,
    worker: Option<std::thread::JoinHandle<()>>,
}

impl HostHeld {
    fn start(chosen: HeldPlaces, out: &std::path::Path, header: &'static str) -> Result<Self> {
        let (send, receive) = std::sync::mpsc::channel::<(i64, &'static str, Field)>();
        let mut live = rows_file(&out.join("HELD_LIVE.tsv"), header)?;
        let mut average = rows_file(&out.join("HELD_AVERAGE.tsv"), header)?;
        let started = std::time::Instant::now();
        let worker = std::thread::spawn(move || {
            for (marker, kind, field) in receive {
                let t = std::time::Instant::now();
                match enumerated_rows(&field, &chosen, &mut holonics::hnn::tower::field::HostField, marker) {
                    Ok(lines) => {
                        let file = if kind == "average" { &mut average } else { &mut live };
                        let written = lines.iter().try_for_each(|l| row(file, l));
                        println!("FIELD_HOST_HELD marker={marker} kind={kind} places={} ms={} at_ms={} ok={}", lines.len(), t.elapsed().as_millis(), started.elapsed().as_millis(), written.is_ok());
                    }
                    Err(e) => println!("FIELD_HOST_HELD marker={marker} kind={kind} error={e}"),
                }
            }
        });
        Ok(Self { send: Some(send), worker: Some(worker) })
    }
    fn read(&self, marker: i64, learner: &FieldLearner) {
        if let Some(send) = &self.send {
            let _ = send.send((marker, "live", learner.field.clone()));
            let _ = send.send((marker, "average", learner.averaged_field()));
        }
    }
    fn finish(&mut self) {
        self.send.take();
        if let Some(w) = self.worker.take() {
            let _ = w.join();
        }
    }
}

impl Drop for HostHeld {
    /// Every requested read completes before the run returns.
    fn drop(&mut self) {
        self.finish();
    }
}

/// The enumerated read's key space, apart from every other draw of the run.
const ENUMERATED_KEY: u64 = 0xE7AC_7 << 40;

/// [definition; the unified-theory reading of November 7, 09:02] **`kernel-write STATE STATE_SHA CODEC CODEC_SHA UNITS
/// UNITS_SHA HELD HELD_SHA COUNT MAX_SWEEPS STOP_MS OUT`**: the energy's own kernel writes the first `COUNT` held answers at
/// their true lengths beside their questions (the questions' places never move). It starts from the joint release
/// ([`holonics::hnn::tower::field::Field::energy_release`]), then sweeps
/// ([`holonics::hnn::tower::field::Field::energy_sweep`]) at the energy's own `T` until the first doubling of sweeps whose
/// second half's mean energy per place lies within one standard error of its first half's, then descends, halving `T` each
/// sweep, until a sweep moves nothing. It prints each sweep's acceptance and energy per place, writes the answers' text at
/// sweeps 1, 2, 4, 8, … and at both stops to `WRITES.txt` (private), and closes with each write's energy per place beside its
/// true answer's.
pub(super) fn kernel_write(args: &[String], realization: &mut dyn FieldRealization) -> Result<()> {
    if args.len() != 13 {
        return Err("kernel-write STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD HELD_SHA COUNT MAX_SWEEPS STOP_MS OUT".into());
    }
    let started = std::time::Instant::now();
    let mut learner = FieldLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    declared_clocks(&mut learner.field);
    let field = &learner.field;
    if !field.declaration.energy {
        return Err("kernel-write writes with a field whose faces are one energy's forces".into());
    }
    let units = units_of(&args[5], &args[6])?;
    let codec = FieldCodec::from_text(std::str::from_utf8(&pinned_read(&args[3], &args[4], CODEC_BUDGET)?)?, units)?;
    let held = problems_of(&pinned_read(&args[7], &args[8], READ_BUDGET as usize)?);
    let (count, max_sweeps, stop_ms) = (positive(&args[9])?, positive(&args[10])?, positive(&args[11])? as u128);
    let out = Path::new(&args[12]);
    std::fs::create_dir(out)?;
    let void = codec.void();
    let seed = u64::from_str_radix(args[2].get(..16).ok_or("a state's hash of fewer than sixteen hex digits")?, 16).map_err(|_| "a state's hash that is not hexadecimal")?;
    let mut prompts: Vec<(Vec<usize>, usize)> = Vec::new();
    let mut truths: Vec<Vec<usize>> = Vec::new();
    for (question, answer) in &held {
        if prompts.len() == count {
            break;
        }
        let (q, room) = opening(&codec, field, question, b"")?;
        let mut a = codec.encode(answer)?;
        a.truncate(room);
        if a.is_empty() {
            continue;
        }
        prompts.push((q, room));
        truths.push(a);
    }
    let problems: Vec<(&[usize], usize)> = prompts.iter().map(|(q, r)| (q.as_slice(), *r)).collect();
    let lengths: Vec<usize> = truths.iter().map(Vec::len).collect();
    let mut writes = std::fs::OpenOptions::new().write(true).create_new(true).open(out.join("WRITES.txt"))?;
    let mut dump = |label: &str, answers: &[Vec<usize>]| -> Result<()> {
        use std::io::Write;
        for (k, a) in answers.iter().enumerate() {
            writeln!(writes, "=== {label} answer {k} ===")?;
            writes.write_all(&codec.decode(a))?;
            writeln!(writes)?;
        }
        Ok(())
    };
    // The true answers' energies (each configuration relaxed at its own halvings), on 2^(−32) bits.
    let configurations: Vec<Vec<usize>> = problems.iter().zip(&truths).map(|(&(q, room), a)| {
        let mut c: Vec<usize> = q.iter().chain(a).copied().collect();
        c.extend(std::iter::repeat_n(void, holonics::hnn::tower::field::NEAR.min(room - a.len())));
        c
    }).collect();
    let asked: Vec<&[usize]> = configurations.iter().map(Vec::as_slice).collect();
    let truth_g = realization.read_energies(field, &asked).map_err(|e| e.to_string())?;
    println!("FIELD_WRITE answers={} lengths={:?} log2_t={} ms={}", problems.len(), lengths, field.theta[field.layout().face_temper], started.elapsed().as_millis());
    // [measurement; theory, November 7 23:34] `FIELD_WRITE_LEADING`: first the writer started at the truths themselves, 8
    // sweeps at `T` dumped at 1, 2, 4 and 8 ("from the truth, sweep k"): how long the field's equilibrium keeps the truth's order.
    if std::env::var_os("FIELD_WRITE_LEADING").is_some() {
        let mut held_answers = truths.clone();
        for sweep in 1..=8usize {
            let (moved, proposed, _) = field.energy_sweep(&problems, &mut held_answers, void, 0, mix(seed ^ 0x7E57, sweep as u64), realization, &mut |_, _| {}).map_err(|e| e.to_string())?;
            println!("FIELD_WRITE_LEADING sweep={sweep} moved={moved} proposed={proposed} ms={}", started.elapsed().as_millis());
            if sweep.is_power_of_two() {
                dump(&format!("from the truth, sweep {sweep}"), &held_answers)?;
            }
        }
        if std::env::var("FIELD_WRITE_LEADING").as_deref() == Ok("only") {
            println!("FIELD_WRITE_DONE leading ms={}", started.elapsed().as_millis());
            return Ok(());
        }
    }
    // The joint release to start from.
    let mut answers = field.energy_release(&problems, &lengths, void, 64, seed, realization, &mut |_, _, _| {}).map_err(|e| e.to_string())?;
    dump("release", &answers)?;
    println!("FIELD_WRITE_RELEASE ms={}", started.elapsed().as_millis());
    let mean_of = |v: &[i128]| -> i128 { v.iter().sum::<i128>() / v.len().max(1) as i128 };
    let milli = |nats_q32: i128| -> i128 { nats_q32 * 1000 >> 32 };
    let mut energies: Vec<i128> = Vec::new();
    let mut stop = None;
    for sweep in 1..=max_sweeps {
        let t0 = std::time::Instant::now();
        let (moved, proposed, per) = field.energy_sweep(&problems, &mut answers, void, 0, mix(seed, sweep as u64), realization, &mut |_, _| {}).map_err(|e| e.to_string())?;
        let e = mean_of(&per);
        energies.push(e);
        println!("FIELD_WRITE_SWEEP sweep={sweep} cool=0 moved={moved} proposed={proposed} accept_milli={} energy_milli={} per_answer_milli={:?} sweep_ms={} ms={}", moved * 1000 / proposed.max(1), milli(e), per.iter().map(|&x| milli(x)).collect::<Vec<_>>(), t0.elapsed().as_millis(), started.elapsed().as_millis());
        if sweep.is_power_of_two() {
            dump(&format!("sweep {sweep}"), &answers)?;
            if sweep >= 2 {
                let (a, b) = energies.split_at(sweep / 2);
                let (ma, mb) = (mean_of(a), mean_of(b));
                let var = |v: &[i128], m: i128| -> i128 { if v.len() < 2 { 0 } else { v.iter().map(|&x| ((x - m) >> 16) * ((x - m) >> 16)).sum::<i128>() / (v.len() as i128 - 1) } };
                let se2 = var(a, ma) / a.len() as i128 + var(b, mb) / b.len() as i128;
                let se = ((se2.max(0) as u128).isqrt() as i128) << 16;
                println!("FIELD_WRITE_HALVES sweep={sweep} first_milli={} second_milli={} se_milli={}", milli(ma), milli(mb), milli(se));
                if (mb - ma).abs() <= se {
                    stop = Some(sweep);
                    break;
                }
            }
        }
        if started.elapsed().as_millis() > stop_ms {
            println!("FIELD_WRITE_STOPPED sweep={sweep} reason=time ms={}", started.elapsed().as_millis());
            break;
        }
    }
    dump(&format!("equilibrium at sweep {}", stop.map_or("-".to_string(), |s| s.to_string())), &answers)?;
    println!("FIELD_WRITE_EQUILIBRIUM sweep={} ms={}", stop.map_or("-".to_string(), |s| s.to_string()), started.elapsed().as_millis());
    // The closing read (theory, November 7 16:56: at `T` and after the descent): each write's energy a place beside its true
    // answer's, both read at the field's own `T`, in nats.
    let closing = |at: &str, answers: &[Vec<usize>], realization: &mut dyn FieldRealization| -> Result<()> {
        let configurations: Vec<Vec<usize>> = problems.iter().zip(answers).map(|(&(q, room), a)| {
            let mut c: Vec<usize> = q.iter().chain(a).copied().collect();
            c.extend(std::iter::repeat_n(void, holonics::hnn::tower::field::NEAR.min(room - a.len())));
            c
        }).collect();
        let asked: Vec<&[usize]> = configurations.iter().map(Vec::as_slice).collect();
        let write_g = realization.read_energies(field, &asked).map_err(|e| e.to_string())?;
        let log2_t = field.theta[field.layout().face_temper] as i128;
        // `1/T = 2^(−log₂ T)` on 2^(−32); `(G/T) ln 2 / len`, the energy a place in nats, as the sweeps read it.
        let inverse = exp2_q32(-(log2_t << 8));
        // `G/T` on 2^(−32) bits (`G` on 2^(−32), `1/T` on 2^(−32)), then nats, then a place's share.
        let nats = |g: i128| -> i128 { (g * inverse >> 32) * LN2_Q30 >> 30 };
        for k in 0..problems.len() {
            let (w, t) = (nats(write_g[k]) / lengths[k] as i128, nats(truth_g[k]) / lengths[k] as i128);
            println!("FIELD_WRITE_ENERGY at={at} answer={k} length={} write_nats_a_place_milli={} truth_nats_a_place_milli={} write_less_truth_milli={}", lengths[k], milli(w), milli(t), milli(w - t));
        }
        Ok(())
    };
    closing("T", &answers, realization)?;
    // [measurement; theory, November 8 12:35] `FIELD_WRITE_HEAT=SWEEPS`: the heating from the equilibrium at T, t = T/T′ stepped
    // in quarter octaves down to 1/4 and then in octaves down to 2^(−10), SWEEPS sweeps a step, each sweep's energy a place
    // read at its own T′ (the analysis rescales to T: u = e·T′/T), and the uniform letters' energy at T for t = 0, so the
    // field's entropy a place is S(T) = ln 99 + u(1) − ∫₀¹ u dt. Run on a copy: the descent below starts from the equilibrium.
    if let Some(heat) = std::env::var("FIELD_WRITE_HEAT").ok().and_then(|v| v.parse::<u32>().ok()).filter(|&k| k > 0) {
        let mut hot = answers.clone();
        let quarter = 1i128 << (holonics::hnn::tower::MATERIAL_BITS - 2);
        let steps: Vec<i128> = (1..=8).map(|j| j * quarter).chain((3..=10).map(|q| q << holonics::hnn::tower::MATERIAL_BITS)).collect();
        for (k, &shift) in steps.iter().enumerate() {
            for sweep in 1..=heat {
                let t0 = std::time::Instant::now();
                let (moved, proposed, per) = field.energy_sweep_shifted(&problems, &mut hot, None, void, shift, mix(seed ^ 0x4EA7, ((k as u64) << 8) | sweep as u64), realization, &mut |_, _| {}).map_err(|e| e.to_string())?;
                println!("FIELD_WRITE_HEAT step={} shift_quarters={} sweep={sweep} moved={moved} proposed={proposed} energy_milli={} per_answer_milli={:?} sweep_ms={} ms={}", k + 1, shift / quarter, milli(mean_of(&per)), per.iter().map(|&x| milli(x)).collect::<Vec<_>>(), t0.elapsed().as_millis(), started.elapsed().as_millis());
            }
        }
        // t = 0: each answer's letters drawn uniformly over the alphabet less the void, four draws, read at T.
        for draw in 0..4u64 {
            let uniform: Vec<Vec<usize>> = answers.iter().enumerate().map(|(k, a)| {
                (0..a.len()).map(|j| {
                    let r = (mix(seed ^ 0x0F1A7, (draw << 40) | ((k as u64) << 20) | j as u64) % (field.declaration.alphabet as u64 - 1)) as usize;
                    if r >= void { r + 1 } else { r }
                }).collect()
            }).collect();
            closing(&format!("uniform{draw}"), &uniform, realization)?;
        }
    }
    // The descent: T halved each sweep until a sweep moves nothing.
    let mut cool = 0u32;
    while started.elapsed().as_millis() <= stop_ms {
        cool += 1;
        let t0 = std::time::Instant::now();
        let (moved, proposed, per) = field.energy_sweep(&problems, &mut answers, void, cool, mix(seed ^ 0xC001, cool as u64), realization, &mut |_, _| {}).map_err(|e| e.to_string())?;
        println!("FIELD_WRITE_SWEEP descent cool={cool} moved={moved} proposed={proposed} accept_milli={} energy_milli={} sweep_ms={} ms={}", moved * 1000 / proposed.max(1), milli(mean_of(&per)), t0.elapsed().as_millis(), started.elapsed().as_millis());
        // [measurement; theory, November 7 23:05] The descent read step by step against its truths (section 7, on the host).
        dump(&format!("descent sweep {cool}"), &answers)?;
        if moved == 0 || cool >= 20 {
            break;
        }
    }
    dump(&format!("descent end at T/2^{cool}"), &answers)?;
    closing("descent", &answers, realization)?;
    println!("FIELD_WRITE_DONE ms={}", started.elapsed().as_millis());
    Ok(())
}

/// [measurement; agent-inferred, November 7] **The writer's declared law** (`FIELD_WRITER_*`): the flags of
/// [`holonics::hnn::tower::field::Field::sample_runs`] a write reads from its environment, one reading for every command that
/// writes (`length-field`, and `contrast-field`'s releases, which are the writer exactly as it writes).
pub(super) struct WriterLaw {
    pub run_bits: i128,
    pub near_tail: bool,
    pub place_order: bool,
    pub one_end: bool,
    pub rest: bool,
    pub spans: bool,
    pub refine_order: holonics::hnn::tower::field::RefineOrder,
}

impl WriterLaw {
    pub(super) fn from_env() -> Result<Self> {
        // [measurement; agent-inferred, November 5, §16.47] `FIELD_WRITER_RUN_BITS`: the writer releases runs bounded by that many
        // bits past each run's first place ([`Field::sample_runs`]), a declared comparison with one place a read on the same keys.
        let run_bits: i128 = std::env::var("FIELD_WRITER_RUN_BITS").ok().and_then(|v| v.parse::<i128>().ok()).unwrap_or(0);
        // [measurement; agent-inferred, November 5] `FIELD_WRITER_ROOM`: the writer reads the whole room past its lowest void,
        // the region law it replaced ([`Field::sample_runs`]'s `near_tail`), a declared comparison.
        let near_tail = std::env::var_os("FIELD_WRITER_ROOM").is_none();
        // [measurement; agent-inferred, November 6] `FIELD_WRITER_PLACE_ORDER`: each octave drawn in place order
        // ([`Field::sample_runs`]'s `place_order`), declared against the keyed order within an octave.
        let place_order = std::env::var_os("FIELD_WRITER_PLACE_ORDER").is_some();
        // [measurement; agent-inferred, November 6] `FIELD_WRITER_ONE_END`: each answer's length drawn once from the release's first
        // read ([`Field::sample_runs`]'s `one_end`).
        let one_end = std::env::var_os("FIELD_WRITER_ONE_END").is_some();
        // [measurement; agent-inferred, November 6, Brandon's lens of 17:31] `FIELD_WRITER_REST`: each answer's refine passes stop
        // where they come to rest ([`holonics::hnn::tower::field::Field::sample_runs`]), `refine` their most.
        let rest = std::env::var_os("FIELD_WRITER_REST").is_some();
        // [measurement; agent-inferred, November 6, the unified-theory reading of 17:58] `FIELD_WRITER_SPANS`: every second refine
        // pass moves spans, each opened whole and redrawn given the rest ([`holonics::hnn::tower::field::Field::sample_runs`]).
        let spans = std::env::var_os("FIELD_WRITER_SPANS").is_some();
        // [measurement; agent-inferred, November 6, the unified-theory reading of 21:14] `FIELD_WRITER_REFINE_ORDER`: `place` or
        // `reversed` walks each single-place refine pass in that scan ([`holonics::hnn::tower::field::RefineOrder`]), keyed otherwise.
        let refine_order = match std::env::var("FIELD_WRITER_REFINE_ORDER").as_deref() {
            Ok("place") => holonics::hnn::tower::field::RefineOrder::Place,
            Ok("reversed") => holonics::hnn::tower::field::RefineOrder::Reversed,
            Ok(other) if other != "keyed" => return Err(format!("FIELD_WRITER_REFINE_ORDER {other}: keyed, place or reversed").into()),
            _ => holonics::hnn::tower::field::RefineOrder::Keyed,
        };
        Ok(Self { run_bits, near_tail, place_order, one_end, rest, spans, refine_order })
    }
}

/// [definition; agent-inferred, November 6, the unified-theory reading of 22:52] **`found-field STATE STATE_SHA KEYS KEYS_SHA
/// OUT`**: a fresh founding of the state's declaration on the key stream `KEYS`, at the state's rate, written to `OUT` as a
/// learner. With `FIELD_ENERGY` set the founding's faces are one stored energy's forces (`FieldDeclaration::energy`); the
/// line's data, passes and levels are its declaration's, so a founding read compares the two laws on one declaration.
pub(super) fn found_field(args: &[String]) -> Result<()> {
    if args.len() != 6 {
        return Err("found-field STATE STATE_SHA KEYS KEYS_SHA OUT".into());
    }
    let learner = FieldLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let declaration = FieldDeclaration { energy: std::env::var_os("FIELD_ENERGY").is_some(), ..learner.field.declaration };
    let field = Field::found(declaration, &pinned_read(&args[3], &args[4], READ_BUDGET as usize)?).map_err(|e| e.to_string())?;
    let founded = FieldLearner::new(field, learner.rate_bits);
    std::fs::write(&args[5], founded.to_text())?;
    println!("FIELD_FOUNDED {} rate={} material={}", declaration_line(&founded.field), founded.rate_bits, founded.field.theta.len());
    Ok(())
}

/// A field's declaration head line.
fn declaration_line(field: &Field) -> String {
    field.to_text().lines().next().unwrap_or("").to_string()
}

/// [definition; the unified-theory reading of November 7, 01:37] The attribution read's step: `2^(−4)` of a letter's weight in
/// the uniform mixture (and four times it), where theory's identity reads the square to first order.
const ENERGY_EPS_SHIFT: u32 = 4;

/// [definition; the unified-theory reading of November 7, 01:37] **`temper-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA
/// TRAIN TRAIN_SHA COUNT OUT`**: an energy field's founding temperature, the letters read at one `T`, set where its faces open
/// at one bit of spread: over the first `COUNT` training problems' writer states (the question known, every answer place
/// open), the root mean square of each open site's face spread across the letters at `T = 1` (`Field::energy_temperature`).
/// Writes the learner with `log₂ T₀` set to `OUT`.
pub(super) fn temper_field(args: &[String]) -> Result<()> {
    if args.len() != 11 {
        return Err("temper-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA TRAIN TRAIN_SHA COUNT OUT".into());
    }
    let started = std::time::Instant::now();
    let mut learner = FieldLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let units = units_of(&args[5], &args[6])?;
    let codec = FieldCodec::from_text(std::str::from_utf8(&pinned_read(&args[3], &args[4], CODEC_BUDGET)?)?, units)?;
    let train = problems_of(&pinned_read(&args[7], &args[8], READ_BUDGET as usize)?);
    let n = count(&args[9])?.min(train.len());
    let void = codec.void();
    let mut states: Vec<(Vec<usize>, Vec<bool>)> = Vec::with_capacity(n);
    for (question, _) in train.iter().take(n) {
        let (q, room) = opening(&codec, &learner.field, question, b"")?;
        let mut classes = q.clone();
        classes.extend(std::iter::repeat_n(void, room));
        let open = (0..classes.len()).map(|t| t >= q.len()).collect();
        states.push((classes, open));
    }
    let regions: Vec<Region> = states.iter().map(|(c, o)| Region { classes: c, unresolved: o, faces: &[], locked: &[], echo: &[], domain: None, port: None }).collect();
    let (ell, spread) = learner.field.energy_temperature(&regions).map_err(|e| e.to_string())?;
    let at = learner.field.layout().face_temper;
    learner.field.theta[at] = ell;
    std::fs::write(&args[10], learner.to_text())?;
    println!("FIELD_TEMPER problems={n} spread_bits={} log2_T={} ms={}", bits(spread as i64 * 16, 1), bits(ell as i64 >> 4, 1), started.elapsed().as_millis());
    Ok(())
}

/// [measurement] **`rows-field`**: where an open and a definite receiver's rows put their mass (§15.9's
/// reading, `Field::row_shares`) on three sets of crib regions: the withheld problems read with their
/// neighbours (`unseen_regions`), training's masked regions over the whole region and over the answer (`shape`), each
/// set over the first `COUNT` training problems. With `KEYS`, the field is founded from the state's
/// declaration on those keys (the founding); else the state is read as it stands.
pub(super) fn rows_field(args: &[String]) -> Result<()> {
    if args.len() != 11 && args.len() != 13 {
        return Err("rows-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA TRAIN TRAIN_SHA COUNT SEED [KEYS KEYS_SHA]".into());
    }
    let started = std::time::Instant::now();
    let learner = FieldLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let field = match args.get(11..13) {
        Some([keys, sha]) => Field::found(learner.field.declaration, &pinned_read(keys, sha, READ_BUDGET as usize)?).map_err(|e| e.to_string())?,
        _ => learner.field,
    };
    let units = units_of(&args[5], &args[6])?;
    let codec = FieldCodec::from_text(std::str::from_utf8(&pinned_read(&args[3], &args[4], CODEC_BUDGET)?)?, units)?;
    let train = problems_of(&pinned_read(&args[7], &args[8], READ_BUDGET as usize)?);
    let (count_n, seed) = (count(&args[9])?, args[10].parse::<u64>().map_err(|_| "a seed that is not a number")?);
    let encoded: Problems = train.iter().take(count_n).map(|(q, a)| Ok((codec.encode(&question_text(q)).map_err(|e| e.to_string())?, codec.encode(a).map_err(|e| e.to_string())?, a.len()))).collect::<std::result::Result<Vec<_>, String>>()?;
    let encoded: Problems = encoded.into_iter().filter(|(_, a, _)| a.len() < codec.answer).collect();
    let all: Vec<usize> = (0..encoded.len()).collect();
    let withheld: Vec<(Vec<usize>, Vec<bool>)> = unseen_regions(&codec, &encoded, &all, seed);
    let (mut masked, mut answers) = (Vec::new(), Vec::new());
    let mut draw = 0u64;
    for (q, a, _) in &encoded {
        draw += 1;
        let length = q.len() + a.len() + tail(seed, draw, codec.answer - a.len());
        let classes = region_classes(&codec, q, a, length);
        match shape(seed, draw, q.len(), length) {
            Shape::Masked(mask) => masked.push((classes, mask)),
            Shape::Answer(mask) => answers.push((classes, mask)),
        }
    }
    for (name, set) in [("withheld", &withheld), ("masked", &masked), ("answer", &answers)] {
        let mut total = holonics::hnn::tower::field::RowShares::default();
        for (classes, open) in set.iter() {
            let r = field.row_shares(&Region { classes, unresolved: open, faces: &[], locked: &[], echo: &[], domain: None, port: None }).map_err(|e| e.to_string())?;
            for k in 0..2 {
                total.rows[k] += r.rows[k];
                total.far_sources[k] += r.far_sources[k];
                total.near[k] += r.near[k];
                total.far[k] += r.far[k];
                total.crowd[k] += r.crowd[k];
                total.peak[k] += r.peak[k];
            }
        }
        let share = |v: u128, k: usize| if total.rows[k] == 0 { 0 } else { (v * 1_000_000 >> 63) / total.rows[k] as u128 };
        for (k, kind) in [(0usize, "open"), (1, "definite")] {
            println!("FIELD_ROWS set={name} receivers={kind} regions={} rows={} far_sources_a_row={} near_millionths={} far_millionths={} crowd_millionths={} peak_millionths={}", set.len(), total.rows[k], total.far_sources[k] / total.rows[k].max(1), share(total.near[k], k), share(total.far[k], k), share(total.crowd[k], k), share(total.peak[k], k));
        }
    }
    println!("FIELD_ROWS_DONE ms={}", started.elapsed().as_millis());
    Ok(())
}

/// [measurement; agent-inferred, November 2] **`currents-field`**: H6's value side and readout side (§16.21), a reading
/// of `STATE` on the held problems read with their neighbours beside their own question (base 1 of [`held_regions`])
/// and beside the next problem's (base 2, the foil), through the realization, with the founding of `KEYS` beside it.
/// For each tick and head, over the answer rows (each unresolved answer site of a part, the foil's row paired with the
/// own row at the same answer offset):
/// - `FIELD_CURRENTS_CHANGE`: the quartiles of `‖F_own − F_foil‖ / ‖F_own‖`, `F` the row's current from the question
///   past the near field ([`RowCurrent`]), of `‖F_own‖ / ‖N_own‖` (`N` the near field's) and of `‖F_own‖ / ‖Y_own‖`
///   (`Y = F + N + R` the row's whole current, `R` its other sources'), in thousandths, rows with no far current
///   counted apart; and how many independent directions the problems' far currents span, the
///   participation ratio `(tr C)² / tr C²` of the centred second moment `C` of each problem's mean `F_own` (the means
///   on `2^(−32)`), in thousandths.
/// - `FIELD_CURRENTS_GAIN`: the face's gain on each part of the change, `Σ ½⟨δỹ_own + δỹ_foil, F_foil − F_own⟩`
///   and the same through `N` and through `R`, each beside its bound `Σ ½‖δỹ_own + δỹ_foil‖ ‖Δ‖` (the gain were the
///   change aligned with the covector), `δỹ` the code's covector of the row's framed current (the face's mass `2^z`, so the
///   covector is in bits), in millionths of a bit an answer site, beside the code itself, foil less own
///   (`FIELD_CURRENTS_CODE`).
/// - `FIELD_CURRENTS_TOP`: the quartiles of each row's largest share, in millionths.
///
/// And each head's two temperatures `log₂ T` (class receiver and listener) against the founding's
/// (`FIELD_CURRENTS_SETTING`). Region-level groups only: no source is paired with a receiver by its class. A reading
/// only.
pub(super) fn currents_field(args: &[String], realization: &mut dyn FieldRealization) -> Result<()> {
    use holonics::hnn::tower::field::RowCurrent;
    if args.len() != 11 {
        return Err("currents-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD HELD_SHA KEYS KEYS_SHA".into());
    }
    let started = std::time::Instant::now();
    let learner = FieldLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let field = &learner.field;
    let d = field.declaration;
    let founded = Field::found(d, &pinned_read(&args[9], &args[10], READ_BUDGET as usize)?).map_err(|e| e.to_string())?;
    let units = units_of(&args[5], &args[6])?;
    let codec = FieldCodec::from_text(std::str::from_utf8(&pinned_read(&args[3], &args[4], CODEC_BUDGET)?)?, units)?;
    let held = problems_of(&pinned_read(&args[7], &args[8], READ_BUDGET as usize)?);
    let held: Problems = held.iter().map(|(q, a)| Ok((codec.encode(&question_text(q)).map_err(|e| e.to_string())?, codec.encode(a).map_err(|e| e.to_string())?, a.len()))).collect::<std::result::Result<Vec<_>, String>>()?;
    let held: Problems = held.into_iter().filter(|(_, a, _)| a.len() < codec.answer).collect();
    let n = held.len();
    let (heads, span) = (d.heads, 2 * d.modes);
    let keys = d.ticks * heads;
    // The settings: each head's temperatures, learned against founded, `log₂ T` on 2^(−24) to four places.
    let log2 = |ell: i32| -> String {
        let v = (ell as i128 * 10_000) >> holonics::hnn::tower::MATERIAL_BITS;
        format!("{}{}.{:04}", if v < 0 { "-" } else { "" }, v.abs() / 10_000, v.abs() % 10_000)
    };
    let layout = field.layout();
    for h in 0..heads {
        for (kind, name) in [(0usize, "class"), (1, "listener")] {
            let (l0, l1) = (founded.theta[layout.temper + 2 * h + kind], field.theta[layout.temper + 2 * h + kind]);
            println!("FIELD_CURRENTS_SETTING head={h} receiver={name} log2_temperature_founded={} log2_temperature_learned={} log2_ratio={}", log2(l0), log2(l1), log2(l1 - l0));
        }
    }
    let regions = held_regions(&codec, &held);
    let view = |k: usize| Region { classes: &regions[k].0, unresolved: &regions[k].1, faces: &[], locked: &[], echo: &[], domain: None, port: None };
    let own: Vec<Region> = (n..n + n * CONTEXT).map(view).collect();
    let foil: Vec<Region> = (n + n * CONTEXT..n + 2 * n * CONTEXT).map(view).collect();
    let q_own: Vec<usize> = held.iter().flat_map(|(q, _, _)| std::iter::repeat_n(q.len(), CONTEXT)).collect();
    let q_foil: Vec<usize> = (0..n).flat_map(|i| std::iter::repeat_n(held[(i + 1) % n].0.len(), CONTEXT)).collect();
    // Per key (tick, head): the change ratios as (‖ΔF‖², ‖F‖²), the far-to-near as (‖F‖², ‖N‖²), the rows with no far
    // current, each problem's sum of F and its rows, the two gains (twice, on 2^(−40) bits), and the tops.
    let mut change: Vec<Vec<(u128, u128)>> = vec![Vec::new(); keys];
    let mut far_near: Vec<Vec<(u128, u128)>> = vec![Vec::new(); keys];
    let mut far_row: Vec<Vec<(u128, u128)>> = vec![Vec::new(); keys];
    let mut silent = vec![0u64; keys];
    let mut sums: Vec<Vec<(Vec<i128>, u64)>> = vec![vec![(vec![0i128; span], 0u64); n]; keys];
    let (mut gain_far, mut gain_near, mut gain_rest) = (vec![0i128; keys], vec![0i128; keys], vec![0i128; keys]);
    let mut bound: Vec<[i128; 3]> = vec![[0i128; 3]; keys];
    let mut tops: Vec<Vec<u64>> = vec![Vec::new(); keys];
    let (mut code_own, mut code_foil, mut sites) = (0i64, 0i64, 0usize);
    let square = |v: &[i128]| -> u128 { v.iter().map(|&x| (x * x) as u128).sum() };
    let chunk = 16 * CONTEXT;
    for at in (0..own.len()).step_by(chunk) {
        let end = (at + chunk).min(own.len());
        let rows_own = realization.read_row_currents(field, &own[at..end], &q_own[at..end], true).map_err(|e| e.to_string())?;
        let rows_foil = realization.read_row_currents(field, &foil[at..end], &q_foil[at..end], true).map_err(|e| e.to_string())?;
        let faces_own = realization.read_faces(field, &own[at..end]).map_err(|e| e.to_string())?;
        let faces_foil = realization.read_faces(field, &foil[at..end]).map_err(|e| e.to_string())?;
        for r in 0..end - at {
            let (k, problem) = (at + r, (at + r) / CONTEXT);
            for (face, &class) in faces_own[r].iter().zip(own[k].classes) {
                if let Some(face) = face {
                    code_own += face.code(class);
                    sites += 1;
                }
            }
            for (face, &class) in faces_foil[r].iter().zip(foil[k].classes) {
                code_foil += face.as_ref().map_or(0, |f| f.code(class));
            }
            if rows_own[r].len() != rows_foil[r].len() {
                return Err("an own and a foil part whose answer rows differ".into());
            }
            for (a, b) in rows_own[r].iter().zip(&rows_foil[r]) {
                let RowCurrent { tick, head, site, .. } = *a;
                if (tick, head) != (b.tick, b.head) || site as usize - q_own[k] != b.site as usize - q_foil[k] {
                    return Err("an own and a foil row at different answer places".into());
                }
                let key = tick as usize * heads + head as usize;
                let df: Vec<i128> = b.far.iter().zip(&a.far).map(|(&y, &x)| y - x).collect();
                let dn: Vec<i128> = b.near.iter().zip(&a.near).map(|(&y, &x)| y - x).collect();
                let dr: Vec<i128> = b.rest.iter().zip(&a.rest).map(|(&y, &x)| y - x).collect();
                let whole: Vec<i128> = (0..span).map(|x| a.far[x] + a.near[x] + a.rest[x]).collect();
                let (cur, near) = (square(&a.far), square(&a.near));
                if cur == 0 {
                    silent[key] += 1;
                } else {
                    change[key].push((square(&df), cur));
                }
                far_near[key].push((cur, near));
                far_row[key].push((cur, square(&whole)));
                let (sum, rows) = &mut sums[key][problem];
                for (s, &x) in sum.iter_mut().zip(&a.far) {
                    *s += x;
                }
                *rows += 1;
                let mut cc = 0u128;
                for x in 0..span.min(a.covector.len()).min(b.covector.len()) {
                    let c = a.covector[x] as i128 + b.covector[x] as i128;
                    cc += (c * c) as u128;
                    gain_far[key] += c * df[x];
                    gain_near[key] += c * dn[x];
                    gain_rest[key] += c * dr[x];
                }
                for (slot, delta) in bound[key].iter_mut().zip([&df, &dn, &dr]) {
                    *slot += (cc * square(delta)).isqrt() as i128;
                }
                tops[key].push(a.top);
            }
        }
    }
    println!("FIELD_CURRENTS_READ problems={n} parts={} answer_sites={sites} ms={}", own.len(), started.elapsed().as_millis());
    // The quartiles of √(num/den) in thousandths, ordered exactly by cross products (a zero denominator last).
    let quartiles = |mut v: Vec<(u128, u128)>| -> String {
        if v.is_empty() {
            return "-/-/-".into();
        }
        v.sort_by(|&(a, b), &(c, e)| (a * e).cmp(&(c * b)).then(b.cmp(&e)));
        let at = |k: usize| {
            let (num, den) = v[(v.len() * k / 4).min(v.len() - 1)];
            if den == 0 { "inf".to_string() } else { ((num * 1_000_000 / den).isqrt()).to_string() }
        };
        format!("{}/{}/{}", at(1), at(2), at(3))
    };
    let micro = |num: i128, den: i128| -> String {
        if den == 0 {
            return "-".into();
        }
        let m = num * 1_000_000 / den;
        format!("{}{}.{:06}", if m < 0 { "-" } else { "" }, m.abs() / 1_000_000, m.abs() % 1_000_000)
    };
    let (mut tick_far, mut tick_near, mut tick_rest) = (vec![0i128; d.ticks], vec![0i128; d.ticks], vec![0i128; d.ticks]);
    for tick in 0..d.ticks {
        for head in 0..heads {
            let key = tick * heads + head;
            // The problems' mean far currents on 2^(−32) (each sum shifted 16 bits before its division), centred
            // without division (P m_i − Σ m), and their second moment.
            let means: Vec<Vec<i128>> = sums[key].iter().filter(|(_, rows)| *rows > 0).map(|(s, rows)| s.iter().map(|&x| (x << 16) / *rows as i128).collect()).collect();
            let directions = if means.len() < 2 {
                "-".to_string()
            } else {
                let p = means.len() as i128;
                let total: Vec<i128> = (0..span).map(|x| means.iter().map(|m| m[x]).sum()).collect();
                let centred: Vec<Vec<num_bigint::BigInt>> = means.iter().map(|m| (0..span).map(|x| num_bigint::BigInt::from(p * m[x] - total[x])).collect()).collect();
                let mut c = vec![num_bigint::BigInt::from(0); span * span];
                for x in &centred {
                    for a in 0..span {
                        for b in 0..span {
                            c[a * span + b] += &x[a] * &x[b];
                        }
                    }
                }
                let trace: num_bigint::BigInt = (0..span).map(|a| c[a * span + a].clone()).sum();
                let frob: num_bigint::BigInt = c.iter().map(|v| v * v).sum();
                if frob == num_bigint::BigInt::from(0) { "-".to_string() } else { (&trace * &trace * num_bigint::BigInt::from(1000) / frob).to_string() }
            };
            let rows = far_near[key].len() as u64;
            println!(
                "FIELD_CURRENTS_CHANGE tick={tick} head={head} rows={rows} silent={} change_over_current_milli={} far_over_near_milli={} far_over_row_milli={} directions_milli={directions} of={span}",
                silent[key],
                quartiles(change[key].clone()),
                quartiles(far_near[key].clone()),
                quartiles(far_row[key].clone()),
            );
            // The gains, twice on 2^(−40) bits, halved at the print, a site.
            let den = (sites as i128) << 41;
            println!(
                "FIELD_CURRENTS_GAIN tick={tick} head={head} far_bits_a_site={} near_bits_a_site={} rest_bits_a_site={} far_bound={} near_bound={} rest_bound={}",
                micro(gain_far[key], den),
                micro(gain_near[key], den),
                micro(gain_rest[key], den),
                micro(bound[key][0], den),
                micro(bound[key][1], den),
                micro(bound[key][2], den)
            );
            tick_far[tick] += gain_far[key];
            tick_near[tick] += gain_near[key];
            tick_rest[tick] += gain_rest[key];
            let mut top = tops[key].clone();
            top.sort_unstable();
            let q = |k: usize| top.get((top.len() * k / 4).min(top.len().saturating_sub(1))).map_or("-".to_string(), |&t| ((t as u128 * 1_000_000) >> 63).to_string());
            println!("FIELD_CURRENTS_TOP tick={tick} head={head} rows={} top_share_micro={}/{}/{}", top.len(), q(1), q(2), q(3));
        }
    }
    let den = (sites as i128) << 41;
    for tick in 0..d.ticks {
        println!("FIELD_CURRENTS_GAIN_TICK tick={tick} far_bits_a_site={} near_bits_a_site={} rest_bits_a_site={}", micro(tick_far[tick], den), micro(tick_near[tick], den), micro(tick_rest[tick], den));
    }
    // The code itself on 2^(−20) bits a site: foil less own is the question's effect.
    let site_den = (sites as i128) << 20;
    println!("FIELD_CURRENTS_CODE sites={sites} own_bits_a_site={} foil_bits_a_site={} foil_less_own={}", micro(code_own as i128, site_den), micro(code_foil as i128, site_den), micro(code_foil as i128 - code_own as i128, site_den));
    println!("FIELD_CURRENTS_DONE ms={}", started.elapsed().as_millis());
    Ok(())
}

/// The host realization, for the dispatcher.
pub(super) fn host() -> HostField {
    HostField
}

#[cfg(test)]
mod tests {
    use super::*;

    /// [theory, November 9 21:43] **The census lens off reads the plain faces exactly, and on reads the residual lens**: on a
    /// small founded field, a lensed read through an empty table is the host's read face for face; through a table it is
    /// [`lensed_face`] of each open site's face at its plate, and moves the faces.
    #[test]
    fn the_census_lens_off_is_the_plain_read_and_on_is_the_residual_lens() {
        let d = FieldDeclaration { alphabet: 5, width: 8, heads: 2, modes: 3, still: 1, contacts: 4, ticks: 2, frames: 2, reach: 16, lanes: 1, depth: 0, energy: false };
        let keys: Vec<u8> = (0..1u32 << 16).map(|i| (i.wrapping_mul(2_654_435_761) >> 13) as u8).collect();
        let field = Field::found(d, &keys).unwrap();
        let classes = [1usize, 4, 0, 2, 2, 3, 1];
        let open = [false, true, false, true, false, false, true];
        let r = Region { classes: &classes, unresolved: &open, faces: &[], locked: &[], echo: &[], domain: None, port: None };
        let plain = HostField.read_faces(&field, &[r]).unwrap();
        let empty = LensTable::new();
        assert_eq!(Lensed { inner: &mut HostField, table: &empty, depth: 1 }.read_faces(&field, &[r]).unwrap(), plain);
        let (faces, plates) = HostField.read_plates(&field, &[r]).unwrap();
        let mut table = LensTable::new();
        for (t, face) in faces[0].iter().enumerate() {
            if face.is_some() {
                let key: Vec<u32> = plates[0][t * 2..t * 2 + 2].iter().map(|&c| c % 3).collect();
                table.insert(key, (vec![9, 0, 3, 0, 1], vec![1 << 20; 5]));
            }
        }
        let lensed = Lensed { inner: &mut HostField, table: &table, depth: 1 }.read_faces(&field, &[r]).unwrap();
        for (t, face) in faces[0].iter().enumerate() {
            assert_eq!(lensed[0][t], face.as_ref().map(|f| lensed_face(f, &plates[0][t * 2..t * 2 + 2], 1, &table)));
        }
        assert_ne!(lensed, plain);
    }

    #[test]
    fn the_bytes_codec_reads_a_number_alike_wherever_it_is_written() {
        let problems = vec![(b"Tom has 1,200 apples.".to_vec(), b"He has <<1200+35=1235>>1235\n#### 1235".to_vec())];
        let codec = FieldCodec::found(Units::bytes(), &problems).unwrap();
        let text = b"He has 1200 apples.\n#### 35".as_slice();
        let classes = codec.encode(text).unwrap();
        assert_eq!(codec.decode(&classes), text);
        assert_eq!(codec.encode(b"1200").unwrap(), codec.encode(b"<<1200").unwrap()[2..].to_vec());
        assert!(codec.encode(b"~").is_err(), "a unit the passage never used");
        let back = FieldCodec::from_text(&codec.to_text(), Units::bytes()).unwrap();
        assert_eq!((back.used.clone(), back.answer), (codec.used.clone(), codec.answer));
        assert_eq!(codec.answer, codec.encode(&problems[0].1).unwrap().len() + 1);
    }

    /// A flat lap widens once the code has fallen at this width; a second growth is held and the laps go on;
    /// a falling lap, a lap before any fall, and the last lap never grow.
    #[test]
    fn a_second_growth_is_held_and_the_laps_go_on() {
        assert_eq!(growth(false, true, false, 1, 27), Growth::Widen);
        assert_eq!(growth(false, true, true, 9, 27), Growth::Held);
        assert_eq!(growth(true, true, true, 9, 27), Growth::None);
        assert_eq!(growth(false, false, false, 0, 27), Growth::None);
        assert_eq!(growth(false, true, false, 26, 27), Growth::None);
        assert_eq!(growth(false, true, true, 26, 27), Growth::None);
    }

    /// [§16.41] The octave nearest the joint parabola's least `μ* = 1 − Σt / 2Σb`: no transfer keeps the step; a transfer
    /// that says the next sections would take more (`Σ t < 0`) doubles it only past `μ* > √2`, one that says they took too
    /// much halves it below `μ* < 1/√2`; with no curvature read the sign of `Σ t` alone moves it.
    #[test]
    fn the_step_moves_to_the_octave_nearest_its_joint_least() {
        assert_eq!(step_transfer(0, 100), 0);
        assert_eq!(step_transfer(-50, 100), 0); // μ* = 1.25
        assert_eq!(step_transfer(-100, 100), 1); // μ* = 1.5 > √2
        assert_eq!(step_transfer(50, 100), 0); // μ* = 0.75 > 1/√2
        assert_eq!(step_transfer(60, 100), -1); // μ* = 0.7 < 1/√2
        assert_eq!(step_transfer(300, 100), -1); // μ* < 0
        assert_eq!(step_transfer(5, 0), -1);
        assert_eq!(step_transfer(-5, -3), 1);
        assert_eq!(step_transfer(0, 0), 0);
    }

    /// [§16.42] A restated result is named by its close and its length where `D = C` inside an opened `<<…>>`; an inexact
    /// restatement, an unopened one and a multi-byte piece are not.
    #[test]
    fn a_restatement_is_named_by_its_close_and_its_length() {
        let pieces = |t: &str| -> Vec<Vec<u8>> { t.bytes().map(|b| vec![b]).collect() };
        assert_eq!(restatements_of(&pieces("He has 2*3=<<2*3=6>>6 and <<6+40=46>>46.")), vec![(18, 1), (35, 2)]);
        assert_eq!(restatements_of(&pieces("<<50*10=500>>50 then 3=4>>4")), vec![]);
        let mut welded = pieces("<<1+1=2>>2");
        welded[6] = b"2>".to_vec();
        assert_eq!(restatements_of(&welded), vec![]);
    }

    /// [§16.23] The joint read's states: one a stratum of `1..m`, each `K_s` inside its stratum, the strata covering
    /// `1..m` once, `K_s` answer sites open and nothing else, keyed alike for the own question and the foil.
    #[test]
    fn the_joint_states_stratify_the_reading_orders() {
        let (q, a) = (vec![1usize, 2, 3, 4, 5], vec![2usize; 11]);
        let states = joint_states(0, &q, &a, 7, 3);
        let m = a.len() + 1;
        assert_eq!(states.len(), CONTEXT);
        assert_eq!(states.iter().map(|s| s.2 .0).sum::<u64>(), m as u64);
        let mut lo = 1u64;
        for (classes, open, (size, k)) in &states {
            assert_eq!(classes.len(), q.len() + m);
            assert!(*k >= lo && *k < lo + size, "K {k} in [{lo}, {})", lo + size);
            lo += size;
            assert_eq!(open.iter().filter(|&&u| u).count() as u64, *k);
            assert!(open[..q.len()].iter().all(|&u| !u), "the question is resolved");
        }
        let foil = joint_states(0, &[9, 9], &a, 7, 3);
        for (own, foil) in states.iter().zip(&foil) {
            assert_eq!(own.1[q.len()..], foil.1[2..], "the foil reads the same states");
        }
        assert_eq!(joint_states(0, &q, &[], 7, 3).len(), 1, "a one-site answer has one stratum");
    }

    #[test]
    fn problems_split_at_blank_lines() {
        let text = b"Q one?\nA one.\n#### 1\n\nQ two?\nA two #### 2\n";
        let problems = problems_of(text);
        assert_eq!(problems.len(), 2);
        assert_eq!(problems[0], (b"Q one?".to_vec(), b"A one.\n#### 1".to_vec()));
        assert_eq!(problems[1].1, b"A two #### 2".to_vec());
    }


    /// The commands end to end on the host: a toy passage trains two laps, rests, continues from
    /// its rested learner, refuses to write over a run, and writes its held problems' answers with their
    /// coupling reads.
    #[test]
    fn the_field_trains_rests_continues_and_writes() {
        let dir = std::env::temp_dir().join(format!("holonics-field-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("dir");
        let at = |name: &str| dir.join(name).to_string_lossy().into_owned();
        let put = |name: &str, bytes: &[u8]| {
            std::fs::write(dir.join(name), bytes).expect("write");
            (at(name), sha256(bytes).expect("sha"))
        };
        let train_text = TOY;
        let held_text = b"Tom has 2 apples and buys 4 more. How many apples does he have?\nHe has <<2+4=6>>6 apples.\n#### 6\n\nTom has 5 apples and buys 3 more. How many apples does he have?\nHe has <<5+3=8>>8 apples.\n#### 8\n";
        let keys: Vec<u8> = (0..1u64 << 13).flat_map(|i| mix(0x5EED, i).to_be_bytes()).collect();
        let (units, units_sha) = put("UNITS", b"founded-units-v1 0\n");
        let (passage, passage_sha) = put("TRAIN", train_text);
        let (held, held_sha) = put("HELD", held_text);
        let (key, key_sha) = put("KEYS", &keys);
        let bounded = |out: &str, stop_ms: &str, from: Option<(String, String)>| {
            let mut args: Vec<String> = ["train-field", &units, &units_sha, &passage, &passage_sha, &held, &held_sha, &key, &key_sha, "8", "2", "3", "1", "4", "2", "2", "2", "4", "600000", "600000", stop_ms, out].iter().map(|s| s.to_string()).collect();
            if let Some((state, sha)) = from {
                args.extend([state, sha]);
            }
            train(&args, &mut host())
        };
        // The run holds two laps of its bound, so the second lap starts.
        let run = |out: &str, from: Option<(String, String)>| bounded(out, "1200000", from);
        // A run past its own bound rests at the section it reached and writes no lap's state.
        bounded(&at("S"), "1", None).expect("stopped");
        assert!(dir.join("S/STATE.stopped").exists() && !dir.join("S/STATE.0").exists());
        let stopped = std::fs::read(dir.join("S/STATE.stopped")).expect("stopped state");
        assert!(FieldLearner::from_text(std::str::from_utf8(&stopped).unwrap()).is_ok());
        run(&at("A"), None).expect("train");
        let rested = std::fs::read(dir.join("A/STATE.1")).expect("rested");
        let codec = std::fs::read(dir.join("A/CODEC")).expect("codec");
        assert!(run(&at("A"), None).is_err(), "a run's directory is never written over");
        run(&at("B"), Some((at("A/STATE.1"), sha256(&rested).unwrap()))).expect("continued");
        assert!(dir.join("B/STATE.1").exists());
        let state_sha = sha256(&rested).unwrap();
        let codec_sha = sha256(&codec).unwrap();
        let args: Vec<String> = ["sample-field", &at("A/STATE.1"), &state_sha, &at("A/CODEC"), &codec_sha, &units, &units_sha, &held, &held_sha, "2", "3", "1", "600000", &at("R")].iter().map(|s| s.to_string()).collect();
        sample(&args, &mut host()).expect("sample");
        let read_in = |run: &str, name: &str| String::from_utf8(std::fs::read(dir.join(run).join(name)).expect("read")).unwrap();
        assert_eq!(read_in("R", "SAMPLE.tsv").lines().count(), 2);
        let coupling = read_in("R", "COUPLING.tsv");
        assert_eq!(coupling.lines().count(), 3);
        for row in coupling.lines().skip(1) {
            let cells: Vec<usize> = row.split('\t').take(5).map(|c| c.parse().unwrap()).collect();
            assert_eq!(cells[1] + cells[2], 2 * cells[3] + cells[4], "F* = |H| + |T| - 2 lambda");
        }
        assert!(sample(&args, &mut host()).is_err(), "a writer's directory is never written over");
        // A write stopped at its deadline still writes a row a problem, every place drawn on its last read.
        let mut stopped = args.clone();
        stopped[12] = "1".to_string();
        stopped[13] = at("Q");
        sample(&stopped, &mut host()).expect("stopped sample");
        assert_eq!(read_in("Q", "SAMPLE.tsv").lines().count(), 2);
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// The keyed tail meets every octave of its room (`FIELD_TAIL_KEYED`; under the law the tail is the near field's).
    #[test]
    fn tails_meet_every_octave_within_their_room() {
        if near_tail() {
            return;
        }
        let room = 100usize;
        let mut octaves = [false; 7];
        for draw in 0..512 {
            let t = tail(9, draw, room);
            assert!((1..=room).contains(&t));
            octaves[(usize::BITS - 1 - t.leading_zeros()) as usize] = true;
        }
        assert!(octaves.iter().all(|&o| o));
        assert_eq!(tail(9, 3, 1), 1);
    }

    /// [theory, November 10 01:29] `phase-field` end to end on the host: its checks pass on a small field (every group's bins
    /// sum to its set's sites, the bins balance, mode 0's key sector is 2b's depth-1 class, the moments sum), and its tables hold
    /// every set, head, mode, word and bin, and every set's letters.
    #[test]
    fn the_phase_census_reads_every_bin_and_moment_on_a_small_field() {
        let dir = std::env::temp_dir().join(format!("holonics-phase-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("dir");
        let put = |name: &str, bytes: &[u8]| {
            std::fs::write(dir.join(name), bytes).expect("write");
            (dir.join(name).to_string_lossy().into_owned(), sha256(bytes).expect("sha"))
        };
        let (codec, problems) = toy();
        let learner = toy_learner(&codec, &problems);
        let keys: Vec<u8> = (0..1u64 << 13).flat_map(|i| mix(0x5EED, i).to_be_bytes()).collect();
        let (state, state_sha) = put("STATE", learner.to_text().as_bytes());
        let (units, units_sha) = put("UNITS", b"founded-units-v1 0\n");
        let (train, train_sha) = put("TRAIN", TOY);
        let (held, held_sha) = put("HELD", TOY);
        let (key, key_sha) = put("KEYS", &keys);
        let out = dir.join("OUT").to_string_lossy().into_owned();
        let args: Vec<String> = ["phase-field", &units, &units_sha, &train, &train_sha, &held, &held_sha, &key, &key_sha, "2", "0", &state, &state_sha, "-", &out].iter().map(|s| s.to_string()).collect();
        phase_field(&args, &mut HostField).unwrap();
        let d = learner.field.declaration;
        let phase = std::fs::read_to_string(dir.join("OUT/CENSUS_PHASE.tsv")).unwrap();
        assert_eq!(phase.lines().count(), 1 + PHASE_SETS.len() * d.heads * d.modes * 2 * (holonics::hnn::tower::field::PHASE_BINS + 1));
        let moment = std::fs::read_to_string(dir.join("OUT/CENSUS_MOMENT.tsv")).unwrap();
        assert_eq!(moment.lines().count(), 1 + PHASE_SETS.len() * (2 + 6 * d.alphabet));
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// [theory, November 10 04:40] `reach2-field` end to end on the host: every (set, d, far, letter) is a row (far a letter, the
    /// void, or the blank of an open place), and each offset counts every site of its set once.
    #[test]
    fn the_reach_census_on_2bs_charge_counts_every_site_once_an_offset() {
        let dir = std::env::temp_dir().join(format!("holonics-reach2-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("dir");
        let put = |name: &str, bytes: &[u8]| {
            std::fs::write(dir.join(name), bytes).expect("write");
            (dir.join(name).to_string_lossy().into_owned(), sha256(bytes).expect("sha"))
        };
        let (codec, problems) = toy();
        let learner = toy_learner(&codec, &problems);
        let keys: Vec<u8> = (0..1u64 << 13).flat_map(|i| mix(0x5EED, i).to_be_bytes()).collect();
        let (state, state_sha) = put("STATE", learner.to_text().as_bytes());
        let (units, units_sha) = put("UNITS", b"founded-units-v1 0\n");
        let (train, train_sha) = put("TRAIN", TOY);
        let (held, held_sha) = put("HELD", TOY);
        let (key, key_sha) = put("KEYS", &keys);
        let out = dir.join("OUT").to_string_lossy().into_owned();
        let args: Vec<String> = ["reach2-field", &units, &units_sha, &train, &train_sha, &held, &held_sha, &key, &key_sha, "2", "0", &state, &state_sha, "-", "1", &out].iter().map(|s| s.to_string()).collect();
        reach2_field(&args, &mut HostField).unwrap();
        let a = learner.field.declaration.alphabet;
        let text = std::fs::read_to_string(dir.join("OUT/REACH2.tsv")).unwrap();
        assert_eq!(text.lines().count(), 1 + 3 * 2 * REACH.len() * (a + 1) * a);
        for name in ["train_even", "train_odd", "held"] {
            let at = |d: &str| -> usize { text.lines().skip(1).map(|l| l.split('\t').collect::<Vec<_>>()).filter(|c| c[0] == name && c[1] == d).map(|c| c[4].parse::<usize>().unwrap()).sum() };
            assert_eq!(at("-1"), at("256"), "{name}: every offset counts every site once");
        }
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// [theory, November 10 03:45] `reach-census-field` end to end on the host: every (set, d, far letter, letter) is a row, and
    /// at each offset every place of its set is counted once.
    #[test]
    fn the_reach_census_counts_every_place_once_an_offset() {
        let dir = std::env::temp_dir().join(format!("holonics-reach-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("dir");
        let put = |name: &str, bytes: &[u8]| {
            std::fs::write(dir.join(name), bytes).expect("write");
            (dir.join(name).to_string_lossy().into_owned(), sha256(bytes).expect("sha"))
        };
        let (codec, problems) = toy();
        let learner = toy_learner(&codec, &problems);
        let (state, state_sha) = put("STATE", learner.to_text().as_bytes());
        let (codec_path, codec_sha) = put("CODEC", codec.to_text().as_bytes());
        let (units, units_sha) = put("UNITS", b"founded-units-v1 0\n");
        let (held, held_sha) = put("HELD", TOY);
        let (train, train_sha) = put("TRAIN", TOY);
        let out = dir.join("OUT").to_string_lossy().into_owned();
        let args: Vec<String> = ["reach-census-field", &state, &state_sha, &codec_path, &codec_sha, &units, &units_sha, &held, &held_sha, &train, &train_sha, "every-1", &out].iter().map(|s| s.to_string()).collect();
        reach_census_field(&args, &mut HostField).unwrap();
        let a = learner.field.declaration.alphabet;
        let text: String = ["held", "train_even", "train_odd"].iter().map(|s| std::fs::read_to_string(dir.join(format!("OUT/REACH.{s}.tsv"))).unwrap().lines().skip(1).map(|l| format!("{l}\n")).collect::<String>()).collect();
        let text = format!("header\n{text}");
        assert_eq!(text.lines().count(), 1 + 3 * 2 * REACH.len() * a * a);
        let places: [usize; 3] = [problems.iter().map(|p| p.1.len()).sum(), problems.iter().step_by(2).map(|p| p.1.len()).sum(), problems.iter().skip(1).step_by(2).map(|p| p.1.len()).sum()];
        for (set, name) in ["held", "train_even", "train_odd"].iter().enumerate() {
            for d in ["-1", "256"] {
                let n: usize = text.lines().skip(1).map(|l| l.split('\t').collect::<Vec<_>>()).filter(|c| c[0] == *name && c[1] == d).map(|c| c[4].parse::<usize>().unwrap()).sum();
                assert_eq!(n, places[set], "{name} d={d}");
            }
        }
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// [theory, November 10 03:25] `charge-field` end to end on the host: three states read, the reference's own state at each
    /// problem, and every state's pooled line.
    #[test]
    fn the_state_charge_census_reads_its_three_states() {
        let dir = std::env::temp_dir().join(format!("holonics-charge-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("dir");
        let put = |name: &str, bytes: &[u8]| {
            std::fs::write(dir.join(name), bytes).expect("write");
            (dir.join(name).to_string_lossy().into_owned(), sha256(bytes).expect("sha"))
        };
        let (codec, problems) = toy();
        let learner = toy_learner(&codec, &problems);
        let raw = problems_of(TOY);
        let written: String = raw.iter().enumerate().map(|(k, (_, ans))| format!("{k}\t{}\n", escaped(ans))).collect();
        let (state, state_sha) = put("STATE", learner.to_text().as_bytes());
        let (codec_path, codec_sha) = put("CODEC", codec.to_text().as_bytes());
        let (units, units_sha) = put("UNITS", b"founded-units-v1 0\n");
        let (held, held_sha) = put("HELD", TOY);
        let (rest, rest_sha) = put("REST", written.as_bytes());
        let (keyed, keyed_sha) = put("KEYED", written.as_bytes());
        let out = dir.join("OUT").to_string_lossy().into_owned();
        let args: Vec<String> = ["charge-field", &state, &state_sha, &codec_path, &codec_sha, &units, &units_sha, &held, &held_sha, "4", &rest, &rest_sha, &keyed, &keyed_sha, &out].iter().map(|s| s.to_string()).collect();
        charge_field(&args, &mut HostField).unwrap();
        assert_eq!(written_answers(&codec, &rest, &rest_sha, 4).unwrap(), problems.iter().map(|p| p.1.clone()).collect::<Vec<_>>());
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// [theory, November 10 02:03] `ring-census-field` end to end on the host: every set, ring, residue and letter is a row, at the
    /// letters' places and at the stop places, and each ring's residues count every place of its set once.
    #[test]
    fn the_ring_census_counts_every_place_once_a_ring() {
        let dir = std::env::temp_dir().join(format!("holonics-ring-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("dir");
        let put = |name: &str, bytes: &[u8]| {
            std::fs::write(dir.join(name), bytes).expect("write");
            (dir.join(name).to_string_lossy().into_owned(), sha256(bytes).expect("sha"))
        };
        let (codec, problems) = toy();
        let learner = toy_learner(&codec, &problems);
        let (state, state_sha) = put("STATE", learner.to_text().as_bytes());
        let (codec_path, codec_sha) = put("CODEC", codec.to_text().as_bytes());
        let (units, units_sha) = put("UNITS", b"founded-units-v1 0\n");
        let (held, held_sha) = put("HELD", TOY);
        let (train, train_sha) = put("TRAIN", TOY);
        let out = dir.join("OUT").to_string_lossy().into_owned();
        let args: Vec<String> = ["ring-census-field", &state, &state_sha, &codec_path, &codec_sha, &units, &units_sha, &held, &held_sha, &train, &train_sha, "2", &out].iter().map(|s| s.to_string()).collect();
        ring_census_field(&args, &mut HostField).unwrap();
        let a = learner.field.declaration.alphabet;
        let residues: usize = RINGS.iter().map(|r| r.3 as usize).sum();
        let places: [usize; 3] = [problems.iter().map(|p| p.1.len()).sum(), problems.iter().step_by(2).map(|p| p.1.len()).sum(), problems.iter().skip(1).step_by(2).map(|p| p.1.len()).sum()];
        for (file, counted) in [("RING.tsv", places), ("RING_STOP.tsv", [4, 2, 2])] {
            let text = std::fs::read_to_string(dir.join("OUT").join(file)).unwrap();
            assert_eq!(text.lines().count(), 1 + 3 * residues * a, "{file}");
            for (set, name) in ["held", "train_even", "train_odd"].iter().enumerate() {
                for (ring, _, _, _) in RINGS {
                    let n: usize = text.lines().skip(1).map(|l| l.split('\t').collect::<Vec<_>>()).filter(|c| c[0] == *name && c[1] == ring).map(|c| c[5].parse::<usize>().unwrap()).sum();
                    assert_eq!(n, counted[set], "{file} {name} {ring}");
                }
            }
        }
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// [theory, November 10 01:21] `exchange-held-field` starts from the held file's own answers: its start (`HELD.tsv`) is each
    /// reference as written, and the walk from it holds each answer's letters.
    #[test]
    fn the_walk_from_held_starts_at_the_references_and_holds_their_letters() {
        let dir = std::env::temp_dir().join(format!("holonics-exchange-held-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("dir");
        let put = |name: &str, bytes: &[u8]| {
            std::fs::write(dir.join(name), bytes).expect("write");
            (dir.join(name).to_string_lossy().into_owned(), sha256(bytes).expect("sha"))
        };
        let (codec, problems) = toy();
        let learner = toy_learner(&codec, &problems);
        let (state, state_sha) = put("STATE", learner.to_text().as_bytes());
        let (codec_path, codec_sha) = put("CODEC", codec.to_text().as_bytes());
        let (units, units_sha) = put("UNITS", b"founded-units-v1 0\n");
        let (held, held_sha) = put("HELD", TOY);
        let out = dir.join("OUT").to_string_lossy().into_owned();
        let args: Vec<String> = ["exchange-held-field", &state, &state_sha, &codec_path, &codec_sha, &units, &units_sha, &held, &held_sha, "2", "0", "64", "2", &out].iter().map(|s| s.to_string()).collect();
        exchange_held_field(&args, &mut HostField).unwrap();
        let start = std::fs::read_to_string(dir.join("OUT/HELD.tsv")).unwrap();
        let end = std::fs::read_to_string(dir.join("OUT/SAMPLE.tsv")).unwrap();
        let raw = problems_of(TOY);
        assert_eq!((start.lines().count(), end.lines().count()), (2, 2));
        let sorted = |l: &str| {
            let mut b = l.as_bytes().to_vec();
            b.sort_unstable();
            b
        };
        for (k, (s_line, e_line)) in start.lines().zip(end.lines()).enumerate() {
            assert_eq!(s_line, format!("{k}\t{}", escaped(&raw[k].1)), "problem {k} starts at its reference");
            assert_eq!(sorted(s_line), sorted(e_line), "problem {k}: the walk holds the answer's letters");
        }
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// [census 2b, November 9 23:30] A section's code read from its faces ([`section_code`]) is the code and the sites its deposit
    /// reads ([`FieldLearner::section_realized`]'s `code_before`), on a section of members and openings (ports at their boundary),
    /// the ports' part among it.
    #[test]
    fn a_sections_code_from_its_faces_is_its_deposits() {
        let (codec, problems) = toy();
        let mut learner = toy_learner(&codec, &problems);
        let members: Vec<usize> = (0..problems.len()).collect();
        let paths: Vec<usize> = members.iter().rev().copied().collect();
        let mut draw = 0u64;
        let (regions, _) = section_regions(&codec, &problems, &members, &paths, 9, &mut draw, &mut learner, &mut HostField).unwrap();
        let views = views_of(&regions);
        assert!(views.iter().any(|r| r.port.is_some()) && views.iter().any(|r| r.domain.is_some()));
        let faces = HostField.read_faces(&learner.field, &views).unwrap();
        let (code, sites, ported) = section_code(&faces, &views).unwrap();
        let receipt = learner.section_realized(&views, &mut HostField).unwrap();
        assert_eq!((code, sites), (receipt.code_before, receipt.sites));
        assert!(ported != 0 && ported != code, "the ports' part {ported} of {code}");
    }

    /// [§16.32] A state's weighed domain is `⌊2√(mK)⌋`: its weight `domain/K` is `2√(m/K)`, the importance ratio `2√τ` of
    /// the density `τ = u²` read at `τ = K/m` times the joint code's `m/K`.
    #[test]
    fn a_state_is_weighed_back_to_the_joint_code() {
        let mask = |k: usize, m: usize| (0..m).map(|t| t < k).collect::<Vec<bool>>();
        assert_eq!(weighed_domain(100, &mask(25, 100)), 100, "2√(100·25) = 100: a quarter open weighs 4 = 2√4");
        assert_eq!(weighed_domain(100, &mask(100, 100)), 200, "every site open weighs 2, the ratio 2√1");
        assert_eq!(weighed_domain(64, &mask(1, 64)), 16, "one of 64 open weighs 16 = 2√64");
        assert_eq!(weighed_domain(10, &mask(0, 10)), 6, "an empty mask is read as one open");
    }

    /// Both shapes open a site; a whole-region mask may open the question, an answer mask never does, and each opens
    /// its domain's sites exactly where the draw's keyed site falls below its density `τ`.
    #[test]
    fn shapes_open_a_site_and_meet_both_halves() {
        let (question, sites) = (3usize, 40usize);
        let (mut masked, mut answers, mut asked) = (0, 0, 0);
        for draw in 0..2048u64 {
            let u = ((mix(7, draw) >> 1) & 0xFFFF) + 1;
            let tau = ((u * u) >> 16).max(1);
            let keyed = |t: usize| (mix(7, draw ^ ((t as u64 + 1) << 32)) & 0xFFFF) < tau;
            let (open, from) = match shape(7, draw, question, sites) {
                Shape::Masked(m) => {
                    masked += 1;
                    asked += usize::from(m[..question].iter().any(|&u| u));
                    (m, 0)
                }
                Shape::Answer(m) => {
                    answers += 1;
                    assert!(m[..question].iter().all(|&u| !u), "the question is known");
                    (m, question)
                }
            };
            assert_eq!(open.len(), sites);
            assert!(open.iter().any(|&u| u));
            if (from..sites).any(keyed) {
                for t in from..sites {
                    assert_eq!(open[t], keyed(t), "site {t} of draw {draw}");
                }
            }
        }
        assert!(masked > 512 && answers > 512 && asked > 256, "{masked} {answers} {asked}");
    }

    const TOY: &[u8] = b"Tom has 3 apples and buys 2 more. How many apples does he have?\nHe has <<3+2=5>>5 apples.\n#### 5\n\nTom has 7 apples and buys 1 more. How many apples does he have?\nHe has <<7+1=8>>8 apples.\n#### 8\n\nTom has 4 apples and buys 6 more. How many apples does he have?\nHe has <<4+6=10>>10 apples.\n#### 10\n\nTom has 9 apples and buys 0 more. How many apples does he have?\nHe has <<9+0=9>>9 apples.\n#### 9\n";

    fn toy() -> (FieldCodec, Problems) {
        let raw = problems_of(TOY);
        let codec = FieldCodec::found(Units::bytes(), &raw).unwrap();
        let problems: Problems = raw.iter().map(|(q, a)| (codec.encode(&question_text(q)).unwrap(), codec.encode(a).unwrap(), a.len())).collect();
        (codec, problems)
    }

    fn toy_learner(codec: &FieldCodec, problems: &Problems) -> FieldLearner {
        let reach = problems.iter().map(|(q, _, _)| q.len() + codec.answer).max().unwrap();
        let d = FieldDeclaration { alphabet: codec.alphabet(), width: 8, heads: 2, modes: 3, still: 1, contacts: 4, ticks: 2, frames: 2, reach, lanes: 1, depth: 0, energy: false };
        let keys: Vec<u8> = (0..1u64 << 13).flat_map(|i| mix(0x5EED, i).to_be_bytes()).collect();
        FieldLearner::new(Field::found(d, &keys).unwrap(), 4)
    }

    /// [measurement; theory, November 8, the lead reading] `lead-field` end to end on the host: an energy field of two lanes,
    /// every family drawn from the key stream (a founding holds the lift and the moment's chart at zero, where the angle and
    /// the ratio read nothing) and its clocks plain, reads its lead at six held places (one a problem, then two drawn by
    /// letter), one row a lane a place whose readings (the relaxed cosine, the ratio, `c_open` and `c_EE`) are its sums', each
    /// place's sums the host's own `Field::energy_lead` at its truth; and a field without one energy is refused. The quartiles
    /// are the nearest ranks.
    #[test]
    fn the_lead_reading_reads_every_held_place_and_lane() {
        assert_eq!(rank_quartiles(vec![4, 1, 3, 2]), Some((1, 2, 3)));
        assert_eq!(rank_quartiles(vec![7]), Some((7, 7, 7)));
        assert_eq!(rank_quartiles::<i64>(Vec::new()), None);
        let dir = std::env::temp_dir().join(format!("holonics-lead-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("dir");
        let at = |name: &str| dir.join(name).to_string_lossy().into_owned();
        let put = |name: &str, bytes: &[u8]| {
            std::fs::write(dir.join(name), bytes).expect("write");
            (at(name), sha256(bytes).expect("sha"))
        };
        let (codec, problems) = toy();
        let reach = problems.iter().map(|(q, _, _)| q.len() + codec.answer).max().unwrap();
        let d = FieldDeclaration { alphabet: codec.alphabet(), width: 8, heads: 2, modes: 3, still: 1, contacts: 4, ticks: 2, frames: 2, reach, lanes: 2, depth: 0, energy: true };
        let keys: Vec<u8> = (0..1u64 << 13).flat_map(|i| mix(0x5EED, i).to_be_bytes()).collect();
        let mut field = Field::found(d, &keys).unwrap();
        let families = field.layout().families.clone();
        for (n, v) in field.theta.iter_mut().enumerate() {
            let k = mix(0x1EAD, n as u64) as u32 as i32 as i64;
            let grain = families.iter().find(|(s, l, _)| (*s..*s + *l).contains(&n)).unwrap().2;
            *v = ((k << grain) >> 32) as i32;
        }
        let l = field.layout().clone();
        field.theta[l.pace..l.pace + d.paced_heads() * (d.alphabet + 1)].fill(0);
        let learner = FieldLearner::new(field, 4);
        let plain = FieldLearner::new(Field::found(FieldDeclaration { energy: false, ..d }, &keys).unwrap(), 4);
        let (state, state_sha) = put("STATE", learner.to_text().as_bytes());
        let (other, other_sha) = put("PLAIN", plain.to_text().as_bytes());
        let (codec_at, codec_sha) = put("CODEC", codec.to_text().as_bytes());
        let (units, units_sha) = put("UNITS", b"founded-units-v1 0\n");
        let (held, held_sha) = put("HELD", TOY);
        let args = |state: &str, sha: &str, out: &str| -> Vec<String> { ["lead-field", state, sha, &codec_at, &codec_sha, &units, &units_sha, &held, &held_sha, "6", out].iter().map(|s| s.to_string()).collect() };
        lead_field(&args(&state, &state_sha, &at("L")), &mut host()).expect("lead");
        let rows = String::from_utf8(std::fs::read(dir.join("L/LEAD.tsv")).expect("rows")).unwrap();
        let rows: Vec<Vec<String>> = rows.lines().skip(1).map(|l| l.split('\t').map(str::to_string).collect()).collect();
        assert_eq!(rows.len(), 6 * 2, "a row a lane a place");
        let held_set = encoded_problems(&codec, &problems_of(TOY), &learner.field).unwrap();
        let void = codec.void();
        let truth_of = |p: &(Vec<usize>, Vec<usize>, usize), letters: &[usize]| truth_with_voids(void, p, letters);
        for (n, (_, truth, t, _)) in enumerated_places(&held_set, 6, &truth_of).iter().enumerate() {
            let lead = learner.field.energy_lead(truth, *t).unwrap();
            for lane in 0..2 {
                let cells = &rows[2 * n + lane];
                let ((dot, rr, oo), (ll, mm)) = (lead.own[lane], lead.opening[lane]);
                assert_eq!(cells[3..8], [dot.to_string(), rr.to_string(), oo.to_string(), ll.to_string(), mm.to_string()], "place {n}, lane {lane}");
                let cos: i64 = cells[8].parse().expect("a lane whose rows are not zero");
                let ratio: u128 = cells[9].parse().expect("a lane whose moment's term is not zero");
                assert!((-1000..=1000).contains(&cos) && Some(cos) == lead.cos_milli(Some(lane)) && Some(ratio) == lead.ratio_milli(Some(lane)), "place {n}, lane {lane}: {cos} {ratio}");
                let ((xo, xx), (eo, ee)) = (lead.open[lane], lead.enc[lane]);
                assert_eq!(cells[10..14], [xo.to_string(), xx.to_string(), eo.to_string(), ee.to_string()], "place {n}, lane {lane}: the opening's sums");
                let (c_open, c_ee): (i64, i64) = (cells[14].parse().expect("an opening lane not at zero"), cells[15].parse().expect("an own term not at zero"));
                assert!((-1000..=1000).contains(&c_open) && (-1000..=1000).contains(&c_ee), "place {n}, lane {lane}: {c_open} {c_ee}");
                assert_eq!((Some(c_open), Some(c_ee)), (lead.cos_open_milli(Some(lane)), lead.cos_ee_milli(Some(lane))), "place {n}, lane {lane}");
            }
        }
        assert!(lead_field(&args(&other, &other_sha, &at("P")), &mut host()).is_err(), "a field without one energy");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// [measurement; theory, November 9 09:34 and 09:42, the word reading] `word-field` end to end on the host: an energy field
    /// whose families are drawn from the key stream reads six held places' truths. `WORDS.tsv` holds a row a site read, head,
    /// mode and kind, each word the host's own `Field::energy_opening_words`, its trit `shell`'s, its band the nearest
    /// thousandth of `|re² − im²|/(re² + im²)`, `inside` the near-cone test read here from its definition at the row's `ε`
    /// (`band_bits(b)`); `KEYS.tsv` a row every site, head and mode; no other file is written. The band's half-width in phase is
    /// `½ arcsin ε` (45°, 15°, 7.239° and 3.590° for `k = 0..3`); the state is read, never written; and a field without one
    /// energy is refused.
    #[test]
    fn the_word_reading_reads_every_site_head_mode_and_kind() {
        use holonics::hnn::tower::field::{band_bits, shell};
        assert_eq!(band_half_width(0), (785_398, 45_000));
        assert_eq!(band_half_width(1), (261_799, 15_000));
        assert_eq!(band_half_width(2), (126_340, 7_239));
        assert_eq!(band_half_width(3), (62_664, 3_590));
        let dir = std::env::temp_dir().join(format!("holonics-words-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("dir");
        let at = |name: &str| dir.join(name).to_string_lossy().into_owned();
        let put = |name: &str, bytes: &[u8]| {
            std::fs::write(dir.join(name), bytes).expect("write");
            (at(name), sha256(bytes).expect("sha"))
        };
        let (codec, problems) = toy();
        let reach = problems.iter().map(|(q, _, _)| q.len() + codec.answer).max().unwrap();
        let d = FieldDeclaration { alphabet: codec.alphabet(), width: 8, heads: 2, modes: 5, still: 1, contacts: 4, ticks: 2, frames: 2, reach, lanes: 1, depth: 0, energy: true };
        let keys: Vec<u8> = (0..1u64 << 13).flat_map(|i| mix(0x5EED, i).to_be_bytes()).collect();
        let mut field = Field::found(d, &keys).unwrap();
        let families = field.layout().families.clone();
        for (n, v) in field.theta.iter_mut().enumerate() {
            let k = mix(0x30BD, n as u64) as u32 as i32 as i64;
            let grain = families.iter().find(|(s, l, _)| (*s..*s + *l).contains(&n)).unwrap().2;
            *v = ((k << grain) >> 32) as i32;
        }
        let l = field.layout().clone();
        field.theta[l.pace..l.pace + d.paced_heads() * (d.alphabet + 1)].fill(0);
        let plain = FieldLearner::new(Field::found(FieldDeclaration { energy: false, ..d }, &keys).unwrap(), 4);
        let (other, other_sha) = put("PLAIN", plain.to_text().as_bytes());
        let (codec_at, codec_sha) = put("CODEC", codec.to_text().as_bytes());
        let (units, units_sha) = put("UNITS", b"founded-units-v1 0\n");
        let (held, held_sha) = put("HELD", TOY);
        let args = |state: &str, sha: &str, out: &str| -> Vec<String> { ["word-field", state, sha, &codec_at, &codec_sha, &units, &units_sha, &held, &held_sha, "6", out].iter().map(|s| s.to_string()).collect() };
        let read_rows = |out: &str, name: &str| -> Vec<String> { String::from_utf8(std::fs::read(dir.join(out).join(name)).expect("rows")).unwrap().lines().skip(1).map(str::to_string).collect() };
        let (n, m, b) = (d.modes, d.complex(), d.class_trits());
        let k = band_bits(b);
        let band = |re: i64, im: i64| -> String {
            let (rr, ii) = (re as i128 * re as i128, im as i128 * im as i128);
            if rr + ii == 0 { "-".to_string() } else { ((2000 * (rr - ii).abs() + rr + ii) / (2 * (rr + ii))).to_string() }
        };
        let near = |re: i64, im: i64| {
            let (rr, ii) = (re as i128 * re as i128, im as i128 * im as i128);
            rr + ii > 0 && ((rr - ii).abs() << k) < rr + ii
        };
        let mut inside_any = false;
        let learner = FieldLearner::new(field, 4);
        let text = learner.to_text();
        let (state, state_sha) = put("STATE", text.as_bytes());
        word_field(&args(&state, &state_sha, &at("OUT")), &mut host()).expect("words");
        assert_eq!(std::fs::read(dir.join("STATE")).expect("state"), text.as_bytes(), "the state is read, never written");
        let held_set = encoded_problems(&codec, &problems_of(TOY), &learner.field).unwrap();
        let void = codec.void();
        let truth_of = |p: &(Vec<usize>, Vec<usize>, usize), letters: &[usize]| truth_with_voids(void, p, letters);
        let (mut words, mut key_rows) = (Vec::new(), Vec::new());
        for (problem, truth, t, q) in &enumerated_places(&held_set, 6, &truth_of) {
            let read = learner.field.energy_opening_words(truth, *t).unwrap();
            for (i, &s) in read.sites.iter().enumerate() {
                for h in 0..d.heads {
                    for li in 0..n {
                        for (kind, word) in [("key", &read.keys[s]), ("probe", &read.probes[i])] {
                            let (re, im) = (word[h * n + li], word[m + h * n + li]);
                            inside_any |= near(re, im);
                            words.push(format!("{problem}\t{}\t{}\t{h}\t{li}\t{kind}\t{re}\t{im}\t{}\t{}\t{}\t{}\t{k}", t - q, s as i64 - *t as i64, shell(re, im), band(re, im), u8::from(near(re, im)), u8::from(li < b)));
                        }
                    }
                }
            }
            for (s, word) in read.keys.iter().enumerate() {
                for h in 0..d.heads {
                    for li in 0..n {
                        let (re, im) = (word[h * n + li], word[m + h * n + li]);
                        key_rows.push(format!("{problem}\t{}\t{s}\t{h}\t{li}\t{re}\t{im}\t{}\t{}", t - q, shell(re, im), band(re, im)));
                    }
                }
            }
        }
        assert_eq!(read_rows("OUT", "WORDS.tsv"), words, "the host's own words, trits, bands and the near-cone test");
        assert_eq!(read_rows("OUT", "KEYS.tsv"), key_rows, "every site's key words");
        let mut written: Vec<String> = std::fs::read_dir(dir.join("OUT")).expect("out").map(|e| e.expect("entry").file_name().to_string_lossy().into_owned()).collect();
        written.sort();
        assert_eq!(written, ["KEYS.tsv", "WORDS.tsv"], "the words and the keys alone");
        assert!(inside_any, "some mode lies inside its band (else the column reads nothing)");
        assert!(word_field(&args(&other, &other_sha, &at("P")), &mut host()).is_err(), "a field without one energy");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// [measurement; theory, November 9 08:13 and 08:15, the held-under reading] `held-under` end to end on the host: an
    /// energy field whose families are drawn from the key stream reads six held places under itself, and in either hold its
    /// `ENUMERATED.tsv` is the plain held read's (`lap` −1) row for row; under a base whose key chart is negated, the rows'
    /// energies are the host's own `Field::energy_g_under` under that base and some move, while every face stays the state's;
    /// the states are read, never written; a base of another declaration and an undeclared hold are refused.
    #[test]
    fn the_held_under_reading_is_the_held_read_under_itself() {
        use holonics::hnn::tower::field::BaseHold;
        let dir = std::env::temp_dir().join(format!("holonics-under-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("dir");
        let at = |name: &str| dir.join(name).to_string_lossy().into_owned();
        let put = |name: &str, bytes: &[u8]| {
            std::fs::write(dir.join(name), bytes).expect("write");
            (at(name), sha256(bytes).expect("sha"))
        };
        let (codec, problems) = toy();
        let reach = problems.iter().map(|(q, _, _)| q.len() + codec.answer).max().unwrap();
        let d = FieldDeclaration { alphabet: codec.alphabet(), width: 8, heads: 2, modes: 3, still: 1, contacts: 4, ticks: 2, frames: 2, reach, lanes: 1, depth: 0, energy: true };
        let keys: Vec<u8> = (0..1u64 << 13).flat_map(|i| mix(0x5EED, i).to_be_bytes()).collect();
        let mut field = Field::found(d, &keys).unwrap();
        let families = field.layout().families.clone();
        for (n, v) in field.theta.iter_mut().enumerate() {
            let k = mix(0x0DE5, n as u64) as u32 as i32 as i64;
            let grain = families.iter().find(|(s, l, _)| (*s..*s + *l).contains(&n)).unwrap().2;
            *v = ((k << grain) >> 32) as i32;
        }
        let l = field.layout().clone();
        field.theta[l.pace..l.pace + d.paced_heads() * (d.alphabet + 1)].fill(0);
        let mut keyed = field.clone();
        for v in &mut keyed.theta[l.q..l.q + 2 * d.complex() * d.width] {
            *v = v.wrapping_neg();
        }
        let (learner, base) = (FieldLearner::new(field, 4), FieldLearner::new(keyed, 4));
        let plain = FieldLearner::new(Field::found(FieldDeclaration { energy: false, ..d }, &keys).unwrap(), 4);
        let text = learner.to_text();
        let (state, state_sha) = put("STATE", text.as_bytes());
        let (other, other_sha) = put("BASE", base.to_text().as_bytes());
        let (plain_at, plain_sha) = put("PLAIN", plain.to_text().as_bytes());
        let (codec_at, codec_sha) = put("CODEC", codec.to_text().as_bytes());
        let (units, units_sha) = put("UNITS", b"founded-units-v1 0\n");
        let (held, held_sha) = put("HELD", TOY);
        let args = |base: &str, base_sha: &str, out: &str, hold: &str| -> Vec<String> {
            ["held-under", base, base_sha, &state, &state_sha, &codec_at, &codec_sha, &units, &units_sha, &held, &held_sha, "6", out, hold].iter().map(|s| s.to_string()).collect()
        };
        let read_rows = |out: &str| -> Vec<String> { String::from_utf8(std::fs::read(dir.join(out).join("ENUMERATED.tsv")).expect("rows")).unwrap().lines().skip(1).map(str::to_string).collect() };
        let held_set = encoded_problems(&codec, &problems_of(TOY), &learner.field).unwrap();
        let void = codec.void();
        let truth_of = |p: &(Vec<usize>, Vec<usize>, usize), letters: &[usize]| truth_with_voids(void, p, letters);
        let chosen = enumerated_places(&held_set, 6, &truth_of);
        let expected: Vec<String> = enumerated_rows(&learner.field, &chosen, &mut host(), -1).unwrap().iter().map(|r| r.trim_end().to_string()).collect();
        for hold in ["classes", "classes+halvings"] {
            let out = format!("S{}", hold.len());
            held_under(&args(&state, &state_sha, &at(&out), hold), &mut host()).expect("under itself");
            assert_eq!(read_rows(&out), expected, "{hold}: under itself, the plain held read");
            let out = format!("K{}", hold.len());
            held_under(&args(&other, &other_sha, &at(&out), hold), &mut host()).expect("under the keyed base");
            let rows = read_rows(&out);
            assert_eq!(rows.len(), expected.len(), "{hold}: a row a place");
            let mut moved = false;
            for ((cells, plain_cells), (_, truth, t, _)) in rows.iter().zip(&expected).zip(&chosen) {
                let (cells, plain_cells): (Vec<&str>, Vec<&str>) = (cells.split('\t').collect(), plain_cells.split('\t').collect());
                assert_eq!((&cells[..7], &cells[8..]), (&plain_cells[..7], &plain_cells[8..]), "{hold}: the faces are the state's own");
                let g: Vec<String> = (0..d.alphabet)
                    .map(|c| {
                        let mut x = truth.clone();
                        x[*t] = c;
                        learner.field.energy_g_under(&base.field, &x, BaseHold::of(hold).unwrap()).unwrap().to_string()
                    })
                    .collect();
                assert_eq!(cells[7], g.join(","), "{hold}: the energies under the base");
                moved |= cells[7] != plain_cells[7];
            }
            assert!(moved, "{hold}: a base whose keys turn moves some energy");
        }
        assert_eq!(std::fs::read(dir.join("STATE")).expect("state"), text.as_bytes(), "the state is read, never written");
        assert!(held_under(&args(&plain_at, &plain_sha, &at("P"), "classes"), &mut host()).is_err(), "a base of another declaration");
        assert!(held_under(&args(&state, &state_sha, &at("H"), "halvings"), &mut host()).is_err(), "an undeclared hold");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// [measurement; theory, November 9, the class reading] `class-field` end to end on the host: an energy field whose families
    /// are drawn from the key stream and whose clocks are plain reads six held places (one a problem, then two drawn by
    /// letter), every letter of the alphabet at each with the rest at the truth; `CLASSES.tsv` holds a row a configuration,
    /// site read and head, each the host's own `Field::energy_held_classes` (its classes, its support's size, word and far
    /// offsets from the place), and `HALVINGS.tsv` a row a configuration, its standing ticks' halvings and `G`; the support's
    /// word is FNV-1a's; the state is read, never written; and a field without one energy is refused.
    #[test]
    fn the_class_reading_reads_every_letter_site_and_head() {
        use holonics::hnn::tower::field::NEAR;
        assert_eq!(support_word(&[]), 0xcbf2_9ce4_8422_2325);
        assert_eq!(support_word(&[1]), (0..8).fold(0xcbf2_9ce4_8422_2325u64, |h, k| (h ^ u64::from(u8::from(k == 0))).wrapping_mul(0x100_0000_01b3)));
        assert_ne!(support_word(&[-1, 2]), support_word(&[2, -1]), "the word reads the order it is given (the offsets are sorted first)");
        let dir = std::env::temp_dir().join(format!("holonics-class-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("dir");
        let at = |name: &str| dir.join(name).to_string_lossy().into_owned();
        let put = |name: &str, bytes: &[u8]| {
            std::fs::write(dir.join(name), bytes).expect("write");
            (at(name), sha256(bytes).expect("sha"))
        };
        let (codec, problems) = toy();
        let reach = problems.iter().map(|(q, _, _)| q.len() + codec.answer).max().unwrap();
        let d = FieldDeclaration { alphabet: codec.alphabet(), width: 8, heads: 2, modes: 3, still: 1, contacts: 4, ticks: 2, frames: 2, reach, lanes: 1, depth: 0, energy: true };
        let keys: Vec<u8> = (0..1u64 << 13).flat_map(|i| mix(0x5EED, i).to_be_bytes()).collect();
        let mut field = Field::found(d, &keys).unwrap();
        let families = field.layout().families.clone();
        for (n, v) in field.theta.iter_mut().enumerate() {
            let k = mix(0xC1A5, n as u64) as u32 as i32 as i64;
            let grain = families.iter().find(|(s, l, _)| (*s..*s + *l).contains(&n)).unwrap().2;
            *v = ((k << grain) >> 32) as i32;
        }
        let l = field.layout().clone();
        field.theta[l.pace..l.pace + d.paced_heads() * (d.alphabet + 1)].fill(0);
        let learner = FieldLearner::new(field, 4);
        let plain = FieldLearner::new(Field::found(FieldDeclaration { energy: false, ..d }, &keys).unwrap(), 4);
        let text = learner.to_text();
        let (state, state_sha) = put("STATE", text.as_bytes());
        let (other, other_sha) = put("PLAIN", plain.to_text().as_bytes());
        let (codec_at, codec_sha) = put("CODEC", codec.to_text().as_bytes());
        let (units, units_sha) = put("UNITS", b"founded-units-v1 0\n");
        let (held, held_sha) = put("HELD", TOY);
        let args = |state: &str, sha: &str, out: &str| -> Vec<String> { ["class-field", state, sha, &codec_at, &codec_sha, &units, &units_sha, &held, &held_sha, "6", out].iter().map(|s| s.to_string()).collect() };
        class_field(&args(&state, &state_sha, &at("C")), &mut host()).expect("class");
        assert_eq!(std::fs::read(dir.join("STATE")).expect("state"), text.as_bytes(), "the state is read, never written");
        let read_rows = |name: &str| -> Vec<String> { String::from_utf8(std::fs::read(dir.join("C").join(name)).expect("rows")).unwrap().lines().skip(1).map(str::to_string).collect() };
        let (classes, halvings) = (read_rows("CLASSES.tsv"), read_rows("HALVINGS.tsv"));
        let held_set = encoded_problems(&codec, &problems_of(TOY), &learner.field).unwrap();
        let void = codec.void();
        let truth_of = |p: &(Vec<usize>, Vec<usize>, usize), letters: &[usize]| truth_with_voids(void, p, letters);
        let chosen = enumerated_places(&held_set, 6, &truth_of);
        let (mut expected, mut expected_halvings) = (Vec::new(), Vec::new());
        for (k, truth, t, q) in &chosen {
            for c in 0..d.alphabet {
                let mut x = truth.clone();
                x[*t] = c;
                let read = learner.field.energy_held_classes(&x, *t).unwrap();
                for (i, &s) in read.sites.iter().enumerate() {
                    for h in 0..d.heads {
                        let row = &read.heads[h][i];
                        let offsets: Vec<i64> = row.support.iter().map(|&j| j as i64 - *t as i64).collect();
                        let far: Vec<String> = row.support.iter().filter(|&&j| (j as usize).abs_diff(s) >= NEAR).map(|&j| (j as i64 - *t as i64).to_string()).collect();
                        let far = if far.is_empty() { "-".to_string() } else { far.join(",") };
                        expected.push(format!("{k}\t{}\t{c}\t{}\t{h}\t{}\t{}\t{}\t{:016x}\t{far}", t - q, s as i64 - *t as i64, row.class, row.probe_class, offsets.len(), support_word(&offsets)));
                    }
                }
                let stood: Vec<String> = read.read.halvings.iter().flatten().map(u32::to_string).collect();
                let list = if stood.is_empty() { "-".to_string() } else { stood.join(",") };
                expected_halvings.push(format!("{k}\t{}\t{c}\t{}\t{}\t{list}\t{}", t - q, stood.len(), u8::from(read.read.halvings.iter().any(Option::is_none)), learner.field.energy_g(&x).unwrap()));
            }
        }
        assert!(classes.len() >= 6 * d.alphabet * 2 * d.heads && halvings.len() == 6 * d.alphabet, "a row a configuration, site and head; a row a configuration");
        assert_eq!(classes, expected, "the host's own held classes");
        assert_eq!(halvings, expected_halvings, "the host's own descent and G");
        assert!(classes.iter().any(|r| r.split('\t').nth(9) != Some("-")), "some row hears a source past its near field");
        assert!(class_field(&args(&other, &other_sha, &at("P")), &mut host()).is_err(), "a field without one energy");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// [measurement; theory, November 8, the line reading] `line-field` end to end on the host: an energy field whose moments
    /// one conditional section opened (each family at its own length) is read at its live `θ` and at five lengths along each
    /// direction, eleven points of six held places; each point's place codes are the conditional chart's over the host's own
    /// energies at that point (the `mv` point at `η = 1` the line's first point along the deposit's step), every point's held
    /// rows are written beside them, and the state is read, never written.
    #[test]
    fn the_line_reading_reads_every_point_and_writes_no_state() {
        use holonics::hnn::tower::field::{conditional_code, line_point};
        let dir = std::env::temp_dir().join(format!("holonics-line-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("dir");
        let at = |name: &str| dir.join(name).to_string_lossy().into_owned();
        let put = |name: &str, bytes: &[u8]| {
            std::fs::write(dir.join(name), bytes).expect("write");
            (at(name), sha256(bytes).expect("sha"))
        };
        let (codec, problems) = toy();
        let reach = problems.iter().map(|(q, _, _)| q.len() + codec.answer).max().unwrap();
        let d = FieldDeclaration { alphabet: codec.alphabet(), width: 8, heads: 2, modes: 3, still: 1, contacts: 4, ticks: 2, frames: 2, reach, lanes: 1, depth: 0, energy: true };
        let keys: Vec<u8> = (0..1u64 << 13).flat_map(|i| mix(0x5EED, i).to_be_bytes()).collect();
        let mut field = Field::found(d, &keys).unwrap();
        let families = field.layout().families.clone();
        for (n, v) in field.theta.iter_mut().enumerate() {
            let k = mix(0x11E5, n as u64) as u32 as i32 as i64;
            let grain = families.iter().find(|(s, l, _)| (*s..*s + *l).contains(&n)).unwrap().2;
            *v = ((k << grain) >> 32) as i32;
        }
        let l = field.layout().clone();
        field.theta[l.pace..l.pace + d.paced_heads() * (d.alphabet + 1)].fill(0);
        let mut learner = FieldLearner::new(field, 14);
        learner.open_family_rates();
        let held_set = encoded_problems(&codec, &problems_of(TOY), &learner.field).unwrap();
        let void = codec.void();
        let truth_of = |p: &(Vec<usize>, Vec<usize>, usize), letters: &[usize]| truth_with_voids(void, p, letters);
        let truths: Vec<Vec<usize>> = held_set.iter().map(|p| truth_of(p, &p.1)).collect();
        let resolved: Vec<Vec<bool>> = truths.iter().map(|t| vec![false; t.len()]).collect();
        let views: Vec<Region> = truths.iter().zip(&resolved).map(|(c, u)| Region { classes: c, unresolved: u, faces: &[], locked: &[], echo: &[], domain: None, port: None }).collect();
        let blocks: Vec<Vec<usize>> = held_set.iter().map(|p| vec![p.0.len(), p.0.len() + 1]).collect();
        let owners: Vec<usize> = (0..held_set.len()).collect();
        learner.section_conditional(&views, &owners, &blocks, &mut host()).expect("a section opens the moments");
        let text = learner.to_text();
        let (state, state_sha) = put("STATE", text.as_bytes());
        let (codec_at, codec_sha) = put("CODEC", codec.to_text().as_bytes());
        let (units, units_sha) = put("UNITS", b"founded-units-v1 0\n");
        let (held, held_sha) = put("HELD", TOY);
        let args: Vec<String> = ["line-field", &state, &state_sha, &codec_at, &codec_sha, &units, &units_sha, &held, &held_sha, "6", &at("L")].iter().map(|s| s.to_string()).collect();
        line_field(&args, &mut host()).expect("line");
        assert_eq!(std::fs::read(dir.join("STATE")).expect("state"), text.as_bytes(), "the state is read, never written");
        let chosen = enumerated_places(&held_set, 6, &truth_of);
        let directions = learner.line_directions().unwrap();
        let alphabet = d.alphabet;
        let points: Vec<(&str, u32, holonics::hnn::tower::field::Field)> = std::iter::once(("none", 0, learner.field.clone()))
            .chain(LINE_ETAS.iter().map(|&e| ("m", e, line_point(&learner.field, &directions.first, e).unwrap().0)))
            .chain(LINE_ETAS.iter().map(|&e| ("mv", e, line_point(&learner.field, &directions.step, e).unwrap().0)))
            .collect();
        assert!(points[6].2.theta != learner.field.theta, "the deposit's step moves θ at η = 1");
        for (direction, eta, point) in &points {
            let rows = String::from_utf8(std::fs::read(dir.join(format!("L/LINE.{direction}.{eta}.tsv"))).expect("a point's codes")).unwrap();
            let rows: Vec<&str> = rows.lines().skip(1).collect();
            assert_eq!(rows.len(), 6, "{direction} {eta}: a row a place");
            for ((k, truth, t, q), cells) in chosen.iter().zip(&rows) {
                let g: Vec<i128> = (0..alphabet)
                    .map(|c| {
                        let mut x = truth.clone();
                        x[*t] = c;
                        point.energy_g(&x).unwrap()
                    })
                    .collect();
                let nats = conditional_code(point, &g, truth[*t]).unwrap() * LN2_Q30 >> 30;
                assert_eq!(*cells, format!("{k}\t{}\t{}", t - q, nats * 1_000_000 >> 32), "{direction} {eta}, problem {k}");
            }
        }
        let enumerated = String::from_utf8(std::fs::read(dir.join("L/ENUMERATED.tsv")).expect("rows")).unwrap();
        assert_eq!(enumerated.lines().count(), 1 + 11 * 6, "the held read's rows, a point's six places each");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// [measurement; theory, November 9 05:31] `contrast-covector-field` end to end on the host: three of the toy's four
    /// problems chosen at the middles of three equal parts (indices 0, 2, 3), their writes started at the truths and swept
    /// twice at the live `θ`'s `T` in one batch ordered by answer length, keyed as the trainer keys section 0; each row of
    /// `CONTRAST_COVECTOR.tsv` is `⟨g_f(p), Σ_other g_f⟩` and `‖g_f(p)‖²` over the contrast's pair covectors of those
    /// writes, formed here in unbounded integers; more problems than the file holds are refused; the state is read, never
    /// written.
    #[test]
    fn the_contrast_covector_reading_reads_the_fresh_writes_pairs() {
        use holonics::hnn::tower::field::contrast_pair_covectors;
        use num_bigint::BigInt;
        let dir = std::env::temp_dir().join(format!("holonics-contrast-covector-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("dir");
        let at = |name: &str| dir.join(name).to_string_lossy().into_owned();
        let put = |name: &str, bytes: &[u8]| {
            std::fs::write(dir.join(name), bytes).expect("write");
            (at(name), sha256(bytes).expect("sha"))
        };
        let (codec, problems) = toy();
        let reach = problems.iter().map(|(q, _, _)| q.len() + codec.answer).max().unwrap();
        let d = FieldDeclaration { alphabet: codec.alphabet(), width: 8, heads: 2, modes: 3, still: 1, contacts: 4, ticks: 2, frames: 2, reach, lanes: 1, depth: 0, energy: true };
        let keys: Vec<u8> = (0..1u64 << 13).flat_map(|i| mix(0x5EED, i).to_be_bytes()).collect();
        let mut field = Field::found(d, &keys).unwrap();
        let families = field.layout().families.clone();
        for (n, v) in field.theta.iter_mut().enumerate() {
            let k = mix(0x11E5, n as u64) as u32 as i32 as i64;
            let grain = families.iter().find(|(s, l, _)| (*s..*s + *l).contains(&n)).unwrap().2;
            *v = ((k << grain) >> 32) as i32;
        }
        let l = field.layout().clone();
        field.theta[l.pace..l.pace + d.paced_heads() * (d.alphabet + 1)].fill(0);
        let learner = FieldLearner::new(field, 14);
        let text = learner.to_text();
        let (state, state_sha) = put("STATE", text.as_bytes());
        let (codec_at, codec_sha) = put("CODEC", codec.to_text().as_bytes());
        let (units, units_sha) = put("UNITS", b"founded-units-v1 0\n");
        let (file, file_sha) = put("PROBLEMS", TOY);
        let args = |count: &str, out: &str| -> Vec<String> { ["contrast-covector-field", &state, &state_sha, &codec_at, &codec_sha, &units, &units_sha, &file, &file_sha, count, "2", &at(out)].iter().map(|s| s.to_string()).collect() };
        assert!(contrast_covector_field(&args("5", "N"), &mut host()).is_err(), "more problems than the file holds");
        contrast_covector_field(&args("3", "C"), &mut host()).expect("contrast covector");
        assert_eq!(std::fs::read(dir.join("STATE")).expect("state"), text.as_bytes(), "the state is read, never written");
        // The reading's problems, batch, writes and pairs, formed here.
        let set = encoded_problems(&codec, &problems_of(TOY), &learner.field).unwrap();
        let chosen = [0usize, 2, 3];
        let mut order: Vec<usize> = (0..3).collect();
        order.sort_by_key(|&c| (set[chosen[c]].1.len(), c));
        let void = codec.void();
        let asked: Vec<(&[usize], usize)> = order.iter().map(|&c| (set[chosen[c]].0.as_slice(), set[chosen[c]].2)).collect();
        let mut active: Vec<Vec<usize>> = order.iter().map(|&c| set[chosen[c]].1.clone()).collect();
        let key = writes_key(contrast_seed(&learner, &state_sha).unwrap(), learner.laps, 0);
        fresh_sweeps_at(&learner.field, &asked, &mut active, 0, 2, key, void, &mut host(), &mut |_, _| Ok(()), &mut |_, _, _, _, _, _| {}).unwrap();
        assert!(order.iter().zip(&active).any(|(&c, w)| w != &set[chosen[c]].1), "the sweeps move some write off its truth");
        let truths: Vec<Vec<usize>> = order.iter().map(|&c| truth_with_voids(void, &set[chosen[c]], &set[chosen[c]].1)).collect();
        let writes: Vec<Vec<usize>> = order.iter().zip(&active).map(|(&c, w)| truth_with_voids(void, &set[chosen[c]], w)).collect();
        let resolved: Vec<Vec<bool>> = truths.iter().map(|t| vec![false; t.len()]).collect();
        let truth_views: Vec<Region> = truths.iter().zip(&resolved).map(|(c, u)| Region { classes: c, unresolved: u, faces: &[], locked: &[], echo: &[], domain: None, port: None }).collect();
        let write_views: Vec<Region> = writes.iter().zip(&resolved).map(|(c, u)| Region { classes: c, unresolved: u, faces: &[], locked: &[], echo: &[], domain: None, port: None }).collect();
        let pairs = contrast_pair_covectors(&learner.field, &truth_views, &write_views, &mut host()).unwrap();
        let mut covectors: Vec<Vec<i128>> = vec![Vec::new(); 3];
        for (&c, pair) in order.iter().zip(pairs) {
            covectors[c] = pair.covector;
        }
        let in_b = [false, true, false];
        let material = learner.field.material_len();
        let half_sum = |b: bool| -> Vec<BigInt> { (0..material).map(|j| (0..3).filter(|&c| in_b[c] == b).map(|c| BigInt::from(covectors[c][j])).sum()).collect() };
        let (sum_a, sum_b) = (half_sum(false), half_sum(true));
        let all_families = learner.field.families_all();
        let names = family_names(&learner.field);
        let rows = String::from_utf8(std::fs::read(dir.join("C/CONTRAST_COVECTOR.tsv")).expect("rows")).unwrap();
        let mut rows = rows.lines().skip(1);
        let mut nonzero = 0;
        for c in 0..3 {
            let (half, other, others) = if in_b[c] { ("b", &sum_a, 2) } else { ("a", &sum_b, 1) };
            for (f, &(start, n, _)) in all_families.iter().enumerate() {
                if n == 0 {
                    continue;
                }
                let dot: BigInt = (start..start + n).map(|j| BigInt::from(covectors[c][j]) * &other[j]).sum();
                let square: BigInt = (start..start + n).map(|j| BigInt::from(covectors[c][j]) * BigInt::from(covectors[c][j])).sum();
                nonzero += usize::from(dot != BigInt::from(0));
                let length = set[chosen[c]].1.len();
                assert_eq!(rows.next(), Some(format!("{}\t{c}\t{half}\t0\t{length}\t{}\t{dot}\t{others}\t{square}", chosen[c], names[f].0).as_str()), "problem {c}, family {f}");
            }
        }
        assert_eq!(rows.next(), None, "a row a problem and family");
        assert!(nonzero > 0, "some family's covector meets the other half's");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// [measurement; theory, November 9 05:31] The `z` at the larger SE is the one of smaller magnitude; an unbounded one stands
    /// above every bounded one, and an unread one leaves none.
    #[test]
    fn the_bar_reads_the_z_at_the_larger_se() {
        assert_eq!(z_at_larger_se("2913", "4663"), "2913");
        assert_eq!(z_at_larger_se("-4663", "-2913"), "-2913");
        assert_eq!(z_at_larger_se("inf", "1200"), "1200");
        assert_eq!(z_at_larger_se("none", "1200"), "none");
    }

    /// [agent-inferred, November 9] The two-limb sum of products is the unbounded integers' sum, the extremes of 128 bits
    /// included, and refuses past `2^255`.
    #[test]
    fn a_sum_of_products_in_two_limbs_is_the_integers_sum() {
        use num_bigint::BigInt;
        let values = [0i128, 1, -1, 7, -13, i128::MAX, i128::MIN, i128::MIN + 1, 1 << 64, -(1 << 64) + 3, (1 << 100) + 12345, -(1 << 90) - 777, u64::MAX as i128];
        let (mut sum, mut want) = (ProductSum::default(), BigInt::from(0));
        for (n, &x) in values.iter().enumerate() {
            for &y in &values[n..] {
                // Two extreme products and their negatives keep the sum inside 2^255 at every step.
                sum.add_product(x, y).unwrap();
                want += BigInt::from(x) * BigInt::from(y);
                assert_eq!(sum.big(), want, "{x} · {y}");
                sum.add_product(x, -y.max(-i128::MAX)).unwrap();
                want -= BigInt::from(x) * BigInt::from(y.max(-i128::MAX));
                assert_eq!(sum.big(), want, "{x} · −{y}");
            }
        }
        let mut past = ProductSum::default();
        past.add_product(i128::MIN, i128::MIN).unwrap();
        assert!(past.add_product(i128::MIN, i128::MIN).is_err(), "two products of 2^254 reach 2^255");
    }

    /// [measurement; theory, November 9 04:40] One half's stationarity test by hand: problem sums 3 and 5 of two places
    /// each against two places, `S = 8/4 = 2`, `SE = √(4/16) = 1/2` (floor 0), `z = 4`; the sums times `4^k` (a grain `2^k`
    /// finer) give the same `z`; equal sums read `inf`, one problem `none`.
    #[test]
    fn a_halfs_stationarity_reads_its_problem_sums() {
        use num_bigint::BigInt;
        let sums = |v: &[i64]| -> Vec<BigInt> { v.iter().map(|&x| BigInt::from(x)).collect() };
        assert_eq!(stationarity(&sums(&[3, 5]), 2, 2), ("2".to_string(), "0".to_string(), "4000".to_string()));
        assert_eq!(stationarity(&sums(&[3 << 20, 5 << 20]), 2, 2).2, "4000", "z does not depend on the grain");
        assert_eq!(stationarity(&sums(&[-3 << 20, -5 << 20]), 2, 2).2, "-4000");
        assert_eq!(stationarity(&sums(&[11, -4, 7, 2]), 6, 5).2, stationarity(&sums(&[11 << 8, -4 << 8, 7 << 8, 2 << 8]), 6, 5).2);
        assert_eq!(stationarity(&sums(&[2, 2]), 2, 2).2, "inf");
        assert_eq!(stationarity(&sums(&[9]), 1, 2), ("5".to_string(), "none".to_string(), "none".to_string()));
    }

    /// [measurement; theory, November 9 04:36] `covector-field` end to end on the host: an energy field whose temperature
    /// learns, two conditional sections in, with its averaged constitution kept, read at six held places of four problems
    /// (halves of two problems each). Each row of `COVECTOR.tsv` is `⟨g_f(i), Σ_other g_f⟩` and `‖g_f(i)‖²` over law (D)'s
    /// per-place covectors at `θ̄` (not the live `θ`), formed here in unbounded integers; a state with no average is refused;
    /// the state is read, never written.
    #[test]
    fn the_covector_reading_reads_law_ds_places_at_the_average() {
        use holonics::hnn::tower::field::conditional_place_covectors;
        use num_bigint::BigInt;
        let dir = std::env::temp_dir().join(format!("holonics-covector-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("dir");
        let at = |name: &str| dir.join(name).to_string_lossy().into_owned();
        let put = |name: &str, bytes: &[u8]| {
            std::fs::write(dir.join(name), bytes).expect("write");
            (at(name), sha256(bytes).expect("sha"))
        };
        let (codec, problems) = toy();
        let reach = problems.iter().map(|(q, _, _)| q.len() + codec.answer).max().unwrap();
        let d = FieldDeclaration { alphabet: codec.alphabet(), width: 8, heads: 2, modes: 3, still: 1, contacts: 4, ticks: 2, frames: 2, reach, lanes: 1, depth: 0, energy: true };
        let keys: Vec<u8> = (0..1u64 << 13).flat_map(|i| mix(0x5EED, i).to_be_bytes()).collect();
        let mut field = Field::found(d, &keys).unwrap();
        let families = field.layout().families.clone();
        for (n, v) in field.theta.iter_mut().enumerate() {
            let k = mix(0x11E5, n as u64) as u32 as i32 as i64;
            let grain = families.iter().find(|(s, l, _)| (*s..*s + *l).contains(&n)).unwrap().2;
            *v = ((k << grain) >> 32) as i32;
        }
        let l = field.layout().clone();
        field.theta[l.pace..l.pace + d.paced_heads() * (d.alphabet + 1)].fill(0);
        let mut learner = FieldLearner::new(field, 14);
        learner.temper_learns = true;
        let held_set = encoded_problems(&codec, &problems_of(TOY), &learner.field).unwrap();
        let void = codec.void();
        let truth_of = |p: &(Vec<usize>, Vec<usize>, usize), letters: &[usize]| truth_with_voids(void, p, letters);
        let truths: Vec<Vec<usize>> = held_set.iter().map(|p| truth_of(p, &p.1)).collect();
        let resolved: Vec<Vec<bool>> = truths.iter().map(|t| vec![false; t.len()]).collect();
        let views: Vec<Region> = truths.iter().zip(&resolved).map(|(c, u)| Region { classes: c, unresolved: u, faces: &[], locked: &[], echo: &[], domain: None, port: None }).collect();
        let blocks: Vec<Vec<usize>> = held_set.iter().map(|p| vec![p.0.len(), p.0.len() + 1]).collect();
        let owners: Vec<usize> = (0..held_set.len()).collect();
        let (codec_at, codec_sha) = put("CODEC", codec.to_text().as_bytes());
        let (units, units_sha) = put("UNITS", b"founded-units-v1 0\n");
        let (held, held_sha) = put("HELD", TOY);
        let args = |state: &str, sha: &str, out: &str| -> Vec<String> { ["covector-field", state, sha, &codec_at, &codec_sha, &units, &units_sha, &held, &held_sha, "6", &at(out)].iter().map(|s| s.to_string()).collect() };
        learner.section_conditional(&views, &owners, &blocks, &mut host()).expect("a section");
        let (bare, bare_sha) = put("BARE", learner.to_text().as_bytes());
        assert!(covector_field(&args(&bare, &bare_sha, "N"), &mut host()).is_err(), "a state with no average");
        learner.average_section();
        learner.section_conditional(&views, &owners, &blocks, &mut host()).expect("a second section");
        learner.average_section();
        let averaged = learner.averaged_field();
        assert!(averaged.theta != learner.field.theta, "the average lags the live θ");
        let text = learner.to_text();
        let (state, state_sha) = put("STATE", text.as_bytes());
        covector_field(&args(&state, &state_sha, "C"), &mut host()).expect("covector");
        assert_eq!(std::fs::read(dir.join("STATE")).expect("state"), text.as_bytes(), "the state is read, never written");
        // The reading's places and halves, formed here: problems in their first place's order, odd positions half B.
        let chosen = enumerated_places(&held_set, 6, &truth_of);
        let mut order: Vec<usize> = Vec::new();
        for (k, _, _, _) in &chosen {
            if !order.contains(k) {
                order.push(*k);
            }
        }
        assert!(order.len() == 4 && chosen.len() == 6, "six places of four problems");
        let views: Vec<Region> = order.iter().map(|&k| Region { classes: &truths[k], unresolved: &resolved[k], faces: &[], locked: &[], echo: &[], domain: None, port: None }).collect();
        let asked: Vec<(usize, usize)> = chosen.iter().map(|(k, truth, t, _)| {
            assert_eq!(truth, &truths[*k]);
            (order.iter().position(|o| o == k).unwrap(), *t)
        }).collect();
        let read = conditional_place_covectors(&averaged, true, &views, &asked, &mut host(), &mut |_, _, _| {}).unwrap();
        let live = conditional_place_covectors(&learner.field, true, &views, &asked, &mut host(), &mut |_, _, _| {}).unwrap();
        assert!(read != live, "the average's covectors are not the live θ's");
        let in_b: Vec<bool> = asked.iter().map(|&(p, _)| p % 2 == 1).collect();
        let material = averaged.material_len();
        let half_sum = |b: bool| -> Vec<BigInt> { (0..material).map(|j| read.iter().zip(&in_b).filter(|(_, x)| **x == b).map(|(r, _)| BigInt::from(r.covector[j])).sum()).collect() };
        let (sum_a, sum_b) = (half_sum(false), half_sum(true));
        let places_b = in_b.iter().filter(|&&b| b).count();
        let all_families = averaged.families_all();
        let names = family_names(&averaged);
        let rows = String::from_utf8(std::fs::read(dir.join("C/COVECTOR.tsv")).expect("rows")).unwrap();
        let mut rows = rows.lines().skip(1);
        let mut nonzero = 0;
        for (i, (k, _, t, q)) in chosen.iter().enumerate() {
            let (half, other, other_places) = if in_b[i] { ("b", &sum_a, 6 - places_b) } else { ("a", &sum_b, places_b) };
            for (f, &(start, n, _)) in all_families.iter().enumerate() {
                if n == 0 {
                    continue;
                }
                let dot: BigInt = (start..start + n).map(|j| BigInt::from(read[i].covector[j]) * &other[j]).sum();
                let square: BigInt = (start..start + n).map(|j| BigInt::from(read[i].covector[j]) * BigInt::from(read[i].covector[j])).sum();
                nonzero += usize::from(dot != BigInt::from(0));
                assert_eq!(rows.next(), Some(format!("{k}\t{}\t{half}\t{}\t{dot}\t{other_places}\t{square}", t - q, names[f].0).as_str()), "place {i}, family {f}");
            }
        }
        assert_eq!(rows.next(), None, "a row a place and family");
        assert!(nonzero > 0, "some family's covector meets the other half's");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// The regions `section_regions` formed for `members` from `first` on, against the draws they stand on: one region a
    /// member, the truth with the keyed open sites unresolved and nothing carried, weighed over the whole region or over
    /// the answer and its tail.
    fn check_regions(codec: &FieldCodec, problems: &Problems, members: &[usize], paths: &[usize], seed: u64, first: u64, regions: &[TrainRegion]) -> usize {
        let mut states = regions[members.len()..].iter();
        for (n, &i) in paths.iter().enumerate() {
            let (q, a, _) = &problems[i];
            // A state with nothing open is no state; every other stands in the paths' order on its member's draw.
            let Some(expected) = opening_region(codec, q, a, seed, first + n as u64 + 1) else { continue };
            let opening = states.next().expect("a path state for each path with a place open");
            assert_eq!(*opening, expected, "member {n}'s path state is its draw's");
            assert!(opening.unresolved.iter().any(|&u| u), "member {n}'s path state has a place open");
            assert!(opening.unresolved[..q.len()].iter().all(|&u| !u), "member {n}'s question is resolved");
            let voided = (q.len()..opening.classes.len()).find(|&t| !opening.unresolved[t] && opening.classes[t] == codec.void());
            if let Some(end) = voided {
                assert!(opening.unresolved[end + 1..].iter().all(|&u| !u), "member {n}: every place past the lowest resolved void is resolved");
                assert_eq!(opening.classes.len(), q.len() + codec.answer, "member {n}: past a resolved void the path keeps the room");
            } else {
                assert!(opening.classes.len() <= q.len() + codec.answer, "member {n}'s path within the room");
            }
            let Some((start, void, target, true, stop, _)) = opening.port.clone() else { panic!("member {n}'s path is compared at its boundary") };
            assert_eq!((start, void, target), (q.len(), codec.void(), a[..a.len().min(opening.classes.len() - q.len())].to_vec()));
            if let Some(stop) = stop {
                assert_eq!(opening.classes.len() - stop, holonics::hnn::tower::field::NEAR - 1, "member {n}: the margin is the near field's");
            }
        }
        assert!(states.next().is_none(), "no path state past the paths'");
        assert!(regions.len() >= members.len());
        let mut answers = 0;
        for (n, &i) in members.iter().enumerate() {
            let (q, a, _) = &problems[i];
            let draw = first + n as u64 + 1;
            let length = q.len() + a.len() + tail(seed, draw, codec.answer - a.len());
            let truth = region_classes(codec, q, a, length);
            let expected = match shape(seed, draw, q.len(), length) {
                Shape::Masked(mask) => TrainRegion { domain: Some(weighed_domain(length, &mask)), ..TrainRegion::plain(truth, mask) },
                Shape::Answer(mask) => {
                    answers += 1;
                    TrainRegion { domain: Some(weighed_domain(length - q.len(), &mask)), ..TrainRegion::plain(truth, mask) }
                }
            };
            assert_eq!(regions[n], expected, "member {n}");
        }
        answers
    }

    /// [definition; the unified-theory reading of November 6, 00:58] **A path state in place order is a prefix compared at its
    /// frontier**: the question and the first `k` answer places resolved to the truth, the frontier open and compared on its own
    /// class (the void where the answer ends), the places past it open, in a port that hears none, the region `NEAR − 1` past
    /// the frontier; every `k` from 0 to the answer's end is met, and none past it.
    #[test]
    fn a_prefix_state_is_compared_at_its_frontier() {
        let (codec, problems) = toy();
        let near = holonics::hnn::tower::field::NEAR;
        let mut met = std::collections::BTreeSet::new();
        for (i, (q, a, _)) in problems.iter().enumerate() {
            for draw in 1..400u64 {
                let state = prefix_region(&codec, q, a, 9 + i as u64, draw);
                let frontier = (0..state.classes.len()).find(|&t| state.unresolved[t]).expect("a frontier");
                let k = frontier - q.len();
                assert!(k <= a.len(), "no frontier past the answer's end");
                met.insert((i, k));
                assert_eq!(&state.classes[..q.len()], &q[..]);
                assert_eq!(&state.classes[q.len()..frontier], &a[..k], "the prefix is the truth");
                assert_eq!(state.classes[frontier], if k < a.len() { a[k] } else { codec.void() }, "the frontier's own class");
                assert!(state.unresolved[frontier..].iter().all(|&u| u), "the room past the frontier is open");
                assert_eq!(state.classes.len(), (frontier + near).min(q.len() + codec.answer));
                let Some((start, _, _, true, None, Some(heard))) = state.port.clone() else { panic!("the room past the frontier stands in a port") };
                assert_eq!(start, frontier + 1);
                assert!(heard.iter().all(|&h| !h), "the port hears none of its places");
                assert_eq!(state.domain, Some(a.len().min(codec.answer - 1) + 1), "the state stands for every place its draw samples");
            }
        }
        for (i, (_, a, _)) in problems.iter().enumerate() {
            assert!((0..=a.len()).all(|k| met.contains(&(i, k))), "problem {i}: every prefix met");
        }
    }

    /// [definition; the unified-theory reading of November 5, 23:26] **b2's far share**: a path state with no resolved void
    /// hears its front octave whole and, past it, exactly one place an octave, the first its keyed order opens there, over
    /// the whole room; a state past a resolved void hears every place; without the far share every place is heard.
    #[test]
    fn a_path_state_hears_its_front_octave_and_one_keyed_place_an_octave() {
        let (codec, problems) = toy();
        let (mut keyed, mut voided) = (0, 0);
        for (i, (q, a, _)) in problems.iter().enumerate() {
            for draw in 1..64u64 {
                let Some(state) = opening_region_with(&codec, q, a, 7 + i as u64, draw, true) else { continue };
                let Some((start, _, _, true, None, heard)) = state.port.clone() else { panic!("a path state compared at its boundary") };
                let plain = opening_region_with(&codec, q, a, 7 + i as u64, draw, false).unwrap();
                assert_eq!(plain.port.as_ref().unwrap().5, None, "without the far share every place is heard");
                assert_eq!((&plain.classes, &plain.unresolved), (&state.classes, &state.unresolved), "the far share keeps the region");
                let Some(heard) = heard else {
                    assert!((start..state.classes.len()).any(|t| !state.unresolved[t] && state.classes[t] == codec.void()), "only a state past a void hears every place");
                    voided += 1;
                    continue;
                };
                let octave = |t: usize| holonics::hnn::tower::field::octave_of(t + 1 - start);
                let front = (start..state.classes.len()).filter(|&t| state.unresolved[t]).map(octave).min().unwrap();
                assert!((start..state.classes.len()).filter(|&t| octave(t) <= front).all(|t| heard[t]), "the front octave is heard whole");
                let far: Vec<usize> = (start..state.classes.len()).filter(|&t| heard[t] && octave(t) > front).collect();
                let octaves: std::collections::BTreeSet<u32> = (start..state.classes.len()).filter(|&t| octave(t) > front).map(octave).collect();
                assert_eq!(far.len(), octaves.len(), "one place an octave past the front");
                assert!(far.iter().all(|&t| state.unresolved[t]), "the far places are open");
                assert!(heard[..start].iter().all(|&h| !h), "the question is not a port place");
                keyed += 1;
            }
        }
        assert!(keyed > 0 && voided > 0, "keyed {keyed}, voided {voided}");
    }

    /// [definition; the unified-theory reading of November 6, 06:50] **The writer's own state given its end**: the question and
    /// the answer's truth, the end's `NEAR` voids resolved and the region cut there, open places only within the answer and at
    /// least one, the resolved ones the first `k` of the writer's order (octaves of distance, never a place of a later octave
    /// before an earlier octave is whole), every octave of `k` met, each open place compared on its own class with weight one.
    #[test]
    fn a_writer_state_is_its_order_given_its_end() {
        let (codec, problems) = toy();
        let near = holonics::hnn::tower::field::NEAR;
        let octave = holonics::hnn::tower::field::octave_of;
        for (i, (q, a, _)) in problems.iter().enumerate() {
            let mut met = std::collections::BTreeSet::new();
            for draw in 1..400u64 {
                let state = writer_region(&codec, q, a, 9 + i as u64, draw).expect("an answer with places has a state");
                let end = q.len() + a.len();
                assert_eq!(state.classes, region_classes(&codec, q, a, (end + near).min(q.len() + codec.answer)), "the truth, cut NEAR places past the end (within the room)");
                assert!(state.unresolved[..q.len()].iter().all(|&u| !u) && state.unresolved[end..].iter().all(|&u| !u), "only answer places open");
                let resolved: Vec<usize> = (q.len()..end).filter(|&t| !state.unresolved[t]).collect();
                let k = resolved.len();
                assert!(k < a.len(), "a place left open");
                if let Some(far) = resolved.iter().map(|&t| octave(t + 1 - q.len())).max() {
                    assert!((q.len()..end).filter(|&t| octave(t + 1 - q.len()) < far).all(|t| !state.unresolved[t]), "the earlier octaves resolved whole");
                }
                met.insert(if k == 0 { 0 } else { octave(k) + 1 });
                assert!(state.port.is_none() && state.domain.is_none() && !state.window && !state.letters, "every open place compared on its own class");
                let open = state.unresolved.iter().filter(|&&u| u).count() as u64;
                assert_eq!(view_of(&state).weight(), (open, open), "weight one");
            }
            let most = a.len() - 1;
            let octaves = usize::BITS - most.leading_zeros() + 1;
            assert_eq!(met.len(), octaves as usize, "problem {i}: every octave of k met");
        }
    }

    /// [definition; law 2 of the unified-theory reading of November 6] **The field's own draft**: each path problem's truth cut
    /// `NEAR` places past its end, the masks' open places (`τ = u²` within the answer, at least one) compared on the truth with
    /// the masks' weight, every other answer place the truth or a letter drawn from the field's own face there (never the
    /// void), the question and the end's voids given.
    #[test]
    fn a_draft_is_the_truth_where_compared_and_the_fields_own_letters_elsewhere() {
        let (codec, problems) = toy();
        let near = holonics::hnn::tower::field::NEAR;
        let learner = toy_learner(&codec, &problems);
        let paths: Vec<usize> = (0..problems.len()).collect();
        let (mut drafted, mut opened) = (0usize, std::collections::BTreeSet::new());
        for seed in 0..40u64 {
            let draws: Vec<u64> = paths.iter().map(|&i| seed * 16 + i as u64).collect();
            let drafts = draft_regions(&codec, &problems, &paths, &draws, seed, &learner.field, &mut host()).unwrap();
            let answered: Vec<_> = problems.iter().filter(|p| !p.1.is_empty()).collect();
            assert_eq!(drafts.len(), answered.len());
            for (state, (q, a, _)) in drafts.iter().zip(answered) {
                let len = a.len().min(codec.answer);
                let end = q.len() + len;
                let truth = region_classes(&codec, q, &a[..len], (end + near).min(q.len() + codec.answer));
                assert_eq!(state.classes.len(), truth.len(), "cut NEAR places past the end (within the room)");
                assert!(state.unresolved[..q.len()].iter().all(|&u| !u) && state.unresolved[end..].iter().all(|&u| !u), "only answer places open");
                let open = state.unresolved.iter().filter(|&&u| u).count();
                assert!(open > 0, "a place compared");
                opened.insert(open);
                for t in 0..truth.len() {
                    if t < q.len() || t >= end || state.unresolved[t] {
                        assert_eq!(state.classes[t], truth[t], "the truth where compared and outside the answer");
                    } else {
                        assert_ne!(state.classes[t], codec.void(), "a drafted place is a letter");
                        drafted += usize::from(state.classes[t] != truth[t]);
                    }
                }
                assert_eq!(state.domain, Some(weighed_domain(len, &state.unresolved[q.len()..end])), "the masks' weight");
                assert!(state.port.is_none() && !state.window && !state.letters);
            }
        }
        assert!(drafted > 0 && opened.len() > 1, "{drafted} drafted places, {opened:?} open counts");
    }

    /// [definition; the unified-theory reading of November 6, 19:04] **The squares agree**: each path problem's square is four
    /// states of its truth cut `NEAR` places past its end, each open at one place of the square and pulling there; the pulls
    /// weigh `w_i`, `w_i`, `w_j`, `w_j` (the turn law's, read through [`square_reads`]) with no radial part, `w_i λ_i + w_j λ_j = 0`,
    /// which the four states' codes sum to (each released to its nearest).
    /// A square's `(λ_i, λ_j)` read back from its four states' own faces (each state's open place, on its letters).
    fn square_lambdas(field: &Field, codec: &FieldCodec, four: &[TrainRegion]) -> (i64, i64) {
        let code = |s: &TrainRegion, c: usize| -> i64 {
            let t = s.unresolved.iter().position(|&u| u).unwrap();
            let faces = field.read_faces(&[Region { classes: &s.classes, unresolved: &s.unresolved, faces: &[], locked: &[], echo: &[], domain: None, port: None }]).unwrap();
            holonics::hnn::tower::field::letters_face(faces[0][t].as_ref().unwrap(), codec.void()).unwrap().code(c)
        };
        let ((a, a2, _), (b, b2, _)) = (four[0].pull.unwrap(), four[2].pull.unwrap());
        let lambda_i = code(&four[0], a2) + code(&four[1], a) - code(&four[0], a) - code(&four[1], a2);
        let lambda_j = code(&four[2], b2) + code(&four[3], b) - code(&four[2], b) - code(&four[3], b2);
        (lambda_i, lambda_j)
    }

    #[test]
    fn the_squares_pull_the_two_readings_together() {
        let (codec, problems) = toy();
        let near = holonics::hnn::tower::field::NEAR;
        let learner = toy_learner(&codec, &problems);
        let paths: Vec<usize> = (0..problems.len()).collect();
        let mut met = 0usize;
        for seed in 0..12u64 {
            let draws: Vec<u64> = paths.iter().map(|&i| seed * 16 + i as u64).collect();
            let (states, squares, _) = square_regions(&codec, &problems, &paths, &draws, seed, &learner.field, &mut host()).unwrap();
            assert_eq!(states.len(), 4 * squares);
            for four in states.chunks(4) {
                let pulls: Vec<(usize, usize, i64)> = four.iter().map(|s| s.pull.unwrap()).collect();
                let (wi, wj) = (pulls[0].2, pulls[2].2);
                assert_eq!(pulls.iter().map(|p| p.2).collect::<Vec<_>>(), vec![wi, wi, wj, wj]);
                assert_eq!((pulls[0].0, pulls[0].1), (pulls[1].1, pulls[1].0), "i's pulls swap its two letters");
                assert_eq!((pulls[2].0, pulls[2].1), (pulls[3].1, pulls[3].0), "j's pulls swap its two letters");
                let mut code = 0i64;
                for s in four {
                    let open: Vec<usize> = (0..s.unresolved.len()).filter(|&t| s.unresolved[t]).collect();
                    assert_eq!(open.len(), 1, "one place open");
                    let (start, _, target, boundary, stop, _) = s.port.as_ref().unwrap();
                    assert_eq!((*start, target.len(), *boundary, *stop), (open[0], 0, false, Some(open[0] + 1)));
                    code += learner.field.code(&view_of(s)).unwrap().0;
                }
                // Σ w·(each face's term) = w_i λ_i + w_j λ_j = 0: no common scale is pulled (to the terms' rounding).
                let (li, lj) = square_lambdas(&learner.field, &codec, four);
                let radial = wi as i128 * li as i128 + wj as i128 * lj as i128;
                let scale = (wi.unsigned_abs() + wj.unsigned_abs()) as i128 * (li.unsigned_abs() + lj.unsigned_abs()) as i128;
                assert!(radial.abs() * 64 <= scale + (1 << 40), "the pull has a radial part: {radial} against {scale}");
                assert!((code as i128 - radial / (1 << 20)).abs() <= 8 + ((wi.unsigned_abs() + wj.unsigned_abs()) >> 18) as i128, "codes {code} against {}", radial / (1 << 20));
                if lj == 0 && li != 0 {
                    assert_eq!(wi, 0, "a one-way square moves only the missing reading");
                }
                met += 1;
            }
            for (state, &p) in states.chunks(4).zip(paths.iter().filter(|&&p| problems[p].1.len().min(codec.answer) >= 2)) {
                let (q, a, _) = &problems[p];
                let len = a.len().min(codec.answer);
                assert_eq!(state[0].classes, region_classes(&codec, q, &a[..len], (q.len() + len + near).min(q.len() + codec.answer)), "the truth given its end");
            }
        }
        assert!(met > 0);
    }

    /// A section's regions on the toy passage are the draws' (one a member), their lengths the projection's, and the
    /// held step is read on them before they are returned (a step held is a step read).
    #[test]
    fn a_section_is_its_draws_and_its_held_step_is_read_on_them() {
        let (codec, problems) = toy();
        let members = [0usize, 1, 2, 3];
        let paths = [3usize, 0, 2, 1];
        let mut learner = toy_learner(&codec, &problems);
        // The held read is the declared comparison (§16.30); the field's law lets a step stand unread.
        learner.read_held = true;
        let (mut draw, mut held, mut read, mut answers) = (0u64, false, 0usize, 0usize);
        for section in 0..8 {
            let first = draw;
            let lengths = region_lengths(&codec, &problems, &members, &paths, 5, &mut { first });
            let (regions, next) = section_regions(&codec, &problems, &members, &paths, 5, &mut draw, &mut learner, &mut host()).unwrap();
            assert_eq!(draw, first + 4);
            assert_eq!(lengths, regions.iter().map(|r| r.classes.len()).collect::<Vec<_>>(), "the projection's lengths are the regions'");
            assert_eq!(next.is_some(), held, "section {section}: a step held is a step read");
            assert!(!learner.holds_step(), "the held step is read before the regions are formed");
            read += usize::from(next.is_some());
            answers += check_regions(&codec, &problems, &members, &paths, 5, first, &regions);
            learner.section_realized(&views_of(&regions), &mut host()).unwrap();
            held = learner.holds_step();
        }
        assert!(read > 0 && answers > 0, "{read} {answers}");
    }

    #[test]
    fn the_held_read_prints_millionths_and_the_question_effect() {
        assert_eq!(micro_bits(3 << 20, 2), "1.500000");
        assert_eq!(micro_bits(-(3 << 20), 2), "-1.500000");
        assert_eq!(micro_bits(1, 1), "0.000001");
        assert_eq!(micro_bits(0, 0), "-");
        let mut held = [(0i64, 0usize); 3];
        held[1] = (5 * 4 << 20, 4);
        held[2] = (5 * 4 << 20, 4);
        held[2].0 += 4;
        let text = held_text(&held);
        assert!(text.contains("context=5.000000 ") && text.contains("foil=5.000001 ") && text.ends_with("question=0.000001"), "{text}");
        assert!(text.contains("answer=- "), "{text}");
        assert_eq!(bits(held[1].0, 4), bits(held[2].0, 4), "the three-decimal reading cannot tell them apart");
    }

    /// A passage of records keeps each question's and answer's bytes whole, blank lines and several lines included.
    #[test]
    fn a_passage_of_records_keeps_its_blank_lines() {
        let text = b"Add two numbers\nin Python\x1f```python\ndef add(a, b):\n\n    return a + b\n```\x1eSay hi\x1fprint('hi')\x1e";
        let problems = problems_of(text);
        assert_eq!(problems.len(), 2);
        assert_eq!(problems[0], (b"Add two numbers\nin Python".to_vec(), b"```python\ndef add(a, b):\n\n    return a + b\n```".to_vec()));
        assert_eq!(problems[1], (b"Say hi".to_vec(), b"print('hi')".to_vec()));
        assert_eq!(problems_of(b"Q one\nA one\n\nQ two\nA two\nmore\n"), vec![(b"Q one".to_vec(), b"A one".to_vec()), (b"Q two".to_vec(), b"A two\nmore".to_vec())], "the blank-line blocks as before");
    }

    /// The withheld problems are never in a section, and every other problem is in one.
    #[test]
    fn sections_withhold_their_unseen_problems() {
        let problems: Problems = (0..40).map(|i| (vec![1; 3 + i % 7], vec![2; 5 + i % 3], 5)).collect();
        let (sections, unseen) = sections_of(&problems, 6, 9, 11);
        assert_eq!(unseen.len(), 9);
        let mut trained: Vec<usize> = sections.concat();
        assert_eq!(trained.len(), 31);
        trained.extend(&unseen);
        trained.sort_unstable();
        assert_eq!(trained, (0..40).collect::<Vec<_>>());
        assert_eq!(sections_of(&problems, 6, 9, 11).1, unseen, "keyed, not drawn afresh");
    }

    /// A lap's path problems are every trained problem once, in the sections' sizes, keyed afresh each lap and not by
    /// length: a section's paths are not its own members.
    #[test]
    fn a_laps_paths_meet_every_problem_once_across_the_lengths() {
        let problems: Problems = (0..40).map(|i| (vec![1; 3 + i % 7], vec![2; 5 + i % 3], 5)).collect();
        let (sections, _) = sections_of(&problems, 6, 9, 11);
        let (a, b) = (paths_of(11, 4, &sections), paths_of(11, 5, &sections));
        for paths in [&a, &b] {
            assert_eq!(paths.iter().map(Vec::len).collect::<Vec<_>>(), sections.iter().map(Vec::len).collect::<Vec<_>>());
            let mut met = paths.concat();
            met.sort_unstable();
            let mut trained = sections.concat();
            trained.sort_unstable();
            assert_eq!(met, trained, "each trained problem's path once a lap");
        }
        assert_eq!(paths_of(11, 4, &sections), a, "keyed by the lap");
        assert_ne!(a, b, "fresh each lap");
        assert!(a.iter().zip(&sections).any(|(p, s)| p != s), "not the sections' own members");
    }

    /// The withheld problems are read with their neighbours, over the same sites every lap: each
    /// answer site and its first void once, in one of four parts, with every other site resolved.
    #[test]
    fn the_held_foil_reads_each_answer_beside_the_next_question() {
        let text: [(&[u8], &[u8]); 3] = [(b"Ann has 3 pens.", b"<<3+1=4>>4\n#### 4"), (b"Bo has 12 cups and 5 more.", b"<<12+5=17>>17\n#### 17"), (b"Cy has 7.", b"#### 7")];
        let raw: Vec<(Vec<u8>, Vec<u8>)> = text.iter().map(|(q, a)| (q.to_vec(), a.to_vec())).collect();
        let codec = FieldCodec::found(Units::bytes(), &raw).unwrap();
        let problems: Problems = raw.iter().map(|(q, a)| (codec.encode(&question_text(q)).unwrap(), codec.encode(a).unwrap(), a.len())).collect();
        let regions = held_regions(&codec, &problems);
        assert_eq!(regions.len(), 3 + 2 * 3 * CONTEXT);
        for (i, parts) in regions.iter().filter(|r| r.2 == 6).collect::<Vec<_>>().chunks(CONTEXT).enumerate() {
            let (q, a) = (&problems[(i + 1) % 3].0, &problems[i].1);
            let own = regions.iter().filter(|r| r.2 == 3).nth(i * CONTEXT).unwrap();
            for part in parts {
                assert_eq!(&part.0[..q.len()], &q[..], "the next problem's question");
                assert_eq!(&part.0[q.len()..q.len() + a.len()], &a[..], "the problem's own answer");
                assert!(part.1[..q.len()].iter().all(|&u| !u), "the question resolved");
            }
            let open = |r: &(Vec<usize>, Vec<bool>, usize), start: usize| r.1[start..].to_vec();
            assert_eq!(open(parts[0], q.len()), open(own, problems[i].0.len()), "the answer's sites read as in its own context");
        }
    }

    #[test]
    fn the_withheld_problems_read_each_answer_site_once_beside_its_neighbours() {
        let problems: Problems = (0..5usize).map(|i| (vec![1; 3 + i], vec![2; 1 + i], 1 + i)).collect();
        let codec_answer = 9;
        let regions = unseen_regions_with(codec_answer, 0, &problems, &[1, 3], 5);
        assert_eq!(regions, unseen_regions_with(codec_answer, 0, &problems, &[1, 3], 5), "keyed, not drawn afresh");
        assert_eq!(regions.len(), 2 * CONTEXT);
        for (parts, &i) in regions.chunks(CONTEXT).zip(&[1usize, 3]) {
            let (q, a, _) = &problems[i];
            let mut read = vec![0usize; parts[0].0.len()];
            for (classes, open) in parts {
                assert!(classes.len() > q.len() + a.len() && classes.len() <= q.len() + codec_answer);
                assert_eq!(&classes[..q.len()], &q[..]);
                assert_eq!(&classes[q.len()..q.len() + a.len()], &a[..]);
                for (t, &u) in open.iter().enumerate() {
                    read[t] += usize::from(u);
                }
            }
            assert!(read.iter().enumerate().all(|(t, &n)| n == usize::from(t >= q.len() && t <= q.len() + a.len())), "each answer site and its void once");
        }
    }

    /// [definition; theory, November 9 11:48] The save law's test: a section that would pass the hour saves, one that would end
    /// on it does not, and before any rate the plain hour test holds (an hour to the millisecond saves). The rate is the largest
    /// measured time over declared work, kept as its pair, and its projection rounds up. On a walk of sections that each take
    /// their work at one rate, the hour test alone (the law this one replaces) saves at the first start past the hour, so a gap
    /// passes the hour by part of a section; the projected crossing holds every gap to the hour.
    #[test]
    fn a_save_falls_where_a_section_would_pass_the_hour() {
        const HOUR: u128 = 3_600_000;
        assert!(!save_due(0, Some(HOUR), HOUR), "a section that ends on the hour does not pass it");
        assert!(save_due(0, Some(HOUR + 1), HOUR));
        assert!(!save_due(HOUR - 600_000, Some(600_000), HOUR));
        assert!(save_due(HOUR - 600_000, Some(600_001), HOUR));
        assert!(!save_due(HOUR, Some(0), HOUR));
        assert!(save_due(HOUR + 1, Some(0), HOUR));
        assert!(!save_due(HOUR - 1, None, HOUR), "no rate: the plain hour test");
        assert!(save_due(HOUR, None, HOUR));
        assert_eq!(SaveRate::larger(None, 5, 0), None, "a section of no declared work measures no rate");
        // 300/7 > 200/5, then 450/10 > 300/7.
        let rate = SaveRate::larger(SaveRate::larger(None, 300, 7), 200, 5);
        assert_eq!(rate, Some(SaveRate { ms: 300, work: 7 }));
        let rate = SaveRate::larger(rate, 450, 10);
        assert_eq!(rate, Some(SaveRate { ms: 450, work: 10 }));
        assert_eq!(SaveRate { ms: 450, work: 10 }.project(3), 135);
        assert_eq!(SaveRate { ms: 300, work: 7 }.project(1), 43, "⌈300/7⌉");
        // Each section takes 90 ms a unit of its work: the gaps between saves under each law.
        let works: [u128; 9] = [1_000, 5_000, 9_000, 2_000, 11_000, 7_000, 3_000, 13_000, 6_000];
        let gaps = |projected: bool| -> Vec<u128> {
            let (mut t, mut saved, mut rate, mut gaps) = (0u128, 0u128, None::<SaveRate>, Vec::new());
            for &w in works.iter().cycle().take(45) {
                if save_due(t - saved, if projected { rate.map(|r| r.project(w)) } else { None }, HOUR) {
                    gaps.push(t - saved);
                    saved = t;
                }
                t += 90 * w;
                rate = SaveRate::larger(rate, 90 * w, w);
            }
            gaps
        };
        let (hour_test, crossing) = (gaps(false), gaps(true));
        assert!(hour_test.len() >= 4 && crossing.len() >= 4);
        assert!(hour_test.iter().any(|&g| g > HOUR), "the hour test alone passes the hour: {hour_test:?}");
        assert!(crossing.iter().all(|&g| g <= HOUR), "the projected crossing holds the hour: {crossing:?}");
    }

    /// [definition; theory, November 9 12:18] The save law's clock, in the trainer's order (a section opens after any save at its
    /// start and closes at its last print): a section followed by a save does not raise the measured rate by the save's held
    /// read. Section A reads 1,000 units in 100 s; the next start saves and its held read takes 103 s; section B reads 500 units
    /// in 45 s. B's 90 ms a unit stays below A's 100, so the rate is A's, where B measured from start to start (148 s) would read
    /// 296 ms a unit. The read is counted once, in the time since the save, from the state's write.
    #[test]
    fn a_saves_held_read_is_not_its_next_sections_rate() {
        let mut clock = SaveClock::default();
        assert_eq!((clock.projected(1_000, false), clock.since(0)), (None, 0), "no rate before a section is measured");
        clock.open(1_000, 0);
        clock.close(100_000);
        assert_eq!(clock.rate, Some(SaveRate { ms: 100_000, work: 1_000 }));
        clock.saved(100_000);
        clock.open(500, 203_000);
        clock.close(248_000);
        assert_eq!(clock.rate, Some(SaveRate { ms: 100_000, work: 1_000 }), "the save's read is not section B's");
        assert_eq!(clock.since(248_000), 148_000, "the time since the save holds the read once");
        assert_eq!(clock.projected(600, false), Some(60_000));
        assert!(save_due(clock.since(248_000), clock.projected(600, false), 200_000), "148 s since the save and 60 s projected pass 200 s");
        assert!(!save_due(clock.since(248_000), clock.projected(500, false), 200_000), "148 s and 50 s do not");
        // A section left open (skipped unread) is dropped unmeasured when the next opens; a closed clock closes nothing.
        clock.open(10, 250_000);
        clock.open(1, 251_000);
        clock.close(252_000);
        assert_eq!(clock.rate, Some(SaveRate { ms: 1_000, work: 1 }), "1 s over one unit, the skipped section unmeasured");
        clock.close(900_000);
        assert_eq!(clock.rate, Some(SaveRate { ms: 1_000, work: 1 }));
    }

    /// [definition; theory, November 9, the unit rule after 12:18] A held read is its own row, in the trainer's call order. The
    /// opening read takes 90 s; kernel section A reads 1,000 units in 100 s; kernel section B, in which a lap's tenth falls,
    /// reads 500 units in 40 s and closes before its tenth's held read of 103 s. B's 80 ms a unit leaves the rate A's (with the
    /// read inside it, 286 ms a unit), the largest held read becomes 103 s, and a section in which a tenth falls projects its
    /// work at the rate plus that read; the next start's time since the save holds the read, and with it the hour test saves
    /// where the rate alone would not. A tenth's read falls where `⌊(n + 1)·10/sections⌋` passes the last printed tenth, never
    /// at the lap's last section.
    #[test]
    fn a_tenths_held_read_is_its_own_row() {
        let mut clock = SaveClock::default();
        clock.held_read(90_000);
        assert_eq!(clock.projected(500, true), None, "no rate before a section is measured");
        clock.open(1_000, 90_000);
        clock.close(190_000);
        let tenth = tenth_read_falls(9, 100, 0);
        assert!(tenth);
        assert_eq!(clock.projected(500, tenth), Some(50_000 + 90_000), "the rate and the largest held read so far");
        clock.open(500, 190_000);
        clock.close(230_000);
        clock.held_read(103_000);
        clock.close(333_000);
        assert_eq!(clock.rate, Some(SaveRate { ms: 100_000, work: 1_000 }), "the tenth's read is not section B's rate");
        assert_eq!(clock.held, Some(103_000));
        assert_eq!((clock.projected(500, true), clock.projected(500, false)), (Some(153_000), Some(50_000)));
        clock.held_read(20_000);
        assert_eq!(clock.held, Some(103_000), "the largest held read is kept");
        assert_eq!(clock.since(333_000), 333_000, "the time since the opening state holds every read");
        assert!(save_due(clock.since(333_000), clock.projected(500, true), 400_000), "333 s, 50 s and a 103 s read pass 400 s");
        assert!(!save_due(clock.since(333_000), clock.projected(500, false), 400_000), "333 s and 50 s do not");
        assert!(!tenth_read_falls(8, 100, 0) && !tenth_read_falls(9, 100, 1), "no new tenth");
        assert!(tenth_read_falls(19, 100, 1) && !tenth_read_falls(99, 100, 9), "the next tenth; the lap's last section reads at the lap's end");
        assert!(tenth_read_falls(0, 5, 0) && tenth_read_falls(1, 5, 2) && !tenth_read_falls(1, 5, 4), "a lap of five sections");
    }

    /// [definition; theory, November 9 11:39, 11:48 and 12:18] A section's declared work. The fresh writes' is their declared
    /// sweeps times walk-field's site reads, `Σ_k (L_k + 1)(Q_k + L_k + v_k)` with `v_k = min(NEAR, room_k − L_k)` (a sweep's
    /// opening read of every region and its proposals), counted here by hand on three problems (a room that leaves the whole near
    /// tail, one that leaves two voids, one that leaves none). The
    /// kernel's blocks are each member's residue class in order, cut alternately at `k₋` and `k₊` on an odd section, and the
    /// kernel's and law D's work are read from them; the joint release's is its reads of every region, the writer's its places.
    #[test]
    fn a_sections_declared_work_is_the_walks_site_reads() {
        use holonics::hnn::tower::field::NEAR;
        let set: Problems = vec![(vec![1; 3], vec![2; 2], 2 + NEAR + 4), (vec![1; 5], vec![2; 4], 4 + 2), (vec![1; 1], vec![2; 7], 7)];
        let members = [0usize, 1, 2];
        let by_hand = 3 * (3 + 2 + NEAR as u128) + 5 * (5 + 4 + 2) + 8 * (1 + 7);
        assert_eq!(sweep_site_reads(&set, &members), by_hand, "walk-field's site reads");
        assert_eq!(sweep_site_reads(&set, &[2, 0, 1]), by_hand);
        // Fresh writes: their release, their sweeps left and their deposit, and the work between the sweep stops.
        let all_regions: u128 = (3 + 2 + NEAR as u128) + (5 + 4 + 2) + (1 + 7);
        assert_eq!(section_work(&SectionLaw::Fresh { sweeps: 24, from: 0, release_reads: 0 }, &set, &members), (24 * by_hand + 2 * all_regions, "site_reads"));
        assert_eq!(section_work(&SectionLaw::Fresh { sweeps: 24, from: 3, release_reads: WRITES_RELEASE_READS }, &set, &members).0, 64 * all_regions + 21 * by_hand + 2 * all_regions);
        let stops = FreshStops::of(&set, &members, WRITES_RELEASE_READS);
        assert_eq!((stops.release, stops.sweep, stops.deposit), (64 * all_regions, by_hand, 2 * all_regions));
        assert_eq!((stops.at_sweep(5, 24), stops.at_sweep(23, 24)), (by_hand, by_hand + 2 * all_regions), "the last sweep runs on into the deposit");
        let (seed, read, n, spacing) = (0x5EED_u64, 3u64, 5usize, 3usize);
        let starts: Vec<usize> = members.iter().enumerate().map(|(j, &i)| residue_start(seed, read, n, j, spacing, set[i].1.len())).collect();
        let (blocks, owners, classes) = kernel_blocks(&set, &members, seed, read, n, 1, (2, 1), false);
        for (m, &i) in members.iter().enumerate() {
            let (q, a, _) = &set[i];
            let joined: Vec<usize> = blocks.iter().zip(&owners).filter(|&(_, &o)| o == m).flat_map(|(b, _)| b.iter().copied()).collect();
            assert_eq!(joined, (q.len()..q.len() + a.len()).collect::<Vec<_>>(), "member {m}: its residue class in order");
        }
        let (f, t) = (Some(false), Some(true));
        assert_eq!(classes, vec![f, None, f, t, f, f, t, f, t, f], "k₋ first on an odd section, a closing short block unread");
        let (whole, whole_owners, whole_classes) = kernel_blocks(&set, &members, seed, read, n, spacing, (2, 1), true);
        assert_eq!((whole_owners, whole_classes), (vec![0, 1, 2], vec![None; 3]));
        assert!(whole.iter().zip(&starts).zip(&members).all(|((b, &r), &i)| b.len() == (r..set[i].1.len()).step_by(spacing).count()));
        assert_eq!(kernel_lengths(true, 18, 0), (18, 18));
        assert_eq!(kernel_lengths(false, 18, log2_q16(18) as i128), (22, 15), "⌈18·2^¼⌉ and ⌊18·2^(−¼)⌋");
        let regions: u128 = members.iter().map(|&i| region_sites(&set[i])).sum();
        let owned: u128 = owners.iter().map(|&o| region_sites(&set[members[o]])).sum();
        let placed: u128 = blocks.iter().zip(&owners).map(|(b, &o)| b.len() as u128 * region_sites(&set[members[o]])).sum();
        assert_eq!(section_work(&SectionLaw::Kernel { owners: &owners }, &set, &members), (2 * regions + 2 * owned, "site_reads"));
        assert_eq!(section_work(&SectionLaw::Conditional { blocks: &blocks, owners: &owners, alphabet: 11 }, &set, &members), (regions + 11 * placed, "site_reads"));
        assert_eq!(section_work(&SectionLaw::Joint { reads: 64 }, &set, &members), (64 * regions, "site_reads"));
        assert_eq!(section_work(&SectionLaw::Writer, &set, &members), (2 + 4 + 7, "places"));
    }

    /// The toy's energy learner: an energy field of one lane over the toy's codec, every family drawn from the key stream (the
    /// pace held at zero), its family lengths open.
    fn toy_energy_learner(codec: &FieldCodec, problems: &Problems) -> FieldLearner {
        let reach = problems.iter().map(|(q, _, _)| q.len() + codec.answer).max().unwrap();
        let d = FieldDeclaration { alphabet: codec.alphabet(), width: 8, heads: 2, modes: 3, still: 1, contacts: 4, ticks: 2, frames: 2, reach, lanes: 1, depth: 0, energy: true };
        let keys: Vec<u8> = (0..1u64 << 13).flat_map(|i| mix(0x5EED, i).to_be_bytes()).collect();
        let mut field = Field::found(d, &keys).unwrap();
        let families = field.layout().families.clone();
        for (n, v) in field.theta.iter_mut().enumerate() {
            let k = mix(0x11E5, n as u64) as u32 as i32 as i64;
            let grain = families.iter().find(|(s, l, _)| (*s..*s + *l).contains(&n)).unwrap().2;
            *v = ((k << grain) >> 32) as i32;
        }
        let l = field.layout().clone();
        field.theta[l.pace..l.pace + d.paced_heads() * (d.alphabet + 1)].fill(0);
        let mut learner = FieldLearner::new(field, 14);
        learner.open_family_rates();
        learner
    }

    /// [definition; theory, November 9 13:29] **A fresh section resumed at a sweep boundary is the uninterrupted one, bit for
    /// bit**, on the host: an energy field of the toy's four problems (every family drawn from the key stream, its family lengths
    /// open), one fresh section from the truths swept four times, keyed as the trainer keys a section, through the trainer's
    /// own sweeps ([`fresh_sweeps_at`]), deposit ([`writes_deposit`]) and averaged constitution. The uninterrupted section runs
    /// on the learner in memory and saves its writes at sweep 2's start ([`SweepWrites`], through its text); the resumed one
    /// loads the learner from the saved state's text, on a fresh realization, and runs sweeps 2 and 3 from the saved writes. Their writes, each sweep's moves, proposals,
    /// energies and retention, the deposit's receipt and the learner's state after the section are the same; the sweeps moved
    /// some write and the learner was not moved by them. A sweep save's text reads back as itself, and a malformed one is refused.
    #[test]
    fn a_fresh_section_resumed_at_a_sweep_is_the_uninterrupted_one() {
        let (codec, problems) = toy();
        let opening = toy_energy_learner(&codec, &problems);
        let state = at_rate(&opening, opening.rate_bits);
        let state_sha = sha256(state.as_bytes()).unwrap();
        let set = encoded_problems(&codec, &problems_of(TOY), &opening.field).unwrap();
        let void = codec.void();
        let asked: Vec<(&[usize], usize)> = set.iter().map(|(q, _, room)| (q.as_slice(), *room)).collect();
        let truths: Vec<Vec<usize>> = set.iter().map(|p| truth_with_voids(void, p, &p.1)).collect();
        let answers: Vec<&[usize]> = set.iter().map(|p| p.1.as_slice()).collect();
        let (sweeps, at, section, read) = (4u64, 2u64, 3usize, 0u64);
        let key = writes_key(0x5EED, read, section);
        type Row = (u64, usize, usize, Vec<i128>, usize);
        // One fresh section from sweep `from`: the sweeps (the writes saved at sweep `at`'s start where `save`), the deposit and
        // the average, as the trainer runs them.
        let section_from = |learner: &mut FieldLearner, active: &mut Vec<Vec<usize>>, from: u64, save: bool| -> (Vec<Row>, holonics::hnn::tower::field::ContrastReceipt, Option<String>) {
            let (mut rows, mut saved): (Vec<Row>, Option<String>) = (Vec::new(), None);
            let before = learner.to_text();
            fresh_sweeps_at(
                &learner.field,
                &asked,
                active,
                from,
                sweeps,
                key,
                void,
                &mut host(),
                &mut |sweep, active| {
                    if save && sweep == at {
                        saved = Some(SweepWrites { read, section, done: sweep, sweeps, key, from_truth: true, state: state_sha.clone(), writes: active.to_vec() }.to_text());
                    }
                    Ok(())
                },
                &mut |sweep, mv, pr, en, active, _| rows.push((sweep, mv, pr, en.to_vec(), retention_milli(active, &answers))),
            )
            .unwrap();
            assert_eq!(learner.to_text(), before, "the sweeps leave the learner as it opened");
            let receipt = writes_deposit(learner, &asked, &truths, active, void, &mut host()).unwrap();
            learner.average_section();
            (rows, receipt, saved)
        };
        // The uninterrupted section runs on the learner as it stands in memory; the resumed one on the saved state's text.
        let mut whole = opening.clone();
        let mut writes: Vec<Vec<usize>> = set.iter().map(|p| p.1.clone()).collect();
        let (rows, receipt, saved) = section_from(&mut whole, &mut writes, 0, true);
        assert_eq!(rows.iter().map(|r| r.0).collect::<Vec<_>>(), vec![1, 2, 3, 4]);
        assert!(rows.iter().any(|r| r.1 > 0), "the sweeps move some write");
        let saved = SweepWrites::from_text(&saved.expect("a save at sweep 2")).unwrap();
        assert_eq!((saved.read, saved.section, saved.done, saved.sweeps, saved.key, &saved.state), (read, section, at, sweeps, key, &state_sha));
        assert_eq!(SweepWrites::from_text(&saved.to_text()).unwrap(), saved, "the save's text reads back as itself");
        let mut resumed = FieldLearner::from_text(&state).unwrap();
        let mut resumed_writes = saved.writes.clone();
        let (resumed_rows, resumed_receipt, _) = section_from(&mut resumed, &mut resumed_writes, saved.done, false);
        assert_eq!(resumed_writes, writes, "the writes");
        assert_eq!(resumed_rows, rows[at as usize..].to_vec(), "each sweep's moves, proposals, energies and retention");
        assert_eq!(resumed_receipt, receipt, "the deposit");
        assert_eq!(resumed.to_text(), whole.to_text(), "the state after the section");
        // A malformed save is refused: a wrong header, a sweep at or past the last, a write whose length is not its classes'.
        let text = saved.to_text();
        assert!(SweepWrites::from_text(&text.replacen("field-sweep-writes v1", "field-sweep-writes v0", 1)).is_err());
        assert!(SweepWrites::from_text(&text.replacen(&format!("done {at} "), "done 4 ", 1)).is_err());
        let first = text.lines().nth(2).unwrap().to_string();
        let parts: Vec<&str> = first.split(' ').collect();
        assert!(SweepWrites::from_text(&text.replacen(&first, &format!("write 0 {} {}", parts[2].parse::<usize>().unwrap() + 1, parts[3]), 1)).is_err());
    }

    /// [measurement; theory, November 9 14:30] **The covector line is a reading.** One fresh section of the toy's four problems
    /// from the truths, swept twice, run in the trainer's order with the reading (the problems' covectors read before the
    /// deposit, the lines after it) and without: the writes and the learner's state after the section are the same bits. Each
    /// line's `norm` is `⌊√Σ g²⌋` of the family's entries of the problems' covectors summed here; `g` stands within
    /// `⌊(n + 1)/2⌋` units of the covector the deposit took, entry by entry; at the run's first section `cos_prev_milli` is `-`,
    /// and against itself a nonzero family's covector reads `1000`. The jackknife reads `√((n − 1)/n·Σ(x − x̄)²)` (three
    /// leave-one-out values 3, 5, 7 give `⌊√(16/3)⌋ = 2`) and none under two problems.
    #[test]
    fn the_covector_line_reads_a_section_and_leaves_its_bits() {
        use num_bigint::BigUint;
        let (codec, problems) = toy();
        let opening = toy_energy_learner(&codec, &problems);
        let set = encoded_problems(&codec, &problems_of(TOY), &opening.field).unwrap();
        let void = codec.void();
        let asked: Vec<(&[usize], usize)> = set.iter().map(|(q, _, room)| (q.as_slice(), *room)).collect();
        let truths: Vec<Vec<usize>> = set.iter().map(|p| truth_with_voids(void, p, &p.1)).collect();
        let key = writes_key(0x5EED, 0, 0);
        let swept = |learner: &FieldLearner| -> Vec<Vec<usize>> {
            let mut active: Vec<Vec<usize>> = set.iter().map(|p| p.1.clone()).collect();
            fresh_sweeps_at(&learner.field, &asked, &mut active, 0, 2, key, void, &mut host(), &mut |_, _| Ok(()), &mut |_, _, _, _, _, _| {}).unwrap();
            active
        };
        let mut plain = opening.clone();
        let plain_writes = swept(&plain);
        writes_deposit(&mut plain, &asked, &truths, &plain_writes, void, &mut host()).unwrap();
        plain.average_section();
        let mut read = opening.clone();
        let writes = swept(&read);
        let pairs = writes_pairs(&read.field, &asked, &truths, &writes, void, &mut host()).unwrap();
        let receipt = writes_deposit(&mut read, &asked, &truths, &writes, void, &mut host()).unwrap();
        read.average_section();
        let formed = read.last_formed_step().expect("the deposit keeps the step it formed").to_vec();
        let (lines, g) = covector_section_lines(&read.field, &pairs, None, &formed, "formed").unwrap();
        assert_eq!(writes, plain_writes, "the writes");
        assert_eq!(read.to_text(), plain.to_text(), "the reading leaves the section's bits");
        assert!(plain_writes.iter().zip(&set).any(|(w, p)| w != &p.1), "the sweeps move some write");
        let field_of = |line: &str, name: &str| -> String { line.split(' ').find_map(|kv| kv.strip_prefix(&format!("{name}="))).unwrap().to_string() };
        let families: Vec<(usize, usize, u32)> = read.field.families_all().into_iter().filter(|f| f.1 > 0).collect();
        assert_eq!(lines.len(), families.len(), "a line a family with entries");
        let n = pairs.len() as i128;
        for (line, &(start, len, _)) in lines.iter().zip(&families) {
            let direct: BigUint = (start..start + len).map(|i| BigUint::from(pairs.iter().map(|p| p[i]).sum::<i128>().unsigned_abs()).pow(2)).sum();
            assert_eq!(field_of(line, "norm"), direct.sqrt().to_string(), "{line}");
            assert_eq!(field_of(line, "cos_prev_milli"), "-", "the run's first section");
            assert_eq!(field_of(line, "step_unit"), "formed");
        }
        assert!(g.iter().zip(&receipt.covector).all(|(a, b)| (a - b).abs() <= (n + 1) / 2), "the problems' sum stands beside the deposit's covector");
        assert!(lines.iter().any(|line| field_of(line, "norm") != "0" && field_of(line, "norm_se") != "-"), "some family reads a covector and its SE");
        let (again, _) = covector_section_lines(&read.field, &pairs, Some(&g), &formed, "formed").unwrap();
        for line in &again {
            if field_of(line, "norm") != "0" {
                assert_eq!(field_of(line, "cos_prev_milli"), "1000", "{line}");
            }
        }
        assert_eq!(jackknife_se(&[3u8, 5, 7].map(BigUint::from)), Some(BigUint::from(2u8)));
        assert_eq!(jackknife_se(&[BigUint::from(9u8)]), None);
        assert_eq!(cosine_milli(&num_bigint::BigInt::from(-6), &BigUint::from(4u8), &BigUint::from(9u8)), Some(-1000), "antiparallel");
        assert_eq!(cosine_milli(&num_bigint::BigInt::from(0), &BigUint::from(0u8), &BigUint::from(9u8)), None, "a zero vector");
    }
}


/// [measurement; agent-inferred, November 4] **`expansion-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD HELD_SHA
/// COUNT`**: the expansion and the volume of the field's state across its ticks (the lens record, §7: information expands
/// and contracts in the geometry), on the first `COUNT` held problems read with their neighbours (the context read's first
/// part). The **volume** of tick `k` is the participation ratio `(tr C)² / tr C²` of the sites' charts `r̂` (`C` their
/// covariance over a region's sites, its effective number of directions out of `D`, every lane's chart together), averaged
/// over the regions. The
/// **expansion** is read against the same regions with every row of the encoding moved by a keyed `±2^(−10)` of its unit:
/// `Δ_k = Σ_t ‖x′_t − x_t‖²` of the faces `x = r̂ · scale` at tick `k`'s opening, and its growth from tick to tick, `½ log₂
/// (Δ_(k+1)/Δ_k)` bits a tick (a finite-time Lyapunov reading: above zero the ticks pull nearby states apart and make
/// information, below zero they bring them together and forget it). A reading only.
pub(super) fn expansion_field(args: &[String], realization: &mut dyn FieldRealization) -> Result<()> {
    if args.len() != 10 {
        return Err("expansion-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD HELD_SHA COUNT".into());
    }
    let started = std::time::Instant::now();
    let learner = FieldLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let field = &learner.field;
    let units = units_of(&args[5], &args[6])?;
    let codec = FieldCodec::from_text(std::str::from_utf8(&pinned_read(&args[3], &args[4], CODEC_BUDGET)?)?, units)?;
    let held = problems_of(&pinned_read(&args[7], &args[8], READ_BUDGET as usize)?);
    let count = positive(&args[9])?;
    let mut owned: Vec<(Vec<usize>, Vec<bool>)> = Vec::new();
    for (q, a) in held.iter().take(count) {
        let (q, a) = (codec.encode(&question_text(q)).map_err(|e| e.to_string())?, codec.encode(a).map_err(|e| e.to_string())?);
        owned.extend(context_regions(codec.void(), &q, &a, q.len() + a.len() + 1).into_iter().take(1));
    }
    let regions: Vec<Region> = owned.iter().map(|(c, u)| Region { classes: c, unresolved: u, faces: &[], locked: &[], echo: &[], domain: None, port: None }).collect();
    let base = realization.read_ticks(field, &regions)?;
    let mut moved = field.clone();
    {
        let l = moved.layout().clone();
        let rows = (moved.declaration.alphabet + 1) * moved.declaration.width;
        let mut z = 0x9E37_79B9_7F4A_7C15u64;
        for v in &mut moved.theta[l.enc..l.enc + rows] {
            z = z.wrapping_mul(0x5851_F42D_4C95_7F2D).wrapping_add(0x1405_7B7E_F767_814F);
            *v += if z >> 63 == 0 { 1 << 6 } else { -(1 << 6) };
        }
    }
    let perturbed = realization.read_ticks(&moved, &regions)?;
    let (dw, lanes) = (field.declaration.width, field.declaration.lanes);
    let ticks = base.first().map_or(0, Vec::len);
    // [measurement; agent-inferred, November 4, §16.40] Each tick is read at its opening and after its current (the pair
    // contact's chart), so its volume and its expansion split into the current's half and the pair contact's half.
    let mut deltas: Vec<[i128; 2]> = vec![[0; 2]; ticks];
    let mut volumes: Vec<[i128; 2]> = vec![[0; 2]; ticks];
    for k in 0..ticks {
        for half in 0..2 {
            let (mut volume_num, mut volume_den) = (0i128, 0i128);
            for (b, p) in base.iter().zip(&perturbed) {
                let (rb, rp) = (&b[k], &p[k]);
                let ((bread, bscale), (pread, pscale)) = if half == 0 { ((&rb.read, &rb.scale), (&rp.read, &rp.scale)) } else { ((&rb.pair_read, &rb.pair_scale), (&rp.pair_read, &rp.pair_scale)) };
                // A site's scales are one a lane, so its count is the read's.
                let sites = bread.len() / dw;
                // The faces' difference, `x = r̂ · scale` on `2^(−32)`, released to `2^(−16)` before it is squared.
                for t in 0..sites {
                    for i in 0..dw {
                        let lane = t * lanes + i / (dw / lanes);
                        let xb = (bread[t * dw + i] as i128 * bscale[lane]) >> 16;
                        let xp = (pread[t * dw + i] as i128 * pscale[lane]) >> 16;
                        let d = (xp - xb) >> 8;
                        deltas[k][half] += d * d;
                    }
                }
                // The volume: integer sums of the charts (each read at `2^(−8)` of its unit), `n² C = n S_ij − S_i S_j`.
                let n = sites as i128;
                let r = |t: usize, i: usize| (bread[t * dw + i] >> 8) as i128;
                let si: Vec<i128> = (0..dw).map(|i| (0..sites).map(|t| r(t, i)).sum()).collect();
                let mut trace = 0i128;
                let mut frob = 0i128;
                for i in 0..dw {
                    for j in i..dw {
                        let sij: i128 = (0..sites).map(|t| r(t, i) * r(t, j)).sum();
                        let c = (n * sij - si[i] * si[j]) >> 16;
                        if i == j {
                            trace += c;
                            frob += c * c;
                        } else {
                            frob += 2 * c * c;
                        }
                    }
                }
                if frob > 0 {
                    volume_num += (trace * trace * 1000) / frob;
                    volume_den += 1;
                }
            }
            volumes[k][half] = if volume_den > 0 { volume_num / volume_den } else { 0 };
        }
    }
    let growth = |from: i128, to: i128| if from > 0 && to > 0 { ((log2_milli(to) - log2_milli(from)) / 2).to_string() } else { "-".to_string() };
    for k in 0..ticks {
        let pair_half = if k + 1 < ticks { growth(deltas[k][1], deltas[k + 1][0]) } else { "-".to_string() };
        println!(
            "FIELD_EXPANSION tick={k} regions={} volume={}.{:03} of {dw} after_current={}.{:03} delta={} growth_millibits_a_tick={} current_millibits={} pair_millibits={pair_half} ms={}",
            regions.len(),
            volumes[k][0] / 1000,
            volumes[k][0] % 1000,
            volumes[k][1] / 1000,
            volumes[k][1] % 1000,
            deltas[k][0],
            if k > 0 { growth(deltas[k - 1][0], deltas[k][0]) } else { "-".to_string() },
            growth(deltas[k][0], deltas[k][1]),
            started.elapsed().as_millis()
        );
    }
    Ok(())
}

/// `log₂ v` in thousandths for `v > 0`: the whole part from the width, the mantissa's through the `ln 2`/exponential
/// navigator's inverse face ([`holonics::hnn::keyed_modes::log2_face`]) on `2^(−10)`.
fn log2_milli(v: i128) -> i128 {
    let v = v.unsigned_abs().max(1);
    let width = 128 - v.leading_zeros() as i128;
    let p = if width > 62 { v >> (width - 62) } else { v << (62 - width) };
    let frac = holonics::hnn::keyed_modes::log2_face(p, 10);
    ((width << 10) + frac) * 1000 >> 10
}

/// Nats on `2^(−20)` from bits on `2^(−20)` (`ln 2` on `2^(−30)`), and a value on `2^(−20)` written in decimal with six
/// places (integers alone).
fn nats_q20(bits: i128) -> i128 {
    let v = bits * LN2_Q30;
    if v >= 0 { (v + (1 << 29)) >> 30 } else { -((-v + (1 << 29)) >> 30) }
}

fn decimal_q20(v: i128) -> String {
    let m = v.unsigned_abs();
    let f = ((m & ((1 << 20) - 1)) * 1_000_000 + (1 << 19)) >> 20;
    let (whole, f) = if f == 1_000_000 { ((m >> 20) + 1, 0) } else { (m >> 20, f) };
    format!("{}{whole}.{f:06}", if v < 0 { "-" } else { "" })
}

/// A problem set read from `text` and encoded: each question and answer, the answer shorter than the room and the region
/// within the field's reach; its opening region (the question resolved, the answer's room open) and its places (the answer's
/// cells and its first void).
fn plate_regions(codec: &FieldCodec, field: &Field, text: &[u8]) -> Result<Vec<(Vec<usize>, Vec<bool>, std::ops::Range<usize>)>> {
    let mut out = Vec::new();
    for (q, a) in problems_of(text) {
        let q = codec.encode(&question_text(&q)).map_err(|e| e.to_string())?;
        let a = codec.encode(&a).map_err(|e| e.to_string())?;
        if a.len() >= codec.answer || q.len() + codec.answer > field.declaration.reach {
            continue;
        }
        let classes = region_classes(codec, &q, &a, q.len() + codec.answer);
        let open = (0..classes.len()).map(|t| t >= q.len()).collect();
        out.push((classes, open, q.len()..q.len() + a.len() + 1));
    }
    Ok(out)
}

/// A plate's training reading: its true letters' counts `N_(p, a)`, and the face's own expected counts `F_(p, a) = Σ f(a)`
/// over the same places, each share formed on `2^(−40)` to the floor with its remainder carried on `2^(−72)` (the remainder
/// over the face's total, to the nearest), so `F = (shares + carried 2^(−32))` on `2^(−40)`.
#[derive(Clone, Default)]
pub(super) struct PlateCounts {
    pub(super) n: Vec<u64>,
    f: Vec<u128>,
    carried: Vec<i128>,
}

impl PlateCounts {
    pub(super) fn new(a: usize) -> Self {
        Self { n: vec![0; a], f: vec![0; a], carried: vec![0; a] }
    }

    pub(super) fn add(&mut self, face: &holonics::hnn::tower::TowerFace, truth: usize) {
        self.n[truth] += 1;
        for (c, &m) in face.masses.iter().enumerate() {
            let q = (m << 40) / face.total;
            let rem = (m << 40) - q * face.total;
            self.f[c] += q;
            self.carried[c] += (((rem << 32) + face.total / 2) / face.total) as i128;
        }
    }

    /// `F_(p, a)` on `2^(−20)`, its carried remainder folded in, to the nearest.
    pub(super) fn expected(&self, c: usize) -> u128 {
        let on40 = (self.f[c] as i128 + ((self.carried[c] + (1 << 31)) >> 32)).max(0) as u128;
        (on40 + (1 << 19)) >> 20
    }

    pub(super) fn places(&self) -> u64 {
        self.n.iter().sum()
    }
}

/// [measurement; theory, November 9 19:43 and 20:04] `plate-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD
/// HELD_SHA TRAIN TRAIN_SHA COUNT TRAIN_COUNT OUT`: **the plate census**, a forward-only reading. A site's plate is the tuple
/// of the classes its key word holds in each head at the last tick ([`Field::read_plates`]). (1) Each held place (the first
/// `COUNT` held problems' opening regions as the held read meets them: the answer's cells and its first void, every room
/// place open) is read with its plate and its code `−ln f(truth)`. (2) One forward pass over TRAIN's openings (its first
/// `TRAIN_COUNT` problems, all of them at zero) counts at every answer place, by plate, the true letters `N_(p, a)` and the
/// face's own expected counts `F_(p, a) = Σ f(a)` in the same visit, and each held place is coded again under the lens
/// `f′(a) ∝ f(a) (N_(p, a) + 1)/(F_(p, a) + 1)` renormalized at the place (theory, 20:04: the face already depends on the
/// state that fixes the plate, so the letters' marginal `N_a` would count the plate's composition twice; the marginal form
/// `(N_(p, a) + 1)/(N_a + 1)` is kept beside it). One count is added on both sides (a declared prior); each lens mass is
/// released to its own grain. [theory, November 9 20:13] **A depth ladder**: the joint plate is read at each depth `d` of
/// `1..=b` trits a head (each head's class taken mod `3^d`, its first `d` shells; `3^(Hd)` cells), since at the full depth
/// most cells are thin; each head alone is read at the full depth. `PLATES.tsv` (each depth's joint plates), `HEADS.tsv` (each
/// head and class), `OCCUPANCY.tsv` (at each depth, the occupied plates by their training places in octave bands 1, 2–3,
/// 4–7, …, with the held places in each band, and the held places on no training plate), and `FIELD_PLATES` (one a depth),
/// `FIELD_PLATES_HEAD` and `FIELD_PLATES_OCCUPANCY` lines. [theory, November 9 20:51] A second visit over TRAIN reads TRAIN's
/// own code under each depth's lenses beside its plain code (`FIELD_PLATES_TRAIN`, one line a depth).
pub(super) fn plate_field(args: &[String], realization: &mut dyn FieldRealization) -> Result<()> {
    if args.len() != 14 {
        return Err("plate-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD HELD_SHA TRAIN TRAIN_SHA COUNT TRAIN_COUNT OUT".into());
    }
    let started = std::time::Instant::now();
    let mut learner = FieldLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    declared_clocks(&mut learner.field);
    let field = &learner.field;
    let units = units_of(&args[5], &args[6])?;
    let codec = FieldCodec::from_text(std::str::from_utf8(&pinned_read(&args[3], &args[4], CODEC_BUDGET)?)?, units)?;
    let mut held = plate_regions(&codec, field, &pinned_read(&args[7], &args[8], READ_BUDGET as usize)?)?;
    held.truncate(count(&args[11])?);
    let mut train = plate_regions(&codec, field, &pinned_read(&args[9], &args[10], READ_BUDGET as usize)?)?;
    if let Some(n) = Some(count(&args[12])?).filter(|&n| n > 0) {
        train.truncate(n);
    }
    let out = Path::new(&args[13]);
    std::fs::create_dir(out)?;
    type Face = holonics::hnn::tower::TowerFace;
    let a = field.declaration.alphabet;
    let heads = field.declaration.heads;
    // Each region's places with their plates and faces, read in chunks.
    let mut read = |set: &[(Vec<usize>, Vec<bool>, std::ops::Range<usize>)], visit: &mut dyn FnMut(&[u32], &Face, usize)| -> Result<()> {
        for chunk in set.chunks(64) {
            let views: Vec<Region> = chunk.iter().map(|(c, u, _)| Region { classes: c, unresolved: u, faces: &[], locked: &[], echo: &[], domain: None, port: None }).collect();
            let (faces, plates) = realization.read_plates(field, &views).map_err(|e| e.to_string())?;
            for (((classes, _, places), faces), plates) in chunk.iter().zip(&faces).zip(&plates) {
                for t in places.clone() {
                    let face = faces[t].as_ref().ok_or("a held place without a face")?;
                    visit(&plates[t * heads..(t + 1) * heads], face, classes[t]);
                }
            }
        }
        Ok(())
    };
    // The keys: the joint plate at each depth `d` (`(0, d)`, each class mod 3^d) and each head's class alone at the full depth
    // (`(1, h)`).
    let trits = field.declaration.class_trits();
    let keys = |plate: &[u32]| -> Vec<(u8, usize, Vec<u32>)> {
        (1..=trits).map(|d| (0u8, d, plate.iter().map(|&c| c % 3u32.pow(d as u32)).collect())).chain((0..heads).map(|h| (1u8, h, vec![plate[h]]))).collect()
    };
    let mut counts: std::collections::BTreeMap<(u8, usize, Vec<u32>), PlateCounts> = std::collections::BTreeMap::new();
    let mut totals = vec![0u64; a];
    read(&train, &mut |plate: &[u32], face: &Face, truth: usize| {
        for key in keys(plate) {
            counts.entry(key).or_insert_with(|| PlateCounts::new(a)).add(face, truth);
        }
        totals[truth] += 1;
    })?;
    let train_ms = started.elapsed().as_millis();
    // Each held key's places and codes (bits on 2^(−20)): plain, the lens against the face's own counts, the marginal lens.
    let lens = |face: &Face, truth: usize, ratio: &dyn Fn(usize) -> (u128, u128)| -> i128 {
        let masses: Vec<u128> = face.masses.iter().enumerate().map(|(c, &m)| { let (num, den) = ratio(c); (m * num) / den.max(1) }).collect();
        let total = masses.iter().sum();
        Face { masses, total }.code(truth) as i128
    };
    // [theory, November 9 20:51] A second visit over TRAIN reads its own code under each depth's lenses, beside the plain code:
    // the counts were fit on these places, so the residual lens cannot code them much above the plain code (a check of the
    // build), and its gain here against the held gain reads what a plate's counts carry to unseen answers.
    let mut train_codes: Vec<[i128; 3]> = vec![[0; 3]; trits + 1];
    let mut train_read = 0i128;
    read(&train, &mut |plate: &[u32], face: &Face, truth: usize| {
        train_read += 1;
        let plain = face.code(truth) as i128;
        for key in keys(plate).into_iter().filter(|k| k.0 == 0) {
            let (own, marginal) = match counts.get(&key) {
                Some(k) => (lens(face, truth, &|c| ((k.n[c] as u128 + 1) << 20, k.expected(c) + (1 << 20))), lens(face, truth, &|c| (k.n[c] as u128 + 1, totals[c] as u128 + 1))),
                None => (plain, plain),
            };
            let slot = &mut train_codes[key.1];
            *slot = [slot[0] + plain, slot[1] + own, slot[2] + marginal];
        }
    })?;
    let train_lens_ms = started.elapsed().as_millis();
    let mut held_keys: std::collections::BTreeMap<(u8, usize, Vec<u32>), [i128; 4]> = std::collections::BTreeMap::new();
    let mut held_places = 0i128;
    read(&held, &mut |plate: &[u32], face: &Face, truth: usize| {
        held_places += 1;
        for key in keys(plate) {
            let plain = face.code(truth) as i128;
            let (own, marginal) = match counts.get(&key) {
                // (N + 1) 2^20 over (F + 1) on 2^(−20); (N + 1) over (N_a + 1).
                Some(k) => (lens(face, truth, &|c| ((k.n[c] as u128 + 1) << 20, k.expected(c) + (1 << 20))), lens(face, truth, &|c| (k.n[c] as u128 + 1, totals[c] as u128 + 1))),
                None => (plain, plain),
            };
            let slot = held_keys.entry(key).or_default();
            *slot = [slot[0] + 1, slot[1] + plain, slot[2] + own, slot[3] + marginal];
        }
    })?;
    let mean = |v: i128, n: i128| if n == 0 { "-".to_string() } else { decimal_q20(nats_q20(v) / n) };
    // The joint plates and each head's classes, held places first.
    let mut joint = rows_file(&out.join("PLATES.tsv"), "depth\tplate\theld_places\tcode_nats\tlens_code_nats\tmarginal_lens_code_nats\ttrain_places\n")?;
    let mut by_head = rows_file(&out.join("HEADS.tsv"), "head\tclass\theld_places\tcode_nats\tlens_code_nats\tmarginal_lens_code_nats\ttrain_places\n")?;
    let mut rows: Vec<(&(u8, usize, Vec<u32>), &[i128; 4])> = held_keys.iter().collect();
    rows.sort_by_key(|(k, s)| (k.0, k.1, std::cmp::Reverse(s[0]), k.2.clone()));
    let mut sums: std::collections::BTreeMap<(u8, usize), [i128; 4]> = std::collections::BTreeMap::new();
    for (key, s) in rows {
        let train_places = counts.get(key).map_or(0, PlateCounts::places);
        let name: Vec<String> = key.2.iter().map(u32::to_string).collect();
        let cells = format!("{}\t{}\t{}\t{}\t{train_places}\n", s[0], mean(s[1], s[0]), mean(s[2], s[0]), mean(s[3], s[0]));
        if key.0 == 0 {
            row(&mut joint, &format!("{}\t{}\t{cells}", key.1, name.join(".")))?;
        } else {
            row(&mut by_head, &format!("{}\t{}\t{cells}", key.1, name.join(".")))?;
        }
        let sum = sums.entry((key.0, key.1)).or_default();
        for i in 0..4 {
            sum[i] += s[i];
        }
    }
    // Occupancy at each depth: the occupied plates by their training places in octave bands, with the held places on each.
    let mut occupancy = rows_file(&out.join("OCCUPANCY.tsv"), "depth\tband\ttrain_places_from\ttrain_places_to\tplates\theld_places\theld_share_millionths\n")?;
    let share = |n: i128| if held_places == 0 { 0 } else { n * 1_000_000 / held_places };
    for d in 1..=trits {
        let mut bands: std::collections::BTreeMap<u32, (u64, i128)> = std::collections::BTreeMap::new();
        for (_, k) in counts.iter().filter(|(key, _)| key.0 == 0 && key.1 == d) {
            bands.entry(63 - k.places().max(1).leading_zeros()).or_default().0 += 1;
        }
        let mut unseen = 0i128;
        for (key, s) in held_keys.iter().filter(|(key, _)| key.0 == 0 && key.1 == d) {
            match counts.get(key) {
                Some(k) => bands.entry(63 - k.places().max(1).leading_zeros()).or_default().1 += s[0],
                None => unseen += s[0],
            }
        }
        for (&b, &(plates, held_in)) in &bands {
            row(&mut occupancy, &format!("{d}\t{b}\t{}\t{}\t{plates}\t{held_in}\t{}\n", 1u64 << b, (2u64 << b) - 1, share(held_in)))?;
            println!("FIELD_PLATES_OCCUPANCY depth={d} band={b} train_places={}..{} plates={plates} held_places={held_in} held_share_millionths={}", 1u64 << b, (2u64 << b) - 1, share(held_in));
        }
        row(&mut occupancy, &format!("{d}\t-\t0\t0\t0\t{unseen}\t{}\n", share(unseen)))?;
        println!("FIELD_PLATES_OCCUPANCY depth={d} band=none plates=0 held_places={unseen} held_share_millionths={}", share(unseen));
    }
    for (d, c) in train_codes.iter().enumerate().skip(1) {
        println!("FIELD_PLATES_TRAIN depth={d} train_places={train_read} code_nats={} lens_code_nats={} marginal_lens_code_nats={} train_lens_ms={}", mean(c[0], train_read), mean(c[1], train_read), mean(c[2], train_read), train_lens_ms - train_ms);
    }
    for (&(tag, which), s) in &sums {
        let occupied = counts.keys().filter(|k| k.0 == tag && k.1 == which).count();
        let held_cells = held_keys.keys().filter(|k| k.0 == tag && k.1 == which).count();
        if tag == 0 {
            println!(
                "FIELD_PLATES depth={which} cells={} held_problems={} held_places={} held_plates={held_cells} train_problems={} train_places={} train_plates={occupied} code_nats={} lens_code_nats={} marginal_lens_code_nats={} train_ms={train_ms} ms={}",
                3u128.pow((heads * which) as u32),
                held.len(),
                s[0],
                train.len(),
                totals.iter().sum::<u64>(),
                mean(s[1], s[0]),
                mean(s[2], s[0]),
                mean(s[3], s[0]),
                started.elapsed().as_millis()
            );
        } else {
            println!("FIELD_PLATES_HEAD head={which} held_classes={held_cells} train_classes={occupied} code_nats={} lens_code_nats={} marginal_lens_code_nats={}", mean(s[1], s[0]), mean(s[2], s[0]), mean(s[3], s[0]));
        }
    }
    Ok(())
}

/// [definition; theory, November 9 19:43 and 21:12] `exchange-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD
/// HELD_SHA COUNT SWEEPS H_MILLINATS MOVES STOP_MS OUT`: **the certified exchange walk** ([`Field::exchange_walk`]; `MOVES` its
/// proposal cap, a defect detector). The keyed write given held's
/// lengths (`FIELD_WRITER_LENGTHS`, required; the writer's laws as `length-field` reads them, refine zero), then the walk
/// from it: composition held, two places' letters exchanged where the gain from the current faces passes `h`
/// (`H_MILLINATS` thousandths of a nat, read on the codes' grain: `⌈H 2^50 / (1000 ln 2)⌉` on `2^(−20)` bits), at most
/// `MOVES` moves a problem. `KEYED.tsv` and `SAMPLE.tsv` hold the keyed write and the walk's in `length-field`'s format,
/// `MOVES.tsv` every move (its places, gain and heat at each place, in nats); `FIELD_EXCHANGE` a line a problem (its moves,
/// summed gain, and the heat a move: first, last and its fall), and `FIELD_EXCHANGE_DONE`.
pub(super) fn exchange_field(args: &[String], realization: &mut dyn FieldRealization) -> Result<()> {
    if args.len() != 15 {
        return Err("exchange-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD HELD_SHA COUNT SWEEPS H_MILLINATS MOVES STOP_MS OUT".into());
    }
    let started = std::time::Instant::now();
    let mut learner = FieldLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    declared_clocks(&mut learner.field);
    let field = &learner.field;
    let units = units_of(&args[5], &args[6])?;
    let codec = FieldCodec::from_text(std::str::from_utf8(&pinned_read(&args[3], &args[4], CODEC_BUDGET)?)?, units)?;
    let held = problems_of(&pinned_read(&args[7], &args[8], READ_BUDGET as usize)?);
    let (limit, sweeps, h_milli, moves, stop_ms) = (count(&args[9])?, positive(&args[10])?, count(&args[11])?, positive(&args[12])?, positive(&args[13])? as u128);
    let out = Path::new(&args[14]);
    std::fs::create_dir(out)?;
    let held = &held[..limit.min(held.len())];
    let seed = u64::from_str_radix(args[2].get(..16).ok_or("a writer's key of fewer than sixteen hex digits")?, 16).map_err(|_| "a writer's key that is not hexadecimal")?;
    let requests: Vec<(Vec<usize>, usize)> = held.iter().map(|(question, _)| opening(&codec, field, question, b"")).collect::<std::result::Result<_, String>>()?;
    let problems: Vec<(&[usize], usize)> = requests.iter().map(|(q, n)| (q.as_slice(), *n)).collect();
    let keyed = keyed_write(field, &codec, &problems, sweeps, seed, realization, &mut |_, _| started.elapsed().as_millis() <= stop_ms)?;
    let keyed_ms = started.elapsed().as_millis();
    exchange_report(field, &codec, &problems, &keyed, "keyed", h_milli, moves, out, started, keyed_ms, realization, &mut |_| started.elapsed().as_millis() <= stop_ms)
}

/// The keyed write given held's lengths (`FIELD_WRITER_LENGTHS`, required; the writer's laws as `length-field` reads them,
/// refine zero) that [`exchange_field`] and [`settle_field`] start from; `sweep` as [`Field::sample_runs`]'.
fn keyed_write(field: &Field, codec: &FieldCodec, problems: &[(&[usize], usize)], sweeps: usize, seed: u64, realization: &mut dyn FieldRealization, sweep: &mut dyn FnMut(usize, usize) -> bool) -> Result<Vec<Vec<usize>>> {
    let void = codec.void();
    let WriterLaw { run_bits, near_tail, place_order, one_end, rest, spans, refine_order } = WriterLaw::from_env()?;
    let path = std::env::var("FIELD_WRITER_LENGTHS").map_err(|_| "the walk writes given held's lengths: FIELD_WRITER_LENGTHS")?;
    let mut by: std::collections::BTreeMap<usize, usize> = std::collections::BTreeMap::new();
    for l in std::fs::read_to_string(path)?.lines().skip(1) {
        let mut c = l.split('\t');
        if let (Some(k), Some(w)) = (c.next().and_then(|v| v.parse().ok()), c.nth(1).and_then(|v| v.parse().ok())) {
            by.insert(k, w);
        }
    }
    let given: Vec<usize> = (0..problems.len()).map(|k| by.get(&k).copied().ok_or("a problem with no length in FIELD_WRITER_LENGTHS")).collect::<std::result::Result<Vec<usize>, _>>()?.into_iter().zip(problems).map(|(l, &(_, n))| l.min(n)).collect();
    Ok(field.sample_runs(problems, sweeps, 0, void, seed, run_bits << 20, near_tail, place_order, Some(&given), one_end, rest, spans, None, refine_order, realization, sweep, &mut |_| {}).map_err(|e| e.to_string())?)
}

/// [definition; theory, November 10 01:36] `settle-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD HELD_SHA COUNT
/// SWEEPS H_MILLINATS PASSES OUT`: **the parallel certified settle** ([`Field::settle`], the exchange walk's law and `h`) from
/// [`exchange_field`]'s keyed write, at most `PASSES` passes (a bound by count). `KEYED.tsv` the write, `SAMPLE.pass<k>.tsv`
/// the answers at every pass (`k` 0 the write), `SAMPLE.tsv` the end, all private; `MOVES.tsv` each kept exchange's proposed
/// gain and attributed fall in nats. `FIELD_SETTLE_PASS` a pass (flushed): its kept and undone exchanges, the pooled code, the
/// share of its re-read's code change outside every claimed neighbourhood (millionths of `Σ |c_t − c′_t|`), and its elapsed
/// time; `FIELD_SETTLE` a problem: its code a place keyed and at its end, its kept exchanges a letter, whether it rested;
/// `FIELD_SETTLE_DONE`.
pub(super) fn settle_field(args: &[String], realization: &mut dyn FieldRealization) -> Result<()> {
    if args.len() != 14 {
        return Err("settle-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD HELD_SHA COUNT SWEEPS H_MILLINATS PASSES OUT".into());
    }
    let started = std::time::Instant::now();
    let mut learner = FieldLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    declared_clocks(&mut learner.field);
    let field = &learner.field;
    let units = units_of(&args[5], &args[6])?;
    let codec = FieldCodec::from_text(std::str::from_utf8(&pinned_read(&args[3], &args[4], CODEC_BUDGET)?)?, units)?;
    let held = problems_of(&pinned_read(&args[7], &args[8], READ_BUDGET as usize)?);
    let (limit, sweeps, h_milli, passes) = (count(&args[9])?, positive(&args[10])?, count(&args[11])?, count(&args[12])?);
    let out = Path::new(&args[13]);
    std::fs::create_dir(out)?;
    let held = &held[..limit.min(held.len())];
    let seed = u64::from_str_radix(args[2].get(..16).ok_or("a writer's key of fewer than sixteen hex digits")?, 16).map_err(|_| "a writer's key that is not hexadecimal")?;
    let requests: Vec<(Vec<usize>, usize)> = held.iter().map(|(question, _)| opening(&codec, field, question, b"")).collect::<std::result::Result<_, String>>()?;
    let problems: Vec<(&[usize], usize)> = requests.iter().map(|(q, n)| (q.as_slice(), *n)).collect();
    let keyed = keyed_write(field, &codec, &problems, sweeps, seed, realization, &mut |_, _| true)?;
    let keyed_ms = started.elapsed().as_millis();
    let void = codec.void();
    let write = |name: &str, answers: &[Vec<usize>]| -> Result<()> {
        let mut file = rows_file(&out.join(name), "")?;
        for (k, places) in answers.iter().enumerate() {
            let written = places.iter().take_while(|&&c| c != void).count();
            row(&mut file, &format!("{k}\t{}\n", escaped(&codec.decode(&places[..written])))).map_err(|e| e.to_string())?;
        }
        Ok(())
    };
    write("KEYED.tsv", &keyed)?;
    // `h` on the codes' 2^(−20) bits: H thousandths of a nat over ln 2, rounded up.
    let h = (((h_milli as i128) << 50) + 1000 * LN2_Q30 - 1) / (1000 * LN2_Q30);
    let mut saved: Result<()> = Ok(());
    let (settled, records) = field
        .settle(&problems, &keyed, void, h, realization, &mut |p| {
            let share = if p.changed == 0 { 0 } else { p.outside * 1_000_000 / p.changed };
            println!("FIELD_SETTLE_PASS pass={} elapsed_ms={} active={} kept={} undone={} c_nats={} entropy_nats={} outside_share_millionths={share} outside_nats={} changed_nats={}", p.pass, started.elapsed().as_millis(), p.active, p.kept, p.undone, decimal_q20(nats_q20(p.code)), decimal_q20(nats_q20(p.entropy)), decimal_q20(nats_q20(p.outside)), decimal_q20(nats_q20(p.changed)));
            let _ = std::io::Write::flush(&mut std::io::stdout());
            if let Err(e) = write(&format!("SAMPLE.pass{}.tsv", p.pass), p.answers) {
                saved = Err(e);
                return false;
            }
            p.pass < passes
        })
        .map_err(|e| e.to_string())?;
    saved?;
    write("SAMPLE.tsv", &settled)?;
    let mut file = rows_file(&out.join("MOVES.tsv"), "problem\tmove\ti\tj\tproposed_gain_nats\tattributed_fall_nats\n")?;
    let (mut kept, mut undone, mut rested, mut places, mut start, mut end) = (0usize, 0usize, 0usize, 0usize, 0i128, 0i128);
    for (k, r) in records.iter().enumerate() {
        for (n, m) in r.kept.iter().enumerate() {
            row(&mut file, &format!("{k}\t{}\t{}\t{}\t{}\t{}\n", n + 1, m.i, m.j, decimal_q20(nats_q20(m.gain)), decimal_q20(nats_q20(m.fall))))?;
        }
        let a_place = |c: i128| if r.places == 0 { "-".to_string() } else { decimal_q20(nats_q20(c) / r.places as i128) };
        let a_letter = if r.places == 0 { 0 } else { r.kept.len() * 1000 / r.places };
        println!("FIELD_SETTLE problem={k} letters={} code_keyed_nats_a_place={} code_end_nats_a_place={} kept={} undone={} moves_a_letter={}.{:03} at_rest={}", r.places, a_place(r.start), a_place(r.end), r.kept.len(), r.undone, a_letter / 1000, a_letter % 1000, r.rested);
        (kept, undone, rested, places, start, end) = (kept + r.kept.len(), undone + r.undone, rested + usize::from(r.rested), places + r.places, start + r.start, end + r.end);
    }
    let pooled = |c: i128| if places == 0 { "-".to_string() } else { decimal_q20(nats_q20(c) / places as i128) };
    println!("FIELD_SETTLE_DONE problems={} at_rest={rested} h_millinats={h_milli} passes_bound={passes} kept={kept} undone={undone} letters={places} code_keyed_nats_a_place={} code_end_nats_a_place={} fall_nats={} keyed_ms={keyed_ms} ms={}", problems.len(), pooled(start), pooled(end), decimal_q20(nats_q20(start - end)), started.elapsed().as_millis());
    Ok(())
}

/// [definition; theory, November 10 01:21] `exchange-held-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD HELD_SHA
/// COUNT H_MILLINATS MOVES PASSES OUT`: **the certified exchange walk from given answers**: [`exchange_field`]'s walk, law and
/// `h`, started from the held file's own reference answers for the same first `COUNT` problems (each cut to its room) instead of
/// the keyed write, and stopped by pass count: `PASSES` passes, never time. `HELD.tsv` holds the start (the references as the
/// walk reads them), `SAMPLE.tsv` the walk's end, both private; every other output as `exchange-field`'s.
pub(super) fn exchange_held_field(args: &[String], realization: &mut dyn FieldRealization) -> Result<()> {
    if args.len() != 14 {
        return Err("exchange-held-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD HELD_SHA COUNT H_MILLINATS MOVES PASSES OUT".into());
    }
    let started = std::time::Instant::now();
    let mut learner = FieldLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    declared_clocks(&mut learner.field);
    let field = &learner.field;
    let units = units_of(&args[5], &args[6])?;
    let codec = FieldCodec::from_text(std::str::from_utf8(&pinned_read(&args[3], &args[4], CODEC_BUDGET)?)?, units)?;
    let held = problems_of(&pinned_read(&args[7], &args[8], READ_BUDGET as usize)?);
    let (limit, h_milli, moves, passes) = (count(&args[9])?, count(&args[10])?, positive(&args[11])?, count(&args[12])?);
    let out = Path::new(&args[13]);
    std::fs::create_dir(out)?;
    let held = &held[..limit.min(held.len())];
    let requests: Vec<(Vec<usize>, usize)> = held.iter().map(|(question, _)| opening(&codec, field, question, b"")).collect::<std::result::Result<_, String>>()?;
    let problems: Vec<(&[usize], usize)> = requests.iter().map(|(q, n)| (q.as_slice(), *n)).collect();
    // Each reference answer's letters, cut to its room (the walk reads a written answer's letters up to its first void).
    let mut cut = 0usize;
    let given: Vec<Vec<usize>> = held
        .iter()
        .zip(&problems)
        .map(|((_, a), &(_, room))| {
            let mut letters = codec.encode(a).map_err(|e| e.to_string())?;
            cut += usize::from(letters.len() > room);
            letters.truncate(room);
            Ok(letters)
        })
        .collect::<std::result::Result<_, String>>()?;
    println!("FIELD_EXCHANGE_START start=held problems={} letters={} cut_to_room={cut} passes={passes}", given.len(), given.iter().map(Vec::len).sum::<usize>());
    exchange_report(field, &codec, &problems, &given, "held", h_milli, moves, out, started, started.elapsed().as_millis(), realization, &mut |p| p.pass < passes)
}

/// The certified exchange walk from `start` (`name` its kind: the keyed write or the held references) and its report, as
/// [`exchange_field`] prints it: `FIELD_EXCHANGE_PASS` a pass (flushed), `FIELD_EXCHANGE` a problem, `MOVES.tsv`, and
/// `FIELD_EXCHANGE_DONE` with the pooled code a place at the start and the end; `go` is shown each pass and stops the walk.
#[allow(clippy::too_many_arguments)]
fn exchange_report(field: &Field, codec: &FieldCodec, problems: &[(&[usize], usize)], start: &[Vec<usize>], name: &str, h_milli: usize, moves: usize, out: &Path, started: std::time::Instant, opened_ms: u128, realization: &mut dyn FieldRealization, go: &mut dyn FnMut(&holonics::hnn::tower::field::ExchangePass) -> bool) -> Result<()> {
    let void = codec.void();
    let write = |file_name: &str, answers: &[Vec<usize>]| -> Result<()> {
        let mut file = rows_file(&out.join(file_name), "")?;
        for (k, places) in answers.iter().enumerate() {
            let written = places.iter().take_while(|&&c| c != void).count();
            row(&mut file, &format!("{k}\t{}\n", escaped(&codec.decode(&places[..written])))).map_err(|e| e.to_string())?;
        }
        Ok(())
    };
    write(if name == "keyed" { "KEYED.tsv" } else { "HELD.tsv" }, start)?;
    // `h` on the codes' 2^(−20) bits: H thousandths of a nat over ln 2, rounded up.
    let h = (((h_milli as i128) << 50) + 1000 * LN2_Q30 - 1) / (1000 * LN2_Q30);
    let (walked, records) = field
        .exchange_walk(problems, start, void, h, moves, realization, &mut |p| {
            // [theory, November 9 22:32] One progress line a pass, flushed.
            println!("FIELD_EXCHANGE_PASS pass={} elapsed_ms={} active={} accepted={} refused={} c_nats={} entropy_nats={}", p.pass, started.elapsed().as_millis(), p.active, p.accepted, p.refused, decimal_q20(nats_q20(p.code)), decimal_q20(nats_q20(p.entropy)));
            let _ = std::io::Write::flush(&mut std::io::stdout());
            go(p)
        })
        .map_err(|e| e.to_string())?;
    write("SAMPLE.tsv", &walked)?;
    // [theory, November 9 21:12] Each standing move's proposed gain against its certified fall, in nats; each problem's code a
    // place at the start and at its end, its standing and refused moves; a problem at the cap is a defect, not a rest.
    let mut file = rows_file(&out.join("MOVES.tsv"), "problem\tmove\ti\tj\tproposed_gain_nats\tcertified_fall_nats\n")?;
    let (mut standing, mut refused, mut defects, mut fall) = (0usize, 0usize, 0usize, 0i128);
    let (mut rested, mut unrested) = (0usize, 0usize);
    let (mut places, mut code_start, mut code_end) = (0usize, 0i128, 0i128);
    for (k, r) in records.iter().enumerate() {
        for (n, m) in r.moves.iter().enumerate() {
            row(&mut file, &format!("{k}\t{}\t{}\t{}\t{}\t{}\n", n + 1, m.i, m.j, decimal_q20(nats_q20(m.gain)), decimal_q20(nats_q20(m.fall))))?;
        }
        let a_place = |c: i128| if r.places == 0 { "-".to_string() } else { decimal_q20(nats_q20(c) / r.places as i128) };
        let heat = |m: Option<&holonics::hnn::tower::field::ExchangeMove>| m.map_or("-".to_string(), |m| decimal_q20(nats_q20(m.fall)));
        println!(
            "FIELD_EXCHANGE problem={k} letters={} code_{name}_nats_a_place={} code_end_nats_a_place={} standing={} refused={} at_rest={} defect={} unrested={} fall_nats={} heat_first_nats={} heat_last_nats={}",
            r.places,
            a_place(r.start),
            a_place(r.end),
            r.moves.len(),
            r.refused,
            r.rested,
            r.capped,
            !r.rested && !r.capped,
            decimal_q20(nats_q20(r.start - r.end)),
            heat(r.moves.first()),
            heat(r.moves.last())
        );
        (standing, refused, defects, fall) = (standing + r.moves.len(), refused + r.refused, defects + usize::from(r.capped), fall + r.start - r.end);
        (rested, unrested) = (rested + usize::from(r.rested), unrested + usize::from(!r.rested && !r.capped));
        (places, code_start, code_end) = (places + r.places, code_start + r.start, code_end + r.end);
    }
    let pooled = |c: i128| if places == 0 { "-".to_string() } else { decimal_q20(nats_q20(c) / places as i128) };
    println!(
        "FIELD_EXCHANGE_DONE problems={} start={name} at_rest={rested} defects={defects} unrested={unrested} h_millinats={h_milli} proposal_cap={moves} standing={standing} refused={refused} fall_nats={} letters={places} code_start_nats_a_place={} code_end_nats_a_place={} {name}_ms={opened_ms} ms={}",
        problems.len(),
        decimal_q20(nats_q20(fall)),
        pooled(code_start),
        pooled(code_end),
        started.elapsed().as_millis()
    );
    Ok(())
}

/// [definition; theory, November 9 21:43] **A census table at one depth**: each plate (each head's class mod `3^d`) with its
/// true letters' counts `N_(p, a)` and the face's own expected counts `F_(p, a)` on `2^(−20)` ([`PlateCounts::expected`]).
pub(super) type LensTable = std::collections::BTreeMap<Vec<u32>, (Vec<u64>, Vec<u128>)>;

/// [definition; theory, November 9 21:43] **The residual lens on a face**: `f′(a) ∝ f(a) (N_(p, a) + 1)/(F_(p, a) + 1)` at the
/// site's plate `p` (its classes mod `3^d`), each mass released to its own grain; a plate the table does not hold leaves the face
/// as it is.
pub(super) fn lensed_face(face: &holonics::hnn::tower::TowerFace, plate: &[u32], depth: u32, table: &LensTable) -> holonics::hnn::tower::TowerFace {
    let key: Vec<u32> = plate.iter().map(|&c| c % 3u32.pow(depth)).collect();
    match table.get(&key) {
        Some((n, f)) => {
            let masses: Vec<u128> = face.masses.iter().enumerate().map(|(c, &m)| (m * ((n[c] as u128 + 1) << 20)) / (f[c] + (1 << 20))).collect();
            let total = masses.iter().sum();
            holonics::hnn::tower::TowerFace { masses, total }
        }
        None => face.clone(),
    }
}

/// [definition; theory, November 9 21:43] **A realization that reads every face through a census lens**
/// ([`lensed_face`]): its faces are the inner realization's, each open site's face lensed at its plate (read beside the faces,
/// [`FieldRealization::read_plates`]); every other read is the inner one's. A writer or a joint read run through it draws and
/// codes on the lensed faces; with an empty table it reads the inner faces exactly.
pub(super) struct Lensed<'a> {
    pub inner: &'a mut dyn FieldRealization,
    pub table: &'a LensTable,
    pub depth: u32,
}

impl FieldRealization for Lensed<'_> {
    fn read_faces(&mut self, field: &Field, regions: &[Region]) -> std::result::Result<Vec<Vec<Option<holonics::hnn::tower::TowerFace>>>, holonics::hnn::tower::TowerError> {
        let heads = field.declaration.heads;
        let (faces, plates) = self.inner.read_plates(field, regions)?;
        Ok(faces
            .into_iter()
            .zip(plates)
            .map(|(row, plate)| row.into_iter().enumerate().map(|(t, f)| f.map(|f| lensed_face(&f, &plate[t * heads..(t + 1) * heads], self.depth, self.table))).collect())
            .collect())
    }
    fn read_and_return(&mut self, field: &Field, regions: &[Region]) -> std::result::Result<(Vec<Vec<Option<holonics::hnn::tower::TowerFace>>>, Vec<i128>), holonics::hnn::tower::TowerError> {
        self.inner.read_and_return(field, regions)
    }
    fn read_logits(&mut self, field: &Field, regions: &[Region]) -> std::result::Result<Vec<holonics::hnn::tower::field::FieldRead>, holonics::hnn::tower::TowerError> {
        self.inner.read_logits(field, regions)
    }
    fn read_landmarks(&mut self, field: &Field, region: &Region, question: usize, sites: &[usize], count: usize) -> std::result::Result<Vec<Vec<(usize, u64)>>, holonics::hnn::tower::TowerError> {
        self.inner.read_landmarks(field, region, question, sites, count)
    }
    fn read_plates(&mut self, field: &Field, regions: &[Region]) -> std::result::Result<(Vec<Vec<Option<holonics::hnn::tower::TowerFace>>>, Vec<Vec<u32>>), holonics::hnn::tower::TowerError> {
        self.inner.read_plates(field, regions)
    }
}

/// A census table file's one depth ([`plate_joint_field`]'s `CENSUS.tsv`).
pub(super) fn census_table(text: &str, depth: u32) -> Result<LensTable> {
    let mut table = LensTable::new();
    for line in text.lines().skip(1) {
        let cells: Vec<&str> = line.split('\t').collect();
        let [d, plate, n, f] = cells[..] else { return Err("a census row that is not depth, plate, counts and expected counts".into()) };
        if d.parse::<u32>().map_err(|_| "a census depth that is not a count")? != depth {
            continue;
        }
        let parse = |v: &str| v.parse::<u128>().map_err(|_| "a census count that is not a count");
        let key: Vec<u32> = plate.split('.').map(|c| c.parse::<u32>().map_err(|_| "a census plate that is not counts")).collect::<std::result::Result<_, _>>()?;
        let n: Vec<u64> = n.split(',').map(|v| parse(v).map(|x| x as u64)).collect::<std::result::Result<_, _>>()?;
        let f: Vec<u128> = f.split(',').map(parse).collect::<std::result::Result<_, _>>()?;
        table.insert(key, (n, f));
    }
    Ok(table)
}

/// [measurement; theory, November 9 23:30] **A visit's charge** ([`lap_visit`]): the sites whose letter the lap's code compares
/// at their own place, the sites that take a content covector (each region's open sites before its port: the members' masks
/// and the writers' states; an opening compared at its boundary codes whether the answer has ended, never which letter it
/// holds, and is charged nothing), each counted once a draw; beside them the lap's code as its deposit reads it, and the counts
/// the checks read.
#[derive(Clone, Debug, Default)]
struct Charge {
    /// The sites charged, and of them those in a question (a member masked over its whole region compares its question's
    /// letters at their places).
    sites: u64,
    question: u64,
    /// Σ over the visit's draws of the drawn problems' answer places `|a| + 1` (the answer and its first void), the member's
    /// and the path problem's.
    bound: u64,
    /// The sites compared at their own place whose input holds their own letter (resolved, carried or locked).
    leaks: u64,
    /// The visit's code as the deposit reads it ([`section_code`]) on `2^(−20)` bits, its sites, and of it the ports' part.
    code: i128,
    code_sites: u64,
    ported: i128,
    /// The charged sites' own code, each once, on `2^(−20)` bits.
    charged_code: i128,
}

/// [measurement; theory, November 9 23:30] **A section's code as its deposit reads it**, from faces already read on its
/// regions: [`FieldLearner::section_realized`]'s `code_before` and sites (each region's sites before its port at its weight
/// `m/K`, released once a region to the nearest, half away from zero, and its port's code; the sites each weighed region's
/// domain where it reads an open site and each port's heard places before its stop), and of the code the ports' part. The same
/// law read on the same faces; nothing moves.
fn section_code(faces: &[Vec<Option<holonics::hnn::tower::TowerFace>>], regions: &[Region]) -> Result<(i64, usize, i64)> {
    let (mut code, mut sites, mut ported) = (0i64, 0usize, 0i64);
    for (r, f) in regions.iter().zip(faces) {
        let len = r.classes.len();
        let end = r.port.map_or(len, |p| p.start);
        let own: i64 = f[..end].iter().zip(r.classes).filter_map(|(face, &c)| face.as_ref().map(|face| face.code(c))).sum();
        let (m, k) = r.weight();
        code += if m == k { own } else { holonics::hnn::overture::div_nearest(own as i128 * m as i128, k as i128) as i64 };
        if r.unresolved[..end].iter().any(|&u| u) {
            sites += m as usize;
        }
        if let Some(p) = r.port {
            let stop = p.stop.unwrap_or(len).min(len);
            let at: Vec<(&[u128], u128)> = (p.start..len)
                .map(|t| match &f[t] {
                    _ if t >= stop || p.heard.is_some_and(|h| !h[t]) => Ok((&[][..], 0)),
                    Some(face) => Ok((face.masses.as_slice(), face.total)),
                    None if p.boundary || p.letters => Ok((&[][..], 0)),
                    None => Err("a port's place without a face"),
                })
                .collect::<std::result::Result<_, _>>()?;
            let c = holonics::hnn::tower::field::port_reading(&at, &p).map_err(|e| e.to_string())?.1;
            (code, ported) = (code + c, ported + c);
            sites += (p.start..stop).filter(|&t| r.unresolved[t] && p.heard.is_none_or(|h| h[t])).count();
        }
    }
    Ok((code, sites, ported))
}

/// [measurement; theory, November 10 01:29] **A charged site as a visit reads it** ([`lap_visit`]): its leaf at the last tick
/// (`[h]`), its face and true letter, its octave of distance to the seam, whether it is a question's, its problem, its unframed
/// key and probe words at the last tick (`[2M]`) and the readout's chart of its last state (`[D]`).
pub(super) struct SiteRead<'a> {
    pub leaf: &'a [u32],
    pub face: &'a holonics::hnn::tower::TowerFace,
    pub truth: usize,
    pub octave: Option<u32>,
    pub asked: bool,
    pub problem: usize,
    pub key: &'a [i64],
    pub probe: &'a [i64],
    pub chart: &'a [i32],
    /// [theory, November 10 04:40] Its region's classes and open sites, and its place in them.
    pub classes: &'a [usize],
    pub open: &'a [bool],
    pub at: usize,
}

/// One visit of a training lap's own states ([`plate_joint_field`]): the first `take` sections of `order`, their regions and
/// open-site draws formed as `train-field` forms them from the draw `draw`, read only; at every charged site ([`Charge`]),
/// `visit(leaf, face, truth, octave, asked)` with its leaf at the last tick (`[h]`, full depth), its octave of distance to the
/// seam and whether it is a question's site.
/// Prints each section's time where `timed`. Where `line` is given (`SITES:BITS`, the `sites` and `before` of the
/// `FIELD_SECTION lap=0 n=0` line of the run that continued from the state, or `-` where none), the first section is read
/// against it and its own letters changed (checks 1 and 3, printed with PASS or FAIL); a FAIL refuses the visit.
#[allow(clippy::too_many_arguments)]
fn lap_visit(codec: &FieldCodec, train: &Problems, sections: &[Vec<usize>], paths: &[Vec<usize>], order: &[usize], seed: u64, mut draw: u64, learner: &mut FieldLearner, realization: &mut dyn FieldRealization, timed: bool, line: Option<&str>, visit: &mut dyn FnMut(&SiteRead)) -> Result<Charge> {
    if path_drafts() || path_squares() {
        return Err("census 2b charges the lap's members, openings and writers; a declared draft or square region is not among them".into());
    }
    let decl = learner.field.declaration;
    let (heads, m2, dw) = (decl.heads, 2 * decl.complex(), decl.width);
    let mut charge = Charge::default();
    for (n, &s) in order.iter().enumerate() {
        let section_start = std::time::Instant::now();
        let (members, path) = (&sections[s], &paths[s]);
        let draws: Vec<u64> = (1..=members.len() as u64).map(|k| draw + k).collect();
        let (regions, _) = section_regions(codec, train, members, path, seed, &mut draw, learner, realization)?;
        let views = views_of(&regions);
        // Each region's problem and draw: the members, then the openings (charged nothing), then the writers' states (a path
        // problem with an answer, [`writer_region`]).
        let writers: Vec<(usize, u64)> = if path_writer() { path.iter().zip(&draws).filter(|&(&j, _)| train[j].1.len().min(codec.answer) > 0).map(|(&j, &d)| (j, d)).collect() } else { Vec::new() };
        let rest = &views[members.len()..];
        let openings = rest.iter().take_while(|r| r.port.is_some()).count();
        if rest.len() != openings + writers.len() || rest[openings..].iter().any(|r| r.port.is_some() || r.domain.is_some()) {
            return Err(format!("section {s}: {} regions past its {} members are not its openings and its {} writers' states", rest.len(), members.len(), writers.len()).into());
        }
        let owner: Vec<Option<(usize, u64)>> = members.iter().zip(&draws).map(|(&i, &d)| Some((i, d))).chain(std::iter::repeat_n(None, openings)).chain(writers.iter().map(|&w| Some(w))).collect();
        charge.bound += members.iter().chain(path).map(|&i| train[i].1.len() as u64 + 1).sum::<u64>();
        let read = realization.read_words(&learner.field, &views).map_err(|e| e.to_string())?;
        let (code, sites, ported) = section_code(&read.faces, &views)?;
        (charge.code, charge.code_sites, charge.ported) = (charge.code + code as i128, charge.code_sites + sites as u64, charge.ported + ported as i128);
        let mut seen: std::collections::HashSet<(usize, u64, usize)> = std::collections::HashSet::new();
        let mut charged: Vec<Vec<usize>> = vec![Vec::new(); views.len()];
        let (mut open, mut own_code) = (0u64, 0i128);
        for (ri, (((((r, faces), leaves), words), probes), charts)) in views.iter().zip(&read.faces).zip(&read.plates).zip(&read.words).zip(&read.probes).zip(&read.charts).enumerate() {
            let end = r.port.map_or(r.classes.len(), |p| p.start);
            for (t, face) in faces[..end].iter().enumerate() {
                let Some(face) = face else { continue };
                if !r.unresolved[t] || r.faces.get(t).is_some_and(|f| f.is_some()) || r.locked.get(t).is_some_and(|&l| l) {
                    charge.leaks += 1;
                    continue;
                }
                let (problem, d) = owner[ri].ok_or("an opening's site compared at its own place")?;
                if !seen.insert((problem, d, t)) {
                    continue;
                }
                let asked = t < train[problem].0.len();
                visit(&SiteRead {
                    leaf: &leaves[t * heads..(t + 1) * heads],
                    face,
                    truth: r.classes[t],
                    octave: holonics::hnn::tower::field::seam_octave(&words[t * m2..(t + 1) * m2], &decl),
                    asked,
                    problem,
                    key: &words[t * m2..(t + 1) * m2],
                    probe: &probes[t * m2..(t + 1) * m2],
                    chart: &charts[t * dw..(t + 1) * dw],
                    classes: r.classes,
                    open: r.unresolved,
                    at: t,
                });
                own_code += face.code(r.classes[t]) as i128;
                charge.question += u64::from(asked);
                charged[ri].push(t);
                open += 1;
            }
        }
        (charge.sites, charge.charged_code) = (charge.sites + open, charge.charged_code + own_code);
        if let Some(line) = line.filter(|_| n == 0) {
            // Check 1: the section's code as its deposit reads it, against the line the lap printed for it.
            let (before, ported_bits) = (bits(code, sites), bits(ported, sites));
            let verdict = match line.split_once(':') {
                Some((ls, lb)) => if ls == sites.to_string() && lb == before { "PASS" } else { "FAIL" },
                None => "NO_LINE",
            };
            println!("FIELD_CHECK check=1 result={verdict} section={s} sites={sites} before={before} code_q20={code} ported_bits_a_site={ported_bits} charged={open} charged_bits_a_site={} line={line} matched=FIELD_SECTION_lap0_n0", bits(own_code as i64, open as usize));
            // Check 3: every charged site's own class changed reads the same faces at every site.
            let mut changed: Vec<TrainRegion> = regions.clone();
            let mut moved = 0u64;
            for (region, sites) in changed.iter_mut().zip(&charged) {
                for &t in sites {
                    region.classes[t] = if region.classes[t] == 0 { 1 } else { 0 };
                    moved += 1;
                }
            }
            let again = realization.read_words(&learner.field, &views_of(&changed)).map_err(|e| e.to_string())?;
            let equal = again.faces == read.faces;
            let leaks = charge.leaks;
            println!("FIELD_CHECK check=3 part=first_section result={} leaks={leaks} changed_sites={moved} faces_equal={equal}", if equal && leaks == 0 { "PASS" } else { "FAIL" });
            if verdict == "FAIL" || !equal || leaks > 0 {
                return Err("census 2b refuses to read: a check failed on the lap's first section".into());
            }
        }
        if timed {
            println!("FIELD_LEAVES_SECTION n={n} section={s} regions={} charged={open} code_sites={sites} ms={}", views.len(), section_start.elapsed().as_millis());
        }
    }
    Ok(charge)
}

/// `log₂(N/F)` on the codes' `2^(−20)` bits for a count `N > 0` and an expected count `F` on `2^(−20)` ([`face_code`] of the
/// ratio, its smaller side over its larger).
fn log2_ratio(n: u64, f: u128) -> i128 {
    let (num, den) = ((n as u128) << 20, f.max(1));
    if num >= den {
        holonics::hnn::tower::face_code(den, num) as i128
    } else {
        -(holonics::hnn::tower::face_code(num, den) as i128)
    }
}

/// [measurement; theory, November 9 21:43 and 21:52] `plate-joint-field UNITS UNITS_SHA TRAIN TRAIN_SHA HELD HELD_SHA KEYS
/// KEYS_SHA SECTION SECTIONS STATE STATE_SHA OUT`: **census 2, on the joint's scale**. A site's *leaf* is the intersection of
/// its shells (a shell a mode's trit, split by the seam, the cone `|Re| = |Im|`), read at the last tick at each depth
/// `d = 1..b` (each head's class mod `3^d`). One forward visit of a training lap's own states (the regions and open-site
/// draws its first `SECTIONS` sections make, all of them at zero: `train-field`'s codec, walk, paths, draws and seed, read at
/// the state's own lap count), reading only and never depositing: at every open site its leaf takes its true letter into
/// `N_(p, a)` and its face's shares into `F_(p, a)` ([`PlateCounts`]); `CENSUS.tsv` holds every depth's table. A second
/// visit of the same states reads TRAIN's own code under each depth's residual lens, and by each site's octave of distance to
/// the nearest seam (the least `||Re| − |Im|| / (|Re| + |Im|)` over its class modes, `SEAMS.tsv`, `FIELD_LEAVES_SEAM`) its
/// leaf's U shared over the leaf's sites and the code the lens releases there; the code the lens releases on TRAIN
/// (plain less lensed, nats a place) beside each depth's stored free energy `U = Σ_leaves Σ_a N_a ln(N_a/F_a)` a place
/// (`FIELD_LEAVES_U`; theory's checks: released ≥ U at every depth, and U never falls with depth), and the 20 leaves of the
/// most `U` at each depth with their shells and counts (`LEAVES_U.tsv`). Then the held problems' joint read
/// (`FIELD_JOINT_NATS`, the train-field lap's own chain, its seed and states) plain (`lap=0`) and through the residual lens at
/// each depth (`lap=d`, [`Lensed`]). `FIELD_LEAVES` and `FIELD_LEAVES_SECTION` lines count and time the visit.
///
/// [measurement; theory, November 10 00:07] The charged sites part by side: the answer's table (`CENSUS.tsv`) is the one the lens,
/// the held joint (which codes answer places only) and the seam reading read; the question's (`CENSUS_QUESTION.tsv`, the
/// letters a masked member compares at their places) prints its plain code, U and released code beside the answer's
/// (`FIELD_LEAVES_U part=`), each under its own table.
///
/// [measurement; theory, November 9 23:30, census 2b] Every count, U, seam and code reads the charged sites alone ([`Charge`]:
/// the sites the lap's code compares at their own place, once a draw; census 2 had charged every open site, the openings'
/// boundary places among them). `LINE` (`SITES:BITS`, or `-`) is the `FIELD_SECTION lap=0 n=0` line of the run that continued
/// from the state. Before any reading, each check printed with PASS or FAIL, and a FAIL refuses the read: (1) the first section's
/// code as the deposit reads it is the line's, in its units (bits a site over the line's sites); (2) the charged sites are at most
/// the visit's draws' answer places ([`Charge::bound`]); (3) no charged site's input holds its own letter (none resolved, carried
/// or locked, and the first section read with every charged site's class changed returns the same faces at every site).
pub(super) fn plate_joint_field(args: &[String], realization: &mut dyn FieldRealization) -> Result<()> {
    if args.len() != 15 {
        return Err("plate-joint-field UNITS UNITS_SHA TRAIN TRAIN_SHA HELD HELD_SHA KEYS KEYS_SHA SECTION SECTIONS STATE STATE_SHA LINE OUT".into());
    }
    let started = std::time::Instant::now();
    let units = units_of(&args[1], &args[2])?;
    let train_problems = problems_of(&pinned_read(&args[3], &args[4], READ_BUDGET as usize)?);
    let dev_problems = problems_of(&pinned_read(&args[5], &args[6], READ_BUDGET as usize)?);
    let keys = pinned_read(&args[7], &args[8], READ_BUDGET as usize)?;
    let (section, limit) = (positive(&args[9])?, count(&args[10])?);
    let mut learner = FieldLearner::from_text(std::str::from_utf8(&pinned_read(&args[11], &args[12], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    declared_clocks(&mut learner.field);
    let line = args[13].as_str();
    let out = Path::new(&args[14]);
    std::fs::create_dir(out)?;
    let codec = FieldCodec::found(units, &train_problems)?;
    let encode = |problems: &[(Vec<u8>, Vec<u8>)]| -> Result<Problems> {
        problems.par_iter().map(|(q, a)| Ok((codec.encode(&question_text(q)).map_err(|e| e.to_string())?, codec.encode(a).map_err(|e| e.to_string())?, a.len()))).collect::<std::result::Result<Vec<_>, String>>().map_err(|e| e.into())
    };
    let train_set = encode(&train_problems)?;
    let dev_set: Problems = encode(&dev_problems)?.into_iter().filter(|(_, a, _)| a.len() < codec.answer).collect();
    let seed = u64::from_be_bytes(keys.get(keys.len().saturating_sub(8)..).filter(|w| w.len() == 8).ok_or("a key file of fewer than eight bytes")?.try_into()?);
    let (sections, _) = sections_of(&train_set, section, dev_set.len(), seed);
    if learner.holds_step() {
        return Err("plate-joint-field reads a state that holds no step (it never deposits)".into());
    }
    println!("FIELD_CLOCKS per_blank={} bare={} laps_read={}", learner.field.per_blank_clock, learner.field.bare_stretch, learner.laps);
    let (heads, trits, a) = (learner.field.declaration.heads, learner.field.declaration.class_trits(), learner.field.declaration.alphabet);
    let read = learner.laps;
    let draw = read * train_set.len() as u64;
    let paths = paths_of(seed, read, &sections);
    let order = walk(seed, read, sections.len());
    let take = if limit == 0 { order.len() } else { limit.min(order.len()) };
    // [theory, November 10 00:07] Two tables, by the site's side: the answer's (part 0), which the lens, the held joint (it codes
    // answer places only) and the seam reading read, and the question's (part 1), whose letters a masked member compares at their
    // places; at one trit a question's site and an answer's would share leaves.
    let mut counts: [Vec<std::collections::BTreeMap<Vec<u32>, PlateCounts>>; 2] = std::array::from_fn(|_| (0..=trits).map(|_| std::collections::BTreeMap::new()).collect());
    let leaf_at = |leaf: &[u32], d: usize| -> Vec<u32> { leaf.iter().map(|&c| c % 3u32.pow(d as u32)).collect() };
    // [theory, November 9 22:07] The seam as a cut: each depth-1 leaf split by its sites' octave of distance to the seam.
    let mut cut: std::collections::BTreeMap<(Vec<u32>, Option<u32>), PlateCounts> = std::collections::BTreeMap::new();
    let charge = lap_visit(&codec, &train_set, &sections, &paths, &order[..take], seed, draw, &mut learner, realization, true, Some(line), &mut |site| {
        let (leaf, face, truth, octave, asked) = (site.leaf, site.face, site.truth, site.octave, site.asked);
        for (d, table) in counts[usize::from(asked)].iter_mut().enumerate().skip(1) {
            table.entry(leaf_at(leaf, d)).or_insert_with(|| PlateCounts::new(a)).add(face, truth);
        }
        if !asked {
            cut.entry((leaf_at(leaf, 1), octave)).or_insert_with(|| PlateCounts::new(a)).add(face, truth);
        }
    })?;
    // Each part's charged places: the answer's, then the question's.
    let parts = [charge.sites - charge.question, charge.question];
    let places = parts[0];
    let census_ms = started.elapsed().as_millis();
    // Checks 2 and 3 over the whole visit, before any reading.
    let bounded = charge.sites <= charge.bound;
    println!("FIELD_CHECK check=2 result={} charged={} question={} answer={} bound={} sections={take}", if bounded { "PASS" } else { "FAIL" }, charge.sites, charge.question, charge.sites - charge.question, charge.bound);
    println!("FIELD_CHECK check=3 part=visit result={} leaks={}", if charge.leaks == 0 { "PASS" } else { "FAIL" }, charge.leaks);
    if !bounded || charge.leaks > 0 {
        return Err("census 2b refuses to read: a check failed over the visit".into());
    }
    // The visit's code in the lap's units (bits a site over the deposit's sites), beside FIELD_LAP's `before` (read on a field
    // that moves through its lap, so not the same number), and the charged sites' own.
    println!(
        "FIELD_CHARGE sites={} lap_code_bits_a_site={} lap_code_sites={} ported_bits_a_site={} charged_bits_a_site={} charged_nats_a_place={}",
        charge.sites,
        bits(i64::try_from(charge.code)?, charge.code_sites as usize),
        charge.code_sites,
        bits(i64::try_from(charge.ported)?, charge.code_sites as usize),
        bits(i64::try_from(charge.charged_code)?, charge.sites as usize),
        if places == 0 { "-".to_string() } else { decimal_q20(nats_q20(charge.charged_code) / places as i128) }
    );
    // The answer's table is `CENSUS.tsv` (the one `lens-field` reads), the question's `CENSUS_QUESTION.tsv`.
    let mut tables: [Vec<LensTable>; 2] = std::array::from_fn(|_| vec![LensTable::new(); trits + 1]);
    // Each leaf's stored free energy `Σ_a N_a log₂(N_a/F_a)` on 2^(−20) bits, a part.
    let mut energies: [Vec<Vec<(i128, Vec<u32>, u64)>>; 2] = std::array::from_fn(|_| vec![Vec::new(); trits + 1]);
    for (part, name) in [(0usize, "CENSUS.tsv"), (1, "CENSUS_QUESTION.tsv")] {
        let mut file = rows_file(&out.join(name), "depth\tleaf\tcounts\texpected_q20\n")?;
        for (d, table) in counts[part].iter().enumerate().skip(1) {
            for (leaf, k) in table {
                let n: Vec<String> = k.n.iter().map(u64::to_string).collect();
                let f: Vec<u128> = (0..a).map(|c| k.expected(c)).collect();
                let fs: Vec<String> = f.iter().map(u128::to_string).collect();
                let name: Vec<String> = leaf.iter().map(u32::to_string).collect();
                row(&mut file, &format!("{d}\t{}\t{}\t{}\n", name.join("."), n.join(","), fs.join(",")))?;
                let u: i128 = (0..a).filter(|&c| k.n[c] > 0).map(|c| k.n[c] as i128 * log2_ratio(k.n[c], f[c])).sum();
                energies[part][d].push((u, leaf.clone(), k.places()));
                tables[part][d].insert(leaf.clone(), (k.n.clone(), f));
            }
            println!("FIELD_LEAVES part={} depth={d} cells={} leaves={} charged_places={} sections={take} of={} census_ms={census_ms}", ["answer", "question"][part], 3u128.pow((heads * d) as u32), table.len(), parts[part], order.len());
        }
    }
    // [theory, November 9 22:07] U of the depth-1 leaves cut by the seam (leaf × octave) beside U at depths 1 and 2, a place:
    // counts add, so the cut's U is at least depth 1's; the gap is the free energy the seam's distance reveals.
    let u_of = |k: &PlateCounts| -> i128 { (0..a).filter(|&c| k.n[c] > 0).map(|c| k.n[c] as i128 * log2_ratio(k.n[c], k.expected(c))).sum() };
    let u_cut: i128 = cut.values().map(u_of).sum();
    let u_depth = |d: usize| -> i128 { energies[0].get(d).map_or(0, |list| list.iter().map(|e| e.0).sum()) };
    let place = |v: i128| if places == 0 { "-".to_string() } else { decimal_q20(nats_q20(v) / places as i128) };
    println!("FIELD_LEAVES_SEAM_CUT u_d1_nats_a_place={} u_d1_octave_nats_a_place={} u_d2_nats_a_place={} d1_leaves={} d1_octave_cells={}", place(u_depth(1)), place(u_cut), place(u_depth(2)), counts[0].get(1).map_or(0, |t| t.len()), cut.len());
    // The second visit: TRAIN's own code plain and under each depth's lens; and by each site's octave of distance to the
    // nearest seam ([`holonics::hnn::tower::field::seam_octave`]), at each depth, the site's own charge
    // `u_t = ln((N + 1)/(F + 1))` at its leaf and its true letter (theory, 22:07: over a leaf's sites these sum to
    // `Σ_a N_a ln((N_a + 1)/(F_a + 1))`, the leaf's U with one count added on both sides), its plain code, and the code the lens
    // releases at the site.
    // Each part's plain and lensed code a depth, each part under its own table; the seam reading reads the answer's sites.
    let mut codes: [Vec<[i128; 2]>; 2] = std::array::from_fn(|_| vec![[0; 2]; trits + 1]);
    let mut seams: Vec<std::collections::BTreeMap<Option<u32>, (u64, i128, i128, i128)>> = vec![std::collections::BTreeMap::new(); trits + 1];
    let second = std::time::Instant::now();
    let again = lap_visit(&codec, &train_set, &sections, &paths, &order[..take], seed, draw, &mut learner, realization, false, None, &mut |site| {
        let (leaf, face, truth, octave, asked) = (site.leaf, site.face, site.truth, site.octave, site.asked);
        let plain = face.code(truth) as i128;
        let part = usize::from(asked);
        for d in 1..=trits {
            let lensed = lensed_face(face, leaf, d as u32, &tables[part][d]).code(truth) as i128;
            codes[part][d] = [codes[part][d][0] + plain, codes[part][d][1] + lensed];
            if asked {
                continue;
            }
            let charge = tables[0][d].get(&leaf_at(leaf, d)).map_or(0, |(n, f)| log2_ratio(n[truth] + 1, f[truth] + (1 << 20)));
            let slot = seams[d].entry(octave).or_default();
            *slot = (slot.0 + 1, slot.1 + charge, slot.2 + plain - lensed, slot.3 + plain);
        }
    })?;
    if again.sites != charge.sites || again.question != charge.question {
        return Err(format!("the second visit charged {} sites ({} asked) where the first charged {} ({})", again.sites, again.question, charge.sites, charge.question).into());
    }
    let mut seam_file = rows_file(&out.join("SEAMS.tsv"), "depth\toctave\tmargin_from\tmargin_to\tsites\tu_nats_a_site\tplain_code_nats_a_site\treleased_nats_a_site\n")?;
    for (d, bins) in seams.iter().enumerate().skip(1) {
        for (octave, &(sites, u, released, plain)) in bins {
            let (name, from, to) = match octave { Some(k) => (k.to_string(), format!("2^-{}", k + 1), format!("2^-{k}")), None => ("seam".to_string(), "0".to_string(), "0".to_string()) };
            let per = |v: i128| decimal_q20(nats_q20(v) / sites.max(1) as i128);
            row(&mut seam_file, &format!("{d}\t{name}\t{from}\t{to}\t{sites}\t{}\t{}\t{}\n", per(u), per(plain), per(released)))?;
            println!("FIELD_LEAVES_SEAM depth={d} octave={name} margin={from}..{to} sites={sites} u_nats_a_site={} plain_code_nats_a_site={} released_nats_a_site={}", per(u), per(plain), per(released));
        }
    }
    let mut top = rows_file(&out.join("LEAVES_U.tsv"), "depth\trank\tleaf_shells\tplaces\tu_nats\n")?;
    for d in 1..=trits {
        // The answer's line, then the question's beside it, each a place of its own part.
        for (part, name) in ["answer", "question"].iter().enumerate() {
            let a_place = |v: i128| if parts[part] == 0 { "-".to_string() } else { decimal_q20(nats_q20(v) / parts[part] as i128) };
            let u: i128 = energies[part][d].iter().map(|e| e.0).sum();
            let [plain, lensed] = codes[part][d];
            println!("FIELD_LEAVES_U part={name} depth={d} places={} u_nats_a_place={} released_nats_a_place={} train_code_nats={} train_lens_code_nats={} second_visit_ms={}", parts[part], a_place(u), a_place(plain - lensed), a_place(plain), a_place(lensed), second.elapsed().as_millis());
        }
        let mut list = energies[0][d].clone();
        list.sort_by_key(|e| (std::cmp::Reverse(e.0), e.1.clone()));
        for (rank, (u, leaf, n)) in list.iter().take(20).enumerate() {
            // Each head's shells as its first `d` trits, least first.
            let shells: Vec<String> = leaf.iter().map(|&c| (0..d).map(|l| ((c / 3u32.pow(l as u32)) % 3).to_string()).collect::<String>()).collect();
            row(&mut top, &format!("{d}\t{}\t{}\t{n}\t{}\n", rank + 1, shells.join("."), decimal_q20(nats_q20(*u))))?;
        }
    }
    // The held joint read, plain and through each depth's lens.
    let mut rows = rows_file(&out.join("JOINT.tsv"), "lap\tproblem\tsites\town\tfoil\tinformation\tseries\n")?;
    let field = &learner.field;
    let t0 = std::time::Instant::now();
    joint_read(field, &codec, &dev_set, seed, realization, 0, &mut rows)?;
    println!("FIELD_LEAVES_JOINT depth=0 ms={}", t0.elapsed().as_millis());
    for (d, table) in tables[0].iter().enumerate().skip(1) {
        let t0 = std::time::Instant::now();
        let mut lensed = Lensed { inner: &mut *realization, table, depth: d as u32 };
        joint_read(field, &codec, &dev_set, seed, &mut lensed, d as i64, &mut rows)?;
        println!("FIELD_LEAVES_JOINT depth={d} ms={}", t0.elapsed().as_millis());
    }
    println!("FIELD_LEAVES_DONE ms={}", started.elapsed().as_millis());
    Ok(())
}

/// The phase census's sets: TRAIN's even problems, its odd problems, and the held problems.
const PHASE_SETS: [&str; 3] = ["train_even", "train_odd", "held"];

/// [measurement; theory, November 10 01:29] One phase-census site while its batch is summed ([`PhaseCensus`]): its set and
/// true letter, each letter's face share on `2^(−40)` floored and its remainder carried on `2^(−72)` ([`PlateCounts::add`]'s
/// law), each head's, mode's and word's phase bin (`[h][l][w]`, `w` 0 the key and 1 the probe), and the readout's chart `r`
/// with its products `r_i r_j` (`i ≤ j`).
struct PhaseSite {
    set: usize,
    truth: usize,
    q: Vec<u128>,
    c: Vec<i128>,
    bins: Vec<u8>,
    r: Vec<i32>,
    rr: Vec<i64>,
}

/// [measurement; theory, November 10 01:29 and 01:30] **The phase census's sums**, by set: `N[a]` and `F[a]` (each share on
/// `2^(−40)`, its carried remainder on `2^(−72)`) in each head's, mode's and word's phase bins (`[set][h][l][w][bin][a]`,
/// [`PHASE_BINS`] and the zero word); and the moments of the readout's chart `r` (on `2^(−16)`) by letter, `LN[a] = Σ_(x = a) r`,
/// `LF[a] = Σ f(a) r` (main on `2^(−56)`, carried on `2^(−88)`), `QN[a] = Σ_(x = a) r rᵀ` (on `2^(−32)`) and
/// `QF[a] = Σ f(a) r rᵀ` (main on `2^(−72)`, carried on `2^(−104)`), upper triangles, with each set's sites, `Σ r` and `Σ |r|`;
/// and, at every site and head, whether mode 0's bin of each word holds the shell of the site's depth-1 class (2b's plate).
struct PhaseCensus {
    a: usize,
    heads: usize,
    modes: usize,
    dw: usize,
    n: Vec<u64>,
    f: Vec<u128>,
    fc: Vec<i128>,
    ln: Vec<i128>,
    lf: Vec<i128>,
    lfc: Vec<i128>,
    qn: Vec<i128>,
    qf: Vec<i128>,
    qfc: Vec<i128>,
    sites: [u64; 3],
    rsum: Vec<i128>,
    rabs: Vec<i128>,
    unmatched: [u64; 2],
    matched_sites: u64,
    pending: Vec<PhaseSite>,
}

impl PhaseCensus {
    /// The sites a batch holds before it is summed.
    const BATCH: usize = 8192;

    fn new(d: &FieldDeclaration) -> Self {
        let (a, heads, modes, dw) = (d.alphabet, d.heads, d.modes, d.width);
        let tri = dw * (dw + 1) / 2;
        let bins = PHASE_SETS.len() * heads * modes * 2 * (holonics::hnn::tower::field::PHASE_BINS + 1) * a;
        let lin = PHASE_SETS.len() * a * dw;
        let quad = PHASE_SETS.len() * a * tri;
        Self { a, heads, modes, dw, n: vec![0; bins], f: vec![0; bins], fc: vec![0; bins], ln: vec![0; lin], lf: vec![0; lin], lfc: vec![0; lin], qn: vec![0; quad], qf: vec![0; quad], qfc: vec![0; quad], sites: [0; 3], rsum: vec![0; PHASE_SETS.len() * dw], rabs: vec![0; PHASE_SETS.len() * dw], unmatched: [0; 2], matched_sites: 0, pending: Vec::new() }
    }

    /// A site into `set`: its shares, bins and products; mode 0's bins checked against its plate.
    fn add(&mut self, set: usize, site: &SiteRead, edges: &[(i64, i64); holonics::hnn::tower::field::PHASE_BINS]) {
        use holonics::hnn::tower::field::{phase_bin, phase_bin_shell};
        let (n, m) = (self.modes, self.heads * self.modes);
        let face = site.face;
        let (mut q, mut c) = (Vec::with_capacity(self.a), Vec::with_capacity(self.a));
        for &mass in &face.masses {
            let share = (mass << 40) / face.total;
            let rem = (mass << 40) - share * face.total;
            q.push(share);
            c.push((((rem << 32) + face.total / 2) / face.total) as i128);
        }
        let mut bins = Vec::with_capacity(self.heads * n * 2);
        for h in 0..self.heads {
            for l in 0..n {
                for word in [site.key, site.probe] {
                    bins.push(phase_bin(word[h * n + l], word[m + h * n + l], edges) as u8);
                }
            }
            for (w, word) in [site.key, site.probe].iter().enumerate() {
                let bin = phase_bin(word[h * n], word[m + h * n], edges);
                self.unmatched[w] += u64::from(phase_bin_shell(bin) != site.leaf[h] % 3);
            }
        }
        self.matched_sites += 1;
        let r = site.chart.to_vec();
        let rr: Vec<i64> = (0..self.dw).flat_map(|i| (i..self.dw).map(move |j| (i, j))).map(|(i, j)| r[i] as i64 * r[j] as i64).collect();
        self.pending.push(PhaseSite { set, truth: site.truth, q, c, bins, r, rr });
        if self.pending.len() >= Self::BATCH {
            self.flush();
        }
    }

    /// The pending sites summed in, in parallel by disjoint parts of the sums (a group of bins, a set's letter), so each sum
    /// is the same integers in any schedule.
    fn flush(&mut self) {
        let sites = std::mem::take(&mut self.pending);
        let (a, dw) = (self.a, self.dw);
        let tri = dw * (dw + 1) / 2;
        let group = (holonics::hnn::tower::field::PHASE_BINS + 1) * a;
        let per_set = self.heads * self.modes * 2;
        self.n.par_chunks_mut(group).zip(self.f.par_chunks_mut(group)).zip(self.fc.par_chunks_mut(group)).enumerate().for_each(|(g, ((n, f), fc))| {
            let (set, k) = (g / per_set, g % per_set);
            for s in sites.iter().filter(|s| s.set == set) {
                let at = s.bins[k] as usize * a;
                n[at + s.truth] += 1;
                for l in 0..a {
                    f[at + l] += s.q[l];
                    fc[at + l] += s.c[l];
                }
            }
        });
        self.ln.par_chunks_mut(dw).zip(self.lf.par_chunks_mut(dw)).zip(self.lfc.par_chunks_mut(dw)).enumerate().for_each(|(g, ((ln, lf), lfc))| {
            let (set, letter) = (g / a, g % a);
            for s in sites.iter().filter(|s| s.set == set) {
                let (q, c) = (s.q[letter] as i128, s.c[letter]);
                for j in 0..dw {
                    let r = s.r[j] as i128;
                    lf[j] += q * r;
                    lfc[j] += c * r;
                    if s.truth == letter {
                        ln[j] += r;
                    }
                }
            }
        });
        self.qn.par_chunks_mut(tri).zip(self.qf.par_chunks_mut(tri)).zip(self.qfc.par_chunks_mut(tri)).enumerate().for_each(|(g, ((qn, qf), qfc))| {
            let (set, letter) = (g / a, g % a);
            for s in sites.iter().filter(|s| s.set == set) {
                let (q, c) = (s.q[letter] as i128, s.c[letter]);
                for (k, &rr) in s.rr.iter().enumerate() {
                    let rr = rr as i128;
                    qf[k] += q * rr;
                    qfc[k] += c * rr;
                    if s.truth == letter {
                        qn[k] += rr;
                    }
                }
            }
        });
        for s in &sites {
            self.sites[s.set] += 1;
            for (j, &r) in s.r.iter().enumerate() {
                self.rsum[s.set * dw + j] += r as i128;
                self.rabs[s.set * dw + j] += (r as i128).abs();
            }
        }
    }
}

/// [measurement; theory, November 10 01:29 and 01:30] `phase-field UNITS UNITS_SHA TRAIN TRAIN_SHA HELD HELD_SHA KEYS KEYS_SHA
/// SECTION SECTIONS STATE STATE_SHA LINE OUT`: **the phase census**, its own forward read on census 2b's charge set at its
/// answer sites ([`lap_visit`], the same tick as 2b's classes: the last), three sets kept apart: TRAIN's even problems, its odd
/// problems, and the held problems (each held problem's own joint states, every open place the joint codes, [`joint_states`]).
/// At each site, for every head, all its modes and both unframed words (the key and the probe), the mode's phase bin
/// ([`holonics::hnn::tower::field::phase_bin`]: `π/12` from `arg 0`, the cone on edges, read on the integers) takes the true
/// letter into `N[a]` and the face's shares into `F[a]` (`CENSUS_PHASE.tsv`); the readout's chart `r` (the vector the lift
/// reads) gives each letter's `LN`, `LF`, `QN` and `QF` (`CENSUS_MOMENT.tsv`, [`PhaseCensus`]), each set's site count beside
/// them. Checks first, each printed with PASS or FAIL, a FAIL refusing the tables: census 2b's (`LINE` and the charge, as
/// `plate-joint-field`), then every (head, mode, word)'s bins sum to its set's sites; `Σ_a (N − F)` is zero in every bin up to
/// the carried remainder (half a grain a letter a site); mode 0's sector of the key word at each site and head holds the shell
/// of 2b's depth-1 class (the probe's misses printed beside); `Σ_a LN = Σ r` exactly and `Σ_a LF = Σ r` up to the carried
/// remainder.
pub(super) fn phase_field(args: &[String], realization: &mut dyn FieldRealization) -> Result<()> {
    use holonics::hnn::tower::field::{phase_edges, PHASE_BINS};
    if args.len() != 15 {
        return Err("phase-field UNITS UNITS_SHA TRAIN TRAIN_SHA HELD HELD_SHA KEYS KEYS_SHA SECTION SECTIONS STATE STATE_SHA LINE OUT".into());
    }
    let started = std::time::Instant::now();
    let units = units_of(&args[1], &args[2])?;
    let train_problems = problems_of(&pinned_read(&args[3], &args[4], READ_BUDGET as usize)?);
    let dev_problems = problems_of(&pinned_read(&args[5], &args[6], READ_BUDGET as usize)?);
    let keys = pinned_read(&args[7], &args[8], READ_BUDGET as usize)?;
    let (section, limit) = (positive(&args[9])?, count(&args[10])?);
    let mut learner = FieldLearner::from_text(std::str::from_utf8(&pinned_read(&args[11], &args[12], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    declared_clocks(&mut learner.field);
    let line = args[13].as_str();
    let out = Path::new(&args[14]);
    std::fs::create_dir(out)?;
    let codec = FieldCodec::found(units, &train_problems)?;
    let encode = |problems: &[(Vec<u8>, Vec<u8>)]| -> Result<Problems> {
        problems.par_iter().map(|(q, a)| Ok((codec.encode(&question_text(q)).map_err(|e| e.to_string())?, codec.encode(a).map_err(|e| e.to_string())?, a.len()))).collect::<std::result::Result<Vec<_>, String>>().map_err(|e| e.into())
    };
    let train_set = encode(&train_problems)?;
    let dev_set: Problems = encode(&dev_problems)?.into_iter().filter(|(_, a, _)| a.len() < codec.answer).collect();
    let seed = u64::from_be_bytes(keys.get(keys.len().saturating_sub(8)..).filter(|w| w.len() == 8).ok_or("a key file of fewer than eight bytes")?.try_into()?);
    let (sections, _) = sections_of(&train_set, section, dev_set.len(), seed);
    if learner.holds_step() {
        return Err("phase-field reads a state that holds no step (it never deposits)".into());
    }
    let d = learner.field.declaration;
    println!("FIELD_CLOCKS per_blank={} bare={} laps_read={}", learner.field.per_blank_clock, learner.field.bare_stretch, learner.laps);
    let (heads, modes, a, dw, m2) = (d.heads, d.modes, d.alphabet, d.width, 2 * d.complex());
    let edges = phase_edges(learner.field.half_turn());
    let read = learner.laps;
    let draw = read * train_set.len() as u64;
    let paths = paths_of(seed, read, &sections);
    let order = walk(seed, read, sections.len());
    let take = if limit == 0 { order.len() } else { limit.min(order.len()) };
    let mut census = PhaseCensus::new(&d);
    let charge = lap_visit(&codec, &train_set, &sections, &paths, &order[..take], seed, draw, &mut learner, realization, true, Some(line), &mut |site| {
        if !site.asked {
            census.add(site.problem % 2, site, &edges);
        }
    })?;
    let bounded = charge.sites <= charge.bound;
    println!("FIELD_CHECK check=2 result={} charged={} question={} answer={} bound={} sections={take}", if bounded { "PASS" } else { "FAIL" }, charge.sites, charge.question, charge.sites - charge.question, charge.bound);
    println!("FIELD_CHECK check=3 part=visit result={} leaks={}", if charge.leaks == 0 { "PASS" } else { "FAIL" }, charge.leaks);
    if !bounded || charge.leaks > 0 {
        return Err("the phase census refuses to read: a check failed over the visit".into());
    }
    let train_ms = started.elapsed().as_millis();
    // The held set: each held problem's own joint states, every open place.
    let mut states: Vec<(Vec<usize>, Vec<bool>)> = Vec::new();
    for (i, (q, ans, _)) in dev_set.iter().enumerate() {
        states.extend(joint_states(codec.void(), q, ans, seed, i as u64).into_iter().map(|(c, u, _)| (c, u)));
    }
    for chunk in states.chunks(64) {
        let views: Vec<Region> = chunk.iter().map(|(c, u)| Region { classes: c, unresolved: u, faces: &[], locked: &[], echo: &[], domain: None, port: None }).collect();
        let words = realization.read_words(&learner.field, &views).map_err(|e| e.to_string())?;
        for (ri, (c, u)) in chunk.iter().enumerate() {
            for t in (0..c.len()).filter(|&t| u[t]) {
                let face = words.faces[ri][t].as_ref().ok_or("a held state's open place without a face")?;
                census.add(2, &SiteRead { leaf: &words.plates[ri][t * heads..(t + 1) * heads], face, truth: c[t], octave: None, asked: false, problem: ri, key: &words.words[ri][t * m2..(t + 1) * m2], probe: &words.probes[ri][t * m2..(t + 1) * m2], chart: &words.charts[ri][t * dw..(t + 1) * dw], classes: c, open: u, at: t }, &edges);
            }
        }
    }
    census.flush();
    let held_ms = started.elapsed().as_millis();
    for (set, name) in PHASE_SETS.iter().enumerate() {
        println!("FIELD_PHASE_SET set={name} sites={}", census.sites[set]);
    }
    // The checks over the sums, before any table.
    let groups = heads * modes * 2;
    let group = (PHASE_BINS + 1) * a;
    let (mut unsummed, mut unbalanced) = (0usize, 0usize);
    for set in 0..PHASE_SETS.len() {
        for k in 0..groups {
            let at = (set * groups + k) * group;
            let mut total = 0u64;
            for b in 0..=PHASE_BINS {
                let bin = at + b * a;
                let n: u64 = census.n[bin..bin + a].iter().sum();
                let f: i128 = (0..a).map(|l| ((census.f[bin + l] as i128) << 32) + census.fc[bin + l]).sum();
                unbalanced += usize::from(((n as i128) << 72).abs_diff(f) > n as u128 * a as u128 / 2 + 1);
                total += n;
            }
            unsummed += usize::from(total != census.sites[set]);
        }
    }
    println!("FIELD_CHECK check=phase_sum result={} unsummed_groups={unsummed} groups={}", if unsummed == 0 { "PASS" } else { "FAIL" }, PHASE_SETS.len() * groups);
    println!("FIELD_CHECK check=phase_balance result={} unbalanced_bins={unbalanced} bins={}", if unbalanced == 0 { "PASS" } else { "FAIL" }, PHASE_SETS.len() * groups * (PHASE_BINS + 1));
    let sectored = census.unmatched[0] == 0;
    println!("FIELD_CHECK check=mode0_sector result={} key_unmatched={} probe_unmatched={} site_heads={} word_2b_reads={}", if sectored { "PASS" } else { "FAIL" }, census.unmatched[0], census.unmatched[1], census.matched_sites * heads as u64, if sectored { "key" } else if census.unmatched[1] == 0 { "probe" } else { "neither" });
    let (mut ln_off, mut lf_off) = (0usize, 0usize);
    for set in 0..PHASE_SETS.len() {
        for j in 0..dw {
            let ln: i128 = (0..a).map(|l| census.ln[(set * a + l) * dw + j]).sum();
            let lf: i128 = (0..a).map(|l| (census.lf[(set * a + l) * dw + j] << 32) + census.lfc[(set * a + l) * dw + j]).sum();
            ln_off += usize::from(ln != census.rsum[set * dw + j]);
            lf_off += usize::from((census.rsum[set * dw + j] << 72).abs_diff(lf) > census.rabs[set * dw + j].unsigned_abs() * a as u128 / 2 + 1);
        }
    }
    println!("FIELD_CHECK check=moment_sum result={} ln_unequal={ln_off} lf_unequal={lf_off} coordinates={}", if ln_off == 0 && lf_off == 0 { "PASS" } else { "FAIL" }, PHASE_SETS.len() * dw);
    if unsummed > 0 || unbalanced > 0 || !sectored || ln_off > 0 || lf_off > 0 {
        return Err("the phase census refuses to write its tables: a check failed".into());
    }
    let join = |v: &[i128]| v.iter().map(i128::to_string).collect::<Vec<_>>().join(",");
    let mut file = rows_file(&out.join("CENSUS_PHASE.tsv"), "set\thead\tmode\tword\tbin\tfrom_pi_12\tto_pi_12\tsites\tcounts\texpected_q40\texpected_carried_q72\n")?;
    for (set, name) in PHASE_SETS.iter().enumerate() {
        for h in 0..heads {
            for l in 0..modes {
                for (w, word) in ["key", "probe"].iter().enumerate() {
                    let at = (set * groups + (h * modes + l) * 2 + w) * group;
                    for b in 0..=PHASE_BINS {
                        let bin = at + b * a;
                        let n = &census.n[bin..bin + a];
                        let (from, to) = if b == PHASE_BINS { ("zero".to_string(), "zero".to_string()) } else { (b.to_string(), (b + 1).to_string()) };
                        let counts: Vec<String> = n.iter().map(u64::to_string).collect();
                        let f: Vec<String> = census.f[bin..bin + a].iter().map(u128::to_string).collect();
                        row(&mut file, &format!("{name}\t{h}\t{l}\t{word}\t{b}\t{from}\t{to}\t{}\t{}\t{}\t{}\n", n.iter().sum::<u64>(), counts.join(","), f.join(","), join(&census.fc[bin..bin + a])))?;
                    }
                }
            }
        }
    }
    let tri = dw * (dw + 1) / 2;
    let mut moments = rows_file(&out.join("CENSUS_MOMENT.tsv"), "set\tletter\tkind\tvalues\n")?;
    for (set, name) in PHASE_SETS.iter().enumerate() {
        row(&mut moments, &format!("{name}\t-\tsites\t{}\n", census.sites[set]))?;
        row(&mut moments, &format!("{name}\t-\tR\t{}\n", join(&census.rsum[set * dw..(set + 1) * dw])))?;
        for l in 0..a {
            let (lin, quad) = ((set * a + l) * dw, (set * a + l) * tri);
            for (kind, v) in [("LN", &census.ln[lin..lin + dw]), ("LF", &census.lf[lin..lin + dw]), ("LF_carried", &census.lfc[lin..lin + dw]), ("QN", &census.qn[quad..quad + tri]), ("QF", &census.qf[quad..quad + tri]), ("QF_carried", &census.qfc[quad..quad + tri])] {
                row(&mut moments, &format!("{name}\t{l}\t{kind}\t{}\n", join(v)))?;
            }
        }
    }
    println!("FIELD_PHASE_DONE sections={take} of={} train_ms={train_ms} held_ms={held_ms} ms={}", order.len(), started.elapsed().as_millis());
    Ok(())
}

/// [definition; theory, November 10 03:45] **A census's TRAIN sample of one parity of the problems' index**: `SAMPLE` a count,
/// its first so many in file order, or `every-K`, every `K`th problem of the parity across the whole file (TRAIN.txt is ordered
/// by kind, so a spread sample meets every kind).
fn parity_sample<'p>(train: &'p [(Vec<u8>, Vec<u8>)], parity: usize, sample: &str) -> Result<Vec<&'p (Vec<u8>, Vec<u8>)>> {
    let of = train.iter().skip(parity).step_by(2);
    Ok(match sample.strip_prefix("every-") {
        Some(k) => of.step_by(positive(k)?).collect(),
        None => of.take(count(sample)?).collect(),
    })
}

/// [definition; theory, November 10 03:45] The reach census's offsets: `±1, 2, 3, 4, 6, 8, 12, 16, …, 192, 256`.
const REACH: [usize; 16] = [1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64, 96, 128, 192, 256];

/// [measurement; theory, November 10 04:40] **The reach census's sums on a partly locked state**: `N` and `F` by
/// `[set][offset][far][letter]`, the far place's letter where it is locked, a blank (`far = alphabet`) where it is open, the void
/// past the region's ends; `F` each share on the face's width `2^(−62)`, its remainder carried on `2^(−94)`.
struct Reach2 {
    a: usize,
    offsets: Vec<i64>,
    n: Vec<u64>,
    f: Vec<u128>,
    fc: Vec<i128>,
    places: [usize; 3],
}

impl Reach2 {
    fn new(a: usize) -> Self {
        let offsets: Vec<i64> = REACH.iter().flat_map(|&d| [-(d as i64), d as i64]).collect();
        let cells = 3 * offsets.len() * (a + 1) * a;
        Self { a, offsets, n: vec![0; cells], f: vec![0; cells], fc: vec![0; cells], places: [0; 3] }
    }

    fn add(&mut self, set: usize, face: &holonics::hnn::tower::TowerFace, truth: usize, classes: &[usize], open: &[bool], at: usize, void: usize) {
        let shares: Vec<(u128, i128)> = face
            .masses
            .iter()
            .map(|&m| {
                let share = (m << 62) / face.total;
                let rem = (m << 62) - share * face.total;
                (share, (((rem << 32) + face.total / 2) / face.total) as i128)
            })
            .collect();
        let a = self.a;
        for (o, &d) in self.offsets.iter().enumerate() {
            let far = match usize::try_from(at as i64 + d).ok().filter(|&u| u < classes.len()) {
                Some(u) if open[u] => a,
                Some(u) => classes[u],
                None => void,
            };
            let cell = ((set * self.offsets.len() + o) * (a + 1) + far) * a;
            self.n[cell + truth] += 1;
            for (l, &(share, carried)) in shares.iter().enumerate() {
                self.f[cell + l] += share;
                self.fc[cell + l] += carried;
            }
        }
        self.places[set] += 1;
    }
}

/// [measurement; theory, November 10 04:40] `reach2-field UNITS UNITS_SHA TRAIN TRAIN_SHA HELD HELD_SHA KEYS KEYS_SHA SECTION
/// SECTIONS STATE STATE_SHA LINE EVERY OUT`: **the reach census on census 2b's charge set**: the lap's own partly locked states
/// ([`lap_visit`], 2b's checks with `LINE`), at the answer sites it charges of TRAIN's spread sample (every `EVERY`th problem of
/// each parity of the index, two sets), and the held problems' own joint states (every open place); at each site `t` and each
/// offset `d = ±`[`REACH`], the far place's letter where it is locked, a blank where it is open and the void past the region's
/// ends, against the letter at `t` ([`Reach2`]). `REACH2.tsv` holds every (set, d, far, letter, n, f) (far `blank` for an open
/// place); `FIELD_REACH2` a line per (set, d): `U` a place, `Σ N ln(N/F)` over (far, letter) less the same with far pooled, and
/// the places. Numbers only.
pub(super) fn reach2_field(args: &[String], realization: &mut dyn FieldRealization) -> Result<()> {
    if args.len() != 16 {
        return Err("reach2-field UNITS UNITS_SHA TRAIN TRAIN_SHA HELD HELD_SHA KEYS KEYS_SHA SECTION SECTIONS STATE STATE_SHA LINE EVERY OUT".into());
    }
    let started = std::time::Instant::now();
    let units = units_of(&args[1], &args[2])?;
    let train_problems = problems_of(&pinned_read(&args[3], &args[4], READ_BUDGET as usize)?);
    let dev_problems = problems_of(&pinned_read(&args[5], &args[6], READ_BUDGET as usize)?);
    let keys = pinned_read(&args[7], &args[8], READ_BUDGET as usize)?;
    let (section, limit) = (positive(&args[9])?, count(&args[10])?);
    let mut learner = FieldLearner::from_text(std::str::from_utf8(&pinned_read(&args[11], &args[12], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    declared_clocks(&mut learner.field);
    let line = args[13].as_str();
    let every = positive(&args[14])?;
    let out = Path::new(&args[15]);
    std::fs::create_dir(out)?;
    let codec = FieldCodec::found(units, &train_problems)?;
    let encode = |problems: &[(Vec<u8>, Vec<u8>)]| -> Result<Problems> {
        problems.par_iter().map(|(q, a)| Ok((codec.encode(&question_text(q)).map_err(|e| e.to_string())?, codec.encode(a).map_err(|e| e.to_string())?, a.len()))).collect::<std::result::Result<Vec<_>, String>>().map_err(|e| e.into())
    };
    let train_set = encode(&train_problems)?;
    let dev_set: Problems = encode(&dev_problems)?.into_iter().filter(|(_, a, _)| a.len() < codec.answer).collect();
    let seed = u64::from_be_bytes(keys.get(keys.len().saturating_sub(8)..).filter(|w| w.len() == 8).ok_or("a key file of fewer than eight bytes")?.try_into()?);
    let (sections, _) = sections_of(&train_set, section, dev_set.len(), seed);
    if learner.holds_step() {
        return Err("reach2-field reads a state that holds no step (it never deposits)".into());
    }
    println!("FIELD_CLOCKS per_blank={} bare={} laps_read={}", learner.field.per_blank_clock, learner.field.bare_stretch, learner.laps);
    let (a, void) = (learner.field.declaration.alphabet, codec.void());
    let read = learner.laps;
    let draw = read * train_set.len() as u64;
    let paths = paths_of(seed, read, &sections);
    let order = walk(seed, read, sections.len());
    let take = if limit == 0 { order.len() } else { limit.min(order.len()) };
    let mut sums = Reach2::new(a);
    let charge = lap_visit(&codec, &train_set, &sections, &paths, &order[..take], seed, draw, &mut learner, realization, true, Some(line), &mut |site| {
        if !site.asked && (site.problem / 2) % every == 0 {
            sums.add(site.problem % 2, site.face, site.truth, site.classes, site.open, site.at, void);
        }
    })?;
    let bounded = charge.sites <= charge.bound;
    println!("FIELD_CHECK check=2 result={} charged={} question={} answer={} bound={} sections={take}", if bounded { "PASS" } else { "FAIL" }, charge.sites, charge.question, charge.sites - charge.question, charge.bound);
    println!("FIELD_CHECK check=3 part=visit result={} leaks={}", if charge.leaks == 0 { "PASS" } else { "FAIL" }, charge.leaks);
    if !bounded || charge.leaks > 0 {
        return Err("the reach census refuses to read: a check failed over the visit".into());
    }
    let train_ms = started.elapsed().as_millis();
    let mut states: Vec<(Vec<usize>, Vec<bool>)> = Vec::new();
    for (i, (q, ans, _)) in dev_set.iter().enumerate() {
        states.extend(joint_states(void, q, ans, seed, i as u64).into_iter().map(|(c, u, _)| (c, u)));
    }
    for chunk in states.chunks(64) {
        let views: Vec<Region> = chunk.iter().map(|(c, u)| Region { classes: c, unresolved: u, faces: &[], locked: &[], echo: &[], domain: None, port: None }).collect();
        let faces = realization.read_faces(&learner.field, &views).map_err(|e| e.to_string())?;
        for ((c, u), f) in chunk.iter().zip(&faces) {
            for t in (0..c.len()).filter(|&t| u[t]) {
                let face = f[t].as_ref().ok_or("a held state's open place without a face")?;
                sums.add(2, face, c[t], c, u, t, void);
            }
        }
    }
    let names = ["train_even", "train_odd", "held"];
    let folded = |i: usize| -> u128 { (sums.f[i] as i128 + ((sums.fc[i] + (1 << 31)) >> 32)).max(0) as u128 };
    let on20 = |v: u128| -> u128 { (v + (1 << 41)) >> 42 };
    let charged = |counts: &[u64], expected: &[u128]| -> i128 { counts.iter().zip(expected).filter(|&(&c, _)| c > 0).map(|(&c, &e)| c as i128 * log2_ratio(c, e)).sum() };
    let mut file = rows_file(&out.join("REACH2.tsv"), "set\td\tfar\tletter\tn\tf_q62\n")?;
    for (set, name) in names.iter().enumerate() {
        for (o, &d) in sums.offsets.iter().enumerate() {
            let base = (set * sums.offsets.len() + o) * (a + 1) * a;
            let (mut joint, mut pooled_n, mut pooled_f) = (0i128, vec![0u64; a], vec![0u128; a]);
            for far in 0..=a {
                let cell = base + far * a;
                let counts = &sums.n[cell..cell + a];
                let expected: Vec<u128> = (0..a).map(|l| folded(cell + l)).collect();
                joint += charged(counts, &expected.iter().map(|&v| on20(v)).collect::<Vec<_>>());
                let far_name = if far == a { "blank".to_string() } else { far.to_string() };
                for l in 0..a {
                    pooled_n[l] += counts[l];
                    pooled_f[l] += expected[l];
                    row(&mut file, &format!("{name}\t{d}\t{far_name}\t{l}\t{}\t{}\n", counts[l], expected[l]))?;
                }
            }
            let marginal = charged(&pooled_n, &pooled_f.iter().map(|&v| on20(v)).collect::<Vec<_>>());
            let places = sums.places[set];
            let per = |v: i128| if places == 0 { "-".to_string() } else { decimal_q20(nats_q20(v) / places as i128) };
            println!("FIELD_REACH2 set={name} d={d} places={places} u_nats_a_place={} joint_nats_a_place={} pooled_nats_a_place={}", per(joint - marginal), per(joint), per(marginal));
        }
    }
    println!("FIELD_REACH2_DONE sections={take} of={} train_ms={train_ms} ms={}", order.len(), started.elapsed().as_millis());
    Ok(())
}

/// [measurement; theory, November 10 03:45] `reach-census-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD HELD_SHA
/// TRAIN TRAIN_SHA SAMPLE OUT`: **the reach census**, on the ring census's locked visit ([`ring_census_field`]: each reference
/// cut to its room, every answer place read once with the rest locked, [`Field::locked_faces`]), three sets (the held
/// problems, and TRAIN's sample of each parity, [`parity_sample`]). At each answer place `t` and each offset `d = ±`[`REACH`]:
/// the letter at `t + d` (the question's letters included, the void past either end) against the letter at `t`, its count `N`
/// and the face's share `F` at `t` (each share on the face's width `2^(−62)`, its remainder carried on `2^(−94)` and folded to
/// the nearest in `REACH.tsv`). `REACH.tsv` holds every (set, d, far letter, letter, n, f); `FIELD_REACH` a line per (set, d):
/// `U` a place, `Σ N ln(N/F)` over (far letter, letter) less the same with the far letter pooled, and the places. Numbers
/// only.
///
/// [measurement; theory, November 10 04:55] `SET` (held, train_even or train_odd, before `OUT`) reads that set alone; every set's
/// table is written as `REACH.<set>.tsv` at the end of its set, and its `FIELD_REACH` lines flushed there, so a partition of the
/// sets across runs loses nothing a deadline stops.
pub(super) fn reach_census_field(args: &[String], realization: &mut dyn FieldRealization) -> Result<()> {
    if args.len() != 13 && args.len() != 14 {
        return Err("reach-census-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD HELD_SHA TRAIN TRAIN_SHA SAMPLE [SET] OUT".into());
    }
    let started = std::time::Instant::now();
    let mut learner = FieldLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    declared_clocks(&mut learner.field);
    let field = &learner.field;
    let units = units_of(&args[5], &args[6])?;
    let codec = FieldCodec::from_text(std::str::from_utf8(&pinned_read(&args[3], &args[4], CODEC_BUDGET)?)?, units)?;
    let held = problems_of(&pinned_read(&args[7], &args[8], READ_BUDGET as usize)?);
    let train = problems_of(&pinned_read(&args[9], &args[10], READ_BUDGET as usize)?);
    let sample = args[11].as_str();
    let only = (args.len() == 14).then(|| args[12].as_str());
    let out = Path::new(&args[args.len() - 1]);
    std::fs::create_dir(out)?;
    let void = codec.void();
    let a = field.declaration.alphabet;
    let names = ["held", "train_even", "train_odd"];
    if only.is_some_and(|o| !names.contains(&o)) {
        return Err("a reach census set that is not held, train_even or train_odd".into());
    }
    let sets: [Vec<&(Vec<u8>, Vec<u8>)>; 3] = [held.iter().collect(), parity_sample(&train, 0, sample)?, parity_sample(&train, 1, sample)?];
    let offsets: Vec<i64> = REACH.iter().flat_map(|&d| [-(d as i64), d as i64]).collect();
    // [set][d][far][letter]: counts, shares on 2^(−62) and their carried remainders on 2^(−94).
    let cells = names.len() * offsets.len() * a * a;
    let (mut n, mut f, mut fc) = (vec![0u64; cells], vec![0u128; cells], vec![0i128; cells]);
    let mut places = [0usize; 3];
    const BATCH: usize = 32;
    for (set, problems) in sets.iter().enumerate() {
        if only.is_some_and(|o| o != names[set]) {
            continue;
        }
        for (b, batch) in problems.chunks(BATCH).enumerate() {
            let requests: Vec<(Vec<usize>, usize)> = batch.iter().map(|(question, _)| opening(&codec, field, question, b"")).collect::<std::result::Result<_, String>>()?;
            let mut answers: Vec<Vec<usize>> = Vec::with_capacity(batch.len());
            for ((_, ans), (_, room)) in batch.iter().zip(&requests) {
                let mut x = codec.encode(ans)?;
                x.truncate(*room);
                answers.push(x);
            }
            let ks: Vec<usize> = (0..batch.len()).filter(|&k| !answers[k].is_empty()).collect();
            let regions: Vec<(&[usize], usize)> = requests.iter().map(|(q, room)| (q.as_slice(), *room)).collect();
            let faces = field.locked_faces(&regions, &answers, &ks, void, false, realization).map_err(|e| e.to_string())?;
            for (&k, fk) in ks.iter().zip(&faces) {
                let (q, x) = (&requests[k].0, &answers[k]);
                let line: Vec<usize> = q.iter().chain(x).copied().collect();
                for (t, face) in fk.iter().enumerate().take(x.len()) {
                    let at = q.len() + t;
                    let shares: Vec<(u128, i128)> = face
                        .masses
                        .iter()
                        .map(|&m| {
                            let share = (m << 62) / face.total;
                            let rem = (m << 62) - share * face.total;
                            (share, (((rem << 32) + face.total / 2) / face.total) as i128)
                        })
                        .collect();
                    for (o, &d) in offsets.iter().enumerate() {
                        let far = usize::try_from(at as i64 + d).ok().and_then(|u| line.get(u).copied()).unwrap_or(void);
                        let cell = ((set * offsets.len() + o) * a + far) * a;
                        n[cell + x[t]] += 1;
                        for (l, &(share, carried)) in shares.iter().enumerate() {
                            f[cell + l] += share;
                            fc[cell + l] += carried;
                        }
                    }
                }
                places[set] += x.len();
            }
            println!("FIELD_REACH_BATCH set={} batch={b} problems={} places={} elapsed_ms={}", names[set], batch.len(), places[set], started.elapsed().as_millis());
            let _ = std::io::Write::flush(&mut std::io::stdout());
        }
        reach_table(&out.join(format!("REACH.{}.tsv", names[set])), names[set], &offsets, a, &n[set * offsets.len() * a * a..(set + 1) * offsets.len() * a * a], &f[set * offsets.len() * a * a..(set + 1) * offsets.len() * a * a], &fc[set * offsets.len() * a * a..(set + 1) * offsets.len() * a * a], places[set])?;
    }
    println!("FIELD_REACH_DONE ms={}", started.elapsed().as_millis());
    Ok(())
}

/// One reach census set's table (`[d][far][letter]`: its counts, shares on `2^(−62)` and their carried remainders on `2^(−94)`)
/// written to `path` (set, d, far, letter, n, f folded to the nearest) and its `FIELD_REACH` lines printed and flushed: `U` a
/// place, `Σ N ln(N/F)` over (far, letter) less the same with the far letter pooled.
#[allow(clippy::too_many_arguments)]
fn reach_table(path: &Path, name: &str, offsets: &[i64], a: usize, n: &[u64], f: &[u128], fc: &[i128], places: usize) -> Result<()> {
    let folded = |i: usize| -> u128 { (f[i] as i128 + ((fc[i] + (1 << 31)) >> 32)).max(0) as u128 };
    let on20 = |v: u128| -> u128 { (v + (1 << 41)) >> 42 };
    let charge = |counts: &[u64], expected: &[u128]| -> i128 { counts.iter().zip(expected).filter(|&(&c, _)| c > 0).map(|(&c, &e)| c as i128 * log2_ratio(c, e)).sum() };
    let per = |v: i128| if places == 0 { "-".to_string() } else { decimal_q20(nats_q20(v) / places as i128) };
    let mut file = rows_file(path, "set\td\tfar\tletter\tn\tf_q62\n")?;
    for (o, &d) in offsets.iter().enumerate() {
        let base = o * a * a;
        let (mut joint, mut pooled_n, mut pooled_f) = (0i128, vec![0u64; a], vec![0u128; a]);
        for far in 0..a {
            let cell = base + far * a;
            let counts = &n[cell..cell + a];
            let expected: Vec<u128> = (0..a).map(|l| folded(cell + l)).collect();
            joint += charge(counts, &expected.iter().map(|&v| on20(v)).collect::<Vec<_>>());
            for l in 0..a {
                pooled_n[l] += counts[l];
                pooled_f[l] += expected[l];
                row(&mut file, &format!("{name}\t{d}\t{far}\t{l}\t{}\t{}\n", counts[l], expected[l]))?;
            }
        }
        let marginal = charge(&pooled_n, &pooled_f.iter().map(|&v| on20(v)).collect::<Vec<_>>());
        println!("FIELD_REACH set={name} d={d} places={places} u_nats_a_place={} joint_nats_a_place={} pooled_nats_a_place={}", per(joint - marginal), per(joint), per(marginal));
    }
    let _ = std::io::Write::flush(&mut std::io::stdout());
    Ok(())
}

/// [measurement; theory, November 10 02:03] The ring census's rings: a symbol's count (less its closing symbol's, where it has
/// one) in a reference's letters before a place, modulo the ring.
const RINGS: [(&str, u8, Option<u8>, i64); 5] = [("backtick", b'`', None, 2), ("paren", b'(', Some(b')'), 3), ("bracket", b'[', Some(b']'), 3), ("dquote", b'"', None, 2), ("squote", b'\'', None, 2)];

/// The ring census's sums: `N` and `F` (each share on the face's own width `2^(−62)`, its remainder carried on `2^(−94)`) by
/// `[set][ring][residue][letter]`, residues up to three.
struct RingSums {
    a: usize,
    n: Vec<u64>,
    f: Vec<u128>,
    fc: Vec<i128>,
}

impl RingSums {
    fn new(a: usize, sets: usize) -> Self {
        let len = sets * RINGS.len() * 3 * a;
        Self { a, n: vec![0; len], f: vec![0; len], fc: vec![0; len] }
    }

    fn add(&mut self, set: usize, residues: &[usize; 5], face: &holonics::hnn::tower::TowerFace, truth: usize) {
        for (ring, &res) in residues.iter().enumerate() {
            let at = ((set * RINGS.len() + ring) * 3 + res) * self.a;
            self.n[at + truth] += 1;
            for (c, &m) in face.masses.iter().enumerate() {
                let share = (m << 62) / face.total;
                let rem = (m << 62) - share * face.total;
                self.f[at + c] += share;
                self.fc[at + c] += (((rem << 32) + face.total / 2) / face.total) as i128;
            }
        }
    }

    fn write(&self, path: &Path, names: &[&str]) -> Result<()> {
        let mut file = rows_file(path, "set\tring\tmodulus\tresidue\tletter\tn\tf_q62\tf_carried_q94\n")?;
        for (set, name) in names.iter().enumerate() {
            for (ring, &(ring_name, _, _, modulus)) in RINGS.iter().enumerate() {
                for res in 0..modulus as usize {
                    let at = ((set * RINGS.len() + ring) * 3 + res) * self.a;
                    for c in 0..self.a {
                        row(&mut file, &format!("{name}\t{ring_name}\t{modulus}\t{res}\t{c}\t{}\t{}\t{}\n", self.n[at + c], self.f[at + c], self.fc[at + c]))?;
                    }
                }
            }
        }
        Ok(())
    }
}

/// [measurement; theory, November 10 02:03] `ring-census-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD HELD_SHA TRAIN
/// TRAIN_SHA SAMPLE OUT`: **the locked-state ring census**. Three sets: the held problems, and TRAIN's sample of each parity of
/// their index ([`parity_sample`]: `SAMPLE` a count, the first so many, or `every-K`, every `K`th across the whole file). Each reference (cut to its room) is read with every place locked: every face once, each place
/// alone open with the rest of the reference given ([`Field::locked_faces`], the run from the references' own re-read), and
/// the stop place (the first void past the letters) likewise. On the host, from the reference's letters before each place, five
/// ring residues ([`RINGS`]: the backticks mod 2, `(` less `)` mod 3, `[` less `]` mod 3, the double quotes mod 2, the single
/// quotes mod 2). `RING.tsv` holds `N` and `F` by set, ring, residue and letter at the letters' places, `RING_STOP.tsv` the same
/// at the stop places (`F` each share on the face's width `2^(−62)`, its remainder carried on `2^(−94)`). Numbers only.
pub(super) fn ring_census_field(args: &[String], realization: &mut dyn FieldRealization) -> Result<()> {
    if args.len() != 13 {
        return Err("ring-census-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD HELD_SHA TRAIN TRAIN_SHA SAMPLE OUT".into());
    }
    let started = std::time::Instant::now();
    let mut learner = FieldLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    declared_clocks(&mut learner.field);
    let field = &learner.field;
    let units = units_of(&args[5], &args[6])?;
    let codec = FieldCodec::from_text(std::str::from_utf8(&pinned_read(&args[3], &args[4], CODEC_BUDGET)?)?, units)?;
    let held = problems_of(&pinned_read(&args[7], &args[8], READ_BUDGET as usize)?);
    let train = problems_of(&pinned_read(&args[9], &args[10], READ_BUDGET as usize)?);
    let sample = args[11].as_str();
    let out = Path::new(&args[12]);
    std::fs::create_dir(out)?;
    let void = codec.void();
    let a = field.declaration.alphabet;
    // Each class's count on each ring.
    let marks: Vec<[i64; 5]> = (0..a)
        .map(|c| {
            let bytes = if c == void { Vec::new() } else { codec.decode(&[c]) };
            RINGS.map(|(_, open, close, _)| bytes.iter().filter(|&&b| b == open).count() as i64 - close.map_or(0, |cl| bytes.iter().filter(|&&b| b == cl).count() as i64))
        })
        .collect();
    let names = ["held", "train_even", "train_odd"];
    let sets: [Vec<&(Vec<u8>, Vec<u8>)>; 3] = [held.iter().collect(), parity_sample(&train, 0, sample)?, parity_sample(&train, 1, sample)?];
    let (mut letters_sums, mut stop_sums) = (RingSums::new(a, names.len()), RingSums::new(a, names.len()));
    const BATCH: usize = 32;
    for (set, problems) in sets.iter().enumerate() {
        let (mut places, mut stops, mut cut, mut empty) = (0usize, 0usize, 0usize, 0usize);
        for (b, batch) in problems.chunks(BATCH).enumerate() {
            let requests: Vec<(Vec<usize>, usize)> = batch.iter().map(|(question, _)| opening(&codec, field, question, b"")).collect::<std::result::Result<_, String>>()?;
            let mut answers: Vec<Vec<usize>> = Vec::with_capacity(batch.len());
            for ((_, ans), (_, room)) in batch.iter().zip(&requests) {
                let mut x = codec.encode(ans).map_err(|e| e.to_string())?;
                cut += usize::from(x.len() > *room);
                x.truncate(*room);
                answers.push(x);
            }
            let ks: Vec<usize> = (0..batch.len()).filter(|&k| !answers[k].is_empty()).collect();
            empty += batch.len() - ks.len();
            let problems: Vec<(&[usize], usize)> = requests.iter().map(|(q, n)| (q.as_slice(), *n)).collect();
            let faces = field.locked_faces(&problems, &answers, &ks, void, true, realization).map_err(|e| e.to_string())?;
            for (&k, f) in ks.iter().zip(&faces) {
                let x = &answers[k];
                let mut ring = [0i64; 5];
                let residues = |ring: &[i64; 5]| -> [usize; 5] { std::array::from_fn(|r| ring[r].rem_euclid(RINGS[r].3) as usize) };
                for (t, face) in f.iter().enumerate().take(x.len()) {
                    letters_sums.add(set, &residues(&ring), face, x[t]);
                    for (r, v) in ring.iter_mut().enumerate() {
                        *v += marks[x[t]][r];
                    }
                }
                places += x.len();
                if let Some(face) = f.get(x.len()) {
                    stop_sums.add(set, &residues(&ring), face, void);
                    stops += 1;
                }
            }
            println!("FIELD_RING_BATCH set={} batch={b} problems={} places={places} stops={stops} elapsed_ms={}", names[set], batch.len(), started.elapsed().as_millis());
            let _ = std::io::Write::flush(&mut std::io::stdout());
        }
        println!("FIELD_RING_SET set={} problems={} places={places} stops={stops} cut_to_room={cut} empty={empty}", names[set], problems.len());
    }
    letters_sums.write(&out.join("RING.tsv"), &names)?;
    stop_sums.write(&out.join("RING_STOP.tsv"), &names)?;
    println!("FIELD_RING_DONE ms={}", started.elapsed().as_millis());
    Ok(())
}

/// The answers a written file holds (`SAMPLE.tsv`'s format: a line a problem, its index and its escaped letters), encoded.
fn written_answers(codec: &FieldCodec, path: &str, sha: &str, problems: usize) -> Result<Vec<Vec<usize>>> {
    let text = pinned_read(path, sha, READ_BUDGET as usize)?;
    let mut out = Vec::with_capacity(problems);
    for (n, line) in text.split(|&b| b == b'\n').filter(|l| !l.is_empty()).take(problems).enumerate() {
        let tab = line.iter().position(|&b| b == b'\t').ok_or("a written line without its index")?;
        if std::str::from_utf8(&line[..tab])?.parse::<usize>()? != n {
            return Err("a written file whose lines are not its problems in order".into());
        }
        out.push(codec.encode(&super::written_coupling::unescape(&line[tab + 1..])?)?);
    }
    if out.len() != problems {
        return Err(format!("a written file of {} answers for {problems} problems", out.len()).into());
    }
    Ok(out)
}

/// [measurement; theory, November 10 03:25] `charge-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD HELD_SHA COUNT
/// REST REST_SHA KEYED KEYED_SHA OUT`: **the state charge census**, a reading of three locked states of the first `COUNT` held
/// problems: the settle's rest (`REST`, a `SAMPLE.tsv`), the keyed write it started from (`KEYED`) and the held file's own
/// references, each cut to its room. Each state is read with every place locked ([`Field::locked_faces`]: every face once,
/// that place alone open, the rest given), and at each place `v = −ln f_t(x_t) − H(f_t)` in nats, the letter's surprise less
/// its face's entropy. Printed a state: its code and summed entropy pooled and a problem; the share of places with `v > 1`
/// and with `v > 2`; the runs of `v > 1` by length (1, 2, 3–4, 5–8, …) and the share of those places in runs of three or
/// more; `v` by the place's share of its answer (tenths, `⌊10 t/n⌋`); and each answer's root charge
/// `Σ_a N(a) ln(N(a)/Σ_t f_t(a))` (its letters' counts against the faces' summed shares, [`PlateCounts`]) beside its excess
/// (code less entropy) and its share of it. Numbers only.
pub(super) fn charge_field(args: &[String], realization: &mut dyn FieldRealization) -> Result<()> {
    if args.len() != 15 {
        return Err("charge-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD HELD_SHA COUNT REST REST_SHA KEYED KEYED_SHA OUT".into());
    }
    let started = std::time::Instant::now();
    let mut learner = FieldLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    declared_clocks(&mut learner.field);
    let field = &learner.field;
    let units = units_of(&args[5], &args[6])?;
    let codec = FieldCodec::from_text(std::str::from_utf8(&pinned_read(&args[3], &args[4], CODEC_BUDGET)?)?, units)?;
    let held = problems_of(&pinned_read(&args[7], &args[8], READ_BUDGET as usize)?);
    let limit = count(&args[9])?;
    let out = Path::new(&args[14]);
    std::fs::create_dir(out)?;
    let held = &held[..limit.min(held.len())];
    let requests: Vec<(Vec<usize>, usize)> = held.iter().map(|(question, _)| opening(&codec, field, question, b"")).collect::<std::result::Result<_, String>>()?;
    let problems: Vec<(&[usize], usize)> = requests.iter().map(|(q, n)| (q.as_slice(), *n)).collect();
    let void = codec.void();
    let a = field.declaration.alphabet;
    let references: Vec<Vec<usize>> = held.iter().map(|(_, ans)| codec.encode(ans)).collect::<Result<_>>()?;
    let states = [("rest", written_answers(&codec, &args[10], &args[11], held.len())?), ("keyed", written_answers(&codec, &args[12], &args[13], held.len())?), ("reference", references)];
    let nats = |v: i128| decimal_q20(nats_q20(v));
    let share = |n: usize, of: usize| if of == 0 { "-".to_string() } else { format!("{}.{:06}", n * 1_000_000 / of / 1_000_000, n * 1_000_000 / of % 1_000_000) };
    for (name, mut answers) in states {
        let state_start = std::time::Instant::now();
        let mut cut = 0usize;
        for (x, &(_, room)) in answers.iter_mut().zip(&problems) {
            cut += usize::from(x.len() > room);
            x.truncate(room);
        }
        let ks: Vec<usize> = (0..problems.len()).filter(|&k| !answers[k].is_empty()).collect();
        let faces = field.locked_faces(&problems, &answers, &ks, void, false, realization).map_err(|e| e.to_string())?;
        let (mut places, mut over1, mut over2, mut in_long) = (0usize, 0usize, 0usize, 0usize);
        let (mut code, mut entropy, mut root) = (0i128, 0i128, 0i128);
        let mut runs: Vec<(usize, usize)> = Vec::new();
        let mut tenths = [(0i128, 0usize); 10];
        for (&k, f) in ks.iter().zip(&faces) {
            let x = &answers[k];
            let n = x.len();
            let (mut c_k, mut h_k) = (0i128, 0i128);
            let mut counts = PlateCounts::new(a);
            let mut run = 0usize;
            let close = |run: usize, runs: &mut Vec<(usize, usize)>, in_long: &mut usize| {
                if run > 0 {
                    let bin = (usize::BITS - (run - 1).leading_zeros()) as usize;
                    if runs.len() <= bin {
                        runs.resize(bin + 1, (0, 0));
                    }
                    runs[bin] = (runs[bin].0 + 1, runs[bin].1 + run);
                    if run >= 3 {
                        *in_long += run;
                    }
                }
            };
            for (t, face) in f.iter().enumerate().take(n) {
                let (c, h) = (face.code(x[t]) as i128, holonics::hnn::tower::field::entropy(face));
                (c_k, h_k) = (c_k + c, h_k + h);
                counts.add(face, x[t]);
                let v = nats_q20(c - h);
                over1 += usize::from(v > 1 << 20);
                over2 += usize::from(v > 2 << 20);
                if v > 1 << 20 {
                    run += 1;
                } else {
                    close(run, &mut runs, &mut in_long);
                    run = 0;
                }
                let tenth = &mut tenths[(10 * t / n).min(9)];
                *tenth = (tenth.0 + c - h, tenth.1 + 1);
            }
            close(run, &mut runs, &mut in_long);
            let r_k: i128 = (0..a).filter(|&l| counts.n[l] > 0).map(|l| counts.n[l] as i128 * log2_ratio(counts.n[l], counts.expected(l))).sum();
            let excess = c_k - h_k;
            println!(
                "FIELD_CHARGE_PROBLEM state={name} problem={k} letters={n} code_nats={} entropy_nats={} excess_nats={} root_nats={} root_share_of_excess={}",
                nats(c_k),
                nats(h_k),
                nats(excess),
                nats(r_k),
                if excess <= 0 { "-".to_string() } else { decimal_q20((r_k << 20) / excess) }
            );
            (places, code, entropy, root) = (places + n, code + c_k, entropy + h_k, root + r_k);
        }
        let excess = code - entropy;
        let a_place = |v: i128| if places == 0 { "-".to_string() } else { decimal_q20(nats_q20(v) / places as i128) };
        println!(
            "FIELD_CHARGE_STATE state={name} problems={} letters={places} cut_to_room={cut} code_nats={} entropy_nats={} code_nats_a_place={} entropy_nats_a_place={} excess_nats={} root_nats={} root_share_of_excess={} v_over_1_share={} v_over_2_share={} ms={}",
            ks.len(),
            nats(code),
            nats(entropy),
            a_place(code),
            a_place(entropy),
            nats(excess),
            nats(root),
            if excess <= 0 { "-".to_string() } else { decimal_q20((root << 20) / excess) },
            share(over1, places),
            share(over2, places),
            state_start.elapsed().as_millis()
        );
        let hist: Vec<String> = runs.iter().enumerate().map(|(b, &(n, sites))| format!("{}:{n}:{sites}", if b == 0 { "1".to_string() } else if b == 1 { "2".to_string() } else { format!("{}-{}", (1usize << (b - 1)) + 1, 1usize << b) })).collect();
        println!("FIELD_CHARGE_RUNS state={name} runs_by_length={} over_1_places={over1} share_in_runs_of_3_or_more={}", hist.join(","), share(in_long, over1));
        for (b, &(v, n)) in tenths.iter().enumerate() {
            println!("FIELD_CHARGE_WRITTEN state={name} written=0.{b}-{} places={n} v_nats_a_place={}", if b == 9 { "1".to_string() } else { format!("0.{}", b + 1) }, if n == 0 { "-".to_string() } else { decimal_q20(nats_q20(v) / n as i128) });
        }
    }
    println!("FIELD_CHARGE_DONE ms={}", started.elapsed().as_millis());
    Ok(())
}

/// [definition; theory, November 10 04:40] **A ring census's tilts** (`RING.tsv` or `RING_STOP.tsv`, [`ring_census_field`]): each
/// (ring, residue, letter)'s `N` and `F` pooled over TRAIN's sets (the held set left out), `F` on the face's width with its
/// carried remainder folded in; a cell of at least `floor` sites kept as `(N, F)` (`F` on `2^(−20)`), the rest dropped.
/// `[ring][residue][letter]`.
type RingTilts = Vec<Vec<Vec<Option<(u64, u128)>>>>;

fn ring_tilts(text: &[u8], a: usize, floor: u64) -> Result<RingTilts> {
    let (mut n, mut f) = (vec![vec![vec![0u64; a]; 3]; RINGS.len()], vec![vec![vec![0i128; a]; 3]; RINGS.len()]);
    for line in std::str::from_utf8(text)?.lines().skip(1) {
        let cells: Vec<&str> = line.split('\t').collect();
        let [set, ring, _, residue, letter, count_n, share, carried] = cells[..] else { return Err("a ring census row that is not set, ring, modulus, residue, letter, n, f and its carried remainder".into()) };
        if set == "held" {
            continue;
        }
        let r = RINGS.iter().position(|x| x.0 == ring).ok_or("a ring census row of no ring")?;
        let (res, l) = (residue.parse::<usize>()?, letter.parse::<usize>()?);
        if res >= 3 || l >= a {
            return Err("a ring census row outside its rings or its letters".into());
        }
        n[r][res][l] += count_n.parse::<u64>()?;
        f[r][res][l] += share.parse::<u128>()? as i128 + ((carried.parse::<i128>()? + (1 << 31)) >> 32);
    }
    Ok((0..RINGS.len()).map(|r| (0..3).map(|res| (0..a).map(|l| (n[r][res][l] >= floor && f[r][res][l] > 0).then(|| (n[r][res][l], ((f[r][res][l] + (1 << 41)) >> 42).max(1) as u128))).collect()).collect()).collect())
}

/// [definition; theory, November 10 04:40] **A face tilted by one ring's cell row**: each kept letter's mass times `N/F`, then every
/// mass shifted right together where the largest passes the face's width `2^62` (the face's shares unchanged to that grain).
fn ring_tilt_face(face: &mut holonics::hnn::tower::TowerFace, cells: &[Option<(u64, u128)>]) {
    for (m, cell) in face.masses.iter_mut().zip(cells) {
        if let Some((n, f)) = cell {
            *m = *m * ((*n as u128) << 20) / f;
        }
    }
    let top = face.masses.iter().copied().max().unwrap_or(0);
    if top >> 62 > 0 {
        let shift = 128 - top.leading_zeros() - 62;
        face.masses.iter_mut().for_each(|m| *m >>= shift);
    }
    face.total = face.masses.iter().sum::<u128>().max(1);
}

/// The ring lens a certificate reads through ([`Field::redraw_lensed`]).
type RingLens = Box<dyn Fn(&[usize], &mut [holonics::hnn::tower::TowerFace])>;

/// [definition; theory, November 10 04:40] **The ring lens**: at each place the ring residues of the answer's letters before it
/// ([`RINGS`], each class's counts from its bytes), each ring's kept cells at that residue tilting the face; the letters' places by
/// `letters`, the stop place (past the letters) by `stops`.
fn ring_lens(codec: &FieldCodec, a: usize, letters: RingTilts, stops: RingTilts) -> RingLens {
    let void = codec.void();
    let marks: Vec<[i64; 5]> = (0..a)
        .map(|c| {
            let bytes = if c == void { Vec::new() } else { codec.decode(&[c]) };
            RINGS.map(|(_, open, close, _)| bytes.iter().filter(|&&b| b == open).count() as i64 - close.map_or(0, |cl| bytes.iter().filter(|&&b| b == cl).count() as i64))
        })
        .collect();
    Box::new(move |x: &[usize], faces: &mut [holonics::hnn::tower::TowerFace]| {
        let mut ring = [0i64; 5];
        for (t, face) in faces.iter_mut().enumerate() {
            let table = if t < x.len() { &letters } else { &stops };
            for (r, &(_, _, _, modulus)) in RINGS.iter().enumerate() {
                ring_tilt_face(face, &table[r][ring[r].rem_euclid(modulus) as usize]);
            }
            if let Some(&c) = x.get(t) {
                for (v, d) in ring.iter_mut().zip(&marks[c]) {
                    *v += d;
                }
            }
        }
    })
}

/// [measurement; theory, November 10 04:40] **The brackets' and quotes' closure** of written answers: for `(` `)` and `[` `]` the
/// pairs matched by a stack, near (the closer within `NEAR − 1` places of its opener) and far, the openers left and the strays,
/// and the answers closed; for the backtick and the quotes, the answers with an even count. Numbers only.
fn ring_closure(codec: &FieldCodec, state: &str, answers: &[Vec<usize>]) {
    let near_reach = holonics::hnn::tower::field::NEAR - 1;
    let texts: Vec<Vec<u8>> = answers.iter().map(|x| codec.decode(x)).collect();
    for (ring, open, close) in [("paren", b'(', b')'), ("bracket", b'[', b']')] {
        let (mut near, mut far, mut left, mut strays, mut closed) = (0usize, 0usize, 0usize, 0usize, 0usize);
        for bytes in &texts {
            let (mut stack, mut stray) = (Vec::new(), 0usize);
            for (i, &b) in bytes.iter().enumerate() {
                if b == open {
                    stack.push(i);
                } else if b == close {
                    match stack.pop() {
                        Some(j) if i - j <= near_reach => near += 1,
                        Some(_) => far += 1,
                        None => stray += 1,
                    }
                }
            }
            (left, strays, closed) = (left + stack.len(), strays + stray, closed + usize::from(stack.is_empty() && stray == 0));
        }
        println!("FIELD_RING_CLOSURE state={state} ring={ring} pairs_near={near} pairs_far={far} unmatched_open={left} unmatched_close={strays} closed_answers={closed} answers={}", texts.len());
    }
    for (ring, mark) in [("backtick", b'`'), ("dquote", b'"'), ("squote", b'\'')] {
        let even = texts.iter().filter(|bytes| bytes.iter().filter(|&&b| b == mark).count() % 2 == 0).count();
        println!("FIELD_RING_CLOSURE state={state} ring={ring} even_answers={even} answers={}", texts.len());
    }
}

/// [definition; theory, November 10 04:15] `redraw-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD HELD_SHA COUNT
/// START START_SHA H_MILLINATS PASSES OUT`: **point re-draws at the highest surprise, alternating with exchanges**
/// ([`Field::redraw`]) from a written start (`START`, a `SAMPLE.tsv`: the settle's rest) of the first `COUNT` held problems,
/// each cut to its room, at most `PASSES` passes (a bound by count). `SAMPLE.pass<k>.tsv` the answers at every pass (`k` 0 the
/// start), `SAMPLE.tsv` the end, all private; `MOVES.tsv` each kept change's places, letters, bare gain and attributed fall.
/// `FIELD_REDRAW_PASS` a pass (flushed): its kind (re-draw or exchange), the pooled code, the faces' summed entropy and the
/// root charge in nats, its kept and undone changes, the shares of places with `v` above one and two nats, and the letters'
/// distance from the start: `tv` (half the summed `|N(a) − N₀(a)|` over the letters, a share of them) and `planes` (each bit
/// plane's `|n_b − n₀_b|`, the bytes with bit `b` set, a share of the bytes); `FIELD_REDRAW` a problem at the end: its code at the
/// start and the end, its entropy and root at the end, a place, and how it stopped (neutral, rest, or the bound).
///
/// [definition; theory, November 10 04:40] `redraw-ring-field` takes `RING RING_SHA RING_STOP RING_STOP_SHA FLOOR` before `OUT`:
/// **the ring tilts in the certificate** ([`Field::redraw_lensed`]): every face the walk reads is tilted by the spread ring
/// census's tables ([`ring_tilts`]), each place's by `RING.tsv` at the ring residues of its answer's letters before it and the stop
/// place's (coded at the void) by `RING_STOP.tsv` at the whole answer's, `f′ ∝ f · Π_rings N/F` ([`ring_tilt_face`]); and the
/// brackets' and quotes' closure is printed for the start and the end ([`ring_closure`]).
pub(super) fn redraw_field(args: &[String], realization: &mut dyn FieldRealization) -> Result<()> {
    let ringed = args.first().is_some_and(|a| a == "redraw-ring-field");
    if args.len() != if ringed { 20 } else { 15 } {
        return Err(if ringed { "redraw-ring-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD HELD_SHA COUNT START START_SHA H_MILLINATS PASSES RING RING_SHA RING_STOP RING_STOP_SHA FLOOR OUT" } else { "redraw-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD HELD_SHA COUNT START START_SHA H_MILLINATS PASSES OUT" }.into());
    }
    let started = std::time::Instant::now();
    let mut learner = FieldLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    declared_clocks(&mut learner.field);
    let field = &learner.field;
    let units = units_of(&args[5], &args[6])?;
    let codec = FieldCodec::from_text(std::str::from_utf8(&pinned_read(&args[3], &args[4], CODEC_BUDGET)?)?, units)?;
    let held = problems_of(&pinned_read(&args[7], &args[8], READ_BUDGET as usize)?);
    let limit = count(&args[9])?;
    let (h_milli, passes) = (count(&args[12])?, count(&args[13])?);
    let out = Path::new(&args[if ringed { 19 } else { 14 }]);
    std::fs::create_dir(out)?;
    let held = &held[..limit.min(held.len())];
    let requests: Vec<(Vec<usize>, usize)> = held.iter().map(|(question, _)| opening(&codec, field, question, b"")).collect::<std::result::Result<_, String>>()?;
    let problems: Vec<(&[usize], usize)> = requests.iter().map(|(q, n)| (q.as_slice(), *n)).collect();
    let void = codec.void();
    let lens: Option<RingLens> = if ringed {
        let a = field.declaration.alphabet;
        let floor = count(&args[18])? as u64;
        let letters = ring_tilts(&pinned_read(&args[14], &args[15], READ_BUDGET as usize)?, a, floor)?;
        let stops = ring_tilts(&pinned_read(&args[16], &args[17], READ_BUDGET as usize)?, a, floor)?;
        let kept = |t: &RingTilts| t.iter().flatten().flatten().filter(|c| c.is_some()).count();
        println!("FIELD_RING_TILTS floor={floor} letter_cells={} stop_cells={}", kept(&letters), kept(&stops));
        Some(ring_lens(&codec, a, letters, stops))
    } else {
        None
    };
    let mut start = written_answers(&codec, &args[10], &args[11], held.len())?;
    for (x, &(_, room)) in start.iter_mut().zip(&problems) {
        x.truncate(room);
    }
    let write = |name: &str, answers: &[Vec<usize>]| -> Result<()> {
        let mut file = rows_file(&out.join(name), "")?;
        for (k, places) in answers.iter().enumerate() {
            let written = places.iter().take_while(|&&c| c != void).count();
            row(&mut file, &format!("{k}\t{}\n", escaped(&codec.decode(&places[..written])))).map_err(|e| e.to_string())?;
        }
        Ok(())
    };
    // The letters' distance from the start: TV over the letters, and each bit plane over the bytes.
    let a = field.declaration.alphabet;
    let bytes: Vec<Vec<u8>> = (0..a).map(|c| codec.decode(&[c])).collect();
    let tally = |answers: &[Vec<usize>]| -> (Vec<i64>, [i64; 8], i64) {
        let (mut n, mut planes, mut total) = (vec![0i64; a], [0i64; 8], 0i64);
        for x in answers {
            for &c in x.iter().take_while(|&&c| c != void) {
                n[c] += 1;
                for &byte in &bytes[c] {
                    total += 1;
                    for (b, plane) in planes.iter_mut().enumerate() {
                        *plane += i64::from(byte >> b & 1);
                    }
                }
            }
        }
        (n, planes, total)
    };
    let (n0, planes0, _) = tally(&start);
    let letters: i64 = n0.iter().sum();
    let millionths = |num: i64, den: i64| if den == 0 { "-".to_string() } else { format!("{}.{:06}", num * 1_000_000 / den / 1_000_000, num * 1_000_000 / den % 1_000_000) };
    let h = (((h_milli as i128) << 50) + 1000 * LN2_Q30 - 1) / (1000 * LN2_Q30);
    let mut saved: Result<()> = Ok(());
    let mut shown = |p: &holonics::hnn::tower::field::SettlePass| -> bool {
            let (n, planes, total) = tally(p.answers);
            let tv: i64 = n.iter().zip(&n0).map(|(x, y)| (x - y).abs()).sum::<i64>();
            let plane: Vec<String> = planes.iter().zip(&planes0).map(|(x, y)| millionths((x - y).abs(), total)).collect();
            let kind = if p.pass == 0 { "start" } else if p.kind == 1 { "redraw" } else { "exchange" };
            println!(
                "FIELD_REDRAW_PASS pass={} kind={kind} elapsed_ms={} active={} kept={} undone={} c_nats={} entropy_nats={} root_nats={} v_over_1_share={} v_over_2_share={} tv={} planes={}",
                p.pass,
                started.elapsed().as_millis(),
                p.active,
                p.kept,
                p.undone,
                decimal_q20(nats_q20(p.code)),
                decimal_q20(nats_q20(p.entropy)),
                decimal_q20(nats_q20(p.root)),
                millionths(p.over as i64, p.places as i64),
                millionths(p.over2 as i64, p.places as i64),
                millionths(tv, 2 * letters),
                plane.join(",")
            );
            let _ = std::io::Write::flush(&mut std::io::stdout());
            if let Err(e) = write(&format!("SAMPLE.pass{}.tsv", p.pass), p.answers) {
                saved = Err(e);
                return false;
            }
            p.pass < passes
        };
    let (settled, records) = match lens.as_deref() {
        Some(lens) => field.redraw_lensed(&problems, &start, void, h, lens, realization, &mut shown),
        None => field.redraw(&problems, &start, void, h, realization, &mut shown),
    }
    .map_err(|e| e.to_string())?;
    saved?;
    write("SAMPLE.tsv", &settled)?;
    if ringed {
        ring_closure(&codec, "start", &start);
        ring_closure(&codec, "end", &settled);
    }
    let mut file = rows_file(&out.join("MOVES.tsv"), "problem\tmove\tplaces\tproposed_gain_nats\tattributed_fall_nats\n")?;
    let (mut neutral, mut rested, mut kept, mut undone, mut places, mut start_code, mut end_code, mut entropy, mut root) = (0usize, 0usize, 0usize, 0usize, 0usize, 0i128, 0i128, 0i128, 0i128);
    for (k, r) in records.iter().enumerate() {
        for (n, m) in r.kept.iter().enumerate() {
            let at: Vec<String> = m.at.iter().map(|&(t, from, to)| format!("{t}:{from}>{to}")).collect();
            row(&mut file, &format!("{k}\t{}\t{}\t{}\t{}\n", n + 1, at.join(","), decimal_q20(nats_q20(m.gain)), decimal_q20(nats_q20(m.fall))))?;
        }
        let a_place = |c: i128| if r.places == 0 { "-".to_string() } else { decimal_q20(nats_q20(c) / r.places as i128) };
        let stop = if r.neutral { "neutral" } else if r.rested { "rest" } else { "bound" };
        println!("FIELD_REDRAW problem={k} letters={} code_start_nats_a_place={} code_end_nats_a_place={} entropy_end_nats_a_place={} root_end_nats={} kept={} undone={} stop={stop}", r.places, a_place(r.start), a_place(r.end), a_place(r.entropy), decimal_q20(nats_q20(r.root)), r.kept.len(), r.undone);
        (neutral, rested, kept, undone, places) = (neutral + usize::from(r.neutral), rested + usize::from(r.rested && !r.neutral), kept + r.kept.len(), undone + r.undone, places + r.places);
        (start_code, end_code, entropy, root) = (start_code + r.start, end_code + r.end, entropy + r.entropy, root + r.root);
    }
    let pooled = |c: i128| if places == 0 { "-".to_string() } else { decimal_q20(nats_q20(c) / places as i128) };
    println!("FIELD_REDRAW_DONE problems={} neutral={neutral} rested={rested} h_millinats={h_milli} passes_bound={passes} kept={kept} undone={undone} letters={places} code_start_nats_a_place={} code_end_nats_a_place={} entropy_end_nats_a_place={} root_end_nats={} ms={}", problems.len(), pooled(start_code), pooled(end_code), pooled(entropy), decimal_q20(nats_q20(root)), started.elapsed().as_millis());
    Ok(())
}

/// [definition; theory, November 9 21:43] `lens-field CENSUS CENSUS_SHA DEPTH` followed by `length-field`'s arguments: **the
/// writer through a census lens** ([`Lensed`]): every face it draws from is lensed at its site's plate by `CENSUS`'s table at
/// `DEPTH` (an input file, never a switch); its reads, files and heat as `length-field`'s.
pub(super) fn lens_field(args: &[String], realization: &mut dyn FieldRealization) -> Result<()> {
    if args.len() < 4 {
        return Err("lens-field CENSUS CENSUS_SHA DEPTH STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD HELD_SHA COUNT SWEEPS REFINE STOP_MS OUT".into());
    }
    let text = pinned_read(&args[1], &args[2], STATE_BUDGET)?;
    let depth = positive(&args[3])? as u32;
    let table = census_table(std::str::from_utf8(&text)?, depth)?;
    println!("FIELD_LENS depth={depth} plates={}", table.len());
    let rest: Vec<String> = std::iter::once(args[0].clone()).chain(args[4..].iter().cloned()).collect();
    let mut lensed = Lensed { inner: realization, table: &table, depth };
    length_field(&rest, &mut lensed)
}

/// [measurement; theory, November 9 19:05] `FIELD_HEAT`: the refine walk's Landauer heat ([`PassDrive::heat`]), one line a
/// refine pass (its heat summed over the problems, in nats and on 2^(−20) bits, and its changed places), then each problem's
/// running total over its passes. A reading only.
fn heat_lines(drives: &[Vec<holonics::hnn::tower::field::PassDrive>]) {
    let passes = drives.iter().map(Vec::len).max().unwrap_or(0);
    for p in 0..passes {
        let (heat, changed, redrawn) = drives.iter().filter_map(|d| d.get(p)).fold((0i128, 0usize, 0usize), |(h, c, r), d| (h + d.heat, c + d.changes, r + d.redrawn));
        println!("FIELD_HEAT pass={} heat_nats={} heat_bits_q20={heat} changed={changed} redrawn={redrawn}", p + 1, decimal_q20(nats_q20(heat)));
    }
    for (k, d) in drives.iter().enumerate() {
        let (heat, changed) = d.iter().fold((0i128, 0usize), |(h, c), p| (h + p.heat, c + p.changes));
        println!("FIELD_HEAT_TOTAL problem={k} passes={} heat_nats={} heat_bits_q20={heat} changed={changed}", d.len(), decimal_q20(nats_q20(heat)));
    }
}
