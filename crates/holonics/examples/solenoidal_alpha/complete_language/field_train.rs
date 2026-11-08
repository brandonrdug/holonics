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
    for chunk in states.chunks(64) {
        let views: Vec<Region> = chunk.iter().map(|(_, _, _, c, u)| Region { classes: c, unresolved: u, faces: &[], locked: &[], echo: &[], domain: None, port: None }).collect();
        let faces = realization.read_faces(field, &views).map_err(|e| e.to_string())?;
        for ((i, is_foil, (size, k), c, _), faces) in chunk.iter().zip(faces) {
            let q_len = c.len() - problems[*i].1.len() - 1;
            let terms = if *is_foil { &mut foil[*i] } else { &mut own[*i] };
            for (t, face) in faces.iter().enumerate() {
                if let Some(face) = face {
                    let x = face.code(c[t]) as i128 * *size as i128;
                    let k = *k as i128;
                    terms[t - q_len] += (if x >= 0 { (x + k / 2) / k } else { -((-x + k / 2) / k) }) as i64;
                }
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
    let mut pass_rows = rows_file(&out.join("PASSES.tsv"), "problem\tpass\tredrawn\tcode\tstanding\tentropy\tdrive\tvarentropy\tchanges\tequilibrium\n")?;
    for ((k, pass), (redrawn, code)) in &passes {
        let d = drives.get(*k).and_then(|d| d.get(pass - 1)).copied().unwrap_or_default();
        row(&mut pass_rows, &format!("{k}\t{pass}\t{redrawn}\t{code}\t{}\t{}\t{}\t{}\t{}\t{}\n", d.standing, d.entropy, d.drive(), d.varentropy, d.changes, d.equilibrium))?;
    }
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
/// `STOP_MS`; past `STOP_MS` the run writes `STATE.stopped` and stops. Writes `STATE.<lap>` and `ENUMERATED.tsv` (private: held
/// answers' letters).
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
    // [the unified-theory reading of November 7, 09:36] `FIELD_CONTRAST_PERSISTENT`: the section deposits against persistent
    // writes (lap 13's law) instead of a kernel step from the truth.
    let persistent = std::env::var_os("FIELD_CONTRAST_PERSISTENT").is_some();
    let conditional = std::env::var_os("FIELD_CONTRAST_CONDITIONAL").is_some();
    // [measurement; theory, November 8 11:10] `FIELD_CONTRAST_READ_ONLY`: each section is read and its learner put back as it
    // opened, so every section's code is read at the opening state and nothing is deposited (the family split's reads).
    let read_only = std::env::var_os("FIELD_CONTRAST_READ_ONLY").is_some();
    // [measurement; theory, November 8 11:35] `FIELD_SECTION_LETTERS`: each section's trained places counted by their true
    // letter, printed, and the section skipped (no read, no deposit), so the walk's letter counts cost no field time.
    let section_letters = std::env::var_os("FIELD_SECTION_LETTERS").is_some();
    // [definition; the unified-theory reading of November 7, 21:58] `FIELD_CONTRAST_AVERAGE`: the averaged constitution moves
    // each section (`FieldLearner::average_section`) and every held read reads it; the live field keeps stepping.
    let averaging = std::env::var_os("FIELD_CONTRAST_AVERAGE").is_some();
    let coherence_every: usize = match std::env::var("FIELD_COHERENCE_EVERY") {
        Ok(v) => v.parse().map_err(|_| "FIELD_COHERENCE_EVERY is a section count".to_string())?,
        Err(_) => 0,
    };
    learner.coin_measure = std::env::var_os("FIELD_COIN_MEASURE").is_some();
    // [definition; theory, November 8, the number record's N5] `FIELD_CARRIED_RELEASE`: each deposit is formed on 2^(−24) of its
    // grain and its remainder carried to the next (`FieldLearner::carried`); a state that carries a `carried` line keeps its
    // remainders, and one without opens them at zero.
    if std::env::var_os("FIELD_CARRIED_RELEASE").is_some() && learner.carried.is_none() {
        learner.carried = Some(vec![0; learner.field.material_len()]);
    }
    // [definition; theory, November 8 05:50] `FIELD_UNIGRAM`: the bias reads its own ratio (`FieldLearner::unigram`); a state
    // that carries a `unigram` line keeps its counts, and one without opens them at zero.
    if std::env::var_os("FIELD_UNIGRAM").is_some() && learner.unigram.is_none() {
        learner.unigram = Some(vec![0; learner.field.declaration.alphabet]);
    }
    // [definition; the unified-theory reading of November 7, 23:34] `FIELD_WIDEN=CAP`: the width law at its share (a state that
    // carries a `widen` line keeps its own share where this is unset).
    if let Ok(v) = std::env::var("FIELD_WIDEN") {
        learner.field.widen = Some(v.parse().map_err(|_| "FIELD_WIDEN is the classes' share".to_string())?);
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
    let from_section: usize = match std::env::var("FIELD_CONTRAST_FROM_SECTION") {
        Ok(v) => v.parse().map_err(|_| "FIELD_CONTRAST_FROM_SECTION is a section count".to_string())?,
        Err(_) => 0,
    };
    let mut persistent_writes: Vec<Vec<usize>> = Vec::new();
    let mut persistent_etas: std::collections::VecDeque<i128> = std::collections::VecDeque::new();
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
    // [the unified-theory reading of November 7, 05:55] The kernel steps by the evidence-shrunk Newton step along the moments'
    // direction; `FIELD_CONTRAST_MOMENTS` keeps laps 4 and 5's law (the moments' own step), a declared comparison.
    // [the unified-theory reading of November 7, 06:26] Retired as the step (lap 6 ran away as its curvature fell): the kernel
    // steps by the moments; `FIELD_CONTRAST_NEWTON` takes the evidence-shrunk Newton step again, a declared comparison, and its
    // terms are read beside the moments' step either way.
    let kernel = writer.is_none() && joint.is_none();
    learner.newton = kernel && std::env::var_os("FIELD_CONTRAST_NEWTON").is_some();
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
            // [the unified-theory reading of November 7, 09:55] Against persistent writes the letters' temperature is held: at
            // writes not relaxed at the current `T` its covector falls toward zero as `T` grows wherever the writes sit below their
            // truths (lap 13 ran `log₂ T` from 9.7 to 24.2 bits in 150 sections until a read refused its carrier).
            learner.temper_learns = !persistent && std::env::var_os("FIELD_CONTRAST_HOLD_T").is_none();
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
    let near = holonics::hnn::tower::field::NEAR;
    // [definition; theory, November 7 22:08] `FIELD_CONTRAST_SEED=HEX`: a read keyed by a declared seed, so laws read from
    // different states pair section by section; laps keep the state-keyed walk.
    let seed = match std::env::var("FIELD_CONTRAST_SEED") {
        Ok(v) => u64::from_str_radix(&v, 16).map_err(|_| "FIELD_CONTRAST_SEED is hexadecimal")?,
        Err(_) => u64::from_str_radix(args[2].get(..16).ok_or("a state's hash of fewer than sixteen hex digits")?, 16).map_err(|_| "a state's hash that is not hexadecimal")?,
    };
    let law = WriterLaw::from_env()?;
    // Each problem's question, its answer cut to the room, and the room (`Problems`' third place).
    let encode = |problems: &[(Vec<u8>, Vec<u8>)], field: &Field| -> Result<Problems> {
        let mut set = Vec::with_capacity(problems.len());
        for (question, answer) in problems {
            let (q, room) = opening(&codec, field, question, b"")?;
            let mut a = codec.encode(answer)?;
            a.truncate(room);
            if !a.is_empty() {
                set.push((q, a, room));
            }
        }
        Ok(set)
    };
    let train_set = encode(&train_text, &learner.field)?;
    let held_set = encode(&held_text, &learner.field)?;
    let (sections, _) = sections_of(&train_set, section, 0, seed);
    let truth_of = |(q, a, room): &(Vec<usize>, Vec<usize>, usize), letters: &[usize]| -> Vec<usize> {
        let mut t: Vec<usize> = q.iter().chain(letters).copied().collect();
        t.extend(std::iter::repeat_n(void, near.min(room - a.len())));
        t
    };
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
        "FIELD_CONTRAST_DECLARATION alphabet={} width={} heads={} modes={} ticks={} reach={} rate={} log2_t={} section={section} sections={} train={} held={} places={places} release={} newton={} moments={},{} run_bits={} rest={} spans={} laps_read={}",
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
        learner.newton,
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
    match &host_held {
        Some(h) => h.read(-1, &learner),
        None => enumerated_read(&held_field(&learner, averaging), &held_set, places, &truth_of, realization, -1, &mut enumerated_rows)?,
    }
    println!("FIELD_ENUMERATED_READ lap=-1 ms={}", started.elapsed().as_millis());
    // [definition; Brandon, November 6 17:11; theory, November 7 16:56] A card run holds at most one hour between saved states:
    // at the first section start an hour (`SAVE_MS`) past the last saved state, the learner rests as `STATE.<lap>.<sections
    // done>`, the held places are read from it (`ENUMERATED.tsv` rows marked `10000·(lap + 1) + sections done`) and the run
    // goes on.
    const SAVE_MS: u128 = 3_600_000;
    let mut saved_ms = started.elapsed().as_millis();
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
            if n > 0 && n == from_section && lap == 0 {
                println!("FIELD_RESUMED lap={lap} sections={n}/{} ms={now}", sections.len());
            }
            if n > 0 && now - saved_ms >= SAVE_MS {
                write_new(&out.join(format!("STATE.{lap}.{n}")), at_rate(&learner, base_rate).as_bytes())?;
                match &host_held {
                    Some(h) => h.read(10_000 * (lap as i64 + 1) + n as i64, &learner),
                    None => enumerated_read(&held_field(&learner, averaging), &held_set, places, &truth_of, realization, 10_000 * (lap as i64 + 1) + n as i64, &mut enumerated_rows)?,
                }
                saved_ms = started.elapsed().as_millis();
                println!("FIELD_SAVED lap={lap} sections={n}/{} ms={now} read_ms={}", sections.len(), saved_ms - now);
                leg.print(&learner.field, lap, n, "leg");
                leg = Leg::new(&learner.field);
            }
            let section_start = std::time::Instant::now();
            let members = &sections[s];
            let truths: Vec<Vec<usize>> = members.iter().map(|&i| truth_of(&train_set[i], &train_set[i].1)).collect();
            if persistent {
                // [definition; the unified-theory reading of November 7, 09:36] **The field meets its persistent writes**: one
                // write a problem slot, started once from the joint release and never restarted; each section, write `j` takes the
                // section's `j`-th question at its true length (cut, or its new places drawn once from their open faces), the
                // energy's own sweep moves one residue class of its places at the energy's `T`, and the section deposits
                // `(1/T) Σ_j [∂G/∂θ(truth_j) − ∂G/∂θ(write_j)]` ([`FieldLearner::section_contrast`]): the loss is the closing read
                // `(G(write) − G(truth))/T`, which rests at the answers' likelihood given their questions.
                let problems: Vec<(&[usize], usize)> = members.iter().map(|&i| (train_set[i].0.as_slice(), train_set[i].2)).collect();
                let lengths: Vec<usize> = members.iter().map(|&i| train_set[i].1.len()).collect();
                let key = mix(seed ^ 0x9E85_15 << 40, read << 32 | n as u64);
                // [the unified-theory reading of November 7, 09:55] Each write is released once at the longest answer's length and
                // carried whole: a question takes its first `L` places, and the rest wait unread and unmoved for a longer question.
                let fresh = persistent_writes.is_empty();
                if fresh {
                    let longest = train_set.iter().map(|p| p.1.len()).max().unwrap_or(1);
                    let wide: Vec<usize> = vec![longest; problems.len()];
                    persistent_writes = learner.field.energy_release(&problems, &wide, void, 64, key, realization, &mut |_, _, _| {}).map_err(|e| e.to_string())?;
                }
                let m = members.len().min(persistent_writes.len());
                let mut active: Vec<Vec<usize>> = (0..m).map(|j| persistent_writes[j][..lengths[j].min(persistent_writes[j].len())].to_vec()).collect();
                // [the unified-theory reading of November 7, 10:12] The writes sunk before the first deposit: eight whole sweeps at
                // `T` over each write's first `L` places.
                if fresh {
                    for sweep in 0..8u64 {
                        let t0 = std::time::Instant::now();
                        let (mv, pr, en) = learner.field.energy_sweep_at(&problems[..m], &mut active, None, void, 0, mix(key, 100 + sweep), realization, &mut |_, _| {}).map_err(|e| e.to_string())?;
                        println!("FIELD_PERSISTENT_SINK sweep={} moved={mv} proposed={pr} accept_milli={} write_energy_milli={} ms={}", sweep + 1, mv * 1000 / pr.max(1), (en.iter().sum::<i128>() / m.max(1) as i128) * 1000 >> 32, t0.elapsed().as_millis());
                    }
                }
                // The sweep over one residue class of each write's first `L` places.
                let positions: Vec<Vec<usize>> = (0..m)
                    .map(|j| {
                        let len = active[j].len();
                        let r = (mix(seed ^ 0xB10C << 44, read << 40 | (n as u64) << 16 | j as u64) as usize) % spacing.min(len);
                        (r..len).step_by(spacing).collect()
                    })
                    .collect();
                let (moved_w, proposed_w, write_energy) = learner
                    .field
                    .energy_sweep_at(&problems[..m], &mut active, Some(&positions), void, 0, mix(key, 7), realization, &mut |_, _| {})
                    .map_err(|e| e.to_string())?;
                for j in 0..m {
                    let len = active[j].len();
                    persistent_writes[j][..len].copy_from_slice(&active[j]);
                }
                let write_energy_milli = (write_energy.iter().sum::<i128>() / m.max(1) as i128) * 1000 >> 32;
                let release_ms = section_start.elapsed().as_millis();
                let near = holonics::hnn::tower::field::NEAR;
                let writes_now: Vec<Vec<usize>> = (0..m)
                    .map(|j| {
                        let (q, room) = problems[j];
                        let w = &active[j];
                        let mut c: Vec<usize> = q.iter().chain(w).copied().collect();
                        c.extend(std::iter::repeat_n(void, near.min(room - w.len())));
                        c
                    })
                    .collect();
                let resolved: Vec<Vec<bool>> = truths.iter().map(|t| vec![false; t.len()]).collect();
                let truth_views: Vec<Region> = truths[..m].iter().zip(&resolved).map(|(c, u)| Region { classes: c, unresolved: u, faces: &[], locked: &[], echo: &[], domain: None, port: None }).collect();
                let write_views: Vec<Region> = writes_now.iter().zip(&resolved).map(|(c, u)| Region { classes: c, unresolved: u, faces: &[], locked: &[], echo: &[], domain: None, port: None }).collect();
                let deposit_start = std::time::Instant::now();
                let (receipt, eta) = learner.section_contrast_scaled(&truth_views, &write_views, &mut persistent_etas, realization).map_err(|e| e.to_string())?;
                let deposit_ms = deposit_start.elapsed().as_millis();
                let eta_milli = eta * 1000 >> 32;
                let places: i128 = lengths[..m].iter().map(|&l| l as i128).sum::<i128>().max(1);
                // The closing read `(G(write) − G(truth))/T` a place in thousandths of a nat (`gap` is `Σ (G(truth) − G(write))/T` on 2^(−32) bits).
                let closing_milli = -(receipt.gap * LN2_Q30 >> 30) * 1000 / places >> 32;
                (states, deposited) = (states + receipt.states, deposited + usize::from(receipt.deposited));
                (gap, same) = (gap + receipt.gap, same + receipt.same);
                (moved_lap, places_lap) = (moved_lap + moved_w, places_lap + proposed_w);
                let micro = |v: Option<i64>| v.map_or("-".to_string(), |c| ((c as i128 * 1_000_000) / ((receipt.states as i128) << 20)).to_string());
                println!(
                    "FIELD_PERSISTENT lap={lap} n={n} writes={m} closing_milli={closing_milli} write_energy_milli={write_energy_milli} eta_milli={eta_milli} moved={moved_w} proposed={proposed_w} accept_milli={} deposited={} predicted_micro={} transfer_micro={} log2_t={} sweep_ms={release_ms} deposit_ms={deposit_ms} ms={}",
                    moved_w * 1000 / proposed_w.max(1),
                    receipt.deposited,
                    micro(receipt.predicted),
                    micro(receipt.transfer),
                    learner.field.theta[learner.field.layout().face_temper],
                    started.elapsed().as_millis()
                );
                if started.elapsed().as_millis() > stop_ms {
                    write_new(&out.join("STATE.stopped"), at_rate(&learner, base_rate).as_bytes())?;
                    println!("FIELD_STOPPED lap={lap} sections={}/{} states={states} ms={}", n + 1, sections.len(), started.elapsed().as_millis());
                    return Ok(());
                }
                continue;
            }
            if writer.is_none() && joint.is_none() {
                // The kernel: each state's answer places `t ≡ r (mod s)`, cut into blocks of at most `k*` places, each block its own
                // kernel step from the truth ([the unified-theory reading of November 7, 07:24]: a block of `k` places moves
                // `k·2Φ(−σ√k/2)` places, most at `σ²k ≈ 5.7`); `FIELD_CONTRAST_WHOLE_BLOCKS` keeps one block a state (laps 4 to 9).
                // [definition; the unified-theory reading of November 7, 08:13] Two lengths a section, `k₊ = ⌈k*·2^¼⌉` and
                // `k₋ = max(1, ⌊k*·2^(−¼)⌋)`, each residue class cut into blocks alternating them (`k₊` first on even sections,
                // `k₋` on odd); a closing block shorter than its length runs but is not read.
                let (k_up, k_down) = if pinned_blocks || whole_blocks {
                    (block_places.max(1), block_places.max(1))
                } else {
                    let up = (1..=1usize << 13).find(|&k| log2_q16(k as u64) as i128 >= log2_k_star + (1 << 14)).unwrap_or(1 << 13);
                    let down = (1..=1usize << 13).rev().find(|&k| log2_q16(k as u64) as i128 <= log2_k_star - (1 << 14)).unwrap_or(1).max(1);
                    (up, down)
                };
                let mut blocks: Vec<Vec<usize>> = Vec::new();
                let mut owners: Vec<usize> = Vec::new();
                // Each block's length class (`Some(true)` k₊, `Some(false)` k₋) where it is whole, `None` where it closes short.
                let mut classes_of: Vec<Option<bool>> = Vec::new();
                for (m, &i) in members.iter().enumerate() {
                    let (q, a, _) = &train_set[i];
                    let r = (mix(seed ^ 0xB10C << 44, read << 40 | (n as u64) << 16 | m as u64) as usize) % spacing.min(a.len());
                    let residue: Vec<usize> = (r..a.len()).step_by(spacing).map(|j| q.len() + j).collect();
                    if whole_blocks {
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
                if section_letters {
                    let mut count = std::collections::BTreeMap::<usize, usize>::new();
                    for (b, &o) in blocks.iter().zip(&owners) {
                        for &t in b {
                            *count.entry(truths[o][t]).or_default() += 1;
                        }
                    }
                    let places: usize = count.values().sum();
                    let text: Vec<String> = count.iter().map(|(&c, &k)| format!("{}:{k}", if c < 256 { escaped(&[c as u8]) } else { format!("#{c}") })).collect();
                    println!("FIELD_SECTION_LETTERS lap={lap} n={n} places={places} {}", text.join(" "));
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
                    *slot = (slot.0 + t.unwrap_or(0) as i128, slot.1 + p.unwrap_or(0) as i128);
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
                {
                    let names = family_names(&learner.field);
                    let text: Vec<String> = learner
                        .field
                        .families_all()
                        .iter()
                        .filter(|fam| fam.1 > 0)
                        .filter_map(|&(start, len, _)| {
                            let total: i128 = (start..start + len).map(|i| (learner.field.theta[i] as i128 - theta_before[i] as i128).abs()).sum();
                            (total > 0).then(|| format!("{}={}/{len}", names.iter().find(|&&(_, at)| at == start).map_or("?", |&(n, _)| n), total))
                        })
                        .collect();
                    println!("FIELD_STEP lap={lap} n={n} {}", text.join(" "));
                }
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
                        *slot = (slot.0 + t.unwrap_or(0) as i128, slot.1 + p.unwrap_or(0) as i128);
                    }
                    let tenth = (n + 1) * 10 / sections.len();
                    if tenth > tenths_printed && n + 1 < sections.len() {
                        // [measurement; theory, November 7 19:50] The held places read at each tenth, beside the tenth's acceptance and
                        // the sections' coherence (rows marked `10000·(lap + 1) + sections done`).
                        match &host_held {
                            // The host's crossings carry the tenths.
                            Some(_) => {}
                            None => enumerated_read(&held_field(&learner, averaging), &held_set, places, &truth_of, realization, 10_000 * (lap as i64 + 1) + (n + 1) as i64, &mut enumerated_rows)?,
                        }
                    }
                    if tenth > tenths_printed || n + 1 == sections.len() {
                        tenths_printed = tenth;
                        println!("FIELD_KERNEL_TENTH lap={lap} tenth={tenth} log2_t={} {}", learner.field.theta[learner.field.layout().face_temper], rates_text(&learner.field, &receipt.rates, &tenth_family));
                        tenth_family.iter_mut().for_each(|x| *x = (0, 0));
                    }
                }
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
            if started.elapsed().as_millis() > stop_ms {
                write_new(&out.join("STATE.stopped"), at_rate(&learner, base_rate).as_bytes())?;
                println!("FIELD_STOPPED lap={lap} sections={}/{} states={states} ms={}", n + 1, sections.len(), started.elapsed().as_millis());
                return Ok(());
            }
        }
        learner.laps += 1;
        write_new(&out.join(format!("STATE.{lap}")), at_rate(&learner, base_rate).as_bytes())?;
        if persistent {
            println!("FIELD_PERSISTENT_LAP lap={lap} states={states} moved={moved_lap} proposed={places_lap} accept_milli={} closing_milli={} ms={}", moved_lap * 1000 / places_lap.max(1), if states == 0 { 0 } else { -(gap * LN2_Q30 >> 30) * 1000 / (states as i128) >> 32 }, started.elapsed().as_millis());
        }
        if states > 0 && writer.is_none() && joint.is_none() && !persistent {
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
        match &host_held {
            Some(h) => h.read(lap as i64, &learner),
            None => enumerated_read(&held_field(&learner, averaging), &held_set, places, &truth_of, realization, lap as i64, &mut enumerated_rows)?,
        }
        println!("FIELD_ENUMERATED_READ lap={lap} ms={}", started.elapsed().as_millis());
    }
    Ok(())
}

/// [measurement; November 7, lap 7] Each family's transfer and predicted change over a lap, named by the layout, in
/// micro-bits a state: `name=transfer/predicted`.
fn family_text(field: &Field, sums: &[(i128, i128)], states: usize) -> String {
    let names = family_names(field);
    field
        .families_all()
        .iter()
        .zip(sums)
        .filter(|(fam, _)| fam.1 > 0)
        .map(|(&(start, _, _), &(t, p))| {
            let name = names.iter().find(|&&(_, at)| at == start).map_or("?", |&(n, _)| n);
            let micro = |v: i128| v * 1_000_000 / ((states.max(1) as i128) << 20);
            format!("{name}={}/{}", micro(t), micro(p))
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
    truth_p: i128,
    places: usize,
    steps: Vec<i128>,
    sections: usize,
}

impl Leg {
    fn new(field: &Field) -> Self {
        Self { coherence: Coherence::new(field), letters: Vec::new(), bands: Vec::new(), kl: 0, truth_p: 0, places: 0, steps: vec![0; field.families_all().len()], sections: 0 }
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

fn enumerated_places(held: &Problems, places: usize, truth_of: &dyn Fn(&(Vec<usize>, Vec<usize>, usize), &[usize]) -> Vec<usize>) -> HeldPlaces {
    held.iter()
        .take(places)
        .enumerate()
        .map(|(k, p)| {
            let t = p.0.len() + (mix(ENUMERATED_KEY, k as u64) as usize) % p.1.len();
            (k, truth_of(p, &p.1), t, p.0.len())
        })
        .collect()
}

/// [`enumerated_read`]'s rows at `chosen` (each line `lap`-marked), read through `realization`.
fn enumerated_rows(field: &Field, chosen: &HeldPlaces, realization: &mut dyn FieldRealization, lap: i64) -> Result<Vec<String>> {
    let alphabet = field.declaration.alphabet;
    let chosen: Vec<(usize, &Vec<usize>, usize, usize)> = chosen.iter().map(|(k, truth, t, q)| (*k, truth, *t, *q)).collect();
    if chosen.is_empty() {
        return Ok(Vec::new());
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
    let energies = realization.read_energies(field, &asked).map_err(|e| e.to_string())?;
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
    Ok(lines)
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
