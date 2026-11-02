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
use holonics::hnn::tower::field::{shares, Echo, Field, FieldDeclaration, FieldLearner, FieldNext, FieldRealization, FieldReceipt, HeldRows, HostField, Region, Released, ReleaseSweep, Shares, NEAR, PUMP_TOP};
use holonics::hnn::tower::TowerFace;
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

    /// [agent-inferred, November 1] A released answer's bytes, each open site written as `open`
    /// (the release never forces an open site into a class), each site's first byte offset beside
    /// it.
    pub(super) fn decode_open(&self, sites: &[Option<usize>], open: &[u8]) -> (Vec<u8>, Vec<usize>) {
        let (mut out, mut at) = (Vec::new(), Vec::with_capacity(sites.len()));
        for site in sites {
            at.push(out.len());
            match site {
                Some(c) if *c < self.void() => out.extend_from_slice(self.units.piece(self.used[*c] as usize)),
                Some(_) => break,
                None => out.extend_from_slice(open),
            }
        }
        (out, at)
    }

    /// Whether a class's unit is all digits (an exterior read: the held-out code is split by it).
    pub(super) fn is_digit(&self, class: usize) -> bool {
        class < self.void() && self.units.piece(self.used[class] as usize).iter().all(u8::is_ascii_digit)
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

/// The problems of a passage: `question \n answer` blocks separated by a blank line.
pub(super) fn problems_of(text: &[u8]) -> Vec<(Vec<u8>, Vec<u8>)> {
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

/// A region's shape: a keyed completion mask over the whole region, or a front region ([`Front`],
/// [`front_faces`], [`section_regions`]).
pub(super) enum Shape {
    Masked(Vec<bool>),
    Front(Front),
}

/// [agent-inferred, November 2] The key of a held read's front (`draw | 7·2^59`, §16.4).
const HELD_FRONT_KEY: u64 = 7 << 59;

/// [agent-inferred, November 1] The key of a front region's front `f` (`draw | 2^62`).
const FRONT_KEY: u64 = 1 << 62;

/// [agent-inferred, November 1] The key of a front region's rung `r` (`draw | 3·2^61`).
const RUNG_KEY: u64 = 3 << 61;

/// [agent-inferred, November 1] The key of the site a front region opens when its keyed subset is
/// empty (`draw | 5·2^60`). Why three keys of their own: the masks read `mix(seed, draw)`, the
/// sites' draws at `draw ^ ((t + 1) << 32)`, the forced site at `draw + 1`, and the tail's octave and
/// length at `draw | 2^63` and `draw | 3·2^62`; a training draw is below `2^40`, so none of these
/// counters meets another, and a front's draws leave the masks' and the tails' untouched.
const FORCE_KEY: u64 = 5 << 60;

/// The pump's rungs, `β = 2^r` for `r` from 0 to `log₂` [`PUMP_TOP`]: 23 of them.
const RUNGS: u64 = PUMP_TOP.trailing_zeros() as u64 + 1;

/// The sites a release reads past its front: its near field less the front's own site
/// ([`NEAR`] `− 1 = 5`), the band a front region opens.
const BAND: usize = NEAR - 1;

/// [definition; agent-inferred, November 1] **A front region's draws** (the dispersing field's §14.6):
/// the region of a release whose front stands at `front` (the place of the first site no lock has yet
/// reached) with a rung `rung` of the pump, cut where the release's own sweep ends, `BAND` sites past
/// the front (`cut`, at most the region's length). `open` is read 1's unresolved sites over `[0, cut)`:
/// a keyed subset of the answer's sites before the front, the band `[front, cut)`, and nothing else
/// (the question is known).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Front {
    pub front: usize,
    pub rung: u32,
    pub cut: usize,
    pub open: Vec<bool>,
}

/// [agent-inferred, November 1] A region's shape: with even odds the whole region's sites, each
/// unresolved with probability `τ` (`τ` uniform on `(0, 1]` on `2^(−16)`, at least one site
/// unresolved), or a front region. A front region of a training answer of `answer` sites (the answer's
/// classes and its one true void, `A`) is drawn as the dispersing field's §14.6 leaves it open:
/// - **The front** `f` is uniform on `[0, A]`, `A + 1` places counted from the question's last site, so
///   the front stands before the first answer site, between any two, beyond the true void (the band
///   then reads the void tail) and at the void. Why inclusive: the release's front reaches any of these
///   places, and a front that could not stand at the end would leave the void's own place unlearned.
/// - **The rung** `r` is uniform on the pump's 23 rungs (`0` to `log₂ PUMP_TOP`), counted from
///   [`PUMP_TOP`] and not written again, so the rungs the pump can reach are all met alike.
/// - **The prefix's open sites** are the masks' own: the answer's sites before the front whose keyed
///   draw falls below `τ`, the draw and the density the masked shape of the same `draw` reads, so
///   that a front region opens where a mask would have, at the masks' density. The question is never
///   open: a release's question is known.
/// - **The band** is the five sites from the front on, open on the unresolved row, and the region is
///   cut at its end or at the region's length.
/// - **An empty region is refused as the masks refuse it**: when no site is open (an empty band,
///   `f = A` with a one-site tail, and no prefix site drawn), one keyed prefix site is opened.
///
/// Why the front regions replace the second sweep (§14.6): the second sweep was the first state a
/// release met after its opening, every answer site open, a state no release meets once the front
/// moves; a front region is the release's state at any sweep of its advance, and the masks remain for
/// the completion that the field also learns.
pub(super) fn shape(seed: u64, draw: u64, question: usize, sites: usize, answer: usize) -> Shape {
    let head = mix(seed, draw);
    let low = (head >> 1) & 0xFFFF;
    let tau = low + 1;
    let mut out: Vec<bool> = (0..sites).map(|t| (mix(seed, draw ^ ((t as u64 + 1) << 32)) & 0xFFFF) < tau).collect();
    if head & 1 == 1 {
        if !out.iter().any(|&u| u) {
            out[mix(seed, draw.wrapping_add(1)) as usize % sites] = true;
        }
        return Shape::Masked(out);
    }
    let front = question + (mix(seed, draw | FRONT_KEY) % (answer as u64 + 1)) as usize;
    let rung = (mix(seed, draw | RUNG_KEY) % RUNGS) as u32;
    let cut = (front + BAND).min(sites);
    let mut open: Vec<bool> = (0..cut).map(|t| t >= question && (t >= front || out[t])).collect();
    if !open.iter().any(|&u| u) {
        open[question + mix(seed, draw | FORCE_KEY) as usize % (cut - question)] = true;
    }
    Shape::Front(Front { front, rung, cut, open })
}

/// Whether a face's top class outweighs every other together (`2 m_top > Σ m`): the release's
/// majority, at which a site locks.
fn majority(face: &TowerFace) -> bool {
    face.masses.iter().max().is_some_and(|&m| m.checked_mul(2).is_some_and(|twice| twice > face.total))
}

/// [definition; agent-inferred, November 1] **Read 2 of a front region** (the dispersing field's
/// §14.6): from read 1's logits (`logits`, every open site's, read through the realization), each
/// open site carries its read-1 face as the release carries it, as shares ([`shares`]) of
/// [`Field::tempered`]:
/// - the prefix's open sites (before the front) at `β = 2^r`, the rung's pump, **locked** where that
///   tempered face resolves a majority (`2 m_top > Σ m`, the release's own rule), so a locked site is
///   definite and radiates past the near field (§14.1);
/// - the band at `β = 1`, soft and never locked, heard in the near field only.
///
/// The faces are tempered over every class, the void's among them: the extent is read at the front,
/// so a training region has not read it, and a release carries every class at a reached site until
/// its extent is read ([`Field::content_face`] is the release's after). The mixtures are data with no
/// covector through them; read 2's covector reaches the encodings through them as every carried
/// mixture's does. Why the logits and not the faces (§14.6): the pump is a temperature over the
/// logits, which are exact on `2^(−16)` bits, while a face keeps its masses on `2^(−62)` with the
/// small ones released, so a face sharpened at a rung of `2^22` would sharpen what the first rounding
/// kept; the release tempers its logits alike. Returns the carried faces and the locks, one a site of
/// `[0, cut)`.
pub(super) fn front_faces(field: &Field, front: &Front, logits: &[Option<Vec<i64>>]) -> Result<(Vec<Option<Shares>>, Vec<bool>)> {
    let mut faces: Vec<Option<Shares>> = vec![None; front.cut];
    let mut locked = vec![false; front.cut];
    for t in (0..front.cut).filter(|&t| front.open[t]) {
        let z = logits.get(t).and_then(Option::as_ref).ok_or("a front region's first read has no face at an open site")?;
        let prefix = t < front.front;
        let face = field.tempered(z, if prefix { 1u64 << front.rung } else { 1 });
        locked[t] = prefix && majority(&face);
        faces[t] = Some(shares(&face));
    }
    Ok((faces, locked))
}

/// [agent-inferred, November 1] A region's void tail past its answer, in `[1, room]`, `room` the
/// codec's answer extent less the answer's: an octave `k` of the room drawn uniform, then a length
/// uniform in `[2^k, min(2^(k+1) − 1, room)]`. Every octave of tail is met alike, so the field
/// meets the long void regions of a release's first sweeps and the short ones of its last; on the
/// GSM8K training passage this reads 1.86 times the sites² of a one-void tail (a uniform length
/// would read 3.42 times).
pub(super) fn tail(seed: u64, draw: u64, room: usize) -> usize {
    let room = room.max(1);
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
/// [`section_regions`] counts it): a masked member's one region, a front member's two (read 1 and
/// read 2, each cut at the front's band).
pub(super) fn region_lengths(codec: &FieldCodec, problems: &Problems, members: &[usize], seed: u64, draw: &mut u64) -> Vec<usize> {
    members
        .iter()
        .flat_map(|&i| {
            let (q, a, _) = &problems[i];
            *draw += 1;
            let length = q.len() + a.len() + tail(seed, *draw, codec.answer - a.len());
            match shape(seed, *draw, q.len(), length, a.len() + 1) {
                Shape::Masked(_) => vec![length],
                Shape::Front(front) => vec![front.cut; 2],
            }
        })
        .collect()
}

/// A training region: its classes, its unresolved sites, its carried faces and its locks (each
/// empty where none).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct TrainRegion {
    pub classes: Vec<usize>,
    pub unresolved: Vec<bool>,
    pub faces: Vec<Option<Shares>>,
    pub locked: Vec<bool>,
    /// Each site's clock (§15.4) and each carried site's echo (§15.3), empty where none.
    pub clock: Vec<u32>,
    pub echo: Vec<Option<Echo>>,
}

impl TrainRegion {
    /// A region carrying no face and no lock.
    pub(super) fn plain(classes: Vec<usize>, unresolved: Vec<bool>) -> Self {
        Self { classes, unresolved, faces: Vec::new(), locked: Vec::new(), clock: Vec::new(), echo: Vec::new() }
    }
}

/// [agent-inferred, November 1] **The clock ring sets a declaration founds** (§15.4): one, the last head's
/// set, where at least two turned sets stay on the strand's place (the helix and its moments keep two
/// rings sets of place; with fewer the clock would take the place the helix reads). A run that reads
/// the release's clock declares a head for it.
pub(super) fn clocks_of(heads: usize, still: usize) -> usize {
    usize::from(heads.saturating_sub(still) >= 3)
}

/// A region as the field reads it.
fn view_of(region: &TrainRegion) -> Region<'_> {
    Region { classes: &region.classes, unresolved: &region.unresolved, faces: &region.faces, locked: &region.locked, clock: &region.clock, echo: &region.echo }
}

/// The regions as the field reads them.
pub(super) fn views_of(regions: &[TrainRegion]) -> Vec<Region<'_>> {
    regions.iter().map(view_of).collect()
}

/// **A section's regions as `train-field` forms them**: each member's classes (its question, its
/// answer and a keyed void tail) and its shape ([`shape`]). A masked member is one region. A front
/// member is two, both compared (the dispersing field's §14.6): **read 1**, the question known, the
/// answer's sites before the front open on the unresolved row where the keyed subset falls and the
/// truth elsewhere, the band open, the region cut at the band's end; and **read 2**, the same region
/// with each open site carrying its read-1 face at its rung, the prefix's locked where it resolves a
/// majority ([`front_faces`]). The step the learner holds is read first, on every region of read 1 and
/// of the masks (the regions as training compares them, which the step was not fit on), so read 2's
/// mixtures are read from the material that stands after it (one more read of the front regions'
/// read 1, through `realization`); the held step's read is returned. Why that order (the build's
/// review, November 1): read under the stepped material before its read, a refused step left read 2
/// carrying mixtures of a material that no longer stood, and the step was read on regions it had
/// partly formed. Why every region of read 1 and not the release's opening (the crib probe of
/// November 1, §13 cause 1): read on the release's opening, every answer site on the unresolved row, a
/// state training never compares, 205 of 248 held steps were refused in the second lap while the
/// withheld problems' code stood still at 4.55 bits. [agent-inferred] Why read 1 beside the masks and
/// not read 2: read 2's mixtures do not exist until the step is read, and read 1 is the state they
/// are read from.
pub(super) fn section_regions(codec: &FieldCodec, problems: &Problems, members: &[usize], seed: u64, draw: &mut u64, learner: &mut FieldLearner, realization: &mut dyn FieldRealization) -> Result<(Vec<TrainRegion>, Option<FieldNext>)> {
    let mut firsts: Vec<TrainRegion> = Vec::with_capacity(members.len());
    let mut fronts: Vec<Option<(Front, usize)>> = Vec::with_capacity(members.len());
    let mut held_fronts: Vec<TrainRegion> = Vec::with_capacity(members.len());
    for &i in members {
        let (q, a, _) = &problems[i];
        *draw += 1;
        let length = q.len() + a.len() + tail(seed, *draw, codec.answer - a.len());
        // [agent-inferred, November 2] The held read meets the admitted future (§15.11, §16.4): each problem
        // also as the release reads it, the question and the answer before a keyed front definite and every
        // site from the front through the answer's first void open, one front a problem keyed by its draw.
        // Read for the held step only, never fit. Why not the context parts (one answer site in four open,
        // the November 2 choice): an open site ticks by the face it carries (§16.2), so a digit clock reads a
        // part's earlier open digits as stopped and its clock is off by their count, while at the release's
        // front every earlier site is definite.
        let front = (mix(seed, *draw | HELD_FRONT_KEY) % (a.len() as u64 + 1)) as usize;
        let mut cc: Vec<usize> = q.iter().chain(a).copied().collect();
        cc.push(codec.void());
        let cu: Vec<bool> = (0..cc.len()).map(|t| t >= q.len() + front).collect();
        held_fronts.push(TrainRegion::plain(cc, cu));
        let mut classes = region_classes(codec, q, a, length);
        match shape(seed, *draw, q.len(), length, a.len() + 1) {
            Shape::Masked(mask) => {
                firsts.push(TrainRegion::plain(classes, mask));
                fronts.push(None);
            }
            Shape::Front(front) => {
                classes.truncate(front.cut);
                firsts.push(TrainRegion::plain(classes, front.open.clone()));
                fronts.push(Some((front, q.len())));
            }
        }
    }
    let next = if learner.holds_step() {
        // [measurement; agent-inferred, November 2] With `FIELD_HELD_KINDS`, the held step is also read on each kind of
        // region alone, on clones (the training-shaped and the front-shaped), so a refusal is read by the kind that
        // refused it (`FIELD_HELD_KINDS change=…/…`); the step that stands is the joint read's, as without it.
        if std::env::var_os("FIELD_HELD_KINDS").is_some() {
            let mut by = |regions: &[TrainRegion]| -> Result<String> {
                let mut probe = learner.clone();
                Ok(probe.read_step_on(&views_of(regions), realization).map_err(|e| e.to_string())?.1.map_or("-".to_string(), |n| format!("{}/{}/{}", n.change, n.halvings, n.refused)))
            };
            println!("FIELD_HELD_KINDS training={} fronts={}", by(&firsts)?, by(&held_fronts)?);
        }
        let held: Vec<TrainRegion> = firsts.iter().cloned().chain(held_fronts).collect();
        learner.read_step_on(&views_of(&held), realization).map_err(|e| e.to_string())?.1
    } else {
        None
    };
    let at: Vec<usize> = (0..firsts.len()).filter(|&k| fronts[k].is_some()).collect();
    let mut logits = if at.is_empty() {
        Vec::new()
    } else {
        let views: Vec<Region> = at.iter().map(|&k| view_of(&firsts[k])).collect();
        realization.read_logits(&learner.field, &views).map_err(|e| e.to_string())?
    }
    .into_iter();
    let mut regions = Vec::with_capacity(firsts.len() + at.len());
    for (first, front) in firsts.into_iter().zip(fronts) {
        let Some((front, question)) = front else {
            regions.push(first);
            continue;
        };
        let read = logits.next().ok_or("a front region's first read was not returned")?;
        let (faces, locked) = front_faces(&learner.field, &front, &read.logits)?;
        // [agent-inferred, November 1] Read 2's clock (§15.4, the rung supplying the count): the prefix's
        // sites at the rung `r`, the question one sweep before them at `r + 1`, the band and past it at
        // zero (just reached, or unreached). Its echoes (§15.3): each carried site's read-1 logits and
        // the echo read 1 returned there, so read 2 meets its cavity field as the release does.
        let clock: Vec<u32> = (0..front.cut).map(|t| if t < question { front.rung + 1 } else if t < front.front { front.rung } else { 0 }).collect();
        let echo: Vec<Option<Echo>> = (0..front.cut).map(|t| faces[t].as_ref().and(read.logits.get(t).cloned().flatten()).map(|z| Echo { b: read.echo[t], logits: z })).collect();
        let second = TrainRegion { classes: first.classes.clone(), unresolved: first.unresolved.clone(), faces, locked, clock, echo };
        regions.push(first);
        regions.push(second);
    }
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

/// The first draw of the withheld problems' regions, the same every lap (apart from every
/// training draw, a lap's count times the passage's).
pub(super) const UNSEEN_DRAW: u64 = 1 << 61;

/// The held-out read: at the release's own opening (the region the question and the codec's
/// answer extent, every answer site unresolved at once), with each site's neighbours resolved
/// ([`context_regions`], the region the question, the answer and its first void), and the same
/// beside another problem's question (the foil, [`held_regions`]), the field's code over the
/// answer's classes and its first void (its digits' and its text's apart), on `2^(−20)` bits,
/// beside each one's count: `[opening, opening digits, opening text, context, context digits,
/// context text, foil, foil digits, foil text]`. A reading only: no decision of the run reads it.
fn held_out(field: &Field, codec: &FieldCodec, problems: &Problems, realization: &mut dyn FieldRealization) -> Result<[(i64, usize); 9]> {
    let regions = held_regions(codec, problems);
    let views: Vec<Region> = regions.iter().map(|(c, u, _)| Region { classes: c, unresolved: u, faces: &[], locked: &[], clock: &[], echo: &[] }).collect();
    let mut out = [(0i64, 0usize); 9];
    for (chunk, parts) in views.chunks(64).zip(regions.chunks(64)) {
        let faces = realization.read_faces(field, chunk).map_err(|e| e.to_string())?;
        for ((region, faces), &(_, _, base)) in chunk.iter().zip(faces).zip(parts) {
            // The opening read counts the answer's sites through its first void.
            let end = if base == 0 { region.classes.iter().enumerate().skip_while(|&(t, _)| !region.unresolved[t]).find(|&(_, &c)| c == codec.void()).map_or(region.classes.len(), |(t, _)| t + 1) } else { region.classes.len() };
            for (face, &class) in faces.iter().zip(region.classes).take(end) {
                if let Some(face) = face {
                    let code = face.code(class);
                    out[base].0 += code;
                    out[base].1 += 1;
                    let part = base + if codec.is_digit(class) { 1 } else { 2 };
                    out[part].0 += code;
                    out[part].1 += 1;
                }
            }
        }
    }
    Ok(out)
}

/// [measurement; agent-inferred, November 2] **The held answer sites' rows by where their mass lies**
/// ([`FieldRealization::read_row_shares`]), read on the held read's context regions (each problem's
/// [`CONTEXT`] parts, base 3 of [`held_regions`], the answer starting at the question's end): for each head and
/// tick, over the unresolved answer sites, the millionths of a row's mass on the question group (definite
/// sites before the answer), on the soft near field (the near sources that are not definite) and on the rest,
/// and the current's part from the question group per row (on the value's grain). A reading only: nothing in
/// the run reads it.
fn held_rows_text(field: &Field, codec: &FieldCodec, problems: &Problems, realization: &mut dyn FieldRealization, lap: i64) -> Result<()> {
    let started = std::time::Instant::now();
    let regions = held_regions(codec, problems);
    let n = problems.len();
    let views: Vec<Region> = regions.iter().skip(n).take(n * CONTEXT).map(|(c, u, _)| Region { classes: c, unresolved: u, faces: &[], locked: &[], clock: &[], echo: &[] }).collect();
    let questions: Vec<usize> = problems.iter().flat_map(|(q, _, _)| std::iter::repeat_n(q.len(), CONTEXT)).collect();
    let d = field.declaration;
    let mut total = vec![HeldRows::default(); d.ticks * d.heads];
    for (chunk, asks) in views.chunks(64).zip(questions.chunks(64)) {
        for (acc, one) in total.iter_mut().zip(realization.read_row_shares(field, chunk, asks).map_err(|e| e.to_string())?) {
            acc.rows += one.rows;
            acc.question += one.question;
            acc.soft_near += one.soft_near;
            acc.other += one.other;
            acc.question_current += one.question_current;
        }
    }
    let share = |v: u128, rows: u64| (v * 1_000_000 >> 63) / rows.max(1) as u128;
    println!("FIELD_ROWS_HELD_READ lap={lap} regions={} ms={}", views.len(), started.elapsed().as_millis());
    for tick in 0..d.ticks {
        for head in 0..d.heads {
            let r = total[tick * d.heads + head];
            println!(
                "FIELD_ROWS_HELD lap={lap} head={head} tick={tick} rows={} question_share={} soft_near_share={} other_share={} question_current={}",
                r.rows,
                share(r.question, r.rows),
                share(r.soft_near, r.rows),
                share(r.other, r.rows),
                r.question_current / r.rows.max(1) as i128
            );
        }
    }
    Ok(())
}

/// [measurement; agent-inferred, November 2] **The closure against the face** (§19): a section's covector with
/// the closure's comparison and without it ([`FieldRealization::read_and_return_open`]) on the same material, the
/// closure's part their difference; `dot = ⟨face, closure⟩`, `face_norm = ⟨face, face⟩`, `closure_norm =
/// ⟨closure, closure⟩`, exact integer sums. One extra return of the lap's first section, read only.
fn covectors_text(field: &Field, views: &[Region], realization: &mut dyn FieldRealization, lap: u64) -> Result<()> {
    use num_bigint::BigInt;
    let started = std::time::Instant::now();
    let (_, full) = realization.read_and_return(field, views).map_err(|e| e.to_string())?;
    let (_, face) = realization.read_and_return_open(field, views).map_err(|e| e.to_string())?;
    let closure: Vec<i128> = full.iter().zip(&face).map(|(a, b)| a - b).collect();
    let dot = |a: &[i128], b: &[i128]| a.iter().zip(b).fold(BigInt::from(0), |s, (&x, &y)| s + BigInt::from(x) * BigInt::from(y));
    let (nf, nc, no) = (face.iter().filter(|&&x| x != 0).count(), closure.iter().filter(|&&x| x != 0).count(), face.iter().zip(&closure).filter(|(a, b)| **a != 0 && **b != 0).count());
    println!("FIELD_COVECTORS_COUNTS lap={lap} entries={} face_nonzero={nf} closure_nonzero={nc} overlap={no}", face.len());
    println!("FIELD_COVECTORS lap={lap} dot={} face_norm={} closure_norm={} ms={}", dot(&face, &closure), dot(&face, &face), dot(&closure, &closure), started.elapsed().as_millis());
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
/// parts read with their neighbours (base 3), and the same parts beside the next problem's
/// question (base 6; the last problem beside the first's).
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
    regions.extend(problems.iter().flat_map(|(q, a, _)| context_regions(codec.void(), q, a, q.len() + a.len() + 1).into_iter().map(|(c, u)| (c, u, 3))));
    let n = problems.len();
    regions.extend((0..n).flat_map(|i| {
        let ((_, a, _), (q, _, _)) = (&problems[i], &problems[(i + 1) % n]);
        context_regions(codec.void(), q, a, q.len() + a.len() + 1).into_iter().map(|(c, u)| (c, u, 6))
    }));
    regions
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
    let views: Vec<Region> = regions.iter().map(|(c, u)| Region { classes: c, unresolved: u, faces: &[], locked: &[], clock: &[], echo: &[] }).collect();
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
/// (millionths): `[opening, opening digits, opening text, context, context digits, context text,
/// foil, foil digits, foil text]`, each a code over its sites ([`held_out`]), and the question's
/// effect, the foil's rate less the context's (signed), beside the context's. Why six decimals
/// (reading 9): the held answer coded 5.629 bits a byte beside its own question and 5.629 beside a
/// foil's, equal at the printed thousandth, so a question effect below a thousandth of a bit could
/// not be seen; the effect is the difference of the two rates and is printed as such, not left to
/// the reader's subtraction of two rounded numbers. One formatter for every `FIELD_HELD` line.
fn held_text(held: &[(i64, usize); 9]) -> String {
    let rate = |k: usize| micro_bits(held[k].0 as i128, held[k].1 as i128);
    let effect = |foil: usize, context: usize| match (held[foil], held[context]) {
        ((_, 0), _) | (_, (_, 0)) => "-".to_string(),
        ((a, na), (b, nb)) => micro_bits(a as i128 * nb as i128 - b as i128 * na as i128, na as i128 * nb as i128),
    };
    format!(
        "answer={} digits={} text={} classes={} context={} context_digits={} context_text={} context_classes={} foil={} foil_digits={} foil_text={} question={} question_digits={} question_text={}",
        rate(0),
        rate(1),
        rate(2),
        held[0].1,
        rate(3),
        rate(4),
        rate(5),
        held[3].1,
        rate(6),
        rate(7),
        rate(8),
        effect(6, 3),
        effect(7, 4),
        effect(8, 5)
    )
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
            let declaration = FieldDeclaration { alphabet: codec.alphabet(), width, heads, modes, still, contacts, ticks, frames: heads, reach, clocks: clocks_of(heads, still) };
            FieldLearner::new(Field::found(declaration, &keys).map_err(|e| e.to_string())?, rate)
        }
    };
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
    let held = held_out(&learner.field, &codec, &dev_set, realization)?;
    println!("FIELD_HELD lap=-1 {} ms={}", held_text(&held), started.elapsed().as_millis());
    held_rows_text(&learner.field, &codec, &dev_set, realization, -1)?;
    let founding_gaps = pace_text(&learner.field, &codec, &dev_set, -1)?;
    // The withheld problems' code after the lap before (at the opening, before any lap).
    let (code, sites, next) = unseen_read(&mut learner, &codec, &train_set, &unseen, seed, realization)?;
    println!("FIELD_UNSEEN lap=-1 code={} sites={sites} {} ms={}", bits(code, sites), next_text(next), started.elapsed().as_millis());
    let mut previous = (code, sites);
    let mut grown = false;
    let mut fallen = false;
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
        let (mut code_before, mut code_after, mut sites, mut deposited, mut halvings, mut held_down, mut refused) = (0i64, 0i64, 0usize, 0usize, 0u64, 0usize, 0usize);
        let lap_start = std::time::Instant::now();
        for (n, &s) in walk(seed, read, sections.len()).iter().enumerate() {
            let section_start = std::time::Instant::now();
            let (regions, next) = section_regions(&codec, &train_set, &sections[s], seed, &mut draw, &mut learner, realization)?;
            let length = regions.iter().map(|r| r.classes.len()).max().unwrap_or(0);
            let views = views_of(&regions);
            if n == 0 {
                covectors_text(&learner.field, &views, realization, lap as u64)?;
            }
            let receipt = learner.section_realized(&views, realization).map_err(|e| e.to_string())?;
            let receipt = FieldReceipt { next: next.or(receipt.next), ..receipt };
            code_before += receipt.code_before;
            code_after += receipt.code_after;
            sites += receipt.sites;
            deposited += usize::from(receipt.deposited);
            halvings += receipt.halvings as u64;
            if let Some(next) = receipt.next {
                held_down += usize::from(next.halvings > 0 && !next.refused);
                refused += usize::from(next.refused);
            }
            println!(
                "FIELD_SECTION lap={lap} n={n} sites={} before={} after={} halvings={} deposited={} {} length={length} ms={}",
                receipt.sites,
                bits(receipt.code_before, receipt.sites),
                bits(receipt.code_after, receipt.sites),
                receipt.halvings,
                receipt.deposited,
                next_text(receipt.next),
                section_start.elapsed().as_millis()
            );
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
                    bits(code_after, sites),
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
        write_new(&out.join(format!("STATE.{lap}")), learner.to_text().as_bytes())?;
        println!(
            "FIELD_LAP lap={lap} read={} sites={sites} before={} after={} deposited={deposited}/{} halvings={halvings} next_halved={held_down} next_refused={refused} ms={}",
            learner.laps,
            bits(code_before, sites),
            bits(code_after, sites),
            sections.len(),
            lap_start.elapsed().as_millis()
        );
        println!("FIELD_UNSEEN lap={lap} code={} sites={unseen_sites} {} ms={}", bits(code, unseen_sites), next_text(next), started.elapsed().as_millis());
        let held = held_out(&learner.field, &codec, &dev_set, realization)?;
        println!("FIELD_HELD lap={lap} {} ms={}", held_text(&held), started.elapsed().as_millis());
        held_rows_text(&learner.field, &codec, &dev_set, realization, lap as i64)?;
        let gaps = pace_text(&learner.field, &codec, &dev_set, lap as i64)?;
        // [agent-inferred, November 2; fixed with the run's declaration] **The early stop** (§16): after nine laps, a run
        // whose paced heads' clocks have not moved toward a digit clock (no head's gap `κ̄ at digits − κ̄ inside words`
        // above its founding's) and whose held question effect is at or below the foil's stops, and is reported
        // incomplete with its clocks by lap. Why: the founding's route to the clock was weak and could not say why
        // (§16.10); nine laps that move neither the clock nor the question's effect read the obstacle.
        let effect = (held[6].0 as i128 * held[3].1 as i128) - (held[3].0 as i128 * held[6].1 as i128);
        if lap + 1 >= EARLY_STOP_LAPS && !gaps.iter().any(|&(h, g)| founding_gaps.iter().any(|&(fh, fg)| fh == h && g > fg)) && effect <= 0 {
            println!("FIELD_STOPPED_EARLY lap={lap} reason=no clock moved toward a digit clock and the question tells the answer no more than the foil ms={}", started.elapsed().as_millis());
            break;
        }
        if std::env::var_os("FIELD_PEAKS_EACH_LAP").is_some() {
            peaks_text(&learner.field, &codec, &dev_set, realization, &lap.to_string())?;
        }
        // [agent-inferred, November 1] The width is the trained body's (growth by copies, the
        // tower's law): when a lap leaves the withheld problems coding no fewer bits a site than
        // the lap before left them, the body has spent its width and grows by two before the next.
        // [agent-inferred, November 2] Only once the withheld code has fallen at this width: a lap
        // that raises it from where the width began has not spent the width but harmed it, and
        // growing then copies the harm (the crib run of November 2 grew at lap 0 after its first lap
        // raised the code from 5.459 to 5.912 bits, and its grown body refused 240 of 248 steps).
        let fell = (code as i128) * (previous.1 as i128) < (previous.0 as i128) * (unseen_sites as i128);
        fallen |= fell;
        match growth(fell, fallen, grown, lap, laps) {
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

/// The laps after which the early stop reads the clocks and the question's effect (§16).
const EARLY_STOP_LAPS: usize = 9;

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

/// The bytes a release writes, escaped as `card_written.py` writes them.
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

/// An answer's calculations as `card_written.py` reads them: each `<<expression=` with the offset
/// just past its `=`.
fn calculations_of(answer: &[u8]) -> Vec<(&[u8], usize)> {
    let mut found = Vec::new();
    let mut i = 0usize;
    while i + 1 < answer.len() {
        if &answer[i..i + 2] == b"<<" {
            let close = answer[i + 2..].windows(2).position(|w| w == b">>").map_or(answer.len(), |c| i + 2 + c);
            if let Some(eq) = answer[i + 2..close].iter().position(|&b| b == b'=') {
                found.push((&answer[i + 2..i + 2 + eq], i + 2 + eq + 1));
            }
            i = close;
        } else {
            i += 1;
        }
    }
    found
}

/// [definition; agent-inferred, November 1] **The coupling read** (the micro-control record's
/// §7): the release `H` and the held answer `T` are two strands on their own clocks, read at the
/// codec's class face. `λ` is the longest order-keeping coupling of equal classes and
/// `F* = |H| + |T| − 2λ` the cells that slip; a contact lies on some least-friction coupling
/// exactly when `P(i−1, j−1) + 1 + S(i+1, j+1) = λ`, and a maximal run of such contacts at one lag
/// `j − i` is a plateau. Exchanging the strands leaves `λ`, `F*` and the plateaus unchanged. An
/// exterior read: nothing of it enters the field.
struct Coupling {
    lambda: usize,
    friction: usize,
    plateaus: Vec<(usize, i64)>,
}

fn coupling(h: &[usize], t: &[usize]) -> Coupling {
    let (n, m) = (h.len(), t.len());
    // P(i, j): the coupling of H[..i] and T[..j]; S(i, j): of H[i..] and T[j..].
    let mut p = vec![0usize; (n + 1) * (m + 1)];
    for i in 1..=n {
        for j in 1..=m {
            p[i * (m + 1) + j] = if h[i - 1] == t[j - 1] { p[(i - 1) * (m + 1) + j - 1] + 1 } else { p[(i - 1) * (m + 1) + j].max(p[i * (m + 1) + j - 1]) };
        }
    }
    let mut s = vec![0usize; (n + 1) * (m + 1)];
    for i in (0..n).rev() {
        for j in (0..m).rev() {
            s[i * (m + 1) + j] = if h[i] == t[j] { s[(i + 1) * (m + 1) + j + 1] + 1 } else { s[(i + 1) * (m + 1) + j].max(s[i * (m + 1) + j + 1]) };
        }
    }
    let lambda = p[n * (m + 1) + m];
    let locked = |i: usize, j: usize| h[i] == t[j] && p[i * (m + 1) + j] + 1 + s[(i + 1) * (m + 1) + j + 1] == lambda;
    let mut plateaus = Vec::new();
    for i in 0..n {
        for j in 0..m {
            if locked(i, j) && !(i > 0 && j > 0 && locked(i - 1, j - 1)) {
                let mut run = 1;
                while i + run < n && j + run < m && locked(i + run, j + run) {
                    run += 1;
                }
                plateaus.push((run, j as i64 - i as i64));
            }
        }
    }
    Coupling { lambda, friction: n + m - 2 * lambda, plateaus }
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

/// `release-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD HELD_SHA COUNT SWEEPS STOP_MS
/// OUT`: for each of the first `COUNT` held problems the field releases the answer from the question
/// alone (the codec's answer sites, refined over at most `SWEEPS` sweeps) and, at each of its
/// calculations, the continuation past the answer written through that calculation's `=`. The free
/// releases are refined first and the marks after them, each sweep only while the command is inside
/// `STOP_MS` ([`within`], a line a sweep with the sites reached and the front): a set stopped there is
/// returned as released and counted open. Each free release's receipt (`FIELD_RELEASE_ONE_RECEIPT`) and
/// the free set's (`FIELD_RELEASE_RECEIPTS`) carry the front's counts (the dispersing field's §14.9):
/// the sites reached and locked, the least, quartiles and most of the sweeps they were reached and
/// locked, each lock's own rung, and the extent's reading ([`extent_text`]). It writes
/// `OUT/FREE.tsv` and `OUT/MARKS.tsv` as `card_written.py convert` writes them for
/// `written_rules.py` (a calculation's release is cut after its first `>>`), and `OUT/COUPLING.tsv`,
/// each free release's coupling read against the held answer at the class face. The free releases
/// are read together, a sweep of every problem in one read, then the marks together; each set's
/// rows are written when it ends, with one line of progress a problem. A problem the field cannot
/// read (a unit the codec never met, a region past the reach) is written empty and counted, never
/// skipped. The marks are written for the bytes alone: a founded-units codec would cut a
/// calculation inside its units (the October 27 review's located cause), so its marks are withheld
/// and counted.
pub(super) fn release(args: &[String], realization: &mut dyn FieldRealization) -> Result<()> {
    if args.len() != 13 {
        return Err("release-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD HELD_SHA COUNT SWEEPS STOP_MS OUT".into());
    }
    let started = std::time::Instant::now();
    let learner = FieldLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let units = units_of(&args[5], &args[6])?;
    let bytes = units.merges().is_empty();
    let codec = FieldCodec::from_text(std::str::from_utf8(&pinned_read(&args[3], &args[4], CODEC_BUDGET)?)?, units)?;
    let held = problems_of(&pinned_read(&args[7], &args[8], READ_BUDGET as usize)?);
    let (limit, sweeps, stop_ms) = (count(&args[9])?, positive(&args[10])?, positive(&args[11])? as u128);
    let out = Path::new(&args[12]);
    std::fs::create_dir(out)?;
    let field = &learner.field;
    let held = &held[..limit.min(held.len())];
    // The free releases: each question alone, the codec's answer sites open.
    let free_requests: Vec<std::result::Result<(Vec<usize>, usize), String>> = held.iter().map(|(question, _)| opening(&codec, field, question, b"")).collect();
    let mut free_last = ReleaseSweep::default();
    let free = release_requests(field, &free_requests, sweeps, codec.void(), realization, &mut within("free", started, stop_ms, &mut free_last))?;
    let mut free_file = rows_file(&out.join("FREE.tsv"), "")?;
    let mut couplings = rows_file(&out.join("COUPLING.tsv"), "problem\treleased\theld\tlambda\tfriction\tplateaus\tlongest\tlag\n")?;
    let mut landmarks_file = rows_file(&out.join("LANDMARKS.tsv"), "problem\tsite\tbyte\tlandmark\tlandmark_byte\tshare\n")?;
    let (mut sum_h, mut sum_t, mut sum_lambda, mut sum_friction, mut refused, mut withheld) = (0usize, 0usize, 0usize, 0usize, 0usize, 0usize);
    let (mut open_sites, mut free_circulation, mut bound, mut locked_whole) = (0usize, 0usize, 0usize, 0usize);
    let mut margins: Vec<i64> = Vec::new();
    // [agent-inferred, November 1] The front's receipts over the free releases (§14.9), count only:
    // the sites reached and locked, the sweep each was reached and each locked, and the extent's
    // reading (its site and sweep, and whether the front reached the bound with no void locked).
    let mut front_receipt = FrontReceipt::default();
    let mut rungs: std::collections::BTreeMap<u64, usize> = std::collections::BTreeMap::new();
    let mut landmark = LandmarkCount::default();
    let mut read_ok = vec![false; held.len()];
    for (i, (((_, answer), released), request)) in held.iter().zip(&free).zip(&free_requests).enumerate() {
        let (h, text) = match released {
            Ok(r) => {
                read_ok[i] = true;
                open_sites += r.open;
                free_circulation += r.free;
                bound += r.bound;
                margins.extend(r.counters.iter().flatten().map(|&(_, margin)| margin));
                front_receipt.add(r);
                locked_whole += usize::from(r.open == 0);
                for &rung in r.rungs.iter().filter(|&&b| b > 0) {
                    *rungs.entry(rung).or_insert(0) += 1;
                }
                let (text, at) = codec.decode_open(&r.sites, OPEN_SITE);
                if let Ok((q, _)) = request {
                    landmark.read(field, &codec, r, q.len(), &text, &at, i, &mut landmarks_file, realization)?;
                }
                println!("FIELD_RELEASE_ONE_RECEIPT problem={i} {}", receipt_text(r));
                (r.classes_or(usize::MAX), text)
            }
            Err(why) => {
                println!("FIELD_RELEASE_REFUSED problem={i} why={why}");
                refused += 1;
                (Vec::new(), Vec::new())
            }
        };
        row(&mut free_file, &format!("{i}\t{}\n", escaped(&text)))?;
        let t = codec.encode(answer).unwrap_or_default();
        let c = coupling(&h, &t);
        let longest = c.plateaus.iter().copied().max_by_key(|&(run, lag)| (run, std::cmp::Reverse(lag.unsigned_abs()))).unwrap_or((0, 0));
        row(&mut couplings, &format!("{i}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n", h.len(), t.len(), c.lambda, c.friction, c.plateaus.len(), longest.0, longest.1))?;
        sum_h += h.len();
        sum_t += t.len();
        sum_lambda += c.lambda;
        sum_friction += c.friction;
        println!("FIELD_RELEASE_ONE problem={i} released={} held={} lambda={} friction={} total_ms={}", h.len(), t.len(), c.lambda, c.friction, started.elapsed().as_millis());
    }
    let lock_rungs: Vec<String> = rungs.iter().map(|(b, n)| format!("{b}:{n}")).collect();
    println!(
        "FIELD_RELEASE_RECEIPTS problems={} locked_whole={locked_whole} open_sites={open_sites} free_circulation={free_circulation} bound_circulation={bound} {} lock_margin_bits_quartiles={} lock_rungs={} landmark_problems={} landmark_digits={} landmark_on_question_digit={} landmark_same_class={} landmark_ms={}",
        held.len(),
        {
            let extents = front_receipt.extents();
            front_receipt.text(extents)
        },
        quartiles(&mut margins),
        if lock_rungs.is_empty() { "-".to_string() } else { lock_rungs.join(",") },
        landmark.problems,
        landmark.digits,
        landmark.on_digit,
        landmark.same,
        landmark.ns / 1_000_000
    );
    // The marks: each calculation's continuation past the answer written through its equals.
    let mut marks_at: Vec<(usize, usize, &[u8])> = Vec::new();
    let mut mark_requests = Vec::new();
    for (i, (question, answer)) in held.iter().enumerate() {
        for (j, (expression, at)) in calculations_of(answer).into_iter().enumerate() {
            if !bytes || !read_ok[i] {
                withheld += 1;
                continue;
            }
            marks_at.push((i, j, expression));
            mark_requests.push(opening(&codec, field, question, &answer[..at]));
        }
    }
    let mut marks_last = ReleaseSweep::default();
    let marks = release_requests(field, &mark_requests, sweeps, codec.void(), realization, &mut within("marks", started, stop_ms, &mut marks_last))?;
    let mut marks_file = rows_file(&out.join("MARKS.tsv"), "")?;
    for (&(i, j, expression), released) in marks_at.iter().zip(&marks) {
        let mut r = match released {
            Ok(continued) => codec.decode_open(&continued.sites, OPEN_SITE).0,
            Err(why) => {
                println!("FIELD_RELEASE_REFUSED problem={i} mark={j} why={why}");
                refused += 1;
                Vec::new()
            }
        };
        if let Some(cut) = r.windows(2).position(|w| w == b">>") {
            r.truncate(cut + 2);
        }
        row(&mut marks_file, &format!("{i}\t{j}\t{}\t{}\n", escaped(expression), escaped(&r)))?;
    }
    println!(
        "FIELD_RELEASE free={} marks={} withheld={withheld} refused={refused} sweeps={sweeps} stop_ms={stop_ms} free_sweeps={} free_live={} free_reached={} free_front={} free_open={} free_rung={} free_stopped={} marks_sweeps={} marks_live={} marks_reached={} marks_front={} marks_open={} marks_rung={} marks_stopped={} released={sum_h} held={sum_t} lambda={sum_lambda} friction={sum_friction} ms={}",
        held.len(),
        marks_at.len(),
        free_last.done,
        free_last.live,
        free_last.reached,
        free_last.front,
        free_last.open,
        free_last.rung,
        free_last.live > 0 && free_last.done < sweeps,
        marks_last.done,
        marks_last.live,
        marks_last.reached,
        marks_last.front,
        marks_last.open,
        marks_last.rung,
        marks_last.live > 0 && marks_last.done < sweeps,
        started.elapsed().as_millis()
    );
    Ok(())
}

/// [agent-inferred, November 1] An open site as a release writes it: one byte no codec class
/// writes (a NUL), so a calculation through an open site is never read as written.
const OPEN_SITE: &[u8] = b"\0";

/// The lock rungs of a release's sites as `β:count`, ascending (`-` where none locked).
fn rung_text(rungs: &[u64]) -> String {
    let mut count: std::collections::BTreeMap<u64, usize> = std::collections::BTreeMap::new();
    for &r in rungs.iter().filter(|&&r| r > 0) {
        *count.entry(r).or_insert(0) += 1;
    }
    if count.is_empty() {
        return "-".into();
    }
    count.iter().map(|(b, n)| format!("{b}:{n}")).collect::<Vec<_>>().join(",")
}

/// [definition; agent-inferred, November 1] **A release's receipt as one line** (the dispersing
/// field's §14.9): its sites, the sites reached and locked (the rest unreached or open), the sweeps
/// each site was reached and each locked as their least, quartiles and most, the extent's reading
/// (`site@sweep:void` where a reached site locked on the void, `site@sweep:bound` where the front
/// reached the answer's bound with no void locked, `-` where neither came in the sweeps run), its free
/// and bound circulation, the quartiles of its locks' margins over their counters (in bits), its lock
/// rungs (each site's own `β_t` at its lock) and the sweeps ridden at each rung. Count only: no site's
/// class enters it.
fn receipt_text(r: &Released) -> String {
    let mut margins: Vec<i64> = r.counters.iter().flatten().map(|&(_, m)| m).collect();
    let mut front = FrontReceipt::default();
    front.add(r);
    format!(
        "sites={} open={} {} free_circulation={} bound_circulation={} lock_margin_bits_quartiles={} rungs={} ridden={}",
        r.sites.len(),
        r.open,
        front.text(format!("extent={}", extent_text(r.extent))),
        r.free,
        r.bound,
        quartiles(&mut margins),
        rung_text(&r.rungs),
        ridden_text(&r.ridden)
    )
}

/// [definition; agent-inferred, November 1] **The front's receipts, summed over releases** (§14.9):
/// the sites reached and locked and the sweep each was reached and each locked, and the extents: how
/// many were read at a locked void and how many at the bound, how many were not read in the sweeps run,
/// and the quartiles of the extents' sites and sweeps. One release's is a sum over one.
#[derive(Default)]
struct FrontReceipt {
    reached: Vec<i64>,
    locked: Vec<i64>,
    void: usize,
    bound: usize,
    unread: usize,
    extent_site: Vec<i64>,
    extent_sweep: Vec<i64>,
}

impl FrontReceipt {
    fn add(&mut self, r: &Released) {
        self.reached.extend(r.reached.iter().flatten().map(|&s| s as i64));
        self.locked.extend(r.lock_sweeps.iter().flatten().map(|&s| s as i64));
        match r.extent {
            Some((site, sweep, bound)) => {
                self.extent_site.push(site as i64);
                self.extent_sweep.push(sweep as i64);
                if bound {
                    self.bound += 1;
                } else {
                    self.void += 1;
                }
            }
            None => self.unread += 1,
        }
    }

    /// The receipt as `key=value` words, the extents' reading as `extents` gives it.
    fn text(&mut self, extents: String) -> String {
        format!("reached={} locked={} reach_sweep_quartiles={} lock_sweep_quartiles={} {extents}", self.reached.len(), self.locked.len(), five(&mut self.reached, 0), five(&mut self.locked, 0))
    }

    /// The extents of the releases summed: how many were read at a locked void, at the bound, and not
    /// read, and the quartiles of their sites and sweeps.
    fn extents(&mut self) -> String {
        format!("extents_void={} extents_bound={} extents_unread={} extent_site_quartiles={} extent_sweep_quartiles={}", self.void, self.bound, self.unread, five(&mut self.extent_site, 0), five(&mut self.extent_sweep, 0))
    }
}

/// A release's extent as `site@sweep:void` (a reached site locked on the void), `site@sweep:bound`
/// (the front reached the answer's bound with no void locked) or `-` (neither, in the sweeps run).
pub(super) fn extent_text(extent: Option<(usize, usize, bool)>) -> String {
    match extent {
        Some((site, sweep, bound)) => format!("{site}@{sweep}:{}", if bound { "bound" } else { "void" }),
        None => "-".into(),
    }
}

/// The least, the quartiles and the most of margins on `2^(−16)` bits, each in whole bits (`-` where
/// none).
fn quartiles(margins: &mut [i64]) -> String {
    five(margins, 16)
}

/// The least, the quartiles and the most of `values`, each shifted right by `shift` (`-` where none).
fn five(values: &mut [i64], shift: u32) -> String {
    if values.is_empty() {
        return "-".into();
    }
    values.sort_unstable();
    let at = |q: usize| values[(q * (values.len() - 1)) / 4] >> shift;
    format!("{}/{}/{}/{}/{}", at(0), at(1), at(2), at(3), at(4))
}

/// Which sites of a release's last state are locked, one a site of its region (the question's and the
/// unreached open sites' not): the locks its last sweep read, which the landmarks and the parity read
/// the last state with.
pub(super) fn locks_of(r: &Released) -> Vec<bool> {
    (0..r.classes.len()).map(|t| t >= r.start && r.sites.get(t - r.start).is_some_and(Option::is_some)).collect()
}

/// The sweeps ridden at each rung as `β:sweeps`.
fn ridden_text(ridden: &[(u64, usize)]) -> String {
    ridden.iter().map(|(b, n)| format!("{b}:{n}")).collect::<Vec<_>>().join(",")
}

/// [definition; agent-inferred, November 1] **The landmarks' counts** (the dispersing field's §3
/// receipt): over the free releases whose answer writes a first calculation `<<…>>`, each digit site
/// of it and the question site carrying the most weight in its still heads' currents
/// ([`Field::landmarks`]); counted are those sites, those whose landmark is a question digit, and
/// those whose landmark holds the site's own class. Each row goes to `LANDMARKS.tsv` (private: it
/// carries the problem's bytes). Read through the realization (on the card, its rows), timed.
/// [agent-inferred] The last state is read with its locks ([`locks_of`]): the release's last sweep
/// read the locked sites as definite sources, heard past the near field (§14.1), and a reading of its
/// last tick without them would be of a state the release never read.
#[derive(Default)]
struct LandmarkCount {
    problems: usize,
    digits: usize,
    on_digit: usize,
    same: usize,
    ns: u128,
}

impl LandmarkCount {
    #[allow(clippy::too_many_arguments)]
    fn read(&mut self, field: &Field, codec: &FieldCodec, r: &Released, question: usize, text: &[u8], at: &[usize], problem: usize, file: &mut std::fs::File, realization: &mut dyn FieldRealization) -> Result<()> {
        let Some(open) = text.windows(2).position(|w| w == b"<<") else { return Ok(()) };
        let Some(close) = text[open..].windows(2).position(|w| w == b">>").map(|c| open + c) else { return Ok(()) };
        let sites: Vec<usize> = (0..r.sites.len()).filter(|&s| at[s] >= open + 2 && at[s] < close && r.sites[s].is_some_and(|c| codec.is_digit(c))).collect();
        if sites.is_empty() {
            return Ok(());
        }
        let started = std::time::Instant::now();
        let unresolved: Vec<bool> = (0..r.classes.len()).map(|t| r.faces[t].is_some()).collect();
        let locked = locks_of(r);
        let region = Region { classes: &r.classes, unresolved: &unresolved, faces: &r.faces, locked: &locked, clock: &[], echo: &[] };
        let marks = realization.read_landmarks(field, &region, question, &sites.iter().map(|&s| r.start + s).collect::<Vec<_>>(), 1).map_err(|e| e.to_string())?;
        self.ns += started.elapsed().as_nanos();
        self.problems += 1;
        for (&s, mark) in sites.iter().zip(&marks) {
            self.digits += 1;
            let class = r.sites[s].unwrap_or(usize::MAX);
            let Some(&(j, share)) = mark.first() else { continue };
            self.on_digit += usize::from(codec.is_digit(r.classes[j]));
            self.same += usize::from(r.classes[j] == class);
            let byte = |c: usize| escaped(&codec.decode(&[c]));
            row(file, &format!("{problem}\t{s}\t{}\t{j}\t{}\t{share}\n", byte(class), byte(r.classes[j])))?;
        }
        Ok(())
    }
}

/// [agent-inferred, November 1] **A release's exterior**: one line a sweep, the sweep run while the
/// command is inside `stop_ms` (fixed before launch from the run's projection, never raised), and the
/// last report kept in `last`. A set that ends with problems open after fewer sweeps than its bound
/// was stopped here (the release ends no other way with problems open).
fn within<'a>(set: &'a str, started: std::time::Instant, stop_ms: u128, last: &'a mut ReleaseSweep) -> impl FnMut(&ReleaseSweep) -> bool + 'a {
    move |sweep| {
        let ms = started.elapsed().as_millis();
        println!(
            "FIELD_RELEASE_SWEEP set={set} done={} live={} reached={} front={} locked={} open={} rung={} change={} holding={} soft={} overturned={} free={} ms={ms}",
            sweep.done, sweep.live, sweep.reached, sweep.front, sweep.locked, sweep.open, sweep.rung, sweep.change, sweep.holding, sweep.soft, sweep.overturned, sweep.free
        );
        *last = *sweep;
        ms < stop_ms
    }
}

/// A release's opening: the question's classes and its written prefix, and the answer sites left
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

/// The releases of every admitted opening read together; a refused opening keeps its refusal. A
/// refused batch is released again one problem at a time (each release is its own region's, so
/// each is the batch's own), and a problem's refusal is that problem's alone.
fn release_requests(field: &Field, requests: &[std::result::Result<(Vec<usize>, usize), String>], sweeps: usize, void: usize, realization: &mut dyn FieldRealization, sweep: &mut dyn FnMut(&ReleaseSweep) -> bool) -> Result<Vec<std::result::Result<Released, String>>> {
    let admitted: Vec<(&[usize], usize)> = requests.iter().filter_map(|r| r.as_ref().ok().map(|(q, open)| (q.as_slice(), *open))).collect();
    let released: Vec<std::result::Result<Released, String>> = if admitted.is_empty() {
        Vec::new()
    } else {
        match field.release_realized(&admitted, sweeps, void, realization, &mut *sweep) {
            Ok(all) => all.into_iter().map(Ok).collect(),
            Err(why) => {
                println!("FIELD_RELEASE_BATCH_REFUSED problems={} why={why}", admitted.len());
                admitted.iter().map(|&one| field.release_realized(&[one], sweeps, void, realization, &mut *sweep).map(|mut r| r.remove(0)).map_err(|e| e.to_string())).collect()
            }
        }
    };
    let mut released = released.into_iter();
    Ok(requests.iter().map(|r| match r {
        Ok(_) => released.next().unwrap_or_else(|| Err("a release the batch did not return".to_string())),
        Err(why) => Err(why.clone()),
    }).collect())
}

/// `release-field-text STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD HELD_SHA COUNT SWEEPS
/// STOP_MS`: each of the first `COUNT` held questions and the answer the field releases for it,
/// whole, its sweeps inside `STOP_MS` (a private read: never committed; the held answer is not
/// printed beside it).
pub(super) fn release_text(args: &[String], realization: &mut dyn FieldRealization) -> Result<()> {
    if args.len() != 12 {
        return Err("release-field-text STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD HELD_SHA COUNT SWEEPS STOP_MS".into());
    }
    let started = std::time::Instant::now();
    let learner = FieldLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let units = units_of(&args[5], &args[6])?;
    let codec = FieldCodec::from_text(std::str::from_utf8(&pinned_read(&args[3], &args[4], CODEC_BUDGET)?)?, units)?;
    let held = problems_of(&pinned_read(&args[7], &args[8], READ_BUDGET as usize)?);
    let (limit, sweeps, stop_ms) = (count(&args[9])?, positive(&args[10])?, positive(&args[11])? as u128);
    let held = &held[..limit.min(held.len())];
    let requests: Vec<_> = held.iter().map(|(question, _)| opening(&codec, &learner.field, question, b"")).collect();
    let mut last = ReleaseSweep::default();
    let released = release_requests(&learner.field, &requests, sweeps, codec.void(), realization, &mut within("text", started, stop_ms, &mut last))?;
    for (i, ((question, _), released)) in held.iter().zip(released).enumerate() {
        let (answer, receipt) = match released {
            Ok(r) => (String::from_utf8_lossy(&codec.decode_open(&r.sites, "\u{2591}".as_bytes()).0).into_owned(), receipt_text(&r)),
            Err(why) => (format!("(refused: {why})"), "refused".into()),
        };
        println!("FIELD_PROMPT {i}\n{}\nFIELD_ANSWER {i} {receipt}\n{answer}\n", String::from_utf8_lossy(question));
    }
    println!("FIELD_RELEASE_TEXT problems={} sweeps={} live={} reached={} front={} open={} rung={} stopped={} ms={}", held.len(), last.done, last.live, last.reached, last.front, last.open, last.rung, last.live > 0 && last.done < sweeps, started.elapsed().as_millis());
    Ok(())
}

/// [measurement] **`rows-field`**: where an open and a definite receiver's rows put their mass (§15.9's
/// reading, `Field::row_shares`) on three sets of crib regions: the withheld problems read with their
/// neighbours (`unseen_regions`), training's masked regions and front regions' read 1 (`shape`), each
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
    let (mut masked, mut fronts) = (Vec::new(), Vec::new());
    let mut draw = 0u64;
    for (q, a, _) in &encoded {
        draw += 1;
        let length = q.len() + a.len() + tail(seed, draw, codec.answer - a.len());
        let mut classes = region_classes(&codec, q, a, length);
        match shape(seed, draw, q.len(), length, a.len() + 1) {
            Shape::Masked(mask) => masked.push((classes, mask)),
            Shape::Front(front) => {
                classes.truncate(front.cut);
                fronts.push((classes, front.open.clone()));
            }
        }
    }
    for (name, set) in [("withheld", &withheld), ("masked", &masked), ("front_read1", &fronts)] {
        let mut total = holonics::hnn::tower::field::RowShares::default();
        for (classes, open) in set.iter() {
            let r = field.row_shares(&Region { classes, unresolved: open, faces: &[], locked: &[], clock: &[], echo: &[] }).map_err(|e| e.to_string())?;
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

/// [measurement; agent-inferred, November 2] **How far each paced head's clock is from a digit clock** (§16): over the
/// held problems' regions (the question and its answer, every site definite), the mean rate `κ` at the digits and at
/// the sites inside words (a letter after a letter), in millionths of a tick, by head (`FIELD_PACE`). A digit clock
/// reads one and zero. Material arithmetic only (the rate reads the opening face).
fn pace_text(field: &Field, codec: &FieldCodec, problems: &Problems, lap: i64) -> Result<Vec<(usize, i128)>> {
    let d = field.declaration;
    let mut acc: std::collections::BTreeMap<usize, (i128, u64, i128, u64)> = std::collections::BTreeMap::new();
    for (q, a, _) in problems.iter().take(32) {
        let classes: Vec<usize> = q.iter().chain(a).copied().collect();
        let open = vec![false; classes.len()];
        let region = Region { classes: &classes, unresolved: &open, faces: &[], locked: &[], clock: &[], echo: &[] };
        let bytes = codec.decode(&classes);
        for (h, kappa) in field.pace_rates(&region).map_err(|e| e.to_string())? {
            let e = acc.entry(h).or_default();
            for (t, &k) in kappa.iter().enumerate() {
                let letter = |u: usize| bytes.get(u).is_some_and(|b| b.is_ascii_alphabetic());
                if codec.is_digit(classes[t]) {
                    e.0 += k as i128;
                    e.1 += 1;
                } else if t > 0 && letter(t) && letter(t - 1) {
                    e.2 += k as i128;
                    e.3 += 1;
                }
            }
        }
    }
    let _ = d;
    let mut gaps = Vec::new();
    for (h, (sd, nd, sw, nw)) in acc {
        let mean = |s: i128, n: u64| (s * 1_000_000 >> 24) / n.max(1) as i128;
        println!("FIELD_PACE lap={lap} head={h} digits={nd} kappa_digits={} inside_words={nw} kappa_inside_words={} gap={}", mean(sd, nd), mean(sw, nw), mean(sd, nd) - mean(sw, nw));
        gaps.push((h, mean(sd, nd) - mean(sw, nw)));
    }
    Ok(gaps)
}

/// [measurement; agent-inferred, November 2] **The held answer rows' concentration on the question, over rested
/// learners** (`peaks-field CODEC CODEC_SHA UNITS UNITS_SHA HELD HELD_SHA STATE STATE_SHA [STATE STATE_SHA …]`):
/// for each state, read through the declared realization with no deposit, the held problems' context regions
/// (base 3 of [`held_regions`], the answer starting at the question's end) by [`FieldRealization::read_row_peaks`],
/// summed per tick and head over three sets of the open answer sites: every one (`FIELD_PEAKS`), those whose
/// target is a digit (`FIELD_PEAKS_DIGIT`), and the first calculation's first operand (`FIELD_PEAKS_OPERAND`: the
/// digits after the answer's first `<<`, whose right source is the same digit of the first question number written
/// as that operand). Each with its chance (`*_flat`, the share a row spread evenly over the question would put
/// there). Then each head's temperatures (`FIELD_TEMPER`, on `2^(−24)`). Millionths and bits are the reading's
/// chart. A reading only: nothing is deposited and no state is written.
/// [measurement; agent-inferred, November 2] **The copy's rows at the release's fronts** (§16): for each held problem and
/// each digit of its first calculation's two operands (`<<a+b=`), the front region (the question and the answer before
/// the digit definite, the digit and every later site open through the answer's first void) read by
/// [`FieldRealization::read_row_peaks`], the digit's own row per tick and head: whether its largest question share is
/// on the same digit of the question's number (`top_site_right`), its share of the question (`top_share`), its spread
/// in thousandths of a bit (`spread_bits`, flat `flat_bits`), and whether its top is a digit (`top_digit`), in
/// millionths of the rows (`FIELD_PEAKS_OPERAND`). A reading only.
fn peaks_text(field: &Field, codec: &FieldCodec, held: &Problems, realization: &mut dyn FieldRealization, lap: &str) -> Result<()> {
    let started = std::time::Instant::now();
    let d = field.declaration;
    let digit: Vec<bool> = (0..codec.alphabet()).map(|c| codec.is_digit(c)).collect();
    // Each operand digit's front: (classes, open, question length, receiver, right source).
    let mut reads: Vec<(Vec<usize>, Vec<bool>, usize, usize, usize)> = Vec::new();
    for (q, a, _) in held {
        let (qb, ab) = (codec.decode(q), codec.decode(a));
        let runs: Vec<(usize, usize)> = (0..qb.len()).filter(|&t| qb[t].is_ascii_digit() && (t == 0 || !qb[t - 1].is_ascii_digit())).map(|t| (t, qb[t..].iter().take_while(|b| b.is_ascii_digit()).count())).collect();
        let Some(open) = ab.windows(2).position(|w| w == b"<<") else { continue };
        let la = ab[open + 2..].iter().take_while(|b| b.is_ascii_digit()).count();
        let lb = ab.get(open + 3 + la..).map_or(0, |r| r.iter().take_while(|b| b.is_ascii_digit()).count());
        if runs.len() < 2 || la == 0 || lb == 0 || runs[0].1 != la || runs[1].1 != lb {
            continue;
        }
        let digits: Vec<(usize, usize)> = (0..la).map(|k| (open + 2 + k, runs[0].0 + k)).chain((0..lb).map(|k| (open + 3 + la + k, runs[1].0 + k))).collect();
        for (offset, source) in digits {
            let mut classes: Vec<usize> = q.iter().chain(a).copied().collect();
            classes.push(codec.void());
            let at = q.len() + offset;
            let open_sites: Vec<bool> = (0..classes.len()).map(|t| t >= at).collect();
            reads.push((classes, open_sites, q.len(), at, source));
        }
    }
    // [tick · heads + head]: rows, Σ top/question (millionths), Σ spread (thousandths of a bit), Σ flat, Σ top a digit,
    // Σ top the right site.
    let mut acc = vec![[0i128; 6]; d.ticks * d.heads];
    for chunk in reads.chunks(64) {
        let views: Vec<Region> = chunk.iter().map(|(c, u, _, _, _)| Region { classes: c, unresolved: u, faces: &[], locked: &[], clock: &[], echo: &[] }).collect();
        let questions: Vec<usize> = chunk.iter().map(|r| r.2).collect();
        let peaks = realization.read_row_peaks(field, &views, &questions, &digit).map_err(|e| e.to_string())?;
        let mut rows = peaks.iter();
        for (classes, open, question, at, source) in chunk {
            let count = open.iter().filter(|&&u| u).count();
            for _ in 0..d.ticks * d.heads * count {
                let peak = rows.next().ok_or("a read's peaks that are fewer than its rows")?;
                if peak.site as usize != *at {
                    continue;
                }
                let cell = &mut acc[peak.tick as usize * d.heads + peak.head as usize];
                let qm = peak.question;
                cell[0] += 1;
                cell[1] += if qm == 0 { 0 } else { (peak.top as u128 * 1_000_000 / qm) as i128 };
                cell[2] += if peak.collision == 0 { 0 } else { (2 * log2_milli(qm) - log2_milli(peak.collision) - 63_000) as i128 };
                cell[3] += log2_milli(*question as u128) as i128;
                cell[4] += i128::from(peak.top_site != u32::MAX && digit[classes[peak.top_site as usize]]);
                cell[5] += i128::from(peak.top_site as usize == *source);
            }
        }
    }
    for tick in 0..d.ticks {
        for head in 0..d.heads {
            let a = acc[tick * d.heads + head];
            let rows = a[0].max(1);
            println!("FIELD_PEAKS_OPERAND lap={lap} tick={tick} head={head} rows={} top_share={} spread_millibits={} flat_millibits={} top_digit={} top_site_right={}", a[0], a[1] / rows, a[2] / rows, a[3] / rows, a[4] * 1_000_000 / rows, a[5] * 1_000_000 / rows);
        }
    }
    println!("FIELD_PEAKS_READ lap={lap} reads={} ms={}", reads.len(), started.elapsed().as_millis());
    Ok(())
}

pub(super) fn peaks_field(args: &[String], realization: &mut dyn FieldRealization) -> Result<()> {
    if args.len() < 9 || (args.len() - 7) % 2 != 0 {
        return Err("peaks-field CODEC CODEC_SHA UNITS UNITS_SHA HELD HELD_SHA STATE STATE_SHA [STATE STATE_SHA ...]".into());
    }
    let started = std::time::Instant::now();
    let units = units_of(&args[3], &args[4])?;
    if !units.merges().is_empty() {
        return Err("peaks-field reads an operand's digits as bytes: a codec of byte units".into());
    }
    let codec = FieldCodec::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], CODEC_BUDGET)?)?, units)?;
    let held_text = pinned_read(&args[5], &args[6], READ_BUDGET as usize)?;
    let held: Problems = problems_of(&held_text)
        .iter()
        .map(|(q, a)| Ok((codec.encode(&question_text(q)).map_err(|e| e.to_string())?, codec.encode(a).map_err(|e| e.to_string())?, a.len())))
        .collect::<std::result::Result<Vec<_>, String>>()?
        .into_iter()
        .filter(|(_, a, _)| a.len() < codec.answer)
        .collect();
    for pair in args[7..].chunks(2) {
        let learner = FieldLearner::from_text(std::str::from_utf8(&pinned_read(&pair[0], &pair[1], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
        let lap = Path::new(&pair[0]).extension().and_then(|e| e.to_str()).unwrap_or("-").to_string();
        peaks_text(&learner.field, &codec, &held, realization, &lap)?;
        for head in 0..learner.field.declaration.heads {
            println!("FIELD_TEMPER lap={lap} head={head} class={} listen={}", learner.field.temper(head, false).map_err(|e| e.to_string())?, learner.field.temper(head, true).map_err(|e| e.to_string())?);
        }
        println!("FIELD_PEAKS_LAP lap={lap} ms={}", started.elapsed().as_millis());
    }
    Ok(())
}

/// [measurement; agent-inferred, November 2] **The founding's route to the clock and the anchor** (`align-field UNITS
/// UNITS_SHA TRAIN TRAIN_SHA DEV DEV_SHA KEYS KEYS_SHA D H n STILL f K SECTION`, §16): the learner founded as
/// `train-field` founds it, its first section's regions drawn as its first lap draws them, read and returned once
/// through the declared realization (no deposit), then two readings of that covector against the material:
/// - `FIELD_ALIGN_PACE`: each paced head's rate change along the descent at digits against elsewhere (a digit clock's
///   route lowers the others' against the digits': `gap = mean elsewhere − mean at digits < 0`, in millionths of the
///   change's root mean square);
/// - `FIELD_ALIGN_ANCHOR`: at each region's first operand digit after `<<`, each paced head's period-81 mode, the
///   definite non-digit keys against that site's probe ([`Field::anchor_census`]): opposing, near-silent, aligned, and
///   the near-silent ones the descent drives to oppose or to align.
pub(super) fn align(args: &[String], realization: &mut dyn FieldRealization) -> Result<()> {
    if args.len() != 16 {
        return Err("align-field UNITS UNITS_SHA TRAIN TRAIN_SHA DEV DEV_SHA KEYS KEYS_SHA D H n STILL f K SECTION".into());
    }
    let started = std::time::Instant::now();
    let units = units_of(&args[1], &args[2])?;
    let train_text = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let dev_text = pinned_read(&args[5], &args[6], READ_BUDGET as usize)?;
    let keys = pinned_read(&args[7], &args[8], READ_BUDGET as usize)?;
    let (width, heads, modes, still, contacts, ticks) = (positive(&args[9])?, positive(&args[10])?, positive(&args[11])?, count(&args[12])?, positive(&args[13])?, positive(&args[14])?);
    let section = positive(&args[15])?;
    let train_problems = problems_of(&train_text);
    let codec = FieldCodec::found(units, &train_problems)?;
    let encode = |problems: &[(Vec<u8>, Vec<u8>)]| -> Result<Problems> {
        problems.iter().map(|(q, a)| Ok((codec.encode(&question_text(q)).map_err(|e| e.to_string())?, codec.encode(a).map_err(|e| e.to_string())?, a.len()))).collect::<std::result::Result<Vec<_>, String>>().map_err(|e| e.into())
    };
    let train_set = encode(&train_problems)?;
    let dev_set: Problems = encode(&problems_of(&dev_text))?.into_iter().filter(|(_, a, _)| a.len() < codec.answer).collect();
    let reach = train_set.iter().chain(&dev_set).map(|(q, _, _)| q.len() + codec.answer).max().unwrap_or(codec.answer);
    let declaration = FieldDeclaration { alphabet: codec.alphabet(), width, heads, modes, still, contacts, ticks, frames: heads, reach, clocks: clocks_of(heads, still) };
    let mut learner = FieldLearner::new(Field::found(declaration, &keys).map_err(|e| e.to_string())?, 8);
    let seed = u64::from_be_bytes(keys.get(keys.len().saturating_sub(8)..).filter(|w| w.len() == 8).ok_or("a key file of fewer than eight bytes")?.try_into()?);
    let (sections, _) = sections_of(&train_set, section, dev_set.len(), seed);
    let first = walk(seed, 0, sections.len())[0];
    let mut draw = 0u64;
    let (regions, _) = section_regions(&codec, &train_set, &sections[first], seed, &mut draw, &mut learner, realization)?;
    let mut views = views_of(&regions);
    let (_, mut g) = realization.read_and_return(&learner.field, &views).map_err(|e| e.to_string())?;
    let founding_nonzero = g[learner.field.layout().pace..].iter().filter(|&&v| v != 0).count() + g[learner.field.layout().q..learner.field.layout().q_bias].iter().filter(|&&v| v != 0).count();
    println!("FIELD_ALIGN_FOUNDING pace_and_word_covector_nonzero={founding_nonzero}");
    // [agent-inferred, November 2] The founding holds the readout at zero, so no covector reaches the word charts or
    // the paces until the readout moves; with `AFTER_FIRST=1` the run's own first section is deposited (nothing is
    // saved) and the read is of the second section's covector, the first that reaches them.
    let regions_next;
    if std::env::var_os("AFTER_FIRST").is_some() {
        learner.section_realized(&views, realization).map_err(|e| e.to_string())?;
        let second = walk(seed, 0, sections.len())[1];
        regions_next = section_regions(&codec, &train_set, &sections[second], seed, &mut draw, &mut learner, realization)?.0;
        views = views_of(&regions_next);
        g = realization.read_and_return(&learner.field, &views).map_err(|e| e.to_string())?.1;
        println!("FIELD_ALIGN_AFTER_FIRST pace_and_word_covector_nonzero={}", g[learner.field.layout().pace..].iter().filter(|&&v| v != 0).count() + g[learner.field.layout().q..learner.field.layout().q_bias].iter().filter(|&&v| v != 0).count());
    }
    let field = &learner.field;
    let d = field.declaration;
    let digit: Vec<bool> = (0..codec.alphabet()).map(|c| codec.is_digit(c)).collect();
    let lt = codec.encode(b"<").map_err(|e| e.to_string())?[0];
    println!("FIELD_ALIGN_READ regions={} sites={} ms={}", views.len(), views.iter().map(|r| r.classes.len()).sum::<usize>(), started.elapsed().as_millis());
    let mut route: std::collections::BTreeMap<usize, (u64, u64, i128, i128, i128)> = std::collections::BTreeMap::new();
    for r in &views {
        for (h, nd, no, sd, so, sq) in field.pace_route(r, &g, &digit).map_err(|e| e.to_string())? {
            let e = route.entry(h).or_default();
            e.0 += nd;
            e.1 += no;
            e.2 += sd;
            e.3 += so;
            e.4 += sq;
        }
    }
    for (h, (nd, no, sd, so, sq)) in route {
        let rms = ((sq / (nd + no).max(1) as i128).max(1) as u128).isqrt() as i128;
        let (md, mo) = (sd / nd.max(1) as i128, so / no.max(1) as i128);
        println!("FIELD_ALIGN_PACE head={h} digit_sites={nd} other_sites={no} mean_digits={md} mean_others={mo} gap_millionths_of_rms={}", (mo - md) * 1_000_000 / rms);
    }
    for h in (0..d.heads).filter(|&h| d.carries_moment(h)) {
        let Some(l) = (0..d.modes).find(|&l| field.rings()[l * (d.frames - d.still) + h % d.frames - d.still].0 == 81) else { continue };
        let mut total = [0u64; 6];
        let mut anchors = 0u64;
        for r in &views {
            let Some(t) = (0..r.classes.len().saturating_sub(2)).find(|&t| r.classes[t] == lt && r.classes[t + 1] == lt) else { continue };
            let a0 = t + 2;
            if a0 >= r.classes.len() || !digit[r.classes[a0]] {
                continue;
            }
            anchors += 1;
            for (acc, v) in total.iter_mut().zip(field.anchor_census(r, a0, h, l, &digit, &g).map_err(|e| e.to_string())?) {
                *acc += v;
            }
        }
        println!("FIELD_ALIGN_ANCHOR head={h} mode={l} anchors={anchors} opposing={} near_silent={} aligned={} silent_driven_to_oppose={} silent_driven_to_align={} digit_sources={}", total[0], total[1], total[2], total[3], total[4], total[5]);
    }
    println!("FIELD_ALIGN_DONE ms={}", started.elapsed().as_millis());
    Ok(())
}

/// [agent-inferred, November 2] **The §16 witness on the crib's codec, completed with a readout** (a reading's
/// fixture, never a learner's): tests.rs's hand-set clock and copy on the crib declaration, and the copy's current
/// carrying the source digit's identity `e^(2πi d/10)` on head 3's coarsest mode (period 729, which turns little over
/// the clock distances the copy reads), written to the face's dimensions 20 and 21 and read by the readout, so the
/// code at an operand digit falls when the copy holds. Returns the field and the witness's parts: the clock's entries
/// (the pace rows) and the readers' (the word and probe charts and their biases).
fn witness_on(codec: &FieldCodec, declaration: FieldDeclaration, keys: &[u8]) -> Result<Field> {
    let mut field = Field::found(declaration, keys).map_err(|e| e.to_string())?;
    field.theta.iter_mut().for_each(|v| *v = 0);
    let d = declaration;
    let (dw, n, m) = (d.width, d.modes, d.complex());
    let m2 = 2 * m;
    let l = field.layout().clone();
    let alphabet = codec.alphabet();
    let face_one = 1i64 << 16;
    let one = 1i64 << 24;
    let lt = codec.encode(b"<").map_err(|e| e.to_string())?[0];
    // A turn of `num/den` (the clock's grain, to the nearest point of `2^(−24)`).
    let face = |field: &Field, num: i128, den: i128| field.turn_face(((num << 25) / den + (num << 25).signum()) / 2, 1);
    let times = |g: i64, part: i64| ((g as i128 * part as i128 + (1 << 29)) >> 30) as i64;
    let root = |k: u128| ((k << 48).isqrt()) as i64;
    let set = |field: &mut Field, at: usize, v: i64| -> Result<()> {
        field.theta[at] = i32::try_from(v).map_err(|_| "a witness entry outside 32 bits")?;
        Ok(())
    };
    for c in 0..=alphabet {
        let digit = c < alphabet && codec.is_digit(c);
        set(&mut field, l.enc + c * dw + usize::from(digit), face_one)?;
        if c == alphabet {
            set(&mut field, l.enc + c * dw + 4, face_one)?;
        }
        if digit {
            let value = codec.decode(&[c])[0] - b'0';
            let (re, im) = face(&field, value as i128, 10);
            set(&mut field, l.enc + c * dw + 7, re >> 14)?;
            set(&mut field, l.enc + c * dw + 8, im >> 14)?;
        }
        set(&mut field, l.before + c * dw + if c == lt { 3 } else { 5 }, face_one)?;
        set(&mut field, l.after + c * dw + 6, face_one)?;
    }
    // Head 3 (pace 1): the digit clock.
    set(&mut field, l.pace + dw, -one)?;
    let turned = |field: &mut Field, chart: usize, c: usize, from: (usize, usize), g: i64, theta: (i64, i64)| -> Result<()> {
        let (gc, gs) = (times(g, theta.0), times(g, theta.1));
        set(field, chart + c * dw + from.0, gc)?;
        set(field, chart + c * dw + from.1, -gs)?;
        set(field, chart + (m + c) * dw + from.0, gs)?;
        set(field, chart + (m + c) * dw + from.1, gc)
    };
    let psi = face(&field, -27, 100);
    let anchor = 64 * one;
    let (c16, c32, c81, c729, c0, c1) = (3 * n + 3, 3 * n + 4, 3 * n + 5, 3 * n + 7, 0usize, 1usize);
    set(&mut field, l.q + c16 * dw + 1, root(3))?;
    set(&mut field, l.q + c32 * dw + 1, root(12))?;
    set(&mut field, l.q + c81 * dw + 1, one)?;
    set(&mut field, l.q + c81 * dw + 3, times(anchor / 2, psi.0))?;
    set(&mut field, l.q + c81 * dw, times(-anchor, psi.0))?;
    set(&mut field, l.q + (m + c81) * dw + 3, times(anchor / 2, psi.1))?;
    set(&mut field, l.q + (m + c81) * dw, times(-anchor, psi.1))?;
    set(&mut field, l.probe + c81 * dw + 3, times(anchor, psi.0))?;
    set(&mut field, l.probe + (m + c81) * dw + 3, times(anchor, psi.1))?;
    let (f2, fm2) = (face(&field, 2, 25), face(&field, -2, 25));
    turned(&mut field, l.probe, c16, (12, 13), one, f2)?;
    turned(&mut field, l.probe, c32, (16, 17), one, fm2)?;
    set(&mut field, l.v + c16 * dw + 1, one)?;
    set(&mut field, l.v + c32 * dw + 1, one)?;
    set(&mut field, l.v + c729 * dw + 7, one)?;
    set(&mut field, l.v + (m + c729) * dw + 8, one)?;
    set(&mut field, l.out + 10 * m2 + c16, 64 * one)?;
    set(&mut field, l.out + 11 * m2 + m + c16, 64 * one)?;
    set(&mut field, l.out + 14 * m2 + c32, 32 * one)?;
    set(&mut field, l.out + 15 * m2 + m + c32, 32 * one)?;
    set(&mut field, l.out + 20 * m2 + c729, 16 * one)?;
    set(&mut field, l.out + 21 * m2 + m + c729, 16 * one)?;
    set(&mut field, l.q + c0 * dw + 1, one)?;
    set(&mut field, l.q + (m + c0) * dw + 3, one)?;
    set(&mut field, l.probe_bias + c0, face_one)?;
    set(&mut field, l.probe_bias + m + c0, face_one)?;
    for (c, from, to) in [(c0, (10usize, 11usize), (12usize, 13usize)), (c1, (14, 15), (16, 17))] {
        set(&mut field, l.v + c * dw + from.0, one)?;
        set(&mut field, l.v + (m + c) * dw + from.1, one)?;
        set(&mut field, l.out + to.0 * m2 + c, one)?;
        set(&mut field, l.out + to.1 * m2 + m + c, one)?;
    }
    // The copy's rest (tests.rs's completed witness): before the anchor's channel arrives a receiver's probe is its
    // bias alone, on head 3's mode 6, where every non-digit's key stands at the anchor's strength, so the copy's
    // first ticks rest on a site that carries no digit.
    let c243 = 3 * n + 6;
    set(&mut field, l.q + c243 * dw, anchor)?;
    set(&mut field, l.probe_bias + c243, face_one >> 6)?;
    // The readout: a digit class reads the identity's turn at its own value, a non-digit is held down.
    for c in 0..alphabet {
        if codec.is_digit(c) {
            let value = codec.decode(&[c])[0] - b'0';
            let (re, im) = face(&field, value as i128, 10);
            set(&mut field, l.read + c * dw + 20, times(32 * one, re))?;
            set(&mut field, l.read + c * dw + 21, times(32 * one, im))?;
        } else {
            set(&mut field, l.read_bias + c, -32 * face_one)?;
        }
    }
    // The temperature (`FIELD_WITNESS_HOT`, 16 by default, the card's: at 32 a lock passes its 128-bit carrier, at
    // tests.rs's 127 a row's exponents span past the card's twenty limbs; each refuses, never clipped).
    // The temperatures are held as their logarithms (§16.12), so `FIELD_WITNESS_HOT` is a power of two.
    let t = std::env::var("FIELD_WITNESS_HOT").ok().and_then(|v| v.parse::<i64>().ok()).unwrap_or(16);
    if t <= 0 || t & (t - 1) != 0 {
        return Err("FIELD_WITNESS_HOT is a power of two".into());
    }
    let hot = t.trailing_zeros() as i64 * one;
    set(&mut field, l.temper + 2 * 3, hot)?;
    set(&mut field, l.temper + 2 * 3 + 1, hot)?;
    set(&mut field, l.temper + 1, hot)?;
    Ok(field)
}

/// `⟨a, b⟩ / (|a| |b|)` in millionths over the entries `range` (exact integer sums, a reading's chart).
fn cosine(a: &[i128], b: &[i128]) -> i128 {
    use num_bigint::BigInt;
    let dot = a.iter().zip(b).fold(BigInt::from(0), |s, (&x, &y)| s + BigInt::from(x) * BigInt::from(y));
    let na = a.iter().fold(BigInt::from(0), |s, &x| s + BigInt::from(x) * BigInt::from(x));
    let nb = b.iter().fold(BigInt::from(0), |s, &x| s + BigInt::from(x) * BigInt::from(x));
    let den = (na * nb).sqrt();
    if den == BigInt::from(0) {
        return 0;
    }
    i128::try_from((dot * BigInt::from(1_000_000)) / den).unwrap_or(0)
}

/// [measurement; agent-inferred, November 2] **Whether descent couples the clock and its readers** (`witness-field
/// UNITS UNITS_SHA TRAIN TRAIN_SHA DEV DEV_SHA KEYS KEYS_SHA K`, §16.10): the witness completed with a readout
/// ([`witness_on`]) on the crib declaration at `K` ticks, read at every first-calculation operand digit of the held
/// problems, each a front cut at the digit (the digit the region's last site, open), the faces' covector (no closure)
/// off the declared realization: the witness's code there beside the founding's, then (i) the readers kept and the
/// clock zeroed, (ii) the clock kept and the readers the founding's, (iii) the witness moved a small keyed step on
/// both; each reported as the descent's cosine with the way to the witness, in millionths; and (iv) the descent on
/// each head's `log₂ T` at the witness with its temperatures at 4, and at the founding.
pub(super) fn witness_field_cmd(args: &[String], realization: &mut dyn FieldRealization) -> Result<()> {
    use num_bigint::BigInt;
    if args.len() != 10 {
        return Err("witness-field UNITS UNITS_SHA TRAIN TRAIN_SHA DEV DEV_SHA KEYS KEYS_SHA K".into());
    }
    let started = std::time::Instant::now();
    let units = units_of(&args[1], &args[2])?;
    let train_text = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let dev_text = pinned_read(&args[5], &args[6], READ_BUDGET as usize)?;
    let keys = pinned_read(&args[7], &args[8], READ_BUDGET as usize)?;
    let ticks = positive(&args[9])?;
    let train_problems = problems_of(&train_text);
    let codec = FieldCodec::found(units, &train_problems)?;
    let encode = |problems: &[(Vec<u8>, Vec<u8>)]| -> Result<Problems> {
        problems.iter().map(|(q, a)| Ok((codec.encode(&question_text(q)).map_err(|e| e.to_string())?, codec.encode(a).map_err(|e| e.to_string())?, a.len()))).collect::<std::result::Result<Vec<_>, String>>().map_err(|e| e.into())
    };
    let train_set = encode(&train_problems)?;
    let dev_set: Problems = encode(&problems_of(&dev_text))?.into_iter().filter(|(_, a, _)| a.len() < codec.answer).collect();
    let reach = train_set.iter().chain(&dev_set).map(|(q, _, _)| q.len() + codec.answer).max().unwrap_or(codec.answer);
    let declaration = FieldDeclaration { alphabet: codec.alphabet(), width: 32, heads: 5, modes: 8, still: 2, contacts: 32, ticks, frames: 5, reach, clocks: clocks_of(5, 2) };
    let witness = witness_on(&codec, declaration, &keys)?;
    let founding = Field::found(declaration, &keys).map_err(|e| e.to_string())?;
    // The reads: each operand digit's front cut at the digit.
    let mut reads: Vec<(Vec<usize>, Vec<bool>)> = Vec::new();
    for (q, a, _) in &dev_set {
        let (qb, ab) = (codec.decode(q), codec.decode(a));
        let Some(open) = ab.windows(2).position(|w| w == b"<<") else { continue };
        let la = ab[open + 2..].iter().take_while(|b| b.is_ascii_digit()).count();
        let lb = ab.get(open + 3 + la..).map_or(0, |r| r.iter().take_while(|b| b.is_ascii_digit()).count());
        let runs = (0..qb.len()).filter(|&t| qb[t].is_ascii_digit() && (t == 0 || !qb[t - 1].is_ascii_digit())).count();
        if runs < 2 || la == 0 || lb == 0 {
            continue;
        }
        for offset in (open + 2..open + 2 + la).chain(open + 3 + la..open + 3 + la + lb) {
            let classes: Vec<usize> = q.iter().chain(&a[..=offset]).copied().collect();
            let mut unresolved = vec![false; classes.len()];
            *unresolved.last_mut().unwrap() = true;
            reads.push((classes, unresolved));
        }
    }
    let views: Vec<Region> = reads.iter().map(|(c, u)| Region { classes: c, unresolved: u, faces: &[], locked: &[], clock: &[], echo: &[] }).collect();
    // `(code, faces whose top class is the digit, covector)`.
    let covector = |field: &Field, realization: &mut dyn FieldRealization| -> Result<(i64, usize, Vec<i128>)> {
        let mut g = vec![0i128; field.theta.len()];
        let (mut code, mut right) = (0i64, 0usize);
        for chunk in views.chunks(64) {
            let (faces, part) = realization.read_and_return_open(field, chunk).map_err(|e| e.to_string())?;
            for (region, faces) in chunk.iter().zip(&faces) {
                let last = region.classes.len() - 1;
                if let Some(face) = &faces[last] {
                    code += face.code(region.classes[last]);
                    right += usize::from((0..face.masses.len()).max_by_key(|&c| face.masses[c]) == Some(region.classes[last]));
                }
            }
            for (acc, v) in g.iter_mut().zip(part) {
                *acc += v;
            }
        }
        Ok((code, right, g))
    };
    let l = witness.layout().clone();
    let (dw, m) = (declaration.width, declaration.complex());
    let pace3 = l.pace + dw..l.pace + 2 * dw;
    let readers: Vec<std::ops::Range<usize>> = vec![l.q..l.q + 2 * m * dw, l.q_bias..l.q_bias + 2 * m, l.probe..l.probe + 2 * m * dw, l.probe_bias..l.probe_bias + 2 * m];
    let gather = |v: &[i128], ranges: &[std::ops::Range<usize>]| -> Vec<i128> { ranges.iter().flat_map(|r| v[r.clone()].iter().copied()).collect() };
    let theta = |f: &Field| -> Vec<i128> { f.theta.iter().map(|&x| x as i128).collect() };
    let (code_w, right_w, _) = covector(&witness, realization)?;
    let (code_f, right_f, _) = covector(&founding, realization)?;
    let sites = views.len().max(1) as i128;
    let bits = |c: i64| { let x = c as i128 * 1000 / sites >> 20; format!("{}.{:03}", x / 1000, x.abs() % 1000) };
    println!("FIELD_WITNESS_READ operand_digits={} witness_faces_right={right_w} witness_code_bits={} founding_faces_right={right_f} founding_code_bits={} ms={}", views.len(), bits(code_w), bits(code_f), started.elapsed().as_millis());
    // (i) the readers kept, the clock zeroed.
    let mut no_clock = witness.clone();
    no_clock.theta[l.pace..].iter_mut().for_each(|v| *v = 0);
    let (_, _, g1) = covector(&no_clock, realization)?;
    let descent1: Vec<i128> = g1[pace3.clone()].iter().map(|&v| -v).collect();
    let toward1: Vec<i128> = theta(&witness)[pace3.clone()].to_vec();
    // The rate's route: digits' and inside words' sums and counts, and the squares' sum (exact, unbounded).
    let mut route: (i128, u64, i128, u64, BigInt) = (0, 0, 0, 0, BigInt::from(0));
    for region in &views {
        let bytes = codec.decode(region.classes);
        let x0 = no_clock.opening(region).map_err(|e| e.to_string())?;
        for t in 0..region.classes.len() - 1 {
            let dk: i128 = descent1.iter().zip(&x0[t * dw..(t + 1) * dw]).map(|(&gc, &x)| (gc * x as i128) >> 16).sum();
            route.4 += BigInt::from(dk) * BigInt::from(dk);
            let letter = |u: usize| bytes.get(u).is_some_and(|b| b.is_ascii_alphabetic());
            if codec.is_digit(region.classes[t]) {
                route.0 += dk;
                route.1 += 1;
            } else if t > 0 && letter(t) && letter(t - 1) {
                route.2 += dk;
                route.3 += 1;
            }
        }
    }
    let rms = (&route.4 / BigInt::from((route.1 + route.3).max(1))).sqrt().max(BigInt::from(1));
    let gap = (BigInt::from(route.0 / route.1.max(1) as i128 - route.2 / route.3.max(1) as i128) * BigInt::from(1_000_000)) / rms;
    println!("FIELD_WITNESS_CLOCK head=3 cosine_to_witness={} gap_digits_less_inside_words_of_rms={gap}", cosine(&descent1, &toward1));
    // (ii) the clock kept, the readers the founding's.
    let mut no_readers = witness.clone();
    for r in &readers {
        no_readers.theta[r.clone()].copy_from_slice(&founding.theta[r.clone()]);
    }
    let (_, _, g2) = covector(&no_readers, realization)?;
    for h in [0usize, 3] {
        let n = declaration.modes;
        let rows: Vec<std::ops::Range<usize>> = (0..n).flat_map(|li| [h * n + li, m + h * n + li]).flat_map(|o| [l.q + o * dw..l.q + (o + 1) * dw, l.q_bias + o..l.q_bias + o + 1, l.probe + o * dw..l.probe + (o + 1) * dw, l.probe_bias + o..l.probe_bias + o + 1]).collect();
        let descent: Vec<i128> = gather(&g2, &rows).into_iter().map(|v| -v).collect();
        let toward: Vec<i128> = gather(&theta(&witness), &rows).iter().zip(gather(&theta(&founding), &rows)).map(|(&w, f)| w - f).collect();
        println!("FIELD_WITNESS_READERS head={h} cosine_to_witness={}", cosine(&descent, &toward));
    }
    let lt = codec.encode(b"<").map_err(|e| e.to_string())?[0];
    let digit: Vec<bool> = (0..codec.alphabet()).map(|c| codec.is_digit(c)).collect();
    let mut census = [0u64; 6];
    for region in &views {
        let Some(t) = (0..region.classes.len().saturating_sub(2)).find(|&t| region.classes[t] == lt && region.classes[t + 1] == lt) else { continue };
        if t + 2 >= region.classes.len() {
            continue;
        }
        for (acc, v) in census.iter_mut().zip(no_readers.anchor_census(region, t + 2, 3, 5, &digit, &g2).map_err(|e| e.to_string())?) {
            *acc += v;
        }
    }
    println!("FIELD_WITNESS_ANCHOR head=3 opposing={} near_silent={} aligned={} silent_driven_to_oppose={} silent_driven_to_align={} digit_sources={}", census[0], census[1], census[2], census[3], census[4], census[5]);
    // (iii) the witness moved a small keyed step on the clock and the readers.
    let mut moved = witness.clone();
    let mut step = vec![0i128; witness.theta.len()];
    let entries: Vec<usize> = std::iter::once(pace3.clone()).chain(readers.iter().cloned()).flatten().collect();
    let tail = keys.len().saturating_sub(4 * entries.len() + 8);
    for (k, &at) in entries.iter().enumerate() {
        let word = &keys[tail + 4 * k..tail + 4 * k + 4];
        // A step of about one part in 2^10 of the material's unit (`2^14` on `2^(−24)`), signed by the key.
        let delta = (i32::from_be_bytes([word[0], word[1], word[2], word[3]]) >> 18) as i128;
        moved.theta[at] = i32::try_from(moved.theta[at] as i128 + delta).map_err(|_| "a moved entry outside 32 bits")?;
        step[at] = delta;
    }
    let (code_m, _, g3) = covector(&moved, realization)?;
    let ranges: Vec<std::ops::Range<usize>> = std::iter::once(pace3).chain(readers).collect();
    let back: Vec<i128> = gather(&step, &ranges).into_iter().map(|v| -v).collect();
    let descent3: Vec<i128> = gather(&g3, &ranges).into_iter().map(|v| -v).collect();
    println!("FIELD_WITNESS_BASIN moved_code_bits={} cosine_back={}", bits(code_m), cosine(&descent3, &back));
    // (iv) the temperatures' covector in their own chart (`log₂ T`, §16.12), at the witness's charts and clock with
    // its temperatures at 4 (`ℓ = 2`), and at the founding: whether descent raises each head's and kind's `ℓ`.
    let mut cool = witness.clone();
    for at in [l.temper + 2 * 3, l.temper + 2 * 3 + 1, l.temper + 1] {
        cool.theta[at] = 2 << 24;
    }
    for (name, field) in [("witness_t4", &cool), ("founding", &founding)] {
        let (code, right, g4) = covector(field, realization)?;
        let descent: Vec<String> = (0..declaration.heads).map(|h| format!("{h}:{}/{}", -g4[l.temper + 2 * h], -g4[l.temper + 2 * h + 1])).collect();
        println!("FIELD_WITNESS_TEMPER at={name} faces_right={right} code_bits={} descent_on_log_t_class/listen={}", bits(code), descent.join(","));
    }
    println!("FIELD_WITNESS_DONE ms={}", started.elapsed().as_millis());
    Ok(())
}

/// `log₂ x` in thousandths of a bit, `x ≥ 1`: the whole bits by the leading zeros and sixteen fraction bits by
/// squaring the mantissa on `2^(−62)` (a reading's chart, exact integers).
pub(super) fn log2_milli(x: u128) -> i64 {
    if x == 0 {
        return 0;
    }
    let whole = 127 - x.leading_zeros() as i64;
    let mut m: u128 = if whole >= 62 { x >> (whole - 62) } else { x << (62 - whole) };
    let mut frac = 0i64;
    for _ in 0..16 {
        m = (m * m) >> 62;
        frac <<= 1;
        if m >= 1u128 << 63 {
            m >>= 1;
            frac |= 1;
        }
    }
    whole * 1000 + ((frac * 1000 + (1 << 15)) >> 16)
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
        assert!(codec.is_digit(codec.encode(b"5").unwrap()[0]) && !codec.is_digit(codec.encode(b"a").unwrap()[0]));
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

    #[test]
    fn problems_split_at_blank_lines() {
        let text = b"Q one?\nA one.\n#### 1\n\nQ two?\nA two #### 2\n";
        let problems = problems_of(text);
        assert_eq!(problems.len(), 2);
        assert_eq!(problems[0], (b"Q one?".to_vec(), b"A one.\n#### 1".to_vec()));
        assert_eq!(problems[1].1, b"A two #### 2".to_vec());
    }

    #[test]
    fn coupling_reads_both_strands_alike() {
        let h = [1usize, 2, 3, 9, 4, 5];
        let t = [7usize, 1, 2, 3, 4, 5];
        let c = coupling(&h, &t);
        assert_eq!((c.lambda, c.friction), (5, 2));
        assert_eq!(c.plateaus, vec![(3, 1), (2, 0)]);
        let back = coupling(&t, &h);
        assert_eq!((back.lambda, back.friction), (5, 2));
        let mut lags: Vec<(usize, i64)> = back.plateaus.iter().map(|&(r, l)| (r, -l)).collect();
        lags.sort();
        let mut forward = c.plateaus.clone();
        forward.sort();
        assert_eq!(lags, forward);
    }

    #[test]
    fn calculations_are_read_at_their_equals() {
        let answer = b"He has <<2*3=6>>6 and <<6+1=7>>7.";
        let found = calculations_of(answer);
        assert_eq!(found.len(), 2);
        assert_eq!(found[0].0, b"2*3");
        assert_eq!(&answer[..found[0].1], b"He has <<2*3=");
        assert_eq!(found[1].0, b"6+1");
    }

    /// The commands end to end on the host: a toy passage trains two laps, rests, continues from
    /// its rested learner, refuses to write over a run, and releases its held problems with their
    /// marks and coupling reads.
    #[test]
    fn the_field_trains_rests_continues_and_releases() {
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
        let args: Vec<String> = ["release-field", &at("A/STATE.1"), &state_sha, &at("A/CODEC"), &codec_sha, &units, &units_sha, &held, &held_sha, "2", "3", "600000", &at("R")].iter().map(|s| s.to_string()).collect();
        release(&args, &mut host()).expect("release");
        let read_in = |run: &str, name: &str| String::from_utf8(std::fs::read(dir.join(run).join(name)).expect("read")).unwrap();
        let read = |name: &str| read_in("R", name);
        assert_eq!(read("FREE.tsv").lines().count(), 2);
        assert_eq!(read("MARKS.tsv").lines().count(), 2, "one calculation a held problem");
        let coupling = read("COUPLING.tsv");
        assert_eq!(coupling.lines().count(), 3);
        for row in coupling.lines().skip(1) {
            let cells: Vec<usize> = row.split('\t').take(5).map(|c| c.parse().unwrap()).collect();
            assert_eq!(cells[1] + cells[2], 2 * cells[3] + cells[4], "F* = |H| + |T| - 2 lambda");
        }
        assert!(release(&args, &mut host()).is_err(), "a release's directory is never written over");
        // A release stopped at its deadline still writes a row a problem.
        let mut stopped = args.clone();
        stopped[11] = "1".to_string();
        stopped[12] = at("Q");
        release(&stopped, &mut host()).expect("stopped release");
        assert_eq!(read_in("Q", "FREE.tsv").lines().count(), 2);
        let text: Vec<String> = ["release-field-text", &at("A/STATE.1"), &state_sha, &at("A/CODEC"), &codec_sha, &units, &units_sha, &held, &held_sha, "1", "2", "600000"].iter().map(|s| s.to_string()).collect();
        release_text(&text, &mut host()).expect("release text");
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn tails_meet_every_octave_within_their_room() {
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

    #[test]
    fn shapes_open_a_site_and_meet_both_halves() {
        let (question, sites, answer) = (3usize, 12usize, 6usize);
        let (mut masked, mut fronts) = (0, 0);
        let (mut places, mut rungs) = (std::collections::BTreeSet::new(), std::collections::BTreeSet::new());
        for draw in 0..2048 {
            match shape(7, draw, question, sites, answer) {
                Shape::Masked(m) => {
                    assert!(m.iter().any(|&u| u));
                    assert_eq!(m.len(), sites);
                    masked += 1;
                }
                Shape::Front(f) => {
                    assert!(f.front >= question && f.front - question <= answer && f.rung <= 22);
                    assert_eq!(f.cut, (f.front + BAND).min(sites));
                    assert_eq!(f.open.len(), f.cut);
                    assert!(f.open[..question].iter().all(|&u| !u), "the question is known");
                    assert!(f.open[f.front..].iter().all(|&u| u), "the band is open");
                    assert!(f.open.iter().any(|&u| u));
                    places.insert(f.front - question);
                    rungs.insert(f.rung);
                    fronts += 1;
                }
            }
        }
        assert!(masked > 512 && fronts > 512, "{masked} {fronts}");
        assert_eq!(places.len(), answer + 1, "every place of the front, the answer's end among them");
        assert_eq!(rungs.len(), 23, "every rung of the pump");
        // A region that ends at the front has no band; one prefix site is opened.
        for draw in 0..512 {
            if let Shape::Front(f) = shape(7, draw, question, question + answer, answer) {
                assert!(f.open.iter().any(|&u| u) && f.cut <= question + answer);
            }
        }
    }

    /// A front region's prefix is opened by the masks' own draws: the site `t` is open exactly where
    /// the keyed draw of that site, `mix(seed, draw ^ ((t + 1) << 32))`, falls below the density `τ`
    /// the draw's head gives, as the masked shape of the same draw opens it.
    #[test]
    fn a_front_opens_the_prefix_where_a_mask_would() {
        let (question, sites, answer) = (3usize, 40usize, 20usize);
        let (mut checked, mut dense) = (0, 0);
        for draw in 0..512u64 {
            let head = mix(7, draw);
            let tau = ((head >> 1) & 0xFFFF) + 1;
            let Shape::Front(f) = shape(7, draw, question, sites, answer) else { continue };
            for t in question..f.front {
                assert_eq!(f.open[t], (mix(7, draw ^ ((t as u64 + 1) << 32)) & 0xFFFF) < tau, "site {t} of draw {draw}");
            }
            checked += 1;
            dense += usize::from((question..f.front).any(|t| f.open[t]));
        }
        assert!(checked > 128 && dense > 32, "{checked} {dense}");
    }

    /// Read 2 of a front region on a face the logits give: the prefix's open site at `β = 2^r`,
    /// locked where it holds a majority (a tie, or a half, is not one), the band at `β = 1` and never
    /// locked however sharp, the known site carrying nothing.
    #[test]
    fn read_2_carries_the_prefix_at_its_rung_locked_and_the_band_soft() {
        let d = FieldDeclaration { alphabet: 3, width: 4, heads: 1, modes: 1, still: 1, contacts: 2, ticks: 1, frames: 1, reach: 8, clocks: 0 };
        let field = Field::found(d, &(0..1u64 << 10).flat_map(|i| mix(3, i).to_be_bytes()).collect::<Vec<_>>()).unwrap();
        let z = |l: [i64; 3]| Some(l.iter().map(|&v| v << 16).collect::<Vec<i64>>());
        let logits = vec![None, None, z([0, 1, 0]), z([2, 2, 0]), z([0, 5, 0]), z([1, 1, 0]), z([0, 0, 0])];
        for rung in [0u32, 3, 22] {
            let front = Front { front: 4, rung, cut: 7, open: vec![false, false, true, true, true, true, true] };
            let (faces, locked) = front_faces(&field, &front, &logits).unwrap();
            assert_eq!(faces.len(), 7);
            assert!(faces[0].is_none() && faces[1].is_none(), "the question carries nothing");
            for t in 2..4 {
                assert_eq!(faces[t], Some(shares(&field.tempered(logits[t].as_ref().unwrap(), 1 << rung))), "prefix site {t} at 2^{rung}");
            }
            for t in 4..7 {
                assert_eq!(faces[t], Some(shares(&field.tempered(logits[t].as_ref().unwrap(), 1))), "band site {t} at 1");
            }
            // Site 2: exactly half at β = 1 (no majority), the majority from rung 1 on. Site 3: a tie of
            // two classes, a majority at no rung. The band: never locked.
            assert_eq!(locked, vec![false, false, rung > 0, false, false, false, false], "rung {rung}");
        }
        let missing = Front { front: 4, rung: 1, cut: 7, open: vec![false, false, true, true, true, true, true] };
        assert!(front_faces(&field, &missing, &logits[..5]).is_err(), "an open site the first read did not return");
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
        let d = FieldDeclaration { alphabet: codec.alphabet(), width: 8, heads: 2, modes: 3, still: 1, contacts: 4, ticks: 2, frames: 2, reach, clocks: 0 };
        let keys: Vec<u8> = (0..1u64 << 13).flat_map(|i| mix(0x5EED, i).to_be_bytes()).collect();
        FieldLearner::new(Field::found(d, &keys).unwrap(), 4)
    }

    /// The regions `section_regions` formed for `members` from `first` on, against the draws they
    /// stand on: a masked member one region, a front member two. Read 1 is the truth cut at the band
    /// with the keyed open sites unresolved and nothing carried; read 2 is the same region with each
    /// open site carrying its read-1 face (read now under `field`) at its rung, the prefix's locked
    /// where it holds a majority, and the band's soft. Returns the front members met and the locks.
    fn check_regions(codec: &FieldCodec, problems: &Problems, members: &[usize], seed: u64, first: u64, regions: &[TrainRegion], field: &Field) -> (usize, usize) {
        let (mut k, mut fronts, mut locks) = (0, 0, 0);
        for (n, &i) in members.iter().enumerate() {
            let (q, a, _) = &problems[i];
            let draw = first + n as u64 + 1;
            let length = q.len() + a.len() + tail(seed, draw, codec.answer - a.len());
            let truth = region_classes(codec, q, a, length);
            match shape(seed, draw, q.len(), length, a.len() + 1) {
                Shape::Masked(mask) => {
                    assert_eq!(regions[k], TrainRegion::plain(truth, mask));
                    k += 1;
                }
                Shape::Front(f) => {
                    let (one, two) = (&regions[k], &regions[k + 1]);
                    k += 2;
                    fronts += 1;
                    assert_eq!(one, &TrainRegion::plain(truth[..f.cut].to_vec(), f.open.clone()), "read 1: the truth cut at the band, the open sites unresolved");
                    assert_eq!((&two.classes, &two.unresolved), (&one.classes, &one.unresolved), "read 2 is read 1's region");
                    let z = field.logits(&view_of(one)).unwrap();
                    assert_eq!(two.faces.len(), f.cut);
                    assert_eq!(two.locked.len(), f.cut);
                    for t in 0..f.cut {
                        if !f.open[t] {
                            assert!(two.faces[t].is_none() && !two.locked[t]);
                            continue;
                        }
                        let prefix = t < f.front;
                        let face = field.tempered(z[t].as_ref().unwrap(), if prefix { 1 << f.rung } else { 1 });
                        assert_eq!(two.faces[t], Some(shares(&face)), "site {t} carries its read-1 face at {}", if prefix { f.rung } else { 0 });
                        let majority = face.masses.iter().max().unwrap() * 2 > face.total;
                        assert_eq!(two.locked[t], prefix && majority, "site {t}");
                        locks += usize::from(two.locked[t]);
                    }
                    field.faces(&view_of(two)).unwrap();
                }
            }
        }
        assert_eq!(k, regions.len());
        (fronts, locks)
    }

    /// The regions of a section on the toy passage are the draws' (a masked member one region, a front
    /// member read 1 and read 2), and the field accepts them, locks included. The learner has read six
    /// sections first: a founded field's readout is dormant, its faces flat, and no flat face holds a
    /// majority at any rung.
    #[test]
    fn a_front_member_is_two_regions_read_1_and_read_2() {
        let (codec, problems) = toy();
        let members = [0usize, 1, 2, 3];
        let mut trained = toy_learner(&codec, &problems);
        let mut draw = 1000u64;
        for _ in 0..6 {
            let (regions, _) = section_regions(&codec, &problems, &members, 11, &mut draw, &mut trained, &mut host()).unwrap();
            trained.section_realized(&views_of(&regions), &mut host()).unwrap();
        }
        let (mut fronts, mut locks) = (0, 0);
        for base in 0..24u64 {
            let mut learner = trained.clone();
            let held = learner.holds_step();
            let first = 100 * base;
            let mut draw = first;
            let (regions, next) = section_regions(&codec, &problems, &members, 11, &mut draw, &mut learner, &mut host()).unwrap();
            assert!(next.is_some() == held && draw == first + 4);
            let lengths = region_lengths(&codec, &problems, &members, 11, &mut { first });
            assert_eq!(lengths, regions.iter().map(|r| r.classes.len()).collect::<Vec<_>>(), "the projection's lengths are the regions'");
            let (f, l) = check_regions(&codec, &problems, &members, 11, first, &regions, &learner.field);
            fronts += f;
            locks += l;
            for r in &regions {
                learner.field.logits(&view_of(r)).unwrap();
            }
        }
        assert!(fronts > 16 && locks > 0, "{fronts} {locks}");
    }

    /// The held step is read on the regions training compares (the masks and read 1) before read 2's
    /// mixtures are read, so a front member's read 2 carries the faces of the material that stands.
    #[test]
    fn the_held_step_is_read_before_read_2_carries_its_mixtures() {
        let (codec, problems) = toy();
        let members = [0usize, 1, 2, 3];
        let mut learner = toy_learner(&codec, &problems);
        let (mut draw, mut held, mut read) = (0u64, false, 0usize);
        for section in 0..8 {
            let first = draw;
            let (regions, next) = section_regions(&codec, &problems, &members, 5, &mut draw, &mut learner, &mut host()).unwrap();
            assert_eq!(next.is_some(), held, "section {section}: a step held is a step read");
            assert!(!learner.holds_step(), "the held step is read before the regions are formed");
            read += usize::from(next.is_some());
            check_regions(&codec, &problems, &members, 5, first, &regions, &learner.field);
            learner.section_realized(&views_of(&regions), &mut host()).unwrap();
            held = learner.holds_step();
        }
        assert!(read > 0, "a step was held and read");
    }

    #[test]
    fn the_held_read_prints_millionths_and_the_question_effect() {
        assert_eq!(micro_bits(3 << 20, 2), "1.500000");
        assert_eq!(micro_bits(-(3 << 20), 2), "-1.500000");
        assert_eq!(micro_bits(1, 1), "0.000001");
        assert_eq!(micro_bits(0, 0), "-");
        let mut held = [(0i64, 0usize); 9];
        held[3] = (5 * 4 << 20, 4);
        held[6] = (5 * 4 << 20, 4);
        held[6].0 += 4;
        let text = held_text(&held);
        assert!(text.contains("context=5.000000 ") && text.contains("foil=5.000001 ") && text.contains("question=0.000001 "), "{text}");
        assert!(text.contains("answer=- ") && text.contains("question_digits=-"), "{text}");
        assert_eq!(bits(held[3].0, 4), bits(held[6].0, 4), "the three-decimal reading cannot tell them apart");
    }

    /// A release's receipt names the sites reached and locked, the sweeps each was reached and
    /// locked, and the extent's reading; the locks of its last state are its locked sites'.
    #[test]
    fn a_receipt_names_the_front() {
        let r = Released {
            sites: vec![Some(1), None, Some(2)],
            reached: vec![Some(0), Some(0), Some(1)],
            lock_sweeps: vec![Some(2), None, Some(3)],
            rungs: vec![4, 0, 1],
            counters: vec![Some((2, 3 << 16)), None, Some((1, 5 << 16))],
            open: 1,
            extent: Some((3, 4, false)),
            classes: vec![0; 6],
            start: 2,
            ..Released::default()
        };
        let text = receipt_text(&r);
        assert!(text.contains("sites=3 open=1 reached=3 locked=2 reach_sweep_quartiles=0/0/0/0/1 lock_sweep_quartiles=2/2/2/2/3 extent=3@4:void "), "{text}");
        assert_eq!(locks_of(&r), vec![false, false, true, false, true, false]);
        assert_eq!(extent_text(Some((7, 2, true))), "7@2:bound");
        assert_eq!(extent_text(None), "-");
        let mut sum = FrontReceipt::default();
        sum.add(&r);
        sum.add(&Released { extent: Some((5, 6, true)), ..r.clone() });
        sum.add(&Released { extent: None, ..r });
        assert_eq!(sum.extents(), "extents_void=1 extents_bound=1 extents_unread=1 extent_site_quartiles=3/3/3/3/5 extent_sweep_quartiles=4/4/4/4/6");
    }

    /// An open site is written as the one byte no class writes, and the answer ends at its first
    /// locked void.
    #[test]
    fn a_release_writes_its_open_sites_open() {
        let problems = vec![(b"Q?".to_vec(), b"ab".to_vec())];
        let codec = FieldCodec::found(Units::bytes(), &problems).unwrap();
        let [a, b] = [codec.encode(b"a").unwrap()[0], codec.encode(b"b").unwrap()[0]];
        let (text, at) = codec.decode_open(&[Some(a), None, Some(b), Some(codec.void()), Some(a)], OPEN_SITE);
        assert_eq!(text, b"a\0b");
        assert_eq!(at, vec![0, 1, 2, 3]);
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

/// [agent-inferred, November 1] **The crib terrain**: `crib-terrain SEED TRAIN DEV OUT_TRAIN
/// OUT_DEV` writes two passages in the GSM8K passage form (a question line, its answer lines, a
/// blank line) whose answers are read from their questions and nowhere else. A question is 48 to 79
/// words of one to three syllables drawn from twenty, with two or three whole numbers of one to
/// three digits at distinct word places; its answer sums them in the order the question writes
/// them, one calculation a sum (`<<a+b=s>>s`, then `<<s+c=t>>t`), and ends `#### total`. The words
/// carry nothing the answer needs, so the answer's first calculation is drawn from the question's
/// numbers only where the field reads them across the question, a median of about 180 bytes back
/// (GSM8K's 190). The terrain writes its truth with an exact routine; the field meets only its
/// classes, as it meets GSM8K's. Why (the seventh reading, November 1): the question told the held
/// answers' digits 0.021 bits on GSM8K, where the operands are both far and few, so whether the
/// field can read a number across a question at all is read here first, where nothing else in the
/// passage can stand in for it. The draws are the exterior mixer's ([`mix`]) of `SEED` and the
/// problem's index, the held passage's indices past `2^40`.
pub(super) fn crib_terrain(args: &[String]) -> Result<()> {
    if args.len() != 6 {
        return Err("crib-terrain SEED TRAIN DEV OUT_TRAIN OUT_DEV".into());
    }
    let seed: u64 = args[1].parse()?;
    let (train, dev) = (positive(&args[2])?, positive(&args[3])?);
    for (path, count, base) in [(&args[4], train, 0u64), (&args[5], dev, 1u64 << 40)] {
        let mut text = Vec::new();
        for i in 0..count as u64 {
            let (q, a) = crib_problem(seed, base + i);
            text.extend(q);
            text.push(b'\n');
            text.extend(a);
            text.extend(b"\n\n");
        }
        write_new(Path::new(path.as_str()), &text)?;
    }
    println!("CRIB_TERRAIN seed={seed} train={train} dev={dev}");
    Ok(())
}

fn crib_problem(seed: u64, problem: u64) -> (Vec<u8>, Vec<u8>) {
    const SYLLABLES: [&[u8]; 20] = [b"ba", b"de", b"ki", b"lo", b"mu", b"na", b"pe", b"ri", b"so", b"tu", b"va", b"we", b"xo", b"yi", b"za", b"ha", b"fe", b"gi", b"jo", b"cu"];
    let mut drawn = 0u64;
    let mut draw = |m: u64| {
        drawn += 1;
        mix(seed, problem << 16 | drawn) % m
    };
    let words = 48 + draw(32) as usize;
    let count = 2 + draw(2) as usize;
    let mut values = Vec::with_capacity(count);
    for _ in 0..count {
        let low = 10u64.pow(draw(3) as u32);
        values.push(low + draw(9 * low));
    }
    let mut places: Vec<usize> = Vec::with_capacity(count);
    while places.len() < count {
        let place = draw(words as u64) as usize;
        if !places.contains(&place) {
            places.push(place);
        }
    }
    places.sort_unstable();
    let mut question = Vec::new();
    let mut next = 0usize;
    for w in 0..words {
        if w > 0 {
            question.push(b' ');
        }
        if next < count && places[next] == w {
            question.extend(values[next].to_string().bytes());
            next += 1;
        } else {
            for _ in 0..1 + draw(3) {
                question.extend_from_slice(SYLLABLES[draw(20) as usize]);
            }
        }
    }
    question.push(b'?');
    let mut answer = Vec::new();
    let mut total = values[0];
    for (j, &v) in values.iter().enumerate().skip(1) {
        if j > 1 {
            answer.push(b'\n');
        }
        answer.extend(format!("<<{total}+{v}={}>>{}", total + v, total + v).bytes());
        total += v;
    }
    answer.extend(format!("\n#### {total}").bytes());
    (question, answer)
}
