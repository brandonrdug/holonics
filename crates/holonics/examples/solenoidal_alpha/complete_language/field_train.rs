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
use holonics::hnn::tower::field::{shares, Field, FieldDeclaration, FieldLearner, FieldNext, FieldRealization, FieldReceipt, HostField, Region, Released, ReleaseSweep, Shares};
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

/// A region's shape: a keyed completion mask over the whole region, or the release's second sweep
/// ([`second_sweep`], its mixtures read from the field, [`section_regions`]).
pub(super) enum Shape {
    Masked(Vec<bool>),
    Second,
}

/// [agent-inferred, November 1] A region's shape: with even odds the whole region's sites, each
/// unresolved with probability `τ` (`τ` uniform on `(0, 1]` on `2^(−16)`, at least one site
/// unresolved), or the release's second sweep. Why the second (the dispersing field's §5): it is the
/// first state a release meets after its opening and the farthest from the masks; later sweeps
/// sharpen the mixtures toward the classes the masks show, so they lie between the two states
/// training reads. The shape it replaces resolved the answer's sites at their true classes in the
/// order the question told most about first, so any other release met states the field never
/// trained on.
pub(super) fn shape(seed: u64, draw: u64, sites: usize) -> Shape {
    let head = mix(seed, draw);
    let low = (head >> 1) & 0xFFFF;
    if head & 1 == 0 {
        return Shape::Second;
    }
    let tau = low + 1;
    let mut out: Vec<bool> = (0..sites).map(|t| (mix(seed, draw ^ ((t as u64 + 1) << 32)) & 0xFFFF) < tau).collect();
    if !out.iter().any(|&u| u) {
        out[mix(seed, draw.wrapping_add(1)) as usize % sites] = true;
    }
    Shape::Masked(out)
}

/// [definition; agent-inferred, November 1] **The release's second sweep** (the dispersing field's
/// §5): read 1 opens every site from `question` on, on the unresolved row, as the release opens, and
/// its logits (`logits`) give the extent as the release reads it ([`Field::extent`]): the region is
/// cut one site past the earliest resolved void, that site resolved at the void. Read 2 opens each
/// content site on the mixture of its read-1 face at `β = 1` over every class but the void
/// ([`Field::content_face`], as the release carries it), held as data with no covector through it,
/// and reads and compares them all at their own classes. The covector of read 2 reaches the encodings
/// through the mixture, `E(a)` weighted by `p(a)`. Why the cut (the build's review, November 1): a
/// release's sweeps run on the cut region, so a second sweep without it was a state no release meets.
pub(super) fn second_sweep(field: &Field, classes: &mut Vec<usize>, logits: &[Option<Vec<i64>>], question: usize, void: usize) -> (Vec<bool>, Vec<Option<Shares>>) {
    let end = field.extent(logits, question, void);
    if let Some(end) = end {
        classes.truncate(end + 1);
        classes[end] = void;
    }
    let content = end.unwrap_or(classes.len());
    let open: Vec<bool> = (0..classes.len()).map(|t| t >= question && t < content).collect();
    let carried = (0..classes.len()).map(|t| if open[t] { logits[t].as_ref().map(|z| shares(&field.content_face(z, 1, void))) } else { None }).collect();
    (open, carried)
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

/// The regions' lengths `members` would read from `draw` on (each draw counted as
/// [`section_regions`] counts it).
pub(super) fn region_lengths(codec: &FieldCodec, problems: &Problems, members: &[usize], seed: u64, draw: &mut u64) -> Vec<usize> {
    members
        .iter()
        .map(|&i| {
            let (q, a, _) = &problems[i];
            *draw += 1;
            q.len() + a.len() + tail(seed, *draw, codec.answer - a.len())
        })
        .collect()
}

/// A training region: its classes, its open sites and its carried faces (empty where none).
pub(super) type TrainRegion = (Vec<usize>, Vec<bool>, Vec<Option<Shares>>);

/// The regions as the field reads them.
pub(super) fn views_of(regions: &[TrainRegion]) -> Vec<Region<'_>> {
    regions.iter().map(|(c, u, f)| Region { classes: c, unresolved: u, faces: f, locked: &[] }).collect()
}

/// **A section's regions as `train-field` forms them**: each member's classes (its question, its
/// answer and a keyed void tail) and its shape ([`shape`]). The step the learner holds is read first
/// on the section's masked regions, which it was not fit on (on the second sweeps' first reads only
/// where the section has no masked region), so the second sweeps' mixtures are read from the material
/// that stands after it (one more read of those regions, through `realization`); the held step's read
/// is returned. Why that order (the build's review, November 1): read under the stepped material
/// before its read, a refused step left read 2 carrying mixtures of a material that no longer stood,
/// and the step was read on regions it had partly formed. Why the masked regions (the crib probe of
/// November 1): read on the masked regions and the second sweeps' first reads together, the step was
/// judged on the release's opening, every answer site on the unresolved row, a state training never
/// compares, and 205 of 248 held steps were refused in the second lap while the withheld problems'
/// code stood still at 4.55 bits.
pub(super) fn section_regions(codec: &FieldCodec, problems: &Problems, members: &[usize], seed: u64, draw: &mut u64, learner: &mut FieldLearner, realization: &mut dyn FieldRealization) -> Result<(Vec<TrainRegion>, Option<FieldNext>)> {
    let mut regions: Vec<TrainRegion> = Vec::with_capacity(members.len());
    let mut states: Vec<(usize, usize)> = Vec::new();
    for &i in members {
        let (q, a, _) = &problems[i];
        *draw += 1;
        let length = q.len() + a.len() + tail(seed, *draw, codec.answer - a.len());
        let classes = region_classes(codec, q, a, length);
        match shape(seed, *draw, length) {
            Shape::Masked(mask) => regions.push((classes, mask, Vec::new())),
            Shape::Second => {
                states.push((regions.len(), q.len()));
                regions.push((classes, Vec::new(), Vec::new()));
            }
        }
    }
    for &(k, q) in &states {
        regions[k].1 = (0..regions[k].0.len()).map(|t| t >= q).collect();
    }
    let next = if learner.holds_step() {
        let masked: Vec<Region> = views_of(&regions).into_iter().enumerate().filter(|(k, _)| !states.iter().any(|&(s, _)| s == *k)).map(|(_, r)| r).collect();
        let on = if masked.is_empty() { views_of(&regions) } else { masked };
        learner.read_step_on(&on, realization).map_err(|e| e.to_string())?.1
    } else {
        None
    };
    if states.is_empty() {
        return Ok((regions, next));
    }
    let logits = {
        let views: Vec<Region> = states.iter().map(|&(k, _)| Region { classes: &regions[k].0, unresolved: &regions[k].1, faces: &[], locked: &[] }).collect();
        realization.read_logits(&learner.field, &views).map_err(|e| e.to_string())?
    };
    for (&(k, q), logits) in states.iter().zip(&logits) {
        let mut classes = std::mem::take(&mut regions[k].0);
        let (open, carried) = second_sweep(&learner.field, &mut classes, logits, q, codec.void());
        regions[k] = (classes, open, carried);
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
    let views: Vec<Region> = regions.iter().map(|(c, u, _)| Region { classes: c, unresolved: u, faces: &[], locked: &[] }).collect();
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
    let views: Vec<Region> = regions.iter().map(|(c, u)| Region { classes: c, unresolved: u, faces: &[], locked: &[] }).collect();
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

fn held_text(held: &[(i64, usize); 9]) -> String {
    format!(
        "answer={} digits={} text={} classes={} context={} context_digits={} context_text={} context_classes={} foil={} foil_digits={} foil_text={}",
        bits(held[0].0, held[0].1),
        bits(held[1].0, held[1].1),
        bits(held[2].0, held[2].1),
        held[0].1,
        bits(held[3].0, held[3].1),
        bits(held[4].0, held[4].1),
        bits(held[5].0, held[5].1),
        held[3].1,
        bits(held[6].0, held[6].1),
        bits(held[7].0, held[7].1),
        bits(held[8].0, held[8].1)
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
/// only the two projections (before and after one growth); a second growth is held and the run
/// ends there (`FIELD_GROW_HELD`), and the keys are checked to cover that one growth before any
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
            let declaration = FieldDeclaration { alphabet: codec.alphabet(), width, heads, modes, still, contacts, ticks, frames: heads, reach };
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
    // The withheld problems' code after the lap before (at the opening, before any lap).
    let (code, sites, next) = unseen_read(&mut learner, &codec, &train_set, &unseen, seed, realization)?;
    println!("FIELD_UNSEEN lap=-1 code={} sites={sites} {} ms={}", bits(code, sites), next_text(next), started.elapsed().as_millis());
    let mut previous = (code, sites);
    let mut grown = false;
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
            let length = regions.iter().map(|(c, _, _)| c.len()).max().unwrap_or(0);
            let views = views_of(&regions);
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
        // [agent-inferred, November 1] The width is the trained body's (growth by copies, the
        // tower's law): when a lap leaves the withheld problems coding no fewer bits a site than
        // the lap before left them, the body has spent its width and grows by two before the next.
        if (code as i128) * (previous.1 as i128) >= (previous.0 as i128) * (unseen_sites as i128) && lap + 1 < laps {
            if grown {
                // A second growth has no projection in this run: the run rests at its last lap and
                // the next run projects the declaration grown again.
                println!("FIELD_GROW_HELD lap={lap} reason=a second growth has no projection ms={}", started.elapsed().as_millis());
                break;
            }
            learner = learner.widened(2, &keys).map_err(|e| e.to_string())?;
            grown = true;
            let d = learner.field.declaration;
            println!("FIELD_GROW lap={lap} width={} heads={} contacts={} rate={} material={} ms={}", d.width, d.heads, d.contacts, learner.rate_bits, learner.field.theta.len(), started.elapsed().as_millis());
        }
        previous = (code, unseen_sites);
    }
    Ok(())
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
/// `STOP_MS` ([`within`]): a set stopped there is returned as released and counted open. It writes
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
        "FIELD_RELEASE_RECEIPTS problems={} locked_whole={locked_whole} open_sites={open_sites} free_circulation={free_circulation} bound_circulation={bound} lock_margin_bits_quartiles={} lock_rungs={} landmark_problems={} landmark_digits={} landmark_on_question_digit={} landmark_same_class={} landmark_ms={}",
        held.len(),
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
        "FIELD_RELEASE free={} marks={} withheld={withheld} refused={refused} sweeps={sweeps} stop_ms={stop_ms} free_sweeps={} free_live={} free_open={} free_rung={} free_stopped={} marks_sweeps={} marks_live={} marks_open={} marks_rung={} marks_stopped={} released={sum_h} held={sum_t} lambda={sum_lambda} friction={sum_friction} ms={}",
        held.len(),
        marks_at.len(),
        free_last.done,
        free_last.live,
        free_last.open,
        free_last.rung,
        free_last.live > 0 && free_last.done < sweeps,
        marks_last.done,
        marks_last.live,
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

/// A release's receipt as one line: its sites and open sites, its free and bound circulation, the
/// quartiles of its locks' margins over their counters (in bits), its lock rungs and the sweeps
/// ridden at each rung.
fn receipt_text(r: &Released) -> String {
    let mut margins: Vec<i64> = r.counters.iter().flatten().map(|&(_, m)| m).collect();
    format!("sites={} open={} free_circulation={} bound_circulation={} lock_margin_bits_quartiles={} rungs={} ridden={}", r.sites.len(), r.open, r.free, r.bound, quartiles(&mut margins), rung_text(&r.rungs), ridden_text(&r.ridden))
}

/// The least, the quartiles and the most of margins on `2^(−16)` bits, each in whole bits (`-` where
/// none).
fn quartiles(margins: &mut [i64]) -> String {
    if margins.is_empty() {
        return "-".into();
    }
    margins.sort_unstable();
    let at = |q: usize| margins[(q * (margins.len() - 1)) / 4] >> 16;
    format!("{}/{}/{}/{}/{}", at(0), at(1), at(2), at(3), at(4))
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
        let region = Region { classes: &r.classes, unresolved: &unresolved, faces: &r.faces, locked: &[] };
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
    println!("FIELD_RELEASE_TEXT problems={} sweeps={} live={} open={} rung={} stopped={} ms={}", held.len(), last.done, last.live, last.open, last.rung, last.live > 0 && last.done < sweeps, started.elapsed().as_millis());
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
        assert!(codec.is_digit(codec.encode(b"5").unwrap()[0]) && !codec.is_digit(codec.encode(b"a").unwrap()[0]));
        assert!(codec.encode(b"~").is_err(), "a unit the passage never used");
        let back = FieldCodec::from_text(&codec.to_text(), Units::bytes()).unwrap();
        assert_eq!((back.used.clone(), back.answer), (codec.used.clone(), codec.answer));
        assert_eq!(codec.answer, codec.encode(&problems[0].1).unwrap().len() + 1);
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
        let train_text = b"Tom has 3 apples and buys 2 more. How many apples does he have?\nHe has <<3+2=5>>5 apples.\n#### 5\n\nTom has 7 apples and buys 1 more. How many apples does he have?\nHe has <<7+1=8>>8 apples.\n#### 8\n\nTom has 4 apples and buys 6 more. How many apples does he have?\nHe has <<4+6=10>>10 apples.\n#### 10\n\nTom has 9 apples and buys 0 more. How many apples does he have?\nHe has <<9+0=9>>9 apples.\n#### 9\n";
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
        let (mut masked, mut second) = (0, 0);
        for draw in 0..64 {
            match shape(7, draw, 12) {
                Shape::Masked(m) => {
                    assert!(m.iter().any(|&u| u));
                    assert_eq!(m.len(), 12);
                    masked += 1;
                }
                Shape::Second => second += 1,
            }
        }
        assert!(masked > 16 && second > 16, "{masked} {second}");
    }

    /// The release's second sweep: the extent cut where read 1's void resolves, that site resolved
    /// at the void and the sites past it gone; every content site open and carried as its read-1 face
    /// at `β = 1` over every class but the void, the question resolved and carried as nothing.
    #[test]
    fn the_second_sweep_is_cut_at_the_extent_and_carries_the_content_s_first_read() {
        let d = FieldDeclaration { alphabet: 3, width: 4, heads: 1, modes: 1, still: 1, contacts: 1, ticks: 1, frames: 1, reach: 8 };
        let field = Field::found(d, &(0..1u64 << 10).flat_map(|i| mix(3, i).to_be_bytes()).collect::<Vec<_>>()).unwrap();
        let z = |l: [i64; 3]| Some(l.iter().map(|&v| v << 16).collect::<Vec<i64>>());
        let logits = vec![None, None, z([0, 1, 0]), z([1, 0, 0]), z([0, 2, 3]), z([3, 0, 0]), z([4, 0, 0])];
        let mut classes = vec![1usize, 2, 1, 2, 0, 0, 0];
        let (open, carried) = second_sweep(&field, &mut classes, &logits, 2, 0);
        assert_eq!(classes, vec![1, 2, 1, 2, 0, 0], "cut one site past the first resolved void, at the void");
        assert_eq!(open, vec![false, false, true, true, true, false]);
        assert!(carried[..2].iter().all(Option::is_none) && carried[5].is_none());
        assert_eq!(carried[2], Some(vec![(1, 43691), (2, 21845)]), "the void left out of a content site's mixture");
        assert_eq!(carried[3], Some(vec![(1, 32768), (2, 32768)]));
        assert_eq!(carried[4], Some(vec![(1, 21845), (2, 43691)]));
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
