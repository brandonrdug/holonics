//! [definition; agent-inferred, October 25] **The tower hears one passage of text, image and
//! sound.** `tools/listener/compose.py` writes GSM8K problems, MNIST digits and LibriSpeech
//! utterances as sections of one passage, each a source through its boundary chart, the end letter,
//! a target and the end letter (`examples/listener/sections.rs`): text as its octets, an image as
//! its stroke, a recording as its half-cycles. The tower reads classes of a declared alphabet and
//! nothing else (`hnn::tower`, "Modality"), so the passage is classes: the octets and one end letter,
//! the alphabet's last class, which no octet writes. A class file holds each class as a big-endian
//! `u16`. The medium, the split and the section's direction are the composer's, never the field's.
//!
//! - `train-gated-tower-classes` trains the gated tower (the GSM8K working law) on a class passage,
//!   as `train-gated-tower` trains it on octets, its held-out read split by four exterior regions:
//!   GSM8K, strokes, half-cycles, and the numerals and transcripts paired with an image or sound.
//! - `read-tower-classes` reads a frozen tower over a held-out class passage and reports, per mark
//!   value, the code and the cells whose face's top class is the class that arrives; at the marks of
//!   a label read after its image, the label each image's face names first.
//! - `release-tower-classes` forks the rested tower at each prompt (a source passage and its end
//!   letter) and releases classes by agreeing exact draws until it releases the end letter or the
//!   declared count; each prompt draws from its own declared share of the keys, so the releases do
//!   not depend on their order. On a participating tower it first reads, at each prompt's closing
//!   end letter where the answer opens, every level's heads over the section's sites.
//!
//! Nothing here is text-, image- or sound-specific: a medium is only the chart that wrote its
//! classes, and a numeral is the same class whether it names a digit image or ends a GSM8K answer.
use super::tower_train::{agreement, count, fit, per, positive, roles_of, Joined, Reading, STATE_BUDGET};
use holonics::receiver::release::agreeing_class;
use super::*;
use holonics::hnn::tower::participation::ENTROPY_BITS;
use holonics::hnn::tower::realization::{HostPass, PassRealization, Slot};
use holonics::hnn::tower::READ_BITS;
use holonics::hnn::tower::{ContactLaw, NewsClock, TowerLearner, TurnLadder};
use rayon::prelude::*;

/// The held-out read's four exterior regions of a composed passage (`compose.py`'s roles).
const CLASS_REGIONS: [&str; 4] = ["gsm8k", "strokes", "cycles", "words"];
/// `compose.py`'s marks: 1 a label after its image, 2 a GSM8K answer, 3 a question, 4 a transcript
/// after its sound, 5 a stroke, 6 a half-cycle octet, 7 an end letter, 8 a numeral or transcript
/// heard before its image or sound.
const MARK_NAMES: [&str; 9] = ["none", "label", "answer", "question", "transcript", "stroke", "cycle", "end", "named"];

pub(super) fn classes_of(bytes: &[u8], alphabet: usize) -> Result<Vec<usize>> {
    if bytes.len() % 2 != 0 {
        return Err("a class file holds two bytes a class".into());
    }
    let classes: Vec<usize> = bytes.chunks(2).map(|b| u16::from_be_bytes([b[0], b[1]]) as usize).collect();
    if classes.iter().any(|&c| c >= alphabet) {
        return Err("a class outside the declared alphabet".into());
    }
    Ok(classes)
}

/// `train-gated-tower-classes ALPHABET TRAIN TRAIN_SHA DEV DEV_SHA DEV_ROLES DEV_ROLES_SHA KEYS
/// KEYS_SHA WIDTH MODES CONTACTS LEVELS STREAMS SECTION PASSES RATE_BITS OUT [FROM FROM_SHA]`; the
/// code is reported a class. `train-credited-tower-classes` takes the same arguments and its streams
/// carry their passage credit (`hnn.tower-passage-credit`); `train-target-tower-classes` carries the
/// credit and compares each face only where a target arrives ([`target_places`]);
/// `train-turned-tower-classes` trains the turned tower (`hnn.tower-turned-mode`), whose arriving
/// class turns each mode, so a mode can carry an accumulated relative change as its phase;
/// `train-scaled-tower-classes` founds the gated tower on the scaled turn ladder and
/// `train-two-ladder-tower-classes` on both ladders, half the bank each ([`TurnLadder`]);
/// `train-two-ladder-news-tower-classes` founds it so and joins the news clock `B = 8`, `r = 2`
/// ([`NewsClock`]), so each level above the first ticks on its own news and the grain its modes
/// move at is the tower's own (record `2026-10-27_THE_LEVELS_TICK_ON_THEIR_OWN_NEWS…`);
/// `train-two-ladder-participating-tower-classes` founds it so and joins participation over the
/// declared section, one head a rung of the first level
/// ([`holonics::hnn::tower::Tower::founded_participation`]), so each
/// site reads the section's earlier sites through the modes' own transport (record
/// `2026-10-28_ATTENTION_IS_THE_FIELDS_PARTICIPATION_…`); `train-two-ladder-news-participating-tower-classes`
/// joins the news clock and then participation, so each level's sites are its own ticks. A continued
/// learner keeps the participation it was founded with. `train-two-ladder-mutual-tower-classes` founds it so and
/// joins the mutual contact ([`holonics::hnn::tower::Tower::join_mutual_contact`]): each face is
/// compared with the target's own encoding through a learned contact, and both move (record
/// `2026-10-29_MUTUAL_CONTACT_…`).
///
/// [agent-inferred, October 25] The credit is what lets a section's target teach its source when the
/// pair is longer than the declared section: a stroke runs about 168 classes against sections of
/// 128, so without it a label's covector stops inside its image and never reaches the image's
/// start (the state at the label kept little of the image, the record's "state at the label").
pub(super) fn train(args: &[String], credit: bool, targets: bool, turned: bool, ladder: TurnLadder, news: Option<NewsClock>) -> Result<()> {
    train_realized(args, credit, targets, turned, ladder, news, &mut HostPass::default())
}

/// [`train`] with each section's forward and reverse run through `realization`
/// (`hnn::tower::realization`): the card's route (`holonics-cuda`'s `tower_pass` example) runs the
/// same passes on the card, and its saved learner is the host's.
pub(crate) fn train_realized(args: &[String], credit: bool, targets: bool, turned: bool, ladder: TurnLadder, news: Option<NewsClock>, realization: &mut dyn PassRealization) -> Result<()> {
    train_joined(args, credit, targets, turned, ladder, news, Joined::Nothing, ContactLaw::Rectifying, realization)
}

/// `train-two-ladder-participating-tower-classes`: [`train_realized`] on both turn ladders with
/// participation joined after the founding; `train-two-ladder-news-participating-tower-classes`
/// joins the race's news clock first, so each level's sites are its own ticks (record
/// `2026-10-29_A_COARSE_LEVELS_SITES_ARE_ITS_OWN_TICKS…`).
pub(crate) fn train_participating_realized(args: &[String], news: Option<NewsClock>, realization: &mut dyn PassRealization) -> Result<()> {
    train_joined(args, false, false, false, TurnLadder::Both, news, Joined::Participation, ContactLaw::Rectifying, realization)
}

/// `train-two-ladder-news-passage-tower-classes`: [`train_realized`] on both turn ladders under the
/// race's news clock, with the passage joined at the founding, so the contacts of every level the
/// clock holds read the passing current; `train-two-ladder-stacked-news-passage-tower-classes`
/// joins [`race_stacked_news_clock`] instead (record
/// `2026-10-29_A_CLOCKED_LEVELS_CONTACTS_HEAR_THE_PASSING_CURRENT…`, §7 and §8).
pub(crate) fn train_passage_realized(args: &[String], news: NewsClock, realization: &mut dyn PassRealization) -> Result<()> {
    train_joined(args, false, false, false, TurnLadder::Both, Some(news), Joined::Passage, ContactLaw::Rectifying, realization)
}

/// `train-two-ladder-stacked-news-packet-tower-classes`: [`train_passage_realized`] under
/// [`race_stacked_news_clock`] with the packets joined after the passage, so each clocked level's
/// push, gate and turn hear the packet its clock closed (record
/// `2026-10-30_A_CLOCKED_LEVEL_HEARS_THE_PACKET…`, §4).
pub(crate) fn train_packet_realized(args: &[String], news: NewsClock, realization: &mut dyn PassRealization) -> Result<()> {
    train_joined(args, false, false, false, TurnLadder::Both, Some(news), Joined::PassagePackets, ContactLaw::Rectifying, realization)
}

/// `train-two-ladder-stacked-news-heading-tower-classes`: [`train_packet_realized`] (the race's
/// C′) with the heading joined after the packets, so each clocked level reads its modes through
/// its own heading before each arrival and the heading meets the trace of the arrivals its next
/// tick closes (record `2026-10-30_THE_COARSE_LEVEL_HEADS_FOR_THE_TRACE_OF_WHAT_COMES_NEXT…`, §4).
pub(crate) fn train_heading_realized(args: &[String], realization: &mut dyn PassRealization) -> Result<()> {
    train_joined(args, false, false, false, TurnLadder::Both, Some(race_stacked_news_clock()), Joined::PassagePacketsHeading, ContactLaw::Rectifying, realization)
}

/// `train-two-ladder-stacked-news-heading-credited-tower-classes`: [`train_heading_realized`] with
/// every stream carrying the clocked levels' credit across its sections' edges (record
/// `2026-10-30_THE_COARSE_LEVEL_HEADS_FOR_THE_TRACE_OF_WHAT_COMES_NEXT…`, §22).
pub(crate) fn train_heading_credited_realized(args: &[String], realization: &mut dyn PassRealization) -> Result<()> {
    train_joined(args, true, false, false, TurnLadder::Both, Some(race_stacked_news_clock()), Joined::PassagePacketsHeading, ContactLaw::Rectifying, realization)
}

/// `train-two-ladder-stacked-news-heading-credited-every-level-tower-classes`:
/// [`train_heading_credited_realized`] with every level's credit carried, the arrival levels' and
/// the packet the last of them carries among it (record
/// `2026-10-30_THE_COARSE_LEVEL_HEADS_FOR_THE_TRACE_OF_WHAT_COMES_NEXT…`, §24).
pub(crate) fn train_heading_credited_every_level_realized(args: &[String], realization: &mut dyn PassRealization) -> Result<()> {
    train_joined(args, super::tower_train::Credit::From(0), false, false, TurnLadder::Both, Some(race_stacked_news_clock()), Joined::PassagePacketsHeading, ContactLaw::Rectifying, realization)
}

/// `train-two-ladder-stacked-news-packet-pair-tower-classes`: [`train_packet_realized`] (the race's
/// C′) with every contact the pair contact, founded on the same draws (record
/// `2026-10-30_THE_PAIR_CONTACT_IS_RACED…`, §3 acceptance 4).
pub(crate) fn train_packet_pair_realized(args: &[String], realization: &mut dyn PassRealization) -> Result<()> {
    train_joined(args, false, false, false, TurnLadder::Both, Some(race_stacked_news_clock()), Joined::PassagePackets, ContactLaw::Pair, realization)
}

/// `train-two-ladder-pair-tower-classes`: [`train_realized`] on both turn ladders with every
/// contact the pair contact ([`ContactLaw::Pair`]), so a contact can read a conjunction of two drives
/// off the same face, the law whose founded split grows the body (record
/// `2026-10-29_A_VALUE_IS_A_RADIX_MOVE…`, §2). Its second drive opens at zero material and unit
/// bias and draws no key, so it is founded on the same draws as the rectifying tower.
pub(crate) fn train_pair_realized(args: &[String], realization: &mut dyn PassRealization) -> Result<()> {
    train_joined(args, false, false, false, TurnLadder::Both, None, Joined::Nothing, ContactLaw::Pair, realization)
}

/// `train-two-ladder-split-tower-classes`: [`train_pair_realized`] with the contact field widened
/// by two at the founding and each section founding the pairs' splits (record
/// `2026-10-30_THE_PAIR_CONTACT_IS_RACED_BEFORE_ITS_SPLIT_FOUNDS…`, §4, §5 acceptance 6);
/// `train-two-ladder-dormant-split-tower-classes` widens it the same way and founds nothing, the
/// race's control. `CONTACTS` names the field before its widening; a founding run continues with
/// its learner and its directions (`PAIRED.<pass>`), the control with its learner alone.
pub(crate) fn train_split_realized(args: &[String], founding: bool, realization: &mut dyn PassRealization) -> Result<()> {
    let joined = if founding { Joined::Split } else { Joined::DormantSplit };
    train_joined(args, false, false, false, TurnLadder::Both, None, joined, ContactLaw::Pair, realization)
}

/// `train-two-ladder-mutual-tower-classes`: [`train_realized`] on both turn ladders with the mutual
/// contact joined at the founding.
pub(crate) fn train_mutual_realized(args: &[String], realization: &mut dyn PassRealization) -> Result<()> {
    train_joined(args, false, false, false, TurnLadder::Both, None, Joined::MutualContact, ContactLaw::Rectifying, realization)
}

#[allow(clippy::too_many_arguments)]
fn train_joined(args: &[String], credit: impl Into<super::tower_train::Credit>, targets: bool, turned: bool, ladder: TurnLadder, news: Option<NewsClock>, joined: Joined, contact: ContactLaw, realization: &mut dyn PassRealization) -> Result<()> {
    if args.len() != 19 && args.len() != 21 && !(joined == Joined::Split && args.len() == 23) {
        return Err("train-gated-tower-classes|train-credited-tower-classes|train-target-tower-classes|train-turned-tower-classes|train-scaled-tower-classes|train-two-ladder-tower-classes|train-two-ladder-news-tower-classes|train-two-ladder-participating-tower-classes|train-two-ladder-news-participating-tower-classes|train-two-ladder-mutual-tower-classes|train-two-ladder-split-tower-classes|train-two-ladder-dormant-split-tower-classes|train-two-ladder-stacked-news-packet-pair-tower-classes|train-two-ladder-stacked-news-heading-tower-classes|train-two-ladder-stacked-news-heading-credited-tower-classes|train-two-ladder-stacked-news-heading-credited-every-level-tower-classes ALPHABET TRAIN TRAIN_SHA DEV DEV_SHA DEV_ROLES DEV_ROLES_SHA KEYS KEYS_SHA WIDTH MODES CONTACTS LEVELS STREAMS SECTION PASSES RATE_BITS OUT [FROM FROM_SHA [PAIRED PAIRED_SHA]]".into());
    }
    let alphabet = count(&args[1])?;
    let train = classes_of(&pinned_read(&args[2], &args[3], READ_BUDGET as usize)?, alphabet)?;
    let dev = classes_of(&pinned_read(&args[4], &args[5], READ_BUDGET as usize)?, alphabet)?;
    let dev_roles = roles_of(&args[6], &args[7], dev.len())?;
    let reading = Reading {
        train_lengths: vec![1; train.len()],
        dev_lengths: vec![1; dev.len()],
        train,
        dev,
        dev_roles,
        alphabet,
        regions: CLASS_REGIONS,
        train_compared: None,
    };
    let reading = Reading { train_compared: targets.then(|| target_places(&reading.train, alphabet - 1)), ..reading };
    fit(&args[8..], reading, true, turned, false, credit, contact, ladder, news, joined, None, realization)
}

/// The news clock the clocked race joins: `B = 8` bits, the news of one octet read with no
/// prediction, and `r = 2`, the least radix whose carry merges epochs (agent-inferred; [`NewsClock`]).
pub(crate) fn race_news_clock() -> NewsClock {
    NewsClock::new(8, 2).expect("a whole positive section and ratio")
}

/// The race's news clock above the plain race's four arrival levels (`F = 4`): those levels tick
/// at every arrival and the levels above them on `B = 8`, `r = 2` (agent-inferred, October 30;
/// record `2026-10-29_A_CLOCKED_LEVELS_CONTACTS_HEAR_THE_PASSING_CURRENT…`, §8). A declaration of
/// four levels or fewer holds no level under it and is refused.
pub(crate) fn race_stacked_news_clock() -> NewsClock {
    NewsClock::above(8, 2, 4).expect("a whole positive section and ratio")
}

/// [agent-inferred, October 25] **A section's comparison is its target.** A passage of sections
/// `source END target END` declares, place by place, which arriving classes are its targets: those
/// after an odd count of end letters, the target and the end letter that closes it. The source and
/// its end letter are heard and not compared, so the covector a step descends is the target's
/// news given its source (a label given its image, an answer given its question, a transcript given
/// its utterance), whatever the medium: the places come from the section's form, never its chart.
fn target_places(classes: &[usize], end: usize) -> Vec<bool> {
    let mut ends = 0usize;
    classes
        .iter()
        .map(|&c| {
            let target = ends % 2 == 1;
            ends += usize::from(c == end);
            target
        })
        .collect()
}

/// `read-tower-classes STATE STATE_SHA CLASSES CLASSES_SHA MARKS MARKS_SHA STREAMS`: the class passage
/// cut into `STREAMS` parts, each read from rest; a class is read on the face the classes before it in
/// its part leave.
pub(super) fn read(args: &[String]) -> Result<()> {
    if args.len() != 8 {
        return Err("read-tower-classes STATE STATE_SHA CLASSES CLASSES_SHA MARKS MARKS_SHA STREAMS".into());
    }
    let started = std::time::Instant::now();
    let learner = TowerLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let tower = &learner.tower;
    let classes = classes_of(&pinned_read(&args[3], &args[4], READ_BUDGET as usize)?, tower.declaration.alphabet)?;
    let marks = pinned_read(&args[5], &args[6], READ_BUDGET as usize)?;
    if marks.len() != classes.len() || marks.iter().any(|&m| m as usize >= MARK_NAMES.len()) {
        return Err("the mark file does not name one mark for each class".into());
    }
    if classes.is_empty() {
        return Err("an empty passage has nothing to read".into());
    }
    let streams = positive(&args[7])?;
    let chunk = classes.len().div_ceil(streams);
    let starts: Vec<usize> = (0..classes.len()).step_by(chunk).collect();
    // Per mark: (code on 2^(−20) bits, cells, top is next); per label read: (arrived, named first).
    type Part = (Vec<(i64, usize, usize)>, Vec<(usize, usize)>);
    let parts: Vec<Part> = starts
        .par_iter()
        .map(|&start| {
            let part = &classes[start..(start + chunk).min(classes.len())];
            let mut state = tower.rest();
            let mut by_mark = vec![(0i64, 0usize, 0usize); MARK_NAMES.len()];
            let mut labels = Vec::new();
            for i in 0..part.len().saturating_sub(1) {
                let face = tower.advance(&mut state, part[i]).map_err(|e| e.to_string())?;
                let next = part[i + 1];
                let top = (0..face.masses.len()).fold(0, |best, c| if face.masses[c] > face.masses[best] { c } else { best });
                let mark = marks[start + i + 1] as usize;
                let m = &mut by_mark[mark];
                m.0 += face.code(next);
                m.1 += 1;
                m.2 += usize::from(top == next);
                if mark == 1 {
                    labels.push((next, top));
                }
            }
            Ok((by_mark, labels))
        })
        .collect::<std::result::Result<_, String>>()?;
    let mut by_mark = vec![(0i64, 0usize, 0usize); MARK_NAMES.len()];
    let mut labels = Vec::new();
    for (part, l) in parts {
        for (m, (code, n, right)) in part.into_iter().enumerate() {
            by_mark[m].0 += code;
            by_mark[m].1 += n;
            by_mark[m].2 += right;
        }
        labels.extend(l);
    }
    for (m, &(code, n, right)) in by_mark.iter().enumerate() {
        if n > 0 {
            println!("CLASSES_READ mark={} cells={n} bits_a_class={} top_is_next={right}", MARK_NAMES[m], per(code, n));
        }
    }
    if !labels.is_empty() {
        // Rows: the label that arrived; columns: the class the face named first (the numerals `0`–`9`,
        // then any other class).
        let mut rows = Vec::new();
        for arrived in b'0'..=b'9' {
            let named: Vec<String> = (b'0'..=b'9')
                .map(|d| labels.iter().filter(|&&(a, t)| a == arrived as usize && t == d as usize).count().to_string())
                .chain(std::iter::once(labels.iter().filter(|&&(a, t)| a == arrived as usize && !(b'0' as usize..=b'9' as usize).contains(&t)).count().to_string()))
                .collect();
            rows.push(format!("{}:{}", arrived as char, named.join(",")));
        }
        println!("CLASSES_LABELS reads={} named_right={} confusion(arrived:named 0..9,other) {}", labels.len(), labels.iter().filter(|(a, t)| a == t).count(), rows.join(" "));
    }
    println!("CLASSES_READ_DONE cells={} elapsed_ms={}", classes.len(), started.elapsed().as_millis());
    Ok(())
}

/// `read-tower-classes-at STATE STATE_SHA CLASSES CLASSES_SHA MARKS MARKS_SHA MARK STREAMS OUT`: the
/// cells of the class passage at which a class of mark `MARK` arrives, each read as `read-tower-classes`
/// reads it (the passage cut into `STREAMS` parts, each from rest), written to OUT (created, never
/// overwritten) in passage order, little-endian: the class that arrives (`u32`), the top face the
/// readout reads there (`width` × `i32`, on `2^(−16)`), then every level's carried modes after the
/// cell's step (`levels` × `modes` × (re, im) `i64`, the state's own grain). An exterior reading of
/// what the frozen tower's state holds where a landmark marks; nothing in it enters the tower.
pub(super) fn read_at(args: &[String]) -> Result<()> {
    if args.len() != 10 {
        return Err("read-tower-classes-at STATE STATE_SHA CLASSES CLASSES_SHA MARKS MARKS_SHA MARK STREAMS OUT".into());
    }
    let started = std::time::Instant::now();
    let learner = TowerLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let tower = &learner.tower;
    let classes = classes_of(&pinned_read(&args[3], &args[4], READ_BUDGET as usize)?, tower.declaration.alphabet)?;
    let marks = pinned_read(&args[5], &args[6], READ_BUDGET as usize)?;
    if marks.len() != classes.len() || marks.iter().any(|&m| m as usize >= MARK_NAMES.len()) {
        return Err("the mark file does not name one mark for each class".into());
    }
    if classes.is_empty() {
        return Err("an empty passage has nothing to read".into());
    }
    let mark: u8 = args[7].parse()?;
    if mark as usize >= MARK_NAMES.len() {
        return Err("MARK names no mark".into());
    }
    let streams = positive(&args[8])?;
    let out = Path::new(&args[9]);
    if out.exists() {
        return Err("OUT exists: the cells are written create-new".into());
    }
    let chunk = classes.len().div_ceil(streams);
    let starts: Vec<usize> = (0..classes.len()).step_by(chunk).collect();
    let parts: Vec<(Vec<u8>, usize)> = starts
        .par_iter()
        .map(|&start| {
            let part = &classes[start..(start + chunk).min(classes.len())];
            let (mut records, mut cells, mut state) = (Vec::new(), 0usize, tower.rest());
            for i in 0..part.len().saturating_sub(1) {
                if marks[start + i + 1] != mark {
                    tower.advance(&mut state, part[i]).map_err(|e| e.to_string())?;
                    continue;
                }
                // The one step at a marked cell, read through the ring reading for its top face.
                tower
                    .read_ring(&mut state, &part[i..i + 2], |_, top, _, _| {
                        records.extend((part[i + 1] as u32).to_le_bytes());
                        top.iter().for_each(|v| records.extend(v.to_le_bytes()));
                        Ok(())
                    })
                    .map_err(|e| e.to_string())?;
                state.modes.iter().flatten().for_each(|&(re, im)| {
                    records.extend(re.to_le_bytes());
                    records.extend(im.to_le_bytes());
                });
                cells += 1;
            }
            Ok((records, cells))
        })
        .collect::<std::result::Result<_, String>>()?;
    let cells: usize = parts.iter().map(|p| p.1).sum();
    let written: Vec<u8> = parts.into_iter().flat_map(|p| p.0).collect();
    write_new(out, &written)?;
    let d = &tower.declaration;
    println!("CLASSES_AT mark={} cells={cells} width={} levels={} modes={} elapsed_ms={}", MARK_NAMES[mark as usize], d.width, d.levels, d.modes, started.elapsed().as_millis());
    Ok(())
}

/// `release-tower-classes STATE STATE_SHA PROMPTS PROMPTS_SHA KEYS KEYS_SHA COUNT AGREE OUT`: each
/// prompt (classes through its end letter) forks the rested tower, which releases at most `COUNT`
/// classes; prompt `p` reads its keys from the `p`-th share of `COUNT` eight-byte keys. A
/// participating tower's participation at each answer's opening is read first
/// ([`participation_read`]).
pub(super) fn release(args: &[String]) -> Result<()> {
    release_realized(args, &mut HostPass::default())
}

/// [agent-inferred, October 27] [`release`] with every read and step run through `realization`
/// ([`Tower::advance_realized`]), so a release runs where the training runs. Each prompt is read
/// whole as one stream (on a participating tower in calls that end at its sections' closes); then
/// the prompts draw together, one class each a step, so the card reads
/// every releasing prompt's class in one launch. A prompt that has released its end letter or its
/// count draws no further key and its later faces are never read, so each release is the one the
/// prompt makes alone.
pub(crate) fn release_realized(args: &[String], realization: &mut dyn PassRealization) -> Result<()> {
    if args.len() != 10 {
        return Err("release-tower-classes STATE STATE_SHA PROMPTS PROMPTS_SHA KEYS KEYS_SHA COUNT AGREE OUT".into());
    }
    let started = std::time::Instant::now();
    let learner = TowerLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let tower = &learner.tower;
    let end = tower.declaration.alphabet - 1;
    let classes = classes_of(&pinned_read(&args[3], &args[4], READ_BUDGET as usize)?, tower.declaration.alphabet)?;
    let keys = pinned_read(&args[5], &args[6], READ_BUDGET as usize)?;
    let limit = positive(&args[7])?;
    let agree = agreement(args.get(8))?;
    let out = Path::new(&args[9]);
    let prompts: Vec<&[usize]> = classes.split_inclusive(|&c| c == end).collect();
    if prompts.is_empty() || prompts.iter().any(|p| p.last() != Some(&end)) {
        return Err("every prompt closes with the end letter".into());
    }
    let share = limit.checked_mul(8).ok_or("key extent overflow")?;
    if keys.len() < prompts.len() * share {
        return Err("fewer keys than the prompts' declared shares".into());
    }
    realization.admit(tower).map_err(|e| e.to_string())?;
    println!("TOWER_REALIZATION {}", realization.realization());
    std::fs::create_dir(out)?;
    if tower.participation().is_some() {
        participation_read(tower, &prompts, end, out)?;
    }
    // A section of the passage is entered after the end letter of the one before it, so a prompt
    // is entered the same way: from rest through one end letter, then its source. From rest alone,
    // a numeral and its end letter are also the close of every GSM8K answer, and the request would
    // not say which section it opens.
    let (mut states, mut faces, mut codes) = (Vec::with_capacity(prompts.len()), Vec::with_capacity(prompts.len()), Vec::with_capacity(prompts.len()));
    for prompt in &prompts {
        let entered: Vec<usize> = std::iter::once(end).chain(prompt.iter().copied()).collect();
        let mut state = vec![tower.rest()];
        let (face, code) = tower.advance_realized(&mut state, &[&entered], realization).map_err(|e| e.to_string())?;
        states.extend(state);
        faces.extend(face);
        codes.extend(code);
    }
    let mut streams: Vec<KeyStream> = (0..prompts.len())
        .map(|p| KeyStream::new(keys[p * share..(p + 1) * share].to_vec(), 8).map_err(|e| format!("{e:?}")))
        .collect::<std::result::Result<_, String>>()?;
    let mut released: Vec<Vec<usize>> = vec![Vec::new(); prompts.len()];
    let mut ended = vec![false; prompts.len()];
    loop {
        let mut drawn = vec![end; prompts.len()];
        let mut releasing = false;
        for p in 0..prompts.len() {
            if ended[p] || released[p].len() >= limit {
                continue;
            }
            let key = streams[p].next_key().ok_or("fewer keys than the declared count")?;
            let class = agreeing_class(&faces[p].masses, agree, &key).map_err(|e| e.to_string())?;
            released[p].push(class);
            if class == end {
                ended[p] = true;
            } else if released[p].len() < limit {
                drawn[p] = class;
                releasing = true;
            }
        }
        if !releasing {
            break;
        }
        let steps: Vec<[usize; 1]> = drawn.iter().map(|&c| [c]).collect();
        let reads: Vec<&[usize]> = steps.iter().map(|s| &s[..]).collect();
        faces = tower.advance_realized(&mut states, &reads, realization).map_err(|e| e.to_string())?.0;
    }
    let releases: Vec<(Vec<usize>, bool, i64)> = released.into_iter().zip(ended).zip(codes).map(|((r, e), c)| (r, e, c)).collect();
    let mut written = Vec::new();
    let mut rows = String::from("prompt\tprompt_classes\tprompt_bits_a_class\treleased\tended\toctets\n");
    for (p, (released, ended, code)) in releases.iter().enumerate() {
        for &c in released {
            written.extend_from_slice(&(c as u16).to_be_bytes());
        }
        let octets: Vec<u8> = released.iter().filter(|&&c| c < 256).map(|&c| c as u8).collect();
        let shown: String = octets.iter().map(|&b| b.escape_ascii().to_string()).collect();
        rows.push_str(&format!("{p}\t{}\t{}\t{}\t{ended}\t{shown}\n", prompts[p].len(), per(*code, prompts[p].len()), released.len()));
        println!("CLASSES_RELEASE prompt={p} prompt_classes={} released={} ended={ended}", prompts[p].len(), released.len());
    }
    write_new(&out.join("RELEASES.classes"), &written)?;
    write_new(&out.join("RELEASES.tsv"), rows.as_bytes())?;
    println!("CLASSES_RELEASE_DONE prompts={} agree={agree} elapsed_ms={}", prompts.len(), started.elapsed().as_millis());
    Ok(())
}

/// [agent-inferred, October 29] **The participation at each answer's opening** (the participation
/// record, §7.3): each prompt is read again on the host, entered as the release enters it, and at
/// its closing end letter, where the answer opens, each level's heads are read over the section's
/// admitted sites. Per prompt and level the sites carrying the most weight, summed over the heads in
/// thousandths of a head, print with the eight classes that end there (`|` the end letter); each
/// head's own top sites go to `PARTICIPATION.tsv`. A reading beside the writings, never a score.
fn participation_read(tower: &holonics::hnn::tower::Tower, prompts: &[&[usize]], end: usize, out: &Path) -> Result<()> {
    let mut rows = String::from(PARTICIPATION_HEAD);
    for (p, prompt) in prompts.iter().enumerate() {
        // The end letter, the prompt, and the end letter that opens the answer, read last.
        let entered: Vec<usize> = std::iter::once(end).chain(prompt[..prompt.len() - 1].iter().copied()).chain([end]).collect();
        let Some(read) = tower.participation_read(&mut tower.rest(), &entered).map_err(|e| e.to_string())? else { return Ok(()) };
        participation_rows(p, &entered, &read, &mut rows);
    }
    write_new(&out.join("PARTICIPATION.tsv"), rows.as_bytes())?;
    Ok(())
}

/// `PARTICIPATION.tsv`'s header.
pub(super) const PARTICIPATION_HEAD: &str = "prompt\tlevel\thead\tsites\treleased\tentropy_millibits\ttop(back:classes:thousandths)\n";

/// One prompt's participation at its answer's opening, `entered` the classes read with the opening's
/// end letter last: per level the sites carrying the most weight, summed over the heads in
/// thousandths of a head, printed as `back:classes:thousandths` with `back` how many classes before
/// the opening the site's arrival came and the eight classes that end there (`|` the end letter),
/// or `before:-:thousandths` for a site carried in from before the read; then the heads' mean
/// entropy in thousandths of a bit ([`Participation::entropy`]), and each head's own top sites and
/// entropy appended to `rows`. A clocked level admits a site only where its clock ticks, so each
/// site is placed by the arrival that admitted it ([`Tower::participation_read`]), never by its
/// count back from the opening.
///
/// [`Participation::entropy`]: holonics::hnn::tower::participation::Participation::entropy
/// [`Tower::participation_read`]: holonics::hnn::tower::Tower::participation_read
pub(super) fn participation_rows(p: usize, entered: &[usize], read: &holonics::hnn::tower::ParticipationRead, rows: &mut String) {
    const SHOWN: usize = 5;
    let last = entered.len() - 1;
    let shown = |at: usize| -> String { entered[at.saturating_sub(7)..=at].iter().map(|&c| if c < 256 { (c as u8).escape_ascii().to_string() } else { "|".into() }).collect() };
    let label = |arrival: Option<usize>| -> String {
        match arrival {
            Some(at) => format!("{}:{:?}", last - at, shown(at)),
            None => "before:-".into(),
        }
    };
    // The heaviest sites, the most recent first among equals.
    let top = |weights: &[u128]| -> Vec<(usize, u128)> {
        let mut order: Vec<(usize, u128)> = weights.iter().copied().enumerate().collect();
        order.sort_by(|a, b| b.1.cmp(&a.1).then(b.0.cmp(&a.0)));
        order.truncate(SHOWN);
        order
    };
    for (l, (heads, arrivals)) in read.levels.iter().zip(&read.arrivals).enumerate() {
        let sites = heads.first().map_or(0, |h| h.weights.len());
        let mut summed = vec![0u128; sites];
        let mut entropy = 0i128;
        for (h, part) in heads.iter().enumerate() {
            let share: Vec<u128> = part.weights.iter().map(|&e| e * 1000 / part.mass.max(1)).collect();
            for (s, &v) in summed.iter_mut().zip(&share) {
                *s += v;
            }
            let bits = millibits(part.entropy());
            entropy += bits;
            let listed: Vec<String> = top(&share).into_iter().map(|(j, v)| format!("{}:{v}", label(arrivals[j]))).collect();
            rows.push_str(&format!("{p}\t{l}\t{h}\t{sites}\t{}\t{bits}\t{}\n", part.released, listed.join(" ")));
        }
        let listed: Vec<String> = top(&summed).into_iter().map(|(j, v)| format!("{}:{}", label(arrivals[j]), v / heads.len().max(1) as u128)).collect();
        println!(
            "CLASSES_PARTICIPATION prompt={p} level={l} sites={sites} heads={} entropy_millibits={} top(back:classes:thousandths) {}",
            heads.len(),
            entropy / heads.len().max(1) as i128,
            listed.join(" ")
        );
    }
}

/// A reading on `2^(−ENTROPY_BITS)` bits in thousandths of a bit, to the nearest.
fn millibits(x: i128) -> i128 {
    (x * 1000 + (1 << (ENTROPY_BITS - 1))) >> ENTROPY_BITS
}

/// A code on `2^(−READ_BITS)` bits written in bits to the thousandth, its sign kept.
fn signed_bits(code: i64) -> String {
    let milli = (code.unsigned_abs() as u128 * 1000 + (1 << (READ_BITS - 1))) >> READ_BITS;
    format!("{}{}.{:03}", if code < 0 { "-" } else { "" }, milli / 1000, milli % 1000)
}

/// [agent-inferred, October 29] `read-tower-race STATE STATE_SHA DEV DEV_SHA PROMPTS PROMPTS_SHA
/// STREAMS SECTION OUT`: the race's readings of one lap's rested learner, beside the lap's bits and
/// writings (records `2026-10-29_A_COARSE_LEVELS_SITES_ARE_ITS_OWN_TICKS…` §5 and
/// `2026-10-29_A_VALUE_IS_A_RADIX_MOVE…` §§3–4). Each decides nothing, trains nothing and selects
/// no lap.
/// - `TOWER_RACE_FRICTIONS`: per level, how many modes sit at each friction octave, written as the
///   memory of `2^k` classes the octave matches (`Tower::mode_octaves`).
/// - `TOWER_RACE_BRIDGE`: per participating level, the join `W₁ᵃ`'s root mean square in thousandths
///   of the contacts', and each one's largest entry on `2^(−24)` (`Tower::participation_bridge`).
/// - At each prompt's opening, entered as the release enters it, each level's heads' participation
///   and entropy (`CLASSES_PARTICIPATION`, `OUT/PARTICIPATION.tsv`).
/// - `TOWER_RACE_SHARE`: over the held-out passage's opening, cut into `STREAMS` parts read from rest
///   with `SECTION` classes coded a part and every class compared, each head's mean entropy over the
///   sites it admitted and the share of its chart covector reaching its score charts (probe and key)
///   against its value chart, in thousandths (`Tower::participation_shares`).
/// - `TOWER_RACE_FLUX`: for each distinct prompt, the classes that follow its first place in `DEV`
///   to the next end letter, coded after its own prompt and after each other prompt;
///   `I = L(after another) − L(after its own)` in bits is the flux the prompt drives into what
///   follows it (atlas `culture.question-answer-information`).
///
/// The covector and the codes are read through `realization` (the card's route, `tower_pass read
/// complete-language read-tower-race …`, reads them on the card); the participation at the prompts'
/// openings and over the held-out opening is read on the host, as the release reads it.
pub(super) fn read_race(args: &[String]) -> Result<()> {
    read_race_realized(args, &mut HostPass::default())
}

/// [`read_race`] with its covector and codes read through `realization`.
pub(crate) fn read_race_realized(args: &[String], realization: &mut dyn PassRealization) -> Result<()> {
    if args.len() != 10 {
        return Err("read-tower-race STATE STATE_SHA DEV DEV_SHA PROMPTS PROMPTS_SHA STREAMS SECTION OUT".into());
    }
    let started = std::time::Instant::now();
    let learner = TowerLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let tower = &learner.tower;
    let alphabet = tower.declaration.alphabet;
    let end = alphabet - 1;
    let dev = classes_of(&pinned_read(&args[3], &args[4], READ_BUDGET as usize)?, alphabet)?;
    let prompts_classes = classes_of(&pinned_read(&args[5], &args[6], READ_BUDGET as usize)?, alphabet)?;
    let streams = positive(&args[7])?;
    let section = positive(&args[8])?;
    let out = Path::new(&args[9]);
    let mut prompts: Vec<&[usize]> = prompts_classes.split_inclusive(|&c| c == end).collect();
    if prompts.is_empty() || prompts.iter().any(|p| p.last() != Some(&end)) {
        return Err("every prompt closes with the end letter".into());
    }
    prompts.dedup();
    if dev.len() < streams * (section + 1) {
        return Err("the held-out passage must hold one section a stream".into());
    }
    realization.admit(tower).map_err(|e| e.to_string())?;
    println!("TOWER_REALIZATION {}", realization.realization());
    std::fs::create_dir(out)?;
    // The frictions and the bridge, read off the material.
    for (l, octaves) in tower.mode_octaves().iter().enumerate() {
        let mut counts: std::collections::BTreeMap<i128, usize> = std::collections::BTreeMap::new();
        for &o in octaves {
            *counts.entry(MOVE_OCTAVE - o).or_default() += 1;
        }
        let listed: Vec<String> = counts.iter().rev().map(|(k, n)| format!("2^{k}:{n}")).collect();
        println!("TOWER_RACE_FRICTIONS level={l} memory_classes:modes {}", listed.join(" "));
    }
    for (l, b) in tower.participation_bridge().unwrap_or_default().iter().enumerate() {
        let rms = (b.bridge_squares.saturating_mul(1_000_000) / b.contact_squares.max(1)).isqrt();
        println!("TOWER_RACE_BRIDGE level={l} rms_thousandths_of_contacts={rms} bridge_largest={} contacts_largest={} entries={}", b.bridge_largest, b.contact_largest, b.entries);
    }
    // The participation at each prompt's opening.
    if tower.participation().is_some() {
        participation_read(tower, &prompts, end, out)?;
    }
    // Each head's entropy and covector share over the held-out opening.
    let parts: Vec<&[usize]> = (0..streams).map(|p| &dev[p * (dev.len() / streams)..p * (dev.len() / streams) + section + 1]).collect();
    if let Some(declared) = tower.participation() {
        let heads = declared.heads.len();
        let entropies: Vec<Vec<(i128, usize)>> = parts
            .par_iter()
            .map(|part| -> std::result::Result<Vec<(i128, usize)>, String> {
                let mut state = tower.rest();
                let mut summed = vec![(0i128, 0usize); tower.declaration.levels * heads];
                for &u in &part[..section] {
                    let levels = tower.participation_at(&mut state, u).map_err(|e| e.to_string())?.unwrap_or_default();
                    for (l, level) in levels.iter().enumerate() {
                        for (h, head) in level.iter().enumerate() {
                            let slot = &mut summed[l * heads + h];
                            slot.0 += head.entropy();
                            slot.1 += 1;
                        }
                    }
                }
                Ok(summed)
            })
            .collect::<std::result::Result<_, String>>()?;
        let opening: Vec<_> = parts.iter().map(|_| tower.rest()).collect();
        let targets: Vec<Vec<Option<usize>>> = parts.iter().map(|c| c[1..].iter().map(|&u| Some(u)).collect()).collect();
        realization.forward(tower, &opening, &parts, &targets, Slot::Opened).map_err(|e| e.to_string())?;
        let g = realization.reverse(tower, &opening, &parts, None).map_err(|e| e.to_string())?;
        for (l, level) in tower.participation_shares(&g).map_err(|e| e.to_string())?.iter().enumerate() {
            let rows: Vec<String> = level
                .iter()
                .enumerate()
                .map(|(h, share)| {
                    let (sum, sites) = entropies.iter().fold((0i128, 0usize), |a, e| (a.0 + e[l * heads + h].0, a.1 + e[l * heads + h].1));
                    let entropy = if sites == 0 { "-".to_string() } else { millibits(sum / sites as i128).to_string() };
                    let score = share.score_thousandths().map_or("-".to_string(), |v| v.to_string());
                    format!("{h}:{}:{entropy}:{sites}:{score}", share.modes)
                })
                .collect();
            println!("TOWER_RACE_SHARE level={l} head:modes:entropy_millibits:sites:score_thousandths {}", rows.join(" "));
        }
    }
    // The flux each prompt drives into what follows it.
    let follows: Vec<Option<&[usize]>> = prompts
        .iter()
        .map(|prompt| {
            let at = dev.windows(prompt.len()).position(|w| w == *prompt)? + prompt.len();
            let rest = &dev[at..];
            let close = rest.iter().position(|&c| c == end)?;
            Some(&rest[..=close])
        })
        .collect();
    // Each continuation is entered after a prompt as the release enters the prompt (from rest
    // through one end letter), its first class compared with the face the prompt's read returned.
    let mut codes: Vec<((usize, usize), i64)> = Vec::new();
    for (a, follow) in follows.iter().enumerate() {
        let Some(follow) = follow else { continue };
        for (q, prompt) in prompts.iter().enumerate() {
            let entered: Vec<usize> = std::iter::once(end).chain(prompt.iter().copied()).collect();
            let mut states = vec![tower.rest()];
            let (faces, _) = tower.advance_realized(&mut states, &[&entered], realization).map_err(|e| e.to_string())?;
            let (_, read) = tower.advance_realized(&mut states, &[follow], realization).map_err(|e| e.to_string())?;
            codes.push(((a, q), faces[0].code(follow[0]) + read[0]));
        }
    }
    let code = |a: usize, q: usize| codes.iter().find(|(k, _)| *k == (a, q)).map(|&(_, c)| c);
    for (a, follow) in follows.iter().enumerate() {
        let Some(follow) = follow else {
            println!("TOWER_RACE_FLUX prompt={a} follows=absent");
            continue;
        };
        let own = code(a, a).unwrap_or(0);
        let others: Vec<String> = (0..prompts.len()).filter(|&q| q != a).filter_map(|q| code(a, q).map(|c| format!("{q}:{}", signed_bits(c - own)))).collect();
        println!("TOWER_RACE_FLUX prompt={a} follows_classes={} own_bits={} flux_bits_after_prompt {}", follow.len(), signed_bits(own), others.join(" "));
    }
    println!("TOWER_RACE_DONE prompts={} streams={streams} section={section} elapsed_ms={}", prompts.len(), started.elapsed().as_millis());
    Ok(())
}

/// The friction octave's memory: an octave `o` of `1 − |λ|` on `2^(−30)` matches about `2^(30 − o)`
/// classes.
const MOVE_OCTAVE: i128 = 30;

#[cfg(test)]
mod tests {
    use super::*;

    /// A class file is read two bytes a class, big-endian, and the end letter of the 257-class
    /// alphabet (octets and one end letter) is class 256; a class past the alphabet or an odd byte
    /// count is refused, never clipped.
    #[test]
    fn a_class_file_reads_the_declared_alphabet_and_refuses_what_lies_outside_it() {
        assert_eq!(classes_of(&[0, 55, 1, 0, 0, 255], 257).unwrap(), vec![55, 256, 255]);
        assert!(classes_of(&[1, 1], 257).is_err());
        assert!(classes_of(&[0, 55, 1], 257).is_err());
    }

    /// In `source END target END`, the target and its closing end letter are compared, the source
    /// and its end letter are not, section after section.
    #[test]
    fn the_targets_are_the_places_after_an_odd_count_of_end_letters() {
        let e = 256;
        let passage = [1, 2, e, 3, e, 4, e, 5, 6, e];
        let want = [false, false, false, true, true, false, false, true, true, true];
        assert_eq!(target_places(&passage, e), want);
    }

    /// A code's bits keep their sign to the thousandth.
    #[test]
    fn a_signed_code_reads_in_bits() {
        assert_eq!(signed_bits(3 << READ_BITS), "3.000");
        assert_eq!(signed_bits(-(1 << (READ_BITS - 1))), "-0.500");
        assert_eq!(signed_bits(0), "0.000");
    }

    /// The split race's routes on a tiny pair tower: the founding run widens the contact field at its
    /// founding, rests its directions beside each learner and continues from both, and refuses to
    /// continue without them; the control widens it the same way, founds nothing and continues
    /// from its learner alone.
    #[test]
    fn the_split_routes_widen_rest_and_continue() {
        use holonics::hnn::tower::split::PairedContacts;
        let dir = std::env::temp_dir().join(format!("holonics-tower-split-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("dir");
        let at = |name: &str| dir.join(name).to_string_lossy().into_owned();
        let put = |name: &str, bytes: &[u8]| {
            std::fs::write(dir.join(name), bytes).expect("write");
            (at(name), sha256(bytes).expect("sha"))
        };
        let classes = |v: &[usize]| -> Vec<u8> { v.iter().flat_map(|&c| (c as u16).to_be_bytes()).collect() };
        let train: Vec<usize> = (0..200).map(|i| (i * i + i / 3) % 4).collect();
        let dev: Vec<usize> = (0..60).map(|i| (i * 7 + i / 5) % 4).collect();
        let (train, train_sha) = put("TRAIN", &classes(&train));
        let (roles, roles_sha) = put("ROLES", &vec![0u8; dev.len()]);
        let (dev, dev_sha) = put("DEV", &classes(&dev));
        let keys: Vec<u8> = (0..4096u32).flat_map(|i| (i.wrapping_mul(2654435761) ^ i.wrapping_mul(i)).to_be_bytes()).collect();
        let (keys, keys_sha) = put("KEYS", &keys);
        let args = |command: &str, out: &str, from: &[&str]| -> Vec<String> {
            let mut a: Vec<String> = [command, "5", &train, &train_sha, &dev, &dev_sha, &roles, &roles_sha, &keys, &keys_sha, "4", "4", "4", "2", "2", "16", "1", "6", &at(out)].map(String::from).to_vec();
            a.extend(from.iter().map(|s| s.to_string()));
            a
        };
        let state = |out: &str, name: &str| -> (String, String, TowerLearner) {
            let text = std::fs::read(dir.join(out).join(name)).expect("rested");
            (at(&format!("{out}/{name}")), sha256(&text).expect("sha"), TowerLearner::from_text(std::str::from_utf8(&text).expect("text")).expect("learner"))
        };
        let founding = "train-two-ladder-split-tower-classes";
        train_split_realized(&args(founding, "S", &[]), true, &mut HostPass::default()).expect("founding run");
        let (learner, learner_sha, rested) = state("S", "STATE.0");
        assert_eq!(rested.tower.declaration.contacts, 8);
        let text = std::fs::read(dir.join("S/PAIRED.0")).expect("directions rested");
        let directions = PairedContacts::from_text(std::str::from_utf8(&text).expect("text")).expect("directions");
        directions.admits(&rested.tower).expect("the directions are the learner's");
        let paired_sha = sha256(&text).expect("sha");
        let paired = at("S/PAIRED.0");
        train_split_realized(&args(founding, "S2", &[&learner, &learner_sha, &paired, &paired_sha]), true, &mut HostPass::default()).expect("continued");
        assert!(train_split_realized(&args(founding, "S3", &[&learner, &learner_sha]), true, &mut HostPass::default()).is_err(), "a founding run continues with its directions");
        let dormant = "train-two-ladder-dormant-split-tower-classes";
        train_split_realized(&args(dormant, "D", &[]), false, &mut HostPass::default()).expect("control");
        assert!(!dir.join("D/PAIRED.0").exists(), "the control carries no directions");
        let (learner, learner_sha, rested) = state("D", "STATE.0");
        assert_eq!(rested.tower.declaration.contacts, 8);
        train_split_realized(&args(dormant, "D2", &[&learner, &learner_sha]), false, &mut HostPass::default()).expect("control continued");
        std::fs::remove_dir_all(&dir).expect("removed");
    }

    /// The race's readings run on a tiny participating learner: the prompts' openings write each
    /// head's entropy, the flux is read for each distinct prompt found in the held-out passage, and
    /// the reading is written create-new.
    #[test]
    fn the_race_readings_run_on_a_rested_learner() {
        use holonics::hnn::tower::{Tower, TowerDeclaration};
        let dir = std::env::temp_dir().join(format!("holonics-tower-race-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("dir");
        let at = |name: &str| dir.join(name).to_string_lossy().into_owned();
        let put = |name: &str, bytes: &[u8]| {
            std::fs::write(dir.join(name), bytes).expect("write");
            (at(name), sha256(bytes).expect("sha"))
        };
        let classes = |v: &[usize]| -> Vec<u8> { v.iter().flat_map(|&c| (c as u16).to_be_bytes()).collect() };
        let key: Vec<u8> = (0..4096u32).flat_map(|i| (i.wrapping_mul(2654435761) ^ i.wrapping_mul(i)).to_be_bytes()).collect();
        let declaration = TowerDeclaration { alphabet: 5, width: 4, modes: 4, contacts: 4, levels: 2, gated: true, turned: false, pumped: false, contact: ContactLaw::Rectifying };
        let mut tower = Tower::found(declaration, &key).expect("founded");
        let heads = tower.founded_participation(8).expect("declared");
        tower.join_participation(heads).expect("joined");
        let (state, state_sha) = put("STATE", TowerLearner::new(tower, 6).to_text().as_bytes());
        let mut dev: Vec<usize> = vec![1, 2, 4, 3, 3, 1, 4, 3, 0, 4, 2, 2, 1, 4];
        dev.extend((0..30).map(|i| (i * i + i / 3) % 4));
        let (dev, dev_sha) = put("DEV", &classes(&dev));
        let (prompts, prompts_sha) = put("PROMPTS", &classes(&[1, 2, 4, 1, 2, 4, 3, 0, 4, 3, 0, 4, 0, 0, 0, 4]));
        let args = ["read-tower-race", &state, &state_sha, &dev, &dev_sha, &prompts, &prompts_sha, "2", "6", &at("READ")].map(String::from);
        read_race(&args).expect("read");
        let rows = std::fs::read_to_string(dir.join("READ/PARTICIPATION.tsv")).expect("participation");
        assert!(rows.starts_with(PARTICIPATION_HEAD));
        assert!(rows.lines().skip(1).all(|r| r.split('\t').nth(5).is_some_and(|e| e.parse::<i128>().is_ok_and(|v| v >= 0))), "{rows}");
        assert!(read_race(&args).is_err(), "a reading is written create-new");
        std::fs::remove_dir_all(&dir).expect("removed");
    }
}
