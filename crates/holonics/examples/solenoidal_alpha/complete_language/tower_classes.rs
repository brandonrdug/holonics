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
use super::tower_train::{agreeing_class, agreement, count, fit, per, positive, roles_of, Reading, STATE_BUDGET};
use super::*;
use holonics::hnn::tower::realization::{HostPass, PassRealization};
use holonics::hnn::tower::{ContactLaw, NewsClock, TowerLearner, TurnLadder};
use rayon::prelude::*;

/// The held-out read's four exterior regions of a composed passage (`compose.py`'s roles).
const CLASS_REGIONS: [&str; 4] = ["gsm8k", "strokes", "cycles", "words"];
/// `compose.py`'s marks: 1 a label after its image, 2 a GSM8K answer, 3 a question, 4 a transcript
/// after its sound, 5 a stroke, 6 a half-cycle octet, 7 an end letter, 8 a numeral or transcript
/// heard before its image or sound.
const MARK_NAMES: [&str; 9] = ["none", "label", "answer", "question", "transcript", "stroke", "cycle", "end", "named"];

fn classes_of(bytes: &[u8], alphabet: usize) -> Result<Vec<usize>> {
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
/// `2026-10-28_ATTENTION_IS_THE_FIELDS_PARTICIPATION_…`). A continued learner keeps the
/// participation it was founded with.
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
    train_joined(args, credit, targets, turned, ladder, news, false, realization)
}

/// `train-two-ladder-participating-tower-classes`: [`train_realized`] on both turn ladders with
/// participation joined after the founding.
pub(crate) fn train_participating_realized(args: &[String], realization: &mut dyn PassRealization) -> Result<()> {
    train_joined(args, false, false, false, TurnLadder::Both, None, true, realization)
}

#[allow(clippy::too_many_arguments)]
fn train_joined(args: &[String], credit: bool, targets: bool, turned: bool, ladder: TurnLadder, news: Option<NewsClock>, participating: bool, realization: &mut dyn PassRealization) -> Result<()> {
    if args.len() != 19 && args.len() != 21 {
        return Err("train-gated-tower-classes|train-credited-tower-classes|train-target-tower-classes|train-turned-tower-classes|train-scaled-tower-classes|train-two-ladder-tower-classes|train-two-ladder-news-tower-classes|train-two-ladder-participating-tower-classes ALPHABET TRAIN TRAIN_SHA DEV DEV_SHA DEV_ROLES DEV_ROLES_SHA KEYS KEYS_SHA WIDTH MODES CONTACTS LEVELS STREAMS SECTION PASSES RATE_BITS OUT [FROM FROM_SHA]".into());
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
    fit(&args[8..], reading, true, turned, false, credit, ContactLaw::Rectifying, ladder, news, participating, None, realization)
}

/// The news clock the clocked race joins: `B = 8` bits, the news of one octet read with no
/// prediction, and `r = 2`, the least radix whose carry merges epochs (agent-inferred; [`NewsClock`]).
pub(crate) fn race_news_clock() -> NewsClock {
    NewsClock::new(8, 2).expect("a whole positive section and ratio")
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
/// whole as one stream; then the prompts draw together, one class each a step, so the card reads
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
    const SHOWN: usize = 5;
    let mut rows = String::from("prompt\tlevel\thead\tsites\treleased\ttop(back:classes:thousandths)\n");
    for (p, prompt) in prompts.iter().enumerate() {
        let entered: Vec<usize> = std::iter::once(end).chain(prompt.iter().copied()).collect();
        let mut state = tower.rest();
        tower.read_cells(&mut state, &entered).map_err(|e| e.to_string())?;
        let Some(levels) = tower.participation_at(&mut state, end).map_err(|e| e.to_string())? else { return Ok(()) };
        let last = entered.len() - 1;
        let shown = |back: usize| -> String {
            let at = last - back;
            entered[at.saturating_sub(7)..=at].iter().map(|&c| if c < 256 { (c as u8).escape_ascii().to_string() } else { "|".into() }).collect()
        };
        // The admitted site `j` of `sites` arrived `sites − 1 − j` classes before the opening.
        let top = |weights: &[u128]| -> Vec<(usize, u128)> {
            let mut order: Vec<(usize, u128)> = weights.iter().enumerate().map(|(j, &w)| (weights.len() - 1 - j, w)).collect();
            order.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
            order.truncate(SHOWN);
            order
        };
        for (l, heads) in levels.iter().enumerate() {
            let sites = heads.first().map_or(0, |h| h.weights.len());
            let mut summed = vec![0u128; sites];
            for (h, part) in heads.iter().enumerate() {
                let share: Vec<u128> = part.weights.iter().map(|&e| e * 1000 / part.mass.max(1)).collect();
                for (s, &v) in summed.iter_mut().zip(&share) {
                    *s += v;
                }
                let listed: Vec<String> = top(&share).into_iter().map(|(back, v)| format!("{back}:{:?}:{v}", shown(back))).collect();
                rows.push_str(&format!("{p}\t{l}\t{h}\t{sites}\t{}\t{}\n", part.released, listed.join(" ")));
            }
            let listed: Vec<String> = top(&summed).into_iter().map(|(back, v)| format!("{back}:{:?}:{}", shown(back), v / heads.len().max(1) as u128)).collect();
            println!("CLASSES_PARTICIPATION prompt={p} level={l} sites={sites} heads={} top(back:classes:thousandths) {}", heads.len(), listed.join(" "));
        }
    }
    write_new(&out.join("PARTICIPATION.tsv"), rows.as_bytes())?;
    Ok(())
}

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
}
