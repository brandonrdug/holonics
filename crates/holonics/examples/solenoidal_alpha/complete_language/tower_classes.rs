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
//!   not depend on their order.
//!
//! Nothing here is text-, image- or sound-specific: a medium is only the chart that wrote its
//! classes, and a numeral is the same class whether it names a digit image or ends a GSM8K answer.
use super::tower_train::{agreeing_class, agreement, count, fit, per, positive, roles_of, Reading, STATE_BUDGET};
use super::*;
use holonics::hnn::tower::{ContactLaw, TowerLearner};
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
/// code is reported a class.
pub(super) fn train(args: &[String]) -> Result<()> {
    if args.len() != 19 && args.len() != 21 {
        return Err("train-gated-tower-classes ALPHABET TRAIN TRAIN_SHA DEV DEV_SHA DEV_ROLES DEV_ROLES_SHA KEYS KEYS_SHA WIDTH MODES CONTACTS LEVELS STREAMS SECTION PASSES RATE_BITS OUT [FROM FROM_SHA]".into());
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
    };
    fit(&args[8..], reading, true, false, false, false, ContactLaw::Rectifying, None)
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

/// `release-tower-classes STATE STATE_SHA PROMPTS PROMPTS_SHA KEYS KEYS_SHA COUNT AGREE OUT`: each
/// prompt (classes through its end letter) forks the rested tower, which releases at most `COUNT`
/// classes; prompt `p` reads its keys from the `p`-th share of `COUNT` eight-byte keys.
pub(super) fn release(args: &[String]) -> Result<()> {
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
    std::fs::create_dir(out)?;
    let releases: Vec<(Vec<usize>, bool, i64)> = prompts
        .par_iter()
        .enumerate()
        .map(|(p, prompt)| {
            // A section of the passage is entered after the end letter of the one before it, so a
            // prompt is entered the same way: from rest through one end letter, then its source.
            // From rest alone, a numeral and its end letter are also the close of every GSM8K
            // answer, and the request would not say which section it opens.
            let entered: Vec<usize> = std::iter::once(end).chain(prompt.iter().copied()).collect();
            let mut state = tower.rest();
            let prompt_code = tower.read(&mut state.clone(), &entered).map_err(|e| e.to_string())?;
            let mut face = None;
            for &c in entered.iter() {
                face = Some(tower.advance(&mut state, c).map_err(|e| e.to_string())?);
            }
            let mut face = face.ok_or("an empty prompt")?;
            let mut stream = KeyStream::new(keys[p * share..(p + 1) * share].to_vec(), 8).map_err(|e| format!("{e:?}"))?;
            let mut released = Vec::new();
            while released.len() < limit {
                let key = stream.next_key().ok_or("fewer keys than the declared count")?;
                let class = agreeing_class(&face.masses, agree, &key).map_err(|e| e.to_string())?;
                released.push(class);
                if class == end {
                    return Ok((released, true, prompt_code));
                }
                face = tower.advance(&mut state, class).map_err(|e| e.to_string())?;
            }
            Ok((released, false, prompt_code))
        })
        .collect::<std::result::Result<_, String>>()?;
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
}
