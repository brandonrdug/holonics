//! The moment tower's exterior commands: train on text over passes, read the held-out partition,
//! release a continuation.
//!
//! [definition; agent-inferred, October 23] The tower (`holonics::hnn::tower`) reads the codec's
//! bytes as its classes. The training text is cut into `S` contiguous streams; a pass walks every
//! stream in sections of `T` bytes, each stream's modes carried from section to section and opened
//! at rest at the pass's start. Each section's covector is the sum of its streams'; its deposit is
//! certified by rereading the section. After each pass the frozen tower reads the held-out text in
//! the same number of streams, and the reading is printed beside the pass. A sample is a fork of
//! the rested tower: it opens at rest, receives the prompt, and releases each byte by an exact draw
//! on its face.
use super::*;
use holonics::hnn::tower::{Tower, TowerDeclaration, TowerFace, TowerLearner, TowerState, READ_BITS};
use holonics::hnn::units::{Units, CODE_BITS};
use rayon::prelude::*;

/// A learner's state read ceiling, `2^30` bytes.
const STATE_BUDGET: usize = 1 << 30;

pub(super) fn count(s: &str) -> Result<usize> {
    Ok(s.parse::<usize>()?)
}

/// The regions an exterior partition names, in order: question, answer prose, answer numbers,
/// calculation markup.
pub(super) const REGIONS: [&str; 4] = ["Q", "P", "N", "M"];

/// The held-out reading: the frozen tower's code of `classes`, cut into `streams` contiguous
/// parts, each read from rest; per region of `roles` (the coded class's region, the region of its
/// first byte), on `2^(−20)` bits, with the bytes coded (`lengths`, each class's bytes).
fn held_out(tower: &Tower, classes: &[usize], lengths: &[u32], roles: &[u8], streams: usize) -> Result<[(i64, usize); 4]> {
    let chunk = classes.len().div_ceil(streams);
    let starts: Vec<usize> = (0..classes.len()).step_by(chunk).collect();
    let parts: Vec<[(i64, usize); 4]> = starts
        .par_iter()
        .map(|&start| {
            let part = &classes[start..(start + chunk).min(classes.len())];
            let mut state = tower.rest();
            let codes = tower.read_cells(&mut state, part).map_err(|e| e.to_string())?;
            let mut regions = [(0i64, 0usize); 4];
            for (i, code) in codes.into_iter().enumerate() {
                let region = &mut regions[roles[start + i + 1] as usize];
                region.0 += code;
                region.1 += lengths[start + i + 1] as usize;
            }
            Ok(regions)
        })
        .collect::<std::result::Result<_, String>>()?;
    let mut regions = [(0i64, 0usize); 4];
    for part in parts {
        for (r, (code, n)) in part.into_iter().enumerate() {
            regions[r].0 += code;
            regions[r].1 += n;
        }
    }
    Ok(regions)
}

/// `Q=… P=… N=… M=…`: bits a byte per region.
pub(super) fn region_line(regions: &[(i64, usize); 4]) -> String {
    REGIONS
        .iter()
        .zip(regions)
        .map(|(name, &(code, n))| format!("{name}={}", per(code, n.max(1))))
        .collect::<Vec<_>>()
        .join(" ")
}

/// An exterior region file: one region index below four for each byte of `bytes`.
pub(super) fn roles_of(path: &str, sha: &str, bytes: usize) -> Result<Vec<u8>> {
    let roles = pinned_read(path, sha, READ_BUDGET as usize)?;
    if roles.len() != bytes || roles.iter().any(|&r| r > 3) {
        return Err("the region file does not name one of four regions for each byte".into());
    }
    Ok(roles)
}

/// `x / 2^20` bits over `n` as thousandths, written `0.xxx`.
pub(super) fn per(code: i64, n: usize) -> String {
    let milli = (code as i128 * 1000 + ((n as i128) << (READ_BITS - 1))) / ((n as i128) << READ_BITS);
    format!("{}.{:03}", milli / 1000, milli % 1000)
}

/// `train-tower` trains the ungated tower, `train-gated-tower` the gated one (its modes' decay keyed by
/// their input), `train-turned-tower` the turned one (its gated modes' turn keyed by their input too),
/// `train-pumped-tower` the pumped one (its turned modes pumped by their input, so a phase can lock),
/// and `train-credited-tower` the gated one whose streams carry their passage credit
/// (`hnn::tower::LevelCredit`), so a section's covector reaches the history its opening carries; a
/// continued learner must carry the same declaration.
pub(super) fn train(args: &[String], gated: bool, turned: bool, pumped: bool, credit: bool) -> Result<()> {
    train_looking_or_not(args, gated, turned, pumped, credit, None)
}

/// `train-looking-gated-tower|train-looking-turned-tower|train-looking-pumped-tower LOOK_KEYS
/// LOOK_KEYS_SHA AGREE MOMENT END TRAIN …` trains with the look inside training ([`Looking`]):
/// `MOMENT` and `END` are the bytes at which the terrain asks for a release and ends a line, and
/// `AGREE` the release's agreeing draws; the rest are `train-tower`'s arguments.
pub(super) fn train_looking(args: &[String], gated: bool, turned: bool, pumped: bool) -> Result<()> {
    if args.len() != 23 && args.len() != 25 {
        return Err("train-looking-gated-tower|train-looking-turned-tower|train-looking-pumped-tower LOOK_KEYS LOOK_KEYS_SHA AGREE MOMENT END TRAIN TRAIN_SHA DEV DEV_SHA DEV_ROLES DEV_ROLES_SHA KEYS KEYS_SHA WIDTH MODES CONTACTS LEVELS STREAMS SECTION PASSES RATE_BITS OUT [FROM FROM_SHA]".into());
    }
    let looking = Looking {
        keys: pinned_read(&args[1], &args[2], READ_BUDGET as usize)?,
        agree: agreement(args.get(3))?,
        moment: args[4].parse::<u8>()? as usize,
        end: args[5].parse::<u8>()? as usize,
    };
    if looking.moment == looking.end {
        return Err("a moment and a line's end are different bytes".into());
    }
    let rest: Vec<String> = std::iter::once(args[0].clone()).chain(args[6..].iter().cloned()).collect();
    train_looking_or_not(&rest, gated, turned, pumped, false, Some(&looking))
}

fn train_looking_or_not(args: &[String], gated: bool, turned: bool, pumped: bool, credit: bool, looking: Option<&Looking>) -> Result<()> {
    if args.len() != 18 && args.len() != 20 {
        return Err("train-tower|train-gated-tower|train-turned-tower|train-pumped-tower|train-credited-tower TRAIN TRAIN_SHA DEV DEV_SHA DEV_ROLES DEV_ROLES_SHA KEYS KEYS_SHA WIDTH MODES CONTACTS LEVELS STREAMS SECTION PASSES RATE_BITS OUT [FROM FROM_SHA]".into());
    }
    let train = pinned_read(&args[1], &args[2], READ_BUDGET as usize)?;
    let dev = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let roles = roles_of(&args[5], &args[6], dev.len())?;
    let reading = Reading {
        train: train.iter().map(|&b| b as usize).collect(),
        train_lengths: vec![1; train.len()],
        dev: dev.iter().map(|&b| b as usize).collect(),
        dev_lengths: vec![1; dev.len()],
        dev_roles: roles,
        alphabet: 256,
    };
    fit(&args[7..], reading, gated, turned, pumped, credit, looking)
}

/// `train-unit-tower` trains the gated tower on founded units (`hnn::units`): the training and
/// held-out text are read in the units, and each code is reported over the bytes its units decode
/// to.
pub(super) fn train_units(args: &[String]) -> Result<()> {
    if args.len() != 20 && args.len() != 22 {
        return Err("train-unit-tower UNITS UNITS_SHA TRAIN TRAIN_SHA DEV DEV_SHA DEV_ROLES DEV_ROLES_SHA KEYS KEYS_SHA WIDTH MODES CONTACTS LEVELS STREAMS SECTION PASSES RATE_BITS OUT [FROM FROM_SHA]".into());
    }
    let units = Units::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], READ_BUDGET as usize)?)?).map_err(|e| e.to_string())?;
    let train = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let dev = pinned_read(&args[5], &args[6], READ_BUDGET as usize)?;
    let byte_roles = roles_of(&args[7], &args[8], dev.len())?;
    let read = |bytes: &[u8]| -> Result<(Vec<usize>, Vec<u32>)> {
        let parsed = units.parse(bytes).map_err(|e| e.to_string())?;
        let lengths = parsed.iter().map(|&u| units.piece(u as usize).len() as u32).collect();
        Ok((parsed.into_iter().map(|u| u as usize).collect(), lengths))
    };
    let (train_classes, train_lengths) = read(&train)?;
    let (dev_classes, dev_lengths) = read(&dev)?;
    // Each unit's region is the region of its first byte.
    let mut dev_roles = Vec::with_capacity(dev_classes.len());
    let mut at = 0usize;
    for &n in &dev_lengths {
        dev_roles.push(byte_roles[at]);
        at += n as usize;
    }
    println!(
        "UNIT_READ units={} train_bytes={} train_units={} dev_bytes={} dev_units={}",
        units.len(), train.len(), train_classes.len(), dev.len(), dev_classes.len()
    );
    let reading = Reading { train: train_classes, train_lengths, dev: dev_classes, dev_lengths, dev_roles, alphabet: units.len() };
    fit(&args[9..], reading, true, false, false, false, None)
}

/// A passage read in a tower's classes: the training and held-out classes, the bytes each class
/// decodes to, and the held-out classes' regions.
struct Reading {
    train: Vec<usize>,
    train_lengths: Vec<u32>,
    dev: Vec<usize>,
    dev_lengths: Vec<u32>,
    dev_roles: Vec<u8>,
    alphabet: usize,
}

/// The passes: `args` are `KEYS KEYS_SHA WIDTH MODES CONTACTS LEVELS STREAMS SECTION PASSES RATE_BITS
/// OUT [FROM FROM_SHA]`.
fn fit(args: &[String], reading: Reading, gated: bool, turned: bool, pumped: bool, credit: bool, looking: Option<&Looking>) -> Result<()> {
    let started = Instant::now();
    let keys = pinned_read(&args[0], &args[1], READ_BUDGET as usize)?;
    let declaration = TowerDeclaration {
        alphabet: reading.alphabet,
        width: count(&args[2])?,
        modes: count(&args[3])?,
        contacts: count(&args[4])?,
        levels: count(&args[5])?,
        gated,
        turned,
        pumped,
    };
    let streams = count(&args[6])?;
    let section = count(&args[7])?;
    let passes = count(&args[8])?;
    let rate_bits: u32 = args[9].parse()?;
    let out = Path::new(&args[10]);
    std::fs::create_dir(out)?;
    let classes = &reading.train;
    if streams == 0 || section == 0 || classes.len() < streams * (section + 1) {
        return Err("the training text must hold one section a stream".into());
    }
    // A run continues a rested learner (its tower and moments) when one is named; its declaration
    // and rate must be the declared ones.
    let mut learner = if args.len() == 13 {
        let from = pinned_read(&args[11], &args[12], STATE_BUDGET)?;
        let learner = TowerLearner::from_text(std::str::from_utf8(&from)?).map_err(|e| e.to_string())?;
        if learner.tower.declaration != declaration || learner.rate_bits != rate_bits {
            return Err("the continued learner's declaration or rate differs from the declared one".into());
        }
        learner
    } else {
        TowerLearner::new(Tower::found(declaration, &keys).map_err(|e| e.to_string())?, rate_bits)
    };
    let chunk = classes.len() / streams;
    let sections_a_pass = (chunk - 1) / section;
    let dev_bytes: usize = reading.dev_lengths.iter().map(|&n| n as usize).sum();
    println!(
        "TOWER_TRAIN material={} streams={} section={} sections_a_pass={} train_bytes={} dev_bytes={}",
        learner.tower.theta.len(),
        streams,
        section,
        sections_a_pass,
        reading.train_lengths.iter().map(|&n| n as usize).sum::<usize>(),
        dev_bytes
    );
    // Each stream releases from its own share of the look's keys, so the releases do not depend on
    // the order the streams are filled in.
    let mut look_keys: Vec<KeyStream> = match looking {
        Some(l) => {
            let share = l.keys.len() / streams / 8 * 8;
            (0..streams).map(|s| KeyStream::new(l.keys[s * share..(s + 1) * share].to_vec(), 8)).collect::<std::result::Result<_, _>>()?
        }
        None => Vec::new(),
    };
    for pass in 0..passes {
        let pass_started = Instant::now();
        let mut states: Vec<TowerState> =
            (0..streams).map(|_| if credit { learner.tower.rest_with_credit() } else { learner.tower.rest() }).collect();
        let (mut code, mut bytes, mut deposits, mut halvings) = (0i64, 0usize, 0usize, 0u32);
        let mut window = (0i64, 0usize);
        let mut sections_run = sections_a_pass;
        if let Some(look) = looking {
            let mut lookers: Vec<Looker> = look_keys.drain(..).enumerate().map(|(s, keys)| Looker::new(s * chunk, (s + 1) * chunk, keys)).collect();
            let mut k = 0usize;
            loop {
                let tower = &learner.tower;
                let filled: Vec<bool> = lookers
                    .par_iter_mut()
                    .zip(states.par_iter())
                    .map(|(l, open)| l.fill(tower, classes, open, section + 1, look).map_err(|e| e.to_string()))
                    .collect::<std::result::Result<_, String>>()?;
                if filled.contains(&false) {
                    break;
                }
                let parts: Vec<Vec<usize>> = lookers.iter().map(|l| l.built[..=section].iter().map(|c| c.0).collect()).collect();
                let charges: Vec<Vec<bool>> = lookers.iter().map(|l| l.built[..=section].iter().map(|c| c.1).collect()).collect();
                let part_refs: Vec<&[usize]> = parts.iter().map(|p| p.as_slice()).collect();
                let charge_refs: Vec<&[bool]> = charges.iter().map(|c| c.as_slice()).collect();
                let receipt = match learner.section_charged(&mut states, &part_refs, Some(&charge_refs)) {
                    Ok(receipt) => receipt,
                    Err(e) => {
                        println!("TOWER_SWELL pass={} section={} {}", pass, k + 1, learner.swell_line());
                        return Err(e.to_string().into());
                    }
                };
                // Each charged class after a part's first is one byte that arrived.
                let coded: usize = charges.iter().map(|c| c[1..].iter().filter(|&&x| x).count()).sum();
                for l in &mut lookers {
                    l.built.drain(..section);
                }
                code += receipt.code_before;
                bytes += coded;
                window.0 += receipt.code_before;
                window.1 += coded;
                deposits += receipt.deposited as usize;
                halvings += receipt.halvings;
                k += 1;
                if k % 32 == 0 {
                    println!(
                        "TOWER_SECTION pass={} section={} bits_a_byte={} deposits={} halvings={} elapsed_ms={}",
                        pass, k, per(window.0, window.1), deposits, halvings, started.elapsed().as_millis()
                    );
                    window = (0, 0);
                }
            }
            let (looks, read) = lookers.iter().fold((0usize, 0usize), |a, l| (a.0 + l.looks, a.1 + l.at - l.start));
            println!(
                "TOWER_LOOKS pass={} sections={} looks={} text_read={} of {} keys_left={}",
                pass, k, looks, read, streams * chunk, lookers.iter().map(|l| l.keys_left()).min().unwrap_or(0)
            );
            look_keys = lookers.into_iter().map(|l| l.keys).collect();
            sections_run = k;
        }
        for k in 0..if looking.is_some() { 0 } else { sections_a_pass } {
            let ranges: Vec<std::ops::Range<usize>> =
                (0..streams).map(|s| s * chunk + k * section..s * chunk + (k + 1) * section + 1).collect();
            let parts: Vec<&[usize]> = ranges.iter().map(|r| &classes[r.clone()]).collect();
            let receipt = match learner.section(&mut states, &parts) {
                Ok(receipt) => receipt,
                Err(e) => {
                    println!("TOWER_SWELL pass={} section={} {}", pass, k + 1, learner.swell_line());
                    return Err(e.to_string().into());
                }
            };
            // The section codes every class of a part after its first.
            let coded: usize = ranges.iter().map(|r| reading.train_lengths[r.start + 1..r.end].iter().map(|&n| n as usize).sum::<usize>()).sum();
            code += receipt.code_before;
            bytes += coded;
            window.0 += receipt.code_before;
            window.1 += coded;
            deposits += receipt.deposited as usize;
            halvings += receipt.halvings;
            if (k + 1) % 32 == 0 || k + 1 == sections_a_pass {
                println!(
                    "TOWER_SECTION pass={} section={} bits_a_byte={} deposits={} halvings={} elapsed_ms={}",
                    pass, k + 1, per(window.0, window.1), deposits, halvings, started.elapsed().as_millis()
                );
                println!("TOWER_SWELL pass={} section={} {}", pass, k + 1, learner.swell_line());
                window = (0, 0);
            }
        }
        // Each pass's learner rests beside the run before the held-out read, so a run stopped at
        // its deadline or refused in the read keeps its last trained pass.
        let text = learner.to_text();
        let name = format!("STATE.{pass}");
        write_new(&out.join(&name), text.as_bytes())?;
        println!("TOWER_STATE {name} state_bytes={} state_sha256={}", text.len(), sha256(text.as_bytes())?);
        let regions = held_out(&learner.tower, &reading.dev, &reading.dev_lengths, &reading.dev_roles, streams)?;
        let (dev_code, dev_coded) = regions.iter().fold((0i64, 0usize), |a, r| (a.0 + r.0, a.1 + r.1));
        println!(
            "TOWER_PASS pass={} train_bits_a_byte={} dev_bits_a_byte={} dev_regions {} deposits={}/{} pass_ms={} elapsed_ms={}",
            pass, per(code, bytes), per(dev_code, dev_coded), region_line(&regions), deposits, sections_run,
            pass_started.elapsed().as_millis(), started.elapsed().as_millis()
        );
    }
    let text = learner.to_text();
    write_new(&out.join("STATE"), text.as_bytes())?;
    println!("TOWER_DONE state_bytes={} state_sha256={} elapsed_ms={}", text.len(), sha256(text.as_bytes())?, started.elapsed().as_millis());
    Ok(())
}

/// `found-units TRAIN TRAIN_SHA OUT`: found units from the training text (`hnn::units`) and write
/// the founding list.
pub(super) fn found_units(args: &[String]) -> Result<()> {
    if args.len() != 4 {
        return Err("found-units TRAIN TRAIN_SHA OUT".into());
    }
    let started = Instant::now();
    let train = pinned_read(&args[1], &args[2], READ_BUDGET as usize)?;
    let out = Path::new(&args[3]);
    std::fs::create_dir(out)?;
    let (units, read, receipt) = Units::found(&train).map_err(|e| e.to_string())?;
    let text = units.to_text();
    write_new(&out.join("UNITS"), text.as_bytes())?;
    let bits = |code: i128| per((code >> (CODE_BITS - READ_BITS)) as i64, train.len());
    println!(
        "UNITS_FOUNDED units={} founded={} refused={} undecided={} priced={} symbols={}->{} order_one_bits_a_byte={}->{} description_bits_a_byte={} complete_bits_a_byte={} elapsed_ms={}",
        units.len(), receipt.founded, receipt.refused, receipt.undecided, receipt.priced, receipt.symbols_before, receipt.symbols_after,
        bits(receipt.code_before), bits(receipt.code_after), bits(receipt.description), bits(receipt.code_after + receipt.description),
        started.elapsed().as_millis()
    );
    println!("UNITS_STATE units_bytes={} units_sha256={}", text.len(), sha256(text.as_bytes())?);
    // The units the passage reads most, with their counts, and the longest founded.
    let mut counts = vec![0usize; units.len()];
    for &u in &read {
        counts[u as usize] += 1;
    }
    let mut order: Vec<usize> = (256..units.len()).collect();
    order.sort_by_key(|&u| std::cmp::Reverse(counts[u]));
    let show = |u: usize| format!("{:?}:{}", String::from_utf8_lossy(units.piece(u)), counts[u]);
    println!("UNITS_READ_MOST {}", order.iter().take(60).map(|&u| show(u)).collect::<Vec<_>>().join(" "));
    order.sort_by_key(|&u| std::cmp::Reverse(units.piece(u).len()));
    println!("UNITS_LONGEST {}", order.iter().take(30).map(|&u| show(u)).collect::<Vec<_>>().join(" "));
    Ok(())
}

/// `sample-unit-tower UNITS UNITS_SHA STATE STATE_SHA PROMPT PROMPT_SHA KEYS KEYS_SHA BYTES OUT
/// [AGREE]`: the prompt read in the units, then units released until the declared bytes.
pub(super) fn sample_units(args: &[String]) -> Result<()> {
    if args.len() != 11 && args.len() != 12 {
        return Err("sample-unit-tower UNITS UNITS_SHA STATE STATE_SHA PROMPT PROMPT_SHA KEYS KEYS_SHA BYTES OUT [AGREE]".into());
    }
    let units = Units::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], READ_BUDGET as usize)?)?).map_err(|e| e.to_string())?;
    release(&args[2..], Some(&units))
}

pub(super) fn sample(args: &[String]) -> Result<()> {
    if args.len() != 9 && args.len() != 10 {
        return Err("sample-tower STATE STATE_SHA PROMPT PROMPT_SHA KEYS KEYS_SHA BYTES OUT [AGREE]".into());
    }
    release(args, None)
}

/// A fork of the rested tower: it receives the prompt (read in the units when named) and releases
/// classes by exact draws on its face until the declared bytes are released. `args` are
/// `_ STATE STATE_SHA PROMPT PROMPT_SHA KEYS KEYS_SHA BYTES OUT [AGREE]`.
fn release(args: &[String], units: Option<&Units>) -> Result<()> {
    let agree = agreement(args.get(9))?;
    let started = Instant::now();
    let state = pinned_read(&args[1], &args[2], STATE_BUDGET)?;
    let prompt = pinned_read(&args[3], &args[4], QUERY_BYTE_BUDGET)?;
    let keys = pinned_read(&args[5], &args[6], READ_BUDGET as usize)?;
    let count: usize = args[7].parse()?;
    if keys.len() < count.checked_mul(8).ok_or("key extent overflow")? {
        return Err("fewer eight-byte keys than declared bytes".into());
    }
    let out = Path::new(&args[8]);
    std::fs::create_dir(out)?;
    let learner = TowerLearner::from_text(std::str::from_utf8(&state)?).map_err(|e| e.to_string())?;
    let tower = &learner.tower;
    let mut modes = tower.rest();
    let classes: Vec<usize> = match units {
        Some(u) => u.parse(&prompt).map_err(|e| e.to_string())?.into_iter().map(|c| c as usize).collect(),
        None => prompt.iter().map(|&b| b as usize).collect(),
    };
    let prompt_code = if classes.len() > 1 { tower.read(&mut modes.clone(), &classes).map_err(|e| e.to_string())? } else { 0 };
    let mut face = None;
    for &c in &classes {
        face = Some(tower.advance(&mut modes, c).map_err(|e| e.to_string())?);
    }
    let mut face = face.ok_or("an empty prompt")?;
    let mut key_stream = KeyStream::new(keys, 8)?;
    let mut released = Vec::with_capacity(count);
    while released.len() < count {
        let key = key_stream.next_key().ok_or("fewer keys than declared bytes")?;
        let class = holonics::receiver::release::draw_exact(&agreement_face(&face.masses, agree), &key)?
            .drawn_class()
            .ok_or("an unresolved draw at an exact face")?;
        match units {
            Some(u) => released.extend_from_slice(u.piece(class)),
            None => released.push(class as u8),
        }
        face = tower.advance(&mut modes, class).map_err(|e| e.to_string())?;
    }
    write_new(&out.join("OUTPUT.bin"), &released)?;
    let prompt_bytes = match units {
        Some(u) => classes[1..].iter().map(|&c| u.piece(c).len()).sum::<usize>(),
        None => classes.len().saturating_sub(1),
    };
    println!(
        "TOWER_SAMPLE prompt_bits_a_byte={} bytes={} agree={} elapsed_ms={}",
        per(prompt_code, prompt_bytes.max(1)), released.len(), agree, started.elapsed().as_millis()
    );
    println!("TOWER_SAMPLE_TEXT {:?}", String::from_utf8_lossy(&released));
    Ok(())
}

/// `read-lines STATE STATE_SHA TEXT TEXT_SHA KEYS KEYS_SHA WRITTEN AGREE OUT`: each line of the
/// text read alone. The frozen tower opens at rest on a line's end, receives the line through its
/// first `=`, and codes the rest of the line class by class (`LINES.tsv`: the line's index, its
/// head, the rest as given and each class's code on `2^(−20)` bits). For the first `WRITTEN` lines
/// a fork at the `=` releases its own rest by exact agreeing draws until a line's end (or as many
/// classes as the given rest and four more), written beside it. An exterior reading of terrain
/// lines (`tools/arithmetic_terrain.py`): what the tower writes after an expression it may never
/// have met. `read-lines-stream` opens each line instead on the state the text's true earlier
/// lines left, the condition the tower trained in: the fork writes from that state, and the true
/// line, not the release, carries the stream on.
///
/// `read-lines-again … AGREE LOOKS OUT` writes in the stream and then looks again: the fork
/// carries the rest it wrote, its line's end and the line's head once more, and releases again,
/// until two looks in a row write the same rest or `LOOKS` looks are spent. `read-lines-redraw`
/// is its foil: each later look draws again at the same moment and carries nothing of the looks
/// before it. The first look spends the key file as the one-look read does, so its releases are
/// that read's; the later looks draw from the file's second half. `LINES.tsv` writes the last look
/// and `LOOKS.tsv` every look (the line's index, its head, the rest as given, whether the last two
/// looks agree, the looks joined by `|`, and what the true rest costs from where each look stands,
/// on `2^(−20)` bits: the frustration's floor and how fast the looks approach it).
/// `read-lines-carried` looks as `read-lines-again` does, and its stream carries each written
/// line's first look, line end and head again before the true rest, the passage a tower trained
/// with the look (`Looking`) met: its codes are read where that tower was taught.
pub(super) fn read_lines(args: &[String], in_stream: bool, look: Look) -> Result<()> {
    let arity = if look == Look::Once { 10 } else { 11 };
    if args.len() != arity {
        return Err("read-lines|read-lines-stream STATE STATE_SHA TEXT TEXT_SHA KEYS KEYS_SHA WRITTEN AGREE OUT; read-lines-again|read-lines-redraw|read-lines-carried STATE STATE_SHA TEXT TEXT_SHA KEYS KEYS_SHA WRITTEN AGREE LOOKS OUT".into());
    }
    let started = Instant::now();
    let learner = TowerLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let text = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let keys = pinned_read(&args[5], &args[6], READ_BUDGET as usize)?;
    let written: usize = args[7].parse()?;
    let agree = agreement(args.get(8))?;
    let looks: usize = if look == Look::Once { 1 } else { args[9].parse()? };
    if looks == 0 {
        return Err("a written line needs at least one look".into());
    }
    let out = Path::new(&args[arity - 1]);
    std::fs::create_dir(out)?;
    let tower = &learner.tower;
    let mut later_keys = KeyStream::new(keys[keys.len() / 2..].to_vec(), 8)?;
    let mut key_stream = KeyStream::new(keys, 8)?;
    let mut rows = String::new();
    let mut look_rows = String::new();
    let (mut spent, mut settled) = (0usize, 0usize);
    let mut lines = 0usize;
    let mut carried = tower.rest();
    let mut carried_face = tower.advance(&mut carried, b'\n' as usize).map_err(|e| e.to_string())?;
    for (i, line) in text.split(|&b| b == b'\n').filter(|l| !l.is_empty()).enumerate() {
        let Some(eq) = line.iter().position(|&b| b == b'=') else {
            for &b in line.iter().chain(b"\n") {
                carried_face = tower.advance(&mut carried, b as usize).map_err(|e| e.to_string())?;
            }
            continue;
        };
        let (mut modes, mut face) = if in_stream {
            (carried.clone(), carried_face.clone())
        } else {
            let mut modes = tower.rest();
            let face = tower.advance(&mut modes, b'\n' as usize).map_err(|e| e.to_string())?;
            (modes, face)
        };
        for &b in &line[..=eq] {
            face = tower.advance(&mut modes, b as usize).map_err(|e| e.to_string())?;
        }
        let rest: Vec<u8> = line[eq + 1..].iter().copied().chain([b'\n']).collect();
        let mut looked: Vec<String> = Vec::new();
        let mut costs: Vec<i64> = Vec::new();
        let mut first_look: Vec<usize> = Vec::new();
        if i < written {
            let cap = rest.len() + 4;
            let mut fork = modes.clone();
            let written = |r: Vec<usize>| r.into_iter().map(|c| char::from(c as u8)).collect::<String>();
            costs.push(rest_code(tower, &modes, face.clone(), &rest)?);
            first_look = release_rest(tower, &mut fork, face.clone(), &mut key_stream, cap, agree)?;
            looked.push(written(first_look.clone()));
            while looked.len() < looks && (looked.len() < 2 || looked[looked.len() - 1] != looked[looked.len() - 2]) {
                let again = match look {
                    Look::Once => break,
                    Look::Again | Look::Carried => {
                        let mut f = tower.advance(&mut fork, b'\n' as usize).map_err(|e| e.to_string())?;
                        for &b in &line[..=eq] {
                            f = tower.advance(&mut fork, b as usize).map_err(|e| e.to_string())?;
                        }
                        costs.push(rest_code(tower, &fork, f.clone(), &rest)?);
                        written(release_rest(tower, &mut fork, f, &mut later_keys, cap, agree)?)
                    }
                    Look::Redraw => {
                        costs.push(costs[0]);
                        written(release_rest(tower, &mut modes.clone(), face.clone(), &mut later_keys, cap, agree)?)
                    }
                };
                looked.push(again);
            }
            spent += looked.len();
            let agreed = looked.len() >= 2 && looked[looked.len() - 1] == looked[looked.len() - 2];
            settled += usize::from(agreed);
            if look != Look::Once {
                look_rows.push_str(&format!(
                    "{}\t{}\t{}\t{}\t{}\t{}\n",
                    i,
                    String::from_utf8_lossy(&line[..=eq]),
                    String::from_utf8_lossy(&rest[..rest.len() - 1]),
                    u8::from(agreed),
                    looked.join("|"),
                    costs.iter().map(|c| c.to_string()).collect::<Vec<_>>().join("|")
                ));
            }
        }
        let release = looked.last().cloned().unwrap_or_default();
        if look == Look::Carried && i < written {
            // The stream carries the first look, its line's end and the head again before the
            // true rest, as a tower trained with the look met its lines.
            let carried_in: Vec<usize> = first_look.iter().copied().chain([b'\n' as usize]).chain(line[..=eq].iter().map(|&b| b as usize)).collect();
            for b in carried_in {
                face = tower.advance(&mut modes, b).map_err(|e| e.to_string())?;
            }
        }
        let mut codes = Vec::with_capacity(rest.len());
        for &b in &rest {
            codes.push(face.code(b as usize).to_string());
            face = tower.advance(&mut modes, b as usize).map_err(|e| e.to_string())?;
        }
        (carried, carried_face) = (modes, face);
        rows.push_str(&format!(
            "{}\t{}\t{}\t{}\t{}\n",
            i,
            String::from_utf8_lossy(&line[..=eq]),
            String::from_utf8_lossy(&rest[..rest.len() - 1]),
            release,
            codes.join(",")
        ));
        lines += 1;
    }
    write_new(&out.join("LINES.tsv"), rows.as_bytes())?;
    if look != Look::Once {
        write_new(&out.join("LOOKS.tsv"), look_rows.as_bytes())?;
        println!("LOOKS_READ looks={} spent={} settled={} looks_sha256={}", looks, spent, settled, sha256(look_rows.as_bytes())?);
    }
    println!("LINES_READ lines={} written={} agree={} lines_sha256={} elapsed_ms={}", lines, written.min(lines), agree, sha256(rows.as_bytes())?, started.elapsed().as_millis());
    Ok(())
}

/// How a written line meets its own moment again (`read_lines`).
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum Look {
    /// One look: the release at the `=` is written as it comes.
    Once,
    /// The fork carries its own release, its line's end and the head again, and releases again.
    Again,
    /// The foil: each later look draws again at the same moment, carrying nothing.
    Redraw,
    /// As `Again`, and the stream carries the first look before the true rest.
    Carried,
}

/// What the line's true rest costs read from `state` and its `face`: its classes' codes summed on
/// `2^(−20)` bits, the rest's line end included. An exterior reading at a look: the state is not
/// moved.
fn rest_code(tower: &Tower, state: &TowerState, mut face: TowerFace, rest: &[u8]) -> Result<i64> {
    let mut s = state.clone();
    let mut code = 0i64;
    for &b in rest {
        code += face.code(b as usize);
        face = tower.advance(&mut s, b as usize).map_err(|e| e.to_string())?;
    }
    Ok(code)
}

/// The rest a fork releases from `face` by exact agreeing draws: classes until a line's end, or
/// `cap` classes. The fork moves through every class it writes.
fn release_rest(tower: &Tower, fork: &mut TowerState, mut face: TowerFace, keys: &mut KeyStream, cap: usize, agree: u32) -> Result<Vec<usize>> {
    let mut release = Vec::new();
    while release.len() < cap {
        let key = keys.next_key().ok_or("fewer keys than the written lines draw")?;
        let class = agreeing_class(&face.masses, agree, &key)?;
        if class == b'\n' as usize {
            break;
        }
        release.push(class);
        face = tower.advance(fork, class).map_err(|e| e.to_string())?;
    }
    Ok(release)
}

/// The look inside training: at each moment the terrain declares (the byte at which a line asks
/// for its rest), the tower releases its own rest from the state its stream has reached, by
/// `agree` exact agreeing draws from its stream's share of `keys`. That release and its line's end
/// re-enter what the stream reads uncharged (`TowerLearner::section_charged`): they are the
/// tower's own and bring no news. The line's head then arrives again and its true rest after it,
/// both charged, so the arrival's covector returns through the state the tower's own release moved
/// and what it learns is what a look after its own should write. The terrain's moment and line
/// end are its codec's declared bytes, read outside the tower.
pub(super) struct Looking {
    keys: Vec<u8>,
    agree: u32,
    moment: usize,
    end: usize,
}

/// One stream's passage with its own releases written in: the classes from the section's first
/// on, each with whether it arrived (charged) or the tower released it.
struct Looker {
    start: usize,
    end: usize,
    at: usize,
    line_start: Option<usize>,
    built: Vec<(usize, bool)>,
    keys: KeyStream,
    looks: usize,
}

impl Looker {
    fn new(start: usize, end: usize, keys: KeyStream) -> Self {
        Self { start, end, at: start, line_start: None, built: Vec::new(), keys, looks: 0 }
    }

    fn keys_left(&self) -> usize {
        self.keys.remaining()
    }

    /// Fill the passage to `need` classes from the stream's text, the state `opening` having
    /// received every class before the first: false when the stream's text ends first. A line's
    /// head is whole only after the stream has met a line's end, so a stream releases only from
    /// its first whole line on.
    fn fill(&mut self, tower: &Tower, text: &[usize], opening: &TowerState, need: usize, look: &Looking) -> Result<bool> {
        let mut probe = opening.clone();
        let mut probed = 0usize;
        while self.built.len() < need {
            if self.at >= self.end {
                return Ok(false);
            }
            let c = text[self.at];
            self.at += 1;
            self.built.push((c, true));
            if c == look.end {
                self.line_start = Some(self.at);
            } else if let (true, Some(head)) = (c == look.moment, self.line_start) {
                let mut face = None;
                for &(b, _) in &self.built[probed..] {
                    face = Some(tower.advance(&mut probe, b).map_err(|e| e.to_string())?);
                }
                probed = self.built.len();
                let given = text[self.at..self.end].iter().position(|&b| b == look.end).unwrap_or(self.end - self.at);
                let mut fork = probe.clone();
                let face = face.ok_or("a moment the probe has not received")?;
                let release = release_rest(tower, &mut fork, face, &mut self.keys, given + 4, look.agree)?;
                self.built.extend(release.into_iter().map(|b| (b, false)));
                self.built.push((look.end, false));
                self.built.extend(text[head..self.at].iter().map(|&b| (b, true)));
                self.looks += 1;
            }
        }
        Ok(true)
    }
}

/// The release at which `agree` independent draws from the face fall on the same class: the face's
/// masses raised to that power over their sum. One draw is the face itself; two give its collision
/// face `p²/Σp²`, the release where two receivers of the same face agree. The release is exact and
/// spends one key a draw whatever `agree` is.
pub(super) fn agreement_face(masses: &[u128], agree: u32) -> Vec<Rat> {
    let powered: Vec<num_bigint::BigInt> = masses.iter().map(|&u| num_bigint::BigInt::from(u).pow(agree)).collect();
    let total: num_bigint::BigInt = powered.iter().sum();
    powered.into_iter().map(|u| Rat::new(u, total.clone())).collect()
}

/// The class `agree` agreeing draws fall on at `key = n/d`: the inverse-CDF class of the face
/// `m^agree / Σ m^agree`, the first `c` with `d Σ_(j≤c) m_j^agree > n Σ m^agree`. It is
/// `release::draw_exact` over [`agreement_face`] read in integers, without normalizing a ratio for
/// every class.
pub(super) fn agreeing_class(masses: &[u128], agree: u32, key: &Rat) -> Result<usize> {
    if key < &Rat::from_integer(0.into()) || key >= &Rat::from_integer(1.into()) {
        return Err("a key outside [0, 1)".into());
    }
    let powered: Vec<num_bigint::BigInt> = masses.iter().map(|&m| num_bigint::BigInt::from(m).pow(agree)).collect();
    let total: num_bigint::BigInt = powered.iter().sum();
    let target = key.numer() * &total;
    let mut through = num_bigint::BigInt::from(0);
    for (class, p) in powered.iter().enumerate() {
        through += p;
        if &through * key.denom() > target {
            return Ok(class);
        }
    }
    Err("an empty face".into())
}

/// The declared number of agreeing draws: one when none is named.
pub(super) fn agreement(arg: Option<&String>) -> Result<u32> {
    let agree = arg.map_or(Ok(1), |a| a.parse::<u32>())?;
    if agree == 0 {
        return Err("a release needs at least one draw".into());
    }
    Ok(agree)
}
