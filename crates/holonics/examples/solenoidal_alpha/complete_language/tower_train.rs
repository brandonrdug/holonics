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
use holonics::hnn::tower::{Tower, TowerDeclaration, TowerLearner, TowerState, READ_BITS};

/// A learner's state read ceiling, `2^30` bytes.
const STATE_BUDGET: usize = 1 << 30;

fn count(s: &str) -> Result<usize> {
    Ok(s.parse::<usize>()?)
}

/// The regions an exterior partition names, in order: question, answer prose, answer numbers,
/// calculation markup.
pub(super) const REGIONS: [&str; 4] = ["Q", "P", "N", "M"];

/// The held-out reading: the frozen tower's code of `bytes`, cut into `streams` contiguous parts,
/// each read from rest; per region of `roles` (the coded byte's region), on `2^(−20)` bits, with the
/// bytes coded.
fn held_out(tower: &Tower, bytes: &[u8], roles: &[u8], streams: usize) -> Result<[(i64, usize); 4]> {
    let classes: Vec<usize> = bytes.iter().map(|&b| b as usize).collect();
    let chunk = classes.len().div_ceil(streams);
    let starts: Vec<usize> = (0..classes.len()).step_by(chunk).collect();
    use rayon::prelude::*;
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
                region.1 += 1;
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

pub(super) fn train(args: &[String]) -> Result<()> {
    if args.len() != 18 && args.len() != 20 {
        return Err("train-tower TRAIN TRAIN_SHA DEV DEV_SHA DEV_ROLES DEV_ROLES_SHA KEYS KEYS_SHA WIDTH MODES CONTACTS LEVELS STREAMS SECTION PASSES RATE_BITS OUT [FROM FROM_SHA]".into());
    }
    let started = Instant::now();
    let train = pinned_read(&args[1], &args[2], READ_BUDGET as usize)?;
    let dev = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let roles = roles_of(&args[5], &args[6], dev.len())?;
    let keys = pinned_read(&args[7], &args[8], READ_BUDGET as usize)?;
    let declaration = TowerDeclaration {
        alphabet: 256,
        width: count(&args[9])?,
        modes: count(&args[10])?,
        contacts: count(&args[11])?,
        levels: count(&args[12])?,
    };
    let streams = count(&args[13])?;
    let section = count(&args[14])?;
    let passes = count(&args[15])?;
    let rate_bits: u32 = args[16].parse()?;
    let out = Path::new(&args[17]);
    std::fs::create_dir(out)?;
    if streams == 0 || section == 0 || train.len() < streams * (section + 1) {
        return Err("the training text must hold one section a stream".into());
    }
    // A run continues a rested learner (its tower and moments) when one is named; its declaration
    // and rate must be the declared ones.
    let mut learner = if args.len() == 20 {
        let from = pinned_read(&args[18], &args[19], STATE_BUDGET)?;
        let learner = TowerLearner::from_text(std::str::from_utf8(&from)?).map_err(|e| e.to_string())?;
        if learner.tower.declaration != declaration || learner.rate_bits != rate_bits {
            return Err("the continued learner's declaration or rate differs from the declared one".into());
        }
        learner
    } else {
        TowerLearner::new(Tower::found(declaration, &keys).map_err(|e| e.to_string())?, rate_bits)
    };
    let classes: Vec<usize> = train.iter().map(|&b| b as usize).collect();
    let chunk = classes.len() / streams;
    let sections_a_pass = (chunk - 1) / section;
    println!(
        "TOWER_TRAIN material={} streams={} section={} sections_a_pass={} train_bytes={} dev_bytes={}",
        learner.tower.theta.len(), streams, section, sections_a_pass, train.len(), dev.len()
    );
    for pass in 0..passes {
        let pass_started = Instant::now();
        let mut states: Vec<TowerState> = (0..streams).map(|_| learner.tower.rest()).collect();
        let (mut code, mut cells, mut deposits, mut halvings) = (0i64, 0usize, 0usize, 0u32);
        let mut window = (0i64, 0usize);
        for k in 0..sections_a_pass {
            let parts: Vec<&[usize]> = (0..streams)
                .map(|s| &classes[s * chunk + k * section..s * chunk + (k + 1) * section + 1])
                .collect();
            let receipt = match learner.section(&mut states, &parts) {
                Ok(receipt) => receipt,
                Err(e) => {
                    println!("TOWER_SWELL pass={} section={} {}", pass, k + 1, learner.swell_line());
                    return Err(e.to_string().into());
                }
            };
            code += receipt.code_before;
            cells += receipt.cells;
            window.0 += receipt.code_before;
            window.1 += receipt.cells;
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
        let regions = held_out(&learner.tower, &dev, &roles, streams)?;
        let (dev_code, dev_cells) = regions.iter().fold((0i64, 0usize), |a, r| (a.0 + r.0, a.1 + r.1));
        println!(
            "TOWER_PASS pass={} train_bits_a_byte={} dev_bits_a_byte={} dev_regions {} deposits={}/{} pass_ms={} elapsed_ms={}",
            pass, per(code, cells), per(dev_code, dev_cells), region_line(&regions), deposits, sections_a_pass,
            pass_started.elapsed().as_millis(), started.elapsed().as_millis()
        );
        // Each pass's learner rests beside the run, so a run stopped at its deadline keeps its last
        // finished pass.
        let text = learner.to_text();
        let name = format!("STATE.{pass}");
        write_new(&out.join(&name), text.as_bytes())?;
        println!("TOWER_STATE {name} state_bytes={} state_sha256={}", text.len(), sha256(text.as_bytes())?);
    }
    let text = learner.to_text();
    write_new(&out.join("STATE"), text.as_bytes())?;
    println!("TOWER_DONE state_bytes={} state_sha256={} elapsed_ms={}", text.len(), sha256(text.as_bytes())?, started.elapsed().as_millis());
    Ok(())
}

pub(super) fn sample(args: &[String]) -> Result<()> {
    if args.len() != 9 {
        return Err("sample-tower STATE STATE_SHA PROMPT PROMPT_SHA KEYS KEYS_SHA BYTES OUT".into());
    }
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
    let classes: Vec<usize> = prompt.iter().map(|&b| b as usize).collect();
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
        let total = num_bigint::BigInt::from(face.total);
        let exact: Vec<Rat> = face.masses.iter().map(|&u| Rat::new(num_bigint::BigInt::from(u), total.clone())).collect();
        let class = holonics::receiver::release::draw_exact(&exact, &key)?
            .drawn_class()
            .ok_or("an unresolved draw at an exact face")?;
        released.push(class as u8);
        face = tower.advance(&mut modes, class).map_err(|e| e.to_string())?;
    }
    write_new(&out.join("OUTPUT.bin"), &released)?;
    println!(
        "TOWER_SAMPLE prompt_bits_a_byte={} bytes={} elapsed_ms={}",
        per(prompt_code, classes.len().saturating_sub(1).max(1)), released.len(), started.elapsed().as_millis()
    );
    println!("TOWER_SAMPLE_TEXT {:?}", String::from_utf8_lossy(&released));
    Ok(())
}
