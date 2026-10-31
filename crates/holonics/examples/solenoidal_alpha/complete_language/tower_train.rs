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
use holonics::hnn::tower::realization::{HostPass, PassRealization};
use holonics::hnn::tower::split::PairedContacts;
use holonics::hnn::tower::{code_of, ClosureReading, ContactLaw, NewsClock, PairFace as ResidentPairFace, Tower, TowerDeclaration, TowerError, TowerFace, TowerLearner, TowerState, TurnLadder, COVECTOR_BITS, READ_BITS};
use holonics::hnn::units::{Units, CODE_BITS};
use holonics::receiver::coupling::coupling;
use holonics::receiver::release::{agreeing_class, agreement_face};
use num_bigint::BigUint;
use rayon::prelude::*;

/// A learner's state read ceiling, `2^30` bytes.
pub(super) const STATE_BUDGET: usize = 1 << 30;

pub(super) fn count(s: &str) -> Result<usize> {
    Ok(s.parse::<usize>()?)
}

/// A count a text is divided by (a number of streams, a stride): at least one.
pub(super) fn positive(s: &str) -> Result<usize> {
    match count(s)? {
        0 => Err("a stream or stride count must be at least one".into()),
        n => Ok(n),
    }
}

/// The regions an exterior partition names, in order: question, answer prose, answer numbers,
/// calculation markup.
pub(super) const REGIONS: [&str; 4] = ["Q", "P", "N", "M"];

/// The held-out reading: the frozen tower's code of `classes`, cut into `streams` contiguous
/// parts, each read from rest; per region of `roles` (the coded class's region, the region of its
/// first byte), on `2^(−20)` bits, with the bytes coded (`lengths`, each class's bytes).
fn held_out(tower: &Tower, classes: &[usize], lengths: &[u32], roles: &[u8], streams: usize, section: usize, realization: &mut dyn PassRealization) -> Result<[(i64, usize); 4]> {
    // Each part from rest, read through the declared realization (the card's route reads it on
    // the card) in windows of the training section.
    let chunk = classes.len().div_ceil(streams).max(1);
    let parts: Vec<&[usize]> = classes.chunks(chunk).collect();
    let codes = tower.read_parts_realized(&parts, section, realization).map_err(|e| e.to_string())?;
    let mut regions = [(0i64, 0usize); 4];
    for (p, part) in codes.into_iter().enumerate() {
        let start = p * chunk;
        for (i, code) in part.into_iter().enumerate() {
            let region = &mut regions[roles[start + i + 1] as usize];
            region.0 += code;
            region.1 += lengths[start + i + 1] as usize;
        }
    }
    Ok(regions)
}

/// `read-tower-held STATE STATE_SHA DEV DEV_SHA DEV_ROLES DEV_ROLES_SHA STREAMS`: the trainer's
/// held-out read (`held_out`) of a rested learner on byte text, alone: bits a byte by region
/// (`TOWER_HELD`) and each region's code on `2^(−20)` bits over its bytes (`TOWER_HELD_CODES`).
pub(super) fn read_tower_held(args: &[String]) -> Result<()> {
    let usage = "read-tower-held STATE STATE_SHA DEV DEV_SHA DEV_ROLES DEV_ROLES_SHA STREAMS";
    if args.len() != 8 {
        return Err(usage.into());
    }
    let started = Instant::now();
    let learner = TowerLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let dev = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let roles = roles_of(&args[5], &args[6], dev.len())?;
    let streams = positive(&args[7])?;
    let classes: Vec<usize> = dev.iter().map(|&b| b as usize).collect();
    let section = classes.len().div_ceil(streams).max(1);
    let regions = held_out(&learner.tower, &classes, &vec![1; classes.len()], &roles, streams, section, &mut HostPass::default())?;
    let (code, coded) = regions.iter().fold((0i64, 0usize), |a, r| (a.0 + r.0, a.1 + r.1));
    println!(
        "TOWER_HELD streams={streams} dev_bits_a_byte={} dev_regions {} elapsed_ms={}",
        per(code, coded), named_region_line(&REGIONS, &regions), started.elapsed().as_millis()
    );
    let codes: Vec<String> = REGIONS.iter().zip(&regions).map(|(name, &(c, n))| format!("{name}={c}/{n}")).collect();
    println!("TOWER_HELD_CODES grain_bits={READ_BITS} {}", codes.join(" "));
    Ok(())
}

/// `read-tower-held-cells STATE STATE_SHA DEV DEV_SHA STREAMS OUT [UNITS UNITS_SHA]`: the
/// held-out read (`held_out`'s partition, each chunk from rest) written cell by cell to `OUT`
/// (create-new): one line per coded class, the place in `DEV` of its first byte, its code on
/// `2^(−20)` bits, its bytes, and its rank on the face that coded it (how many classes carry more
/// mass; 0 when the face gives it the largest). A unit tower reads `DEV` in the founded `UNITS`. A
/// reading beside the code, for an observer to set each class's code beside what it knows of it (the
/// runs the text shares with the heard text, whether an answer's unit was in its question); nothing
/// here enters the machine.
pub(super) fn read_tower_held_cells(args: &[String]) -> Result<()> {
    let usage = "read-tower-held-cells STATE STATE_SHA DEV DEV_SHA STREAMS OUT [UNITS UNITS_SHA]";
    let units = match args.get(7..).ok_or(usage)? {
        [] => None,
        [path, sha] => Some(Units::from_text(std::str::from_utf8(&pinned_read(path, sha, READ_BUDGET as usize)?)?).map_err(|e| e.to_string())?),
        _ => return Err(usage.into()),
    };
    let learner = TowerLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let dev = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let streams = positive(&args[5])?;
    let (classes, lengths): (Vec<usize>, Vec<usize>) = match &units {
        None => (dev.iter().map(|&b| b as usize).collect(), vec![1; dev.len()]),
        Some(units) => units.parse(&dev).map_err(|e| e.to_string())?.into_iter().map(|u| (u as usize, units.piece(u as usize).len())).unzip(),
    };
    let mut places = Vec::with_capacity(lengths.len());
    lengths.iter().fold(0usize, |at, &n| {
        places.push(at);
        at + n
    });
    let chunk = classes.len().div_ceil(streams);
    let starts: Vec<usize> = (0..classes.len()).step_by(chunk).collect();
    let parts: Vec<Vec<(i64, usize)>> = starts
        .par_iter()
        .map(|&start| {
            let mut state = learner.tower.rest();
            let part = &classes[start..(start + chunk).min(classes.len())];
            let mut read = Vec::with_capacity(part.len());
            learner
                .tower
                .read_faces(&mut state, part, |i, _, face| {
                    read.push((face.code(part[i + 1]), face.rank(part[i + 1])));
                    Ok(())
                })
                .map_err(|e| e.to_string())?;
            Ok(read)
        })
        .collect::<std::result::Result<_, String>>()?;
    let mut written = String::new();
    for (&start, read) in starts.iter().zip(&parts) {
        for (i, (code, rank)) in read.iter().enumerate() {
            written.push_str(&format!("{}\t{code}\t{}\t{rank}\n", places[start + i + 1], lengths[start + i + 1]));
        }
    }
    std::io::Write::write_all(&mut std::fs::OpenOptions::new().write(true).create_new(true).open(&args[6])?, written.as_bytes())?;
    println!(
        "TOWER_HELD_CELLS units={} streams={streams} cells={} grain_bits={READ_BITS} out={}",
        units.as_ref().map_or(0, Units::len), parts.iter().map(Vec::len).sum::<usize>(), args[6]
    );
    Ok(())
}

/// [agent-inferred, October 23] The modes' faces over a text, read through a frozen tower in the
/// held-out read's streams (`held_out`): per level and mode, `max |h|` and `Σ |h|²` over the cells;
/// per level and region of `roles` (the region of the class the state predicts next), the cells'
/// `Σ max_k |h_k|²` against `Σ Σ_k |h_k|²`, the largest mode's share of the level's face energy. A
/// reading beside the code, not material: it locates whether a few swollen modes carry a level's
/// face where the code is lost.
pub(super) fn read_tower_faces(args: &[String]) -> Result<()> {
    if args.len() != 8 {
        return Err("read-tower-faces STATE STATE_SHA TEXT TEXT_SHA ROLES ROLES_SHA STREAMS".into());
    }
    let learner = TowerLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let text = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let roles = roles_of(&args[5], &args[6], text.len())?;
    let streams = positive(&args[7])?;
    let tower = &learner.tower;
    let (levels, modes) = (tower.declaration.levels, tower.declaration.modes);
    // Per level: each mode's max |h|² and Σ|h|², then per region (Σ max_k |h_k|², Σ Σ_k |h_k|², cells),
    // `h` on `2^(−24)`.
    type Faces = Vec<(Vec<(u128, u128)>, [(u128, u128, usize); 4])>;
    let empty = || -> Faces { (0..levels).map(|_| (vec![(0u128, 0u128); modes], [(0u128, 0u128, 0usize); 4])).collect() };
    let chunk = text.len().div_ceil(streams);
    let starts: Vec<usize> = (0..text.len()).step_by(chunk).collect();
    let parts: Vec<Faces> = starts
        .par_iter()
        .map(|&start| {
            let end = (start + chunk).min(text.len());
            let mut state = tower.rest();
            let mut faces = empty();
            for i in start..end.saturating_sub(1) {
                tower.advance(&mut state, text[i] as usize).map_err(|e| e.to_string())?;
                let region = roles[i + 1] as usize;
                for (l, (per_mode, per_region)) in faces.iter_mut().enumerate() {
                    let (mut largest, mut whole) = (0u128, 0u128);
                    let outgrew = || "a face sum outgrew its 128-bit carrier".to_string();
                    for (k, &(re, im)) in state.modes[l].iter().enumerate() {
                        let e = (re.unsigned_abs() as u128).pow(2).checked_add((im.unsigned_abs() as u128).pow(2)).ok_or_else(outgrew)?;
                        per_mode[k].0 = per_mode[k].0.max(e);
                        per_mode[k].1 = per_mode[k].1.checked_add(e).ok_or_else(outgrew)?;
                        largest = largest.max(e);
                        whole = whole.checked_add(e).ok_or_else(outgrew)?;
                    }
                    let r = &mut per_region[region];
                    r.0 = r.0.checked_add(largest).ok_or_else(outgrew)?;
                    r.1 = r.1.checked_add(whole).ok_or_else(outgrew)?;
                    r.2 += 1;
                }
            }
            Ok(faces)
        })
        .collect::<std::result::Result<_, String>>()?;
    let mut faces = empty();
    for part in parts {
        for (l, (per_mode, per_region)) in part.into_iter().enumerate() {
            let outgrew = || "a face sum outgrew its 128-bit carrier";
            for (k, (m, s)) in per_mode.into_iter().enumerate() {
                faces[l].0[k].0 = faces[l].0[k].0.max(m);
                faces[l].0[k].1 = faces[l].0[k].1.checked_add(s).ok_or_else(outgrew)?;
            }
            for (r, (a, b, n)) in per_region.into_iter().enumerate() {
                faces[l].1[r].0 = faces[l].1[r].0.checked_add(a).ok_or_else(outgrew)?;
                faces[l].1[r].1 = faces[l].1[r].1.checked_add(b).ok_or_else(outgrew)?;
                faces[l].1[r].2 += n;
            }
        }
    }
    // `|h|` on `2^(−24)` written on the face's grain `2^(−16)`, as the swell line writes it.
    let unit = |e: u128| e.isqrt() >> (24 - 16);
    let cells: usize = faces.first().map_or(0, |f| f.1.iter().map(|r| r.2).sum());
    for (l, (per_mode, per_region)) in faces.iter().enumerate() {
        let mut order: Vec<usize> = (0..modes).collect();
        order.sort_by_key(|&k| std::cmp::Reverse(per_mode[k].0));
        let top: Vec<String> = order.iter().take(8).map(|&k| format!("{k}:{}/{}", unit(per_mode[k].0), unit(per_mode[k].1 / cells.max(1) as u128))).collect();
        let mut shares = Vec::with_capacity(REGIONS.len());
        for (name, &(a, b, _)) in REGIONS.iter().zip(per_region) {
            let permille = if b == 0 { 0 } else { a.checked_mul(1000).ok_or("a face share outgrew its 128-bit carrier")? / b };
            shares.push(format!("{name}={permille}"));
        }
        println!("TOWER_FACES level={l} cells={cells} largest_share_permille {} top_modes(mode:max/rms, 2^-16) {}", shares.join(" "), top.join(" "));
    }
    Ok(())
}

/// [agent-inferred, October 24] `read-tower-modes STATE STATE_SHA TEXT TEXT_SHA CELLS CELLS_SHA
/// full|after`: the circuit reading ([`Tower::read_circuit`]) mode by mode at the cells `CELLS`
/// names (ascending cell indices, whitespace-separated; cell `i` has heard `TEXT[..=i]` and codes
/// `TEXT[i + 1]`), `TEXT` read as one passage from rest. Each named cell prints `MODES i class
/// code`, then per level `L<l>=` and its modes separated by `;`: with `full`, each mode's
/// `before`, `carried` and `after` (re, im on `2^(−24)`) and `λ_t`, `β_t` (re, im on `2^(−30)`);
/// with `after`, its state after the push alone. An exterior reading; the tower is not moved.
pub(super) fn read_tower_modes(args: &[String]) -> Result<()> {
    if args.len() != 8 {
        return Err("read-tower-modes STATE STATE_SHA TEXT TEXT_SHA CELLS CELLS_SHA full|after".into());
    }
    let full = match args[7].as_str() {
        "full" => true,
        "after" => false,
        _ => return Err("the fields are full or after".into()),
    };
    let learner = TowerLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let text = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let classes: Vec<usize> = text.iter().map(|&b| b as usize).collect();
    let cells: Vec<usize> = std::str::from_utf8(&pinned_read(&args[5], &args[6], READ_BUDGET as usize)?)?.split_whitespace().map(count).collect::<Result<_>>()?;
    let Some(&last) = cells.last() else {
        return Err("CELLS names no cell".into());
    };
    if cells.windows(2).any(|w| w[0] >= w[1]) || last + 1 >= classes.len() {
        return Err("CELLS must ascend and code a class inside the passage".into());
    }
    let tower = &learner.tower;
    let mut state = tower.rest();
    let (mut line, mut next) = (String::new(), 0);
    tower
        .read_circuit(&mut state, &classes[..last + 2], |i, cell| {
            use std::fmt::Write as _;
            if cells.get(next) != Some(&i) {
                return Ok(());
            }
            next += 1;
            line.clear();
            let _ = write!(line, "MODES {i} {} {}", classes[i + 1], cell.code);
            for (l, c) in cell.levels.iter().enumerate() {
                let _ = write!(line, " L{l}=");
                for (k, m) in c.modes.iter().enumerate() {
                    if k > 0 {
                        line.push(';');
                    }
                    let _ = if full {
                        write!(
                            line,
                            "{},{},{},{},{},{},{},{},{},{}",
                            m.before.0, m.before.1, m.carried.0, m.carried.1, m.after.0, m.after.1, m.lam.0, m.lam.1, m.beta.0, m.beta.1
                        )
                    } else {
                        write!(line, "{},{}", m.after.0, m.after.1)
                    };
                }
            }
            println!("{line}");
            Ok(())
        })
        .map_err(|e| e.to_string())?;
    Ok(())
}

/// [agent-inferred, October 24] `read-tower-circuit STATE STATE_SHA TEXT TEXT_SHA`: the frozen
/// tower reads `TEXT` as one passage from rest, and every cell's power is printed beside its code
/// ([`Tower::read_circuit`]): `CIRCUIT i class code` on `2^(−20)` bits, then per level
/// `before,carried,after` on `2^(−48)` and `scale,drive,conduct` on `2^(−16)`. A reading beside the
/// code for an exterior partition of the passage (where the energy expands, where it is lost, where
/// the push cancels what the modes carry); the tower is not moved.
pub(super) fn read_tower_circuit(args: &[String]) -> Result<()> {
    if args.len() != 5 {
        return Err("read-tower-circuit STATE STATE_SHA TEXT TEXT_SHA".into());
    }
    let learner = TowerLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let text = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let classes: Vec<usize> = text.iter().map(|&b| b as usize).collect();
    let tower = &learner.tower;
    let mut state = tower.rest();
    let mut line = String::new();
    tower
        .read_circuit(&mut state, &classes, |i, cell| {
            use std::fmt::Write as _;
            line.clear();
            let _ = write!(line, "CIRCUIT {i} {} {}", classes[i + 1], cell.code);
            for (l, c) in cell.levels.iter().enumerate() {
                let _ = write!(line, " L{l}={},{},{},{},{},{}", c.before, c.carried, c.after, c.scale, c.drive, c.conduct);
            }
            println!("{line}");
            Ok(())
        })
        .map_err(|e| e.to_string())?;
    Ok(())
}

/// `Q=… P=… N=… M=…`: bits a byte per region.
/// `read-tower-pair STATE STATE_SHA`: where a pair tower's bilinear weight sits
/// ([`Tower::bilinear_rungs`]), each level's weight on the founded memory rungs of the two drives'
/// modes, in thousandths of the level's whole (`TOWER_PAIR_RUNGS`, the first drive's rung by row),
/// and its three parts with the ladder's upper half as the held rungs and its lower half as the
/// fast (agent-inferred: the halves of the declared ladder, no cut chosen from the material):
/// held × fast (both orders), fast × fast and held × held (`TOWER_PAIR`).
pub(super) fn read_tower_pair(args: &[String]) -> Result<()> {
    if args.len() != 3 {
        return Err("read-tower-pair STATE STATE_SHA".into());
    }
    let learner = TowerLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let levels = learner.tower.bilinear_rungs().map_err(|e| e.to_string())?;
    let thousandths = |part: &BigUint, whole: &BigUint| -> String {
        if *whole == BigUint::from(0u32) { "0".into() } else { ((part * 1000u32 + whole / 2u32) / whole).to_string() }
    };
    for (l, e) in levels.iter().enumerate() {
        let rungs = e.len();
        let whole: BigUint = e.iter().flatten().sum();
        let held = |s: usize| 2 * s >= rungs;
        let part = |keep: &dyn Fn(usize, usize) -> bool| -> BigUint {
            (0..rungs).flat_map(|s| (0..rungs).map(move |t| (s, t))).filter(|&(s, t)| keep(s, t)).map(|(s, t)| e[s][t].clone()).sum()
        };
        let held_fast = part(&|s, t| held(s) != held(t));
        let fast_fast = part(&|s, t| !held(s) && !held(t));
        let held_held = part(&|s, t| held(s) && held(t));
        println!(
            "TOWER_PAIR level={l} rungs={rungs} held_from_rung={} held_x_fast={} fast_x_fast={} held_x_held={} whole_bits={}",
            rungs.div_ceil(2),
            thousandths(&held_fast, &whole),
            thousandths(&fast_fast, &whole),
            thousandths(&held_held, &whole),
            whole.bits()
        );
        let rows: Vec<String> = e.iter().map(|row| row.iter().map(|x| thousandths(x, &whole)).collect::<Vec<_>>().join(",")).collect();
        println!("TOWER_PAIR_RUNGS level={l} {}", rows.join(";"));
    }
    Ok(())
}

/// [agent-inferred, October 27] `read-tower-pair-modes STATE STATE_SHA`: where a pair tower's
/// bilinear weight sits entry by entry ([`Tower::bilinear_modes`]), in thousandths of the level's
/// whole. Per level, each drive's weight on every entry (`TOWER_PAIR_MODES drive=first|second`,
/// `entry:thousandths`: the level's modes, then on the strands' level each strand residue's face);
/// on the strands' level, the block between the modes and each strand residue (named by its
/// strand's law and its ring's modulus; `TOWER_PAIR_STRANDS`, rows the first drive's), and the
/// comparison's own entries, a turned residue against the stepped residue of its ring in either
/// order (`TOWER_PAIR_COMPARISON`). Record
/// `2026-10-26_THE_OPERANDS_ARE_HELD_BY_LOCATED_STRANDS_AND_THE_RESULT_IS_READ_ON_THE_RING_THAT_CLOSES.md`
/// §6 and §7: a coefficient multiplies the entry's face, so what a contact hears of a mode is this
/// weight times the mode's loudness (`numeral_rings.py scale`), and of a strand's face, at amplitude
/// one, this weight. An exterior reading; the tower is not moved.
pub(super) fn read_tower_pair_modes(args: &[String]) -> Result<()> {
    if args.len() != 3 {
        return Err("read-tower-pair-modes STATE STATE_SHA".into());
    }
    let learner = TowerLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let tower = &learner.tower;
    let levels = tower.bilinear_modes().map_err(|e| e.to_string())?;
    let per = |part: &BigUint, whole: &BigUint, scale: u32| -> String {
        if *whole == BigUint::from(0u32) { "0".into() } else { ((part * scale + whole / 2u32) / whole).to_string() }
    };
    let thousandths = |part: &BigUint, whole: &BigUint| per(part, whole, 1000);
    for (l, level) in levels.iter().enumerate() {
        for (name, drive) in [("first", &level.first), ("second", &level.second)] {
            let whole: BigUint = drive.iter().sum();
            let each: Vec<String> = drive.iter().enumerate().map(|(k, x)| format!("{k}:{}", thousandths(x, &whole))).collect();
            println!("TOWER_PAIR_MODES level={l} drive={name} whole_bits={} {}", whole.bits(), each.join(" "));
        }
        let Some(strands) = tower.strands().filter(|s| s.level() == l) else {
            continue;
        };
        let whole: BigUint = level.block.iter().flatten().sum();
        let rings = strands.rings();
        let (n, entries) = (tower.declaration.modes, level.first.len());
        // Groups: the level's modes, then each strand residue.
        let group = |k: usize| if k < n { 0 } else { 1 + k - n };
        let mut names = vec!["modes".to_string()];
        for law in strands.laws() {
            for ring in rings {
                names.push(format!("{}{}", law.name(), ring.modulus));
            }
        }
        let g = names.len();
        let mut e = vec![vec![BigUint::from(0u32); g]; g];
        for k in 0..entries {
            for k2 in 0..entries {
                e[group(k)][group(k2)] += &level.block[k][k2];
            }
        }
        let rows: Vec<String> = e.iter().map(|row| row.iter().map(|x| thousandths(x, &whole)).collect::<Vec<_>>().join(",")).collect();
        println!("TOWER_PAIR_STRANDS level={l} whole_bits={} groups={} {}", whole.bits(), names.join(","), rows.join(";"));
        // The comparison's entries: the turned and the stepped strand of one ring, both orders.
        let at = |law: holonics::hnn::tower::StrandLaw| strands.laws().iter().position(|&x| x == law);
        if let (Some(t), Some(s)) = (at(holonics::hnn::tower::StrandLaw::Turned), at(holonics::hnn::tower::StrandLaw::Stepped)) {
            let entries: Vec<String> = rings
                .iter()
                .enumerate()
                .map(|(i, ring)| {
                    let (a, b) = (n + t * rings.len() + i, n + s * rings.len() + i);
                    let both = &level.block[a][b] + &level.block[b][a];
                    format!("{}:{}/{}", ring.modulus, thousandths(&both, &whole), per(&both, &whole, 1_000_000))
                })
                .collect();
            println!("TOWER_PAIR_COMPARISON level={l} (ring:thousandths/millionths) {}", entries.join(" "));
        }
    }
    Ok(())
}

/// `read-tower-tension STATE STATE_SHA TEXT TEXT_SHA ROLES ROLES_SHA STREAMS`: the tension a frozen
/// tower leaves on a text ([`TensionCell`], the mathematics thread's split of October 24), per
/// region of `roles`, at line starts (the cells read just after a line feed, pooled over the
/// regions) and over the whole, read in the held-out read's streams from rest.
///
/// [agent-inferred, October 24] Each cell `v = (top, 1, quadrature, below, foil, dz)` deposits
/// `v vᵀ` into its region's joint Gram, exact in `i128`; the foil is the quadrature read half a
/// stream away in the same stream, a face of the same medium that is not aligned with the cell's
/// comparison; the region is the exterior reader's own face (one cell of four on, the region of the
/// arriving class), read only here: how much of the tension a face that carried the medium
/// perfectly would bridge, the reference the tower's own faces are read against. Fraction-free elimination of the face block `f̄ = (top, 1)` leaves `d·S` on the
/// covector block, `d` the last pivot, so every reading below is a ratio of exact integers:
/// `tr T` per cell is the Brier score of the faces; `S` is what no readout of `top` bridges;
/// the most opposed class pairs are the most negative `S_ab`; a candidate face's drop is the part
/// of `tr S` its own unread part carries (eliminating its block after the face's).
pub(super) fn read_tower_tension(args: &[String]) -> Result<()> {
    if args.len() != 8 {
        return Err("read-tower-tension STATE STATE_SHA TEXT TEXT_SHA ROLES ROLES_SHA STREAMS".into());
    }
    let started = std::time::Instant::now();
    let learner = TowerLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let text = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let roles = roles_of(&args[5], &args[6], text.len())?;
    let streams = positive(&args[7])?;
    let tower = &learner.tower;
    let (w, a) = (tower.declaration.width, tower.declaration.alphabet);
    let layout = TensionLayout { w, a };
    let dim = layout.dim();
    let chunk = text.len().div_ceil(streams.max(1));
    let starts: Vec<usize> = (0..text.len()).step_by(chunk).collect();
    // Per stream, each region's upper triangle and `Σ max|v|²`, the bound its carrier must hold.
    let grams: Vec<Vec<(Vec<i128>, u128, usize)>> = starts
        .par_iter()
        .map(|&start| {
            let end = (start + chunk).min(text.len());
            let classes: Vec<usize> = text[start..end].iter().map(|&b| b as usize).collect();
            let mut state = tower.rest();
            let mut cells = Vec::with_capacity(classes.len());
            tower.read_tension(&mut state, &classes, |cell| {
                cells.push(cell);
                Ok(())
            })
            .map_err(|e| e.to_string())?;
            // The four regions, then the line starts.
            let mut regions: Vec<(Vec<i128>, u128, usize)> = (0..5).map(|_| (vec![0i128; dim * dim], 0u128, 0usize)).collect();
            let half = cells.len() / 2;
            let mut v = vec![0i64; dim];
            for (i, cell) in cells.iter().enumerate() {
                let foil = &cells[(i + half) % cells.len()].quadrature;
                layout.fill(&mut v, cell, foil, roles[start + i + 1] as usize);
                let reach = v.iter().map(|x| x.unsigned_abs() as u128).max().unwrap_or(0);
                let start_of_line = classes[i] == b'\n' as usize;
                for part in [roles[start + i + 1] as usize].into_iter().chain(start_of_line.then_some(4)) {
                    let region = &mut regions[part];
                    region.1 = region.1.checked_add(reach * reach).filter(|&b| b < 1u128 << 126).ok_or("a tension Gram outgrew its 128-bit carrier")?;
                    region.2 += 1;
                    for (r, &vi) in v.iter().enumerate() {
                        if vi == 0 {
                            continue;
                        }
                        let row = &mut region.0[r * dim..(r + 1) * dim];
                        for (slot, &vj) in row[r..].iter_mut().zip(&v[r..]) {
                            *slot += vi as i128 * vj as i128;
                        }
                    }
                }
            }
            Ok(regions)
        })
        .collect::<std::result::Result<_, String>>()?;
    // The four regions, the line starts and the whole (the regions' sum).
    let mut parts: Vec<(Vec<i128>, u128, usize)> = (0..6).map(|_| (vec![0i128; dim * dim], 0u128, 0usize)).collect();
    for stream in grams {
        for (r, (g, bound, n)) in stream.into_iter().enumerate() {
            for p in if r < 4 { vec![r, 5] } else { vec![4] } {
                let part = &mut parts[p];
                part.1 = part.1.checked_add(bound).filter(|&b| b < 1u128 << 126).ok_or("a tension Gram outgrew its 128-bit carrier")?;
                part.2 += n;
                for (slot, x) in part.0.iter_mut().zip(&g) {
                    *slot += x;
                }
            }
        }
    }
    println!("TENSION_READ cells={} streams={} dim={dim} read_ms={}", parts[5].2, streams, started.elapsed().as_millis());
    let names = ["prose", "lean", "rust", "digits", "starts", "all"];
    for (p, (g, _, n)) in parts.iter().enumerate() {
        if *n == 0 {
            continue;
        }
        tension_part(&layout, names[p], g, *n, started)?;
    }
    Ok(())
}

/// The joint face of one cell: `top`, the unit, the quadrature, the face below, the foil, the
/// exterior region and the covector, in that order.
struct TensionLayout {
    w: usize,
    a: usize,
}

impl TensionLayout {
    fn dim(&self) -> usize {
        4 * self.w + 5 + self.a
    }
    fn face(&self) -> std::ops::Range<usize> {
        0..self.w + 1
    }
    fn quadrature(&self) -> std::ops::Range<usize> {
        self.w + 1..2 * self.w + 1
    }
    fn below(&self) -> std::ops::Range<usize> {
        2 * self.w + 1..3 * self.w + 1
    }
    fn foil(&self) -> std::ops::Range<usize> {
        3 * self.w + 1..4 * self.w + 1
    }
    fn region(&self) -> std::ops::Range<usize> {
        4 * self.w + 1..4 * self.w + 5
    }
    fn covector(&self) -> std::ops::Range<usize> {
        4 * self.w + 5..self.dim()
    }
    fn fill(&self, v: &mut [i64], cell: &holonics::hnn::tower::TensionCell, foil: &[i32], region: usize) {
        let w = self.w;
        for j in 0..w {
            v[j] = cell.top[j] as i64;
            v[w + 1 + j] = cell.quadrature[j] as i64;
            v[2 * w + 1 + j] = cell.below[j] as i64;
            v[3 * w + 1 + j] = foil[j] as i64;
        }
        v[w] = 1;
        for (k, slot) in v[4 * w + 1..4 * w + 5].iter_mut().enumerate() {
            *slot = (k == region) as i64;
        }
        v[4 * w + 5..].copy_from_slice(&cell.covector);
    }
}

/// A symmetric matrix kept by its upper rows, `rows[i][j − i]`.
struct Upper {
    rows: Vec<Vec<num_bigint::BigInt>>,
}

impl Upper {
    fn from_gram(g: &[i128], dim: usize) -> Self {
        Self { rows: (0..dim).map(|i| (i..dim).map(|j| num_bigint::BigInt::from(g[i * dim + j])).collect()).collect() }
    }
    fn get(&self, i: usize, j: usize) -> &num_bigint::BigInt {
        if i <= j { &self.rows[i][j - i] } else { &self.rows[j][i - j] }
    }

    /// Fraction-free (Bareiss) elimination of `pivots` in order, over the entries whose indices are
    /// both live (the pivots not yet eliminated and `keep`), skipping a pair `thin` names; `last`
    /// is the last pivot before. A zero pivot of a positive semidefinite matrix has a zero row and
    /// is passed over (refused otherwise). Returns the last pivot and the pivots that were not zero.
    fn eliminate(&mut self, pivots: &[usize], keep: &[usize], mut last: num_bigint::BigInt, thin: &(dyn Fn(usize, usize) -> bool + Sync)) -> Result<(num_bigint::BigInt, usize)> {
        use num_traits::Zero;
        let dim = self.rows.len();
        let mut live = vec![false; dim];
        for &i in pivots.iter().chain(keep) {
            live[i] = true;
        }
        let mut rank = 0;
        for &p in pivots {
            live[p] = false;
            let pivot = self.get(p, p).clone();
            let column: Vec<num_bigint::BigInt> = (0..dim).map(|i| if live[i] { self.get(i, p).clone() } else { num_bigint::BigInt::zero() }).collect();
            if pivot.is_zero() {
                if column.iter().any(|x| !x.is_zero()) {
                    return Err("a zero pivot with a nonzero row: the Gram is not positive semidefinite".into());
                }
                continue;
            }
            rank += 1;
            let live_ref = &live;
            self.rows.par_iter_mut().enumerate().filter(|(i, _)| live_ref[*i]).for_each(|(i, row)| {
                for (k, slot) in row.iter_mut().enumerate() {
                    let j = i + k;
                    if !live_ref[j] || thin(i, j) {
                        continue;
                    }
                    *slot = (&pivot * &*slot - &column[i] * &column[j]) / &last;
                }
            });
            last = pivot;
        }
        Ok((last, rank))
    }
}

/// `num/den` as a decimal with three places (both nonnegative), or with a sign.
fn thousandths_of(num: &num_bigint::BigInt, den: &num_bigint::BigInt) -> String {
    use num_traits::Signed;
    let milli = (num.abs() * 1000 + den / 2) / den;
    format!("{}{}.{:03}", if num.is_negative() { "-" } else { "" }, &milli / 1000, &milli % 1000)
}

/// A class byte as text.
fn class_name(c: usize) -> String {
    if c < 0x80 { format!("{:?}", c as u8 as char) } else { format!("0x{c:02x}") }
}

fn tension_part(layout: &TensionLayout, name: &str, gram: &[i128], cells: usize, started: std::time::Instant) -> Result<()> {
    use num_bigint::BigInt;
    use num_traits::{One, Signed, Zero};
    let dim = layout.dim();
    let mut m = Upper::from_gram(gram, dim);
    let z = layout.covector();
    let in_z = |i: usize| z.contains(&i);
    // The covector block's trace: `tr T` before any elimination, `d·tr S` after the face's.
    let trace = |m: &Upper| -> BigInt { z.clone().map(|c| m.get(c, c).clone()).sum() };
    // `tr T`, on 2^(−48) a cell.
    let tr_t = trace(&m);
    let unit = BigInt::from(cells) << 48;
    let face: Vec<usize> = layout.face().collect();
    let rest: Vec<usize> = (layout.w + 1..dim).collect();
    let (d, rank) = m.eliminate(&face, &rest, BigInt::one(), &|_, _| false)?;
    let tr_ds = trace(&m);
    // tr S = tr_ds / d.
    let bridged = &tr_t * &d - &tr_ds;
    println!(
        "TENSION part={name} cells={cells} face_rank={rank} brier_T={} tension_S={} bridged_by_readout_permille={} tension_permille={} elapsed_ms={}",
        thousandths_of(&tr_t, &unit),
        thousandths_of(&tr_ds, &(&unit * &d)),
        thousandths_of(&(&bridged * 1000), &(&tr_t * &d)),
        thousandths_of(&(&tr_ds * 1000), &(&tr_t * &d)),
        started.elapsed().as_millis()
    );
    // The most opposed class pairs: the most negative d·S_ab, with S_ab/√(S_aa S_bb).
    let mut pairs: Vec<(BigInt, usize, usize)> = Vec::new();
    for i in z.clone() {
        for j in i + 1..z.end {
            let s = m.get(i, j);
            if s.is_negative() {
                pairs.push((s.clone(), i, j));
            }
        }
    }
    pairs.sort_by(|x, y| x.0.cmp(&y.0));
    let opposed: Vec<String> = pairs
        .iter()
        .take(16)
        .map(|(s, i, j)| {
            let scale = (m.get(*i, *i) * m.get(*j, *j)).sqrt();
            let corr = if scale.is_zero() { "0".into() } else { thousandths_of(s, &scale) };
            format!("{}|{}:{}:{}", class_name(i - z.start), class_name(j - z.start), thousandths_of(s, &(&unit * &d)), corr)
        })
        .collect();
    println!("TENSION_OPPOSED part={name} (a|b:S_ab per cell:correlation) {}", opposed.join(" "));
    // Each class's own tension S_aa per cell, the largest.
    let mut own: Vec<(BigInt, usize)> = z.clone().map(|c| (m.get(c, c).clone(), c - z.start)).collect();
    own.sort_by(|x, y| y.0.cmp(&x.0));
    let own: Vec<String> = own.iter().take(16).map(|(s, c)| format!("{}:{}", class_name(*c), thousandths_of(s, &(&unit * &d)))).collect();
    println!("TENSION_OWN part={name} (a:S_aa per cell) {}", own.join(" "));
    // The candidates: each eliminated after the face, on the covector's diagonal.
    let zs: Vec<usize> = z.clone().collect();
    let thin = |i: usize, j: usize| i != j && in_z(i) && in_z(j);
    let candidates: [(&str, Vec<usize>, Vec<usize>); 5] = [
        ("quadrature", layout.quadrature().collect(), Vec::new()),
        ("below", layout.below().collect(), Vec::new()),
        ("foil", layout.foil().collect(), Vec::new()),
        ("quadrature+below", layout.quadrature().collect(), layout.below().collect()),
        ("region", layout.region().collect(), Vec::new()),
    ];
    for (label, first, second) in candidates {
        let mut c = Upper { rows: m.rows.clone() };
        let pivots: Vec<usize> = first.iter().chain(&second).copied().collect();
        let (d2, rank2) = c.eliminate(&pivots, &zs, d.clone(), &thin)?;
        let tr_after = trace(&c);
        // drop = tr S − tr S_after = tr_ds/d − tr_after/d2.
        let drop = &tr_ds * &d2 - &tr_after * &d;
        let dd = &d * &d2;
        println!(
            "TENSION_CANDIDATE part={name} face={label} novel_rank={rank2} drop={} drop_of_tension_permille={} elapsed_ms={}",
            thousandths_of(&drop, &(&unit * &dd)),
            thousandths_of(&(&drop * 1000 * &d), &(&tr_ds * &dd)),
            started.elapsed().as_millis()
        );
    }
    Ok(())
}


/// `read-tower-floor STATE STATE_SHA TRAIN TRAIN_SHA TRAIN_ROLES TRAIN_ROLES_SHA DEV DEV_SHA
/// DEV_ROLES DEV_ROLES_SHA STREAMS ORDER`: how much of the tension a frozen tower leaves is the
/// text's floor and how much a new face could still carry, read against two exterior references
/// (the mathematics thread's split of October 24): a count model of the last bytes, and the linear
/// face of the last `ORDER` bytes' encodings.
///
/// [agent-inferred, October 24] The count model is an exterior reader, never a face of the
/// machine: the bytes that followed each context of `j ≤ 2·ORDER` bytes in the training text,
/// interpolated from the longest context down (Witten–Bell: a context that has been followed by
/// `n` distinct bytes in `C` arrivals keeps `n/(C + n)` for the order below) to the training
/// text's byte counts, on `2^(−48)` rounded to nearest at each order and read on `2^(−24)`, the
/// covector's grain. On the held-out text it counts the training text; on the training text it
/// counts it with the cell's own arrival deleted (the deleted estimate), so both of its Brier
/// scores are out of sample. Its Brier per region beside the tower's is the first split: what a
/// conjunction of the last bytes knows that the tower does not.
///
/// The second split is read on the training text, whose 1.8 million cells keep a face of a few
/// hundred coordinates from removing more than a thousandth of the tension by chance (the held-out
/// text's twelve thousand cells a medium would let it remove about 2% by chance, the size of the
/// signal). Each cell `v = (top, 1, E(u_t), …, E(u_(t−ORDER+1)), p_ORDER, foil, dz)` deposits
/// `v vᵀ` into one joint Gram, exact in `i128` (the covector's off-diagonal entries are not kept:
/// only its trace and diagonal are read). After the face's elimination the encodings are eliminated
/// one block at a time (the drop of the linear face of the last `k` bytes, what a new mode driven
/// by the encodings could carry), then the count model's prediction (the conjunction past that
/// linear face); separately the count model alone, and the foil (the encoding of the byte half a
/// stream away). Per class, the drops of its own tension `S_aa` say which contrasts a mode could
/// carry and which only a conjunction.
pub(super) fn read_tower_floor(args: &[String]) -> Result<()> {
    if args.len() != 13 {
        return Err("read-tower-floor STATE STATE_SHA TRAIN TRAIN_SHA TRAIN_ROLES TRAIN_ROLES_SHA DEV DEV_SHA DEV_ROLES DEV_ROLES_SHA STREAMS ORDER".into());
    }
    let started = std::time::Instant::now();
    let learner = TowerLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let train = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let train_roles = roles_of(&args[5], &args[6], train.len())?;
    let dev = pinned_read(&args[7], &args[8], READ_BUDGET as usize)?;
    let dev_roles = roles_of(&args[9], &args[10], dev.len())?;
    let streams = positive(&args[11])?;
    let order = count(&args[12])?;
    if order == 0 || 2 * order > 7 {
        return Err("the reference order must be between one and three (contexts of up to seven bytes are keyed in 64 bits)".into());
    }
    let tower = &learner.tower;
    let (w, a) = (tower.declaration.width, tower.declaration.alphabet);
    let cut = |text: &[u8]| -> Vec<Vec<usize>> {
        let chunk = text.len().div_ceil(streams.max(1));
        text.chunks(chunk).map(|s| s.iter().map(|&b| b as usize).collect()).collect()
    };
    let (train_streams, dev_streams) = (cut(&train), cut(&dev));
    let followers = Followers::count(&train_streams, 2 * order, a);
    println!(
        "FLOOR_COUNTS contexts_per_order={} seen_classes={} counted_ms={}",
        followers.orders.iter().map(|o| o.len().to_string()).collect::<Vec<_>>().join(","),
        followers.seen.len(),
        started.elapsed().as_millis()
    );
    // The Brier scores, per part: the tower's and the count model's at each order. The held-out
    // text is read here; the training text beside its Gram, below.
    let names = ["prose", "lean", "rust", "digits", "starts", "all"];
    let top = 2 * order;
    let chunk = dev_roles.len().div_ceil(streams.max(1));
    let held_out: Vec<BrierParts> = dev_streams
        .par_iter()
        .enumerate()
        .map(|(s, classes)| {
            let mut parts = BrierParts::new(top);
            let mut state = tower.rest();
            let mut ps = vec![vec![0u128; a]; top + 1];
            let mut i = 0usize;
            tower.read_tension(&mut state, classes, |cell| {
                followers.predict(classes, i, false, &mut ps);
                parts.add(&followers, &cell, &ps, classes, i, dev_roles[s * chunk + i + 1] as usize);
                i += 1;
                Ok(())
            })
            .map_err(|e| e.to_string())?;
            Ok(parts)
        })
        .collect::<std::result::Result<_, String>>()?;
    BrierParts::print("held_out", &names, &held_out, started);
    // The joint Gram on the training text, the whole, with the deleted count model's Brier.
    let layout = FloorLayout { w, a, order };
    let dim = layout.dim();
    let chunk = train_roles.len().div_ceil(streams.max(1));
    let grams: Vec<(Vec<i128>, u128, usize, BrierParts)> = train_streams
        .par_iter()
        .enumerate()
        .map(|(s, classes)| {
            let mut gram = vec![0i128; dim * dim];
            let (mut bound, mut n) = (0u128, 0usize);
            let mut parts = BrierParts::new(top);
            let mut state = tower.rest();
            let mut ps = vec![vec![0u128; a]; top + 1];
            let mut v = vec![0i64; dim];
            let mut nz: Vec<usize> = Vec::with_capacity(dim);
            let half = classes.len().saturating_sub(1) / 2;
            let cells = classes.len().saturating_sub(1);
            let cov = layout.covector();
            // The cross moments are kept for the coordinates the eliminations read: every one but
            // the covector of a class that never arrives, whose diagonal alone is kept.
            let mut crossed = vec![true; dim];
            for c in cov.clone() {
                crossed[c] = false;
            }
            for &c in &followers.seen {
                crossed[cov.start + c] = true;
            }
            let mut i = 0usize;
            tower.read_tension(&mut state, classes, |cell| {
                followers.predict(classes, i, true, &mut ps);
                parts.add(&followers, &cell, &ps, classes, i, train_roles[s * chunk + i + 1] as usize);
                let foil = classes[(i + half) % cells.max(1)];
                layout.fill(&mut v, tower, &cell, classes, i, &ps[order], foil);
                let reach = v.iter().map(|x| x.unsigned_abs() as u128).max().unwrap_or(0);
                bound = bound.saturating_add(reach * reach);
                n += 1;
                nz.clear();
                for r in 0..dim {
                    if v[r] == 0 {
                        continue;
                    }
                    if crossed[r] {
                        nz.push(r);
                    } else {
                        gram[r * dim + r] += v[r] as i128 * v[r] as i128;
                    }
                }
                for (x, &r) in nz.iter().enumerate() {
                    let vr = v[r] as i128;
                    let row = &mut gram[r * dim..(r + 1) * dim];
                    if cov.contains(&r) {
                        row[r] += vr * vr;
                        continue;
                    }
                    for &c in &nz[x..] {
                        row[c] += vr * v[c] as i128;
                    }
                }
                i += 1;
                Ok(())
            })
            .map_err(|e| e.to_string())?;
            if bound >= 1u128 << 126 {
                return Err("a floor Gram outgrew its 128-bit carrier".to_string());
            }
            Ok((gram, bound, n, parts))
        })
        .collect::<std::result::Result<_, String>>()?;
    let mut gram = vec![0i128; dim * dim];
    let (mut bound, mut cells) = (0u128, 0usize);
    let mut training = Vec::with_capacity(grams.len());
    for (g, b, n, parts) in grams {
        bound = bound.checked_add(b).filter(|&b| b < 1u128 << 126).ok_or("a floor Gram outgrew its 128-bit carrier")?;
        cells += n;
        for (slot, x) in gram.iter_mut().zip(&g) {
            *slot += x;
        }
        training.push(parts);
    }
    BrierParts::print("training_deleted", &names, &training, started);
    println!("FLOOR_READ cells={cells} streams={streams} dim={dim} read_ms={}", started.elapsed().as_millis());
    floor_chains(&layout, &gram, cells, &followers.seen, started)
}

/// The Brier scores of one stream, per part (the four regions, the line starts, the whole): the
/// tower's (`tr T`, `Σ dz²` on `2^(−48)`), the count model's at each order, and the cells.
struct BrierParts {
    parts: Vec<(i128, Vec<i128>, usize)>,
}

impl BrierParts {
    fn new(top: usize) -> Self {
        Self { parts: (0..6).map(|_| (0i128, vec![0i128; top + 1], 0usize)).collect() }
    }

    /// Cell `i`, read after `classes[i]` at `classes[i + 1]`, of `role` (the arriving class's
    /// region): into its region, the whole, and the line starts when it reads a line feed.
    fn add(&mut self, followers: &Followers, cell: &holonics::hnn::tower::TensionCell, ps: &[Vec<u128>], classes: &[usize], i: usize, role: usize) {
        let target = classes[i + 1];
        let tower: i128 = cell.covector.iter().map(|&x| x as i128 * x as i128).sum();
        let start_of_line = classes[i] == b'\n' as usize;
        for p in [role, 5].into_iter().chain(start_of_line.then_some(4)) {
            let part = &mut self.parts[p];
            part.0 += tower;
            for (slot, prediction) in part.1.iter_mut().zip(ps) {
                *slot += followers.brier(prediction, target);
            }
            part.2 += 1;
        }
    }

    fn print(label: &str, names: &[&str], streams: &[BrierParts], started: std::time::Instant) {
        for (p, name) in names.iter().enumerate() {
            let top = streams.first().map_or(0, |s| s.parts[p].1.len());
            let (mut tower, mut counts, mut n) = (0i128, vec![0i128; top], 0usize);
            for stream in streams {
                tower += stream.parts[p].0;
                for (slot, x) in counts.iter_mut().zip(&stream.parts[p].1) {
                    *slot += x;
                }
                n += stream.parts[p].2;
            }
            if n == 0 {
                continue;
            }
            let unit = num_bigint::BigInt::from(n) << 48;
            let orders: Vec<String> = counts.iter().enumerate().map(|(j, x)| format!("order{j}={}", thousandths_of(&num_bigint::BigInt::from(*x), &unit))).collect();
            println!("FLOOR_BRIER text={label} part={name} cells={n} tower={} {} elapsed_ms={}", thousandths_of(&num_bigint::BigInt::from(tower), &unit), orders.join(" "), started.elapsed().as_millis());
        }
    }
}

/// The bytes that followed each context of a text, per order, and the bytes it contains.
struct Followers {
    /// `orders[j]`: a context of `j` bytes (keyed by its bytes, the last lowest) → the bytes that
    /// followed it with their counts, and their total.
    orders: Vec<std::collections::HashMap<u64, (Vec<(u8, u32)>, u32)>>,
    /// The classes the text contains, the only ones a count gives mass.
    seen: Vec<usize>,
}

impl Followers {
    /// The context of `j` bytes ending at cell `i`.
    fn key(classes: &[usize], i: usize, j: usize) -> u64 {
        classes[i + 1 - j..=i].iter().fold(0u64, |k, &c| (k << 8) | c as u64)
    }

    fn count(streams: &[Vec<usize>], top: usize, a: usize) -> Self {
        let mut orders: Vec<std::collections::HashMap<u64, (Vec<(u8, u32)>, u32)>> = (0..=top).map(|_| std::collections::HashMap::new()).collect();
        for s in streams {
            for i in 0..s.len().saturating_sub(1) {
                let next = s[i + 1] as u8;
                for (j, order) in orders.iter_mut().enumerate().take(top.min(i + 1) + 1) {
                    let entry = order.entry(Self::key(s, i, j)).or_insert_with(|| (Vec::new(), 0));
                    match entry.0.iter_mut().find(|(b, _)| *b == next) {
                        Some(slot) => slot.1 += 1,
                        None => entry.0.push((next, 1)),
                    }
                    entry.1 += 1;
                }
            }
        }
        let seen = orders[0].get(&0).map(|(f, _)| f.iter().map(|&(b, _)| b as usize).filter(|&b| b < a).collect::<Vec<_>>()).unwrap_or_default();
        let mut seen = seen;
        seen.sort_unstable();
        Self { orders, seen }
    }

    /// The count model's prediction after cell `i` at each order `j < ps.len()`, on `2^(−48)`:
    /// `p_0(b) = c(b)/C`; `p_j(b) = (c_j(b) + n_j p_(j−1)(b))/(C_j + n_j)`, the order below where
    /// the context is shorter than `j` or was never followed. `deleted`: the cell's own arrival,
    /// `classes[i + 1]`, is removed from every count it entered.
    fn predict(&self, classes: &[usize], i: usize, deleted: bool, ps: &mut [Vec<u128>]) {
        let target = classes[i + 1];
        for j in 0..ps.len() {
            let (below, here) = ps.split_at_mut(j);
            let here = &mut here[0];
            let found = (i + 1 >= j).then(|| self.orders[j].get(&Self::key(classes, i, j))).flatten();
            let Some((list, total)) = found else {
                match below.last() {
                    Some(prior) => here.copy_from_slice(prior),
                    None => here.fill(0),
                }
                continue;
            };
            let own = if deleted { list.iter().find(|(b, _)| *b as usize == target).map_or(0, |&(_, c)| c) } else { 0 };
            let arrivals = (*total - deleted as u32) as u128;
            let distinct = (list.len() - (deleted && own == 1) as usize) as u128;
            if arrivals == 0 {
                match below.last() {
                    Some(prior) => here.copy_from_slice(prior),
                    None => here.fill(0),
                }
                continue;
            }
            let denom = if j == 0 { arrivals } else { arrivals + distinct };
            for &b in &self.seen {
                let interpolated = if j == 0 { 0 } else { distinct * below[j - 1][b] };
                here[b] = (interpolated + denom / 2) / denom;
            }
            for &(b, c) in list {
                let c = c - (deleted && b as usize == target) as u32;
                let interpolated = if j == 0 { 0 } else { distinct * below[j - 1][b as usize] };
                here[b as usize] = (((c as u128) << 48) + interpolated + denom / 2) / denom;
            }
        }
    }

    /// The Brier score of a prediction on `2^(−48)` read at `target`, on `2^(−48)`:
    /// `Σ q_b² − 2 q_target + 1` with `q` on `2^(−24)`.
    fn brier(&self, p: &[u128], target: usize) -> i128 {
        let q = |b: usize| ((p[b] + (1 << 23)) >> 24) as i128;
        let squares: i128 = self.seen.iter().map(|&b| q(b) * q(b)).sum();
        squares - 2 * (q(target) << 24) + (1i128 << 48)
    }
}

/// The floor reading's joint face of one cell: `top`, the unit, the last `order` encodings, the
/// count model's prediction, the foil and the covector, in that order.
struct FloorLayout {
    w: usize,
    a: usize,
    order: usize,
}

impl FloorLayout {
    fn dim(&self) -> usize {
        self.w + 1 + self.order * self.w + self.a + self.w + self.a
    }
    fn face(&self) -> std::ops::Range<usize> {
        0..self.w + 1
    }
    fn encoding(&self, j: usize) -> std::ops::Range<usize> {
        let s = self.w + 1 + j * self.w;
        s..s + self.w
    }
    fn count(&self) -> std::ops::Range<usize> {
        let s = self.w + 1 + self.order * self.w;
        s..s + self.a
    }
    fn foil(&self) -> std::ops::Range<usize> {
        let s = self.count().end;
        s..s + self.w
    }
    fn covector(&self) -> std::ops::Range<usize> {
        self.foil().end..self.dim()
    }
    #[allow(clippy::too_many_arguments)]
    fn fill(&self, v: &mut [i64], tower: &Tower, cell: &holonics::hnn::tower::TensionCell, classes: &[usize], i: usize, p: &[u128], foil: usize) {
        let w = self.w;
        for (slot, &x) in v[..w].iter_mut().zip(&cell.top) {
            *slot = x as i64;
        }
        v[w] = 1;
        for j in 0..self.order {
            let range = self.encoding(j);
            if i >= j {
                for (slot, &x) in v[range].iter_mut().zip(tower.encoding(classes[i - j])) {
                    *slot = x as i64;
                }
            } else {
                v[range].fill(0);
            }
        }
        for (slot, &x) in v[self.count()].iter_mut().zip(p) {
            *slot = ((x + (1 << 23)) >> 24) as i64;
        }
        for (slot, &x) in v[self.foil()].iter_mut().zip(tower.encoding(foil)) {
            *slot = x as i64;
        }
        v[self.covector()].copy_from_slice(&cell.covector);
    }
}

/// The floor reading's eliminations on the joint Gram: the face, then the chains. The covector and
/// the count model are read on the classes that arrive in the training text (`arriving`): the count
/// model gives no other class mass, and another class's coordinate of the covector is its face's
/// mass alone, whose tension is at most its `T_cc`, printed beside the reading.
fn floor_chains(layout: &FloorLayout, gram: &[i128], cells: usize, arriving: &[usize], started: std::time::Instant) -> Result<()> {
    use num_bigint::BigInt;
    use num_traits::One;
    let dim = layout.dim();
    let z = layout.covector();
    let zs: Vec<usize> = arriving.iter().map(|&c| z.start + c).collect();
    let in_z = |i: usize| z.contains(&i);
    let thin = |i: usize, j: usize| i != j && in_z(i) && in_z(j);
    let unit = BigInt::from(cells) << 48;
    let mut base = Upper::from_gram(gram, dim);
    let diagonal = |m: &Upper| -> Vec<BigInt> { zs.iter().map(|&c| m.get(c, c).clone()).collect() };
    let t_diag = diagonal(&base);
    let tr_t: BigInt = t_diag.iter().sum();
    let tr_t_all: BigInt = z.clone().map(|c| base.get(c, c).clone()).sum();
    println!(
        "FLOOR_CLASSES arriving={} brier_T_all={} brier_T_arriving={} brier_T_never_arriving={}",
        arriving.len(),
        thousandths_of(&tr_t_all, &unit),
        thousandths_of(&tr_t, &unit),
        thousandths_of(&(&tr_t_all - &tr_t), &unit)
    );
    let face: Vec<usize> = layout.face().collect();
    let encodings: Vec<Vec<usize>> = (0..layout.order).map(|j| layout.encoding(j).collect()).collect();
    let count: Vec<usize> = arriving.iter().map(|&c| layout.count().start + c).collect();
    let foil: Vec<usize> = layout.foil().collect();
    let rest: Vec<usize> = encodings.iter().flatten().chain(&count).chain(&foil).chain(&zs).copied().collect();
    let (d, rank) = base.eliminate(&face, &rest, BigInt::one(), &thin)?;
    let s_diag = diagonal(&base);
    let tr_ds: BigInt = s_diag.iter().sum();
    println!(
        "FLOOR part=all cells={cells} face_rank={rank} brier_T={} tension_S={} tension_permille={} elapsed_ms={}",
        thousandths_of(&tr_t, &unit),
        thousandths_of(&tr_ds, &(&unit * &d)),
        thousandths_of(&(&tr_ds * 1000), &(&tr_t * &d)),
        started.elapsed().as_millis()
    );
    let order = layout.order;
    // Each chain: its blocks in order, each eliminated after the ones before, with the labels.
    let mut linear: Vec<(String, Vec<usize>)> = encodings.iter().enumerate().map(|(j, e)| (if j == 0 { "E(u_t)".to_string() } else { format!("+E(u_(t-{j}))") }, e.clone())).collect();
    linear.push((format!("+count{order}"), count.clone()));
    let chains: Vec<(&str, Vec<(String, Vec<usize>)>)> = vec![("linear", linear), ("count", vec![(format!("count{order}"), count.clone())]), ("foil", vec![("E(foil)".to_string(), foil.clone())])];
    // The chains run together, each on its own copy of the face's elimination; each step prints as
    // it closes. Per class: the diagonal after each step of each chain.
    let chained: Vec<Vec<(String, BigInt, Vec<BigInt>)>> = chains
        .into_par_iter()
        .map(|(name, blocks)| {
            let mut m = Upper { rows: base.rows.clone() };
            let mut steps = Vec::new();
            let mut last = d.clone();
            let mut prior = tr_ds.clone();
            let mut prior_d = d.clone();
            for (b, (label, pivots)) in blocks.iter().enumerate() {
                let later: Vec<usize> = blocks[b + 1..].iter().flat_map(|(_, p)| p.iter().copied()).chain(zs.iter().copied()).collect();
                let (d2, rank2) = m.eliminate(pivots, &later, last.clone(), &thin).map_err(|e| e.to_string())?;
                let after = diagonal(&m);
                let tr_after: BigInt = after.iter().sum();
                // drop = prior/prior_d − tr_after/d2; from the face: tr_ds/d − tr_after/d2.
                let drop = &prior * &d2 - &tr_after * &prior_d;
                let total = &tr_ds * &d2 - &tr_after * &d;
                println!(
                    "FLOOR_DROP chain={name} step={label} novel_rank={rank2} drop={} drop_of_tension_permille={} chain_drop_of_tension_permille={} elapsed_ms={}",
                    thousandths_of(&drop, &(&unit * &prior_d * &d2)),
                    thousandths_of(&(&drop * 1000 * &d), &(&tr_ds * &prior_d * &d2)),
                    thousandths_of(&(&total * 1000), &(&tr_ds * &d2)),
                    started.elapsed().as_millis()
                );
                steps.push((format!("{name}:{label}"), d2.clone(), after));
                prior = tr_after;
                prior_d = d2.clone();
                last = d2;
            }
            Ok(steps)
        })
        .collect::<std::result::Result<_, String>>()?;
    let steps: Vec<(String, BigInt, Vec<BigInt>)> = chained.into_iter().flatten().collect();
    // The classes with the most tension: each step's remaining share of the class's own tension.
    let mut own: Vec<(BigInt, usize)> = s_diag.iter().cloned().zip(0..).collect();
    own.sort_by(|x, y| y.0.cmp(&x.0));
    for (s, c) in own.iter().take(24) {
        let shares: Vec<String> = steps
            .iter()
            .map(|(label, d2, after)| format!("{label}={}", thousandths_of(&(&after[*c] * 1000 * &d), &(s * d2))))
            .collect();
        println!("FLOOR_CLASS class={} S_aa={} remaining_permille {}", class_name(arriving[*c]), thousandths_of(s, &(&unit * &d)), shares.join(" "));
    }
    Ok(())
}

/// The moments a part of a text keeps for founding faces on pairs of bytes: the face's
/// `H = Σ f̄f̄ᵀ` (`f̄ = (top, 1)`), `B = Σ t f̄ᵀ` and the covector's diagonal `Σ t²`, on the
/// classes that arrive in the training text; and for each pair `p = (u_(t−1), u_t)` that occurs,
/// its cells `n_p`, `τ_p = Σ t` and `φ_p = Σ f̄`. A stream's first cell is paired with the
/// alphabet's end, which has no encoding. Below `2^32` cells every pair sum fits in 64 bits.
struct PairMoments {
    m: usize,
    h: Vec<i128>,
    b: Vec<i128>,
    t: Vec<i128>,
    cells: usize,
    pairs: std::collections::HashMap<(usize, usize), PairCell>,
}

struct PairCell {
    n: i64,
    tau: Vec<i64>,
    phi: Vec<i64>,
}

impl PairMoments {
    fn new(m: usize, classes: usize) -> Self {
        Self { m, h: vec![0; m * m], b: vec![0; classes * m], t: vec![0; classes], cells: 0, pairs: std::collections::HashMap::new() }
    }
    fn add(&mut self, f: &[i64], t: &[i64], pair: (usize, usize)) {
        let m = self.m;
        for i in 0..m {
            let fi = f[i] as i128;
            if fi != 0 {
                for (slot, &fj) in self.h[i * m + i..(i + 1) * m].iter_mut().zip(&f[i..]) {
                    *slot += fi * fj as i128;
                }
            }
        }
        for (k, &tk) in t.iter().enumerate() {
            if tk == 0 {
                continue;
            }
            let tk = tk as i128;
            self.t[k] += tk * tk;
            for (slot, &fj) in self.b[k * m..(k + 1) * m].iter_mut().zip(f) {
                *slot += tk * fj as i128;
            }
        }
        self.cells += 1;
        let cell = self.pairs.entry(pair).or_insert_with(|| PairCell { n: 0, tau: vec![0; t.len()], phi: vec![0; m] });
        cell.n += 1;
        for (slot, &x) in cell.tau.iter_mut().zip(t) {
            *slot += x;
        }
        for (slot, &x) in cell.phi.iter_mut().zip(f) {
            *slot += x;
        }
    }
    fn merge(&mut self, other: Self) {
        for (x, y) in self.h.iter_mut().chain(&mut self.b).chain(&mut self.t).zip(other.h.iter().chain(&other.b).chain(&other.t)) {
            *x += y;
        }
        self.cells += other.cells;
        for (key, cell) in other.pairs {
            match self.pairs.entry(key) {
                std::collections::hash_map::Entry::Occupied(mut e) => {
                    let into = e.get_mut();
                    into.n += cell.n;
                    for (x, y) in into.tau.iter_mut().zip(&cell.tau).chain(into.phi.iter_mut().zip(&cell.phi)) {
                        *x += y;
                    }
                }
                std::collections::hash_map::Entry::Vacant(e) => {
                    e.insert(cell);
                }
            }
        }
    }
    /// The pairs in their order (the byte before, then the current byte).
    fn table(&self) -> (Vec<(usize, usize)>, Vec<&PairCell>) {
        let mut pairs: Vec<(&(usize, usize), &PairCell)> = self.pairs.iter().collect();
        pairs.sort_by_key(|(key, _)| **key);
        pairs.into_iter().map(|(key, cell)| (*key, cell)).unzip()
    }
}

/// A founded coordinate of a pair, `c_p = r(u_t)·s(u_(t−1))`: each factor is a read of its byte's
/// encoding with the unit, released to `2^16` its largest value over the alphabet (and, for the
/// byte before, the stream's start).
#[derive(Clone)]
struct PairFace {
    r: Vec<i64>,
    s: Vec<i64>,
}

impl PairFace {
    fn value(&self, (prev, cur): (usize, usize)) -> i64 {
        self.r[cur] * self.s[prev]
    }
    fn table(&self) -> PairTable {
        let alphabet = self.r.len();
        PairTable { alphabet, values: self.s.iter().flat_map(|&s| self.r.iter().map(move |&r| r * s)).collect() }
    }
}

/// A founded coordinate of a pair as its value at every pair of the alphabet, the byte before
/// (with the stream's start, `alphabet`) by the current byte: the resident face of the form that
/// founded it, so a pair the training text never met is read by the same form.
#[derive(Clone)]
struct PairTable {
    alphabet: usize,
    values: Vec<i64>,
}

impl PairTable {
    fn value(&self, (prev, cur): (usize, usize)) -> i64 {
        self.values[prev * self.alphabet + cur]
    }
}

fn mac(acc: i128, x: i128, y: i128) -> std::result::Result<i128, String> {
    x.checked_mul(y).and_then(|p| acc.checked_add(p)).ok_or_else(|| "a pair moment outgrew its 128-bit carrier".to_string())
}

/// `xs` released to below `2^bits` its largest magnitude: shifted right, rounded to nearest.
pub(super) fn release_wide(xs: &[i128], bits: u32) -> Vec<i64> {
    let top = xs.iter().map(|x| x.unsigned_abs()).max().unwrap_or(0);
    let shift = (128 - top.leading_zeros()).saturating_sub(bits);
    xs.iter().map(|&x| if shift == 0 { x as i64 } else { ((x + (1i128 << (shift - 1))) >> shift) as i64 }).collect()
}

pub(super) fn release_big(xs: &[num_bigint::BigInt], bits: u64) -> Vec<i64> {
    use num_traits::ToPrimitive;
    let top = xs.iter().map(|x| x.bits()).max().unwrap_or(0);
    let shift = top.saturating_sub(bits);
    xs.iter()
        .map(|x| if shift == 0 { x.clone() } else { (x + (num_bigint::BigInt::from(1) << (shift - 1))) >> shift })
        .map(|x| x.to_i64().unwrap_or(0))
        .collect()
}

/// The exact solve of a positive semidefinite system `h·y = r` by fraction-free elimination with
/// diagonal pivots, scaled by the last pivot `D`. A zero pivot of a semidefinite matrix has a zero
/// row: its coordinate lies in the span of the ones before and is given no weight (with `strict`,
/// a zero pivot with a nonzero row is refused; otherwise its coordinate is passed over too, which
/// solves the system without it exactly). Returns `D` and `D·y`, each back-substitution division
/// checked exact.
pub(super) fn solve_scaled(h: &[Vec<num_bigint::BigInt>], r: &[Vec<num_bigint::BigInt>], strict: bool) -> Result<(num_bigint::BigInt, Vec<Vec<num_bigint::BigInt>>)> {
    use num_bigint::BigInt;
    use num_traits::{One, Zero};
    let m = h.len();
    let k = r.first().map_or(0, |x| x.len());
    let mut rows: Vec<Vec<BigInt>> = h.iter().zip(r).map(|(x, y)| x.iter().chain(y).cloned().collect()).collect();
    let mut last = BigInt::one();
    let mut independent = Vec::new();
    for p in 0..m {
        let pivot = rows[p][p].clone();
        if pivot.is_zero() {
            if strict && rows[p][p + 1..m].iter().any(|x| !x.is_zero()) {
                return Err("a zero pivot with a nonzero row: the moments are not positive semidefinite".into());
            }
            continue;
        }
        independent.push(p);
        let (head, tail) = rows.split_at_mut(p + 1);
        let (prow, last_ref) = (&head[p], &last);
        tail.par_iter_mut().for_each(|row| {
            let f = row[p].clone();
            for j in p + 1..m + k {
                row[j] = (&pivot * &row[j] - &f * &prow[j]) / last_ref;
            }
        });
        last = pivot;
    }
    let columns: Vec<Vec<BigInt>> = (0..k)
        .into_par_iter()
        .map(|c| {
            let mut x = vec![BigInt::zero(); m];
            for (n, &p) in independent.iter().enumerate().rev() {
                let mut num = &last * &rows[p][m + c];
                for &j in &independent[n + 1..] {
                    num -= &rows[p][j] * &x[j];
                }
                let q = &num / &rows[p][p];
                if &q * &rows[p][p] != num {
                    return Err("an exact solve left a remainder".to_string());
                }
                x[p] = q;
            }
            Ok(x)
        })
        .collect::<std::result::Result<_, String>>()?;
    Ok((last, (0..m).map(|i| columns.iter().map(|col| col[i].clone()).collect()).collect()))
}

/// The readout of a face fitted on the training moments: `D`, `adj = D·H⁻¹`, `X = D·H⁻¹Bᵀ` and
/// each arriving class's `D·S_kk`, `S = T − BH⁻¹Bᵀ`.
struct Readout {
    d: num_bigint::BigInt,
    adj: Vec<Vec<num_bigint::BigInt>>,
    x: Vec<Vec<num_bigint::BigInt>>,
    s: Vec<num_bigint::BigInt>,
}

/// A part's face extended by the founded coordinates: each pair's `φ̂_p = (φ_p, n_p c_p, …)` in
/// the table's order, `H` and `B` with the founded rows.
type Extended = (Vec<Vec<i128>>, Vec<Vec<num_bigint::BigInt>>, Vec<Vec<num_bigint::BigInt>>);

fn extended(moments: &PairMoments, keys: &[(usize, usize)], cells: &[&PairCell], founded: &[PairTable]) -> Result<Extended> {
    use num_bigint::BigInt;
    let (m0, r, a_n) = (moments.m, founded.len(), moments.t.len());
    let m = m0 + r;
    let values: Vec<Vec<i64>> = keys.iter().map(|&key| founded.iter().map(|f| f.value(key)).collect()).collect();
    let phihat: Vec<Vec<i128>> = cells
        .iter()
        .zip(&values)
        .map(|(cell, c)| cell.phi.iter().map(|&x| x as i128).chain(c.iter().map(|&v| cell.n as i128 * v as i128)).collect())
        .collect();
    // The founded columns: Σ_p φ̂_p c_p and Σ_p τ_p c_p.
    let mut l = vec![vec![0i128; r]; m];
    let mut k = vec![vec![0i128; r]; a_n];
    for ((cell, ph), c) in cells.iter().zip(&phihat).zip(&values) {
        for (j, &v) in c.iter().enumerate() {
            if v == 0 {
                continue;
            }
            for (row, &x) in l.iter_mut().zip(ph) {
                row[j] = mac(row[j], x, v as i128)?;
            }
            for (row, &x) in k.iter_mut().zip(&cell.tau) {
                row[j] = mac(row[j], x as i128, v as i128)?;
            }
        }
    }
    let h: Vec<Vec<BigInt>> = (0..m)
        .map(|i| {
            (0..m)
                .map(|j| {
                    let (i, j) = (i.min(j), i.max(j));
                    BigInt::from(if j < m0 { moments.h[i * m0 + j] } else { l[i][j - m0] })
                })
                .collect()
        })
        .collect();
    let b: Vec<Vec<BigInt>> = (0..a_n).map(|c| (0..m).map(|j| BigInt::from(if j < m0 { moments.b[c * m0 + j] } else { k[c][j - m0] })).collect()).collect();
    Ok((phihat, h, b))
}

fn fit_readout(h: &[Vec<num_bigint::BigInt>], b: &[Vec<num_bigint::BigInt>], t: &[i128]) -> Result<Readout> {
    use num_bigint::BigInt;
    let m = h.len();
    let rhs: Vec<Vec<BigInt>> = (0..m).map(|i| (0..m).map(|j| BigInt::from((i == j) as i64)).chain(b.iter().map(|row| row[i].clone())).collect()).collect();
    let (d, y) = solve_scaled(h, &rhs, true)?;
    let adj: Vec<Vec<BigInt>> = y.iter().map(|row| row[..m].to_vec()).collect();
    let x: Vec<Vec<BigInt>> = y.iter().map(|row| row[m..].to_vec()).collect();
    let s = (0..b.len()).into_par_iter().map(|c| &d * t[c] - (0..m).map(|j| &b[c][j] * &x[j][c]).sum::<BigInt>()).collect();
    Ok(Readout { d, adj, x, s })
}

/// `D²` times the residual the readout leaves on a part's moments, `Σ_k |t_k − W_k f̂|²` with
/// `W = Xᵀ/D`.
fn readout_residual(readout: &Readout, h: &[Vec<num_bigint::BigInt>], b: &[Vec<num_bigint::BigInt>], t: &[i128]) -> num_bigint::BigInt {
    use num_bigint::BigInt;
    let (d, x, m) = (&readout.d, &readout.x, h.len());
    (0..t.len())
        .into_par_iter()
        .map(|k| {
            let cross: BigInt = (0..m).map(|j| &x[j][k] * &b[k][j]).sum();
            let quadratic: BigInt = (0..m).map(|i| &x[i][k] * (0..m).map(|j| &h[i][j] * &x[j][k]).sum::<BigInt>()).sum();
            d * d * t[k] - d * &cross * 2 + quadratic
        })
        .sum()
}

/// The moments of the pool `z_p = x̂_u·g_p`, grouped by the byte `u` the side reads (the current
/// byte or the byte before) with the other factor's value `g_p`: `K = Σ τ_p z_pᵀ`, `L = Σ φ̂_p z_pᵀ`
/// and `C = Σ n_p z_p z_pᵀ`.
type Pool = (Vec<Vec<i128>>, Vec<Vec<i128>>, Vec<Vec<i128>>);

fn pool_moments(keys: &[(usize, usize)], cells: &[&PairCell], phihat: &[Vec<i128>], hats: &[Vec<i64>], by_current: bool, other: &[i64]) -> std::result::Result<Pool, String> {
    let (a_n, m, q, bytes) = (cells[0].tau.len(), phihat[0].len(), hats[0].len(), hats.len());
    let mut tau = vec![vec![0i128; a_n]; bytes];
    let mut phi = vec![vec![0i128; m]; bytes];
    let mut n = vec![0i128; bytes];
    for ((&(prev, cur), cell), ph) in keys.iter().zip(cells).zip(phihat) {
        let (u, g) = if by_current { (cur, other[prev]) } else { (prev, other[cur]) };
        if g == 0 {
            continue;
        }
        let g = g as i128;
        for (slot, &x) in tau[u].iter_mut().zip(&cell.tau) {
            *slot = mac(*slot, x as i128, g)?;
        }
        for (slot, &x) in phi[u].iter_mut().zip(ph) {
            *slot = mac(*slot, x, g)?;
        }
        n[u] = mac(n[u], cell.n as i128 * g, g)?;
    }
    let outer = |grouped: &[Vec<i128>], rows: usize| -> std::result::Result<Vec<Vec<i128>>, String> {
        (0..rows)
            .into_par_iter()
            .map(|i| (0..q).map(|j| (0..bytes).try_fold(0i128, |acc, u| mac(acc, grouped[u][i], hats[u][j] as i128))).collect::<std::result::Result<Vec<i128>, String>>())
            .collect()
    };
    let k = outer(&tau, a_n)?;
    let l = outer(&phi, m)?;
    let c = (0..q)
        .into_par_iter()
        .map(|i| (0..q).map(|j| (0..bytes).try_fold(0i128, |acc, u| mac(acc, mac(0, n[u], hats[u][i] as i128)?, hats[u][j] as i128))).collect::<std::result::Result<Vec<i128>, String>>())
        .collect::<std::result::Result<Vec<Vec<i128>>, String>>()?;
    Ok((k, l, c))
}

/// `D·M = D·K − XᵀL` and `D·Q = D·C − Lᵀ adj L` of a block of coordinates read after the face.
fn reduced(readout: &Readout, k: &[Vec<i128>], l: &[Vec<i128>], c: &[Vec<i128>]) -> (Vec<Vec<num_bigint::BigInt>>, Vec<Vec<num_bigint::BigInt>>) {
    use num_bigint::BigInt;
    let (d, x, adj) = (&readout.d, &readout.x, &readout.adj);
    let (m, q) = (l.len(), c.len());
    let lb: Vec<Vec<BigInt>> = l.iter().map(|row| row.iter().map(|&v| BigInt::from(v)).collect()).collect();
    let dm = (0..k.len()).into_par_iter().map(|a| (0..q).map(|j| d * k[a][j] - (0..m).map(|i| &x[i][a] * &lb[i][j]).sum::<BigInt>()).collect()).collect();
    let adj_l: Vec<Vec<BigInt>> = (0..m).into_par_iter().map(|i| (0..q).map(|j| (0..m).map(|i2| &adj[i][i2] * &lb[i2][j]).sum()).collect()).collect();
    let dq = (0..q).into_par_iter().map(|i| (0..q).map(|j| d * c[i][j] - (0..m).map(|i2| &lb[i2][i] * &adj_l[i2][j]).sum::<BigInt>()).collect()).collect();
    (dm, dq)
}

/// The leading generalized eigenvector of `(MᵀM, Q)` by the power step `w = Q⁻¹Mᵀv`, `v ← Mw`, on
/// `M` and `Q` released to below `2^60` their largest entry (only directions are read), each vector
/// released to `2^15`; it stops when a step raises the Rayleigh quotient `|Mw|²/(wᵀQw)` by less
/// than `2^(−15)` of itself. Returns the factor, the carried `v` and the steps taken.
pub(super) fn leading_factor(dm: &[Vec<num_bigint::BigInt>], dq: &[Vec<num_bigint::BigInt>], mut v: Vec<i64>) -> Result<(Vec<i64>, Vec<i64>, usize)> {
    use num_bigint::BigInt;
    let (rows, q) = (dm.len(), dq.len());
    let mt = release_big(&dm.iter().flatten().cloned().collect::<Vec<_>>(), 60);
    let qt = release_big(&dq.iter().flatten().cloned().collect::<Vec<_>>(), 60);
    let qbig: Vec<Vec<BigInt>> = (0..q).map(|i| (0..q).map(|j| BigInt::from(qt[i * q + j])).collect()).collect();
    let identity: Vec<Vec<BigInt>> = (0..q).map(|i| (0..q).map(|j| BigInt::from((i == j) as i64)).collect()).collect();
    let (_, inverse) = solve_scaled(&qbig, &identity, false)?;
    let mut best: Option<(BigInt, BigInt, Vec<i64>, Vec<i64>)> = None;
    let mut steps = 0;
    loop {
        steps += 1;
        let g: Vec<i128> = (0..q).map(|j| (0..rows).map(|a| mt[a * q + j] as i128 * v[a] as i128).sum()).collect();
        let wide: Vec<BigInt> = (0..q).map(|i| inverse[i].iter().zip(&g).map(|(x, &y)| x * y).sum()).collect();
        let w = release_big(&wide, 15);
        let u: Vec<i128> = (0..rows).map(|a| (0..q).map(|j| mt[a * q + j] as i128 * w[j] as i128).sum()).collect();
        let num: BigInt = u.iter().map(|&x| BigInt::from(x) * x).sum();
        let den: BigInt = (0..q).map(|i| (0..q).map(|j| BigInt::from(qt[i * q + j] as i128 * w[i] as i128) * w[j]).sum::<BigInt>()).sum();
        v = release_wide(&u, 15);
        if den <= BigInt::from(0) || w.iter().all(|&x| x == 0) {
            break;
        }
        let gained = match &best {
            None => true,
            Some((bn, bd, _, _)) => (&num * bd) << 15u32 > bn * &den * ((1i64 << 15) + 1),
        };
        let better = best.as_ref().is_none_or(|(bn, bd, _, _)| &num * bd > bn * &den);
        if better {
            best = Some((num, den, w, v.clone()));
        }
        if !gained {
            break;
        }
    }
    let (_, _, w, v) = best.ok_or("the power step found no direction")?;
    Ok((w, v, steps))
}

/// The exact moments of one pair coordinate `c_p` read after the face: `D·M` per class and `D·Q`.
fn coordinate_drop(readout: &Readout, keys: &[(usize, usize)], cells: &[&PairCell], phihat: &[Vec<i128>], face: &PairFace) -> Result<(Vec<num_bigint::BigInt>, num_bigint::BigInt)> {
    let (a_n, m) = (readout.s.len(), phihat[0].len());
    let (mut k, mut l, mut c) = (vec![vec![0i128; 1]; a_n], vec![vec![0i128; 1]; m], vec![vec![0i128; 1]; 1]);
    for ((&key, cell), ph) in keys.iter().zip(cells).zip(phihat) {
        let v = face.value(key) as i128;
        if v == 0 {
            continue;
        }
        for (row, &x) in k.iter_mut().zip(&cell.tau) {
            row[0] = mac(row[0], x as i128, v)?;
        }
        for (row, &x) in l.iter_mut().zip(ph) {
            row[0] = mac(row[0], x, v)?;
        }
        c[0][0] = mac(c[0][0], cell.n as i128 * v, v)?;
    }
    let (dm, dq) = reduced(readout, &k, &l, &c);
    Ok((dm.into_iter().map(|mut row| row.remove(0)).collect(), dq[0][0].clone()))
}

/// The pair moments of a text's streams, one part per region of `roles` (the region of the byte
/// that arrives), or one part.
fn read_pair_moments(tower: &Tower, streams: &[Vec<usize>], arriving: &[usize], roles: Option<&[u8]>) -> Result<Vec<PairMoments>> {
    let (w, alphabet) = (tower.declaration.width, tower.declaration.alphabet);
    let parts = if roles.is_some() { REGIONS.len() } else { 1 };
    let chunk = streams.first().map_or(0, |s| s.len());
    let read: Vec<Vec<PairMoments>> = streams
        .par_iter()
        .enumerate()
        .map(|(s, classes)| {
            let mut moments: Vec<PairMoments> = (0..parts).map(|_| PairMoments::new(w + 1, arriving.len())).collect();
            let mut state = tower.rest();
            let (mut f, mut t) = (vec![0i64; w + 1], vec![0i64; arriving.len()]);
            let mut i = 0usize;
            tower
                .read_tension(&mut state, classes, |cell| {
                    for (slot, &x) in f.iter_mut().zip(&cell.top) {
                        *slot = x as i64;
                    }
                    f[w] = 1;
                    for (slot, &c) in t.iter_mut().zip(arriving) {
                        *slot = cell.covector[c];
                    }
                    let prev = if i == 0 { alphabet } else { classes[i - 1] };
                    moments[roles.map_or(0, |r| r[s * chunk + i + 1] as usize)].add(&f, &t, (prev, classes[i]));
                    i += 1;
                    Ok(())
                })
                .map_err(|e| e.to_string())?;
            Ok(moments)
        })
        .collect::<std::result::Result<_, String>>()?;
    let mut merged: Vec<PairMoments> = (0..parts).map(|_| PairMoments::new(w + 1, arriving.len())).collect();
    for stream in read {
        for (into, part) in merged.iter_mut().zip(stream) {
            into.merge(part);
        }
    }
    Ok(merged)
}

/// The ceiling: the tension left within the pairs, `S_w = T_w − B_w H_w⁻¹ B_wᵀ` with each moment
/// less its pairs' means (`X_w = X − Σ_p x_p y_pᵀ/n_p`, each term rounded to nearest, so each
/// entry is within half the number of pairs of its exact value; the unit's terms are exact and its
/// row is zero).
struct Ceiling {
    /// `D_w` and each class's `D_w·S_w,kk`.
    d: num_bigint::BigInt,
    s: Vec<num_bigint::BigInt>,
    /// The covector's between-pair moments `G = Σ_p τ_pτ_pᵀ/n_p = T − T_w`, and `B_w·D_wH_w⁻¹B_wᵀ`.
    between: Vec<Vec<i128>>,
    bridged: Vec<Vec<num_bigint::BigInt>>,
}

fn ceiling(moments: &PairMoments, cells: &[&PairCell]) -> Result<Ceiling> {
    use num_bigint::BigInt;
    let (m, a_n) = (moments.m, moments.t.len());
    let mean = |x: i128, y: i128, n: i128| -> std::result::Result<i128, String> {
        let p = x.checked_mul(y).and_then(|p| p.checked_mul(2)).and_then(|p| p.checked_add(n)).ok_or("a pair mean outgrew its 128-bit carrier")?;
        Ok(p.div_euclid(2 * n))
    };
    type Means = (Vec<i128>, Vec<i128>, Vec<i128>);
    let zero = || -> Means { (vec![0i128; m * m], vec![0i128; a_n * m], vec![0i128; a_n * a_n]) };
    let (hl, bl, g) = cells
        .par_iter()
        .try_fold(zero, |(mut h, mut b, mut g): Means, cell: &&PairCell| -> std::result::Result<Means, String> {
            let n = cell.n as i128;
            for i in 0..m {
                for j in i..m {
                    h[i * m + j] += mean(cell.phi[i] as i128, cell.phi[j] as i128, n)?;
                }
            }
            for k in 0..a_n {
                let tk = cell.tau[k] as i128;
                for j in 0..m {
                    b[k * m + j] += mean(tk, cell.phi[j] as i128, n)?;
                }
                for l in k..a_n {
                    g[k * a_n + l] += mean(tk, cell.tau[l] as i128, n)?;
                }
            }
            Ok((h, b, g))
        })
        .try_reduce(zero, |(mut h, mut b, mut g), (h2, b2, g2)| {
            for (x, y) in h.iter_mut().chain(&mut b).chain(&mut g).zip(h2.iter().chain(&b2).chain(&g2)) {
                *x += y;
            }
            Ok((h, b, g))
        })?;
    let h: Vec<Vec<BigInt>> = (0..m)
        .map(|i| {
            (0..m)
                .map(|j| {
                    let (i, j) = (i.min(j), i.max(j));
                    BigInt::from(moments.h[i * m + j] - hl[i * m + j])
                })
                .collect()
        })
        .collect();
    let b: Vec<Vec<BigInt>> = (0..a_n).map(|k| (0..m).map(|j| BigInt::from(moments.b[k * m + j] - bl[k * m + j])).collect()).collect();
    let between: Vec<Vec<i128>> = (0..a_n).map(|k| (0..a_n).map(|l| g[k.min(l) * a_n + k.max(l)]).collect()).collect();
    let rhs: Vec<Vec<BigInt>> = (0..m).map(|i| b.iter().map(|row| row[i].clone()).collect()).collect();
    let (d, x) = solve_scaled(&h, &rhs, true)?;
    let bridged: Vec<Vec<BigInt>> = (0..a_n).into_par_iter().map(|k| (0..a_n).map(|l| (0..m).map(|j| &b[k][j] * &x[j][l]).sum()).collect()).collect();
    let s = (0..a_n).map(|k| &d * (moments.t[k] - between[k][k]) - &bridged[k][k]).collect();
    Ok(Ceiling { d, s, between, bridged })
}

/// The leading directions of a symmetric positive semidefinite matrix `y`, by power steps on a
/// copy released to below `2^60` its largest entry (only directions are read), each found direction
/// projected out of the later ones; a direction stops when a step raises its Rayleigh quotient by
/// less than `2^(−15)` of itself. Each direction is released to `2^15`.
fn leading_directions(y: &[Vec<num_bigint::BigInt>], count: usize) -> Vec<Vec<i64>> {
    use num_bigint::BigInt;
    let a = y.len();
    let yt = release_big(&y.iter().flatten().cloned().collect::<Vec<_>>(), 60);
    let mut found: Vec<Vec<i64>> = Vec::new();
    let project = |u: Vec<BigInt>, found: &[Vec<i64>]| -> Vec<BigInt> {
        found.iter().fold(u, |u, f| {
            let ff: i128 = f.iter().map(|&x| x as i128 * x as i128).sum();
            let uf: BigInt = u.iter().zip(f).map(|(x, &y)| x * y).sum();
            u.iter().zip(f).map(|(x, &y)| x * ff - &uf * y).collect()
        })
    };
    let rayleigh = |v: &[i64]| -> (BigInt, BigInt) {
        let num: BigInt = (0..a).map(|i| BigInt::from(v[i]) * (0..a).map(|j| yt[i * a + j] as i128 * v[j] as i128).sum::<i128>()).sum();
        (num, v.iter().map(|&x| BigInt::from(x as i128 * x as i128)).sum())
    };
    while found.len() < count.min(a) {
        let start = (0..a).max_by_key(|&i| yt[i * a + i]).unwrap_or(0);
        let mut v = release_big(&project((0..a).map(|i| BigInt::from((i == start) as i64)).collect(), &found), 15);
        if v.iter().all(|&x| x == 0) {
            v = release_big(&project((0..a).map(|i| BigInt::from((i + found.len()) % 2 + 1)).collect(), &found), 15);
        }
        let mut last = rayleigh(&v);
        loop {
            let u: Vec<BigInt> = (0..a).map(|i| BigInt::from((0..a).map(|j| yt[i * a + j] as i128 * v[j] as i128).sum::<i128>())).collect();
            let next = release_big(&project(u, &found), 15);
            if next.iter().all(|&x| x == 0) {
                break;
            }
            let r = rayleigh(&next);
            let gained = (&r.0 * &last.1) << 15u32 > &last.0 * &r.1 * ((1i64 << 15) + 1);
            v = next;
            last = r;
            if !gained {
                break;
            }
        }
        found.push(v);
    }
    found
}

/// Over the span of the leading `k` directions of a symmetric positive semidefinite `e`, the exact
/// sum `tr((VᵀV)⁻¹VᵀeV)` (a lower bound on the sum of its leading `k` eigenvalues), for each `k` a
/// power of two up to the directions found, as `(k, numerator, denominator)`; with each direction's
/// own Rayleigh quotient `(vᵀev, vᵀv)`.
type LeadingSums = (Vec<(usize, num_bigint::BigInt, num_bigint::BigInt)>, Vec<(num_bigint::BigInt, num_bigint::BigInt)>);

fn leading_sums(e: &[Vec<num_bigint::BigInt>], directions: &[Vec<i64>]) -> Result<LeadingSums> {
    use num_bigint::BigInt;
    let a_n = e.len();
    let ev: Vec<Vec<BigInt>> = (0..a_n).into_par_iter().map(|k| directions.iter().map(|v| (0..a_n).map(|l| &e[k][l] * v[l]).sum()).collect()).collect();
    let gram: Vec<Vec<BigInt>> = directions.iter().map(|u| directions.iter().map(|v| BigInt::from(u.iter().zip(v).map(|(&x, &y)| x as i128 * y as i128).sum::<i128>())).collect()).collect();
    let quadratic: Vec<Vec<BigInt>> = directions.iter().map(|u| (0..directions.len()).map(|c| (0..a_n).map(|k| &ev[k][c] * u[k]).sum()).collect()).collect();
    let mut sums = Vec::new();
    for k in (0..usize::BITS).map(|b| 1usize << b).take_while(|&k| k <= directions.len()) {
        let g: Vec<Vec<BigInt>> = gram[..k].iter().map(|row| row[..k].to_vec()).collect();
        let q: Vec<Vec<BigInt>> = quadratic[..k].iter().map(|row| row[..k].to_vec()).collect();
        let (dg, z) = solve_scaled(&g, &q, true)?;
        sums.push((k, (0..k).map(|i| z[i][i].clone()).sum(), dg));
    }
    Ok((sums, (0..directions.len()).map(|i| (quadratic[i][i].clone(), gram[i][i].clone())).collect()))
}

/// A direction over the arriving classes, its largest `count` entries with their signs.
fn leading_classes(v: &[i64], arriving: &[usize], count: usize) -> String {
    let mut order: Vec<usize> = (0..v.len()).collect();
    order.sort_by_key(|&k| std::cmp::Reverse(v[k].unsigned_abs()));
    order.iter().take(count).map(|&k| format!("{}:{}", class_name(arriving[k]), v[k])).collect::<Vec<_>>().join(" ")
}

/// The region names of the held-out partition's roles, in order.
const PAIR_REGIONS: [&str; 4] = ["prose", "lean", "rust", "digits"];

/// Each byte's encoding with the unit, `x̂ = (E(u), 2^16)`, for the current byte, and for the byte
/// before with the stream's start, `ŷ = (0, 2^16)`.
pub(super) fn pair_hats(tower: &Tower) -> (Vec<Vec<i64>>, Vec<Vec<i64>>) {
    let (w, alphabet) = (tower.declaration.width, tower.declaration.alphabet);
    let hat = |u: usize| -> Vec<i64> {
        let mut x: Vec<i64> = if u < alphabet { tower.encoding(u).iter().map(|&e| e as i64).collect() } else { vec![0; w] };
        x.push(1 << 16);
        x
    };
    ((0..alphabet).map(hat).collect(), (0..=alphabet).map(hat).collect())
}

/// The pass both pair foundings share: the frozen tower read once over the training text (one
/// part) and over the held-out text (one part per region), keeping each part's face moments and
/// the table of the pairs of bytes that occur, with the classes that arrive.
struct PairReading {
    learner: TowerLearner,
    arriving: Vec<usize>,
    train: PairMoments,
    held: Vec<PairMoments>,
    train_streams: Vec<Vec<usize>>,
    dev_streams: Vec<Vec<usize>>,
    dev_roles: Vec<u8>,
    started: std::time::Instant,
}

impl PairReading {
    /// `STATE STATE_SHA TRAIN TRAIN_SHA DEV DEV_SHA DEV_ROLES DEV_ROLES_SHA STREAMS` and the
    /// command's own last argument.
    fn read(args: &[String], usage: &str) -> Result<Self> {
        if args.len() != 11 {
            return Err(usage.into());
        }
        let started = std::time::Instant::now();
        let learner = TowerLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
        let train = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
        let dev = pinned_read(&args[5], &args[6], READ_BUDGET as usize)?;
        let dev_roles = roles_of(&args[7], &args[8], dev.len())?;
        let streams = positive(&args[9])?;
        if train.len() >= 1 << 32 || dev.len() >= 1 << 32 {
            return Err("the pair sums are carried in 64 bits, for texts below 2^32 bytes".into());
        }
        let tower = &learner.tower;
        let alphabet = tower.declaration.alphabet;
        let cut = |text: &[u8]| -> Vec<Vec<usize>> {
            let chunk = text.len().div_ceil(streams.max(1));
            text.chunks(chunk).map(|s| s.iter().map(|&b| b as usize).collect()).collect()
        };
        let (train_streams, dev_streams) = (cut(&train), cut(&dev));
        let mut arrives = vec![false; alphabet];
        for s in &train_streams {
            for &c in s.iter().skip(1) {
                arrives[c] = true;
            }
        }
        let arriving: Vec<usize> = (0..alphabet).filter(|&c| arrives[c]).collect();
        let train_moments = read_pair_moments(tower, &train_streams, &arriving, None)?.pop().ok_or("no training moments")?;
        let held = read_pair_moments(tower, &dev_streams, &arriving, Some(&dev_roles))?;
        if train_moments.pairs.is_empty() {
            return Err("the training text has no pairs".into());
        }
        println!(
            "FOUND_PASS train_cells={} pairs={} arriving={} held_out_cells={} read_ms={}",
            train_moments.cells,
            train_moments.pairs.len(),
            arriving.len(),
            held.iter().map(|m| m.cells).sum::<usize>(),
            started.elapsed().as_millis()
        );
        Ok(Self { learner, arriving, train: train_moments, held, train_streams, dev_streams, dev_roles, started })
    }

    /// Each byte's encoding with the unit, `x̂ = (E(u), 2^16)`, for the current byte, and for the
    /// byte before with the stream's start, `ŷ = (0, 2^16)`.
    fn hats(&self) -> (Vec<Vec<i64>>, Vec<Vec<i64>>) {
        pair_hats(&self.learner.tower)
    }

    /// The held-out reading of a readout: per region and in all, the brier `T`, the residual, and
    /// (against the face's own readout, `R₀/D₀²`) the share of the face's residual the founded
    /// rows remove.
    fn held_out(&self, rank: usize, readout: &Readout, founded: &[PairTable], base: Option<(&[num_bigint::BigInt], &num_bigint::BigInt)>) -> Result<Vec<num_bigint::BigInt>> {
        use num_bigint::BigInt;
        let d2 = &readout.d * &readout.d;
        let change = |part: usize, r: &BigInt| -> String {
            base.map_or(String::new(), |(base, base_d2)| {
                let scale = (&base[part] * &d2).max(BigInt::from(1));
                format!(":{}", thousandths_of(&((&base[part] * &d2 - r * base_d2) * 1000), &scale))
            })
        };
        let mut residuals = Vec::new();
        let (mut all_t, mut all_r, mut all_cells) = (BigInt::from(0), BigInt::from(0), 0usize);
        let mut line = Vec::new();
        for (part, moments) in self.held.iter().enumerate() {
            let (keys, cells) = moments.table();
            let (_, h, b) = extended(moments, &keys, &cells, founded)?;
            let r = readout_residual(readout, &h, &b, &moments.t);
            let t: BigInt = moments.t.iter().map(|&x| BigInt::from(x)).sum();
            let cell_unit = BigInt::from(moments.cells.max(1)) << 48;
            line.push(format!("{}={}/{}{}", PAIR_REGIONS[part], thousandths_of(&t, &cell_unit), thousandths_of(&r, &(&cell_unit * &d2)), change(part, &r)));
            all_t += &t;
            all_r += &r;
            all_cells += moments.cells;
            residuals.push(r);
        }
        let all_unit = BigInt::from(all_cells.max(1)) << 48;
        line.push(format!("all={}/{}{}", thousandths_of(&all_t, &all_unit), thousandths_of(&all_r, &(&all_unit * &d2)), change(PAIR_REGIONS.len(), &all_r)));
        residuals.push(all_r);
        println!(
            "HELD_OUT rank={rank} (part=brier_T/residual{}) {} elapsed_ms={}",
            if base.is_some() { ":permille_of_the_face_residual_removed" } else { "" },
            line.join(" "),
            self.started.elapsed().as_millis()
        );
        Ok(residuals)
    }
}

/// `found-tower-pair STATE STATE_SHA TRAIN TRAIN_SHA DEV DEV_SHA DEV_ROLES DEV_ROLES_SHA STREAMS
/// RANKS`: found faces on pairs of bytes from the tension a frozen tower leaves, and read each on
/// the held-out text (the mathematics thread's founding at scale, October 24).
///
/// [agent-inferred with the mathematics thread, October 24] One pass over the training text keeps
/// the face's moments and the table of the pairs of bytes that occur ([`PairMoments`]); nothing
/// after the pass touches the cells. A face that is a function of the pair is read from the table
/// alone: its moments are `K = Σ_p τ_p c_p`, `L = Σ_p φ_p c_p` and `C = Σ_p n_p c_p²`, and reading
/// it after the face removes `tr M Q⁻¹ Mᵀ` of the tension (`M = K − BH⁻¹L`, `Q = C − LᵀH⁻¹L`).
///
/// The ceiling is the table itself, every pair its own coordinate: what any face of the pair could
/// carry, against its chance level `(P − 1)/N`. Its class matrix `S − S_w` says how many
/// coordinates that takes: its leading eigenvalue is the most one coordinate of the pair could
/// carry, the sum of the leading `k` the most `k` could ([`leading_directions`]). Each rank founds
/// one coordinate
/// `c_p = (aᵀx̂_p)(bᵀŷ_p)` on the current byte's encoding and the byte before's, each with the
/// unit (`x̂ = (E(u_t), 2^16)`, `ŷ = (E(u_(t−1)), 2^16)`, so either byte's linear face is among
/// them and each step can only keep or raise the drop). With one factor held, the other is the
/// leading generalized eigenvector of `(MᵀM, Q)` on its pool ([`leading_factor`]); the factors
/// alternate from the current byte's with `b` the unit, `v` starting at the class whose tension the
/// ceiling says the pairs carry most; each step's coordinate is read exactly from the table, and
/// the rank stops when a step gains less than `2^(−15)` of its drop. The founded coordinate joins
/// the face and the next rank is founded on what remains. The readout fitted on the training text,
/// with and without the founded coordinates, is read on the held-out text per region.
pub(super) fn found_tower_pair(args: &[String]) -> Result<()> {
    use num_bigint::BigInt;
    let reading = PairReading::read(args, "found-tower-pair STATE STATE_SHA TRAIN TRAIN_SHA DEV DEV_SHA DEV_ROLES DEV_ROLES_SHA STREAMS RANKS")?;
    let ranks = count(&args[10])?;
    let (tower, arriving, train_moments, started) = (&reading.learner.tower, &reading.arriving, &reading.train, reading.started);
    let alphabet = tower.declaration.alphabet;
    let (keys, cells) = train_moments.table();
    let n = train_moments.cells;
    let unit = BigInt::from(n) << 48;
    let (current_hats, before_hats) = reading.hats();
    let held_out = |rank: usize, readout: &Readout, founded: &[PairTable], base: Option<(&[BigInt], &BigInt)>| reading.held_out(rank, readout, founded, base);
    // The face alone.
    let mut founded: Vec<PairTable> = Vec::new();
    let (mut phihat, h, b) = extended(&train_moments, &keys, &cells, &founded)?;
    let mut readout = fit_readout(&h, &b, &train_moments.t)?;
    let tr_t: BigInt = train_moments.t.iter().map(|&x| BigInt::from(x)).sum();
    let (d0, tr_s0): (BigInt, BigInt) = (readout.d.clone(), readout.s.iter().sum());
    println!(
        "FOUND_FACE brier_T={} tension_S={} tension_permille_of_T={} elapsed_ms={}",
        thousandths_of(&tr_t, &unit),
        thousandths_of(&tr_s0, &(&unit * &d0)),
        thousandths_of(&(&tr_s0 * 1000), &(&tr_t * &d0)),
        started.elapsed().as_millis()
    );
    let top = ceiling(&train_moments, &cells)?;
    let (dw, sw) = (top.d.clone(), top.s.clone());
    let tr_sw: BigInt = sw.iter().sum();
    println!(
        "FOUND_CEILING pairs={} ceiling_drop_permille_of_tension={} chance_permille={} rounding=each_entry_within_{}_halves elapsed_ms={}",
        keys.len(),
        thousandths_of(&((&tr_s0 * &dw - &tr_sw * &d0) * 1000), &(&tr_s0 * &dw)),
        thousandths_of(&(BigInt::from(keys.len() - 1) * 1000), &BigInt::from(n)),
        keys.len(),
        started.elapsed().as_millis()
    );
    // The ceiling's class matrix `E = S − S_w = G − BH⁻¹Bᵀ + B_wH_w⁻¹B_wᵀ`, on `D·D_w`: its
    // leading eigenvalue is the most one coordinate of the pair could carry, the leading `k` the
    // most `k` could. Read exactly over the span of its leading directions located at the grain,
    // `tr((VᵀV)⁻¹VᵀEV)`, a lower bound on the sum of the leading `k`.
    let a_n = arriving.len();
    let bx: Vec<Vec<BigInt>> = (0..a_n).into_par_iter().map(|k| (0..a_n).map(|l| (0..b[k].len()).map(|j| &b[k][j] * &readout.x[j][l]).sum()).collect()).collect();
    let dd = &d0 * &dw;
    let e: Vec<Vec<BigInt>> = (0..a_n).map(|k| (0..a_n).map(|l| &dd * top.between[k][l] - &dw * &bx[k][l] + &d0 * &top.bridged[k][l]).collect()).collect();
    let directions = leading_directions(&e, 32);
    let (sums, quadratic) = leading_sums(&e, &directions)?;
    let trace_e: BigInt = (0..a_n).map(|k| e[k][k].clone()).sum();
    let mut line = vec![format!("all:{}", thousandths_of(&(&trace_e * 1000), &(&dw * &tr_s0)))];
    line.extend(sums.iter().map(|(k, num, den)| format!("{k}:{}", thousandths_of(&(num * 1000), &(den * &dw * &tr_s0)))));
    println!("FOUND_SPECTRUM (leading_k:permille_of_tension, at least) {} elapsed_ms={}", line.join(" "), started.elapsed().as_millis());
    for (i, v) in directions.iter().take(8).enumerate() {
        println!("FOUND_DIRECTION {} eigen_permille_of_tension={} classes {}", i + 1, thousandths_of(&(&quadratic[i].0 * 1000), &(&quadratic[i].1 * &dw * &tr_s0)), leading_classes(v, arriving, 8));
    }
    let base = held_out(0, &readout, &founded, None)?;
    let base_d2 = &readout.d * &readout.d;
    let tension = |r: &Readout| -> BigInt { r.s.iter().sum() };
    for rank in 1..=ranks {
        // The class whose tension the ceiling says the pairs carry most: S_kk/D − S_w,kk/D_w.
        let open = (0..arriving.len()).max_by(|&x, &y| (&readout.s[x] * &dw - &sw[x] * &readout.d).cmp(&(&readout.s[y] * &dw - &sw[y] * &readout.d))).unwrap_or(0);
        let mut v = vec![0i64; arriving.len()];
        v[open] = 1 << 15;
        let mut face = PairFace { r: vec![0; alphabet], s: vec![1 << 16; alphabet + 1] };
        let mut best: Option<(PairFace, BigInt, BigInt, Vec<BigInt>, BigInt)> = None;
        let mut last: Option<(BigInt, BigInt)> = None;
        for step in 0.. {
            let current = step % 2 == 0;
            let (hats, other) = if current { (&current_hats, &face.s) } else { (&before_hats, &face.r) };
            let (k, l, c) = pool_moments(&keys, &cells, &phihat, hats, current, other)?;
            let (dm, dq) = reduced(&readout, &k, &l, &c);
            let (factor, carried, powers) = leading_factor(&dm, &dq, v)?;
            v = carried;
            let read: Vec<i128> = hats.iter().map(|x| x.iter().zip(&factor).map(|(&a, &b)| a as i128 * b as i128).sum()).collect();
            if current {
                face.r = release_wide(&read, 16);
            } else {
                face.s = release_wide(&read, 16);
            }
            let (dm, dq) = coordinate_drop(&readout, &keys, &cells, &phihat, &face)?;
            let num: BigInt = dm.iter().map(|x| x * x).sum();
            let den = &readout.d * &dq;
            let positive = den > BigInt::from(0);
            println!(
                "FOUND_STEP rank={rank} step={step} factor={} power_steps={powers} drop_permille_of_tension={} elapsed_ms={}",
                if current { "current_byte" } else { "byte_before" },
                if positive { thousandths_of(&(&num * &d0 * 1000), &(&den * &tr_s0)) } else { "0".into() },
                started.elapsed().as_millis()
            );
            if !positive {
                break;
            }
            if best.as_ref().is_none_or(|(_, bn, bd, _, _)| &num * bd > bn * &den) {
                best = Some((face.clone(), num.clone(), den.clone(), dm, dq));
            }
            let gained = last.as_ref().is_none_or(|(ln, ld)| (&num * ld) << 15u32 > ln * &den * ((1i64 << 15) + 1));
            if !gained {
                break;
            }
            last = Some((num, den));
        }
        let (face, num, den, dm, dq) = best.ok_or("the rank founded no coordinate")?;
        let before = readout.s.clone();
        founded.push(face.table());
        let (next_phihat, h, b) = extended(&train_moments, &keys, &cells, &founded)?;
        phihat = next_phihat;
        readout = fit_readout(&h, &b, &train_moments.t)?;
        let tr_s = tension(&readout);
        println!(
            "FOUND_RANK rank={rank} drop_permille_of_tension={} cumulative_permille_of_tension={} elapsed_ms={}",
            thousandths_of(&(&num * &d0 * 1000), &(&den * &tr_s0)),
            thousandths_of(&((&tr_s0 * &readout.d - &tr_s * &d0) * 1000), &(&tr_s0 * &readout.d)),
            started.elapsed().as_millis()
        );
        // Per class: this rank's drop of the class's own tension, the largest.
        let mut classes: Vec<(BigInt, usize)> = dm.iter().enumerate().filter(|(a, _)| before[*a] > BigInt::from(0)).map(|(a, x)| (x * x * 1000, a)).collect();
        classes.sort_by(|x, y| (&y.0 * &dq * &before[x.1]).cmp(&(&x.0 * &dq * &before[y.1])));
        let classes: Vec<String> = classes
            .iter()
            .take(12)
            .map(|(x, a)| format!("{}:{}", class_name(arriving[*a]), thousandths_of(x, &(&dq * &before[*a]))))
            .collect();
        println!("FOUND_CLASSES rank={rank} (class:permille_of_its_tension) {}", classes.join(" "));
        let lit = |values: &[i64], count: usize| -> String {
            let mut order: Vec<usize> = (0..values.len()).collect();
            order.sort_by_key(|&u| std::cmp::Reverse(values[u].unsigned_abs()));
            order.iter().take(count).map(|&u| format!("{}:{}", if u == alphabet { "start".to_string() } else { class_name(u) }, values[u])).collect::<Vec<_>>().join(" ")
        };
        println!("FOUND_BYTES rank={rank} current_byte {} | byte_before {}", lit(&face.r, 10), lit(&face.s, 10));
        let mut pairs: Vec<(i128, usize)> = keys.iter().zip(&cells).enumerate().map(|(i, (&key, cell))| (cell.n as i128 * (face.value(key) as i128).pow(2), i)).collect();
        pairs.sort_by_key(|&(e, _)| std::cmp::Reverse(e));
        let pairs: Vec<String> = pairs
            .iter()
            .take(12)
            .map(|&(_, i)| {
                let (prev, cur) = keys[i];
                format!("{}{}:{}:{}", if prev == alphabet { "start".to_string() } else { class_name(prev) }, class_name(cur), face.value(keys[i]).signum(), cells[i].n)
            })
            .collect();
        println!("FOUND_PAIRS rank={rank} (pair:sign:cells, by n·c²) {}", pairs.join(" "));
        held_out(rank, &readout, &founded, Some((&base, &base_d2)))?;
    }
    Ok(())
}

/// The search's grain: each feature of the joint face and pair form is scaled by a power of two so
/// its diagonal lies below `2^SEARCH_DIAGONAL_BITS`; the elimination takes, among the face's
/// features and then among the pool's, the one with the largest variance left, and stops a set when
/// that is below `2^(−SEARCH_KEPT_BITS)` of the scale (what is left lies in the span of the ones
/// taken at the grain, and is given no weight). The factor `L` keeps `SEARCH_FRACTION` fractional
/// bits; each term `l·u` is rounded alone and sums are exact, so the factor does not depend on the
/// order the rows are worked in.
///
/// The floor must stand above what the rounding accumulates. A term `l·u` is off by at most
/// `½ + 2^(D−F−1)` (its own rounding, and `u ≤ 2^D` times `l`'s) and an entry takes one term per
/// coordinate taken, under `2^13`: with `D = 50`, `F = 46`, below `2^17`, under the floor
/// `2^(D−K) = 2^20`. Within a set the largest variance is taken first, so `|l| ≤ 1`; a pool row
/// read on a face step has `|l| ≤ (2^D/2^(D−K))^½ = 2^(K/2) = 2^15`, so `l·2^F` stays in 64 bits.
///
/// [measured, October 24] An elimination in the coordinates' own order left the semidefinite cone on
/// the slice (926 pairs against 4,225 products, most of them dependent): pivots just above the floor
/// carried the rounding into entries past `2^61`, first with `F = 30` and then with `F = 46`.
/// Taking the largest variance first is the rank-revealing order, and it bounds `l`.
const SEARCH_DIAGONAL_BITS: u32 = 50;
const SEARCH_KEPT_BITS: u32 = 30;
const SEARCH_FRACTION: u32 = 46;

/// The full pair form's search: the joint moments of the face `f̄` and the pool of every product of
/// a current byte's coordinate with a byte before's, `z_p = x̂_p ⊗ ŷ_p` (the full bilinear form
/// `x̂ᵀWŷ` is a read of this pool), with the covector's cross moments, scaled to the search's grain
/// and factored `G = L·diag(d)·Lᵀ` in the order taken, the cross moments carried through `L⁻¹` as
/// `y`.
struct FormSearch {
    m: usize,
    q: usize,
    n: usize,
    a_n: usize,
    /// The scaled moments' lower triangle, `n × n`.
    gram: Vec<i64>,
    /// `L` by row and step, `n × n`; the coordinate taken at each step, its `d`; how many of the
    /// steps are the face's.
    l: Vec<i64>,
    order: Vec<usize>,
    d: Vec<i64>,
    face_steps: usize,
    /// The cross moments by row, `n × a_n`: carried through `L⁻¹` at each taken row's step.
    y: Vec<i64>,
    e: Vec<i32>,
    s: i32,
}

/// `x·2^(−s)`, rounded to nearest (a left shift when `s` is negative), within 64 bits.
fn scaled(x: i128, s: i32) -> std::result::Result<i64, String> {
    let v = if s > 0 { (x + (1i128 << (s - 1))) >> s } else { x.checked_mul(1i128 << (-s)).ok_or("a scaled moment outgrew its carrier")? };
    i64::try_from(v).map_err(|_| "a scaled moment outgrew its 64-bit grain".to_string())
}

fn narrow(x: i128, what: &str, j: usize, i: usize) -> std::result::Result<i64, String> {
    i64::try_from(x).map_err(|_| format!("the search outgrew its 64-bit grain: {what} at pivot {j}, row {i}: {x}"))
}

impl FormSearch {
    fn new(moments: &PairMoments, keys: &[(usize, usize)], cells: &[&PairCell], cur: &[Vec<i64>], prev: &[Vec<i64>]) -> Result<Self> {
        let (m, a_n, q) = (moments.m, moments.t.len(), cur[0].len());
        let n = m + q * q;
        // Every sum below is of terms bounded by these; under `2^125` no partial sum can overflow.
        let big = |v: &[Vec<i64>]| -> u128 { v.iter().flatten().map(|x| x.unsigned_abs() as u128).max().unwrap_or(0) };
        let (bx, by) = (big(cur), big(prev));
        let total: u128 = cells.iter().map(|c| c.n as u128).sum();
        let largest = |v: &[i64]| -> u128 { v.iter().map(|x| x.unsigned_abs() as u128).max().unwrap_or(0) };
        let phi: u128 = cells.iter().map(|c| largest(&c.phi)).sum();
        let tau: u128 = cells.iter().map(|c| largest(&c.tau)).sum();
        let under = |terms: [u128; 3]| terms.iter().try_fold(1u128, |acc, &x| acc.checked_mul(x)).is_some_and(|x| x < 1 << 125);
        if !under([total, bx * bx, by * by]) || !under([phi, bx, by]) || !under([tau, bx, by]) {
            return Err("the pair form's moments could outgrow their 128-bit carrier".into());
        }
        // Grouped by the current byte: `Σ n_p ŷŷᵀ`, `Σ φ_p ŷᵀ` and `Σ τ_p ŷᵀ`.
        let mut by_cur: Vec<Vec<usize>> = vec![Vec::new(); cur.len()];
        for (p, &(_, c)) in keys.iter().enumerate() {
            by_cur[c].push(p);
        }
        let present: Vec<usize> = (0..cur.len()).filter(|&c| !by_cur[c].is_empty()).collect();
        type Group = (Vec<i128>, Vec<i128>, Vec<i128>);
        let groups: Vec<Group> = present
            .par_iter()
            .map(|&c| {
                let (mut yy, mut fy, mut ty) = (vec![0i128; q * q], vec![0i128; m * q], vec![0i128; a_n * q]);
                for &p in &by_cur[c] {
                    let (cell, yh) = (cells[p], &prev[keys[p].0]);
                    for j in 0..q {
                        let nj = cell.n as i128 * yh[j] as i128;
                        for (slot, &y2) in yy[j * q..(j + 1) * q].iter_mut().zip(yh) {
                            *slot += nj * y2 as i128;
                        }
                    }
                    for (f, &x) in cell.phi.iter().enumerate() {
                        for (slot, &y2) in fy[f * q..(f + 1) * q].iter_mut().zip(yh) {
                            *slot += x as i128 * y2 as i128;
                        }
                    }
                    for (a, &x) in cell.tau.iter().enumerate() {
                        for (slot, &y2) in ty[a * q..(a + 1) * q].iter_mut().zip(yh) {
                            *slot += x as i128 * y2 as i128;
                        }
                    }
                }
                (yy, fy, ty)
            })
            .collect();
        // The diagonal, then each feature's power of two.
        let mut diagonal: Vec<i128> = (0..m).map(|f| moments.h[f * m + f]).collect();
        for i in 0..q {
            for j in 0..q {
                diagonal.push(present.iter().zip(&groups).map(|(&c, g)| (cur[c][i] as i128).pow(2) * g.0[j * q + j]).sum());
            }
        }
        let exponent = |x: i128| -> i32 {
            let bits = 128 - x.unsigned_abs().leading_zeros() as i32;
            if x == 0 { 0 } else { (bits - SEARCH_DIAGONAL_BITS as i32 + 1).div_euclid(2) }
        };
        let e: Vec<i32> = diagonal.iter().map(|&x| exponent(x)).collect();
        let s = exponent(moments.t.iter().copied().max().unwrap_or(0));
        // The lower triangle: the face's own rows, then each block of rows of a current-byte
        // coordinate `i`: its reads of the face, then its products with every block `i₂ ≤ i`.
        let mut lower = vec![0i64; n * n];
        for f in 0..m {
            for f2 in 0..=f {
                lower[f * n + f2] = scaled(moments.h[f2 * m + f], e[f] + e[f2])?;
            }
        }
        let mut y = vec![0i64; n * a_n];
        for f in 0..m {
            for a in 0..a_n {
                y[f * a_n + a] = scaled(moments.b[a * m + f], e[f] + s)?;
            }
        }
        lower[m * n..]
            .par_chunks_mut(q * n)
            .zip(y[m * a_n..].par_chunks_mut(q * a_n))
            .enumerate()
            .try_for_each(|(i, (rows, yrows))| -> std::result::Result<(), String> {
                let read = |part: fn(&Group) -> &Vec<i128>, len: usize, i2: Option<usize>| -> Vec<i128> {
                    let mut acc = vec![0i128; len];
                    for (&c, g) in present.iter().zip(&groups) {
                        let x = cur[c][i] as i128 * i2.map_or(1, |i2| cur[c][i2] as i128);
                        if x != 0 {
                            for (slot, &v) in acc.iter_mut().zip(part(g)) {
                                *slot += x * v;
                            }
                        }
                    }
                    acc
                };
                let face = read(|g| &g.1, m * q, None);
                let cross = read(|g| &g.2, a_n * q, None);
                for j in 0..q {
                    let row = m + i * q + j;
                    for f in 0..m {
                        rows[j * n + f] = scaled(face[f * q + j], e[f] + e[row])?;
                    }
                    for a in 0..a_n {
                        yrows[j * a_n + a] = scaled(cross[a * q + j], e[row] + s)?;
                    }
                }
                for i2 in 0..=i {
                    let block = read(|g| &g.0, q * q, Some(i2));
                    for j in 0..q {
                        let row = m + i * q + j;
                        for j2 in 0..if i2 == i { j + 1 } else { q } {
                            let col = m + i2 * q + j2;
                            rows[j * n + col] = scaled(block[j * q + j2], e[row] + e[col])?;
                        }
                    }
                }
                Ok(())
            })?;
        let mut search = Self { m, q, n, a_n, gram: lower, l: Vec::new(), order: Vec::new(), d: Vec::new(), face_steps: 0, y, e, s };
        search.factor()?;
        Ok(search)
    }

    /// `G = L·diag(d)·Lᵀ`, left-looking: each step takes the remaining coordinate with the largest
    /// variance left (the face's first, then the pool's), reads its column against the steps
    /// before, and carries its row of `y` through them.
    fn factor(&mut self) -> std::result::Result<(), String> {
        let (n, m, a_n) = (self.n, self.m, self.a_n);
        let floor = 1i64 << (SEARCH_DIAGONAL_BITS - SEARCH_KEPT_BITS);
        let half = 1i128 << (SEARCH_FRACTION - 1);
        let term = move |l: i64, u: i64| -> i128 { (l as i128 * u as i128 + half) >> SEARCH_FRACTION };
        let gram = &self.gram;
        let at = |i: usize, j: usize| gram[i.max(j) * n + i.min(j)];
        let mut diag: Vec<i64> = (0..n).map(|i| at(i, i)).collect();
        let mut remaining = vec![true; n];
        let mut l = vec![0i64; n * n];
        let mut face = true;
        loop {
            let k = self.order.len();
            let set = if face { 0..m } else { m..n };
            let taken = set.filter(|&i| remaining[i]).max_by_key(|&i| (diag[i], std::cmp::Reverse(i)));
            let piv = match taken {
                Some(p) if diag[p] >= floor => p,
                _ if face => {
                    face = false;
                    self.face_steps = k;
                    continue;
                }
                _ => break,
            };
            let dk = diag[piv];
            remaining[piv] = false;
            let lp = l[piv * n..piv * n + k].to_vec();
            // The taken row's `u = L·d` on the steps before, and its row of `y` carried through them.
            let w: Vec<i64> = lp.iter().zip(&self.d).map(|(&x, &d)| narrow(term(x, d), "u", k, piv)).collect::<std::result::Result<_, String>>()?;
            let order = &self.order;
            let carried: Vec<i64> = (0..a_n)
                .into_par_iter()
                .map(|a| narrow(self.y[piv * a_n + a] as i128 - lp.iter().zip(order).map(|(&x, &o)| term(x, self.y[o * a_n + a])).sum::<i128>(), "y", k, piv))
                .collect::<std::result::Result<_, String>>()?;
            self.y[piv * a_n..(piv + 1) * a_n].copy_from_slice(&carried);
            l.par_chunks_mut(n).zip(diag.par_iter_mut()).enumerate().filter(|(i, _)| remaining[*i]).try_for_each(|(i, (row, di))| -> std::result::Result<(), String> {
                let u = narrow(at(i, piv) as i128 - row[..k].iter().zip(&w).map(|(&x, &u)| term(x, u)).sum::<i128>(), "u", k, i)?;
                let li = narrow((2 * ((u as i128) << SEARCH_FRACTION) + dk as i128).div_euclid(2 * dk as i128), "l", k, i)?;
                row[k] = li;
                *di = narrow(*di as i128 - term(li, u), "the variance left", k, i)?;
                Ok(())
            })?;
            self.d.push(dk);
            self.order.push(piv);
        }
        self.l = l;
        Ok(())
    }

    /// What the face explains, `Σ_f |y_f|²/d_f`, and the pool's `N = Σ_i y_i y_iᵀ/d_i` over the
    /// pair form's coordinates taken (each term rounded alone), on the scaled covector's grain.
    fn explained(&self) -> (i128, Vec<Vec<i128>>) {
        let a_n = self.a_n;
        let row = |k: usize| &self.y[self.order[k] * a_n..(self.order[k] + 1) * a_n];
        let ratio = |x: i128, d: i128| (2 * x + d).div_euclid(2 * d);
        let face: i128 = (0..self.face_steps).map(|k| row(k).iter().map(|&v| ratio(v as i128 * v as i128, self.d[k] as i128)).sum::<i128>()).sum();
        let pool = (self.face_steps..self.order.len())
            .into_par_iter()
            .fold(
                || vec![vec![0i128; a_n]; a_n],
                |mut acc, k| {
                    let (y, d) = (row(k), self.d[k] as i128);
                    for a in 0..a_n {
                        if y[a] != 0 {
                            for b in a..a_n {
                                acc[a][b] += ratio(y[a] as i128 * y[b] as i128, d);
                            }
                        }
                    }
                    acc
                },
            )
            .reduce(
                || vec![vec![0i128; a_n]; a_n],
                |mut x, y| {
                    for (r, s) in x.iter_mut().zip(&y) {
                        for (u, v) in r.iter_mut().zip(s) {
                            *u += v;
                        }
                    }
                    x
                },
            );
        let full = (0..a_n).map(|a| (0..a_n).map(|b| pool[a.min(b)][a.max(b)]).collect()).collect();
        (face, full)
    }

    /// The face's features and the pool's that no step took.
    fn passed_over(&self) -> (usize, usize) {
        (self.m - self.face_steps, self.n - self.m - (self.order.len() - self.face_steps))
    }

    /// The pair form `W` of the coordinate read along a covector direction `v`: the pool's part of
    /// `G⁻¹Rv`, carried exactly through `Lᵀ` from `d⁻¹L⁻¹Rv = d⁻¹yv` and returned on the
    /// unscaled pool `x̂ ⊗ ŷ` (`W[i][j]`, current byte's coordinate by the byte before's), released
    /// to below `2^62` its largest entry. A coordinate no step took has no weight.
    fn form(&self, v: &[i64]) -> Vec<Vec<i64>> {
        use num_bigint::BigInt;
        let (n, m, q, a_n) = (self.n, self.m, self.q, self.a_n);
        let mut x: Vec<BigInt> = (0..self.order.len())
            .map(|k| {
                let o = self.order[k];
                let g: i128 = self.y[o * a_n..(o + 1) * a_n].iter().zip(v).map(|(&y, &v)| y as i128 * v as i128).sum();
                (BigInt::from(g) << 64u32) / self.d[k]
            })
            .collect();
        for k in (0..self.order.len()).rev() {
            let xk = x[k].clone();
            let o = self.order[k];
            for (k2, &l) in self.l[o * n..o * n + k].iter().enumerate() {
                if l != 0 {
                    x[k2] -= (&xk * l) >> SEARCH_FRACTION;
                }
            }
        }
        let mut by_feature = vec![BigInt::from(0); n];
        for (k, value) in x.into_iter().enumerate() {
            by_feature[self.order[k]] = value;
        }
        let taken: Vec<usize> = self.order[self.face_steps..].to_vec();
        let top = taken.iter().map(|&i| self.e[i]).max().unwrap_or(0);
        let wide: Vec<BigInt> = (m..n).map(|i| if self.e[i] <= top { &by_feature[i] << ((top - self.e[i]) as u32) } else { BigInt::from(0) }).collect();
        let released = release_big(&wide, 62);
        (0..q).map(|i| released[i * q..(i + 1) * q].to_vec()).collect()
    }
}

/// A pair form's values at every pair of the alphabet, `x̂_curᵀ W ŷ_prev`, released to below
/// `2^16` the largest over the pairs the training text holds.
fn form_table(w: &[Vec<i64>], tower: &Tower, keys: &[(usize, usize)]) -> std::result::Result<(PairTable, i32), String> {
    let alphabet = tower.declaration.alphabet;
    let wide = form_values(w, tower);
    let top = keys.iter().map(|&(prev, cur)| wide[prev * alphabet + cur].unsigned_abs()).max().unwrap_or(0);
    let shift = (128 - top.leading_zeros()).saturating_sub(16) as i32;
    Ok((form_table_at(&wide, alphabet, shift)?, shift))
}

/// A form's exact values `x̂ᵀ W ŷ` at every pair of the alphabet, the byte before (with the
/// stream's start) by the current byte, on the tower's encoding ([`ResidentPairFace::exact_values`]).
fn form_values(w: &[Vec<i64>], tower: &Tower) -> Vec<i128> {
    let d = &tower.declaration;
    let opening: Vec<i32> = (0..d.alphabet).flat_map(|u| tower.encoding(u).to_vec()).collect();
    let flat: Vec<i64> = w.iter().flatten().copied().collect();
    ResidentPairFace::exact_values(d.alphabet, d.width, &opening, &flat)
}

/// A form's table: its values released by `shift`.
fn form_table_at(wide: &[i128], alphabet: usize, shift: i32) -> std::result::Result<PairTable, String> {
    let values = wide.iter().map(|&v| scaled(v, shift)).collect::<std::result::Result<Vec<i64>, String>>()?;
    Ok(PairTable { alphabet, values })
}

/// `found-tower-pair-block STATE STATE_SHA TRAIN TRAIN_SHA DEV DEV_SHA DEV_ROLES DEV_ROLES_SHA
/// STREAMS BLOCK`: found a block of `BLOCK` pair coordinates, each a full pair form
/// `c_p = x̂_pᵀ W ŷ_p` of the current byte's encoding and the byte before's, from the tension a
/// frozen tower leaves, and read the block on the held-out text.
///
/// [agent-inferred, October 24] The spectrum of the pairs' class matrix says one product of reads
/// carries about a third of the best single coordinate and text needs tens of coordinates: the
/// mathematics thread's one pair contact `W(x̄⊗ȳ)` is a full bilinear form. Every such form is a
/// read of the pool `z_p = x̂_p ⊗ ŷ_p` (65² coordinates with the units, so either byte's linear face
/// and the constant are among them), and the best block of `k` coordinates is the reduced-rank
/// readout of the tension on the pool after the face: the leading `k` eigenvectors `v` of
/// `M Q⁻¹ Mᵀ`, each coordinate `W_v = Q⁻¹Mᵀv`. The pool's moments come from the pair table alone,
/// grouped by the current byte. The search for the directions and forms runs at a declared grain
/// ([`FormSearch`]): a 4,290-dimensional exact elimination would not finish. What is founded is
/// read exactly: each form's values over the alphabet are its table ([`form_table`]), and the face
/// with the first `k` founded coordinates is fitted on the training moments and read on the
/// held-out text, for each `k` a power of two up to the block.
pub(super) fn found_tower_pair_block(args: &[String]) -> Result<()> {
    use num_bigint::BigInt;
    let reading = PairReading::read(args, "found-tower-pair-block STATE STATE_SHA TRAIN TRAIN_SHA DEV DEV_SHA DEV_ROLES DEV_ROLES_SHA STREAMS BLOCK")?;
    let founded = found_block(&reading, count(&args[10])?)?;
    let train = &reading.train;
    let (keys, cells) = train.table();
    for k in (0..usize::BITS).map(|b| 1usize << b).take_while(|&k| k <= founded.tables.len()) {
        let (_, h, b) = extended(train, &keys, &cells, &founded.tables[..k])?;
        let fitted = fit_readout(&h, &b, &train.t)?;
        let tr_s: BigInt = fitted.s.iter().sum();
        println!(
            "FOUND_BLOCK coordinates={k} cumulative_permille_of_tension={} elapsed_ms={}",
            thousandths_of(&((&founded.tr_s0 * &fitted.d - &tr_s * &founded.d0) * 1000), &(&founded.tr_s0 * &fitted.d)),
            reading.started.elapsed().as_millis()
        );
        reading.held_out(k, &fitted, &founded.tables[..k], Some((&founded.base, &founded.base_d2)))?;
    }
    Ok(())
}

/// What a block founding returns: each form's weight `W`, the shift its table was released by,
/// and its table; the face's own training tension `D₀·tr S₀` with its `D₀`; and the face's own
/// held-out residuals with their `D₀²`, against which a block is read.
struct FoundedBlock {
    forms: Vec<Vec<Vec<i64>>>,
    shifts: Vec<i32>,
    tables: Vec<PairTable>,
    tr_s0: num_bigint::BigInt,
    d0: num_bigint::BigInt,
    base: Vec<num_bigint::BigInt>,
    base_d2: num_bigint::BigInt,
}

/// The founding `found-tower-pair-block` and `install-tower-pair-block` share: the face's readout,
/// the search, the spectrum, `block` forms and their tables, and the face's own held-out reading.
fn found_block(reading: &PairReading, block: usize) -> Result<FoundedBlock> {
    use num_bigint::BigInt;
    let (arriving, train, started) = (&reading.arriving, &reading.train, reading.started);
    let alphabet = reading.learner.tower.declaration.alphabet;
    let (keys, cells) = train.table();
    let n = train.cells;
    let unit = BigInt::from(n) << 48;
    let (cur, prev) = reading.hats();
    let (_, h, b) = extended(train, &keys, &cells, &[])?;
    let readout = fit_readout(&h, &b, &train.t)?;
    let tr_t: BigInt = train.t.iter().map(|&x| BigInt::from(x)).sum();
    let (d0, tr_s0): (BigInt, BigInt) = (readout.d.clone(), readout.s.iter().sum());
    println!(
        "FOUND_FACE brier_T={} tension_S={} tension_permille_of_T={} elapsed_ms={}",
        thousandths_of(&tr_t, &unit),
        thousandths_of(&tr_s0, &(&unit * &d0)),
        thousandths_of(&(&tr_s0 * 1000), &(&tr_t * &d0)),
        started.elapsed().as_millis()
    );
    let search = FormSearch::new(train, &keys, &cells, &cur, &prev)?;
    let (passed_face, passed_pool) = search.passed_over();
    let (face, pool) = search.explained();
    // `tr T` on the search's grain, against which the face's and the pool's shares are read.
    let tr_t_grain: i128 = train.t.iter().map(|&t| if search.s > 0 { (t + (1i128 << (2 * search.s - 1))) >> (2 * search.s) } else { t << (-2 * search.s) }).sum();
    let tension_grain = tr_t_grain - face;
    let pool_trace: i128 = (0..search.a_n).map(|a| pool[a][a]).sum();
    println!(
        "FOUND_FORM coordinates={} passed_over_face={} passed_over_pool={} face_permille_of_T exact={} search={} pool_permille_of_tension={} elapsed_ms={}",
        search.n - search.m,
        passed_face,
        passed_pool,
        thousandths_of(&((&tr_t * &d0 - &tr_s0) * 1000), &(&tr_t * &d0)),
        thousandths_of(&BigInt::from(face * 1000), &BigInt::from(tr_t_grain.max(1))),
        thousandths_of(&BigInt::from(pool_trace * 1000), &BigInt::from(tension_grain.max(1))),
        started.elapsed().as_millis()
    );
    let pool_big: Vec<Vec<BigInt>> = pool.iter().map(|row| row.iter().map(|&x| BigInt::from(x)).collect()).collect();
    let directions = leading_directions(&pool_big, block);
    let (sums, quadratic) = leading_sums(&pool_big, &directions)?;
    let line: Vec<String> = sums.iter().map(|(k, num, den)| format!("{k}:{}", thousandths_of(&(num * 1000), &(den * BigInt::from(tension_grain.max(1)))))).collect();
    println!("FOUND_FORM_SPECTRUM (leading_k:permille_of_tension, at the search grain) {} elapsed_ms={}", line.join(" "), started.elapsed().as_millis());
    let forms: Vec<Vec<Vec<i64>>> = directions.par_iter().map(|v| search.form(v)).collect();
    let tower = &reading.learner.tower;
    let (tables, shifts): (Vec<PairTable>, Vec<i32>) = forms.par_iter().map(|w| form_table(w, tower, &keys)).collect::<std::result::Result<Vec<_>, String>>()?.into_iter().unzip();
    println!("FOUND_FORMS founded={} elapsed_ms={}", tables.len(), started.elapsed().as_millis());
    let unseen = |table: &PairTable| -> String {
        // The held-out pairs the training text never met, and the share of this coordinate's
        // held-out square they carry.
        let (mut count, mut square, mut all) = (0usize, 0i128, 0i128);
        for moments in &reading.held {
            for (&key, cell) in &moments.pairs {
                let v = table.value(key) as i128;
                all += cell.n as i128 * v * v;
                if !train.pairs.contains_key(&key) {
                    count += cell.n as usize;
                    square += cell.n as i128 * v * v;
                }
            }
        }
        format!("held_out_unseen_cells={count} unseen_permille_of_square={}", thousandths_of(&BigInt::from(square * 1000), &BigInt::from(all.max(1))))
    };
    for (i, (v, table)) in directions.iter().zip(&tables).take(4).enumerate() {
        let mut pairs: Vec<(i128, usize)> = keys.iter().zip(&cells).enumerate().map(|(p, (&key, cell))| (cell.n as i128 * (table.value(key) as i128).pow(2), p)).collect();
        pairs.sort_by_key(|&(e, _)| std::cmp::Reverse(e));
        let pairs: Vec<String> = pairs
            .iter()
            .take(12)
            .map(|&(_, p)| {
                let (b, c) = keys[p];
                format!("{}{}:{}:{}", if b == alphabet { "start".to_string() } else { class_name(b) }, class_name(c), table.value(keys[p]).signum(), cells[p].n)
            })
            .collect();
        println!(
            "FOUND_FORM_COORDINATE {} eigen_permille_of_tension={} {} classes {} | pairs (pair:sign:cells, by n·c²) {}",
            i + 1,
            thousandths_of(&(&quadratic[i].0 * 1000), &(&quadratic[i].1 * BigInt::from(tension_grain.max(1)))),
            unseen(table),
            leading_classes(v, arriving, 8),
            pairs.join(" ")
        );
    }
    let base = reading.held_out(0, &readout, &[], None)?;
    let base_d2 = &readout.d * &readout.d;
    Ok(FoundedBlock { forms, shifts, tables, tr_s0, d0, base, base_d2 })
}

/// The step grain of the block's mixture, `η = j/2^5`: the code is convex in `η`, so the least
/// code on this partition of `[0, 1)` lies within `2^(−5)` of the least code. [agent-inferred,
/// October 24]
const BLOCK_GRAIN: u32 = 5;

/// [definition; agent-inferred, October 24] **The founded block joined beside the tower's
/// readout.** At a cell the readout fitted with the face and the forms reads the covector it
/// expects, `ĝ = R f̂` with `f̂ = (top, 1, c_1(p), …, c_k(p))` (on the covector's grain `2^(−24)`),
/// so `q̂ = p̂ − ĝ` is the block's estimate of the distribution the cell's next class is drawn
/// from: the face the Brier tension is measured against. On the classes the training text
/// brought (nothing off them) it is projected on the simplex, the distribution nearest it in
/// the Brier distance ([`PairBlock::projected`]), and the joined face is the mixture
///
/// ```text
/// p′ = (1 − η) p̂ + η q̃,        η = j/2^grain,  0 ≤ j < 2^grain
/// ```
///
/// which keeps every class the tower's face keeps, so every code stays finite. Its code
/// `−log₂ p′(a)` is convex in `η`; the installed `η` is the least code over the training text on
/// the declared partition, and the held-out text is read at every `η` beside it.
struct PairBlock {
    tower_sha: String,
    alphabet: usize,
    arriving: Vec<usize>,
    forms: Vec<Vec<Vec<i64>>>,
    shifts: Vec<i32>,
    tables: Vec<PairTable>,
    /// `R` on `2^(−readout_bits)`, a row per coordinate of `f̂`, a column per arriving class.
    readout: Vec<Vec<i64>>,
    readout_bits: u32,
    grain: u32,
    eta: u64,
}

impl PairBlock {
    /// The block from its founding: the readout fitted with the face and the forms, released
    /// below `2^62` its largest weight (`R = round(X 2^b / D)`).
    fn new(tower_sha: &str, tower: &Tower, arriving: &[usize], founded: FoundedBlock, fitted: &Readout) -> Result<Self> {
        use num_bigint::BigInt;
        use num_traits::{Signed, ToPrimitive};
        let top = fitted.x.iter().flatten().map(|x| x.bits()).max().unwrap_or(0) as i64;
        let bits = 61 + fitted.d.bits() as i64 - top;
        if bits < 0 || fitted.d <= BigInt::from(0) {
            return Err("the block's readout outgrew its 64-bit grain".into());
        }
        let half: BigInt = &fitted.d >> 1usize;
        let readout = fitted
            .x
            .iter()
            .map(|row| {
                row.iter()
                    .map(|x| {
                        let num: BigInt = x << bits as usize;
                        let q: BigInt = if num.is_negative() { -((-num + &half) / &fitted.d) } else { (num + &half) / &fitted.d };
                        q.to_i64().ok_or("the block's readout outgrew its 64-bit grain")
                    })
                    .collect::<std::result::Result<Vec<i64>, _>>()
            })
            .collect::<std::result::Result<Vec<_>, _>>()?;
        Ok(Self {
            tower_sha: tower_sha.to_string(),
            alphabet: tower.declaration.alphabet,
            arriving: arriving.to_vec(),
            forms: founded.forms,
            shifts: founded.shifts,
            tables: founded.tables,
            readout,
            readout_bits: bits as u32,
            grain: BLOCK_GRAIN,
            eta: 0,
        })
    }

    /// The block's face at a cell: `q̂ = p̂ − ĝ` on the arriving classes (on `2^(−24)`), projected
    /// on the simplex, `q̃_c = Q_c / (K 2^24)` with `Q_c = max(K q̂_c − (S_K − 2^24), 0)`: `K` the
    /// largest count whose `K`th largest `q̂` lies above the shared shift `(S_K − 2^24)/K`, `S_K`
    /// the sum of those `K`. Returns `Q` over the alphabet (none off the arriving classes) and its
    /// sum `K 2^24`.
    fn projected(&self, top: &[i32], face: &TowerFace, pair: (usize, usize)) -> std::result::Result<(Vec<u128>, u128), &'static str> {
        const OUTGREW: &str = "the block's face outgrew its 128-bit carrier";
        let one = 1i128 << COVECTOR_BITS;
        let f: Vec<i128> = top.iter().map(|&x| x as i128).chain(std::iter::once(1)).chain(self.tables.iter().map(|t| t.value(pair) as i128)).collect();
        if f.len() != self.readout.len() {
            return Err("the block's readout does not read this tower's face");
        }
        // ĝ = R f̂ on 2^(−24 − readout_bits): the face's rows stay below 2^100 (|top| < 2^31,
        // |R| < 2^62, 65 rows); a form's value is checked.
        let mut g = vec![0i128; self.arriving.len()];
        for (j, (row, &x)) in self.readout.iter().zip(&f).enumerate() {
            if x == 0 {
                continue;
            }
            if j < top.len() + 1 {
                for (gk, &r) in g.iter_mut().zip(row) {
                    *gk += r as i128 * x;
                }
            } else {
                for (gk, &r) in g.iter_mut().zip(row) {
                    *gk = (r as i128).checked_mul(x).and_then(|v| v.checked_add(*gk)).ok_or(OUTGREW)?;
                }
            }
        }
        let total = face.total;
        let half = 1i128 << (self.readout_bits.max(1) - 1);
        let q: Vec<i128> = self
            .arriving
            .iter()
            .zip(&g)
            .map(|(&c, &g)| {
                let p = (((face.masses[c] << COVECTOR_BITS) + total / 2) / total) as i128;
                let g = if self.readout_bits == 0 { g } else if g >= 0 { (g + half) >> self.readout_bits } else { -((-g + half) >> self.readout_bits) };
                p - g
            })
            .collect();
        let mut sorted = q.clone();
        sorted.sort_unstable_by(|a, b| b.cmp(a));
        let (mut sum, mut kept, mut kept_sum) = (0i128, 0i128, 0i128);
        for (i, &v) in sorted.iter().enumerate() {
            sum = sum.checked_add(v).ok_or(OUTGREW)?;
            let count = i as i128 + 1;
            if count * v > sum - one {
                kept = count;
                kept_sum = sum;
            }
        }
        let shift = kept_sum - one;
        let mut out = vec![0u128; self.alphabet];
        for (&c, &v) in self.arriving.iter().zip(&q) {
            out[c] = (kept * v - shift).max(0) as u128;
        }
        Ok((out, (kept * one) as u128))
    }

    /// The joined face's total at a cell, `2^grain T K 2^24`, and a class's mass at `η = j/2^grain`,
    /// `(2^grain − j) m_c K 2^24 + j Q_c T`. Below `2^8` classes every term stays below `2^108`.
    fn total(&self, face: &TowerFace, qt: u128) -> u128 {
        (face.total * qt) << self.grain
    }

    fn mass(&self, face: &TowerFace, q: &[u128], qt: u128, j: u64, class: usize) -> u128 {
        ((1u128 << self.grain) - j as u128) * face.masses[class] * qt + j as u128 * q[class] * face.total
    }

    /// The joined face at the installed `η`, over the alphabet.
    fn joined(&self, top: &[i32], face: &TowerFace, pair: (usize, usize)) -> Result<Vec<u128>> {
        let (q, qt) = self.projected(top, face, pair)?;
        Ok((0..self.alphabet).map(|c| self.mass(face, &q, qt, self.eta, c)).collect())
    }

    fn to_text(&self) -> String {
        let join = |xs: &mut dyn Iterator<Item = String>| xs.collect::<Vec<_>>().join(" ");
        let mut out = format!(
            "tower-pair-block 1\ntower {}\nalphabet {} forms {} grain {} eta {} readout_bits {}\narriving {}\n",
            self.tower_sha,
            self.alphabet,
            self.forms.len(),
            self.grain,
            self.eta,
            self.readout_bits,
            join(&mut self.arriving.iter().map(|c| c.to_string()))
        );
        for (w, s) in self.forms.iter().zip(&self.shifts) {
            out += &format!("form {s} {}\n", join(&mut w.iter().flatten().map(|v| v.to_string())));
        }
        for row in &self.readout {
            out += &format!("readout {}\n", join(&mut row.iter().map(|v| v.to_string())));
        }
        out
    }

    /// The block read back for `tower`: each form's table rebuilt from its weight and shift.
    fn from_text(text: &str, tower: &Tower, tower_sha: &str) -> Result<Self> {
        let bad = || -> Box<dyn std::error::Error> { "a malformed pair block".into() };
        let mut lines = text.lines();
        if lines.next() != Some("tower-pair-block 1") {
            return Err(bad());
        }
        let sha = lines.next().and_then(|l| l.strip_prefix("tower ")).ok_or_else(bad)?;
        if sha != tower_sha {
            return Err("the pair block was founded on another tower state".into());
        }
        let head: Vec<&str> = lines.next().ok_or_else(bad)?.split(' ').collect();
        if head.len() != 10 || head[0] != "alphabet" || head[2] != "forms" || head[4] != "grain" || head[6] != "eta" || head[8] != "readout_bits" {
            return Err(bad());
        }
        let (alphabet, forms, grain, eta, readout_bits): (usize, usize, u32, u64, u32) = (head[1].parse()?, head[3].parse()?, head[5].parse()?, head[7].parse()?, head[9].parse()?);
        if alphabet != tower.declaration.alphabet || grain >= 8 || eta >= 1 << grain {
            return Err(bad());
        }
        let arriving: Vec<usize> = lines.next().and_then(|l| l.strip_prefix("arriving ")).ok_or_else(bad)?.split(' ').map(|c| c.parse()).collect::<std::result::Result<_, _>>()?;
        if arriving.iter().any(|&c| c >= alphabet) {
            return Err(bad());
        }
        let hat = tower.declaration.width + 1;
        let (mut ws, mut shifts, mut tables) = (Vec::new(), Vec::new(), Vec::new());
        for _ in 0..forms {
            let words: Vec<i64> = lines.next().and_then(|l| l.strip_prefix("form ")).ok_or_else(bad)?.split(' ').map(|v| v.parse()).collect::<std::result::Result<_, _>>()?;
            if words.len() != 1 + hat * hat {
                return Err(bad());
            }
            let w: Vec<Vec<i64>> = words[1..].chunks(hat).map(|r| r.to_vec()).collect();
            let shift = words[0] as i32;
            tables.push(form_table_at(&form_values(&w, tower), alphabet, shift)?);
            ws.push(w);
            shifts.push(shift);
        }
        let readout: Vec<Vec<i64>> = lines
            .map(|l| l.strip_prefix("readout ").ok_or_else(bad).and_then(|r| r.split(' ').map(|v| v.parse::<i64>().map_err(|e| e.into())).collect::<Result<Vec<i64>>>()))
            .collect::<Result<_>>()?;
        if readout.len() != tower.declaration.width + 1 + forms || readout.iter().any(|r| r.len() != arriving.len()) {
            return Err(bad());
        }
        Ok(Self { tower_sha: sha.to_string(), alphabet, arriving, forms: ws, shifts, tables, readout, readout_bits, grain, eta })
    }
}

/// The codes of a text's cells read in its streams, per region of `roles` (one part when none):
/// the tower's own code, the joined face's at every `η = j/2^grain` on `2^(−20)` bits, and the
/// cells.
type BlockCodes = Vec<(i64, Vec<i64>, usize)>;

fn block_codes(tower: &Tower, block: &PairBlock, streams: &[Vec<usize>], roles: Option<&[u8]>) -> Result<BlockCodes> {
    let parts = if roles.is_some() { PAIR_REGIONS.len() } else { 1 };
    let steps = 1usize << block.grain;
    let alphabet = tower.declaration.alphabet;
    let chunk = streams.first().map_or(0, |s| s.len());
    let read: Vec<BlockCodes> = streams
        .par_iter()
        .enumerate()
        .map(|(s, classes)| {
            let mut out: BlockCodes = (0..parts).map(|_| (0i64, vec![0i64; steps], 0usize)).collect();
            let mut state = tower.rest();
            tower
                .read_faces(&mut state, classes, |i, top, face| {
                    let prev = if i == 0 { alphabet } else { classes[i - 1] };
                    let actual = classes[i + 1];
                    let part = &mut out[roles.map_or(0, |r| r[s * chunk + i + 1] as usize)];
                    part.0 += face.code(actual);
                    let (q, qt) = block.projected(top, face, (prev, classes[i])).map_err(TowerError::Refused)?;
                    let total = block.total(face, qt);
                    for (j, code) in part.1.iter_mut().enumerate() {
                        *code += code_of(block.mass(face, &q, qt, j as u64, actual), total);
                    }
                    part.2 += 1;
                    Ok(())
                })
                .map_err(|e| e.to_string())?;
            Ok(out)
        })
        .collect::<std::result::Result<_, String>>()?;
    let mut merged: BlockCodes = (0..parts).map(|_| (0i64, vec![0i64; steps], 0usize)).collect();
    for stream in read {
        for (into, part) in merged.iter_mut().zip(stream) {
            into.0 += part.0;
            for (x, y) in into.1.iter_mut().zip(&part.1) {
                *x += y;
            }
            into.2 += part.2;
        }
    }
    Ok(merged)
}

/// One part's codes as a line: the tower's own bits a byte, then each `η`'s.
fn block_code_line(name: &str, (own, codes, cells): &(i64, Vec<i64>, usize), grain: u32) -> String {
    let etas: Vec<String> = codes.iter().enumerate().map(|(j, &c)| format!("{j}:{}", per(c, (*cells).max(1)))).collect();
    format!("part={name} cells={cells} tower={} (j:bits_a_byte, eta=j/{}) {}", per(*own, (*cells).max(1)), 1u32 << grain, etas.join(" "))
}

/// `install-tower-pair-block STATE STATE_SHA TRAIN TRAIN_SHA DEV DEV_SHA DEV_ROLES DEV_ROLES_SHA
/// STREAMS BLOCK OUT`: found a block of `BLOCK` full pair forms as `found-tower-pair-block` does,
/// join it beside the tower's readout ([`PairBlock`]), install the `η` whose code over the
/// training text is least, read the held-out text at every `η`, and write the block to `OUT`.
pub(super) fn install_tower_pair_block(args: &[String]) -> Result<()> {
    const USAGE: &str = "install-tower-pair-block STATE STATE_SHA TRAIN TRAIN_SHA DEV DEV_SHA DEV_ROLES DEV_ROLES_SHA STREAMS BLOCK OUT";
    if args.len() != 12 {
        return Err(USAGE.into());
    }
    let out = Path::new(&args[11]);
    if out.exists() {
        return Err("the block's file already exists".into());
    }
    let reading = PairReading::read(&args[..11], USAGE)?;
    let founded = found_block(&reading, count(&args[10])?)?;
    let train = &reading.train;
    let (keys, cells) = train.table();
    let (_, h, b) = extended(train, &keys, &cells, &founded.tables)?;
    let fitted = fit_readout(&h, &b, &train.t)?;
    let (base, base_d2) = (founded.base.clone(), founded.base_d2.clone());
    reading.held_out(founded.tables.len(), &fitted, &founded.tables, Some((&base, &base_d2)))?;
    let tower = &reading.learner.tower;
    let mut block = PairBlock::new(&args[2], tower, &reading.arriving, founded, &fitted)?;
    let trained = block_codes(tower, &block, &reading.train_streams, None)?;
    println!("BLOCK_JOIN text=training {} elapsed_ms={}", block_code_line("all", &trained[0], block.grain), reading.started.elapsed().as_millis());
    let (_, codes, cells) = &trained[0];
    let least = (0..codes.len()).min_by_key(|&j| codes[j]).unwrap_or(0);
    block.eta = least as u64;
    println!(
        "BLOCK_JOIN_INSTALLED eta={least}/{} training_bits_a_byte={} tower={} readout_bits={}",
        1u32 << block.grain,
        per(codes[least], (*cells).max(1)),
        per(trained[0].0, (*cells).max(1)),
        block.readout_bits
    );
    let held = block_codes(tower, &block, &reading.dev_streams, Some(&reading.dev_roles))?;
    let mut all = (0i64, vec![0i64; 1 << block.grain], 0usize);
    for (name, part) in PAIR_REGIONS.iter().zip(&held) {
        println!("BLOCK_JOIN text=held_out {}", block_code_line(name, part, block.grain));
        all.0 += part.0;
        for (x, y) in all.1.iter_mut().zip(&part.1) {
            *x += y;
        }
        all.2 += part.2;
    }
    println!("BLOCK_JOIN text=held_out {} elapsed_ms={}", block_code_line("all", &all, block.grain), reading.started.elapsed().as_millis());
    let at: Vec<String> = PAIR_REGIONS
        .iter()
        .zip(&held)
        .chain(std::iter::once((&"all", &all)))
        .map(|(name, (own, codes, n))| format!("{name}={}->{}", per(*own, (*n).max(1)), per(codes[least], (*n).max(1))))
        .collect();
    println!("BLOCK_JOIN_HELD_OUT eta={least}/{} (part=tower->joined, bits a byte) {}", 1u32 << block.grain, at.join(" "));
    write_new(out, block.to_text().as_bytes())?;
    let written = std::fs::read(out)?;
    println!("BLOCK_WRITTEN bytes={} sha256={} elapsed_ms={}", written.len(), sha256(&written)?, reading.started.elapsed().as_millis());
    Ok(())
}

/// `sample-tower-block STATE STATE_SHA BLOCK BLOCK_SHA PROMPT PROMPT_SHA KEYS KEYS_SHA BYTES OUT
/// [AGREE]`: a fork of the rested tower with its pair block joined at the installed `η`. It
/// receives the prompt and releases bytes by exact agreeing draws on the joined face, as
/// `sample-tower` does on the tower's own; at `η = 0` the two release the same bytes.
pub(super) fn sample_tower_block(args: &[String]) -> Result<()> {
    if args.len() != 11 && args.len() != 12 {
        return Err("sample-tower-block STATE STATE_SHA BLOCK BLOCK_SHA PROMPT PROMPT_SHA KEYS KEYS_SHA BYTES OUT [AGREE]".into());
    }
    let agree = agreement(args.get(11))?;
    let started = Instant::now();
    let learner = TowerLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let tower = &learner.tower;
    let block = PairBlock::from_text(std::str::from_utf8(&pinned_read(&args[3], &args[4], STATE_BUDGET)?)?, tower, &args[2])?;
    let prompt = pinned_read(&args[5], &args[6], QUERY_BYTE_BUDGET)?;
    let keys = pinned_read(&args[7], &args[8], READ_BUDGET as usize)?;
    let count: usize = args[9].parse()?;
    if keys.len() < count.checked_mul(8).ok_or("key extent overflow")? {
        return Err("fewer eight-byte keys than declared bytes".into());
    }
    let out = Path::new(&args[10]);
    std::fs::create_dir(out)?;
    let alphabet = tower.declaration.alphabet;
    let mut state = tower.rest();
    let (mut own, mut joined_code, mut prev) = (0i64, 0i64, alphabet);
    let mut last: Option<(Vec<i32>, TowerFace, (usize, usize))> = None;
    for &b in &prompt {
        let c = b as usize;
        if let Some((top, face, pair)) = &last {
            own += face.code(c);
            let masses = block.joined(top, face, *pair)?;
            joined_code += code_of(masses[c], masses.iter().sum());
        }
        let (face, top) = tower.advance_top(&mut state, c).map_err(|e| e.to_string())?;
        last = Some((top, face, (prev, c)));
        prev = c;
    }
    let (mut top, mut face, mut pair) = last.ok_or("an empty prompt")?;
    let mut key_stream = KeyStream::new(keys, 8)?;
    let mut released = Vec::with_capacity(count);
    while released.len() < count {
        let key = key_stream.next_key().ok_or("fewer keys than declared bytes")?;
        let class = agreeing_class(&block.joined(&top, &face, pair)?, agree, &key)?;
        released.push(class as u8);
        (face, top) = tower.advance_top(&mut state, class).map_err(|e| e.to_string())?;
        pair = (pair.1, class);
    }
    write_new(&out.join("OUTPUT.bin"), &released)?;
    let prompt_bytes = prompt.len().saturating_sub(1).max(1);
    println!(
        "TOWER_SAMPLE prompt_bits_a_byte={} joined_prompt_bits_a_byte={} eta={}/{} bytes={} agree={} elapsed_ms={}",
        per(own, prompt_bytes),
        per(joined_code, prompt_bytes),
        block.eta,
        1u32 << block.grain,
        released.len(),
        agree,
        started.elapsed().as_millis()
    );
    println!("TOWER_SAMPLE_TEXT {:?}", String::from_utf8_lossy(&released));
    Ok(())
}

/// The pairs `(class before, class arriving)` a training text read in `streams` contiguous streams
/// meets, each stream opening at the start `A` (the training passes' cut, `fit`).
fn met_pairs(text: &[u8], streams: usize, alphabet: usize) -> Result<std::collections::HashSet<(usize, usize)>> {
    if streams == 0 || text.len() < 2 * streams {
        return Err("a stream needs two bytes, one cell".into());
    }
    let chunk = text.len() / streams;
    let mut met = std::collections::HashSet::new();
    for s in 0..streams {
        let part = &text[s * chunk..(s + 1) * chunk];
        met.insert((alphabet, part[0] as usize));
        for w in part.windows(2) {
            met.insert((w[0] as usize, w[1] as usize));
        }
    }
    Ok(met)
}

/// `join-tower-pair-face STATE STATE_SHA BLOCK BLOCK_SHA TRAIN TRAIN_SHA STREAMS OUT`: the founded
/// block's forms joined to the learner as its resident pair face ([`Tower::join_pair_face`]), the
/// face's readout and lift opened at zero, written as `OUT/STATE.0` for the passes to continue.
///
/// [agent-inferred, October 24] The block joined beside the readout (`install-tower-pair-block`)
/// reads the forms through a closed-form Brier fit and a mixture; joined to the learner they are
/// read through learned material, `z += V c(p)` and `x⁰ = E(u) + P c(p)`, which the section's
/// covector moves under the certified deposit. Beside the join, each form's largest value over the
/// pairs the training text meets and over the pairs it never meets is printed: a form takes large
/// values on unmet pairs whose leverage is large (GPT-6's extension witness,
/// `|wᵀQQ⁺c*| ≤ √(wᵀQw) √(c*ᵀQ⁺c*)`), and the joined learner reads those pairs too. The face is
/// the forms' face at every pair (no table of which contexts were seen); the held-out cells at
/// unmet pairs are read apart by `read-tower-pair-cells`.
pub(super) fn join_tower_pair_face(args: &[String]) -> Result<()> {
    if args.len() != 9 {
        return Err("join-tower-pair-face STATE STATE_SHA BLOCK BLOCK_SHA TRAIN TRAIN_SHA STREAMS OUT".into());
    }
    let started = Instant::now();
    let state = pinned_read(&args[1], &args[2], STATE_BUDGET)?;
    let mut learner = TowerLearner::from_text(std::str::from_utf8(&state)?).map_err(|e| e.to_string())?;
    let block_text = pinned_read(&args[3], &args[4], STATE_BUDGET)?;
    let block = PairBlock::from_text(std::str::from_utf8(&block_text)?, &learner.tower, &args[2])?;
    let train = pinned_read(&args[5], &args[6], READ_BUDGET as usize)?;
    let streams = positive(&args[7])?;
    let out = Path::new(&args[8]);
    let d = learner.tower.declaration;
    let opening: Vec<i32> = (0..d.alphabet).flat_map(|u| learner.tower.encoding(u).to_vec()).collect();
    let forms: Vec<Vec<i64>> = block.forms.iter().map(|w| w.iter().flatten().copied().collect()).collect();
    let face = ResidentPairFace::new(d.alphabet, d.width, opening, forms, block.shifts.clone()).map_err(|e| e.to_string())?;
    // The face is the block's tables, pair by pair.
    let k = face.forms();
    for prev in 0..=d.alphabet {
        for cur in 0..d.alphabet {
            let c = face.at(prev, cur);
            if (0..k).any(|v| c[v] as i64 != block.tables[v].value((prev, cur))) {
                return Err("the pair face parts from the block's tables".into());
            }
        }
    }
    let met = met_pairs(&train, streams, d.alphabet)?;
    let pairs = (d.alphabet + 1) * d.alphabet;
    println!("PAIR_FACE forms={k} pairs={pairs} met={} unmet={} agrees_with_block=true elapsed_ms={}", met.len(), pairs - met.len(), started.elapsed().as_millis());
    let mut line = Vec::new();
    for v in 0..k {
        let (mut on_met, mut on_unmet, mut past) = (0u32, 0u32, 0usize);
        for prev in 0..=d.alphabet {
            for cur in 0..d.alphabet {
                let c = face.at(prev, cur)[v].unsigned_abs();
                if met.contains(&(prev, cur)) {
                    on_met = on_met.max(c);
                } else {
                    on_unmet = on_unmet.max(c);
                }
            }
        }
        for prev in 0..=d.alphabet {
            for cur in 0..d.alphabet {
                past += (!met.contains(&(prev, cur)) && face.at(prev, cur)[v].unsigned_abs() > on_met) as usize;
            }
        }
        line.push(format!("{}:{on_met}:{on_unmet}:{past}", v + 1));
    }
    println!("PAIR_FACE_REACH (form:max|c|_met:max|c|_unmet:unmet_pairs_past_the_met_max, on 2^-16) {}", line.join(" "));
    learner.join_pair_face(face).map_err(|e| e.to_string())?;
    std::fs::create_dir(out)?;
    let text = learner.to_text();
    write_new(&out.join("STATE.0"), text.as_bytes())?;
    println!("PAIR_FACE_JOINED material={} state_bytes={} state_sha256={} elapsed_ms={}", learner.tower.theta.len(), text.len(), sha256(text.as_bytes())?, started.elapsed().as_millis());
    Ok(())
}

/// `read-tower-pair-cells STATE STATE_SHA TRAIN TRAIN_SHA TRAIN_STREAMS DEV DEV_SHA DEV_ROLES
/// DEV_ROLES_SHA STREAMS`: the held-out reading (`held_out`, `STREAMS` parts each from rest) split
/// by whether each cell's pair `(class before, class arriving)` is one the training text meets in
/// its `TRAIN_STREAMS` streams (`met_pairs`): per region, the cells and bits a byte of each side.
/// A reading of any tower, with or without a pair face, so a joined tower and its foil are read
/// alike.
pub(super) fn read_tower_pair_cells(args: &[String]) -> Result<()> {
    if args.len() != 11 {
        return Err("read-tower-pair-cells STATE STATE_SHA TRAIN TRAIN_SHA TRAIN_STREAMS DEV DEV_SHA DEV_ROLES DEV_ROLES_SHA STREAMS".into());
    }
    let started = Instant::now();
    let learner = TowerLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let tower = &learner.tower;
    let train = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let met = met_pairs(&train, positive(&args[5])?, tower.declaration.alphabet)?;
    let dev = pinned_read(&args[6], &args[7], READ_BUDGET as usize)?;
    let roles = roles_of(&args[8], &args[9], dev.len())?;
    let streams = positive(&args[10])?;
    let classes: Vec<usize> = dev.iter().map(|&b| b as usize).collect();
    let chunk = classes.len().div_ceil(streams);
    let starts: Vec<usize> = (0..classes.len()).step_by(chunk).collect();
    // Per region, (met code, met cells, unmet code, unmet cells).
    let parts: Vec<[(i64, usize, i64, usize); 4]> = starts
        .par_iter()
        .map(|&start| {
            let part = &classes[start..(start + chunk).min(classes.len())];
            let mut state = tower.rest();
            let codes = tower.read_cells(&mut state, part).map_err(|e| e.to_string())?;
            let mut regions = [(0i64, 0usize, 0i64, 0usize); 4];
            for (i, code) in codes.into_iter().enumerate() {
                let prev = if i == 0 { tower.declaration.alphabet } else { part[i - 1] };
                let r = &mut regions[roles[start + i + 1] as usize];
                if met.contains(&(prev, part[i])) {
                    r.0 += code;
                    r.1 += 1;
                } else {
                    r.2 += code;
                    r.3 += 1;
                }
            }
            Ok(regions)
        })
        .collect::<std::result::Result<_, String>>()?;
    let mut regions = [(0i64, 0usize, 0i64, 0usize); 4];
    for part in parts {
        for (r, p) in regions.iter_mut().zip(part) {
            *r = (r.0 + p.0, r.1 + p.1, r.2 + p.2, r.3 + p.3);
        }
    }
    let all = regions.iter().fold((0i64, 0usize, 0i64, 0usize), |a, r| (a.0 + r.0, a.1 + r.1, a.2 + r.2, a.3 + r.3));
    let line: Vec<String> = PAIR_REGIONS
        .iter()
        .zip(&regions)
        .chain(std::iter::once((&"all", &all)))
        .map(|(name, r)| format!("{name}=met:{}:{} unmet:{}:{}", r.1, per(r.0, r.1), r.3, per(r.2, r.3)))
        .collect();
    println!("PAIR_CELLS (region=met:cells:bits_a_byte unmet:cells:bits_a_byte) {} elapsed_ms={}", line.join(" "), started.elapsed().as_millis());
    Ok(())
}

/// `read-tower-pair-leverage STATE STATE_SHA TRAIN TRAIN_SHA TRAIN_STREAMS DEV DEV_SHA DEV_ROLES
/// DEV_ROLES_SHA STREAMS STRIDE`: the leverage of each held-out reading against the training
/// text's exact Gram of what the readout reads, `x = (top, 1, c(pair))` (the top face, the bias's
/// coordinate, and the pair face's values when the tower carries one).
///
/// [agent-inferred with the mathematics thread, October 24; its effective-tension record §9] The
/// training text read in its `TRAIN_STREAMS` streams gives `G = Σ x xᵀ` exactly. Its fraction-free
/// elimination in the order face, bias, pair face keeps each row as it stood at its pivot; one
/// forward pass of a reading over those rows gives the border entries `Γ_k`, and
/// `h = Σ Γ_k²/(Δ_(k−1)Δ_k) = −corner/Δ_r`. A passed (zero) pivot with a nonzero border entry is
/// an open part of the reading, a direction no training cell fixed: it is carried as
/// `(coordinate, β_p, Δ_before)` (`ρ_p = β_p/Δ_before` keeps its sign and scale), never refused,
/// and wherever one is carried `h` is the supported chart's part only.
/// For every readout form `w`, `|wᵀv_s|² ≤ (wᵀGw)·h`, so `h` bounds how far a reading's value can
/// sit from what the training cells fixed; in range, the readout's mean square error at the
/// reading is `σ²(1 + h)`. `h` splits at the bias into the face's part and the pair face's part
/// given the face. Held-out cells at pairs the training text never meets are all read; the others
/// at every `STRIDE`th cell. Each `h` is written against the average training cell's leverage,
/// `rank/N` (the training cells' own leverages sum to the rank).
pub(super) fn read_tower_pair_leverage(args: &[String]) -> Result<()> {
    use num_bigint::BigInt;
    use num_traits::{One, Zero};
    if args.len() != 12 {
        return Err("read-tower-pair-leverage STATE STATE_SHA TRAIN TRAIN_SHA TRAIN_STREAMS DEV DEV_SHA DEV_ROLES DEV_ROLES_SHA STREAMS STRIDE".into());
    }
    let started = Instant::now();
    let learner = TowerLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let tower = &learner.tower;
    let (a, w) = (tower.declaration.alphabet, tower.declaration.width);
    let train = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let train_streams = positive(&args[5])?;
    let met = met_pairs(&train, train_streams, a)?;
    let dev = pinned_read(&args[6], &args[7], READ_BUDGET as usize)?;
    let roles = roles_of(&args[8], &args[9], dev.len())?;
    let streams = positive(&args[10])?;
    let stride = positive(&args[11])?;
    let k = tower.pair_face().map_or(0, |face| face.forms());
    let dim = w + 1 + k;
    let fill = |v: &mut [i64], top: &[i32], prev: usize, cur: usize| {
        for (slot, &t) in v[..w].iter_mut().zip(top) {
            *slot = t as i64;
        }
        v[w] = 1;
        if let Some(face) = tower.pair_face() {
            for (slot, &c) in v[w + 1..].iter_mut().zip(face.at(prev, cur)) {
                *slot = c as i64;
            }
        }
    };
    // The training Gram, stream by stream (each from rest, as the passes read it), upper rows.
    let chunk = train.len() / train_streams;
    let grams: Vec<(Vec<i128>, usize)> = (0..train_streams)
        .into_par_iter()
        .map(|s| {
            let part: Vec<usize> = train[s * chunk..(s + 1) * chunk].iter().map(|&b| b as usize).collect();
            let mut g = vec![0i128; dim * dim];
            let mut v = vec![0i64; dim];
            let mut cells = 0usize;
            let mut state = tower.rest();
            tower
                .read_faces(&mut state, &part, |i, top, _| {
                    fill(&mut v, top, if i == 0 { a } else { part[i - 1] }, part[i]);
                    for p in 0..dim {
                        let vp = v[p] as i128;
                        if vp != 0 {
                            for (slot, &vq) in g[p * dim + p..(p + 1) * dim].iter_mut().zip(&v[p..]) {
                                *slot += vp * vq as i128;
                            }
                        }
                    }
                    cells += 1;
                    Ok(())
                })
                .map_err(|e| e.to_string())?;
            Ok((g, cells))
        })
        .collect::<std::result::Result<_, String>>()?;
    let mut gram = vec![0i128; dim * dim];
    let mut cells = 0usize;
    for (g, n) in grams {
        for (slot, x) in gram.iter_mut().zip(g) {
            *slot = slot.checked_add(x).ok_or("the training Gram outgrew its 128-bit carrier")?;
        }
        cells += n;
    }
    let mut m = Upper::from_gram(&gram, dim);
    let order: Vec<usize> = (0..dim).collect();
    let (last, rank) = m.eliminate(&order, &[], BigInt::one(), &|_, _| false)?;
    // Each pivot's predecessor (the last nonzero pivot before it), and the face's last pivot.
    let mut prevs = vec![BigInt::one(); dim];
    let mut before = BigInt::one();
    let mut face_last = BigInt::one();
    for p in 0..dim {
        prevs[p] = before.clone();
        if !m.get(p, p).is_zero() {
            before = m.get(p, p).clone();
        }
        if p == w {
            face_last = before.clone();
        }
    }
    let passed = (0..dim).filter(|&p| m.get(p, p).is_zero()).count();
    println!(
        "LEVERAGE_GRAM state_sha256={} chart=(top,1,c(pair)) cells={cells} dim={dim} forms={k} rank={rank} passed_pivots={passed} face_last_pivot_bits={} last_pivot_bits={} elapsed_ms={}",
        args[2],
        face_last.bits(),
        last.bits(),
        started.elapsed().as_millis()
    );
    // A reading's (−corner at the face's last pivot, −corner, open parts `(p, β_p)`).
    let forward = |x: &[i64]| -> (BigInt, BigInt, Vec<(usize, BigInt)>) {
        let mut xs: Vec<BigInt> = x.iter().map(|&t| BigInt::from(t)).collect();
        let (mut corner, mut corner_face, mut open) = (BigInt::zero(), BigInt::zero(), Vec::new());
        for p in 0..dim {
            let piv = m.get(p, p);
            if piv.is_zero() {
                if !xs[p].is_zero() {
                    open.push((p, xs[p].clone()));
                }
            } else {
                let g = xs[p].clone();
                for i in p + 1..dim {
                    xs[i] = (piv * &xs[i] - m.get(p, i) * &g) / &prevs[p];
                }
                corner = (piv * &corner - &g * &g) / &prevs[p];
            }
            if p == w {
                corner_face = corner.clone();
            }
        }
        (-corner_face, -corner, open)
    };
    // The held-out parts, each from rest: per sampled cell, (met, region, code, −corner_face, −corner, open).
    let classes: Vec<usize> = dev.iter().map(|&b| b as usize).collect();
    let part_len = classes.len().div_ceil(streams);
    let starts: Vec<usize> = (0..classes.len()).step_by(part_len).collect();
    type Read = (bool, usize, i64, BigInt, BigInt, Vec<(usize, BigInt)>);
    let reads: Vec<Vec<Read>> = starts
        .par_iter()
        .map(|&start| {
            let part = &classes[start..(start + part_len).min(classes.len())];
            let mut state = tower.rest();
            let codes = tower.read_cells(&mut state, part).map_err(|e| e.to_string())?;
            let mut state = tower.rest();
            let mut v = vec![0i64; dim];
            let mut out = Vec::new();
            tower
                .read_faces(&mut state, part, |i, top, _| {
                    let prev = if i == 0 { a } else { part[i - 1] };
                    let is_met = met.contains(&(prev, part[i]));
                    if !is_met || (start + i) % stride == 0 {
                        fill(&mut v, top, prev, part[i]);
                        let (face_part, whole, open) = forward(&v);
                        out.push((is_met, roles[start + i + 1] as usize, codes[i], face_part, whole, open));
                    }
                    Ok(())
                })
                .map_err(|e| e.to_string())?;
            Ok(out)
        })
        .collect::<std::result::Result<_, String>>()?;
    let reads: Vec<Read> = reads.into_iter().flatten().collect();
    // Written against the average training cell's leverage rank/N: a reading's h/(rank/N), on the
    // common denominators Δ_face and Δ_r.
    let unit_whole = &last * BigInt::from(rank);
    let unit_face = &face_last * BigInt::from(rank);
    let n_train = BigInt::from(cells);
    for (side, want) in [("met_sampled", true), ("unmet", false)] {
        let mut chosen: Vec<&Read> = reads.iter().filter(|r| r.0 == want).collect();
        let n = chosen.len();
        if n == 0 {
            println!("LEVERAGE side={side} cells=0");
            continue;
        }
        let code: i64 = chosen.iter().map(|r| r.2).sum();
        let sum_whole: BigInt = chosen.iter().map(|r| r.4.clone()).sum();
        let sum_face: BigInt = chosen.iter().map(|r| r.3.clone()).sum();
        let open = chosen.iter().filter(|r| !r.5.is_empty()).count();
        // A few open parts as they stand: the coordinate (face j, the bias, or form v) and ρ_p.
        let name = |p: usize| if p < w { format!("face{p}") } else if p == w { "bias".into() } else { format!("form{}", p - w) };
        let rows: Vec<String> = chosen
            .iter()
            .flat_map(|r| r.5.iter())
            .take(4)
            .map(|(p, beta)| format!("{}:{}", name(*p), thousandths_of(beta, &prevs[*p])))
            .collect();
        chosen.sort_by(|x, y| x.4.cmp(&y.4));
        let median = &chosen[n / 2].4;
        let max = &chosen[n - 1].4;
        let nb = BigInt::from(n);
        // Σ h_pool = Σ(−corner)/Δ_r − Σ(−corner_face)/Δ_face.
        let pool = &sum_whole * &face_last - &sum_face * &last;
        let regions: Vec<String> = PAIR_REGIONS
            .iter()
            .enumerate()
            .map(|(r, name)| format!("{name}:{}", chosen.iter().filter(|c| c.1 == r).count()))
            .collect();
        println!(
            "LEVERAGE side={side} cells={n} ({}) bits_a_byte={} mean_h_over_training_mean={} median={} max={} face_part_mean={} pair_part_mean={} cells_with_an_open_part={open} open_rows(coordinate:rho)=[{}] elapsed_ms={}",
            regions.join(" "),
            per(code, n),
            thousandths_of(&(&sum_whole * &n_train), &(&unit_whole * &nb)),
            thousandths_of(&(median * &n_train), &unit_whole),
            thousandths_of(&(max * &n_train), &unit_whole),
            thousandths_of(&(&sum_face * &n_train), &(&unit_face * &nb)),
            thousandths_of(&(&pool * &n_train), &(&unit_whole * &face_last * &nb)),
            rows.join(" "),
            started.elapsed().as_millis()
        );
    }
    Ok(())
}

pub(super) fn region_line(regions: &[(i64, usize); 4]) -> String {
    named_region_line(&REGIONS, regions)
}

/// The regions' codes under their names.
pub(super) fn named_region_line(names: &[&str; 4], regions: &[(i64, usize); 4]) -> String {
    names
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
/// A signed code on `2^(−20)` bits written in bits.
/// A sum of `n` scales on `2^(−32)` read as their mean, to three places (none without a scale).
fn scale_mean(sum: u128, n: usize) -> String {
    if n == 0 {
        return "none".into();
    }
    let milli = (sum * 1000 + ((n as u128) << 31)) / ((n as u128) << 32);
    format!("{}.{:03}", milli / 1000, milli % 1000)
}

fn signed_bits(code: i64) -> String {
    format!("{}{}", if code < 0 { "-" } else { "" }, per(code.abs(), 1))
}

/// A section's closure readings ([`ClosureReading`]) added to the window's, one entry a level.
fn gather_closures(window: &mut Vec<(usize, usize, i64, i64)>, readings: &[ClosureReading]) {
    for r in readings {
        match window.iter_mut().find(|w| w.0 == r.level) {
            Some(w) => (w.1, w.2, w.3) = (w.1 + r.ticks, w.2 + r.code, w.3 + r.flat),
            None => window.push((r.level, r.ticks, r.code, r.flat)),
        }
    }
}

/// The window's closure per level: its ticks, the closure's code a tick and the flat menu's
/// `log₂ |M|` a tick, in bits; the heading is located where the code falls below the flat.
fn closure_line(window: &[(usize, usize, i64, i64)]) -> String {
    window
        .iter()
        .map(|&(level, ticks, code, flat)| format!("level={level} ticks={ticks} code_bits_a_tick={} flat_bits_a_tick={}", per(code, ticks.max(1)), per(flat, ticks.max(1))))
        .collect::<Vec<_>>()
        .join(" ")
}

pub(super) fn per(code: i64, n: usize) -> String {
    let milli = (code as i128 * 1000 + ((n as i128) << (READ_BITS - 1))) / ((n as i128) << READ_BITS);
    format!("{}.{:03}", milli / 1000, milli % 1000)
}

/// `train-tower` trains the ungated tower, `train-gated-tower` the gated one (its modes' decay keyed by
/// their input), `train-turned-tower` the turned one (its gated modes' turn keyed by their input too),
/// `train-pumped-tower` the pumped one (its turned modes pumped by their input, so a phase can lock),
/// and `train-credited-tower` the gated one whose streams carry their passage credit
/// (`hnn::tower::LevelCredit`), so a section's covector reaches the history its opening carries;
/// `train-pair-pumped-tower` the pumped one whose contacts are pair contacts
/// (`hnn::tower::ContactLaw::Pair`) and `train-pair-linear-pumped-tower` its foil, the pair contact
/// with its bilinear block held at zero. A continued learner must carry the same declaration.
pub(super) fn train(args: &[String], gated: bool, turned: bool, pumped: bool, credit: bool, contact: ContactLaw) -> Result<()> {
    train_looking_or_not(args, gated, turned, pumped, credit, contact, None)
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
    train_looking_or_not(&rest, gated, turned, pumped, false, ContactLaw::Rectifying, Some(&looking))
}

fn train_looking_or_not(args: &[String], gated: bool, turned: bool, pumped: bool, credit: bool, contact: ContactLaw, looking: Option<&Looking>) -> Result<()> {
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
        regions: REGIONS,
        train_compared: None,
    };
    fit(&args[7..], reading, gated, turned, pumped, credit, contact, TurnLadder::Fixed, None, Joined::Nothing, looking, &mut HostPass::default())
}

/// `train-unit-tower` trains the gated tower on founded units (`hnn::units`): the training and
/// held-out text are read in the units, and each code is reported over the bytes its units decode
/// to. `train-unit-pumped-tower` trains the pumped tower on the same units (each arriving unit
/// turns and reflects every mode, the Swing's three kinds keyed by the unit), and
/// `train-unit-pair-pumped-tower` the pumped tower whose contacts are pair contacts, which take the
/// product of two modes' phases (record `2026-10-26_THE_GENERATOR_IS_THE_MODULATOR_…`).
pub(super) fn train_units(args: &[String], turned: bool, pumped: bool, contact: ContactLaw, realization: &mut dyn PassRealization) -> Result<()> {
    if args.len() != 20 && args.len() != 22 {
        return Err("train-unit-tower|train-unit-pumped-tower|train-unit-pair-pumped-tower UNITS UNITS_SHA TRAIN TRAIN_SHA DEV DEV_SHA DEV_ROLES DEV_ROLES_SHA KEYS KEYS_SHA WIDTH MODES CONTACTS LEVELS STREAMS SECTION PASSES RATE_BITS OUT [FROM FROM_SHA]".into());
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
    let reading = Reading { train: train_classes, train_lengths, dev: dev_classes, dev_lengths, dev_roles, alphabet: units.len(), regions: REGIONS, train_compared: None };
    fit(&args[9..], reading, true, turned, pumped, false, contact, TurnLadder::Fixed, None, Joined::Nothing, None, realization)
}

/// A passage read in a tower's classes: the training and held-out classes, the bytes each class
/// decodes to, the held-out classes' regions and the regions' names.
pub(super) struct Reading {
    pub(super) train: Vec<usize>,
    pub(super) train_lengths: Vec<u32>,
    pub(super) dev: Vec<usize>,
    pub(super) dev_lengths: Vec<u32>,
    pub(super) dev_roles: Vec<u8>,
    pub(super) alphabet: usize,
    pub(super) regions: [&'static str; 4],
    /// The places of `train` whose arriving class each face is compared with
    /// (`TowerLearner::section_compared`); every place when `None`.
    pub(super) train_compared: Option<Vec<bool>>,
}

/// What a founded run joins before its first section: nothing, participation over its section
/// (one head a founded rung), the mutual contact at the comparison, or the passage (every level's
/// contacts reading the passing current).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Joined {
    Nothing,
    Participation,
    MutualContact,
    Passage,
    /// The passage with the packets ([`Tower::join_packets`]): each clocked level's push, gate and
    /// turn hear the packet its clock closed.
    PassagePackets,
    /// The passage and the packets with the heading ([`Tower::join_heading`]): each clocked level
    /// reads its modes through its own heading material before each arrival, and the heading meets
    /// the trace of the arrivals its next tick closes.
    PassagePacketsHeading,
    /// The pair contacts paired at the founding ([`TowerLearner::paired`]), each section founding
    /// their splits ([`TowerLearner::section_founding`]); the carried directions rest beside each
    /// learner (`PAIRED.<pass>`, `PAIRED`).
    Split,
    /// The pair contacts paired at the founding, every pair dormant throughout
    /// ([`TowerLearner::section_dormant`]): the copies deposit as one contact and nothing founds,
    /// the split race's control (the pair learner in the wider chart).
    DormantSplit,
}

/// [agent-inferred, October 29] The mutual contact's face scale `β = 2^(−2)`, the scale
/// participation's pairing uses, so a founded encoding's `2⟨y, E⟩` spans a few bits of face (record
/// `2026-10-29_MUTUAL_CONTACT_…`, §3).
pub(super) const MUTUAL_SHIFT: u32 = 2;

/// The passes: `args` are `KEYS KEYS_SHA WIDTH MODES CONTACTS LEVELS STREAMS SECTION PASSES RATE_BITS
/// OUT [FROM FROM_SHA [PAIRED PAIRED_SHA]]`, the paired directions named only when a founding split
/// run continues (`CONTACTS` is the field before its pairing). Each section's forward and reverse run through `realization`
/// (`hnn::tower::realization`; the host's own for every command but a card route's), which
/// returns the host's bits.
#[allow(clippy::too_many_arguments)]
pub(super) fn fit(args: &[String], reading: Reading, gated: bool, turned: bool, pumped: bool, credit: bool, contact: ContactLaw, ladder: TurnLadder, news: Option<NewsClock>, joined: Joined, looking: Option<&Looking>, realization: &mut dyn PassRealization) -> Result<()> {
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
        contact,
    };
    let streams = positive(&args[6])?;
    let section = count(&args[7])?;
    let passes = count(&args[8])?;
    let rate_bits: u32 = args[9].parse()?;
    let out = Path::new(&args[10]);
    let classes = &reading.train;
    let paired_run = matches!(joined, Joined::Split | Joined::DormantSplit);
    if paired_run && (looking.is_some() || contact != ContactLaw::Pair) {
        return Err("a split run trains the pair tower on its passage, without a look".into());
    }
    if joined == Joined::Split && !realization.forms_split() {
        return Err(format!("{} does not form the paired contacts' split read", realization.realization()).into());
    }
    if (joined == Joined::Split && args.len() == 13) || (joined != Joined::Split && args.len() > 13) {
        return Err("a founding split run continues with its learner and its paired directions; every other run with its learner alone".into());
    }
    if streams == 0 || section == 0 || classes.len() < streams * (section + 1) {
        return Err("the training text must hold one section a stream".into());
    }
    // A run that trains declares at least one pass: a learner saved after none would be read as
    // trained (Epime's review of October 27). A rested learner is read alone by the read commands.
    if passes == 0 {
        return Err("a training run declares at least one pass".into());
    }
    // A run continues a rested learner (its tower and moments) when one is named; its declaration
    // and rate must be the declared ones.
    // A paired run's learner carries the field widened by two.
    let carried = if paired_run { TowerDeclaration { contacts: declaration.contacts * 2, ..declaration } } else { declaration };
    let mut paired: Option<PairedContacts> = None;
    let mut learner = if args.len() >= 13 {
        let from = pinned_read(&args[11], &args[12], STATE_BUDGET)?;
        let learner = TowerLearner::from_text(std::str::from_utf8(&from)?).map_err(|e| e.to_string())?;
        if joined == Joined::Split {
            let text = pinned_read(&args[13], &args[14], STATE_BUDGET)?;
            let directions = PairedContacts::from_text(std::str::from_utf8(&text)?).map_err(|e| e.to_string())?;
            directions.admits(&learner.tower).map_err(|e| e.to_string())?;
            paired = Some(directions);
        }
        if learner.tower.declaration != carried || learner.rate_bits != rate_bits || learner.tower.news() != news {
            return Err("the continued learner's declaration, rate or news clock differs from the declared one".into());
        }
        if learner.tower.participation().map(|p| p.section) != (joined == Joined::Participation).then_some(section) {
            return Err("the continued learner's participation differs from the declared one".into());
        }
        if learner.tower.mutual_contact() != (joined == Joined::MutualContact).then_some(MUTUAL_SHIFT) {
            return Err("the continued learner's comparison differs from the declared one".into());
        }
        let packets = matches!(joined, Joined::PassagePackets | Joined::PassagePacketsHeading);
        if learner.tower.passage() != (packets || joined == Joined::Passage) || learner.tower.packets() != packets {
            return Err("the continued learner's passage or packets differ from the declared ones".into());
        }
        if learner.tower.heading() != (joined == Joined::PassagePacketsHeading) {
            return Err("the continued learner's heading differs from the declared one".into());
        }
        learner
    } else {
        let mut learner = TowerLearner::new(Tower::found_on(declaration, &keys, ladder).map_err(|e| e.to_string())?, rate_bits);
        // A clocked run's levels tick on their own news from the founding on ([`NewsClock`]).
        if let Some(clock) = news {
            learner.join_news(clock).map_err(|e| e.to_string())?;
        }
        // A participating run reads its sections' earlier sites from the founding on, one head a
        // founded rung ([`Tower::founded_participation`]).
        match joined {
            Joined::Nothing => {}
            Joined::Participation => {
                let founded = learner.tower.founded_participation(section).map_err(|e| e.to_string())?;
                println!("TOWER_PARTICIPATION section={} beta_shift={} heads={:?}", founded.section, founded.beta_shift, founded.heads);
                learner.join_participation(founded).map_err(|e| e.to_string())?;
            }
            // A mutual run compares each face with the target's own encoding through a learned
            // contact from the founding on ([`Tower::join_mutual_contact`]).
            Joined::MutualContact => {
                learner.join_mutual_contact(MUTUAL_SHIFT).map_err(|e| e.to_string())?;
                println!("TOWER_MUTUAL_CONTACT shift={MUTUAL_SHIFT}");
            }
            // A passage run's contacts read the passing current from the founding on, on the levels
            // its clock holds, its `W₁ˣ` at zero ([`Tower::join_passage`]).
            Joined::Passage => {
                learner.join_passage().map_err(|e| e.to_string())?;
                println!("TOWER_PASSAGE first_clocked_level={}", learner.tower.news().map_or(0, |c| c.first()));
            }
            // A packet run also gives each clocked level the packet its clock closed as the input
            // of its push, gate and turn ([`Tower::join_packets`]).
            Joined::PassagePackets => {
                learner.join_passage().map_err(|e| e.to_string())?;
                learner.join_packets().map_err(|e| e.to_string())?;
                println!("TOWER_PASSAGE first_clocked_level={} packets", learner.tower.news().map_or(0, |c| c.first()));
            }
            // A heading run also gives each clocked level its heading, `D` at zero, so it opens on
            // the packet run face for face ([`Tower::join_heading`]).
            Joined::PassagePacketsHeading => {
                learner.join_passage().map_err(|e| e.to_string())?;
                learner.join_packets().map_err(|e| e.to_string())?;
                learner.join_heading().map_err(|e| e.to_string())?;
                println!("TOWER_PASSAGE first_clocked_level={} packets heading", learner.tower.news().map_or(0, |c| c.first()));
            }
            // A split run widens the contact field by two at the founding, every pair dormant
            // ([`TowerLearner::paired`]); the founding run carries their directions.
            Joined::Split | Joined::DormantSplit => {
                let (widened, directions) = learner.paired().map_err(|e| e.to_string())?;
                learner = widened;
                println!("TOWER_PAIRED contacts={} dormant={} founding={}", learner.tower.declaration.contacts, directions.dormant(), joined == Joined::Split);
                if joined == Joined::Split {
                    paired = Some(directions);
                }
            }
        }
        learner
    };
    // The realization admits the whole law before any section is read or any output is written.
    realization.admit(&learner.tower).map_err(|e| e.to_string())?;
    println!("TOWER_REALIZATION {}", realization.realization());
    std::fs::create_dir(out)?;
    let chunk = classes.len() / streams;
    // [agent-inferred, October 30] A lap may be declared as the passage's first sections
    // (`TOWER_LAP_SECTIONS`): a partition of the pass whose time a smoke's deadline projects from
    // a measured rate, the learner resting and read after them as after a whole pass.
    let sections_a_pass = match std::env::var("TOWER_LAP_SECTIONS") {
        Ok(v) => v.parse::<usize>()?.clamp(1, (chunk - 1) / section),
        Err(_) => (chunk - 1) / section,
    };
    // [agent-inferred, October 30] A declared hold (`TOWER_HOLD`, `heading` and/or `descent`): the
    // heading's read `C^→` or its descent `D` read and never deposited, a foil that separates which
    // family's step the certificate refuses.
    if let Ok(words) = std::env::var("TOWER_HOLD") {
        let [heading, descent] = learner.tower.heading_families();
        if heading.is_empty() {
            return Err("TOWER_HOLD holds the heading's families, and this tower has no heading".into());
        }
        for word in words.split(',') {
            match word {
                "heading" => learner.held.extend(heading.iter().cloned()),
                "descent" => learner.held.extend(descent.iter().cloned()),
                _ => return Err(format!("TOWER_HOLD names heading or descent, not {word}").into()),
            }
        }
        println!("TOWER_HOLD {words} entries={}", learner.held.iter().map(|r| r.len()).sum::<usize>());
    }
    // [agent-inferred, October 30] A declared reading (`TOWER_REFUSAL_PARTS=1`): each refused step
    // read again under each of its five parts alone, the descent, the heading's read, the
    // readout, the clocked levels and the rest (the record's §13); it costs five forwards a
    // refusal and moves nothing.
    if std::env::var("TOWER_REFUSAL_PARTS").is_ok_and(|v| v == "1") {
        if learner.tower.heading_families()[0].is_empty() {
            return Err("TOWER_REFUSAL_PARTS reads the heading's parts, and this tower has no heading".into());
        }
        learner.refusal_parts = true;
        println!("TOWER_REFUSAL_PARTS declared");
    }
    // [agent-inferred, October 30] A declared reading (`TOWER_REFUSAL_TICKS=1`): each refused step
    // read again whole, its clocked levels ticking where the section's opening read ticked (the
    // record's §16); it costs one forward a refusal and moves nothing.
    if std::env::var("TOWER_REFUSAL_TICKS").is_ok_and(|v| v == "1") {
        if learner.tower.news().is_none() {
            return Err("TOWER_REFUSAL_TICKS reads the clocked levels' ticks, and this tower has no news clock".into());
        }
        learner.refusal_ticks = true;
        println!("TOWER_REFUSAL_TICKS declared");
    }
    // [agent-inferred, October 30] The meeting form's law (`TOWER_MEETING=1`, the record's §17):
    // a refused step's five parts read once through the receiving face's metric at the halving the
    // section first refused, their scales solved on the box, and each trial accepted only when the
    // arrivals' faces fall and the change is at least a quarter of the model's. It costs six logits
    // reads a refused section and a reread a trial.
    if std::env::var("TOWER_MEETING").is_ok_and(|v| v == "1") {
        if learner.tower.heading_families()[0].is_empty() {
            return Err("TOWER_MEETING reads the heading's parts, and this tower has no heading".into());
        }
        learner.meeting = true;
        println!("TOWER_MEETING declared");
    }
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
        // Under the heading, each clocked level's closure over the window: ticks, code, flat.
        let mut closures: Vec<(usize, usize, i64, i64)> = Vec::new();
        // The window's refused steps: how many, how many raised the arrivals' code and how many
        // the closure's, and the changes they made.
        let mut refusals = (0usize, 0usize, 0usize, 0i64, 0i64);
        let mut refusal_parts = ([0usize; 5], [0i64; 5]);
        // The window's refused steps read on the opening's ticks: how many rose on their own ticks
        // and on the opening's, and the changes on each.
        let mut refusal_ticks = (0usize, 0usize, 0i64, 0i64);
        // The window's meeting forms: the forms read, the trials solved, the trials read again,
        // the accepted ones, the model's and the actual change over the trials read, and each
        // part's scale summed over the accepted trials.
        let mut meetings = (0usize, 0usize, 0usize, 0usize, 0i64, 0i64, [0u128; 5]);
        let mut sections_run = sections_a_pass;
        let (mut proposed, mut admitted) = (0usize, vec![0usize; learner.tower.declaration.levels]);
        if let Some(look) = looking {
            let mut lookers: Vec<Looker> = look_keys.drain(..).enumerate().map(|(s, keys)| Looker::new(s * chunk, (s + 1) * chunk, keys)).collect();
            let mut k = 0usize;
            // Over the pass's deposits: the plain streams' code change and the forks', and the
            // deposits under which the plain streams' code rose while the whole code fell.
            let (mut plain_change, mut fork_change, mut plain_rose) = (0i64, 0i64, 0usize);
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
                // The streams' plain parts, then the forks their moments opened in the section,
                // each from its own state; the forks' states end with the section.
                let forks: Vec<Fork> = lookers.iter_mut().flat_map(|l| l.forks.drain(..)).collect();
                let mut parts: Vec<&[usize]> = lookers.iter().map(|l| &l.built[..=section]).collect();
                parts.extend(forks.iter().map(|f| f.classes.as_slice()));
                let plain: Vec<Vec<Option<usize>>> = lookers.iter().map(|l| l.built[..=section].iter().map(|&c| Some(c)).collect()).collect();
                let mut compared: Vec<&[Option<usize>]> = plain.iter().map(|c| c.as_slice()).collect();
                compared.extend(forks.iter().map(|f| f.compared.as_slice()));
                states.extend(forks.iter().map(|f| f.opening.clone()));
                let result = learner.section_realized(&mut states, &parts, Some(&compared), realization);
                states.truncate(streams);
                let receipt = match result {
                    Ok(receipt) => receipt,
                    Err(e) => {
                        println!("TOWER_SWELL pass={} section={} {}", pass, k + 1, learner.swell_line());
                        return Err(e.to_string().into());
                    }
                };
                if receipt.deposited {
                    let change = |parts: &[(i64, i64)]| parts.iter().map(|&(before, after)| after - before).sum::<i64>();
                    let plain = change(&receipt.parts[..streams]);
                    plain_change += plain;
                    fork_change += change(&receipt.parts[streams..]);
                    plain_rose += (plain > 0) as usize;
                }
                // Each compared place after a part's first is one byte coded.
                let coded: usize = compared.iter().map(|c| c[1..].iter().filter(|x| x.is_some()).count()).sum();
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
            let (looks, right, read) = lookers.iter().fold((0usize, 0usize, 0usize), |a, l| (a.0 + l.looks, a.1 + l.right, a.2 + l.at - l.start));
            println!(
                "TOWER_LOOKS pass={} sections={} looks={} right={} text_read={} of {} keys_left={}",
                pass, k, looks, right, read, streams * chunk, lookers.iter().map(|l| l.keys_left()).min().unwrap_or(0)
            );
            println!(
                "TOWER_PARTS pass={} deposits={} plain_rose={} plain_change_bits={} fork_change_bits={}",
                pass, deposits, plain_rose, signed_bits(plain_change), signed_bits(fork_change)
            );
            look_keys = lookers.into_iter().map(|l| l.keys).collect();
            sections_run = k;
        }
        for k in 0..if looking.is_some() { 0 } else { sections_a_pass } {
            let ranges: Vec<std::ops::Range<usize>> =
                (0..streams).map(|s| s * chunk + k * section..s * chunk + (k + 1) * section + 1).collect();
            let parts: Vec<&[usize]> = ranges.iter().map(|r| &classes[r.clone()]).collect();
            let compared: Option<Vec<Vec<Option<usize>>>> =
                reading.train_compared.as_ref().map(|mask| ranges.iter().map(|r| r.clone().map(|i| mask[i].then_some(classes[i])).collect()).collect());
            let slices: Option<Vec<&[Option<usize>]>> = compared.as_ref().map(|c| c.iter().map(|v| v.as_slice()).collect());
            let result = match paired.as_mut() {
                Some(directions) => learner.section_founding(&mut states, &parts, slices.as_deref(), realization, directions).map(|(receipt, founding)| {
                    proposed += usize::from(founding.proposed.is_some());
                    // A founding proposed on the section before, certified on this one: its
                    // predicted change on the section it was read on, the same test's on this
                    // one (`refused` where it did not pass with the proposal's sign), whether its
                    // pair opened, the pairs founded, and how far they have learned apart (the
                    // largest difference between a founded pair's drive copies, on `2^(−24)`).
                    if let Some(f) = &founding.certified {
                        if founding.admitted {
                            admitted[f.level] += 1;
                        }
                        let confirmed = founding.confirmed.as_ref().map_or_else(|| "refused".to_string(), |c| signed_bits(c.predicted));
                        let parting = directions.parting(&learner.tower).map_or_else(|e| format!("{e:?}"), |p| p.to_string());
                        println!(
                            "TOWER_FOUNDING pass={} section={} level={} pair={} predicted_bits={} confirmed_bits={confirmed} admitted={} dormant={} founded={} parting={}",
                            pass, k + 1, f.level, f.pair, signed_bits(f.predicted), founding.admitted, founding.dormant, directions.founded.len(), parting
                        );
                    }
                    receipt
                }),
                None if joined == Joined::DormantSplit => learner.section_dormant(&mut states, &parts, slices.as_deref(), realization),
                None => learner.section_realized(&mut states, &parts, slices.as_deref(), realization),
            };
            let receipt = match result {
                Ok(receipt) => receipt,
                Err(e) => {
                    println!("TOWER_SWELL pass={} section={} {}", pass, k + 1, learner.swell_line());
                    return Err(e.to_string().into());
                }
            };
            // The section codes every compared class of a part after its first.
            let coded: usize = ranges
                .iter()
                .map(|r| (r.start + 1..r.end).filter(|&i| reading.train_compared.as_ref().is_none_or(|m| m[i])).map(|i| reading.train_lengths[i] as usize).sum::<usize>())
                .sum();
            code += receipt.code_before;
            bytes += coded;
            window.0 += receipt.code_before;
            window.1 += coded;
            deposits += receipt.deposited as usize;
            halvings += receipt.halvings;
            gather_closures(&mut closures, &receipt.closure);
            for &(arrivals, closure) in &receipt.refused {
                refusals = (refusals.0 + 1, refusals.1 + usize::from(arrivals > 0), refusals.2 + usize::from(closure > 0), refusals.3 + arrivals, refusals.4 + closure);
            }
            for (&(own, _), &opening) in receipt.refused.iter().zip(&receipt.refused_on_ticks) {
                refusal_ticks = (refusal_ticks.0 + usize::from(own > 0), refusal_ticks.1 + usize::from(opening > 0), refusal_ticks.2 + own, refusal_ticks.3 + opening);
            }
            for parts in &receipt.refused_parts {
                for (n, &change) in parts.iter().enumerate() {
                    refusal_parts.0[n] += usize::from(change > 0);
                    refusal_parts.1[n] += change;
                }
            }
            meetings.0 += usize::from(!receipt.meeting.is_empty());
            for trial in &receipt.meeting {
                meetings.1 += 1;
                if let Some(change) = trial.change {
                    meetings.2 += 1;
                    meetings.4 += trial.model;
                    meetings.5 += change;
                }
                if trial.accepted {
                    meetings.3 += 1;
                    for (sum, &scale) in meetings.6.iter_mut().zip(&trial.scales) {
                        *sum += u128::from(scale);
                    }
                }
            }
            if (k + 1) % 32 == 0 || k + 1 == sections_a_pass {
                println!(
                    "TOWER_SECTION pass={} section={} bits_a_byte={} deposits={} halvings={} elapsed_ms={}",
                    pass, k + 1, per(window.0, window.1), deposits, halvings, started.elapsed().as_millis()
                );
                if !closures.is_empty() {
                    println!("TOWER_CLOSURE pass={} section={} {}", pass, k + 1, closure_line(&closures));
                }
                println!(
                    "TOWER_REFUSALS pass={} section={} refused={} arrivals_rose={} closure_rose={} arrivals_change_bits={} closure_change_bits={}",
                    pass, k + 1, refusals.0, refusals.1, refusals.2, signed_bits(refusals.3), signed_bits(refusals.4)
                );
                if learner.refusal_parts {
                    let (rose, change) = refusal_parts;
                    println!(
                        "TOWER_REFUSAL_PARTS pass={} section={} rose descent={} read={} readout={} clocked={} rest={} change_bits descent={} read={} readout={} clocked={} rest={}",
                        pass,
                        k + 1,
                        rose[0],
                        rose[1],
                        rose[2],
                        rose[3],
                        rose[4],
                        signed_bits(change[0]),
                        signed_bits(change[1]),
                        signed_bits(change[2]),
                        signed_bits(change[3]),
                        signed_bits(change[4])
                    );
                    refusal_parts = ([0; 5], [0; 5]);
                }
                if learner.refusal_ticks {
                    let (own, opening, own_change, opening_change) = refusal_ticks;
                    println!(
                        "TOWER_REFUSAL_TICKS pass={} section={} refused={} rose_on_own_ticks={} rose_on_opening_ticks={} change_bits own={} opening={}",
                        pass,
                        k + 1,
                        refusals.0,
                        own,
                        opening,
                        signed_bits(own_change),
                        signed_bits(opening_change)
                    );
                    refusal_ticks = (0, 0, 0, 0);
                }
                if learner.meeting {
                    let (forms, trials, read, accepted, model, change, scales) = meetings;
                    let mean = |sum: u128| scale_mean(sum, accepted);
                    println!(
                        "TOWER_MEETING pass={} section={} forms={} trials={} read={} accepted={} model_bits={} change_bits={} scales descent={} read={} readout={} clocked={} rest={}",
                        pass,
                        k + 1,
                        forms,
                        trials,
                        read,
                        accepted,
                        signed_bits(model),
                        signed_bits(change),
                        mean(scales[0]),
                        mean(scales[1]),
                        mean(scales[2]),
                        mean(scales[3]),
                        mean(scales[4])
                    );
                    meetings = (0, 0, 0, 0, 0, 0, [0; 5]);
                }
                refusals = (0, 0, 0, 0, 0);
                println!("TOWER_SWELL pass={} section={} {}", pass, k + 1, learner.swell_line());
                window = (0, 0);
                closures.clear();
            }
        }
        // Each pass's learner rests beside the run before the held-out read, so a run stopped at
        // its deadline or refused in the read keeps its last trained pass.
        println!("TOWER_REALIZATION pass={pass} {}", realization.realization());
        let text = learner.to_text();
        let name = format!("STATE.{pass}");
        write_new(&out.join(&name), text.as_bytes())?;
        println!("TOWER_STATE {name} state_bytes={} state_sha256={}", text.len(), sha256(text.as_bytes())?);
        // A founding proposed on the pass's last section is released before the directions rest, so
        // a run continued from them is the run that went on.
        if let Some(f) = paired.as_mut().and_then(|d| d.pending.take()) {
            println!("TOWER_FOUNDING_RELEASED pass={pass} level={} pair={} predicted_bits={}", f.level, f.pair, signed_bits(f.predicted));
        }
        if let Some(directions) = &paired {
            let text = directions.to_text();
            let name = format!("PAIRED.{pass}");
            write_new(&out.join(&name), text.as_bytes())?;
            println!("TOWER_PAIRED {name} paired_bytes={} paired_sha256={} proposed={proposed} admitted={admitted:?} dormant={}", text.len(), sha256(text.as_bytes())?, directions.dormant());
        }
        let regions = held_out(&learner.tower, &reading.dev, &reading.dev_lengths, &reading.dev_roles, streams, section, realization)?;
        let (dev_code, dev_coded) = regions.iter().fold((0i64, 0usize), |a, r| (a.0 + r.0, a.1 + r.1));
        println!(
            "TOWER_PASS pass={} train_bits_a_byte={} dev_bits_a_byte={} dev_regions {} deposits={}/{} pass_ms={} elapsed_ms={} train_code={code} dev_code={dev_code} grain_bits={READ_BITS}",
            pass, per(code, bytes), per(dev_code, dev_coded), named_region_line(&reading.regions, &regions), deposits, sections_run,
            pass_started.elapsed().as_millis(), started.elapsed().as_millis()
        );
    }
    let text = learner.to_text();
    write_new(&out.join("STATE"), text.as_bytes())?;
    if let Some(directions) = &paired {
        let text = directions.to_text();
        write_new(&out.join("PAIRED"), text.as_bytes())?;
        println!("TOWER_PAIRED PAIRED paired_bytes={} paired_sha256={}", text.len(), sha256(text.as_bytes())?);
    }
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

/// The problems of a held text: each a question line and its answer lines, the problems separated
/// by a blank line (the text as `tools/gsm8k` frames it). Each problem keeps its last line end.
fn problems_of(text: &[u8]) -> Vec<&[u8]> {
    let mut problems = Vec::new();
    let (mut start, mut i) = (0, 0);
    while i + 1 < text.len() {
        if text[i] == b'\n' && text[i + 1] == b'\n' {
            if i > start {
                problems.push(&text[start..=i]);
            }
            start = i + 2;
            i += 2;
        } else {
            i += 1;
        }
    }
    if text[start.min(text.len())..].iter().any(|&b| b != b'\n') {
        problems.push(&text[start..]);
    }
    problems
}

/// Where an answer writes a calculation: for each `<<` with an `=` before its `>>`, the
/// expression between them and the offset just past the `=`.
fn calculations_of(answer: &[u8]) -> Vec<(&[u8], usize)> {
    let mut found = Vec::new();
    let mut i = 0;
    while i + 1 < answer.len() {
        if answer[i] == b'<' && answer[i + 1] == b'<' {
            let close = answer[i + 2..].windows(2).position(|w| w == b">>").map_or(answer.len(), |p| i + 2 + p);
            if let Some(eq) = answer[i + 2..close].iter().position(|&b| b == b'=') {
                found.push((&answer[i + 2..i + 2 + eq], i + 3 + eq));
            }
            i = close;
        } else {
            i += 1;
        }
    }
    found
}

/// A fork of the rested tower receives `prompt` read in the units and releases units by `agree`
/// exact agreeing draws, each moved through, until `stop` holds of its bytes, `bytes` bytes are
/// released or `cap` units are. Returns the released bytes, the prompt's units, the units released,
/// the bytes of the withheld tail, whether the tail's last draw ran past it and the tail's units
/// placed without a draw (none agreeing held mass).
///
/// [definition; agent-inferred, October 27] **The read meets the units** (`heal`; the review
/// record §2). A prompt cut at a byte the passage does not end a unit at (an `=` the founded units
/// join to the digit after it, `=3`) ends in a unit the tower never met there. Healed, the fork
/// receives the prompt without its last unit and releases with that unit's bytes as the release's
/// opening: while the tail is unspent only units whose bytes agree with it are drawn (the face
/// restricted to them, the tower's own conditional given the bytes it was shown), and a unit that
/// runs past the tail (`=3`) writes the rest. The returned release is what follows the tail. The
/// units stay as founded; only the check's cut moves to a boundary of the machine's own reading.
#[allow(clippy::too_many_arguments)]
fn written_release(tower: &Tower, units: &Units, prompt: &[u8], keys: &mut KeyStream, agree: u32, bytes: usize, cap: usize, stop: fn(&[u8]) -> bool, heal: bool) -> std::result::Result<(Vec<u8>, [usize; 5]), String> {
    let mut classes = units.parse(prompt).map_err(|e| e.to_string())?;
    let tail: Vec<u8> = match heal {
        true => units.piece(classes.pop().ok_or("an empty prompt")? as usize).to_vec(),
        false => Vec::new(),
    };
    let mut state = tower.rest();
    let mut face = None;
    for &c in &classes {
        face = Some(tower.advance(&mut state, c as usize).map_err(|e| e.to_string())?);
    }
    let mut face = face.ok_or("an empty prompt")?;
    let (mut released, mut drawn, mut past, mut placed) = (Vec::new(), 0, false, 0);
    while released.len() < bytes.saturating_add(tail.len()) && drawn < cap {
        let key = keys.next_key().ok_or("fewer keys than a problem's window draws")?;
        let class = if released.len() < tail.len() {
            // The units whose bytes agree with the unspent tail: a prefix of it, or running past it.
            let rest = &tail[released.len()..];
            let agreeing: Vec<u128> = face
                .masses
                .iter()
                .enumerate()
                .map(|(u, &m)| {
                    let piece = units.piece(u);
                    if rest.starts_with(piece) || piece.starts_with(rest) { m } else { 0 }
                })
                .collect();
            let class = match agreeing.iter().any(|&m| m > 0) {
                true => agreeing_class(&agreeing, agree, &key).map_err(|e| e.to_string())?,
                // No agreeing unit holds mass at the face's grain: the shown bytes are placed as
                // the units parse them.
                false => {
                    placed += 1;
                    units.parse(rest).map_err(|e| e.to_string())?[0] as usize
                }
            };
            past = units.piece(class).len() > rest.len();
            class
        } else {
            agreeing_class(&face.masses, agree, &key).map_err(|e| e.to_string())?
        };
        released.extend_from_slice(units.piece(class));
        drawn += 1;
        let after = &released[tail.len().min(released.len())..];
        if released.len() >= tail.len() && (stop(after) || after.len() >= bytes) || drawn == cap {
            break;
        }
        face = tower.advance(&mut state, class).map_err(|e| e.to_string())?;
    }
    let after = released.get(tail.len()..).unwrap_or_default().to_vec();
    Ok((after, [classes.len(), drawn, tail.len(), usize::from(past), placed]))
}

/// `read-unit-tower-written UNITS UNITS_SHA STATE STATE_SHA HELD HELD_SHA KEYS KEYS_SHA BYTES
/// AGREE MARK_AGREE MARK_CAP OUT`: every held-out problem read by the rested tower, for the written
/// rules of the record
/// `2026-10-26_THE_HELD_OUT_PROBLEMS_ARE_READ_BY_WRITTEN_RULES_AND_THE_MARKUP_IS_WRITTEN_AT_ITS_EQUALS`.
/// For each problem a fork receives the framed question (a blank line, the question, its line
/// end) and releases `BYTES` bytes at `AGREE` agreeing draws (`FREE.tsv`: the problem's index and
/// the release). At every calculation the answer writes, `<<expression=`, a fork receives the
/// framed question and the answer through that `=`, healed ([`written_release`]: the prompt's last
/// unit is withheld and the release opens with its bytes, so the cut falls where the units read),
/// and releases units at `MARK_AGREE` agreeing draws until its bytes past the `=` hold `>>` or a
/// line end, or `MARK_CAP` units are released, the tail's among them (`MARKS.tsv`:
/// the problem's index, the calculation's, the expression and the release; `CUTS.tsv`: the
/// problem's index, the calculation's, and 1 where the whole problem read in the units ends a unit
/// at that `=`, else 0). Every fork opens at
/// rest, so each problem and each calculation is read alone, as the John prompt is. Problem `i`
/// draws from its own window of the key file, `BYTES + MARK_CAP · (the most calculations a problem
/// writes)` eight-byte keys: the free release from the window's start, the calculations after its
/// first `BYTES`. The fields are escaped as [`field`] writes them. Nothing here grades: the rules
/// are read outside the machine (`tools/gsm8k/written_rules.py`).
pub(super) fn read_unit_written(args: &[String]) -> Result<()> {
    if args.len() != 14 {
        return Err("read-unit-tower-written UNITS UNITS_SHA STATE STATE_SHA HELD HELD_SHA KEYS KEYS_SHA BYTES AGREE MARK_AGREE MARK_CAP OUT".into());
    }
    let started = Instant::now();
    let units = Units::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], READ_BUDGET as usize)?)?).map_err(|e| e.to_string())?;
    let learner = TowerLearner::from_text(std::str::from_utf8(&pinned_read(&args[3], &args[4], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let held = pinned_read(&args[5], &args[6], READ_BUDGET as usize)?;
    let keys = pinned_read(&args[7], &args[8], READ_BUDGET as usize)?;
    let bytes = positive(&args[9])?;
    let agree = agreement(Some(&args[10]))?;
    let mark_agree = agreement(Some(&args[11]))?;
    let mark_cap = positive(&args[12])?;
    let out = Path::new(&args[13]);
    let problems = problems_of(&held);
    let split = |p: &[u8]| -> (Vec<u8>, Vec<u8>) {
        let line = p.iter().position(|&b| b == b'\n').unwrap_or(p.len());
        (p[..line].to_vec(), p[(line + 1).min(p.len())..].to_vec())
    };
    let most = problems.iter().map(|p| calculations_of(&split(p).1).len()).max().ok_or("a held text without problems")?;
    let window = bytes + mark_cap * most;
    if keys.len() < problems.len() * window * 8 {
        return Err(format!("fewer eight-byte keys ({}) than the problems' windows ({} x {window})", keys.len() / 8, problems.len()).into());
    }
    std::fs::create_dir(out)?;
    println!("TOWER_WRITTEN_OPEN problems={} most_calculations={most} window={window} elapsed_ms={}", problems.len(), started.elapsed().as_millis());
    let tower = &learner.tower;
    let done = std::sync::atomic::AtomicUsize::new(0);
    type Read = (Vec<u8>, Vec<(Vec<u8>, Vec<u8>, bool)>, [usize; 5]);
    let reads: Vec<Read> = problems
        .par_iter()
        .enumerate()
        .map(|(i, p)| -> std::result::Result<Read, String> {
            let (question, answer) = split(p);
            let at = i * window * 8;
            let mut framed = b"\n\n".to_vec();
            framed.extend_from_slice(&question);
            framed.push(b'\n');
            let mut free_keys = KeyStream::new(keys[at..at + bytes * 8].to_vec(), 8).map_err(|e| e.to_string())?;
            let (free, [mut prompts, mut drawn, _, _, _]) = written_release(tower, &units, &framed, &mut free_keys, agree, bytes, usize::MAX, |_| false, false)?;
            let (mut wide, mut past, mut placed) = (0usize, 0usize, 0usize);
            let mut mark_keys = KeyStream::new(keys[at + bytes * 8..at + window * 8].to_vec(), 8).map_err(|e| e.to_string())?;
            // Where the problem's own reading in the units ends a unit: the whole problem parsed
            // as the training text frames it.
            let mut whole = framed.clone();
            whole.extend_from_slice(&answer);
            let mut ends = std::collections::BTreeSet::new();
            let mut end = 0;
            for u in units.parse(&whole).map_err(|e| e.to_string())? {
                end += units.piece(u as usize).len();
                ends.insert(end);
            }
            let mut marks = Vec::new();
            for (expression, through) in calculations_of(&answer) {
                let mut prompt = framed.clone();
                prompt.extend_from_slice(&answer[..through]);
                let stop: fn(&[u8]) -> bool = |r| r.windows(2).any(|w| w == b">>") || r.contains(&b'\n');
                let (release, [p, d, tail, ran, put]) = written_release(tower, &units, &prompt, &mut mark_keys, mark_agree, usize::MAX, mark_cap, stop, true)?;
                prompts += p;
                drawn += d;
                wide += usize::from(tail > 1);
                past += ran;
                placed += put;
                marks.push((expression.to_vec(), release, ends.contains(&(framed.len() + through))));
            }
            let n = done.fetch_add(1, std::sync::atomic::Ordering::Relaxed) + 1;
            if n % 64 == 0 {
                println!("TOWER_WRITTEN_PROGRESS problems={n} elapsed_ms={}", started.elapsed().as_millis());
            }
            Ok((free, marks, [prompts, drawn, wide, past, placed]))
        })
        .collect::<std::result::Result<_, String>>()?;
    let mut free_tsv = String::new();
    let mut marks_tsv = String::new();
    let mut cuts_tsv = String::new();
    let mut bounded = 0;
    let (mut marks, mut prompts, mut drawn, mut most_moved, mut released, mut wide, mut past, mut placed) = (0, 0, 0, 0, 0, 0, 0, 0);
    for (i, (free, calcs, [p, d, w, r, q])) in reads.iter().enumerate() {
        free_tsv.push_str(&format!("{i}\t{}\n", field(free)));
        released += free.len();
        for (j, (expression, release, at_end)) in calcs.iter().enumerate() {
            marks_tsv.push_str(&format!("{i}\t{j}\t{}\t{}\n", field(expression), field(release)));
            cuts_tsv.push_str(&format!("{i}\t{j}\t{}\n", u8::from(*at_end)));
            bounded += usize::from(*at_end);
        }
        marks += calcs.len();
        prompts += p;
        drawn += d;
        wide += w;
        past += r;
        placed += q;
        most_moved = most_moved.max(p + d);
    }
    write_new(&out.join("FREE.tsv"), free_tsv.as_bytes())?;
    write_new(&out.join("MARKS.tsv"), marks_tsv.as_bytes())?;
    write_new(&out.join("CUTS.tsv"), cuts_tsv.as_bytes())?;
    println!(
        "TOWER_WRITTEN problems={} calculations={marks} free_bytes={released} prompt_units={prompts} released_units={drawn} most_units_a_problem={most_moved} agree={agree} mark_agree={mark_agree} mark_cap={mark_cap} elapsed_ms={}",
        reads.len(), started.elapsed().as_millis()
    );
    // The healed cut: marks whose `=` the problem's own reading ends a unit at, marks whose
    // withheld unit held more than the `=` (an operand's digit joined to it), marks whose release
    // opened with a unit running past the tail (`=3`), and tail units placed without a draw.
    println!("TOWER_WRITTEN_HEALED calculations={marks} bounded_at_equals={bounded} tail_wider_than_equals={wide} opened_past_tail={past} tail_units_placed={placed}");
    println!(
        "TOWER_WRITTEN_FILES free_sha256={} marks_sha256={} cuts_sha256={}",
        sha256(free_tsv.as_bytes())?,
        sha256(marks_tsv.as_bytes())?,
        sha256(cuts_tsv.as_bytes())?
    );
    Ok(())
}

/// `read-unit-tower-at UNITS UNITS_SHA STATE STATE_SHA TEXT TEXT_SHA PLACES PLACES_SHA OUT`: the
/// rested tower's carried modes at places an observer names in a run of problems. Each problem of
/// `TEXT` is read alone from rest in the founded `UNITS`, framed as `read-unit-tower-written` frames
/// it (a blank line, the question, its line end), followed by its true answer. `PLACES` holds one
/// place a line, the problem's index and a byte of its framed text, tab-separated, each problem's
/// bytes increasing. After the unit that holds a place's byte steps, `OUT` (create-new) receives,
/// little-endian, the place's line in `PLACES` (`u32`) and every level's carried modes (`levels` ×
/// `modes` × (re, im) `i64`, the state's own grain): the record `read-tower-classes-at` writes, with
/// no top face. An exterior reading of what the frozen tower holds where an observer looks
/// (`tools/gsm8k/numeral_rings.py`); nothing in it enters the tower.
pub(super) fn read_unit_at(args: &[String]) -> Result<()> {
    if args.len() != 10 {
        return Err("read-unit-tower-at UNITS UNITS_SHA STATE STATE_SHA TEXT TEXT_SHA PLACES PLACES_SHA OUT".into());
    }
    let started = Instant::now();
    let units = Units::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], READ_BUDGET as usize)?)?).map_err(|e| e.to_string())?;
    let learner = TowerLearner::from_text(std::str::from_utf8(&pinned_read(&args[3], &args[4], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let text = pinned_read(&args[5], &args[6], READ_BUDGET as usize)?;
    let named = pinned_read(&args[7], &args[8], READ_BUDGET as usize)?;
    let out = Path::new(&args[9]);
    if out.exists() {
        return Err("OUT exists: the cells are written create-new".into());
    }
    let problems = problems_of(&text);
    let mut places: Vec<Vec<(u32, usize)>> = vec![Vec::new(); problems.len()];
    for (line, place) in std::str::from_utf8(&named)?.lines().enumerate() {
        let (problem, byte) = match place.split('\t').collect::<Vec<_>>()[..] {
            [p, b] => (count(p)?, count(b)?),
            _ => return Err("a place is a problem and a byte, tab-separated".into()),
        };
        let list = places.get_mut(problem).ok_or("a place names no problem of the text")?;
        if list.last().is_some_and(|&(_, last)| last >= byte) {
            return Err("a problem's places are not increasing".into());
        }
        list.push((u32::try_from(line)?, byte));
    }
    let tower = &learner.tower;
    let records: Vec<Vec<u8>> = problems
        .par_iter()
        .zip(&places)
        .map(|(p, places)| -> std::result::Result<Vec<u8>, String> {
            let mut records = Vec::new();
            if places.is_empty() {
                return Ok(records);
            }
            let line = p.iter().position(|&b| b == b'\n').unwrap_or(p.len());
            let mut framed = b"\n\n".to_vec();
            framed.extend_from_slice(&p[..line]);
            framed.push(b'\n');
            framed.extend_from_slice(&p[(line + 1).min(p.len())..]);
            let mut state = tower.rest();
            let (mut end, mut next) = (0usize, 0usize);
            for c in units.parse(&framed).map_err(|e| e.to_string())? {
                tower.advance(&mut state, c as usize).map_err(|e| e.to_string())?;
                end += units.piece(c as usize).len();
                while next < places.len() && places[next].1 < end {
                    records.extend(places[next].0.to_le_bytes());
                    state.modes.iter().flatten().for_each(|&(re, im)| {
                        records.extend(re.to_le_bytes());
                        records.extend(im.to_le_bytes());
                    });
                    next += 1;
                }
            }
            if next < places.len() {
                return Err("a place lies past its problem's framed text".into());
            }
            Ok(records)
        })
        .collect::<std::result::Result<_, String>>()?;
    let written: Vec<u8> = records.concat();
    write_new(out, &written)?;
    println!(
        "UNIT_AT problems={} places={} levels={} modes={} bytes={} sha256={} elapsed_ms={}",
        problems.len(),
        places.iter().map(Vec::len).sum::<usize>(),
        learner.tower.declaration.levels,
        learner.tower.declaration.modes,
        written.len(),
        sha256(&written)?,
        started.elapsed().as_millis()
    );
    Ok(())
}

/// A text field of `LINES.tsv` or `LOOKS.tsv`: the bytes escaped (`read_lines`).
fn field(bytes: &[u8]) -> String {
    bytes.iter().map(|&b| if b == b'|' { "\\x7c".to_string() } else { b.escape_ascii().to_string() }).collect()
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
/// on `2^(−20)` bits: the frustration's floor and how fast the looks approach it; then each look's
/// lock with the true rest, `λ` and `F*` joined by `|`, the micro-control's success reading: `λ`
/// grows or holds and `F*` falls or holds at 0 from look to look).
/// `read-lines-carried` looks as `read-lines-again` does, and its stream carries each written
/// line's first look, line end and head again before the true rest, the passage a tower trained
/// with the look (`Looking`) met: its codes are read where that tower was taught.
/// `read-lines-own` lets the tower decide: after each look and its line's end the fork writes on,
/// and it looks again only where it writes its line's head again, at most `LOOKS` looks. Its
/// stream is the plain text, the passage a tower trained with the look (`Looking`) read.
///
/// Every text field of both files (head, rest, looks) is its bytes escaped as Rust's
/// `escape_ascii` writes them, with `|` written `\x7c`, so a field holds no tab or `|` and reads
/// back to its exact bytes (Python's `codecs.escape_decode`). A look is the tower's bytes, which
/// need not be UTF-8.
pub(super) fn read_lines(args: &[String], in_stream: bool, look: Look) -> Result<()> {
    let arity = if look == Look::Once { 10 } else { 11 };
    if args.len() != arity {
        return Err("read-lines|read-lines-stream STATE STATE_SHA TEXT TEXT_SHA KEYS KEYS_SHA WRITTEN AGREE OUT; read-lines-again|read-lines-redraw|read-lines-carried|read-lines-own STATE STATE_SHA TEXT TEXT_SHA KEYS KEYS_SHA WRITTEN AGREE LOOKS OUT".into());
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
    let moments: Vec<Option<usize>> = text.split(|&b| b == b'\n').filter(|l| !l.is_empty()).map(|l| l.iter().position(|&b| b == b'=')).collect();
    for (i, line) in text.split(|&b| b == b'\n').filter(|l| !l.is_empty()).enumerate() {
        let Some(eq) = moments[i] else {
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
        let mut looked: Vec<Vec<u8>> = Vec::new();
        let mut costs: Vec<i64> = Vec::new();
        let mut first_look: Vec<usize> = Vec::new();
        let mut locks: Vec<(usize, usize)> = Vec::new();
        if i < written {
            let cap = rest.len() + 4;
            let mut fork = modes.clone();
            let written = |r: Vec<usize>| r.into_iter().map(|c| c as u8).collect::<Vec<u8>>();
            costs.push(rest_code(tower, &modes, face.clone(), &rest)?);
            first_look = release_rest(tower, &mut fork, face.clone(), &mut key_stream, cap, agree)?.0;
            looked.push(written(first_look.clone()));
            while looked.len() < looks && (look == Look::Own || looked.len() < 2 || looked[looked.len() - 1] != looked[looked.len() - 2]) {
                let again = match look {
                    Look::Once => break,
                    Look::Again | Look::Carried => {
                        let mut f = tower.advance(&mut fork, b'\n' as usize).map_err(|e| e.to_string())?;
                        for &b in &line[..=eq] {
                            f = tower.advance(&mut fork, b as usize).map_err(|e| e.to_string())?;
                        }
                        costs.push(rest_code(tower, &fork, f.clone(), &rest)?);
                        written(release_rest(tower, &mut fork, f, &mut later_keys, cap, agree)?.0)
                    }
                    Look::Redraw => {
                        costs.push(costs[0]);
                        written(release_rest(tower, &mut modes.clone(), face.clone(), &mut later_keys, cap, agree)?.0)
                    }
                    Look::Own => {
                        // The fork's attempt meets its line's end and the tower writes on: it
                        // looks again only where it writes its line's head again.
                        let f = tower.advance(&mut fork, b'\n' as usize).map_err(|e| e.to_string())?;
                        let (asked, f) = release_rest(tower, &mut fork, f, &mut later_keys, eq + 1, agree)?;
                        if asked.iter().map(|&c| c as u8).ne(line[..=eq].iter().copied()) {
                            break;
                        }
                        costs.push(rest_code(tower, &fork, f.clone(), &rest)?);
                        written(release_rest(tower, &mut fork, f, &mut later_keys, cap, agree)?.0)
                    }
                };
                looked.push(again);
            }
            // Each look read by the lock with the true rest (micro-control §7): the longest
            // order-consistent coupling `λ` and its friction `F* = |H| + |T| − 2λ`, the look's end
            // counted where it wrote one (a look cut at `cap` wrote none).
            for l in &looked {
                let mut h = l.clone();
                if h.len() < cap {
                    h.push(b'\n');
                }
                let c = coupling(&h, &rest).map_err(|e| e.to_string())?;
                locks.push((c.lambda, c.least_friction));
            }
            spent += looked.len();
            let agreed = looked.len() >= 2 && looked[looked.len() - 1] == looked[looked.len() - 2];
            settled += usize::from(agreed);
            if look != Look::Once {
                look_rows.push_str(&format!(
                    "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
                    i,
                    field(&line[..=eq]),
                    field(&rest[..rest.len() - 1]),
                    u8::from(agreed),
                    looked.iter().map(|l| field(l)).collect::<Vec<_>>().join("|"),
                    costs.iter().map(|c| c.to_string()).collect::<Vec<_>>().join("|"),
                    locks.iter().map(|l| l.0.to_string()).collect::<Vec<_>>().join("|"),
                    locks.iter().map(|l| l.1.to_string()).collect::<Vec<_>>().join("|")
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
            field(&line[..=eq]),
            field(&rest[..rest.len() - 1]),
            field(&release),
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
    /// The tower decides: after a look and its line's end it writes on, and looks again only
    /// where it writes its line's head again.
    Own,
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
/// `cap` classes, with the face the fork stands at after the last class it wrote. The fork moves
/// through every class it writes.
fn release_rest(tower: &Tower, fork: &mut TowerState, mut face: TowerFace, keys: &mut KeyStream, cap: usize, agree: u32) -> Result<(Vec<usize>, TowerFace)> {
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
    Ok((release, face))
}

/// The look inside training: at each moment the terrain declares (the byte at which a line asks
/// for its rest), the tower releases its own rest from the state its stream has reached, by
/// `agree` exact agreeing draws from its stream's share of `keys`. The stream's own passage stays
/// the plain text, so every first arrival is compared at every place. Where the release and its
/// line end part from the true rest, a fork opens from the stream's state at the moment and reads
/// the release and its end, compared with nothing (up to the place they part its faces are the
/// stream's own, compared already; past it the passage is the fork's own), then the line's head
/// again and the true rest and its end. On the fork only the news is compared
/// (`TowerLearner::section_compared`): the true rest's places that lie on no least-friction
/// coupling with the release and its end (`receiver::coupling`, the micro-control's §7 lock), the
/// places the release carries at no lag. The lock reads both strands from both ends alike, so no
/// place, first or last, frames the comparison. The head again and the true rest's places the
/// release can hold are what the fork has just read, so they are read with nothing compared:
/// compared, the head taught that a line's question returns after its answer, against the passage,
/// and the held places were learned by copying the release (the record of October 23 on a terrain
/// of interacting digits, "Reading the side-fork tower's faces"; the fork that compared them is at
/// [`79a440c06`](https://github.com/brandonrdug/holonics/tree/79a440c06), and the fork that
/// compared the true rest from the first place it parts from the release, a teacher's frame that
/// privileges the beginning, at
/// [`0ef7c4fc4`](https://github.com/brandonrdug/holonics/tree/0ef7c4fc4)). The fork joins the
/// section its moment falls in, deposits with the streams and ends there. Where the release is the
/// true rest no fork opens. The terrain's moment and line end are its codec's declared bytes, read
/// outside the tower.
pub(super) struct Looking {
    keys: Vec<u8>,
    agree: u32,
    moment: usize,
    end: usize,
}

/// One stream's plain passage from the section's first class on, and the forks its moments opened
/// in the section.
struct Looker {
    start: usize,
    end: usize,
    at: usize,
    line_start: Option<usize>,
    built: Vec<usize>,
    forks: Vec<Fork>,
    keys: KeyStream,
    looks: usize,
    right: usize,
}

/// A look's fork: the state having received every class before the moment, and the classes it
/// reads from the moment on, each with the class its face is compared with, or nothing.
struct Fork {
    opening: TowerState,
    classes: Vec<usize>,
    compared: Vec<Option<usize>>,
}

impl Looker {
    fn new(start: usize, end: usize, keys: KeyStream) -> Self {
        Self { start, end, at: start, line_start: None, built: Vec::new(), forks: Vec::new(), keys, looks: 0, right: 0 }
    }

    fn keys_left(&self) -> usize {
        self.keys.remaining()
    }

    /// Fill the passage to `need` classes from the stream's text, the state `opening` having
    /// received every class before the first, and open a fork at each moment where the release
    /// parts from the true rest: false when the stream's text ends first. A line's head is whole
    /// only after the stream has met a line's end, so a stream releases only from its first whole
    /// line on.
    fn fill(&mut self, tower: &Tower, text: &[usize], opening: &TowerState, need: usize, look: &Looking) -> Result<bool> {
        let mut probe = opening.clone();
        let mut probed = 0usize;
        while self.built.len() < need {
            if self.at >= self.end {
                return Ok(false);
            }
            let c = text[self.at];
            self.at += 1;
            self.built.push(c);
            if c == look.end {
                self.line_start = Some(self.at);
            } else if let (true, Some(head)) = (c == look.moment, self.line_start) {
                let moment = self.built.len() - 1;
                for &b in &self.built[probed..moment] {
                    tower.advance(&mut probe, b).map_err(|e| e.to_string())?;
                }
                let before = probe.clone();
                let face = tower.advance(&mut probe, c).map_err(|e| e.to_string())?;
                probed = self.built.len();
                let given = text[self.at..self.end].iter().position(|&b| b == look.end).unwrap_or(self.end - self.at);
                let release = release_rest(tower, &mut probe.clone(), face, &mut self.keys, given + 4, look.agree)?.0;
                let attempt: Vec<usize> = release.into_iter().chain(std::iter::once(look.end)).collect();
                let truth = &text[self.at..(self.at + given + 1).min(self.end)];
                self.looks += 1;
                if attempt == truth {
                    self.right += 1;
                } else {
                    let head = &text[head..self.at];
                    // The true rest's places the release holds on no least-friction coupling.
                    let slips = coupling(&attempt, truth).map_err(|e| e.to_string())?.never_held_t_indices;
                    let classes: Vec<usize> = std::iter::once(c).chain(attempt.iter().copied()).chain(head.iter().copied()).chain(truth.iter().copied()).collect();
                    let compared: Vec<Option<usize>> = std::iter::once(Some(c))
                        .chain(attempt.iter().chain(head).map(|_| None))
                        .chain(truth.iter().enumerate().map(|(j, &b)| slips.binary_search(&j).is_ok().then_some(b)))
                        .collect();
                    self.forks.push(Fork { opening: before, classes, compared });
                }
            }
        }
        Ok(true)
    }
}

/// The declared number of agreeing draws: one when none is named.
pub(super) fn agreement(arg: Option<&String>) -> Result<u32> {
    let agree = arg.map_or(Ok(1), |a| a.parse::<u32>())?;
    if agree == 0 {
        return Err("a release needs at least one draw".into());
    }
    Ok(agree)
}
