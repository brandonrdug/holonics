//! The duplex's exterior commands (`holonics::hnn::tower::duplex`): train it on text over passes
//! and read terrain lines from both sides.
//!
//! [definition; agent-inferred, October 23] A pass walks the streams in sections as the tower's
//! does (`tower_train`); the forward strand's state is carried from section to section and the
//! reverse opens at rest at each section's end. After each pass the frozen duplex reads the
//! held-out text in the same number of streams, the reverse opening at each section's end as in
//! training, and prints the forward's and the meeting's codes per region beside the pass.
use super::tower_train::{agreement, agreement_face, count, per, region_line, roles_of, REGIONS};
use super::*;
use holonics::hnn::tower::duplex::{Duplex, DuplexLearner};
use holonics::hnn::tower::{TowerDeclaration, TowerFace, TowerState};

/// A learner's state read ceiling, `2^30` bytes.
const STATE_BUDGET: usize = 1 << 30;

/// The held-out reading: the frozen duplex's forward and meeting codes per region of `roles` (each
/// coded byte's region), the text cut into `streams` contiguous parts.
fn held_out(duplex: &Duplex, classes: &[usize], roles: &[u8], streams: usize, section: usize) -> Result<[[(i64, usize); 4]; 2]> {
    let chunk = classes.len().div_ceil(streams);
    let starts: Vec<usize> = (0..classes.len()).step_by(chunk).collect();
    use rayon::prelude::*;
    let parts: Vec<[[(i64, usize); 4]; 2]> = starts
        .par_iter()
        .map(|&start| {
            let part = &classes[start..(start + chunk).min(classes.len())];
            let mut regions = [[(0i64, 0usize); 4]; 2];
            if part.len() < 3 {
                return Ok(regions);
            }
            let (forward, meeting) = duplex.read_cells(part, Some(section)).map_err(|e| e.to_string())?;
            for (face, codes) in [forward, meeting].into_iter().enumerate() {
                for (i, code) in codes.into_iter().enumerate() {
                    let region = &mut regions[face][roles[start + i + 1] as usize];
                    region.0 += code;
                    region.1 += 1;
                }
            }
            Ok(regions)
        })
        .collect::<std::result::Result<_, String>>()?;
    let mut regions = [[(0i64, 0usize); 4]; 2];
    for part in parts {
        for face in 0..2 {
            for r in 0..4 {
                regions[face][r].0 += part[face][r].0;
                regions[face][r].1 += part[face][r].1;
            }
        }
    }
    Ok(regions)
}

/// `train-duplex TRAIN TRAIN_SHA DEV DEV_SHA DEV_ROLES DEV_ROLES_SHA KEYS KEYS_SHA WIDTH MODES
/// CONTACTS LEVELS MEETING STREAMS SECTION PASSES RATE_BITS OUT [FROM FROM_SHA]`: the gated duplex
/// at the byte classes, each strand of the declared width, bank, contacts and levels, meeting
/// through `MEETING` contacts.
pub(super) fn train(args: &[String]) -> Result<()> {
    if args.len() != 19 && args.len() != 21 {
        return Err("train-duplex TRAIN TRAIN_SHA DEV DEV_SHA DEV_ROLES DEV_ROLES_SHA KEYS KEYS_SHA WIDTH MODES CONTACTS LEVELS MEETING STREAMS SECTION PASSES RATE_BITS OUT [FROM FROM_SHA]".into());
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
        gated: true,
        turned: false,
    };
    let meeting = count(&args[13])?;
    let streams = count(&args[14])?;
    let section = count(&args[15])?;
    let passes = count(&args[16])?;
    let rate_bits: u32 = args[17].parse()?;
    let out = Path::new(&args[18]);
    std::fs::create_dir(out)?;
    let classes: Vec<usize> = train.iter().map(|&b| b as usize).collect();
    let dev: Vec<usize> = dev.iter().map(|&b| b as usize).collect();
    if streams == 0 || section < 2 || classes.len() < streams * (section + 1) {
        return Err("the training text must hold one section of at least two a stream".into());
    }
    let mut learner = if args.len() == 21 {
        let from = pinned_read(&args[19], &args[20], STATE_BUDGET)?;
        let learner = DuplexLearner::from_text(std::str::from_utf8(&from)?).map_err(|e| e.to_string())?;
        if learner.duplex.forward.declaration != declaration || learner.duplex.contacts != meeting || learner.rate_bits != rate_bits {
            return Err("the continued learner's declaration or rate differs from the declared one".into());
        }
        learner
    } else {
        DuplexLearner::new(Duplex::found(declaration, meeting, &keys).map_err(|e| e.to_string())?, rate_bits)
    };
    let chunk = classes.len() / streams;
    let sections_a_pass = (chunk - 1) / section;
    println!(
        "DUPLEX_TRAIN strand_material={} meeting_material={} streams={} section={} sections_a_pass={} train_bytes={} dev_bytes={}",
        learner.duplex.forward.theta.len(),
        learner.duplex.meeting.len(),
        streams,
        section,
        sections_a_pass,
        classes.len(),
        dev.len()
    );
    for pass in 0..passes {
        let pass_started = Instant::now();
        let mut states: Vec<TowerState> = (0..streams).map(|_| learner.duplex.forward.rest()).collect();
        let (mut code, mut cells, mut deposits, mut halvings) = ([0i64; 3], [0usize; 2], 0usize, 0u32);
        let mut window = ([0i64; 3], [0usize; 2]);
        for k in 0..sections_a_pass {
            let ranges: Vec<std::ops::Range<usize>> =
                (0..streams).map(|s| s * chunk + k * section..s * chunk + (k + 1) * section + 1).collect();
            let parts: Vec<&[usize]> = ranges.iter().map(|r| &classes[r.clone()]).collect();
            let receipt = learner.section(&mut states, &parts).map_err(|e| e.to_string())?;
            for sum in [&mut code, &mut window.0] {
                sum[0] += receipt.forward_before;
                sum[1] += receipt.reverse_before;
                sum[2] += receipt.meeting_before;
            }
            for n in [&mut cells, &mut window.1] {
                n[0] += receipt.forward_cells;
                n[1] += receipt.meeting_cells;
            }
            deposits += receipt.deposited as usize;
            halvings += receipt.halvings;
            if (k + 1) % 32 == 0 || k + 1 == sections_a_pass {
                println!(
                    "DUPLEX_SECTION pass={} section={} forward={} reverse={} meeting={} deposits={} halvings={} elapsed_ms={}",
                    pass,
                    k + 1,
                    per(window.0[0], window.1[0]),
                    per(window.0[1], window.1[0]),
                    per(window.0[2], window.1[1]),
                    deposits,
                    halvings,
                    started.elapsed().as_millis()
                );
                window = ([0; 3], [0; 2]);
            }
        }
        let text = learner.to_text();
        let name = format!("STATE.{pass}");
        write_new(&out.join(&name), text.as_bytes())?;
        println!("DUPLEX_STATE {name} state_bytes={} state_sha256={}", text.len(), sha256(text.as_bytes())?);
        let [forward, meeting] = held_out(&learner.duplex, &dev, &roles, streams, section)?;
        println!(
            "DUPLEX_PASS pass={} train_forward={} train_reverse={} train_meeting={} dev_forward {} dev_meeting {} deposits={}/{} pass_ms={} elapsed_ms={}",
            pass,
            per(code[0], cells[0]),
            per(code[1], cells[0]),
            per(code[2], cells[1]),
            region_line(&forward),
            region_line(&meeting),
            deposits,
            sections_a_pass,
            pass_started.elapsed().as_millis(),
            started.elapsed().as_millis()
        );
    }
    let text = learner.to_text();
    write_new(&out.join("STATE"), text.as_bytes())?;
    println!("DUPLEX_DONE state_bytes={} state_sha256={} regions={} elapsed_ms={}", text.len(), sha256(text.as_bytes())?, REGIONS.join(","), started.elapsed().as_millis());
    Ok(())
}

/// One exact draw from `face` at `agree` agreeing draws, the classes `barred` given no mass.
fn draw(face: &TowerFace, agree: u32, barred: Option<usize>, keys: &mut KeyStream) -> Result<usize> {
    let mut masses = face.masses.clone();
    if let Some(b) = barred {
        masses[b] = 0;
    }
    if masses.iter().all(|&m| m == 0) {
        return Err("a face with no mass outside the barred class".into());
    }
    let key = keys.next_key().ok_or("fewer keys than the draws")?;
    Ok(holonics::receiver::release::draw_exact(&agreement_face(&masses, agree), &key)?
        .drawn_class()
        .ok_or("an unresolved draw at an exact face")?)
}

/// `read-lines-duplex STATE STATE_SHA TEXT TEXT_SHA KEYS KEYS_SHA WRITTEN AGREE SWEEPS OUT`: each
/// line of the text read alone, `\n line \n`. The forward strand opens at rest on the first line
/// end and codes the rest of the line after its first `=`; the meeting codes the same places but
/// the closing line end, each from what lies on both sides. For the first `WRITTEN` lines a fork
/// of the forward strand at the `=` releases its own rest by exact agreeing draws until a line's
/// end (or as many classes as the given rest and four more), and the meeting refines that release
/// at its length (the line end barred) for at most `SWEEPS` sweeps (`Duplex::refine`).
/// `LINES.tsv`: the line's index, its head, the rest as given, the forward's release, the refined
/// release, the sweeps run and whether the last changed nothing, the forward's codes of the rest and
/// its line end, the meeting's codes of the rest, each on `2^(−20)` bits.
pub(super) fn read_lines(args: &[String]) -> Result<()> {
    if args.len() != 11 {
        return Err("read-lines-duplex STATE STATE_SHA TEXT TEXT_SHA KEYS KEYS_SHA WRITTEN AGREE SWEEPS OUT".into());
    }
    let started = Instant::now();
    let learner = DuplexLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let text = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let keys = pinned_read(&args[5], &args[6], READ_BUDGET as usize)?;
    let written: usize = args[7].parse()?;
    let agree = agreement(args.get(8))?;
    let sweeps: usize = args[9].parse()?;
    let out = Path::new(&args[10]);
    std::fs::create_dir(out)?;
    let duplex = &learner.duplex;
    let forward = &duplex.forward;
    let end = b'\n' as usize;
    let mut key_stream = KeyStream::new(keys, 8)?;
    let mut rows = String::new();
    let (mut lines, mut settled, mut refined_lines) = (0usize, 0usize, 0usize);
    for (i, line) in text.split(|&b| b == b'\n').filter(|l| !l.is_empty()).enumerate() {
        let Some(eq) = line.iter().position(|&b| b == b'=') else { continue };
        let classes: Vec<usize> = std::iter::once(end).chain(line.iter().map(|&b| b as usize)).chain([end]).collect();
        let head = &classes[..eq + 2];
        let rest = &line[eq + 1..];
        let (fcodes, mcodes) = duplex.read_cells(&classes, None).map_err(|e| e.to_string())?;
        let (mut release, mut refined, mut run) = (Vec::new(), Vec::new(), String::new());
        if i < written {
            let mut modes = forward.rest();
            let mut face = None;
            for &u in head {
                face = Some(forward.advance(&mut modes, u).map_err(|e| e.to_string())?);
            }
            let mut face = face.ok_or("an empty head")?;
            while release.len() < rest.len() + 4 {
                let class = draw(&face, agree, None, &mut key_stream)?;
                if class == end {
                    break;
                }
                release.push(class);
                face = forward.advance(&mut modes, class).map_err(|e| e.to_string())?;
            }
            refined = release.clone();
            if !refined.is_empty() {
                let mut redraw = |f: &TowerFace| -> std::result::Result<usize, holonics::hnn::tower::TowerError> {
                    draw(f, agree, Some(end), &mut key_stream).map_err(|_| holonics::hnn::tower::TowerError::Refused("a refinement draw failed"))
                };
                let (ran, still) = duplex.refine(head, &mut refined, end, sweeps, &mut redraw).map_err(|e| e.to_string())?;
                settled += still as usize;
                refined_lines += 1;
                run = format!("{ran}{}", if still { "" } else { "+" });
            }
        }
        let bytes = |c: &[usize]| c.iter().map(|&u| char::from(u as u8)).collect::<String>();
        let at = eq + 1;
        rows.push_str(&format!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
            i,
            String::from_utf8_lossy(&line[..=eq]),
            String::from_utf8_lossy(rest),
            bytes(&release),
            bytes(&refined),
            run,
            fcodes[at..].iter().map(|c| c.to_string()).collect::<Vec<_>>().join(","),
            mcodes[at..].iter().map(|c| c.to_string()).collect::<Vec<_>>().join(",")
        ));
        lines += 1;
    }
    write_new(&out.join("LINES.tsv"), rows.as_bytes())?;
    println!(
        "LINES_READ lines={} written={} refined={} settled={} agree={} sweeps={} lines_sha256={} elapsed_ms={}",
        lines,
        written.min(lines),
        refined_lines,
        settled,
        agree,
        sweeps,
        sha256(rows.as_bytes())?,
        started.elapsed().as_millis()
    );
    Ok(())
}
