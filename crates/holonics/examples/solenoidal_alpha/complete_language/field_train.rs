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
//! The mask draws are an exterior keyed stream (the key file's first word seeds an integer
//! mixer): they choose which sites a section compares, never what the field deposits.

use super::tower_train::{count, positive, STATE_BUDGET};
use super::*;
use holonics::hnn::tower::field::{Field, FieldDeclaration, FieldLearner, FieldRealization, HostField, Region};
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
fn question_text(q: &[u8]) -> Vec<u8> {
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
fn mix(seed: u64, counter: u64) -> u64 {
    let mut z = seed.wrapping_add(counter.wrapping_mul(0x9E37_79B9_7F4A_7C15));
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

/// A region's completion mask (agent-inferred, November 1): with even odds the answer's sites
/// (its void included) or the whole region's are open to the comparison, each unresolved with
/// probability `τ`, `τ` drawn uniform on `(0, 1]` on `2^(−16)`; at least one site is unresolved.
fn mask(seed: u64, draw: u64, question: usize, sites: usize) -> Vec<bool> {
    let head = mix(seed, draw);
    let whole = head & 1 == 1;
    let tau = ((head >> 1) & 0xFFFF) + 1;
    let first = if whole { 0 } else { question };
    let mut out: Vec<bool> = (0..sites).map(|t| t >= first && (mix(seed, draw ^ ((t as u64 + 1) << 32)) & 0xFFFF) < tau).collect();
    if !out.iter().any(|&u| u) {
        let pick = first + (mix(seed, draw.wrapping_add(1)) as usize) % (sites - first);
        out[pick] = true;
    }
    out
}

/// A problem's region classes: the question and its line, the answer, then `void` to `length`.
fn region_classes(codec: &FieldCodec, q: &[usize], a: &[usize], length: usize) -> Vec<usize> {
    let mut out: Vec<usize> = q.iter().chain(a).copied().collect();
    out.resize(length, codec.void());
    out
}

/// The held-out read: every answer site (and its void) unresolved at once, the field's code of
/// the answer's classes, its digits' and its text's, on `2^(−20)` bits, beside each one's count
/// and the answer's bytes.
fn held_out(field: &Field, codec: &FieldCodec, problems: &[(Vec<usize>, Vec<usize>, usize)], realization: &mut dyn FieldRealization) -> Result<[(i64, usize); 3]> {
    let regions: Vec<(Vec<usize>, Vec<bool>)> = problems
        .iter()
        .map(|(q, a, _)| {
            let classes = region_classes(codec, q, a, q.len() + a.len() + 1);
            let open = (0..classes.len()).map(|t| t >= q.len()).collect();
            (classes, open)
        })
        .collect();
    let views: Vec<Region> = regions.iter().map(|(c, u)| Region { classes: c, unresolved: u }).collect();
    let mut out = [(0i64, 0usize); 3];
    for chunk in views.chunks(64) {
        let faces = realization.read_faces(field, chunk).map_err(|e| e.to_string())?;
        for (region, faces) in chunk.iter().zip(faces) {
            for (face, &class) in faces.iter().zip(region.classes) {
                if let Some(face) = face {
                    let code = face.code(class);
                    out[0].0 += code;
                    out[0].1 += 1;
                    let part = if codec.is_digit(class) { 1 } else { 2 };
                    out[part].0 += code;
                    out[part].1 += 1;
                }
            }
        }
    }
    Ok(out)
}

fn bits(code: i64, n: usize) -> String {
    if n == 0 {
        return "-".into();
    }
    // The reading on 2^(−20) bits as a decimal to three places.
    let thousandths = (code as i128 * 1000 + ((n as i128) << 19)) / ((n as i128) << 20);
    format!("{}.{:03}", thousandths / 1000, thousandths % 1000)
}

/// `train-field UNITS UNITS_SHA TRAIN TRAIN_SHA DEV DEV_SHA KEYS KEYS_SHA D H n STILL f K SECTION
/// LAPS RATE OUT [FROM FROM_SHA]`: the field founded on the keys (or continued from a rested
/// learner), trained over `LAPS` laps of the training problems in sections of `SECTION` regions,
/// each lap's sections in a keyed order; after each lap the learner rests as `OUT/STATE.lap` and
/// the held-out problems are read. The codec is founded on the training passage and written as
/// `OUT/CODEC`. After a lap whose passage, read before each deposit, codes no fewer bits a site
/// than the lap before's, the body grows by copies (`FieldLearner::widened`) before the next.
pub(super) fn train(args: &[String], realization: &mut dyn FieldRealization) -> Result<()> {
    if !(args.len() == 19 || args.len() == 21) {
        return Err("train-field UNITS UNITS_SHA TRAIN TRAIN_SHA DEV DEV_SHA KEYS KEYS_SHA D H n STILL f K SECTION LAPS RATE OUT [FROM FROM_SHA]".into());
    }
    let started = std::time::Instant::now();
    let units = units_of(&args[1], &args[2])?;
    let train_text = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let dev_text = pinned_read(&args[5], &args[6], READ_BUDGET as usize)?;
    let keys = pinned_read(&args[7], &args[8], READ_BUDGET as usize)?;
    let (width, heads, modes, still, contacts, ticks) = (positive(&args[9])?, positive(&args[10])?, positive(&args[11])?, count(&args[12])?, positive(&args[13])?, positive(&args[14])?);
    let (section, laps, rate) = (positive(&args[15])?, count(&args[16])?, count(&args[17])? as u32);
    let out = Path::new(&args[18]);
    std::fs::create_dir(out)?;
    let train_problems = problems_of(&train_text);
    let dev_problems = problems_of(&dev_text);
    let codec = FieldCodec::found(units, &train_problems)?;
    write_new(&out.join("CODEC"), codec.to_text().as_bytes())?;
    let encode = |problems: &[(Vec<u8>, Vec<u8>)]| -> Result<Vec<(Vec<usize>, Vec<usize>, usize)>> {
        problems.par_iter().map(|(q, a)| Ok((codec.encode(&question_text(q)).map_err(|e| e.to_string())?, codec.encode(a).map_err(|e| e.to_string())?, a.len()))).collect::<std::result::Result<Vec<_>, String>>().map_err(|e| e.into())
    };
    let train_set = encode(&train_problems)?;
    let dev_set: Vec<_> = encode(&dev_problems)?.into_iter().filter(|(_, a, _)| a.len() < codec.answer).collect();
    let mut learner = match args.get(19..21) {
        Some([path, sha]) => FieldLearner::from_text(std::str::from_utf8(&pinned_read(path, sha, STATE_BUDGET)?)?).map_err(|e| e.to_string())?,
        _ => {
            let declaration = FieldDeclaration { alphabet: codec.alphabet(), width, heads, modes, still, contacts, ticks };
            FieldLearner::new(Field::found(declaration, &keys).map_err(|e| e.to_string())?, rate)
        }
    };
    if learner.field.declaration.alphabet != codec.alphabet() {
        return Err("a continued learner whose alphabet is not the codec's".into());
    }
    let seed = u64::from_be_bytes(keys.get(..8).ok_or("a key file of fewer than eight bytes")?.try_into()?);
    // Sections of problems of like length, padded with void past the section's longest by one.
    let mut order: Vec<usize> = (0..train_set.len()).collect();
    order.sort_by_key(|&i| (train_set[i].0.len() + train_set[i].1.len(), i));
    let sections: Vec<Vec<usize>> = order.chunks(section).map(|c| c.to_vec()).collect();
    let sites_total: usize = sections.iter().map(|s| s.len() * (s.iter().map(|&i| train_set[i].0.len() + train_set[i].1.len()).max().unwrap_or(0) + 1)).sum();
    println!(
        "FIELD_DECLARATION alphabet={} width={width} heads={heads} modes={modes} still={still} contacts={contacts} ticks={ticks} section={section} rate={} answer={} train={} dev={} sections={} sites_a_lap={sites_total} material={}",
        codec.alphabet(),
        learner.rate_bits,
        codec.answer,
        train_set.len(),
        dev_set.len(),
        sections.len(),
        learner.field.theta.len()
    );
    let held = held_out(&learner.field, &codec, &dev_set, realization)?;
    println!("FIELD_HELD lap=-1 answer={} digits={} text={} classes={} ms={}", bits(held[0].0, held[0].1), bits(held[1].0, held[1].1), bits(held[2].0, held[2].1), held[0].1, started.elapsed().as_millis());
    let mut draw = 0u64;
    // The previous lap's code read before each section's deposit, and its sites.
    let mut previous: Option<(i64, usize)> = None;
    for lap in 0..laps {
        let mut walk: Vec<usize> = (0..sections.len()).collect();
        walk.sort_by_key(|&s| (mix(seed, ((lap as u64) << 40) ^ s as u64), s));
        let (mut code_before, mut code_after, mut sites, mut deposited, mut halvings) = (0i64, 0i64, 0usize, 0usize, 0u64);
        let lap_start = std::time::Instant::now();
        for (n, &s) in walk.iter().enumerate() {
            let members = &sections[s];
            let length = members.iter().map(|&i| train_set[i].0.len() + train_set[i].1.len()).max().unwrap_or(0) + 1;
            let regions: Vec<(Vec<usize>, Vec<bool>)> = members
                .iter()
                .map(|&i| {
                    let (q, a, _) = &train_set[i];
                    draw += 1;
                    (region_classes(&codec, q, a, length), mask(seed, draw, q.len(), length))
                })
                .collect();
            let views: Vec<Region> = regions.iter().map(|(c, u)| Region { classes: c, unresolved: u }).collect();
            let section_start = std::time::Instant::now();
            let receipt = learner.section_realized(&views, realization).map_err(|e| e.to_string())?;
            code_before += receipt.code_before;
            code_after += receipt.code_after;
            sites += receipt.sites;
            deposited += usize::from(receipt.deposited);
            halvings += receipt.halvings as u64;
            println!(
                "FIELD_SECTION lap={lap} n={n} sites={} before={} after={} halvings={} deposited={} length={length} ms={}",
                receipt.sites,
                bits(receipt.code_before, receipt.sites),
                bits(receipt.code_after, receipt.sites),
                receipt.halvings,
                receipt.deposited,
                section_start.elapsed().as_millis()
            );
        }
        write_new(&out.join(format!("STATE.{lap}")), learner.to_text().as_bytes())?;
        println!("FIELD_LAP lap={lap} sites={sites} before={} after={} deposited={deposited}/{} halvings={halvings} ms={}", bits(code_before, sites), bits(code_after, sites), sections.len(), lap_start.elapsed().as_millis());
        let held = held_out(&learner.field, &codec, &dev_set, realization)?;
        println!("FIELD_HELD lap={lap} answer={} digits={} text={} classes={} ms={}", bits(held[0].0, held[0].1), bits(held[1].0, held[1].1), bits(held[2].0, held[2].1), held[0].1, started.elapsed().as_millis());
        // [agent-inferred, November 1] The width is the trained body's (growth by copies, the
        // tower's law): when a lap's passage, read before each deposit, codes no fewer bits a site
        // than the lap before's, the body has spent its width and grows by two before the next.
        if let Some((code, n)) = previous {
            if (code_before as i128) * (n as i128) >= (code as i128) * (sites as i128) && lap + 1 < laps {
                learner = learner.widened(2, &keys).map_err(|e| e.to_string())?;
                let d = learner.field.declaration;
                println!("FIELD_GROW lap={lap} width={} heads={} contacts={} material={} ms={}", d.width, d.heads, d.contacts, learner.field.theta.len(), started.elapsed().as_millis());
            }
        }
        previous = Some((code_before, sites));
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

/// `release-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD HELD_SHA COUNT SWEEPS OUT`:
/// for each of the first `COUNT` held problems the field releases the answer from the question
/// alone (the codec's answer sites, refined over `SWEEPS` sweeps) and, at each of its
/// calculations, the continuation past the answer written through that calculation's `=`. It writes
/// `OUT/FREE.tsv` and `OUT/MARKS.tsv` as `card_written.py convert` writes them for
/// `written_rules.py` (a calculation's release is cut after its first `>>`), and `OUT/COUPLING.tsv`,
/// each free release's coupling read against the held answer at the class face.
pub(super) fn release(args: &[String], realization: &mut dyn FieldRealization) -> Result<()> {
    if args.len() != 12 {
        return Err("release-field STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD HELD_SHA COUNT SWEEPS OUT".into());
    }
    let started = std::time::Instant::now();
    let learner = FieldLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let units = units_of(&args[5], &args[6])?;
    let codec = FieldCodec::from_text(std::str::from_utf8(&pinned_read(&args[3], &args[4], CODEC_BUDGET)?)?, units)?;
    let held = problems_of(&pinned_read(&args[7], &args[8], READ_BUDGET as usize)?);
    let (limit, sweeps) = (count(&args[9])?, positive(&args[10])?);
    let out = Path::new(&args[11]);
    std::fs::create_dir(out)?;
    let field = &learner.field;
    let mut release_one = |question: &[u8], prefix: &[u8]| -> Result<Vec<usize>> {
        let mut q = codec.encode(&question_text(question))?;
        let written = codec.encode(prefix)?;
        let open = codec.answer.saturating_sub(written.len()).max(1);
        q.extend(&written);
        field.release_realized(&q, open, sweeps, codec.void(), realization).map_err(|e| e.to_string().into())
    };
    let (mut free_rows, mut mark_rows, mut couplings) = (String::new(), String::new(), String::from("problem\treleased\theld\tlambda\tfriction\tplateaus\tlongest\tlag\n"));
    let (mut sum_h, mut sum_t, mut sum_lambda, mut sum_friction, mut marks) = (0usize, 0usize, 0usize, 0usize, 0usize);
    for (i, (question, answer)) in held.iter().take(limit).enumerate() {
        let released = release_one(question, b"")?;
        let h: Vec<usize> = released.iter().copied().take_while(|&c| c < codec.void()).collect();
        free_rows.push_str(&format!("{i}\t{}\n", escaped(&codec.decode(&h))));
        let t = codec.encode(answer)?;
        let c = coupling(&h, &t);
        let longest = c.plateaus.iter().copied().max_by_key(|&(run, lag)| (run, std::cmp::Reverse(lag.unsigned_abs()))).unwrap_or((0, 0));
        couplings.push_str(&format!("{i}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n", h.len(), t.len(), c.lambda, c.friction, c.plateaus.len(), longest.0, longest.1));
        sum_h += h.len();
        sum_t += t.len();
        sum_lambda += c.lambda;
        sum_friction += c.friction;
        for (j, (expression, at)) in calculations_of(answer).into_iter().enumerate() {
            let continued = release_one(question, &answer[..at])?;
            let mut r = codec.decode(&continued);
            if let Some(cut) = r.windows(2).position(|w| w == b">>") {
                r.truncate(cut + 2);
            }
            mark_rows.push_str(&format!("{i}\t{j}\t{}\t{}\n", escaped(expression), escaped(&r)));
            marks += 1;
        }
    }
    write_new(&out.join("FREE.tsv"), free_rows.as_bytes())?;
    write_new(&out.join("MARKS.tsv"), mark_rows.as_bytes())?;
    write_new(&out.join("COUPLING.tsv"), couplings.as_bytes())?;
    println!(
        "FIELD_RELEASE free={} marks={marks} sweeps={sweeps} released={sum_h} held={sum_t} lambda={sum_lambda} friction={sum_friction} ms={}",
        held.len().min(limit),
        started.elapsed().as_millis()
    );
    Ok(())
}

/// `release-field-text STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD HELD_SHA COUNT SWEEPS`:
/// each of the first `COUNT` held questions and the answer the field releases for it, whole (a
/// private read: never committed; the held answer is not printed beside it).
pub(super) fn release_text(args: &[String], realization: &mut dyn FieldRealization) -> Result<()> {
    if args.len() != 11 {
        return Err("release-field-text STATE STATE_SHA CODEC CODEC_SHA UNITS UNITS_SHA HELD HELD_SHA COUNT SWEEPS".into());
    }
    let learner = FieldLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let units = units_of(&args[5], &args[6])?;
    let codec = FieldCodec::from_text(std::str::from_utf8(&pinned_read(&args[3], &args[4], CODEC_BUDGET)?)?, units)?;
    let held = problems_of(&pinned_read(&args[7], &args[8], READ_BUDGET as usize)?);
    let (limit, sweeps) = (count(&args[9])?, positive(&args[10])?);
    for (i, (question, _)) in held.iter().take(limit).enumerate() {
        let q = codec.encode(&question_text(question))?;
        let released = learner.field.release_realized(&q, codec.answer, sweeps, codec.void(), realization).map_err(|e| e.to_string())?;
        println!("FIELD_PROMPT {i}\n{}\nFIELD_ANSWER {i}\n{}\n", String::from_utf8_lossy(question), String::from_utf8_lossy(&codec.decode(&released)));
    }
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
        let run = |out: &str, from: Option<(String, String)>| {
            let mut args: Vec<String> = ["train-field", &units, &units_sha, &passage, &passage_sha, &held, &held_sha, &key, &key_sha, "8", "2", "3", "1", "4", "2", "2", "2", "4", out].iter().map(|s| s.to_string()).collect();
            if let Some((state, sha)) = from {
                args.extend([state, sha]);
            }
            train(&args, &mut host())
        };
        run(&at("A"), None).expect("train");
        let rested = std::fs::read(dir.join("A/STATE.1")).expect("rested");
        let codec = std::fs::read(dir.join("A/CODEC")).expect("codec");
        assert!(run(&at("A"), None).is_err(), "a run's directory is never written over");
        run(&at("B"), Some((at("A/STATE.1"), sha256(&rested).unwrap()))).expect("continued");
        assert!(dir.join("B/STATE.1").exists());
        let state_sha = sha256(&rested).unwrap();
        let codec_sha = sha256(&codec).unwrap();
        let args: Vec<String> = ["release-field", &at("A/STATE.1"), &state_sha, &at("A/CODEC"), &codec_sha, &units, &units_sha, &held, &held_sha, "2", "3", &at("R")].iter().map(|s| s.to_string()).collect();
        release(&args, &mut host()).expect("release");
        let read = |name: &str| String::from_utf8(std::fs::read(dir.join("R").join(name)).expect("read")).unwrap();
        assert_eq!(read("FREE.tsv").lines().count(), 2);
        assert_eq!(read("MARKS.tsv").lines().count(), 2, "one calculation a held problem");
        let coupling = read("COUPLING.tsv");
        assert_eq!(coupling.lines().count(), 3);
        for row in coupling.lines().skip(1) {
            let cells: Vec<usize> = row.split('\t').take(5).map(|c| c.parse().unwrap()).collect();
            assert_eq!(cells[1] + cells[2], 2 * cells[3] + cells[4], "F* = |H| + |T| - 2 lambda");
        }
        assert!(release(&args, &mut host()).is_err(), "a release's directory is never written over");
        let text: Vec<String> = ["release-field-text", &at("A/STATE.1"), &state_sha, &at("A/CODEC"), &codec_sha, &units, &units_sha, &held, &held_sha, "1", "2"].iter().map(|s| s.to_string()).collect();
        release_text(&text, &mut host()).expect("release text");
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn masks_open_a_site() {
        for draw in 0..64 {
            let m = mask(7, draw, 5, 12);
            assert!(m.iter().any(|&u| u));
            assert_eq!(m.len(), 12);
        }
    }
}
