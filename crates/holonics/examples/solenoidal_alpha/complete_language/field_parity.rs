//! The field's card realization read against the host's (`holonics-cuda`'s `field_pass`), on the
//! sections `train-field` forms (record `2026-11-01_THE_PROBLEM_IS_ONE_FIELD…`, §7 and §8's acceptance
//! 2).
//!
//! `parity-field` founds the field as `train-field` does (and widens it by `GROW` when `GROW > 1`)
//! and has two learners, one through the host ([`HostField`]) and one through the card, each form
//! and take the first `SECTIONS` sections of its next lap exactly as `train-field` does (the keyed
//! walk, tails and shapes), then read its held step on the withheld problems as a lap's end does. Every read
//! each makes (the masks' reads, the held step's reads, the section's read and return, and each of the
//! certificate's rereads) is compared face for face (each unresolved site's masses and total) and
//! covector entry for entry, and the regions and the learners' texts after each section; then the
//! field writes the first `RELEASES` held problems' answers through both ([`Field::sample_realized`], `SWEEPS` sweeps,
//! the same keyed draws), each answer compared place for place.
//! `time-field` reads the card alone over the opening sections and the opening writes and projects a lap from the
//! measured upper time a site pair, and the held problems' writes from the measured time a sweep.

use super::field_train::{held_regions, paths_of, problems_of, question_text, region_lengths, section_regions, sections_of, unseen_regions, units_of, views_of, walk, FieldCodec, Problems, TrainRegion};
use super::tower_train::{count, positive};
use super::*;
use holonics::hnn::tower::field::{Field, FieldDeclaration, FieldLearner, FieldNext, FieldRead, FieldRealization, FieldReceipt, HeldRows, HostField, Region, RowCurrent};
use holonics::hnn::tower::{TowerError, TowerFace};
use rayon::prelude::*;

/// The training passage as `train-field` reads it: the codec, the encoded training and held problems,
/// the reach, the keys and the mask stream's seed, the sections of like length and the withheld
/// problems.
struct Passage {
    codec: FieldCodec,
    train: Problems,
    held: Problems,
    reach: usize,
    keys: Vec<u8>,
    seed: u64,
    sections: Vec<Vec<usize>>,
    unseen: Vec<usize>,
}

/// `UNITS UNITS_SHA TRAIN TRAIN_SHA HELD HELD_SHA KEYS KEYS_SHA` and the section's regions, as
/// `train-field` reads them.
fn passage(args: &[String], section: usize) -> Result<Passage> {
    let units = units_of(&args[0], &args[1])?;
    let train_text = pinned_read(&args[2], &args[3], READ_BUDGET as usize)?;
    let held_text = pinned_read(&args[4], &args[5], READ_BUDGET as usize)?;
    let keys = pinned_read(&args[6], &args[7], READ_BUDGET as usize)?;
    let train_problems = problems_of(&train_text);
    let held_problems = problems_of(&held_text);
    let codec = FieldCodec::found(units, &train_problems)?;
    let encode = |problems: &[(Vec<u8>, Vec<u8>)]| -> Result<Problems> {
        problems.par_iter().map(|(q, a)| Ok((codec.encode(&question_text(q)).map_err(|e| e.to_string())?, codec.encode(a).map_err(|e| e.to_string())?, a.len()))).collect::<std::result::Result<Vec<_>, String>>().map_err(|e| e.into())
    };
    let train = encode(&train_problems)?;
    let held: Problems = encode(&held_problems)?.into_iter().filter(|(_, a, _)| a.len() < codec.answer).collect();
    let reach = train.iter().chain(&held).map(|(q, _, _)| q.len() + codec.answer).max().unwrap_or(codec.answer);
    let seed = u64::from_be_bytes(keys.get(keys.len().saturating_sub(8)..).filter(|w| w.len() == 8).ok_or("a key file of fewer than eight bytes")?.try_into()?);
    let (sections, unseen) = sections_of(&train, section, held.len(), seed);
    println!("FIELD_PASSAGE train={} withheld={} held={} held_read={} alphabet={} answer={} reach={}", train.len() - unseen.len(), unseen.len(), held_problems.len(), held.len(), codec.alphabet(), codec.answer, reach);
    Ok(Passage { codec, train, held, reach, keys, seed, sections, unseen })
}

impl Passage {
    /// A section's regions as `train-field` forms them from `draw` on, its path states those of `paths`, read through
    /// `realization` after `learner`'s held step is read on them (its read returned); with `withheld`, the withheld
    /// problems `members` read with their neighbours (the held step then read by the caller).
    fn regions(&self, members: &[usize], paths: &[usize], draw: &mut u64, withheld: bool, learner: &mut FieldLearner, realization: &mut dyn FieldRealization) -> Result<(Vec<TrainRegion>, Option<FieldNext>)> {
        if withheld {
            return Ok((unseen_regions(&self.codec, &self.train, members, self.seed).into_iter().map(|(c, u)| TrainRegion::plain(c, u)).collect(), None));
        }
        section_regions(&self.codec, &self.train, members, paths, self.seed, draw, learner, realization)
    }

    /// The founded learner of the declaration `D H n STILL f K` at `RATE`.
    fn learner(&self, args: &[String], rate: u32) -> Result<FieldLearner> {
        let (width, heads, modes, still, contacts, ticks) = (positive(&args[0])?, positive(&args[1])?, positive(&args[2])?, count(&args[3])?, positive(&args[4])?, positive(&args[5])?);
        let declaration = FieldDeclaration { alphabet: self.codec.alphabet(), width, heads, modes, still, contacts, ticks, frames: heads, reach: self.reach, lanes: 1 };
        let mut field = Field::found(declaration, &self.keys).map_err(|e| e.to_string())?;
        // The trainer's declared clock (`FIELD_CLOCK_PER_BLANK`, `Field::per_blank_clock`), so its parity reads that law.
        field.per_blank_clock = std::env::var_os("FIELD_CLOCK_PER_BLANK").is_some();
        Ok(FieldLearner::new(field, rate))
    }
}

/// A realization whose every read is kept beside its result, so two learners' reads are compared
/// (a logits read kept as the faces at `β = 1` its logits carry, beside the logits themselves).
struct Recorder<'a> {
    inner: &'a mut dyn FieldRealization,
    reads: Vec<(Vec<Vec<Option<TowerFace>>>, Option<Vec<i128>>)>,
    logits: Vec<Vec<FieldRead>>,
}

impl FieldRealization for Recorder<'_> {
    fn read_and_return(&mut self, field: &Field, regions: &[Region]) -> std::result::Result<(Vec<Vec<Option<TowerFace>>>, Vec<i128>), TowerError> {
        let (faces, g) = self.inner.read_and_return(field, regions)?;
        self.reads.push((faces.clone(), Some(g.clone())));
        Ok((faces, g))
    }
    fn read_faces(&mut self, field: &Field, regions: &[Region]) -> std::result::Result<Vec<Vec<Option<TowerFace>>>, TowerError> {
        let faces = self.inner.read_faces(field, regions)?;
        self.reads.push((faces.clone(), None));
        Ok(faces)
    }
    fn read_logits(&mut self, field: &Field, regions: &[Region]) -> std::result::Result<Vec<FieldRead>, TowerError> {
        let logits = self.inner.read_logits(field, regions)?;
        self.logits.push(logits.clone());
        Ok(logits)
    }
    fn read_landmarks(&mut self, field: &Field, region: &Region, question: usize, sites: &[usize], count: usize) -> std::result::Result<Vec<Vec<(usize, u64)>>, TowerError> {
        self.inner.read_landmarks(field, region, question, sites, count)
    }
    fn met_pairs(&self) -> Option<u128> {
        self.inner.met_pairs()
    }
    fn read_row_shares(&mut self, field: &Field, regions: &[Region], questions: &[usize]) -> std::result::Result<Vec<HeldRows>, TowerError> {
        self.inner.read_row_shares(field, regions, questions)
    }
    fn read_covector_shares(&mut self, field: &Field, regions: &[Region]) -> std::result::Result<Vec<[u128; 2]>, TowerError> {
        self.inner.read_covector_shares(field, regions)
    }
    fn read_row_currents(&mut self, field: &Field, regions: &[Region], questions: &[usize], returning: bool) -> std::result::Result<Vec<Vec<RowCurrent>>, TowerError> {
        self.inner.read_row_currents(field, regions, questions, returning)
    }
}

/// A realization that counts the site rows it reads: a region's sites, times the heads and the
/// ticks, every call. (A site's row meets its near field and its classes, so the pairs a read
/// meets are counted on the card, `FIELD_CARD pairs=`; a row is the unit a projection reads.)
struct Counted<'a> {
    inner: &'a mut dyn FieldRealization,
    rows: u128,
}

impl Counted<'_> {
    fn count(&mut self, field: &Field, regions: &[Region]) {
        let d = field.declaration;
        self.rows += regions.iter().map(|r| r.classes.len() as u128).sum::<u128>() * (d.heads * d.ticks) as u128;
    }
}

impl FieldRealization for Counted<'_> {
    fn read_and_return(&mut self, field: &Field, regions: &[Region]) -> std::result::Result<(Vec<Vec<Option<TowerFace>>>, Vec<i128>), TowerError> {
        self.count(field, regions);
        self.inner.read_and_return(field, regions)
    }
    fn read_faces(&mut self, field: &Field, regions: &[Region]) -> std::result::Result<Vec<Vec<Option<TowerFace>>>, TowerError> {
        self.count(field, regions);
        self.inner.read_faces(field, regions)
    }
    fn read_logits(&mut self, field: &Field, regions: &[Region]) -> std::result::Result<Vec<FieldRead>, TowerError> {
        self.count(field, regions);
        self.inner.read_logits(field, regions)
    }
    fn read_landmarks(&mut self, field: &Field, region: &Region, question: usize, sites: &[usize], count: usize) -> std::result::Result<Vec<Vec<(usize, u64)>>, TowerError> {
        self.inner.read_landmarks(field, region, question, sites, count)
    }
    fn met_pairs(&self) -> Option<u128> {
        self.inner.met_pairs()
    }
    fn read_row_shares(&mut self, field: &Field, regions: &[Region], questions: &[usize]) -> std::result::Result<Vec<HeldRows>, TowerError> {
        self.count(field, regions);
        self.inner.read_row_shares(field, regions, questions)
    }
    fn read_covector_shares(&mut self, field: &Field, regions: &[Region]) -> std::result::Result<Vec<[u128; 2]>, TowerError> {
        self.count(field, regions);
        self.inner.read_covector_shares(field, regions)
    }
    fn read_row_currents(&mut self, field: &Field, regions: &[Region], questions: &[usize], returning: bool) -> std::result::Result<Vec<Vec<RowCurrent>>, TowerError> {
        self.count(field, regions);
        self.inner.read_row_currents(field, regions, questions, returning)
    }
}

const FAMILIES: [&str; 17] = ["enc", "before", "after", "word", "word_bias", "v", "v_bias", "out", "out_bias", "a", "a_bias", "b", "b_bias", "w", "w_bias", "read", "read_bias"];

/// The family and the entry within it of a material index.
fn family_of(field: &Field, index: usize) -> String {
    for (n, &(start, len, _)) in field.families_all().iter().enumerate() {
        if index < start + len {
            return format!("{}[{}]", FAMILIES.get(n).copied().unwrap_or("?"), index - start);
        }
    }
    format!("past[{index}]")
}

/// Two reads compared: the unequal faces (and the first, region, site and class), the unequal
/// covector entries (and the first, by family).
fn compare(field: &Field, host: &(Vec<Vec<Option<TowerFace>>>, Option<Vec<i128>>), card: &(Vec<Vec<Option<TowerFace>>>, Option<Vec<i128>>)) -> (usize, usize, Option<String>) {
    let (mut faces, mut entries, mut first) = (0usize, 0usize, None);
    if host.0.len() != card.0.len() {
        return (1, 0, Some(format!("regions {} against {}", host.0.len(), card.0.len())));
    }
    for (r, (h, c)) in host.0.iter().zip(&card.0).enumerate() {
        if h.len() != c.len() {
            faces += 1;
            first.get_or_insert(format!("region {r} sites {} against {}", h.len(), c.len()));
            continue;
        }
        for (t, (hf, cf)) in h.iter().zip(c).enumerate() {
            if hf != cf {
                faces += 1;
                let detail = match (hf, cf) {
                    (Some(a), Some(b)) => {
                        let class = a.masses.iter().zip(&b.masses).position(|(x, y)| x != y);
                        format!("face region {r} site {t} class {class:?} total {} against {}", a.total, b.total)
                    }
                    _ => format!("face region {r} site {t} present {} against {}", hf.is_some(), cf.is_some()),
                };
                first.get_or_insert(detail);
            }
        }
    }
    if let (Some(hg), Some(cg)) = (&host.1, &card.1) {
        for (i, (a, b)) in hg.iter().zip(cg).enumerate() {
            if a != b {
                entries += 1;
                first.get_or_insert(format!("covector {} host {a} card {b}", family_of(field, i)));
            }
        }
        entries += hg.len().abs_diff(cg.len());
    }
    (faces, entries, first)
}

fn ms(ns: u128) -> u128 {
    ns / 1_000_000
}

/// `parity-field UNITS UNITS_SHA TRAIN TRAIN_SHA HELD HELD_SHA KEYS KEYS_SHA D H n STILL f K SECTION
/// SECTIONS RATE GROW RELEASES SWEEPS WITHHELD`: the withheld read on its first `WITHHELD` problems in their
/// keyed order (all of them past their count).
/// [agent-inferred, November 2] Why a sample (Brandon, November 2: two checks of 8 minutes each, every time): the
/// parity reads the card's bits against the host's region by region through the same kernels, so the withheld read's
/// 512 regions check no path that a few of them do not, while the host replays each at about 110 times the card's
/// time (a GSM8K section 8,541 ms against 77); the whole withheld read is each lap's own receipt on the card.
pub(super) fn parity(args: &[String], card: &mut dyn FieldRealization) -> Result<()> {
    if args.len() != 22 {
        return Err("parity-field UNITS UNITS_SHA TRAIN TRAIN_SHA HELD HELD_SHA KEYS KEYS_SHA D H n STILL f K SECTION SECTIONS RATE GROW RELEASES SWEEPS WITHHELD".into());
    }
    let started = std::time::Instant::now();
    let p = passage(&args[1..9], positive(&args[15])?)?;
    let (sections, rate, grow, releases, sweeps) = (positive(&args[16])?, count(&args[17])? as u32, positive(&args[18])?, count(&args[19])?, positive(&args[20])?);
    let withheld = &p.unseen[..positive(&args[21])?.min(p.unseen.len())];
    let mut founded = p.learner(&args[9..15], rate)?;
    if grow > 1 {
        founded = founded.widened(grow, &p.keys).map_err(|e| e.to_string())?;
    }
    // [agent-inferred, November 4, §16.40] Lanes (`FIELD_PARITY_LANE=k`): the founded field grown by `k` fresh lanes
    // ([`FieldLearner::laned`]), so the parity reads every lane's own chart and its adjoint on both realizations (the
    // lanes' reads open at zero and carry their covector from the first section, so every later read meets them).
    if let Some(k) = std::env::var("FIELD_PARITY_LANE").ok().and_then(|v| v.parse::<usize>().ok()) {
        for _ in 0..k {
            founded = founded.laned(&p.keys).map_err(|e| e.to_string())?;
        }
        println!("FIELD_PARITY_LANE lanes={} width={} material={}", founded.field.declaration.lanes, founded.field.declaration.width, founded.field.material_len());
    }
    // [agent-inferred, November 2] A pace far from the founding (`FIELD_PARITY_PACE=s`, §16): every pace entry drawn from
    // the key file's tail, a 32-bit word shifted down `s` bits, so the clocks run off the byte place (fractional,
    // fast, stopping and backward rates) and the parity reads the series between whole places on both realizations.
    if let Some(shift) = std::env::var("FIELD_PARITY_PACE").ok().and_then(|v| v.parse::<u32>().ok()) {
        let (start, len) = (founded.field.layout().pace, founded.field.layout().moment_face - founded.field.layout().pace);
        let tail = p.keys.len().checked_sub(4 * len + 8).ok_or("a key file too short for the pace's draws")?;
        for k in 0..len {
            let word = &p.keys[tail + 4 * k..tail + 4 * k + 4];
            founded.field.theta[start + k] = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) >> shift;
        }
        println!("FIELD_PARITY_PACE shift={shift} entries={len}");
    }
    // [agent-inferred, November 3, the tower record] A tower of scales (`FIELD_PARITY_SCALE=P`): the founded field grown in
    // scale with packets of `P` sites after half its ticks, the packets' field declared as the fine one on the packets'
    // reach, and the prolongation drawn from the key file's tail (its founding opens it at zero, where no covector reaches
    // the packets), so the parity reads every path of the tower on both realizations.
    if let Some(period) = std::env::var("FIELD_PARITY_SCALE").ok().and_then(|v| v.parse::<usize>().ok()).filter(|&p| p > 1) {
        let d = founded.field.declaration;
        let coarse = holonics::hnn::tower::field::FieldDeclaration { alphabet: 2, reach: d.reach.div_ceil(period), ..d };
        let (tower, read) = founded.field.scaled_up(period, (d.ticks / 2).max(1), coarse, &p.keys, founded.drawn).map_err(|e| e.to_string())?;
        founded = holonics::hnn::tower::field::FieldLearner::new(tower, founded.rate_bits);
        founded.drawn = read;
        let s = founded.field.scale.as_deref_mut().ok_or("a tower without its scale")?;
        let (_, _, b, _, len) = s.glue_offsets(d.width);
        let tail = p.keys.len().checked_sub(4 * (len - b) + 8).ok_or("a key file too short for the prolongation's draws")?;
        for (k, v) in s.glue[b..].iter_mut().enumerate() {
            let word = &p.keys[tail + 4 * k..tail + 4 * k + 4];
            *v = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) >> 12;
        }
        println!("FIELD_PARITY_SCALE period={period} split={} coarse_width={} material={}", (d.ticks / 2).max(1), coarse.width, founded.field.material_len());
    }
    let d = founded.field.declaration;
    println!("FIELD_PARITY_DECLARATION width={} heads={} modes={} still={} contacts={} ticks={} frames={} reach={} rate={} material={} grow={grow} withheld_read={}", d.width, d.heads, d.modes, d.still, d.contacts, d.ticks, d.frames, d.reach, founded.rate_bits, founded.field.material_len(), withheld.len());
    let mut host_learner = founded.clone();
    let mut card_learner = founded;
    let order = walk(p.seed, host_learner.laps, p.sections.len());
    let paths = paths_of(p.seed, host_learner.laps, &p.sections);
    let mut draw = host_learner.laps * p.train.len() as u64;
    let (mut reads_unequal, mut faces_unequal, mut entries_unequal, mut learners_unequal, mut reads_all) = (0usize, 0usize, 0usize, 0usize, 0usize);
    let (mut host_ns, mut card_ns) = (0u128, 0u128);
    // The sections, then the withheld problems as a lap's end reads them.
    let steps: Vec<(usize, bool)> = order.iter().take(sections).map(|&s| (s, false)).chain(std::iter::once((usize::MAX, true))).collect();
    for (k, &(s, end)) in steps.iter().enumerate() {
        let (members, along): (&[usize], &[usize]) = if end { (withheld, &[]) } else { (&p.sections[s], &paths[s]) };
        let mut host = HostField;
        let mut host_rec = Recorder { inner: &mut host, reads: Vec::new(), logits: Vec::new() };
        let (mut host_draw, mut card_draw) = (draw, draw);
        let t0 = std::time::Instant::now();
        let (host_regions, host_next) = p.regions(members, along, &mut host_draw, end, &mut host_learner, &mut host_rec)?;
        let host_views = views_of(&host_regions);
        let receipt_h = if end {
            let (_, next) = host_learner.read_step_on(&host_views, &mut host_rec).map_err(|e| e.to_string())?;
            FieldReceipt { next, ..FieldReceipt::default() }
        } else {
            let r = host_learner.section_realized(&host_views, &mut host_rec).map_err(|e| e.to_string())?;
            FieldReceipt { next: host_next.or(r.next), ..r }
        };
        let t1 = std::time::Instant::now();
        let mut card_rec = Recorder { inner: &mut *card, reads: Vec::new(), logits: Vec::new() };
        let (card_regions, card_next) = p.regions(members, along, &mut card_draw, end, &mut card_learner, &mut card_rec)?;
        let card_views = views_of(&card_regions);
        let receipt_c = if end {
            let (_, next) = card_learner.read_step_on(&card_views, &mut card_rec).map_err(|e| e.to_string())?;
            FieldReceipt { next, ..FieldReceipt::default() }
        } else {
            let r = card_learner.section_realized(&card_views, &mut card_rec).map_err(|e| e.to_string())?;
            FieldReceipt { next: card_next.or(r.next), ..r }
        };
        let t2 = std::time::Instant::now();
        if !end {
            draw = host_draw;
        }
        host_ns += (t1 - t0).as_nanos();
        card_ns += (t2 - t1).as_nanos();
        let views = &host_views;
        let rows: usize = views.iter().map(|r| d.heads * r.classes.len()).sum::<usize>() * d.ticks;
        let mut first = if host_regions == card_regions { None } else { Some("the regions differ".to_string()) };
        let (mut faces, mut entries) = (0usize, 0usize);
        let calls = host_rec.reads.len().max(card_rec.reads.len()) + host_rec.logits.len().max(card_rec.logits.len());
        if host_rec.reads.len() != card_rec.reads.len() || host_rec.logits.len() != card_rec.logits.len() {
            first = Some(format!("reads {}+{} against {}+{}", host_rec.reads.len(), host_rec.logits.len(), card_rec.reads.len(), card_rec.logits.len()));
        }
        for (h, c) in host_rec.logits.iter().zip(&card_rec.logits) {
            if h != c {
                faces += 1;
                reads_unequal += 1;
                first.get_or_insert("a logits read differs".to_string());
            }
        }
        for (h, c) in host_rec.reads.iter().zip(&card_rec.reads) {
            let (fu, eu, f) = compare(&host_learner.field, h, c);
            faces += fu;
            entries += eu;
            if fu + eu > 0 {
                reads_unequal += 1;
            }
            if first.is_none() {
                first = f;
            }
        }
        reads_all += calls;
        faces_unequal += faces;
        entries_unequal += entries;
        // The landmarks of a section's first region that carries a lock (else its first region; a
        // masked, read-1 or read-2 region, its last four sites against its first half), read on both.
        let marks_equal = match host_views.iter().find(|r| r.locked.iter().any(|&l| l)).or(host_views.first()) {
            Some(r) if !end => {
                let n = r.classes.len();
                let sites: Vec<usize> = (n.saturating_sub(4)..n).collect();
                host_learner.field.landmarks(r, n / 2, &sites, 3).map_err(|e| e.to_string())? == card.read_landmarks(&card_learner.field, r, n / 2, &sites, 3).map_err(|e| e.to_string())?
            }
            _ => true,
        };
        // The near field by offset of the same region's last four sites, every tick and head (§16.42), host against card.
        let near_equal = match host_views.iter().find(|r| r.locked.iter().any(|&l| l)).or(host_views.first()) {
            Some(r) if !end => {
                let n = r.classes.len();
                let sites: Vec<usize> = (n.saturating_sub(4)..n).collect();
                host_learner.field.near_offsets(r, &sites).map_err(|e| e.to_string())? == card.read_near_offsets(&card_learner.field, r, &sites).map_err(|e| e.to_string())?
            }
            _ => true,
        };
        // The blanks' clocks by tick of the same region's last four sites (§16.44), host against card.
        let clocks_equal = match host_views.iter().find(|r| r.locked.iter().any(|&l| l)).or(host_views.first()) {
            Some(r) if !end => {
                let n = r.classes.len();
                let sites: Vec<usize> = (n.saturating_sub(4)..n).collect();
                host_learner.field.blank_clocks(r, &sites).map_err(|e| e.to_string())? == card.read_blank_clocks(&card_learner.field, r, &sites).map_err(|e| e.to_string())?
            }
            _ => true,
        };
        // The rows by where their mass lies (a reading for the receipts), the section's first regions read on both
        // with the answer start at each region's first open site: bit for bit.
        let rows_equal = {
            let some = &host_views[..host_views.len().min(6)];
            let questions: Vec<usize> = some.iter().map(|r| r.unresolved.iter().position(|&u| u).unwrap_or(r.classes.len())).collect();
            some.is_empty() || host_learner.field.held_rows_all(some, &questions).map_err(|e| e.to_string())? == card.read_row_shares(&card_learner.field, some, &questions).map_err(|e| e.to_string())?
        };
        // The contact covector by where its pairs lie on the same regions (§16.20), host against card.
        let shares_equal = {
            let some = &host_views[..host_views.len().min(6)];
            some.is_empty() || host_learner.field.covector_shares(some).map_err(|e| e.to_string())? == card.read_covector_shares(&card_learner.field, some).map_err(|e| e.to_string())?
        };
        // The held rows' currents by where they come from, with their covectors (§16.21), on the section's first two
        // regions, host against card.
        let currents_equal = {
            let some = &host_views[..host_views.len().min(2)];
            let questions: Vec<usize> = some.iter().map(|r| r.unresolved.iter().position(|&u| u).unwrap_or(r.classes.len())).collect();
            let host: Vec<Vec<RowCurrent>> = some.iter().zip(&questions).map(|(r, &q)| host_learner.field.row_currents(r, q, true)).collect::<std::result::Result<_, _>>().map_err(|e| e.to_string())?;
            some.is_empty() || host == card.read_row_currents(&card_learner.field, some, &questions, true).map_err(|e| e.to_string())?
        };
        let learner_equal = host_regions == card_regions && receipt_h == receipt_c && host_learner.to_text() == card_learner.to_text() && marks_equal && near_equal && clocks_equal && rows_equal && shares_equal && currents_equal;
        learners_unequal += usize::from(!learner_equal);
        let length = views.iter().map(|r| r.classes.len()).max().unwrap_or(0);
        let next = receipt_h.next.map_or("-".to_string(), |n| format!("{}/{}/{}", n.change, n.halvings, n.refused));
        println!(
            "FIELD_PARITY section={} withheld={end} regions={} length={length} sites={} rows={rows} reads={calls} faces_unequal={faces} covector_unequal={entries} first={} deposited={} halvings={} next={next} learner_equal={learner_equal} near_equal={near_equal} clocks_equal={clocks_equal} rows_equal={rows_equal} shares_equal={shares_equal} currents_equal={currents_equal} pace_nonzero={} kappa={} host_ms={} card_ms={}",
            k + 1,
            views.len(),
            receipt_h.sites,
            first.unwrap_or_else(|| "-".into()),
            receipt_h.deposited,
            receipt_h.halvings,
            { let l = host_learner.field.layout(); host_learner.field.theta[l.pace..l.moment_face].iter().filter(|&&v| v != 0).count() },
            host_views.first().and_then(|r| host_learner.field.pace_range(r).ok().flatten()).map_or("-".to_string(), |(lo, hi)| format!("{}..{}", (lo as i128 * 1000) >> 24, (hi as i128 * 1000) >> 24)),
            ms((t1 - t0).as_nanos()),
            ms((t2 - t1).as_nanos())
        );
    }
    // [agent-inferred, November 3, §16.27] The writer through both: the same keyed draws on faces that must agree, so
    // each answer's places agree class for class.
    let questions: Vec<(&[usize], usize)> = p.held.iter().take(releases).map(|(q, _, _)| (q.as_slice(), p.codec.answer)).collect();
    let t0 = std::time::Instant::now();
    let carded = card_learner.field.sample_realized(&questions, sweeps, 0, p.codec.void(), p.seed, card, &mut |_, _| true).map_err(|e| e.to_string())?;
    let card_release_ms = ms(t0.elapsed().as_nanos());
    let t0 = std::time::Instant::now();
    let hosted = host_learner.field.sample_realized(&questions, sweeps, 0, p.codec.void(), p.seed, &mut HostField, &mut |_, _| true).map_err(|e| e.to_string())?;
    let mut releases_unequal = 0usize;
    for (i, (h, c)) in hosted.iter().zip(&carded).enumerate() {
        let equal = h == c;
        releases_unequal += usize::from(!equal);
        println!("FIELD_PARITY_WRITE problem={i} question={} places={} written={} equal={equal}", questions[i].0.len(), h.len(), h.iter().filter(|&&k| k != p.codec.void()).count());
    }
    println!("FIELD_PARITY_WRITES problems={} sweeps={sweeps} host_ms={}", hosted.len(), ms(t0.elapsed().as_nanos()));
    println!(
        "FIELD_PARITY_DONE sections={} reads={reads_all} reads_unequal={reads_unequal} faces_unequal={faces_unequal} covector_unequal={entries_unequal} learners_unequal={learners_unequal} releases={} releases_unequal={releases_unequal} card_release_ms={card_release_ms} host_ms={} card_ms={} elapsed_ms={}",
        steps.len(),
        releases.min(p.held.len()),
        ms(host_ns),
        ms(card_ns),
        started.elapsed().as_millis()
    );
    if reads_unequal + learners_unequal + releases_unequal > 0 {
        return Err("the card's field is not the host's".into());
    }
    Ok(())
}

/// The site rows a write reads: every sweep reads the question and every answer place once.
fn release_rows(heads: usize, ticks: usize, sweeps: usize, sites: usize) -> u128 {
    (heads * ticks * sweeps) as u128 * sites as u128
}

/// `time-field UNITS UNITS_SHA TRAIN TRAIN_SHA HELD HELD_SHA KEYS KEYS_SHA D H n STILL f K SECTION
/// SECTIONS RATE RELEASES SWEEPS`: the card alone over the opening sections of the founded field's
/// first lap and its opening writes ([`Field::sample_realized`]); each section's time and site pairs, and the lap and
/// the held problems' writes projected from the largest time a site pair measured.
pub(super) fn time(args: &[String], card: &mut dyn FieldRealization) -> Result<()> {
    if args.len() != 20 {
        return Err("time-field UNITS UNITS_SHA TRAIN TRAIN_SHA HELD HELD_SHA KEYS KEYS_SHA D H n STILL f K SECTION SECTIONS RATE RELEASES SWEEPS".into());
    }
    let started = std::time::Instant::now();
    let p = passage(&args[1..9], positive(&args[15])?)?;
    let (sections, rate, releases, sweeps) = (positive(&args[16])?, count(&args[17])? as u32, count(&args[18])?, positive(&args[19])?);
    let mut learner = p.learner(&args[9..15], rate)?;
    let d = learner.field.declaration;
    println!("FIELD_TIME_DECLARATION width={} heads={} modes={} still={} contacts={} ticks={} reach={} material={}", d.width, d.heads, d.modes, d.still, d.contacts, d.ticks, d.reach, learner.field.theta.len());
    // The whole lap's site pairs (one read and return a section), from the regions' lengths.
    let order = walk(p.seed, learner.laps, p.sections.len());
    let paths = paths_of(p.seed, learner.laps, &p.sections);
    let mut lengths_draw = learner.laps * p.train.len() as u64;
    let lengths: Vec<usize> = order.iter().flat_map(|&s| region_lengths(&p.codec, &p.train, &p.sections[s], &paths[s], p.seed, &mut lengths_draw)).collect();
    let lap_pairs: u128 = lengths.iter().map(|&l| (d.heads * l) as u128).sum::<u128>() * d.ticks as u128;
    let lap_sites: usize = lengths.iter().sum();
    let mut worst = (0u128, 1u128); // the largest ns a row as (ns, rows) of a section's reads and return
    let mut read_worst = (0u128, 1u128); // the same of one read of the section's regions
    let mut met_worst = (0u128, 1u128); // the most pairs met a row in one read, as (pairs, rows)
    let all_pairs: u128 = lengths.iter().map(|&l| (d.heads * l * l) as u128).sum::<u128>() * d.ticks as u128;
    let mut draw = learner.laps * p.train.len() as u64;
    for (k, &s) in order.iter().take(sections).enumerate() {
        let mut rec = Recorder { inner: &mut *card, reads: Vec::new(), logits: Vec::new() };
        let t0 = std::time::Instant::now();
        let (regions, next) = p.regions(&p.sections[s], &paths[s], &mut draw, false, &mut learner, &mut rec)?;
        let views = views_of(&regions);
        let pairs: u128 = views.iter().map(|r| (d.heads * r.classes.len()) as u128).sum::<u128>() * d.ticks as u128;
        let receipt = learner.section_realized(&views, &mut rec).map_err(|e| e.to_string())?;
        let receipt = FieldReceipt { next: next.or(receipt.next), ..receipt };
        let ns = t0.elapsed().as_nanos();
        let reads = rec.reads.len() as u128;
        if ns * worst.1 > worst.0 * pairs {
            worst = (ns, pairs);
        }
        // One read of the section's regions alone: the held step's read on the next section and
        // the certificate may each read them twice more than a step that stands at its size
        // (`scaled`, the one bounded law of a step's size).
        let t1 = std::time::Instant::now();
        let met_before = card.met_pairs().unwrap_or(0);
        card.read_faces(&learner.field, &views).map_err(|e| e.to_string())?;
        let read_ns = t1.elapsed().as_nanos();
        let met = card.met_pairs().unwrap_or(0) - met_before;
        if read_ns * read_worst.1 > read_worst.0 * pairs {
            read_worst = (read_ns, pairs);
        }
        if met * met_worst.1 > met_worst.0 * pairs {
            met_worst = (met, pairs);
        }
        let length = views.iter().map(|r| r.classes.len()).max().unwrap_or(0);
        let next = receipt.next.map_or("-".to_string(), |n| format!("{}/{}", n.halvings, n.refused));
        println!("FIELD_TIME section={} length={length} rows={pairs} met_pairs={met} reads={reads} halvings={} deposited={} next={next} ms={} ns_a_row={} read_ms={}", k + 1, receipt.halvings, receipt.deposited, ms(ns), ns / pairs.max(1), ms(read_ns));
    }
    let sections_lap = p.sections.len();
    // The lap's end: the held step read on the withheld problems (its opening read and at most four
    // more, `scaled`) and the held-out read, each region read with its neighbours (§13).
    let square = |lengths: &mut dyn Iterator<Item = usize>| -> u128 { lengths.map(|l| l as u128).sum::<u128>() * (d.heads * d.ticks) as u128 };
    let end_pairs = 5 * square(&mut unseen_regions(&p.codec, &p.train, &p.unseen, p.seed).iter().map(|(c, _)| c.len())) + square(&mut held_regions(&p.codec, &p.held).iter().map(|(c, _, _)| c.len()));
    // The upper bound of a lap: every section at the worst measured section time a pair, four more
    // reads of it at the worst measured read time a pair (the most the held step's read and the
    // certificate add to a section whose steps stand at their size; the second reading's projection
    // lacked them), the held step's read of each section problem as one context region (§15.11: one region a
    // problem, of the problem's own length, read once a section, `section_regions`), and the lap's end at the same
    // read time a pair. [agent-inferred, November 2] The measured sections run `section_regions`, so their time
    // already holds that read once; it is counted again here at the worst read time a pair, an upper bound.
    let context_rows = lap_pairs;
    println!(
        "FIELD_TIME_LAP sections={sections_lap} sites={lap_sites} rows={lap_pairs} end_rows={end_pairs} context_rows={context_rows} worst_ps_a_section_row={} worst_ps_a_read_row={} at_size_ms={} context_ms={} projection_ms={} (every section's reads and return at the worst measured time a site row, four more reads of it, the held step's context read, and the lap's end)",
        1000 * worst.0 / worst.1.max(1),
        1000 * read_worst.0 / read_worst.1.max(1),
        ms(lap_pairs * worst.0 / worst.1.max(1)),
        ms(context_rows * read_worst.0 / read_worst.1.max(1)),
        ms(lap_pairs * worst.0 / worst.1.max(1) + (4 * lap_pairs + context_rows + end_pairs) * read_worst.0 / read_worst.1.max(1))
    );
    // The pairs a lap's one read of every section meets, projected from the most met a row at the
    // opening sections, beside the pairs every site reading every other would read (reading 8's
    // 31.0 × 10⁹): a row's support follows the learned classes, so the projection is the opening's.
    println!("FIELD_TIME_PAIRS lap_met_pairs={} met_pairs_a_row_millis={} all_pairs={all_pairs}", lap_pairs * met_worst.0 / met_worst.1.max(1), 1000 * met_worst.0 / met_worst.1.max(1));
    // [agent-inferred, November 3, §16.27] The writes: the opening held problems' answers written together over `SWEEPS`
    // sweeps and timed, every sweep a read of every problem's whole region; the held set's writes projected from the
    // largest time a row measured, the same sweeps over every held problem at its whole region.
    let questions: Vec<(&[usize], usize)> = p.held.iter().take(releases).map(|(q, _, _)| (q.as_slice(), p.codec.answer)).collect();
    let mut counted = Counted { inner: &mut *card, rows: 0 };
    let t0 = std::time::Instant::now();
    let written = learner.field.sample_realized(&questions, sweeps, 0, p.codec.void(), p.seed, &mut counted, &mut |_, _| true).map_err(|e| e.to_string())?;
    let ns = t0.elapsed().as_nanos();
    let release_worst = (ns, counted.rows.max(1));
    println!(
        "FIELD_TIME_WRITE problems={} places={} written={} sweeps={sweeps} rows_read={} ms={}",
        questions.len(),
        written.iter().map(Vec::len).sum::<usize>(),
        written.iter().flatten().filter(|&&k| k != p.codec.void()).count(),
        counted.rows,
        ms(ns)
    );
    let held_pairs: u128 = p.held.iter().map(|(q, _, _)| release_rows(d.heads, d.ticks, sweeps, q.len() + p.codec.answer)).sum();
    println!(
        "FIELD_TIME_WRITES problems={} sweeps={sweeps} rows_at_most={held_pairs} ps_a_row={} projection_ms={}",
        p.held.len(),
        1000 * release_worst.0 / release_worst.1.max(1),
        ms(held_pairs * release_worst.0 / release_worst.1.max(1))
    );
    println!("FIELD_TIME_DONE elapsed_ms={}", started.elapsed().as_millis());
    Ok(())
}
