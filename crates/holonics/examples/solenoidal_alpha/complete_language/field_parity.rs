//! The field's card realization read against the host's (`holonics-cuda`'s `field_pass`), on the
//! sections `train-field` forms (record `2026-11-01_THE_PROBLEM_IS_ONE_FIELD…`, §7 and §8's acceptance
//! 2).
//!
//! `parity-field` founds the field as `train-field` does (and widens it by `GROW` when `GROW > 1`)
//! and has two learners, one through the host ([`HostField`]) and one through the card, each form
//! and take the first `SECTIONS` sections of its next lap exactly as `train-field` does (the keyed
//! walk, tails and shapes, the front regions' read 2 carrying faces read from its own field and
//! their locks), then read its held step on the withheld problems as a lap's end does. Every read
//! each makes (the masks' reads, the held step's reads, the section's read and return, and each of the
//! certificate's rereads) is compared face for face (each unresolved site's masses and total) and
//! covector entry for entry, and the regions and the learners' texts after each section; then the
//! field releases the first `RELEASES` held problems through both, `SWEEPS` sweeps each, the card's
//! read together, each release compared whole (its sites, the sweep each was reached and locked, the
//! extent's reading, lock rungs, rungs ridden, circulation and last mixtures).
//! `time-field` reads the card alone over the opening sections and the opening releases and
//! projects a lap from the measured upper time a site pair, and the held problems' releases from that
//! time and the sweeps the front's measured speed gives.

use super::field_train::{extent_text, held_regions, locks_of, problems_of, question_text, region_lengths, section_regions, sections_of, unseen_regions, units_of, views_of, walk, FieldCodec, Problems, TrainRegion};
use super::tower_train::{count, positive};
use super::*;
use holonics::hnn::tower::field::{Field, FieldDeclaration, FieldLearner, FieldNext, FieldRead, FieldRealization, FieldReceipt, HeldRows, HostField, Region, ReleaseSweep, RowCurrent};
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
    /// A section's regions as `train-field` forms them from `draw` on, read through `realization`
    /// after `learner`'s held step is read on them (its read returned); with `withheld`, the withheld
    /// problems `members` read with their neighbours (the held step then read by the caller).
    fn regions(&self, members: &[usize], draw: &mut u64, withheld: bool, learner: &mut FieldLearner, realization: &mut dyn FieldRealization) -> Result<(Vec<TrainRegion>, Option<FieldNext>)> {
        if withheld {
            return Ok((unseen_regions(&self.codec, &self.train, members, self.seed).into_iter().map(|(c, u)| TrainRegion::plain(c, u)).collect(), None));
        }
        section_regions(&self.codec, &self.train, members, self.seed, draw, learner, realization)
    }

    /// The founded learner of the declaration `D H n STILL f K` at `RATE`.
    fn learner(&self, args: &[String], rate: u32) -> Result<FieldLearner> {
        let (width, heads, modes, still, contacts, ticks) = (positive(&args[0])?, positive(&args[1])?, positive(&args[2])?, count(&args[3])?, positive(&args[4])?, positive(&args[5])?);
        let declaration = FieldDeclaration { alphabet: self.codec.alphabet(), width, heads, modes, still, contacts, ticks, frames: heads, reach: self.reach };
        Ok(FieldLearner::new(Field::found(declaration, &self.keys).map_err(|e| e.to_string())?, rate))
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
    for (n, &(start, len, _)) in field.families().iter().enumerate() {
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
    let d = founded.field.declaration;
    println!("FIELD_PARITY_DECLARATION width={} heads={} modes={} still={} contacts={} ticks={} frames={} reach={} rate={} material={} grow={grow} withheld_read={}", d.width, d.heads, d.modes, d.still, d.contacts, d.ticks, d.frames, d.reach, founded.rate_bits, founded.field.theta.len(), withheld.len());
    let mut host_learner = founded.clone();
    let mut card_learner = founded;
    let order = walk(p.seed, host_learner.laps, p.sections.len());
    let mut draw = host_learner.laps * p.train.len() as u64;
    let (mut reads_unequal, mut faces_unequal, mut entries_unequal, mut learners_unequal, mut reads_all) = (0usize, 0usize, 0usize, 0usize, 0usize);
    let (mut host_ns, mut card_ns) = (0u128, 0u128);
    // The sections, then the withheld problems as a lap's end reads them.
    let steps: Vec<(usize, bool)> = order.iter().take(sections).map(|&s| (s, false)).chain(std::iter::once((usize::MAX, true))).collect();
    for (k, &(s, end)) in steps.iter().enumerate() {
        let members = if end { withheld } else { &p.sections[s] };
        let mut host = HostField;
        let mut host_rec = Recorder { inner: &mut host, reads: Vec::new(), logits: Vec::new() };
        let (mut host_draw, mut card_draw) = (draw, draw);
        let t0 = std::time::Instant::now();
        let (host_regions, host_next) = p.regions(members, &mut host_draw, end, &mut host_learner, &mut host_rec)?;
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
        let (card_regions, card_next) = p.regions(members, &mut card_draw, end, &mut card_learner, &mut card_rec)?;
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
        let learner_equal = host_regions == card_regions && receipt_h == receipt_c && host_learner.to_text() == card_learner.to_text() && marks_equal && rows_equal && shares_equal && currents_equal;
        learners_unequal += usize::from(!learner_equal);
        let length = views.iter().map(|r| r.classes.len()).max().unwrap_or(0);
        let next = receipt_h.next.map_or("-".to_string(), |n| format!("{}/{}/{}", n.change, n.halvings, n.refused));
        println!(
            "FIELD_PARITY section={} withheld={end} regions={} length={length} sites={} rows={rows} reads={calls} faces_unequal={faces} covector_unequal={entries} first={} deposited={} halvings={} next={next} learner_equal={learner_equal} rows_equal={rows_equal} shares_equal={shares_equal} currents_equal={currents_equal} pace_nonzero={} kappa={} host_ms={} card_ms={}",
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
    let mut releases_unequal = 0usize;
    let questions: Vec<(&[usize], usize)> = p.held.iter().take(releases).map(|(q, _, _)| (q.as_slice(), p.codec.answer)).collect();
    let t0 = std::time::Instant::now();
    let carded = card_learner.field.release_realized(&questions, sweeps, p.codec.void(), card, &mut |_| true).map_err(|e| e.to_string())?;
    let card_release_ms = ms(t0.elapsed().as_nanos());
    for (i, (&(q, open), carded)) in questions.iter().zip(&carded).enumerate() {
        let t0 = std::time::Instant::now();
        let host = host_learner.field.release(q, open, sweeps, p.codec.void()).map_err(|e| e.to_string())?;
        // The landmarks of every content site, read from the last state on both.
        let unresolved: Vec<bool> = host.faces.iter().map(Option::is_some).collect();
        let locked = locks_of(&host);
        let region = Region { classes: &host.classes, unresolved: &unresolved, faces: &host.faces, locked: &locked, echo: &[], domain: None, port: None };
        let sites: Vec<usize> = (host.start..host.start + host.sites.len()).collect();
        let marks_equal = sites.is_empty() || host_learner.field.landmarks(&region, q.len(), &sites, 3).map_err(|e| e.to_string())? == card.read_landmarks(&card_learner.field, &region, q.len(), &sites, 3).map_err(|e| e.to_string())?;
        let equal = &host == carded && marks_equal;
        releases_unequal += usize::from(!equal);
        println!(
            "FIELD_PARITY_RELEASE problem={i} question={} released={} reached={} open={} extent={} free={} bound={} equal={equal} landmarks_equal={marks_equal} host_ms={}",
            q.len(),
            host.sites.len(),
            host.reached.iter().flatten().count(),
            host.open,
            extent_text(host.extent),
            host.free,
            host.bound,
            ms(t0.elapsed().as_nanos())
        );
    }
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

/// The site rows a release reads at most: every sweep reads the question and the open answer once
/// (a region released short of its void reads fewer).
fn release_rows(heads: usize, ticks: usize, sweeps: usize, sites: usize) -> u128 {
    (heads * ticks * sweeps) as u128 * sites as u128
}

/// `time-field UNITS UNITS_SHA TRAIN TRAIN_SHA HELD HELD_SHA KEYS KEYS_SHA D H n STILL f K SECTION
/// SECTIONS RATE RELEASES SWEEPS`: the card alone over the opening sections of the founded field's
/// first lap and its opening free releases; each section's and release's time and site pairs, and the
/// lap and the held problems' releases (free and at each calculation's equals) projected from the
/// largest time a site pair measured. [definition; agent-inferred, November 1] **The release's sweeps
/// are the front's** (the dispersing field's §14.9): a release's front moves at most five sites a
/// sweep and only where a site has locked, so the sweeps a release runs are not a bound chosen but
/// its answer's extent over the front's speed. The speed of an opening release is the sites its front
/// reached over the sweeps it ran (a release that ended, up to the sweep of its last lock or its
/// extent's reading; one that did not, all it ran), the void site where it locked on the void counted
/// among the sites, and the projection takes the slowest of them, the upper end: `⌈A · sweeps /
/// reached⌉` sweeps for the codec's answer extent `A`. Why the slowest and not the mean: the deadline
/// is the projection's upper end, and a release past it is reported incomplete, never run again with
/// more.
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
    let mut lengths_draw = learner.laps * p.train.len() as u64;
    let lengths: Vec<usize> = order.iter().flat_map(|&s| region_lengths(&p.codec, &p.train, &p.sections[s], p.seed, &mut lengths_draw)).collect();
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
        let (regions, next) = p.regions(&p.sections[s], &mut draw, false, &mut learner, &mut rec)?;
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
    // The releases: the free releases of the opening held problems, read together and timed, and
    // the pairs they read counted; the projection reads every held problem's free release and one at
    // each calculation's equals, each at most the full region every sweep for the sweeps the front's
    // measured speed gives, at the time a pair the opening releases measured on the pairs they read.
    // (The third reading's projection divided by the pairs a release reads at most; a founded field
    // that releases its void at once reads few, so its time a pair, and the projection from it, came
    // out a sixth of the one it bounded.)
    let questions: Vec<(&[usize], usize)> = p.held.iter().take(releases).map(|(q, _, _)| (q.as_slice(), p.codec.answer)).collect();
    let mut counted = Counted { inner: &mut *card, rows: 0 };
    let mut last = ReleaseSweep::default();
    let t0 = std::time::Instant::now();
    let released = learner.field.release_realized(&questions, sweeps, p.codec.void(), &mut counted, &mut |sweep| {
        last = *sweep;
        true
    });
    let released = released.map_err(|e| e.to_string())?;
    let ns = t0.elapsed().as_nanos();
    let pairs: u128 = questions.iter().map(|&(q, open)| release_rows(d.heads, d.ticks, sweeps, q.len() + open)).sum();
    let release_worst = (ns, counted.rows.max(1));
    // The front's speed on each opening release: the sites its front reached over the sweeps it ran.
    let answer = p.codec.answer as u128;
    let speeds: Vec<(u128, u128)> = released
        .iter()
        .map(|r| {
            let reached = r.reached.iter().flatten().count() + usize::from(matches!(r.extent, Some((_, _, false))));
            let ended = r.open == 0 && r.extent.is_some();
            let ran = if ended { r.lock_sweeps.iter().flatten().copied().chain(r.extent.map(|(_, sweep, _)| sweep)).max().map_or(1, |s| s + 1) } else { last.done.max(1) };
            (reached.max(1) as u128, ran as u128)
        })
        .collect();
    let projected = speeds.iter().map(|&(reached, ran)| (answer * ran).div_ceil(reached)).max().unwrap_or(sweeps as u128).max(1);
    let slowest = speeds.iter().map(|&(reached, ran)| 1000 * reached / ran).min().unwrap_or(0);
    println!(
        "FIELD_TIME_RELEASE problems={} released={} reached={} open={} sweeps_run={} front={} ended={} rows_at_most={pairs} rows_read={} ms={}",
        questions.len(),
        released.iter().map(|r| r.sites.len()).sum::<usize>(),
        released.iter().map(|r| r.reached.iter().flatten().count()).sum::<usize>(),
        released.iter().map(|r| r.open).sum::<usize>(),
        last.done,
        last.front,
        released.iter().filter(|r| r.open == 0 && r.extent.is_some()).count(),
        counted.rows,
        ms(ns)
    );
    let held_text = pinned_read(&args[5], &args[6], READ_BUDGET as usize)?;
    let held_problems = problems_of(&held_text);
    // One sweep of each set at most (both its reads, every region at its full length).
    let (mut free_pairs, mut marks_pairs) = (0u128, 0u128);
    let mut held_releases = 0usize;
    for (question, answer) in &held_problems {
        let q = p.codec.encode(&question_text(question)).map_err(|e| e.to_string())?;
        free_pairs += release_rows(d.heads, d.ticks, 1, q.len() + p.codec.answer);
        held_releases += 1;
        // Each calculation's equals: the question and the answer through it, the rest opened.
        let mut at = 0usize;
        while let Some(off) = answer[at..].windows(2).position(|w| w == b"<<") {
            let close = answer[at + off..].windows(2).position(|w| w == b">>").map_or(answer.len(), |c| at + off + c);
            if let Some(eq) = answer[at + off..close].iter().position(|&b| b == b'=') {
                let prefix = p.codec.encode(&answer[..at + off + eq + 1]).map_err(|e| e.to_string())?.len();
                let open = p.codec.answer.saturating_sub(prefix).max(1);
                marks_pairs += release_rows(d.heads, d.ticks, 1, q.len() + prefix + open);
                held_releases += 1;
            }
            at = close.max(at + off + 2);
        }
    }
    // A sweep's time at most, each set's, at the projected sweeps: a release's deadline is fixed from
    // them. The rows are the full region every sweep, an upper bound (a sweep reads the question, the
    // reached sites and five past the front); the time a row is the opening releases' measured one.
    let at_worst = |pairs: u128| ms(pairs * release_worst.0 / release_worst.1.max(1));
    let held_pairs = projected * (free_pairs + marks_pairs);
    println!(
        "FIELD_TIME_RELEASES problems={} releases={held_releases} sweeps={sweeps} answer={answer} front_sites_a_sweep_millis={slowest} projected_sweeps={projected} rows_at_most={held_pairs} ps_a_row={} free_sweep_ms={} marks_sweep_ms={} projection_ms={}",
        held_problems.len(),
        1000 * release_worst.0 / release_worst.1.max(1),
        at_worst(free_pairs),
        at_worst(marks_pairs),
        at_worst(held_pairs)
    );
    println!("FIELD_TIME_DONE elapsed_ms={}", started.elapsed().as_millis());
    Ok(())
}
