//! The field's card realization read against the host's (`holonics-cuda`'s `field_pass`), on the
//! sections `train-field` forms (record `2026-11-01_THE_PROBLEM_IS_ONE_FIELD…`, §7 and §8's acceptance
//! 2).
//!
//! `parity-field` founds the field as `train-field` does (and widens it by `GROW` when `GROW > 1`)
//! and has two learners, one through the host ([`HostField`]) and one through the card, each form
//! and take the first `SECTIONS` sections of its next lap exactly as `train-field` does (the keyed
//! walk, tails and shapes, the release-state masks read from its own field), then read its held
//! step on the withheld problems as a lap's end does. Every read each makes (the masks' reads, the
//! held step's reads, the section's read and return, and each of the certificate's rereads) is
//! compared face for face (each unresolved site's masses and total) and covector entry for entry,
//! and the regions and the learners' texts after each section; then the field releases the first
//! `RELEASES` held problems through both, `SWEEPS` sweeps each, the card's read together.
//! `time-field` reads the card alone over the opening sections and the opening releases and
//! projects a lap and a release of the held problems from the measured upper time a site pair.

use super::field_train::{problems_of, question_text, region_lengths, section_regions, sections_of, units_of, walk, FieldCodec, Problems, UNSEEN_DRAW};
use super::tower_train::{count, positive};
use super::*;
use holonics::hnn::tower::field::{Field, FieldDeclaration, FieldLearner, FieldRealization, FieldReceipt, HostField, Region};
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
    /// Section `s`'s regions as `train-field` forms them from `draw` on, read from `learner`'s field
    /// through `realization` (or the withheld problems' at the release's states).
    fn regions(&self, members: &[usize], draw: &mut u64, released: bool, learner: &FieldLearner, realization: &mut dyn FieldRealization) -> Result<Vec<(Vec<usize>, Vec<bool>)>> {
        section_regions(&self.codec, &self.train, members, self.seed, draw, released, &learner.field, realization)
    }

    /// The founded learner of the declaration `D H n STILL f K` at `RATE`.
    fn learner(&self, args: &[String], rate: u32) -> Result<FieldLearner> {
        let (width, heads, modes, still, contacts, ticks) = (positive(&args[0])?, positive(&args[1])?, positive(&args[2])?, count(&args[3])?, positive(&args[4])?, positive(&args[5])?);
        let declaration = FieldDeclaration { alphabet: self.codec.alphabet(), width, heads, modes, still, contacts, ticks, frames: heads, reach: self.reach };
        Ok(FieldLearner::new(Field::found(declaration, &self.keys).map_err(|e| e.to_string())?, rate))
    }
}

/// A realization whose every read is kept beside its result, so two learners' reads are compared.
struct Recorder<'a> {
    inner: &'a mut dyn FieldRealization,
    reads: Vec<(Vec<Vec<Option<TowerFace>>>, Option<Vec<i128>>)>,
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
}

const FAMILIES: [&str; 17] = ["enc", "q", "q_bias", "k", "k_bias", "v", "v_bias", "out", "out_bias", "a", "a_bias", "b", "b_bias", "w", "w_bias", "read", "read_bias"];

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
/// SECTIONS RATE GROW RELEASES SWEEPS`.
pub(super) fn parity(args: &[String], card: &mut dyn FieldRealization) -> Result<()> {
    if args.len() != 21 {
        return Err("parity-field UNITS UNITS_SHA TRAIN TRAIN_SHA HELD HELD_SHA KEYS KEYS_SHA D H n STILL f K SECTION SECTIONS RATE GROW RELEASES SWEEPS".into());
    }
    let started = std::time::Instant::now();
    let p = passage(&args[1..9], positive(&args[15])?)?;
    let (sections, rate, grow, releases, sweeps) = (positive(&args[16])?, count(&args[17])? as u32, positive(&args[18])?, count(&args[19])?, positive(&args[20])?);
    let mut founded = p.learner(&args[9..15], rate)?;
    if grow > 1 {
        founded = founded.widened(grow, &p.keys).map_err(|e| e.to_string())?;
    }
    let d = founded.field.declaration;
    println!("FIELD_PARITY_DECLARATION width={} heads={} modes={} still={} contacts={} ticks={} frames={} reach={} rate={} material={} grow={grow}", d.width, d.heads, d.modes, d.still, d.contacts, d.ticks, d.frames, d.reach, founded.rate_bits, founded.field.theta.len());
    let mut host_learner = founded.clone();
    let mut card_learner = founded;
    let order = walk(p.seed, host_learner.laps, p.sections.len());
    let mut draw = host_learner.laps * p.train.len() as u64;
    let (mut reads_unequal, mut faces_unequal, mut entries_unequal, mut learners_unequal, mut reads_all) = (0usize, 0usize, 0usize, 0usize, 0usize);
    let (mut host_ns, mut card_ns) = (0u128, 0u128);
    // The sections, then the withheld problems as a lap's end reads them.
    let steps: Vec<(usize, bool)> = order.iter().take(sections).map(|&s| (s, false)).chain(std::iter::once((usize::MAX, true))).collect();
    for (k, &(s, end)) in steps.iter().enumerate() {
        let members = if end { &p.unseen } else { &p.sections[s] };
        let mut host = HostField;
        let mut host_rec = Recorder { inner: &mut host, reads: Vec::new() };
        let (mut host_draw, mut card_draw) = if end { (UNSEEN_DRAW, UNSEEN_DRAW) } else { (draw, draw) };
        let t0 = std::time::Instant::now();
        let host_regions = p.regions(members, &mut host_draw, end, &host_learner, &mut host_rec)?;
        let host_views: Vec<Region> = host_regions.iter().map(|(c, u)| Region { classes: c, unresolved: u }).collect();
        let receipt_h = if end {
            let (_, next) = host_learner.read_step_on(&host_views, &mut host_rec).map_err(|e| e.to_string())?;
            FieldReceipt { next, ..FieldReceipt::default() }
        } else {
            host_learner.section_realized(&host_views, &mut host_rec).map_err(|e| e.to_string())?
        };
        let t1 = std::time::Instant::now();
        let mut card_rec = Recorder { inner: &mut *card, reads: Vec::new() };
        let card_regions = p.regions(members, &mut card_draw, end, &card_learner, &mut card_rec)?;
        let card_views: Vec<Region> = card_regions.iter().map(|(c, u)| Region { classes: c, unresolved: u }).collect();
        let receipt_c = if end {
            let (_, next) = card_learner.read_step_on(&card_views, &mut card_rec).map_err(|e| e.to_string())?;
            FieldReceipt { next, ..FieldReceipt::default() }
        } else {
            card_learner.section_realized(&card_views, &mut card_rec).map_err(|e| e.to_string())?
        };
        let t2 = std::time::Instant::now();
        if !end {
            draw = host_draw;
        }
        host_ns += (t1 - t0).as_nanos();
        card_ns += (t2 - t1).as_nanos();
        let views = &host_views;
        let pairs: usize = views.iter().map(|r| d.heads * r.classes.len() * r.classes.len()).sum::<usize>() * d.ticks;
        let mut first = if host_regions == card_regions { None } else { Some("the regions differ".to_string()) };
        let (mut faces, mut entries) = (0usize, 0usize);
        let calls = host_rec.reads.len().max(card_rec.reads.len());
        if host_rec.reads.len() != card_rec.reads.len() {
            first = Some(format!("reads {} against {}", host_rec.reads.len(), card_rec.reads.len()));
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
        let learner_equal = host_regions == card_regions && receipt_h == receipt_c && host_learner.to_text() == card_learner.to_text();
        learners_unequal += usize::from(!learner_equal);
        let length = views.iter().map(|r| r.classes.len()).max().unwrap_or(0);
        let next = receipt_h.next.map_or("-".to_string(), |n| format!("{}/{}/{}", n.change, n.halvings, n.refused));
        println!(
            "FIELD_PARITY section={} withheld={end} regions={} length={length} sites={} pairs={pairs} reads={calls} faces_unequal={faces} covector_unequal={entries} first={} deposited={} halvings={} next={next} learner_equal={learner_equal} host_ms={} card_ms={}",
            k + 1,
            views.len(),
            receipt_h.sites,
            first.unwrap_or_else(|| "-".into()),
            receipt_h.deposited,
            receipt_h.halvings,
            ms((t1 - t0).as_nanos()),
            ms((t2 - t1).as_nanos())
        );
    }
    let mut releases_unequal = 0usize;
    let questions: Vec<(&[usize], usize)> = p.held.iter().take(releases).map(|(q, _, _)| (q.as_slice(), p.codec.answer)).collect();
    let t0 = std::time::Instant::now();
    let carded = card_learner.field.release_realized(&questions, sweeps, p.codec.void(), card).map_err(|e| e.to_string())?;
    let card_release_ms = ms(t0.elapsed().as_nanos());
    for (i, (&(q, open), carded)) in questions.iter().zip(&carded).enumerate() {
        let t0 = std::time::Instant::now();
        let host = host_learner.field.release(q, open, sweeps, p.codec.void()).map_err(|e| e.to_string())?;
        let equal = &host == carded;
        releases_unequal += usize::from(!equal);
        println!("FIELD_PARITY_RELEASE problem={i} question={} released={} equal={equal} host_ms={}", q.len(), host.len(), ms(t0.elapsed().as_nanos()));
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

/// The site pairs a release reads at most: every sweep reads the question and the open answer
/// twice, with the question and without it (a region released short of its void reads fewer).
fn release_pairs(heads: usize, ticks: usize, sweeps: usize, sites: usize) -> u128 {
    (2 * heads * ticks * sweeps) as u128 * (sites * sites) as u128
}

/// `time-field UNITS UNITS_SHA TRAIN TRAIN_SHA HELD HELD_SHA KEYS KEYS_SHA D H n STILL f K SECTION
/// SECTIONS RATE RELEASES SWEEPS`: the card alone over the opening sections of the founded field's
/// first lap and its opening free releases; each section's and release's time and site pairs, and the
/// lap and the held problems' releases (free and at each calculation's equals) projected from the
/// largest time a site pair measured.
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
    let lap_pairs: u128 = lengths.iter().map(|&l| (d.heads * l * l) as u128).sum::<u128>() * d.ticks as u128;
    let lap_sites: usize = lengths.iter().sum();
    let mut worst = (0u128, 1u128); // the largest ms a pair as (ns, pairs) of a section's read and return
    let mut reads_worst = (0u128, 1u128);
    let mut draw = learner.laps * p.train.len() as u64;
    for (k, &s) in order.iter().take(sections).enumerate() {
        let mut rec = Recorder { inner: &mut *card, reads: Vec::new() };
        let t0 = std::time::Instant::now();
        let regions = p.regions(&p.sections[s], &mut draw, false, &learner, &mut rec)?;
        let views: Vec<Region> = regions.iter().map(|(c, u)| Region { classes: c, unresolved: u }).collect();
        let pairs: u128 = views.iter().map(|r| (d.heads * r.classes.len() * r.classes.len()) as u128).sum::<u128>() * d.ticks as u128;
        let receipt = learner.section_realized(&views, &mut rec).map_err(|e| e.to_string())?;
        let ns = t0.elapsed().as_nanos();
        let reads = rec.reads.len() as u128;
        if ns * worst.1 > worst.0 * pairs {
            worst = (ns, pairs);
        }
        // A section's time over its reads' pairs (its return and each reread read its pairs once).
        if ns * reads_worst.1 > reads_worst.0 * pairs * reads {
            reads_worst = (ns, pairs * reads);
        }
        let length = views.iter().map(|r| r.classes.len()).max().unwrap_or(0);
        println!("FIELD_TIME section={} length={length} pairs={pairs} reads={reads} halvings={} deposited={} ms={} ns_a_pair={}", k + 1, receipt.halvings, receipt.deposited, ms(ns), ns / pairs.max(1));
    }
    let sections_lap = p.sections.len();
    println!(
        "FIELD_TIME_LAP sections={sections_lap} sites={lap_sites} pairs={lap_pairs} worst_ns_a_section_pair={} projection_ms={} (the section's read, return and rereads at the worst measured time a pair)",
        worst.0 / worst.1.max(1),
        ms(lap_pairs * worst.0 / worst.1.max(1))
    );
    // The releases: the free releases of the opening held problems, read together and timed; the
    // projection reads every held problem's free release and one at each calculation's equals, each
    // at most the full region, at the time a pair the opening releases measured.
    let questions: Vec<(&[usize], usize)> = p.held.iter().take(releases).map(|(q, _, _)| (q.as_slice(), p.codec.answer)).collect();
    let t0 = std::time::Instant::now();
    let released = learner.field.release_realized(&questions, sweeps, p.codec.void(), card).map_err(|e| e.to_string())?;
    let ns = t0.elapsed().as_nanos();
    let pairs: u128 = questions.iter().map(|&(q, open)| release_pairs(d.heads, d.ticks, sweeps, q.len() + open)).sum();
    let release_worst = (ns, pairs.max(1));
    println!("FIELD_TIME_RELEASE problems={} released={} pairs_at_most={pairs} ms={}", questions.len(), released.iter().map(Vec::len).sum::<usize>(), ms(ns));
    let held_text = pinned_read(&args[5], &args[6], READ_BUDGET as usize)?;
    let held_problems = problems_of(&held_text);
    let mut held_pairs = 0u128;
    let mut held_releases = 0usize;
    for (question, answer) in &held_problems {
        let q = p.codec.encode(&question_text(question)).map_err(|e| e.to_string())?;
        held_pairs += release_pairs(d.heads, d.ticks, sweeps, q.len() + p.codec.answer);
        held_releases += 1;
        // Each calculation's equals: the question and the answer through it, the rest opened.
        let mut at = 0usize;
        while let Some(off) = answer[at..].windows(2).position(|w| w == b"<<") {
            let close = answer[at + off..].windows(2).position(|w| w == b">>").map_or(answer.len(), |c| at + off + c);
            if let Some(eq) = answer[at + off..close].iter().position(|&b| b == b'=') {
                let prefix = p.codec.encode(&answer[..at + off + eq + 1]).map_err(|e| e.to_string())?.len();
                let open = p.codec.answer.saturating_sub(prefix).max(1);
                held_pairs += release_pairs(d.heads, d.ticks, sweeps, q.len() + prefix + open);
                held_releases += 1;
            }
            at = close.max(at + off + 2);
        }
    }
    println!(
        "FIELD_TIME_RELEASES problems={} releases={held_releases} sweeps={sweeps} pairs_at_most={held_pairs} worst_ns_a_pair={} projection_ms={}",
        held_problems.len(),
        release_worst.0 / release_worst.1.max(1),
        ms(held_pairs * release_worst.0 / release_worst.1.max(1))
    );
    println!("FIELD_TIME_DONE elapsed_ms={}", started.elapsed().as_millis());
    Ok(())
}
