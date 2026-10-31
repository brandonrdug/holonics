//! **The opening's omitted return, read on the card, and the credit's return beside it** (October
//! 30 and 31; record `2026-10-30_THE_COARSE_LEVEL_HEADS_FOR_THE_TRACE_OF_WHAT_COMES_NEXT…`, §21 and
//! §22, acceptance 40; Refs #404 #406). A training section reads its covector from its carried
//! opening, so whatever B's faces would return into the cells before that opening is omitted; the
//! clocked levels' credit (`LevelCredit`) carries the part of it its moments hold. On a saved
//! learner, for a handful of streams and two consecutive spans A then B:
//!
//! ```text
//! g_B   = B's covector from B's carried opening, as training reads it (compared = None)
//! g_AB  = B's covector over A then B, A's places compared with nothing, so only B's faces send
//!         a covector and it returns through A's cells
//! g_AB − g_B = the opening's omitted return
//! g_Bc  = B's covector from the same opening carrying the credit, opened at rest at A's opening
//!         and carried through A section by section as training carries it
//! g_Bc − g_B = the credit's return; g_AB − g_Bc what it leaves
//! ```
//!
//! Per level and family, `‖g_AB − g_B‖ / ‖g_B‖` and the cosine of `g_AB` with `g_B`, and
//! `‖g_AB − g_Bc‖ / ‖g_AB − g_B‖` and the cosine of the credit's return with the omitted return, in
//! thousandths (exact integer sums of squares and products, the square root to the floor), beside
//! each level's slowest span `1/(1 − |λ|)` in its own ticks, for each declared length of A in
//! sections.
//!
//! `opening_return STATE STATE_SHA CLASSES CLASSES_SHA STREAMS SECTION B HANDFUL LENGTHS`: the
//! passage two bytes a class (big-endian), split into `STREAMS` streams as training splits it; the
//! `HANDFUL` streams `j · STREAMS / HANDFUL`; B is section `B` of each; `LENGTHS` the lengths of A in
//! sections, comma-separated. Every stream opens at rest and is carried section by section on the
//! card under the saved material, so every opening is the contemporary constitution's. Two checks
//! print beside the readings: B's faces read after A equal B's faces read from its carried opening
//! (the carry is the same state), and B's covector with every place compared equals it with
//! `compared = None`. A reading beside the bits: it trains nothing and decides nothing.
#![allow(clippy::disallowed_methods, clippy::disallowed_types, reason = "explicit exterior CLI file/process boundary")]

use holonics::hnn::tower::realization::{PassRealization, Slot};
use holonics::hnn::tower::{TowerLearner, TowerState, MOVE_BITS};
use holonics_cuda::hnn::{Card, TowerCard};
use num_bigint::{BigInt, BigUint};
use num_traits::Zero;
use std::collections::BTreeMap;
use std::error::Error;
use std::process::Command;
use std::time::Instant;

type Result<T> = std::result::Result<T, Box<dyn Error>>;

/// A file read whole, refused unless its SHA-256 is the declared one (`sha256sum`, the exterior's).
fn pinned(path: &str, sha: &str) -> Result<Vec<u8>> {
    let output = Command::new("sha256sum").arg(path).output()?;
    let digest = std::str::from_utf8(&output.stdout)?.split_whitespace().next().unwrap_or("").to_owned();
    if !output.status.success() || digest != sha {
        return Err(format!("{path}: sha256 {digest} is not the declared {sha}").into());
    }
    Ok(std::fs::read(path)?)
}

fn count(s: &str) -> Result<usize> {
    Ok(s.parse()?)
}

/// One family group's sums: `Σ g_B²`, `Σ (g_AB − g_B)²`, `Σ g_AB g_B`, `Σ g_AB²`, and of the
/// credit's return `r = g_Bc − g_B` against the omitted `d = g_AB − g_B`: `Σ (d − r)²`, `Σ r d`,
/// `Σ r²`.
#[derive(Default)]
struct Sums {
    entries: usize,
    b2: BigInt,
    d2: BigInt,
    ab: BigInt,
    a2: BigInt,
    left2: BigInt,
    rd: BigInt,
    r2: BigInt,
}

impl Sums {
    fn add(&mut self, a: i128, b: i128, c: i128) {
        let (a, b, c) = (BigInt::from(a), BigInt::from(b), BigInt::from(c));
        let d = &a - &b;
        let r = &c - &b;
        let left = &d - &r;
        self.entries += 1;
        self.b2 += &b * &b;
        self.d2 += &d * &d;
        self.ab += &a * &b;
        self.a2 += &a * &a;
        self.left2 += &left * &left;
        self.rd += &r * &d;
        self.r2 += &r * &r;
    }

    fn join(&mut self, o: &Sums) {
        self.entries += o.entries;
        self.b2 += &o.b2;
        self.d2 += &o.d2;
        self.ab += &o.ab;
        self.a2 += &o.a2;
        self.left2 += &o.left2;
        self.rd += &o.rd;
        self.r2 += &o.r2;
    }

    /// `‖g_AB − g_Bc‖ / ‖g_AB − g_B‖` in thousandths, to the floor: what the credit leaves of the
    /// omitted return; `None` where nothing is omitted.
    fn left(&self) -> Option<BigUint> {
        (!self.d2.is_zero()).then(|| (&self.left2 * BigInt::from(1_000_000u32) / &self.d2).magnitude().sqrt())
    }

    /// The cosine of the credit's return with the omitted return in thousandths, toward zero.
    fn carried(&self) -> Option<BigInt> {
        let root = (&self.r2 * &self.d2).magnitude().sqrt();
        (!root.is_zero()).then(|| &self.rd * BigInt::from(1000u32) / BigInt::from(root))
    }

    /// `‖g_AB − g_B‖ / ‖g_B‖` in thousandths, to the floor; `None` where `g_B` is zero.
    fn ratio(&self) -> Option<BigUint> {
        (!self.b2.is_zero()).then(|| (&self.d2 * BigInt::from(1_000_000u32) / &self.b2).magnitude().sqrt())
    }

    /// The cosine of `g_AB` with `g_B` in thousandths, toward zero; `None` where either is zero.
    fn cosine(&self) -> Option<BigInt> {
        let root = (&self.a2 * &self.b2).magnitude().sqrt();
        (!root.is_zero()).then(|| &self.ab * BigInt::from(1000u32) / BigInt::from(root))
    }

    /// `log₂ ‖g_B‖`, to the floor, so families of different grains can be told apart by size.
    fn b_octave(&self) -> Option<u64> {
        (!self.b2.is_zero()).then(|| self.b2.magnitude().sqrt().bits() - 1)
    }
}

fn show<T: ToString>(v: Option<T>) -> String {
    v.map_or("none".into(), |v| v.to_string())
}

fn main() -> Result<()> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.len() != 9 {
        return Err("opening_return STATE STATE_SHA CLASSES CLASSES_SHA STREAMS SECTION B HANDFUL LENGTHS".into());
    }
    let started = Instant::now();
    let learner = TowerLearner::from_text(std::str::from_utf8(&pinned(&args[0], &args[1])?)?)?;
    let tower = &learner.tower;
    let bytes = pinned(&args[2], &args[3])?;
    if bytes.len() % 2 != 0 {
        return Err("a class passage of two bytes a class".into());
    }
    let classes: Vec<usize> = bytes.chunks(2).map(|b| u16::from_be_bytes([b[0], b[1]]) as usize).collect();
    let (streams, section, b, handful) = (count(&args[4])?, count(&args[5])?, count(&args[6])?, count(&args[7])?);
    let lengths: Vec<usize> = args[8].split(',').map(count).collect::<Result<_>>()?;
    let chunk = classes.len() / streams;
    let longest = lengths.iter().copied().max().unwrap_or(0);
    if handful == 0 || handful > streams || lengths.contains(&0) || longest > b || (chunk - 1) / section <= b {
        return Err("each A at least one section and no longer than B's place, B inside every stream".into());
    }
    let chosen: Vec<usize> = (0..handful).map(|j| j * streams / handful).collect();
    let part = |s: usize, from: usize, to: usize| &classes[s * chunk + from * section..s * chunk + to * section + 1];
    let opened = Card::open(0)?;
    let mut card = TowerCard::open(&opened)?;
    card.admit(tower)?;
    // The credit's carry runs on a realization of its own, which holds it resident.
    let mut credited = TowerCard::open(&opened)?;
    println!(
        "OPENING_RETURN_OPEN material={} levels={} news_first={} streams={streams} section={section} B={b} handful={handful} chosen={chosen:?} lengths={lengths:?} card={}",
        tower.theta.len(),
        tower.declaration.levels,
        show(tower.news().map(|c| c.first())),
        opened.census().name
    );

    // Each stream from rest, carried section by section on the card; the openings A needs kept.
    let mut states: Vec<TowerState> = chosen.iter().map(|_| tower.rest()).collect();
    let mut openings: BTreeMap<usize, Vec<TowerState>> = BTreeMap::new();
    let carry_started = Instant::now();
    for k in 0..b {
        if lengths.iter().any(|&m| b - m == k) {
            openings.insert(k, states.clone());
        }
        let parts: Vec<&[usize]> = chosen.iter().map(|&s| part(s, k, k + 1)).collect();
        let targets: Vec<Vec<Option<usize>>> = parts.iter().map(|p| p[1..].iter().map(|&c| Some(c)).collect()).collect();
        let opening = states.clone();
        card.forward(tower, &opening, &parts, &targets, Slot::Opened)?.admitted(&targets)?;
        card.carry(tower, &mut states, &opening, Slot::Opened)?;
    }
    println!("OPENING_RETURN_CARRIED sections={b} ms={}", carry_started.elapsed().as_millis());

    // B from its carried opening, as training reads it, and again with every place compared.
    let parts_b: Vec<&[usize]> = chosen.iter().map(|&s| part(s, b, b + 1)).collect();
    let targets_b: Vec<Vec<Option<usize>>> = parts_b.iter().map(|p| p[1..].iter().map(|&c| Some(c)).collect()).collect();
    let read_b = card.forward(tower, &states, &parts_b, &targets_b, Slot::Opened)?.admitted(&targets_b)?;
    let g_b = card.reverse(tower, &states, &parts_b, None)?;
    let every: Vec<Vec<Option<usize>>> = parts_b.iter().map(|p| p.iter().map(|&c| Some(c)).collect()).collect();
    let every_slices: Vec<&[Option<usize>]> = every.iter().map(Vec::as_slice).collect();
    let g_every = card.reverse(tower, &states, &parts_b, Some(&every_slices))?;
    println!("OPENING_RETURN_CHECK compared_every_equals_none={}", g_every == g_b);

    let named = tower.named_families();
    let spans: Vec<i128> = tower.slowest_distances().iter().map(|&d| ((1i128 << MOVE_BITS) + d / 2) / d).collect();
    for (l, span) in spans.iter().enumerate() {
        println!("OPENING_RETURN_SPAN level={l} slowest_span_ticks={span}");
    }

    for &m in &lengths {
        let t0 = Instant::now();
        let opening = &openings[&(b - m)];
        let parts: Vec<&[usize]> = chosen.iter().map(|&s| part(s, b - m, b + 1)).collect();
        // A's places compared with nothing (its last place is B's first class, which B alone
        // does not compare either); B's places compared with their classes.
        let compared: Vec<Vec<Option<usize>>> = parts.iter().map(|p| p.iter().enumerate().map(|(i, &c)| (i > m * section).then_some(c)).collect()).collect();
        let targets: Vec<Vec<Option<usize>>> = compared.iter().map(|c| c[1..].to_vec()).collect();
        let read = card.forward(tower, opening, &parts, &targets, Slot::Opened)?.admitted(&targets)?;
        let faces_equal = read.faces.iter().zip(&read_b.faces).all(|(ab, bb)| ab[m * section..] == bb[..]);
        let slices: Vec<&[Option<usize>]> = compared.iter().map(Vec::as_slice).collect();
        let g_ab = card.reverse(tower, opening, &parts, Some(&slices))?;
        // The credit opened at rest at A's opening and carried through A section by section, then
        // B read from the same opening with it.
        let rest = tower.rest_with_credit().credit;
        let mut carried: Vec<TowerState> = opening.iter().map(|o| TowerState { credit: rest.clone(), ..o.clone() }).collect();
        for k in b - m..b {
            let parts_k: Vec<&[usize]> = chosen.iter().map(|&s| part(s, k, k + 1)).collect();
            let targets_k: Vec<Vec<Option<usize>>> = parts_k.iter().map(|p| p[1..].iter().map(|&c| Some(c)).collect()).collect();
            let open_k = carried.clone();
            credited.forward(tower, &open_k, &parts_k, &targets_k, Slot::Opened)?.admitted(&targets_k)?;
            credited.carry(tower, &mut carried, &open_k, Slot::Opened)?;
        }
        let read_c = credited.forward(tower, &carried, &parts_b, &targets_b, Slot::Opened)?.admitted(&targets_b)?;
        let credit_faces_equal = read_c.faces == read_b.faces;
        let g_bc = credited.reverse(tower, &carried, &parts_b, None)?;
        // Per level and family, in the layout's order.
        let mut groups: Vec<((Option<usize>, &'static str), Sums)> = Vec::new();
        for (level, name, range) in &named {
            let key = (*level, *name);
            if !groups.iter().any(|(k, _)| *k == key) {
                groups.push((key, Sums::default()));
            }
            let sums = &mut groups.iter_mut().find(|(k, _)| *k == key).expect("pushed above").1;
            for i in range.clone() {
                sums.add(g_ab[i], g_b[i], g_bc[i]);
            }
        }
        println!("OPENING_RETURN_A sections={m} faces_of_B_equal={faces_equal} credited_faces_of_B_equal={credit_faces_equal} ms={}", t0.elapsed().as_millis());
        let mut levels: BTreeMap<Option<usize>, Sums> = BTreeMap::new();
        let mut whole = Sums::default();
        for ((level, name), sums) in &groups {
            println!(
                "OPENING_RETURN A={m} level={} family={name} entries={} gB_octave={} omitted_over_gB_thousandths={} cosine_thousandths={} credit_left_over_omitted_thousandths={} credit_cosine_thousandths={}",
                show(*level),
                sums.entries,
                show(sums.b_octave()),
                show(sums.ratio()),
                show(sums.cosine()),
                show(sums.left()),
                show(sums.carried())
            );
            levels.entry(*level).or_default().join(sums);
            whole.join(sums);
        }
        for (level, sums) in &levels {
            let span = level.and_then(|l| spans.get(l)).copied();
            println!(
                "OPENING_RETURN_LEVEL A={m} level={} slowest_span_ticks={} omitted_over_gB_thousandths={} cosine_thousandths={} credit_left_over_omitted_thousandths={} credit_cosine_thousandths={}",
                show(*level),
                show(span),
                show(sums.ratio()),
                show(sums.cosine()),
                show(sums.left()),
                show(sums.carried())
            );
        }
        println!("OPENING_RETURN_WHOLE A={m} omitted_over_gB_thousandths={} cosine_thousandths={} credit_left_over_omitted_thousandths={} credit_cosine_thousandths={}", show(whole.ratio()), show(whole.cosine()), show(whole.left()), show(whole.carried()));
    }
    let times = card.times();
    println!(
        "OPENING_RETURN_DONE card_forwards={} card_forward_ms={} card_reverses={} card_reverse_ms={} elapsed_ms={}",
        times.forwards,
        times.forward_ns / 1_000_000,
        times.reverses,
        times.reverse_ns / 1_000_000,
        started.elapsed().as_millis()
    );
    Ok(())
}
