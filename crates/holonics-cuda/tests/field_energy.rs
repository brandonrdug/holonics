//! [measurement] **The energy field's forward on the card returns the host's bits** (`holonics::hnn::tower::field::energy`,
//! `holonics_cuda::hnn::CardField::energy_read`): each region's faces (the energy's total derivative, through the reverse over
//! the ticks and the opening), logits and energy read (the opening's and the last
//! tick's energy, every tick's halvings, the reads and the site pairs met), on the tiny `energetic` fixtures of every ring
//! set (open, carried and locked sites, regions of several lengths read in one batch), and on a founding of the line's
//! declaration on a synthetic region of 1,500 sites, timed against the host; each under both opening laws of the state (the
//! own row `E(u_t)` and the letters' force, `Field::opened_at_force`). Run alone under the card's lock:
//! `flock -w 900 .local/gpu.lock cargo test --release -p holonics-cuda --test field_energy -- --include-ignored --test-threads=1`.
use std::time::Instant;

use holonics::hnn::tower::field::{EnergyLead, EnergyRead, EnergySquare, Field, FieldDeclaration, FieldRealization, Region, Shares};
use rayon::prelude::*;
use holonics::hnn::tower::TowerFace;
use holonics_cuda::hnn::{Card, CardField};

/// An exterior integer mixer's words from a seed (the host fixtures' draws, `field/tests.rs`).
fn mixer(seed: u64) -> impl FnMut() -> u64 {
    let mut s = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ 0xD1B5_4A32_D192_ED03;
    move || {
        s = s.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = s;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
}

/// `n` draws of four bytes of the fixtures' key stream.
fn keys(n: usize) -> Vec<u8> {
    let mut next = mixer(0x5EED);
    (0..n.div_ceil(2)).flat_map(|_| next().to_be_bytes()).take(4 * n).collect()
}

fn tiny_declaration(still: usize) -> FieldDeclaration {
    FieldDeclaration { alphabet: 5, width: 8, heads: 2, modes: 3, still, contacts: 4, ticks: 2, frames: 2, reach: 16, lanes: 1, depth: 0, energy: true }
}

/// The host's `energetic` fixture rebuilt: every family drawn from the fixture key stream as `shaped` draws it (a uniform
/// draw on `[−½, ½)` of its family's grain), the pace rows and the families the energy does not read (`V`, `b_v`, `O`, `b_o`,
/// `W_c`, `b_c`) at zero.
fn energetic(still: usize) -> Field {
    energetic_with(tiny_declaration(still))
}

/// The host's `shaped_with`: a founding with every family drawn from the fixture key stream, a uniform draw on `[−½, ½)` of its
/// family's grain.
fn shaped_with(d: FieldDeclaration) -> Field {
    let mut field = Field::found(d, &keys(1 << 14)).unwrap();
    let stream = keys(1 << 15);
    let families = field.layout().families.clone();
    for (n, v) in field.theta.iter_mut().enumerate() {
        let word = &stream[4 * n..4 * n + 4];
        let k = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) as i64;
        let grain = families.iter().find(|(s, l, _)| (*s..*s + *l).contains(&n)).unwrap().2;
        *v = ((k << grain) >> 32) as i32;
    }
    field
}

/// [`energetic`] on a declaration of the caller's (its families laid out as the tiny declaration's).
fn energetic_with(d: FieldDeclaration) -> Field {
    let mut field = shaped_with(d);
    let (l, d) = (field.layout().clone(), field.declaration);
    let (dw, m2) = (d.width, 2 * d.complex());
    field.theta[l.pace..l.pace + d.paced_heads() * (d.alphabet + 1)].fill(0);
    for (start, len) in [(l.v, m2 * dw), (l.v_bias, m2), (l.out, dw * m2), (l.out_bias, dw), (l.w, dw * d.contacts), (l.w_bias, dw)] {
        field.theta[start..start + len].fill(0);
    }
    field
}

/// A field under each opening law of the state: its own (`E(u_t)` at a site, which retires once the force opening's claim is
/// judged) and the letters' force (`Field::opened_at_force`, theory November 9 03:56), each named for the receipt.
fn openings(field: Field) -> [(&'static str, Field); 2] {
    let force = field.opened_at_force().unwrap();
    [("own", field), ("force", force)]
}

/// A region's owned parts.
struct Owned {
    classes: Vec<usize>,
    unresolved: Vec<bool>,
    faces: Vec<Option<Shares>>,
    locked: Vec<bool>,
}

impl Owned {
    fn region(&self) -> Region<'_> {
        Region { classes: &self.classes, unresolved: &self.unresolved, faces: &self.faces, locked: &self.locked, echo: &[], domain: None, port: None }
    }
}

/// The tiny regions: the host's `region()` (open sites), the same with a carried site (a listener) and a locked one, and a
/// longer region with every kind.
fn tiny_regions() -> Vec<Owned> {
    let classes = vec![1, 4, 0, 2, 2, 3, 1];
    let open = vec![false, true, false, true, false, false, true];
    let plain = Owned { classes: classes.clone(), unresolved: open.clone(), faces: Vec::new(), locked: Vec::new() };
    let mut faces: Vec<Option<Shares>> = vec![None; 7];
    faces[1] = Some(vec![(0, 40_000), (3, 25_536)]);
    faces[3] = Some(vec![(2, 1 << 16)]);
    let mut locked = vec![false; 7];
    locked[3] = true;
    let carried = Owned { classes, unresolved: open, faces, locked };
    let long_classes: Vec<usize> = (0..13).map(|t| (t * 3 + t / 4) % 5).collect();
    let long_open: Vec<bool> = (0..13).map(|t| t % 3 == 1 || t >= 10).collect();
    let mut long_faces: Vec<Option<Shares>> = vec![None; 13];
    long_faces[4] = Some(vec![(1, 30_000), (2, 20_000), (4, 15_536)]);
    long_faces[10] = Some(vec![(3, 50_000), (0, 15_536)]);
    long_faces[7] = Some(vec![(4, 1 << 16)]);
    let mut long_locked = vec![false; 13];
    long_locked[7] = true;
    vec![plain, carried, Owned { classes: long_classes, unresolved: long_open, faces: long_faces, locked: long_locked }]
}

/// The host's faces, logits and energy reads of each region (`Field::energy_logits`).
#[allow(clippy::type_complexity)]
fn host(field: &Field, regions: &[Region]) -> (Vec<Vec<Option<TowerFace>>>, Vec<Vec<Option<Vec<i64>>>>, Vec<EnergyRead>) {
    let (mut faces, mut logits, mut reads) = (Vec::new(), Vec::new(), Vec::new());
    for region in regions {
        let (z, read) = field.energy_logits(region).unwrap();
        faces.push(z.iter().map(|z| z.as_ref().map(|z| field.tempered(z, 1))).collect());
        logits.push(z);
        reads.push(read);
    }
    (faces, logits, reads)
}

/// The first place two reads differ, for the receipt.
fn first_difference(host: &(Vec<Vec<Option<TowerFace>>>, Vec<Vec<Option<Vec<i64>>>>, Vec<EnergyRead>), card: &(Vec<Vec<Option<TowerFace>>>, Vec<Vec<Option<Vec<i64>>>>, Vec<EnergyRead>)) -> Option<String> {
    for (r, (h, c)) in host.2.iter().zip(&card.2).enumerate() {
        if h != c {
            return Some(format!("region {r}: energy read host {h:?} card {c:?}"));
        }
    }
    for (r, (h, c)) in host.1.iter().zip(&card.1).enumerate() {
        for (t, (hz, cz)) in h.iter().zip(c).enumerate() {
            if hz != cz {
                return Some(format!("region {r} site {t}: logits host {hz:?} card {cz:?}"));
            }
        }
    }
    for (r, (h, c)) in host.0.iter().zip(&card.0).enumerate() {
        if h != c {
            return Some(format!("region {r}: faces differ"));
        }
    }
    (host.2.len() != card.2.len() || host.1.len() != card.1.len()).then(|| "the reads' counts differ".to_string())
}

/// [measurement] **The tiny energy fields' forward on the card is the host's, bit for bit**: on every ring set, each of the
/// three regions read alone and all three in one batch (their ticks in lockstep, each at its own halvings), through the
/// energy read and through the realization's faces and logits, under each opening law.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_tiny_energy_forward_on_the_card_is_the_hosts() {
    let opened = Card::open(0).unwrap();
    let mut card = CardField::open(&opened).unwrap();
    let owned = tiny_regions();
    let regions: Vec<Region> = owned.iter().map(Owned::region).collect();
    for (still, (opening, field)) in (0..=2).flat_map(|still| openings(energetic(still)).map(|f| (still, f))) {
        let reference = host(&field, &regions);
        for (r, region) in regions.iter().enumerate() {
            let alone = card.energy_read(&field, std::slice::from_ref(region)).unwrap();
            let expected = (vec![reference.0[r].clone()], vec![reference.1[r].clone()], vec![reference.2[r].clone()]);
            let diff = first_difference(&expected, &alone);
            println!("ENERGY_PARITY tiny opening={opening} still={still} region={r} sites={} bit_equal={} read={:?}", region.classes.len(), diff.is_none(), alone.2[0]);
            assert!(diff.is_none(), "opening {opening} still {still} region {r}: {}", diff.unwrap_or_default());
        }
        let batch = card.energy_read(&field, &regions).unwrap();
        let diff = first_difference(&reference, &batch);
        println!("ENERGY_PARITY tiny opening={opening} still={still} batch regions={} bit_equal={}", regions.len(), diff.is_none());
        assert!(diff.is_none(), "opening {opening} still {still} batch: {}", diff.unwrap_or_default());
        // The realization's faces and logits are the energy forward's.
        assert_eq!(card.read_faces(&field, &regions).unwrap(), reference.0, "opening {opening} still {still}: the realization's faces");
        let read = card.read_logits(&field, &regions).unwrap();
        for (r, fr) in read.iter().enumerate() {
            assert_eq!(fr.logits, reference.1[r], "opening {opening} still {still} region {r}: the realization's logits");
            assert!(fr.echo.iter().all(|&e| e == 0), "an energy read carries no echo");
        }
        // Training is refused: the return through the ticks is not built.
        assert!(card.read_and_return(&field, &regions).is_err(), "opening {opening} still {still}: an energy field's return is refused on the card");
    }
}

/// [measurement] **A tiny energy field ticked long, with a region at rest, is the host's on the card**: twenty-four ticks on
/// every ring set, the three regions and a fourth in one batch. The fourth is known throughout and of a class whose rows of
/// the encoding, the strand contacts and the moments are zero, with the moment's bias at zero, so its state opens at zero,
/// its chart's scale is zero and its step moves nothing: it rests at its first tick (no read counted) while the others tick
/// on, each at its own halvings.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn a_tiny_energy_forward_ticked_long_with_a_region_at_rest_is_the_hosts() {
    let opened = Card::open(0).unwrap();
    let mut card = CardField::open(&opened).unwrap();
    let mut owned = tiny_regions();
    owned.push(Owned { classes: vec![0; 7], unresolved: vec![false; 7], faces: Vec::new(), locked: Vec::new() });
    let regions: Vec<Region> = owned.iter().map(Owned::region).collect();
    for still in 0..=2 {
        let mut field = energetic_with(FieldDeclaration { ticks: 24, ..tiny_declaration(still) });
        let (l, d) = (field.layout().clone(), field.declaration);
        let tm2 = 2 * d.moment_modes();
        for (start, width) in [(l.enc, d.width), (l.before, d.width), (l.after, d.width), (l.moment_before, tm2), (l.moment_after, tm2)] {
            field.theta[start..start + width].fill(0);
        }
        field.theta[l.moment_face_bias..l.moment_face_bias + d.width].fill(0);
        let reference = host(&field, &regions);
        let before = card.times().energy_rereads;
        let batch = card.energy_read(&field, &regions).unwrap();
        let diff = first_difference(&reference, &batch);
        for (r, read) in batch.2.iter().enumerate() {
            println!("ENERGY_PARITY long still={still} region={r} bit_equal={} halvings={:?} reads={}", diff.is_none(), read.halvings, read.reads);
        }
        println!("ENERGY_PARITY long still={still} rereads={}", card.times().energy_rereads - before);
        assert!(diff.is_none(), "still {still}: {}", diff.unwrap_or_default());
        assert_eq!((reference.2[3].halvings.as_slice(), reference.2[3].reads), (&[None][..], 1), "still {still}: the region at zero rests at its first tick");
        assert!(reference.2[..3].iter().all(|r| r.halvings.len() == 24), "still {still}: the other regions tick on");
    }
}

/// [measurement] **A letters-only energy ticked to its minimum is the host's on the card**: the key and probe charts, the pair
/// drives and the lift's matrix at zero, so each site's energy is linear in its chart read and its descent converges on
/// the sphere; past its minimum a step moves the state along its own chart read (the energy unchanged) and no halving
/// certifies a fall, so the regions rest, at different ticks. Since `MOST_HALVINGS` was retired (November 8), a region
/// rests when its step moves nothing, not when it exhausts 24 halvings, so this descent no longer makes a tick's last
/// states be read again (rereads 0, every region's bits the host's).
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn a_letters_only_energy_ticked_to_its_minimum_is_the_hosts() {
    let opened = Card::open(0).unwrap();
    let mut card = CardField::open(&opened).unwrap();
    let owned = tiny_regions();
    let regions: Vec<Region> = owned.iter().map(Owned::region).collect();
    let mut rested = 0usize;
    for still in 0..=2 {
        let mut field = energetic_with(FieldDeclaration { ticks: 48, ..tiny_declaration(still) });
        let (l, d) = (field.layout().clone(), field.declaration);
        let (dw, m2, f) = (d.width, 2 * d.complex(), d.contacts);
        for (start, len) in [(l.q, m2 * dw), (l.q_bias, m2), (l.probe, m2 * dw), (l.probe_bias, m2), (l.a, f * dw), (l.a_bias, f), (l.b, f * dw), (l.b_bias, f), (l.read, dw * dw)] {
            field.theta[start..start + len].fill(0);
        }
        let reference = host(&field, &regions);
        let before = card.times().energy_rereads;
        let batch = card.energy_read(&field, &regions).unwrap();
        let diff = first_difference(&reference, &batch);
        for (r, read) in batch.2.iter().enumerate() {
            println!("ENERGY_PARITY letters still={still} region={r} bit_equal={} halvings={:?} reads={}", diff.is_none(), read.halvings, read.reads);
        }
        rested += reference.2.iter().filter(|r| r.halvings.last().is_some_and(Option::is_none)).count();
        println!("ENERGY_PARITY letters still={still} rereads={}", card.times().energy_rereads - before);
        assert!(diff.is_none(), "still {still}: {}", diff.unwrap_or_default());
    }
    let rereads = card.times().energy_rereads;
    println!("ENERGY_PARITY letters rested={rested} rereads={rereads}");
    assert!(rested > 0, "the letters' descent reached no rest ({rested}; rereads {rereads})");
}

/// [measurement] **The field's training return on the card is still the host's** beside the energy forward: on the tiny
/// declaration read through its readout (every family drawn, `shaped_with`), the faces and the whole covector of the
/// three regions, on every ring set; the moments' return to the strands is shared with the energy face's moment part.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_tiny_fields_return_on_the_card_is_still_the_hosts() {
    let opened = Card::open(0).unwrap();
    let mut card = CardField::open(&opened).unwrap();
    let owned = tiny_regions();
    let regions: Vec<Region> = owned.iter().map(Owned::region).collect();
    for still in 0..=2 {
        let field = shaped_with(FieldDeclaration { energy: false, ..tiny_declaration(still) });
        let (faces, g) = field.read_and_return(&regions).unwrap();
        let (card_faces, card_g) = card.read_and_return(&field, &regions).unwrap();
        let equal = faces == card_faces && g == card_g;
        println!("FIELD_RETURN_PARITY tiny still={still} regions={} bit_equal={equal} covector_nonzero={}", regions.len(), g.iter().filter(|&&v| v != 0).count());
        assert!(equal, "still {still}: the card's return differs from the host's");
    }
}

/// The line's declaration (`hnn-field-v15 100 32 4 8 2 32 4 4 3771 1 0 1`).
fn line_declaration() -> FieldDeclaration {
    FieldDeclaration { alphabet: 100, width: 32, heads: 4, modes: 8, still: 2, contacts: 32, ticks: 4, frames: 4, reach: 3771, lanes: 1, depth: 0, energy: true }
}

/// A synthetic region of `sites` sites over the alphabet: the first two thirds known (classes from the key stream), the
/// last third open, every seventh open site carrying a face of three classes (a listener) and every eleventh a locked face.
fn synthetic(sites: usize, alphabet: usize) -> Owned {
    let mut next = mixer(0xE4E2);
    let classes: Vec<usize> = (0..sites).map(|_| (next() % alphabet as u64) as usize).collect();
    let known = 2 * sites / 3;
    let unresolved: Vec<bool> = (0..sites).map(|t| t >= known).collect();
    let mut faces: Vec<Option<Shares>> = vec![None; sites];
    let mut locked = vec![false; sites];
    for t in known..sites {
        let k = t - known;
        if k % 11 == 5 {
            faces[t] = Some(vec![(classes[t] as u32, 1 << 16)]);
            locked[t] = true;
        } else if k % 7 == 3 {
            let (a, b, c) = (classes[t] as u32, ((classes[t] + 17) % alphabet) as u32, ((classes[t] + 41) % alphabet) as u32);
            faces[t] = Some(vec![(a, 36_000), (b, 20_000), (c, 9_536)]);
        }
    }
    Owned { classes, unresolved, faces, locked }
}

/// [measurement] **The line's founding on a 1,500-site region: the card's energy forward is the host's, bit for bit**, with
/// the card's time (cold, then warm) beside the host's, under each opening law (the profiled read at the letters' force).
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_lines_energy_forward_on_the_card_is_the_hosts_at_1500_sites() {
    let d = line_declaration();
    let opened = Card::open(0).unwrap();
    for (opening, field) in openings(Field::found(d, &keys(d.founding_draws())).unwrap()) {
        let mut card = CardField::open(&opened).unwrap();
        line_forward(&opened, &mut card, &field, opening);
    }
}

/// [`the_lines_energy_forward_on_the_card_is_the_hosts_at_1500_sites`] under one opening law.
fn line_forward(opened: &Card, card: &mut CardField, field: &Field, opening: &str) {
    let field = field.clone();
    let d = field.declaration;
    let owned = synthetic(1500, d.alphabet);
    let region = owned.region();
    let started = Instant::now();
    let cold = card.energy_read(&field, std::slice::from_ref(&region)).unwrap();
    let cold_ms = started.elapsed().as_millis();
    let started = Instant::now();
    let warm = card.energy_read(&field, std::slice::from_ref(&region)).unwrap();
    let warm_ms = started.elapsed().as_millis();
    let started = Instant::now();
    let reference = host(&field, std::slice::from_ref(&region));
    let host_ms = started.elapsed().as_millis();
    let diff = first_difference(&reference, &cold);
    let warm_diff = first_difference(&reference, &warm);
    let memory = opened.census().memory;
    println!(
        "ENERGY_PARITY line opening={opening} sites=1500 bit_equal={} warm_bit_equal={} card={} card_cold_ms={cold_ms} card_warm_ms={warm_ms} host_ms={host_ms} host_threads=1 free={} peak_store={} read={:?}",
        diff.is_none(),
        warm_diff.is_none(),
        opened.census().name,
        memory.free_bytes,
        card.times().peak_store,
        reference.2[0]
    );
    assert!(diff.is_none(), "opening {opening}: {}", diff.unwrap_or_default());
    assert!(warm_diff.is_none(), "opening {opening}: {}", warm_diff.unwrap_or_default());
    let single = reference;
    // Three regions of the line's founding in one batch, their ticks in lockstep, each at its own halvings.
    let parts: Vec<Owned> = [400usize, 900, 1500].iter().map(|&n| synthetic(n, d.alphabet)).collect();
    let regions: Vec<Region> = parts.iter().map(Owned::region).collect();
    let started = Instant::now();
    let batch = card.energy_read(&field, &regions).unwrap();
    let batch_ms = started.elapsed().as_millis();
    let started = Instant::now();
    let reference = host(&field, &regions);
    let host_ms = started.elapsed().as_millis();
    let diff = first_difference(&reference, &batch);
    for (r, read) in reference.2.iter().enumerate() {
        println!("ENERGY_PARITY line opening={opening} batch region={r} sites={} halvings={:?} reads={} pairs={}", regions[r].classes.len(), read.halvings, read.reads, read.pairs);
    }
    println!("ENERGY_PARITY line opening={opening} batch regions=3 sites=2800 bit_equal={} card_ms={batch_ms} host_ms={host_ms} host_threads=1 rereads={}", diff.is_none(), card.times().energy_rereads);
    assert!(diff.is_none(), "opening {opening}: {}", diff.unwrap_or_default());
    // The profiled read under the opening that stands once the claim is judged.
    if opening != "force" {
        return;
    }
    // A profiled read (every launch timed alone, the card synchronized around it): the kernels' time beside the copies' and
    // the allocations', and the pairs the card met over its reads.
    let pairs_before = card.times().pairs;
    card.profile();
    let started = Instant::now();
    let profiled = card.energy_read(&field, std::slice::from_ref(&region)).unwrap();
    let profiled_ms = started.elapsed().as_millis();
    assert!(first_difference(&single, &profiled).is_none(), "the profiled read");
    let p = card.profiled().unwrap();
    let kernels: u128 = p.kernels.values().map(|v| v.1).sum();
    let mut top: Vec<(&str, u64, u128)> = p.kernels.iter().map(|(k, v)| (*k, v.0, v.1)).collect();
    top.sort_by_key(|t| std::cmp::Reverse(t.2));
    println!(
        "ENERGY_PROFILE line sites=1500 elapsed_ms={profiled_ms} kernels_ms={} copies={} copies_ms={} allocations={} allocations_ms={} card_pairs={}",
        kernels / 1_000_000,
        p.copies.0,
        p.copies.1 / 1_000_000,
        p.allocations.0,
        p.allocations.1 / 1_000_000,
        card.times().pairs - pairs_before
    );
    for (entry, launches, ns) in top.iter().take(8) {
        println!("ENERGY_PROFILE entry={entry} launches={launches} us={}", ns / 1_000);
    }
}

/// The square's `ε` the curl's reading uses (`ENERGY_EPS` of `curl-field`, `2^(−6)` of a mixture's weight).
const SQUARE_EPS: u32 = 1 << 10;

/// The line's square `ε`, `2^7`: the wide read's `4ε` below a letter's uniform weight over the line's hundred letters (`2^16/100
/// = 655`), past which the moved mixture's lowered letter would pass below zero (`curl-field`'s `2^10` is refused there, on the
/// host and the card alike).
const LINE_SQUARE_EPS: u32 = 1 << 7;

/// The host's squares at `eps`, read in parallel (`Field::energy_square_corners`).
fn host_squares(field: &Field, squares: &[(&[usize], (usize, usize))], void: usize, eps: u32) -> Vec<Option<EnergySquare>> {
    squares.par_iter().map(|&(truth, ij)| field.energy_square_corners(truth, ij, void, eps).unwrap()).collect()
}

/// [measurement; the unified-theory reading of November 7, 01:37] **The tiny squares at one base on the card are the host's**:
/// on every ring set (the letters' temperature drawn), squares over the two tiny truths (7 and 13 sites), all in one batch of
/// thirteen reads, each square's `EnergySquare` (the runner-ups, the readings over whole letters, on the logits and of `G`, the
/// floors and the attribution read at `ε` and `4ε`) equal to the host's.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_tiny_squares_at_one_base_on_the_card_are_the_hosts() {
    let opened = Card::open(0).unwrap();
    let mut card = CardField::open(&opened).unwrap();
    let short = vec![1usize, 4, 0, 2, 2, 3, 1];
    let long: Vec<usize> = (0..13).map(|t| (t * 3 + t / 4) % 5).collect();
    let squares: Vec<(&[usize], (usize, usize))> = vec![(&short, (1, 3)), (&short, (0, 5)), (&short, (2, 6)), (&short, (3, 4)), (&long, (4, 9)), (&long, (0, 12)), (&long, (6, 7)), (&long, (2, 11))];
    let void = 4;
    for still in 0..=2 {
        let field = energetic(still);
        let reference = host_squares(&field, &squares, void, SQUARE_EPS);
        let read = card.energy_squares(&field, &squares, void, SQUARE_EPS).unwrap();
        for (k, (h, c)) in reference.iter().zip(&read).enumerate() {
            println!("ENERGY_SQUARE tiny still={still} square={k} bit_equal={} host={h:?}", h == c);
        }
        assert_eq!(read, reference, "still {still}: the card's squares");
        assert!(reference.iter().filter(|s| s.is_some()).count() >= 6, "still {still}: squares with runner-ups");
    }
}

/// [measurement; the unified-theory readings of November 7, 03:22 and 04:20] **The central squares and the configurations'
/// energies on the card are the host's**: on every ring set, the tiny squares' central readings at three steps
/// (`CardField::energy_central_squares` against `Field::energy_central_square`), and each tiny truth's energy with every
/// site resolved, and the same with one site at each letter (`CardField::energies` against `Field::energy_g`), equal.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_tiny_central_squares_and_energies_on_the_card_are_the_hosts() {
    let opened = Card::open(0).unwrap();
    let mut card = CardField::open(&opened).unwrap();
    let short = vec![1usize, 4, 0, 2, 2, 3, 1];
    let long: Vec<usize> = (0..13).map(|t| (t * 3 + t / 4) % 5).collect();
    let squares: Vec<(&[usize], (usize, usize))> = vec![(&short, (1, 3)), (&short, (0, 5)), (&short, (2, 6)), (&long, (4, 9)), (&long, (0, 12)), (&long, (6, 7))];
    let void = 4;
    let steps = [SQUARE_EPS / 4, SQUARE_EPS / 2, SQUARE_EPS];
    let mut configurations: Vec<Vec<usize>> = vec![short.clone(), long.clone()];
    configurations.extend((0..5).map(|c| {
        let mut x = long.clone();
        x[6] = c;
        x
    }));
    let views: Vec<&[usize]> = configurations.iter().map(|c| c.as_slice()).collect();
    for still in 0..=2 {
        let field = energetic(still);
        let reference: Vec<Option<Vec<(i128, i128)>>> = squares.par_iter().map(|&(truth, ij)| field.energy_central_square(truth, ij, void, &steps).unwrap()).collect();
        let read = card.energy_central_squares(&field, &squares, void, &steps).unwrap();
        for (k, (h, c)) in reference.iter().zip(&read).enumerate() {
            println!("ENERGY_CENTRAL tiny still={still} square={k} bit_equal={} host={h:?}", h == c);
        }
        assert_eq!(read, reference, "still {still}: the card's central squares");
        assert!(reference.iter().filter(|s| s.is_some()).count() >= 4, "still {still}: squares with runner-ups");
        let host_g: Vec<i128> = views.iter().map(|c| field.energy_g(c).unwrap()).collect();
        let card_g = card.energies(&field, &views).unwrap();
        println!("ENERGY_G tiny still={still} bit_equal={} host={host_g:?}", host_g == card_g);
        assert_eq!(card_g, host_g, "still {still}: the card's energies");
    }
}

/// [measurement; theory, November 8, the lead reading] **A place's lead read on the card is the host's**: on every ring set and
/// on two lanes, the tiny truths' lead reads at both ends and inside (`CardField::energy_leads` against `Field::energy_lead`: the
/// relaxed chart read against `Rᵀ E(u_t)`, the opening's letters' part beside its moment's term, and (theory, November 9) the
/// opening state and the opening's own term `E(u_t)` against `Rᵀ E(u_t)`), read in one batch and again two regions a batch (each
/// batch reading its own regions' sites), every lane's sums equal.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_tiny_lead_reads_on_the_card_are_the_hosts() {
    let opened = Card::open(0).unwrap();
    let mut card = CardField::open(&opened).unwrap();
    let short = vec![1usize, 4, 0, 2, 2, 3, 1];
    let long: Vec<usize> = (0..13).map(|t| (t * 3 + t / 4) % 5).collect();
    let places: Vec<(&[usize], usize)> = vec![(&short, 0), (&short, 3), (&short, 6), (&long, 0), (&long, 7), (&long, 12)];
    let laned = |still: usize| energetic_with(FieldDeclaration { width: 16, lanes: 2, ..tiny_declaration(still) });
    let own: Vec<(String, Field)> = (0..=2).map(|s| (format!("still {s}"), energetic(s))).chain((0..=1).map(|s| (format!("laned still {s}"), laned(s)))).collect();
    let fields: Vec<(String, Field)> = own.iter().cloned().chain(own.iter().map(|(name, f)| (format!("{name} at the letters' force"), f.opened_at_force().unwrap()))).collect();
    for (name, field) in &fields {
        let host: Vec<EnergyLead> = places.iter().map(|&(c, t)| field.energy_lead(c, t).unwrap()).collect();
        assert!(host.iter().all(|l| l.open.len() == field.declaration.lanes && l.enc.len() == field.declaration.lanes), "{name}: the opening's sums a lane");
        let whole = card.energy_leads(field, &places).unwrap();
        card.energy_batch_regions(Some(2));
        let cut = card.energy_leads(field, &places).unwrap();
        card.energy_batch_regions(None);
        let part = |reads: &[EnergyLead]| reads.iter().map(|l| (l.open.clone(), l.enc.clone())).collect::<Vec<_>>();
        println!("ENERGY_LEAD tiny {name} bit_equal={} cut_bit_equal={} opening_sums_equal={}", whole == host, cut == host, part(&whole) == part(&host) && part(&cut) == part(&host));
        assert_eq!(whole, host, "{name}: the card's lead reads");
        assert_eq!(cut, host, "{name}: the card's lead reads two regions a batch");
    }
}

/// [measurement; the unified-theory reading of November 7, 01:37] **The line's squares at one base on the card are the
/// host's**: on the founding of the line's declaration, squares on two synthetic truths of 400 sites (eight a truth, their
/// sites in the truths' last third, one to eleven apart), at `ε = 2^7` ([`LINE_SQUARE_EPS`]), read in one batch on the card
/// (cold, then warm) and on the host's threads, square for square equal.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_lines_squares_at_one_base_on_the_card_are_the_hosts() {
    let d = line_declaration();
    let field = Field::found(d, &keys(d.founding_draws())).unwrap();
    let truths: Vec<Vec<usize>> = (0..2u64)
        .map(|k| {
            let mut next = mixer(0x5A_0000 + k);
            (0..400).map(|_| (next() % d.alphabet as u64) as usize).collect()
        })
        .collect();
    let mut next = mixer(0x5A_1111);
    let mut squares: Vec<(&[usize], (usize, usize))> = Vec::new();
    for truth in &truths {
        for _ in 0..8 {
            let gap = 1 + (next() % 11) as usize;
            let i = 267 + (next() % (400 - 267 - gap) as u64) as usize;
            squares.push((truth, (i, i + gap)));
        }
    }
    let void = d.alphabet - 1;
    let opened = Card::open(0).unwrap();
    let mut card = CardField::open(&opened).unwrap();
    let started = Instant::now();
    let cold = card.energy_squares(&field, &squares, void, LINE_SQUARE_EPS).unwrap();
    let cold_ms = started.elapsed().as_millis();
    let started = Instant::now();
    let warm = card.energy_squares(&field, &squares, void, LINE_SQUARE_EPS).unwrap();
    let warm_ms = started.elapsed().as_millis();
    let threads = rayon::current_num_threads();
    let started = Instant::now();
    let reference = host_squares(&field, &squares, void, LINE_SQUARE_EPS);
    let host_ms = started.elapsed().as_millis();
    for (k, (h, c)) in reference.iter().zip(&cold).enumerate() {
        println!("ENERGY_SQUARE line square={k} bit_equal={} host={h:?}", h == c);
    }
    let n = squares.len() as u128;
    println!(
        "ENERGY_SQUARE line squares={n} sites=400 bit_equal={} warm_bit_equal={} card_cold_ms={cold_ms} card_warm_ms={warm_ms} card_ms_a_square={} host_ms={host_ms} host_threads={threads} host_ms_a_square={} peak_store={}",
        cold == reference,
        warm == reference,
        warm_ms / n,
        host_ms / n,
        card.times().peak_store
    );
    assert_eq!(cold, reference, "the card's squares");
    assert_eq!(warm, reference, "the card's squares, warm");
}

/// The host's material covectors, read in parallel (`Field::energy_material`).
fn host_material(field: &Field, regions: &[Region]) -> Vec<(Vec<i128>, i128)> {
    regions.par_iter().map(|r| field.energy_material(r).unwrap()).collect()
}

/// The first entry two material covectors differ at, for the receipt.
fn material_difference(field: &Field, host: &[(Vec<i128>, i128)], card: &[(Vec<i128>, i128)]) -> Option<String> {
    for (r, ((hg, hphi), (cg, cphi))) in host.iter().zip(card).enumerate() {
        if hphi != cphi {
            return Some(format!("region {r}: G host {hphi} card {cphi}"));
        }
        if let Some(k) = (0..hg.len()).find(|&k| hg[k] != cg[k]) {
            let family = field.layout().families.iter().position(|&(s, l, _)| (s..s + l).contains(&k));
            return Some(format!("region {r}: g[{k}] (family {family:?}) host {} card {}", hg[k], cg[k]));
        }
    }
    (host.len() != card.len()).then(|| "the reads' counts differ".to_string())
}

/// [measurement; agent-inferred, November 7] **The tiny energy fields' material covector on the card is the host's**: on every
/// ring set, each region's `∂G/∂θ` (every family on `2^(−40)`) and `G`, the three regions alone and in one batch, and through
/// the realization, under each opening law (at the letters' force the opening's own row returns `R λ⁰` to the encoding and
/// `E(u_t) ⊗ λ⁰` to the lift).
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_tiny_energy_material_on_the_card_is_the_hosts() {
    let opened = Card::open(0).unwrap();
    let mut card = CardField::open(&opened).unwrap();
    let owned = tiny_regions();
    let regions: Vec<Region> = owned.iter().map(Owned::region).collect();
    for (still, (opening, field)) in (0..=2).flat_map(|still| openings(energetic(still)).map(|f| (still, f))) {
        let reference = host_material(&field, &regions);
        for (r, region) in regions.iter().enumerate() {
            let alone = card.energy_material(&field, std::slice::from_ref(region)).unwrap();
            let diff = material_difference(&field, &reference[r..r + 1], &alone);
            let nonzero = reference[r].0.iter().filter(|&&v| v != 0).count();
            println!("ENERGY_MATERIAL tiny opening={opening} still={still} region={r} bit_equal={} nonzero={nonzero} of {} G={}", diff.is_none(), reference[r].0.len(), reference[r].1);
            assert!(diff.is_none(), "opening {opening} still {still} region {r}: {}", diff.unwrap_or_default());
        }
        let batch = card.read_energy_material(&field, &regions).unwrap();
        let diff = material_difference(&field, &reference, &batch);
        println!("ENERGY_MATERIAL tiny opening={opening} still={still} batch regions={} bit_equal={}", regions.len(), diff.is_none());
        assert!(diff.is_none(), "opening {opening} still {still} batch: {}", diff.unwrap_or_default());
    }
}

/// [measurement; agent-inferred, November 7] **The line's material covector on the card is the host's at 1,500 sites**: on the
/// founding of the line's declaration, the synthetic 1,500-site region alone (card cold and warm against the host) and 400 +
/// 900 + 1,500 sites in one batch, `∂G/∂θ` and `G` bit-equal, under each opening law.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_lines_energy_material_on_the_card_is_the_hosts_at_1500_sites() {
    let d = line_declaration();
    let opened = Card::open(0).unwrap();
    for (opening, field) in openings(Field::found(d, &keys(d.founding_draws())).unwrap()) {
        let mut card = CardField::open(&opened).unwrap();
        line_material(&mut card, &field, opening);
    }
}

/// [`the_lines_energy_material_on_the_card_is_the_hosts_at_1500_sites`] under one opening law.
fn line_material(card: &mut CardField, field: &Field, opening: &str) {
    let field = field.clone();
    let d = field.declaration;
    let owned = synthetic(1500, d.alphabet);
    let region = owned.region();
    let started = Instant::now();
    let cold = card.energy_material(&field, std::slice::from_ref(&region)).unwrap();
    let cold_ms = started.elapsed().as_millis();
    let started = Instant::now();
    let warm = card.energy_material(&field, std::slice::from_ref(&region)).unwrap();
    let warm_ms = started.elapsed().as_millis();
    let started = Instant::now();
    let reference = vec![field.energy_material(&region).unwrap()];
    let host_ms = started.elapsed().as_millis();
    let diff = material_difference(&field, &reference, &cold);
    let nonzero = reference[0].0.iter().filter(|&&v| v != 0).count();
    println!(
        "ENERGY_MATERIAL line opening={opening} sites=1500 bit_equal={} warm_bit_equal={} card_cold_ms={cold_ms} card_warm_ms={warm_ms} host_ms={host_ms} host_threads=1 nonzero={nonzero} of {} G={} peak_store={}",
        diff.is_none(),
        material_difference(&field, &reference, &warm).is_none(),
        reference[0].0.len(),
        reference[0].1,
        card.times().peak_store
    );
    assert!(diff.is_none(), "{}", diff.unwrap_or_default());
    let parts: Vec<Owned> = [400usize, 900, 1500].iter().map(|&n| synthetic(n, d.alphabet)).collect();
    let regions: Vec<Region> = parts.iter().map(Owned::region).collect();
    let started = Instant::now();
    let batch = card.energy_material(&field, &regions).unwrap();
    let batch_ms = started.elapsed().as_millis();
    let threads = rayon::current_num_threads();
    let started = Instant::now();
    let reference = host_material(&field, &regions);
    let host_ms = started.elapsed().as_millis();
    let diff = material_difference(&field, &reference, &batch);
    println!("ENERGY_MATERIAL line opening={opening} batch regions=3 sites=2800 bit_equal={} card_ms={batch_ms} host_ms={host_ms} host_threads={threads}", diff.is_none());
    assert!(diff.is_none(), "{}", diff.unwrap_or_default());
}

/// [measurement; agent-inferred, November 7] **One writer release of the line's energy field on the card** (the lap's
/// projection: theory wants one release per training state): a founding of the line's declaration, a synthetic question of
/// 400 known places and the line's answer room of 2,062 places (reach 3,771), released by `Field::sample_runs` through the card
/// realization as `length-field` does (run bits 0, the near tail, keyed order, sweeps 2,062, refine 10). Prints a line a
/// thousand reads (elapsed ms, the read's region) and the release's reads, card time and wall time. `FIELD_RELEASE_SWEEPS` and
/// `FIELD_RELEASE_REFINE` replace the sweeps and the refine (a development read), `FIELD_RELEASE_STOP` stops after that many
/// sweeps, `FIELD_RELEASE_PROBLEMS` releases that many questions together (each read a batch of their regions).
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn a_writer_release_of_the_lines_energy_field_on_the_card() {
    let d = line_declaration();
    let field = Field::found(d, &keys(d.founding_draws())).unwrap();
    let void = d.alphabet - 1;
    let room = 2062usize;
    let env = |name: &str, default: usize| std::env::var(name).ok().and_then(|v| v.parse().ok()).unwrap_or(default);
    let (sweeps, refine, stop, count) = (env("FIELD_RELEASE_SWEEPS", 2062), env("FIELD_RELEASE_REFINE", 10), env("FIELD_RELEASE_STOP", usize::MAX), env("FIELD_RELEASE_PROBLEMS", 1));
    let questions: Vec<Vec<usize>> = (0..count as u64)
        .map(|k| {
            let mut next = mixer(0x7E1E + k);
            (0..400).map(|_| (next() % void as u64) as usize).collect()
        })
        .collect();
    let question = &questions[0];
    let opened = Card::open(0).unwrap();
    let mut card = CardField::open(&opened).unwrap();
    let problems: Vec<(&[usize], usize)> = questions.iter().map(|q| (q.as_slice(), room)).collect();
    let started = Instant::now();
    let mut reads = 0usize;
    let answers = field
        .sample_runs(
            &problems,
            sweeps,
            refine,
            void,
            0x5EED_7E1E,
            0,
            true,
            false,
            None,
            false,
            false,
            false,
            None,
            holonics::hnn::tower::field::RefineOrder::Keyed,
            &mut card,
            &mut |done, _| done < stop,
            &mut |r| {
                if r.faces.is_some() {
                    reads += 1;
                    if reads % 1000 == 0 {
                        let end = (question.len()..r.classes[0].len()).find(|&t| !r.open[0][t] && r.classes[0][t] == void).map_or(r.classes[0].len(), |e| (e + 6).min(r.classes[0].len()));
                        println!("ENERGY_RELEASE reads={reads} pass={} region_sites={end} elapsed_ms={}", r.pass, started.elapsed().as_millis());
                    }
                }
            },
        )
        .unwrap();
    let wall = started.elapsed().as_millis();
    let t = card.times();
    let length = answers[0].iter().position(|&c| c == void).unwrap_or(answers[0].len());
    println!("ENERGY_RELEASE done problems={count} sweeps={sweeps} refine={refine} stop={stop} reads={reads} card_reads={} card_read_ms={} wall_ms={wall} ms_a_read={} answer_length={length} batches={} peak_store={} card={}", t.reads, t.read_ns / 1_000_000, wall / (reads.max(1) as u128), t.batches, t.peak_store, opened.census().name);
}

/// Words of one width class from the fixtures' mixer: the carrier's extremes (`i32::MIN`, `i32::MAX`, `±1`, `0`, the powers
/// of two and their neighbours at the limbs' edges), full-width draws, and draws at 8, 16 and 24 bits (a tile of one, two or
/// three limbs).
fn extreme_word(next: &mut impl FnMut() -> u64, class: u64) -> i32 {
    let edges = [i32::MIN, i32::MAX, -1, 0, 1, i32::MIN + 1, -(1 << 23), (1 << 23) - 1, -(1 << 15), (1 << 15) - 1, -128, 127, 1 << 24, -(1 << 24) - 1];
    let x = next();
    match class % 5 {
        0 => edges[(x % edges.len() as u64) as usize],
        1 => x as i32,
        2 => (x as i32) >> 24,
        3 => (x as i32) >> 16,
        _ => (x as i32) >> 8,
    }
}

/// 64-bit words of one width class: the carrier's extremes (`i64::MIN`, `i64::MAX`, `±1`, `0`, the limbs' edges), full-width
/// draws, and draws at 8 to 56 bits (a tile of one to seven limbs).
fn extreme_word64(next: &mut impl FnMut() -> u64, class: u64) -> i64 {
    let edges = [i64::MIN, i64::MAX, -1, 0, 1, i64::MIN + 1, -(1 << 55), (1 << 55) - 1, -(1 << 31), (1 << 31) - 1, -128, 127, 1 << 40, -(1 << 47) - 1];
    let x = next() as i64;
    match class % 9 {
        0 => edges[(x.unsigned_abs() % edges.len() as u64) as usize],
        1 => x,
        c => x >> (64 - 8 * (c - 1)),
    }
}

/// [measurement; agent-inferred, November 7] **The tensor cores' score tangent is the scalar one at the carriers'
/// extremes** (`CardField::dz_check`): a skinless head's `δz = release(T Σ (δp̂·k̂ + p̂·δk̂ − k̂·δk̂), 24)` at unit temperature
/// from the tiles' limb products (the tangents' 64-bit words in up to eight limbs, the unit words' 32-bit values in up to four,
/// each tile's limbs from its own bound) against `energy_pair_dz` mode by mode, bit for bit with no refusal, on tangents at
/// the 64-bit carrier's edges and every limb width and unit words at the 32-bit carrier's, spans of one and two tiles.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_tensor_cores_score_tangent_is_the_scalar_one_at_the_carriers_extremes() {
    let opened = Card::open(0).unwrap();
    let card = CardField::open(&opened).unwrap();
    let mut next = mixer(0x7E46);
    for &(span, na, nb) in &[(16usize, 53usize, 37usize), (6, 19, 11), (32, 35, 23), (20, 17, 9)] {
        let mut wide = |rows: usize, shift: u64| -> Vec<i64> { (0..rows * span).map(|e| extreme_word64(&mut next, (e / span) as u64 * 5 + shift)).collect() };
        let (tp, tk) = (wide(na, 0), wide(nb, 2));
        let mut narrow = |rows: usize, shift: u64| -> Vec<i64> { (0..rows * span).map(|e| extreme_word(&mut next, (e / span) as u64 * 3 + shift) as i64).collect() };
        let (p, k) = (narrow(na, 1), narrow(nb, 4));
        let (new, old, status) = card.dz_check(&tp, &p, &k, &tk, span).unwrap();
        let differ = new.iter().zip(&old).filter(|(x, y)| x != y).count();
        let widest = new.iter().map(|v| 128 - v.unsigned_abs().leading_zeros()).max().unwrap_or(0);
        println!("DZ_CHECK span={span} rows={na} columns={nb} pairs={} differ={differ} status={status} widest_bits={widest}", new.len());
        assert_eq!(status, 0, "span {span}: a refusal");
        assert_eq!(differ, 0, "span {span}: the tensor cores' score tangent differs from the scalar one");
    }
}

/// [definition; the unified-theory reading of November 7, 23:34] **The width law on the card is the host's**: with a share small
/// enough to split the founded line's classes, the card's lists are the host's own (`ClassLists::widened`, built on the host from
/// the card's opening words), so `∂G/∂θ` and `G` of a batch of 400 + 900 + 1,500 sites, and the faces at an open structure, are
/// bit-equal to the host's. [agent-inferred, November 8] Read again one region a batch, each batch's opening and leaves formed
/// while the batch before it runs (`CardField::energy_stream`), every bit is still the host's.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_width_law_on_the_card_is_the_hosts() {
    let d = line_declaration();
    let mut field = Field::found(d, &keys(d.founding_draws())).unwrap();
    field.widen = Some(6);
    let parts: Vec<Owned> = [400usize, 900, 1500].iter().map(|&n| synthetic(n, d.alphabet)).collect();
    let regions: Vec<Region> = parts.iter().map(Owned::region).collect();
    let opened = Card::open(0).unwrap();
    let mut card = CardField::open(&opened).unwrap();
    let started = Instant::now();
    let batch = card.energy_material(&field, &regions).unwrap();
    let card_ms = started.elapsed().as_millis();
    let started = Instant::now();
    let reference: Vec<(Vec<i128>, i128)> = regions.iter().map(|r| field.energy_material(r).unwrap()).collect();
    let host_ms = started.elapsed().as_millis();
    let diff = material_difference(&field, &reference, &batch);
    let mut plain = field.clone();
    plain.widen = None;
    let unwidened: Vec<i128> = regions.iter().map(|r| plain.energy_material(r).unwrap().1).collect();
    println!(
        "ENERGY_WIDEN material bit_equal={} card_ms={card_ms} host_ms={host_ms} G={:?} G_unwidened={:?}",
        diff.is_none(),
        reference.iter().map(|r| r.1).collect::<Vec<_>>(),
        unwidened
    );
    assert!(diff.is_none(), "{}", diff.unwrap_or_default());
    assert!(reference.iter().zip(&unwidened).any(|(r, &u)| r.1 != u), "the share splits some class (else the test reads nothing)");
    let host: Vec<_> = regions.iter().map(|r| field.energy_faces_read(r).unwrap()).collect();
    let (faces, g) = card.read_energy_faces(&field, &regions).unwrap();
    for (k, (hf, hg)) in host.iter().enumerate() {
        assert_eq!(*hg, g[k], "region {k}: G");
        assert_eq!(*hf, faces[k], "region {k}: faces");
    }
    // One region a batch: each batch's opening and leaves formed beside the batch before it.
    card.energy_batch_regions(Some(1));
    let before = card.times().batches;
    let streamed = card.energy_material(&field, &regions).unwrap();
    assert_eq!(card.times().batches - before, regions.len() as u64, "one region a batch");
    let diff = material_difference(&field, &reference, &streamed);
    assert!(diff.is_none(), "streamed: {}", diff.unwrap_or_default());
    let (faces, g) = card.read_energy_faces(&field, &regions).unwrap();
    for (k, (hf, hg)) in host.iter().enumerate() {
        assert_eq!(*hg, g[k], "streamed region {k}: G");
        assert_eq!(*hf, faces[k], "streamed region {k}: faces");
    }
}

/// [measurement; agent-inferred, November 8] **A crowds' difference array carried as limbs holds the ring sum's 128 bits**
/// (`CardField::limbs_check`: `add_difference` against `add_wide`, `kernels/field.cu`): `2^20` terms a cell (past the
/// `2^19 + 64` a head's crowds can bring one cell), each added as a crowd's term, `v` at its cell and `−v` at its mate; the
/// carrier's and the digits' extremes, full-width draws and one-digit draws, and a cell whose every term has its two low digits
/// at `−2^42` (its planes' sums at `∓2^62`), against the host's wrapping sum.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn a_difference_arrays_limbs_are_its_ring_sum() {
    let opened = Card::open(0).unwrap();
    let card = CardField::open(&opened).unwrap();
    let mut next = mixer(0x11B5);
    let edges = [0i128, 1, -1, i128::MIN, i128::MAX, i128::MIN + 1, i128::MAX - 1, (1 << 42) - 1, -(1 << 42), 1 << 42, -(1 << 42) - 1, (1 << 43) - 1, -(1 << 43), 1 << 85, -(1 << 85), (1 << 86) - 1, -(1 << 86), (1 << 126) + (1 << 85) + (1 << 42)];
    let cells = 5usize;
    let per = 1usize << 20;
    let values: Vec<i128> = (0..cells * per)
        .map(|k| {
            let (cell, x) = (k % cells, next());
            match cell {
                // Every term's two low digits at the bottom of their range.
                0 => -(1i128 << 42) - (1i128 << 85),
                1 => edges[(x % edges.len() as u64) as usize],
                2 => ((x as u128) << 64 | next() as u128) as i128,
                3 => (x as i64 >> 21) as i128,
                _ => ((x as u128) << 64 | next() as u128) as i128 >> (x % 127),
            }
        })
        .collect();
    let mut host = vec![0i128; 2 * cells];
    for (k, &v) in values.iter().enumerate() {
        host[k % cells] = host[k % cells].wrapping_add(v);
        host[cells + k % cells] = host[cells + k % cells].wrapping_sub(v);
    }
    let (ring, limbs) = card.limbs_check(&values, cells).unwrap();
    println!("LIMBS_CHECK cells={cells} terms_a_cell={per} ring_equal={} limbs_equal={}", ring == host, limbs == host);
    assert_eq!(ring, host, "the ring's atomic step");
    assert_eq!(limbs, host, "the limbs");
}

/// [measurement; agent-inferred, November 8] **A row's crowd tangents formed at once are the one-lane chain's, bit for bit**
/// (`CardField::crowds_check`: `energy_crowds_dz` against `energy_crowd_dz`, `kernels/field_energy.cuh`, at a skinless head):
/// rows of every crowd count from none to 32 (both lane layouts: two lanes a crowd up to 16, one past it) in scattered
/// slots, at spans of 6, 16 and 32, counts from 1 to `2^18`; words in the line's ranges (unit words on 32 bits, tangents on
/// 40, every chain passing its checks) and at the carriers' extremes (64-bit words, crowds' sums to `2^120`, so the mean
/// words take 128-bit quotients and the chains refuse at varied modes). Each crowd's `δz`, the row's `Σ p δz` and the status
/// bits are equal. The crowds' sums stay inside `|W| + |C|/2 < 2^127`, where `div_nearest` is the quotient (a crowd's sum is
/// at most `reach · 2^64` on the card).
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn a_rows_crowd_tangents_are_the_one_lane_chains() {
    let opened = Card::open(0).unwrap();
    let card = CardField::open(&opened).unwrap();
    let mut next = mixer(0xC50D);
    let counts_at = [1u64, 2, 3, 7, 64, 1 << 18];
    for n in [3usize, 8, 16] {
        let span = 2 * n;
        for extreme in [false, true] {
            let rows = 33 * 4;
            let (mut p, mut tp, mut sw, mut tsw) = (Vec::new(), Vec::new(), Vec::new(), Vec::new());
            let (mut counts, mut ce) = (vec![0u64; rows * 32], vec![0u64; rows * 32]);
            for row in 0..rows {
                let crowds = row % 33;
                let (start, step) = ((next() % 32) as usize, 2 * (next() % 16) as usize + 1);
                for k in 0..crowds {
                    let slot = (start + k * step) % 32;
                    let x = next();
                    counts[row * 32 + slot] = if x % 3 == 0 { counts_at[(x / 3 % counts_at.len() as u64) as usize] } else { 1 + (x >> 46) };
                    ce[row * 32 + slot] = next() >> 1;
                }
                for _ in 0..span {
                    let (a, b) = (next() as i64, next() as i64);
                    p.push(if extreme { a } else { a >> 32 });
                    tp.push(if extreme { b } else { b >> 24 });
                }
                for slot in 0..32 {
                    let count = counts[row * 32 + slot].max(1) as i128;
                    for (sums, bits) in [(&mut sw, 31u32), (&mut tsw, 39)] {
                        let (mut lo, mut hi) = (Vec::with_capacity(span), Vec::with_capacity(span));
                        for _ in 0..span {
                            let base = (next() as i64 as i128) << 36;
                            let x = (next() as u128) << 64 | next() as u128;
                            let sum = if extreme { (x as i128) >> 8 } else { count * ((x as i128) >> (127 - bits)) };
                            lo.push(base);
                            hi.push(base + sum);
                        }
                        sums.extend(lo);
                        sums.extend(hi);
                    }
                }
            }
            for temper in [1i128 << 24, 0x2F3_9A41] {
                let (fresh, before, status) = card.crowds_check(n, temper, &p, &tp, &sw, &tsw, &counts, &ce).unwrap();
                let differ = fresh.iter().zip(&before).filter(|(a, b)| a != b).count();
                let zero = before.chunks_exact(33).zip(counts.chunks_exact(32)).map(|(dz, held)| dz[..32].iter().zip(held).filter(|(dz, count)| **count != 0 && **dz == 0).count()).sum::<usize>();
                println!("CROWDS_CHECK span={span} extreme={extreme} temper={temper} rows={rows} differ={differ} status={status:?} zero_tangents={zero}");
                assert_eq!(differ, 0, "span {span}, extreme {extreme}: the crowds' tangents differ from the one-lane chain's");
                assert_eq!(status[0], status[1], "span {span}, extreme {extreme}: the refusals differ");
                if extreme {
                    assert_ne!(status[1], 0, "the extremes refuse some chain (else the refusal is not read)");
                } else {
                    assert_eq!(status[1], 0, "the line's ranges pass every check");
                }
            }
        }
    }
}
