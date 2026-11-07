//! [measurement] **The energy field's forward on the card returns the host's bits** (`holonics::hnn::tower::field::energy`,
//! `holonics_cuda::hnn::CardField::energy_read`): each region's faces, logits and energy read (the opening's and the last
//! tick's energy, every tick's halvings, the reads and the site pairs met), on the tiny `energetic` fixtures of every ring
//! set (open, carried and locked sites, regions of several lengths read in one batch), and on a founding of the line's
//! declaration on a synthetic region of 1,500 sites, timed against the host. Run alone under the card's lock:
//! `flock -w 900 .local/gpu.lock cargo test --release -p holonics-cuda --test field_energy -- --include-ignored --test-threads=1`.
use std::time::Instant;

use holonics::hnn::tower::field::{EnergyRead, Field, FieldDeclaration, FieldRealization, Region, Shares};
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
/// energy read and through the realization's faces and logits.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_tiny_energy_forward_on_the_card_is_the_hosts() {
    let opened = Card::open(0).unwrap();
    let mut card = CardField::open(&opened).unwrap();
    let owned = tiny_regions();
    let regions: Vec<Region> = owned.iter().map(Owned::region).collect();
    for still in 0..=2 {
        let field = energetic(still);
        let reference = host(&field, &regions);
        for (r, region) in regions.iter().enumerate() {
            let alone = card.energy_read(&field, std::slice::from_ref(region)).unwrap();
            let expected = (vec![reference.0[r].clone()], vec![reference.1[r].clone()], vec![reference.2[r].clone()]);
            let diff = first_difference(&expected, &alone);
            println!("ENERGY_PARITY tiny still={still} region={r} sites={} bit_equal={} read={:?}", region.classes.len(), diff.is_none(), alone.2[0]);
            assert!(diff.is_none(), "still {still} region {r}: {}", diff.unwrap_or_default());
        }
        let batch = card.energy_read(&field, &regions).unwrap();
        let diff = first_difference(&reference, &batch);
        println!("ENERGY_PARITY tiny still={still} batch regions={} bit_equal={}", regions.len(), diff.is_none());
        assert!(diff.is_none(), "still {still} batch: {}", diff.unwrap_or_default());
        // The realization's faces and logits are the energy forward's.
        assert_eq!(card.read_faces(&field, &regions).unwrap(), reference.0, "still {still}: the realization's faces");
        let read = card.read_logits(&field, &regions).unwrap();
        for (r, fr) in read.iter().enumerate() {
            assert_eq!(fr.logits, reference.1[r], "still {still} region {r}: the realization's logits");
            assert!(fr.echo.iter().all(|&e| e == 0), "an energy read carries no echo");
        }
        // Training is refused: the return through the ticks is not built.
        assert!(card.read_and_return(&field, &regions).is_err(), "still {still}: an energy field's return is refused on the card");
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
/// certifies a fall, so the regions exhaust their halvings, at different ticks, and a tick's last states are read again.
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
    assert!(rested > 0 && rereads > 0, "the letters' descent reached no rest ({rested}) or no reread ({rereads})");
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
/// the card's time (cold, then warm) beside the host's.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_lines_energy_forward_on_the_card_is_the_hosts_at_1500_sites() {
    let d = line_declaration();
    let field = Field::found(d, &keys(d.founding_draws())).unwrap();
    let owned = synthetic(1500, d.alphabet);
    let region = owned.region();
    let opened = Card::open(0).unwrap();
    let mut card = CardField::open(&opened).unwrap();
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
        "ENERGY_PARITY line sites=1500 bit_equal={} warm_bit_equal={} card={} card_cold_ms={cold_ms} card_warm_ms={warm_ms} host_ms={host_ms} host_threads=1 free={} peak_store={} read={:?}",
        diff.is_none(),
        warm_diff.is_none(),
        opened.census().name,
        memory.free_bytes,
        card.times().peak_store,
        reference.2[0]
    );
    assert!(diff.is_none(), "{}", diff.unwrap_or_default());
    assert!(warm_diff.is_none(), "{}", warm_diff.unwrap_or_default());
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
        println!("ENERGY_PARITY line batch region={r} sites={} halvings={:?} reads={} pairs={}", regions[r].classes.len(), read.halvings, read.reads, read.pairs);
    }
    println!("ENERGY_PARITY line batch regions=3 sites=2800 bit_equal={} card_ms={batch_ms} host_ms={host_ms} host_threads=1 rereads={}", diff.is_none(), card.times().energy_rereads);
    assert!(diff.is_none(), "{}", diff.unwrap_or_default());
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
