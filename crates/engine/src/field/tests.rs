use super::*;

/// An exterior integer mixer's words from a seed (the fixtures' draws).
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

/// `n` draws of four bytes.
fn keys(n: usize) -> Vec<u8> {
    // A fixed exterior key stream for the fixtures: an integer mixer's words. (A counter's squares
    // and Weyl steps, the stream before November 1, drew the founding's rows along one lattice, so
    // every founded word was nearly every other: a word's contact with its equal scored about 70
    // against the region's 80 to 90 at 450 sites, where a mixed stream gives 16 against 9 to 22.)
    let mut next = mixer(0x5EED);
    (0..n.div_ceil(2)).flat_map(|_| next().to_be_bytes()).take(4 * n).collect()
}

fn tiny_declaration(still: usize) -> Declaration {
    Declaration { alphabet: 5, width: 8, heads: 2, modes: 3, still, contacts: 4, ticks: 2, frames: 2, reach: 16, lanes: 1, depth: 0, carry: 0, triads: 0, opening: false, junction: false, mark: false, loud: false, crossing: false, closed: 0, pump: false, lane_leak: false, friction: false, friction_gate: false, fade: false }
}

/// A tiny field with every family drawn from the keys (the founding holds the returns and the
/// readout at zero, where no covector reaches the charts).
fn shaped(still: usize) -> Constitution {
    shaped_with(tiny_declaration(still))
}

/// [`shaped`] on a declaration of the caller's.
fn shaped_with(d: Declaration) -> Constitution {
    drawn(Constitution::found(d, &keys(1 << 14)).unwrap())
}

/// Every family of `field` drawn from the keys, a uniform draw on `[−½, ½)` of its family's grain.
fn drawn(mut field: Constitution) -> Constitution {
    let stream = keys(1 << 15);
    for (n, v) in field.theta.iter_mut().enumerate() {
        let word = &stream[4 * n..4 * n + 4];
        let k = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) as i64;
        // A uniform draw on [−½, ½) of its family's grain.
        let grain = field.layout.families.iter().find(|(s, l, _)| (*s..*s + *l).contains(&n)).unwrap().2;
        *v = ((k << grain) >> 32) as i32;
    }
    field
}

/// The field with its strand contacts silent (`E₋ = E₊ = 0`, as founded): a site opens on its own
/// class alone.
fn silent_contacts(mut field: Constitution) -> Constitution {
    let rows = (field.declaration.alphabet + 1) * field.declaration.width;
    let l = field.layout.clone();
    for start in [l.before, l.after] {
        field.theta[start..start + rows].iter_mut().for_each(|v| *v = 0);
    }
    field
}

const CLASSES: [usize; 7] = [1, 4, 0, 2, 2, 3, 1];
const OPEN: [bool; 7] = [false, true, false, true, false, false, true];

fn region() -> Region<'static> {
    Region { classes: &CLASSES, unresolved: &OPEN, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None }
}

/// The most halvings of a probe's step that seek a step crossing no seam (`2^(grain − 9)` down to
/// `2^(grain − 15)`, past which the forward's releases are a tenth of the difference).
const STRADDLE_HALVINGS: u32 = 6;

/// The largest step `2^(grain − 9 − h)`, `h ≤ STRADDLE_HALVINGS`, at which `straddles` is false, with
/// its `h`; `None` where every one straddles (the probe stands on a seam).
fn unstraddled(grain: u32, straddles: &dyn Fn(i32) -> bool) -> Option<(i32, u32)> {
    (0..=STRADDLE_HALVINGS).map(|h| (1i32 << (grain - 9 - h), h)).find(|&(delta, _)| !straddles(delta))
}

/// The most doublings of a probe's step that lift a quiet entry's predicted difference above the
/// rounding floor (`2^(grain − 9)` up to `2^(grain − 5)`): an entry whose code moves less than the
/// forward's releases at `2^(grain − 9)` is read where its difference stands above them (measured
/// November 2: a listener's temperature, `−55` predicted against `44` measured at `2^(grain − 9)`, read
/// `−876` against `−860` at `2^(grain − 5)`).
const QUIET_DOUBLINGS: u32 = 4;

/// The probe's step: from `2^(grain − 9)`, doubled while the predicted difference `predict(δ)` stays
/// under four floors and no seam is crossed, then halved off a seam ([`unstraddled`]); with its
/// halvings (a doubling counts as none).
fn probe_step(grain: u32, predict: &dyn Fn(i32) -> i128, straddles: &dyn Fn(i32) -> bool) -> Option<(i32, u32)> {
    let mut up = 0u32;
    while up < QUIET_DOUBLINGS && predict(1i32 << (grain - 9 + up)).abs() < 256 && !straddles(1i32 << (grain - 9 + up + 1)) {
        up += 1;
    }
    if up > 0 {
        return Some((1i32 << (grain - 9 + up), 0));
    }
    unstraddled(grain, straddles)
}

/// The code's own covector.
fn covector_of(field: &Constitution, region: &Region) -> Vec<i128> {
    let pass = field.pass(region, true).unwrap();
    let mut g = vec![0i128; field.theta.len()];
    field.returned(region, &pass, &mut g).unwrap();
    field.both_reads_mean(g)
}

/// The learner's covector of one region (the reverse).
fn reversed_of(field: &Constitution, region: &Region) -> Vec<i128> {
    let pass = field.pass(region, true).unwrap();
    let mut g = vec![0i128; field.theta.len()];
    field.returned(region, &pass, &mut g).unwrap();
    g
}

#[test]
fn ring_periods_sample_both_towers_to_the_reach() {
    assert_eq!(ring_periods(4, 16), vec![2, 3, 16, 27]);
    assert_eq!(ring_periods(1, 100), vec![128]);
    assert_eq!(ring_periods(8, 1000), vec![2, 3, 16, 27, 128, 243, 1024, 2187]);
    // More slots than closures cycle the towers.
    assert_eq!(ring_periods(6, 4), vec![2, 2, 3, 3, 4, 9]);
}

/// A region past the reach is refused: its sites would repeat every frame.
#[test]
fn a_region_past_the_reach_is_refused() {
    let field = shaped(1);
    let classes = [1usize; 17];
    let open = [true; 17];
    assert!(field.faces(&Region { classes: &classes, unresolved: &open, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None }).is_err());
    assert!(field.faces(&Region { classes: &classes[..16], unresolved: &open[..16], faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None }).is_ok());
}

/// With flat weights (no chart reads) and silent strand contacts, a still field's current is the
/// same at every interior site (an end site lacks a strand mate, §16.34), and a framed field's carries each site's place:
/// the moment is phase-carried. Every
/// site carries the same face, so each is keyed and every site a source (§16.20).
#[test]
fn the_current_carries_place_when_the_weights_are_flat() {
    for (still, framed) in [(2usize, false), (1, true)] {
        // [§16.34] One tick: an end site lacks a strand mate on one side, so its merge differs by construction, and a
        // second tick's contact carries that difference to every site by its falloff.
        let mut d = tiny_declaration(still);
        d.ticks = 1;
        let mut field = silent_contacts(shaped_with(d));
        let l = field.layout.clone();
        let m2 = 2 * field.declaration.complex();
        let dw = field.declaration.width;
        field.theta[l.q..l.q + m2 * dw].iter_mut().for_each(|v| *v = 0);
        field.theta[l.q_bias..l.q_bias + m2].iter_mut().for_each(|v| *v = 0);
        let classes = [2usize; 6];
        let open = [true; 6];
        let carried: Vec<Option<Shares>> = vec![Some(vec![(2, 1 << STATE_BITS)]); 6];
        let faces = field.faces(&Region { classes: &classes, unresolved: &open, faces: &carried, locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None }).unwrap();
        let alike = faces[1..5].iter().all(|f| f == &faces[1]);
        assert_eq!(alike, !framed, "still {still}");
    }
}

#[test]
fn ring_phasors_close_on_the_unit_circle() {
    let pi = half_turn(MOVE_BITS + 16);
    let one = 1i128 << MOVE_BITS;
    for n in [2usize, 3, 5, 7, 16] {
        assert_eq!(ring_phasor(0, n, pi), (one as i64, 0));
        for r in 0..n {
            let (re, im) = ring_phasor(r, n, pi);
            let power = re as i128 * re as i128 + im as i128 * im as i128;
            // Unit modulus to a few grains of 2^(−30).
            assert!((power - (one * one)).abs() < 16 * one, "n {n} r {r}");
        }
    }
    // The half turn of an even ring is −1.
    assert_eq!(ring_phasor(1, 2, pi).0, -(one as i64));
}

#[test]
fn founding_opens_on_the_flat_face() {
    let field = Constitution::found(tiny_declaration(1), &keys(1 << 14)).unwrap();
    let faces = field.faces(&region()).unwrap();
    for (t, face) in faces.iter().enumerate() {
        match face {
            Some(face) => assert!(face.masses.iter().all(|&m| m == face.masses[0]), "site {t}"),
            None => assert!(!OPEN[t]),
        }
    }
}

#[test]
fn text_restores_exactly() {
    let field = shaped(1);
    let back = Constitution::from_text(&field.to_text()).unwrap();
    assert_eq!(back, field);
    let mut learner = Learner::new(field, 6);
    learner.section(&[region()]).unwrap();
    let back = Learner::from_text(&learner.to_text()).unwrap();
    // The transfer's operand is a reading's, not retained (§16.41).
    assert_eq!(back, Learner { last: None, ..learner });
}

/// The covector agrees with the code's central difference on every family: the three entries of
/// each family with the largest covectors, and in the charts the largest on a turned mode's row
/// and on a still mode's, are each moved by `±δ` and the code's change is compared with the
/// covector's prediction, `g · 2δ · 2^(20 − natural − grain)` on `2^(−20)` bits. The resonance
/// classes are locks, piecewise constant in the material: a probe whose `±δ` moves some site across
/// a sheet changes the support, the difference then crosses a seam the covector does not read, and
/// it is left out (counted; most probes are read).
#[test]
fn covector_matches_the_codes_difference() {
    let sheets = |field: &Constitution, r: &Region| -> Vec<Vec<u32>> { field.pass(r, true).unwrap().ticks.iter().flat_map(|c| c.classes.iter().map(|l| l.off.iter().chain(&l.members).copied().chain(l.probes.iter().flat_map(|p| std::iter::once(u32::MAX).chain(p.iter().copied()))).collect())).collect() };
    let (mut read, mut seams, mut halvings) = (0usize, 0usize, 0u32);
    // The region as it stands, and with two resolved sites and an unresolved one carried as mixtures
    // of several classes (a mixture opening returns to each class's rows by its share, the shares
    // held as data; the unresolved one is read and compared as the release's sweeps read it).
    let mut carried: Vec<Option<Shares>> = vec![None; CLASSES.len()];
    carried[0] = Some(vec![(1, 40_000), (3, 25_536)]);
    carried[3] = Some(vec![(2, 50_000), (0, 15_536)]);
    carried[4] = Some(vec![(2, 30_000), (4, 20_000), (0, 15_536)]);
    // [§16.24] And a region whose last three sites are an answer port, compared through its coupling with two cells;
    // [§16.47] and the same port compared at its boundary (two letters, then the void), open and with its middle place
    // resolved (a state of the writer's path).
    const PORTED: [bool; 7] = [false, true, false, false, true, true, true];
    const PATH: [bool; 7] = [false, true, false, false, true, false, true];
    let port = Port { start: 4, void: 0, target: &[2, 3], boundary: false, stop: None, heard: None, window: false, letters: false };
    let bounded = Port { boundary: true, ..port };
    // [the unified-theory reading of November 6, 11:49] And a port on its letters off the void, with its middle place resolved
    // (the writer's own state given its end).
    let lettered = Port { letters: true, target: &[2, 3, 1], ..port };
    // [the depth rings, November 6] And with a depth ring among the turned sets (its rate the located increment alone, no
    // skin, no moment).
    // [the unified-theory reading of November 6, 10:31] And under the bare stretch (`Constitution::bare_stretch`: past the last arrival
    // a silent place runs at the bare rate and returns nothing), declared beside the one-rate stretch.
    for (still, depth, bare, r) in [(0usize, 0usize, false), (1, 0, false), (2, 0, false), (0, 1, false), (1, 1, false), (0, 0, true), (1, 0, true)].into_iter().flat_map(|(still, depth, bare)| [(still, region()), (still, Region { classes: &CLASSES, unresolved: &OPEN, faces: &carried, locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None }), (still, Region { classes: &CLASSES, unresolved: &PORTED, faces: &[], locked: &[], echo: &[], domain: None, port: Some(port), before: false, strand: false, past: false, second: false, targets: None }), (still, Region { classes: &CLASSES, unresolved: &PORTED, faces: &[], locked: &[], echo: &[], domain: None, port: Some(bounded), before: false, strand: false, past: false, second: false, targets: None }), (still, Region { classes: &CLASSES, unresolved: &PATH, faces: &[], locked: &[], echo: &[], domain: None, port: Some(bounded), before: false, strand: false, past: false, second: false, targets: None }), (still, Region { classes: &CLASSES, unresolved: &PATH, faces: &[], locked: &[], echo: &[], domain: None, port: Some(lettered), before: false, strand: false, past: false, second: false, targets: None })].map(|(still, r)| (still, depth, bare, r))) {
        let mut field = shaped_with(Declaration { depth, ..tiny_declaration(still) });
        field.bare_stretch = bare;
        let g = covector_of(&field, &r);
        let (m, n, dw) = (field.declaration.complex(), field.declaration.modes, field.declaration.width);
        let l = field.layout.clone();
        for &(start, len, grain) in field.families() {
            let natural: u32 = if grain == MATERIAL_BITS { 40 } else { 24 };
            let mut entries: Vec<usize> = (start..start + len).collect();
            entries.sort_by_key(|&i| std::cmp::Reverse(g[i].unsigned_abs()));
            let mut probed: Vec<usize> = entries.iter().copied().take(3).collect();
            if [l.q, l.v].contains(&start) {
                // A chart row is (real or imaginary part, mode c); mode c is head c / n's, of ring
                // set (c / n) mod frames, turned past the still sets.
                let turned = |i: usize| (((i - start) / dw) % m / n) % field.declaration.frames >= field.declaration.still;
                probed.extend(entries.iter().copied().find(|&i| turned(i)));
                probed.extend(entries.iter().copied().find(|&i| !turned(i)));
            }
            for i in probed {
            if g[i] == 0 {
                continue;
            }
            let straddles = |delta: i32| {
                let (mut plus, mut minus) = (field.clone(), field.clone());
                plus.theta[i] += delta;
                minus.theta[i] -= delta;
                sheets(&plus, &r) != sheets(&field, &r) || sheets(&minus, &r) != sheets(&field, &r)
            };
            let shift = natural + grain - 20;
            let Some((delta, h)) = probe_step(grain, &|delta: i32| (g[i] * 2 * delta as i128) >> shift, &straddles) else {
                seams += 1;
                continue;
            };
            halvings += h as u32;
            let mut plus = field.clone();
            plus.theta[i] += delta;
            let mut minus = field.clone();
            minus.theta[i] -= delta;
            read += 1;
            // A temperature moves every row's every score at once, so one difference stands near the code's own
            // rounding (about ±50 a read, §16.13): its slope is fitted over 17 reads in `±δ`, as the pace's is.
            let measured = if start == l.temper {
                let at = |k: i32| { let mut f = field.clone(); f.theta[i] += k * (delta / 8); f.code(&r).unwrap().0 as i128 };
                let weighted: i128 = (-8..=8).map(|k| k as i128 * at(k)).sum();
                div_nearest(16 * weighted, 408) as i64
            } else {
                plus.code(&r).unwrap().0 - minus.code(&r).unwrap().0
            };
            let predicted = (g[i] * 2 * delta as i128) >> shift;
            let tolerance = predicted.abs() / 8 + (64 << h);
            assert!((measured as i128 - predicted).abs() <= tolerance, "still {still} family at {start} (grain {grain}) entry {i} at {h} halvings: measured {measured}, predicted {predicted}");
            }
        }
    }
    // Every probe is read at the largest step `2^(grain − 9 − h)` that crosses no sheet and no band
    // edge (the receivers' probes across their seams, §15.2's multi-probe, add a jump at each band
    // edge), halving `h ≤ STRADDLE_HALVINGS` times; one still straddling at the smallest step stands on
    // a seam and is counted apart. The tolerance's floor is the code's rounding, `64` on 2^(−20) bits,
    // which stands while the difference falls by `2^h`, so it is `64 · 2^h`; a quiet entry's step is
    // first doubled above the floor ([`probe_step`]). Measured November 2: the face's 364 probes, the
    // closure's 204 and the far support's 232 are every one read, after 26, 0 and 137 halvings in all (the far
    // support read by its fitted window and with the paces, §16: 264 read after 344 halvings),
    // none on a seam.
    eprintln!("COVECTOR_PROBES read={read} halvings={halvings} on_a_seam={seams}");
    assert!(16 * seams <= read, "read {read} probes, {seams} on a seam at the smallest step");
}

/// [definition; agent-inferred, November 1; November 3, §16.38] **A still head weighs its faces, not its distances** (the
/// dispersing field's §2.3, and conservation of faces): with every key and probe zero (so every site shares one class and
/// meets every other, every source known), a still field's sources are one face and share its mass alike at every distance,
/// to the shares' rounding (§14.11: each term keeps its own exponent); with its strand contacts silent it still reads the
/// order of its classes, through the strand's pair contact. (A turned head's falloff, the octave of its distance, is read
/// through the covector's checks; its probes carry the moments, so its classes differ by site.)
#[test]
fn the_falloff_weighs_a_source_by_the_octave_of_its_distance() {
    for still in [2usize] {
        let mut field = silent_contacts(shaped(still));
        let l = field.layout.clone();
        let (m2, dw) = (2 * field.declaration.complex(), field.declaration.width);
        for (chart, bias) in [(l.q, l.q_bias), (l.probe, l.probe_bias)] {
            field.theta[chart..chart + m2 * dw].iter_mut().for_each(|v| *v = 0);
            field.theta[bias..bias + m2].iter_mut().for_each(|v| *v = 0);
        }
        let classes = [1usize, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2];
        let open = [false; 12];
        let pass = field.pass(&Region { classes: &classes, unresolved: &open, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None }, true).unwrap();
        for cell in &pass.ticks {
            for (hi, row) in cell.rows.iter().enumerate() {
                let i = hi % classes.len();
                assert_eq!(row.len(), classes.len() - 1, "every site meets every other where the words are one class");
                let scaled: Vec<u128> = row.iter().map(|src| src.p as u128).collect();
                let (low, high) = (*scaled.iter().min().unwrap(), *scaled.iter().max().unwrap());
                assert!(high - low <= 1 << 10, "still {still} site {i}: one face shares its mass alike: {scaled:?}");
            }
        }
        let faces = field.faces(&region()).unwrap();
        let order = [3usize, 0, 6, 1, 5, 2, 4];
        let classes: Vec<usize> = order.iter().map(|&t| CLASSES[t]).collect();
        let open: Vec<bool> = order.iter().map(|&t| OPEN[t]).collect();
        let permuted = field.faces(&Region { classes: &classes, unresolved: &open, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None }).unwrap();
        assert!(order.iter().enumerate().any(|(n, &t)| permuted[n] != faces[t]), "still {still}: the field reads order");
    }
    assert_eq!([1usize, 2, 3, 4, 5, 7, 8, 1000].map(octave), [0, 1, 1, 2, 2, 2, 3, 9]);
}

/// [definition; agent-inferred, November 1] **The class lists and the support** (§2.5, §12): each
/// site's class is its unframed word's shells over the head's first `b` modes; the lists are a stable
/// counting sort, each class's definite sites first; a site's support is its near field and the
/// definite members of its class past it, each site once, never itself (§14.1: directional).
#[test]
fn the_classes_are_the_word_s_sheets_and_the_support_is_symmetric() {
    let definite: Vec<bool> = (0..14).map(|t| t % 3 != 1).collect();
    let lists = ClassLists::of(vec![2, 0, 2, 1, 0, 2, 3, 2, 0, 2, 2, 1, 0, 2], definite.clone(), 4);
    assert_eq!(lists.off, vec![0, 2, 4, 6, 6, 10, 13, 14, 14]);
    assert_eq!(lists.members, vec![8, 12, 1, 4, 3, 11, 0, 2, 5, 9, 7, 10, 13, 6]);
    for i in 0..14 {
        let support: Vec<usize> = lists.support(i).collect();
        let mut sorted = support.clone();
        sorted.sort_unstable();
        sorted.dedup();
        assert_eq!(sorted.len(), support.len(), "each site once");
        assert!(!support.contains(&i));
        for j in 0..14 {
            // A definite receiver hears its class's definite members far; an open one every definite site (§15.9).
            let meets = j != i && (i.abs_diff(j) < NEAR || (definite[j] && (!definite[i] || lists.class[i] == lists.class[j])));
            assert_eq!(support.contains(&j), meets, "site {i} source {j}");
        }
    }
    // Only the plates radiate far: past the near field an open site hears every definite site, a
    // definite one the definite members of its class, and a soft or unreached source is heard by none.
    let lists = ClassLists::of(vec![1u32; 20], (0..20).map(|t| t == 15).collect(), 3);
    assert_eq!(lists.support(2).collect::<Vec<_>>(), vec![1, 3, 0, 4, 5, 6, 7, 15]);
    assert!(!lists.support(15).any(|k| k == 2) && !lists.support(2).any(|k| k == 12));
    let lists = ClassLists::of(vec![1, 2, 1, 2, 1, 2, 1, 2, 1, 2], vec![true, true, false, true, true, true, true, true, true, true], 3);
    assert_eq!(lists.support(2).filter(|&j| j.abs_diff(2) >= NEAR).collect::<Vec<_>>(), vec![8, 9], "an open site hears every definite site far");
    assert_eq!(lists.support(3).filter(|&j| j.abs_diff(3) >= NEAR).collect::<Vec<_>>(), vec![9], "a definite one its class's");
    assert_eq!([(2, 0), (-2, 1), (0, 0), (5, -5), (-5, 5), (6, 5), (-6, 5), (1, -2)].map(|(re, im)| shell(re, im)), [2, 0, 1, 1, 1, 2, 0, 1], "the plates where the in-phase part dominates, the bridge on and inside the light cone");
    // The field's own classes are its words' shells.
    for still in [0usize, 1, 2] {
        let field = shaped(still);
        let d = field.declaration;
        let pass = field.pass(&region(), true).unwrap();
        let sites = CLASSES.len();
        let x = field.opening(&region()).unwrap();
        let cell = &pass.ticks[0];
        let l = &field.layout;
        let m2 = 2 * d.complex();
        let reaches = field.reaches();
        for t in 0..sites {
            let (r, _) = ratio_to_power(&x[t * d.width..(t + 1) * d.width]).unwrap();
            let mut q = vec![0i64; m2];
            affine(&field.theta[l.q..l.q + m2 * d.width], reaches.q, d.width, &r, Some(&field.theta[l.q_bias..l.q_bias + m2]), MATERIAL_BITS, MATERIAL_BITS, &mut q).unwrap();
            let m = d.complex();
            for h in 0..d.heads {
                let class: u32 = (0..d.class_trits()).map(|li| 3u32.pow(li as u32) * shell(q[h * d.modes + li], q[m + h * d.modes + li])).sum();
                assert_eq!((cell.classes[h].class[t], cell.classes[h].definite[t]), (class, !OPEN[t]), "still {still} head {h} site {t}");
            }
        }
    }
}

/// [definition; agent-inferred, November 1] **A lock is greatest at the equal word** (§2.1, §12, §15.2):
/// the score of every met pair is the lock of the receiver's modes against the source as it arrives
/// ([`lock`]), which at a still head is never above the receiver's own `|a|²/2` and reaches it exactly
/// at an equal word; and each row's shares (its sources' and its crowds') sum to its whole `2^63` to
/// their rounding.
#[test]
fn a_mode_s_lock_is_greatest_at_the_equal_word() {
    for (a, b) in [((70_000i128, -3_000i128), (70_000i128, -3_000i128)), ((5, 9), (-4, 2)), ((60_000, 1), (120_000, 2))] {
        let at = |b: (i128, i128)| lock(a, b, 1, (1, 0)).unwrap();
        assert!(at(b) <= at(a), "a louder key never outscores the equal one");
    }
    assert_eq!(lock((3, 4), (3, 4), 1, (1, 0)).unwrap(), 25);
    for still in [0usize, 1, 2] {
        let field = shaped(still);
        let d = field.declaration;
        let pass = field.pass(&region(), true).unwrap();
        let sites = CLASSES.len();
        for cell in &pass.ticks {
            for h in 0..d.heads {
                for i in 0..sites {
                    let row = &cell.rows[h * sites + i];
                    let total: i128 = row.iter().map(|src| src.p as i128).sum::<i128>() + cell.crowds[h * sites + i].iter().map(|c| c.e as i128).sum::<i128>();
                    let terms = (row.len() + cell.crowds[h * sites + i].len()) as i128;
                    assert!((total - (1i128 << SHARE_BITS)).abs() <= terms, "still {still} head {h} site {i}: shares {total}");
                }
            }
        }
    }
}

/// The strand contacts read the word: with every mode still, the same classes in another order
/// read differently once a site opens with its neighbours.
#[test]
fn the_strand_contacts_read_order_without_frames() {
    let field = shaped(2);
    let faces = field.faces(&region()).unwrap();
    let order = [3usize, 0, 6, 1, 5, 2, 4];
    let classes: Vec<usize> = order.iter().map(|&t| CLASSES[t]).collect();
    let open: Vec<bool> = order.iter().map(|&t| OPEN[t]).collect();
    let permuted = field.faces(&Region { classes: &classes, unresolved: &open, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None }).unwrap();
    assert!(order.iter().enumerate().any(|(n, &t)| permuted[n] != faces[t]));
}

/// The frames make place matter: the same classes in another order read differently.
#[test]
fn framed_field_reads_place() {
    let field = shaped(1);
    let faces = field.faces(&region()).unwrap();
    let order = [3usize, 0, 6, 1, 5, 2, 4];
    let classes: Vec<usize> = order.iter().map(|&t| CLASSES[t]).collect();
    let open: Vec<bool> = order.iter().map(|&t| OPEN[t]).collect();
    let permuted = field.faces(&Region { classes: &classes, unresolved: &open, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None }).unwrap();
    assert!(order.iter().enumerate().any(|(n, &t)| permuted[n] != faces[t]));
}

/// [definition; §16.47, Brandon, November 5 17:32] **The step fluxes**: every section deposits its step at its size with no
/// reread (none is read after it), and over a few sections the regions' code falls from the founding's.
#[test]
fn fluxing_deposits_lower_the_code() {
    let field = Constitution::found(tiny_declaration(1), &keys(1 << 14)).unwrap();
    let mut learner = Learner::new(field, 6);
    let second_classes = [2usize, 2, 3, 1, 0, 4, 4];
    let second_open = [true, false, false, true, true, false, false];
    let regions = [region(), Region { classes: &second_classes, unresolved: &second_open, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None }];
    let opening: i64 = regions.iter().map(|r| learner.field.code(r).unwrap().0).sum();
    let mut deposited = 0;
    for _ in 0..12 {
        let receipt = learner.section(&regions).unwrap();
        assert_eq!(receipt.sites, 6);
        assert!(receipt.code_after.is_none() && receipt.change.is_none() && receipt.halvings == 0, "no reread");
        deposited += usize::from(receipt.deposited);
    }
    let after: i64 = regions.iter().map(|r| learner.field.code(r).unwrap().0).sum();
    assert_eq!(deposited, 12);
    assert!(after < opening, "{after} against {opening}");
}

/// The covector summed over regions in parallel is the sum of each region's, bit for bit.
#[test]
fn regions_sum_in_any_order() {
    let field = shaped(1);
    let second_classes = [2usize, 2, 3, 1, 0, 4, 4];
    let second_open = [true, false, false, true, true, false, false];
    let regions = [region(), Region { classes: &second_classes, unresolved: &second_open, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None }];
    let (_, g) = field.read_and_return(&regions).unwrap();
    let a = reversed_of(&field, &regions[0]);
    let b = reversed_of(&field, &regions[1]);
    let summed: Vec<i128> = a.iter().zip(&b).map(|(x, y)| x + y).collect();
    assert_eq!(g, summed);
    let (_, reversed) = field.read_and_return(&[regions[1], regions[0]]).unwrap();
    assert_eq!(reversed, g);
}

/// [definition; §16.27] **The writer draws every place from its own face**: every answer place is written with a class
/// of the alphabet, the same seed draws the same answer and another seed another, a write stopped after its first sweep
/// still draws every place (on its last read), and a face that is a point mass at one class writes that class at every
/// place.
#[test]
fn the_writer_draws_every_place_from_its_own_face() {
    let mut field = shaped(1);
    let questions: [&[usize]; 2] = [&[1, 4, 0, 2], &[3, 3]];
    let problems: Vec<(&[usize], usize)> = questions.iter().zip([6usize, 5]).map(|(q, a)| (*q, a)).collect();
    let once = field.sample_realized(&problems, 3, 0, 0, 11, &mut Host, &mut |_, _| true).unwrap();
    assert_eq!(once.iter().map(Vec::len).collect::<Vec<_>>(), vec![6, 5]);
    assert!(once.iter().flatten().all(|&c| c < field.declaration.alphabet));
    assert_eq!(field.sample_realized(&problems, 3, 0, 0, 11, &mut Host, &mut |_, _| true).unwrap(), once, "the same draws");
    assert!((12..20).any(|seed| field.sample_realized(&problems, 3, 0, 0, seed, &mut Host, &mut |_, _| true).unwrap() != once), "another seed draws another answer");
    let mut asked = 0;
    let stopped = field.sample_realized(&problems, 3, 0, 0, 11, &mut Host, &mut |_, _| {
        asked += 1;
        asked < 2
    }).unwrap();
    assert_eq!(stopped.iter().map(Vec::len).collect::<Vec<_>>(), vec![6, 5], "a stopped write draws every place");
    let l = field.layout.clone();
    field.theta[l.read_bias + 2] = 40 << 16;
    let pointed = field.sample_realized(&problems, 3, 0, 0, 11, &mut Host, &mut |_, _| true).unwrap();
    assert!(pointed.iter().flatten().all(|&c| c == 2), "{pointed:?}");
}

/// [definition; §16.35] **A drawn void closes the answer**: in every write, every place past an answer's first void is the
/// void (the region stays an answer and its void tail), and some write ends early.
#[test]
fn a_drawn_void_closes_the_answer() {
    let field = shaped(1);
    let questions: [&[usize]; 2] = [&[1, 4, 0, 2], &[3, 3]];
    let problems: Vec<(&[usize], usize)> = questions.iter().zip([9usize, 8]).map(|(q, a)| (*q, a)).collect();
    let mut closed_early = false;
    for seed in 11..27 {
        for (places, n) in field.sample_realized(&problems, 4, 0, 0, seed, &mut Host, &mut |_, _| true).unwrap().into_iter().zip([9usize, 8]) {
            assert_eq!(places.len(), n);
            if let Some(end) = places.iter().position(|&c| c == 0) {
                assert!(places[end..].iter().all(|&c| c == 0), "a letter past the first void, seed {seed}: {places:?}");
                closed_early |= end + 1 < n;
            }
        }
    }
    assert!(closed_early, "no write ended before its last place");
}

/// A site carried as a mixture of one class and locked opens and radiates exactly as the site resolved
/// to that class: the mixture of one row at the whole share is the row, and a lock is definite. A
/// carried site holds nothing for the closure, and an unresolved site carried so is read beside the
/// rest exactly as the region with that site's opening resolved reads them.
#[test]
fn a_carried_face_of_one_class_opens_as_that_class() {
    for still in [0usize, 1, 2] {
        let field = shaped(still);
        let r = region();
        let mut carried: Vec<Option<Shares>> = vec![None; CLASSES.len()];
        carried[2] = Some(vec![(0, 1 << STATE_BITS)]);
        carried[5] = Some(vec![(3, 1 << STATE_BITS)]);
        // Locked, a carried site is definite as a known one is (§14.1), so it is heard alike.
        let mut locked = [false; 7];
        locked[2] = true;
        locked[5] = true;
        let as_faces = Region { classes: &CLASSES, unresolved: &OPEN, faces: &carried, locked: &locked, echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None };
        assert_eq!(field.faces(&as_faces).unwrap(), field.faces(&r).unwrap(), "still {still}");
        assert!(field.faces(&Region { classes: &CLASSES, unresolved: &OPEN, faces: &[], locked: &locked, echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None }).is_err(), "a lock on a site that carries no face");
        // An unresolved site carried as one class, locked, opens on it and is still read.
        let mut at_open = carried.clone();
        at_open[1] = Some(vec![(4, 1 << STATE_BITS)]);
        locked[1] = true;
        let mut resolved_open = OPEN;
        resolved_open[1] = false;
        let read = field.faces(&Region { classes: &CLASSES, unresolved: &OPEN, faces: &at_open, locked: &locked, echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None }).unwrap();
        let resolved = field.faces(&Region { classes: &CLASSES, unresolved: &resolved_open, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None }).unwrap();
        assert!(read[1].is_some());
        for t in (0..CLASSES.len()).filter(|&t| t != 1) {
            assert_eq!(read[t], resolved[t], "still {still} site {t}");
        }
        assert!(field.faces(&Region { classes: &CLASSES, unresolved: &OPEN, faces: &carried[..3], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None }).is_err(), "one carried face a site or none");
    }
}

/// The grown field reads the old faces exactly, on the framed and the still field, by two and
/// by three; the draws counted are the draws read; and one learned section parts the copies.
#[test]
fn the_grown_field_reads_the_old_faces() {
    for still in [0usize, 1, 2] {
        // Every family is shaped, the returns and the readout among them, as a trained field's are.
        let field = shaped(still);
        let faces = field.faces(&region()).unwrap();
        for factor in [2usize, 3] {
            let draws = field.growth_draws(factor);
            let (grown, from) = field.grown(factor, &keys(draws)).unwrap();
            assert_eq!(from.len(), grown.theta.len());
            assert!(field.grown(factor, &keys(draws).as_slice()[..4 * draws - 1]).is_err(), "the draws counted are the draws read");
            assert_eq!(grown.declaration.width, factor * field.declaration.width);
            assert_eq!(grown.faces(&region()).unwrap(), faces, "still {still} factor {factor}");
        }
    }
    assert!(shaped(1).grown(1, &keys(1 << 12)).is_err(), "one copy is no growth");
}

#[test]
fn the_grown_learner_lifts_its_moments_and_parts_its_copies() {
    let field = Constitution::found(tiny_declaration(1), &keys(1 << 14)).unwrap();
    let mut learner = Learner::new(field, 4);
    learner.read_held = true;
    for _ in 0..3 {
        learner.section(&[region()]).unwrap();
    }
    let stream = keys(1 << 16);
    assert!(learner.holds_step() && learner.widened(2, &stream).is_err(), "a held step is read before the body widens");
    learner.read_step_on(&[region()], &mut Host).unwrap();
    let grown = learner.widened(2, &stream).unwrap();
    assert_eq!(grown.drawn, learner.drawn + 4 * learner.field.growth_draws(2));
    let l = grown.field.layout().clone();
    let old = learner.field.layout().clone();
    // The readout keeps its moments; an encoding entry's copy carries a half of the first.
    assert_eq!(grown.first[l.read_bias], learner.first[old.read_bias]);
    assert_eq!(grown.first[l.enc], div_nearest(learner.first[old.enc], 2));
    assert_eq!(grown.second[l.enc], div_nearest(learner.second[old.enc], 4));
    // Whether a step is read on the next regions is the run's declaration, not the learner's text (§16.30).
    let back = Learner { read_held: grown.read_held, ..Learner::from_text(&grown.to_text()).unwrap() };
    assert_eq!(back, grown);
    // One learned section on the grown learner parts some pair of encoding copies.
    let mut next = grown.clone();
    next.section(&[region()]).unwrap();
    let w = next.field.declaration.width / 2;
    let parted = (0..=next.field.declaration.alphabet).any(|row| (0..w).any(|j| next.field.theta[l.enc + row * 2 * w + j] != next.field.theta[l.enc + row * 2 * w + w + j]));
    assert!(parted, "the copies part under learning");
}

/// The size the law reads a step at on `regions` against `old` (the doc of [`scaled`], step by
/// step): the further halvings of the last size read and whether the step stands there.
fn law_scale(base: &Constitution, step: &[i128], h0: u32, old: &Compared, strict: bool, regions: &[Region]) -> (u32, bool) {
    let on = |field: &Constitution| compared(&regions.iter().map(|r| field.faces(r).unwrap()).collect::<Vec<_>>(), regions).unwrap();
    let spans = spans_of(regions);
    let stands = |new: &Compared| if strict { fewer(old, new, &spans) } else { !fewer(new, old, &spans) };
    let at = |h: u32| stepped(base, step, h0 + h).unwrap();
    let (full, moved) = at(0);
    if !moved {
        return (0, false);
    }
    if stands(&on(&full)) {
        return (0, true);
    }
    let (half, moved) = at(1);
    if !moved {
        return (1, false);
    }
    if stands(&on(&half)) {
        return (1, true);
    }
    let (e1, e2) = ((code_of(&on(&full), &spans) - code_of(old, &spans)) as i128, (code_of(&on(&half), &spans) - code_of(old, &spans)) as i128);
    if e1 <= 0 || e2 <= 0 || 4 * e2 - e1 >= 0 {
        return (1, false);
    }
    // The largest halving at or below the parabola's lowest point, μ* = (e1 − 4e2)/(4e1 − 8e2).
    let h = (2u32..).find(|&h| (e1 - 4 * e2) << h >= 4 * e1 - 8 * e2).unwrap();
    let (candidate, moved) = at(h);
    (h, moved && stands(&on(&candidate)))
}

/// The read the law makes of a held step on `regions`, from the material before it
/// ([`Learner::next_scale`]): the further halvings and whether it is refused.
fn law_next(before: &Constitution, step: &[i128], h0: u32, regions: &[Region]) -> (u32, bool) {
    let old = compared(&regions.iter().map(|r| before.faces(r).unwrap()).collect::<Vec<_>>(), regions).unwrap();
    let (halvings, stands) = law_scale(before, step, h0, &old, false, regions);
    (halvings, !stands)
}

/// [§16.30, the declared comparison] A deposited step is held and read on the next section: the material that stands is the law's
/// (the step at its size or half of it, or at the parabola's halving, or refused), it never codes
/// the next regions higher than the material before the step, and the section's opening read is
/// the standing material's; the held step crosses the learner's text.
#[test]
fn a_held_step_is_read_on_the_next_section() {
    let field = Constitution::found(tiny_declaration(1), &keys(1 << 14)).unwrap();
    // [§16.34] At `2^(−3)`: under the strand's pair contact the fixture certifies too few steps at `2^(−2)` to hold one.
    let mut learner = Learner::new(field, 3);
    // The read is the declared comparison (§16.30); the field's law lets a step stand unread.
    learner.read_held = true;
    let second_classes = [2usize, 2, 3, 1, 0, 4, 4];
    let second_open = [true, false, false, true, true, false, false];
    let second = Region { classes: &second_classes, unresolved: &second_open, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None };
    let (mut read, mut halved) = (0, 0);
    // Twenty-four sections: with the face's covector alone (§16.19) the first twelve stand every step at its size.
    for k in 0..24 {
        let before = learner.clone();
        let regions = if k % 2 == 0 { [region()] } else { [second] };
        let receipt = learner.section(&regions).unwrap();
        assert_eq!(receipt.next.is_some(), before.holds_step());
        if let (Some(next), Some(held)) = (receipt.next, before.held.as_ref()) {
            read += 1;
            let mut material = before.field.clone();
            for (slot, &q) in material.theta.iter_mut().zip(&held.step) {
                *slot += release(q, held.halvings) as i32;
            }
            let compared_on = |field: &Constitution| compared(&[field.faces(&regions[0]).unwrap()], &regions).unwrap();
            let old = compared_on(&material);
            assert_eq!(next.change, code_of(&compared_on(&before.field), &spans_of(&regions)) - code_of(&old, &spans_of(&regions)));
            assert_eq!((next.halvings, next.refused), law_next(&material, &held.step, held.halvings, &regions));
            let standing = if next.refused { material.clone() } else { stepped(&material, &held.step, held.halvings + next.halvings).unwrap().0 };
            assert!(!fewer(&compared_on(&standing), &old, &spans_of(&regions)), "the standing material codes the next regions no higher");
            if next.halvings > 0 || next.refused {
                halved += 1;
                assert!(fewer(&compared_on(&before.field), &old, &spans_of(&regions)), "the step at its size coded them higher");
            }
            // The section's opening read is the standing material's.
            assert_eq!(receipt.code_before, code_of(&compared_on(&standing), &spans_of(&regions)));
        }
        if learner.holds_step() {
            assert_eq!(Learner::from_text(&learner.to_text()).unwrap(), learner);
        }
    }
    // On these sections the law stands steps at their size, at half, at the parabola's halving
    // (five) and refuses others.
    assert!(read >= 4 && halved >= 1, "read {read} halved {halved}");
}

/// A held step that climbs the next regions' code is refused from two reads (its size and half
/// of it), not halved until it moves nothing: the material before it stands and the opening read
/// is that material's.
#[test]
fn a_step_that_codes_the_next_regions_higher_is_refused() {
    let material = shaped(1);
    let regions = [region()];
    let compared_on = |field: &Constitution| compared(&[field.faces(&regions[0]).unwrap()], &regions).unwrap();
    let old = compared_on(&material);
    // The covector is the code's gradient (a deposit subtracts the step), so the step that moved
    // the material to `material + sign(g) 2^k` climbed it; held, it is the negated sign.
    let g = covector_of(&material, &regions[0]);
    for k in [0u32, 3, 6] {
        let step: Vec<i128> = g.iter().map(|&v| -(v.signum() << k)).collect();
        let mut learner = Learner::new(material.clone(), 2);
        learner.field = stepped(&material, &step, 0).unwrap().0;
        let climbed = compared_on(&learner.field);
        learner.held = Some(HeldStep { step: step.clone(), halvings: 0 });
        let mut counted = Counted { reads: 0 };
        let (faces, next) = learner.read_step_on(&regions, &mut counted).unwrap();
        let next = next.expect("a held step is read");
        assert!(next.refused, "k {k}: halvings {}", next.halvings);
        assert_eq!((next.halvings, next.refused), law_next(&material, &step, 0, &regions));
        assert!(counted.reads <= 4, "k {k}: {} reads", counted.reads);
        assert!(!learner.holds_step());
        assert_eq!(learner.field, material, "the material before the step stands");
        assert_eq!(faces, vec![material.faces(&regions[0]).unwrap()]);
        assert_eq!(next.change, code_of(&climbed, &spans_of(&regions)) - code_of(&old, &spans_of(&regions)));
        assert!(next.change > 0);
    }
}

/// The host realization, its reads counted.
struct Counted {
    reads: usize,
}

impl Realization for Counted {
    fn read_and_return(&mut self, field: &Constitution, regions: &[Region]) -> Result<(Vec<Vec<Option<TowerFace>>>, Vec<i128>)> {
        self.reads += 1;
        field.read_and_return(regions)
    }
    fn read_faces(&mut self, field: &Constitution, regions: &[Region]) -> Result<Vec<Vec<Option<TowerFace>>>> {
        self.reads += 1;
        field.read_faces(regions)
    }
    fn read_logits(&mut self, field: &Constitution, regions: &[Region]) -> Result<Vec<ReadLogits>> {
        self.reads += 1;
        field.read_logits(regions)
    }
    fn read_landmarks(&mut self, field: &Constitution, region: &Region, question: usize, sites: &[usize], count: usize) -> Result<Vec<Vec<(usize, u64)>>> {
        field.landmarks(region, question, sites, count)
    }
}


/// The founding draws the key and the probe apart (§16.19): each its own keyed draw, neither the other,
/// every class has a word in the encoding and both strand contacts, and the unresolved rows carry none.
#[test]
fn the_founding_draws_the_key_and_the_probe_apart() {
    let field = Constitution::found(tiny_declaration(1), &keys(1 << 14)).unwrap();
    let (dw, a, m2) = (field.declaration.width, field.declaration.alphabet, 2 * field.declaration.complex());
    let l = field.layout.clone();
    let (key, probe) = (&field.theta[l.q..l.q + m2 * dw], &field.theta[l.probe..l.probe + m2 * dw]);
    assert!(key.iter().any(|&v| v != 0) && probe.iter().any(|&v| v != 0));
    assert_ne!(key, probe, "the probe is not the key");
    let tm = field.declaration.moment_modes();
    assert_eq!(4 * field.declaration.founding_draws(), 4 * (3 * a * dw + 3 * m2 * dw + 2 * field.declaration.contacts * dw + 2 * tm * dw));
    let stream = keys(field.declaration.founding_draws());
    assert_eq!(Constitution::found(tiny_declaration(1), &stream).unwrap(), field, "the draws counted are the draws read");
    assert!(Constitution::found(tiny_declaration(1), &stream[..stream.len() - 1]).is_err());
    // The moment's chart into the face (§16.22): drawn at the modes that carry a moment, zero at a still mode's.
    let (m, n) = (field.declaration.complex(), field.declaration.modes);
    for k in 0..m2 {
        let column: Vec<i32> = (0..dw).map(|o| field.theta[l.moment_face + o * m2 + k]).collect();
        assert_eq!(column.iter().any(|&v| v != 0), field.declaration.carries_moment((k % m) / n), "column {k}");
    }
    for start in [l.enc, l.before, l.after] {
        for row in 0..a {
            assert!(field.theta[start + row * dw..start + (row + 1) * dw].iter().any(|&v| v != 0), "class {row} has a word");
        }
        assert!(field.theta[start + a * dw..start + (a + 1) * dw].iter().all(|&v| v == 0), "the unresolved row is silent");
    }
}

/// No site meets itself: no row's support holds its own site, and the row's shares are the others'.
#[test]
fn no_site_meets_itself() {
    for still in [0usize, 1, 2] {
        let field = shaped(still);
        let pass = field.pass(&region(), true).unwrap();
        let sites = CLASSES.len();
        for cell in &pass.ticks {
            for (hi, row) in cell.rows.iter().enumerate() {
                assert!(row.iter().all(|src| src.j as usize != hi % sites), "still {still} row {hi}");
                assert!(row.iter().any(|src| src.p > 0), "some other site carries a share");
            }
        }
    }
    let one = [1usize];
    assert!(shaped(1).faces(&Region { classes: &one, unresolved: &[true], faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None }).is_err(), "a lone site has no site to meet");
}

/// The contact's gain covers the falloff: the largest shift, negative where it amplifies, at which a
/// head's lock of an equal word (`n` at unit power, half its `2n` reals) reads `2⌈log₂ reach⌉` bits.
#[test]
fn the_contact_s_gain_covers_the_falloff() {
    let at = |modes: usize, reach: usize| Declaration { alphabet: 5, width: 8, heads: 2, modes, still: 1, contacts: 4, ticks: 2, frames: 2, reach, lanes: 1, depth: 0, carry: 0, triads: 0, opening: false, junction: false, mark: false, loud: false, crossing: false, closed: 0, pump: false, lane_leak: false, friction: false, friction_gate: false, fade: false }.score_shift();
    assert_eq!(at(8, 2221), -2, "reading 8's declaration locks an equal word at 32 bits");
    assert_eq!(at(16, 16), 1);
    assert_eq!(at(3, 16), -2);
    for (modes, reach) in [(8usize, 2221usize), (16, 16), (3, 16), (8, 2), (16, 1 << 20), (1, 1 << 20)] {
        let (beta, need) = (at(modes, reach), 2 * (u128::BITS - ((reach - 1) as u128).leading_zeros()).max(1) as u128);
        let gained = |b: i32| if b >= 0 { (modes as u128) >> b } else { (modes as u128) << -b };
        assert!(gained(beta) >= need && gained(beta + 1) < need, "the largest such shift: modes {modes} reach {reach}");
    }
    let d = Declaration { alphabet: 5, width: 8, heads: 2, modes: 8, still: 1, contacts: 4, ticks: 2, frames: 2, reach: 2221, lanes: 1, depth: 0, carry: 0, triads: 0, opening: false, junction: false, mark: false, loud: false, crossing: false, closed: 0, pump: false, lane_leak: false, friction: false, friction_gate: false, fade: false };
    assert_eq!((d.class_trits(), d.classes()), (4, 81), "81 classes at reading 8's reach");
    assert_eq!(Declaration { modes: 3, ..d }.class_trits(), 3);
    assert_eq!((Declaration { reach: 81, ..d }.class_trits(), Declaration { reach: 82, ..d }.class_trits()), (2, 3));
}

/// A region's classes drawn from a seed (a fixed exterior stream for the fixtures).
fn drawn_classes(seed: u64, sites: usize, alphabet: usize) -> Vec<usize> {
    let mut state = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ 0xD1B5_4A32_D192_ED03;
    (0..sites)
        .map(|_| {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            (state % alphabet as u64) as usize
        })
        .collect()
}

/// [definition; agent-inferred, November 1] **The skin decay** (§12): one at no distance, one e-fold
/// a radian of turn (`D(a + b) = D(a) D(b)` to the exponent's grain), read by the distance alone, and zero once it
/// falls below the frames' grain, so a fine ring is heard only a few sites away and a coarse one far.
#[test]
fn the_skin_decay_is_an_e_fold_a_radian_and_vanishes_below_the_grain() {
    let field = shaped(0);
    let pi = half_turn(MOVE_BITS + 16);
    let one = 1i64 << MOVE_BITS;
    for n in [2usize, 3, 16, 27, 2187] {
        let at = |d: usize| skin_decay(d, n, pi, &field.exponential);
        assert_eq!(at(0), one);
        for (a, b) in [(1usize, 1usize), (1, 2), (2, 3), (3, 4)] {
            let product = ((at(a) as i128 * at(b) as i128) >> MOVE_BITS) as i64;
            // Each exponent is attained on the exponential's `2^(−16)` bits, so the law holds to a
            // part in `2^15` of the face (and the frames' grain).
            assert!((at(a + b) - product).abs() <= (at(a + b) >> 15) + 4, "n {n}: D({a} + {b}) = {} against {product}", at(a + b));
        }
        assert!((1..16).all(|d| at(d) <= at(d - 1)), "n {n}: it falls with distance");
    }
    // e^(−π) a site on the finest ring: below the grain within eight sites; the top ring still carries
    // across the reach.
    assert!(skin_decay(6, 2, pi, &field.exponential) > 0 && skin_decay(8, 2, pi, &field.exponential) == 0);
    assert!(skin_decay(2221, 2187, pi, &field.exponential) > one >> 10);
    // A still head is undecayed; a turned head reads its slot's face by the distance alone (head 1
    // of one still set among two: its mode `l` is slot `l`).
    let mixed = shaped(1);
    assert_eq!(mixed.decay(0, 0, 5), (1, 0));
    assert_eq!(mixed.decay(1, 1, 3), (mixed.decays[1][3] as i128, MOVE_BITS));
}

/// The covector agrees with the code's central difference on a region past the near field: 26 sites
/// whose classes recur, so rows meet class-mates far from them through the decayed transport, and
/// unresolved sites whose class is held far away (the closure over the support), on a still, a mixed
/// and a turned field. Probes across a sheet are left out and counted.
#[test]
fn the_covector_matches_the_code_across_the_far_support() {
    let d = Declaration { alphabet: 5, width: 8, heads: 2, modes: 3, still: 1, contacts: 4, ticks: 2, frames: 2, reach: 32, lanes: 1, depth: 0, carry: 0, triads: 0, opening: false, junction: false, mark: false, loud: false, crossing: false, closed: 0, pump: false, lane_leak: false, friction: false, friction_gate: false, fade: false };
    let classes: Vec<usize> = (0..26).map(|t| [1usize, 3, 2, 4, 0, 2, 1][t % 7]).collect();
    let open: Vec<bool> = (0..26).map(|t| t % 9 == 4 || t == 25).collect();
    let r = Region { classes: &classes, unresolved: &open, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None };
    let sheets = |field: &Constitution| -> Vec<Vec<u32>> { field.pass(&r, true).unwrap().ticks.iter().flat_map(|c| c.classes.iter().map(|l| l.off.iter().chain(&l.members).copied().chain(l.probes.iter().flat_map(|p| std::iter::once(u32::MAX).chain(p.iter().copied()))).collect())).collect() };
    let (mut read, mut seams, mut far, mut halvings) = (0usize, 0usize, 0usize, 0u32);
    for still in [0usize, 1, 2] {
        let mut field = Constitution::found(Declaration { still, ..d }, &keys(1 << 14)).unwrap();
        let stream = keys(1 << 15);
        for (k, v) in field.theta.iter_mut().enumerate() {
            let word = &stream[4 * k..4 * k + 4];
            let grain = field.layout.families.iter().find(|(s, l, _)| (*s..*s + *l).contains(&k)).unwrap().2;
            *v = (((i32::from_be_bytes([word[0], word[1], word[2], word[3]]) as i64) << grain) >> 32) as i32;
        }
        far += field.pass(&r, true).unwrap().ticks.iter().flat_map(|c| c.rows.iter().enumerate()).filter(|(hi, row)| row.iter().any(|src| (src.j as usize).abs_diff(hi % 26) >= NEAR)).count();
        {
            let g = covector_of(&field, &r);
            for &(start, len, grain) in field.families() {
                let natural: u32 = if grain == MATERIAL_BITS { 40 } else { 24 };
                let mut entries: Vec<usize> = (start..start + len).collect();
                entries.sort_by_key(|&i| std::cmp::Reverse(g[i].unsigned_abs()));
                for &i in entries.iter().take(2).filter(|&&i| g[i] != 0) {
                    let straddles = |delta: i32| {
                        let (mut plus, mut minus) = (field.clone(), field.clone());
                        plus.theta[i] += delta;
                        minus.theta[i] -= delta;
                        sheets(&plus) != sheets(&field) || sheets(&minus) != sheets(&field)
                    };
                    let Some((delta, h)) = probe_step(grain, &|delta: i32| (g[i] * 2 * delta as i128) >> (natural + grain - 20), &straddles) else {
                        seams += 1;
                        continue;
                    };
                    halvings += h;
                    let code = |f: &Constitution| f.code(&r).unwrap().0;
                    // [agent-inferred, November 2] The slope through a wide window: a line fitted to 17 reads at
                    // `k δ/2`, `k = −8..8` (`±4δ`), read as its change over `2δ`, `4 Σ k c_k / Σ k²`; a window that
                    // crosses a sheet at any read is left out. Why: the integer forward's releases jump at steps no
                    // seam marks, and the paced field (§16) jumps more often, so one central difference cannot
                    // resolve the slope at the narrow step (measured: a q-chart entry under a random pace read
                    // −357 and −187 against −509 and −255 at `±2^15` and `±2^14`, a line over `±2^14` −383.5 and over
                    // `±2^16` −475.3, over `±2^18` −509.0; at a zero pace −476.1, −513.9 and −542.7 against −543).
                    // A window that crosses a sheet is halved (each halving counted as the step's are), up to
                    // `STRADDLE_HALVINGS`; one that still crosses stands on a seam.
                    let points: Vec<i32> = (-8..=8).collect();
                    let moved = |k: i32, step: i32| { let mut f = field.clone(); f.theta[i] += k * (step / 2); f };
                    let Some(w) = (0..=STRADDLE_HALVINGS).find(|&w| (delta >> w) >= 2 && points.iter().all(|&k| sheets(&moved(k, delta >> w)) == sheets(&field))) else {
                        seams += 1;
                        continue;
                    };
                    let (step, h) = (delta >> w, h + w);
                    halvings += w;
                    read += 1;
                    let weighted: i128 = points.iter().map(|&k| k as i128 * code(&moved(k, step)) as i128).sum();
                    let squares: i128 = points.iter().map(|&k| (k * k) as i128).sum();
                    let measured = div_nearest(4 * weighted, squares) as i64;
                    let predicted = (g[i] * 2 * step as i128) >> (natural + grain - 20);
                    let agrees = |m: i64, p: i128| (m as i128 - p).abs() <= p.abs() / 8 + (64 << h);
                    assert!(agrees(measured, predicted), "still {still} family at {start} entry {i} at {h} halvings: measured {measured}, predicted {predicted}");
                }
            }
        }
    }
    assert!(far > 0, "some row meets a class-mate past the near field");
    // Every probe is read at the largest step `2^(grain − 9 − h)` that crosses no sheet and no band
    // edge (the receivers' probes across their seams, §15.2's multi-probe, add a jump at each band
    // edge), halving `h ≤ STRADDLE_HALVINGS` times; one still straddling at the smallest step stands on
    // a seam and is counted apart. The tolerance's floor is the code's rounding, `64` on 2^(−20) bits,
    // which stands while the difference falls by `2^h`, so it is `64 · 2^h`; a quiet entry's step is
    // first doubled above the floor ([`probe_step`]). Measured November 2: the face's 364 probes, the
    // closure's 204 and the far support's 232 are every one read, after 26, 0 and 137 halvings in all (the far
    // support read by its fitted window and with the paces, §16: 264 read after 344 halvings),
    // none on a seam.
    eprintln!("FAR_PROBES read={read} halvings={halvings} on_a_seam={seams}");
    assert!(16 * seams <= read, "read {read} probes, {seams} on a seam at the smallest step");
}


/// [definition; agent-inferred, November 2] **A listener's founding row keeps its near field** (§15.10, §16.20):
/// on a crib-sized region (420 sites, no word recurring, every other site of the last 40 open, so each open
/// site's near field holds keyed sites: a site with no key is no source, §16.20), at the founding, an open
/// receiver's row puts more of its mass on its near field than on its loudest far source, on the mean over
/// its rows, at the listener's own temperature (`β = 2` at this reach, §16.20). [measurement, November 2] The
/// test prints it beside the class receiver's gain (`−2`), where the loudest far source outweighs the keyed near
/// field (0.40 of a row against 0.14; at the listener's 0.035 against 0.30), the reason a listener's gain is its
/// own. (The record's §15.10 read both before §16.20 at `β = 0` on a contiguous open block: the near field 0.818
/// of a row, the loudest far source 0.005.)
#[test]
fn a_listener_s_founding_row_keeps_its_near_field() {
    let d = Declaration { alphabet: 44, width: 32, heads: 5, modes: 8, still: 2, contacts: 32, ticks: 2, frames: 5, reach: 484, lanes: 1, depth: 0, carry: 0, triads: 0, opening: false, junction: false, mark: false, loud: false, crossing: false, closed: 0, pump: false, lane_leak: false, friction: false, friction_gate: false, fade: false };
    assert_eq!((d.score_shift(), d.listen_shift()), (-2, 2));
    let sites = 420;
    let classes = drawn_classes(7, sites, d.alphabet);
    let open: Vec<bool> = (0..sites).map(|t| t >= sites - 40 && t % 2 == 0).collect();
    let r = Region { classes: &classes, unresolved: &open, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None };
    let read = |field: &Constitution| -> (u128, u128) {
        let pass = field.pass(&r, true).unwrap();
        let (mut near, mut peak) = (0u128, 0u128);
        for cell in &pass.ticks {
            for (hi, row) in cell.rows.iter().enumerate() {
                let i = hi % sites;
                if !open[i] {
                    continue;
                }
                near += row.iter().filter(|s| (s.j as usize).abs_diff(i) < NEAR).map(|s| s.p as u128).sum::<u128>();
                peak += row.iter().filter(|s| (s.j as usize).abs_diff(i) >= NEAR).map(|s| s.p as u128).max().unwrap_or(0);
            }
        }
        (near, peak)
    };
    let field = Constitution::found(d, &keys(1 << 20)).unwrap();
    let (near, peak) = read(&field);
    eprintln!("LISTENER_FOUNDING near={} far_peak={} (millionths of a row on the mean)", (near * 1_000_000 >> SHARE_BITS) / 200, (peak * 1_000_000 >> SHARE_BITS) / 200);
    assert!(near > peak, "the near field holds more of a listener's row than its loudest far source");
    let mut hot = field.clone();
    for h in 0..d.heads {
        hot.theta[hot.layout.temper + 2 * h + 1] = hot.theta[hot.layout.temper + 2 * h];
    }
    let (near, peak) = read(&hot);
    eprintln!("LISTENER_AT_CLASS_GAIN near={} far_peak={}", (near * 1_000_000 >> SHARE_BITS) / 200, (peak * 1_000_000 >> SHARE_BITS) / 200);
}



/// [agent-inferred, November 2] **The pace's covector against its code** (§16, Law 1): on the shaped field (every
/// family drawn, the paces too, so the clocks run off the byte place at fractional, stopping and fast rates), on the
/// plain region and a long far-support region, each paced head's three largest pace entries are read by the slope
/// of the code over two windows, `±4δ` and `±8δ` (17 reads each, a line fitted), and both agree with the covector's
/// prediction within the far-support test's tolerance. A window that crosses a sheet is halved as there.
#[test]
fn the_pace_covector_matches_the_code_at_two_steps() {
    // [§16.34] The sheets read with the probes' classes as the covector's own test reads them: a receiver whose probed
    // classes change crosses a seam its covector does not read.
    let sheets = |field: &Constitution, r: &Region| -> Vec<Vec<u32>> { field.pass(r, true).unwrap().ticks.iter().flat_map(|c| c.classes.iter().map(|l| l.off.iter().chain(&l.members).copied().chain(l.probes.iter().flat_map(|p| std::iter::once(u32::MAX).chain(p.iter().copied()))).collect())).collect() };
    let long: Vec<usize> = (0..26).map(|t| [1usize, 3, 2, 4, 0, 2, 1][t % 7]).collect();
    let long_open: Vec<bool> = (0..26).map(|t| t % 9 == 4 || t == 25).collect();
    // [§16.47] A silent stretch of six places past the last arrival, whose rates return to its first place.
    let stretch_open: Vec<bool> = (0..26).map(|t| t % 9 == 4 || t >= 20).collect();
    let (mut read, mut seams) = (0usize, 0usize);
    for (still, depth) in [(0usize, 0usize), (1, 0), (0, 1), (1, 1)] {
        let mut d = tiny_declaration(still);
        d.reach = 32;
        d.depth = depth;
        let mut field = Constitution::found(d, &keys(1 << 14)).unwrap();
        let stream = keys(1 << 15);
        for (k, v) in field.theta.iter_mut().enumerate() {
            let word = &stream[4 * k..4 * k + 4];
            let grain = field.layout.families.iter().find(|(s, l, _)| (*s..*s + *l).contains(&k)).unwrap().2;
            *v = (((i32::from_be_bytes([word[0], word[1], word[2], word[3]]) as i64) << grain) >> 32) as i32;
        }
        for r in [region(), Region { classes: &long, unresolved: &long_open, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None }, Region { classes: &long, unresolved: &stretch_open, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None }] {
            let pass = field.pass(&r, true).unwrap();
            assert!(pass.paces.plain.iter().all(|&p| !p), "the shaped clocks are no byte place");
            let g = covector_of(&field, &r);
            let (start, len) = (field.layout.pace, field.layout.pace + d.paced_heads() * (d.alphabet + 1));
            let mut entries: Vec<usize> = (start..len).collect();
            entries.sort_by_key(|&i| std::cmp::Reverse(g[i].unsigned_abs()));
            for &i in entries.iter().take(3).filter(|&&i| g[i] != 0) {
                let grain = MATERIAL_BITS;
                let base = sheets(&field, &r);
                let moved = |k: i32, step: i32| { let mut f = field.clone(); f.theta[i] += k * (step / 2); f };
                for (window, delta0) in [(4, 1i32 << (grain - 9)), (8, 1i32 << (grain - 9))] {
                    let points: Vec<i32> = (-8..=8).collect();
                    let Some(w) = (0..=STRADDLE_HALVINGS).find(|&w| points.iter().all(|&k| sheets(&moved(k * window / 4, delta0 >> w), &r) == base)) else {
                        seams += 1;
                        continue;
                    };
                    let step = (delta0 >> w) * window / 4;
                    let weighted: i128 = points.iter().map(|&k| k as i128 * moved(k, step).code(&r).unwrap().0 as i128).sum();
                    let squares: i128 = points.iter().map(|&k| (k * k) as i128).sum();
                    let measured = div_nearest(4 * weighted, squares);
                    let predicted = (g[i] * 2 * step as i128) >> (40 + grain - 20);
                    assert!((measured - predicted).abs() <= predicted.abs() / 8 + (64 << w), "still {still} pace entry {i} window ±{window}δ at {w} halvings: measured {measured}, predicted {predicted}");
                    read += 1;
                }
            }
        }
    }
    eprintln!("PACE_PROBES read={read} on_a_seam={seams}");
    assert!(read >= 16 && 8 * seams <= read, "read {read}, {seams} on a seam");
}



/// [definition; §16.44] **A blank place runs at its expected duration**: on the shaped field (its paces drawn), every tick
/// after the first runs each silent open site at `1 + Σ_a w_a c_h[a]` for the face the tick before gave it, while every
/// written site keeps its own class's rate; the first tick runs the blanks at the bare rate; a region with no blank, and a
/// founded field (every rate one), read the pass's clocks in every tick.
#[test]
fn a_blank_place_runs_at_its_expected_duration() {
    let mut field = shaped(1);
    let r = region();
    let pass = field.pass(&r, true).unwrap();
    assert!(pass.ticks[0].clock.is_none(), "the first tick runs the blanks at the bare rate");
    let d = field.declaration;
    let width = d.alphabet + 1;
    let mut moved = false;
    for cell in &pass.ticks[1..] {
        let clock = cell.clock.as_ref().expect("a later tick reads its own clocks");
        for (p, kappa) in clock.paces.kappa.iter().enumerate() {
            let base = field.layout.pace + p * width;
            for (t, &k) in kappa.iter().enumerate() {
                if Constitution::silent(&r, t) {
                    let face = clock.blank[t].as_ref().expect("a blank's face");
                    let rate = release(face.iter().map(|&(c, w)| w as i128 * field.theta[base + c as usize] as i128).sum(), STATE_BITS);
                    assert_eq!(k as i128, (1i128 << PACE_BITS) + rate, "site {t}");
                    moved |= k != 1 << PACE_BITS;
                } else {
                    assert_eq!(k, pass.paces.kappa[p][t], "a written site keeps its rate, site {t}");
                }
            }
        }
    }
    assert!(moved, "no blank ran off the bare rate");
    // [§16.47] Past the last arrival the silent stretch is one passage: every place there runs at its first place's rate,
    // so a place `D` past it reads `τ_f + D κ₁`, while a silent place between two arrivals keeps its own face's rate; [the
    // unified-theory reading of November 6, 08:16] a face past the stretch's first place is read by no clock and is not read.
    let long: Vec<usize> = (0..14).map(|t| [1usize, 3, 2, 4, 0, 2, 1][t % 7]).collect();
    let open: Vec<bool> = (0..14).map(|t| t == 2 || t >= 7).collect();
    let stretch = Region { classes: &long, unresolved: &open, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None };
    assert_eq!(Constitution::silent_stretch(&stretch), 7);
    let mut between = false;
    for cell in &field.pass(&stretch, true).unwrap().ticks[1..] {
        let clock = cell.clock.as_ref().expect("a later tick reads its own clocks");
        for (p, kappa) in clock.paces.kappa.iter().enumerate() {
            let base = field.layout.pace + p * width;
            let own = |t: usize| (1i128 << PACE_BITS) + release(clock.blank[t].as_ref().unwrap().iter().map(|&(c, w)| w as i128 * field.theta[base + c as usize] as i128).sum(), STATE_BITS);
            assert_eq!(kappa[2] as i128, own(2), "a silent place between arrivals keeps its rate");
            between |= own(2) != 1 << PACE_BITS;
            assert_eq!(kappa[7] as i128, own(7));
            for t in 8..14 {
                assert_eq!(kappa[t], kappa[7], "place {t} runs at the stretch's first rate");
                assert_eq!(clock.paces.tau[p][t] as i128, clock.paces.tau[p][7] as i128 + (t - 7) as i128 * kappa[7] as i128, "the clock at {t} is c_f + D κ₁");
                assert!(clock.blank[t].is_none() && clock.reads[t].is_none(), "place {t}'s face is read by no clock");
            }
        }
    }
    assert!(between, "a silent place between arrivals never ran off the bare rate");
    // [the depth rings] A depth ring takes no blank face: every silent place runs at rate zero at every tick.
    let ring = shaped_with(Declaration { depth: 1, ..tiny_declaration(1) });
    for cell in &ring.pass(&stretch, true).unwrap().ticks[1..] {
        let clock = cell.clock.as_ref().expect("a later tick reads its own clocks");
        for kappa in &clock.paces.kappa {
            for t in (0..14).filter(|&t| Constitution::silent(&stretch, t)) {
                assert_eq!(kappa[t], 0, "a depth ring's silent place {t} turns");
            }
        }
    }
    // Declared against it, the per-blank clock runs every silent place at its own face's rate past the last arrival too.
    let mut per_blank = field.clone();
    per_blank.per_blank_clock = true;
    for cell in &per_blank.pass(&stretch, true).unwrap().ticks[1..] {
        let clock = cell.clock.as_ref().expect("a later tick reads its own clocks");
        for (p, kappa) in clock.paces.kappa.iter().enumerate() {
            let base = per_blank.layout.pace + p * width;
            for t in 7..14 {
                let own = (1i128 << PACE_BITS) + release(clock.blank[t].as_ref().unwrap().iter().map(|&(c, w)| w as i128 * per_blank.theta[base + c as usize] as i128).sum(), STATE_BITS);
                assert_eq!(kappa[t] as i128, own, "the per-blank clock at place {t}");
            }
        }
    }
    let written: Vec<bool> = r.unresolved.iter().map(|_| false).collect();
    let full = Region { unresolved: &written, ..r };
    assert!(field.pass(&full, true).unwrap().ticks.iter().all(|c| c.clock.is_none()), "a region with no blank reads one clock");
    let l = field.layout.clone();
    for v in &mut field.theta[l.pace..l.pace + d.paced_heads() * width] {
        *v = 0;
    }
    let plain = field.pass(&r, true).unwrap();
    for cell in &plain.ticks[1..] {
        assert_eq!(cell.clock.as_ref().map(|c| &c.paces), Some(&plain.paces), "at the bare rate the blanks' clocks are the pass's");
    }
}

/// [measurement] **The contact covector by where its pairs lie** (§16.20): at the founding it is zero (the readout
/// and the current's return stand at zero, so no covector reaches a contact); on the shaped field every family is
/// drawn, so a head's near and far pairs carry covector, and the reading sums each pair's `|δs|` once.
#[test]
fn the_covector_s_far_share_is_zero_at_the_founding_and_read_where_the_returns_move() {
    let founded = Constitution::found(tiny_declaration(1), &keys(1 << 14)).unwrap();
    let long: Vec<usize> = (0..14).map(|t| [1usize, 3, 2, 4, 0, 2, 1][t % 7]).collect();
    let open: Vec<bool> = (0..14).map(|t| t % 3 == 1).collect();
    let r = Region { classes: &long, unresolved: &open, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None };
    assert!(founded.covector_shares(&[r]).unwrap().iter().all(|&[near, far]| near == 0 && far == 0));
    let shaped = shaped(1);
    let shares = shaped.covector_shares(&[r]).unwrap();
    assert_eq!(shares.len(), shaped.declaration.heads);
    assert!(shares.iter().all(|&[near, _]| near > 0), "{shares:?}");
    assert!(shares.iter().any(|&[_, far]| far > 0), "{shares:?}");
}

/// The field with its moment's chart into the face and its bias silent (the opening before §16.22).
fn silent_moment_face(mut field: Constitution) -> Constitution {
    let (dw, m2) = (field.declaration.width, 2 * field.declaration.complex());
    let l = field.layout.clone();
    field.theta[l.moment_face..l.moment_face + dw * m2].iter_mut().for_each(|v| *v = 0);
    field.theta[l.moment_face_bias..l.moment_face_bias + dw].iter_mut().for_each(|v| *v = 0);
    field
}

/// [definition; agent-inferred, November 2, §16.22] **A site opens on its moment**: two sites whose own class and both
/// neighbours' agree open on one face where the moment's chart is silent, and apart where it reads their moments, which
/// differ past the trigram (the word each stands in); a field with no turned mode has no moment and opens them alike.
/// At the founding the moment encodings are zero, so the chart adds nothing: the faces are as before.
#[test]
fn a_site_opens_on_its_moment() {
    const WORDS: [usize; 11] = [1, 1, 2, 3, 4, 0, 0, 2, 3, 4, 1];
    const KNOWN: [bool; 11] = [false; 11];
    let r = Region { classes: &WORDS, unresolved: &KNOWN, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None };
    let (a, b) = (3usize, 8usize);
    for still in [0usize, 1, 2] {
        let field = shaped(still);
        let dw = field.declaration.width;
        let x = field.opening(&r).unwrap();
        let y = silent_moment_face(field.clone()).opening(&r).unwrap();
        assert_eq!(y[a * dw..(a + 1) * dw], y[b * dw..(b + 1) * dw], "still {still}: the trigram alone opens one face");
        if field.declaration.moment_modes() > 0 {
            assert_ne!(x[a * dw..(a + 1) * dw], x[b * dw..(b + 1) * dw], "still {still}: the moment opens them apart");
        } else {
            assert_eq!(x[a * dw..(a + 1) * dw], x[b * dw..(b + 1) * dw], "still {still}: no turned mode, no moment");
        }
    }
    let field = Constitution::found(tiny_declaration(1), &keys(1 << 14)).unwrap();
    let silent = silent_moment_face(field.clone());
    assert_ne!(field, silent, "the chart is drawn at the founding");
    assert_eq!(field.opening(&r).unwrap(), silent.opening(&r).unwrap());
    assert_eq!(field.faces(&region()).unwrap(), silent.faces(&region()).unwrap());
}

/// [theory, November 13, the design record of that day §4.4a; P60 item 1c] **A place's cavity opening is its masked opening**: at every
/// place of each fixture region, written or open, the cavity opening formed from the region's standing sums
/// ([`Constitution::cavity_openings`]) against the built opening of the region with that place unresolved and silent ([`Constitution::opening`]).
/// The difference is printed by word, in the opening's last place (`2^(−16)`), and is not assumed zero: the cavity moment recomposes the
/// far crowds from prefix sums at the standing phases, where the masked region's crowds are released at its own, so the two can part
/// by the moment's release (one unit of `2^(−16)` a mode) carried through the moment's chart. The bound read is that rounding: one unit
/// a moment mode times the chart's largest row sum on `2^(−24)`, plus one unit for the affine's own release.
#[test]
fn a_place_s_cavity_opening_is_its_masked_opening() {
    const WORDS: [usize; 11] = [1, 1, 2, 3, 4, 0, 0, 2, 3, 4, 1];
    const KNOWN: [bool; 11] = [false; 11];
    const LONG: [usize; 16] = [2, 0, 4, 1, 1, 3, 0, 2, 4, 4, 1, 0, 3, 2, 1, 0];
    const LONG_OPEN: [bool; 16] = [false, false, true, false, false, false, true, true, false, false, false, true, false, false, false, true];
    let regions = [
        ("seven places, three open", region()),
        ("eleven places, all written", Region { classes: &WORDS, unresolved: &KNOWN, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None }),
        ("sixteen places, five open", Region { classes: &LONG, unresolved: &LONG_OPEN, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None }),
    ];
    for still in [0usize, 1, 2] {
        let field = shaped(still);
        let d = &field.declaration;
        let (dw, m2) = (d.width, 2 * d.complex());
        let mf = field.layout.moment_face;
        let chart = &field.theta[mf..mf + dw * m2];
        let row_sum = (0..dw).map(|i| chart[i * m2..(i + 1) * m2].iter().map(|&c| c.unsigned_abs() as u64).sum::<u64>()).max().unwrap();
        let bound = row_sum.div_ceil(1 << 24) + 1;
        for (name, r) in &regions {
            let (worst, at, differ) = field.cavity_check(r).unwrap();
            println!("CAVITY_CHECK still={still} region=\"{name}\" places={} words={} differing_words={differ} largest_difference={worst} at_place={at} bound={bound} (units of 2^-16)", r.classes.len(), r.classes.len() * dw);
            assert!(worst <= bound, "still {still}, {name}: the cavity opening parts from the masked one by {worst} at place {at}, past the moment's release {bound}");
            // The check is not vacuous: at a written place the cavity opening is not the place's own opening (its row and its own
            // moment term are out), and where a turned mode carries a moment the cavity moment is not the standing one.
            let (cav, own) = (field.cavity_openings(r).unwrap(), field.opening(r).unwrap());
            let written: Vec<usize> = (0..r.classes.len()).filter(|&t| !r.unresolved[t]).collect();
            assert!(written.iter().all(|&t| cav[t * dw..(t + 1) * dw] != own[t * dw..(t + 1) * dw]), "still {still}, {name}: a written place's cavity opening is its own");
            if d.moment_modes() > 0 {
                let paces = field.paces(r).unwrap();
                let (cm, sm) = (field.cavity_moments_of(r, &paces).unwrap(), field.moments_of(r, &paces).unwrap());
                assert!(cm.iter().any(|&v| v != 0), "still {still}, {name}: the cavity moments are zero");
                assert!(written.iter().any(|&t| cm[t * m2..(t + 1) * m2] != sm[t * m2..(t + 1) * m2]), "still {still}, {name}: the cavity moment is the standing one");
            }
        }
    }
}

/// A tiny field with the opening's lift, every family drawn from the keys (the lift too, so its return reaches the chart and the moment).
fn opened(still: usize) -> Constitution {
    shaped_with(Declaration { opening: true, ..tiny_declaration(still) })
}

/// [P60 item 1h] The opening comparison's covector alone at `places`, its clocks' covectors folded into the strides as the pass's own fold.
fn opening_covector_of(field: &Constitution, region: &Region, places: std::ops::Range<usize>) -> Vec<i128> {
    let paces = field.paces(region).unwrap();
    let mut g = vec![0i128; field.theta.len()];
    let mut r = ClockReturn::new(paces.kappa.len(), region.classes.len(), 2 * field.declaration.complex());
    field.opening_compare_return(region, &paces, places, &mut g, &mut r.gtau, &mut r.gsig).unwrap();
    field.clock_return(region, &paces, &[], None, &mut r, &mut g).unwrap();
    g
}

/// The opening's summed code over a region's compared places, on `2^(−20)` bits.
fn opening_code(field: &Constitution, region: &Region) -> i64 {
    field.opening_codes(region).unwrap().iter().flatten().sum()
}

const LONG: [usize; 16] = [2, 0, 4, 1, 1, 3, 0, 2, 4, 4, 1, 0, 3, 2, 1, 0];
const LONG_OPEN: [bool; 16] = [false, false, true, false, false, false, true, true, false, false, false, true, false, false, false, true];

/// [theory, November 13, P60 item 1h] **The opening's comparison returns its code's covector**: on tiny fields with the opening's lift (paced
/// heads, every family drawn), for each family the entries with the largest covectors are moved by `±δ` and the summed opening code's change is
/// compared with the covector's prediction, as [`covector_matches_the_codes_difference`] reads the last tick's: the encoding's rows and bias
/// through `tied`, the lift and its bias, the unresolved row, the neighbours' strand rows, the moment's chart and bias, the moment encodings
/// (the others' terms) and the paces (their clocks). The opening's read crosses no sheet (the lane chart is smooth), so every probe is read.
/// [the lead, November 18, the frontier record §6] Read again under the known stream (a ruler's forward at `3`), where the compared opening is
/// the retarded one: the same families are reached but the two after rows, which take no covector there.
#[test]
fn the_opening_comparison_s_covector_matches_its_codes_difference() {
    for far in [0u8, 3] {
    let (mut read, mut seams, mut halvings) = (0usize, 0usize, 0u32);
    let mut reached = std::collections::BTreeSet::new();
    for still in [0usize, 1] {
        let mut field = opened(still);
        field.ruler_far = far;
        if far == 3 {
            let (l, d) = (field.layout.clone(), field.declaration);
            let r = Region { classes: &LONG, unresolved: &LONG_OPEN, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None };
            let g = opening_covector_of(&field, &r, 0..r.classes.len());
            assert!(g[l.after..l.after + (d.alphabet + 1) * d.width].iter().all(|&v| v == 0), "still {still}: the retarded opening's after rows take no covector");
            assert!(g[l.moment_after..l.moment_after + (d.alphabet + 1) * 2 * d.moment_modes()].iter().all(|&v| v == 0), "still {still}: the retarded moments' after rows take none");
            let mut law = field.clone();
            law.ruler_far = 0;
            assert_ne!(opening_code(&field, &r), opening_code(&law, &r), "still {still}: the retarded opening's code is not the law's");
        }
        for r in [region(), Region { classes: &LONG, unresolved: &LONG_OPEN, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None }] {
            let g = opening_covector_of(&field, &r, 0..r.classes.len());
            let places = r.classes.len() as i128;
            for &(start, len, grain) in field.families() {
                let natural: u32 = if grain == MATERIAL_BITS { 40 } else { 24 };
                let mut entries: Vec<usize> = (start..start + len).collect();
                entries.sort_by_key(|&i| std::cmp::Reverse(g[i].unsigned_abs()));
                for i in entries.into_iter().take(3) {
                    if g[i] == 0 {
                        continue;
                    }
                    // The opening's read has no sheet: the lane chart `r / ‖r‖_rms` is smooth, and no contact selects a support.
                    let straddles = |_: i32| false;
                    let shift = natural + grain - 20;
                    let Some((delta, h)) = probe_step(grain, &|delta: i32| (g[i] * 2 * delta as i128) >> shift, &straddles) else {
                        seams += 1;
                        continue;
                    };
                    halvings += h;
                    let (mut plus, mut minus) = (field.clone(), field.clone());
                    plus.theta[i] += delta;
                    minus.theta[i] -= delta;
                    read += 1;
                    reached.insert(start);
                    let measured = (opening_code(&plus, &r) - opening_code(&minus, &r)) as i128;
                    let predicted = (g[i] * 2 * delta as i128) >> shift;
                    let tolerance = predicted.abs() / 8 + ((64 * ((places + 2) / 3)) << h);
                    assert!((measured - predicted).abs() <= tolerance, "still {still} family at {start} (grain {grain}) entry {i} at {h} halvings: measured {measured}, predicted {predicted}");
                }
            }
        }
    }
    let l = opened(0).layout;
    let named = [("enc", l.enc), ("before", l.before), ("after", l.after), ("read_bias", l.read_bias), ("moment_before", l.moment_before), ("moment_after", l.moment_after), ("pace", l.pace), ("moment_face", l.moment_face), ("moment_face_bias", l.moment_face_bias), ("opening", l.opening), ("opening_bias", l.opening_bias)];
    eprintln!("OPENING_PROBES far={far} read={read} halvings={halvings} on_a_seam={seams} families_reached={}", named.iter().filter(|(_, s)| reached.contains(s)).map(|(n, _)| *n).collect::<Vec<_>>().join(","));
    for (name, start) in named {
        let sided_out = far == 3 && (name == "after" || name == "moment_after");
        assert!(reached.contains(&start) != sided_out, "at {far}: the opening's covector was read against its code in family {name}, or reached a family the retarded opening does not read");
    }
    assert!(16 * seams <= read, "read {read} probes, {seams} on a seam at the smallest step");
    }
}

/// [theory, November 13, P60 items 1b and 1h] **A place's own row, own moment term and own stride are no operand of its comparison**: on the
/// forward, a place's cavity opening and its opening face stand when the class written there changes (to every other class, written or open),
/// to the moment's release carried through the chart (the bound of [`a_place_s_cavity_opening_is_its_masked_opening`]); on the return, one
/// place's comparison alone, at a place whose class is written nowhere else in the region, returns nothing to that class's strand rows and
/// moment encodings, and to its encoding row only the readout's own term (`tied`: `release(δz_u y⁰, 16)`); its stride's covector is printed, the
/// remainder of its cavity moment's releases ([`moment`]'s test of the own stride bounds it).
#[test]
fn a_place_s_comparison_reaches_nothing_of_its_own() {
    for still in [0usize, 1] {
        let field = opened(still);
        let d = &field.declaration;
        let (dw, m2, a) = (d.width, 2 * d.complex(), d.alphabet);
        let mf = field.layout.moment_face;
        let chart = &field.theta[mf..mf + dw * m2];
        let row_sum = (0..dw).map(|i| chart[i * m2..(i + 1) * m2].iter().map(|&c| c.unsigned_abs() as u64).sum::<u64>()).max().unwrap();
        let bound = row_sum.div_ceil(1 << 24) + 1;
        let (mut worst, mut changes) = (0u64, 0usize);
        for (classes, open) in [(&CLASSES[..], &OPEN[..]), (&LONG[..], &LONG_OPEN[..])] {
            let r = Region { classes, unresolved: open, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None };
            let x = field.cavity_openings(&r).unwrap();
            for t in 0..classes.len() {
                for c in 0..a {
                    for u in [false, true] {
                        let mut cs = classes.to_vec();
                        let mut us = open.to_vec();
                        (cs[t], us[t]) = (c, u);
                        let changed = Region { classes: &cs, unresolved: &us, ..r };
                        let y = field.cavity_openings(&changed).unwrap();
                        for (p, q) in x[t * dw..(t + 1) * dw].iter().zip(&y[t * dw..(t + 1) * dw]) {
                            worst = worst.max(p.abs_diff(*q));
                        }
                        changes += 1;
                    }
                }
            }
        }
        println!("OWN_FORWARD still={still} changes={changes} largest_difference={worst} bound={bound} (units of 2^-16)");
        assert!(worst <= bound, "still {still}: a place's cavity opening moved by {worst} with its own class");
        // The return of one place's comparison alone, at the places whose class the region writes nowhere else.
        let r = region();
        let l = &field.layout;
        let paces = field.paces(&r).unwrap();
        let tm = d.moment_modes();
        let x = field.cavity_openings(&r).unwrap();
        let reach_o = reach(&field.theta[l.opening..l.opening + dw * dw]);
        for t in 0..CLASSES.len() {
            let u = CLASSES[t];
            if CLASSES.iter().filter(|&&c| c == u).count() > 1 {
                continue;
            }
            let g = opening_covector_of(&field, &r, t..t + 1);
            for (name, base, width) in [("before", l.before, dw), ("after", l.after, dw), ("moment_before", l.moment_before, 2 * tm), ("moment_after", l.moment_after, 2 * tm)] {
                assert!(g[base + u * width..base + (u + 1) * width].iter().all(|&v| v == 0), "still {still} place {t}: its comparison reached its own class's {name} row");
            }
            let read = field.opening_read(&x[t * dw..(t + 1) * dw], reach_o).unwrap();
            let dz = read.face.covector(u);
            let tied: Vec<i128> = read.lift.iter().map(|&y| release(dz[u] as i128 * y as i128, STATE_BITS)).collect();
            assert_eq!(g[l.enc + u * dw..l.enc + (u + 1) * dw].to_vec(), tied, "still {still} place {t}: its own encoding row took more than the readout's term");
            let strides: Vec<i128> = (0..paces.kappa.len()).map(|p| g[l.pace + p * (a + 1) + u]).collect();
            println!("OWN_STRIDE still={still} place={t} class={u} stride_covector_by_paced_head={strides:?}");
        }
    }
}

/// [theory, November 13, P60 items 1a, 1f and 3] **A learner founds the opening's lift and keeps every line**: the founded learner's text equals
/// the source's but the declaration's head (`v14g` with the opening's word), the material, first and second moments (each the source's with the
/// block appended), and the parts line (the opening's octave appended at 0); its field reads the same last-tick faces, restores from its text,
/// and a section on it returns the opening's codes. A field read without the block reads as the declaration without it.
#[test]
fn a_learner_founds_the_opening_lift_and_keeps_every_line() {
    let mut learner = Learner::new(shaped(1), 6);
    learner.rate_parts = Some(RateParts { contacts_before: learner.field.declaration.contacts, octaves: [1; PARTS] });
    learner.section(&[region()]).unwrap();
    let founded = learner.with_opening().unwrap();
    assert!(founded.field.declaration.opening && !learner.field.declaration.opening);
    let (dw, l) = (founded.field.declaration.width, &founded.field.layout);
    assert_eq!(l.opening, learner.field.material_len());
    assert_eq!(founded.field.material_len(), learner.field.material_len() + dw * dw + dw);
    assert!(founded.field.theta[l.opening..].iter().all(|&v| v == 0), "the lift is founded at zero");
    assert_eq!(founded.field.theta[..l.opening], learner.field.theta[..], "every standing entry kept");
    assert_eq!(founded.rate_parts.unwrap().octaves[OPENING_PART], 0);
    assert_eq!(founded.field.faces(&region()).unwrap(), learner.field.faces(&region()).unwrap(), "the last tick reads as before");
    let (a, b) = (learner.to_text(), founded.to_text());
    let (la, lb): (Vec<&str>, Vec<&str>) = (a.lines().collect(), b.lines().collect());
    assert_eq!(la.len(), lb.len());
    for (k, (x, y)) in la.iter().zip(&lb).enumerate() {
        if x == y {
            continue;
        }
        let (wx, wy): (Vec<&str>, Vec<&str>) = (x.split(' ').collect(), y.split(' ').collect());
        match k {
            1 => assert!(wy[0] == "hnn-field-v14g" && wy.last() == Some(&"1"), "the declaration's head: {y}"),
            _ if wx[0] == "parts" => assert_eq!((&wy[..wx.len()], wy.len()), (&wx[..], wx.len() + 1), "the parts line gains the opening's octave"),
            _ => assert_eq!(&wy[..wx.len()], &wx[..], "line {k} keeps every standing word, the block appended"),
        }
    }
    let back = Learner::from_text(&b).unwrap();
    assert_eq!(back.to_text(), b);
    let mut trained = founded.clone();
    let receipt = trained.section(&[region()]).unwrap();
    assert_eq!(receipt.opening.len(), 1);
    assert_eq!(receipt.opening[0].1, CLASSES.len(), "every place compared");
    assert!(learner.section(&[region()]).unwrap().opening.is_empty(), "no codes without the lift");
}

/// [§16.23] **A region's covector is its state's in the joint code**: a region whose `K` open sites were drawn from a
/// domain of `m` returns the covector of its code read at `m/K`, the unweighed covector times `m/K` to the releases'
/// rounding, and its weight is `(m, K)`, `(K, K)` with no domain declared. [§16.28] The moment chart's covector is the
/// outer product `Σ_t δx⁰_t s_tᵀ`, so the opening covector's rounding at each site enters it times that site's moment:
/// its entries are read to sixteen of the opening covector's units times `Σ_t |s_t|` beside the relative bound (on this
/// fixture the moments reach about `2^16`, and an entry whose terms cancel to a sixth of their sum is otherwise read
/// past it).
#[test]
fn a_region_s_covector_is_weighed_by_its_domain() {
    let field = shaped(1);
    let plain = region();
    let open = OPEN.iter().filter(|&&u| u).count() as u64;
    assert_eq!(plain.weight(), (open, open));
    let weighed = Region { domain: Some(7), ..region() };
    assert_eq!(weighed.weight(), (7, open));
    let (g1, g7) = (covector_of(&field, &plain), covector_of(&field, &weighed));
    let m2 = 2 * field.declaration.complex();
    let moment = field.pass(&plain, false).unwrap().moment;
    let mf = field.layout.moment_face;
    let rounding = |i: usize| -> i128 {
        if !(mf..mf + field.declaration.width * m2).contains(&i) {
            return 0;
        }
        let col = (i - mf) % m2;
        16 * (0..CLASSES.len()).map(|t| moment[t * m2 + col].unsigned_abs() as i128).sum::<i128>()
    };
    let mut read = 0usize;
    for (i, (&a, &b)) in g1.iter().zip(&g7).enumerate() {
        let scaled = a * 7 / open as i128;
        if scaled.abs() < 1 << 20 {
            continue;
        }
        read += 1;
        assert!((b - scaled).abs() <= scaled.abs() / 64 + 4096 + rounding(i), "entry {i}: weighed {b}, plain times m/K {scaled}");
    }
    assert!(read > 32, "{read} entries read");
}

/// [§16.24] **A port's code is its coupling's**: the region's code is its place-wise code before the port and the
/// coupling code over the port's places.
#[test]
fn a_port_is_read_through_its_coupling() {
    let field = shaped(1);
    const PORTED: [bool; 7] = [false, true, false, false, true, true, true];
    let target = [2usize, 3];
    let r = Region { classes: &CLASSES, unresolved: &PORTED, faces: &[], locked: &[], echo: &[], domain: None, port: Some(Port { start: 4, void: 0, target: &target, boundary: false, stop: None, heard: None, window: false, letters: false }), before: false, strand: false, past: false, second: false, targets: None };
    let faces = field.faces(&r).unwrap();
    let place = faces[1].as_ref().unwrap().code(CLASSES[1]);
    let at: Vec<(&[u128], u128)> = faces[4..].iter().map(|f| { let f = f.as_ref().unwrap(); (f.masses.as_slice(), f.total) }).collect();
    let coupled = crate::coupling::coupling_code(&at, 0, &target, None).unwrap().code;
    assert_eq!(field.code(&r).unwrap(), (place + coupled, 1 + 3));
    let unported = Region { port: None, ..r };
    assert_ne!(field.code(&unported).unwrap().0, field.code(&r).unwrap().0, "the place-wise code differs from the coupling's");
}

/// [§16.47] **A port compared at its boundary codes only whether the answer has ended**: before the target's end a place
/// codes `−log₂(1 − p̂_void)` and its covector moves the void alone against the letters by their own shares (each row sums
/// to zero within its rounding, and a letter's entry is its share times the void's over the letters'), past it a place
/// codes the void; the region's code is its place-wise code before the port and that boundary code over the port.
#[test]
fn a_port_at_its_boundary_codes_only_the_end() {
    use crate::field::face_code;
    let field = shaped(1);
    const PORTED: [bool; 7] = [false, true, false, false, true, true, true];
    let target = [2usize, 3];
    let port = Port { start: 4, void: 0, target: &target, boundary: true, stop: None, heard: None, window: false, letters: false };
    let r = Region { classes: &CLASSES, unresolved: &PORTED, faces: &[], locked: &[], echo: &[], domain: None, port: Some(port), before: false, strand: false, past: false, second: false, targets: None };
    let faces = field.faces(&r).unwrap();
    let at: Vec<(&[u128], u128)> = faces[4..].iter().map(|f| { let f = f.as_ref().unwrap(); (f.masses.as_slice(), f.total) }).collect();
    let (rows, code) = port_reading(&at, &port).unwrap();
    let mut expected = 0i64;
    let one = 1i64 << crate::field::COVECTOR_BITS;
    for (i, ((masses, total), row)) in at.iter().zip(&rows).enumerate() {
        let share = |a: usize| (((masses[a] << crate::field::COVECTOR_BITS) + total / 2) / total) as i64;
        if i < target.len() {
            expected += face_code(total - masses[0], *total);
            assert_eq!(row[0], share(0), "the void's entry is its share, place {i}");
            assert!(row.iter().sum::<i64>().abs() <= row.len() as i64, "a letter place's row sums to zero, place {i}: {row:?}");
            for a in 1..row.len() {
                let predicted = -(share(a) as i128 * share(0) as i128 / (one - share(0)) as i128) as i64;
                assert!((row[a] - predicted).abs() <= 1, "letter {a} at place {i}: {} against {predicted}", row[a]);
            }
        } else {
            expected += face_code(masses[0], *total);
            assert_eq!(row[0], share(0) - one, "past the end the void is the target, place {i}");
        }
    }
    assert_eq!(code, expected);
    let place = faces[1].as_ref().unwrap().code(CLASSES[1]);
    assert_eq!(field.code(&r).unwrap(), (place + expected, 1 + 3));
}

/// [definition; §16.28, §16.34] **An open site is silent on the strand**: on a field whose every family is drawn (the
/// unresolved rows of the moment encodings and the paces among them), an open stretch appended past a region adds nothing
/// to any moment or clock; its own openings reach the region only through the strand's pair contacts, one site a tick, so
/// a stretch longer than the ticks reach leaves every original site's face as a longer one does: the writer's long open
/// extent reads its answer places as a short training region does.
#[test]
fn an_open_stretch_leaves_the_other_sites_faces_as_they_were() {
    for still in [0usize, 1] {
        let field = shaped(still);
        let ticks = field.declaration.ticks;
        let stretched = |extra: usize| {
            let mut classes = CLASSES.to_vec();
            let mut open = OPEN.to_vec();
            classes.extend(std::iter::repeat_n(0usize, extra));
            open.extend(std::iter::repeat_n(true, extra));
            let r = Region { classes: &classes, unresolved: &open, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None };
            field.faces(&r).unwrap()[..CLASSES.len()].to_vec()
        };
        assert_eq!(stretched(ticks + 2), stretched(ticks + 5), "still {still}");
    }
}


/// [§16.30] **A step stands at the size its own section certified**: under the field's law no step is held, the next
/// section opens on the stepped material, and its receipt reads no held step.
#[test]
fn a_step_stands_unread_at_its_certified_size() {
    let field = Constitution::found(tiny_declaration(1), &keys(1 << 14)).unwrap();
    let mut learner = Learner::new(field, 2);
    assert!(!learner.read_held);
    let mut deposited = 0;
    for _ in 0..6 {
        let before = learner.field.clone();
        let receipt = learner.section(&[region()]).unwrap();
        assert!(receipt.next.is_none() && !learner.holds_step());
        if receipt.deposited {
            deposited += 1;
            assert_ne!(learner.field, before);
            let stepped = learner.field.code(&region()).unwrap().0;
            let next = learner.section(&[region()]).unwrap();
            assert_eq!(next.code_before, stepped, "the next section opens on the stepped material");
        }
    }
    assert!(deposited > 0);
}



/// [definition; §16.36] **The places keep moving**: refinement passes rewrite places of a written answer (some seed's answer
/// changes), every place stays a class of the alphabet, the closing law still holds (every place past the first void is the
/// void), the same seed draws the same refined answer, and a face that is a point mass at one class still writes it everywhere.
#[test]
fn refinement_revisits_the_written_answer() {
    let mut field = shaped(1);
    let questions: [&[usize]; 2] = [&[1, 4, 0, 2], &[3, 3]];
    let problems: Vec<(&[usize], usize)> = questions.iter().zip([9usize, 8]).map(|(q, a)| (*q, a)).collect();
    let mut moved = false;
    for seed in 11..19 {
        let once = field.sample_realized(&problems, 4, 0, 0, seed, &mut Host, &mut |_, _| true).unwrap();
        let refined = field.sample_realized(&problems, 4, 2, 0, seed, &mut Host, &mut |_, _| true).unwrap();
        assert_eq!(field.sample_realized(&problems, 4, 2, 0, seed, &mut Host, &mut |_, _| true).unwrap(), refined, "the same draws");
        for places in &refined {
            assert!(places.iter().all(|&c| c < field.declaration.alphabet));
            if let Some(end) = places.iter().position(|&c| c == 0) {
                assert!(places[end..].iter().all(|&c| c == 0), "a letter past the first void, seed {seed}: {places:?}");
            }
        }
        moved |= refined != once;
    }
    assert!(moved, "no refinement moved a place");
    let l = field.layout.clone();
    field.theta[l.read_bias + 2] = 40 << 16;
    let pointed = field.sample_realized(&problems, 3, 2, 0, 11, &mut Host, &mut |_, _| true).unwrap();
    assert!(pointed.iter().flatten().all(|&c| c == 2), "{pointed:?}");
}

/// The host realization, the regions each read meets counted.
struct RegionsCounted {
    regions: Vec<usize>,
}

impl Realization for RegionsCounted {
    fn read_and_return(&mut self, field: &Constitution, regions: &[Region]) -> Result<(Vec<Vec<Option<TowerFace>>>, Vec<i128>)> {
        field.read_and_return(regions)
    }
    fn read_faces(&mut self, field: &Constitution, regions: &[Region]) -> Result<Vec<Vec<Option<TowerFace>>>> {
        self.regions.push(regions.len());
        field.read_faces(regions)
    }
    fn read_logits(&mut self, field: &Constitution, regions: &[Region]) -> Result<Vec<ReadLogits>> {
        field.read_logits(regions)
    }
    fn read_landmarks(&mut self, field: &Constitution, region: &Region, question: usize, sites: &[usize], count: usize) -> Result<Vec<Vec<(usize, u64)>>> {
        field.landmarks(region, question, sites, count)
    }
}

/// [agent-inferred, November 5] **A finished problem leaves the release's reads**: written together, each problem is written
/// as it is alone, the same bits, and a read meets only the problems that still have a place to draw.
#[test]
fn a_finished_problem_leaves_the_reads() {
    let field = shaped(1);
    let questions: [&[usize]; 3] = [&[1, 4, 0, 2], &[3, 3], &[2]];
    let problems: Vec<(&[usize], usize)> = questions.iter().zip([9usize, 8, 6]).map(|(q, a)| (*q, a)).collect();
    for seed in 11..15 {
        let mut counted = RegionsCounted { regions: Vec::new() };
        let together = field.sample_realized(&problems, 9, 2, 0, seed, &mut counted, &mut |_, _| true).unwrap();
        assert!(counted.regions.iter().all(|&n| n <= problems.len()));
        assert!(counted.regions.iter().sum::<usize>() < counted.regions.len() * problems.len() || counted.regions.iter().all(|&n| n == problems.len()));
        let mut alone = Vec::new();
        for (k, problem) in problems.iter().enumerate() {
            // A problem's keys are its index's, so alone it is written as the batch's `k`th: pad the batch before it.
            let mut padded: Vec<(&[usize], usize)> = problems[..k].to_vec();
            padded.push(*problem);
            alone.push(field.sample_realized(&padded, 9, 2, 0, seed, &mut Host, &mut |_, _| true).unwrap().pop().unwrap());
        }
        assert_eq!(together, alone, "seed {seed}");
    }
}

/// [measurement; the unified-theory reading of November 5, 18:53, its check 1] **The room past the front is heard only
/// through the near field**: a writer's state (its question resolved, the places of its first octaves resolved from a truth,
/// the rest open and silent) read over the whole room and over the room cut past the front octave's end; at and before the
/// front, cut at the end itself, some of the front's open faces differ, and cut `NEAR − 1` places past it every face is the
/// whole room's, bit for bit, at two and four ticks.
#[test]
fn the_room_past_the_front_is_heard_only_through_the_near_field() {
    for still in [0usize, 1, 2] {
        for ticks in [2usize, 4] {
        let field = shaped_with(Declaration { reach: 96, ticks, ..tiny_declaration(still) });
        let reach = field.declaration.reach;
        let q = [1usize, 4, 0, 2];
        let truth = [3usize, 1, 2, 4, 1, 3, 2, 1];
        for (front, margin) in [(0u32, 0usize), (0, 4), (0, 5), (1, 5), (2, 4), (2, 5), (3, 5), (4, 5), (5, 5)] {
            // Resolved: every place of the octaves before `front` (distances below 2^front); open: the rest of the room.
            let room = reach - q.len();
            let cut = q.len() + (1usize << (front + 1)) - 1;
            let kept_faces = cut;
            let cut = (cut + margin).min(reach);
            let mut classes: Vec<usize> = q.to_vec();
            classes.extend((0..room).map(|d| if d + 1 < (1 << front) { truth[d % truth.len()] } else { 0 }));
            let open: Vec<bool> = (0..classes.len()).map(|t| t >= q.len() && t + 1 - q.len() >= (1 << front)).collect();
            let full = field.faces(&Region { classes: &classes, unresolved: &open, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None }).unwrap();
            let short = field.faces(&Region { classes: &classes[..cut], unresolved: &open[..cut], faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None }).unwrap();
            let unequal = (0..kept_faces).filter(|&t| full[t] != short[t]).count();
            eprintln!("ROOM_CUT still={still} front={front} margin={margin} kept={kept_faces} read={cut} room={} unequal={unequal}", classes.len());
            if margin == NEAR - 1 {
                assert_eq!(unequal, 0, "still {still} front {front}: a face before the front heard the room past its near field");
            }
        }
        }
    }
}

/// [definition; the unified-theory reading of November 6, 10:31] **Past the last arrival the bare rate**: under
/// `Constitution::bare_stretch` every silent place past the region's last arrival runs at one on a turned head (its clock the place
/// count), reads no face and takes no covector, while a silent place between arrivals keeps its own face's rate.
#[test]
fn past_the_last_arrival_a_place_runs_at_the_bare_rate() {
    let mut field = shaped(0);
    field.bare_stretch = true;
    let long: Vec<usize> = (0..14).map(|t| [1usize, 3, 2, 4, 0, 2, 1][t % 7]).collect();
    let open: Vec<bool> = (0..14).map(|t| t == 2 || t >= 7).collect();
    let r = Region { classes: &long, unresolved: &open, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None };
    assert_eq!(Constitution::silent_stretch(&r), 7);
    let one = 1i64 << PACE_BITS;
    let mut between = false;
    for cell in &field.pass(&r, true).unwrap().ticks[1..] {
        let clock = cell.clock.as_ref().expect("a later tick reads its own clocks");
        assert!(clock.reads[2].is_some(), "a blank between arrivals reads its face");
        for (p, kappa) in clock.paces.kappa.iter().enumerate() {
            between |= kappa[2] != one;
            for t in 7..14 {
                assert_eq!(kappa[t], one, "place {t} runs at the bare rate");
                assert!(clock.reads[t].is_none(), "place {t} reads no face");
                assert_eq!(clock.paces.tau[p][t] - clock.paces.tau[p][6], (t - 6) as i64 * one, "the clock past the arrival counts places");
            }
        }
    }
    assert!(between, "a blank between arrivals never ran off the bare rate");
}

/// [definition; the unified-theory reading of November 6, 06:50, E] **A cut room reads and returns the whole room's bits**: the
/// opening (the question resolved, every answer place silent) compared at its boundary at a few heard places, the front and
/// far ones, with its room cut to their windows ([`Port::window`]), reads every tick's state at each heard place, each heard
/// face, the port's code and the whole covector (the clock's among it) bit for bit as the whole room does, and meets fewer
/// pairs.
#[test]
fn a_cut_room_reads_and_returns_the_whole_rooms_bits() {
    for still in [0usize, 1, 2] {
        for ticks in [2usize, 4] {
            let field = shaped_with(Declaration { reach: 400, ticks, ..tiny_declaration(still) });
            let dw = field.declaration.width;
            let q = [1usize, 4, 0, 2, 3, 1];
            let sites = field.declaration.reach;
            let mut classes: Vec<usize> = q.to_vec();
            classes.resize(sites, 0);
            let open: Vec<bool> = (0..sites).map(|t| t >= q.len()).collect();
            let target = [3usize, 1, 2, 4, 1, 3, 2, 1, 4, 2, 3];
            // The front octave and one far place an octave, as the opening hears them.
            let heard: Vec<bool> = (0..sites).map(|t| [0usize, 1, 2, 5, 13, 22, 47, 90, 200, 330].iter().any(|&d| t == q.len() + d)).collect();
            let region = |window: bool| Region {
                classes: &classes,
                unresolved: &open,
                faces: &[],
                locked: &[],
                echo: &[],
                domain: None,
                port: Some(Port { start: q.len(), void: 0, target: &target, boundary: true, stop: None, heard: Some(&heard), window, letters: false }), before: false, strand: false, past: false, second: false, targets: None
            };
            let (whole, cut) = (region(false), region(true));
            let kept = cut.window(ticks).unwrap();
            assert!(kept.iter().filter(|&&k| !k).count() > sites / 3, "still {still} ticks {ticks}: the cut leaves a room out");
            let (wr, cr) = (field.tick_reads(&whole).unwrap(), field.tick_reads(&cut).unwrap());
            let (wf, cf) = (field.faces(&whole).unwrap(), field.faces(&cut).unwrap());
            for t in (0..sites).filter(|&t| heard[t]) {
                for (k, (a, b)) in wr.iter().zip(&cr).enumerate() {
                    assert_eq!(a.read[t * dw..(t + 1) * dw], b.read[t * dw..(t + 1) * dw], "still {still} ticks {ticks}: place {t} at tick {k}");
                    assert_eq!(a.pair_read[t * dw..(t + 1) * dw], b.pair_read[t * dw..(t + 1) * dw], "still {still} ticks {ticks}: place {t}'s pair read at tick {k}");
                }
                assert_eq!(wf[t], cf[t], "still {still} ticks {ticks}: place {t}'s face");
            }
            assert_eq!(field.code(&whole).unwrap(), field.code(&cut).unwrap(), "still {still} ticks {ticks}: the port's code");
            let (_, gw) = field.read_and_return(&[whole]).unwrap();
            let (_, gc) = field.read_and_return(&[cut]).unwrap();
            let unequal = gw.iter().zip(&gc).filter(|(a, b)| a != b).count();
            assert_eq!(unequal, 0, "still {still} ticks {ticks}: the covector");
            assert!(gw.iter().any(|&v| v != 0), "still {still} ticks {ticks}: a covector to compare");
            assert!(field.met_pairs(&cut).unwrap() < field.met_pairs(&whole).unwrap(), "still {still} ticks {ticks}: the cut meets fewer pairs");
        }
    }
}

/// [definition; theory, November 16 20:39Z] **A draft is redrawn once, place by place, the rest of its run kept**: the refine takes as many
/// reads as the longest draft has places, keeps every place past each draft and the void out of each draft, keyed by its seed (the same
/// seed the same bits), and a draft of no places is the run as written.
#[test]
fn a_draft_is_redrawn_once_place_by_place() {
    let field = shaped(1);
    let questions: [&[usize]; 2] = [&[1, 4, 0, 2], &[3, 3]];
    let problems: Vec<(&[usize], usize)> = questions.iter().zip([9usize, 8]).map(|(q, a)| (*q, a)).collect();
    let written = field.sample_runs(&problems, 9, 0, 0, 13, 0, true, false, None, false, &mut Host, &mut |_, _| true, &mut |_| {}).unwrap();
    let (drafts, void) = ([5usize, 0], 0usize);
    let mut counted = RegionsCounted { regions: Vec::new() };
    let refined = field.refine_drafts(&questions, &written, &drafts, void, 17, &mut counted).unwrap();
    assert_eq!(counted.regions.len(), 5, "one read a place of the longest draft, the draft of none read never");
    assert_eq!(refined[1], written[1], "a draft of no places is its run");
    assert_eq!(refined[0][5..], written[0][5..], "the run past the draft stands");
    assert!(refined[0][..5].iter().all(|&c| c != void), "a draft place is drawn a letter");
    assert_eq!(field.refine_drafts(&questions, &written, &drafts, void, 17, &mut Host).unwrap(), refined, "the same seed, the same bits");
    assert!(field.refine_drafts(&questions, &written, &[10, 0], void, 17, &mut Host).is_err(), "a draft past its run is refused");
}

/// [definition; §16.47] **A read releases a run**: with no bound the runs are the one place a read's writer, the same bits;
/// with a bound of a bit the writer reads no more often, and its answers keep the closing law at every read, no letter at a
/// later octave while an earlier one is open, and a boundary that moves at most one place a read in the refine passes.
#[test]
fn a_read_releases_a_run() {
    let field = shaped(1);
    let questions: [&[usize]; 2] = [&[1, 4, 0, 2], &[3, 3]];
    let problems: Vec<(&[usize], usize)> = questions.iter().zip([9usize, 8]).map(|(q, a)| (*q, a)).collect();
    let octave = |d: usize| usize::BITS - 1 - d.leading_zeros();
    let (mut fewer, mut reads_one, mut reads_run) = (false, 0usize, 0usize);
    for seed in 11..19 {
        let one = field.sample_observed(&problems, 9, 2, 0, seed, &mut Host, &mut |_, _| true, &mut |_| {}).unwrap();
        assert_eq!(field.sample_runs(&problems, 9, 2, 0, seed, 0, true, false, None, false, &mut Host, &mut |_, _| true, &mut |_| {}).unwrap(), one, "no bound, one place a read");
        let mut counted = RegionsCounted { regions: Vec::new() };
        field.sample_runs(&problems, 9, 2, 0, seed, 0, true, false, None, false, &mut counted, &mut |_, _| true, &mut |_| {}).unwrap();
        reads_one += counted.regions.len();
        let mut counted = RegionsCounted { regions: Vec::new() };
        let mut last: Option<Vec<usize>> = None;
        let run = field
            .sample_runs(&problems, 9, 2, 0, seed, 1 << 20, true, false, None, false, &mut counted, &mut |_, _| true, &mut |r| {
                for (k, &(q, _)) in problems.iter().enumerate() {
                    let earliest = (q.len()..r.classes[k].len()).filter(|&t| r.open[k][t]).map(|t| octave(t + 1 - q.len())).min();
                    if let (0, Some(j)) = (r.pass, earliest) {
                        assert!((q.len()..r.classes[k].len()).all(|t| r.open[k][t] || r.classes[k][t] == 0 || octave(t + 1 - q.len()) <= j), "a letter past octave {j}, seed {seed}");
                    }
                }
                if r.pass > 0 {
                    let ends: Vec<usize> = problems.iter().enumerate().map(|(k, &(q, _))| (q.len()..r.classes[k].len()).find(|&t| r.classes[k][t] == 0 && !r.open[k][t]).unwrap_or(r.classes[k].len())).collect();
                    if let Some(before) = &last {
                        assert!(before.iter().zip(&ends).all(|(a, b)| a.abs_diff(*b) <= 1), "the end moved more than one place a read, seed {seed}");
                    }
                    last = Some(ends);
                }
            })
            .unwrap();
        reads_run += counted.regions.len();
        for places in &run {
            if let Some(end) = places.iter().position(|&c| c == 0) {
                assert!(places[end..].iter().all(|&c| c == 0), "a letter past the first void, seed {seed}");
            }
        }
        fewer |= counted.regions.len() < reads_one;
    }
    assert!(reads_run <= reads_one, "{reads_run} reads in runs against {reads_one}");
    let _ = fewer;
}

/// [definition; the unified-theory reading of November 5, 22:38] **A void never unwrites a letter**: at every read of the
/// sweeps every place written as a letter stays that letter (a place before the last letter draws from its letters, only a
/// place past every letter from its whole face), the closing law still holds, and some write still ends before its last
/// place, in one place a read and in runs.
#[test]
fn a_void_never_unwrites_a_letter() {
    let field = shaped(1);
    let questions: [&[usize]; 2] = [&[1, 4, 0, 2], &[3, 3]];
    let problems: Vec<(&[usize], usize)> = questions.iter().zip([9usize, 8]).map(|(q, a)| (*q, a)).collect();
    let mut closed_early = false;
    for run_bound in [0i128, 1 << 20] {
        for seed in 11..27 {
            let mut letters: Vec<Vec<Option<usize>>> = problems.iter().map(|&(q, n)| vec![None; q.len() + n]).collect();
            let places = field
                .sample_runs(&problems, 4, 0, 0, seed, run_bound, true, false, None, false, &mut Host, &mut |_, _| true, &mut |r| {
                    if r.pass != 0 {
                        return;
                    }
                    for (k, &(q, _)) in problems.iter().enumerate() {
                        for t in q.len()..r.classes[k].len() {
                            if let Some(c) = letters[k][t] {
                                assert_eq!((r.open[k][t], r.classes[k][t]), (false, c), "a written letter unwritten at place {t}, seed {seed}");
                            } else if !r.open[k][t] && r.classes[k][t] != 0 {
                                letters[k][t] = Some(r.classes[k][t]);
                            }
                        }
                    }
                })
                .unwrap();
            for (places, n) in places.into_iter().zip([9usize, 8]) {
                if let Some(end) = places.iter().position(|&c| c == 0) {
                    assert!(places[end..].iter().all(|&c| c == 0), "a letter past the first void, seed {seed}");
                    closed_early |= end + 1 < n;
                }
            }
        }
    }
    assert!(closed_early, "no write ended before its last place");
}

/// [definition; the unified-theory reading of November 6, 03:08] **A given length is kept**: with each answer's length given,
/// every write holds exactly that many letters and the void past them, in the sweeps and through the refine passes, in runs and
/// one place a read.
/// [definition; the unified-theory reading of November 6, 07:21] **One end, one draw, conditioned on the room**: a profile whose
/// void mass rises to one half draws every `u` within the room (unconditioned, a `u` above one half ran to the room's end), the
/// end at the first place past `u` of the largest void mass, exactly; a profile of totals that differ reads its shares, not its
/// masses; no void mass anywhere is the room's extent.
#[test]
fn one_end_is_drawn_within_the_room() {
    let face = |void: u128, total: u128| TowerFace { masses: vec![void, total - void], total };
    let one = 1u128 << 62;
    // Void shares 0, 1/8, 1/4, 3/8, 1/2, 1/2 over six places.
    let profile: Vec<TowerFace> = [0u128, 1, 2, 3, 4, 4].iter().map(|&e| face(e * one / 8, one)).collect();
    let room: Vec<Option<&TowerFace>> = profile.iter().map(Some).collect();
    // `u` in hundredths of one, on `2^(−32)`.
    let u = |hundredths: u128| hundredths * (1u128 << 32) / 100;
    let at = |hundredths: u128| one_end_length(&room, 0, u(hundredths));
    assert_eq!(at(0), 1, "the first place with any void mass");
    assert_eq!(at(30), 2, "a void share of 1/4 passes 0.3 of 1/2");
    assert_eq!(at(70), 3, "3/8 passes 0.7 of 1/2");
    assert_eq!(at(99), 4, "a u near one ends where the profile reaches its largest, within the room");
    // Shares, not masses: the same profile on a doubled total at one place.
    let mut doubled: Vec<TowerFace> = profile.iter().map(|f| face(f.masses[0], f.total)).collect();
    doubled[2] = face(2 * one / 8, 2 * one);
    let room2: Vec<Option<&TowerFace>> = doubled.iter().map(Some).collect();
    assert_eq!(one_end_length(&room2, 0, u(30)), 3, "1/8 at place 2 no longer passes 0.3 of 1/2");
    let silent: Vec<TowerFace> = (0..4).map(|_| face(0, one)).collect();
    assert_eq!(one_end_length(&silent.iter().map(Some).collect::<Vec<_>>(), 0, 1 << 31), 4, "no void mass: the room's extent");
}

#[test]
fn a_given_length_is_kept() {
    let field = shaped(1);
    let questions: [&[usize]; 2] = [&[1, 4, 0, 2], &[3, 3]];
    let problems: Vec<(&[usize], usize)> = questions.iter().zip([9usize, 8]).map(|(q, a)| (*q, a)).collect();
    for run_bound in [0i128, 1 << 20] {
        for seed in 11..19 {
            let written = field.sample_runs(&problems, 4, 2, 0, seed, run_bound, true, false, Some(&[3, 5]), false, &mut Host, &mut |_, _| true, &mut |_| {}).unwrap();
            for (places, l) in written.iter().zip([3usize, 5]) {
                assert!(places[..l].iter().all(|&c| c != 0), "a void inside the given length, seed {seed}: {places:?}");
                assert!(places[l..].iter().all(|&c| c == 0), "a letter past the given length, seed {seed}: {places:?}");
            }
            // One end, one draw: the length drawn from the first read is kept the same way.
            let drawn = field.sample_runs(&problems, 4, 2, 0, seed, run_bound, true, false, None, true, &mut Host, &mut |_, _| true, &mut |_| {}).unwrap();
            for places in &drawn {
                let l = places.iter().position(|&c| c == 0).unwrap_or(places.len());
                assert!(places[l..].iter().all(|&c| c == 0), "a letter past the drawn end, seed {seed}: {places:?}");
            }
        }
    }
}

/// [definition; the unified-theory reading of November 5, 22:38] **The writer's region ends `NEAR` places past its lowest
/// void**: past a resolved void the read's faces are the region's cut there, every open place's face that of the cut region,
/// none past the cut; before any void, and under the whole room, the region is read whole.
#[test]
fn the_writer_reads_its_region_to_the_near_field_past_its_void() {
    let field = shaped(1);
    let q = [1usize, 4, 0, 2];
    let n = 12;
    let mut classes: Vec<usize> = q.iter().copied().chain(std::iter::repeat_n(0, n)).collect();
    let mut open: Vec<bool> = (0..classes.len()).map(|t| t >= q.len()).collect();
    for (t, c) in [(4usize, 3usize), (5, 1), (7, 2)] {
        classes[t] = c;
        open[t] = false;
    }
    let whole = Region { classes: &classes, unresolved: &open, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None };
    let read = field.read_active(&[q.len()], std::slice::from_ref(&classes), std::slice::from_ref(&open), &[0], 0, true, &mut Host).unwrap().remove(0);
    assert_eq!(read, field.faces(&whole).unwrap(), "before any void the region is read whole");
    let end = 8;
    for t in end..classes.len() {
        classes[t] = 0;
        open[t] = false;
    }
    let read = field.read_active(&[q.len()], std::slice::from_ref(&classes), std::slice::from_ref(&open), &[0], 0, true, &mut Host).unwrap().remove(0);
    let cut = Region { classes: &classes[..end + NEAR], unresolved: &open[..end + NEAR], faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None };
    let short = field.faces(&cut).unwrap();
    assert_eq!(read.len(), classes.len());
    assert_eq!(&read[..end + NEAR], &short[..], "the faces are the cut region's");
    assert!(read[end + NEAR..].iter().all(Option::is_none), "no face past the cut");
    let room = field.read_active(&[q.len()], std::slice::from_ref(&classes), std::slice::from_ref(&open), &[0], 0, false, &mut Host).unwrap().remove(0);
    assert_eq!(room, field.faces(&Region { classes: &classes, unresolved: &open, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None }).unwrap(), "the whole room, declared");
}

/// [definition; §16.47] **The answer is released by octaves of distance**: at every read of the sweeps, while a place at
/// distance `d` from the question stands open, no letter stands at a place of a later octave (`⌊log₂ d⌋`); a void's
/// closing law may resolve later places, as the void tail.
#[test]
fn the_answer_is_released_by_octaves_of_distance() {
    let field = shaped(1);
    let questions: [&[usize]; 2] = [&[1, 4, 0, 2], &[3, 3]];
    let problems: Vec<(&[usize], usize)> = questions.iter().zip([9usize, 8]).map(|(q, a)| (*q, a)).collect();
    let octave = |d: usize| usize::BITS - 1 - d.leading_zeros();
    let mut reads = 0;
    for seed in 11..19 {
        field
            .sample_observed(&problems, 9, 0, 0, seed, &mut Host, &mut |_, _| true, &mut |r| {
                for (k, &(q, _)) in problems.iter().enumerate() {
                    let earliest = (q.len()..r.classes[k].len()).filter(|&t| r.open[k][t]).map(|t| octave(t + 1 - q.len())).min();
                    if let Some(j) = earliest {
                        for t in q.len()..r.classes[k].len() {
                            if !r.open[k][t] && r.classes[k][t] != 0 {
                                assert!(octave(t + 1 - q.len()) <= j, "a letter at distance {} while octave {j} is open, seed {seed}", t + 1 - q.len());
                            }
                        }
                    }
                }
                reads += 1;
            })
            .unwrap();
    }
    assert!(reads > 0);
}

/// [definition; §16.47] **Refinement moves the end one place a read**: between any two reads of the refine passes each
/// problem's boundary (its first resolved void) moves at most one place, in or out, so no void is drawn before the last
/// letter and a boundary drawn as a letter moves out by one; the closing law holds at every read.
#[test]
fn refinement_moves_the_end_one_place_a_read() {
    let field = shaped(1);
    let questions: [&[usize]; 2] = [&[1, 4, 0, 2], &[3, 3]];
    let problems: Vec<(&[usize], usize)> = questions.iter().zip([9usize, 8]).map(|(q, a)| (*q, a)).collect();
    let mut reads = 0;
    for seed in 11..19 {
        let mut last: Option<Vec<usize>>;
        for refine in [3] {
        last = None;
        field
            .sample_observed(&problems, 4, refine, 0, seed, &mut Host, &mut |_, _| true, &mut |r| {
                if r.pass == 0 {
                    return;
                }
                let ends: Vec<usize> = problems
                    .iter()
                    .enumerate()
                    .map(|(k, &(q, _))| {
                        let end = (q.len()..r.classes[k].len()).find(|&t| r.classes[k][t] == 0 && !r.open[k][t]).unwrap_or(r.classes[k].len());
                        assert!((end..r.classes[k].len()).all(|t| r.classes[k][t] == 0 && !r.open[k][t]), "a letter past the boundary, seed {seed}");
                        end
                    })
                    .collect();
                if let Some(before) = &last {
                    for (a, b) in before.iter().zip(&ends) {
                        assert!(a.abs_diff(*b) <= 1, "the end moved {a} to {b} in one read, seed {seed}");
                    }
                }
                last = Some(ends);
                reads += 1;
            })
            .unwrap();
        }
    }
    assert!(reads > 0);
}

/// The level's field of the tower fixtures.
fn coarse_declaration() -> Declaration {
    Declaration { alphabet: 2, width: 8, heads: 2, modes: 3, still: 1, contacts: 4, ticks: 2, frames: 2, reach: 6, lanes: 1, depth: 0, carry: 0, triads: 0, opening: false, junction: false, mark: false, loud: false, crossing: false, closed: 0, pump: false, lane_leak: false, friction: false, friction_gate: false, fade: false }
}

/// A level on [`opened`]`(still)` (the level reads the opening's news): six harmonics after the first of its two ticks, founded
/// from the fixtures' keys past the fine field's founding.
fn towered(still: usize) -> Constitution {
    let field = opened(still);
    let offset = 4 * field.declaration.founding_draws();
    field.scaled_up(6, 1, coarse_declaration(), &keys(1 << 16), offset).unwrap().0
}

/// [`towered`] with its prolongation and every family of its packets' field drawn, so every path of the tower carries a
/// covector.
fn towered_live(still: usize) -> Constitution {
    let mut field = towered(still);
    let stream = keys(1 << 16);
    let families = field.families_all();
    let base = field.theta.len();
    for (n, v) in field.material_mut().enumerate().skip(base) {
        let word = &stream[4 * n..4 * n + 4];
        let k = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) as i64;
        let grain = families.iter().find(|(s, l, _)| (*s..*s + *l).contains(&n)).unwrap().2;
        *v = ((k << grain) >> 32) as i32;
    }
    field
}

/// The tower's covector over its whole material.
fn tower_covector(field: &Constitution, region: &Region) -> Vec<i128> {
    let pass = field.pass(region, true).unwrap();
    let mut g = vec![0i128; field.material_len()];
    field.returned(region, &pass, &mut g).unwrap();
    field.both_reads_mean(g)
}

/// [measurement; the lead, November 17, the level's design record §6] **The level's links are its forward's own, and the covector
/// read at its locus is the one its return consumes**: [`Constitution::level_links`] gives [`Constitution::level_trace`]'s reading
/// with every link in its shape; at the founding the prolonged rows are zero; and on a live tower the prolongation's bias takes the
/// chart of that covector, epoch by epoch (`δb_B = Σ_j release(Σ_(t∈e_j) h_k(φ_t) δx_t, 30)`), as the reverse deposits it.
#[test]
fn the_levels_links_are_its_forwards_own_and_its_locus_covector_is_the_one_its_return_consumes() {
    let region = region();
    let sites = region.classes.len();
    let founded = towered(1);
    let at_founding = founded.level_links(&region).unwrap().unwrap();
    assert!(at_founding.prolonged.iter().all(|&v| v == 0));
    let field = towered_live(1);
    let before = field.to_text();
    let links = field.level_links(&region).unwrap().unwrap();
    let trace = field.level_trace(&region).unwrap().unwrap();
    assert_eq!((&links.news, &links.anchors, &links.coarse_read), (&trace.news, &trace.anchors, &trace.coarse_read));
    assert_eq!(field.to_text(), before);
    let scale = field.scale.as_deref().unwrap();
    let (d0, d1, h, epochs) = (field.declaration.width, scale.coarse.declaration.width, scale.harmonics, links.anchors.len());
    assert_eq!((links.phase.len(), links.read.len(), links.prolonged.len(), links.covector.len()), (sites * h, sites * d0, sites * d0, sites * d0));
    assert_eq!((links.moment.len(), links.restricted.len(), links.coarse_read.len()), (epochs * h * d0, epochs * d1, epochs * d1));
    assert!(links.prolonged.iter().any(|&v| v != 0) && links.covector.iter().any(|&v| v != 0));
    let pass = field.pass(&region, true).unwrap();
    let mut g = vec![0i128; field.material_len()];
    field.returned(&region, &pass, &mut g).unwrap();
    let (_, _, _, bb, _) = scale.glue_offsets(d0);
    let base = field.theta.len() + scale.coarse.theta.len() + bb;
    for k in 0..h {
        for c in 0..d0 {
            let mut want = 0i128;
            for j in 0..epochs {
                let end = links.anchors.get(j + 1).copied().unwrap_or(sites);
                let sum: i128 = (links.anchors[j]..end).map(|t| i128::from(links.phase[t * h + k]) * i128::from(links.covector[t * d0 + c])).sum();
                want += release(sum, 30);
            }
            assert_eq!(g[base + k * d0 + c], want, "harmonic {k}, entry {c}");
        }
    }
}

/// [definition; the tower record, D1] **Growth in scale keeps every face**: a tower founded on a field (its prolongation
/// at zero) reads every face the field read, its families tile its material, and its text restores it exactly.
#[test]
fn a_tower_founded_on_a_field_reads_its_faces() {
    for still in [0usize, 1, 2] {
        let field = opened(still);
        let tower = towered(still);
        assert_eq!(tower.faces(&region()).unwrap(), field.faces(&region()).unwrap(), "still {still}");
        let cut = tower.pass(&region(), false).unwrap().tower.unwrap().cut().clone();
        assert!(cut.anchors.len() > 1 && cut.anchors.len() < region().classes.len(), "still {still}: the fixture's news cuts {} epochs of {} places", cut.anchors.len(), region().classes.len());
        let mut at = 0;
        for (start, len, _) in tower.families_all() {
            assert_eq!(start, at);
            at += len;
        }
        assert_eq!(at, tower.material_len());
        assert_eq!(Constitution::from_text(&tower.to_text()).unwrap(), tower);
    }
    let mut learner = Learner::new(towered_live(1), 6);
    learner.section(&[region()]).unwrap();
    assert_eq!(Learner::from_text(&learner.to_text()).unwrap(), Learner { last: None, ..learner });
}

/// [definition; the lead, November 17] **The store's leak** ([`Learner::leak`]): a learner with a leak deposits the unleaked learner's
/// step and then relaxes every entry by `release(θ, leak)`; an entry held by its rate does not leak; the leak is carried in the learner's
/// text, a state without the line has none, and a leak under one bit or past the carrier is refused.
#[test]
fn the_stores_leak_relaxes_each_entry_after_its_step_and_is_carried_in_the_text() {
    let mut plain = Learner::new(towered_live(1), 6);
    let mut leaky = plain.clone();
    leaky.leak = Some(4);
    for _ in 0..3 {
        let before = leaky.clone();
        let mut twin = Learner { leak: None, ..before.clone() };
        twin.section(&[region()]).unwrap();
        leaky.section(&[region()]).unwrap();
        let mut moved = 0;
        for ((&l, &t), &b) in leaky.field.material().zip(twin.field.material()).zip(before.field.material()) {
            assert_eq!(i128::from(l), i128::from(t) - release(i128::from(t), 4));
            moved += usize::from(l != b);
        }
        assert!(moved > 0);
        assert_eq!((&leaky.first, &leaky.second), (&twin.first, &twin.second), "the moments read the covector alone");
    }
    plain.section(&[region()]).unwrap();
    assert_ne!(plain.field, leaky.field);
    let text = leaky.to_text();
    assert!(text.contains("\nleak 4\n"));
    assert_eq!(Learner::from_text(&text).unwrap(), Learner { last: None, ..leaky.clone() });
    assert!(!plain.to_text().contains("leak"));
    assert_eq!(Learner::from_text(&plain.to_text()).unwrap().leak, None);
    for bad in ["leak 0", "leak 32", "leak x"] {
        assert!(Learner::from_text(&text.replace("leak 4", bad)).is_err(), "{bad}");
    }
    // An entry held by its rate neither steps nor leaks.
    let mut held = leaky.clone();
    held.own_rates = Some((0..held.field.material_len()).map(|i| if i % 2 == 0 { 100 } else { 6 }).collect());
    let before: Vec<i32> = held.field.material().copied().collect();
    held.section(&[region()]).unwrap();
    for (i, (&a, &b)) in held.field.material().zip(&before).enumerate() {
        if i % 2 == 0 {
            assert_eq!(a, b, "entry {i} is held");
        }
    }
}

/// [definition; the lead, November 18] **The step's carried remainder** ([`Learner::remainder`]): at a rate where the truncated step
/// leaves a face-grain entry where it stands, the learner that carries its remainders moves it; over the sections the released steps and
/// the remainder left sum to the finer steps with nothing lost; from one state the moments read the covector alone; and the remainders are carried in the
/// learner's text, a state without the line has none, and a remainder outside one grain is refused.
#[test]
fn the_steps_remainder_is_carried_so_a_cool_rate_still_moves_an_entry_and_nothing_is_dropped() {
    let cool = 20;
    let mut plain = Learner::new(towered_live(1), cool);
    let mut carried = plain.clone();
    carried.remainder = Some(vec![0; carried.field.material_len()]);
    let families = carried.field.families_all();
    let start: Vec<i128> = carried.field.material().map(|&v| i128::from(v)).collect();
    let mut fine_sum = vec![0i128; start.len()];
    for section in 0..6 {
        plain.section(&[region()]).unwrap();
        carried.section(&[region()]).unwrap();
        if section == 0 {
            assert_eq!((&carried.first, &carried.second), (&plain.first, &plain.second), "the moments read the covector alone");
        }
        let rates = carried.entry_rates();
        for &(at, len, grain) in &families {
            for i in at..at + len {
                fine_sum[i] += deposit_step(carried.first[i], carried.second[i], grain + REMAINDER_BITS, rates[i]);
            }
        }
    }
    let remainder = carried.remainder.as_ref().unwrap();
    let (mut moved_carried, mut moved_plain) = (0, 0);
    for (i, ((&c, &p), &s)) in carried.field.material().zip(plain.field.material()).zip(&start).enumerate() {
        // The field's step is taken off the entry: what was released and what is still carried are the finer steps' sum.
        assert_eq!(((s - i128::from(c)) << REMAINDER_BITS) + i128::from(remainder[i]), fine_sum[i], "entry {i}");
        assert!((0..1i64 << REMAINDER_BITS).contains(&remainder[i]));
        moved_carried += usize::from(i128::from(c) != s);
        moved_plain += usize::from(i128::from(p) != s);
    }
    assert!(moved_carried > moved_plain, "the carried remainder moved {moved_carried} entries, the truncated step {moved_plain}");
    let text = carried.to_text();
    assert!(text.contains("\nremainder "));
    assert_eq!(Learner::from_text(&text).unwrap(), Learner { last: None, ..carried.clone() });
    assert!(!plain.to_text().contains("remainder"));
    assert_eq!(Learner::from_text(&plain.to_text()).unwrap().remainder, None);
    let line = text.lines().find(|l| l.starts_with("remainder ")).unwrap();
    let short = line.rsplit_once(' ').unwrap().0;
    assert!(Learner::from_text(&text.replace(line, short)).is_err(), "a remainder short of an entry");
    let outside = format!("remainder {} {}", 1i64 << REMAINDER_BITS, line.strip_prefix("remainder ").unwrap().split_once(' ').unwrap().1);
    assert!(Learner::from_text(&text.replace(line, &outside)).is_err(), "a remainder outside one grain");
}

/// [definition; the tower record, D1] **The tower's covector agrees with its code's central difference** on the packets'
/// field's families and the glue's: each family's three entries with the largest covectors, moved by `±δ` (the probe law of
/// [`covector_matches_the_codes_difference`], a probe whose step moves a site or a packet across a sheet left out and
/// counted), and the live prolongation reaching the code at the bytes.
#[test]
fn the_towers_covector_matches_its_codes_difference() {
    let sheets = |field: &Constitution, r: &Region| -> Vec<Vec<u32>> {
        let pass = field.pass(r, true).unwrap();
        let coarse = pass.tower.iter().flat_map(|t| t.ticks().iter());
        pass.ticks.iter().chain(coarse).flat_map(|c| c.classes.iter().map(|l| l.off.iter().chain(&l.members).copied().chain(l.probes.iter().flat_map(|p| std::iter::once(u32::MAX).chain(p.iter().copied()))).collect())).collect()
    };
    let (mut read, mut seams) = (0usize, 0usize);
    for still in [0usize, 1, 2] {
        let field = towered_live(still);
        let r = region();
        let g = tower_covector(&field, &r);
        let base = field.theta.len();
        for (start, len, grain) in field.families_all().into_iter().filter(|&(s, _, _)| s >= base) {
            let natural: u32 = if grain == MATERIAL_BITS { 40 } else { 24 };
            let mut entries: Vec<usize> = (start..start + len).collect();
            entries.sort_by_key(|&i| std::cmp::Reverse(g[i].unsigned_abs()));
            for i in entries.into_iter().take(3).filter(|&i| g[i] != 0) {
                let moved = |delta: i32| {
                    let mut f = field.clone();
                    *f.material_mut().nth(i).unwrap() += delta;
                    f
                };
                let straddles = |delta: i32| sheets(&moved(delta), &r) != sheets(&field, &r) || sheets(&moved(-delta), &r) != sheets(&field, &r);
                let shift = natural + grain - 20;
                let Some((delta, h)) = probe_step(grain, &|delta: i32| (g[i] * 2 * delta as i128) >> shift, &straddles) else {
                    seams += 1;
                    continue;
                };
                read += 1;
                let measured = moved(delta).code(&r).unwrap().0 - moved(-delta).code(&r).unwrap().0;
                let predicted = (g[i] * 2 * delta as i128) >> shift;
                let tolerance = predicted.abs() / 8 + (64 << h);
                assert!((measured as i128 - predicted).abs() <= tolerance, "still {still} family at {start} (grain {grain}) entry {i} at {h} halvings: measured {measured}, predicted {predicted}");
            }
        }
    }
    eprintln!("TOWER_COVECTOR_PROBES read={read} on_a_seam={seams}");
    assert!(read > 0 && 16 * seams <= read, "read {read} probes, {seams} on a seam");
}


/// [definition; §16.40] **A lane founded beside a field keeps every face**: the laned field (one lane, then two, past the
/// first) reads every face the field read, its draws counted are the draws read, its families tile its material and its
/// text restores it; the laned learner keeps every old moment, opens the lane's on its family's second moment and keeps its
/// rate; and every read
/// from the lane has a covector at once (the key chart's columns over the lane among them).
#[test]
fn a_lane_founded_beside_a_field_reads_its_faces() {
    for still in [0usize, 1, 2] {
        let field = shaped(still);
        let faces = field.faces(&region()).unwrap();
        let mut laned = field.clone();
        for lanes in [2usize, 3] {
            let draws = laned.declaration.lane_draws();
            assert!(laned.laned(&keys(draws).as_slice()[..4 * draws - 1]).is_err(), "the draws counted are the draws read");
            let (next, from) = laned.laned(&keys(draws)).unwrap();
            assert_eq!(from.len(), next.theta.len());
            assert_eq!((next.declaration.width, next.declaration.lanes), (lanes * 8, lanes));
            assert_eq!(next.faces(&region()).unwrap(), faces, "still {still}, {lanes} lanes");
            let mut at = 0;
            for (start, len, _) in next.families_all() {
                assert_eq!(start, at);
                at += len;
            }
            assert_eq!(at, next.material_len());
            assert_eq!(Constitution::from_text(&next.to_text()).unwrap(), next);
            laned = next;
        }
        let g = covector_of(&laned, &region());
        let (l, dw, m2) = (laned.layout.clone(), laned.declaration.width, 2 * laned.declaration.complex());
        assert!((0..m2).any(|row| (8..dw).any(|j| g[l.q + row * dw + j] != 0)), "still {still}: the key chart's reads from the lanes carry a covector");
    }
    let mut learner = Learner::new(Constitution::found(tiny_declaration(1), &keys(1 << 14)).unwrap(), 4);
    for _ in 0..2 {
        learner.section(&[region()]).unwrap();
    }
    let stream = keys(1 << 16);
    let laned = learner.laned(&stream).unwrap();
    assert_eq!((laned.drawn, laned.rate_bits), (learner.drawn + 4 * learner.field.declaration.lane_draws(), learner.rate_bits));
    let (l, old) = (laned.field.layout().clone(), learner.field.layout().clone());
    assert_eq!(laned.first[l.read_bias], learner.first[old.read_bias]);
    assert_eq!(laned.first[l.enc + 16 + 3], learner.first[old.enc + 8 + 3], "an encoding row's old entries keep their moments");
    let enc_old = &learner.second[old.enc..old.enc + (learner.field.declaration.alphabet + 1) * 8];
    let mean = enc_old.iter().map(|v| v / enc_old.len() as i128).sum::<i128>() + enc_old.iter().map(|v| v % enc_old.len() as i128).sum::<i128>() / enc_old.len() as i128;
    assert!(mean > 0);
    assert_eq!((laned.first[l.enc + 16 + 8], laned.second[l.enc + 16 + 8]), (0, mean), "the lane's entries open on their family's statistics");
    let back = Learner { read_held: laned.read_held, ..Learner::from_text(&laned.to_text()).unwrap() };
    assert_eq!(back, laned);
}

/// [definition; the lead, November 17] **A lane founded beside a field with triads keeps every face and every product**: on the drawn triad
/// fixtures, with carry circles and without (every triad's return off zero, so every product reaches the face), the laned field reads
/// every face the field read; the triads' charts' columns over the lane and their return's rows into it are zero and every standing entry
/// of the three families keeps its place; the families tile the material and the text restores it; and the laned learner keeps every
/// triad entry's moments.
#[test]
fn a_lane_founded_beside_triads_reads_their_faces() {
    for field in [triad_shaped(1, TRIADS), circled_triad_shaped(1, TRIADS)] {
        let faces = field.faces(&region()).unwrap();
        let draws = field.declaration.lane_draws();
        let (laned, from) = field.laned(&keys(draws)).unwrap();
        assert_eq!(laned.faces(&region()).unwrap(), faces, "the faces before the lane");
        let (l, o) = (laned.layout.clone(), field.layout.clone());
        let (dw, dw2, j2, j6) = (field.declaration.width, laned.declaration.width, 2 * TRIADS, 6 * TRIADS);
        for row in 0..j6 {
            for c in 0..dw2 {
                let (at, kept) = (l.triad + row * dw2 + c, c < dw);
                assert_eq!(from[at], kept.then(|| o.triad + row * dw + c));
                assert_eq!(laned.theta[at], if kept { field.theta[o.triad + row * dw + c] } else { 0 });
            }
            assert_eq!(laned.theta[l.triad_bias + row], field.theta[o.triad_bias + row]);
        }
        for row in 0..dw2 {
            for c in 0..j2 {
                let (at, kept) = (l.w_triad + row * j2 + c, row < dw);
                assert_eq!(from[at], kept.then(|| o.w_triad + row * j2 + c));
                assert_eq!(laned.theta[at], if kept { field.theta[o.w_triad + row * j2 + c] } else { 0 });
            }
        }
        let mut at = 0;
        for (start, len, _) in laned.families_all() {
            assert_eq!(start, at);
            at += len;
        }
        assert_eq!(at, laned.material_len());
        assert_eq!(Constitution::from_text(&laned.to_text()).unwrap(), laned);
        let mut learner = Learner::new(field, 4);
        for _ in 0..2 {
            learner.section(&[region()]).unwrap();
        }
        let grown = learner.laned(&keys(1 << 16)).unwrap();
        let (l, o) = (grown.field.layout().clone(), learner.field.layout().clone());
        assert_eq!((grown.first[l.w_triad + 3], grown.second[l.w_triad + 3]), (learner.first[o.w_triad + 3], learner.second[o.w_triad + 3]), "a return entry keeps its moments");
        assert_eq!((grown.first[l.triad + dw2 + 2], grown.second[l.triad + dw2 + 2]), (learner.first[o.triad + dw + 2], learner.second[o.triad + dw + 2]), "a chart entry keeps its moments");
        assert_eq!(grown.first[l.triad + dw], 0, "a chart's entry over the lane opens with no first moment");
        let back = Learner { read_held: grown.read_held, ..Learner::from_text(&grown.to_text()).unwrap() };
        assert_eq!(back, grown);
    }
}

/// [definition; §16.40] **A laned field's covector agrees with its code's central difference**: on a field of two lanes
/// with every family shaped, each family's three entries with the largest covectors (the probe law of
/// [`covector_matches_the_codes_difference`], a probe whose step moves a site across a sheet left out and counted), so each
/// lane's chart and its adjoint are read on their own.
#[test]
fn the_laned_fields_covector_matches_its_codes_difference() {
    let sheets = |field: &Constitution, r: &Region| -> Vec<Vec<u32>> { field.pass(r, true).unwrap().ticks.iter().flat_map(|c| c.classes.iter().map(|l| l.off.iter().chain(&l.members).copied().chain(l.probes.iter().flat_map(|p| std::iter::once(u32::MAX).chain(p.iter().copied()))).collect())).collect() };
    let (mut read, mut seams) = (0usize, 0usize);
    for still in [0usize, 1, 2] {
        let field = shaped_with(Declaration { width: 16, lanes: 2, ..tiny_declaration(still) });
        let r = region();
        let g = covector_of(&field, &r);
        let l = field.layout.clone();
        for &(start, len, grain) in field.families() {
            if start == l.temper {
                continue;
            }
            let natural: u32 = if grain == MATERIAL_BITS { 40 } else { 24 };
            let mut entries: Vec<usize> = (start..start + len).collect();
            entries.sort_by_key(|&i| std::cmp::Reverse(g[i].unsigned_abs()));
            for i in entries.into_iter().take(3).filter(|&i| g[i] != 0) {
                let moved = |delta: i32| {
                    let mut f = field.clone();
                    f.theta[i] += delta;
                    f
                };
                let straddles = |delta: i32| sheets(&moved(delta), &r) != sheets(&field, &r) || sheets(&moved(-delta), &r) != sheets(&field, &r);
                let shift = natural + grain - 20;
                let Some((delta, h)) = probe_step(grain, &|delta: i32| (g[i] * 2 * delta as i128) >> shift, &straddles) else {
                    seams += 1;
                    continue;
                };
                read += 1;
                let measured = moved(delta).code(&r).unwrap().0 - moved(-delta).code(&r).unwrap().0;
                let predicted = (g[i] * 2 * delta as i128) >> shift;
                let tolerance = predicted.abs() / 8 + (64 << h);
                assert!((measured as i128 - predicted).abs() <= tolerance, "still {still} family at {start} (grain {grain}) entry {i} at {h} halvings: measured {measured}, predicted {predicted}");
            }
        }
    }
    eprintln!("LANE_COVECTOR_PROBES read={read} on_a_seam={seams}");
    assert!(read > 0 && 16 * seams <= read, "read {read} probes, {seams} on a seam");
}

/// [measurement; §16.41] **A step's first-order change is its code's change in the small**: on the tiny field with every
/// family shaped, a section's step taken at a small rate changes the section's code by what [`predicted_change`] reads,
/// within a fifth (the second-order term falls with the step's square), and both are falls.
#[test]
fn a_steps_predicted_change_is_its_codes_change_in_the_small() {
    for still in [0usize, 1, 2] {
        let mut learner = Learner::new(shaped(still), 14);
        let receipt = learner.section(&[region()]).unwrap();
        let predicted = receipt.predicted.expect("a predicted change within its carrier") as i128;
        let r = [region()];
        let change = (code_of(&compared(&[learner.field.faces(&r[0]).unwrap()], &r).unwrap(), &spans_of(&r)) - receipt.code_before) as i128;
        eprintln!("STEP_PARABOLA still={still} predicted={predicted} change={change}");
        assert!(predicted < 0 && change < 0, "still {still}: predicted {predicted}, change {change}");
        assert!((change - predicted).abs() * 5 <= predicted.abs(), "still {still}: predicted {predicted}, change {change}");
    }
}

/// [measurement; §16.41] **A step's transfer is the next section's change in the small**: on the tiny field, after a section
/// on one region deposits its step, the next section on another region prices that step at the material that stands, and
/// the price is the second region's code change were the step taken once more, within a fifth at a small rate. The first
/// section prices nothing, and a growth clears the operand.
#[test]
fn a_steps_transfer_is_the_next_sections_change_in_the_small() {
    let second_classes = [2usize, 2, 3, 1, 0, 4, 4];
    let second_open = [true, false, false, true, true, false, false];
    let second = [Region { classes: &second_classes, unresolved: &second_open, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None }];
    let code_on = |field: &Constitution| code_of(&compared(&[field.faces(&second[0]).unwrap()], &second).unwrap(), &spans_of(&second));
    let mut read = 0;
    for still in [0usize, 1, 2] {
        let mut learner = Learner::new(shaped(still), 14);
        let first = learner.section(&[region()]).unwrap();
        assert_eq!(first.transfer, None, "still {still}: the first section prices no step");
        if !first.deposited {
            continue;
        }
        let last = learner.last.clone().expect("a deposited step is kept for the next section's price");
        let once_more = stepped(&learner.field, &last.step, last.halvings).unwrap().0;
        let change = (code_on(&once_more) - code_on(&learner.field)) as i128;
        let receipt = learner.section(&second).unwrap();
        let transfer = receipt.transfer.expect("a transfer within its carrier") as i128;
        eprintln!("STEP_TRANSFER still={still} transfer={transfer} change={change} own={:?}", first.predicted);
        assert!((change - transfer).abs() * 5 <= transfer.abs().max(change.abs()), "still {still}: transfer {transfer}, change {change}");
        read += 1;
        assert_eq!(learner.widened(2, &keys(1 << 16)).unwrap().last, None, "still {still}: a growth clears the operand");
    }
    assert!(read >= 2, "read {read}");
}

/// A tiny learner grown by a lane and by four contacts (width 16 in two lanes, eight contacts, four of them new), a section into
/// its life so every moment is open.
fn grown_learner() -> Learner {
    let mut learner = Learner::new(Constitution::found(tiny_declaration(1), &keys(1 << 14)).unwrap(), 6);
    for _ in 0..2 {
        learner.section(&[region()]).unwrap();
    }
    let stream = keys(1 << 16);
    let learner = learner.laned(&stream).unwrap();
    learner.contacted(4, &stream).unwrap()
}

/// [definition; theory, November 10 19:05] **The founded parts tile the grown entries**: each of the fifteen parts holds entries, the
/// old entries and `W`'s lane rows hold none, and a new contact's `W` column, `a` row and `b` row are its parts' at every face
/// coordinate (the lane's included).
#[test]
fn the_founded_parts_hold_the_lane_and_the_new_contacts() {
    let learner = grown_learner();
    let field = &learner.field;
    let parts = field.founded_parts(4);
    let (d, l) = (field.declaration, field.layout().clone());
    assert_eq!((d.width, d.lanes, d.contacts), (16, 2, 8));
    let count = |p: usize| parts.iter().filter(|&&q| q as usize == p).count();
    // f = 8: new contacts are the real parts [2, 4) and the imaginary [6, 8).
    let new_contacts = [2usize, 3, 6, 7];
    assert_eq!(count(0), 16 * 4, "W's new columns: every face coordinate of the four new contacts");
    assert_eq!(count(1), 16 * 4 + 4, "the new a rows and their biases");
    assert_eq!(count(2), 16 * 4 + 4, "the new b rows and their biases");
    let (a1, m2) = (d.alphabet + 1, 2 * d.complex());
    assert_eq!((count(3), count(4), count(5)), (a1 * 8, a1 * 8, a1 * 8));
    assert_eq!((count(6), count(7), count(8)), (m2 * 8, m2 * 8, m2 * 8));
    assert_eq!((count(9), count(10)), (8 * m2, 8 * m2));
    assert_eq!(count(11), 16 * 16 - 8 * 8, "the lift's rows and columns of the lane");
    assert_eq!(count(12), 4 * 8, "the face biases' lane entries");
    assert_eq!((count(13), count(14)), (4 * 8, 4 * 8), "the lane's columns of a and b over the old contacts");
    assert_eq!((count(19), count(20), count(21)), (a1 * 8, a1 * 8, a1 * 8), "the first lane's letter rows: each class as itself, before and after, over the first lane");
    assert!((0..a1).all(|r| (0..8).all(|c| parts[l.enc + r * 16 + c] == 19 && parts[l.before + r * 16 + c] == 20 && parts[l.after + r * 16 + c] == 21)));
    for &e in &new_contacts {
        assert!((0..16).all(|r| parts[l.w + r * 8 + e] == 0));
        assert!((0..16).all(|j| parts[l.a + e * 16 + j] == 1 && parts[l.b + e * 16 + j] == 2));
    }
    // An old contact's W column over the face's first lane is no part; over the lane's rows it is none either.
    assert!((0..16).all(|r| parts[l.w + r * 8] == OLD_PART));
    assert_eq!(parts.iter().filter(|&&q| q == OLD_PART).count(), field.theta.len() - (0..PARTS).map(count).sum::<usize>());
    assert!(parts[l.q] == OLD_PART && parts[l.q + 8] == 6);
}

/// [definition; theory, November 10 19:05] **The cosine rule**: a part whose two displacements run along one line (`c = 1`) goes one octave
/// faster, one that reverses (`c = −1`) one slower, one at exactly `c = 1/2` rests, and a part with no travel goes slower; never
/// under the old rate (`octaves 0`) nor past the rate's own bits; the travel is read from three materials by [`part_travel`].
#[test]
fn the_cosine_rule_moves_a_part_one_octave_by_its_travel() {
    use std::cmp::Ordering::*;
    assert_eq!(PartTravel { entries: 4, dot: 4, first: 4, second: 4 }.against_half(), Greater);
    assert_eq!(PartTravel { entries: 4, dot: -4, first: 4, second: 4 }.against_half(), Less);
    assert_eq!(PartTravel { entries: 1, dot: 1, first: 4, second: 1 }.against_half(), Equal, "c = 1/2 exactly");
    assert_eq!(PartTravel { entries: 1, dot: 1, first: 4, second: 1 }.cosine_micro(), 500_000);
    assert_eq!(PartTravel { entries: 2, dot: 3, first: 8, second: 2 }.against_half(), Greater, "c = 3/4");
    assert_eq!(PartTravel { entries: 2, dot: 0, first: 8, second: 0 }.against_half(), Less, "no travel");
    let mut travel = [PartTravel::default(); PARTS];
    travel[0] = PartTravel { entries: 4, dot: 4, first: 4, second: 4 };
    travel[1] = PartTravel { entries: 4, dot: -4, first: 4, second: 4 };
    travel[2] = PartTravel { entries: 1, dot: 1, first: 4, second: 1 };
    travel[3] = PartTravel { entries: 4, dot: 4, first: 4, second: 4 };
    let mut octaves = [0u32; PARTS];
    (octaves[0], octaves[1], octaves[2], octaves[3]) = (3, 2, 2, 5);
    let rp = RateParts { contacts_before: 4, octaves };
    let next = rp.updated(&travel, 6);
    assert_eq!((next.octaves[0], next.octaves[1], next.octaves[2], next.octaves[3]), (4, 1, 2, 5), "up, down, rest, and the rate's own bits (5 under six)");
    assert_eq!(next.octaves[4], 0, "the old rate is the floor: a part with no travel at 0 stays at 0");
    // From three materials: part 0's entries move one way twice, part 1's out and back.
    let learner = grown_learner();
    let parts = learner.field.founded_parts(4);
    let n = parts.len();
    let (older, mut old, mut now) = (vec![0i32; n], vec![0i32; n], vec![0i32; n]);
    for (i, &p) in parts.iter().enumerate() {
        match p {
            0 => (old[i], now[i]) = (10, 20),
            1 => (old[i], now[i]) = (10, 0),
            _ => {}
        }
    }
    let t = part_travel(&parts, &older, &old, &now);
    assert_eq!((t[0].against_half(), t[1].against_half(), t[2].against_half()), (Greater, Less, Less));
    assert_eq!(t[0].entries, 64);
}

/// [measurement; theory, November 11] **The lap's mean of the material** ([`MaterialMean`]): each entry's sum over the states joined,
/// released to the nearest with a half away from zero; the field it is released onto keeps its own material, and the entries that
/// differ are counted with their squared distance; refused before a state joined and on a material of another length.
#[test]
fn the_laps_mean_is_each_entrys_sum_released_to_the_nearest() {
    let base = shaped(1);
    let with = |values: [i32; 4]| {
        let mut field = base.clone();
        field.theta[..4].copy_from_slice(&values);
        field
    };
    let (a, b) = (with([1, -1, 1, -1]), with([2, -2, 0, 0]));
    let mut mean = MaterialMean::new(base.material_len());
    assert!(mean.released(&base).is_err(), "no state joined");
    // Thirds: 5/3 and −5/3 release to 2 and −2, 1/3 and −1/3 to 0; every other entry is the same in the three states.
    for field in [&a, &b, &b] {
        mean.take(field).unwrap();
    }
    assert_eq!(mean.states(), 3);
    let (rest, moved, square) = mean.released(&b).unwrap();
    assert_eq!((rest == b, moved, square), (true, 0, 0), "the mean of these three is the second's material");
    let (rest, moved, square) = mean.released(&a).unwrap();
    assert_eq!((&rest.theta[..4], moved, square), (&[2, -2, 0, 0][..], 4, 4));
    assert_eq!((&rest.theta[4..], &a.theta[..4]), (&base.theta[4..], &[1, -1, 1, -1][..]), "the others stand, and the field it was released onto keeps its own");
    // Halves go away from zero: 3/2 to 2 and −3/2 to −2.
    let mut halves = MaterialMean::new(base.material_len());
    for field in [&with([1, -1, 3, -3]), &b] {
        halves.take(field).unwrap();
    }
    assert_eq!(&halves.released(&base).unwrap().0.theta[..4], &[2, -2, 2, -2][..]);
    assert!(MaterialMean::new(base.material_len() + 1).take(&base).is_err(), "another length");
    assert!(MaterialMean::new(base.material_len() + 1).released(&base).is_err());
}

/// [definition; theory, November 10 19:05] **A part steps at its own rate, and every part at the old rate is the plain deposit**: with
/// the parts' octaves zero, three sections give the plain learner's material and moments bit for bit; with a part at `k` octaves its
/// entries' step is the deposit's at `rate − k` and the old entries' the plain rate's; and the parts' rates round-trip through the
/// learner's text, a state without them reading as none.
#[test]
fn a_part_steps_at_its_own_rate_and_the_plain_rate_is_the_plain_deposit() {
    let plain = grown_learner();
    let mut zero = plain.clone();
    zero.rate_parts = Some(RateParts { contacts_before: 4, octaves: [0; PARTS] });
    let mut plain = plain;
    for _ in 0..3 {
        plain.section(&[region()]).unwrap();
        zero.section(&[region()]).unwrap();
    }
    assert_eq!((plain.field.theta.clone(), plain.first.clone(), plain.second.clone()), (zero.field.theta.clone(), zero.first.clone(), zero.second.clone()), "octaves 0: the plain deposit");
    // One octave count per part: part 0 (W's new columns) at 2, part 1 (the new a rows) at 3.
    let mut fast = grown_learner();
    let mut octaves = [0u32; PARTS];
    (octaves[0], octaves[1]) = (2, 3);
    fast.rate_parts = Some(RateParts { contacts_before: 4, octaves });
    let parts = fast.field.founded_parts(4);
    let rates = fast.entry_rates();
    assert!(parts.iter().zip(&rates).all(|(&p, &r)| r == match p { 0 => 4, 1 => 3, _ => 6 }), "rate 6, its octaves less");
    fast.section(&[region()]).unwrap();
    let step = fast.last.as_ref().unwrap().step.clone();
    for &(start, len, grain) in &fast.field.families_all() {
        for i in start..start + len {
            assert_eq!(step[i], deposit_step(fast.first[i], fast.second[i], grain, rates[i]), "entry {i} steps at its part's rate");
        }
    }
    // The text.
    let back = Learner::from_text(&fast.to_text()).unwrap();
    assert_eq!(back.rate_parts, fast.rate_parts);
    assert_eq!(back.field.theta, fast.field.theta);
    let stripped: String = fast.to_text().lines().filter(|l| !l.starts_with("parts ")).map(|l| format!("{l}\n")).collect();
    assert_eq!(Learner::from_text(&stripped).unwrap().rate_parts, None, "a state without the line has no parts' rates");
    assert_eq!(stripped, grown_learner_text_of(&fast), "the state's other lines are a plain state's");
}

/// [measurement; theory, November 12, G96's third branch] **The predicted change by part is the total's partition**: a covector and a
/// step on one part's entries alone give that part the total and every other part zero; on the grown learner with its parts at their
/// own rates, each section's parts sum to its predicted change less at most one unit a family and part (the releases' floors), and a
/// part that holds no entry reads zero; without parts' rates the reading still partitions, no contact new.
#[test]
fn the_predicted_change_by_part_is_its_totals_partition() {
    let mut learner = grown_learner();
    let mut octaves = [0u32; PARTS];
    (octaves[0], octaves[1]) = (2, 3);
    learner.rate_parts = Some(RateParts { contacts_before: 4, octaves });
    let parts = learner.reading_parts();
    assert_eq!(parts, learner.field.founded_parts(4));
    // One part's entries alone: part 1 (the new a rows).
    let n = parts.len();
    let (mut g, mut step) = (vec![0i128; n], vec![0i128; n]);
    for (i, &p) in parts.iter().enumerate() {
        if p == 1 {
            (g[i], step[i]) = (-(1i128 << 50) - i as i128, 3 << 20);
        }
    }
    let total = predicted_change(&learner.field, &g, &step, 0).unwrap();
    let by = predicted_parts(&learner.field, &g, &step, 0, &parts).unwrap();
    assert!(total > 0, "a positive step (subtracted) on a negative covector raises the code at first order");
    assert_eq!(by[1], total, "the one part holds the total");
    assert!(by.iter().enumerate().all(|(p, &v)| p == 1 || v == 0), "every other part reads zero");
    let families = learner.field.families_all().len() as i64;
    let holds = |p: usize| parts.iter().any(|&q| if p == PARTS { q == OLD_PART } else { usize::from(q) == p });
    for _ in 0..3 {
        let receipt = learner.section(&[region()]).unwrap();
        let (total, by) = (receipt.predicted.unwrap(), receipt.predicted_parts.unwrap());
        let sum: i64 = by.iter().sum();
        assert!(sum <= total && total - sum <= families * (PARTS as i64 + 1), "parts {sum} against the total {total}");
        for (p, &v) in by.iter().enumerate() {
            assert!(holds(p) || v == 0, "part {p} holds no entry and reads {v}");
        }
    }
    let mut plain = grown_learner();
    assert_eq!(plain.reading_parts(), plain.field.founded_parts(plain.field.declaration.contacts), "no parts' rates: no contact is new");
    let receipt = plain.section(&[region()]).unwrap();
    let (total, sum) = (receipt.predicted.unwrap(), receipt.predicted_parts.unwrap().iter().sum::<i64>());
    assert!(sum <= total && total - sum <= families * (PARTS as i64 + 1));
}

/// The learner's text without its parts' rates (what a binary without them writes).
fn grown_learner_text_of(learner: &Learner) -> String {
    let mut plain = learner.clone();
    plain.rate_parts = None;
    plain.to_text()
}

/// [definition; theory, November 12 00:20] **An entry steps at its own rate where the learner carries it**: own rates equal to the parts'
/// give the parts' deposit bit for bit over three sections; rates of their own (some entries under the base word, some over it) step each
/// entry at its own rate; the line trails the state and round-trips through the learner's text, a state without it reads as none, and a
/// line that is not one count an entry, or that holds a rate of zero or one past the step's carrier, is refused.
#[test]
fn an_entry_steps_at_its_own_rate_where_the_learner_carries_it() {
    let mut octaves = [0u32; PARTS];
    (octaves[0], octaves[1]) = (2, 3);
    let mut parts = grown_learner();
    parts.rate_parts = Some(RateParts { contacts_before: 4, octaves });
    let mut own = parts.clone();
    own.own_rates = Some(parts.entry_rates());
    for _ in 0..3 {
        parts.section(&[region()]).unwrap();
        own.section(&[region()]).unwrap();
    }
    assert_eq!((parts.field.theta.clone(), parts.first.clone(), parts.second.clone()), (own.field.theta.clone(), own.first.clone(), own.second.clone()), "own rates equal to the parts': the parts' deposit");
    // Rates of their own about the base 6: every third entry two bits slower, every other fifth one bit faster.
    let mut free = grown_learner();
    let rates: Vec<u32> = (0..free.field.material_len()).map(|i| if i % 3 == 0 { 8 } else if i % 5 == 0 { 5 } else { 6 }).collect();
    free.own_rates = Some(rates.clone());
    assert_eq!(free.entry_rates(), rates);
    free.section(&[region()]).unwrap();
    let step = free.last.as_ref().unwrap().step.clone();
    for &(start, len, grain) in &free.field.families_all() {
        for i in start..start + len {
            assert_eq!(step[i], deposit_step(free.first[i], free.second[i], grain, rates[i]), "entry {i} steps at its own rate");
        }
    }
    let text = free.to_text();
    assert!(text.lines().last().unwrap().starts_with("rates "), "the line trails the state");
    assert_eq!(Learner::from_text(&text).unwrap().own_rates, free.own_rates);
    let stripped: String = text.lines().filter(|l| !l.starts_with("rates ")).map(|l| format!("{l}\n")).collect();
    assert_eq!(Learner::from_text(&stripped).unwrap().own_rates, None, "a state without the line has no own rates");
    let short: String = text.lines().map(|l| if l.starts_with("rates ") { format!("{}\n", l.rsplit_once(' ').unwrap().0) } else { format!("{l}\n") }).collect();
    assert!(Learner::from_text(&short).is_err(), "a line that is not one count an entry is refused");
    for bad in ["0", "128"] {
        let wrong: String = text.lines().map(|l| if l.starts_with("rates ") { format!("{} {bad}\n", l.rsplit_once(' ').unwrap().0) } else { format!("{l}\n") }).collect();
        assert!(Learner::from_text(&wrong).is_err(), "a rate of {bad} is refused");
    }
}

/// [measurement; theory, November 10 19:05] The founded parts and their travel read from saved states (`HOLONICS_PARTS_OLDER`,
/// `HOLONICS_PARTS_OLD`, `HOLONICS_PARTS_NOW`, `HOLONICS_PARTS_BEFORE`: the paths of three learner states of one line and the contact
/// count before the growth): the entries each part holds and its travel's cosine in millionths, printed as `PART name entries c`, the
/// line `tools/part_rates.py` is checked against. Reads saved text and computes no model; ignored by default.
#[test]
#[ignore]
#[allow(clippy::disallowed_methods, reason = "an exterior reading of saved state files")]
fn founded_parts_and_their_cosines_on_saved_states() {
    let var = |k: &str| std::env::var(k).unwrap_or_else(|_| panic!("{k} names a saved state"));
    let load = |k: &str| Learner::from_text(&std::fs::read_to_string(var(k)).unwrap()).unwrap();
    let (older, old, now) = (load("HOLONICS_PARTS_OLDER"), load("HOLONICS_PARTS_OLD"), load("HOLONICS_PARTS_NOW"));
    let parts = now.field.founded_parts(var("HOLONICS_PARTS_BEFORE").parse().unwrap());
    let travel = part_travel(&parts, &older.field.theta, &old.field.theta, &now.field.theta);
    for (name, t) in PART_NAMES.iter().zip(&travel) {
        println!("PART {name} {} {} {:?}", t.entries, t.cosine_micro(), t.against_half());
    }
}

/// A tiny declaration with four complex contacts and no carry circle.
fn four_contacts(still: usize) -> Declaration {
    Declaration { contacts: 8, ..tiny_declaration(still) }
}

/// [`four_contacts`]'s founded field grown by two carry circles (complex contacts 4 and 5 of six: one scans from the left, one from the
/// right), then every family drawn ([`drawn`]): the circles' charts, their biases and their `W` columns off zero, so the gate has friction
/// on some sites and none on others.
fn circled_shaped(still: usize) -> Constitution {
    let plain = Constitution::found(four_contacts(still), &keys(1 << 14)).unwrap();
    let (grown, _) = plain.with_carry(2, &keys(plain.declaration.carry_draws(2))).unwrap();
    drawn(grown)
}

/// [definition; theory, November 11 17:25 and November 12] **The carry circles' declaration**: `C` even and at most `f/2` is admitted; `C = 0` is
/// the `hnn-field-v14` line exactly (twelve words), `C > 0` writes `hnn-field-v14e` with `C` its thirteenth word and round-trips; the retired
/// carries' heads (`hnn-field-v14k`, founded at zero friction, and `hnn-field-v14t`, the leak's linear chart) and a `v14e` head with no circle are
/// refused.
#[test]
fn the_carry_circles_are_even_among_the_contacts_and_the_retired_carries_are_refused() {
    let d = four_contacts(1);
    assert!(Declaration { carry: 2, ..d }.admit().is_ok() && Declaration { carry: 4, ..d }.admit().is_ok());
    assert!(Declaration { carry: 1, ..d }.admit().is_err(), "an odd count of circles");
    assert!(Declaration { carry: 6, ..d }.admit().is_err(), "more circles than complex contacts");
    let plain = d.to_text();
    assert!(plain.starts_with("hnn-field-v14 ") && plain.split(' ').count() == 12);
    assert_eq!(Declaration::from_text(&plain).unwrap(), d);
    let circled = Declaration { carry: 2, ..d }.to_text();
    assert!(circled.starts_with("hnn-field-v14e ") && circled.split(' ').count() == 13 && circled.ends_with(" 2"));
    assert_eq!(Declaration::from_text(&circled).unwrap(), Declaration { carry: 2, ..d });
    let retired = format!("{} 1", plain.replacen("hnn-field-v14 ", "hnn-field-v14k ", 1));
    assert!(matches!(Declaration::from_text(&retired), Err(TowerError::Refused(m)) if m.contains("zero friction is retired")));
    let linear = circled.replacen("hnn-field-v14e ", "hnn-field-v14t ", 1);
    assert!(matches!(Declaration::from_text(&linear), Err(TowerError::Refused(m)) if m.contains("linear chart is retired")));
    assert!(Declaration::from_text(&format!("{} 0", plain.replacen("hnn-field-v14 ", "hnn-field-v14e ", 1))).is_err());
}

/// [definition; theory, November 11 17:25 and November 12, G96's third branch; `CarryGate.lean`] **The gate keeps its circle and its friction on
/// the leak's log chart**: at `q = ℓ = 0` the founded friction `d = 2^14` (`1/4`) and the gate `2^32/5` to the nearest (`|γ| = 4/5`); the turn
/// alone is the Cayley tick at that friction (`q = 2` gives `4i/5`); `ℓ = 2` gives `d = 1`, which halves the turn; each whole step of `ℓ` doubles
/// the friction, and from `ℓ = −14` down it keeps one grain; over a sweep of `q` and `ℓ` the friction is monotone in `ℓ`, stands between
/// `d₀ 2^⌊ℓ⌋` and `d₀ 2^(⌊ℓ⌋+1)`, a step of `ℓ` by one doubles it within a grain, and `|γ|² (1 + d)² = 2^60` within the releases' rounding;
/// refused, typed, past the carriers.
#[test]
fn the_carry_gate_keeps_its_circle_and_its_friction() {
    let exp = Exponential::new(FACE_BITS);
    let gate = |q: i128, l: i128| carry_gate(&exp, q, l);
    assert_eq!(gate(0, 0).unwrap(), ((858_993_459, 0), 1 << 14), "founded: the near field's friction, 1/4");
    assert_eq!(gate(2 << 16, 0).unwrap().0, (0, 858_993_459), "the Cayley step of i at q = 2, at the founded friction");
    assert_eq!(gate(-(2 << 16), 0).unwrap().0, (0, -858_993_459));
    assert_eq!(gate(0, 2 << 16).unwrap(), ((1 << 29, 0), 1 << 16), "ℓ = 2: a friction of one halves the turn");
    for k in -40i128..=32 {
        assert_eq!(gate(0, k << 16).unwrap().1, if k >= -14 { 1 << (14 + k) } else { 1 }, "ℓ = {k}: each whole step doubles the friction, and one grain is its floor");
    }
    let friction = |l: i128| gate(0, l).unwrap().1;
    let mut previous = friction(-(40 << 16));
    for l in (-(40i128 << 16)..(32 << 16)).step_by(4_099) {
        let d = friction(l);
        assert!(d >= previous, "ℓ {l}: the friction is monotone in its chart");
        previous = d;
        let a = l >> 16;
        let (low, high) = if a >= -14 { (1i128 << (14 + a), 1i128 << (15 + a)) } else { (1, 1) };
        assert!(low <= d && d <= high.max(1), "ℓ {l}: d {d} between d₀ 2^⌊ℓ⌋ and d₀ 2^(⌊ℓ⌋+1)");
        if a >= -14 && a < 31 {
            assert!((friction(l + (1 << 16)) - 2 * d).abs() <= 1, "ℓ {l}: one more step doubles the friction within a grain");
        }
    }
    for q in [0i128, 1 << 16, -(1 << 16), 3 << 15, 5 << 16, 123_456, -78_901, 1 << 30, -(1 << 38), 1] {
        for l in [-(1i128 << 22), -(15 << 16), -1, 0, 1, 1 << 16, 7 << 16, 123_457, (32 << 16) + 65_535] {
            let ((re, im), d) = gate(q, l).unwrap();
            assert!(d >= 1 && d < 1 << 47, "q {q} ℓ {l}: d {d} keeps its grain and its carrier");
            let norm = i128::from(re) * i128::from(re) + i128::from(im) * i128::from(im);
            assert!(norm < 1 << 60, "q {q} ℓ {l}: |γ|² {norm} under one, strictly");
            let one = (1i128 << 16) + d;
            let expected = (1i128 << 92) / (one * one);
            assert!((norm - expected).abs() <= 1 << 32, "q {q} ℓ {l}: |γ|² {norm} against {expected}");
        }
    }
    assert!(gate(1 << 39, 0).is_err() && gate(-(1 << 39), 0).is_err(), "the turn's carrier");
    assert!(gate(0, 33 << 16).is_err() && gate(0, (33 << 16) - 1).is_ok(), "the friction's carrier, 2^47 at ℓ = 33");
    assert!(gate(0, i128::from(i64::MAX) + 1).is_err(), "a leak read past 64 bits");
}

/// [definition; theory, November 12, G96's third branch; `CarryGate.lean`, `leak_hasDerivAt`] **The gate's return reads the leak chart's
/// derivative at every read**: with a fixed `δγ`, `δℓ = ln 2 · d · δd` where `δd = −Re(conj(γ) δγ)/(1 + d)`: against that product read at the
/// friction's word, within a part in `2^10` wherever the word holds at least 64 grains; below the floor the chart's own derivative stands,
/// nonzero and under the floor's (`2^ℓ` smaller).
#[test]
fn the_gates_return_reads_the_leak_charts_derivative() {
    let exp = Exponential::new(FACE_BITS);
    let dgamma = (-(3i64 << 40), 5i64 << 38);
    let ln2 = ln2_face();
    for l in [-(20i128 << 16), -(16 << 16), -(8 << 16), -(3 << 16) - 4_321, -1, 0, 1, 12_345, 1 << 16, (5 << 16) + 777, 20 << 16] {
        let q = 3 << 15;
        let (gamma, d) = carry_gate(&exp, q, l).unwrap();
        let ((_, dl), db) = carry_gate_return(&exp, gamma, dgamma, (0, 0), (0, 0), q, l).unwrap();
        assert_eq!(db, (0, 0), "ℓ {l}: no charge's covector, no drive's");
        let (yr, yi, dr, di) = (i128::from(gamma.0), i128::from(gamma.1), i128::from(dgamma.0), i128::from(dgamma.1));
        let re = release(yr * dr + yi * di, GAMMA_BITS);
        let dd = -div_nearest(re << 16, (1i128 << 16) + d);
        let at_word = release(release(dd * ln2, LN2_FACE_BITS) * d, 16);
        assert!(dl != 0, "ℓ {l}: the covector stands at every read");
        assert_eq!(dl.signum() as i128, at_word.signum(), "ℓ {l}: the covector's sign is the friction's");
        if d >= 64 {
            assert!((i128::from(dl) - at_word).abs() <= at_word.abs() / 1024 + 1, "ℓ {l}: δℓ {dl} against ln 2 · d · δd {at_word}");
        } else if l < -(14 << 16) {
            assert!(i128::from(dl).abs() < at_word.abs(), "ℓ {l}: below the floor the chart's own derivative, under the floor's");
        }
    }
}

/// [definition; theory, November 12, G98; `CarryGate.lean`, `coupling_leak_zero`, `gate_and_coupling`, `charge_le`, `coupling_hasDerivAt`]
/// **The drive is charged through the leak**: the coupling `κ = N₀ d/(1 + d)` is `2^30` at the founded friction, so there the coupled drive is
/// the drive bit for bit and the coupled scan is the sum form's; `κ` is monotone in the friction and under `N₀`, and with the gate `|γ| + κ/N₀`
/// is one within two grains; along a strand of the reach's sites under a constant drive (a turn of zero and of one), the coupled charge stays
/// within `N₀` places' drive and a grain a place of the circle's group, at the friction's floor, its founding and far above it, where the sum
/// form's charge at the floor passes 3,000 places' drive. With no `δγ` the gate's return carries the coupling alone: `δb = κ u`; `∂κ/∂d =
/// N₀/(1 + d)²` against the coupling's central difference within a part in `2^6`; and `δℓ = ln 2 · d · δd_κ` against that product read at the
/// friction's word within a part in `2^10` wherever the word holds at least 64 grains, of `Re(conj(b) u)`'s sign.
#[test]
fn the_drive_is_charged_through_the_leak() {
    let exp = Exponential::new(FACE_BITS);
    assert_eq!(CARRY_GROUP_FOUNDING, 5);
    let founded = carry_coupling(i128::from(CARRY_LEAK_FOUNDING));
    assert_eq!(founded, 1 << 30, "the coupling is one at the founding");
    for b in [0i64, 1, -1, 12_345, -98_765, 1 << 40, -(1 << 40) + 7, i64::MAX >> 3] {
        assert_eq!(carry_drive(founded, b).unwrap(), b, "founded, the coupled drive is the drive bit for bit");
    }
    let mut previous = 0i128;
    for l in (-(40i128 << 16)..(32 << 16)).step_by(4_099) {
        let ((re, im), d) = carry_gate(&exp, 0, l).unwrap();
        let kappa = carry_coupling(d);
        assert!(kappa >= previous && kappa < 5 << 30, "ℓ {l}: κ {kappa} monotone in the friction and under N₀");
        previous = kappa;
        assert_eq!(im, 0, "ℓ {l}: no turn");
        assert!((i128::from(re) + kappa / 5 - (1 << 30)).abs() <= 2, "ℓ {l}: |γ| {re} and κ/N₀ {} sum to one", kappa / 5);
    }
    // A strand of the reach's sites under a constant drive.
    let b = 1i64 << 20;
    let strand = |q: i128, l: i128, coupled: bool| -> i128 {
        let ((yr, yi), d) = carry_gate(&exp, q, l).unwrap();
        let (yr, yi) = (i128::from(yr), i128::from(yi));
        let drive = i128::from(if coupled { carry_drive(carry_coupling(d), b).unwrap() } else { b });
        let (mut qr, mut qi, mut most) = (0i128, 0i128, 0i128);
        for _ in 0..3_771 {
            (qr, qi) = (drive + release(yr * qr - yi * qi, GAMMA_BITS), release(yr * qi + yi * qr, GAMMA_BITS));
            most = most.max(((qr * qr + qi * qi) as u128).isqrt() as i128);
        }
        most
    };
    for q in [0i128, 1 << 16] {
        for l in [-(20i128 << 16), -(14 << 16), -(3 << 16), 0, 3 << 16, 10 << 16, 30 << 16] {
            let most = strand(q, l, true);
            assert!(most <= 5 * i128::from(b) + (1 << 16) + 1, "q {q} ℓ {l}: the coupled charge {most} within N₀ places' drive");
        }
        assert_eq!(strand(q, 0, true), strand(q, 0, false), "q {q}: founded, the coupled scan is the sum form's");
    }
    assert!(strand(0, -(20 << 16), false) > 3_000 * i128::from(b), "the sum form's charge at the floor passes 3,000 places' drive");
    // The coupling's derivative in the friction.
    for d in [64i128, 1 << 10, 1 << 14, 1 << 16, 1 << 20, 1 << 30] {
        let step = (d / 64).max(1);
        let difference = (carry_coupling(d + step) - carry_coupling(d - step)) / (2 * step);
        let one = (1i128 << 16) + d;
        let expected = div_nearest(5i128 << 46, one * one);
        assert!((difference - expected).abs() <= expected / 64 + 1, "d {d}: ∂κ/∂d {difference} against N₀/(1 + d)² {expected}");
    }
    // The gate's return with no δγ: the coupling alone.
    let ln2 = ln2_face();
    let drive = (7i64 << 30, -(3i64 << 30));
    for du in [(5i64 << 36, 11i64 << 34), (-(9i64 << 33), 2i64 << 37)] {
        for l in [-(20i128 << 16), -(10 << 16) - 321, -(3 << 16), -1, 0, 7_777, 4 << 16, (12 << 16) + 99] {
            let q = 3 << 15;
            let (gamma, d) = carry_gate(&exp, q, l).unwrap();
            let kappa = carry_coupling(d);
            let ((dq, dl), db) = carry_gate_return(&exp, gamma, (0, 0), drive, du, q, l).unwrap();
            assert_eq!(dq, 0, "ℓ {l}: with no δγ the turn has no covector");
            assert_eq!(db, (carry_drive(kappa, du.0).unwrap(), carry_drive(kappa, du.1).unwrap()), "ℓ {l}: δb = κ u");
            let w = release(i128::from(drive.0) * i128::from(du.0) + i128::from(drive.1) * i128::from(du.1), FACE_BITS);
            let one = (1i128 << 16) + d;
            let ddk = div_nearest((5 * w) << 32, one * one);
            let at_word = release(release(ddk * ln2, LN2_FACE_BITS) * d, 16);
            assert!(dl != 0, "ℓ {l}: the coupling's covector stands at every read");
            assert_eq!(dl.signum() as i128, w.signum(), "ℓ {l}: the drive's covector pulls the leak its own way");
            if d >= 64 {
                assert!((i128::from(dl) - at_word).abs() <= at_word.abs() / 1024 + 1, "ℓ {l}: δℓ {dl} against ln 2 · d · δd_κ {at_word}");
            } else if l < -(14 << 16) {
                assert!(i128::from(dl).abs() < at_word.abs(), "ℓ {l}: below the floor the chart's own derivative, under the floor's");
            }
        }
    }
}

/// [definition; the lead, November 18, the record of the two streams §19] **More carry circles keep every face, every standing circle and a
/// tower's level** ([`Constitution::more_carry`]): on a field with circles and every family drawn, two more circles follow the standing ones
/// as the last complex contacts; every face of the law and of a strand is kept bit for bit; a standing circle keeps its number, its turn
/// row, its leak row and its gates; the new circles' `W` columns, leak rows and biases stand at zero and their turn rows are drawn; the new
/// `W` columns have a covector; the map carries every standing entry once. On a tower with its one-sided block the level's entries are
/// carried as they stood and a strand's faces are kept. A field with no circles, an odd count and a field with triads are refused. The
/// learner keeps every standing moment, opens the new entries as a growth opens them and round-trips through its text.
#[test]
fn more_carry_circles_keep_every_face_every_standing_circle_and_a_towers_level() {
    for still in [0usize, 1, 2] {
        let field = circled_shaped(still);
        let old = field.declaration;
        let (grown, from) = field.more_carry(2, &keys(old.carry_draws(2))).unwrap();
        let (d, l, ol) = (grown.declaration, grown.layout.clone(), field.layout.clone());
        assert_eq!((d.contacts, d.carry, d.carry_first()), (old.contacts + 4, old.carry + 2, old.carry_first()), "the standing circles keep their complex indices");
        assert_eq!(grown.faces(&region()).unwrap(), field.faces(&region()).unwrap(), "still {still}: every face of the law kept");
        let classes = drawn_classes(0xC1, 11, d.alphabet);
        for past in [false, true] {
            assert_eq!(grown.strand_pass(&classes, false, past).unwrap().faces, field.strand_pass(&classes, false, past).unwrap().faces, "still {still}: every face of a strand kept");
        }
        assert_eq!(from.len(), grown.theta.len());
        let mut seen = vec![0u8; field.theta.len()];
        for o in from.iter().flatten() {
            seen[*o] += 1;
        }
        assert!(seen.iter().all(|&n| n == 1), "every standing entry carried once");
        assert!(from.iter().zip(&grown.theta).all(|(o, &v)| o.is_none_or(|i| field.theta[i] == v)), "each with its value");
        let (dw, f, c0, c1) = (d.width, d.contacts, old.carry, d.carry);
        // A standing circle's rows: turn row k at k, leak row k at C' + k; its biases the same way.
        for k in 0..c0 {
            assert_eq!(grown.theta[l.carry + k * dw..l.carry + (k + 1) * dw], field.theta[ol.carry + k * dw..ol.carry + (k + 1) * dw]);
            assert_eq!(grown.theta[l.carry + (c1 + k) * dw..l.carry + (c1 + k + 1) * dw], field.theta[ol.carry + (c0 + k) * dw..ol.carry + (c0 + k + 1) * dw]);
            assert_eq!((grown.theta[l.carry_bias + k], grown.theta[l.carry_bias + c1 + k]), (field.theta[ol.carry_bias + k], field.theta[ol.carry_bias + c0 + k]));
        }
        // The new circles: complex contacts f_old/2 .. f_old/2 + 2, circles C..C'.
        let fresh: Vec<usize> = (old.contacts / 2..old.contacts / 2 + 2).flat_map(|e| [e, f / 2 + e]).collect();
        assert!(fresh.iter().all(|&e| (0..dw).all(|r| grown.theta[l.w + r * f + e] == 0)), "the new circles' W columns at zero");
        assert!(fresh.iter().all(|&e| grown.theta[l.a_bias + e] == 0 && grown.theta[l.b_bias + e] == 0), "their drives' biases at zero");
        assert!(fresh.iter().all(|&e| grown.theta[l.a + e * dw..l.a + (e + 1) * dw].iter().any(|&v| v != 0) && grown.theta[l.b + e * dw..l.b + (e + 1) * dw].iter().any(|&v| v != 0)), "their drives drawn");
        assert!(grown.theta[l.carry + c0 * dw..l.carry + c1 * dw].iter().any(|&v| v != 0), "the new turn rows drawn");
        assert!(grown.theta[l.carry + (c1 + c0) * dw..l.carry + 2 * c1 * dw].iter().all(|&v| v == 0), "the new leak rows at zero");
        assert!((c0..c1).all(|k| grown.theta[l.carry_bias + k] == 0 && grown.theta[l.carry_bias + c1 + k] == 0), "the new biases at zero");
        // The standing circles' gates are the ones before the growth; the new ones stand at their founding friction.
        let (before, after) = (field.carry_gates_of(&region()).unwrap(), grown.carry_gates_of(&region()).unwrap());
        assert_eq!((after.reads, &after.modulus[..c0], &after.friction[..c0]), (before.reads, &before.modulus[..], &before.friction[..]));
        assert!(after.friction[c0..].iter().all(|&n| n == after.reads), "a new circle's leak reads zero at every site: the founded friction");
        let g = covector_of(&grown, &region());
        assert!(fresh.iter().any(|&e| (0..dw).any(|r| g[l.w + r * f + e] != 0)), "still {still}: the new circles' W columns have a covector");
        assert!(grown.more_carry(3, &keys(d.carry_draws(3))).is_err(), "an odd count of circles");
    }
    assert!(shaped_with(four_contacts(1)).more_carry(2, &keys(1 << 12)).is_err(), "a field with no circles takes its first by with_carry");
    // A tower with its one-sided block: the level's entries carried as they stood, a strand's faces kept.
    for (still, past) in [(1usize, false), (2, true)] {
        // The fine field as the line's was grown: its circles first, then the opening's lift (the level reads the opening's news).
        let fine = Constitution::found(four_contacts(still), &keys(1 << 14)).unwrap();
        let (fine, _) = fine.with_carry(2, &keys(fine.declaration.carry_draws(2))).unwrap();
        let fine = drawn(fine.with_opening().unwrap().0);
        let offset = 4 * (fine.declaration.founding_draws() + fine.declaration.carry_draws(2));
        let mut tower = fine.scaled_up(6, 1, Declaration { reach: 16, ..coarse_declaration() }, &keys(1 << 16), offset).unwrap().0;
        let base = tower.theta.len();
        draw_from(&mut tower, base);
        let before_block = tower.material_len();
        let mut tower = tower.level_before().unwrap();
        draw_from(&mut tower, before_block);
        let (grown, from) = tower.more_carry(2, &keys(tower.declaration.carry_draws(2))).unwrap();
        assert_eq!(from.len(), grown.material_len());
        assert_eq!(grown.material_len() - grown.theta.len(), tower.material_len() - tower.theta.len(), "the level's material keeps its length");
        let (old_all, new_all): (Vec<i32>, Vec<i32>) = (tower.material().copied().collect(), grown.material().copied().collect());
        assert!((grown.theta.len()..grown.material_len()).all(|k| from[k] == Some(tower.theta.len() + k - grown.theta.len()) && new_all[k] == old_all[from[k].unwrap()]), "the level's entries carried as they stood");
        let classes = drawn_classes(0xD5, 13, grown.declaration.alphabet);
        assert_eq!(grown.strand_pass(&classes, false, past).unwrap().faces, tower.strand_pass(&classes, false, past).unwrap().faces, "still {still}: every face of a strand on the tower kept");
        assert_eq!(grown.faces(&region()).unwrap(), tower.faces(&region()).unwrap(), "still {still}: and every face of the law");
    }
    // The learner.
    let mut learner = Learner::new(circled_shaped(1), 6);
    learner.section(&[region()]).unwrap();
    learner.held = None;
    learner.rate_parts = Some(RateParts { contacts_before: 8, octaves: [0; PARTS] });
    let draws = learner.field.declaration.carry_draws(2);
    let stream = keys(learner.drawn / 4 + draws + 8);
    let grown = learner.more_carry(2, &stream).unwrap();
    assert_eq!(grown.drawn, learner.drawn + 4 * draws);
    let (_, from) = learner.field.more_carry(2, &stream[learner.drawn..]).unwrap();
    assert!(from.iter().enumerate().all(|(k, o)| o.is_none_or(|i| grown.first[k] == learner.first[i] && grown.second[k] == learner.second[i])), "every standing entry keeps its moments");
    assert!(from.iter().enumerate().filter(|(_, o)| o.is_none()).all(|(k, _)| grown.first[k] == 0), "a new entry's first moment at zero");
    let l = grown.field.layout.clone();
    let (dw, c0, c1) = (grown.field.declaration.width, learner.field.declaration.carry, grown.field.declaration.carry);
    assert!((l.carry + c0 * dw..l.carry + c1 * dw).all(|k| grown.second[k] > 0), "a new turn row opens on its family's standing scale");
    assert_eq!(grown.rate_parts, learner.rate_parts);
    let text = grown.to_text();
    let back = Learner::from_text(&text).unwrap();
    assert!(back.to_text() == text && back.field == grown.field, "the grown learner reads back as itself");
}

/// [definition; theory, November 11 17:25] **A growth by carry circles keeps every face and returns through its circles**: on a field with every
/// family drawn, [`Constitution::with_carry`] adds the circles as the last contacts (their `W` columns, leak rows and biases at zero, their turn rows
/// drawn), reads every face bit for bit, and the circles' `W` columns have a covector; a lane keeps the faces again with the lane's columns of the
/// circles' charts at zero; a second growth, a plain growth by contacts and a growth by copies are refused; the learner opens the circles' entries
/// as a growth in contacts opens them, its charts' moments at zero, its draws past the contacts' and the turn rows', and its text (the parts
/// line of nineteen) round-trips.
#[test]
fn a_growth_by_carry_circles_keeps_every_face_and_returns_through_its_circles() {
    for still in [0usize, 1, 2] {
        let plain = shaped_with(four_contacts(still));
        let (grown, from) = plain.with_carry(2, &keys(plain.declaration.carry_draws(2))).unwrap();
        let (d, l) = (grown.declaration, grown.layout.clone());
        assert_eq!((d.contacts, d.carry, d.carry_first()), (12, 2, 4));
        assert_eq!(grown.faces(&region()).unwrap(), plain.faces(&region()).unwrap(), "still {still}: every face kept");
        assert_eq!(from.iter().flatten().count(), plain.theta.len());
        let (dw, f) = (d.width, d.contacts);
        let circle_columns: Vec<usize> = (4..6).flat_map(|e| [e, f / 2 + e]).collect();
        assert!(circle_columns.iter().all(|&e| (0..dw).all(|r| grown.theta[l.w + r * f + e] == 0)), "the circles' W columns at zero");
        assert!(grown.theta[l.carry + 2 * dw..l.carry + 4 * dw].iter().all(|&v| v == 0) && grown.theta[l.carry_bias..l.carry_bias + 4].iter().all(|&v| v == 0), "the leak rows and both biases at zero: the leak's chart founded at its zero");
        assert_eq!(CARRY_LEAK_FOUNDING, 1 << 14, "the chart's zero is the near field's friction, 1/4");
        assert!(grown.theta[l.carry..l.carry + 2 * dw].iter().any(|&v| v != 0), "the turn rows drawn");
        let g = covector_of(&grown, &region());
        assert!(circle_columns.iter().any(|&e| (0..dw).any(|r| g[l.w + r * f + e] != 0)), "still {still}: the circles' W columns have a covector");
        let (laned, _) = grown.laned(&keys(grown.declaration.lane_draws())).unwrap();
        assert_eq!(laned.faces(&region()).unwrap(), plain.faces(&region()).unwrap());
        let (ll, dw2) = (laned.layout.clone(), laned.declaration.width);
        for row in 0..4 {
            assert_eq!(laned.theta[ll.carry + row * dw2..ll.carry + row * dw2 + dw], grown.theta[l.carry + row * dw..l.carry + (row + 1) * dw]);
            assert!(laned.theta[ll.carry + row * dw2 + dw..ll.carry + (row + 1) * dw2].iter().all(|&v| v == 0), "the lane's columns of the circles' charts at zero");
        }
        assert!(grown.with_carry(2, &keys(d.carry_draws(2))).is_err(), "a second growth by carry circles");
        assert!(grown.contacted(4, &keys(d.contact_draws(4))).is_err(), "a plain growth in contacts with carry circles");
        assert!(grown.grown(2, &keys(grown.growth_draws(2))).is_err(), "a growth by copies with carry circles");
    }
    // The learner.
    let mut learner = Learner::new(shaped_with(four_contacts(1)), 6);
    learner.section(&[region()]).unwrap();
    learner.held = None;
    learner.rate_parts = Some(RateParts { contacts_before: 8, octaves: [0; PARTS] });
    let stream = keys(learner.drawn / 4 + learner.field.declaration.carry_draws(2) + 8);
    let grown = learner.with_carry(2, &stream).unwrap();
    assert_eq!(grown.drawn, learner.drawn + 4 * learner.field.declaration.carry_draws(2));
    let l = grown.field.layout.clone();
    let (dw, f) = (grown.field.declaration.width, grown.field.declaration.contacts);
    assert!((l.carry..l.carry_bias + 4).all(|k| grown.first[k] == 0 && grown.second[k] == 0), "the circles' charts' moments at zero");
    let old_a: Vec<i128> = (0..8).flat_map(|e| (0..dw).map(move |j| (e, j))).map(|(e, j)| learner.second[learner.field.layout.a + e * dw + j]).collect();
    let n = old_a.len() as i128;
    let mean = old_a.iter().map(|v| v / n).sum::<i128>() + old_a.iter().map(|v| v % n).sum::<i128>() / n;
    assert!(mean > 0);
    for e in (4..6).flat_map(|e| [e, f / 2 + e]) {
        assert!((0..dw).all(|j| grown.second[l.a + e * dw + j] == mean && grown.first[l.a + e * dw + j] == 0), "a circle's a row opens on its family's mean");
    }
    assert_eq!(grown.rate_parts, Some(RateParts { contacts_before: 8, octaves: [0; PARTS] }));
    let text = grown.to_text();
    // The parts a field with circles and no triads writes: every part before the triad's (twenty-two), the line as before the triads.
    assert_eq!(text.lines().find(|l| l.starts_with("parts ")).unwrap().split(' ').count(), 2 + written_parts(2, 0, false, false, false, false, false).len(), "a field with carry circles writes all twenty-two parts before the triad's");
    assert_eq!(written_parts(2, 0, false, false, false, false, false).len(), TRIAD_PART);
    let back = Learner::from_text(&text).unwrap();
    assert_eq!((back.field.theta.clone(), back.first.clone(), back.second.clone(), back.rate_parts, back.drawn), (grown.field.theta.clone(), grown.first.clone(), grown.second.clone(), grown.rate_parts, grown.drawn));
    assert_eq!(back.field.declaration, grown.field.declaration);
    assert_eq!(learner.to_text().lines().find(|l| l.starts_with("parts ")).unwrap().split(' ').count(), 2 + written_parts(0, 0, false, false, false, false, false).len(), "a field without carry circles writes nineteen: the plain sixteen and the first lane's letter rows");
}

/// [definition; theory, November 11 17:25 and November 12 (G98)] **The carry circles' scan is the law, site by site in strand order**: on a drawn
/// field with two circles, at every tick each plain contact is the built pair contact with its strand mate, each circle's gate is [`carry_gate`] of
/// its charts' reads and its drive the pair's `b` coupled through the same leak ([`carry_coupling`]), and the circle's `p(t) = a(t) Qm(t)`,
/// `Q(t) = κ(t) b(t) + γ(t) Qm(t)` hold in its strand order. With the current, the pair's
/// return and the moment's chart at zero (so the pair chart is the opening's), a left circle's pair at `t` reads the class of site `t − 4`, a
/// right circle's that of `t + 3` (`t + 4` is the region's open site, which carries no word), and a plain contact's reads neither.
#[test]
fn the_carry_circles_scan_is_the_law_site_by_site() {
    let mut base = circled_shaped(1);
    let l = base.layout.clone();
    let d = base.declaration;
    let (dw, f, m2, c) = (d.width, d.contacts, 2 * d.complex(), d.carry);
    let (half, plain, c2) = (f / 2, d.carry_first(), 2 * c);
    for (start, len) in [(l.out, dw * m2), (l.out_bias, dw), (l.w, dw * f), (l.w_bias, dw), (l.moment_face, dw * m2), (l.moment_face_bias, dw)] {
        base.theta[start..start + len].fill(0);
    }
    let classes: Vec<usize> = vec![1, 3, 0, 2, 4, 1, 3, 2, 0, 4, 2, 1];
    let unresolved = {
        let mut u = vec![false; classes.len()];
        u[11] = true;
        u
    };
    let pass = |c: &[usize]| base.pass(&Region { classes: c, unresolved: &unresolved, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None }, true).unwrap();
    let t = 7usize;
    let c0 = pass(&classes);
    let mut left = classes.clone();
    left[t - 4] = (left[t - 4] + 1) % 5;
    let c1 = pass(&left);
    let mut right = classes.clone();
    right[t + 3] = (right[t + 3] + 1) % 5;
    let c3 = pass(&right);
    for e in 0..plain {
        assert_eq!(c0.ticks[0].c[t * f + e], c1.ticks[0].c[t * f + e], "plain contact {e} does not read site {}", t - 4);
        assert_eq!(c0.ticks[0].c[t * f + e], c3.ticks[0].c[t * f + e], "plain contact {e} does not read site {}", t + 3);
    }
    let even = plain + (plain % 2);
    let odd = plain + 1 - (plain % 2);
    assert!(c0.ticks[0].c[t * f + even] != c1.ticks[0].c[t * f + even] || c0.ticks[0].c[t * f + half + even] != c1.ticks[0].c[t * f + half + even], "the left circle reads site {} within one tick", t - 4);
    assert!(c0.ticks[0].c[t * f + odd] != c3.ticks[0].c[t * f + odd] || c0.ticks[0].c[t * f + half + odd] != c3.ticks[0].c[t * f + half + odd], "the right circle reads site {} within one tick", t + 3);
    // The law, in strand order.
    let sites = classes.len();
    for (tick, cell) in c0.ticks.iter().enumerate() {
        for tt in 0..sites {
            for e in 0..plain {
                let (ar, ai) = (cell.a[tt * f + e] as i128, cell.a[tt * f + half + e] as i128);
                let (br, bi) = strand_mate(tt, e, sites).map_or((0, 0), |s| (cell.b[s * f + e] as i128, cell.b[s * f + half + e] as i128));
                assert_eq!((cell.c[tt * f + e] as i128, cell.c[tt * f + half + e] as i128), (release(ar * br - ai * bi, FACE_BITS), release(ar * bi + ai * br, FACE_BITS)), "tick {tick} site {tt} plain contact {e}");
            }
            for k in 0..c {
                let (gamma, friction) = carry_gate(&base.exponential, cell.qh[tt * c2 + k] as i128, cell.qh[tt * c2 + c + k] as i128).unwrap();
                assert_eq!((cell.gam[tt * c2 + k], cell.gam[tt * c2 + c + k]), gamma, "tick {tick} site {tt} circle {k}'s gate");
                let (kappa, e) = (carry_coupling(friction), plain + k);
                let drive = (carry_drive(kappa, cell.b[tt * f + e]).unwrap(), carry_drive(kappa, cell.b[tt * f + half + e]).unwrap());
                assert_eq!((cell.kb[tt * c2 + k], cell.kb[tt * c2 + c + k]), drive, "tick {tick} site {tt} circle {k}'s drive, coupled through its leak");
            }
        }
        for k in 0..c {
            let e = plain + k;
            let (mut qr, mut qi) = (0i128, 0i128);
            for step in 0..sites {
                let tt = if e % 2 == 0 { step } else { sites - 1 - step };
                assert_eq!((cell.qm[tt * c2 + k] as i128, cell.qm[tt * c2 + c + k] as i128), (qr, qi));
                let (ar, ai) = (cell.a[tt * f + e] as i128, cell.a[tt * f + half + e] as i128);
                assert_eq!((cell.c[tt * f + e] as i128, cell.c[tt * f + half + e] as i128), (release(ar * qr - ai * qi, FACE_BITS), release(ar * qi + ai * qr, FACE_BITS)), "tick {tick} site {tt} circle {k}");
                let (yr, yi) = (i128::from(cell.gam[tt * c2 + k]), i128::from(cell.gam[tt * c2 + c + k]));
                (qr, qi) = (cell.kb[tt * c2 + k] as i128 + release(yr * qr - yi * qi, GAMMA_BITS), cell.kb[tt * c2 + c + k] as i128 + release(yr * qi + yi * qr, GAMMA_BITS));
            }
        }
    }
}

/// [definition; theory, November 11 17:25 and November 12 (G98)] **The carry circles' adjoint agrees with its code's central difference** on a
/// drawn field with two circles (ticks two, three fixtures), their charts, biases and `W` columns off zero and the leak `ℓ` below zero on some sites
/// and above on others (so the drive's coupling `κ` stands off one and its covector is read through `b` and `ℓ`): each family's three entries with
/// the largest covectors (the circles' charts and biases, `a`, `b` and `W` among them) against
/// the code's difference ([`the_laned_fields_covector_matches_its_codes_difference`]'s probe law), the circles' charts and biases read at least
/// once each. On the leak's log chart the friction has no seam where it moves (the linear chart's `max(0, h)` had one at zero); the friction's
/// floor of one grain stands at `ℓ < −14`, which no read of this fixture reaches.
#[test]
fn the_carry_circles_covector_matches_its_codes_difference() {
    // The seams: the class sheets.
    let sheets = |field: &Constitution, r: &Region| -> Vec<Vec<u32>> {
        let pass = field.pass(r, true).unwrap();
        pass.ticks.iter().flat_map(|c| c.classes.iter().map(|l| l.off.iter().chain(&l.members).copied().chain(l.probes.iter().flat_map(|p| std::iter::once(u32::MAX).chain(p.iter().copied()))).collect())).collect()
    };
    let (mut read, mut seams, mut charts_read, mut biases_read) = (0usize, 0usize, 0usize, 0usize);
    let (mut below, mut above) = (0usize, 0usize);
    for still in [0usize, 1, 2] {
        let field = circled_shaped(still);
        let r = region();
        let (c, c2) = (field.declaration.carry, 2 * field.declaration.carry);
        let pass = field.pass(&r, true).unwrap();
        let leaks: Vec<i64> = pass.ticks.iter().flat_map(|cell| (0..CLASSES.len()).flat_map(move |t| (0..c).map(move |k| cell.qh[t * c2 + c + k]))).collect();
        below += leaks.iter().filter(|&&l| l < 0).count();
        above += leaks.iter().filter(|&&l| l > 0).count();
        assert!(leaks.iter().all(|&l| l >= -(14 << 16)), "still {still}: no read at the friction's floor, so the chart is smooth over the fixture");
        let g = covector_of(&field, &r);
        let l = field.layout.clone();
        assert!(g[l.carry..l.carry + c2 * field.declaration.width].iter().any(|&v| v != 0), "still {still}: the circles' charts have a covector");
        for &(start, len, grain) in field.families() {
            if start == l.temper {
                continue;
            }
            let natural: u32 = if grain == MATERIAL_BITS { 40 } else { 24 };
            let mut entries: Vec<usize> = (start..start + len).collect();
            entries.sort_by_key(|&i| std::cmp::Reverse(g[i].unsigned_abs()));
            for i in entries.into_iter().take(3).filter(|&i| g[i] != 0) {
                let moved = |delta: i32| {
                    let mut f = field.clone();
                    f.theta[i] += delta;
                    f
                };
                let straddles = |delta: i32| sheets(&moved(delta), &r) != sheets(&field, &r) || sheets(&moved(-delta), &r) != sheets(&field, &r);
                let shift = natural + grain - 20;
                let Some((delta, h)) = probe_step(grain, &|delta: i32| (g[i] * 2 * delta as i128) >> shift, &straddles) else {
                    seams += 1;
                    continue;
                };
                read += 1;
                charts_read += usize::from(start == l.carry);
                biases_read += usize::from(start == l.carry_bias);
                let measured = moved(delta).code(&r).unwrap().0 - moved(-delta).code(&r).unwrap().0;
                let predicted = (g[i] * 2 * delta as i128) >> shift;
                let tolerance = predicted.abs() / 8 + (64 << h);
                assert!((measured as i128 - predicted).abs() <= tolerance, "still {still} family at {start} (grain {grain}) entry {i} at {h} halvings: measured {measured}, predicted {predicted}");
            }
        }
    }
    eprintln!("CARRY_COVECTOR_PROBES read={read} on_a_seam={seams} charts={charts_read} biases={biases_read} leak_below={below} leak_above={above}");
    assert!(below > 0 && above > 0, "the friction below its founding on some sites and above on others: {below} below zero, {above} above");
    assert!(read > 0 && 16 * seams <= read && charts_read > 0 && biases_read > 0, "read {read} probes, {seams} on a seam, {charts_read} of the charts, {biases_read} of the biases");
}

/// [definition; the lead, November 19 (G-1119-7); `CarryGate.lean`, `pumped_charge_step_le`] **The pumped gate at zero is the unpumped gate,
/// and its leak is shared**: over a sweep of `q` and `ℓ`, at `p = 0` the pumped gate, its pump, its friction and its coupling are
/// [`carry_gate`]'s and [`carry_coupling`]'s in integers, and its return (whatever `δη`) is [`carry_gate_return`]'s; over a sweep of `p` the
/// turn, the pump and the coupling share one leak, `|γ| + |η| + κ/N₀ ≤ 1` within three grains, and the pump stands at `p/(1 + d + n)`;
/// a part of `p` past `2^39` is refused.
#[test]
fn the_pumped_gate_at_zero_is_the_unpumped_gate_and_its_leak_is_shared() {
    let exp = Exponential::new(FACE_BITS);
    let qs = [0i128, 1 << 16, -(1 << 16), 3 << 15, 123_456, -78_901, 1 << 30];
    let ls = [-(1i128 << 22), -(15 << 16), -1, 0, 1, 1 << 16, 7 << 16, 123_457];
    for &q in &qs {
        for &l in &ls {
            let (gamma, d) = carry_gate(&exp, q, l).unwrap();
            let (pg, eta, pd, n, kappa) = carry_gate_pumped(&exp, q, l, (0, 0)).unwrap();
            assert_eq!((pg, eta, pd, n, kappa), (gamma, (0, 0), d, 0, carry_coupling(d)), "q {q} ℓ {l}: at p = 0 the unpumped gate in integers");
            for (dgamma, deta, drive, du) in [((3i64 << 40, -(5i64 << 38)), (7i64 << 39, 1i64 << 33), (7i64 << 30, -(3i64 << 30)), (5i64 << 36, 11i64 << 34)), ((-(9i64 << 33), 2i64 << 37), (-(1i64 << 41), -(3i64 << 35)), (-(1i64 << 28), 1i64 << 31), (-(9i64 << 33), 2i64 << 37))] {
                let plain = carry_gate_return(&exp, gamma, dgamma, drive, du, q, l).unwrap();
                let (dqdl, _, db) = carry_gate_return_pumped(&exp, gamma, dgamma, (0, 0), deta, drive, du, q, l, (0, 0)).unwrap();
                assert_eq!((dqdl, db), plain, "q {q} ℓ {l}: at p = 0 the unpumped gate's return in integers");
            }
            for p in [(1i128 << 16, 0i128), (0, -(1 << 14)), (3 << 15, -(5 << 15)), (-(123_456), 98_765), (1 << 30, 1 << 29), ((1 << 39) - 1, 0)] {
                let ((yr, yi), (er, ei), d, n, kappa) = carry_gate_pumped(&exp, q, l, p).unwrap();
                assert_eq!(n, p.0.abs() + p.1.abs());
                let modulus = |a: i64, b: i64| ((i128::from(a) * i128::from(a) + i128::from(b) * i128::from(b)) as u128).isqrt() as i128;
                let total = modulus(yr, yi) + modulus(er, ei) + kappa / i128::from(CARRY_GROUP_FOUNDING);
                assert!(total <= (1 << 30) + 3, "q {q} ℓ {l} p {p:?}: |γ| + |η| + κ/N₀ = {total} within three grains of one");
                let one = (1i128 << 16) + d + n;
                assert_eq!((i128::from(er), i128::from(ei)), (div_nearest(p.0 << 30, one), div_nearest(p.1 << 30, one)), "the pump is p/(1 + d + n)");
            }
        }
    }
    assert!(carry_gate_pumped(&exp, 0, 0, (1 << 39, 0)).is_err() && carry_gate_pumped(&exp, 0, 0, (0, -(1 << 39))).is_err(), "the pump's carrier");
}

/// [`circled_shaped`]'s field with its circles pumped and every family drawn again ([`drawn`] draws by entry, so every standing entry keeps
/// its draw and the pump's chart is drawn off zero).
fn pumped_shaped(still: usize) -> Constitution {
    drawn(circled_shaped(still).with_pump().unwrap().0)
}

/// [definition; the lead, November 19] **A field pumped at zero keeps every face and returns through its pump**: [`Constitution::with_pump`]
/// appends the pump's chart at zero; every face of the law and of a strand is the source's bit for bit and every standing entry's covector is
/// the source's; the chart has a covector (`η`'s, `u Qm`, stands at `p = 0`); its head line is `hnn-field-v14p` and round-trips; a second pump
/// and a field with no circles are refused; the chart is the `carry` part's; the learner keeps every standing moment, opens the chart's second
/// moments on the circles' charts' scale and round-trips through its text.
#[test]
fn a_field_pumped_at_zero_keeps_every_face_and_returns_through_its_pump() {
    for still in [0usize, 1, 2] {
        let field = circled_shaped(still);
        let (pumped, from) = field.with_pump().unwrap();
        let (d, l) = (pumped.declaration, pumped.layout.clone());
        assert!(d.pump && pumped.theta[l.pump..].iter().all(|&v| v == 0));
        assert_eq!(pumped.faces(&region()).unwrap(), field.faces(&region()).unwrap(), "still {still}: every face of the law kept");
        let classes = drawn_classes(0xE7, 11, d.alphabet);
        for past in [false, true] {
            assert_eq!(pumped.strand_pass(&classes, false, past).unwrap().faces, field.strand_pass(&classes, false, past).unwrap().faces, "still {still}: every face of a strand kept");
        }
        assert!(from.iter().enumerate().all(|(k, o)| o.is_none_or(|i| pumped.theta[k] == field.theta[i])));
        let (g, g0) = (covector_of(&pumped, &region()), covector_of(&field, &region()));
        assert_eq!(&g[..field.theta.len()], &g0[..], "still {still}: every standing entry's covector kept");
        assert!(g[l.pump..l.pump + 2 * d.carry * d.width].iter().any(|&v| v != 0), "still {still}: the pump's chart has a covector at zero");
        let text = d.to_text();
        assert!(text.starts_with("hnn-field-v14p ") && text.split(' ').count() == 21 && text.ends_with(" 1"));
        assert_eq!(Declaration::from_text(&text).unwrap(), d);
        assert!(Declaration::from_text(&format!("{} 0", &text[..text.len() - 2])).is_err(), "a v14p head whose pump word is not one");
        assert!(pumped.with_pump().is_err(), "a second pump");
        // A lane on the pumped field keeps every face, with the pump's chart drawn so the lane's zero columns are read.
        let drawn_pump = pumped_shaped(still);
        let (laned, _) = drawn_pump.laned(&keys(drawn_pump.declaration.lane_draws())).unwrap();
        assert_eq!(laned.faces(&region()).unwrap(), drawn_pump.faces(&region()).unwrap(), "still {still}: a lane on the pumped field keeps every face");
        let (ll, dw2) = (laned.layout.clone(), laned.declaration.width);
        for row in 0..2 * d.carry {
            assert_eq!(laned.theta[ll.pump + row * dw2..ll.pump + row * dw2 + d.width], drawn_pump.theta[l.pump + row * d.width..l.pump + (row + 1) * d.width]);
            assert!(laned.theta[ll.pump + row * dw2 + d.width..ll.pump + (row + 1) * dw2].iter().all(|&v| v == 0), "the lane's columns of the pump's chart at zero");
        }
        let parts = pumped.founded_parts(8);
        assert!(parts[l.pump..l.pump + 2 * d.carry * (d.width + 1)].iter().all(|&p| p == 15), "the pump's chart is the carry part's");
    }
    assert!(shaped_with(four_contacts(1)).with_pump().is_err(), "a field with no circles");
    assert!(Declaration { pump: true, ..four_contacts(1) }.admit().is_err());
    // The learner.
    let mut learner = Learner::new(circled_shaped(1), 6);
    learner.section(&[region()]).unwrap();
    learner.held = None;
    let pumped = learner.with_pump().unwrap();
    let (_, from) = learner.field.with_pump().unwrap();
    assert!(from.iter().enumerate().all(|(k, o)| o.is_none_or(|i| pumped.first[k] == learner.first[i] && pumped.second[k] == learner.second[i])), "every standing entry keeps its moments");
    let l = pumped.field.layout.clone();
    assert!((l.pump..pumped.field.theta.len()).all(|k| pumped.first[k] == 0), "the chart's first moments at zero");
    assert!((l.pump..pumped.field.theta.len()).any(|k| pumped.second[k] > 0), "the chart opens on the circles' charts' scale");
    let text = pumped.to_text();
    let back = Learner::from_text(&text).unwrap();
    assert!(back.to_text() == text && back.field == pumped.field, "the pumped learner reads back as itself");
}

/// [definition; the lead, November 20] **A lane beside a tower's one-sided block keeps every face**: on a tower with its one-sided block drawn
/// ([`Constitution::level_before`]) over a fine field with circles, pumped and drawn, and the opening's lift, [`Constitution::laned`] grows the
/// fine level by one lane, the block's rows of the fine face taking the lane at zero as `B`'s do; every face of the law and of a strand (with and
/// without the odd contacts facing the past) is the tower's before the lane, and every standing entry is carried once with its value.
#[test]
fn a_lane_beside_a_towers_one_sided_block_keeps_every_face() {
    for (still, past) in [(1usize, false), (2, true)] {
        let fine = Constitution::found(four_contacts(still), &keys(1 << 14)).unwrap();
        let (fine, _) = fine.with_carry(2, &keys(fine.declaration.carry_draws(2))).unwrap();
        let fine = drawn(fine.with_opening().unwrap().0.with_pump().unwrap().0);
        let offset = 4 * (fine.declaration.founding_draws() + fine.declaration.carry_draws(2));
        let mut tower = fine.scaled_up(6, 1, Declaration { reach: 16, ..coarse_declaration() }, &keys(1 << 16), offset).unwrap().0;
        let base = tower.theta.len();
        draw_from(&mut tower, base);
        let before_block = tower.material_len();
        let mut tower = tower.level_before().unwrap();
        draw_from(&mut tower, before_block);
        let (laned, from) = tower.laned(&keys(tower.declaration.lane_draws())).unwrap();
        assert_eq!(from.len(), laned.material_len());
        let (old_all, new_all): (Vec<i32>, Vec<i32>) = (tower.material().copied().collect(), laned.material().copied().collect());
        let mut seen = vec![0u8; old_all.len()];
        for (k, o) in from.iter().enumerate() {
            if let Some(i) = o {
                seen[*i] += 1;
                assert_eq!(new_all[k], old_all[*i], "entry {k} carries {i} with its value");
            }
        }
        assert!(seen.iter().all(|&n| n == 1), "every standing entry carried once");
        let classes = drawn_classes(0xA7, 13, laned.declaration.alphabet);
        assert_eq!(laned.strand_pass(&classes, false, past).unwrap().faces, tower.strand_pass(&classes, false, past).unwrap().faces, "still {still}: every face of a strand kept");
        assert_eq!(laned.faces(&region()).unwrap(), tower.faces(&region()).unwrap(), "still {still}: and every face of the law");
    }
}

/// [definition; the lead, November 19] **The pumped circles' adjoint agrees with its code's central difference**, as the unpumped circles' does
/// ([`the_carry_circles_covector_matches_its_codes_difference`]): on [`pumped_shaped`]'s fields (the pump's chart drawn, so `η` stands off zero at
/// every site), each family's three entries with the largest covectors against the code's difference, the pump's chart and its bias read at
/// least once each. The pump's budget `n = |p_re| + |p_im|` has a seam where a part of `p` crosses zero; no probe of this fixture moves one
/// across it (checked: every read part of `p` stands at least 64 grains off zero).
#[test]
fn the_pumped_circles_covector_matches_its_codes_difference() {
    let (mut read, mut pump_read, mut pump_bias_read) = (0usize, 0usize, 0usize);
    for still in [0usize, 1, 2] {
        let field = pumped_shaped(still);
        let r = region();
        let c2 = 2 * field.declaration.carry;
        let pass = field.pass(&r, true).unwrap();
        assert!(pass.ticks.iter().all(|cell| cell.ph[..CLASSES.len() * c2].iter().all(|&p| p.abs() >= 64)), "still {still}: every part of p off its seam");
        assert!(pass.ticks.iter().any(|cell| cell.eta.iter().any(|&e| e != 0)), "still {still}: the pump stands off zero");
        let g = covector_of(&field, &r);
        let l = field.layout.clone();
        for &(start, len, grain) in field.families() {
            if start == l.temper {
                continue;
            }
            let natural: u32 = if grain == MATERIAL_BITS { 40 } else { 24 };
            let mut entries: Vec<usize> = (start..start + len).collect();
            entries.sort_by_key(|&i| std::cmp::Reverse(g[i].unsigned_abs()));
            for i in entries.into_iter().take(3).filter(|&i| g[i] != 0) {
                let moved = |delta: i32| {
                    let mut f = field.clone();
                    f.theta[i] += delta;
                    f
                };
                let sheets = |f: &Constitution| -> Vec<Vec<u32>> {
                    let pass = f.pass(&r, true).unwrap();
                    pass.ticks.iter().flat_map(|c| c.classes.iter().map(|l| l.off.iter().chain(&l.members).copied().collect())).collect()
                };
                let straddles = |delta: i32| sheets(&moved(delta)) != sheets(&field) || sheets(&moved(-delta)) != sheets(&field);
                let shift = natural + grain - 20;
                let Some((delta, h)) = probe_step(grain, &|delta: i32| (g[i] * 2 * delta as i128) >> shift, &straddles) else {
                    continue;
                };
                read += 1;
                pump_read += usize::from(start == l.pump);
                pump_bias_read += usize::from(start == l.pump_bias);
                let measured = moved(delta).code(&r).unwrap().0 - moved(-delta).code(&r).unwrap().0;
                let predicted = (g[i] * 2 * delta as i128) >> shift;
                let tolerance = predicted.abs() / 8 + (64 << h);
                assert!((measured as i128 - predicted).abs() <= tolerance, "still {still} family at {start} (grain {grain}) entry {i} at {h} halvings: measured {measured}, predicted {predicted}");
            }
        }
    }
    eprintln!("PUMP_COVECTOR_PROBES read={read} pump={pump_read} pump_bias={pump_bias_read}");
    assert!(read > 0 && pump_read > 0 && pump_bias_read > 0, "read {read} probes, {pump_read} of the pump's chart, {pump_bias_read} of its bias");
}

/// [definition; theory, November 11 17:25] **The carry circles are founded parts of their own**: the circles' charts and biases (part 15), their
/// `W` columns (16) and their `a` and `b` rows with the drives' biases (17, 18), over the new contacts' marks, so a field grown by circles alone
/// has no new plain contact.
#[test]
fn the_carry_circles_are_founded_parts_of_their_own() {
    let plain = shaped_with(four_contacts(1));
    let (grown, _) = plain.with_carry(2, &keys(plain.declaration.carry_draws(2))).unwrap();
    let parts = grown.founded_parts(8);
    let (dw, c2) = (grown.declaration.width, 2 * grown.declaration.carry);
    let count = |p: u8| parts.iter().filter(|&&q| q == p).count();
    assert_eq!((count(0), count(1), count(2)), (0, 0, 0), "the circles are the only new contacts");
    assert_eq!(count(15), c2 * dw + c2, "the circles' charts and biases");
    assert_eq!(count(16), c2 * dw, "the circles' W columns, real and imaginary");
    assert_eq!((count(17), count(18)), (c2 * dw + c2, c2 * dw + c2), "the circles' a and b rows with their biases");
    assert_eq!(PART_NAMES[15], "carry");
}

/// [definition; theory, November 10 05:30] **An answer's root charge is its letters' counts against its faces' summed shares**
/// ([`root_charge`]): faces that share their mass evenly between letters 1 and 2 under an answer of three 1s and one 2 hold
/// `F = (2, 2)` against `N = (3, 1)`, so the charge is `3 log₂(3/2) + log₂(1/2)` bits, positive, at the counts' `2^72`; and
/// faces whose shares match the counts read none.
#[test]
fn an_answers_root_charge_is_its_counts_against_its_summed_shares() {
    let face = |m1: u128, m2: u128| TowerFace { masses: vec![0, m1, m2], total: m1 + m2 };
    let x = [1usize, 1, 1, 2];
    let even = vec![face(1 << 60, 1 << 60); 4];
    // 3 log₂ 1.5 − 1 = 0.754887… bits on 2^(−20): 791,557.
    let r = root_charge(&x, &even);
    assert!((r - 791_557).abs() < 64, "the root charge {r}");
    let matched = vec![face(3 << 58, 1 << 58); 4];
    assert!(root_charge(&x, &matched).abs() < 64);
}

/// [definition; theory, November 10 04:40] **The re-draws through a lens code the stop place and certify every pass**
/// ([`Constitution::redraw_lensed`]): with a lens that weighs the void four times at the stop place, each answer's code at the start is
/// its lensed locked faces' code, the stop place at the void among them, and every pass that keeps changes lowers the pooled
/// code by more than `h` for each one; every answer keeps its length and stops neutral or at rest.
#[test]
fn the_lensed_redraw_codes_its_stop_place_and_certifies_every_pass() {
    let field = shaped_with(Declaration { reach: 40, ..tiny_declaration(1) });
    let (q1, q2) = ([1usize, 4, 0, 2, 2, 3], [3usize, 3, 1, 0]);
    let problems: Vec<(&[usize], usize)> = vec![(&q1, 24), (&q2, 22)];
    let letters = |seed: usize, n: usize, room: usize| -> Vec<usize> { (0..room).map(|t| if t < n { 1 + (t * 7 + t / 3 + seed) % 4 } else { 0 }).collect() };
    let written = vec![letters(0, 20, 24), letters(3, 20, 22)];
    let lens = |x: &[usize], faces: &mut [TowerFace]| {
        if let Some(stop) = faces.get_mut(x.len()) {
            stop.masses[0] *= 4;
            stop.total = stop.masses.iter().sum();
        }
    };
    let answers0: Vec<Vec<usize>> = written.iter().map(|w| w[..20].to_vec()).collect();
    let mut locked = field.locked_faces(&problems, &answers0, &[0, 1], 0, true, &mut Host).unwrap();
    for (x, f) in answers0.iter().zip(locked.iter_mut()) {
        assert_eq!(f.len(), x.len() + 1, "the stop place is read");
        lens(x, f);
    }
    for h in [0i128, 1 << 18] {
        let mut passes: Vec<(usize, usize, i128)> = Vec::new();
        let (answers, records) = field.redraw_lensed(&problems, &written, 0, h, &lens, &mut Host, &mut |p| {
            passes.push((p.pass, p.kept, p.code));
            true
        }).unwrap();
        for (k, r) in records.iter().enumerate() {
            let expected: i128 = locked[k].iter().enumerate().map(|(t, f)| f.code(answers0[k].get(t).copied().unwrap_or(0)) as i128).sum();
            assert_eq!(r.start, expected, "problem {k}: the start is the lensed code, the stop place's among it");
            assert!(r.neutral || r.rested, "h={h} problem {k} stops");
            assert!(answers[k][..20].iter().all(|&c| c != 0) && answers[k][20..].iter().all(|&c| c == 0));
        }
        for w in passes.windows(2) {
            let ((_, _, before), (pass, kept, after)) = (w[0], w[1]);
            if kept > 0 {
                assert!(before - after > h * kept as i128, "h={h} pass {pass}");
            } else {
                assert_eq!(before, after, "h={h} pass {pass} kept nothing");
            }
        }
    }
}

/// [definition; theory, November 10 04:15] **A point re-draw proposal** ([`redraw_proposals`]): a place more than a nat past its
/// face's entropy is re-drawn to its face's top letter, never the void, only where that letter's price is at least a nat; the
/// most surprised first, and no two claims within `NEAR − 1` of each other.
#[test]
fn a_point_redraw_takes_the_top_letter_of_a_surprised_place() {
    // Five letters, the void 0: a face sure of letter `top` (the void heavier still where `void_heavy`).
    let face = |top: usize, void_heavy: bool| {
        let masses: Vec<u128> = (0..5).map(|c| if c == top { 1u128 << 60 } else if c == 0 && void_heavy { 1 << 61 } else { 1 << 40 }).collect();
        let total = masses.iter().sum();
        TowerFace { masses, total }
    };
    let n = 2 * NEAR + 2;
    // Every place holds letter 1; place 0 is sure of 2, place 1 (inside its claim) sure of 3, the last sure of 4 behind a
    // heavier void, and the rest sure of 1.
    let x = vec![1usize; n];
    let faces: Vec<TowerFace> = (0..n).map(|t| match t { 0 => face(2, false), 1 => face(3, false), t if t == n - 1 => face(4, true), _ => face(1, false) }).collect();
    let out = redraw_proposals(&x, &faces, 0);
    let at: Vec<Vec<(usize, usize)>> = out.iter().map(|(at, _)| at.clone()).collect();
    assert!(at.iter().all(|a| a.len() == 1 && a[0].1 != 0), "never the void");
    assert!(at.contains(&vec![(n - 1, 4)]), "the top letter behind the void: {at:?}");
    assert_eq!(at.iter().filter(|a| a[0].0 < NEAR).count(), 1, "one claim among the first places: {at:?}");
    assert!(out.iter().all(|(_, g)| *g > 0));
}

/// [definition; theory, November 10 04:15] **Point re-draws alternate with exchanges, certify every pass and stop** ([`Constitution::redraw`]):
/// on the settle's two answers, at `h` zero and at a quarter of a bit, each answer keeps its length and its void, the passes
/// alternate re-draw (odd) and exchange (even), every pass that keeps changes lowers the pooled code by more than `h` for each
/// one, a pass that keeps none leaves it as it was, and every answer stops neutral (its code at or under its entropy) or at
/// rest; its end is its final answer's code read again.
#[test]
fn point_redraws_alternate_with_exchanges_certify_every_pass_and_stop() {
    let field = shaped_with(Declaration { reach: 40, ..tiny_declaration(1) });
    let (q1, q2) = ([1usize, 4, 0, 2, 2, 3], [3usize, 3, 1, 0]);
    let problems: Vec<(&[usize], usize)> = vec![(&q1, 24), (&q2, 22)];
    let letters = |seed: usize, n: usize, room: usize| -> Vec<usize> { (0..room).map(|t| if t < n { 1 + (t * 7 + t / 3 + seed) % 4 } else { 0 }).collect() };
    let written = vec![letters(0, 20, 24), letters(3, 20, 22)];
    for h in [0i128, 1 << 18] {
        let mut passes: Vec<(usize, usize, usize, i128)> = Vec::new();
        let (answers, records) = field.redraw(&problems, &written, 0, h, &mut Host, &mut |p| {
            passes.push((p.pass, p.kind, p.kept, p.code));
            true
        }).unwrap();
        for w in passes.windows(2) {
            let ((_, _, _, before), (pass, kind, kept, after)) = (w[0], w[1]);
            assert_eq!(kind, pass % 2, "pass {pass} alternates");
            if kept > 0 {
                assert!(before - after > h * kept as i128, "h={h} pass {pass}: {kept} kept, the code fell {}", before - after);
            } else {
                assert_eq!(before, after, "h={h} pass {pass} kept nothing");
            }
        }
        for (k, (a, w)) in answers.iter().zip(&written).enumerate() {
            assert_eq!(a.len(), w.len());
            assert!(a[..20].iter().all(|&c| c != 0) && a[20..].iter().all(|&c| c == 0), "problem {k} keeps its length and its void");
            let r = &records[k];
            assert!(r.neutral || r.rested, "h={h} problem {k} stops");
            assert!(!r.neutral || r.end <= r.entropy, "h={h} problem {k}: neutral at or under its entropy");
            eprintln!("REDRAW h={h} problem={k} kept={} undone={} start={} end={} entropy={} neutral={} passes={}", r.kept.len(), r.undone, r.start, r.end, r.entropy, r.neutral, passes.len() - 1);
        }
        let (_, check) = field.redraw(&problems, &answers, 0, i128::MAX, &mut Host, &mut |_| false).unwrap();
        for (k, r) in records.iter().enumerate() {
            assert_eq!(check[k].start, r.end, "the end is the final answer's code read again");
        }
    }
}

/// [definition; theory, November 10 01:36] **The parallel certified settle holds composition, certifies every pass and rests**
/// ([`Constitution::settle`]): on two answers of twenty letters, at `h` zero and at a quarter of a bit, each answer keeps its letters
/// and its void, every pass that keeps exchanges lowers the pooled code by more than `h` for each one (each problem's kept set
/// is certified whole), a pass that keeps none leaves it as it was, every problem rests, and its end is its final
/// answer's code read again; some exchange is kept.
#[test]
fn the_parallel_settle_certifies_every_pass_and_rests() {
    let field = shaped_with(Declaration { reach: 40, ..tiny_declaration(1) });
    let (q1, q2) = ([1usize, 4, 0, 2, 2, 3], [3usize, 3, 1, 0]);
    let problems: Vec<(&[usize], usize)> = vec![(&q1, 24), (&q2, 22)];
    let letters = |seed: usize, n: usize, room: usize| -> Vec<usize> { (0..room).map(|t| if t < n { 1 + (t * 7 + t / 3 + seed) % 4 } else { 0 }).collect() };
    let written = vec![letters(0, 20, 24), letters(3, 20, 22)];
    let mut kept_any = false;
    for h in [0i128, 1 << 18] {
        let mut passes: Vec<(usize, usize, i128)> = Vec::new();
        let (answers, records) = field.settle(&problems, &written, 0, h, &mut Host, &mut |p| {
            passes.push((p.pass, p.kept, p.code));
            true
        }).unwrap();
        for w in passes.windows(2) {
            let ((_, _, before), (pass, kept, after)) = (w[0], w[1]);
            if kept > 0 {
                assert!(before - after > h * kept as i128, "h={h} pass {pass}: {kept} kept, the code fell {}", before - after);
            } else {
                assert_eq!(before, after, "h={h} pass {pass} kept nothing");
            }
        }
        for (k, (a, w)) in answers.iter().zip(&written).enumerate() {
            let (mut x, mut y) = (a.clone(), w.clone());
            x.sort_unstable();
            y.sort_unstable();
            assert_eq!(x, y, "problem {k}: composition held");
            assert!(a[20..].iter().all(|&c| c == 0), "the void past the letters stays");
            let r = &records[k];
            assert!(r.rested, "h={h} problem {k} rests");
            kept_any |= !r.kept.is_empty();
            eprintln!("SETTLE h={h} problem={k} kept={} undone={} start={} end={} passes={}", r.kept.len(), r.undone, r.start, r.end, passes.len() - 1);
        }
        let (again, check) = field.settle(&problems, &answers, 0, i128::MAX, &mut Host, &mut |_| true).unwrap();
        assert_eq!(again, answers);
        for (k, r) in records.iter().enumerate() {
            assert_eq!(check[k].start, r.end, "the end is the final answer's code read again");
        }
    }
    assert!(kept_any, "the settle kept some exchange");
}


/// [measurement; theory, November 11 18:33, part P2; the founding of 19:56, G85] **The carry circles' gates, read**: on a drawn field grown by two
/// carry circles (founded: the leak rows and the leak's bias at zero), every (open site, tick) read has `ℓ = 0`, so `d = 1/4` and `|γ| = 4/5`,
/// `2^32/5` on `2^(−30)` within the rounding of its two parts, and `ℓ ≥ 0` (the friction at its founding or above) counts every read; a moved
/// leak row turns some reads below zero and closes their count; the read changes no face.
#[test]
fn the_carry_circles_gates_are_read_from_the_forwards_own_cells() {
    let plain = shaped_with(four_contacts(1));
    let (mut grown, _) = plain.with_carry(2, &keys(plain.declaration.carry_draws(2))).unwrap();
    let r = region();
    let faces = grown.faces(&r).unwrap();
    let gates = grown.carry_gates_of(&r).unwrap();
    let open = OPEN.iter().filter(|&&u| u).count() as u64;
    assert_eq!(gates.reads, open * grown.declaration.ticks as u64);
    for k in 0..2 {
        assert_eq!(gates.friction[k], gates.reads, "founded, every leak read stands at its zero, the friction at 1/4");
        let mean = gates.modulus[k] / u128::from(gates.reads);
        assert!(mean.abs_diff(858_993_459) <= 2, "circle {k}: |γ| = 4/5 to the grain, {mean}");
    }
    assert_eq!(grown.faces(&r).unwrap(), faces, "the read changes no face");
    // A leak row moved at every coordinate's sign: some reads fall below the founding and leave the count.
    let (l, dw) = (grown.layout.clone(), grown.declaration.width);
    for j in 0..dw {
        grown.theta[l.carry + 2 * dw + j] = if j % 2 == 0 { -(1 << 24) } else { 1 << 24 };
    }
    let moved = grown.carry_gates_of(&r).unwrap();
    assert_eq!(moved.reads, gates.reads);
    assert!(moved.friction[0] < moved.reads, "a moved leak row takes some reads below the founded friction");
}

/// [measurement; theory, November 12, G90's first branch and G96's third] **The carry circles' leaks and charges, read**: on a drawn field
/// grown by two carry circles ([`circled_shaped`]), with circle 0's leak row moved so that some reads fall below zero (the friction below its
/// founding on the leak's log chart), [`Constitution::carry_leaks`] over each tick's pair chart gives every site's leak read `ℓ` as the forward's own
/// cell holds it (`qh`), and its charge after the site as the scan's value before the next site in scan order (`qm`, even contacts from the
/// left and odd from the right); a field without circles refuses.
#[test]
fn the_carry_circles_leaks_and_charges_are_the_forwards_own() {
    let mut field = circled_shaped(1);
    let (l, dw) = (field.layout.clone(), field.declaration.width);
    for j in 0..dw {
        field.theta[l.carry + 2 * dw + j] = if j % 2 == 0 { -(1 << 24) } else { 1 << 24 };
    }
    let r = region();
    let pass = field.pass(&r, true).unwrap();
    let (circles, first) = (field.declaration.carry, field.declaration.carry_first());
    let c2 = 2 * circles;
    let (mut below, mut charged) = (0usize, 0usize);
    for cell in &pass.ticks {
        let (leak, charge) = field.carry_leaks(&cell.read2).unwrap();
        let sites = cell.read2.len() / dw;
        assert_eq!((leak.len(), charge.len()), (sites * circles, sites * circles));
        for t in 0..sites {
            for k in 0..circles {
                assert_eq!(leak[t * circles + k], cell.qh[t * c2 + circles + k], "site {t} circle {k}: the leak read is the forward's");
                below += usize::from(leak[t * circles + k] < 0);
                let next = if (first + k) % 2 == 0 { t + 1 } else { t.wrapping_sub(1) };
                if next < sites {
                    let (qr, qi) = (i128::from(cell.qm[next * c2 + k]), i128::from(cell.qm[next * c2 + circles + k]));
                    assert_eq!(charge[t * circles + k], ((qr * qr + qi * qi) as u128).isqrt() as u64, "site {t} circle {k}: the charge is the scan's");
                    charged += 1;
                }
            }
        }
    }
    assert!(below > 0 && charged > 0, "the moved leak row turns some reads below zero, and the charges are read");
    assert!(shaped_with(four_contacts(1)).carry_leaks(&pass.ticks[0].read2).is_err(), "a field without circles refuses");
}

/// [definition; theory, November 11 19:56, G83's second defect, G85] **A field with carry circles keeps every room whole**: with the circles' charts,
/// biases and `W` columns drawn (so from the second tick a circle carries a place's state past any window), a region whose port cuts its room reads
/// the same faces, the same port code and the same covector as the same region with the cut off, because [`Declaration::room_window`] admits
/// no window where the field has circles; the same region on the field without circles still cuts.
#[test]
fn a_field_with_carry_circles_keeps_every_room_whole() {
    for ticks in [2usize, 4] {
        let plain = Constitution::found(Declaration { reach: 400, ticks, ..four_contacts(1) }, &keys(1 << 14)).unwrap();
        let (grown, _) = plain.with_carry(2, &keys(plain.declaration.carry_draws(2))).unwrap();
        let field = drawn(grown);
        let q = [1usize, 4, 0, 2, 3, 1];
        let sites = field.declaration.reach;
        let mut classes: Vec<usize> = q.to_vec();
        classes.resize(sites, 0);
        let open: Vec<bool> = (0..sites).map(|t| t >= q.len()).collect();
        let target = [3usize, 1, 2, 4, 1, 3, 2, 1, 4, 2, 3];
        let heard: Vec<bool> = (0..sites).map(|t| [0usize, 1, 2, 5, 13, 22, 47, 90, 200, 330].iter().any(|&d| t == q.len() + d)).collect();
        let region = |window: bool| Region {
            classes: &classes,
            unresolved: &open,
            faces: &[],
            locked: &[],
            echo: &[],
            domain: None,
            port: Some(Port { start: q.len(), void: 0, target: &target, boundary: true, stop: None, heard: Some(&heard), window, letters: false }), before: false, strand: false, past: false, second: false, targets: None
        };
        let (whole, cut) = (region(false), region(true));
        assert!(cut.window(ticks).is_some() && field.declaration.room_window(&cut).is_none(), "ticks {ticks}: the region cuts, the field keeps it whole");
        assert!(plain.declaration.room_window(&cut).is_some(), "ticks {ticks}: without circles the cut stands");
        assert_eq!(field.faces(&whole).unwrap(), field.faces(&cut).unwrap(), "ticks {ticks}: every face");
        assert_eq!(field.code(&whole).unwrap(), field.code(&cut).unwrap(), "ticks {ticks}: the port's code");
        let (_, gw) = field.read_and_return(&[whole]).unwrap();
        let (_, gc) = field.read_and_return(&[cut]).unwrap();
        assert_eq!(gw, gc, "ticks {ticks}: the covector");
        let l = field.layout.clone();
        assert!(gw[l.carry..l.carry_bias].iter().any(|&v| v != 0), "ticks {ticks}: the circles' charts have a covector to compare");
    }
}

/// [definition; theory, November 11 21:15, G86] **The parts line reads its own order and every older one**: a field without carry circles
/// writes nineteen parts (the plain sixteen, then the first lane's letter rows), one with circles twenty-two; a line of sixteen (before the
/// letter rows' parts) reads with them at octave 0, and so does a circled field's line of nineteen (the turn-carry line); a learner's octaves
/// round-trip through the text.
#[test]
fn the_parts_line_reads_its_own_order_and_every_older_one() {
    let mut learner = grown_learner();
    let mut octaves = [0u32; PARTS];
    (octaves[3], octaves[19], octaves[20], octaves[21]) = (1, 2, 3, 4);
    learner.rate_parts = Some(RateParts { contacts_before: 4, octaves });
    let text = learner.to_text();
    let line = text.lines().find(|l| l.starts_with("parts ")).unwrap().to_string();
    assert_eq!(line.split(' ').count(), 2 + 19);
    assert_eq!(Learner::from_text(&text).unwrap().rate_parts, learner.rate_parts, "the line's own order round-trips");
    let older: String = text.lines().map(|l| if l.starts_with("parts ") { format!("{}\n", l.split(' ').take(2 + PLAIN_PARTS).collect::<Vec<_>>().join(" ")) } else { format!("{l}\n") }).collect();
    let read = Learner::from_text(&older).unwrap().rate_parts.unwrap();
    assert_eq!((read.octaves[3], read.octaves[19], read.octaves[20], read.octaves[21]), (1, 0, 0, 0), "a sixteen-part line reads the letter rows at octave 0");
    assert_eq!(written_parts(0, 0, false, false, false, false, false), (0..16).chain(19..22).collect::<Vec<_>>());
    assert_eq!(written_parts(2, 0, false, false, false, false, false), (0..22).collect::<Vec<_>>());
}

/// The triads the drawn fixtures carry: four (the founding counts its triads in fours, the triad record §4).
const TRIADS: usize = 4;

/// [`four_contacts`]'s founded field grown by `triads` triads ([`Constitution::with_triads`]), then every family drawn ([`drawn`]): the triads' charts,
/// their biases and their return `W_T` off zero, so every triad's product reaches the face and every leg has a covector.
fn triad_shaped(still: usize, triads: usize) -> Constitution {
    let plain = Constitution::found(four_contacts(still), &keys(1 << 14)).unwrap();
    let (grown, _) = plain.with_triads(triads, &keys(plain.declaration.triad_draws(triads))).unwrap();
    drawn(grown)
}

/// A ring of four over the fixture's classes 0 to 3 under two characters (`K_1(a) = i^a`, `K_2(a) = (−1)^a`, at unit modulus on `2^(−16)`),
/// class 4 off the ring.
fn ring_of_four(alphabet: usize) -> Vec<i32> {
    let e = 2;
    let mut ring = vec![0i32; alphabet * 2 * e];
    for a in 0..4 {
        let (re, im) = [(1 << 16, 0), (0, 1 << 16), (-(1 << 16), 0), (0, -(1 << 16))][a];
        (ring[a * 2 * e], ring[a * 2 * e + e]) = (re, im);
        ring[a * 2 * e + 1] = if a % 2 == 0 { 1 << 16 } else { -(1 << 16) };
    }
    ring
}

/// [`triad_shaped`]'s field with closed characters on [`ring_of_four`], its odds' rows off zero.
fn closed_shaped(still: usize) -> Constitution {
    let field = triad_shaped(still, TRIADS);
    let d = field.declaration;
    let mut odds = vec![0i32; d.heads * (d.width + 1)];
    for h in 0..d.heads {
        for i in 0..d.width {
            odds[h * d.width + i] = (((h * 31 + i * 17) % 13) as i32 - 6) << 18;
        }
    }
    field.with_closed(2, &ring_of_four(d.alphabet), &odds).unwrap().0
}

/// [the lead, November 17, the founding records] **The closed face** ([`crate::closed`]): with no class on the ring every face is the
/// field's own; on a ring the faces move; the state reads back under `hnn-field-v14c`; and a learner's section runs through the reverse.
#[test]
fn the_closed_face_is_the_fields_own_with_no_ring_and_moves_on_one() {
    let field = triad_shaped(1, TRIADS);
    let d = field.declaration;
    let faces = field.faces(&region()).unwrap();
    let odds = vec![0i32; d.heads * (d.width + 1)];
    let (dark, from) = field.with_closed(2, &vec![0; d.alphabet * 4], &odds).unwrap();
    assert_eq!(dark.faces(&region()).unwrap(), faces, "with no class on the ring the faces are the field's own");
    assert!(from[..field.material_len()].iter().enumerate().all(|(i, o)| *o == Some(i)) && from[field.material_len()..].iter().all(Option::is_none));
    let closed = closed_shaped(1);
    assert_ne!(closed.faces(&region()).unwrap(), faces, "on a ring the faces are mixed");
    assert!(closed.declaration.to_text().starts_with("hnn-field-v14c "));
    assert_eq!(Constitution::from_text(&closed.to_text()).unwrap(), closed);
    assert!(field.with_closed(0, &[], &[]).is_err() && closed.with_closed(2, &ring_of_four(d.alphabet), &odds).is_err() && field.with_closed(2, &ring_of_four(d.alphabet)[1..], &odds).is_err());
    let mut learner = Learner::new(closed, 4);
    learner.section(&[region()]).unwrap();
}

/// [the lead, November 17, the founding records] **The closed face's covector matches its code's difference**: over every family of a
/// field with closed characters (the odds' rows and biases among them, and the lock's material, which the mixture reaches through the
/// last tick's rows), the reverse's covector at an entry predicts the code's change under a small step of that entry.
#[test]
fn the_closed_faces_covector_matches_its_codes_difference() {
    let sheets = |field: &Constitution, r: &Region| -> Vec<Vec<u32>> {
        let pass = field.pass(r, true).unwrap();
        pass.ticks.iter().flat_map(|c| c.classes.iter().map(|l| l.off.iter().chain(&l.members).copied().chain(l.probes.iter().flat_map(|p| std::iter::once(u32::MAX).chain(p.iter().copied()))).collect())).collect()
    };
    let (mut read, mut seams, mut odds_read, mut lock_read) = (0usize, 0usize, 0usize, 0usize);
    for still in [0usize, 1] {
        let field = closed_shaped(still);
        let r = region();
        let g = covector_of(&field, &r);
        let l = field.layout.clone();
        let (dw, heads) = (field.declaration.width, field.declaration.heads);
        assert!(g[l.closed_odds..l.closed_odds + heads * dw].iter().any(|&v| v != 0), "still {still}: the odds' rows have a covector");
        for &(start, len, grain) in field.families() {
            // The keys take no covector. The paces are read by their own test at two steps (`the_pace_covector_matches_the_code_at_two_steps`):
            // at one step their small covectors stand inside the code's grain here, on the plain field as on this one (a pace entry read
            // −154 against −40 predicted with no closed characters).
            if start == l.temper || start == l.closed_key || start == l.pace {
                continue;
            }
            let natural: u32 = if grain == MATERIAL_BITS { 40 } else { 24 };
            let mut entries: Vec<usize> = (start..start + len).collect();
            entries.sort_by_key(|&i| std::cmp::Reverse(g[i].unsigned_abs()));
            for i in entries.into_iter().take(3).filter(|&i| g[i] != 0) {
                let moved = |delta: i32| {
                    let mut f = field.clone();
                    f.theta[i] += delta;
                    f
                };
                let straddles = |delta: i32| sheets(&moved(delta), &r) != sheets(&field, &r) || sheets(&moved(-delta), &r) != sheets(&field, &r);
                let shift = natural + grain - 20;
                let Some((delta, h)) = probe_step(grain, &|delta: i32| (g[i] * 2 * delta as i128) >> shift, &straddles) else {
                    seams += 1;
                    continue;
                };
                read += 1;
                odds_read += usize::from(start == l.closed_odds || start == l.closed_odds_bias);
                lock_read += usize::from(start == l.q || start == l.probe);
                let measured = moved(delta).code(&r).unwrap().0 - moved(-delta).code(&r).unwrap().0;
                let predicted = (g[i] * 2 * delta as i128) >> shift;
                let tolerance = predicted.abs() / 8 + (64 << h);
                assert!((measured as i128 - predicted).abs() <= tolerance, "still {still} family at {start} (grain {grain}) entry {i} at {h} halvings: measured {measured}, predicted {predicted}");
            }
        }
    }
    eprintln!("CLOSED_COVECTOR_PROBES read={read} on_a_seam={seams} odds={odds_read} lock={lock_read}");
    assert!(odds_read >= 4 && lock_read >= 4, "the odds and the lock's words were read against the code ({odds_read}, {lock_read})");
}

/// [`four_contacts`]'s founded field grown by two carry circles and then by `triads` triads (the line's order: the triads are founded on a
/// circle line's end), every family drawn, with the circles' leak rows and leak biases set back to zero (`ℓ = 0`, the friction at its founding at
/// every site, far from its floor of one grain).
fn circled_triad_shaped(still: usize, triads: usize) -> Constitution {
    let plain = Constitution::found(four_contacts(still), &keys(1 << 14)).unwrap();
    let (circled, _) = plain.with_carry(2, &keys(plain.declaration.carry_draws(2))).unwrap();
    let (grown, _) = circled.with_triads(triads, &keys(circled.declaration.triad_draws(triads))).unwrap();
    let mut field = drawn(grown);
    let (l, dw, c) = (field.layout.clone(), field.declaration.width, field.declaration.carry);
    field.theta[l.carry + c * dw..l.carry + 2 * c * dw].fill(0);
    field.theta[l.carry_bias + c..l.carry_bias + 2 * c].fill(0);
    field
}

/// [definition; theory, November 12, the triad record §4] **The triads' head line, and every line at `J = 0` as before**: at `J = 0` the head is
/// `hnn-field-v14` (twelve words) or `hnn-field-v14e` (thirteen), exactly the lines before, and the triads' three families stand zero long at the
/// end; at `J = 16` it is `hnn-field-v14f`, the thirteen words of `v14e` with `C` written (also where it is zero), then `J`, and it round-trips;
/// the triads' families follow every other (`6J` rows of `D`, `6J` biases and `D × 2J`), every old offset and family unchanged; a `v14f` line with
/// no triads is refused, as a `v14e` line with no circles is, and so is a `v14f` line of thirteen words.
#[test]
fn the_triads_head_line_is_v14f_and_at_no_triads_every_line_is_as_before() {
    let d = four_contacts(1);
    let dw = d.width;
    let plain = d.to_text();
    assert!(plain.starts_with("hnn-field-v14 ") && plain.split(' ').count() == 12);
    assert_eq!(Declaration::from_text(&plain).unwrap(), d);
    let circled = Declaration { carry: 2, ..d };
    let line = circled.to_text();
    assert!(line.starts_with("hnn-field-v14e ") && line.split(' ').count() == 13 && line.ends_with(" 2"));
    assert_eq!(Declaration::from_text(&line).unwrap(), circled);
    let counts: Vec<String> = plain.split(' ').skip(1).map(str::to_string).collect();
    let j = 16usize;
    for base in [d, circled] {
        let tri = Declaration { triads: j, ..base };
        assert!(tri.admit().is_ok());
        let text = tri.to_text();
        let words: Vec<&str> = text.split(' ').collect();
        let c = base.carry.to_string();
        assert_eq!((words[0], words.len(), words[12], words[13]), ("hnn-field-v14f", 14, c.as_str(), "16"), "C {c}: the thirteen words of v14e with C written, then J");
        assert_eq!(words[1..12], counts.iter().map(String::as_str).collect::<Vec<_>>()[..], "C {c}: the declaration's eleven counts as before");
        assert_eq!(Declaration::from_text(&text).unwrap(), tri, "C {c}: the v14f line round-trips");
        let none = format!("{} 0", words[..13].join(" "));
        assert!(matches!(Declaration::from_text(&none), Err(TowerError::Refused(m)) if m.contains("no triads")), "C {c}: a v14f line with no triads is refused");
        assert!(Declaration::from_text(&words[..13].join(" ")).is_err(), "C {c}: a v14f line of thirteen words is refused");
        let (old, new) = (Loci::new(&base), Loci::new(&tri));
        assert_eq!((old.triad, old.triad_bias, old.w_triad), (old.len, old.len, old.len), "C {c}: at J = 0 the triads' families are zero long at the end");
        assert_eq!(new.families.len(), old.families.len() + 3);
        assert_eq!(new.families[..old.families.len()], old.families[..], "C {c}: every old family as before");
        assert_eq!(new.families[old.families.len()..], [(old.len, 6 * j * dw, MATERIAL_BITS), (old.len + 6 * j * dw, 6 * j, FACE_BITS), (old.len + 6 * j * dw + 6 * j, dw * 2 * j, MATERIAL_BITS)]);
        assert_eq!((new.triad, new.triad_bias, new.w_triad, new.len), (old.len, old.len + 6 * j * dw, old.len + 6 * j * dw + 6 * j, old.len + 6 * j * dw + 6 * j + dw * 2 * j));
        assert_eq!(Loci { triad: old.triad, triad_bias: old.triad_bias, w_triad: old.w_triad, opening: old.opening, opening_bias: old.opening_bias, junction: old.junction, junction_bias: old.junction_bias, mark: old.mark, loud: old.loud, closed_key: old.closed_key, closed_odds: old.closed_odds, closed_odds_bias: old.closed_odds_bias, pump: old.pump, pump_bias: old.pump_bias, lane_leak: old.lane_leak, friction: old.friction, friction_gate: old.friction_gate, fade: old.fade, len: old.len, families: old.families.clone(), ..new.clone() }, old, "C {c}: every old offset unchanged");
    }
}

/// [definition; theory, November 12, the triad record §4] **A growth by triads keeps every face, and its return has a covector**: on a drawn
/// field, with carry circles and without, [`Constitution::with_triads`] lays the triads' families after every other (the charts' rows drawn, their biases
/// and `W_T` at zero), keeps every old entry at its offset, reads every face and the code bit for bit and restores from its text, and `W_T` has a
/// covector while none yet reaches the charts (`∇_α ℓ = 0` while `W_T = 0`, §3.2); the draws counted are the draws read; a second growth, a growth
/// in contacts, in circles, in lanes or by copies of a field with triads, a growth by none, a founding with triads and a tower's growth are
/// refused. The learner keeps every old entry's moments, opens the triads' first moments at zero and their second at the means of their
/// counterparts' (the charts the pair drives', the biases the drives' biases', `W_T` `W`'s), keeps the parts' rates with the triad's at octave 0
/// and each entry's own rate with the triads' at the base rate, advances its draws by the triads', and its text round-trips with the written
/// parts; a parts line without the triad's octave (the line before the growth) reads it at 0.
#[test]
fn a_growth_by_triads_keeps_every_face_and_its_return_has_a_covector() {
    let j = 16usize;
    for still in [0usize, 1, 2] {
        for circled in [false, true] {
            let plain = if circled { circled_shaped(still) } else { shaped_with(four_contacts(still)) };
            let draws = plain.declaration.triad_draws(j);
            assert_eq!(draws, 6 * j * plain.declaration.width);
            assert!(plain.with_triads(j, &keys(draws)[..4 * draws - 1]).is_err(), "the draws counted are the draws read");
            let (grown, from) = plain.with_triads(j, &keys(draws)).unwrap();
            let (d, l, dw) = (grown.declaration, grown.layout.clone(), grown.declaration.width);
            assert_eq!(d, Declaration { triads: j, ..plain.declaration });
            let old = plain.theta.len();
            assert_eq!(grown.theta[..old], plain.theta[..], "still {still} circled {circled}: every old entry at its offset");
            assert!(from.len() == grown.theta.len() && from[..old].iter().enumerate().all(|(i, &o)| o == Some(i)) && from[old..].iter().all(Option::is_none));
            assert_eq!(grown.faces(&region()).unwrap(), plain.faces(&region()).unwrap(), "still {still} circled {circled}: every face kept");
            assert_eq!(grown.code(&region()).unwrap(), plain.code(&region()).unwrap(), "still {still} circled {circled}: the code kept");
            assert_eq!(Constitution::from_text(&grown.to_text()).unwrap(), grown);
            assert_eq!(l.len, l.w_triad + dw * 2 * j);
            assert!(grown.theta[l.triad..l.triad_bias].iter().any(|&v| v != 0), "the charts' rows drawn");
            assert!(grown.theta[l.triad_bias..l.len].iter().all(|&v| v == 0), "the charts' biases and W_T at zero");
            let g = covector_of(&grown, &region());
            assert!(g[l.w_triad..l.len].iter().any(|&v| v != 0), "still {still} circled {circled}: W_T has a covector");
            assert!(g[l.triad..l.w_triad].iter().all(|&v| v == 0), "still {still} circled {circled}: while W_T is zero no covector reaches the charts");
            assert!(grown.with_triads(4, &keys(d.triad_draws(4))).is_err(), "a second growth by triads");
            assert!(grown.contacted(4, &keys(d.contact_draws(4))).is_err(), "a growth in contacts of a field with triads");
            assert!(grown.with_carry(2, &keys(d.carry_draws(2))).is_err(), "a growth in circles of a field with triads");
            assert!(grown.laned(&keys(d.lane_draws())).is_ok(), "a lane grows beside triads (the lane's test holds its faces)");
            assert!(grown.grown(2, &keys(grown.growth_draws(2))).is_err(), "a growth by copies of a field with triads");
        }
    }
    assert!(shaped_with(four_contacts(1)).with_triads(0, &keys(1)).is_err(), "a growth by no triads");
    assert!(Constitution::found(Declaration { triads: 4, ..four_contacts(1) }, &keys(1 << 14)).is_err(), "a founding with triads");
    let tower = towered(1);
    assert!(tower.with_triads(4, &keys(tower.declaration.triad_draws(4))).is_err(), "a tower's levels take triads level by level");
    // The learner.
    let mut learner = Learner::new(shaped_with(four_contacts(1)), 6);
    learner.section(&[region()]).unwrap();
    learner.held = None;
    let mut octaves = [0u32; PARTS];
    (octaves[3], octaves[19], octaves[TRIAD_PART]) = (2, 1, 5);
    learner.rate_parts = Some(RateParts { contacts_before: 8, octaves });
    let j = TRIADS;
    let stream = keys(learner.drawn / 4 + learner.field.declaration.triad_draws(j) + 8);
    let grown = learner.with_triads(j, &stream).unwrap();
    assert_eq!(grown.drawn, learner.drawn + 4 * learner.field.declaration.triad_draws(j));
    let old = learner.field.theta.len();
    assert_eq!((&grown.first[..old], &grown.second[..old]), (&learner.first[..], &learner.second[..]), "every old entry keeps its moments");
    let (l, ol) = (grown.field.layout.clone(), learner.field.layout.clone());
    let (dw, f) = (learner.field.declaration.width, learner.field.declaration.contacts);
    let mean = |ranges: &[(usize, usize)]| -> i128 {
        let v: Vec<i128> = ranges.iter().flat_map(|&(s, n)| learner.second[s..s + n].iter().copied()).collect();
        let n = v.len() as i128;
        v.iter().map(|x| x / n).sum::<i128>() + v.iter().map(|x| x % n).sum::<i128>() / n
    };
    let (drives, biases, ret) = (mean(&[(ol.a, f * dw), (ol.b, f * dw)]), mean(&[(ol.a_bias, f), (ol.b_bias, f)]), mean(&[(ol.w, dw * f)]));
    assert!(drives > 0 && ret > 0, "the counterparts' second moments are open");
    assert!(grown.first[old..].iter().all(|&v| v == 0), "the triads' first moments open at zero");
    assert!(grown.second[l.triad..l.triad_bias].iter().all(|&v| v == drives), "A, B and G open at the pair drives' mean");
    assert!(grown.second[l.triad_bias..l.w_triad].iter().all(|&v| v == biases), "the charts' biases at the drives' biases' mean");
    assert!(grown.second[l.w_triad..l.len].iter().all(|&v| v == ret), "W_T at W's mean");
    let mut kept = octaves;
    kept[TRIAD_PART] = 0;
    assert_eq!(grown.rate_parts, Some(RateParts { contacts_before: 8, octaves: kept }), "the parts' rates kept, the triad's at octave 0");
    assert_eq!(grown.own_rates, None);
    assert_eq!(grown.field.faces(&region()).unwrap(), learner.field.faces(&region()).unwrap(), "the grown learner reads every face");
    // The text: the parts line of the written parts, the triad's last, round-tripping.
    let mut fast = grown.clone();
    fast.rate_parts.as_mut().unwrap().octaves[TRIAD_PART] = 3;
    let text = fast.to_text();
    let line = text.lines().find(|l| l.starts_with("parts ")).unwrap().to_string();
    assert_eq!(line.split(' ').count(), 2 + written_parts(0, j, false, false, false, false, false).len());
    assert_eq!(line.rsplit_once(' ').unwrap().1, "3", "the triad's octave written last");
    let back = Learner::from_text(&text).unwrap();
    assert_eq!((back.field.clone(), back.first.clone(), back.second.clone(), back.rate_parts, back.drawn), (fast.field.clone(), fast.first.clone(), fast.second.clone(), fast.rate_parts, fast.drawn));
    let before: String = text.lines().map(|l| if l.starts_with("parts ") { format!("{}\n", l.rsplit_once(' ').unwrap().0) } else { format!("{l}\n") }).collect();
    assert_eq!(Learner::from_text(&before).unwrap().rate_parts, grown.rate_parts, "a line without the triad's octave reads it at 0 and every other part as written");
    // Each entry's own rate, where the learner carries it.
    let mut own = learner.clone();
    own.own_rates = Some((0..own.field.material_len()).map(|i| if i % 3 == 0 { 8 } else { 5 }).collect());
    let grown_own = own.with_triads(j, &stream).unwrap();
    let rates = grown_own.own_rates.clone().unwrap();
    assert_eq!(rates.len(), grown_own.field.material_len());
    assert_eq!(rates[..old], own.own_rates.as_ref().unwrap()[..], "every old entry keeps its own rate");
    assert!(rates[old..].iter().all(|&r| r == own.rate_bits), "the triads' entries at the base rate");
    assert_eq!(grown_own.entry_rates(), rates);
}

/// [proved-derived; theory, November 12, the triad record §3.2; `lean/Holonics/HNN/TriadGauge.lean`] **The quarter-turn gauge leaves every face and
/// the code**: on a drawn field with triads and a nonzero `W_T`, with carry circles and without, turning every triad's `α` by `i` and its `β` by
/// `−i` on `A`'s and `B`'s rows and their biases (`α_r ← −α_i`, `α_i ← α_r`; `β_r ← β_i`, `β_i ← −β_r`) changes every read of the two legs and leaves
/// every product `p`, every `c^T`, every face and the code bit for bit, since `(iα)(−iβ) = αβ` holds on Gaussian integers and each read is one
/// affine whose release is odd; a turn of `α` alone moves the faces, so the reads do see the triads.
#[test]
fn the_quarter_turn_gauge_leaves_every_face_and_the_code() {
    // A leg turned `by` `i` (`1`) or `−i` (`−1`), or left (`0`): `(r, i) → (−by·i, by·r)` on its rows' entries and its biases.
    let gauge = |field: &Constitution, alpha: i32, beta: i32| -> Constitution {
        let mut out = field.clone();
        let (l, dw, j) = (field.layout.clone(), field.declaration.width, field.declaration.triads);
        for k in 0..j {
            for (by, re, im) in [(alpha, k, j + k), (beta, 2 * j + k, 3 * j + k)] {
                if by == 0 {
                    continue;
                }
                for (rr, ii) in (0..dw).map(|c| (l.triad + re * dw + c, l.triad + im * dw + c)).chain([(l.triad_bias + re, l.triad_bias + im)]) {
                    (out.theta[rr], out.theta[ii]) = (-by * field.theta[ii], by * field.theta[rr]);
                }
            }
        }
        out
    };
    let mut carried: Vec<Option<Shares>> = vec![None; CLASSES.len()];
    carried[0] = Some(vec![(1, 40_000), (3, 25_536)]);
    carried[4] = Some(vec![(2, 30_000), (4, 20_000), (0, 15_536)]);
    for (still, circled) in [(0usize, false), (1, false), (2, false), (1, true)] {
        let field = if circled { circled_triad_shaped(still, TRIADS) } else { triad_shaped(still, TRIADS) };
        let l = field.layout.clone();
        assert!(field.theta[l.w_triad..l.len].iter().any(|&v| v != 0), "a nonzero W_T");
        let turned = gauge(&field, 1, -1);
        assert_ne!(turned.theta, field.theta);
        for r in [region(), Region { classes: &CLASSES, unresolved: &OPEN, faces: &carried, locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None }] {
            assert_eq!(turned.faces(&r).unwrap(), field.faces(&r).unwrap(), "still {still} circled {circled}: every face");
            assert_eq!(turned.code(&r).unwrap(), field.code(&r).unwrap(), "still {still} circled {circled}: the code");
            let (a, b) = (field.pass(&r, true).unwrap(), turned.pass(&r, true).unwrap());
            for (x, y) in a.ticks.iter().zip(&b.ticks) {
                assert_ne!(x.abg, y.abg, "still {still} circled {circled}: the legs' reads turn");
                assert_eq!((&x.tp, &x.ct), (&y.tp, &y.ct), "still {still} circled {circled}: every product and every triad as before");
            }
        }
        assert_ne!(gauge(&field, 1, 0).faces(&region()).unwrap(), field.faces(&region()).unwrap(), "still {still} circled {circled}: a turn of α alone moves the faces");
    }
}

/// [definition; theory, November 12, the triad record §4] **The triads' reverse agrees with the code's change along a direction**: on drawn fields
/// with triads (three ring sets' stills, and one with carry circles beside the triads), each family's three entries with the largest covectors
/// (the triads' charts, biases and `W_T` among them) are moved by `±δ` and the code's change is read against the covector's prediction by the
/// probe law of [`the_carry_circles_covector_matches_its_codes_difference`] (a probe whose step moves a site across a sheet is left out and
/// counted); the triads' charts, biases and return are each read at least once.
#[test]
fn the_triads_covector_matches_its_codes_difference() {
    let sheets = |field: &Constitution, r: &Region| -> Vec<Vec<u32>> {
        let pass = field.pass(r, true).unwrap();
        pass.ticks.iter().flat_map(|c| c.classes.iter().map(|l| l.off.iter().chain(&l.members).copied().chain(l.probes.iter().flat_map(|p| std::iter::once(u32::MAX).chain(p.iter().copied()))).collect())).collect()
    };
    let (mut read, mut seams, mut charts, mut biases, mut returns) = (0usize, 0usize, 0usize, 0usize, 0usize);
    for (still, circled) in [(0usize, false), (1, false), (2, false), (1, true)] {
        let field = if circled { circled_triad_shaped(still, TRIADS) } else { triad_shaped(still, TRIADS) };
        let r = region();
        let g = covector_of(&field, &r);
        let l = field.layout.clone();
        assert!(g[l.triad..l.triad_bias].iter().any(|&v| v != 0) && g[l.w_triad..l.len].iter().any(|&v| v != 0), "still {still} circled {circled}: the charts and W_T have a covector");
        for &(start, len, grain) in field.families() {
            if start == l.temper {
                continue;
            }
            let natural: u32 = if grain == MATERIAL_BITS { 40 } else { 24 };
            let mut entries: Vec<usize> = (start..start + len).collect();
            entries.sort_by_key(|&i| std::cmp::Reverse(g[i].unsigned_abs()));
            for i in entries.into_iter().take(3).filter(|&i| g[i] != 0) {
                let moved = |delta: i32| {
                    let mut f = field.clone();
                    f.theta[i] += delta;
                    f
                };
                let straddles = |delta: i32| sheets(&moved(delta), &r) != sheets(&field, &r) || sheets(&moved(-delta), &r) != sheets(&field, &r);
                let shift = natural + grain - 20;
                let Some((delta, h)) = probe_step(grain, &|delta: i32| (g[i] * 2 * delta as i128) >> shift, &straddles) else {
                    seams += 1;
                    continue;
                };
                read += 1;
                charts += usize::from(start == l.triad);
                biases += usize::from(start == l.triad_bias);
                returns += usize::from(start == l.w_triad);
                let measured = moved(delta).code(&r).unwrap().0 - moved(-delta).code(&r).unwrap().0;
                let predicted = (g[i] * 2 * delta as i128) >> shift;
                let tolerance = predicted.abs() / 8 + (64 << h);
                assert!((measured as i128 - predicted).abs() <= tolerance, "still {still} circled {circled} family at {start} (grain {grain}) entry {i} at {h} halvings: measured {measured}, predicted {predicted}");
            }
        }
    }
    eprintln!("TRIAD_COVECTOR_PROBES read={read} on_a_seam={seams} charts={charts} biases={biases} returns={returns}");
    assert!(read > 0 && 16 * seams <= read && charts > 0 && biases > 0 && returns > 0, "read {read} probes, {seams} on a seam, {charts} of the charts, {biases} of the biases, {returns} of the return");
}

/// [proved-derived; theory, November 12, the triad record §3.2 (the legs exchange equal quanta); `TriadGauge.lean`] **Each leg and the return
/// carry one scale covector**: the return is unchanged under `(α_k, w_k) → (s α_k, w_k/s)` for real `s` (and so for `β_k` and for `γ_k`), so the
/// code's derivative along that direction is zero at `s = 1` and the reverse gives `Re⟨α_k, ∇_α ℓ⟩ = Re⟨w_k, ∇_w ℓ⟩`, and likewise for `β_k` and
/// `γ_k`: on drawn fields with triads, each triad's three legs (their two rows and two biases each) and its two columns of `W_T` read `Σ θ g` on
/// the codes' `2^(−20)` bits (the probes' shifts) equal within an eighth and the releases' floor. Why it is read: the legs and the return are
/// one family that no receiver tells apart, and this identity is what their covectors keep at every state. Under a plain step at one rate it
/// gives each leg the same squared norm to first order (Manley–Rowe); this learner divides each entry's step by its own `⌊√v⌋ + 1`, and its
/// divisors move with what reaches each entry, so equal gains of the legs are no prediction for it. The triad's one octave stands because an
/// octave between the legs would be a rate set by hand.
#[test]
fn each_triads_legs_and_return_carry_one_scale_covector() {
    for (still, circled) in [(0usize, false), (1, false), (2, false), (1, true)] {
        let field = if circled { circled_triad_shaped(still, TRIADS) } else { triad_shaped(still, TRIADS) };
        let g = covector_of(&field, &region());
        let (l, dw, j) = (field.layout.clone(), field.declaration.width, field.declaration.triads);
        // `Σ θ g` over a set of entries on the codes' grain: shifted 44 bits on the material's grain and 20 on the face's.
        let scale = |entries: &[usize], shift: u32| -> i128 { entries.iter().map(|&i| i128::from(field.theta[i]) * g[i]).sum::<i128>() >> shift };
        let mut standing = 0usize;
        for k in 0..j {
            let columns: Vec<usize> = (0..dw).flat_map(|o| [l.w_triad + o * 2 * j + k, l.w_triad + o * 2 * j + j + k]).collect();
            let ret = scale(&columns, 44);
            standing += usize::from(ret.abs() > 64);
            for (leg, (re, im)) in [(k, j + k), (2 * j + k, 3 * j + k), (4 * j + k, 5 * j + k)].into_iter().enumerate() {
                let rows: Vec<usize> = (0..dw).flat_map(|c| [l.triad + re * dw + c, l.triad + im * dw + c]).collect();
                let along = scale(&rows, 44) + scale(&[l.triad_bias + re, l.triad_bias + im], 20);
                assert!((along - ret).abs() <= ret.abs() / 8 + 64, "still {still} circled {circled} triad {k} leg {leg}: Re⟨leg, ∇⟩ {along} against Re⟨w, ∇_w⟩ {ret}");
            }
        }
        assert!(standing > 0, "still {still} circled {circled}: some triad's scale covector stands above the floor");
    }
}

/// [`triad_shaped`] with the triads' legs at the site ([`Declaration::crossing`]): the same material, the legs read where the theory's crossing
/// triad reads them.
fn crossing_shaped(still: usize, triads: usize) -> Constitution {
    let strand = triad_shaped(still, triads);
    let d = Declaration { crossing: true, ..strand.declaration };
    let mut out = Constitution::with_theta(d, strand.theta.clone());
    (out.per_blank_clock, out.bare_stretch) = (strand.per_blank_clock, strand.bare_stretch);
    out
}

/// [definition; theory, November 16 19:10Z, the crossing triad] **The crossing triads are the law at every site, the region's ends included**: with
/// the legs at the site, `p = release(α(t) β(t), 16)` and `c^T = release(p γ(t), 16)` at every site (a region of two sites included), and the
/// reverse is each site's own three slots (`δγ(t) = conj(p) u`, `δp = conj(γ(t)) u`, `δα(t) = conj(β(t)) δp`, `δβ(t) = conj(α(t)) δp`); each leg
/// and the return carry one scale covector (the Manley–Rowe gauge, as the strand's legs do); and the declaration's head line reads and writes back
/// as `hnn-field-v14x` while every field without the crossing writes its line as before.
#[test]
fn the_crossing_triads_are_the_law_at_every_site() {
    let field = crossing_shaped(1, TRIADS);
    let (l, dw, j) = (field.layout.clone(), field.declaration.width, field.declaration.triads);
    let (j2, j6) = (2 * j, 6 * j);
    let sites = CLASSES.len();
    let pass = field.pass(&region(), true).unwrap();
    let conj = |(zr, zi): (i128, i128), (ur, ui): (i128, i128)| (release(zr * ur + zi * ui, FACE_BITS), release(zr * ui - zi * ur, FACE_BITS));
    let leg = |v: &[i64], s: usize, base: usize, k: usize| (i128::from(v[s * j6 + base + k]), i128::from(v[s * j6 + base + j + k]));
    let pair = |v: &[i64], s: usize, k: usize| (i128::from(v[s * j2 + k]), i128::from(v[s * j2 + j + k]));
    for (tick, cell) in pass.ticks.iter().enumerate() {
        for t in 0..sites {
            for k in 0..j {
                let ((ar, ai), (br, bi), (gr, gi)) = (leg(&cell.abg, t, 0, k), leg(&cell.abg, t, j2, k), leg(&cell.abg, t, 2 * j2, k));
                let (pr, pi) = (release(ar * br - ai * bi, FACE_BITS), release(ar * bi + ai * br, FACE_BITS));
                assert_eq!(pair(&cell.tp, t, k), (pr, pi), "tick {tick} site {t} triad {k}: p = α(t) β(t)");
                assert_eq!(pair(&cell.ct, t, k), (release(pr * gr - pi * gi, FACE_BITS), release(pr * gi + pi * gr, FACE_BITS)), "tick {tick} site {t} triad {k}: c^T = p γ(t)");
            }
        }
        assert!(cell.ct[..j2].iter().chain(&cell.ct[(sites - 1) * j2..]).any(|&v| v != 0), "tick {tick}: the crossing stands at the region's ends");
        let dct: Vec<i64> = (0..sites * j2).map(|i| ((i % 7) as i64 - 3) << 30).collect();
        let dabg = triad_back(j, sites, &cell.abg, &cell.tp, &dct, true).unwrap();
        for t in 0..sites {
            for k in 0..j {
                let u = pair(&dct, t, k);
                let dp = conj(leg(&cell.abg, t, 2 * j2, k), u);
                assert_eq!(leg(&dabg, t, 2 * j2, k), conj(pair(&cell.tp, t, k), u), "tick {tick} site {t} triad {k}: δγ(t) = conj(p) u");
                assert_eq!(leg(&dabg, t, 0, k), conj(leg(&cell.abg, t, j2, k), dp), "tick {tick} site {t} triad {k}: δα(t) = conj(β(t)) δp");
                assert_eq!(leg(&dabg, t, j2, k), conj(leg(&cell.abg, t, 0, k), dp), "tick {tick} site {t} triad {k}: δβ(t) = conj(α(t)) δp");
            }
        }
    }
    let (two, open) = ([1usize, 3], [false, true]);
    let small = Region { classes: &two, unresolved: &open, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None };
    assert!(field.pass(&small, true).unwrap().ticks.iter().any(|c| c.ct.iter().any(|&v| v != 0)), "a region of two sites holds crossing triads");
    // One scale covector across each triad's legs and its return, as the strand's.
    let g = covector_of(&field, &region());
    let scale = |entries: &[usize], shift: u32| -> i128 { entries.iter().map(|&i| i128::from(field.theta[i]) * g[i]).sum::<i128>() >> shift };
    let mut standing = 0usize;
    for k in 0..j {
        let columns: Vec<usize> = (0..dw).flat_map(|o| [l.w_triad + o * 2 * j + k, l.w_triad + o * 2 * j + j + k]).collect();
        let ret = scale(&columns, 44);
        standing += usize::from(ret.abs() > 64);
        for (re, im) in [(k, j + k), (2 * j + k, 3 * j + k), (4 * j + k, 5 * j + k)] {
            let rows: Vec<usize> = (0..dw).flat_map(|c| [l.triad + re * dw + c, l.triad + im * dw + c]).collect();
            let along = scale(&rows, 44) + scale(&[l.triad_bias + re, l.triad_bias + im], 20);
            assert!((along - ret).abs() <= ret.abs() / 8 + 64, "triad {k}: Re⟨leg, ∇⟩ {along} against Re⟨w, ∇_w⟩ {ret}");
        }
    }
    assert!(standing > 0, "some crossing triad's scale covector stands above the floor");
    let line = field.declaration.to_text();
    assert!(line.starts_with("hnn-field-v14x ") && line.ends_with(" 1"), "{line}");
    assert_eq!(Declaration::from_text(&line).unwrap(), field.declaration);
    assert!(!triad_shaped(1, TRIADS).declaration.to_text().starts_with("hnn-field-v14x"));
    assert!(Declaration::from_text(&line.replace("hnn-field-v14x", "hnn-field-v14l")).is_err(), "a crossing word after a v14l head is no line");
}

/// [definition; theory, November 12, the triad record §3 and §4] **The triads are the law site by site, with no triad and no covector at a
/// region's two ends**: on a drawn field with triads, at every tick each site's reads `α, β, γ` are the charts' affine of its pair chart, and at
/// every site with both strand mates `p = release(α(t) β(t − 1), 16)` and `c^T = release(p γ(t + 1), 16)`, while `p` and `c^T` are zero at the first
/// and last sites; the reverse ([`triad_back`]) is each slot's one product (`δγ(t + 1) = conj(p) u`, `δp = conj(γ(t + 1)) u`,
/// `δα(t) = conj(β(t − 1)) δp`, `δβ(t − 1) = conj(α(t)) δp`) and writes nothing to `δα` at the two ends, to `δβ` at the last two sites or to `δγ` at
/// the first two; a region of two sites holds no triad, and no covector reaches the triads' families from it.
#[test]
fn the_triads_are_the_law_site_by_site_with_none_at_a_regions_two_ends() {
    let field = triad_shaped(1, TRIADS);
    let (l, dw, j) = (field.layout.clone(), field.declaration.width, field.declaration.triads);
    let (j2, j6) = (2 * j, 6 * j);
    let sites = CLASSES.len();
    let reaches = field.reaches();
    let pass = field.pass(&region(), true).unwrap();
    let conj = |(zr, zi): (i128, i128), (ur, ui): (i128, i128)| (release(zr * ur + zi * ui, FACE_BITS), release(zr * ui - zi * ur, FACE_BITS));
    // A leg's complex value `[t][6J]` (its base `0`, `2J` or `4J`), and a product's `[t][2J]`.
    let leg = |v: &[i64], s: usize, base: usize, k: usize| (i128::from(v[s * j6 + base + k]), i128::from(v[s * j6 + base + j + k]));
    let pair = |v: &[i64], s: usize, k: usize| (i128::from(v[s * j2 + k]), i128::from(v[s * j2 + j + k]));
    for (tick, cell) in pass.ticks.iter().enumerate() {
        let mut abg = vec![0i64; j6];
        for t in 0..sites {
            affine(&field.theta[l.triad..l.triad + j6 * dw], reaches.triad, dw, &cell.read2[t * dw..(t + 1) * dw], Some(&field.theta[l.triad_bias..l.triad_bias + j6]), MATERIAL_BITS, MATERIAL_BITS, &mut abg).unwrap();
            assert_eq!(cell.abg[t * j6..(t + 1) * j6], abg[..], "tick {tick} site {t}: the charts' reads of the pair chart");
        }
        for t in [0, sites - 1] {
            assert!(cell.tp[t * j2..(t + 1) * j2].iter().chain(&cell.ct[t * j2..(t + 1) * j2]).all(|&v| v == 0), "tick {tick}: no triad at the region's end {t}");
        }
        for t in 1..sites - 1 {
            for k in 0..j {
                let ((ar, ai), (br, bi), (gr, gi)) = (leg(&cell.abg, t, 0, k), leg(&cell.abg, t - 1, j2, k), leg(&cell.abg, t + 1, 2 * j2, k));
                let (pr, pi) = (release(ar * br - ai * bi, FACE_BITS), release(ar * bi + ai * br, FACE_BITS));
                assert_eq!(pair(&cell.tp, t, k), (pr, pi), "tick {tick} site {t} triad {k}: p = α(t) β(t − 1)");
                assert_eq!(pair(&cell.ct, t, k), (release(pr * gr - pi * gi, FACE_BITS), release(pr * gi + pi * gr, FACE_BITS)), "tick {tick} site {t} triad {k}: c^T = p γ(t + 1)");
            }
        }
        assert!(cell.ct.iter().any(|&v| v != 0), "tick {tick}: the triads stand inside the region");
        // The reverse against a covector standing at every site.
        let dct: Vec<i64> = (0..sites * j2).map(|i| ((i % 7) as i64 - 3) << 30).collect();
        let dabg = triad_back(j, sites, &cell.abg, &cell.tp, &dct, false).unwrap();
        for k in 0..j {
            for t in [0, sites - 1] {
                assert_eq!(leg(&dabg, t, 0, k), (0, 0), "tick {tick} triad {k}: no δα at the end {t}");
            }
            for t in [sites - 2, sites - 1] {
                assert_eq!(leg(&dabg, t, j2, k), (0, 0), "tick {tick} triad {k}: no δβ at {t}, which no place after it reads");
            }
            for t in [0, 1] {
                assert_eq!(leg(&dabg, t, 2 * j2, k), (0, 0), "tick {tick} triad {k}: no δγ at {t}, which no place before it reads");
            }
            for t in 1..sites - 1 {
                let u = pair(&dct, t, k);
                let dp = conj(leg(&cell.abg, t + 1, 2 * j2, k), u);
                assert_eq!(leg(&dabg, t + 1, 2 * j2, k), conj(pair(&cell.tp, t, k), u), "tick {tick} site {t} triad {k}: δγ(t + 1) = conj(p) u");
                assert_eq!(leg(&dabg, t, 0, k), conj(leg(&cell.abg, t - 1, j2, k), dp), "tick {tick} site {t} triad {k}: δα(t) = conj(β(t − 1)) δp");
                assert_eq!(leg(&dabg, t - 1, j2, k), conj(leg(&cell.abg, t, 0, k), dp), "tick {tick} site {t} triad {k}: δβ(t − 1) = conj(α(t)) δp");
            }
        }
        assert!(dabg.iter().any(|&v| v != 0), "tick {tick}: the reverse reaches the legs inside the region");
    }
    // A region of two sites: no place has both of its strand mates.
    let (two, open) = ([1usize, 3], [false, true]);
    let small = Region { classes: &two, unresolved: &open, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None };
    let pass = field.pass(&small, true).unwrap();
    assert!(pass.ticks.iter().all(|c| c.tp.iter().chain(&c.ct).all(|&v| v == 0)), "no triad in a region of two sites");
    let g = covector_of(&field, &small);
    assert!(g[l.triad..l.len].iter().all(|&v| v == 0), "no covector reaches the triads' families from a region of two sites");
    assert!(g[..l.triad].iter().any(|&v| v != 0), "the region's covector stands elsewhere");
}

/// [definition; theory, November 12, the triad record §4] **The triad is one founded part, written only where the field has triads**: its charts,
/// their biases and its return hold part 22, `triad`, and every old entry's part is as before; the parts line writes it after the first lane's
/// letter rows only where the field has triads, so at `J = 0` the written parts are the lines before.
#[test]
fn the_triad_is_one_founded_part_written_only_where_the_field_has_triads() {
    assert_eq!((PART_NAMES[TRIAD_PART], TRIAD_PART, PARTS), ("triad", 22, 30));
    assert_eq!((PART_NAMES[FRICTION_PART], FRICTION_PART), ("friction", 28));
    assert_eq!((PART_NAMES[FADE_PART], FADE_PART), ("fade", 29));
    assert_eq!((PART_NAMES[LOUD_PART], LOUD_PART), ("loud", 26));
    assert_eq!((PART_NAMES[LEAK_PART], LEAK_PART), ("lane_leak", 27));
    assert_eq!((PART_NAMES[OPENING_PART], OPENING_PART), ("opening", 23));
    assert_eq!((PART_NAMES[JUNCTION_PART], JUNCTION_PART), ("junction", 24));
    assert_eq!((PART_NAMES[MARK_PART], MARK_PART), ("mark", 25));
    assert_eq!(written_parts(2, TRIADS, true, true, true, false, false), (0..26).collect::<Vec<_>>(), "the mark's part last, only where the field reads twice");
    assert_eq!(written_parts(2, TRIADS, true, true, false, false, false), (0..25).collect::<Vec<_>>(), "the junction's part last, only where the tick has the return");
    assert_eq!(written_parts(0, 0, false, false, false, false, false), (0..16).chain(19..22).collect::<Vec<_>>());
    assert_eq!(written_parts(2, 0, false, false, false, false, false), (0..22).collect::<Vec<_>>());
    assert_eq!(written_parts(0, TRIADS, false, false, false, false, false), (0..16).chain(19..23).collect::<Vec<_>>());
    assert_eq!(written_parts(2, TRIADS, false, false, false, false, false), (0..23).collect::<Vec<_>>());
    for circled in [false, true] {
        let field = if circled { circled_triad_shaped(1, TRIADS) } else { triad_shaped(1, TRIADS) };
        let (l, dw, j) = (field.layout.clone(), field.declaration.width, field.declaration.triads);
        let contacts = field.declaration.contacts;
        let parts = field.founded_parts(contacts);
        assert!(parts[l.triad..l.len].iter().all(|&p| usize::from(p) == TRIAD_PART), "circled {circled}: the charts, their biases and W_T");
        assert_eq!(parts.iter().filter(|&&p| usize::from(p) == TRIAD_PART).count(), 6 * j * dw + 6 * j + dw * 2 * j, "circled {circled}: and nothing else");
        let mut before = field.clone();
        before.declaration.triads = 0;
        before.theta.truncate(l.triad);
        before.layout = Loci::new(&before.declaration);
        assert_eq!(parts[..l.triad], before.founded_parts(contacts)[..], "circled {circled}: every old entry's part as before");
    }
}

/// [definition; theory, November 12 (the record of the opening's room, §4 item 4)] **A growth by letters keeps every standing entry and reads
/// each fresh letter at the least class bias**: on drawn fields (still heads or turned, plain, with carry circles, with triads), [`Constitution::lettered`]
/// at no fresh class returns the field as it stands (its text byte for byte, every entry its own); at one and three fresh classes every standing
/// entry keeps its value (the open rows at the end of their families), each fresh class's rows of the encodings, the moment encodings and the
/// paces stand at zero and its class bias at the least the standing classes hold, the text round-trips, and on a region of standing classes each
/// face's standing logits are equal entry for entry before and after and each fresh logit is the least bias. A tower's levels are refused. The
/// learner reads no key (its draws stand), keeps every standing entry's moments, opens a fresh entry's first moment at zero and its second at
/// its family's standing mean, keeps the parts' rates and each standing entry's own rate (a fresh one at `rate_bits`), keeps its pass, and is
/// refused while a step is held.
#[test]
fn a_growth_by_letters_keeps_every_standing_entry_and_reads_fresh_letters_at_the_least_bias() {
    let fields: Vec<(&str, Constitution)> = (0..3usize)
        .flat_map(|still| [(format!("plain {still}"), shaped_with(four_contacts(still))), (format!("circled {still}"), circled_shaped(still)), (format!("triads {still}"), circled_triad_shaped(still, TRIADS))])
        .map(|(n, f)| (Box::leak(n.into_boxed_str()) as &str, f))
        .collect();
    let mut forward_kept = 0usize;
    for (name, plain) in &fields {
        let (same, from) = plain.lettered(0).unwrap();
        assert_eq!((&same, same.to_text()), (plain, plain.to_text()), "{name}: no fresh class leaves the field as it stands");
        assert!(from.iter().enumerate().all(|(i, &o)| o == Some(i)), "{name}: every entry its own");
        let (a, dw) = (plain.declaration.alphabet, plain.declaration.width);
        let (ol, tm2, paced) = (plain.layout.clone(), 2 * plain.declaration.moment_modes(), plain.declaration.paced_heads());
        let least = plain.theta[ol.read_bias..ol.read_bias + a].iter().copied().min().unwrap();
        let before = plain.logits(&region()).unwrap();
        for fresh in [1usize, 3] {
            let (grown, from) = plain.lettered(fresh).unwrap();
            let (d, l, a2) = (grown.declaration, grown.layout.clone(), a + fresh);
            assert_eq!(d, Declaration { alphabet: a2, ..plain.declaration }, "{name}: the alphabet grows and nothing else");
            assert_eq!(from.len(), grown.theta.len());
            assert_eq!(from.iter().filter(|o| o.is_some()).count(), plain.theta.len(), "{name}: every standing entry is carried once");
            for (k, &o) in from.iter().enumerate() {
                if let Some(i) = o {
                    assert_eq!(grown.theta[k], plain.theta[i], "{name} +{fresh}: entry {k} keeps its value");
                }
            }
            for (o, n, width) in [(ol.enc, l.enc, dw), (ol.before, l.before, dw), (ol.after, l.after, dw), (ol.moment_before, l.moment_before, tm2), (ol.moment_after, l.moment_after, tm2)] {
                assert_eq!(grown.theta[n..n + a * width], plain.theta[o..o + a * width], "{name} +{fresh}: the standing classes' rows at their indices");
                assert!(grown.theta[n + a * width..n + a2 * width].iter().all(|&v| v == 0), "{name} +{fresh}: a fresh class's rows at zero");
                assert_eq!(grown.theta[n + a2 * width..n + (a2 + 1) * width], plain.theta[o + a * width..o + (a + 1) * width], "{name} +{fresh}: the open row at the end");
            }
            for p in 0..paced {
                let (o, n) = (ol.pace + p * (a + 1), l.pace + p * (a2 + 1));
                assert_eq!(grown.theta[n..n + a], plain.theta[o..o + a]);
                assert!(grown.theta[n + a..n + a2].iter().all(|&v| v == 0), "{name} +{fresh}: a fresh pace at zero");
                assert_eq!(grown.theta[n + a2], plain.theta[o + a], "{name} +{fresh}: the open row's pace at the end");
            }
            assert_eq!(grown.theta[l.read_bias..l.read_bias + a], plain.theta[ol.read_bias..ol.read_bias + a]);
            assert!(grown.theta[l.read_bias + a..l.read_bias + a2].iter().all(|&v| v == least), "{name} +{fresh}: a fresh class bias at the least standing one");
            assert!(from[l.read_bias + a..l.read_bias + a2].iter().all(Option::is_none));
            assert_eq!(Constitution::from_text(&grown.to_text()).unwrap(), grown, "{name} +{fresh}: the text round-trips");
            // The face read through the encoding, at any lift: every standing logit as before, every fresh one the least bias.
            let mut next = mixer(0x1E77 + fresh as u64);
            for _ in 0..16 {
                let y: Vec<i64> = (0..dw).map(|_| (next() as i64) >> 40).collect();
                let (mut zp, mut zg) = (vec![0i64; a], vec![0i64; a2]);
                plain.tied(&y, &mut zp).unwrap();
                grown.tied(&y, &mut zg).unwrap();
                assert_eq!(zg[..a], zp[..], "{name} +{fresh}: the standing logits of a lift kept entry for entry");
                assert!(zg[a..].iter().all(|&z| z == i64::from(least)), "{name} +{fresh}: a fresh logit at the least bias");
            }
            // The whole forward on a region of standing classes. Where no head is paced no blank's clock reads a face, so each face's
            // standing logits are its logits before, entry for entry, and each fresh logit is the least bias. Where a head is paced, a blank
            // between arrivals runs at `κ = 1 + Σ_a p_a c[a]` over its own face, which a fresh class's share at the least bias moves; there the
            // faces move by the founding's price, read on a held passage before and after it (owed to #410).
            let after = grown.logits(&region()).unwrap();
            assert_eq!(before.len(), after.len());
            for (t, (b, g)) in before.iter().zip(&after).enumerate() {
                match (b, g) {
                    (None, None) => {}
                    (Some(b), Some(g)) if paced == 0 => {
                        assert_eq!(g[..a], b[..], "{name} +{fresh}: site {t}'s standing logits kept entry for entry");
                        assert!(g[a..].iter().all(|&z| z == i64::from(least)), "{name} +{fresh}: site {t}'s fresh logits at the least bias");
                        forward_kept += 1;
                    }
                    (Some(_), Some(g)) => assert_eq!(g.len(), a2),
                    _ => panic!("{name} +{fresh}: site {t} read before and not after, or after and not before"),
                }
            }
        }
    }
    assert!(forward_kept > 0, "a field with no paced head read the whole forward");
    let tower = towered(1);
    assert!(tower.lettered(1).is_err(), "a tower's levels take letters level by level");
    // The learner.
    let mut learner = Learner::new(shaped_with(four_contacts(1)), 6);
    learner.section(&[region()]).unwrap();
    learner.held = None;
    let mut octaves = [0u32; PARTS];
    (octaves[3], octaves[19]) = (2, 1);
    learner.rate_parts = Some(RateParts { contacts_before: 8, octaves });
    learner.own_rates = Some((0..learner.field.material_len()).map(|i| 3 + (i % 5) as u32).collect());
    learner.pass = Some(StorePass { role: "prefix".into(), store: "ab".repeat(32), stretches: 7, least: 4, octaves: 7, pairs: 15_606_223, sites: 41_490, own: false, slices: vec![PassSlice { name: "code".into(), piece: 2, cursor: 17, taken: 900 }], world: None, frontier: 0, before: false, strand: false, past: false, second: false, terrain: None, slice_tension: None, slice_clock: None });
    let same = learner.lettered(0).unwrap();
    assert_eq!(same.to_text(), learner.to_text(), "no fresh class leaves the learner's text byte for byte");
    let fresh = 2usize;
    let grown = learner.lettered(fresh).unwrap();
    let (_, from) = learner.field.lettered(fresh).unwrap();
    assert_eq!((grown.drawn, grown.rate_bits, grown.laps), (learner.drawn, learner.rate_bits, learner.laps), "no key is read");
    assert_eq!((grown.rate_parts, &grown.pass), (learner.rate_parts, &learner.pass));
    let own = grown.own_rates.as_ref().unwrap();
    for (k, &o) in from.iter().enumerate() {
        match o {
            Some(i) => {
                assert_eq!((grown.first[k], grown.second[k], own[k]), (learner.first[i], learner.second[i], learner.own_rates.as_ref().unwrap()[i]), "entry {k} keeps its moments and rate");
            }
            None => {
                assert_eq!((grown.first[k], own[k]), (0, learner.rate_bits), "a fresh entry's first moment at zero and its rate at rate_bits");
                let &(start, len, _) = grown.field.families_all().iter().find(|&&(s, l, _)| (s..s + l).contains(&k)).unwrap();
                let old: Vec<i128> = (start..start + len).filter_map(|j| from[j].map(|i| learner.second[i])).collect();
                let n = old.len() as i128;
                assert_eq!(grown.second[k], old.iter().map(|v| v / n).sum::<i128>() + old.iter().map(|v| v % n).sum::<i128>() / n, "a fresh entry's second moment at its family's standing mean");
            }
        }
    }
    assert_eq!(Learner::from_text(&grown.to_text()).unwrap(), grown);
    let mut holding = learner.clone();
    holding.held = Some(HeldStep { step: vec![0; learner.field.material_len()], halvings: 0 });
    assert!(holding.lettered(1).is_err(), "refused while a step is held");
}

/// [definition; theory, November 12 (the record of the opening's room, §4 item 5)] **The pass's place is the learner's last line, written only
/// where present**: a learner with no pass writes no pass line and reads back as it was; with one, its text is the text without it and the pass
/// line after, and it reads back with it; a malformed pass line is refused.
#[test]
fn the_pass_line_is_the_learners_last_line_and_only_where_present() {
    let mut learner = Learner::new(shaped_with(four_contacts(1)), 6);
    learner.section(&[region()]).unwrap();
    learner.held = None;
    let plain = learner.to_text();
    assert!(!plain.lines().any(|l| l.starts_with("pass ")));
    assert_eq!(Learner::from_text(&plain).unwrap().to_text(), plain, "a learner with no pass reads and writes byte for byte");
    let pass = StorePass {
        role: "prefix".into(),
        store: "0123456789abcdef".repeat(4),
        stretches: 1234,
        least: 4,
        octaves: 7,
        pairs: 15_606_223,
        sites: 41_490,
        own: false,
        slices: ["code", "web", "science", "books", "wikidata"].iter().enumerate().map(|(k, n)| PassSlice { name: n.to_string(), piece: k as u64, cursor: 3 * k as u64, taken: 100 * k as u64 }).collect(),
        world: None,
        frontier: 0,
        before: false,
        strand: false,
        past: false,
        second: false,
        terrain: None,
        slice_tension: None,
        slice_clock: None,
    };
    learner.pass = Some(pass.clone());
    let text = learner.to_text();
    assert_eq!(text, format!("{plain}{}\n", pass.to_line()), "the pass line follows every other line");
    // [the lead, November 21] A terrain's line follows the pass line only where set, reads back as itself, and its share is its tension's.
    let held = StorePass { terrain: Some(PassTerrain { records: 4, met: 99, tension_world: 3_000_000, tension_passage: 1_000_000, suffix: false, strand: false }), ..pass.clone() };
    learner.pass = Some(held.clone());
    let with_terrain = learner.to_text();
    assert_eq!(with_terrain, format!("{plain}{}\nterrain 4 99 3000000 1000000\n", pass.to_line()));
    assert_eq!(Learner::from_text(&with_terrain).unwrap().pass, Some(held.clone()));
    let t = held.terrain.clone().unwrap();
    assert_eq!((t.share(41_490), PassTerrain { tension_world: 0, tension_passage: 0, ..t.clone() }.share(41_490)), (31_117, 20_745));
    assert!(PassTerrain::from_line("terrain 0 1 2 3").is_err() && PassTerrain::from_line("terrain 4 1 2").is_err());
    let suffix = PassTerrain { suffix: true, ..t.clone() };
    assert_eq!(suffix.to_line(), "terrain 4 99 3000000 1000000 suffix");
    assert_eq!(PassTerrain::from_line(&suffix.to_line()).unwrap(), suffix);
    assert!(PassTerrain::from_line("terrain 4 99 1 2 prefix").is_err());
    let strand = PassTerrain { strand: true, ..t.clone() };
    assert_eq!(strand.to_line(), "terrain 4 99 3000000 1000000 strand");
    assert_eq!(PassTerrain::from_line(&strand.to_line()).unwrap(), strand);
    learner.pass = Some(pass.clone());
    let back = Learner::from_text(&text).unwrap();
    assert_eq!((back.pass.as_ref(), back.to_text()), (Some(&pass), text.clone()));
    assert_eq!(StorePass::from_line(&pass.to_line()).unwrap(), pass);
    for bad in ["pass prefix", "pass prefix nothex 1 4 7 1 1", "pass prefix 0123 1 4 7 1 1 code 1 2"] {
        assert!(StorePass::from_line(bad).is_err(), "{bad}");
    }
    let short = format!("{plain}pass prefix {} 1 4 7 1 1 code 1 2\n", "ab".repeat(32));
    assert!(Learner::from_text(&short).is_err(), "a slice of three words is refused");
    // [the record of the states a field trains on, §5 item 1] The word `own` stands ninth only where set: the line without it is the line as
    // before, with it the slices follow it, and either reads back as itself.
    let own = StorePass { own: true, ..pass.clone() };
    assert_eq!(own.to_line(), pass.to_line().replacen(" 41490 ", " 41490 own ", 1));
    assert_eq!(StorePass::from_line(&own.to_line()).unwrap(), own);
    assert!(!pass.to_line().contains(" own"));
    let named_own = StorePass { slices: vec![PassSlice { name: "own".into(), piece: 1, cursor: 2, taken: 3 }], ..pass.clone() };
    assert_eq!(StorePass::from_line(&named_own.to_line()).unwrap(), named_own, "a slice named `own` is a slice");
    let both = StorePass { own: true, ..named_own };
    assert_eq!(StorePass::from_line(&both.to_line()).unwrap(), both);
    // [the theory thread's Build B, November 16] A world's clause stands last only where set; with `own` or without, it reads back as itself,
    // and a world on a slice the pass lacks, a zero count, or a slice named `world` is refused.
    let world = StorePass { world: Some(PassWorld { slice: "books".into(), every: 8, records: 3, run: 48, refine: 0 }), ..pass.clone() };
    let refined = StorePass { world: Some(PassWorld { refine: 1, ..world.world.clone().unwrap() }), ..pass.clone() };
    assert_eq!(refined.to_line(), format!("{} world books 8 3 48 1", pass.to_line()));
    assert_eq!(StorePass::from_line(&refined.to_line()).unwrap(), refined);
    assert!(StorePass::from_line(&format!("{} world books 8 3 48 0", pass.to_line())).is_err(), "a refine word of zero is no clause");
    assert_eq!(world.to_line(), format!("{} world books 8 3 48", pass.to_line()));
    assert_eq!(StorePass::from_line(&world.to_line()).unwrap(), world);
    let world_own = StorePass { own: true, ..world.clone() };
    assert_eq!(StorePass::from_line(&world_own.to_line()).unwrap(), world_own);
    assert!(!pass.to_line().contains(" world"));
    for bad in [format!("{} world arithmetic 8 3 48", pass.to_line()), format!("{} world books 0 3 48", pass.to_line()), format!("{} world books 8 3 0", pass.to_line())] {
        assert!(StorePass::from_line(&bad).is_err(), "{bad}");
    }
    let named_world = StorePass { slices: vec![PassSlice { name: "world".into(), piece: 1, cursor: 2, taken: 3 }], ..pass.clone() };
    assert!(StorePass::from_line(&named_world.to_line()).is_err(), "a slice named `world` is refused");
    // [the lead, November 18] The frontier's clause stands as the line's last two words only where set; with `own`, with a world or
    // without, it reads back as itself; a share of zero or past eight, or a slice named `frontier`, is refused.
    let frontier = StorePass { frontier: 6, ..pass.clone() };
    assert_eq!(frontier.to_line(), format!("{} frontier 6", pass.to_line()));
    assert!(!pass.to_line().contains(" frontier"));
    for p in [frontier.clone(), StorePass { own: true, ..frontier.clone() }, StorePass { frontier: 8, ..world.clone() }, StorePass { frontier: 1, ..refined.clone() }, StorePass { frontier: 3, ..world_own.clone() }] {
        assert_eq!(StorePass::from_line(&p.to_line()).unwrap(), p, "{}", p.to_line());
    }
    for bad in [format!("{} frontier 0", pass.to_line()), format!("{} frontier 9", pass.to_line()), format!("{} frontier x", pass.to_line())] {
        assert!(StorePass::from_line(&bad).is_err(), "{bad}");
    }
    let named_frontier = StorePass { slices: vec![PassSlice { name: "frontier".into(), piece: 1, cursor: 2, taken: 3 }], ..pass.clone() };
    assert!(StorePass::from_line(&named_frontier.to_line()).is_err(), "a slice named `frontier` is refused");
    learner.pass = Some(frontier.clone());
    let with = learner.to_text();
    assert_eq!(with, format!("{plain}{}\n", frontier.to_line()));
    assert_eq!(Learner::from_text(&with).unwrap().to_text(), with, "a learner whose pass has a frontier reads and writes byte for byte");
    // [the lead, November 18] The known streams' word stands after the frontier's share, only where set; it reads back as itself with
    // `own` and with a world; without a frontier's clause before it, or as a slice's name, it is refused.
    let known = StorePass { before: true, ..frontier.clone() };
    assert_eq!(known.to_line(), format!("{} frontier 6 before", pass.to_line()));
    assert!(!frontier.to_line().contains(" before"));
    for p in [known.clone(), StorePass { own: true, ..known.clone() }, StorePass { frontier: 8, before: true, ..world.clone() }, StorePass { frontier: 1, before: true, ..refined.clone() }] {
        assert_eq!(StorePass::from_line(&p.to_line()).unwrap(), p, "{}", p.to_line());
    }
    assert!(StorePass::from_line(&format!("{} before", pass.to_line())).is_err(), "the word without a frontier's clause");
    let named_before = StorePass { slices: vec![PassSlice { name: "before".into(), piece: 1, cursor: 2, taken: 3 }], ..pass.clone() };
    assert!(StorePass::from_line(&named_before.to_line()).is_err(), "a slice named `before` is refused");
    learner.pass = Some(known.clone());
    let with = learner.to_text();
    assert_eq!(Learner::from_text(&with).unwrap().to_text(), with, "a learner whose frontier is read as known streams reads and writes byte for byte");
    // [the lead, November 18] The two streams' word stands in the same place, `frontier E strand`, and reads back as itself.
    let strand = StorePass { strand: true, ..frontier.clone() };
    assert_eq!(strand.to_line(), format!("{} frontier 6 strand", pass.to_line()));
    for p in [strand.clone(), StorePass { own: true, ..strand.clone() }, StorePass { frontier: 8, strand: true, ..world.clone() }] {
        assert_eq!(StorePass::from_line(&p.to_line()).unwrap(), p, "{}", p.to_line());
    }
    assert!(StorePass::from_line(&format!("{} strand", pass.to_line())).is_err(), "the word without a frontier's clause");
    let named_strand = StorePass { slices: vec![PassSlice { name: "strand".into(), piece: 1, cursor: 2, taken: 3 }], ..pass.clone() };
    assert!(StorePass::from_line(&named_strand.to_line()).is_err(), "a slice named `strand` is refused");
    // The word `past` stands last, after either one-sided reading, and alone it is refused.
    let faced = StorePass { past: true, ..strand.clone() };
    assert_eq!(faced.to_line(), format!("{} frontier 6 strand past", pass.to_line()));
    for p in [faced.clone(), StorePass { past: true, ..known.clone() }, StorePass { own: true, ..faced.clone() }] {
        assert_eq!(StorePass::from_line(&p.to_line()).unwrap(), p, "{}", p.to_line());
    }
    assert!(StorePass::from_line(&format!("{} frontier 6 past", pass.to_line())).is_err(), "the word after no one-sided reading");
    learner.pass = Some(faced);
    let with = learner.to_text();
    assert_eq!(Learner::from_text(&with).unwrap().to_text(), with, "a learner whose frontier is read by two streams reads and writes byte for byte");
}

/// [definition; the lead, November 17 and 18, the boundary chart (the record of the dwell §13, acceptance (b))] **A passage read at its
/// boundary reads nothing at or past a place**: under [`Constitution::chart_faces`] a place's face is the same bits when any symbol at it or
/// after it is changed, on fields with a still head and without, with circles scanned from both ends and paces off their rest; and a
/// changed symbol is read by places after it.
#[test]
fn the_boundary_charts_face_reads_nothing_at_or_past_its_place() {
    for (name, field) in [("circles, one still head", circled_shaped(1)), ("circles, turned heads", circled_shaped(0)), ("plain contacts", shaped(1))] {
        let a = field.declaration.alphabet;
        let sites = 14;
        let base = drawn_classes(0xB0, sites, a);
        let faces = field.chart_faces(&base).unwrap();
        assert_eq!(faces.len(), sites);
        let mut read_after = 0;
        for p in 0..sites {
            let mut other = base.clone();
            other[p] = (other[p] + 1 + p % (a - 1)) % a;
            let changed = field.chart_faces(&other).unwrap();
            for t in 0..=p {
                assert_eq!(changed[t], faces[t], "{name}: place {t} read the symbol at place {p}");
            }
            read_after += usize::from((p + 1..sites).any(|t| changed[t] != faces[t]));
        }
        assert!(read_after >= sites - 2, "{name}: a changed symbol is read after it ({read_after} of {} places)", sites - 1);
    }
}

/// [definition; the lead, November 23, play] **A strand compared with its targets** ([`Region::targets`]): its faces are the known
/// stream's own (the targets move no face), its covector in a section is the strand's return against the targets, targets equal to the
/// known stream give the covector of none, and other targets move it; targets on a region not read by two streams, or not one a site,
/// are refused.
#[test]
fn a_strand_compared_with_its_targets_reads_its_known_stream_and_returns_against_its_targets() {
    let field = circled_shaped(1);
    let a = field.declaration.alphabet;
    let sites = 9;
    let classes = drawn_classes(0xB4, sites, a);
    let targets = drawn_classes(0x5D, sites, a);
    let known = vec![false; sites];
    let strand = |with: Option<&[usize]>| -> (Vec<Vec<Option<TowerFace>>>, Vec<i128>) {
        let r = Region { classes: &classes, unresolved: &known, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: true, past: false, second: false, targets: with };
        field.read_and_return(&[r]).unwrap()
    };
    let (plain_faces, plain_g) = strand(None);
    let (aimed_faces, aimed_g) = strand(Some(&targets));
    let (_, itself_g) = strand(Some(&classes));
    assert_eq!(plain_faces, aimed_faces, "the targets move no face");
    assert_eq!(itself_g, plain_g, "targets equal to the known stream are none");
    assert_ne!(aimed_g, plain_g, "other targets move the comparison");
    let pass = field.strand_pass(&classes, true, false).unwrap();
    let mut g = vec![0i128; field.theta.len()];
    field.strand_returned(&classes, &targets, &pass, &mut g).unwrap();
    assert_eq!(aimed_g, g, "a strand region's covector in a section is the strand's return against its targets");
    let short = &targets[..sites - 1];
    let r = Region { classes: &classes, unresolved: &known, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: true, past: false, second: false, targets: Some(short) };
    assert!(field.read_and_return(&[r]).is_err(), "targets not one a site are refused");
    let r = Region { classes: &classes, unresolved: &known, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: Some(&targets) };
    assert!(field.read_and_return(&[r]).is_err(), "targets on a region not read by two streams are refused");
}

/// [definition; the lead, November 24] **The level's own lane** ([`Scale::lane`], [`Learner::level_laned`]): the founded learner's text
/// keeps the word; every entry the lane holds is zero and the lane's rows of the prolongation are drawn; in a passage read by two streams
/// the prolongation writes the lane alone (the state before the split and after it differ only in the lane's coordinates); and sections
/// leave every held entry at zero while the lane's readers open and then the lane's rows of the prolongation move.
#[test]
fn the_levels_own_lane_is_written_by_the_prolongation_alone_and_a_section_keeps_it_so() {
    for (still, past) in [(1usize, false), (2, true)] {
        let field = towered_before_live(still);
        let stream = keys(1 << 18);
        let learner = Learner::new(field, 12);
        let laned = learner.level_laned(&stream).unwrap();
        let f = &laned.field;
        assert!(f.scale.as_deref().unwrap().lane, "still {still}: the level owns its lane");
        assert_eq!(Constitution::from_text(&f.to_text()).unwrap(), *f, "still {still}: the text keeps the lane");
        let held = f.level_lane_held().unwrap().unwrap();
        let material: Vec<i32> = f.material().copied().collect();
        assert!(held.iter().all(|&i| material[i] == 0), "still {still}: every held entry founded at zero");
        let (dw, w) = (f.declaration.width, f.declaration.lane_width());
        let sc = f.scale.as_deref().unwrap();
        let (b2, _, _) = sc.before_offsets(dw).unwrap();
        let glue = f.theta.len() + sc.coarse.theta.len();
        let d1 = sc.coarse.declaration.width;
        let lane_rows: Vec<i32> = (dw - w..dw).flat_map(|c| (0..d1).map(move |j| (c, j))).map(|(c, j)| material[glue + b2 + c * d1 + j]).collect();
        assert!(lane_rows.iter().any(|&v| v != 0), "still {still}: the lane's rows of the prolongation are drawn");
        // The prolongation writes the lane alone: the state the split's tick reads differs from the tick before's only in the lane.
        let a = f.declaration.alphabet;
        let classes = drawn_classes(0xC7, 13, a);
        let pass = f.strand_pass(&classes, true, past).unwrap();
        let split = sc.split;
        let (before, at) = (&pass.ticks[split - 1].after, &pass.ticks[split].before);
        let mut moved_in_lane = false;
        for (t, (xb, xa)) in before.chunks_exact(dw).zip(at.chunks_exact(dw)).enumerate() {
            for c in 0..dw {
                if c < dw - w {
                    assert_eq!(xb[c], xa[c], "still {still}: site {t} coordinate {c} outside the lane is written by the level");
                } else {
                    moved_in_lane |= xb[c] != xa[c];
                }
            }
        }
        assert!(moved_in_lane, "still {still}: the level writes its lane");
        // A section keeps the held entries at zero and moves the lane's rows.
        let mut trained = laned.clone();
        let known = vec![false; classes.len()];
        let region = Region { classes: &classes, unresolved: &known, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: true, past, second: false, targets: None };
        trained.section(&[region]).unwrap();
        let after: Vec<i32> = trained.field.material().copied().collect();
        assert!(held.iter().all(|&i| after[i] == 0), "still {still}: a section keeps every held entry at zero");
        // The lane's readers open first (their columns at zero read a drawn lane), and the prolongation's rows once they read it.
        let read = f.layout.read;
        let opened = (0..dw).flat_map(|o| (dw - w..dw).map(move |i| read + o * dw + i)).filter(|&i| after[i] != material[i]).count();
        assert!(opened > 0, "still {still}: the readout's columns of the lane open in a section");
        let lane_block = |m: &[i32]| -> Vec<i32> { (dw - w..dw).flat_map(|c| (0..d1).map(move |j| glue + b2 + c * d1 + j)).map(|i| m[i]).collect() };
        let mut again = trained.clone();
        for _ in 0..3 {
            again.section(&[region]).unwrap();
        }
        let later: Vec<i32> = again.field.material().copied().collect();
        assert!(held.iter().all(|&i| later[i] == 0), "still {still}: sections keep every held entry at zero");
        assert_ne!(lane_block(&later), lane_block(&material), "still {still}: the lane's rows of the prolongation move once the lane is read");
    }
}

/// [definition; the lead, November 23, an act answered in kind] **A place read and not compared** ([`UNCOMPARED`]): its faces are
/// the strand's own, a strand whose every target is uncompared returns nothing and counts in no code, the section's scored pairs and
/// spans leave the uncompared places out, and a place's being left out moves the covector where a comparison at it would; a target
/// outside the alphabet is refused.
#[test]
fn a_strand_place_read_and_not_compared_takes_no_covector_and_counts_in_no_code() {
    // (a field that compares its opening, so the opening's comparison leaves the places out too)
    let plain = Constitution::found(four_contacts(1), &keys(1 << 14)).unwrap();
    let (grown, _) = plain.with_carry(2, &keys(plain.declaration.carry_draws(2))).unwrap();
    let field = drawn(grown.with_opening().unwrap().0);
    assert!(field.declaration.opening);
    let a = field.declaration.alphabet;
    let sites = 9;
    let classes = drawn_classes(0xB4, sites, a);
    let known = vec![false; sites];
    let none = vec![UNCOMPARED; sites];
    let some: Vec<usize> = classes.iter().enumerate().map(|(t, &c)| if t % 3 == 1 { UNCOMPARED } else { c }).collect();
    fn strand<'a>(classes: &'a [usize], known: &'a [bool], with: Option<&'a [usize]>) -> Region<'a> {
        Region { classes, unresolved: known, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: true, past: false, second: false, targets: with }
    }
    let (plain_faces, plain_g) = field.read_and_return(&[strand(&classes, &known, None)]).unwrap();
    let (none_faces, none_g) = field.read_and_return(&[strand(&classes, &known, Some(&none))]).unwrap();
    let (some_faces, some_g) = field.read_and_return(&[strand(&classes, &known, Some(&some))]).unwrap();
    assert_eq!(plain_faces, none_faces, "an uncompared place moves no face");
    assert_eq!(plain_faces, some_faces, "uncompared places move no face");
    assert!(none_g.iter().all(|&v| v == 0), "a strand with every place uncompared returns nothing");
    assert_ne!(some_g, plain_g, "leaving places out moves the comparison");
    assert!(some_g.iter().any(|&v| v != 0), "the compared places still return");
    let regions = [strand(&classes, &known, Some(&some))];
    let compared_some = crate::learner::compared(&plain_faces, &regions).unwrap();
    let compared_plain = crate::learner::compared(&plain_faces, &[strand(&classes, &known, None)]).unwrap();
    let left_out = (1..sites).filter(|t| t % 3 == 1).count();
    assert_eq!(compared_plain.pairs.len() - compared_some.pairs.len(), left_out, "the uncompared places count in no code");
    assert_eq!(crate::learner::spans_of(&regions)[0].0, sites - 1 - left_out, "a strand's span is its compared places");
    let at_class = faces_at_class(&plain_faces, &regions);
    assert_eq!(crate::learner::compared_at_class(&at_class, &regions).unwrap().pairs, compared_some.pairs, "the faces read at their targets give the same pairs");
    let none_codes = field.opening_codes(&strand(&classes, &known, Some(&none))).unwrap();
    assert!(none_codes.iter().all(Option::is_none), "an uncompared place has no opening code");
    let some_codes = field.opening_codes(&strand(&classes, &known, Some(&some))).unwrap();
    assert_eq!(some_codes.iter().flatten().count(), (0..sites).filter(|t| t % 3 != 1).count(), "the opening is coded at the compared places alone");
    let wide = vec![a; sites];
    assert!(field.read_and_return(&[strand(&classes, &known, Some(&wide))]).is_err(), "a target outside the alphabet is refused");
}

/// [definition; the lead, November 18, the frontier record §6] **The strand's covector matches its code's difference, and the sum of its
/// frontier regions' covectors.** The code is the passage's in place order, `Σ_(t≥1) −log₂ p̂_t(u_t)` over the open places of
/// [`Constitution::strand_pass`]; [`Constitution::strand_returned`] is its reverse. Family by family at its largest entries the covector
/// matches the code's difference (a probe that moves a site across a sheet is counted apart, as in
/// [`covector_matches_the_codes_difference`]); and it stands beside the sum, over the passage's places, of the covectors of the regions
/// that end there read with every known place hearing only what stands before it (a ruler's forward at `3`): the same law returned a
/// region a place, whose releases fall elsewhere, so the two agree to a part in a thousand of the reference's size, family by family
/// (read November 18: 18 millionths at the farthest family).
#[test]
fn the_strands_covector_matches_the_codes_difference() {
    // (read with the strand's odd contacts at rest, and with them facing the past: [`Region::past`])
    for past in [false, true] {
    // The strand's code: each open place's, and where the field compares its opening the retarded opening's at every place.
    let code = |field: &Constitution, classes: &[usize]| -> i64 {
        let places: i64 = field.strand_pass(classes, false, past).unwrap().faces.iter().zip(classes).skip(1).map(|(f, &c)| crate::field::ratio_code(f.masses[c], f.total)).sum();
        let known = vec![false; classes.len()];
        let opening = if field.declaration.opening { opening_code(field, &Region { classes, unresolved: &known, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: true, strand: false, past, second: false, targets: None }) } else { 0 };
        places + opening
    };
    let sheets = |field: &Constitution, classes: &[usize]| -> Vec<Vec<u32>> { field.strand_pass(classes, true, past).unwrap().ticks.iter().flat_map(|c| c.classes.iter().map(|l| l.off.iter().chain(&l.members).copied().chain(l.probes.iter().flat_map(|p| std::iter::once(u32::MAX).chain(p.iter().copied()))).collect())).collect() };
    let (mut read, mut seams) = (0usize, 0usize);
    let mut worst = 0u128;
    for (name, field) in [("circles, one still head", circled_shaped(1)), ("circles, turned heads", circled_shaped(0)), ("plain contacts", shaped(1)), ("the opening compared", opened(1))] {
        let a = field.declaration.alphabet;
        let sites = 9;
        let classes = drawn_classes(0xB4, sites, a);
        let pass = field.strand_pass(&classes, true, past).unwrap();
        let mut g = vec![0i128; field.theta.len()];
        field.strand_returned(&classes, &classes, &pass, &mut g).unwrap();
        // The region's own word reads the same forward and returns the same covector (a section's mean leaves one region's whole), its
        // faces the open places' and none at the first place, its code the open places' sum.
        {
            let known = vec![false; sites];
            let region = Region { classes: &classes, unresolved: &known, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: true, past, second: false, targets: None };
            let (faces, section) = field.read_and_return(&[region]).unwrap();
            assert!(faces[0][0].is_none() && faces[0][1..].iter().zip(&pass.faces[1..]).all(|(a, b)| a.as_ref() == Some(b)), "{name}: a strand region's faces are the open places'");
            assert_eq!(section, g, "{name}: a strand region's covector in a section is the strand's return");
            let (c, count) = field.code(&region).unwrap();
            assert_eq!((c, count), (pass.faces.iter().zip(&classes).skip(1).map(|(f, &u)| crate::field::ratio_code(f.masses[u], f.total)).sum::<i64>(), sites - 1), "{name}: its code is its open places'");
            let open: Vec<bool> = (0..sites).map(|t| t == 3).collect();
            assert!(field.pass(&Region { unresolved: &open, ..region }, false).is_err(), "{name}: a strand whose site is open is refused");
        }
        // The reference: a region a place, each returned under the known stream with its open place on the bare clock, as the strand's are.
        let mut ruled = field.clone();
        ruled.ruler_far = if past { 9 } else { 3 };
        ruled.bare_stretch = true;
        let mut reference = vec![0i128; field.theta.len()];
        for t in 1..sites {
            let open: Vec<bool> = (0..=t).map(|k| k == t).collect();
            let region = Region { classes: &classes[..=t], unresolved: &open, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None };
            let fwd = ruled.pass(&region, true).unwrap();
            ruled.returned(&region, &fwd, &mut reference).unwrap();
        }
        // (a region a place compares its own opening at every place where the field compares one, so the sum is the reference only where it does not)
        for &(start, len, _) in field.families().iter().filter(|_| !field.declaration.opening) {
            let (size, apart): (u128, u128) = (start..start + len).fold((0, 0), |(s, d), i| (s + reference[i].unsigned_abs(), d + (g[i] - reference[i]).unsigned_abs()));
            assert!(1000 * apart <= size + 1000 * 64 * len as u128, "{name}: family at {start}: the strand's covector stands {apart} from the regions' sum of size {size}");
            if size > 0 {
                worst = worst.max(apart * 1_000_000 / size);
            }
        }
        for &(start, len, grain) in field.families() {
            let natural: u32 = if grain == MATERIAL_BITS { 40 } else { 24 };
            let mut entries: Vec<usize> = (start..start + len).collect();
            entries.sort_by_key(|&i| std::cmp::Reverse(g[i].unsigned_abs()));
            for i in entries.into_iter().take(3).filter(|&i| g[i] != 0) {
                let straddles = |delta: i32| {
                    let (mut plus, mut minus) = (field.clone(), field.clone());
                    plus.theta[i] += delta;
                    minus.theta[i] -= delta;
                    sheets(&plus, &classes) != sheets(&field, &classes) || sheets(&minus, &classes) != sheets(&field, &classes)
                };
                let shift = natural + grain - 20;
                let Some((delta, h)) = probe_step(grain, &|delta: i32| (g[i] * 2 * delta as i128) >> shift, &straddles) else {
                    seams += 1;
                    continue;
                };
                read += 1;
                let l = field.layout.clone();
                let measured = if start == l.temper {
                    let at = |k: i32| { let mut f = field.clone(); f.theta[i] += k * (delta / 8); code(&f, &classes) as i128 };
                    let weighted: i128 = (-8..=8).map(|k| k as i128 * at(k)).sum();
                    div_nearest(16 * weighted, 408) as i64
                } else {
                    let (mut plus, mut minus) = (field.clone(), field.clone());
                    plus.theta[i] += delta;
                    minus.theta[i] -= delta;
                    code(&plus, &classes) - code(&minus, &classes)
                };
                let predicted = (g[i] * 2 * delta as i128) >> shift;
                let tolerance = predicted.abs() / 8 + ((64 * (sites as i128 - 1)) << h);
                assert!((measured as i128 - predicted).abs() <= tolerance, "{name}: family at {start} (grain {grain}) entry {i} at {h} halvings: measured {measured}, predicted {predicted}");
            }
        }
    }
    eprintln!("STRAND_COVECTOR_PROBES past={past} read={read} on_a_seam={seams} farthest_family_from_the_regions_sum_millionths={worst}");
    assert!(read >= 60 && 8 * seams <= read, "read {read} probes, {seams} on a seam");
    }
}

/// [`towered_live`] opened to one-sided streams ([`Constitution::level_before`]) with the block's every entry drawn, so a strand's level
/// carries a covector on every path.
fn towered_before_live(still: usize) -> Constitution {
    let founded = towered_far_live(still);
    let from = founded.material_len();
    let mut field = founded.level_before().unwrap();
    draw_from(&mut field, from);
    field
}

/// [`towered_live`] with a level's field that reaches as many epochs as a strand of the fixtures has places (a one-sided stream
/// names a site wherever no earlier place within a section carries news as large, so a passage's epochs can be its places).
fn towered_far_live(still: usize) -> Constitution {
    let fine = opened(still);
    let offset = 4 * fine.declaration.founding_draws();
    let mut field = fine.scaled_up(6, 1, Declaration { reach: 16, ..coarse_declaration() }, &keys(1 << 16), offset).unwrap().0;
    let base = field.theta.len();
    draw_from(&mut field, base);
    field
}

/// Every material entry from `from` on drawn from the fixtures' keys at its family's grain.
fn draw_from(field: &mut Constitution, from: usize) {
    let stream = keys(1 << 17);
    let families = field.families_all();
    for (n, v) in field.material_mut().enumerate().skip(from) {
        let word = &stream[4 * n..4 * n + 4];
        let k = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) as i64;
        let grain = families.iter().find(|(s, l, _)| (*s..*s + *l).contains(&n)).unwrap().2;
        *v = ((k << grain) >> 32) as i32;
    }
}

/// [definition; the lead, November 18, the record of the two streams §11] **The level as a passage read by two streams hears it**
/// ([`Constitution::scale_forward_before`]). At its founding ([`Constitution::level_before`]) every face of a strand is the face the
/// tower's strand read without the block, the families tile the material and the text restores it. With the block drawn: the level
/// moves some face; a place's face is the same bits in the passage cut after it (nothing at or after a place is read through the
/// level either); the law's own prolongation takes no covector from a strand; and the covector of every family the level reaches
/// (the level's field's, the restriction's, the block's, and the fine field's) matches the code's central difference.
#[test]
fn the_level_a_strand_hears_is_the_epoch_before_and_its_covector_matches_the_codes_difference() {
    let code = |field: &Constitution, classes: &[usize], past: bool| -> i64 {
        let places: i64 = field.strand_pass(classes, false, past).unwrap().faces.iter().zip(classes).skip(1).map(|(f, &c)| crate::field::ratio_code(f.masses[c], f.total)).sum();
        let known = vec![false; classes.len()];
        places + opening_code(field, &Region { classes, unresolved: &known, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: true, strand: false, past, second: false, targets: None })
    };
    let sheets = |field: &Constitution, classes: &[usize], past: bool| -> Vec<Vec<u32>> {
        let pass = field.strand_pass(classes, true, past).unwrap();
        let coarse = pass.tower.iter().flat_map(|t| t.ticks().iter());
        let mut out: Vec<Vec<u32>> = pass.ticks.iter().chain(coarse).flat_map(|c| c.classes.iter().map(|l| l.off.iter().chain(&l.members).copied().chain(l.probes.iter().flat_map(|p| std::iter::once(u32::MAX).chain(p.iter().copied()))).collect())).collect();
        // (the cut is data: a probe that moves an anchor is a seam too)
        out.push(pass.tower.iter().flat_map(|t| t.cut().anchors.iter().map(|&a| a as u32)).collect());
        out
    };
    // The news phases a strand's level read: data by the level's law (nothing returns to the news), so a probe that moves one reads a
    // difference the covector does not hold, and is left out and counted.
    let phases = |field: &Constitution, classes: &[usize], past: bool| -> Vec<i64> {
        let pass = field.strand_pass(classes, true, past).unwrap();
        pass.tower.iter().flat_map(|t| t.cut().harmonics.iter().chain(t.open_harmonics()).copied()).collect()
    };
    let (mut read, mut seams, mut news_moved, mut fine_read, mut epochs_read) = (0usize, 0usize, 0usize, 0usize, 0usize);
    for (still, past) in [(0usize, false), (1, false), (1, true), (2, true)] {
        let founded = towered_far_live(still);
        let a = founded.declaration.alphabet;
        let sites = 13;
        let classes = drawn_classes(0xD5, sites, a);
        // The founding keeps every face, tiles the material and is restored by its text.
        let opened = founded.level_before().unwrap();
        assert!(opened.level_before().is_err(), "a level opened twice is refused");
        assert_eq!(opened.strand_pass(&classes, false, past).unwrap().faces, founded.strand_pass(&classes, false, past).unwrap().faces, "still {still}: the founding keeps every face of a strand");
        assert_eq!(opened.faces(&region()).unwrap(), founded.faces(&region()).unwrap(), "still {still}: and every face of the law");
        let mut at = 0;
        for (start, len, _) in opened.families_all() {
            assert_eq!(start, at);
            at += len;
        }
        assert_eq!(at, opened.material_len());
        assert_eq!(Constitution::from_text(&opened.to_text()).unwrap(), opened);
        // The live block.
        let field = towered_before_live(still);
        let pass = field.strand_pass(&classes, true, past).unwrap();
        let tower = pass.tower.as_ref().expect("a strand of a tower with the block hears its level");
        let epochs = tower.cut().anchors.len();
        assert!(epochs >= 3, "still {still}: the passage holds {epochs} epochs");
        epochs_read += epochs;
        assert_ne!(pass.faces, opened.strand_pass(&classes, false, past).unwrap().faces, "still {still}: the level moves some face");
        for t in 1..sites {
            let cut = field.strand_pass(&classes[..=t], false, past).unwrap().faces;
            assert_eq!(cut[t], pass.faces[t], "still {still}, past {past}: place {t} reads the passage cut after it as it reads the whole");
        }
        let mut g = vec![0i128; field.material_len()];
        field.strand_returned(&classes, &classes, &pass, &mut g).unwrap();
        // The region's own word reads the same forward and returns the same covector.
        {
            let known = vec![false; sites];
            let region = Region { classes: &classes, unresolved: &known, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: true, past, second: false, targets: None };
            let (faces, section) = field.read_and_return(&[region]).unwrap();
            assert!(faces[0][0].is_none() && faces[0][1..].iter().zip(&pass.faces[1..]).all(|(a, b)| a.as_ref() == Some(b)), "still {still}: a strand region's faces are the open places'");
            assert_eq!(section, g, "still {still}: a strand region's covector in a section is the strand's return");
        }
        // The law's own prolongation is no operand of a strand.
        let base = field.theta.len();
        let sc = field.scale.as_deref().unwrap();
        let glue_at = base + sc.coarse.theta.len();
        let (_, _, b, _, len) = sc.glue_offsets(field.declaration.width);
        assert!(g[glue_at + b..glue_at + len].iter().all(|&v| v == 0), "still {still}: the law's prolongation takes nothing from a strand");
        let (b2, _, end) = sc.before_offsets(field.declaration.width).unwrap();
        assert!(g[glue_at + b2..glue_at + end].iter().any(|&v| v != 0), "still {still}: the block takes a covector");
        for (start, len, grain) in field.families_all() {
            let natural: u32 = if grain == MATERIAL_BITS { 40 } else { 24 };
            let mut entries: Vec<usize> = (start..start + len).collect();
            entries.sort_by_key(|&i| std::cmp::Reverse(g[i].unsigned_abs()));
            // (the fine field's families are probed once an entry, the level's and the glue's three)
            for i in entries.into_iter().take(if start >= base { 3 } else { 1 }).filter(|&i| g[i] != 0) {
                let moved = |delta: i32| {
                    let mut f = field.clone();
                    *f.material_mut().nth(i).unwrap() += delta;
                    f
                };
                // (the lock's temperature is read through a smoother difference in the strand's own test; it is left to that test here)
                if start == field.layout.temper {
                    continue;
                }
                if start < base && phases(&moved(1 << grain.saturating_sub(8)), &classes, past) != phases(&field, &classes, past) {
                    news_moved += 1;
                    continue;
                }
                let straddles = |delta: i32| sheets(&moved(delta), &classes, past) != sheets(&field, &classes, past) || sheets(&moved(-delta), &classes, past) != sheets(&field, &classes, past);
                let shift = natural + grain - 20;
                let Some((delta, h)) = probe_step(grain, &|delta: i32| (g[i] * 2 * delta as i128) >> shift, &straddles) else {
                    seams += 1;
                    continue;
                };
                read += 1;
                fine_read += usize::from(start < base);
                let measured = code(&moved(delta), &classes, past) - code(&moved(-delta), &classes, past);
                let predicted = (g[i] * 2 * delta as i128) >> shift;
                let tolerance = predicted.abs() / 8 + ((64 * (sites as i128 - 1)) << h);
                assert!((measured as i128 - predicted).abs() <= tolerance, "still {still}, past {past}: family at {start} (grain {grain}) entry {i} at {h} halvings: measured {measured}, predicted {predicted}");
            }
        }
    }
    eprintln!("STRAND_LEVEL_COVECTOR_PROBES read={read} of_the_fine_field={fine_read} on_a_seam={seams} moved_the_news={news_moved} epochs={epochs_read}");
    assert!(read >= 60 && fine_read >= 12 && 4 * seams <= read, "read {read} probes ({fine_read} of the fine field), {seams} on a seam");
}

/// [definition; the lead, November 23] **The level's receipt at its own grain** ([`Scale::receipt`]): with the word, a strand's faces are
/// the same bits (the receipt reads the prolonged rows alone and changes no state), the text keeps the word, the opening's reader takes no
/// covector from it (the opening block and its bias move as without the word), the block `B⁻` takes one that differs from
/// the one without it, and the covector of the block's largest entries matches the central difference of the code with the receipt's
/// own code added.
#[test]
fn the_levels_receipt_reads_its_prolonged_rows_and_returns_through_the_level_alone() {
    let (mut read, mut seams) = (0usize, 0usize);
    for (still, past) in [(1usize, false), (2, true)] {
        let plain = towered_before_live(still);
        let mut field = plain.clone();
        field.scale.as_mut().unwrap().receipt = true;
        assert_eq!(Constitution::from_text(&field.to_text()).unwrap(), field, "still {still}: the text keeps the receipt");
        let a = field.declaration.alphabet;
        let sites = 13;
        let classes = drawn_classes(0xD5, sites, a);
        let (with, without) = (field.strand_pass(&classes, true, past).unwrap(), plain.strand_pass(&classes, true, past).unwrap());
        assert_eq!(with.faces, without.faces, "still {still}: the receipt moves no face");
        let (rc, rn) = with.tower.as_ref().unwrap().receipt_code();
        assert!(rn > 0 && rc > 0, "still {still}: the receipt compares {rn} places");
        let (mut g, mut g0) = (vec![0i128; field.material_len()], vec![0i128; plain.material_len()]);
        field.strand_returned(&classes, &classes, &with, &mut g).unwrap();
        plain.strand_returned(&classes, &classes, &without, &mut g0).unwrap();
        let l = &field.layout;
        let dw = field.declaration.width;
        // (the encoding is the input's as well as the reader's, and the receipt's covector reaches the input through the restriction)
        for (name, range) in [("opening", l.opening..l.opening + dw * dw), ("opening bias", l.opening_bias..l.opening_bias + dw)] {
            assert_eq!(g[range.clone()], g0[range], "still {still}: the {name} takes nothing from the receipt");
        }
        let base = field.theta.len();
        let sc = field.scale.as_deref().unwrap();
        let glue_at = base + sc.coarse.theta.len();
        let (b2, bb2, _) = sc.before_offsets(dw).unwrap();
        assert_ne!(g[glue_at + b2..glue_at + bb2], g0[glue_at + b2..glue_at + bb2], "still {still}: the block takes the receipt's covector");
        let code = |f: &Constitution| -> i64 {
            let pass = f.strand_pass(&classes, false, past).unwrap();
            let places: i64 = pass.faces.iter().zip(&classes).skip(1).map(|(face, &c)| crate::field::ratio_code(face.masses[c], face.total)).sum();
            let known = vec![false; sites];
            places + opening_code(f, &Region { classes: &classes, unresolved: &known, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: true, strand: false, past, second: false, targets: None }) + pass.tower.as_ref().map_or(0, |t| t.receipt_code().0)
        };
        let sheets = |f: &Constitution| -> Vec<Vec<u32>> {
            let pass = f.strand_pass(&classes, true, past).unwrap();
            let coarse = pass.tower.iter().flat_map(|t| t.ticks().iter());
            pass.ticks.iter().chain(coarse).flat_map(|c| c.classes.iter().map(|lst| lst.off.iter().chain(&lst.members).copied().collect())).collect()
        };
        let grain = MATERIAL_BITS;
        let mut entries: Vec<usize> = (glue_at + b2..glue_at + bb2).collect();
        entries.sort_by_key(|&i| std::cmp::Reverse(g[i].unsigned_abs()));
        for i in entries.into_iter().take(4).filter(|&i| g[i] != 0) {
            let moved = |delta: i32| {
                let mut f = field.clone();
                *f.material_mut().nth(i).unwrap() += delta;
                f
            };
            let straddles = |delta: i32| sheets(&moved(delta)) != sheets(&field) || sheets(&moved(-delta)) != sheets(&field);
            let shift = 40 + grain - 20;
            let Some((delta, h)) = probe_step(grain, &|delta: i32| (g[i] * 2 * delta as i128) >> shift, &straddles) else {
                seams += 1;
                continue;
            };
            read += 1;
            let measured = code(&moved(delta)) - code(&moved(-delta));
            let predicted = (g[i] * 2 * delta as i128) >> shift;
            let tolerance = predicted.abs() / 8 + ((64 * (sites as i128 - 1)) << h);
            assert!((measured as i128 - predicted).abs() <= tolerance, "still {still}, past {past}: the block's entry {i} at {h} halvings: measured {measured}, predicted {predicted}");
        }
    }
    eprintln!("LEVEL_RECEIPT_PROBES read={read} on_a_seam={seams}");
    assert!(read >= 4, "read {read} probes, {seams} on a seam");
}

/// [definition; the lead, November 18, the record of the two streams §15] **The row of the site after reads the second site before**
/// ([`Region::second`]) in a passage read by two streams: with the word some face moves; a place's face is the same bits in the
/// passage cut after it; the region's own word reads the same forward and returns the same covector; the rows `E₊` take a covector
/// (without the word a strand gives them none); and the covector matches the code's central difference on every family's largest
/// entries, the rows `E₊` among them.
#[test]
fn a_strands_row_of_the_second_place_before_is_read_and_returned() {
    let (mut read, mut seams) = (0usize, 0usize);
    for (name, field, past) in [("circles, turned heads", circled_shaped(0), false), ("plain contacts", shaped(1), true), ("the opening compared", opened(1), true), ("the opening compared, odd contacts at rest", opened(1), false)] {
        let a = field.declaration.alphabet;
        let sites = 11;
        let classes = drawn_classes(0xE6, sites, a);
        let code = |field: &Constitution, classes: &[usize]| -> i64 {
            let places: i64 = field.strand_pass_with(classes, false, past, true).unwrap().faces.iter().zip(classes).skip(1).map(|(f, &c)| crate::field::ratio_code(f.masses[c], f.total)).sum();
            let known = vec![false; classes.len()];
            let opening = if field.declaration.opening { opening_code(field, &Region { classes, unresolved: &known, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: true, strand: false, past, second: true, targets: None }) } else { 0 };
            places + opening
        };
        let sheets = |field: &Constitution, classes: &[usize]| -> Vec<Vec<u32>> { field.strand_pass_with(classes, true, past, true).unwrap().ticks.iter().flat_map(|c| c.classes.iter().map(|l| l.off.iter().chain(&l.members).copied().chain(l.probes.iter().flat_map(|p| std::iter::once(u32::MAX).chain(p.iter().copied()))).collect())).collect() };
        let pass = field.strand_pass_with(&classes, true, past, true).unwrap();
        assert_ne!(pass.faces, field.strand_pass(&classes, false, past).unwrap().faces, "{name}: the row of the second place before moves some face");
        for t in 1..sites {
            let cut = field.strand_pass_with(&classes[..=t], false, past, true).unwrap().faces;
            assert_eq!(cut[t], pass.faces[t], "{name}: place {t} reads the passage cut after it as it reads the whole");
        }
        let mut g = vec![0i128; field.theta.len()];
        field.strand_returned(&classes, &classes, &pass, &mut g).unwrap();
        {
            let known = vec![false; sites];
            let region = Region { classes: &classes, unresolved: &known, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: true, past, second: true, targets: None };
            let (faces, section) = field.read_and_return(&[region]).unwrap();
            assert!(faces[0][0].is_none() && faces[0][1..].iter().zip(&pass.faces[1..]).all(|(a, b)| a.as_ref() == Some(b)), "{name}: a strand region's faces are the open places'");
            assert_eq!(section, g, "{name}: a strand region's covector in a section is the strand's return");
        }
        let l = field.layout.clone();
        let rows_after = l.after..l.after + (a + 1) * field.declaration.width;
        assert!(g[rows_after.clone()].iter().any(|&v| v != 0), "{name}: the rows of the site after take a covector");
        let plain = field.strand_pass(&classes, true, past).unwrap();
        let mut g0 = vec![0i128; field.theta.len()];
        field.strand_returned(&classes, &classes, &plain, &mut g0).unwrap();
        assert!(g0[rows_after].iter().all(|&v| v == 0), "{name}: without the word a strand reads no row of the site after");
        for &(start, len, grain) in field.families() {
            let natural: u32 = if grain == MATERIAL_BITS { 40 } else { 24 };
            let mut entries: Vec<usize> = (start..start + len).collect();
            entries.sort_by_key(|&i| std::cmp::Reverse(g[i].unsigned_abs()));
            for i in entries.into_iter().take(if start == l.after { 6 } else { 2 }).filter(|&i| g[i] != 0) {
                if start == l.temper {
                    continue;
                }
                let moved = |delta: i32| {
                    let mut f = field.clone();
                    f.theta[i] += delta;
                    f
                };
                let straddles = |delta: i32| sheets(&moved(delta), &classes) != sheets(&field, &classes) || sheets(&moved(-delta), &classes) != sheets(&field, &classes);
                let shift = natural + grain - 20;
                let Some((delta, h)) = probe_step(grain, &|delta: i32| (g[i] * 2 * delta as i128) >> shift, &straddles) else {
                    seams += 1;
                    continue;
                };
                read += 1;
                let measured = code(&moved(delta), &classes) - code(&moved(-delta), &classes);
                let predicted = (g[i] * 2 * delta as i128) >> shift;
                let tolerance = predicted.abs() / 8 + ((64 * (sites as i128 - 1)) << h);
                assert!((measured as i128 - predicted).abs() <= tolerance, "{name}: family at {start} (grain {grain}) entry {i} at {h} halvings: measured {measured}, predicted {predicted}");
            }
        }
    }
    eprintln!("STRAND_SECOND_COVECTOR_PROBES read={read} on_a_seam={seams}");
    assert!(read >= 60 && 8 * seams <= read, "read {read} probes, {seams} on a seam");
}

/// [definition; the lead, November 18, the record of the two streams §9] **A strand's place reads nothing at or after it**: the face of the
/// open place at place `t` of a passage read by two streams is the same bits as the last face of the passage cut after place `t`, at
/// every place, with the strand's odd contacts at rest and facing the past, on fields with circles, with plain contacts and with the
/// opening compared. A place's reading stands whatever follows it; and with the odd contacts facing the past some face differs from
/// its reading with them at rest.
#[test]
fn a_strands_place_reads_nothing_at_or_after_it() {
    for (name, field) in [("circles, one still head", circled_shaped(1)), ("circles, turned heads", circled_shaped(0)), ("plain contacts", shaped(1)), ("the opening compared", opened(1))] {
        let a = field.declaration.alphabet;
        let sites = 13;
        let classes = drawn_classes(0xC7, sites, a);
        let whole: Vec<Vec<TowerFace>> = [false, true].iter().map(|&past| field.strand_pass(&classes, false, past).unwrap().faces).collect();
        for (k, past) in [false, true].into_iter().enumerate() {
            for t in 1..sites {
                let cut = field.strand_pass(&classes[..=t], false, past).unwrap().faces;
                assert_eq!(cut[t], whole[k][t], "{name}, past {past}: place {t} reads the passage cut after it as it reads the whole");
            }
        }
        assert_ne!(whole[0], whole[1], "{name}: the odd contacts facing the past move some face");
    }
}

/// [definition; the lead, November 18, the frontier record §6] **The strand's two streams in one tick are the second tick's bits**: the
/// faces of [`Constitution::strand_pass`] (the open places as sites of the known stream's batch, read by their places) are those of
/// [`Constitution::strand_faces`] (a second tick written for them) at every place, on fields with a still head and without, with
/// circles and paces off their rest.
#[test]
fn the_strands_two_streams_in_one_tick_are_the_second_ticks_bits() {
    for (name, field) in [("circles, one still head", circled_shaped(1)), ("circles, turned heads", circled_shaped(0)), ("plain contacts", shaped(1)), ("no still head, plain contacts", shaped(0))] {
        let a = field.declaration.alphabet;
        for (seed, sites) in [(0xB1u64, 14usize), (0xB2, 9), (0xB3, 2)] {
            let classes = drawn_classes(seed, sites, a);
            let second = field.strand_faces(&classes).unwrap();
            let joined = field.strand_pass(&classes, false, false).unwrap().faces;
            assert_eq!(joined.len(), sites);
            for t in 0..sites {
                assert_eq!(joined[t], second[t], "{name}: {sites} places, place {t}");
            }
        }
    }
}

/// [definition; the lead, November 18, the frontier record §6] **The return under the strand's known stream**: on a region whose places
/// are known but its last, read with every known place hearing only what stands before it (a ruler's forward at `3`), the covector
/// matches the code's difference, family by family at its largest entries, as [`covector_matches_the_codes_difference`] reads the law's
/// (a probe that moves a site across a sheet crosses a seam the covector does not read and is counted apart). The rows the forward left
/// out take none: the opening's and the moments' after rows.
#[test]
fn the_covector_under_the_known_stream_matches_the_codes_difference() {
    let sheets = |field: &Constitution, r: &Region| -> Vec<Vec<u32>> { field.pass(r, true).unwrap().ticks.iter().flat_map(|c| c.classes.iter().map(|l| l.off.iter().chain(&l.members).copied().chain(l.probes.iter().flat_map(|p| std::iter::once(u32::MAX).chain(p.iter().copied()))).collect())).collect() };
    const LAST: [bool; 7] = [false, false, false, false, false, false, true];
    let r = Region { classes: &CLASSES, unresolved: &LAST, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None };
    let (mut read, mut seams) = (0usize, 0usize);
    for (name, mut field) in [("circles, one still head", circled_shaped(1)), ("circles, turned heads", circled_shaped(0)), ("plain contacts", shaped(1))] {
        field.ruler_far = 3;
        let g = covector_of(&field, &r);
        let l = field.layout.clone();
        let dw = field.declaration.width;
        let rows = (field.declaration.alphabet + 1) * dw;
        assert!(g[l.after..l.after + rows].iter().all(|&v| v == 0), "{name}: the opening's after rows take no covector");
        let tm2 = 2 * field.declaration.moment_modes();
        assert!(g[l.moment_after..l.moment_after + (field.declaration.alphabet + 1) * tm2].iter().all(|&v| v == 0), "{name}: the moments' after rows take none");
        for &(start, len, grain) in field.families() {
            let natural: u32 = if grain == MATERIAL_BITS { 40 } else { 24 };
            let mut entries: Vec<usize> = (start..start + len).collect();
            entries.sort_by_key(|&i| std::cmp::Reverse(g[i].unsigned_abs()));
            for i in entries.into_iter().take(3).filter(|&i| g[i] != 0) {
                let straddles = |delta: i32| {
                    let (mut plus, mut minus) = (field.clone(), field.clone());
                    plus.theta[i] += delta;
                    minus.theta[i] -= delta;
                    sheets(&plus, &r) != sheets(&field, &r) || sheets(&minus, &r) != sheets(&field, &r)
                };
                let shift = natural + grain - 20;
                let Some((delta, h)) = probe_step(grain, &|delta: i32| (g[i] * 2 * delta as i128) >> shift, &straddles) else {
                    seams += 1;
                    continue;
                };
                read += 1;
                let measured = if start == l.temper {
                    let at = |k: i32| { let mut f = field.clone(); f.theta[i] += k * (delta / 8); f.code(&r).unwrap().0 as i128 };
                    let weighted: i128 = (-8..=8).map(|k| k as i128 * at(k)).sum();
                    div_nearest(16 * weighted, 408) as i64
                } else {
                    let (mut plus, mut minus) = (field.clone(), field.clone());
                    plus.theta[i] += delta;
                    minus.theta[i] -= delta;
                    plus.code(&r).unwrap().0 - minus.code(&r).unwrap().0
                };
                let predicted = (g[i] * 2 * delta as i128) >> shift;
                let tolerance = predicted.abs() / 8 + (64 << h);
                assert!((measured as i128 - predicted).abs() <= tolerance, "{name}: family at {start} (grain {grain}) entry {i} at {h} halvings: measured {measured}, predicted {predicted}");
            }
        }
    }
    eprintln!("KNOWN_STREAM_COVECTOR_PROBES read={read} on_a_seam={seams}");
    assert!(read >= 60 && 8 * seams <= read, "read {read} probes, {seams} on a seam");
}

/// [definition; the lead, November 18, the frontier record §6] **A region read as a known stream is the ruler's forward at three, as the
/// region's own word** ([`Region::before`]): on fields with circles, with the opening compared, with a level and with a level reading twice,
/// a region carrying the word reads under the law the faces the same region reads under a ruler's forward at `3`, which are not the law's
/// faces; its covector in a section is that forward's own return at the weight of any region's (in a field that reads twice the one read
/// stands for both, so the section's mean leaves it whole); a section holding it beside a region of the law is the sum of the two; and the
/// level's material takes nothing from it.
#[test]
fn a_region_read_as_a_known_stream_is_the_rulers_forward_at_three() {
    const LAST: [bool; 7] = [false, false, false, false, false, false, true];
    let marked = {
        let (mut f, _) = towered_live(1).with_mark().unwrap();
        let l = f.layout.clone();
        f.theta[l.mark..l.mark + MARK_BASES].copy_from_slice(&[1 << 22, 1 << 21, 3 << 20]);
        f
    };
    for (name, field) in [("circles", circled_shaped(1)), ("opened", opened(1)), ("tower", towered_live(1)), ("marked tower", marked)] {
        let mut ruled = field.clone();
        ruled.ruler_far = 3;
        let len = field.material_len();
        let raw = |f: &Constitution, r: &Region| -> Vec<i128> {
            let pass = f.pass(r, true).unwrap();
            let mut g = vec![0i128; len];
            f.returned(r, &pass, &mut g).unwrap();
            g
        };
        // The fixtures' level holds a region of seven places' epochs, so the long region is read on the fields without one.
        let long = Region { classes: &LONG, unresolved: &LONG_OPEN, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None };
        let masked = Region { classes: &CLASSES, unresolved: &OPEN, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None };
        let frontier = Region { classes: &CLASSES, unresolved: &LAST, faces: &[], locked: &[], echo: &[], domain: Some(7), port: None, before: false, strand: false, past: false, second: false, targets: None };
        for r in [if field.scale.is_some() { masked } else { long }, frontier] {
            let word = Region { before: true, ..r };
            let (faces, g) = field.read_and_return(&[word]).unwrap();
            assert_eq!(faces[0], ruled.faces(&r).unwrap(), "{name}: the word's faces are the ruler's");
            assert_ne!(faces[0], field.faces(&r).unwrap(), "{name}: and not the law's");
            let once = raw(&ruled, &r);
            assert!(once.iter().any(|&v| v != 0) && once[field.theta.len()..].iter().all(|&v| v == 0), "{name}: the forward returns, and nothing to the level");
            assert_eq!(g, once, "{name}: the word's covector in a section is the forward's own return");
            let (both_faces, both) = field.read_and_return(&[r, word]).unwrap();
            assert_eq!(both_faces[1], faces[0], "{name}: a region's reading stands beside another's");
            let times = if field.declaration.mark { 2 } else { 1 };
            let sum: Vec<i128> = raw(&field, &r).iter().zip(&once).map(|(&a, &b)| a + times * b).collect();
            assert_eq!(both, field.both_reads_mean(sum), "{name}: a section is its regions' sum");
        }
    }
}

/// [definition; the lead, November 18, the frontier record §6] **The strand's open place is its frontier region's**: under
/// [`Constitution::strand_faces`] the face at place `t` is the same bits as the open last place of the region `[0, t]` read with every known
/// place hearing only what stands before it (a ruler's forward at `3`) and its open place on the bare clock (`bare_stretch`: the strand's
/// open places are not read again by a clock), at every place, on fields with a still head and without, with circles and paces off their
/// rest. One forward of a passage reads what a region a place reads.
#[test]
fn the_strands_open_place_is_its_frontier_regions() {
    for (name, field) in [("circles, one still head", circled_shaped(1)), ("circles, turned heads", circled_shaped(0)), ("plain contacts", shaped(1))] {
        let a = field.declaration.alphabet;
        let sites = 14;
        let classes = drawn_classes(0xB1, sites, a);
        let faces = field.strand_faces(&classes).unwrap();
        assert_eq!(faces.len(), sites);
        // (an open place of the strand runs on the bare clock at every tick, as the region's open last place does where the stretch runs bare)
        let mut ruled = field.clone();
        ruled.ruler_far = 3;
        ruled.bare_stretch = true;
        for t in 1..sites {
            let open: Vec<bool> = (0..=t).map(|k| k == t).collect();
            let region = Region { classes: &classes[..=t], unresolved: &open, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None };
            let law = ruled.faces(&region).unwrap()[t].clone().unwrap();
            assert_eq!(faces[t], law, "{name}: place {t}");
        }
    }
}

/// [definition; the lead, November 18, the audit of that day §1.4] **A stretch read at the frontier is its context and the one place after
/// it**: the cut takes the stretch's own draw of a context and one place while the piece goes on by the least context or more; at a piece's
/// end it takes every place left, the open place the true end's first void where the piece closes its document and the piece's last place
/// where it does not; a piece walked by the frontier's cut alone is consumed whole, one compared place a stretch. The state has every place
/// known but its last, its domain its sites. The keyed share takes none at zero, all at eight, and about its eighths between.
#[test]
fn a_stretch_at_the_frontier_is_its_context_and_the_next_place_alone() {
    use crate::passage::{frontier_cut_of, frontier_here, frontier_state_of, lengths_of, Kind};
    let (seed, least, octaves) = (0xABCD_u64, 4u64, 7u64);
    for closes in [false, true] {
        for places in [1u64, 2, 5, 9, 100, 1000, 4321] {
            let (mut cursor, mut d, mut compared, mut done) = (0u64, 0u64, 0u64, false);
            while !done {
                d += 1;
                let rest = places - cursor;
                let (q0, _) = lengths_of(seed, d, least, octaves);
                let (q, a, ends, last) = frontier_cut_of(seed, d, rest, closes, least, octaves);
                if rest > q0 + least {
                    assert_eq!((q, a, ends, last), (q0, 1, false, false), "the stretch's own context and one place");
                    assert!(rest - (q + a) >= least, "the piece goes on by the least context or more");
                } else if closes {
                    assert_eq!((q, a, ends, last), (rest, 0, true, true), "every place left known, the end's void open");
                } else {
                    assert_eq!((q, a, ends, last), (rest - 1, 1, false, true), "the piece's last place open");
                }
                cursor += q + a;
                compared += 1;
                done = last;
            }
            assert_eq!(cursor, places, "the piece is consumed whole");
            assert_eq!(compared, d);
        }
    }
    let classes: Vec<usize> = (0..9).collect();
    let s = frontier_state_of(classes.clone(), None);
    assert_eq!((s.kind, s.counted, s.q, s.region.domain), (Kind::Frontier, 9, 8, Some(9)));
    assert_eq!(s.region.classes, classes);
    assert_eq!(s.region.unresolved, (0..9).map(|t| t == 8).collect::<Vec<_>>(), "the last place alone is open");
    assert_eq!(crate::region::view_of(&s.region).weight(), (9, 1), "one place compared for the region's sites");
    let e = frontier_state_of(classes.clone(), Some(77));
    assert_eq!((e.counted, e.q, e.region.classes.last().copied(), e.region.unresolved.iter().filter(|&&u| u).count()), (10, 9, Some(77), 1), "a true end's void is the open place");
    assert!(*e.region.unresolved.last().unwrap());
    let lone = frontier_state_of(vec![5], None);
    assert_eq!((lone.counted, lone.q, lone.region.unresolved.clone()), (1, 0, vec![true]));
    assert!((1..=4096u64).all(|d| !frontier_here(seed, d, 0)) && (1..=4096u64).all(|d| frontier_here(seed, d, 8)));
    for share in 1..8u64 {
        let n = (1..=8192u64).filter(|&d| frontier_here(seed, d, share)).count() as u64;
        assert!(n.abs_diff(1024 * share) < 160, "share {share}: {n} of 8192");
        assert!((1..=8192u64).all(|d| !frontier_here(seed, d, share) || frontier_here(seed, d, share + 1)), "a larger share keeps a smaller one's stretches");
    }
}

/// [definition; theory, November 13, the record of the landmarks §5 and the design record §4.9] **A level's sites are the landmarks of its
/// news**: on random streams the isolation's sites are the places no greater place reaches (`u ≻ t`: more news, or as much and earlier),
/// read pair by pair; a place with a section of news or more is a site (statement 1); two sites stand a section or more apart (statement
/// 2); under a flat face, each place carrying the section, every place is a site; a stream of equal places under a section is one epoch.
#[test]
fn a_levels_sites_are_the_landmarks_of_its_news() {
    let section = 40i64;
    let stream = keys(1 << 14);
    for n in 0..200 {
        let len = 1 + n % 23;
        let news: Vec<i64> = (0..len).map(|t| (stream[(n * 31 + t) % stream.len()] % 64) as i64).collect();
        let sum = |t: usize| news[..=t].iter().sum::<i64>();
        let greater = |u: usize, t: usize| news[u] > news[t] || (news[u] == news[t] && u < t);
        let brute: Vec<usize> = (0..len).filter(|&t| !(0..len).any(|u| u != t && greater(u, t) && (sum(u) - sum(t)).abs() < section)).collect();
        let anchors = level_anchors(&news, section);
        let sites: Vec<usize> = anchors.iter().copied().filter(|&a| a > 0 || brute.contains(&0)).collect();
        assert_eq!(sites, brute, "stream {n}: {news:?}");
        assert_eq!(anchors[0], 0);
        for (t, &c) in news.iter().enumerate() {
            if c >= section {
                assert!(brute.contains(&t), "stream {n}: a place with a section of news is a site");
            }
        }
        for w in brute.windows(2) {
            assert!(sum(w[1]) - sum(w[0]) >= section, "stream {n}: two sites stand a section apart");
        }
    }
    assert_eq!(level_anchors(&[40; 9], 40), (0..9).collect::<Vec<_>>(), "under a flat face every place is a site");
    assert_eq!(level_anchors(&[5; 9], 40), vec![0], "equal places under a section are one epoch");
    let flat = level_section(244);
    assert_eq!(flat, face_code(1, 244));
    assert!(flat > 7 << 20 && flat < 8 << 20, "the section over 244 classes is the flat face's 7.93 bits");
}

/// [definition; theory, November 13, the design record §4.5 and §4.9] **The cut's phases and clock**: a place's phase is the news from its
/// epoch's anchor in sections, its first harmonic one and its others the turn's faces at whole multiples of the phase (a whole section
/// is a whole turn, half a section a half turn); the level's clock is the news between anchors in sections; every epoch's places follow
/// its anchor.
#[test]
fn the_levels_cut_reads_its_phases_and_clock() {
    let pi = opened(1).half_turn();
    let one = 1i64 << MOVE_BITS;
    // Sites at 0 and 3 (news 8 a section of 8); the places between carry half a section and a quarter.
    let news = [8i64, 4, 2, 8, 2, 2];
    let cut = level_cut(&news, 8, 6, pi).unwrap();
    assert_eq!(cut.anchors, vec![0, 3]);
    assert_eq!(cut.epoch, vec![0, 0, 0, 1, 1, 1]);
    let h = |t: usize| &cut.harmonics[t * 6..(t + 1) * 6];
    assert_eq!(h(0), &[one, one, 0, one, 0, one][..], "at its anchor a place stands at phase zero");
    // Place 1: half a section, so cos π = −1, sin π = 0, cos 2π = 1, sin 2π = 0, cos 3π = −1.
    assert_eq!(h(1), &[one, -one, 0, one, 0, -one][..]);
    // Place 2: three quarters of a section, so cos 3π/2 = 0, sin = −1, cos 3π = −1, sin 3π = 0, cos 9π/2 = 0.
    assert_eq!(h(2), &[one, 0, -one, -one, 0, 0][..]);
    assert_eq!(cut.tau, vec![0, (14i64 << PACE_BITS) / 8], "the news from the first anchor to the second, 14 of a section of 8");
    assert!(level_cut(&[1, -1], 8, 6, pi).is_err(), "news below zero");
}

/// A field of four ticks and eight contacts, every family drawn: the return acts at three ticks, so a return's owed term reaches a tick with a
/// return of its own.
fn four_ticks(still: usize) -> Constitution {
    shaped_with(Declaration { ticks: 4, contacts: 8, ..tiny_declaration(still) })
}

/// [definition; theory, November 13, the junction record §7] **The junction's return founded at the matched load keeps every face and the built
/// reverse**: grown onto a field (plain, with carry circles, with the opening's lift, and a tower), the chart `L` and `ℓ_b` are zero, every face
/// is the source's, and the code's covector is the source's on every standing entry, with the chart's own covector beside it, nonzero where a
/// return pairs a covector with a moved state; the head line is `hnn-field-v14j` and round-trips; a second growth is refused.
#[test]
fn the_junctions_return_founded_at_the_matched_load_keeps_every_face_and_the_built_reverse() {
    let mut fields: Vec<(&str, Constitution)> = Vec::new();
    for still in [0usize, 1, 2] {
        fields.push(("four ticks", four_ticks(still)));
        fields.push(("carry", circled_shaped(still)));
        fields.push(("opened", opened(still)));
        fields.push(("tower", towered_live(still)));
    }
    for (name, plain) in &fields {
        let (grown, from) = plain.with_junction().unwrap();
        let (d, l) = (grown.declaration, grown.layout.clone());
        assert!(d.junction && !plain.declaration.junction);
        assert_eq!(l.junction, plain.theta.len(), "{name}: the chart at the fine field's end");
        assert!(grown.theta[l.junction..l.junction + d.width].iter().all(|&v| v == 0) && grown.theta[l.junction_bias] == 0, "{name}: founded at zero");
        assert_eq!(from.len(), grown.material_len());
        assert_eq!(from.iter().flatten().count(), plain.material_len(), "{name}: every standing entry kept");
        assert_eq!(grown.faces(&region()).unwrap(), plain.faces(&region()).unwrap(), "{name}: every face kept");
        let (g, h) = (tower_covector(&grown, &region()), tower_covector(plain, &region()));
        for (n, o) in from.iter().enumerate() {
            if let Some(o) = o {
                assert_eq!(g[n], h[*o], "{name}: the covector of standing entry {o}");
            }
        }
        assert!(g[l.junction..=l.junction_bias].iter().any(|&v| v != 0), "{name}: the chart has a covector at the founding");
        let text = d.to_text();
        assert!(text.starts_with("hnn-field-v14j "), "{name}: {text}");
        assert_eq!(Declaration::from_text(&text).unwrap(), d);
        assert!(grown.with_junction().is_err(), "{name}: a second growth");
    }
    // The return reads every tick past the first, and none at the first.
    let (grown, _) = four_ticks(1).with_junction().unwrap();
    let (by_tick, _) = grown.junction_covectors(&region()).unwrap();
    assert_eq!(by_tick.iter().map(|(k, _, _)| *k).collect::<Vec<_>>(), vec![1, 2, 3]);
    assert!(four_ticks(1).junction_covectors(&region()).is_err());
    // The head line without the return, and a v14j line whose words are not the return's, refused.
    assert!(Declaration::from_text(&Declaration { opening: true, ..four_ticks(1).declaration }.to_text()).unwrap().opening);
    let line = grown.declaration.to_text();
    assert!(Declaration::from_text(&format!("{} 0", &line[..line.len() - 2])).is_err(), "a junction word of zero");
}

/// [definition; theory, November 13, the junction record §7] **The return's covector matches its code's difference**: on fields of four ticks with
/// the return off its founding (`L` drawn and `ℓ_b` half a unit, so `Γ` stands off zero and most returns carry a rate), the
/// code's covector predicts the code's central difference at the entries with the largest covector of each family, the chart's among them, as the
/// carry's covector test reads it: so the output's `(1 + Γ) λ`, the owed `−Γ λ` two ticks back and the chart's term through the lane adjoint are
/// each the reverse of their forward.
#[test]
fn the_junctions_return_covector_matches_its_codes_difference() {
    let (mut read, mut seams, mut charts_read) = (0usize, 0usize, 0usize);
    let mut gammas: Vec<i64> = Vec::new();
    for still in [0usize, 1, 2] {
        let (mut field, _) = four_ticks(still).with_junction().unwrap();
        let l = field.layout.clone();
        let dw = field.declaration.width;
        let stream = keys(1 << 15);
        for (n, v) in field.theta[l.junction..l.junction + dw].iter_mut().enumerate() {
            let word = &stream[4 * (n + 9000)..4 * (n + 9000) + 4];
            let k = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) as i64;
            *v = ((k << MATERIAL_BITS) >> 32) as i32;
        }
        field.theta[l.junction_bias] = 1 << 15;
        let r = region();
        let pass = field.pass(&r, true).unwrap();
        gammas.extend(pass.ticks.iter().flat_map(|c| c.jg.iter().copied()));
        let g = covector_of(&field, &r);
        let sheets = |f: &Constitution| -> Vec<Vec<u32>> {
            let p = f.pass(&r, true).unwrap();
            p.ticks.iter().flat_map(|c| c.classes.iter().map(|cl| cl.off.iter().chain(&cl.members).copied().chain(cl.probes.iter().flat_map(|p| std::iter::once(u32::MAX).chain(p.iter().copied()))).collect())).collect()
        };
        for &(start, len, grain) in field.families() {
            if start == l.temper {
                continue;
            }
            let natural: u32 = if grain == MATERIAL_BITS { 40 } else { 24 };
            let mut entries: Vec<usize> = (start..start + len).collect();
            entries.sort_by_key(|&i| std::cmp::Reverse(g[i].unsigned_abs()));
            for i in entries.into_iter().take(3).filter(|&i| g[i] != 0) {
                let moved = |delta: i32| {
                    let mut f = field.clone();
                    f.theta[i] += delta;
                    f
                };
                let straddles = |delta: i32| sheets(&moved(delta)) != sheets(&field) || sheets(&moved(-delta)) != sheets(&field);
                let shift = natural + grain - 20;
                let Some((delta, h)) = probe_step(grain, &|delta: i32| (g[i] * 2 * delta as i128) >> shift, &straddles) else {
                    seams += 1;
                    continue;
                };
                read += 1;
                charts_read += usize::from(start == l.junction || start == l.junction_bias);
                let measured = moved(delta).code(&r).unwrap().0 - moved(-delta).code(&r).unwrap().0;
                let predicted = (g[i] * 2 * delta as i128) >> shift;
                let tolerance = predicted.abs() / 8 + (64 << h);
                assert!((measured as i128 - predicted).abs() <= tolerance, "still {still} family at {start} (grain {grain}) entry {i} at {h} halvings: measured {measured}, predicted {predicted}");
            }
        }
    }
    let (least, most) = (gammas.iter().copied().min().unwrap(), gammas.iter().copied().max().unwrap());
    eprintln!("JUNCTION_COVECTOR_PROBES read={read} on_a_seam={seams} charts={charts_read} gamma_least={least} gamma_most={most}");
    assert!(least > -(1 << 30) && most < 1 << 30 && gammas.iter().filter(|&&g| g.abs() > 1 << 26).count() * 2 > gammas.len(), "the return carries a rate at most sites and stays passive: Γ from {least} to {most} on 2^(−30)");
    assert!(read > 0 && 16 * seams <= read && charts_read > 0, "read {read} probes, {seams} on a seam, {charts_read} of the chart");
}

/// [definition; theory, November 13, the junction record §7] **The return's reflection** is zero at the matched load, odd in `ℓ`, under one at
/// every admitted chart and refused past it; its sensitivity is `ln 2/2` at the founding.
#[test]
fn the_junctions_reflection_is_the_cayley_map_of_its_load() {
    let e = Exponential::new(FACE_BITS);
    assert_eq!(junction_gamma(&e, 0).unwrap(), 0);
    for l in [1i64 << 14, 1 << 16, 3 << 16, 29 << 16, (30 << 16) + 65535] {
        let (up, down) = (junction_gamma(&e, l).unwrap(), junction_gamma(&e, -l).unwrap());
        assert!((up + down).abs() <= 1, "odd at {l}: {up} {down}");
        assert!(up > 0 && up < 1 << 30, "under one at {l}: {up}");
    }
    // ℓ = 1: ρ = 2 and Γ = 1/3.
    assert!((junction_gamma(&e, 1 << 16).unwrap() - (1i64 << 30) / 3).abs() <= 1);
    assert!(junction_gamma(&e, 31 << 16).is_err() && junction_gamma(&e, -(32 << 16)).is_err());
    assert_eq!(junction_sensitivity(0), release(ln2_face(), 1));
}

/// [measurement; G157] **The reach's logs**: `log₂ n` on the face's grain is the octave at powers of two and `log₂ 3` between, and at a plain
/// clock (a tick a place) the clock's log is zero and the remainder the place's.
#[test]
fn the_reachs_logs_are_zero_at_a_plain_clock() {
    assert_eq!((log2_grain(1), log2_grain(2), log2_grain(1024)), (0, 1 << 16, 10 << 16));
    assert!((log2_grain(3) - 103_872).abs() <= 2, "log₂ 3 on 2^(−16): {}", log2_grain(3));
    let plain: Vec<i64> = (0..40).map(|t| (t as i64) << PACE_BITS).collect();
    for (i, j) in [(5usize, 4usize), (20, 3), (0, 39), (7, 13)] {
        let (lw, lu) = reach_logs(&plain, i, j);
        assert_eq!(lw, 0, "a plain clock reads the place count at {i} {j}");
        assert_eq!(lu, log2_grain(i.abs_diff(j) as u128) & ((1 << 16) - 1));
    }
    // A clock twice the place count reads one octave more.
    let fast: Vec<i64> = (0..40).map(|t| (2 * t as i64) << PACE_BITS).collect();
    assert_eq!(reach_logs(&fast, 20, 3).0, 1 << 16);
}

/// [definition; agent-inferred, November 14, the ring record §4] **The field that reads twice, founded at zero, keeps every face and the built
/// reverse**: grown onto a field (plain, with carry circles, with the opening's lift, with the junction's return, and a tower), the strengths are
/// zero, every face is the source's, and the code's covector is the source's on every standing entry, with the strengths' own covector beside
/// it, nonzero where a silent site's mark pairs with the opening's covector; the head line is `hnn-field-v14m` and round-trips; a second growth
/// is refused; the parts line carries the mark's part last.
#[test]
fn the_mark_founded_at_zero_keeps_every_face_and_the_built_reverse() {
    let mut fields: Vec<(&str, Constitution)> = Vec::new();
    for still in [0usize, 1, 2] {
        fields.push(("four ticks", four_ticks(still)));
        fields.push(("carry", circled_shaped(still)));
        fields.push(("opened", opened(still)));
        fields.push(("joined", four_ticks(still).with_junction().unwrap().0));
        fields.push(("tower", towered_live(still)));
    }
    for (name, plain) in &fields {
        let (grown, from) = plain.with_mark().unwrap();
        let (d, l) = (grown.declaration, grown.layout.clone());
        assert!(d.mark && !plain.declaration.mark);
        assert_eq!(l.mark, plain.theta.len(), "{name}: the strengths at the fine field's end");
        assert!(grown.theta[l.mark..l.mark + MARK_BASES].iter().all(|&v| v == 0), "{name}: founded at zero");
        assert_eq!(from.len(), grown.material_len());
        assert_eq!(from.iter().flatten().count(), plain.material_len(), "{name}: every standing entry kept");
        assert_eq!(grown.faces(&region()).unwrap(), plain.faces(&region()).unwrap(), "{name}: every face kept");
        let (g, h) = (tower_covector(&grown, &region()), tower_covector(plain, &region()));
        for (n, o) in from.iter().enumerate() {
            if let Some(o) = o {
                assert_eq!(g[n], h[*o], "{name}: the covector of standing entry {o}");
            }
        }
        assert!(g[l.mark..l.mark + MARK_BASES].iter().any(|&v| v != 0), "{name}: the strengths have a covector at the founding");
        let text = d.to_text();
        assert!(text.starts_with("hnn-field-v14m "), "{name}: {text}");
        assert_eq!(Declaration::from_text(&text).unwrap(), d);
        assert!(grown.with_mark().is_err(), "{name}: a second growth");
    }
    let line = four_ticks(1).with_mark().unwrap().0.declaration.to_text();
    assert!(Declaration::from_text(&format!("{} 0", &line[..line.len() - 2])).is_err(), "a mark word of zero");
}

/// [definition; agent-inferred, November 14, the ring record §4] **The mark's covector matches its code's difference**: on fields of four ticks
/// reading twice with the strengths off their founding (a quarter, an eighth and three sixteenths), the code's covector predicts the code's
/// central difference at the entries with the largest covector of each family, the strengths among them, as the junction's covector test reads
/// it, the marks held at the unmoved field's first read (the first read's faces are data to the second) and the two reads' codes summed
/// (both are compared, G180): so each read's return, and the marked opening's into its open row, each class row by its share and its
/// strength, is the reverse of its forward.
#[test]
fn the_marks_covector_matches_its_codes_difference() {
    let (mut read, mut seams, mut strengths_read) = (0usize, 0usize, 0usize);
    for still in [0usize, 1, 2] {
        let (mut field, _) = four_ticks(still).with_mark().unwrap();
        let l = field.layout.clone();
        field.theta[l.mark..l.mark + MARK_BASES].copy_from_slice(&[1 << 22, 1 << 21, 3 << 20]);
        let r = region();
        let g = covector_of(&field, &r);
        let first = field.pass_with(&r, false, None).unwrap();
        let marks: Vec<Option<Shares>> = (0..r.classes.len()).map(|t| if Constitution::silent(&r, t) { first.faces[t].as_ref().map(shares) } else { None }).collect();
        // [G180] Both reads are compared: the first read's code and the second's with the marks held, summed (the covector is their mean).
        let code_of = |p: Forward| -> i64 { p.faces.iter().zip(r.classes).filter_map(|(face, &c)| face.as_ref().map(|x| x.code(c))).sum() };
        let held = |f: &Constitution| -> i64 { code_of(f.pass_with(&r, false, None).unwrap()) + code_of(f.pass_with(&r, false, Some(&marks)).unwrap()) };
        // Both reads' sheets, since both are compared: a probe that moves either read's classes stands on a seam.
        let sheets = |f: &Constitution| -> Vec<Vec<u32>> {
            [f.pass_with(&r, true, None).unwrap(), f.pass_with(&r, true, Some(&marks)).unwrap()]
                .iter()
                .flat_map(|p| p.ticks.iter().flat_map(|c| c.classes.iter().map(|cl| cl.off.iter().chain(&cl.members).copied().chain(cl.probes.iter().flat_map(|p| std::iter::once(u32::MAX).chain(p.iter().copied()))).collect())).collect::<Vec<Vec<u32>>>())
                .collect()
        };
        for &(start, len, grain) in field.families() {
            if start == l.temper {
                continue;
            }
            let natural: u32 = if grain == MATERIAL_BITS { 40 } else { 24 };
            let mut entries: Vec<usize> = (start..start + len).collect();
            entries.sort_by_key(|&i| std::cmp::Reverse(g[i].unsigned_abs()));
            for i in entries.into_iter().take(3).filter(|&i| g[i] != 0) {
                let moved = |delta: i32| {
                    let mut f = field.clone();
                    f.theta[i] += delta;
                    f
                };
                let straddles = |delta: i32| sheets(&moved(delta)) != sheets(&field) || sheets(&moved(-delta)) != sheets(&field);
                let shift = natural + grain - 20;
                let Some((delta, h)) = probe_step(grain, &|delta: i32| (g[i] * 4 * delta as i128) >> shift, &straddles) else {
                    seams += 1;
                    continue;
                };
                read += 1;
                strengths_read += usize::from(start == l.mark);
                let measured = held(&moved(delta)) - held(&moved(-delta));
                let predicted = (g[i] * 4 * delta as i128) >> shift;
                let tolerance = predicted.abs() / 8 + (64 << h);
                assert!((measured as i128 - predicted).abs() <= tolerance, "still {still} family at {start} (grain {grain}) entry {i} at {h} halvings: measured {measured}, predicted {predicted}");
            }
        }
    }
    eprintln!("MARK_COVECTOR_PROBES read={read} on_a_seam={seams} strengths={strengths_read}");
    assert!(read > 0 && 16 * seams <= read && strengths_read > 0, "read {read} probes, {seams} on a seam, {strengths_read} of the strengths");
}

/// [definition; agent-inferred, November 14, the ring record §4 and §5] **The mark's founding covector is the carried slope G175 read**: on a field
/// reading twice at its founding, the strengths' covectors sum to `Σ_t ⟨λ⁰_t, D_t⟩` of [`Constitution::carried_slopes`] on the field before the growth,
/// faced by its own first read, halved since both reads are compared and only the second is marked (G180); so the reading that sized the
/// strength is the law's own first-order direction.
#[test]
fn the_marks_founding_covector_is_the_carried_slope() {
    for still in [0usize, 1, 2] {
        for plain in [four_ticks(still), circled_shaped(still), opened(still)] {
            let (grown, _) = plain.with_mark().unwrap();
            let l = grown.layout.clone();
            let r = region();
            let g = covector_of(&grown, &r);
            let faces = plain.faces(&r).unwrap();
            let slopes: i128 = plain.carried_slopes(&r, &faces).unwrap().iter().sum();
            // Both reads are compared and only the second is marked, so the strengths' covector is half the slope, each entry released by one bit.
            let doubled: i128 = g[l.mark..l.mark + MARK_BASES].iter().map(|v| 2 * v).sum();
            assert!((doubled - slopes).abs() <= MARK_BASES as i128, "still {still}: the strengths' covector is half the carried slope: {doubled} against {slopes}");
        }
    }
}



/// [definition; agent-inferred, November 14] **A lane founded beside a tower keeps every face**: on a field with the opening's block, on its
/// tower (the level's prolongation drawn, so every path carries a covector), on that tower reading twice with the mark off its founding, and
/// on a field whose tick has the junction's return, the laned field reads every face the field read; its map covers the whole material and
/// its families tile it; its text restores it; every standing entry's covector is the one it had, the level's and the glue's included; and the
/// key chart's reads from the lane carry a covector at once.
#[test]
fn a_lane_founded_beside_a_tower_keeps_every_face() {
    for still in [0usize, 1, 2] {
        let marked = {
            let (mut f, _) = towered_live(still).with_mark().unwrap();
            let l = f.layout.clone();
            f.theta[l.mark..l.mark + MARK_BASES].copy_from_slice(&[1 << 22, 1 << 21, 3 << 20]);
            f
        };
        let fields: [(&str, Constitution); 4] = [("opened", opened(still)), ("tower", towered_live(still)), ("marked tower", marked), ("joined", four_ticks(still).with_junction().unwrap().0)];
        for (name, field) in fields {
            let r = region();
            let draws = field.declaration.lane_draws();
            let (laned, from) = field.laned(&keys(draws)).unwrap();
            assert_eq!(laned.declaration.lanes, field.declaration.lanes + 1, "{name}");
            assert_eq!(from.len(), laned.material_len(), "{name}: the map covers the material");
            assert_eq!(from.iter().flatten().count(), field.material_len(), "{name}: every standing entry kept");
            assert_eq!(laned.faces(&r).unwrap(), field.faces(&r).unwrap(), "still {still} {name}: every face kept");
            let mut at = 0;
            for (start, len, _) in laned.families_all() {
                assert_eq!(start, at, "{name}");
                at += len;
            }
            assert_eq!(at, laned.material_len(), "{name}");
            assert_eq!(Constitution::from_text(&laned.to_text()).unwrap(), laned, "{name}: its text restores it");
            let (g, h) = (tower_covector(&laned, &r), tower_covector(&field, &r));
            for (n, o) in from.iter().enumerate() {
                if let Some(o) = o {
                    assert_eq!(g[n], h[*o], "still {still} {name}: the covector of standing entry {o}");
                }
            }
            let (l, dw, old, m2) = (laned.layout.clone(), laned.declaration.width, field.declaration.width, 2 * laned.declaration.complex());
            assert!((0..m2).any(|row| (old..dw).any(|j| g[l.q + row * dw + j] != 0)), "still {still} {name}: the key chart's reads from the lane carry a covector");
        }
    }
}

/// [definition; Brandon, November 15 02:06Z] **The face's loudness founded at zero keeps every face and the built reverse**: on fields of four
/// ticks, with carry circles, with the opening's lift, reading twice and with a level, the loudness's block is appended at zero, every face is the
/// source's, the code's covector is the source's on every standing entry, and the new block has its own covector beside it; the head line is
/// `hnn-field-v14l` and round-trips; a second growth is refused; a chart's face is refused without its lanes' powers.
#[test]
fn the_loudness_founded_at_zero_keeps_every_face_and_the_built_reverse() {
    let mut fields: Vec<(&str, Constitution)> = Vec::new();
    for still in [0usize, 1, 2] {
        fields.push(("four ticks", four_ticks(still)));
        fields.push(("carry", circled_shaped(still)));
        fields.push(("opened", opened(still)));
        fields.push(("marked", four_ticks(still).with_mark().unwrap().0));
        fields.push(("tower", towered_live(still)));
    }
    for (name, plain) in &fields {
        let (grown, from) = plain.with_loud().unwrap();
        let (d, l) = (grown.declaration, grown.layout.clone());
        assert!(d.loud && !plain.declaration.loud);
        assert_eq!(l.loud, plain.theta.len(), "{name}: the block at the fine field's end");
        assert!(grown.theta[l.loud..l.loud + d.lanes + 1].iter().all(|&v| v == 0), "{name}: founded at zero");
        assert_eq!(from.iter().flatten().count(), plain.material_len(), "{name}: every standing entry kept");
        assert_eq!(grown.faces(&region()).unwrap(), plain.faces(&region()).unwrap(), "{name}: every face kept");
        let (g, h) = (tower_covector(&grown, &region()), tower_covector(plain, &region()));
        for (n, o) in from.iter().enumerate() {
            if let Some(o) = o {
                assert_eq!(g[n], h[*o], "{name}: the covector of standing entry {o}");
            }
        }
        assert!(g[l.loud..l.loud + d.lanes + 1].iter().any(|&v| v != 0), "{name}: the loudness has a covector at the founding");
        let text = d.to_text();
        assert!(text.starts_with("hnn-field-v14l "), "{name}: {text}");
        assert_eq!(Declaration::from_text(&text).unwrap(), d);
        assert!(grown.with_loud().is_err(), "{name}: a second growth");
        assert!(grown.face_of_read(&vec![0; d.width]).is_err(), "{name}: a loud chart's face needs its powers");
    }
}

/// [definition; Brandon, November 15 02:06Z] **The face's loudness's covector matches its code's difference**: on fields of four ticks whose
/// face reads its sites' loudness off the founding (`κ` an eighth of a unit an octave, `b` a sixteenth below one), the code's covector predicts
/// the code's central difference at the entries with the largest covector of each family, the loudness's among them, as the mark's test reads
/// it: so the return through the sharpness, and its radial part into the state the face read, is the reverse of its forward.
#[test]
fn the_loudness_covector_matches_its_codes_difference() {
    let (mut read, mut seams, mut loud_read) = (0usize, 0usize, 0usize);
    for still in [0usize, 1, 2] {
        let (mut field, _) = four_ticks(still).with_loud().unwrap();
        let (l, lanes) = (field.layout.clone(), field.declaration.lanes);
        for k in 0..lanes {
            field.theta[l.loud + k] = 1 << 13;
        }
        field.theta[l.loud + lanes] = -(1 << 12);
        let r = region();
        let g = covector_of(&field, &r);
        let code_of = |f: &Constitution| -> i64 { f.pass_with(&r, false, None).unwrap().faces.iter().zip(r.classes).filter_map(|(face, &c)| face.as_ref().map(|x| x.code(c))).sum() };
        let sheets = |f: &Constitution| -> Vec<Vec<u32>> {
            f.pass_with(&r, true, None).unwrap().ticks.iter().flat_map(|c| c.classes.iter().map(|cl| cl.off.iter().chain(&cl.members).copied().chain(cl.probes.iter().flat_map(|p| std::iter::once(u32::MAX).chain(p.iter().copied()))).collect())).collect()
        };
        for &(start, len, grain) in field.families() {
            if start == l.temper {
                continue;
            }
            let natural: u32 = if grain == MATERIAL_BITS { 40 } else { 24 };
            let mut entries: Vec<usize> = (start..start + len).collect();
            entries.sort_by_key(|&i| std::cmp::Reverse(g[i].unsigned_abs()));
            for i in entries.into_iter().take(3).filter(|&i| g[i] != 0) {
                let moved = |delta: i32| {
                    let mut f = field.clone();
                    f.theta[i] += delta;
                    f
                };
                let straddles = |delta: i32| sheets(&moved(delta)) != sheets(&field) || sheets(&moved(-delta)) != sheets(&field);
                let shift = natural + grain - 20;
                let Some((delta, h)) = probe_step(grain, &|delta: i32| (g[i] * 2 * delta as i128) >> shift, &straddles) else {
                    seams += 1;
                    continue;
                };
                read += 1;
                loud_read += usize::from(start == l.loud);
                let measured = code_of(&moved(delta)) - code_of(&moved(-delta));
                let predicted = (g[i] * 2 * delta as i128) >> shift;
                let tolerance = predicted.abs() / 8 + (64 << h);
                assert!((measured as i128 - predicted).abs() <= tolerance, "still {still} family at {start} (grain {grain}) entry {i} at {h} halvings: measured {measured}, predicted {predicted}");
            }
        }
    }
    eprintln!("LOUD_COVECTOR_PROBES read={read} on_a_seam={seams} loudness={loud_read}");
    assert!(read > 0 && 16 * seams <= read && loud_read > 0, "read {read} probes, {seams} on a seam, {loud_read} of the loudness");
}

/// The serial passes [`deposit_pass`] replaced (the section's deposit as it stood until November 20), the reference its bits are read against.
#[allow(clippy::too_many_arguments)]
fn deposit_serial(field: &Constitution, g: &[i128], first: &mut [i128], second: &mut [i128], rates: &[u32], remainder: Option<&mut [i64]>, last: Option<&HeldStep>, parts: &[u8]) -> DepositPass {
    let raw = g.to_vec();
    let mut g = g.to_vec();
    let transfer = last.and_then(|s| predicted_change(field, &raw, &s.step, s.halvings));
    let families = field.families_all();
    let mut external_step = vec![0i128; g.len()];
    for &(start, len, grain) in &families {
        for k in start..start + len {
            external_step[k] = deposit_step(first[k], second[k], grain, rates[k]);
        }
    }
    let external = predicted_change(field, &raw, &external_step, 0);
    for &(start, len, grain) in &families {
        for v in &mut g[start..start + len] {
            *v = on_step_grain(grain, *v);
        }
    }
    for ((m, v), gv) in first.iter_mut().zip(second.iter_mut()).zip(&g) {
        let square = gv.checked_mul(*gv).unwrap();
        if *m == 0 && *v == 0 {
            (*m, *v) = (*gv, square);
        } else {
            *m = toward(*m, *gv, FIRST_RATE);
            *v = toward(*v, square, SECOND_RATE);
        }
    }
    let mut step = vec![0i128; g.len()];
    match remainder {
        None => {
            for &(start, len, grain) in &families {
                for k in start..start + len {
                    step[k] = deposit_step(first[k], second[k], grain, rates[k]);
                }
            }
        }
        Some(remainder) => {
            for &(start, len, grain) in &families {
                for k in start..start + len {
                    let fine = deposit_step(first[k], second[k], grain + REMAINDER_BITS, rates[k]);
                    let sum = i128::from(remainder[k]) + fine;
                    let whole = sum >> REMAINDER_BITS;
                    remainder[k] = (sum - (whole << REMAINDER_BITS)) as i64;
                    step[k] = whole;
                }
            }
        }
    }
    let predicted = predicted_change(field, &raw, &step, 0);
    let parts = predicted_parts(field, &raw, &step, 0, parts);
    DepositPass { step, transfer, external, predicted, parts }
}

/// [realization; the lead, November 20] **The deposit in one pass is the serial passes bit for bit**: on a grown learner (a lane and four new
/// contacts, so the founded parts gather unlike entries) whose moments are open, with a covector drawn near the line's scale (some entries
/// zero, so a coordinate opens), the one-pass deposit ([`deposit_pass`]) forms the same step, moments, carried remainders and four prices as
/// the serial passes it replaced, with and without a step before to transfer and a remainder carried, and at entry rates that differ.
#[test]
fn the_deposit_in_one_pass_is_the_serial_passes_bit_for_bit() {
    let learner = grown_learner();
    let field = &learner.field;
    let n = field.material_len();
    let mut seed = 0x9e37_79b9_7f4a_7c15u64;
    let mut draw = move |bits: u32| -> i128 {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        let v = (seed >> (64 - bits)) as i128;
        if seed & 1 == 0 { -v } else { v }
    };
    let parts = learner.reading_parts();
    assert!(parts.iter().any(|&p| p != OLD_PART), "the grown learner holds founded parts");
    let mut read = 0;
    for (with_last, with_remainder) in [(false, false), (true, false), (false, true), (true, true)] {
        let g: Vec<i128> = (0..n).map(|k| if k % 11 == 3 { 0 } else { draw(44) }).collect();
        let rates: Vec<u32> = (0..n).map(|k| 6 + (k % 5) as u32).collect();
        let last = with_last.then(|| HeldStep { step: (0..n).map(|_| draw(20)).collect(), halvings: 1 });
        let mut first = learner.first.clone();
        let mut second = learner.second.clone();
        for k in (0..n).step_by(17) {
            (first[k], second[k]) = (0, 0);
        }
        let mut remainder: Vec<i64> = (0..n).map(|_| (draw(15) as i64).rem_euclid(1 << REMAINDER_BITS)).collect();
        let (mut f1, mut s1, mut r1) = (first.clone(), second.clone(), remainder.clone());
        let serial = deposit_serial(field, &g, &mut f1, &mut s1, &rates, with_remainder.then_some(&mut r1[..]), last.as_ref(), &parts);
        let pass = deposit_pass(&field.families_all(), &g, &mut first, &mut second, &rates, with_remainder.then_some(&mut remainder[..]), None, last.as_ref(), &parts).unwrap();
        assert_eq!(pass, serial, "last {with_last}, remainder {with_remainder}: the step and the prices");
        assert_eq!((first, second), (f1, s1), "last {with_last}, remainder {with_remainder}: the moments");
        assert_eq!(remainder, r1, "last {with_last}, remainder {with_remainder}: the remainders");
        assert!(pass.predicted.is_some() && pass.external.is_some() && pass.parts.is_some() && pass.transfer.is_some() == with_last);
        assert!(pass.step.iter().any(|&s| s != 0));
        read += 1;
    }
    eprintln!("DEPOSIT_PASS entries={n} read={read}");
    assert_eq!(read, 4);
}

/// [measurement; the lead, November 20] **The one-pass deposit on a line's saved state**: the learner at `DEPOSIT_STATE` (a store line's
/// state), a covector drawn at the line's scale, the serial passes and the one pass each timed three times, every bit compared. A reading on
/// the host; run with `DEPOSIT_STATE=… cargo test --release -p holonics-engine -- --ignored the_deposit_pass_on_a_lines_state`.
#[test]
#[ignore]
#[allow(clippy::disallowed_methods, reason = "an exterior reading of saved state files")]
fn the_deposit_pass_on_a_lines_state() {
    let path = std::env::var("DEPOSIT_STATE").expect("DEPOSIT_STATE names a learner's saved state");
    let learner = Learner::from_text(&std::fs::read_to_string(path).unwrap()).unwrap();
    let field = &learner.field;
    let n = field.material_len();
    let mut seed = 0x2545_f491_4f6c_dd1du64;
    let g: Vec<i128> = (0..n)
        .map(|_| {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            let v = (seed >> 20) as i128;
            if seed & 1 == 0 { -v } else { v }
        })
        .collect();
    let rates = learner.entry_rates();
    let parts = learner.reading_parts();
    let families = field.families_all();
    let last = HeldStep { step: learner.first.iter().map(|&m| m >> 40).collect(), halvings: 0 };
    let (mut serial_us, mut pass_us) = (Vec::new(), Vec::new());
    for _ in 0..3 {
        let (mut f1, mut s1, mut r1) = (learner.first.clone(), learner.second.clone(), learner.remainder.clone());
        let t = std::time::Instant::now();
        let serial = deposit_serial(field, &g, &mut f1, &mut s1, &rates, r1.as_deref_mut(), Some(&last), &parts);
        serial_us.push(t.elapsed().as_micros());
        let (mut f2, mut s2, mut r2) = (learner.first.clone(), learner.second.clone(), learner.remainder.clone());
        let t = std::time::Instant::now();
        let pass = deposit_pass(&families, &g, &mut f2, &mut s2, &rates, r2.as_deref_mut(), None, Some(&last), &parts).unwrap();
        pass_us.push(t.elapsed().as_micros());
        assert_eq!(pass, serial);
        assert_eq!((f1, s1, r1), (f2, s2, r2));
    }
    eprintln!("DEPOSIT_PASS_STATE entries={n} families={} remainder={} threads={} serial_us={serial_us:?} pass_us={pass_us:?}", families.len(), learner.remainder.is_some(), rayon::current_num_threads());
}

/// [measurement; the lead, November 20, the engineering report's item A5] **A census of the material's carriers**: on the learner at
/// `DEPOSIT_STATE`, each family of the layout (start, entries, grain) with the bits its largest entry needs and the bits at which 50%, 99%
/// and 99.9% of its entries stand (an entry's bits: the length of its magnitude, sign apart). A ruler on the host; no state changes. Run with
/// `DEPOSIT_STATE=… cargo test --release -p holonics-engine -- --ignored a_census_of_the_materials_carriers --nocapture`.
#[test]
#[ignore]
#[allow(clippy::disallowed_methods, reason = "an exterior reading of saved state files")]
fn a_census_of_the_materials_carriers() {
    let path = std::env::var("DEPOSIT_STATE").expect("DEPOSIT_STATE names a learner's saved state");
    let learner = Learner::from_text(&std::fs::read_to_string(path).unwrap()).unwrap();
    let field = &learner.field;
    let l = field.layout();
    let named = [("enc", l.enc), ("before", l.before), ("after", l.after), ("q", l.q), ("v", l.v), ("out", l.out), ("a", l.a), ("b", l.b), ("w", l.w), ("read", l.read), ("probe", l.probe), ("carry", l.carry), ("pump", l.pump), ("pace", l.pace), ("temper", l.temper), ("moment_before", l.moment_before), ("moment_after", l.moment_after), ("moment_face", l.moment_face)];
    let theta: Vec<i32> = field.material().copied().collect();
    let mut hist_all = [0u64; 33];
    for &(start, len, grain) in &field.families_all() {
        let mut hist = [0u64; 33];
        for &v in &theta[start..start + len] {
            hist[(32 - v.unsigned_abs().leading_zeros()) as usize] += 1;
        }
        for (a, h) in hist_all.iter_mut().zip(hist) {
            *a += h;
        }
        let at = |milli: u64| {
            let mut acc = 0u64;
            (0..33).find(|&b| {
                acc += hist[b];
                1000 * acc >= milli * len as u64
            }).unwrap_or(32)
        };
        let max = (0..33).rev().find(|&b| hist[b] > 0).unwrap_or(0);
        let name = named.iter().filter(|(_, at)| *at <= start).max_by_key(|(_, at)| *at).map_or("-", |(n, _)| n);
        eprintln!("CARRIER family_at={start} near={name} entries={len} grain={grain} max_bits={max} p50_bits={} p99_bits={} p999_bits={}", at(500), at(990), at(999));
    }
    let total: u64 = hist_all.iter().sum();
    let mut acc = 0u64;
    let cumulative: Vec<String> = (0..33).filter(|&b| hist_all[b] > 0).map(|b| {
        acc += hist_all[b];
        format!("{b}:{}/10000", acc * 10_000 / total)
    }).collect();
    eprintln!("CARRIER_ALL entries={total} cumulative_share_by_bits={}", cumulative.join(" "));
}

/// The bits each entry of `v` needs (its magnitude's length, sign apart): `(entries, max, p50, p99, p999)`.
fn census_bits<T: Copy + Into<i128>>(v: &[T]) -> (usize, u32, u32, u32, u32) {
    let mut hist = [0usize; 129];
    for &x in v {
        hist[(128 - x.into().unsigned_abs().leading_zeros()) as usize] += 1;
    }
    let n = v.len();
    let at = |milli: usize| {
        let mut acc = 0usize;
        (0..129u32).find(|&b| {
            acc += hist[b as usize];
            1000 * acc >= milli * n
        }).unwrap_or(128)
    };
    (n, (0..129u32).rev().find(|&b| hist[b as usize] > 0).unwrap_or(0), at(500), at(990), at(999))
}

/// [measurement; the lead, November 20, the engineering report's item A5, its operands] **A census of a pass's carriers**: the learner at
/// `DEPOSIT_STATE` reads one region of `CARRIER_SITES` sites cut from `CARRIER_TEXT` through the codec `CARRIER_CODEC` over the units
/// `CARRIER_UNITS`, about five places in eleven open, every tick kept; each carrier the card keeps a tick, the chart's read, the words, the
/// current, the contacts' operands, the carry circles' and the pump's, with the bits its entries need (the length of a magnitude). A ruler on
/// the host; no state changes.
#[test]
#[ignore]
#[allow(clippy::disallowed_methods, reason = "an exterior reading of saved state files")]
fn a_census_of_a_passes_carriers() {
    let var = |k: &str| std::env::var(k).unwrap_or_else(|_| panic!("{k} is not set"));
    let learner = Learner::from_text(&std::fs::read_to_string(var("DEPOSIT_STATE")).unwrap()).unwrap();
    let units = crate::units::Units::from_text(&std::fs::read_to_string(var("CARRIER_UNITS")).unwrap()).unwrap();
    let codec = crate::codec::Codec::from_text(&std::fs::read_to_string(var("CARRIER_CODEC")).unwrap(), units).unwrap();
    let sites: usize = var("CARRIER_SITES").parse().unwrap();
    let text = std::fs::read(var("CARRIER_TEXT")).unwrap();
    let mut classes = Vec::new();
    for line in text.split(|&b| b == b'\n') {
        let mut l = line.to_vec();
        l.push(b'\n');
        if let Ok(c) = codec.encode(&l) {
            classes.extend(c);
        }
        if classes.len() >= sites {
            break;
        }
    }
    classes.truncate(sites);
    let unresolved: Vec<bool> = (0..classes.len()).map(|t| (t * 7) % 11 < 5).collect();
    let region = Region { classes: &classes, unresolved: &unresolved, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None };
    let forward = learner.field.pass(&region, true).unwrap();
    let show = |name: &str, c: (usize, u32, u32, u32, u32)| eprintln!("PASS_CARRIER {name} entries={} max_bits={} p50_bits={} p99_bits={} p999_bits={}", c.0, c.1, c.2, c.3, c.4);
    show("read", census_bits(&forward.read));
    show("scale", census_bits(&forward.scale));
    show("lift", census_bits(&forward.lift));
    show("moment", census_bits(&forward.moment));
    for (k, tick) in forward.ticks.iter().enumerate() {
        let named: [(&str, &[i64]); 17] = [("before", &tick.before), ("after", &tick.after), ("word", &tick.word), ("vword", &tick.vword), ("probe", &tick.probe), ("q", &tick.q), ("v", &tick.v), ("pq", &tick.pq), ("y", &tick.y), ("a", &tick.a), ("b", &tick.b), ("c", &tick.c), ("qh", &tick.qh), ("gam", &tick.gam), ("kb", &tick.kb), ("qm", &tick.qm), ("ph", &tick.ph)];
        for (name, v) in named {
            if !v.is_empty() {
                show(&format!("tick{k}.{name}"), census_bits(v));
            }
        }
        show(&format!("tick{k}.eta"), census_bits(&tick.eta));
        show(&format!("tick{k}.read"), census_bits(&tick.read));
        show(&format!("tick{k}.read2"), census_bits(&tick.read2));
        show(&format!("tick{k}.scale"), census_bits(&tick.scale));
    }
    eprintln!("PASS_CARRIERS sites={} open={}", classes.len(), unresolved.iter().filter(|&&u| u).count());
}

/// [measurement; the lead, November 20, the hardware record §8's premise] **The trained tick's residual by tick**: the learner at
/// `DEPOSIT_STATE` with its ticks raised to `CARRIER_TICKS` reads one region of `CARRIER_SITES` sites cut from `CARRIER_TEXT` (as the census
/// of a pass's carriers cuts it), every tick kept; for each tick `k`, over the region's sites, the state's step `‖x^(k+1) − x^k‖` against
/// `‖x^k‖`, and the chart's step `‖r^(k+1) − r^k‖` (each site's chart, its lanes read as ratios to their powers) against `‖r^k‖`, each a sum of
/// squares over the sites (millionths), and the ratio of successive steps. A contraction shows steps falling by a steady factor under one; the
/// running mean (`tower.field-tick-running-mean`) shows `(k − 1)/(k + 1)`. A ruler on the host; no state changes.
#[test]
#[ignore]
#[allow(clippy::disallowed_methods, reason = "an exterior reading of saved state files")]
fn the_trained_ticks_residual_by_tick() {
    let var = |k: &str| std::env::var(k).unwrap_or_else(|_| panic!("{k} is not set"));
    let mut learner = Learner::from_text(&std::fs::read_to_string(var("DEPOSIT_STATE")).unwrap()).unwrap();
    let units = crate::units::Units::from_text(&std::fs::read_to_string(var("CARRIER_UNITS")).unwrap()).unwrap();
    let codec = crate::codec::Codec::from_text(&std::fs::read_to_string(var("CARRIER_CODEC")).unwrap(), units).unwrap();
    let sites: usize = var("CARRIER_SITES").parse().unwrap();
    let ticks: usize = var("CARRIER_TICKS").parse().unwrap();
    let text = std::fs::read(var("CARRIER_TEXT")).unwrap();
    let mut classes = Vec::new();
    for line in text.split(|&b| b == b'\n') {
        let mut l = line.to_vec();
        l.push(b'\n');
        if let Ok(c) = codec.encode(&l) {
            classes.extend(c);
        }
        if classes.len() >= sites {
            break;
        }
    }
    classes.truncate(sites);
    let unresolved: Vec<bool> = (0..classes.len()).map(|t| (t * 7) % 11 < 5).collect();
    let region = Region { classes: &classes, unresolved: &unresolved, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None };
    learner.field.declaration.ticks = ticks;
    let forward = learner.field.pass(&region, true).unwrap();
    let sq = |v: &[i64]| -> u128 { v.iter().map(|&x| (x as i128 * x as i128) as u128).sum() };
    let diff = |a: &[i64], b: &[i64]| -> u128 { a.iter().zip(b).map(|(&x, &y)| { let d = x as i128 - y as i128; (d * d) as u128 }).sum() };
    let (mut prev_state, mut prev_chart) = (0u128, 0u128);
    for (k, tick) in forward.ticks.iter().enumerate() {
        let (step, norm) = (diff(&tick.after, &tick.before), sq(&tick.before).max(1));
        let chart_now: Vec<i64> = tick.read.iter().map(|&v| i64::from(v)).collect();
        let chart_next: Option<Vec<i64>> = forward.ticks.get(k + 1).map(|n| n.read.iter().map(|&v| i64::from(v)).collect());
        let (cstep, cnorm) = chart_next.as_ref().map_or((0, 1), |n| (diff(n, &chart_now), sq(&chart_now).max(1)));
        let ratio = |now: u128, before: u128| if before == 0 { "-".to_string() } else { format!("{}", now * 1000 / before) };
        eprintln!("TICK_RESIDUAL k={k} state_step_over_state_micro={} state_step_ratio_milli={} chart_step_over_chart_micro={} chart_step_ratio_milli={}", step * 1_000_000 / norm, ratio(step, prev_state), cstep * 1_000_000 / cnorm, ratio(cstep, prev_chart));
        (prev_state, prev_chart) = (step, cstep);
    }
    eprintln!("TICK_RESIDUALS sites={} open={} ticks={ticks}", classes.len(), unresolved.iter().filter(|&&u| u).count());
}

/// [measurement; the lead, November 21, the lattice record §6.1's read before any leak is built] **The tick's gains by finite differences**:
/// the learner at `DEPOSIT_STATE`, its ticks raised past the largest of `PROBE_TICKS`, reads one region of `CARRIER_SITES` sites cut from
/// `CARRIER_TEXT` (as the census of a pass's carriers cuts it). At each tick `k` of `PROBE_TICKS` and each site `t` of `PROBE_SITES`, every
/// entry `d` of the site's state is moved by `±ε` (`ε` a lane's root mean square released by ten bits, at least `2^6`) and the perturbed
/// state run through that one tick with the tick's own operands; the site's own block of the state after the tick, `x⁺ − x⁻`, is written
/// to `PROBE_OUT/probe_k{k}_t{t}.txt` with the opening and settled blocks and each entry's `ε`, for the host's eigenvalues (`tools/tick_gains.py`).
/// A ruler on the host; no state changes.
#[test]
#[ignore]
#[allow(clippy::disallowed_methods, reason = "an exterior reading of saved state files and a write of the ruler's tables")]
fn the_ticks_gains_by_finite_differences() {
    let var = |k: &str| std::env::var(k).unwrap_or_else(|_| panic!("{k} is not set"));
    let mut learner = Learner::from_text(&std::fs::read_to_string(var("DEPOSIT_STATE")).unwrap()).unwrap();
    let units = crate::units::Units::from_text(&std::fs::read_to_string(var("CARRIER_UNITS")).unwrap()).unwrap();
    let codec = crate::codec::Codec::from_text(&std::fs::read_to_string(var("CARRIER_CODEC")).unwrap(), units).unwrap();
    let sites: usize = var("CARRIER_SITES").parse().unwrap();
    let at: Vec<usize> = var("PROBE_TICKS").split(',').map(|v| v.parse().unwrap()).collect();
    let probed: Vec<usize> = var("PROBE_SITES").split(',').map(|v| v.parse().unwrap()).collect();
    let out = std::path::PathBuf::from(var("PROBE_OUT"));
    let text = std::fs::read(var("CARRIER_TEXT")).unwrap();
    let mut classes = Vec::new();
    for line in text.split(|&b| b == b'\n') {
        let mut l = line.to_vec();
        l.push(b'\n');
        if let Ok(c) = codec.encode(&l) {
            classes.extend(c);
        }
        if classes.len() >= sites {
            break;
        }
    }
    classes.truncate(sites);
    let unresolved: Vec<bool> = (0..classes.len()).map(|t| (t * 7) % 11 < 5).collect();
    let region = Region { classes: &classes, unresolved: &unresolved, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None };
    learner.field.declaration.ticks = at.iter().max().unwrap() + 1;
    let dw = learner.field.declaration.width;
    let lanes = learner.field.declaration.lanes;
    let lw = dw / lanes;
    let eps_of = |x: &[i64], t: usize| -> Vec<i64> {
        (0..dw).map(|d| {
            let l = d / lw;
            let ss: i128 = x[t * dw + l * lw..t * dw + (l + 1) * lw].iter().map(|&v| i128::from(v) * i128::from(v)).sum();
            let rms = ((ss / lw as i128) as u128).isqrt() as i64;
            (rms >> 10).max(64)
        }).collect()
    };
    for &k in &at {
        let t0 = std::time::Instant::now();
        let perturb = |x: &[i64]| -> Vec<Vec<(usize, i64)>> {
            let mut all = Vec::new();
            for &t in &probed {
                let eps = eps_of(x, t);
                for d in 0..dw {
                    all.push(vec![(t * dw + d, eps[d])]);
                    all.push(vec![(t * dw + d, -eps[d])]);
                }
            }
            all
        };
        let mut probe = crate::contact::TickProbe { at: k, perturb: &perturb, before: Vec::new(), after: Vec::new(), outputs: Vec::new() };
        learner.field.pass_probed(&region, &mut probe).unwrap();
        assert_eq!(probe.outputs.len(), probed.len() * 2 * dw, "the probe ran at tick {k}");
        for (n, &t) in probed.iter().enumerate() {
            let eps = eps_of(&probe.before, t);
            let block = |v: &[i64]| v[t * dw..(t + 1) * dw].iter().map(i64::to_string).collect::<Vec<_>>().join(" ");
            let mut s = format!("k {k} t {t} dw {dw} lanes {lanes} open {}\n", u8::from(unresolved[t]));
            s += &format!("before {}\nafter {}\neps {}\n", block(&probe.before), block(&probe.after), eps.iter().map(i64::to_string).collect::<Vec<_>>().join(" "));
            for d in 0..dw {
                let (p, m) = (&probe.outputs[(n * dw + d) * 2], &probe.outputs[(n * dw + d) * 2 + 1]);
                let col: Vec<String> = (0..dw).map(|e| (p[t * dw + e] - m[t * dw + e]).to_string()).collect();
                s += &format!("col {d} {}\n", col.join(" "));
            }
            std::fs::write(out.join(format!("probe_k{k}_t{t}.txt")), s).unwrap();
        }
        eprintln!("TICK_PROBE k={k} sites={} probes={} ms={}", probed.len(), probe.outputs.len(), t0.elapsed().as_millis());
    }
    eprintln!("TICK_PROBES region_sites={} open={} ticks={:?} sites={probed:?}", classes.len(), unresolved.iter().filter(|&&u| u).count(), at);
}

/// [measurement; the lead, November 21, the news write's premise] **A leak's first deposit against the tick's gains**: a leak `x ← x + g(x) − Λ x`
/// founded at `Λ = 0` reads every bit of the built tick, and its first descent is `ΔΛ ∝ M = Σ_(t,k) λ_t^(k+1) (x_t^k)ᵀ` (the covector each
/// tick's return receives against the state the tick began from). The learner at `DEPOSIT_STATE` at its own declared ticks reads one region of
/// `CARRIER_SITES` sites cut from `CARRIER_TEXT`, returns it, and writes `M` over the region (`grad_all.txt`) and each `PROBE_SITES` site's own
/// (`grad_t{t}.txt`), with the tick's own block at its last tick by central differences (`probe_k{K−1}_t{t}.txt`, as
/// `the_ticks_gains_by_finite_differences` writes it), for `tools/tick_gains.py --leak`. A ruler on the host; no state changes.
#[test]
#[ignore]
#[allow(clippy::disallowed_methods, reason = "an exterior reading of saved state files and a write of the ruler's tables")]
fn a_leaks_first_deposit_against_the_ticks_gains() {
    let var = |k: &str| std::env::var(k).unwrap_or_else(|_| panic!("{k} is not set"));
    let learner = Learner::from_text(&std::fs::read_to_string(var("DEPOSIT_STATE")).unwrap()).unwrap();
    let units = crate::units::Units::from_text(&std::fs::read_to_string(var("CARRIER_UNITS")).unwrap()).unwrap();
    let codec = crate::codec::Codec::from_text(&std::fs::read_to_string(var("CARRIER_CODEC")).unwrap(), units).unwrap();
    let sites: usize = var("CARRIER_SITES").parse().unwrap();
    let probed: Vec<usize> = var("PROBE_SITES").split(',').map(|v| v.parse().unwrap()).collect();
    let out = std::path::PathBuf::from(var("PROBE_OUT"));
    let text = std::fs::read(var("CARRIER_TEXT")).unwrap();
    let mut classes = Vec::new();
    for line in text.split(|&b| b == b'\n') {
        let mut l = line.to_vec();
        l.push(b'\n');
        if let Ok(c) = codec.encode(&l) {
            classes.extend(c);
        }
        if classes.len() >= sites {
            break;
        }
    }
    classes.truncate(sites);
    let unresolved: Vec<bool> = (0..classes.len()).map(|t| (t * 7) % 11 < 5).collect();
    let region = Region { classes: &classes, unresolved: &unresolved, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None };
    let field = &learner.field;
    let (dw, lanes, ticks) = (field.declaration.width, field.declaration.lanes, field.declaration.ticks);
    let pass = field.pass(&region, true).unwrap();
    let mut g = vec![0i128; field.material_len()];
    let mut lams: Vec<Vec<i64>> = Vec::new();
    field.returned_with(&region, &pass, &mut g, None, None, None, None, Some(&mut lams), None, None).unwrap();
    assert_eq!(lams.len(), pass.ticks.len(), "one covector a tick");
    let outer = |ts: &[usize]| -> Vec<i128> {
        let mut m = vec![0i128; dw * dw];
        for (i, lam) in lams.iter().enumerate() {
            let k = pass.ticks.len() - 1 - i;
            let x = &pass.ticks[k].before;
            for &t in ts {
                let (l, xs) = (&lam[t * dw..(t + 1) * dw], &x[t * dw..(t + 1) * dw]);
                for d in 0..dw {
                    for e in 0..dw {
                        m[d * dw + e] += i128::from(l[d]) * i128::from(xs[e]);
                    }
                }
            }
        }
        m
    };
    let write = |name: &str, m: &[i128]| {
        let s: String = (0..dw).map(|d| m[d * dw..(d + 1) * dw].iter().map(i128::to_string).collect::<Vec<_>>().join(" ") + "\n").collect();
        std::fs::write(out.join(name), s).unwrap();
    };
    let all: Vec<usize> = (0..classes.len()).collect();
    write("grad_all.txt", &outer(&all));
    for &t in &probed {
        write(&format!("grad_t{t}.txt"), &outer(&[t]));
    }
    // The tick's own block at its last tick, as the gains' ruler writes it.
    let lw = dw / lanes;
    let eps_of = |x: &[i64], t: usize| -> Vec<i64> {
        (0..dw).map(|d| {
            let l = d / lw;
            let ss: i128 = x[t * dw + l * lw..t * dw + (l + 1) * lw].iter().map(|&v| i128::from(v) * i128::from(v)).sum();
            ((ss / lw as i128) as u128).isqrt() as i64 >> 10
        }).map(|e| e.max(64)).collect()
    };
    let k = ticks - 1;
    let perturb = |x: &[i64]| -> Vec<Vec<(usize, i64)>> {
        let mut all = Vec::new();
        for &t in &probed {
            let eps = eps_of(x, t);
            for (d, &e) in eps.iter().enumerate() {
                all.push(vec![(t * dw + d, e)]);
                all.push(vec![(t * dw + d, -e)]);
            }
        }
        all
    };
    let mut probe = crate::contact::TickProbe { at: k, perturb: &perturb, before: Vec::new(), after: Vec::new(), outputs: Vec::new() };
    field.pass_probed(&region, &mut probe).unwrap();
    for (n, &t) in probed.iter().enumerate() {
        let eps = eps_of(&probe.before, t);
        let block = |v: &[i64]| v[t * dw..(t + 1) * dw].iter().map(i64::to_string).collect::<Vec<_>>().join(" ");
        let mut s = format!("k {k} t {t} dw {dw} lanes {lanes} open {}\n", u8::from(unresolved[t]));
        s += &format!("before {}\nafter {}\neps {}\n", block(&probe.before), block(&probe.after), eps.iter().map(i64::to_string).collect::<Vec<_>>().join(" "));
        for d in 0..dw {
            let (p, m) = (&probe.outputs[(n * dw + d) * 2], &probe.outputs[(n * dw + d) * 2 + 1]);
            let col: Vec<String> = (0..dw).map(|e| (p[t * dw + e] - m[t * dw + e]).to_string()).collect();
            s += &format!("col {d} {}\n", col.join(" "));
        }
        std::fs::write(out.join(format!("probe_k{k}_t{t}.txt")), s).unwrap();
    }
    eprintln!("LEAK_PREMISE sites={} open={} ticks={ticks} probed={probed:?}", classes.len(), unresolved.iter().filter(|&&u| u).count());
}

/// [measurement; the lead, November 21, the lattice record §6.2's read] **A part's transport for its polygons**: the learner at `DEPOSIT_STATE`
/// writes its site maps, each a block of the material read as rows by columns (`affine`'s layout: `read` `D × D`, `out` `D × 2M`, `q` and `v`
/// `2M × D`, `a` and `b` `f × D`, `w` `D × f`), to `PROBE_OUT/map_{name}.txt` (a line `rows cols`, then the entries), for the polygons of their
/// one-step gains (`tools/tick_gains.py --polygons`). A ruler on the host; no state changes.
#[test]
#[ignore]
#[allow(clippy::disallowed_methods, reason = "an exterior reading of a saved state file and a write of the ruler's tables")]
fn a_parts_transport_for_its_polygons() {
    let var = |k: &str| std::env::var(k).unwrap_or_else(|_| panic!("{k} is not set"));
    let learner = Learner::from_text(&std::fs::read_to_string(var("DEPOSIT_STATE")).unwrap()).unwrap();
    let out = std::path::PathBuf::from(var("PROBE_OUT"));
    let field = &learner.field;
    let (dw, f, m2) = (field.declaration.width, field.declaration.contacts, 2 * field.declaration.complex());
    let l = field.layout();
    for (name, at, rows, cols) in [("read", l.read, dw, dw), ("out", l.out, dw, m2), ("q", l.q, m2, dw), ("v", l.v, m2, dw), ("a", l.a, f, dw), ("b", l.b, f, dw), ("w", l.w, dw, f)] {
        let block = &field.theta[at..at + rows * cols];
        let mut s = format!("{rows} {cols}\n");
        for r in 0..rows {
            s += &block[r * cols..(r + 1) * cols].iter().map(i32::to_string).collect::<Vec<_>>().join(" ");
            s.push('\n');
        }
        std::fs::write(out.join(format!("map_{name}.txt")), s).unwrap();
    }
    eprintln!("PART_MAPS width={dw} contacts={f} m2={m2} lanes={}", field.declaration.lanes);
}

/// [measurement; the lead, November 21, the lattice record §6.3's read] **The fork's closing orders on the carry circles**: three pairs opened
/// in one order, `([{`, closed in each of the six orders of `)]}`, inside one filler of `FORK_FILLERS` (`{f}` in each line of fillers is
/// replaced by the brackets), each a region of its own through the codec; at the region's last site (the line's end) the last tick's scan
/// operand `Q(t − 1)` of every circle is written, with the order and its crossings (inversions against the nested order), for the pumped
/// state as it stands and with the pump's chart and bias at zero (`p = 0`, so `η = 0`: the unpumped circles), to `PROBE_OUT/fork_{pumped,
/// unpumped}.txt` (`tools/tick_gains.py --fork`). A ruler on the host; no state changes.
#[test]
#[ignore]
#[allow(clippy::disallowed_methods, reason = "an exterior reading of saved state files and a write of the ruler's tables")]
fn the_forks_closing_orders_on_the_carry_circles() {
    let var = |k: &str| std::env::var(k).unwrap_or_else(|_| panic!("{k} is not set"));
    let learner = Learner::from_text(&std::fs::read_to_string(var("DEPOSIT_STATE")).unwrap()).unwrap();
    let units = crate::units::Units::from_text(&std::fs::read_to_string(var("CARRIER_UNITS")).unwrap()).unwrap();
    let codec = crate::codec::Codec::from_text(&std::fs::read_to_string(var("CARRIER_CODEC")).unwrap(), units).unwrap();
    let fillers: Vec<String> = std::fs::read_to_string(var("FORK_FILLERS")).unwrap().lines().filter(|l| l.contains("{f}")).map(str::to_string).collect();
    let out = std::path::PathBuf::from(var("PROBE_OUT"));
    let closers = [b')', b']', b'}'];
    let orders: [[usize; 3]; 6] = [[2, 1, 0], [1, 2, 0], [2, 0, 1], [0, 2, 1], [1, 0, 2], [0, 1, 2]];
    let mut unpumped = learner.field.clone();
    {
        let (l, c2, dw) = (unpumped.layout().clone(), 2 * unpumped.declaration.carry, unpumped.declaration.width);
        assert!(unpumped.declaration.pump, "the state's circles are pumped");
        for v in &mut unpumped.theta[l.pump..l.pump + c2 * dw] {
            *v = 0;
        }
        for v in &mut unpumped.theta[l.pump_bias..l.pump_bias + c2] {
            *v = 0;
        }
    }
    for (name, field) in [("pumped", &learner.field), ("unpumped", &unpumped)] {
        let mut s = String::new();
        let mut n = 0usize;
        for (fi, filler) in fillers.iter().enumerate() {
            for (oi, order) in orders.iter().enumerate() {
                // The nested order closes `}` `]` `)`: its closers' ranks 2, 1, 0; crossings are the inversions against it.
                let crossings = (0..3).flat_map(|a| ((a + 1)..3).map(move |b| (a, b))).filter(|&(a, b)| order[a] < order[b]).count();
                let brackets: Vec<u8> = b"([{".iter().copied().chain(order.iter().map(|&c| closers[c])).collect();
                let line = filler.replace("{f}", std::str::from_utf8(&brackets).unwrap()) + "\n";
                let Ok(classes) = codec.encode(line.as_bytes()) else { continue };
                let unresolved = vec![false; classes.len()];
                let region = Region { classes: &classes, unresolved: &unresolved, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None };
                let pass = field.pass(&region, true).unwrap();
                let last = pass.ticks.last().unwrap();
                let c2 = 2 * field.declaration.carry;
                let t = classes.len() - 1;
                let q = &last.qm[t * c2..(t + 1) * c2];
                s += &format!("filler {fi} order {oi} crossings {crossings} sites {} q {}\n", classes.len(), q.iter().map(i64::to_string).collect::<Vec<_>>().join(" "));
                n += 1;
            }
        }
        std::fs::write(out.join(format!("fork_{name}.txt")), s).unwrap();
        eprintln!("FORK {name} samples={n} fillers={} circles={}", fillers.len(), field.declaration.carry);
    }
}

/// [measurement; the lead, November 21, the reads B1 to B5 and F3 the leak's founding record offers] **A lane leak's reads at set strengths**:
/// the learner at `DEPOSIT_STATE` reads one region of `CARRIER_SITES` sites cut from `CARRIER_TEXT` (as the census of a pass's carriers cuts
/// it) with its ticks raised to `LEAK_TICKS` and the ruler's lane leak `x ← (1 − δ)x + g` at each `δ = n 2^(−b)` of `LEAK_DELTAS` (`n/b` pairs),
/// and once at the line's own declared ticks with no leak. For each read and each face lane: the moves `m_k = r^(k+1) − r^k` of every site's chart
/// (`tick.read`), their pooled cosine `Σ⟨m_k, m_(k−1)⟩ / Σ‖m_k‖‖m_(k−1)‖` over the ticks of a span, and each tick's pooled move `(Σ‖m_k‖²)^½`; the
/// held code over the open sites (nats a place, from the faces); and, at the line's own read, each circle's gate `γ` at every site (`tick.gam`,
/// `2^(−30)`). Written as lines to stderr. A ruler on the host; no state changes.
#[test]
#[ignore]
#[allow(clippy::disallowed_methods, reason = "an exterior reading of saved state files")]
#[allow(clippy::disallowed_types, reason = "a ruler's cosines and codes are reported on the host as floats")]
fn a_lane_leaks_reads_at_set_strengths() {
    let var = |k: &str| std::env::var(k).unwrap_or_else(|_| panic!("{k} is not set"));
    let learner = Learner::from_text(&std::fs::read_to_string(var("DEPOSIT_STATE")).unwrap()).unwrap();
    let units = crate::units::Units::from_text(&std::fs::read_to_string(var("CARRIER_UNITS")).unwrap()).unwrap();
    let codec = crate::codec::Codec::from_text(&std::fs::read_to_string(var("CARRIER_CODEC")).unwrap(), units).unwrap();
    let sites: usize = var("CARRIER_SITES").parse().unwrap();
    let ticks: usize = var("LEAK_TICKS").parse().unwrap();
    let deltas: Vec<(i64, u32)> = var("LEAK_DELTAS").split(',').map(|p| { let (n, b) = p.split_once('/').unwrap(); (n.parse().unwrap(), b.parse().unwrap()) }).collect();
    let text = std::fs::read(var("CARRIER_TEXT")).unwrap();
    let mut classes = Vec::new();
    for line in text.split(|&b| b == b'\n') {
        let mut l = line.to_vec();
        l.push(b'\n');
        if let Ok(c) = codec.encode(&l) {
            classes.extend(c);
        }
        if classes.len() >= sites {
            break;
        }
    }
    classes.truncate(sites);
    let unresolved: Vec<bool> = (0..classes.len()).map(|t| (t * 7) % 11 < 5).collect();
    let region = Region { classes: &classes, unresolved: &unresolved, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None };
    let (dw, lanes) = (learner.field.declaration.width, learner.field.declaration.lanes);
    let lw = dw / lanes;
    let read = |tag: &str, field: &Constitution| {
        let pass = field.pass(&region, true).unwrap();
        let n = pass.ticks.len();
        // moves m_k for k in 0..n-1, per site and lane
        let mv = |k: usize, t: usize, l: usize| -> Vec<f64> {
            let (a, b) = (&pass.ticks[k].read, &pass.ticks[k + 1].read);
            (0..lw).map(|i| f64::from(b[t * dw + l * lw + i]) - f64::from(a[t * dw + l * lw + i])).collect()
        };
        let span_cos = |from: usize, to: usize, l: usize| -> f64 {
            let (mut num, mut den) = (0.0, 0.0);
            for k in from.max(1)..to.min(n - 1) {
                for t in 0..classes.len() {
                    let (p, q) = (mv(k - 1, t, l), mv(k, t, l));
                    num += p.iter().zip(&q).map(|(x, y)| x * y).sum::<f64>();
                    den += p.iter().map(|x| x * x).sum::<f64>().sqrt() * q.iter().map(|x| x * x).sum::<f64>().sqrt();
                }
            }
            if den > 0.0 { num / den } else { f64::NAN }
        };
        let norm = |k: usize, l: usize| -> f64 { (0..classes.len()).map(|t| mv(k, t, l).iter().map(|x| x * x).sum::<f64>()).sum::<f64>().sqrt() };
        let lanes_cos = |from: usize, to: usize| (0..lanes).map(|l| format!("{:.3}", span_cos(from, to, l))).collect::<Vec<_>>().join(" ");
        let norms: Vec<String> = (0..n - 1).map(|k| format!("{:.0}", (0..lanes).map(|l| norm(k, l).powi(2)).sum::<f64>().sqrt())).collect();
        let lane_growth: Vec<String> = (0..lanes).map(|l| if n > 16 { format!("{:.3}", norm(15, l) / norm(5, l)) } else { "-".into() }).collect();
        let (mut code, mut open) = (0.0, 0usize);
        for t in 0..classes.len() {
            if let (true, Some(face)) = (unresolved[t], pass.faces[t].as_ref()) {
                code += face.code(classes[t]) as f64 / f64::from(1u32 << 20) * std::f64::consts::LN_2;
                open += 1;
            }
        }
        eprintln!("LEAK_READ {tag} ticks={n} cos_ticks_1_to_16_by_lane=[{}] cos_ticks_5_to_16_by_lane=[{}] cos_all_by_lane=[{}] move_by_tick=[{}] move_16_over_move_6_by_lane=[{}] held_code_nats={:.4} open={open}",
            lanes_cos(1, 17), lanes_cos(5, 17), lanes_cos(1, n), norms.join(" "), lane_growth.join(" "), code / open.max(1) as f64);
        let by_pair: Vec<String> = (1..n - 1).map(|k| format!("{k}:{}", (0..lanes).map(|l| format!("{:.3}", span_cos(k, k + 1, l))).collect::<Vec<_>>().join(","))).collect();
        eprintln!("LEAK_PAIRS {tag} cos_by_pair_of_moves(k-1,k)_by_lane=[{}]", by_pair.join(" "));
        pass
    };
    let own = read("own_ticks_no_leak", &learner.field);
    // F3: the circles' gates at the line's own read, every site and circle, the last tick.
    let c2 = 2 * learner.field.declaration.carry;
    if c2 > 0 {
        let gam = &own.ticks.last().unwrap().gam;
        let c = c2 / 2;
        let (mut mags, mut near_third) = (Vec::new(), 0usize);
        for t in 0..classes.len() {
            for k in 0..c {
                let (re, im) = (gam[t * c2 + k] as f64 / f64::from(1u32 << 30), gam[t * c2 + c + k] as f64 / f64::from(1u32 << 30));
                let m = re.hypot(im);
                mags.push(m);
                let arg = im.atan2(re).abs();
                if (arg - 2.0 * std::f64::consts::PI / 3.0).abs() < 0.3 && m.powi(3) > 0.5 {
                    near_third += 1;
                }
            }
        }
        mags.sort_by(f64::total_cmp);
        let q = |p: f64| mags[((mags.len() - 1) as f64 * p) as usize];
        eprintln!("LEAK_F3 circles={c} gates={} median_abs_gamma={:.3} p10={:.3} p90={:.3} share_near_a_third_turn_with_abs3_over_half={:.4}", mags.len(), q(0.5), q(0.1), q(0.9), near_third as f64 / mags.len() as f64);
    }
    let mut raised = learner.field.clone();
    raised.declaration.ticks = ticks;
    read("raised_no_leak", &raised);
    // [the formal thread, 03:04Z] The law itself at stores given by lane (`LEAK_LAW_DELTAS`, each `δ` in millionths), the opening held.
    if let Ok(list) = std::env::var("LEAK_LAW_DELTAS") {
        let (mut f, _) = raised.with_lane_leak().unwrap();
        let at = f.layout.lane_leak;
        let ds: Vec<i64> = list.split(',').map(|v| v.parse().unwrap()).collect();
        for (l, &dm) in ds.iter().enumerate() {
            // d = δ/(1 − δ) on the face's grain
            f.theta[at + l] = ((dm << FACE_BITS) / (1_000_000 - dm)) as i32;
        }
        read(&format!("law_at_deltas_millionths_{list}"), &f);
    }
    let hold = std::env::var("LEAK_HOLD").is_ok_and(|v| v == "1");
    for &(n, b) in &deltas {
        let mut f = raised.clone();
        f.ruler_leak = Some((n, b));
        f.ruler_leak_hold = hold;
        read(&format!("raised_delta_{n}/2^{b}{}", if hold { "_opening_held" } else { "" }), &f);
    }
}

/// [definition; the formal thread, November 21 (the record of the store's leak, §3)] **The lane leak founded at zero keeps every face and the
/// built reverse**: grown onto a field (plain, with carry circles, with the opening's lift, and a tower), the stores are zero, every face is the
/// source's, the code's covector is the source's on every standing entry, and the stores' covector, the store's own news, is
/// `−Σ ⟨Δr̂^k, Δr̂^(k−1)⟩` released by the face's grain, read here from the pass's charts directly; the head line is `hnn-field-v14q` and
/// round-trips (with and without the pump); a second growth is refused.
#[test]
fn the_lane_leak_founded_at_zero_keeps_every_face_and_the_built_reverse() {
    let mut fields: Vec<(&str, Constitution)> = Vec::new();
    for still in [0usize, 1, 2] {
        fields.push(("four ticks", four_ticks(still)));
        fields.push(("carry", circled_shaped(still)));
        fields.push(("opened", opened(still)));
        fields.push(("tower", towered_live(still)));
    }
    for (name, plain) in &fields {
        let (grown, from) = plain.with_lane_leak().unwrap();
        let (d, l) = (grown.declaration, grown.layout.clone());
        assert!(d.lane_leak && !plain.declaration.lane_leak);
        assert_eq!(l.lane_leak, plain.theta.len(), "{name}: the stores at the fine field's end");
        assert!(grown.theta[l.lane_leak..l.lane_leak + d.lanes].iter().all(|&v| v == 0), "{name}: founded at zero");
        assert_eq!(from.iter().flatten().count(), plain.material_len(), "{name}: every standing entry kept");
        let r = region();
        assert_eq!(grown.faces(&r).unwrap(), plain.faces(&r).unwrap(), "{name}: every face kept");
        let (g, h) = (tower_covector(&grown, &r), tower_covector(plain, &r));
        for (n, o) in from.iter().enumerate() {
            if let Some(o) = o {
                assert_eq!(g[n], h[*o], "{name}: the covector of standing entry {o}");
            }
        }
        // The stores' covector from the charts: one read's (the field's single read; a marked field's both reads are meaned).
        if !grown.declaration.mark {
            let pass = grown.pass(&r, true).unwrap();
            let (dw, lanes) = (d.width, d.lanes);
            let lw = dw / lanes;
            let sites = r.classes.len();
            let mut charts: Vec<Vec<i32>> = pass.ticks.iter().map(|c| c.read.clone()).collect();
            let mut end = Vec::new();
            for t in 0..sites {
                let (mut rr, mut sc) = (Vec::new(), Vec::new());
                crate::contact::lane_chart(&pass.ticks.last().unwrap().after[t * dw..(t + 1) * dw], lanes, &mut rr, &mut sc).unwrap();
                end.extend(rr);
            }
            charts.push(end);
            for lane in 0..lanes {
                let mut ip = 0i128;
                for k in 1..charts.len() - 1 {
                    for t in 0..sites {
                        for i in t * dw + lane * lw..t * dw + (lane + 1) * lw {
                            ip += (i128::from(charts[k][i]) - i128::from(charts[k - 1][i])) * (i128::from(charts[k + 1][i]) - i128::from(charts[k][i]));
                        }
                    }
                }
                let mut gg = vec![0i128; grown.material_len()];
                grown.returned(&r, &pass, &mut gg).unwrap();
                assert_eq!(gg[l.lane_leak + lane], -release(ip, FACE_BITS), "{name}: lane {lane}'s store covector is its successive moves' pairing");
            }
        }
        let text = d.to_text();
        assert!(text.starts_with("hnn-field-v14q "), "{name}: {text}");
        assert_eq!(Declaration::from_text(&text).unwrap(), d);
        assert!(grown.with_lane_leak().is_err(), "{name}: a second growth");
    }
    // With the pump: the v14q line carries the pump's word as one.
    let pumped = Declaration { pump: true, lane_leak: true, friction: false, friction_gate: false, ..circled_shaped(1).declaration };
    assert_eq!(Declaration::from_text(&pumped.to_text()).unwrap(), pumped);
    let line = pumped.to_text();
    assert!(Declaration::from_text(&format!("{} 0", &line[..line.len() - 2])).is_err(), "a leak word of zero");
}

/// [definition; the formal thread, November 21] **The lane leak's return matches its code's difference**: on fields of four ticks with the
/// stores drawn off zero (so every lane leaks, `δ` from about a tenth to a half), the code's covector predicts the code's central difference at
/// the entries with the largest covector of each family but the stores' (whose covector is their own news, not the code's), as the carry's and
/// the junction's covector tests read it: so the leak's `−δ λ^(k+1)` into the state each tick began from is the reverse of its forward.
#[test]
fn the_lane_leaks_return_matches_its_codes_difference() {
    let (mut read, mut seams) = (0usize, 0usize);
    for still in [0usize, 1, 2] {
        let (mut field, _) = four_ticks(still).with_lane_leak().unwrap();
        let l = field.layout.clone();
        let lanes = field.declaration.lanes;
        for (n, v) in field.theta[l.lane_leak..l.lane_leak + lanes].iter_mut().enumerate() {
            *v = (1 << 13) + (n as i32) * (1 << 14);
        }
        let r = region();
        let g = covector_of(&field, &r);
        let sheets = |f: &Constitution| -> Vec<Vec<u32>> {
            let p = f.pass(&r, true).unwrap();
            p.ticks.iter().flat_map(|c| c.classes.iter().map(|cl| cl.off.iter().chain(&cl.members).copied().chain(cl.probes.iter().flat_map(|p| std::iter::once(u32::MAX).chain(p.iter().copied()))).collect())).collect()
        };
        assert_ne!(field.faces(&r).unwrap(), four_ticks(still).faces(&r).unwrap(), "still {still}: the leak moves the faces");
        for &(start, len, grain) in field.families() {
            if start == l.temper || start == l.lane_leak {
                continue;
            }
            let natural: u32 = if grain == MATERIAL_BITS { 40 } else { 24 };
            let mut entries: Vec<usize> = (start..start + len).collect();
            entries.sort_by_key(|&i| std::cmp::Reverse(g[i].unsigned_abs()));
            for i in entries.into_iter().take(3).filter(|&i| g[i] != 0) {
                let moved = |delta: i32| {
                    let mut f = field.clone();
                    f.theta[i] += delta;
                    f
                };
                let straddles = |delta: i32| sheets(&moved(delta)) != sheets(&field) || sheets(&moved(-delta)) != sheets(&field);
                let shift = natural + grain - 20;
                let Some((delta, h)) = probe_step(grain, &|delta: i32| (g[i] * 2 * delta as i128) >> shift, &straddles) else {
                    seams += 1;
                    continue;
                };
                read += 1;
                let measured = moved(delta).code(&r).unwrap().0 - moved(-delta).code(&r).unwrap().0;
                let predicted = (g[i] * 2 * delta as i128) >> shift;
                let tolerance = predicted.abs() / 8 + (64 << h);
                assert!((measured as i128 - predicted).abs() <= tolerance, "still {still} family at {start} (grain {grain}) entry {i} at {h} halvings: measured {measured}, predicted {predicted}");
            }
        }
    }
    eprintln!("LANE_LEAK_COVECTOR_PROBES read={read} on_a_seam={seams}");
    assert!(read > 0 && 16 * seams <= read, "read {read} probes, {seams} on a seam");
}

/// [measurement; the lead, November 21, the formal thread's read S4 (04:04Z)] **The circles' successive news**: the learner at `DEPOSIT_STATE`
/// reads one region of `CARRIER_SITES` sites cut from `CARRIER_TEXT` at its own ticks; at each site the circle's news is the part of its move the
/// turn does not carry, `u(t) = Q(t) − γ̂(t) Q(t∓1)` with `γ̂ = γ/|γ|` the gate's unit turn (`Q(t)` the scan's state after the site, the operand the
/// next site in the scan's order holds), the tracker's `δ n(t)` (with the pump's reflection beside it where the circles are pumped); and by
/// circle the pooled cosine of successive news along its scan, `Σ Re(ū(t) γ̂(t) u(t∓1)) / Σ |u(t)| |u(t∓1)|`, over the sites and the pass's ticks
/// (and the last tick alone). Lines to stderr: the circles' median, quartiles and the share above `+0.10`. A ruler on the host; no state changes.
#[test]
#[ignore]
#[allow(clippy::disallowed_methods, reason = "an exterior reading of saved state files")]
#[allow(clippy::disallowed_types, reason = "a ruler's cosines are reported on the host as floats")]
fn the_circles_successive_news() {
    let var = |k: &str| std::env::var(k).unwrap_or_else(|_| panic!("{k} is not set"));
    let learner = Learner::from_text(&std::fs::read_to_string(var("DEPOSIT_STATE")).unwrap()).unwrap();
    let units = crate::units::Units::from_text(&std::fs::read_to_string(var("CARRIER_UNITS")).unwrap()).unwrap();
    let codec = crate::codec::Codec::from_text(&std::fs::read_to_string(var("CARRIER_CODEC")).unwrap(), units).unwrap();
    let sites: usize = var("CARRIER_SITES").parse().unwrap();
    let text = std::fs::read(var("CARRIER_TEXT")).unwrap();
    let mut classes = Vec::new();
    for line in text.split(|&b| b == b'\n') {
        let mut l = line.to_vec();
        l.push(b'\n');
        if let Ok(c) = codec.encode(&l) {
            classes.extend(c);
        }
        if classes.len() >= sites {
            break;
        }
    }
    classes.truncate(sites);
    let unresolved: Vec<bool> = (0..classes.len()).map(|t| (t * 7) % 11 < 5).collect();
    let region = Region { classes: &classes, unresolved: &unresolved, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None };
    let field = &learner.field;
    let d = field.declaration;
    let (c, f) = (d.carry, d.contacts);
    let (c2, plain) = (2 * c, f / 2 - c);
    let pass = field.pass(&region, true).unwrap();
    let n = classes.len();
    let read = |ticks: &[crate::contact::TickCell]| -> Vec<f64> {
        (0..c).map(|k| {
            let left = (plain + k) % 2 == 0;
            let (mut num, mut den) = (0.0f64, 0.0f64);
            for cell in ticks {
                let q = |t: usize| (cell.qm[t * c2 + k] as f64, cell.qm[t * c2 + c + k] as f64);
                let g = |t: usize| {
                    let (gr, gi) = (cell.gam[t * c2 + k] as f64, cell.gam[t * c2 + c + k] as f64);
                    let m = gr.hypot(gi).max(1.0);
                    (gr / m, gi / m)
                };
                // the scan's order: left circles t = 0, 1, ..; right circles t = n − 1, n − 2, ..
                let order: Vec<usize> = if left { (0..n).collect() } else { (0..n).rev().collect() };
                // u at the i-th site of the order: Q after it (the next site's operand) less the turned Q before it
                let u = |i: usize| -> Option<(f64, f64)> {
                    if i + 1 >= order.len() {
                        return None;
                    }
                    let (t, next) = (order[i], order[i + 1]);
                    let (qr, qi) = q(t);
                    let (ar, ai) = q(next);
                    let (gr, gi) = g(t);
                    Some((ar - (gr * qr - gi * qi), ai - (gr * qi + gi * qr)))
                };
                for i in 1..order.len() {
                    let (Some(now), Some(before)) = (u(i), u(i - 1)) else { continue };
                    let (gr, gi) = g(order[i]);
                    let turned = (gr * before.0 - gi * before.1, gr * before.1 + gi * before.0);
                    num += now.0 * turned.0 + now.1 * turned.1;
                    den += now.0.hypot(now.1) * before.0.hypot(before.1);
                }
            }
            if den > 0.0 { num / den } else { f64::NAN }
        }).collect()
    };
    let report = |tag: &str, v: Vec<f64>| {
        let mut s: Vec<f64> = v.into_iter().filter(|x| x.is_finite()).collect();
        s.sort_by(f64::total_cmp);
        let q = |p: f64| s[((s.len() - 1) as f64 * p) as usize];
        let above = s.iter().filter(|&&x| x > 0.10).count() as f64 / s.len() as f64;
        let below = s.iter().filter(|&&x| x < -0.20).count() as f64 / s.len() as f64;
        eprintln!("CIRCLE_NEWS {tag} circles={} median={:.3} q25={:.3} q75={:.3} p10={:.3} p90={:.3} share_above_+0.10={above:.3} share_under_-0.20={below:.3}", s.len(), q(0.5), q(0.25), q(0.75), q(0.1), q(0.9));
    };
    report("all_ticks", read(&pass.ticks));
    report("last_tick", read(&pass.ticks[pass.ticks.len() - 1..]));
    // the gates' own strength: δ = 1 − |γ| at the last tick, by circle's median
    let last = pass.ticks.last().unwrap();
    let mut deltas: Vec<f64> = (0..n).flat_map(|t| (0..c).map(move |k| (t, k))).map(|(t, k)| 1.0 - (last.gam[t * c2 + k] as f64).hypot(last.gam[t * c2 + c + k] as f64) / f64::from(1u32 << 30)).collect();
    deltas.sort_by(f64::total_cmp);
    eprintln!("CIRCLE_NEWS gates delta=1-|gamma| median={:.3} p10={:.3} p90={:.3} white_drive_cosine=-delta/2={:.3}", deltas[deltas.len() / 2], deltas[deltas.len() / 10], deltas[deltas.len() * 9 / 10], -deltas[deltas.len() / 2] / 2.0);
}

/// [measurement; the lead, November 21, the formal thread's reads S1 and S2 (04:04Z)] **The circles' scan with its residue carried**: the learner
/// at `DEPOSIT_STATE` reads one region of `CARRIER_SITES` sites cut from `CARRIER_TEXT` at its own ticks, once as built and once with the ruler's
/// scan that keeps the orbit 48 bits finer and releases it at each read ([`Constitution::ruler_scan_carry`]). S1: at the first tick, where both
/// passes' operands are the same, each circle's operand `Q(t∓1)` against the carried orbit's, in grains of `2^(−16)` (share within one grain and the
/// largest gap), and the same at every tick beside it. S2: the held code over the open places (nats a place), both ways. A ruler; no state changes.
#[test]
#[ignore]
#[allow(clippy::disallowed_methods, reason = "an exterior reading of saved state files")]
#[allow(clippy::disallowed_types, reason = "a ruler's codes are reported on the host as floats")]
fn the_circles_scan_with_its_residue_carried() {
    let var = |k: &str| std::env::var(k).unwrap_or_else(|_| panic!("{k} is not set"));
    let learner = Learner::from_text(&std::fs::read_to_string(var("DEPOSIT_STATE")).unwrap()).unwrap();
    let units = crate::units::Units::from_text(&std::fs::read_to_string(var("CARRIER_UNITS")).unwrap()).unwrap();
    let codec = crate::codec::Codec::from_text(&std::fs::read_to_string(var("CARRIER_CODEC")).unwrap(), units).unwrap();
    let sites: usize = var("CARRIER_SITES").parse().unwrap();
    let text = std::fs::read(var("CARRIER_TEXT")).unwrap();
    let mut classes = Vec::new();
    for line in text.split(|&b| b == b'\n') {
        let mut l = line.to_vec();
        l.push(b'\n');
        if let Ok(c) = codec.encode(&l) {
            classes.extend(c);
        }
        if classes.len() >= sites {
            break;
        }
    }
    classes.truncate(sites);
    let unresolved: Vec<bool> = (0..classes.len()).map(|t| (t * 7) % 11 < 5).collect();
    let region = Region { classes: &classes, unresolved: &unresolved, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None };
    let built = learner.field.clone();
    let mut carried = learner.field.clone();
    carried.ruler_scan_carry = true;
    let (pb, pc) = (built.pass(&region, true).unwrap(), carried.pass(&region, true).unwrap());
    for (k, (a, b)) in pb.ticks.iter().zip(&pc.ticks).enumerate() {
        let gaps: Vec<u64> = a.qm.iter().zip(&b.qm).map(|(&x, &y)| (x - y).unsigned_abs()).collect();
        let within = gaps.iter().filter(|&&g| g <= 1).count() as f64 / gaps.len() as f64;
        let zero = gaps.iter().filter(|&&g| g == 0).count() as f64 / gaps.len() as f64;
        eprintln!("SCAN_CARRY tick={k} components={} within_one_grain={within:.4} equal={zero:.4} largest_gap={}", gaps.len(), gaps.iter().max().unwrap());
    }
    let code = |p: &crate::contact::Forward| -> f64 {
        let (mut s, mut n) = (0.0, 0usize);
        for t in 0..classes.len() {
            if let (true, Some(face)) = (unresolved[t], p.faces[t].as_ref()) {
                s += face.code(classes[t]) as f64 / f64::from(1u32 << 20) * std::f64::consts::LN_2;
                n += 1;
            }
        }
        s / n as f64
    };
    eprintln!("SCAN_CARRY held_code_nats built={:.5} carried={:.5} change={:+.5}", code(&pb), code(&pc), code(&pc) - code(&pb));
}

/// [measurement; the lead, November 21, the formal thread's gate law G (04:15Z), reads G1 and G2] **The circles' news at lighter gates**: the
/// learner at `DEPOSIT_STATE` with every circle's friction `d` multiplied by `2^(−k)` (its leak chart's bias lowered by `k` on the log chart, the
/// coupling `κ` following `d` as built), for each `k` of `NEWS_SHIFTS`, reads one region of `CARRIER_SITES` sites cut from `CARRIER_TEXT` at its own
/// ticks: by circle the pooled cosine of successive news along its scan (as `the_circles_successive_news` reads it, over the pass's ticks), the
/// gates' median strength `δ = 1 − |γ|`, and the held code over the open places. Lines to stderr. A ruler on the host; no state changes.
#[test]
#[ignore]
#[allow(clippy::disallowed_methods, reason = "an exterior reading of saved state files")]
#[allow(clippy::disallowed_types, reason = "a ruler's cosines and codes are reported on the host as floats")]
fn the_circles_news_at_lighter_gates() {
    let var = |k: &str| std::env::var(k).unwrap_or_else(|_| panic!("{k} is not set"));
    let learner = Learner::from_text(&std::fs::read_to_string(var("DEPOSIT_STATE")).unwrap()).unwrap();
    let units = crate::units::Units::from_text(&std::fs::read_to_string(var("CARRIER_UNITS")).unwrap()).unwrap();
    let codec = crate::codec::Codec::from_text(&std::fs::read_to_string(var("CARRIER_CODEC")).unwrap(), units).unwrap();
    let sites: usize = var("CARRIER_SITES").parse().unwrap();
    let shifts: Vec<i32> = var("NEWS_SHIFTS").split(',').map(|v| v.parse().unwrap()).collect();
    let text = std::fs::read(var("CARRIER_TEXT")).unwrap();
    let mut classes = Vec::new();
    for line in text.split(|&b| b == b'\n') {
        let mut l = line.to_vec();
        l.push(b'\n');
        if let Ok(c) = codec.encode(&l) {
            classes.extend(c);
        }
        if classes.len() >= sites {
            break;
        }
    }
    classes.truncate(sites);
    let unresolved: Vec<bool> = (0..classes.len()).map(|t| (t * 7) % 11 < 5).collect();
    let region = Region { classes: &classes, unresolved: &unresolved, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None };
    let d = learner.field.declaration;
    let (c, f) = (d.carry, d.contacts);
    let (c2, plain) = (2 * c, f / 2 - c);
    let n = classes.len();
    for &k in &shifts {
        let mut field = learner.field.clone();
        let at = field.layout.carry_bias + c;
        for v in &mut field.theta[at..at + c] {
            *v -= k << FACE_BITS;
        }
        let pass = field.pass(&region, true).unwrap();
        let mut cos: Vec<f64> = (0..c).map(|j| {
            let left = (plain + j) % 2 == 0;
            let order: Vec<usize> = if left { (0..n).collect() } else { (0..n).rev().collect() };
            let (mut num, mut den) = (0.0f64, 0.0f64);
            for cell in &pass.ticks {
                let q = |t: usize| (cell.qm[t * c2 + j] as f64, cell.qm[t * c2 + c + j] as f64);
                let g = |t: usize| {
                    let (gr, gi) = (cell.gam[t * c2 + j] as f64, cell.gam[t * c2 + c + j] as f64);
                    let m = gr.hypot(gi).max(1.0);
                    (gr / m, gi / m)
                };
                let u = |i: usize| -> Option<(f64, f64)> {
                    if i + 1 >= order.len() {
                        return None;
                    }
                    let (t, next) = (order[i], order[i + 1]);
                    let ((qr, qi), (ar, ai), (gr, gi)) = (q(t), q(next), g(t));
                    Some((ar - (gr * qr - gi * qi), ai - (gr * qi + gi * qr)))
                };
                for i in 1..order.len() {
                    let (Some(now), Some(before)) = (u(i), u(i - 1)) else { continue };
                    let (gr, gi) = g(order[i]);
                    let turned = (gr * before.0 - gi * before.1, gr * before.1 + gi * before.0);
                    num += now.0 * turned.0 + now.1 * turned.1;
                    den += now.0.hypot(now.1) * before.0.hypot(before.1);
                }
            }
            if den > 0.0 { num / den } else { f64::NAN }
        }).filter(|x| x.is_finite()).collect();
        cos.sort_by(f64::total_cmp);
        let last = pass.ticks.last().unwrap();
        let mut deltas: Vec<f64> = (0..n).flat_map(|t| (0..c).map(move |j| (t, j))).map(|(t, j)| 1.0 - (last.gam[t * c2 + j] as f64).hypot(last.gam[t * c2 + c + j] as f64) / f64::from(1u32 << 30)).collect();
        deltas.sort_by(f64::total_cmp);
        let (mut code, mut open) = (0.0, 0usize);
        for t in 0..n {
            if let (true, Some(face)) = (unresolved[t], pass.faces[t].as_ref()) {
                code += face.code(classes[t]) as f64 / f64::from(1u32 << 20) * std::f64::consts::LN_2;
                open += 1;
            }
        }
        let q = |p: f64| cos[((cos.len() - 1) as f64 * p) as usize];
        eprintln!("GATE_LIGHTER k={k} cos_median={:.3} q25={:.3} q75={:.3} share_above_0={:.3} delta_median={:.3} held_code_nats={:.4}", q(0.5), q(0.25), q(0.75), cos.iter().filter(|&&x| x > 0.0).count() as f64 / cos.len() as f64, deltas[deltas.len() / 2], code / open as f64);
    }
}

/// [definition; the lead, November 21, the reach] **Each head's friction of distance, founded at zero, keeps every face and every standing
/// covector** ([`Constitution::with_friction`]): on fields with still and turned heads, circles, four ticks and the opening, the founded field
/// reads the same faces and returns the same covector at every standing entry, in a region and in a passage read by two streams; its line is
/// `hnn-field-v14r` and reads back as written, with the pump's and the leak's words carried; a second founding is refused.
#[test]
fn the_friction_founded_at_zero_keeps_every_face_and_every_standing_covector() {
    let fields: Vec<(&str, Constitution)> = vec![("plain, one still", shaped(1)), ("four ticks, two still", four_ticks(2)), ("circles, one still", circled_shaped(1)), ("opened, turned", opened(0))];
    for (name, plain) in &fields {
        let (grown, from) = plain.with_friction().unwrap();
        let (d, l) = (grown.declaration, grown.layout.clone());
        assert!(d.friction && !plain.declaration.friction);
        assert_eq!(l.friction, plain.theta.len(), "{name}: the frictions at the fine field's end");
        assert!(grown.theta[l.friction..l.friction + 2 * d.heads].iter().all(|&v| v == 0), "{name}: founded at zero");
        assert_eq!(from.iter().flatten().count(), plain.material_len(), "{name}: every standing entry kept");
        let r = region();
        assert_eq!(grown.faces(&r).unwrap(), plain.faces(&r).unwrap(), "{name}: every face kept");
        let (g, h) = (covector_of(&grown, &r), covector_of(plain, &r));
        for (n, o) in from.iter().enumerate() {
            if let Some(o) = o {
                assert_eq!(g[n], h[*o], "{name}: the covector of standing entry {o}");
            }
        }
        let classes = drawn_classes(0xF1, 9, d.alphabet);
        for past in [false, true] {
            let (pg, pp) = (grown.strand_pass(&classes, true, past).unwrap(), plain.strand_pass(&classes, true, past).unwrap());
            assert_eq!(pg.faces, pp.faces, "{name}: a strand's faces kept");
            let (mut sg, mut sp) = (vec![0i128; grown.theta.len()], vec![0i128; plain.theta.len()]);
            grown.strand_returned(&classes, &classes, &pg, &mut sg).unwrap();
            plain.strand_returned(&classes, &classes, &pp, &mut sp).unwrap();
            assert_eq!(&sg[..plain.theta.len()], &sp[..], "{name}: a strand's standing covector kept");
        }
        let text = d.to_text();
        assert!(text.starts_with("hnn-field-v14r "), "{name}: {text}");
        assert_eq!(Declaration::from_text(&text).unwrap(), d);
        assert!(grown.with_friction().is_err(), "{name}: a second founding");
    }
    for (pump, lane_leak) in [(true, false), (false, true), (true, true)] {
        let both = Declaration { pump, lane_leak, friction: true, friction_gate: false, ..circled_shaped(1).declaration };
        assert_eq!(Declaration::from_text(&both.to_text()).unwrap(), both);
    }
    let line = Declaration { friction: true, friction_gate: false, ..shaped(1).declaration }.to_text();
    assert!(Declaration::from_text(&format!("{} 0", &line[..line.len() - 2])).is_err(), "a friction word of zero");
}

/// [definition; the lead, November 21, the reach] **The friction's return matches its code's difference**: with every head's frictions
/// drawn off zero (a quarter of a bit to one bit an octave, of either sign), the code's covector predicts the code's central difference at
/// each friction entry and at the entries of every family with the largest covector, in a region whose open sites listen and in a passage
/// read by two streams with its odd contacts facing the past: so `δψ = −Σ δz ⌊log₂ d⌋` is the reverse of the friction's forward.
#[test]
fn the_frictions_return_matches_its_codes_difference() {
    let (mut read, mut seams, mut frictions) = (0usize, 0usize, 0usize);
    for (name, plain) in [("plain, one still", shaped(1)), ("circles, one still", circled_shaped(1)), ("four ticks, two still", four_ticks(2))] {
        let (mut field, _) = plain.with_friction().unwrap();
        let l = field.layout.clone();
        let heads = field.declaration.heads;
        for (n, v) in field.theta[l.friction..l.friction + 2 * heads].iter_mut().enumerate() {
            *v = [1 << 14, -(1 << 15), 3 << 14, 1 << 16][n % 4];
        }
        let r = region();
        assert_ne!(field.faces(&r).unwrap(), plain.faces(&r).unwrap(), "{name}: the friction moves the faces");
        let classes = drawn_classes(0xF2, 11, field.declaration.alphabet);
        let strand_code = |f: &Constitution| -> i64 { f.strand_pass(&classes, false, true).unwrap().faces.iter().zip(&classes).skip(1).map(|(fc, &c)| crate::field::ratio_code(fc.masses[c], fc.total)).sum() };
        let strand_g = {
            let pass = field.strand_pass(&classes, true, true).unwrap();
            let mut g = vec![0i128; field.theta.len()];
            field.strand_returned(&classes, &classes, &pass, &mut g).unwrap();
            g
        };
        let region_g = covector_of(&field, &r);
        let sheets = |f: &Constitution| -> Vec<Vec<u32>> {
            let p = f.pass(&r, true).unwrap();
            let s = f.strand_pass(&classes, true, true).unwrap();
            p.ticks.iter().chain(&s.ticks).flat_map(|c| c.classes.iter().map(|cl| cl.off.iter().chain(&cl.members).copied().chain(cl.probes.iter().flat_map(|p| std::iter::once(u32::MAX).chain(p.iter().copied()))).collect())).collect()
        };
        for (which, g) in [("region", &region_g), ("strand", &strand_g)] {
            for &(start, len, grain) in field.families() {
                if start == l.temper {
                    continue;
                }
                let natural: u32 = if grain == MATERIAL_BITS { 40 } else { 24 };
                let mut entries: Vec<usize> = (start..start + len).collect();
                entries.sort_by_key(|&i| std::cmp::Reverse(g[i].unsigned_abs()));
                let take = if start == l.friction { len } else { 2 };
                for i in entries.into_iter().take(take).filter(|&i| g[i] != 0) {
                    let moved = |delta: i32| {
                        let mut f = field.clone();
                        f.theta[i] += delta;
                        f
                    };
                    let straddles = |delta: i32| sheets(&moved(delta)) != sheets(&field) || sheets(&moved(-delta)) != sheets(&field);
                    let shift = natural + grain - 20;
                    let Some((delta, h)) = probe_step(grain, &|delta: i32| (g[i] * 2 * delta as i128) >> shift, &straddles) else {
                        seams += 1;
                        continue;
                    };
                    read += 1;
                    frictions += usize::from(start == l.friction);
                    let measured = if which == "region" { moved(delta).code(&r).unwrap().0 - moved(-delta).code(&r).unwrap().0 } else { strand_code(&moved(delta)) - strand_code(&moved(-delta)) };
                    let predicted = (g[i] * 2 * delta as i128) >> shift;
                    let tolerance = predicted.abs() / 8 + (64 * 10 << h);
                    assert!((measured as i128 - predicted).abs() <= tolerance, "{name}, {which}: family at {start} (grain {grain}) entry {i} at {h} halvings: measured {measured}, predicted {predicted}");
                }
            }
        }
    }
    eprintln!("FRICTION_COVECTOR_PROBES read={read} on_a_seam={seams} at_the_frictions={frictions}");
    assert!(read >= 30 && 8 * seams <= read && frictions >= 12, "read {read} probes, {seams} on a seam, {frictions} at the frictions");
}

/// [definition; the lead, November 21, the reach §6] **The friction read from the receiver's state, founded at zero, keeps every face, and its
/// return matches its code's difference**: the gate founded on a field with its frictions drawn reads the same faces and returns the same
/// covector at every standing entry, its line writes the friction word two and reads back; with the gate drawn off zero (a row of `D` a head),
/// the code's covector predicts the code's central difference at the gate's entries and at every family's largest, in a region whose open sites
/// listen and in a passage read by two streams facing the past: so `δa_h = Σ δψ r̂` and the read's `a_h δψ` are the gate's reverse.
#[test]
fn the_friction_read_from_the_receivers_state_keeps_every_face_at_zero_and_returns_its_codes_difference() {
    let (mut read, mut seams, mut gated) = (0usize, 0usize, 0usize);
    for (name, plain) in [("plain, one still", shaped(1)), ("circles, one still", circled_shaped(1)), ("four ticks, two still", four_ticks(2))] {
        let (mut frictioned, _) = plain.with_friction().unwrap();
        let l0 = frictioned.layout.clone();
        let heads = frictioned.declaration.heads;
        for (n, v) in frictioned.theta[l0.friction..l0.friction + 2 * heads].iter_mut().enumerate() {
            *v = [1 << 14, -(1 << 15), 3 << 14, 1 << 16][n % 4];
        }
        let (mut field, from) = frictioned.with_friction_gate().unwrap();
        let (d, l) = (field.declaration, field.layout.clone());
        assert!(d.friction_gate && l.friction_gate == frictioned.theta.len(), "{name}: the gate at the fine field's end");
        assert_eq!(from.iter().flatten().count(), frictioned.material_len(), "{name}: every standing entry kept");
        let r = region();
        assert_eq!(field.faces(&r).unwrap(), frictioned.faces(&r).unwrap(), "{name}: every face kept at the founding");
        let (g, h) = (covector_of(&field, &r), covector_of(&frictioned, &r));
        for (n, o) in from.iter().enumerate() {
            if let Some(o) = o {
                assert_eq!(g[n], h[*o], "{name}: the covector of standing entry {o}");
            }
        }
        assert!(g[l.friction_gate..l.friction_gate + heads * d.width].iter().any(|&v| v != 0), "{name}: the gate has a slope at its founding");
        let text = d.to_text();
        assert!(text.starts_with("hnn-field-v14r ") && text.ends_with(" 2"), "{name}: {text}");
        assert_eq!(Declaration::from_text(&text).unwrap(), d);
        assert!(field.with_friction_gate().is_err() && plain.with_friction_gate().is_err(), "{name}: a second gate, and a gate without the friction");
        // The gate drawn: a row of D a head, at about a tenth of a bit an octave a unit of the read.
        let stream = keys(1 << 14);
        for (n, v) in field.theta[l.friction_gate..l.friction_gate + heads * d.width].iter_mut().enumerate() {
            let w = &stream[4 * n..4 * n + 4];
            *v = i32::from_be_bytes([w[0], w[1], w[2], w[3]]) >> 12;
        }
        assert_ne!(field.faces(&r).unwrap(), frictioned.faces(&r).unwrap(), "{name}: the gate moves the faces");
        let classes = drawn_classes(0xF3, 11, d.alphabet);
        let strand_code = |f: &Constitution| -> i64 { f.strand_pass(&classes, false, true).unwrap().faces.iter().zip(&classes).skip(1).map(|(fc, &c)| crate::field::ratio_code(fc.masses[c], fc.total)).sum() };
        let strand_g = {
            let pass = field.strand_pass(&classes, true, true).unwrap();
            let mut g = vec![0i128; field.theta.len()];
            field.strand_returned(&classes, &classes, &pass, &mut g).unwrap();
            g
        };
        let region_g = covector_of(&field, &r);
        let sheets = |f: &Constitution| -> Vec<Vec<u32>> {
            let p = f.pass(&r, true).unwrap();
            let s = f.strand_pass(&classes, true, true).unwrap();
            p.ticks.iter().chain(&s.ticks).flat_map(|c| c.classes.iter().map(|cl| cl.off.iter().chain(&cl.members).copied().chain(cl.probes.iter().flat_map(|p| std::iter::once(u32::MAX).chain(p.iter().copied()))).collect())).collect()
        };
        for (which, g) in [("region", &region_g), ("strand", &strand_g)] {
            for &(start, len, grain) in field.families() {
                if start == l.temper {
                    continue;
                }
                let natural: u32 = if grain == MATERIAL_BITS { 40 } else { 24 };
                let mut entries: Vec<usize> = (start..start + len).collect();
                entries.sort_by_key(|&i| std::cmp::Reverse(g[i].unsigned_abs()));
                let take = if start == l.friction_gate { 6 } else { 2 };
                for i in entries.into_iter().take(take).filter(|&i| g[i] != 0) {
                    let moved = |delta: i32| {
                        let mut f = field.clone();
                        f.theta[i] += delta;
                        f
                    };
                    let straddles = |delta: i32| sheets(&moved(delta)) != sheets(&field) || sheets(&moved(-delta)) != sheets(&field);
                    let shift = natural + grain - 20;
                    let Some((delta, hv)) = probe_step(grain, &|delta: i32| (g[i] * 2 * delta as i128) >> shift, &straddles) else {
                        seams += 1;
                        continue;
                    };
                    read += 1;
                    gated += usize::from(start == l.friction_gate);
                    let measured = if which == "region" { moved(delta).code(&r).unwrap().0 - moved(-delta).code(&r).unwrap().0 } else { strand_code(&moved(delta)) - strand_code(&moved(-delta)) };
                    let predicted = (g[i] * 2 * delta as i128) >> shift;
                    let tolerance = predicted.abs() / 8 + (64 * 10 << hv);
                    assert!((measured as i128 - predicted).abs() <= tolerance, "{name}, {which}: family at {start} (grain {grain}) entry {i} at {hv} halvings: measured {measured}, predicted {predicted}");
                }
            }
        }
    }
    eprintln!("FRICTION_GATE_COVECTOR_PROBES read={read} on_a_seam={seams} at_the_gate={gated}");
    assert!(read >= 30 && 8 * seams <= read && gated >= 18, "read {read} probes, {seams} on a seam, {gated} at the gate");
}

/// [definition; the lead, November 21, E4 of #1088] **A moment with its remainder carried tracks its true mean within a grain and reaches its
/// input**: driven by a constant input, the carried moment ends at the input where the forced grain ends there too; driven by an input
/// a quarter grain a section away, the carried moment's `m + r 2^(−rate)` stays within a grain of the exact mean `M ← M + (g − M) 2^(−rate)`
/// at every section, and a learner's text with the carried lines reads back as itself.
#[test]
fn a_moment_with_its_remainder_carried_tracks_its_mean() {
    use crate::deposit::{toward, toward_carried};
    for rate in [FIRST_RATE, SECOND_RATE] {
        let (mut m, mut r, mut f) = (0i128, 0i32, 0i128);
        for _ in 0..4000 {
            m = toward_carried(m, &mut r, 1000, rate).unwrap();
            f = toward(f, 1000, rate);
        }
        assert_eq!((m, f), (1000, 1000), "rate {rate}: both reach a constant input");
        assert!(r.unsigned_abs() <= 1 << (rate - 1), "rate {rate}: the remainder inside half a grain");
        // A slowly moving input: the exact mean on a fine grain, against the carried moment read with its remainder.
        let fine = 20u32;
        let (mut m, mut r, mut exact) = (0i128, 0i32, 0i128);
        let mut worst = 0i128;
        for k in 0..20_000i128 {
            let g = k / 4;
            m = toward_carried(m, &mut r, g, rate).unwrap();
            exact += ((g << fine) - exact) >> rate;
            let tracked = (m << fine) + (i128::from(r) << (fine - rate));
            worst = worst.max((tracked - exact).abs());
        }
        assert!(worst <= 2 << fine, "rate {rate}: the carried moment stands {worst} fine grains (2^-{fine} of a grain) from its mean");
    }
    let mut learner = Learner::new(shaped(1), 12);
    let n = learner.field.material_len();
    learner.carried = Some(((0..n).map(|k| (k % 7) as i32 - 3).collect(), (0..n).map(|k| (k % 255) as i32 - 127).collect()));
    let text = learner.to_text();
    assert!(text.contains("\ncarried_first ") && text.contains("\ncarried_second "));
    assert_eq!(Learner::from_text(&text).unwrap().to_text(), text, "the carried lines read back");
}

/// [definition; the lead, November 21, E5 of #1088; re-founded November 22, the second precision pass] **The lattice deposit keeps the whole
/// word and reads the read part, on each family's own spread**: founded from an end and a mean whose difference stands at a known spread by
/// family, every family's places stand one place under its spread's power of two, every entry's read part plus its rest is the end's entry,
/// and every read part stands on its family's lattice; the text reads back; over three sections the whole word moves by exactly the sum of
/// the steps (every step lands); re-founded from a mean whose spread moved a place, the moved families take it and every whole word is kept,
/// and re-founded from the same spread nothing moves; and from a mean equal to the end (no spread) every family is read whole, the plain
/// learner bit for bit.
#[test]
fn the_lattice_deposit_keeps_the_whole_word_and_reads_the_read_part() {
    let learner = Learner::new(drawn(shaped(1)), 12);
    let families = learner.field.families_all();
    let len = learner.field.material_len();
    // A mean standing `±2^(s−1)` to `±2^s` units of each entry's grain from the end, `s` by family.
    let mean_at = |shift: u32| {
        let mut m = learner.clone();
        for (k, v) in m.field.material_mut().enumerate() {
            *v -= ((k % 3) as i32 - 1) << shift;
        }
        m
    };
    for shift in [6u32, 9] {
        let mean = mean_at(shift);
        let latticed = learner.with_lattice_from(&mean).unwrap();
        let l = latticed.lattice.as_ref().unwrap();
        assert_eq!(l.spread.len(), families.len());
        for (k, (&(_, n, grain), p)) in families.iter().zip(l.places()).enumerate() {
            if n == 0 {
                continue;
            }
            // The spread is `2^shift · √(2/3)` grains of the family, so its power of two is `2^(shift − 1)` grains: one place under it is
            // `grain − shift + 2` places below the point.
            assert_eq!(p, Some(grain + 2 - shift.min(grain + 2)), "shift {shift}, family {k}: one place under its own spread");
        }
        assert_eq!(latticed.whole_material(), learner.whole_material(), "shift {shift}: the whole word is the end's");
        let drops = l.drops(&families, len);
        assert!(latticed.field.material().zip(&drops).all(|(&v, &q)| q == 0 || v % (1 << q) == 0), "shift {shift}: every read part on its lattice");
        assert!(drops.iter().any(|&q| q > 0), "shift {shift}: some family is read coarser than its grain");
        let text = latticed.to_text();
        assert_eq!(Learner::from_text(&text).unwrap().to_text(), text, "the lattice's lines read back");
        let mut run = latticed.clone();
        for _ in 0..3 {
            let before = run.whole_material();
            run.section(&[region()]).unwrap();
            let step = run.last.as_ref().map(|s| s.step.clone()).unwrap_or_default();
            for (k, ((a, b), s)) in run.whole_material().iter().zip(&before).zip(&step).enumerate() {
                assert_eq!(*a - *b, -(*s as i64), "shift {shift}: entry {k} moves by its step (the descent, θ − s), read part and rest together");
            }
        }
        // Re-founded at a save: the same spread moves nothing; a spread two places finer moves every family that moved, and keeps the word.
        let kept = run.whole_material();
        let same: Vec<i64> = kept.iter().zip(mean.whole_material()).zip(learner.whole_material()).map(|((&w, m), e)| w - (e - m)).collect();
        let mut again = run.clone();
        assert_eq!(again.refound_lattice(&same).unwrap(), 0, "shift {shift}: the same spread re-founds nothing");
        let finer: Vec<i64> = kept.iter().zip(mean_at(shift - 2).whole_material()).zip(learner.whole_material()).map(|((&w, m), e)| w - (e - m)).collect();
        let moved = again.refound_lattice(&finer).unwrap();
        assert_eq!(moved, families.iter().filter(|f| f.1 > 0).count(), "shift {shift}: every family's spread moved two places");
        assert_eq!(again.whole_material(), kept, "shift {shift}: re-founding keeps every whole word");
        let drops = again.lattice.as_ref().unwrap().drops(&families, len);
        assert!(again.field.material().zip(&drops).all(|(&v, &q)| q == 0 || v % (1 << q) == 0), "shift {shift}: re-founded, every read part on its new lattice");
        let text = again.to_text();
        assert_eq!(Learner::from_text(&text).unwrap().to_text(), text, "the re-founded lattice reads back");
    }
    // No spread: every family read whole, the plain learner bit for bit.
    let whole = learner.with_lattice_from(&learner).unwrap();
    assert!(whole.lattice.as_ref().unwrap().places().iter().all(Option::is_none));
    let (mut a, mut b) = (learner.clone(), whole.clone());
    for _ in 0..2 {
        a.section(&[region()]).unwrap();
        b.section(&[region()]).unwrap();
    }
    assert_eq!(a.field, b.field, "a lattice with no spread changes nothing");
}

/// [definition; the lead, November 22] **A growth carries the lattice and the remainders**: a learner on a lattice with carried remainders,
/// grown by crossing triads, keeps every standing entry's whole word, read part, lattice rest and remainders at its new index and every
/// family's spread; the families it adds open read whole with no rest; the grown learner reads back; and its legs founded at zero keep the
/// lattice, the founded families read whole.
#[test]
fn a_growth_carries_the_lattice_and_the_remainders() {
    let mut learner = Learner::new(drawn(shaped(1)), 12);
    let n = learner.field.material_len();
    learner.remainder = Some((0..n).map(|k| (k % 5) as i64).collect());
    learner.carried = Some(((0..n).map(|k| (k % 7) as i32 - 3).collect(), (0..n).map(|k| (k % 3) as i32 - 1).collect()));
    let mut mean = learner.clone();
    for (k, v) in mean.field.material_mut().enumerate() {
        *v -= ((k % 3) as i32 - 1) << 6;
    }
    let latticed = learner.with_lattice_from(&mean).unwrap();
    let triads = 2;
    let d = latticed.field.declaration;
    let grown = latticed.with_crossings(triads, &keys(latticed.drawn + 4 * d.triad_draws(triads))).unwrap();
    let (_, from) = latticed.field.with_crossings(triads, &keys(latticed.drawn + 4 * d.triad_draws(triads))[latticed.drawn..]).unwrap();
    let (old_whole, new_whole) = (latticed.whole_material(), grown.whole_material());
    let (ol, nl) = (latticed.lattice.as_ref().unwrap(), grown.lattice.as_ref().unwrap());
    let (or, nr) = (latticed.remainder.as_ref().unwrap(), grown.remainder.as_ref().unwrap());
    for (i, o) in from.iter().enumerate() {
        match o {
            Some(j) => {
                assert_eq!(new_whole[i], old_whole[*j], "entry {i}: the whole word at its new index");
                assert_eq!(nl.rest[i], ol.rest[*j], "entry {i}: the lattice's rest at its new index");
                assert_eq!(nr[i], or[*j], "entry {i}: the step's remainder at its new index");
            }
            None => assert_eq!(nl.rest[i], 0, "entry {i}: a new entry opens with no rest"),
        }
    }
    let places = nl.places();
    for (k, &(start, len, _)) in grown.field.families_all().iter().enumerate() {
        if len > 0 && from[start].is_none() {
            assert!(places[k].is_none(), "family {k}: a family the growth adds is read whole");
        }
    }
    let text = grown.to_text();
    assert_eq!(Learner::from_text(&text).unwrap().to_text(), text, "the grown learner reads back");
    let g = grown.field.declaration;
    let legs: Vec<i32> = (0..6 * g.triads * g.width + 6 * g.triads).map(|k| ((k % 9) as i32 - 4) << 10).collect();
    let founded = grown.with_located_legs(&legs, None).unwrap();
    assert!(founded.lattice.is_some(), "the legs' founding keeps the lattice");
    let text = founded.to_text();
    assert_eq!(Learner::from_text(&text).unwrap().to_text(), text, "the founded learner reads back");
}

/// A slice's bytes that are never read (the cut's choice reads only the pass's counts).
struct UnreadBytes;
impl crate::passage::PieceBytes for UnreadBytes {
    fn read_at(&mut self, _at: u64, out: &mut [u8]) -> std::result::Result<(), Box<dyn std::error::Error>> {
        out.fill(b'a');
        Ok(())
    }
}

/// [definition; the lead, November 24 and 25] **The cut held by its slices' tensions reads each slice at its quota weighed by its news, by
/// each slice's own clock, and the quotas alone without them**: without tensions the slice behind its quota takes the next stretch; with
/// them the slice whose clock stands furthest behind does, so over many stretches a slice at three times another's tension gives three
/// times its places, whatever each had taken before the tensions were set (W113s: a slice that owed its history was never read); the
/// tension and clock lines read back as written.
#[test]
fn the_cut_held_by_its_slices_tensions_reads_a_slice_by_its_quota_weighed_by_its_news_and_reads_the_quotas_alone_without_it() {
    let piece = crate::passage::Piece { document: 0, offset: 0, title: 0, text: 1 << 20, opens: false, closes: true };
    let slice = |name: &str| crate::passage::Slice { name: name.into(), quota: 1000, pieces: vec![piece], source: Box::new(UnreadBytes) };
    let pass = |taken: [u64; 2], tension: Option<Vec<u64>>, clock: Option<Vec<u128>>| StorePass {
        role: "prefix".into(),
        store: "ab".repeat(32),
        stretches: 7,
        least: 4,
        octaves: 7,
        pairs: 15_606_223,
        sites: 41_490,
        own: false,
        slices: vec![PassSlice { name: "a".into(), piece: 0, cursor: taken[0], taken: taken[0] }, PassSlice { name: "b".into(), piece: 0, cursor: taken[1], taken: taken[1] }],
        world: None,
        frontier: 0,
        before: false,
        strand: false,
        past: false,
        second: false,
        terrain: None,
        slice_tension: tension,
        slice_clock: clock,
    };
    let cut = |taken: [u64; 2], tension: Option<Vec<u64>>, clock: Option<Vec<u128>>| crate::passage::Cut { seed: 3, slices: vec![slice("a"), slice("b")], pass: pass(taken, tension, clock) };
    // Without tensions the quotas alone: the slice behind takes the next stretch.
    assert_eq!(cut([100, 101], None, None).next().unwrap().slice, 0);
    assert_eq!(cut([101, 100], None, None).next().unwrap().slice, 1);
    // With them, the clock furthest behind, whatever was taken before: a's history of four times b's places is no debt.
    assert_eq!(cut([400, 100], Some(vec![1_000, 3_000]), Some(vec![5, 6])).next().unwrap().slice, 0);
    assert_eq!(cut([100, 400], Some(vec![1_000, 3_000]), None).next().unwrap().slice, 0);
    // Over many stretches, b at three times a's tension gives three times a's places (each stretch's places advance its slice's clock).
    // The first stretches are read before any slice has a reading (one each), as a pass held by its tensions opens (W113t's first section).
    let mut c = cut([400, 100], Some(vec![0, 0]), Some(vec![0, 0]));
    let mut gave = [0u64; 2];
    let mut step = |c: &mut crate::passage::Cut, gave: &mut [u64; 2]| {
        let s = c.next().unwrap().slice;
        let (w, mean) = c.slice_weights().unwrap();
        c.pass.slice_clock.as_mut().unwrap()[s] += crate::passage::clock_step(10, c.slices[s].quota, w[s], mean);
        gave[s] += 10;
    };
    for _ in 0..2 {
        step(&mut c, &mut gave);
    }
    assert_eq!(gave, [10, 10], "one stretch each before any reading");
    c.pass.slice_tension = Some(vec![1_000_000, 3_000_000]);
    for _ in 0..4_000 {
        step(&mut c, &mut gave);
    }
    assert!((gave[1] as i64 - 3 * gave[0] as i64).abs() <= 60, "b gives three times a's places, the first stretches no debt: {gave:?}");
    // Unlike quotas: a at quota 1,000 and three times b's tension, b at quota 4,000; b gives four thirds of a's places.
    let mut c = crate::passage::Cut { seed: 3, slices: vec![slice("a"), crate::passage::Slice { quota: 4000, ..slice("b") }], pass: pass([0, 0], Some(vec![0, 0]), Some(vec![0, 0])) };
    let mut gave = [0u64; 2];
    for _ in 0..2 {
        step(&mut c, &mut gave);
    }
    c.pass.slice_tension = Some(vec![3_000_000, 1_000_000]);
    for _ in 0..7_000 {
        step(&mut c, &mut gave);
    }
    assert!((3 * gave[1] as i64 - 4 * gave[0] as i64).abs() <= 120, "b gives four thirds of a's places: {gave:?}");
    // A slice with no reading weighs as the mean of those with one; with no reading at all, one each.
    assert_eq!(cut([0, 0], Some(vec![0, 3_000]), None).slice_weights().unwrap(), (vec![3_000, 3_000], 3_000));
    assert_eq!(cut([0, 0], Some(vec![0, 0]), None).slice_weights().unwrap(), (vec![1, 1], 1));
    // The tension and clock lines read back as written, after the pass's line.
    let mut learner = Learner::new(shaped_with(four_contacts(1)), 6);
    learner.pass = Some(pass([100, 250], Some(vec![1_000, 3_000]), Some(vec![17, 4])));
    let text = learner.to_text();
    assert!(text.lines().any(|l| l == "tension 1000 3000"), "the tension line is written");
    assert!(text.lines().any(|l| l == "clock 17 4"), "the clock line is written");
    assert_eq!(Learner::from_text(&text).unwrap().pass, learner.pass, "and read back");
}

/// [definition; the lead, November 24] **The rings' fades founded at zero keep every face, and their return matches their code's
/// difference**: a field whose rings hold their fades founded at zero reads every face of its source and returns the same covector at
/// every standing entry, its line writes `hnn-field-v14s` and reads back; with the fades drawn off zero, the code's covector at each fade
/// (`ln 2 Σ s ∂L/∂s` from the skin's homogeneity, [`Constitution::fade_covector`]) predicts the code's central difference, in a region
/// and in a passage read by two streams.
#[test]
fn the_rings_fades_founded_at_zero_keep_every_face_and_their_return_matches_their_codes_difference() {
    let (mut read, mut seams) = (0usize, 0usize);
    for (name, plain) in [("plain, one still", shaped(1)), ("circles, one still", circled_shaped(1)), ("four ticks, one still", four_ticks(1)), ("the opening, one still", opened(1))] {
        let (zero, _) = plain.with_fade(2, 0).unwrap();
        let r = region();
        assert_eq!(zero.faces(&r).unwrap(), plain.faces(&r).unwrap(), "{name}: the fades founded at zero keep every face");
        let base_g = covector_of(&plain, &r);
        let zero_g = covector_of(&zero, &r);
        assert_eq!(&zero_g[..plain.theta.len()], &base_g[..], "{name}: and every standing entry's covector");
        let text = zero.to_text();
        assert!(text.starts_with("hnn-field-v14s "), "{name}: the line is v14s");
        assert_eq!(Constitution::from_text(&text).unwrap().theta, zero.theta, "{name}: and reads back");
        let mut field = zero.clone();
        let l = field.layout.clone();
        let slots = field.declaration.turned_slots();
        for (k, v) in field.theta[l.fade..l.fade + slots].iter_mut().enumerate() {
            *v = [-(1 << 23), 1 << 22, -(3 << 22), 1 << 23][k % 4];
        }
        field.refresh_fade().unwrap();
        assert_ne!(field.faces(&r).unwrap(), plain.faces(&r).unwrap(), "{name}: the fades move the faces");
        let classes = drawn_classes(0xFA, 11, field.declaration.alphabet);
        // A strand on a field that compares its opening compares the retarded opening at every place too, so its code is its places' and
        // its opening's, as the strand's own tests read it.
        let strand_code = |f: &Constitution| -> i64 {
            let places: i64 = f.strand_pass(&classes, false, true).unwrap().faces.iter().zip(&classes).skip(1).map(|(fc, &c)| crate::field::ratio_code(fc.masses[c], fc.total)).sum();
            let known = vec![false; classes.len()];
            let opening = if f.declaration.opening { opening_code(f, &Region { classes: &classes, unresolved: &known, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: true, strand: false, past: true, second: false, targets: None }) } else { 0 };
            places + opening
        };
        let strand_g = {
            let pass = field.strand_pass(&classes, true, true).unwrap();
            let mut g = vec![0i128; field.theta.len()];
            field.strand_returned(&classes, &classes, &pass, &mut g).unwrap();
            g
        };
        let region_g = covector_of(&field, &r);
        let sheets = |f: &Constitution| -> Vec<Vec<u32>> {
            let p = f.pass(&r, true).unwrap();
            let s = f.strand_pass(&classes, true, true).unwrap();
            p.ticks.iter().chain(&s.ticks).flat_map(|c| c.classes.iter().map(|cl| cl.off.iter().chain(&cl.members).copied().chain(cl.probes.iter().flat_map(|p| std::iter::once(u32::MAX).chain(p.iter().copied()))).collect())).collect()
        };
        for (which, g) in [("region", &region_g), ("strand", &strand_g)] {
            for i in (l.fade..l.fade + slots).filter(|&i| g[i] != 0) {
                let moved = |delta: i32| {
                    let mut f = field.clone();
                    f.theta[i] += delta;
                    f.refresh_fade().unwrap();
                    f
                };
                let straddles = |delta: i32| sheets(&moved(delta)) != sheets(&field) || sheets(&moved(-delta)) != sheets(&field);
                let shift = 40 + MATERIAL_BITS - 20;
                let Some((delta, h)) = probe_step(MATERIAL_BITS, &|delta: i32| (g[i] * 2 * delta as i128) >> shift, &straddles) else {
                    seams += 1;
                    continue;
                };
                read += 1;
                let measured = if which == "region" { moved(delta).code(&r).unwrap().0 - moved(-delta).code(&r).unwrap().0 } else { strand_code(&moved(delta)) - strand_code(&moved(-delta)) };
                let predicted = (g[i] * 2 * delta as i128) >> shift;
                let tolerance = predicted.abs() / 8 + (64 * 10 << h);
                assert!((measured as i128 - predicted).abs() <= tolerance, "{name}, {which}: fade entry {} at {h} halvings: measured {measured}, predicted {predicted}", i - l.fade);
            }
        }
    }
    eprintln!("FADE_COVECTOR_PROBES read={read} on_a_seam={seams}");
    assert!(read >= 12 && 8 * seams <= read.max(1), "read {read} probes, {seams} on a seam");
}

