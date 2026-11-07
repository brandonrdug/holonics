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

fn tiny_declaration(still: usize) -> FieldDeclaration {
    FieldDeclaration { alphabet: 5, width: 8, heads: 2, modes: 3, still, contacts: 4, ticks: 2, frames: 2, reach: 16, lanes: 1, depth: 0, energy: false }
}

/// A tiny field with every family drawn from the keys (the founding holds the returns and the
/// readout at zero, where no covector reaches the charts).
fn shaped(still: usize) -> Field {
    shaped_with(tiny_declaration(still))
}

/// [`shaped`] on a declaration of the caller's.
fn shaped_with(d: FieldDeclaration) -> Field {
    let mut field = Field::found(d, &keys(1 << 14)).unwrap();
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
fn silent_contacts(mut field: Field) -> Field {
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
    Region { classes: &CLASSES, unresolved: &OPEN, faces: &[], locked: &[], echo: &[], domain: None, port: None }
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
fn covector_of(field: &Field, region: &Region) -> Vec<i128> {
    let pass = field.pass(region, true).unwrap();
    let mut g = vec![0i128; field.theta.len()];
    field.returned(region, &pass, &mut g).unwrap();
    g
}

/// The learner's covector of one region (the reverse).
fn reversed_of(field: &Field, region: &Region) -> Vec<i128> {
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
    assert!(field.faces(&Region { classes: &classes, unresolved: &open, faces: &[], locked: &[], echo: &[], domain: None, port: None }).is_err());
    assert!(field.faces(&Region { classes: &classes[..16], unresolved: &open[..16], faces: &[], locked: &[], echo: &[], domain: None, port: None }).is_ok());
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
        let faces = field.faces(&Region { classes: &classes, unresolved: &open, faces: &carried, locked: &[], echo: &[], domain: None, port: None }).unwrap();
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
    let field = Field::found(tiny_declaration(1), &keys(1 << 14)).unwrap();
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
    let back = Field::from_text(&field.to_text()).unwrap();
    assert_eq!(back, field);
    let mut learner = FieldLearner::new(field, 6);
    learner.section(&[region()]).unwrap();
    let back = FieldLearner::from_text(&learner.to_text()).unwrap();
    // The transfer's operand is a reading's, not retained (§16.41).
    assert_eq!(back, FieldLearner { last: None, ..learner });
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
    let sheets = |field: &Field, r: &Region| -> Vec<Vec<u32>> { field.pass(r, true).unwrap().ticks.iter().flat_map(|c| c.classes.iter().map(|l| l.off.iter().chain(&l.members).copied().chain(l.probes.iter().flat_map(|p| std::iter::once(u32::MAX).chain(p.iter().copied()))).collect())).collect() };
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
    let port = Port { start: 4, void: 0, target: &[2, 3], boundary: false, stop: None, heard: None, window: false, letters: false, pull: None };
    let bounded = Port { boundary: true, ..port };
    // [the unified-theory reading of November 6, 11:49] And a port on its letters off the void, with its middle place resolved
    // (the writer's own state given its end).
    let lettered = Port { letters: true, target: &[2, 3, 1], ..port };
    // [the unified-theory reading of November 6, 19:04] And a declared pull at the port's first place, the rest past its stop.
    let pulled = Port { pull: Some((2, 3, 3 << 19)), stop: Some(5), ..port };
    // [the depth rings, November 6] And with a depth ring among the turned sets (its rate the located increment alone, no
    // skin, no moment).
    // [the unified-theory reading of November 6, 10:31] And under the bare stretch (`Field::bare_stretch`: past the last arrival
    // a silent place runs at the bare rate and returns nothing), declared beside the one-rate stretch.
    for (still, depth, bare, r) in [(0usize, 0usize, false), (1, 0, false), (2, 0, false), (0, 1, false), (1, 1, false), (0, 0, true), (1, 0, true)].into_iter().flat_map(|(still, depth, bare)| [(still, region()), (still, Region { classes: &CLASSES, unresolved: &OPEN, faces: &carried, locked: &[], echo: &[], domain: None, port: None }), (still, Region { classes: &CLASSES, unresolved: &PORTED, faces: &[], locked: &[], echo: &[], domain: None, port: Some(port) }), (still, Region { classes: &CLASSES, unresolved: &PORTED, faces: &[], locked: &[], echo: &[], domain: None, port: Some(bounded) }), (still, Region { classes: &CLASSES, unresolved: &PATH, faces: &[], locked: &[], echo: &[], domain: None, port: Some(bounded) }), (still, Region { classes: &CLASSES, unresolved: &PATH, faces: &[], locked: &[], echo: &[], domain: None, port: Some(lettered) }), (still, Region { classes: &CLASSES, unresolved: &PORTED, faces: &[], locked: &[], echo: &[], domain: None, port: Some(pulled) })].map(|(still, r)| (still, depth, bare, r))) {
        let mut field = shaped_with(FieldDeclaration { depth, ..tiny_declaration(still) });
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
        let pass = field.pass(&Region { classes: &classes, unresolved: &open, faces: &[], locked: &[], echo: &[], domain: None, port: None }, true).unwrap();
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
        let permuted = field.faces(&Region { classes: &classes, unresolved: &open, faces: &[], locked: &[], echo: &[], domain: None, port: None }).unwrap();
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
    let permuted = field.faces(&Region { classes: &classes, unresolved: &open, faces: &[], locked: &[], echo: &[], domain: None, port: None }).unwrap();
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
    let permuted = field.faces(&Region { classes: &classes, unresolved: &open, faces: &[], locked: &[], echo: &[], domain: None, port: None }).unwrap();
    assert!(order.iter().enumerate().any(|(n, &t)| permuted[n] != faces[t]));
}

/// [definition; §16.47, Brandon, November 5 17:32] **The step fluxes**: every section deposits its step at its size with no
/// reread (none is read after it), and over a few sections the regions' code falls from the founding's.
#[test]
fn fluxing_deposits_lower_the_code() {
    let field = Field::found(tiny_declaration(1), &keys(1 << 14)).unwrap();
    let mut learner = FieldLearner::new(field, 6);
    let second_classes = [2usize, 2, 3, 1, 0, 4, 4];
    let second_open = [true, false, false, true, true, false, false];
    let regions = [region(), Region { classes: &second_classes, unresolved: &second_open, faces: &[], locked: &[], echo: &[], domain: None, port: None }];
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
    let regions = [region(), Region { classes: &second_classes, unresolved: &second_open, faces: &[], locked: &[], echo: &[], domain: None, port: None }];
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
    let once = field.sample_realized(&problems, 3, 0, 0, 11, &mut HostField, &mut |_, _| true).unwrap();
    assert_eq!(once.iter().map(Vec::len).collect::<Vec<_>>(), vec![6, 5]);
    assert!(once.iter().flatten().all(|&c| c < field.declaration.alphabet));
    assert_eq!(field.sample_realized(&problems, 3, 0, 0, 11, &mut HostField, &mut |_, _| true).unwrap(), once, "the same draws");
    assert!((12..20).any(|seed| field.sample_realized(&problems, 3, 0, 0, seed, &mut HostField, &mut |_, _| true).unwrap() != once), "another seed draws another answer");
    let mut asked = 0;
    let stopped = field.sample_realized(&problems, 3, 0, 0, 11, &mut HostField, &mut |_, _| {
        asked += 1;
        asked < 2
    }).unwrap();
    assert_eq!(stopped.iter().map(Vec::len).collect::<Vec<_>>(), vec![6, 5], "a stopped write draws every place");
    let l = field.layout.clone();
    field.theta[l.read_bias + 2] = 40 << 16;
    let pointed = field.sample_realized(&problems, 3, 0, 0, 11, &mut HostField, &mut |_, _| true).unwrap();
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
        for (places, n) in field.sample_realized(&problems, 4, 0, 0, seed, &mut HostField, &mut |_, _| true).unwrap().into_iter().zip([9usize, 8]) {
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
        let as_faces = Region { classes: &CLASSES, unresolved: &OPEN, faces: &carried, locked: &locked, echo: &[], domain: None, port: None };
        assert_eq!(field.faces(&as_faces).unwrap(), field.faces(&r).unwrap(), "still {still}");
        assert!(field.faces(&Region { classes: &CLASSES, unresolved: &OPEN, faces: &[], locked: &locked, echo: &[], domain: None, port: None }).is_err(), "a lock on a site that carries no face");
        // An unresolved site carried as one class, locked, opens on it and is still read.
        let mut at_open = carried.clone();
        at_open[1] = Some(vec![(4, 1 << STATE_BITS)]);
        locked[1] = true;
        let mut resolved_open = OPEN;
        resolved_open[1] = false;
        let read = field.faces(&Region { classes: &CLASSES, unresolved: &OPEN, faces: &at_open, locked: &locked, echo: &[], domain: None, port: None }).unwrap();
        let resolved = field.faces(&Region { classes: &CLASSES, unresolved: &resolved_open, faces: &[], locked: &[], echo: &[], domain: None, port: None }).unwrap();
        assert!(read[1].is_some());
        for t in (0..CLASSES.len()).filter(|&t| t != 1) {
            assert_eq!(read[t], resolved[t], "still {still} site {t}");
        }
        assert!(field.faces(&Region { classes: &CLASSES, unresolved: &OPEN, faces: &carried[..3], locked: &[], echo: &[], domain: None, port: None }).is_err(), "one carried face a site or none");
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
    let field = Field::found(tiny_declaration(1), &keys(1 << 14)).unwrap();
    let mut learner = FieldLearner::new(field, 4);
    learner.read_held = true;
    for _ in 0..3 {
        learner.section(&[region()]).unwrap();
    }
    let stream = keys(1 << 16);
    assert!(learner.holds_step() && learner.widened(2, &stream).is_err(), "a held step is read before the body widens");
    learner.read_step_on(&[region()], &mut HostField).unwrap();
    let grown = learner.widened(2, &stream).unwrap();
    assert_eq!(grown.drawn, learner.drawn + 4 * learner.field.growth_draws(2));
    let l = grown.field.layout().clone();
    let old = learner.field.layout().clone();
    // The readout keeps its moments; an encoding entry's copy carries a half of the first.
    assert_eq!(grown.first[l.read_bias], learner.first[old.read_bias]);
    assert_eq!(grown.first[l.enc], div_nearest(learner.first[old.enc], 2));
    assert_eq!(grown.second[l.enc], div_nearest(learner.second[old.enc], 4));
    // Whether a step is read on the next regions is the run's declaration, not the learner's text (§16.30).
    let back = FieldLearner { read_held: grown.read_held, ..FieldLearner::from_text(&grown.to_text()).unwrap() };
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
fn law_scale(base: &Field, step: &[i128], h0: u32, old: &Compared, strict: bool, regions: &[Region]) -> (u32, bool) {
    let on = |field: &Field| compared(&regions.iter().map(|r| field.faces(r).unwrap()).collect::<Vec<_>>(), regions).unwrap();
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
/// ([`FieldLearner::next_scale`]): the further halvings and whether it is refused.
fn law_next(before: &Field, step: &[i128], h0: u32, regions: &[Region]) -> (u32, bool) {
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
    let field = Field::found(tiny_declaration(1), &keys(1 << 14)).unwrap();
    // [§16.34] At `2^(−3)`: under the strand's pair contact the fixture certifies too few steps at `2^(−2)` to hold one.
    let mut learner = FieldLearner::new(field, 3);
    // The read is the declared comparison (§16.30); the field's law lets a step stand unread.
    learner.read_held = true;
    let second_classes = [2usize, 2, 3, 1, 0, 4, 4];
    let second_open = [true, false, false, true, true, false, false];
    let second = Region { classes: &second_classes, unresolved: &second_open, faces: &[], locked: &[], echo: &[], domain: None, port: None };
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
            let compared_on = |field: &Field| compared(&[field.faces(&regions[0]).unwrap()], &regions).unwrap();
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
            assert_eq!(FieldLearner::from_text(&learner.to_text()).unwrap(), learner);
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
    let compared_on = |field: &Field| compared(&[field.faces(&regions[0]).unwrap()], &regions).unwrap();
    let old = compared_on(&material);
    // The covector is the code's gradient (a deposit subtracts the step), so the step that moved
    // the material to `material + sign(g) 2^k` climbed it; held, it is the negated sign.
    let g = covector_of(&material, &regions[0]);
    for k in [0u32, 3, 6] {
        let step: Vec<i128> = g.iter().map(|&v| -(v.signum() << k)).collect();
        let mut learner = FieldLearner::new(material.clone(), 2);
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

impl FieldRealization for Counted {
    fn read_and_return(&mut self, field: &Field, regions: &[Region]) -> Result<(Vec<Vec<Option<TowerFace>>>, Vec<i128>)> {
        self.reads += 1;
        field.read_and_return(regions)
    }
    fn read_faces(&mut self, field: &Field, regions: &[Region]) -> Result<Vec<Vec<Option<TowerFace>>>> {
        self.reads += 1;
        field.read_faces(regions)
    }
    fn read_logits(&mut self, field: &Field, regions: &[Region]) -> Result<Vec<FieldRead>> {
        self.reads += 1;
        field.read_logits(regions)
    }
    fn read_landmarks(&mut self, field: &Field, region: &Region, question: usize, sites: &[usize], count: usize) -> Result<Vec<Vec<(usize, u64)>>> {
        field.landmarks(region, question, sites, count)
    }
}


/// The founding draws the key and the probe apart (§16.19): each its own keyed draw, neither the other,
/// every class has a word in the encoding and both strand contacts, and the unresolved rows carry none.
#[test]
fn the_founding_draws_the_key_and_the_probe_apart() {
    let field = Field::found(tiny_declaration(1), &keys(1 << 14)).unwrap();
    let (dw, a, m2) = (field.declaration.width, field.declaration.alphabet, 2 * field.declaration.complex());
    let l = field.layout.clone();
    let (key, probe) = (&field.theta[l.q..l.q + m2 * dw], &field.theta[l.probe..l.probe + m2 * dw]);
    assert!(key.iter().any(|&v| v != 0) && probe.iter().any(|&v| v != 0));
    assert_ne!(key, probe, "the probe is not the key");
    let tm = field.declaration.moment_modes();
    assert_eq!(4 * field.declaration.founding_draws(), 4 * (3 * a * dw + 3 * m2 * dw + 2 * field.declaration.contacts * dw + 2 * tm * dw));
    let stream = keys(field.declaration.founding_draws());
    assert_eq!(Field::found(tiny_declaration(1), &stream).unwrap(), field, "the draws counted are the draws read");
    assert!(Field::found(tiny_declaration(1), &stream[..stream.len() - 1]).is_err());
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
    assert!(shaped(1).faces(&Region { classes: &one, unresolved: &[true], faces: &[], locked: &[], echo: &[], domain: None, port: None }).is_err(), "a lone site has no site to meet");
}

/// The contact's gain covers the falloff: the largest shift, negative where it amplifies, at which a
/// head's lock of an equal word (`n` at unit power, half its `2n` reals) reads `2⌈log₂ reach⌉` bits.
#[test]
fn the_contact_s_gain_covers_the_falloff() {
    let at = |modes: usize, reach: usize| FieldDeclaration { alphabet: 5, width: 8, heads: 2, modes, still: 1, contacts: 4, ticks: 2, frames: 2, reach, lanes: 1, depth: 0, energy: false }.score_shift();
    assert_eq!(at(8, 2221), -2, "reading 8's declaration locks an equal word at 32 bits");
    assert_eq!(at(16, 16), 1);
    assert_eq!(at(3, 16), -2);
    for (modes, reach) in [(8usize, 2221usize), (16, 16), (3, 16), (8, 2), (16, 1 << 20), (1, 1 << 20)] {
        let (beta, need) = (at(modes, reach), 2 * (u128::BITS - ((reach - 1) as u128).leading_zeros()).max(1) as u128);
        let gained = |b: i32| if b >= 0 { (modes as u128) >> b } else { (modes as u128) << -b };
        assert!(gained(beta) >= need && gained(beta + 1) < need, "the largest such shift: modes {modes} reach {reach}");
    }
    let d = FieldDeclaration { alphabet: 5, width: 8, heads: 2, modes: 8, still: 1, contacts: 4, ticks: 2, frames: 2, reach: 2221, lanes: 1, depth: 0, energy: false };
    assert_eq!((d.class_trits(), d.classes()), (4, 81), "81 classes at reading 8's reach");
    assert_eq!(FieldDeclaration { modes: 3, ..d }.class_trits(), 3);
    assert_eq!((FieldDeclaration { reach: 81, ..d }.class_trits(), FieldDeclaration { reach: 82, ..d }.class_trits()), (2, 3));
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
    let d = FieldDeclaration { alphabet: 5, width: 8, heads: 2, modes: 3, still: 1, contacts: 4, ticks: 2, frames: 2, reach: 32, lanes: 1, depth: 0, energy: false };
    let classes: Vec<usize> = (0..26).map(|t| [1usize, 3, 2, 4, 0, 2, 1][t % 7]).collect();
    let open: Vec<bool> = (0..26).map(|t| t % 9 == 4 || t == 25).collect();
    let r = Region { classes: &classes, unresolved: &open, faces: &[], locked: &[], echo: &[], domain: None, port: None };
    let sheets = |field: &Field| -> Vec<Vec<u32>> { field.pass(&r, true).unwrap().ticks.iter().flat_map(|c| c.classes.iter().map(|l| l.off.iter().chain(&l.members).copied().chain(l.probes.iter().flat_map(|p| std::iter::once(u32::MAX).chain(p.iter().copied()))).collect())).collect() };
    let (mut read, mut seams, mut far, mut halvings) = (0usize, 0usize, 0usize, 0u32);
    for still in [0usize, 1, 2] {
        let mut field = Field::found(FieldDeclaration { still, ..d }, &keys(1 << 14)).unwrap();
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
                    let code = |f: &Field| f.code(&r).unwrap().0;
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
    let d = FieldDeclaration { alphabet: 44, width: 32, heads: 5, modes: 8, still: 2, contacts: 32, ticks: 2, frames: 5, reach: 484, lanes: 1, depth: 0, energy: false };
    assert_eq!((d.score_shift(), d.listen_shift()), (-2, 2));
    let sites = 420;
    let classes = drawn_classes(7, sites, d.alphabet);
    let open: Vec<bool> = (0..sites).map(|t| t >= sites - 40 && t % 2 == 0).collect();
    let r = Region { classes: &classes, unresolved: &open, faces: &[], locked: &[], echo: &[], domain: None, port: None };
    let read = |field: &Field| -> (u128, u128) {
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
    let field = Field::found(d, &keys(1 << 20)).unwrap();
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
    let sheets = |field: &Field, r: &Region| -> Vec<Vec<u32>> { field.pass(r, true).unwrap().ticks.iter().flat_map(|c| c.classes.iter().map(|l| l.off.iter().chain(&l.members).copied().chain(l.probes.iter().flat_map(|p| std::iter::once(u32::MAX).chain(p.iter().copied()))).collect())).collect() };
    let long: Vec<usize> = (0..26).map(|t| [1usize, 3, 2, 4, 0, 2, 1][t % 7]).collect();
    let long_open: Vec<bool> = (0..26).map(|t| t % 9 == 4 || t == 25).collect();
    // [§16.47] A silent stretch of six places past the last arrival, whose rates return to its first place.
    let stretch_open: Vec<bool> = (0..26).map(|t| t % 9 == 4 || t >= 20).collect();
    let (mut read, mut seams) = (0usize, 0usize);
    for (still, depth) in [(0usize, 0usize), (1, 0), (0, 1), (1, 1)] {
        let mut d = tiny_declaration(still);
        d.reach = 32;
        d.depth = depth;
        let mut field = Field::found(d, &keys(1 << 14)).unwrap();
        let stream = keys(1 << 15);
        for (k, v) in field.theta.iter_mut().enumerate() {
            let word = &stream[4 * k..4 * k + 4];
            let grain = field.layout.families.iter().find(|(s, l, _)| (*s..*s + *l).contains(&k)).unwrap().2;
            *v = (((i32::from_be_bytes([word[0], word[1], word[2], word[3]]) as i64) << grain) >> 32) as i32;
        }
        for r in [region(), Region { classes: &long, unresolved: &long_open, faces: &[], locked: &[], echo: &[], domain: None, port: None }, Region { classes: &long, unresolved: &stretch_open, faces: &[], locked: &[], echo: &[], domain: None, port: None }] {
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
                if Field::silent(&r, t) {
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
    let stretch = Region { classes: &long, unresolved: &open, faces: &[], locked: &[], echo: &[], domain: None, port: None };
    assert_eq!(Field::silent_stretch(&stretch), 7);
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
    let ring = shaped_with(FieldDeclaration { depth: 1, ..tiny_declaration(1) });
    for cell in &ring.pass(&stretch, true).unwrap().ticks[1..] {
        let clock = cell.clock.as_ref().expect("a later tick reads its own clocks");
        for kappa in &clock.paces.kappa {
            for t in (0..14).filter(|&t| Field::silent(&stretch, t)) {
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
    let founded = Field::found(tiny_declaration(1), &keys(1 << 14)).unwrap();
    let long: Vec<usize> = (0..14).map(|t| [1usize, 3, 2, 4, 0, 2, 1][t % 7]).collect();
    let open: Vec<bool> = (0..14).map(|t| t % 3 == 1).collect();
    let r = Region { classes: &long, unresolved: &open, faces: &[], locked: &[], echo: &[], domain: None, port: None };
    assert!(founded.covector_shares(&[r]).unwrap().iter().all(|&[near, far]| near == 0 && far == 0));
    let shaped = shaped(1);
    let shares = shaped.covector_shares(&[r]).unwrap();
    assert_eq!(shares.len(), shaped.declaration.heads);
    assert!(shares.iter().all(|&[near, _]| near > 0), "{shares:?}");
    assert!(shares.iter().any(|&[_, far]| far > 0), "{shares:?}");
}

/// The field with its moment's chart into the face and its bias silent (the opening before §16.22).
fn silent_moment_face(mut field: Field) -> Field {
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
    let r = Region { classes: &WORDS, unresolved: &KNOWN, faces: &[], locked: &[], echo: &[], domain: None, port: None };
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
    let field = Field::found(tiny_declaration(1), &keys(1 << 14)).unwrap();
    let silent = silent_moment_face(field.clone());
    assert_ne!(field, silent, "the chart is drawn at the founding");
    assert_eq!(field.opening(&r).unwrap(), silent.opening(&r).unwrap());
    assert_eq!(field.faces(&region()).unwrap(), silent.faces(&region()).unwrap());
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
    let r = Region { classes: &CLASSES, unresolved: &PORTED, faces: &[], locked: &[], echo: &[], domain: None, port: Some(Port { start: 4, void: 0, target: &target, boundary: false, stop: None, heard: None, window: false, letters: false, pull: None }) };
    let faces = field.faces(&r).unwrap();
    let place = faces[1].as_ref().unwrap().code(CLASSES[1]);
    let at: Vec<(&[u128], u128)> = faces[4..].iter().map(|f| { let f = f.as_ref().unwrap(); (f.masses.as_slice(), f.total) }).collect();
    let coupled = crate::receiver::coupling::coupling_code(&at, 0, &target, None).unwrap().code;
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
    use crate::hnn::tower::face_code;
    let field = shaped(1);
    const PORTED: [bool; 7] = [false, true, false, false, true, true, true];
    let target = [2usize, 3];
    let port = Port { start: 4, void: 0, target: &target, boundary: true, stop: None, heard: None, window: false, letters: false, pull: None };
    let r = Region { classes: &CLASSES, unresolved: &PORTED, faces: &[], locked: &[], echo: &[], domain: None, port: Some(port) };
    let faces = field.faces(&r).unwrap();
    let at: Vec<(&[u128], u128)> = faces[4..].iter().map(|f| { let f = f.as_ref().unwrap(); (f.masses.as_slice(), f.total) }).collect();
    let (rows, code) = port_reading(&at, &port).unwrap();
    let mut expected = 0i64;
    let one = 1i64 << crate::hnn::tower::COVECTOR_BITS;
    for (i, ((masses, total), row)) in at.iter().zip(&rows).enumerate() {
        let share = |a: usize| (((masses[a] << crate::hnn::tower::COVECTOR_BITS) + total / 2) / total) as i64;
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
            let r = Region { classes: &classes, unresolved: &open, faces: &[], locked: &[], echo: &[], domain: None, port: None };
            field.faces(&r).unwrap()[..CLASSES.len()].to_vec()
        };
        assert_eq!(stretched(ticks + 2), stretched(ticks + 5), "still {still}");
    }
}


/// [§16.30] **A step stands at the size its own section certified**: under the field's law no step is held, the next
/// section opens on the stepped material, and its receipt reads no held step.
#[test]
fn a_step_stands_unread_at_its_certified_size() {
    let field = Field::found(tiny_declaration(1), &keys(1 << 14)).unwrap();
    let mut learner = FieldLearner::new(field, 2);
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
        let once = field.sample_realized(&problems, 4, 0, 0, seed, &mut HostField, &mut |_, _| true).unwrap();
        let refined = field.sample_realized(&problems, 4, 2, 0, seed, &mut HostField, &mut |_, _| true).unwrap();
        assert_eq!(field.sample_realized(&problems, 4, 2, 0, seed, &mut HostField, &mut |_, _| true).unwrap(), refined, "the same draws");
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
    let pointed = field.sample_realized(&problems, 3, 2, 0, 11, &mut HostField, &mut |_, _| true).unwrap();
    assert!(pointed.iter().flatten().all(|&c| c == 2), "{pointed:?}");
}

/// The host realization, the regions each read meets counted.
struct RegionsCounted {
    regions: Vec<usize>,
}

impl FieldRealization for RegionsCounted {
    fn read_and_return(&mut self, field: &Field, regions: &[Region]) -> Result<(Vec<Vec<Option<TowerFace>>>, Vec<i128>)> {
        field.read_and_return(regions)
    }
    fn read_faces(&mut self, field: &Field, regions: &[Region]) -> Result<Vec<Vec<Option<TowerFace>>>> {
        self.regions.push(regions.len());
        field.read_faces(regions)
    }
    fn read_logits(&mut self, field: &Field, regions: &[Region]) -> Result<Vec<FieldRead>> {
        field.read_logits(regions)
    }
    fn read_landmarks(&mut self, field: &Field, region: &Region, question: usize, sites: &[usize], count: usize) -> Result<Vec<Vec<(usize, u64)>>> {
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
            alone.push(field.sample_realized(&padded, 9, 2, 0, seed, &mut HostField, &mut |_, _| true).unwrap().pop().unwrap());
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
        let field = shaped_with(FieldDeclaration { reach: 96, ticks, ..tiny_declaration(still) });
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
            let full = field.faces(&Region { classes: &classes, unresolved: &open, faces: &[], locked: &[], echo: &[], domain: None, port: None }).unwrap();
            let short = field.faces(&Region { classes: &classes[..cut], unresolved: &open[..cut], faces: &[], locked: &[], echo: &[], domain: None, port: None }).unwrap();
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
/// `Field::bare_stretch` every silent place past the region's last arrival runs at one on a turned head (its clock the place
/// count), reads no face and takes no covector, while a silent place between arrivals keeps its own face's rate.
#[test]
fn past_the_last_arrival_a_place_runs_at_the_bare_rate() {
    let mut field = shaped(0);
    field.bare_stretch = true;
    let long: Vec<usize> = (0..14).map(|t| [1usize, 3, 2, 4, 0, 2, 1][t % 7]).collect();
    let open: Vec<bool> = (0..14).map(|t| t == 2 || t >= 7).collect();
    let r = Region { classes: &long, unresolved: &open, faces: &[], locked: &[], echo: &[], domain: None, port: None };
    assert_eq!(Field::silent_stretch(&r), 7);
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
            let field = shaped_with(FieldDeclaration { reach: 400, ticks, ..tiny_declaration(still) });
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
                port: Some(Port { start: q.len(), void: 0, target: &target, boundary: true, stop: None, heard: Some(&heard), window, letters: false, pull: None }),
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
        let one = field.sample_observed(&problems, 9, 2, 0, seed, &mut HostField, &mut |_, _| true, &mut |_| {}).unwrap();
        assert_eq!(field.sample_runs(&problems, 9, 2, 0, seed, 0, true, false, None, false, false, false, None, RefineOrder::Keyed, &mut HostField, &mut |_, _| true, &mut |_| {}).unwrap(), one, "no bound, one place a read");
        let mut counted = RegionsCounted { regions: Vec::new() };
        field.sample_runs(&problems, 9, 2, 0, seed, 0, true, false, None, false, false, false, None, RefineOrder::Keyed, &mut counted, &mut |_, _| true, &mut |_| {}).unwrap();
        reads_one += counted.regions.len();
        let mut counted = RegionsCounted { regions: Vec::new() };
        let mut last: Option<Vec<usize>> = None;
        let run = field
            .sample_runs(&problems, 9, 2, 0, seed, 1 << 20, true, false, None, false, false, false, None, RefineOrder::Keyed, &mut counted, &mut |_, _| true, &mut |r| {
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

/// [definition; agent-inferred, November 6, Brandon's lens of 17:31 and the unified-theory reading of 17:38] **An answer rests
/// where its drive is spent**: each refine pass's [`PassDrive`] sums the faces its draws were read from (their entropies
/// beside the faces the release shows, the letters' face before the last letter), and with `rest` an answer is redrawn in pass `p + 1` exactly while no pass so far had
/// `D ≤ √C` or a fall of `D` within `√C`; without it every answer walks every pass. A face's varentropy is its codes' spread.
#[test]
fn an_answer_rests_where_its_drive_is_spent() {
    let uniform = TowerFace { masses: vec![1, 1, 1, 1], total: 4 };
    assert_eq!((entropy(&uniform), varentropy(&uniform)), (2 << 20, 0));
    let skew = TowerFace { masses: vec![3, 1], total: 4 };
    // `Var = ¾ log₂²(4/3) + ¼ · 2² − H² ≈ 0.4715` bits², on `2^(−40)`.
    let v = varentropy(&skew);
    assert!((v - 4715 * (1i128 << 40) / 10_000).abs() < (1i128 << 40) / 1000, "{v}");
    let mut one = PassDrive::default();
    one.add(&skew, 1);
    assert_eq!((one.redrawn, one.standing, one.entropy), (1, 2 << 20, entropy(&skew)));
    assert_eq!(one.equilibrium, (1 << 20) - ((1 << 20) * 10 / 16), "1 − (9 + 1)/16");
    let field = shaped(1);
    let questions: [&[usize]; 3] = [&[1, 4, 0, 2], &[3, 3], &[2, 1, 1]];
    let problems: Vec<(&[usize], usize)> = questions.iter().zip([9usize, 8, 12]).map(|(q, a)| (*q, a)).collect();
    let refine = 12;
    let (mut rested, mut changed) = (0usize, 0usize);
    for seed in 3..15 {
        for rest in [false, true] {
            let mut entropies: std::collections::BTreeMap<(usize, usize), i128> = std::collections::BTreeMap::new();
            let mut drives: Vec<Vec<PassDrive>> = Vec::new();
            field
                .sample_runs(&problems, 9, refine, 0, seed, 1 << 20, true, false, None, false, rest, false, None, RefineOrder::Keyed, &mut HostField, &mut |_, _| true, &mut |r| {
                    if let (true, Some(faces)) = (r.pass >= 1, r.faces) {
                        for k in 0..problems.len() {
                            let q = problems[k].0.len();
                            let end = (q..r.classes[k].len()).find(|&t| r.classes[k][t] == 0 && !r.open[k][t]).unwrap_or(r.classes[k].len());
                            for t in (0..r.classes[k].len()).filter(|&t| r.open[k][t]) {
                                let face = faces[k][t].as_ref().unwrap();
                                let drawn = if t + 1 >= end { Some(face.clone()) } else { letters_face(face, 0) };
                                *entropies.entry((k, r.pass)).or_default() += drawn.map_or(0, |f| entropy(&f));
                            }
                        }
                    }
                    drives = r.drives.to_vec();
                })
                .unwrap();
            for (k, passes) in drives.iter().enumerate() {
                let shown: Vec<i128> = (1..=passes.len()).map(|p| entropies[&(k, p)]).collect();
                assert_eq!(passes.iter().map(|d| d.entropy).collect::<Vec<_>>(), shown, "seed {seed}: the drives sum the faces the draws were read from");
                assert!(!entropies.contains_key(&(k, passes.len() + 1)), "seed {seed}: no pass past the drives'");
                changed += passes.iter().map(|d| d.changes).sum::<usize>();
                if !rest {
                    assert_eq!(passes.len(), refine, "seed {seed}: without rest every pass");
                    continue;
                }
                let stop = (0..refine).find(|&i| passes.get(i).is_some_and(|d| d.rests(i.checked_sub(1).map(|j| passes[j].drive()))));
                assert_eq!(passes.len(), stop.map_or(refine, |i| i + 1), "seed {seed} problem {k}: it rests after its first spent pass");
                rested += usize::from(passes.len() < refine);
            }
        }
    }
    assert!(rested > 0 && changed > 0, "{rested} answers rested, {changed} letters changed");
}

/// [definition; agent-inferred, November 6, the unified-theory reading of 17:58] **A span pass opens a span whole**: with
/// `spans`, at every read of an even refine pass each answer's open places are the rest of one span in place order (a
/// contiguous run of places, at most the pass's span length, `2^(1 + (m − 1) mod 4)` at the `m`-th span pass), every place
/// before the pass's boundary is redrawn once in it, and the closing law holds after the release; odd passes stay single
/// places and runs.
#[test]
fn a_span_pass_opens_a_span_whole() {
    let field = shaped(1);
    let questions: [&[usize]; 3] = [&[1, 4, 0, 2], &[3, 3], &[2, 1, 1]];
    let problems: Vec<(&[usize], usize)> = questions.iter().zip([9usize, 8, 12]).map(|(q, a)| (*q, a)).collect();
    let (mut widest, mut spanned) = (0usize, 0usize);
    for seed in 3..11 {
        let mut drawn: std::collections::BTreeMap<(usize, usize), std::collections::BTreeSet<usize>> = std::collections::BTreeMap::new();
        let written = field
            .sample_runs(&problems, 9, 8, 0, seed, 1 << 20, true, false, Some(&[6, 5, 9]), false, false, true, None, RefineOrder::Keyed, &mut HostField, &mut |_, _| true, &mut |r| {
                if r.pass == 0 || r.faces.is_none() {
                    return;
                }
                for (k, &(q, _)) in problems.iter().enumerate() {
                    let opened: Vec<usize> = (q.len()..r.classes[k].len()).filter(|&t| r.open[k][t]).collect();
                    drawn.entry((k, r.pass)).or_default().extend(opened.iter().copied());
                    if r.pass % 2 == 0 && !opened.is_empty() {
                        let length = 1usize << (1 + (r.pass / 2 - 1) % 4);
                        assert!(opened.windows(2).all(|w| w[1] == w[0] + 1), "seed {seed}: a span's open places are contiguous");
                        assert!(opened.len() <= length, "seed {seed} pass {}: {} open, span {length}", r.pass, opened.len());
                        widest = widest.max(opened.len());
                        spanned += usize::from(opened.len() > 1);
                    }
                }
            })
            .unwrap();
        for (k, &(q, _)) in problems.iter().enumerate() {
            let length = [6usize, 5, 9][k];
            for pass in 1..=8 {
                let places: Vec<usize> = drawn[&(k, pass)].iter().copied().collect();
                assert_eq!(places, (q.len()..q.len() + length).collect::<Vec<_>>(), "seed {seed} problem {k} pass {pass}: each place once");
            }
            assert!(written[k][..length].iter().all(|&c| c != 0) && written[k][length..].iter().all(|&c| c == 0), "seed {seed}: the given length holds");
        }
    }
    assert!(spanned > 0 && widest > 2, "spans opened ({spanned} reads, widest {widest})");
}

/// [measurement; agent-inferred, November 6, the unified-theory reading of 21:14] **A refine pass walks its declared scan**:
/// one place a read, each place before the given length redrawn once a pass, in place order, in reversed place order, or
/// (keyed) in an order that is neither on some pass.
#[test]
fn a_refine_pass_walks_its_declared_scan() {
    let field = shaped(1);
    let questions: [&[usize]; 3] = [&[1, 4, 0, 2], &[3, 3], &[2, 1, 1]];
    let problems: Vec<(&[usize], usize)> = questions.iter().zip([9usize, 8, 12]).map(|(q, a)| (*q, a)).collect();
    let lengths = [6usize, 5, 9];
    let mut keyed_scrambled = false;
    for order in [RefineOrder::Place, RefineOrder::Reversed, RefineOrder::Keyed] {
        for seed in 3..9 {
            let mut walked: std::collections::BTreeMap<(usize, usize), Vec<usize>> = std::collections::BTreeMap::new();
            field
                .sample_runs(&problems, 9, 4, 0, seed, 0, true, false, Some(&lengths), false, false, false, None, order, &mut HostField, &mut |_, _| true, &mut |r| {
                    if r.pass == 0 || r.faces.is_none() {
                        return;
                    }
                    for (k, &(q, _)) in problems.iter().enumerate() {
                        let opened: Vec<usize> = (q.len()..r.classes[k].len()).filter(|&t| r.open[k][t]).collect();
                        assert!(opened.len() <= 1, "seed {seed}: one place a read at run bits 0, {opened:?}");
                        walked.entry((k, r.pass)).or_default().extend(opened);
                    }
                })
                .unwrap();
            for (k, &(q, _)) in problems.iter().enumerate() {
                let places: Vec<usize> = (q.len()..q.len() + lengths[k]).collect();
                for pass in 1..=4 {
                    let scan = &walked[&(k, pass)];
                    let mut sorted = scan.clone();
                    sorted.sort_unstable();
                    assert_eq!(sorted, places, "{order:?} seed {seed} problem {k} pass {pass}: each place once");
                    match order {
                        RefineOrder::Place => assert_eq!(scan, &places, "seed {seed}: place order"),
                        RefineOrder::Reversed => assert!(scan.iter().rev().eq(places.iter()), "seed {seed}: reversed place order, {scan:?}"),
                        RefineOrder::Keyed => keyed_scrambled |= scan != &places && !scan.iter().rev().eq(places.iter()),
                    }
                }
            }
        }
    }
    assert!(keyed_scrambled, "the keyed order is neither scan on some pass");
}

/// [measurement; agent-inferred, November 6, the unified-theory reading of 18:28] **A walk from given answers** reads them
/// first: no sweep is drawn, the first refine pass keeps every standing letter (its changes none, its drive read on the
/// given answers), so one pass returns the answers as given, and later passes walk from them.
#[test]
fn a_walk_from_given_answers_reads_them_first() {
    let field = shaped(1);
    let questions: [&[usize]; 2] = [&[1, 4, 0, 2], &[3, 3]];
    let problems: Vec<(&[usize], usize)> = questions.iter().zip([9usize, 8]).map(|(q, a)| (*q, a)).collect();
    let answers = vec![vec![2usize, 3, 1, 4, 2, 1], vec![1usize, 1, 2, 3, 4]];
    let lengths = [6usize, 5];
    let mut moved = 0usize;
    for seed in 3..9 {
        for refine in [1usize, 3] {
            let mut sweeps = 0usize;
            let mut drives: Vec<Vec<PassDrive>> = Vec::new();
            let written = field
                .sample_runs(&problems, 9, refine, 0, seed, 1 << 20, true, false, Some(&lengths), false, false, false, Some(&answers), RefineOrder::Keyed, &mut HostField, &mut |_, _| true, &mut |r| {
                    sweeps += usize::from(r.pass == 0 && r.faces.is_some());
                    drives = r.drives.to_vec();
                })
                .unwrap();
            assert_eq!(sweeps, 0, "no sweep is drawn");
            for k in 0..2 {
                assert_eq!(drives[k].len(), refine);
                assert_eq!((drives[k][0].redrawn, drives[k][0].changes), (lengths[k], 0), "the first pass reads every place and keeps it");
                assert!(written[k][lengths[k]..].iter().all(|&c| c == 0));
                if refine == 1 {
                    assert_eq!(written[k][..lengths[k]], answers[k][..], "one pass returns the answers as given");
                } else {
                    moved += drives[k][1..].iter().map(|d| d.changes).sum::<usize>();
                }
            }
        }
    }
    assert!(moved > 0, "later passes walk");
}

/// [definition; the unified-theory reading of November 6, 19:04] **A declared pull** reads `w (c(b) − c(a))` on its first
/// place's face and returns `w (e_a − e_b)` there, nothing at its later places, and refuses a class the face does not hold.
#[test]
fn a_pull_reads_its_two_classes_ratio() {
    let face = TowerFace { masses: vec![1, 3, 4], total: 8 };
    let empty = TowerFace { masses: Vec::new(), total: 0 };
    let faces = [(face.masses.as_slice(), face.total), (empty.masses.as_slice(), 0)];
    let port = Port { start: 0, void: 0, target: &[], boundary: false, stop: None, heard: None, window: false, letters: false, pull: Some((2, 1, 1 << 20)) };
    let (rows, code) = port_reading(&faces, &port).unwrap();
    assert_eq!(rows, vec![vec![0, -(1 << 24), 1 << 24], Vec::new()]);
    // c(1) − c(2) = log₂(4/3) bits.
    assert_eq!(code, face.code(1) - face.code(2));
    let half = Port { pull: Some((2, 1, -(1 << 19))), ..port };
    assert_eq!(port_reading(&faces, &half).unwrap().1, -((face.code(1) - face.code(2) + 1) / 2));
    let missing = TowerFace { masses: vec![1, 0, 4], total: 5 };
    assert!(port_reading(&[(missing.masses.as_slice(), missing.total)], &port).is_err());
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
                .sample_runs(&problems, 4, 0, 0, seed, run_bound, true, false, None, false, false, false, None, RefineOrder::Keyed, &mut HostField, &mut |_, _| true, &mut |r| {
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
            let written = field.sample_runs(&problems, 4, 2, 0, seed, run_bound, true, false, Some(&[3, 5]), false, false, false, None, RefineOrder::Keyed, &mut HostField, &mut |_, _| true, &mut |_| {}).unwrap();
            for (places, l) in written.iter().zip([3usize, 5]) {
                assert!(places[..l].iter().all(|&c| c != 0), "a void inside the given length, seed {seed}: {places:?}");
                assert!(places[l..].iter().all(|&c| c == 0), "a letter past the given length, seed {seed}: {places:?}");
            }
            // One end, one draw: the length drawn from the first read is kept the same way.
            let drawn = field.sample_runs(&problems, 4, 2, 0, seed, run_bound, true, false, None, true, false, false, None, RefineOrder::Keyed, &mut HostField, &mut |_, _| true, &mut |_| {}).unwrap();
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
    let whole = Region { classes: &classes, unresolved: &open, faces: &[], locked: &[], echo: &[], domain: None, port: None };
    let read = field.read_active(&[q.len()], std::slice::from_ref(&classes), std::slice::from_ref(&open), &[0], 0, true, &mut HostField).unwrap().remove(0);
    assert_eq!(read, field.faces(&whole).unwrap(), "before any void the region is read whole");
    let end = 8;
    for t in end..classes.len() {
        classes[t] = 0;
        open[t] = false;
    }
    let read = field.read_active(&[q.len()], std::slice::from_ref(&classes), std::slice::from_ref(&open), &[0], 0, true, &mut HostField).unwrap().remove(0);
    let cut = Region { classes: &classes[..end + NEAR], unresolved: &open[..end + NEAR], faces: &[], locked: &[], echo: &[], domain: None, port: None };
    let short = field.faces(&cut).unwrap();
    assert_eq!(read.len(), classes.len());
    assert_eq!(&read[..end + NEAR], &short[..], "the faces are the cut region's");
    assert!(read[end + NEAR..].iter().all(Option::is_none), "no face past the cut");
    let room = field.read_active(&[q.len()], std::slice::from_ref(&classes), std::slice::from_ref(&open), &[0], 0, false, &mut HostField).unwrap().remove(0);
    assert_eq!(room, field.faces(&Region { classes: &classes, unresolved: &open, faces: &[], locked: &[], echo: &[], domain: None, port: None }).unwrap(), "the whole room, declared");
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
            .sample_observed(&problems, 9, 0, 0, seed, &mut HostField, &mut |_, _| true, &mut |r| {
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
        let mut last: Option<Vec<usize>> = None;
        for refine in [3] {
        last = None;
        field
            .sample_observed(&problems, 4, refine, 0, seed, &mut HostField, &mut |_, _| true, &mut |r| {
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

/// The packets' field of the tower fixtures: packets of three sites of the tiny field's reach of 16.
fn coarse_declaration() -> FieldDeclaration {
    FieldDeclaration { alphabet: 2, width: 8, heads: 2, modes: 3, still: 1, contacts: 4, ticks: 2, frames: 2, reach: 6, lanes: 1, depth: 0, energy: false }
}

/// A tower of scales on [`shaped`]`(still)`: packets of three sites after the first of its two ticks, founded from the
/// fixtures' keys past the fine field's founding.
fn towered(still: usize) -> Field {
    let field = shaped(still);
    let offset = 4 * field.declaration.founding_draws();
    field.scaled_up(3, 1, coarse_declaration(), &keys(1 << 15), offset).unwrap().0
}

/// [`towered`] with its prolongation and every family of its packets' field drawn, so every path of the tower carries a
/// covector.
fn towered_live(still: usize) -> Field {
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
fn tower_covector(field: &Field, region: &Region) -> Vec<i128> {
    let pass = field.pass(region, true).unwrap();
    let mut g = vec![0i128; field.material_len()];
    field.returned(region, &pass, &mut g).unwrap();
    g
}

/// [definition; the tower record, D1] **Growth in scale keeps every face**: a tower founded on a field (its prolongation
/// at zero) reads every face the field read, its families tile its material, and its text restores it exactly.
#[test]
fn a_tower_founded_on_a_field_reads_its_faces() {
    for still in [0usize, 1, 2] {
        let field = shaped(still);
        let tower = towered(still);
        assert_eq!(tower.faces(&region()).unwrap(), field.faces(&region()).unwrap(), "still {still}");
        let mut at = 0;
        for (start, len, _) in tower.families_all() {
            assert_eq!(start, at);
            at += len;
        }
        assert_eq!(at, tower.material_len());
        assert_eq!(Field::from_text(&tower.to_text()).unwrap(), tower);
    }
    let mut learner = FieldLearner::new(towered_live(1), 6);
    learner.section(&[region()]).unwrap();
    assert_eq!(FieldLearner::from_text(&learner.to_text()).unwrap(), FieldLearner { last: None, ..learner });
}

/// [definition; the tower record, D1] **The tower's covector agrees with its code's central difference** on the packets'
/// field's families and the glue's: each family's three entries with the largest covectors, moved by `±δ` (the probe law of
/// [`covector_matches_the_codes_difference`], a probe whose step moves a site or a packet across a sheet left out and
/// counted), and the live prolongation reaching the code at the bytes.
#[test]
fn the_towers_covector_matches_its_codes_difference() {
    let sheets = |field: &Field, r: &Region| -> Vec<Vec<u32>> {
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
            assert_eq!(Field::from_text(&next.to_text()).unwrap(), next);
            laned = next;
        }
        let g = covector_of(&laned, &region());
        let (l, dw, m2) = (laned.layout.clone(), laned.declaration.width, 2 * laned.declaration.complex());
        assert!((0..m2).any(|row| (8..dw).any(|j| g[l.q + row * dw + j] != 0)), "still {still}: the key chart's reads from the lanes carry a covector");
    }
    let mut learner = FieldLearner::new(Field::found(tiny_declaration(1), &keys(1 << 14)).unwrap(), 4);
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
    let back = FieldLearner { read_held: laned.read_held, ..FieldLearner::from_text(&laned.to_text()).unwrap() };
    assert_eq!(back, laned);
}

/// [definition; §16.40] **A laned field's covector agrees with its code's central difference**: on a field of two lanes
/// with every family shaped, each family's three entries with the largest covectors (the probe law of
/// [`covector_matches_the_codes_difference`], a probe whose step moves a site across a sheet left out and counted), so each
/// lane's chart and its adjoint are read on their own.
#[test]
fn the_laned_fields_covector_matches_its_codes_difference() {
    let sheets = |field: &Field, r: &Region| -> Vec<Vec<u32>> { field.pass(r, true).unwrap().ticks.iter().flat_map(|c| c.classes.iter().map(|l| l.off.iter().chain(&l.members).copied().chain(l.probes.iter().flat_map(|p| std::iter::once(u32::MAX).chain(p.iter().copied()))).collect())).collect() };
    let (mut read, mut seams) = (0usize, 0usize);
    for still in [0usize, 1, 2] {
        let field = shaped_with(FieldDeclaration { width: 16, lanes: 2, ..tiny_declaration(still) });
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
        let mut learner = FieldLearner::new(shaped(still), 14);
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
    let second = [Region { classes: &second_classes, unresolved: &second_open, faces: &[], locked: &[], echo: &[], domain: None, port: None }];
    let code_on = |field: &Field| code_of(&compared(&[field.faces(&second[0]).unwrap()], &second).unwrap(), &spans_of(&second));
    let mut read = 0;
    for still in [0usize, 1, 2] {
        let mut learner = FieldLearner::new(shaped(still), 14);
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

/// An energy field ([`FieldDeclaration::energy`]) on the tiny declaration, every family drawn as [`shaped`]'s, its clocks
/// plain (the pace rows at zero) and the families the energy does not read at zero.
fn energetic(still: usize) -> Field {
    let mut field = shaped_with(FieldDeclaration { energy: true, ..tiny_declaration(still) });
    let (l, d) = (field.layout.clone(), field.declaration);
    let (dw, m2) = (d.width, 2 * d.complex());
    field.theta[l.pace..l.pace + d.paced_heads() * (d.alphabet + 1)].fill(0);
    // The letters read the energy at `T = 1`.
    field.theta[l.face_temper] = 0;
    for (start, len) in [(l.v, m2 * dw), (l.v_bias, m2), (l.out, dw * m2), (l.out_bias, dw), (l.w, dw * d.contacts), (l.w_bias, dw)] {
        field.theta[start..start + len].fill(0);
    }
    field
}

/// [definition; the unified-theory reading of November 6, 22:52] **An energy field states its law**: its head line is
/// `hnn-field-v15` with the energy word, a v14 line reads as a field whose faces are read through the readout, its
/// material carries the pair's contraction past every other family, and its founding is the line's with the value chart
/// at zero.
#[test]
fn an_energy_head_line_states_its_law() {
    let d = FieldDeclaration { energy: true, ..tiny_declaration(1) };
    let text = d.to_text();
    assert!(text.starts_with("hnn-field-v15 ") && text.ends_with(" 1"), "{text}");
    assert_eq!(FieldDeclaration::from_text(&text).unwrap(), d);
    let plain = tiny_declaration(1).to_text();
    let v14 = plain[..plain.rfind(' ').unwrap()].replace("hnn-field-v15", "hnn-field-v14");
    assert_eq!(FieldDeclaration::from_text(&v14).unwrap(), tiny_declaration(1));
    assert_eq!(FieldLayout::new(&d).len, FieldLayout::new(&tiny_declaration(1)).len + d.contacts + 1);
    let (e, f) = (Field::found(d, &keys(1 << 14)).unwrap(), Field::found(tiny_declaration(1), &keys(1 << 14)).unwrap());
    let l = e.layout.clone();
    let vlen = 2 * d.complex() * d.width;
    assert!(e.theta[l.v..l.v + vlen].iter().all(|&v| v == 0));
    assert_eq!(e.theta[..l.v], f.theta[..l.v]);
    assert_eq!(e.theta[l.v + vlen..l.pair_c], f.theta[l.v + vlen..]);
    assert!(e.theta[l.pair_c..].iter().all(|&v| v == 0));
}

/// [definition; the unified-theory reading of November 6, 22:52] **Each tick descends the energy**: on every ring set the
/// energy at the last tick is below the opening's, some tick's fall is certified, and the faces stand at the unresolved
/// sites alone.
#[test]
fn each_energy_tick_falls() {
    for still in 0..=2 {
        let field = energetic(still);
        let read = field.energy_read(&region()).unwrap();
        assert!(read.last < read.opening, "still {still}: {read:?}");
        assert!(read.halvings.iter().any(Option::is_some), "still {still}: {read:?}");
        let faces = field.faces(&region()).unwrap();
        for (t, &open) in OPEN.iter().enumerate() {
            assert_eq!(faces[t].is_some(), open, "still {still} site {t}");
        }
    }
}

/// [definition; the unified-theory reading of November 7, 00:02] **The face is the total derivative of one scalar**:
/// `z_t(a) = −dG/de_t(a)`, `G(e) = Φ(x^K(e); e)` read through the opening and the ticks at the base's halvings and supports,
/// so at every open site a central difference of `G` across the site's mixture moved by `±ε(δ_b − δ_a)` reads
/// `−2ε(z_t(b) − z_t(a))` to the difference's own curvature, on every ring set.
#[test]
fn an_energy_face_is_the_total_derivative() {
    let eps = 1i128 << 9;
    for still in 0..=2 {
        let field = energetic(still);
        let r = region();
        let logits = field.logits(&r).unwrap();
        let alphabet = field.declaration.alphabet as u32;
        let base = (1u32 << 16) / alphabet;
        for t in (0..OPEN.len()).filter(|&t| OPEN[t]) {
            let z = logits[t].as_ref().unwrap();
            for (a, b) in [(0u32, 1u32), (2, 4), (3, 1)] {
                let moved = |sign: i128| -> Shares { (0..alphabet).map(|c| (c, (base as i128 + if c == b { sign * eps } else if c == a { -sign * eps } else { 0 }) as u32)).collect() };
                let dg = field.energy_g_at(&r, t, &moved(1)).unwrap() - field.energy_g_at(&r, t, &moved(-1)).unwrap();
                let predicted = -2 * eps * (z[b as usize] - z[a as usize]) as i128;
                // A tenth of the reading for the difference's curvature, and 2^23 (2^(−9) bits) for the replayed states'
                // rounding at the state's grain (measured: the gap falls with ε where the reading is large, and scatters by
                // about 2^21 where it is small).
                assert!(10 * (dg - predicted).abs() <= predicted.abs() + (10 << 23), "still {still} site {t} letters {a}, {b}: ΔG {dg} against −2ε Δz {predicted} (2^(−32) bits)");
            }
        }
    }
}

/// [definition; the unified-theory reading of November 6, 22:52] **The force is the energy's slope**: at the opening, a
/// small step's fall is its first-order fall `η Σ_t (|F_t|² − ⟨r̂_t, F_t⟩²/W)` to within the step's own curvature, on every
/// ring set, with the pair's contraction, the moments and the readout drawn.
#[test]
fn the_energy_force_is_its_slope() {
    for still in 0..=2 {
        let field = energetic(still);
        // Steps of 2^(−8) and 2^(−10) of a site's scale: a larger step reads the energy's curvature, a smaller one nears the
        // state's grain and the fall its rounding.
        for h in [8u32, 10] {
            let (predicted, actual, _) = field.energy_fall(&region(), 0, h).unwrap();
            assert!(predicted > 0 && 20 * (actual - predicted).abs() <= predicted, "still {still} h {h}: fall {actual} against its first order {predicted} (2^(−32) bits)");
        }
    }
}

/// [definition; the unified-theory reading of November 7, 00:02] **The force's tangent is the energy's Hessian on a
/// direction**: at the opening, on every ring set, the tangent along a keyed lane-tangent direction matches the force's
/// difference across a small step to within a tenth of its size, and the Hessian it stands for is symmetric
/// (`⟨u, H v⟩ = ⟨v, H u⟩` to a hundredth).
#[test]
fn the_force_tangent_is_the_energy_hessian() {
    for still in 0..=2 {
        let field = energetic(still);
        for seed in [3u64, 5] {
            let (tangent, difference, uv, vu) = field.energy_tangent_check(&region(), 8, seed).unwrap();
            let norm = |a: &[i64]| -> i128 { a.iter().map(|&x| x as i128 * x as i128).sum() };
            let gap: Vec<i64> = tangent.iter().zip(&difference).map(|(&a, &b)| a - b).collect();
            assert!(100 * norm(&gap) <= norm(&tangent), "still {still} seed {seed}: |δF − ΔF|² {} against |δF|² {}", norm(&gap), norm(&tangent));
            assert!(100 * (uv - vu).abs() <= uv.abs() + vu.abs(), "still {still} seed {seed}: ⟨u, Hv⟩ {uv} against ⟨v, Hu⟩ {vu}");
        }
    }
}

/// [definition; the unified-theory reading of November 7, 00:02] **A square agrees at one base** (theory's build identity):
/// as the face is one scalar's gradient, a square read at one base reads `λ_i = λ_j` to first order, so from `ε = 2^(−6)` to
/// `2^(−4)` the readings grow four times and the curl, third order, grows more slowly than they do.
#[test]
fn a_square_agrees_at_one_base() {
    let classes = [1usize, 4, 0, 2, 2, 3, 1];
    let open = [false; 7];
    let r = Region { classes: &classes, unresolved: &open, faces: &[], locked: &[], echo: &[], domain: None, port: None };
    for still in 0..=2 {
        let field = energetic(still);
        let mut sums = [(0i128, 0i128); 2];
        for (k, eps) in [1u32 << 10, 1 << 12].into_iter().enumerate() {
            for i in 0..classes.len() {
                for j in (i + 1)..classes.len().min(i + 4) {
                    let (li, lj) = field.energy_square(&r, (i, classes[i], (classes[i] + 1) % 5), (j, classes[j], (classes[j] + 2) % 5), eps).unwrap();
                    sums[k].0 += (li - lj).abs();
                    sums[k].1 += li.abs() + lj.abs();
                }
            }
        }
        println!("still {still}: curl/readings {}/{} at 2^-6, {}/{} at 2^-4", sums[0].0, sums[0].1, sums[1].0, sums[1].1);
        // The readings grow about four times, and the curl's share of them falls as ε falls.
        assert!(3 * sums[0].1 <= sums[1].1 && sums[1].1 <= 5 * sums[0].1, "still {still}: readings {sums:?}");
        assert!(sums[0].0 * sums[1].1 <= sums[1].0 * sums[0].1, "still {still}: the curl's share does not fall with ε, {sums:?}");
    }
}

/// [definition; the unified-theory reading of November 7, 01:37] **The letters read the energy at one temperature**: at
/// `log₂ T = τ` every face's logits are the `T = 1` logits times `2^(−τ)` (to the face's grain), and the founding's
/// temperature opens the faces at one bit of spread.
#[test]
fn the_letters_read_the_energy_at_one_temperature() {
    for still in 0..=2 {
        let mut field = energetic(still);
        let at = field.layout.face_temper;
        field.theta[at] = 0;
        let flat = field.logits(&region()).unwrap();
        let (ell, spread) = field.energy_temperature(&[region()]).unwrap();
        assert!(spread > 1 << 16, "still {still}: a drawn field's faces spread past a bit ({spread})");
        field.theta[at] = ell;
        let tempered = field.logits(&region()).unwrap();
        let inverse = temperature_of(-ell, &field.fine).unwrap();
        for (a, b) in flat.iter().zip(&tempered) {
            if let (Some(a), Some(b)) = (a, b) {
                for (&x, &y) in a.iter().zip(b) {
                    assert_eq!(y as i128, release(x as i128 * inverse, MATERIAL_BITS), "still {still}");
                }
            }
        }
        // The faces at T0: the root mean square of their spread across the letters, one bit to the face's grain.
        let a_ = field.declaration.alphabet as i128;
        let (mut second, mut sites) = (0i128, 0i128);
        for z in tempered.iter().flatten() {
            let mean = div_nearest(z.iter().map(|&v| v as i128).sum(), a_);
            second += div_nearest(z.iter().map(|&v| (v as i128 - mean).pow(2)).sum(), a_);
            sites += 1;
        }
        let opened = (div_nearest(second, sites) as u128).isqrt() as i128;
        assert!((opened - (1 << 16)).abs() <= 1 << 10, "still {still}: the faces at T0 spread {opened} (2^(−16) bits)");
    }
}

/// An energy field shaped as the line's (four heads on four ring sets, two still, four ticks) on a small width, every family
/// drawn as [`shaped`]'s, its clocks plain, the families the energy does not read at zero and its letters at `T = 1`.
fn energetic_line() -> Field {
    let d = FieldDeclaration { alphabet: 5, width: 8, heads: 4, modes: 3, still: 2, contacts: 4, ticks: 4, frames: 4, reach: 64, lanes: 1, depth: 0, energy: true };
    let mut field = shaped_with(d);
    let (l, d) = (field.layout.clone(), field.declaration);
    let (dw, m2) = (d.width, 2 * d.complex());
    field.theta[l.pace..l.pace + d.paced_heads() * (d.alphabet + 1)].fill(0);
    field.theta[l.face_temper] = 0;
    for (start, len) in [(l.v, m2 * dw), (l.v_bias, m2), (l.out, dw * m2), (l.out_bias, dw), (l.w, dw * d.contacts), (l.w_bias, dw)] {
        field.theta[start..start + len].fill(0);
    }
    field
}

/// [definition; the unified-theory reading of November 7, 00:02] **The total derivative holds on a line-shaped field**: on 40
/// sites (crowds past the near field, far supports by class, four heads, four ticks), a central difference of `G` across an
/// open site's mixture reads `−2ε(z_b − z_a)`.
#[test]
fn the_total_derivative_holds_on_a_line_shaped_field() {
    let field = energetic_line();
    let classes: Vec<usize> = (0..40).map(|t| (t * 7 + t / 3) % 5).collect();
    let open: Vec<bool> = (0..40).map(|t| t % 9 == 4).collect();
    let r = Region { classes: &classes, unresolved: &open, faces: &[], locked: &[], echo: &[], domain: None, port: None };
    let logits = field.logits(&r).unwrap();
    let alphabet = 5u32;
    let base = (1u32 << 16) / alphabet;
    let eps = 1i128 << 9;
    for t in (0..40).filter(|&t| open[t]) {
        let z = logits[t].as_ref().unwrap();
        for (a, b) in [(0u32, 1u32), (2, 4)] {
            let moved = |sign: i128| -> Shares { (0..alphabet).map(|c| (c, (base as i128 + if c == b { sign * eps } else if c == a { -sign * eps } else { 0 }) as u32)).collect() };
            let dg = field.energy_g_at(&r, t, &moved(1)).unwrap() - field.energy_g_at(&r, t, &moved(-1)).unwrap();
            let predicted = -2 * eps * (z[b as usize] - z[a as usize]) as i128;
            assert!(10 * (dg - predicted).abs() <= predicted.abs() + (10 << 23), "site {t} letters {a}, {b}: ΔG {dg} against −2ε Δz {predicted} (2^(−32) bits)");
        }
    }
}

/// [definition; the unified-theory reading of November 7, 02:00] **Squares agree at one base on a line-shaped field**: at `ε`
/// of a sixty-fourth of a letter's weight the curl is under a twentieth of the readings, and from `ε` to `4ε` the readings grow
/// about four times while the curl's share grows (measured: 0.013 at `ε`, 0.034 at `4ε`, readings 3.86 times).
#[test]
fn squares_agree_at_one_base_on_a_line_shaped_field() {
    let field = energetic_line();
    let truth: Vec<usize> = (0..40).map(|t| (t * 7 + t / 3) % 5).collect();
    let base = (1u32 << 16) / 5;
    {
        let eps = base >> 6;
        let (mut curl, mut size, mut wcurl, mut wsize) = (0i128, 0i128, 0i128, 0i128);
        for i in (2..33).step_by(5) {
            for d in [1usize, 2, 5] {
                let Some(sq) = field.energy_square_corners(&truth, (i, i + d), 4, eps).unwrap() else { continue };
                curl += (sq.small_i - sq.small_j).abs();
                size += sq.small_i.abs() + sq.small_j.abs();
                wcurl += (sq.wide_i - sq.wide_j).abs();
                wsize += sq.wide_i.abs() + sq.wide_j.abs();
            }
        }
        assert!(20 * curl <= size, "curl/readings {curl}/{size} at ε");
        assert!(3 * size <= wsize && wsize <= 5 * size, "readings {size} at ε, {wsize} at 4ε");
        assert!(curl * wsize <= wcurl * size, "the curl's share does not grow with ε: {curl}/{size}, {wcurl}/{wsize}");
    }
}

/// [definition; agent-inferred, November 7] **The energy's material covector is `G`'s slope in its material**: at each family's
/// largest entry, a central difference of `G` (replayed at the base's halvings under its supports) across `±δ` of the entry
/// reads `2δ ∂G/∂θ`, on the tiny and the line-shaped fields.
#[test]
fn the_energy_material_is_g_slope() {
    let line_classes: Vec<usize> = (0..40).map(|t| (t * 7 + t / 3) % 5).collect();
    let line_open: Vec<bool> = (0..40).map(|t| t % 9 == 4).collect();
    for (name, field, classes, open) in [("tiny", energetic(1), CLASSES.to_vec(), OPEN.to_vec()), ("line", energetic_line(), line_classes, line_open)] {
        let r = Region { classes: &classes, unresolved: &open, faces: &[], locked: &[], echo: &[], domain: None, port: None };
        let (g, _) = field.energy_material(&r).unwrap();
        let l = field.layout.clone();
        let families = [("q", l.q), ("q_bias", l.q_bias), ("probe", l.probe), ("probe_bias", l.probe_bias), ("a", l.a), ("a_bias", l.a_bias), ("b", l.b), ("b_bias", l.b_bias), ("pair_c", l.pair_c), ("read", l.read), ("lift_bias", l.lift_bias), ("enc", l.enc), ("before", l.before), ("after", l.after), ("read_bias", l.read_bias), ("moment_face", l.moment_face), ("moment_face_bias", l.moment_face_bias), ("moment_before", l.moment_before), ("moment_after", l.moment_after)];
        let mut report = Vec::new();
        for (fam, start) in families {
            let &(_, len, grain) = l.families.iter().find(|(s, _, _)| *s == start).unwrap();
            let Some(k) = (start..start + len).max_by_key(|&k| g[k].abs()) else { continue };
            if g[k] == 0 {
                report.push(format!("{fam}: zero"));
                continue;
            }
            let delta = 1i32 << grain.saturating_sub(10);
            let moved = |sign: i32| -> i128 {
                let mut f2 = field.clone();
                f2.theta[k] += sign * delta;
                f2.energy_g_replayed(&field, &r).unwrap()
            };
            let dg = moved(1) - moved(-1);
            let predicted = div_nearest(g[k] * delta as i128, 1i128 << (grain + 7));
            report.push(format!("{fam}: ΔG {dg} against {predicted}"));
            assert!(10 * (dg - predicted).abs() <= predicted.abs() + (10 << 16), "{name} {fam} entry {k}: ΔG {dg} against 2δ ∂G/∂θ {predicted}");
        }
        println!("{name}: {}", report.join("; "));
    }
}

/// [definition; the unified-theory reading of November 7, 04:05, route (b)] **A contrast step lowers the truth's energy
/// against its release**: on the tiny and the line-shaped fields, every site resolved, the truth beside a release that wrote
/// its open places otherwise, one section's step (the moments opening at its covector, so each entry moves by about its
/// rate) leaves `G(truth) − G(e′)` lower, by about the step's first-order change read on that gap.
#[test]
fn a_contrast_step_lowers_the_truths_energy_against_its_release() {
    let line_classes: Vec<usize> = (0..40).map(|t| (t * 7 + t / 3) % 5).collect();
    let line_open: Vec<bool> = (0..40).map(|t| t % 9 == 4).collect();
    for (name, field, classes, open) in [("tiny", energetic(1), CLASSES.to_vec(), OPEN.to_vec()), ("line", energetic_line(), line_classes, line_open)] {
        let alphabet = field.declaration.alphabet;
        let released: Vec<usize> = classes.iter().zip(&open).map(|(&c, &o)| if o { (c + 1) % alphabet } else { c }).collect();
        let none = vec![false; classes.len()];
        let truth = [Region { classes: &classes, unresolved: &none, faces: &[], locked: &[], echo: &[], domain: None, port: None }];
        let release = [Region { classes: &released, ..truth[0] }];
        let gap = |f: &Field| -> i128 { f.energy_material(&truth[0]).unwrap().1 - f.energy_material(&release[0]).unwrap().1 };
        let before = gap(&field);
        let mut learner = FieldLearner::new(field, 14);
        let receipt = learner.section_contrast(&truth, &release, &mut HostField).unwrap();
        assert_eq!(receipt.gap, before, "{name}: the receipt's gap at T = 1 is G(truth) − G(e′)");
        assert!(receipt.deposited && receipt.states == 1 && receipt.same == 0, "{name}: {receipt:?}");
        let after = gap(&learner.field);
        // The first-order change on the codes' 2^(−20) bits, against the gap's move on 2^(−32).
        let predicted = receipt.predicted.unwrap() as i128;
        let moved = release_i(after - before, 12);
        println!("{name}: gap {before} → {after} (2^(−32) bits), moved {moved} against its first order {predicted} (2^(−20))");
        assert!(after < before, "{name}: the step left the gap at {after} from {before}");
        assert!(4 * (moved - predicted).abs() <= predicted.abs(), "{name}: moved {moved} against {predicted}");
    }
}

fn release_i(v: i128, bits: u32) -> i128 {
    div_nearest(v, 1i128 << bits)
}

/// [definition; agent-inferred, November 7, Brandon's lens of 04:42] **An energy field releases an answer as one field**: on
/// the line-shaped field, two answers of given lengths beside their questions are relaxed jointly (every open place's mixture
/// moved toward its face each read) until no share moves by more than a grain or the reads run out; each comes back at its
/// length, on the letters (never the void), the same for the same key, and the mixtures' largest move falls from the first
/// read to the last.
#[test]
fn an_energy_field_releases_an_answer_as_one_field() {
    let field = energetic_line();
    let void = field.declaration.alphabet - 1;
    let q1: Vec<usize> = (0..12).map(|t| (t * 3 + 1) % 4).collect();
    let q2: Vec<usize> = (0..9).map(|t| (t * 2 + t / 3) % 4).collect();
    let problems: Vec<(&[usize], usize)> = vec![(&q1, 20), (&q2, 14)];
    let lengths = [9usize, 6];
    let mut moves = Vec::new();
    let answers = field.energy_release(&problems, &lengths, void, 64, 7, &mut HostField, &mut |_, _, m| moves.push(m)).unwrap();
    let again = field.energy_release(&problems, &lengths, void, 64, 7, &mut HostField, &mut |_, _, _| {}).unwrap();
    println!("moves {moves:?}; answers {answers:?}");
    assert_eq!(answers, again, "one key, one release");
    for (a, &n) in answers.iter().zip(&lengths) {
        assert_eq!(a.len(), n);
        assert!(a.iter().all(|&c| c != void), "a joint release on the letters: {a:?}");
    }
    assert!(moves.len() >= 2 && moves.len() < 63 && moves.last() < moves.first(), "the mixtures settle: {moves:?}");
}

/// [definition; the unified-theory reading of November 7, 05:20] **A kernel step's weight is its Metropolis–Hastings ratio**:
/// on the line-shaped field, a block of places eleven apart opened at the truth, each drawn from its face, weighed by
/// `min(1, A)` with `A = 2^((G − G′)/T) Π face′(truth)/face(a)`; the receipt's weights lie in `[0, 1]` and a proposal that
/// moves no place is weighed whole. At `T = 1` the shaped field's faces are sharp and a moved proposal is weighed near zero;
/// at `T = 2^10` the faces are near uniform, `G′ − G` is small against `T`, and a moved proposal is weighed near whole.
#[test]
fn a_kernel_steps_weight_is_its_metropolis_hastings_ratio() {
    let mut field = energetic_line();
    field.theta[field.layout.face_temper] = 10 << MATERIAL_BITS;
    let classes: Vec<usize> = (0..40).map(|t| (t * 7 + t / 3) % 5).collect();
    let none = vec![false; classes.len()];
    let truth = [Region { classes: &classes, unresolved: &none, faces: &[], locked: &[], echo: &[], domain: None, port: None }];
    let mut seen = Vec::new();
    for seed in 0..6u64 {
        let mut learner = FieldLearner::new(field.clone(), 14);
        let blocks = vec![vec![3usize, 14, 25, 36]];
        let r = learner.section_kernel(&truth, &blocks, seed, &mut HostField).unwrap();
        let unit = 1i128 << MATERIAL_BITS;
        assert!(r.states == 1 && r.places == 4 && (0..=unit).contains(&r.least) && r.most <= unit && r.weight == r.least, "{r:?}");
        if r.moved == 0 {
            assert_eq!(r.weight, unit, "a proposal that moves no place is weighed whole");
        }
        seen.push((r.moved, r.weight * 1000 / unit, r.deposited));
    }
    println!("kernel (moved, weight in thousandths, deposited): {seen:?}");
    assert!(seen.iter().any(|&(m, w, _)| m > 0 && w > 500), "a moved proposal weighed near whole at a warm temperature: {seen:?}");
}

/// [definition; the unified-theory reading of November 7, 05:55] **An evidence-shrunk Newton step moves along the moments'
/// direction by `α = −(s/c)(1 − v/s²)`**: on the warm line-shaped field, a first kernel section opens the moments (no step:
/// they hold no direction yet), and a second, on other blocks, steps by `α` times the moments' step where its slope along
/// it is downhill past its noise, or deposits nothing; its read states `α`, the shrink and the slope's terms.
#[test]
fn an_evidence_shrunk_newton_step_moves_by_its_alpha() {
    let mut field = energetic_line();
    field.theta[field.layout.face_temper] = 10 << MATERIAL_BITS;
    let truths: Vec<Vec<usize>> = (0..6).map(|k| (0..40).map(|t| (t * 7 + t / 3 + k) % 5).collect()).collect();
    let none = vec![false; 40];
    let regions: Vec<Region> = truths.iter().map(|c| Region { classes: c, unresolved: &none, faces: &[], locked: &[], echo: &[], domain: None, port: None }).collect();
    let mut learner = FieldLearner::new(field, 14);
    learner.newton = true;
    let first = learner.section_kernel(&regions, &vec![vec![3usize, 14, 25, 36]; 6], 1, &mut HostField).unwrap();
    let r = first.newton.unwrap();
    assert!(!r.deposited && r.alpha == (0, 0), "the moments hold no direction before their first covector: {r:?}");
    let before = learner.field.theta.clone();
    let second = learner.section_kernel(&regions, &vec![vec![8usize, 19, 30]; 6], 2, &mut HostField).unwrap();
    let r = second.newton.unwrap();
    println!("second section: {r:?}");
    assert!(r.curvature > 0, "{r:?}");
    if r.slope < 0 && r.shrink.0 > 0 {
        assert!(r.deposited && r.alpha.0 > 0 && r.alpha.1 > 0 && learner.field.theta != before, "a downhill slope past its noise steps: {r:?}");
    } else {
        assert!(!r.deposited && learner.field.theta == before, "an uphill or noisy slope deposits nothing: {r:?}");
    }
}

/// [definition; the unified-theory reading of November 7, 07:40] **Several blocks a problem, the truth formed once**: on the
/// warm line-shaped field, one problem's two blocks read grouped give a receipt with two blocks and their weights in
/// `[0, 1]`, and with one block a problem the grouped read is the plain one's, bit for bit.
#[test]
fn a_problems_blocks_share_one_truth() {
    let mut field = energetic_line();
    field.theta[field.layout.face_temper] = 10 << MATERIAL_BITS;
    let classes: Vec<usize> = (0..40).map(|t| (t * 7 + t / 3) % 5).collect();
    let none = vec![false; 40];
    let truth = [Region { classes: &classes, unresolved: &none, faces: &[], locked: &[], echo: &[], domain: None, port: None }];
    let mut grouped = FieldLearner::new(field.clone(), 14);
    let r = grouped.section_kernel_grouped(&truth, &[0, 0], &[vec![3usize, 14], vec![25, 36]], 5, &mut HostField).unwrap();
    let unit = 1i128 << MATERIAL_BITS;
    assert!(r.states == 2 && r.places == 4 && r.per_state.iter().all(|&(k, w)| k == 2 && (0..=unit).contains(&w)), "{r:?}");
    let (mut a, mut b) = (FieldLearner::new(field.clone(), 14), FieldLearner::new(field, 14));
    let one = a.section_kernel(&truth, &[vec![3usize, 14, 25]], 9, &mut HostField).unwrap();
    let two = b.section_kernel_grouped(&truth, &[0], &[vec![3usize, 14, 25]], 9, &mut HostField).unwrap();
    assert_eq!(one, two);
    assert_eq!(a.field.theta, b.field.theta);
}

/// [definition; the unified-theory reading of November 7, 20:29, law (D)] **A place's deposit against its whole
/// conditional**: on the warm line-shaped field, each place's truth share `p(t)` is the enumerated conditional's,
/// `2^(−G(x_t)/T) / Σ_v 2^(−G(x_v)/T)` from each letter's energy, within the weights' grain; the section deposits.
#[test]
fn a_places_conditional_is_the_enumerated_one() {
    let mut field = energetic_line();
    field.theta[field.layout.face_temper] = 10 << MATERIAL_BITS;
    let classes: Vec<usize> = (0..40).map(|t| (t * 7 + t / 3) % 5).collect();
    let none = vec![false; 40];
    let truth = [Region { classes: &classes, unresolved: &none, faces: &[], locked: &[], echo: &[], domain: None, port: None }];
    let mut learner = FieldLearner::new(field.clone(), 14);
    let before = learner.field.theta.clone();
    let r = learner.section_conditional(&truth, &[0, 0], &[vec![3usize], vec![25]], &mut HostField).unwrap();
    assert!(r.states == 2 && r.moved == 0 && r.deposited && learner.field.theta != before, "{r:?}");
    let inverse = temperature_of(-field.theta[field.layout.face_temper], &field.fine).unwrap();
    for (&(_, pt), &t) in r.per_state.iter().zip(&[3usize, 25]) {
        let g: Vec<i128> = (0..field.declaration.alphabet)
            .map(|v| {
                let mut c = classes.clone();
                c[t] = v;
                field.energy_g(&c).unwrap()
            })
            .collect();
        let lo = *g.iter().min().unwrap();
        let w: Vec<i128> = g
            .iter()
            .map(|&x| {
                let ell = release((lo - x) * inverse, MATERIAL_BITS) >> (ENERGY_BITS - MATERIAL_BITS);
                if ell >= 0 { 1 << MATERIAL_BITS } else if ell <= -((MATERIAL_BITS as i128 - 1) << MATERIAL_BITS) { 0 } else { temperature_of(ell as i32, &field.fine).unwrap() }
            })
            .collect();
        let want = div_nearest(w[classes[t]] << MATERIAL_BITS, w.iter().sum());
        assert_eq!(pt, want, "place {t}: the conditional's truth share from the material reads against the energies'");
    }
}

/// [definition; the unified-theory reading of November 7, 21:08] **Every place on its beat, band zero**: with the bands held
/// to zero every place is spent at weight one, so the beat section is the full conditional section bit for bit, and its counts
/// of counts read every place in band zero.
#[test]
fn a_beat_held_to_band_zero_is_the_full_conditional() {
    let mut field = energetic_line();
    field.theta[field.layout.face_temper] = 10 << MATERIAL_BITS;
    let classes: Vec<usize> = (0..40).map(|t| (t * 7 + t / 3) % 5).collect();
    let none = vec![false; 40];
    let truth = [Region { classes: &classes, unresolved: &none, faces: &[], locked: &[], echo: &[], domain: None, port: None }];
    let (mut a, mut b) = (FieldLearner::new(field.clone(), 14), FieldLearner::new(field, 14));
    let blocks = [vec![3usize], vec![14], vec![25]];
    let full = a.section_conditional(&truth, &[0, 0, 0], &blocks, &mut HostField).unwrap();
    let mut beat = b.section_conditional_beat(&truth, &[0, 0, 0], &blocks, &[7], 5, 0, &mut HostField).unwrap();
    assert_eq!(beat.bands, vec![(3, 3)]);
    beat.bands = Vec::new();
    assert_eq!(full, beat);
    assert_eq!(a.field.theta, b.field.theta);
}
