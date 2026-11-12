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
    FieldDeclaration { alphabet: 5, width: 8, heads: 2, modes: 3, still, contacts: 4, ticks: 2, frames: 2, reach: 16, lanes: 1, depth: 0, carry: 0 }
}

/// A tiny field with every family drawn from the keys (the founding holds the returns and the
/// readout at zero, where no covector reaches the charts).
fn shaped(still: usize) -> Field {
    shaped_with(tiny_declaration(still))
}

/// [`shaped`] on a declaration of the caller's.
fn shaped_with(d: FieldDeclaration) -> Field {
    drawn(Field::found(d, &keys(1 << 14)).unwrap())
}

/// Every family of `field` drawn from the keys, a uniform draw on `[−½, ½)` of its family's grain.
fn drawn(mut field: Field) -> Field {
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
    let port = Port { start: 4, void: 0, target: &[2, 3], boundary: false, stop: None, heard: None, window: false, letters: false };
    let bounded = Port { boundary: true, ..port };
    // [the unified-theory reading of November 6, 11:49] And a port on its letters off the void, with its middle place resolved
    // (the writer's own state given its end).
    let lettered = Port { letters: true, target: &[2, 3, 1], ..port };
    // [the depth rings, November 6] And with a depth ring among the turned sets (its rate the located increment alone, no
    // skin, no moment).
    // [the unified-theory reading of November 6, 10:31] And under the bare stretch (`Field::bare_stretch`: past the last arrival
    // a silent place runs at the bare rate and returns nothing), declared beside the one-rate stretch.
    for (still, depth, bare, r) in [(0usize, 0usize, false), (1, 0, false), (2, 0, false), (0, 1, false), (1, 1, false), (0, 0, true), (1, 0, true)].into_iter().flat_map(|(still, depth, bare)| [(still, region()), (still, Region { classes: &CLASSES, unresolved: &OPEN, faces: &carried, locked: &[], echo: &[], domain: None, port: None }), (still, Region { classes: &CLASSES, unresolved: &PORTED, faces: &[], locked: &[], echo: &[], domain: None, port: Some(port) }), (still, Region { classes: &CLASSES, unresolved: &PORTED, faces: &[], locked: &[], echo: &[], domain: None, port: Some(bounded) }), (still, Region { classes: &CLASSES, unresolved: &PATH, faces: &[], locked: &[], echo: &[], domain: None, port: Some(bounded) }), (still, Region { classes: &CLASSES, unresolved: &PATH, faces: &[], locked: &[], echo: &[], domain: None, port: Some(lettered) })].map(|(still, r)| (still, depth, bare, r))) {
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
    let at = |modes: usize, reach: usize| FieldDeclaration { alphabet: 5, width: 8, heads: 2, modes, still: 1, contacts: 4, ticks: 2, frames: 2, reach, lanes: 1, depth: 0, carry: 0 }.score_shift();
    assert_eq!(at(8, 2221), -2, "reading 8's declaration locks an equal word at 32 bits");
    assert_eq!(at(16, 16), 1);
    assert_eq!(at(3, 16), -2);
    for (modes, reach) in [(8usize, 2221usize), (16, 16), (3, 16), (8, 2), (16, 1 << 20), (1, 1 << 20)] {
        let (beta, need) = (at(modes, reach), 2 * (u128::BITS - ((reach - 1) as u128).leading_zeros()).max(1) as u128);
        let gained = |b: i32| if b >= 0 { (modes as u128) >> b } else { (modes as u128) << -b };
        assert!(gained(beta) >= need && gained(beta + 1) < need, "the largest such shift: modes {modes} reach {reach}");
    }
    let d = FieldDeclaration { alphabet: 5, width: 8, heads: 2, modes: 8, still: 1, contacts: 4, ticks: 2, frames: 2, reach: 2221, lanes: 1, depth: 0, carry: 0 };
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
    let d = FieldDeclaration { alphabet: 5, width: 8, heads: 2, modes: 3, still: 1, contacts: 4, ticks: 2, frames: 2, reach: 32, lanes: 1, depth: 0, carry: 0 };
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
    let d = FieldDeclaration { alphabet: 44, width: 32, heads: 5, modes: 8, still: 2, contacts: 32, ticks: 2, frames: 5, reach: 484, lanes: 1, depth: 0, carry: 0 };
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
    let r = Region { classes: &CLASSES, unresolved: &PORTED, faces: &[], locked: &[], echo: &[], domain: None, port: Some(Port { start: 4, void: 0, target: &target, boundary: false, stop: None, heard: None, window: false, letters: false }) };
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
    let port = Port { start: 4, void: 0, target: &target, boundary: true, stop: None, heard: None, window: false, letters: false };
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
                port: Some(Port { start: q.len(), void: 0, target: &target, boundary: true, stop: None, heard: Some(&heard), window, letters: false }),
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
        assert_eq!(field.sample_runs(&problems, 9, 2, 0, seed, 0, true, false, None, false, &mut HostField, &mut |_, _| true, &mut |_| {}).unwrap(), one, "no bound, one place a read");
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
                .sample_runs(&problems, 4, 0, 0, seed, run_bound, true, false, None, false, &mut HostField, &mut |_, _| true, &mut |r| {
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
            let written = field.sample_runs(&problems, 4, 2, 0, seed, run_bound, true, false, Some(&[3, 5]), false, &mut HostField, &mut |_, _| true, &mut |_| {}).unwrap();
            for (places, l) in written.iter().zip([3usize, 5]) {
                assert!(places[..l].iter().all(|&c| c != 0), "a void inside the given length, seed {seed}: {places:?}");
                assert!(places[l..].iter().all(|&c| c == 0), "a letter past the given length, seed {seed}: {places:?}");
            }
            // One end, one draw: the length drawn from the first read is kept the same way.
            let drawn = field.sample_runs(&problems, 4, 2, 0, seed, run_bound, true, false, None, true, &mut HostField, &mut |_, _| true, &mut |_| {}).unwrap();
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
    FieldDeclaration { alphabet: 2, width: 8, heads: 2, modes: 3, still: 1, contacts: 4, ticks: 2, frames: 2, reach: 6, lanes: 1, depth: 0, carry: 0 }
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

/// A tiny learner grown by a lane and by four contacts (width 16 in two lanes, eight contacts, four of them new), a section into
/// its life so every moment is open.
fn grown_learner() -> FieldLearner {
    let mut learner = FieldLearner::new(Field::found(tiny_declaration(1), &keys(1 << 14)).unwrap(), 6);
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
    let back = FieldLearner::from_text(&fast.to_text()).unwrap();
    assert_eq!(back.rate_parts, fast.rate_parts);
    assert_eq!(back.field.theta, fast.field.theta);
    let stripped: String = fast.to_text().lines().filter(|l| !l.starts_with("parts ")).map(|l| format!("{l}\n")).collect();
    assert_eq!(FieldLearner::from_text(&stripped).unwrap().rate_parts, None, "a state without the line has no parts' rates");
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
fn grown_learner_text_of(learner: &FieldLearner) -> String {
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
    assert_eq!(FieldLearner::from_text(&text).unwrap().own_rates, free.own_rates);
    let stripped: String = text.lines().filter(|l| !l.starts_with("rates ")).map(|l| format!("{l}\n")).collect();
    assert_eq!(FieldLearner::from_text(&stripped).unwrap().own_rates, None, "a state without the line has no own rates");
    let short: String = text.lines().map(|l| if l.starts_with("rates ") { format!("{}\n", l.rsplit_once(' ').unwrap().0) } else { format!("{l}\n") }).collect();
    assert!(FieldLearner::from_text(&short).is_err(), "a line that is not one count an entry is refused");
    for bad in ["0", "128"] {
        let wrong: String = text.lines().map(|l| if l.starts_with("rates ") { format!("{} {bad}\n", l.rsplit_once(' ').unwrap().0) } else { format!("{l}\n") }).collect();
        assert!(FieldLearner::from_text(&wrong).is_err(), "a rate of {bad} is refused");
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
    let load = |k: &str| FieldLearner::from_text(&std::fs::read_to_string(var(k)).unwrap()).unwrap();
    let (older, old, now) = (load("HOLONICS_PARTS_OLDER"), load("HOLONICS_PARTS_OLD"), load("HOLONICS_PARTS_NOW"));
    let parts = now.field.founded_parts(var("HOLONICS_PARTS_BEFORE").parse().unwrap());
    let travel = part_travel(&parts, &older.field.theta, &old.field.theta, &now.field.theta);
    for (name, t) in PART_NAMES.iter().zip(&travel) {
        println!("PART {name} {} {} {:?}", t.entries, t.cosine_micro(), t.against_half());
    }
}

/// A tiny declaration with four complex contacts and no carry circle.
fn four_contacts(still: usize) -> FieldDeclaration {
    FieldDeclaration { contacts: 8, ..tiny_declaration(still) }
}

/// [`four_contacts`]'s founded field grown by two carry circles (complex contacts 4 and 5 of six: one scans from the left, one from the
/// right), then every family drawn ([`drawn`]): the circles' charts, their biases and their `W` columns off zero, so the gate has friction
/// on some sites and none on others.
fn circled_shaped(still: usize) -> Field {
    let plain = Field::found(four_contacts(still), &keys(1 << 14)).unwrap();
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
    assert!(FieldDeclaration { carry: 2, ..d }.admit().is_ok() && FieldDeclaration { carry: 4, ..d }.admit().is_ok());
    assert!(FieldDeclaration { carry: 1, ..d }.admit().is_err(), "an odd count of circles");
    assert!(FieldDeclaration { carry: 6, ..d }.admit().is_err(), "more circles than complex contacts");
    let plain = d.to_text();
    assert!(plain.starts_with("hnn-field-v14 ") && plain.split(' ').count() == 12);
    assert_eq!(FieldDeclaration::from_text(&plain).unwrap(), d);
    let circled = FieldDeclaration { carry: 2, ..d }.to_text();
    assert!(circled.starts_with("hnn-field-v14e ") && circled.split(' ').count() == 13 && circled.ends_with(" 2"));
    assert_eq!(FieldDeclaration::from_text(&circled).unwrap(), FieldDeclaration { carry: 2, ..d });
    let retired = format!("{} 1", plain.replacen("hnn-field-v14 ", "hnn-field-v14k ", 1));
    assert!(matches!(FieldDeclaration::from_text(&retired), Err(TowerError::Refused(m)) if m.contains("zero friction is retired")));
    let linear = circled.replacen("hnn-field-v14e ", "hnn-field-v14t ", 1);
    assert!(matches!(FieldDeclaration::from_text(&linear), Err(TowerError::Refused(m)) if m.contains("linear chart is retired")));
    assert!(FieldDeclaration::from_text(&format!("{} 0", plain.replacen("hnn-field-v14 ", "hnn-field-v14e ", 1))).is_err());
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

/// [definition; theory, November 11 17:25] **A growth by carry circles keeps every face and returns through its circles**: on a field with every
/// family drawn, [`Field::with_carry`] adds the circles as the last contacts (their `W` columns, leak rows and biases at zero, their turn rows
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
    let mut learner = FieldLearner::new(shaped_with(four_contacts(1)), 6);
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
    assert_eq!(text.lines().find(|l| l.starts_with("parts ")).unwrap().split(' ').count(), 2 + PARTS, "a field with carry circles writes all nineteen parts");
    let back = FieldLearner::from_text(&text).unwrap();
    assert_eq!((back.field.theta.clone(), back.first.clone(), back.second.clone(), back.rate_parts, back.drawn), (grown.field.theta.clone(), grown.first.clone(), grown.second.clone(), grown.rate_parts, grown.drawn));
    assert_eq!(back.field.declaration, grown.field.declaration);
    assert_eq!(learner.to_text().lines().find(|l| l.starts_with("parts ")).unwrap().split(' ').count(), 2 + written_parts(0).len(), "a field without carry circles writes nineteen: the plain sixteen and the first lane's letter rows");
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
    let pass = |c: &[usize]| base.pass(&Region { classes: c, unresolved: &unresolved, faces: &[], locked: &[], echo: &[], domain: None, port: None }, true).unwrap();
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
    let sheets = |field: &Field, r: &Region| -> Vec<Vec<u32>> {
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
/// ([`Field::redraw_lensed`]): with a lens that weighs the void four times at the stop place, each answer's code at the start is
/// its lensed locked faces' code, the stop place at the void among them, and every pass that keeps changes lowers the pooled
/// code by more than `h` for each one; every answer keeps its length and stops neutral or at rest.
#[test]
fn the_lensed_redraw_codes_its_stop_place_and_certifies_every_pass() {
    let field = shaped_with(FieldDeclaration { reach: 40, ..tiny_declaration(1) });
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
    let mut locked = field.locked_faces(&problems, &answers0, &[0, 1], 0, true, &mut HostField).unwrap();
    for (x, f) in answers0.iter().zip(locked.iter_mut()) {
        assert_eq!(f.len(), x.len() + 1, "the stop place is read");
        lens(x, f);
    }
    for h in [0i128, 1 << 18] {
        let mut passes: Vec<(usize, usize, i128)> = Vec::new();
        let (answers, records) = field.redraw_lensed(&problems, &written, 0, h, &lens, &mut HostField, &mut |p| {
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

/// [definition; theory, November 10 04:15] **Point re-draws alternate with exchanges, certify every pass and stop** ([`Field::redraw`]):
/// on the settle's two answers, at `h` zero and at a quarter of a bit, each answer keeps its length and its void, the passes
/// alternate re-draw (odd) and exchange (even), every pass that keeps changes lowers the pooled code by more than `h` for each
/// one, a pass that keeps none leaves it as it was, and every answer stops neutral (its code at or under its entropy) or at
/// rest; its end is its final answer's code read again.
#[test]
fn point_redraws_alternate_with_exchanges_certify_every_pass_and_stop() {
    let field = shaped_with(FieldDeclaration { reach: 40, ..tiny_declaration(1) });
    let (q1, q2) = ([1usize, 4, 0, 2, 2, 3], [3usize, 3, 1, 0]);
    let problems: Vec<(&[usize], usize)> = vec![(&q1, 24), (&q2, 22)];
    let letters = |seed: usize, n: usize, room: usize| -> Vec<usize> { (0..room).map(|t| if t < n { 1 + (t * 7 + t / 3 + seed) % 4 } else { 0 }).collect() };
    let written = vec![letters(0, 20, 24), letters(3, 20, 22)];
    for h in [0i128, 1 << 18] {
        let mut passes: Vec<(usize, usize, usize, i128)> = Vec::new();
        let (answers, records) = field.redraw(&problems, &written, 0, h, &mut HostField, &mut |p| {
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
        let (_, check) = field.redraw(&problems, &answers, 0, i128::MAX, &mut HostField, &mut |_| false).unwrap();
        for (k, r) in records.iter().enumerate() {
            assert_eq!(check[k].start, r.end, "the end is the final answer's code read again");
        }
    }
}

/// [definition; theory, November 10 01:36] **The parallel certified settle holds composition, certifies every pass and rests**
/// ([`Field::settle`]): on two answers of twenty letters, at `h` zero and at a quarter of a bit, each answer keeps its letters
/// and its void, every pass that keeps exchanges lowers the pooled code by more than `h` for each one (each problem's kept set
/// is certified whole), a pass that keeps none leaves it as it was, every problem rests, and its end is its final
/// answer's code read again; some exchange is kept.
#[test]
fn the_parallel_settle_certifies_every_pass_and_rests() {
    let field = shaped_with(FieldDeclaration { reach: 40, ..tiny_declaration(1) });
    let (q1, q2) = ([1usize, 4, 0, 2, 2, 3], [3usize, 3, 1, 0]);
    let problems: Vec<(&[usize], usize)> = vec![(&q1, 24), (&q2, 22)];
    let letters = |seed: usize, n: usize, room: usize| -> Vec<usize> { (0..room).map(|t| if t < n { 1 + (t * 7 + t / 3 + seed) % 4 } else { 0 }).collect() };
    let written = vec![letters(0, 20, 24), letters(3, 20, 22)];
    let mut kept_any = false;
    for h in [0i128, 1 << 18] {
        let mut passes: Vec<(usize, usize, i128)> = Vec::new();
        let (answers, records) = field.settle(&problems, &written, 0, h, &mut HostField, &mut |p| {
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
        let (again, check) = field.settle(&problems, &answers, 0, i128::MAX, &mut HostField, &mut |_| true).unwrap();
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
/// founding on the leak's log chart), [`Field::carry_leaks`] over each tick's pair chart gives every site's leak read `ℓ` as the forward's own
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
/// the same faces, the same port code and the same covector as the same region with the cut off, because [`FieldDeclaration::room_window`] admits
/// no window where the field has circles; the same region on the field without circles still cuts.
#[test]
fn a_field_with_carry_circles_keeps_every_room_whole() {
    for ticks in [2usize, 4] {
        let plain = Field::found(FieldDeclaration { reach: 400, ticks, ..four_contacts(1) }, &keys(1 << 14)).unwrap();
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
            port: Some(Port { start: q.len(), void: 0, target: &target, boundary: true, stop: None, heard: Some(&heard), window, letters: false }),
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
    assert_eq!(FieldLearner::from_text(&text).unwrap().rate_parts, learner.rate_parts, "the line's own order round-trips");
    let older: String = text.lines().map(|l| if l.starts_with("parts ") { format!("{}\n", l.split(' ').take(2 + PLAIN_PARTS).collect::<Vec<_>>().join(" ")) } else { format!("{l}\n") }).collect();
    let read = FieldLearner::from_text(&older).unwrap().rate_parts.unwrap();
    assert_eq!((read.octaves[3], read.octaves[19], read.octaves[20], read.octaves[21]), (1, 0, 0, 0), "a sixteen-part line reads the letter rows at octave 0");
    assert_eq!(written_parts(0), (0..16).chain(19..22).collect::<Vec<_>>());
    assert_eq!(written_parts(2), (0..22).collect::<Vec<_>>());
}
