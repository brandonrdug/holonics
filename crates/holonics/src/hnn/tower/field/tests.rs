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
    FieldDeclaration { alphabet: 5, width: 8, heads: 2, modes: 3, still, contacts: 4, ticks: 2, frames: 2, reach: 16 }
}

/// A tiny field with every family drawn from the keys (the founding holds the returns and the
/// readout at zero, where no covector reaches the charts).
fn shaped(still: usize) -> Field {
    let d = tiny_declaration(still);
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
/// same at every site, and a framed field's carries each site's place: the moment is phase-carried. Every
/// site carries the same face, so each is keyed and every site a source (§16.20).
#[test]
fn the_current_carries_place_when_the_weights_are_flat() {
    for (still, framed) in [(2usize, false), (1, true)] {
        let mut field = silent_contacts(shaped(still));
        let l = field.layout.clone();
        let m2 = 2 * field.declaration.complex();
        let dw = field.declaration.width;
        field.theta[l.q..l.q + m2 * dw].iter_mut().for_each(|v| *v = 0);
        field.theta[l.q_bias..l.q_bias + m2].iter_mut().for_each(|v| *v = 0);
        let classes = [2usize; 6];
        let open = [true; 6];
        let carried: Vec<Option<Shares>> = vec![Some(vec![(2, 1 << STATE_BITS)]); 6];
        let faces = field.faces(&Region { classes: &classes, unresolved: &open, faces: &carried, locked: &[], echo: &[], domain: None, port: None }).unwrap();
        let alike = faces.iter().all(|f| f == &faces[0]);
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
    assert_eq!(back, learner);
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
    // [§16.24] And a region whose last three sites are an answer port, compared through its coupling with two cells.
    const PORTED: [bool; 7] = [false, true, false, false, true, true, true];
    let port = Port { start: 4, void: 0, target: &[2, 3] };
    for (still, r) in [0usize, 1, 2].into_iter().flat_map(|still| [(still, region()), (still, Region { classes: &CLASSES, unresolved: &OPEN, faces: &carried, locked: &[], echo: &[], domain: None, port: None }), (still, Region { classes: &CLASSES, unresolved: &PORTED, faces: &[], locked: &[], echo: &[], domain: None, port: Some(port) })]) {
        let field = shaped(still);
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

/// [definition; agent-inferred, November 1] **The falloff is the medium's distance** (the
/// dispersing field's §2.3): with every key and probe zero (so every site shares one class and meets every
/// other, every source known) a row's terms differ by the octave of their distance and nothing else,
/// `p_j 2^⌊log₂ |i − j|⌋` one value across the row's sources to the shares' rounding (§14.11: each term
/// keeps its own exponent); so even a still field with its strand contacts silent reads the order of
/// its classes.
#[test]
fn the_falloff_weighs_a_source_by_the_octave_of_its_distance() {
    let mut field = silent_contacts(shaped(2));
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
            let scaled: Vec<u128> = row.iter().map(|src| (src.p as u128) << octave(i.abs_diff(src.j as usize))).collect();
            let (low, high) = (*scaled.iter().min().unwrap(), *scaled.iter().max().unwrap());
            assert!(high - low <= 1 << 10, "site {i}: the terms differ by their octaves alone: {scaled:?}");
        }
    }
    assert_eq!([1usize, 2, 3, 4, 5, 7, 8, 1000].map(octave), [0, 1, 1, 2, 2, 2, 3, 9]);
    let faces = field.faces(&region()).unwrap();
    let order = [3usize, 0, 6, 1, 5, 2, 4];
    let classes: Vec<usize> = order.iter().map(|&t| CLASSES[t]).collect();
    let open: Vec<bool> = order.iter().map(|&t| OPEN[t]).collect();
    let permuted = field.faces(&Region { classes: &classes, unresolved: &open, faces: &[], locked: &[], echo: &[], domain: None, port: None }).unwrap();
    assert!(order.iter().enumerate().any(|(n, &t)| permuted[n] != faces[t]), "a still field reads distance");
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

/// The learner's deposits are certified: each deposited section codes its own regions in fewer
/// bits, and over a few sections the regions' code falls from the founding's. (At the rate `2^(−4)`
/// the opening's three encodings step together and, from the second section, both the full and the
/// half step raise the code, so every later step is refused; at `2^(−5)` to `2^(−8)` all twelve
/// deposit, measured November 1.)
#[test]
fn certified_deposits_lower_the_code() {
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
        if receipt.deposited {
            assert!(receipt.code_after < receipt.code_before);
            deposited += 1;
        }
    }
    let after: i64 = regions.iter().map(|r| learner.field.code(r).unwrap().0).sum();
    assert!(deposited >= 6, "deposited {deposited}");
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
    let once = field.sample_realized(&problems, 3, 0, 11, &mut HostField, &mut |_, _| true).unwrap();
    assert_eq!(once.iter().map(Vec::len).collect::<Vec<_>>(), vec![6, 5]);
    assert!(once.iter().flatten().all(|&c| c < field.declaration.alphabet));
    assert_eq!(field.sample_realized(&problems, 3, 0, 11, &mut HostField, &mut |_, _| true).unwrap(), once, "the same draws");
    assert!((12..20).any(|seed| field.sample_realized(&problems, 3, 0, seed, &mut HostField, &mut |_, _| true).unwrap() != once), "another seed draws another answer");
    let mut asked = 0;
    let stopped = field.sample_realized(&problems, 3, 0, 11, &mut HostField, &mut |_, _| {
        asked += 1;
        asked < 2
    }).unwrap();
    assert_eq!(stopped.iter().map(Vec::len).collect::<Vec<_>>(), vec![6, 5], "a stopped write draws every place");
    let l = field.layout.clone();
    field.theta[l.read_bias + 2] = 40 << 16;
    let pointed = field.sample_realized(&problems, 3, 0, 11, &mut HostField, &mut |_, _| true).unwrap();
    assert!(pointed.iter().flatten().all(|&c| c == 2), "{pointed:?}");
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
    let mut learner = FieldLearner::new(field, 2);
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

/// The certificate reads its step's size by the same bounded law: a section deposits the step
/// at the size the law stands it at on the section's own regions, strictly fewer bits, or none,
/// and reads the regions at most three times for it after its opening read.
#[test]
fn the_certificate_reads_the_step_s_size_by_the_bounded_law() {
    let field = Field::found(tiny_declaration(1), &keys(1 << 14)).unwrap();
    let mut learner = FieldLearner::new(field, 2);
    let regions = [region()];
    let compared_on = |field: &Field| compared(&[field.faces(&regions[0]).unwrap()], &regions).unwrap();
    let (mut deposited, mut withheld) = (0, 0);
    for k in 0..12 {
        // The held step is read first; the certificate reads from the material that stands.
        learner.held = None;
        let opening = learner.field.clone();
        let mut counted = Counted { reads: 0 };
        let receipt = learner.section_realized(&regions, &mut counted).unwrap();
        assert!(counted.reads <= 4, "section {k}: {} reads", counted.reads);
        let mut step = vec![0i128; opening.theta.len()];
        for &(start, len, grain) in opening.families() {
            for i in start..start + len {
                step[i] = deposit_step(learner.first[i], learner.second[i], grain, learner.rate_bits);
            }
        }
        let old = compared_on(&opening);
        assert_eq!((receipt.halvings, receipt.deposited), law_scale(&opening, &step, 0, &old, true, &regions), "section {k}");
        if receipt.deposited {
            deposited += 1;
            assert_eq!(learner.field, stepped(&opening, &step, receipt.halvings).unwrap().0);
            assert!(fewer(&old, &compared_on(&learner.field), &spans_of(&regions)), "the deposit codes its section strictly fewer bits");
        } else {
            withheld += 1;
            assert_eq!(learner.field, opening);
        }
    }
    assert!(deposited >= 1, "deposited {deposited} withheld {withheld}");
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
    let at = |modes: usize, reach: usize| FieldDeclaration { alphabet: 5, width: 8, heads: 2, modes, still: 1, contacts: 4, ticks: 2, frames: 2, reach }.score_shift();
    assert_eq!(at(8, 2221), -2, "reading 8's declaration locks an equal word at 32 bits");
    assert_eq!(at(16, 16), 1);
    assert_eq!(at(3, 16), -2);
    for (modes, reach) in [(8usize, 2221usize), (16, 16), (3, 16), (8, 2), (16, 1 << 20), (1, 1 << 20)] {
        let (beta, need) = (at(modes, reach), 2 * (u128::BITS - ((reach - 1) as u128).leading_zeros()).max(1) as u128);
        let gained = |b: i32| if b >= 0 { (modes as u128) >> b } else { (modes as u128) << -b };
        assert!(gained(beta) >= need && gained(beta + 1) < need, "the largest such shift: modes {modes} reach {reach}");
    }
    let d = FieldDeclaration { alphabet: 5, width: 8, heads: 2, modes: 8, still: 1, contacts: 4, ticks: 2, frames: 2, reach: 2221 };
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
    let d = FieldDeclaration { alphabet: 5, width: 8, heads: 2, modes: 3, still: 1, contacts: 4, ticks: 2, frames: 2, reach: 32 };
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
    let d = FieldDeclaration { alphabet: 44, width: 32, heads: 5, modes: 8, still: 2, contacts: 32, ticks: 2, frames: 5, reach: 484 };
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
    let sheets = |field: &Field, r: &Region| -> Vec<Vec<u32>> { field.pass(r, true).unwrap().ticks.iter().flat_map(|c| c.classes.iter().map(|l| l.off.iter().chain(&l.members).copied().collect())).collect() };
    let long: Vec<usize> = (0..26).map(|t| [1usize, 3, 2, 4, 0, 2, 1][t % 7]).collect();
    let long_open: Vec<bool> = (0..26).map(|t| t % 9 == 4 || t == 25).collect();
    let (mut read, mut seams) = (0usize, 0usize);
    for still in [0usize, 1] {
        let mut d = tiny_declaration(still);
        d.reach = 32;
        let mut field = Field::found(d, &keys(1 << 14)).unwrap();
        let stream = keys(1 << 15);
        for (k, v) in field.theta.iter_mut().enumerate() {
            let word = &stream[4 * k..4 * k + 4];
            let grain = field.layout.families.iter().find(|(s, l, _)| (*s..*s + *l).contains(&k)).unwrap().2;
            *v = (((i32::from_be_bytes([word[0], word[1], word[2], word[3]]) as i64) << grain) >> 32) as i32;
        }
        for r in [region(), Region { classes: &long, unresolved: &long_open, faces: &[], locked: &[], echo: &[], domain: None, port: None }] {
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
    let r = Region { classes: &CLASSES, unresolved: &PORTED, faces: &[], locked: &[], echo: &[], domain: None, port: Some(Port { start: 4, void: 0, target: &target }) };
    let faces = field.faces(&r).unwrap();
    let place = faces[1].as_ref().unwrap().code(CLASSES[1]);
    let at: Vec<(&[u128], u128)> = faces[4..].iter().map(|f| { let f = f.as_ref().unwrap(); (f.masses.as_slice(), f.total) }).collect();
    let coupled = crate::receiver::coupling::coupling_code(&at, 0, &target, None).unwrap().code;
    assert_eq!(field.code(&r).unwrap(), (place + coupled, 1 + 3));
    let unported = Region { port: None, ..r };
    assert_ne!(field.code(&unported).unwrap().0, field.code(&r).unwrap().0, "the place-wise code differs from the coupling's");
}

/// [definition; §16.28] **An open site is silent on the strand**: on a field whose every family is drawn (the
/// unresolved rows of the moment encodings and the paces among them), a run of open sites appended past a region leaves
/// every earlier site's face as it was, except the last original site's, whose after-neighbour's contact row is now the
/// open one; so the writer's long open extent reads its answer places as a short training region does.
#[test]
fn an_open_stretch_leaves_the_other_sites_faces_as_they_were() {
    for still in [0usize, 1] {
        let field = shaped(still);
        let short = field.faces(&region()).unwrap();
        let mut classes = CLASSES.to_vec();
        let mut open = OPEN.to_vec();
        classes.extend([0usize; 6]);
        open.extend([true; 6]);
        let long = Region { classes: &classes, unresolved: &open, faces: &[], locked: &[], echo: &[], domain: None, port: None };
        let faces = field.faces(&long).unwrap();
        for t in 0..CLASSES.len() - 1 {
            assert_eq!(faces[t], short[t], "still {still} site {t}");
        }
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
            let next = learner.section(&[region()]).unwrap();
            assert_eq!(next.code_before, learner.field.code(&region()).unwrap().0.min(next.code_before), "the next section opens on the stepped material");
        }
    }
    assert!(deposited > 0);
}
