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
    FieldDeclaration { alphabet: 5, width: 8, heads: 2, modes: 3, still, contacts: 4, ticks: 2, frames: 2, reach: 16, clocks: 0 }
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
    Region { classes: &CLASSES, unresolved: &OPEN, faces: &[], locked: &[], clock: &[], echo: &[] }
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

/// The code's own covector (the face's comparison alone, without the closure's).
fn covector_of(field: &Field, region: &Region) -> Vec<i128> {
    let pass = field.pass(region, true).unwrap();
    let mut g = vec![0i128; field.theta.len()];
    field.returned(region, &pass, &mut g, false).unwrap();
    g
}

/// The learner's covector of one region (the reverse, with the closure's comparison).
fn reversed_of(field: &Field, region: &Region) -> Vec<i128> {
    let pass = field.pass(region, true).unwrap();
    let mut g = vec![0i128; field.theta.len()];
    field.reverse(region, &pass, &mut g).unwrap();
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
    assert!(field.faces(&Region { classes: &classes, unresolved: &open, faces: &[], locked: &[], clock: &[], echo: &[] }).is_err());
    assert!(field.faces(&Region { classes: &classes[..16], unresolved: &open[..16], faces: &[], locked: &[], clock: &[], echo: &[] }).is_ok());
}

/// With flat weights (no chart reads) and silent strand contacts, a still field's current is the
/// same at every site, and a framed field's carries each site's place: the moment is phase-carried.
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
        let faces = field.faces(&Region { classes: &classes, unresolved: &open, faces: &[], locked: &[], clock: &[], echo: &[] }).unwrap();
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
    for (still, r) in [0usize, 1, 2].into_iter().flat_map(|still| [(still, region()), (still, Region { classes: &CLASSES, unresolved: &OPEN, faces: &carried, locked: &[], clock: &[], echo: &[] })]) {
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
            let measured = plus.code(&r).unwrap().0 - minus.code(&r).unwrap().0;
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
    // closure's 204 and the far support's 232 are every one read, after 26, 0 and 137 halvings in all,
    // none on a seam.
    eprintln!("COVECTOR_PROBES read={read} halvings={halvings} on_a_seam={seams}");
    assert!(16 * seams <= read, "read {read} probes, {seams} on a seam at the smallest step");
}

/// [definition; agent-inferred, November 1] **The falloff is the medium's distance** (the
/// dispersing field's §2.3): with every word zero (so every site shares one class and meets every
/// other, every source known) a row's terms differ by the octave of their distance and nothing else,
/// `p_j 2^⌊log₂ |i − j|⌋` one value across the row's sources to the shares' rounding (§14.11: each term
/// keeps its own exponent); so even a still field with its strand contacts silent reads the order of
/// its classes.
#[test]
fn the_falloff_weighs_a_source_by_the_octave_of_its_distance() {
    let mut field = silent_contacts(shaped(2));
    let l = field.layout.clone();
    let (m2, dw) = (2 * field.declaration.complex(), field.declaration.width);
    field.theta[l.q..l.q + m2 * dw].iter_mut().for_each(|v| *v = 0);
    field.theta[l.q_bias..l.q_bias + m2].iter_mut().for_each(|v| *v = 0);
    let classes = [1usize, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2];
    let open = [false; 12];
    let pass = field.pass(&Region { classes: &classes, unresolved: &open, faces: &[], locked: &[], clock: &[], echo: &[] }, true).unwrap();
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
    let permuted = field.faces(&Region { classes: &classes, unresolved: &open, faces: &[], locked: &[], clock: &[], echo: &[] }).unwrap();
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
        let x = field.open(&region());
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
    let permuted = field.faces(&Region { classes: &classes, unresolved: &open, faces: &[], locked: &[], clock: &[], echo: &[] }).unwrap();
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
    let permuted = field.faces(&Region { classes: &classes, unresolved: &open, faces: &[], locked: &[], clock: &[], echo: &[] }).unwrap();
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
    let regions = [region(), Region { classes: &second_classes, unresolved: &second_open, faces: &[], locked: &[], clock: &[], echo: &[] }];
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
    let regions = [region(), Region { classes: &second_classes, unresolved: &second_open, faces: &[], locked: &[], clock: &[], echo: &[] }];
    let (_, g) = field.read_and_return(&regions).unwrap();
    let a = reversed_of(&field, &regions[0]);
    let b = reversed_of(&field, &regions[1]);
    let summed: Vec<i128> = a.iter().zip(&b).map(|(x, y)| x + y).collect();
    assert_eq!(g, summed);
    let (_, reversed) = field.read_and_return(&[regions[1], regions[0]]).unwrap();
    assert_eq!(reversed, g);
}

/// A logits read for a fixture: each unresolved site's face from `face(t, region)`.
fn read_with(face: &dyn Fn(usize, &Region) -> Vec<i64>) -> impl Fn(&[Region]) -> Result<Vec<FieldRead>> + '_ {
    move |rs: &[Region]| Ok(rs.iter().map(|r| FieldRead { logits: (0..r.classes.len()).map(|t| r.unresolved[t].then(|| face(t, r))).collect(), echo: vec![0; r.classes.len()] }).collect())
}

/// [definition; agent-inferred, November 1] **The front** (§14.3–§14.5) on a fixture whose sites read
/// class 2 before the answer's eighth site and the void from it: the answer's first five sites are
/// reached at the opening, beside the question, ride their momentum from rest on that face and lock at
/// their own rungs; each lock reaches the sites within its near field at the next sweep; the extent is
/// read where the front first locks the void (the eighth site), the sites past it leave, and every
/// site inside it locks at class 2. Reached is distance from a definite surface, never sureness.
#[test]
fn the_answer_grows_from_the_question_and_its_extent_is_read_at_the_front() {
    let field = shaped(1);
    let (void, question) = (0usize, [3usize, 1]);
    let start = question.len();
    let face = |t: usize, _: &Region| if t >= start + 7 { vec![3 << 16, 0, 0, 0, 0] } else { vec![0, 1 << 16, 3 << 16, 0, 0] };
    let mut seen = Vec::new();
    let released = field.release_with(&[(&question, 20)], 64, void, &mut read_with(&face), &mut |s| {
        seen.push(*s);
        true
    }).unwrap().remove(0);
    assert_eq!(released.sites, vec![Some(2); 7], "{released:?}");
    assert_eq!(released.extent.map(|(site, _, bound)| (site, bound)), Some((7, false)));
    assert!(released.reached[..5].iter().all(|&r| r == Some(0)), "the first five beside the question: {:?}", released.reached);
    assert!(released.reached.windows(2).all(|w| w[0] <= w[1]), "the front only grows outward");
    assert!(released.reached[5..].iter().all(|&r| r > Some(0)), "the rest only once a lock reaches them");
    assert!(released.lock_sweeps.iter().zip(&released.reached).all(|(l, r)| l > r), "a site moves only after it is reached");
    assert!(seen.iter().all(|s| s.front <= 20) && seen.last().unwrap().live == 0);
    // Determinism, and the release of k sweeps is the release stopped after k.
    assert_eq!(field.release_with(&[(&question, 20)], 64, void, &mut read_with(&face), &mut |_| true).unwrap().remove(0), released);
}

/// No void locks: the front reaches the answer's bound, and the extent is the bound, said so.
#[test]
fn an_extent_with_no_void_is_the_bound() {
    let field = shaped(1);
    let (void, question) = (0usize, [3usize, 1]);
    let face = |_: usize, _: &Region| vec![0, 1 << 16, 3 << 16, 0, 0];
    let released = field.release_with(&[(&question, 12)], 64, void, &mut read_with(&face), &mut |_| true).unwrap().remove(0);
    assert_eq!(released.extent.map(|(site, _, bound)| (site, bound)), Some((12, true)));
    assert_eq!(released.sites, vec![Some(2); 12]);
}

/// [definition; agent-inferred, November 1] **Each site keeps its own clock** (§14.4): a site whose
/// read flips with its neighbour's top never holds a majority through a sweep, so it never locks, its
/// own pump holds where its change does not fall, its overturns are the free circulation, the front
/// holds where nothing locks, and it is released open; read as its own copy, it locks.
#[test]
fn a_frustrated_site_holds_the_front_and_is_released_open() {
    let field = shaped(1);
    let (void, question) = (0usize, [3usize, 1]);
    let start = question.len();
    // The answer's first two sites each read the other's top and answer the other class of {1, 2}
    // (on the unresolved row, the other reads as 1); every other site reads 2.
    let flip = |t: usize, r: &Region| {
        if t != start && t != start + 1 {
            return vec![0, 0, 6 << 16, 0, 0];
        }
        let other = if t == start { start + 1 } else { start };
        match r.faces.get(other).and_then(Option::as_ref).map(|f| f.iter().max_by_key(|&&(_, w)| w).unwrap().0) {
            Some(1) => vec![0, 0, 6 << 16, 0, 0],
            _ => vec![0, 6 << 16, 0, 0, 0],
        }
    };
    let mut last = ReleaseSweep::default();
    let released = field.release_with(&[(&question, 8)], 40, void, &mut read_with(&flip), &mut |s| {
        last = *s;
        true
    }).unwrap().remove(0);
    assert_eq!(released.sites[..2], [None, None], "never forced into a class: {released:?}");
    assert!(released.free >= 10, "{released:?}");
    assert_eq!(last.done, 40);
    assert_eq!(released.trits[0].iter().filter(|&&t| t < 0).count() + released.trits[1..].iter().map(|t| t.iter().filter(|&&x| x < 0).count()).sum::<usize>(), released.free);
}

/// The release of `k` sweeps is the release its exterior stops after `k`.
#[test]
fn a_release_stopped_by_its_exterior_is_the_release_of_the_sweeps_it_ran() {
    let field = shaped(1);
    let questions: [&[usize]; 3] = [&[1, 4, 0, 2], &[3, 3], &[2, 1, 1, 4, 0]];
    let problems: Vec<(&[usize], usize)> = questions.iter().zip([5usize, 7, 3]).map(|(q, a)| (*q, a)).collect();
    for k in 1..=4 {
        let mut asked = Vec::new();
        let stopped = field.release_realized(&problems, 9, 0, &mut HostField, &mut |s| {
            asked.push(*s);
            s.done < k
        }).unwrap();
        let ran = asked.last().unwrap().done;
        assert!(ran <= k);
        for (&(q, a), released) in problems.iter().zip(&stopped) {
            assert_eq!(&field.release(q, a, ran, 0).unwrap(), released, "stopped after {ran} sweeps");
        }
    }
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
        let as_faces = Region { classes: &CLASSES, unresolved: &OPEN, faces: &carried, locked: &locked, clock: &[], echo: &[] };
        assert_eq!(field.faces(&as_faces).unwrap(), field.faces(&r).unwrap(), "still {still}");
        assert!(field.faces(&Region { classes: &CLASSES, unresolved: &OPEN, faces: &[], locked: &locked, clock: &[], echo: &[] }).is_err(), "a lock on a site that carries no face");
        // An unresolved site carried as one class, locked, opens on it and is still read.
        let mut at_open = carried.clone();
        at_open[1] = Some(vec![(4, 1 << STATE_BITS)]);
        locked[1] = true;
        let mut resolved_open = OPEN;
        resolved_open[1] = false;
        let read = field.faces(&Region { classes: &CLASSES, unresolved: &OPEN, faces: &at_open, locked: &locked, clock: &[], echo: &[] }).unwrap();
        let resolved = field.faces(&Region { classes: &CLASSES, unresolved: &resolved_open, faces: &[], locked: &[], clock: &[], echo: &[] }).unwrap();
        assert!(read[1].is_some());
        for t in (0..CLASSES.len()).filter(|&t| t != 1) {
            assert_eq!(read[t], resolved[t], "still {still} site {t}");
        }
        assert!(field.faces(&Region { classes: &CLASSES, unresolved: &OPEN, faces: &carried[..3], locked: &[], clock: &[], echo: &[] }).is_err(), "one carried face a site or none");
    }
}

/// A face resolves its top class only when the class outweighs every other together.
#[test]
fn a_face_resolves_only_a_majority() {
    assert_eq!(resolved(&TowerFace { masses: vec![6, 3, 2], total: 11 }), Some(0));
    assert_eq!(resolved(&TowerFace { masses: vec![5, 3, 2], total: 10 }), None, "half is not more than half");
    assert_eq!(resolved(&TowerFace { masses: vec![1, 4, 4], total: 9 }), None);
    assert_eq!(resolved(&TowerFace { masses: vec![1, 9, 1], total: 11 }), Some(1));
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
    let back = FieldLearner::from_text(&grown.to_text()).unwrap();
    assert_eq!(back, grown);
    // One learned section on the grown learner parts some pair of encoding copies.
    let mut next = grown.clone();
    next.section(&[region()]).unwrap();
    let w = next.field.declaration.width / 2;
    let parted = (0..=next.field.declaration.alphabet).any(|row| (0..w).any(|j| next.field.theta[l.enc + row * 2 * w + j] != next.field.theta[l.enc + row * 2 * w + w + j]));
    assert!(parted, "the copies part under learning");
}

fn face(masses: &[u128]) -> Option<TowerFace> {
    Some(TowerFace { masses: masses.to_vec(), total: masses.iter().sum() })
}

/// Problems released together are each problem's own release.
#[test]
fn releases_read_together_are_each_problem_s_own() {
    let field = shaped(1);
    let questions: [&[usize]; 3] = [&[1, 4, 0, 2], &[3, 3], &[2, 1, 1, 4, 0]];
    let problems: Vec<(&[usize], usize)> = questions.iter().zip([5usize, 7, 3]).map(|(q, a)| (*q, a)).collect();
    let together = field.release_realized(&problems, 3, 0, &mut HostField, &mut |_| true).unwrap();
    for (&(q, a), released) in problems.iter().zip(&together) {
        assert_eq!(&field.release(q, a, 3, 0).unwrap(), released);
    }
}

/// The size the law reads a step at on `regions` against `old` (the doc of [`scaled`], step by
/// step): the further halvings of the last size read and whether the step stands there.
fn law_scale(base: &Field, step: &[i128], h0: u32, old: &[(u128, u128)], strict: bool, regions: &[Region]) -> (u32, bool) {
    let on = |field: &Field| compared(&regions.iter().map(|r| field.faces(r).unwrap()).collect::<Vec<_>>(), regions);
    let stands = |new: &[(u128, u128)]| if strict { fewer_bits(old, new) } else { !fewer_bits(new, old) };
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
    let (e1, e2) = ((code_of(&on(&full)) - code_of(old)) as i128, (code_of(&on(&half)) - code_of(old)) as i128);
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
    let old = compared(&regions.iter().map(|r| before.faces(r).unwrap()).collect::<Vec<_>>(), regions);
    let (halvings, stands) = law_scale(before, step, h0, &old, false, regions);
    (halvings, !stands)
}

/// A deposited step is held and read on the next section: the material that stands is the law's
/// (the step at its size or half of it, or at the parabola's halving, or refused), it never codes
/// the next regions higher than the material before the step, and the section's opening read is
/// the standing material's; the held step crosses the learner's text.
#[test]
fn a_held_step_is_read_on_the_next_section() {
    let field = Field::found(tiny_declaration(1), &keys(1 << 14)).unwrap();
    let mut learner = FieldLearner::new(field, 2);
    let second_classes = [2usize, 2, 3, 1, 0, 4, 4];
    let second_open = [true, false, false, true, true, false, false];
    let second = Region { classes: &second_classes, unresolved: &second_open, faces: &[], locked: &[], clock: &[], echo: &[] };
    let (mut read, mut halved) = (0, 0);
    for k in 0..12 {
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
            let compared_on = |field: &Field| compared(&[field.faces(&regions[0]).unwrap()], &regions);
            let old = compared_on(&material);
            assert_eq!(next.change, code_of(&compared_on(&before.field)) - code_of(&old));
            assert_eq!((next.halvings, next.refused), law_next(&material, &held.step, held.halvings, &regions));
            let standing = if next.refused { material.clone() } else { stepped(&material, &held.step, held.halvings + next.halvings).unwrap().0 };
            assert!(!fewer_bits(&compared_on(&standing), &old), "the standing material codes the next regions no higher");
            if next.halvings > 0 || next.refused {
                halved += 1;
                assert!(fewer_bits(&compared_on(&before.field), &old), "the step at its size coded them higher");
            }
            // The section's opening read is the standing material's.
            assert_eq!(receipt.code_before, code_of(&compared_on(&standing)));
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
    let compared_on = |field: &Field| compared(&[field.faces(&regions[0]).unwrap()], &regions);
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
        assert_eq!(next.change, code_of(&climbed) - code_of(&old));
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
    let compared_on = |field: &Field| compared(&[field.faces(&regions[0]).unwrap()], &regions);
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
            assert!(fewer_bits(&old, &compared_on(&learner.field)), "the deposit codes its section strictly fewer bits");
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

trait Top {
    fn rank_top(&self) -> usize;
}

impl Top for TowerFace {
    fn rank_top(&self) -> usize {
        (0..self.masses.len()).find(|&c| self.rank(c) == 0).unwrap()
    }
}

/// Four pairs, their keys distinct in `0..8` and their values in `8..16`, then one of the keys and
/// its value unresolved.
fn recall_problem(seed: u64) -> Vec<usize> {
    let mut state = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ 0xD1B5_4A32_D192_ED03;
    let mut next = move || {
        state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    };
    let mut keys: Vec<usize> = (0..8).collect();
    for i in (1..8).rev() {
        keys.swap(i, (next() % (i as u64 + 1)) as usize);
    }
    let mut classes = Vec::new();
    for &key in &keys[..4] {
        classes.extend([key, 8 + (next() % 8) as usize]);
    }
    let j = (next() % 4) as usize;
    classes.extend([keys[j], classes[2 * j + 1]]);
    classes
}

/// The strand contacts let a value be found by its key: a site opens with the word before it, so the
/// unresolved value meets the value site whose key is its own in one contact, and the field learns
/// the recall. Measured November 1 at this declaration and rate (§17 of the field's record): held
/// codes 0.020 bits at 1,000 sections and 0.000 at 2,000; the same field opened on its own class
/// alone stayed at 2.09 bits after 2,000 sections, the code of knowing only which values are present.
/// Under the dispersing field (a site past the near field met only through its classes, its weight
/// charged the octave of its distance) the held recall coded 0.295 bits at 1,000 sections with two
/// sheet bits (4 classes) and 0.557 with two shell trits (9 classes, fewer class-mates for the open
/// site's word to meet): read here against a third of the 2.09 bits of knowing only which values are
/// present.
#[test]
fn the_strand_contacts_let_a_value_be_recalled_by_its_key() {
    let d = FieldDeclaration { alphabet: 16, width: 16, heads: 2, modes: 4, still: 2, contacts: 16, ticks: 2, frames: 2, reach: 16, clocks: 0 };
    let mut learner = FieldLearner::new(Field::found(d, &keys(1 << 18)).unwrap(), 6);
    let open: Vec<bool> = (0..10).map(|t| t == 9).collect();
    let code = |learner: &FieldLearner| -> i64 {
        (0..64u64).map(|i| learner.field.code(&Region { classes: &recall_problem(1_000_000 + i), unresolved: &open, faces: &[], locked: &[], clock: &[], echo: &[] }).unwrap().0).sum::<i64>() / 64
    };
    for s in 0..1000u64 {
        let problems: Vec<Vec<usize>> = (0..16).map(|i| recall_problem(s * 16 + i)).collect();
        let regions: Vec<Region> = problems.iter().map(|c| Region { classes: c, unresolved: &open, faces: &[], locked: &[], clock: &[], echo: &[] }).collect();
        learner.section(&regions).unwrap();
    }
    let held = code(&learner);
    eprintln!("RECALL_HELD millibits={}", held * 1000 >> 20);
    // The record's bar (§14.8): 0.25 bits on 2^(−20).
    assert!(held < 1 << 18, "the held recall codes {} millibits", held * 1000 >> 20);
}


/// The founding is the pair's likeness: one word chart is the probe and the key at once, every class
/// has a word in the encoding and both strand contacts, and the unresolved rows carry none.
#[test]
fn the_founding_is_the_pair_s_likeness() {
    let field = Field::found(tiny_declaration(1), &keys(1 << 14)).unwrap();
    let (dw, a, m2) = (field.declaration.width, field.declaration.alphabet, 2 * field.declaration.complex());
    let l = field.layout.clone();
    assert!(field.theta[l.q..l.q + m2 * dw].iter().any(|&v| v != 0));
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
    assert!(shaped(1).faces(&Region { classes: &one, unresolved: &[true], faces: &[], locked: &[], clock: &[], echo: &[] }).is_err(), "a lone site has no site to meet");
}

/// The contact's gain covers the falloff: the largest shift, negative where it amplifies, at which a
/// head's lock of an equal word (`n` at unit power, half its `2n` reals) reads `2⌈log₂ reach⌉` bits.
#[test]
fn the_contact_s_gain_covers_the_falloff() {
    let at = |modes: usize, reach: usize| FieldDeclaration { alphabet: 5, width: 8, heads: 2, modes, still: 1, contacts: 4, ticks: 2, frames: 2, reach, clocks: 0 }.score_shift();
    assert_eq!(at(8, 2221), -2, "reading 8's declaration locks an equal word at 32 bits");
    assert_eq!(at(16, 16), 1);
    assert_eq!(at(3, 16), -2);
    for (modes, reach) in [(8usize, 2221usize), (16, 16), (3, 16), (8, 2), (16, 1 << 20), (1, 1 << 20)] {
        let (beta, need) = (at(modes, reach), 2 * (u128::BITS - ((reach - 1) as u128).leading_zeros()).max(1) as u128);
        let gained = |b: i32| if b >= 0 { (modes as u128) >> b } else { (modes as u128) << -b };
        assert!(gained(beta) >= need && gained(beta + 1) < need, "the largest such shift: modes {modes} reach {reach}");
    }
    let d = FieldDeclaration { alphabet: 5, width: 8, heads: 2, modes: 8, still: 1, contacts: 4, ticks: 2, frames: 2, reach: 2221, clocks: 0 };
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

/// The share of row `i`'s weight at site `j` in still head `h` of a pass's first tick, on `2^(−20)`,
/// on the mean over the head's modes.
fn share(pass: &FieldPass, sites: usize, h: usize, i: usize, j: usize) -> u64 {
    let row = &pass.ticks[0].rows[h * sites + i];
    let at: u128 = row.iter().find(|src| src.j as usize == j).map_or(0, |src| src.p as u128);
    let total: u128 = row.iter().map(|src| src.p as u128).sum();
    (at << 20).div_euclid(total.max(1)) as u64
}

/// A row as `(place, share)`.
fn as_pairs(row: &[Source]) -> Vec<(u32, u64)> {
    row.iter().map(|src| (src.j, src.p)).collect()
}

/// The site carrying a row's peak (the lower site on a tie).
fn peak_of(row: &[(u32, u64)]) -> usize {
    row.iter().fold((0usize, 0u64), |b, &(j, e)| if e > b.1 || (e == b.1 && (j as usize) < b.0) { (j as usize, e) } else { b }).0
}

/// The founded contact meets the site whose word is its own: in a still set, an equal word shares
/// every resonance class, so a site meets the one other site whose word (its class and both
/// neighbours') is the same wherever it stands, and outweighs every other site past the near field,
/// in every region and head, at the founding, before any learning (a word at unit power meets its
/// equal at `2n`, the most any pair reaches, and the falloff charges both the same octave). The near
/// field is heard at every frequency, so a near site can outweigh it: measured November 1, the
/// equal word held the whole row's peak in 31 of these 32 rows.
#[test]
fn the_founded_contact_meets_the_site_whose_word_is_its_own() {
    let d = FieldDeclaration { alphabet: 16, width: 32, heads: 2, modes: 8, still: 2, contacts: 8, ticks: 1, frames: 2, reach: 64, clocks: 0 };
    let field = Field::found(d, &keys(1 << 16)).unwrap();
    let sites = 48;
    let (mut met, mut read) = (0usize, 0usize);
    for seed in 0..16u64 {
        let mut classes = drawn_classes(seed, sites, d.alphabet);
        // Site 40's word, written again at 10.
        let (i, j) = (40usize, 10usize);
        let word = classes[i - 1..=i + 1].to_vec();
        classes[j - 1..=j + 1].copy_from_slice(&word);
        let open = vec![false; sites];
        let pass = field.pass(&Region { classes: &classes, unresolved: &open, faces: &[], locked: &[], clock: &[], echo: &[] }, true).unwrap();
        for h in 0..d.heads {
            let far: Vec<(u32, u64)> = as_pairs(&pass.ticks[0].rows[h * sites + i]).into_iter().filter(|&(k, _)| (k as usize).abs_diff(i) >= NEAR).collect();
            met += usize::from(peak_of(&far) == j);
            read += 1;
        }
    }
    assert_eq!(met, read, "met {met} of {read}");
}

/// [measurement, not a law] The founded contact's share at its crib at a GSM8K region's size and the
/// realized declaration of the seventh reading's field: a resolved site whose whole word recurs, an
/// open site whose two neighbours recur around one question site, and an open site whose left
/// neighbour alone recurs. Printed for the record; run with `--ignored --nocapture`.
#[test]
#[ignore]
fn founded_contact_shares_at_a_question_s_size() {
    let d = FieldDeclaration { alphabet: 122, width: 32, heads: 4, modes: 8, still: 2, contacts: 32, ticks: 1, frames: 4, reach: 2221, clocks: 0 };
    let field = Field::found(d, &keys(1 << 20)).unwrap();
    let sites = 450;
    for (name, case) in [("whole word", 0usize), ("both neighbours", 1), ("left neighbour", 2)] {
        let mut shares = Vec::new();
        let mut peaks = 0usize;
        for seed in 0..8u64 {
            let mut classes = drawn_classes(seed, sites, d.alphabet);
            let (i, j) = (400usize, 60usize);
            let mut open = vec![false; sites];
            match case {
                0 => {
                    let word = classes[i - 1..=i + 1].to_vec();
                    classes[j - 1..=j + 1].copy_from_slice(&word);
                }
                1 => {
                    classes[j - 1] = classes[i - 1];
                    classes[j + 1] = classes[i + 1];
                    open[i] = true;
                }
                _ => {
                    classes[j - 1] = classes[i - 1];
                    open[i] = true;
                    open[i + 1] = true;
                }
            }
            let pass = field.pass(&Region { classes: &classes, unresolved: &open, faces: &[], locked: &[], clock: &[], echo: &[] }, true).unwrap();
            for h in 0..d.still {
                shares.push(share(&pass, sites, h, i, j));
                peaks += usize::from(peak_of(&as_pairs(&pass.ticks[0].rows[h * sites + i])) == j);
            }
        }
        shares.sort_unstable();
        println!("FOUNDED_SHARE case={name} sites={sites} peaks={peaks}/{} shares_on_2^-20={shares:?}", shares.len());
    }
}

/// A permutation of the ten words `0..10`, the separator `10`, then one of its words (the cue) and
/// the word that followed it in the permutation, unresolved.
fn cue_problem(seed: u64) -> Vec<usize> {
    let mut next = mixer(seed);
    let mut classes: Vec<usize> = (0..10).collect();
    for i in (1..10).rev() {
        classes.swap(i, (next() % (i as u64 + 1)) as usize);
    }
    let k = (next() % 9) as usize;
    classes.extend([10, classes[k], classes[k + 1]]);
    classes
}

/// The contact finds a cue's successor: the open site's word is the cue on its left, so it meets
/// the one site of the permutation whose left neighbour is the cue, and the field learns to read
/// that site's class. Its own class and the words present alone code the successor at about
/// `log₂ 9` bits. Measured November 1 at this declaration and rate (§18 of the field's record): held
/// codes 0.204 bits at 200 sections, 0.017 at 400, 0.006 at 600 and 0.000 from 1,400; under §17's
/// founding and contact (charts at their own scale, the fixtures' former key stream) the same problems
/// stayed at 3.3 bits after 2,000 sections. Under the dispersing field it codes 0.095 bits at 600
/// sections, read here below a quarter of a bit, under a twelfth of `log₂ 9`.
#[test]
fn the_contact_finds_a_cue_s_successor() {
    let d = FieldDeclaration { alphabet: 11, width: 16, heads: 2, modes: 4, still: 2, contacts: 16, ticks: 2, frames: 2, reach: 16, clocks: 0 };
    let mut learner = FieldLearner::new(Field::found(d, &keys(1 << 18)).unwrap(), 6);
    let open: Vec<bool> = (0..13).map(|t| t == 12).collect();
    let code = |learner: &FieldLearner| -> i64 {
        (0..64u64).map(|i| learner.field.code(&Region { classes: &cue_problem(1_000_000 + i), unresolved: &open, faces: &[], locked: &[], clock: &[], echo: &[] }).unwrap().0).sum::<i64>() / 64
    };
    for s in 0..600u64 {
        let problems: Vec<Vec<usize>> = (0..16).map(|i| cue_problem(s * 16 + i)).collect();
        let regions: Vec<Region> = problems.iter().map(|c| Region { classes: c, unresolved: &open, faces: &[], locked: &[], clock: &[], echo: &[] }).collect();
        learner.section(&regions).unwrap();
    }
    let held = code(&learner);
    eprintln!("CUE_HELD millibits={}", held * 1000 >> 20);
    // The record's bar (§14.8): 0.0625 bits on 2^(−20).
    assert!(held < 1 << 16, "the held successor codes {} millibits", held * 1000 >> 20);
}

/// Without a holder (no resolved site holds an unresolved site's class) or without a still ring
/// set, the closure compares nothing and the reverse is the code's own covector, bit for bit; with
/// one, the closure's comparison joins it (§19).
#[test]
fn the_closure_compares_only_where_a_class_is_held() {
    let returned = |field: &Field, region: &Region, closure: bool| -> Vec<i128> {
        let pass = field.pass(region, true).unwrap();
        let mut g = vec![0i128; field.theta.len()];
        field.returned(region, &pass, &mut g, closure).unwrap();
        g
    };
    let unheld_classes = [1usize, 4, 0, 2, 3, 3, 1];
    let unheld_open = [false, true, false, true, false, false, false];
    let unheld = Region { classes: &unheld_classes, unresolved: &unheld_open, faces: &[], locked: &[], clock: &[], echo: &[] };
    for still in [0usize, 1, 2] {
        let field = shaped(still);
        assert_eq!(returned(&field, &unheld, true), returned(&field, &unheld, false), "still {still}: no class is held");
        let held = region();
        let (with, without) = (returned(&field, &held, true), returned(&field, &held, false));
        if still == 0 {
            assert_eq!(with, without, "no still ring set compares");
        } else {
            assert_ne!(with, without, "still {still}: a held class is compared");
        }
    }
}

/// The closure's own code (§19), on `2^(−20)` bits: at every tick and every head of a still ring
/// set, each unresolved site's code of its class on its row's copy face over its support,
/// `−log₂ Σ_(j∈S_i holds) p_ij`, read over its set's `copies` heads.
fn closure_code(field: &Field, region: &Region) -> i64 {
    let d = field.declaration;
    let pass = field.pass(region, true).unwrap();
    let sites = region.classes.len();
    let mut code = 0i64;
    for (tick, cell) in pass.ticks.iter().enumerate() {
        for h in (0..d.heads).filter(|&h| d.closes(tick, h)) {
            for i in (0..sites).filter(|&i| region.unresolved[i]) {
                let row = &cell.rows[h * sites + i];
                let held: u128 = row.iter().filter(|src| !region.unresolved[src.j as usize] && region.classes[src.j as usize] == region.classes[i]).map(|src| src.p as u128).sum();
                if held > 0 {
                    code += face(&[held, (1u128 << SHARE_BITS) - held]).unwrap().code(0);
                }
            }
        }
    }
    code / d.copies() as i64
}

/// The closure's covector is its code's: the reverse with the closure less the reverse without it
/// agrees with the closure's code's central difference (as the face's covector does with the face's
/// code, [`covector_matches_the_codes_difference`]) on the entries of every family it reaches, on
/// the founded declaration and grown by two, where each still ring set holds two copies.
#[test]
fn the_closure_s_covector_matches_its_code_s_difference() {
    let r = region();
    // A probe whose `±δ` moves a site across a sheet changes the support, and the code jumps there
    // (the address is sharp, §15.2's measurement): it is left out and counted.
    let sheets = |field: &Field| -> Vec<Vec<u32>> { field.pass(&r, true).unwrap().ticks.iter().flat_map(|c| c.classes.iter().map(|l| l.class.iter().copied().chain(l.probes.iter().flat_map(|p| std::iter::once(u32::MAX).chain(p.iter().copied()))).collect())).collect() };
    let (mut seams, mut read, mut halvings) = (0usize, 0usize, 0u32);
    for still in [1usize, 2] {
        let base = shaped(still);
        let draws = base.growth_draws(2);
        let grown = base.grown(2, &keys(draws)).unwrap().0;
        assert_eq!(closure_code(&grown, &r), closure_code(&base, &r), "still {still}: a set compares once however many heads it holds");
        for field in [base, grown] {
            let (with, without) = (reversed_of(&field, &r), covector_of(&field, &r));
            let g: Vec<i128> = with.iter().zip(&without).map(|(a, b)| a - b).collect();
            let mut probed = 0;
            for &(start, len, grain) in field.families() {
                let natural: u32 = if grain == MATERIAL_BITS { 40 } else { 24 };
                let mut entries: Vec<usize> = (start..start + len).collect();
                entries.sort_by_key(|&i| std::cmp::Reverse(g[i].unsigned_abs()));
                for &i in entries.iter().take(3).filter(|&&i| g[i] != 0) {
                    // The central difference at `δ` and at `δ/2`: the closure's code is `−log₂` of a
                    // holder share, curved enough that a step of `2^(−9)` can miss by its `δ²` term,
                    // and the forward's releases put a noise of about a tenth on a step much smaller
                    // (measured November 1: at the founded field's `b_bias` 3,326 at `δ` and 4,254 at
                    // `δ/2` against 4,481 predicted, converging; at `q_bias` 13,474, 12,064, 14,632 and
                    // 13,216 at `δ` to `δ/8` against 13,697, scattered). The covector agrees where
                    // either step does.
                    let central = |step: i32| -> Option<i64> {
                        let (mut plus, mut minus) = (field.clone(), field.clone());
                        plus.theta[i] += step;
                        minus.theta[i] -= step;
                        (sheets(&plus) == sheets(&field) && sheets(&minus) == sheets(&field)).then(|| closure_code(&plus, &r) - closure_code(&minus, &r))
                    };
                    let straddles = |step: i32| central(step).is_none() || central(step / 2).is_none();
                    let Some((delta, h)) = unstraddled(grain, &straddles) else {
                        seams += 1;
                        continue;
                    };
                    halvings += h;
                    let (whole, half) = (central(delta).unwrap(), central(delta / 2).unwrap());
                    let predicted = (g[i] * 2 * delta as i128) >> (natural + grain - 20);
                    // The closure's code is `−log₂` of a holder share, which magnifies the forward's
                    // releases: its rounding floor is about 512 on 2^(−20) bits (measured November 1 at
                    // the founded field's `b_bias` read at the last of two ticks: its differences at
                    // steps 2^(−13) to 2^(−16) scatter by ±560 around a signal under 400, while at
                    // 2^(−9) it reads −6,023 against −5,922 predicted).
                    let tolerance = predicted.abs() / 8 + (512 << h);
                    let agrees = |measured: i64| (measured as i128 - predicted).abs() <= tolerance;
                    read += 1;
                    assert!(agrees(whole) || agrees(2 * half), "still {still} width {} family at {start} (grain {grain}) entry {i}: measured {whole} at δ and {} at δ/2 ({h} halvings), predicted {predicted}", field.declaration.width, 2 * half);
                    probed += 1;
                }
            }
            assert!(probed > 0, "still {still}: the closure reaches the charts");
        }
    }
    // Every probe is read at the largest step `2^(grain − 9 − h)` that crosses no sheet and no band
    // edge (the receivers' probes across their seams, §15.2's multi-probe, add a jump at each band
    // edge), halving `h ≤ STRADDLE_HALVINGS` times; one still straddling at the smallest step stands on
    // a seam and is counted apart. The tolerance's floor is the code's rounding, `64` on 2^(−20) bits,
    // which stands while the difference falls by `2^h`, so it is `64 · 2^h`; a quiet entry's step is
    // first doubled above the floor ([`probe_step`]). Measured November 2: the face's 364 probes, the
    // closure's 204 and the far support's 232 are every one read, after 26, 0 and 137 halvings in all,
    // none on a seam.
    eprintln!("CLOSURE_PROBES read={read} halvings={halvings} on_a_seam={seams}");
    assert!(16 * seams <= read, "read {read} probes, {seams} on a seam at the smallest step");
}

/// Two numbers of two digits stand in a filler text, the first anywhere before the second; the
/// region ends with the marker `14` and two unresolved sites, the first number's digits. Nothing in
/// a word tells the first number from the second: only their order does.
fn order_problem(seed: u64, n: usize) -> Vec<usize> {
    let mut next = mixer(seed);
    let mut classes: Vec<usize> = (0..n - 3).map(|_| (next() % 4) as usize).collect();
    let mut digits: Vec<usize> = (4..14).collect();
    for i in (1..10).rev() {
        digits.swap(i, (next() % (i as u64 + 1)) as usize);
    }
    let room = n - 3 - 1;
    let (p, q) = loop {
        let a = (next() % room as u64) as usize;
        let b = (next() % room as u64) as usize;
        if a + 3 <= b {
            break (a, b);
        }
    };
    classes[p] = digits[0];
    classes[p + 1] = digits[1];
    classes[q] = digits[2];
    classes[q + 1] = digits[3];
    classes.extend([14, digits[0], digits[1]]);
    classes
}

/// [measured] The closure locates a number told only by its order: the answer's sites have no word
/// that any site of the text shares, so the face's covector reaches the first number only through
/// a contact the founding did not make; the closure's comparison reaches it wherever it stands.
#[test]
#[ignore]
fn the_closure_locates_a_number_told_by_order() {
    let var = |k: &str, d: usize| std::env::var(k).ok().map(|v| v.parse().unwrap()).unwrap_or(d);
    let (n, sections) = (var("ORDER_SITES", 24), var("ORDER_SECTIONS", 300) as u64);
    let d = FieldDeclaration { alphabet: 15, width: 16, heads: 4, modes: 4, still: 2, contacts: 16, ticks: 2, frames: 4, reach: n, clocks: 0 };
    let mut learner = FieldLearner::new(Field::found(d, &keys(1 << 18)).unwrap(), 6);
    let open: Vec<bool> = (0..n).map(|t| t + 2 >= n).collect();
    let code = |field: &Field| -> i64 { (0..64u64).map(|i| field.code(&Region { classes: &order_problem(1_000_000 + i, n), unresolved: &open, faces: &[], locked: &[], clock: &[], echo: &[] }).unwrap().0).sum::<i64>() / 64 };
    let started = std::time::Instant::now();
    for s in 0..sections {
        let problems: Vec<Vec<usize>> = (0..16).map(|i| order_problem(s * 16 + i, n)).collect();
        let regions: Vec<Region> = problems.iter().map(|c| Region { classes: c, unresolved: &open, faces: &[], locked: &[], clock: &[], echo: &[] }).collect();
        learner.section(&regions).unwrap();
        if s % 50 == 49 {
            eprintln!("ORDER s={} held={} millibits ms={}", s + 1, code(&learner.field) * 1000 >> 20, started.elapsed().as_millis());
        }
    }
}

/// Three numbers of two digits, drawn with repetition, the first before the second and the second
/// before the third, in a filler text; the region ends with the marker `14` and the first number's
/// digits. A digit of the answer stands wherever it recurs, so its class has plural holders.
fn repeated_order_problem(seed: u64, n: usize) -> Vec<usize> {
    let mut next = mixer(seed);
    let mut classes: Vec<usize> = (0..n - 3).map(|_| (next() % 4) as usize).collect();
    let digits: Vec<usize> = (0..6).map(|_| 4 + (next() % 10) as usize).collect();
    let room = n - 3 - 1;
    let (p, q, r) = loop {
        let a = (next() % room as u64) as usize;
        let b = (next() % room as u64) as usize;
        let c = (next() % room as u64) as usize;
        if a + 3 <= b && b + 3 <= c {
            break (a, b, c);
        }
    };
    for (k, &at) in [p, q, r].iter().enumerate() {
        classes[at] = digits[2 * k];
        classes[at + 1] = digits[2 * k + 1];
    }
    classes.extend([14, digits[0], digits[1]]);
    classes
}

/// [measured] The closure locates a number among its repeated digits under the crib's completion
/// mask: with even odds a region's answer alone is open, or every site at a rate `τ` uniform on
/// `(0, 1]`, so most open sites' classes stand at many sites. The comparison is the code of the class
/// on the row's own copy face, so a row on any holder is settled and the rows of the many-held
/// classes stop pushing (24 sites, 1,200 sections: 0.54 bits against 0.70 when every holder is
/// asked for alike, 5.57 without the closure).
#[test]
#[ignore]
fn the_closure_locates_a_number_among_repeated_digits() {
    let var = |k: &str, d: usize| std::env::var(k).ok().map(|v| v.parse().unwrap()).unwrap_or(d);
    let (n, sections) = (var("ORDER_SITES", 24), var("ORDER_SECTIONS", 1200) as u64);
    let d = FieldDeclaration { alphabet: 15, width: 16, heads: 4, modes: 4, still: 2, contacts: 16, ticks: 2, frames: 4, reach: n, clocks: 0 };
    let mut learner = FieldLearner::new(Field::found(d, &keys(1 << 18)).unwrap(), 6);
    let answer: Vec<bool> = (0..n).map(|t| t + 2 >= n).collect();
    let code = |field: &Field| -> i64 { (0..64u64).map(|i| field.code(&Region { classes: &repeated_order_problem(1_000_000 + i, n), unresolved: &answer, faces: &[], locked: &[], clock: &[], echo: &[] }).unwrap().0).sum::<i64>() / 64 };
    let started = std::time::Instant::now();
    for s in 0..sections {
        let problems: Vec<Vec<usize>> = (0..16).map(|i| repeated_order_problem(s * 16 + i, n)).collect();
        let opens: Vec<Vec<bool>> = (0..16u64)
            .map(|i| {
                let mut next = mixer((s * 16 + i) ^ 0x5151);
                let head = next();
                if head & 1 == 0 {
                    return answer.clone();
                }
                let tau = (head >> 1) % 65536 + 1;
                let mut open: Vec<bool> = (0..n).map(|_| next() % 65536 < tau).collect();
                if !open.iter().any(|&u| u) {
                    open[n - 1] = true;
                }
                open
            })
            .collect();
        let regions: Vec<Region> = problems.iter().zip(&opens).map(|(c, o)| Region { classes: c, unresolved: o, faces: &[], locked: &[], clock: &[], echo: &[] }).collect();
        learner.section(&regions).unwrap();
        if s % 100 == 99 {
            eprintln!("REPEATED s={} held={} millibits ms={}", s + 1, code(&learner.field) * 1000 >> 20, started.elapsed().as_millis());
        }
    }
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
    let d = FieldDeclaration { alphabet: 5, width: 8, heads: 2, modes: 3, still: 1, contacts: 4, ticks: 2, frames: 2, reach: 32, clocks: 0 };
    let classes: Vec<usize> = (0..26).map(|t| [1usize, 3, 2, 4, 0, 2, 1][t % 7]).collect();
    let open: Vec<bool> = (0..26).map(|t| t % 9 == 4 || t == 25).collect();
    let r = Region { classes: &classes, unresolved: &open, faces: &[], locked: &[], clock: &[], echo: &[] };
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
        for g in [covector_of(&field, &r), reversed_of(&field, &r)] {
            let closure = g != covector_of(&field, &r);
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
                    let (mut plus, mut minus) = (field.clone(), field.clone());
                    plus.theta[i] += delta;
                    minus.theta[i] -= delta;
                    read += 1;
                    let code = |f: &Field| f.code(&r).unwrap().0 + if closure { closure_code(f, &r) } else { 0 };
                    let measured = code(&plus) - code(&minus);
                    let predicted = (g[i] * 2 * delta as i128) >> (natural + grain - 20);
                    let tolerance = predicted.abs() / 8 + (64 << h);
                    // Read again at half the step where the first read misses: the integer forward's
                    // releases can jump at one step that no seam marks (measured November 2: the
                    // listener's probe chart read 191 against 328 at `2^(grain − 9)`, and 631 against 656
                    // and 144 against 164 at the steps beside it).
                    let agrees = |m: i64, p: i128| (m as i128 - p).abs() <= p.abs() / 8 + (64 << h);
                    let half = || {
                        let (mut plus, mut minus) = (field.clone(), field.clone());
                        plus.theta[i] += delta / 2;
                        minus.theta[i] -= delta / 2;
                        2 * (code(&plus) - code(&minus))
                    };
                    let _ = tolerance;
                    assert!(agrees(measured, predicted) || agrees(half(), predicted), "still {still} closure {closure} family at {start} entry {i} at {h} halvings: measured {measured}, predicted {predicted}");
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
    // closure's 204 and the far support's 232 are every one read, after 26, 0 and 137 halvings in all,
    // none on a seam.
    eprintln!("FAR_PROBES read={read} halvings={halvings} on_a_seam={seams}");
    assert!(16 * seams <= read, "read {read} probes, {seams} on a seam at the smallest step");
}

/// [measurement, not a law] Where the cue fixture's held successor is read from after its 600
/// sections: for each held problem, head and tick, whether the receiver's support holds the
/// successor's earlier site (`k + 1`, past the near field and in the receiver's class) and its share
/// there, and whether the cue's site (11) holds the cue's earlier site `k`. Run with `--ignored
/// --nocapture`.
#[test]
#[ignore]
fn where_the_cue_is_read_from() {
    let d = FieldDeclaration { alphabet: 11, width: 16, heads: 2, modes: 4, still: 2, contacts: 16, ticks: 2, frames: 2, reach: 16, clocks: 0 };
    let mut learner = FieldLearner::new(Field::found(d, &keys(1 << 18)).unwrap(), 6);
    let open: Vec<bool> = (0..13).map(|t| t == 12).collect();
    let report = |field: &Field, label: &str| {
        let (mut rows, mut met, mut share, mut cue_met, mut near, mut code) = (0u64, 0u64, 0u128, 0u64, 0u64, 0i64);
        for i in 0..64u64 {
            let classes = cue_problem(1_000_000 + i);
            let k = (0..10).find(|&t| classes[t] == classes[11]).unwrap();
            let r = Region { classes: &classes, unresolved: &open, faces: &[], locked: &[], clock: &[], echo: &[] };
            let own = field.code(&r).unwrap().0;
            code += own;
            let pass = field.pass(&r, true).unwrap();
            let met_rows: usize = pass.ticks.iter().map(|c| (0..d.heads).filter(|&h| c.rows[h * 13 + 12].iter().any(|s| s.j as usize == k + 1)).count()).sum();
            let same_class: usize = pass.ticks.iter().map(|c| (0..d.heads).filter(|&h| c.classes[h].class[12] == c.classes[h].class[k + 1]).count()).sum();
            if label == "section_600" {
                eprintln!("CUE_PROBLEM i={i} k={k} near={} met_rows={met_rows} same_class={same_class} code_millibits={}", 12 - (k + 1) < NEAR, own * 1000 >> 20);
            }
            for cell in &pass.ticks {
                for h in 0..d.heads {
                    rows += 1;
                    let row = &cell.rows[h * 13 + 12];
                    near += u64::from(12 - (k + 1) < NEAR);
                    if let Some(src) = row.iter().find(|s| s.j as usize == k + 1) {
                        met += 1;
                        share += src.p as u128;
                    }
                    cue_met += u64::from(cell.rows[h * 13 + 11].iter().any(|s| s.j as usize == k));
                }
            }
        }
        eprintln!("CUE_WHERE {label} code_millibits={} rows={rows} successor_met={met} successor_near={near} successor_share_millionths={} cue_meets_its_earlier={cue_met}", (code / 64) * 1000 >> 20, (share * 1_000_000 >> SHARE_BITS) / rows.max(1) as u128);
    };
    report(&learner.field, "founding");
    for s in 0..600u64 {
        let problems: Vec<Vec<usize>> = (0..16).map(|i| cue_problem(s * 16 + i)).collect();
        let regions: Vec<Region> = problems.iter().map(|c| Region { classes: c, unresolved: &open, faces: &[], locked: &[], clock: &[], echo: &[] }).collect();
        learner.section(&regions).unwrap();
        if s == 99 || s == 299 {
            report(&learner.field, &format!("section_{}", s + 1));
        }
    }
    report(&learner.field, "section_600");
}

/// [measurement, not a law] The cue fixture over several founding key streams (each its own
/// founding, the same terrain and sections). Run with `--ignored --nocapture`.
#[test]
#[ignore]
fn the_cue_over_foundings() {
    let d = FieldDeclaration { alphabet: 11, width: 16, heads: 2, modes: 4, still: 2, contacts: 16, ticks: 2, frames: 2, reach: 16, clocks: 0 };
    let open: Vec<bool> = (0..13).map(|t| t == 12).collect();
    let codes: Vec<i64> = (0..6u64)
        .into_par_iter()
        .map(|seed| {
            let mut next = mixer(0xC0E + seed);
            let stream: Vec<u8> = (0..(1 << 17)).flat_map(|_| next().to_be_bytes()).collect();
            let mut learner = FieldLearner::new(Field::found(d, &stream).unwrap(), 6);
            for s in 0..600u64 {
                let problems: Vec<Vec<usize>> = (0..16).map(|i| cue_problem(s * 16 + i)).collect();
                let regions: Vec<Region> = problems.iter().map(|c| Region { classes: c, unresolved: &open, faces: &[], locked: &[], clock: &[], echo: &[] }).collect();
                learner.section(&regions).unwrap();
            }
            (0..64u64).map(|i| learner.field.code(&Region { classes: &cue_problem(1_000_000 + i), unresolved: &open, faces: &[], locked: &[], clock: &[], echo: &[] }).unwrap().0).sum::<i64>() / 64
        })
        .collect();
    eprintln!("CUE_FOUNDINGS millibits={:?}", codes.iter().map(|c| c * 1000 >> 20).collect::<Vec<_>>());
}


/// [definition; agent-inferred, November 2] **A listener's founding row keeps its near field** (§15.10):
/// on a crib-sized region (420 sites, no word recurring, the last 40 open), at the founding, an open
/// receiver's row puts more of its mass on its near field than on its loudest far source, on the mean
/// over its rows, at the listener's own temperature. [measurement] It holds at the class receiver's
/// temperature too (`−2`: the near field 0.836 of a row, the loudest far source 0.018, against 0.818 and
/// 0.005 at the listener's): on this fixture the founding does not drown the near field (the record's
/// §15.10).
#[test]
fn a_listener_s_founding_row_keeps_its_near_field() {
    let d = FieldDeclaration { alphabet: 44, width: 32, heads: 5, modes: 8, still: 2, contacts: 32, ticks: 2, frames: 5, reach: 484, clocks: 1 };
    assert_eq!((d.score_shift(), d.listen_shift()), (-2, 0));
    let sites = 420;
    let classes = drawn_classes(7, sites, d.alphabet);
    let open: Vec<bool> = (0..sites).map(|t| t >= sites - 40).collect();
    let r = Region { classes: &classes, unresolved: &open, faces: &[], locked: &[], clock: &[], echo: &[] };
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
    eprintln!("LISTENER_FOUNDING near={} far_peak={} (millionths of a row on the mean)", (near * 1_000_000 >> SHARE_BITS) / 400, (peak * 1_000_000 >> SHARE_BITS) / 400);
    assert!(near > peak, "the near field holds more of a listener's row than its loudest far source");
    let mut hot = field.clone();
    for h in 0..d.heads {
        hot.theta[hot.layout.temper + 2 * h + 1] = hot.theta[hot.layout.temper + 2 * h];
    }
    let (near, peak) = read(&hot);
    eprintln!("LISTENER_AT_CLASS_GAIN near={} far_peak={}", (near * 1_000_000 >> SHARE_BITS) / 400, (peak * 1_000_000 >> SHARE_BITS) / 400);
    assert!(near > peak, "and at the class receiver's");
}
