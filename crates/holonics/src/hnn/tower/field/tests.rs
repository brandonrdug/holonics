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
    Region { classes: &CLASSES, unresolved: &OPEN }
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
    assert!(field.faces(&Region { classes: &classes, unresolved: &open }).is_err());
    assert!(field.faces(&Region { classes: &classes[..16], unresolved: &open[..16] }).is_ok());
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
        for start in [l.q, l.k] {
            field.theta[start..start + m2 * dw].iter_mut().for_each(|v| *v = 0);
        }
        for start in [l.q_bias, l.k_bias] {
            field.theta[start..start + m2].iter_mut().for_each(|v| *v = 0);
        }
        let classes = [2usize; 6];
        let open = [true; 6];
        let faces = field.faces(&Region { classes: &classes, unresolved: &open }).unwrap();
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
/// covector's prediction, `g · 2δ · 2^(20 − natural − grain)` on `2^(−20)` bits.
#[test]
fn covector_matches_the_codes_difference() {
    for still in [0usize, 1, 2] {
        let field = shaped(still);
        let r = region();
        let g = covector_of(&field, &r);
        let (m, n, dw) = (field.declaration.complex(), field.declaration.modes, field.declaration.width);
        let l = field.layout.clone();
        for &(start, len, grain) in field.families() {
            let natural: u32 = if grain == MATERIAL_BITS { 40 } else { 24 };
            let mut entries: Vec<usize> = (start..start + len).collect();
            entries.sort_by_key(|&i| std::cmp::Reverse(g[i].unsigned_abs()));
            let mut probed: Vec<usize> = entries.iter().copied().take(3).collect();
            if [l.q, l.k, l.v].contains(&start) {
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
            let delta = 1i32 << (grain - 9);
            let mut plus = field.clone();
            plus.theta[i] += delta;
            let mut minus = field.clone();
            minus.theta[i] -= delta;
            let measured = plus.code(&r).unwrap().0 - minus.code(&r).unwrap().0;
            let shift = natural + grain - 20;
            let predicted = (g[i] * 2 * delta as i128) >> shift;
            let tolerance = predicted.abs() / 8 + 64;
            assert!((measured as i128 - predicted).abs() <= tolerance, "still {still} family at {start} (grain {grain}) entry {i}: measured {measured}, predicted {predicted}");
            }
        }
    }
}

/// Without frames (every mode still) and with the strand contacts silent, a site's face depends on
/// the region's classes, not their order: permuting the sites permutes the faces exactly, bit for
/// bit.
#[test]
fn still_field_is_order_free() {
    let field = silent_contacts(shaped(2));
    let faces = field.faces(&region()).unwrap();
    let order = [3usize, 0, 6, 1, 5, 2, 4];
    let classes: Vec<usize> = order.iter().map(|&t| CLASSES[t]).collect();
    let open: Vec<bool> = order.iter().map(|&t| OPEN[t]).collect();
    let permuted = field.faces(&Region { classes: &classes, unresolved: &open }).unwrap();
    for (n, &t) in order.iter().enumerate() {
        assert_eq!(permuted[n], faces[t]);
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
    let permuted = field.faces(&Region { classes: &classes, unresolved: &open }).unwrap();
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
    let permuted = field.faces(&Region { classes: &classes, unresolved: &open }).unwrap();
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
    let regions = [region(), Region { classes: &second_classes, unresolved: &second_open }];
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
    let regions = [region(), Region { classes: &second_classes, unresolved: &second_open }];
    let (_, g) = field.read_and_return(&regions).unwrap();
    let a = reversed_of(&field, &regions[0]);
    let b = reversed_of(&field, &regions[1]);
    let summed: Vec<i128> = a.iter().zip(&b).map(|(x, y)| x + y).collect();
    assert_eq!(g, summed);
    let (_, reversed) = field.read_and_return(&[regions[1], regions[0]]).unwrap();
    assert_eq!(reversed, g);
}

/// The release the law makes of one problem, sweep by sweep (the doc of [`Field::release`]): the
/// sites the field resolves, or the one with the most news, until the void or the last sweep; the
/// void only at the answer's first open site; and after each sweep's releases, the refinement of one
/// part of the released answer sites (every [`REFINE_PARTS`]-th), read with that part open and
/// revised where the field now resolves another class; once every answer site is released, in
/// rounds of every part's reread, until a round revises nothing or no fewer sites than the one before.
fn law_release(field: &Field, question: &[usize], answer: usize, sweeps: usize, void: usize) -> Vec<usize> {
    law_release_counted(field, question, answer, sweeps, void).0
}

/// [`law_release`] with the number of revisions it made.
fn law_release_counted(field: &Field, question: &[usize], answer: usize, sweeps: usize, void: usize) -> (Vec<usize>, usize) {
    let start = question.len();
    let mut classes: Vec<usize> = question.iter().copied().chain(std::iter::repeat_n(void, answer)).collect();
    let mut open: Vec<bool> = (0..classes.len()).map(|t| t >= start).collect();
    // The closed answer's round: its sweeps, its revisions and the round before's.
    let (mut round, mut round_revised, mut before, mut ended) = (0usize, 0usize, None::<usize>, false);
    let mut revisions = 0usize;
    for sweep in 0..sweeps {
        if !open.iter().any(|&u| u) && ended {
            break;
        }
        if open.iter().any(|&u| u) {
            let first = (start..open.len()).find(|&t| open[t]).unwrap();
            let faces = field.faces(&Region { classes: &classes, unresolved: &open }).unwrap();
            // At the opening, the earliest site whose void resolves bounds the answer.
            let extent = if sweep == 0 {
                faces.iter().enumerate().find(|(_, face)| face.as_ref().is_some_and(|f| f.rank_top() == void && 2 * f.masses[void] > f.total)).map(|(t, _)| t)
            } else {
                None
            };
            let mut released: Vec<(usize, usize)> = Vec::new();
            for (t, face) in faces.iter().enumerate() {
                if let Some(face) = face {
                    let top = face.rank_top();
                    if 2 * face.masses[top] > face.total && (top != void || t == first || Some(t) == extent) && extent.is_none_or(|e| t <= e) {
                        released.push((t, top));
                    }
                }
            }
            if released.is_empty() {
                let prior_open: Vec<bool> = open.iter().enumerate().map(|(t, &u)| u || t < start).collect();
                let prior = field.faces(&Region { classes: &classes, unresolved: &prior_open }).unwrap();
                released.push(by_news(&faces, &prior).unwrap().into_iter().find(|&(t, c)| c != void || t == first || Some(t) == extent).unwrap());
            }
            for (t, c) in released {
                classes[t] = c;
                open[t] = false;
            }
            if let Some(end) = (start..classes.len()).find(|&t| !open[t] && classes[t] == void) {
                classes.truncate(end + 1);
                open.truncate(end + 1);
            }
        }
        // The refinement of this sweep's part.
        let part = sweep % REFINE_PARTS;
        let reread: Vec<bool> = (0..classes.len()).map(|t| open[t] || (t >= start && (t - start) % REFINE_PARTS == part && classes[t] != void)).collect();
        let mut revised = 0usize;
        if reread.iter().zip(&open).any(|(&r, &u)| r && !u) {
            let faces = field.faces(&Region { classes: &classes, unresolved: &reread }).unwrap();
            for t in 0..classes.len() {
                if !reread[t] || open[t] {
                    continue;
                }
                let face = faces[t].as_ref().unwrap();
                let top = face.rank_top();
                if 2 * face.masses[top] > face.total && top != void && top != classes[t] {
                    classes[t] = top;
                    revised += 1;
                }
            }
        }
        revisions += revised;
        if open.iter().any(|&u| u) {
            (round, round_revised, before) = (0, 0, None);
        } else {
            round += 1;
            round_revised += revised;
            if round == REFINE_PARTS {
                if round_revised == 0 || before.is_some_and(|b| round_revised >= b) {
                    ended = true;
                } else {
                    (round, round_revised, before) = (0, 0, Some(round_revised));
                }
            }
        }
    }
    let end = (start..classes.len()).find(|&t| open[t]).unwrap_or(classes.len());
    (classes[start..end].to_vec(), revisions)
}

/// The release commits only the sites the field resolves (or, resolving none, the one the question
/// tells most about), so a sweep never commits a site against the field's own read; it is the law's
/// sweep by sweep, ends at its first void, and stops at its first site still unresolved.
#[test]
fn the_release_commits_only_what_the_field_resolves() {
    let question = [1usize, 4, 0, 2];
    for still in [0usize, 1] {
        let field = shaped(still);
        for sweeps in [1usize, 2, 3, 6] {
            let once = field.release(&question, 5, sweeps, 0).unwrap();
            assert_eq!(once, law_release(&field, &question, 5, sweeps, 0), "still {still} sweeps {sweeps}");
            assert_eq!(field.release(&question, 5, sweeps, 0).unwrap(), once);
            assert!(once.len() <= 5);
            // The answer ends at its first void: none before its last site.
            assert!(once.iter().rev().skip(1).all(|&c| c != 0));
        }
        // One sweep from the opening releases at least one site, and only sites the opening
        // read resolves or the single site of the most news.
        let classes: Vec<usize> = question.iter().copied().chain(std::iter::repeat_n(0, 5)).collect();
        let open: Vec<bool> = std::iter::repeat_n(false, 4).chain(std::iter::repeat_n(true, 5)).collect();
        let faces = field.faces(&Region { classes: &classes, unresolved: &open }).unwrap();
        let resolved_sites: Vec<usize> = (4..9).filter(|&t| faces[t].as_ref().is_some_and(|f| 2 * f.masses[f.rank_top()] > f.total)).collect();
        let one = law_release(&field, &question, 5, 1, 0);
        if resolved_sites.is_empty() {
            assert!(one.len() <= 1, "resolving none, one sweep releases one site");
        } else {
            assert!(one.len() <= resolved_sites.len() + 1);
        }
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

/// A released answer refines while it settles: a round ends the refinement when it revises nothing
/// or no fewer sites than the round before, so any sequence of rounds ends within one round more
/// than the first round's revisions, a cycle of revisions at its second round.
#[test]
fn the_refinement_ends_where_it_stops_settling() {
    assert!(refinement_ends(0, None));
    assert!(!refinement_ends(3, None));
    assert!(!refinement_ends(2, Some(3)));
    assert!(refinement_ends(3, Some(3)), "a round that revises as many as the last is a cycle");
    assert!(refinement_ends(4, Some(3)));
    for rounds in [vec![2usize, 2, 2, 2, 2], vec![5, 4, 3, 2, 1, 0, 7], vec![1, 0], vec![3, 1, 2, 0], vec![9; 20]] {
        let mut before = None;
        let mut ran = 0usize;
        for &revised in &rounds {
            ran += 1;
            if refinement_ends(revised, before) {
                break;
            }
            before = Some(revised);
        }
        assert!(ran <= rounds[0] + 1, "{rounds:?} ran {ran}");
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

/// The release's order is the news the question gives a site's top class, not the top class's
/// share: a site the place alone predicts as surely is released last, however sure it is.
#[test]
fn the_release_orders_by_the_question_s_news() {
    let faces = [None, face(&[1, 9]), face(&[6, 4]), face(&[1, 3]), face(&[5, 5])];
    let prior = [face(&[1, 1]), face(&[1, 9]), face(&[1, 1]), face(&[1, 1]), face(&[1, 1])];
    // Site 1 is the surest (0.9) but the place alone predicts it as surely: no news. Site 2 carries
    // 0.6 of log₂(0.6/0.5), site 3 0.75 of log₂(0.75/0.5), site 4 none (a tie takes class 0).
    let order = by_news(&faces, &prior).unwrap();
    assert_eq!(order, vec![(3, 1), (2, 0), (1, 1), (4, 0)]);
    // A site the question makes less sure of its top class than the place does comes last.
    let doubted = [face(&[7, 3]), face(&[2, 1])];
    assert_eq!(by_news(&doubted, &[face(&[9, 1]), face(&[1, 1])]).unwrap(), vec![(1, 0), (0, 0)]);
    assert!(by_news(&faces, &[None, None, None, None, None]).is_err(), "an open site needs its prior face");
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

/// The void is the answer's boundary, one nested variable. A read whose void resolves at every
/// site past the fifth, and at a site next to a released void (the hazard of an extent: given
/// `L ≤ t`, `L < t` is likely), while no content site resolves, would, released as an ordinary
/// class, creep from the fifth site to the first and release nothing. Read once at the opening,
/// the extent is the fifth site: the region is cut there, every later read is of the bounded
/// region, the void creeps only where it is the first open site, and the release is four content
/// sites, then its void.
#[test]
fn the_void_follows_the_released_content() {
    let field = shaped(1);
    let (void, start, answer) = (0usize, 2usize, 9usize);
    let question = [3usize, 1];
    let face = |masses: [u128; 5]| Some(TowerFace { total: masses.iter().sum(), masses: masses.to_vec() });
    let read = |regions: &[Region]| -> Result<Vec<Vec<Option<TowerFace>>>> {
        Ok(regions
            .iter()
            .map(|r| {
                (0..r.classes.len())
                    .map(|t| {
                        if !r.unresolved[t] {
                            return None;
                        }
                        let next_void = t + 1 < r.classes.len() && !r.unresolved[t + 1] && r.classes[t + 1] == void;
                        if t >= start + 5 || next_void {
                            face([8, 1, 1, 1, 1])
                        } else {
                            face([3, 1, 4, 1, 1])
                        }
                    })
                    .collect()
            })
            .collect())
    };
    let mut asked = Vec::new();
    let mut lengths = Vec::new();
    let mut counted = |regions: &[Region]| {
        lengths.extend(regions.iter().map(|r| r.classes.len()));
        read(regions)
    };
    let released = field.release_with(&[(&question, answer)], answer + 1, void, &mut counted, &mut |s| {
        asked.push(*s);
        true
    }).unwrap();
    assert_eq!(released, vec![vec![2, 2, 2, 2, void]]);
    let last = asked.last().unwrap();
    assert_eq!((last.live, last.open, last.resolved, last.by_news, last.cut, last.cut_sites, last.revised), (0, 0, 2, 4, 1, 5, 0), "the extent at the opening, four content sites by news, then the void at the first open site; no content face resolves, so none is revised");
    assert_eq!(lengths[0], start + answer, "the opening reads the whole extent");
    // Every later read is of the bounded region, and once the void ends the answer at its fifth
    // site, the refinement's rereads are of the answer through its void.
    let ended = lengths.iter().position(|&n| n == start + 5).unwrap();
    assert!(lengths[1..ended].iter().all(|&n| n == start + 6) && lengths[ended..].iter().all(|&n| n == start + 5), "{lengths:?}");
}

/// The exterior that stops a release after `k` sweeps receives the release of `k` sweeps; it is
/// asked before every sweep and once after the last, every sweep releases a site of every open
/// problem, and a release given its open sites as sweeps ends every problem.
#[test]
fn a_release_stopped_by_its_exterior_is_the_release_of_the_sweeps_it_ran() {
    let field = shaped(1);
    let questions: [&[usize]; 3] = [&[1, 4, 0, 2], &[3, 3], &[2, 1, 1, 4, 0]];
    let problems: Vec<(&[usize], usize)> = questions.iter().zip([5usize, 7, 3]).map(|(q, a)| (*q, a)).collect();
    for k in 1..=3 {
        let mut asked = Vec::new();
        let stopped = field.release_realized(&problems, 7, 0, &mut HostField, &mut |s| {
            asked.push(*s);
            s.done < k
        }).unwrap();
        let ran = asked.last().unwrap().done;
        assert!(ran <= k);
        for (&(q, a), released) in problems.iter().zip(&stopped) {
            assert_eq!(&field.release(q, a, ran, 0).unwrap(), released, "stopped after {ran} sweeps");
        }
        for pair in asked.windows(2) {
            let (before, after) = (pair[0], pair[1]);
            if after.done > before.done {
                assert!(after.resolved + after.by_news >= before.resolved + before.by_news + before.open, "a sweep releases a site of every open problem");
            }
        }
    }
    let mut last = ReleaseSweep::default();
    field.release_realized(&problems, 7, 0, &mut HostField, &mut |s| {
        last = *s;
        true
    }).unwrap();
    assert_eq!(last.open, 0, "sweeps at the open sites release every problem");
    let mut last = ReleaseSweep::default();
    field.release_realized(&problems, 64, 0, &mut HostField, &mut |s| {
        last = *s;
        true
    }).unwrap();
    assert_eq!(last.live, 0, "and the parts' rereads past them end every refinement: {last:?}");
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
    let second = Region { classes: &second_classes, unresolved: &second_open };
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
#[test]
fn the_strand_contacts_let_a_value_be_recalled_by_its_key() {
    let d = FieldDeclaration { alphabet: 16, width: 16, heads: 2, modes: 4, still: 2, contacts: 16, ticks: 2, frames: 2, reach: 16 };
    let mut learner = FieldLearner::new(Field::found(d, &keys(1 << 18)).unwrap(), 6);
    let open: Vec<bool> = (0..10).map(|t| t == 9).collect();
    let code = |learner: &FieldLearner| -> i64 {
        (0..64u64).map(|i| learner.field.code(&Region { classes: &recall_problem(1_000_000 + i), unresolved: &open }).unwrap().0).sum::<i64>() / 64
    };
    for s in 0..1000u64 {
        let problems: Vec<Vec<usize>> = (0..16).map(|i| recall_problem(s * 16 + i)).collect();
        let regions: Vec<Region> = problems.iter().map(|c| Region { classes: c, unresolved: &open }).collect();
        learner.section(&regions).unwrap();
    }
    let held = code(&learner);
    assert!(held < 1 << 18, "the held recall codes {} millibits", held * 1000 >> 20);
}


/// The founding is the pair's likeness: the key chart is the probe chart, every class has a word
/// in the encoding and both strand contacts, and the unresolved rows carry none.
#[test]
fn the_founding_is_the_pair_s_likeness() {
    let field = Field::found(tiny_declaration(1), &keys(1 << 14)).unwrap();
    let (dw, a, m2) = (field.declaration.width, field.declaration.alphabet, 2 * field.declaration.complex());
    let l = field.layout.clone();
    assert_eq!(field.theta[l.k..l.k + m2 * dw], field.theta[l.q..l.q + m2 * dw]);
    assert!(field.theta[l.q..l.q + m2 * dw].iter().any(|&v| v != 0));
    for start in [l.enc, l.before, l.after] {
        for row in 0..a {
            assert!(field.theta[start + row * dw..start + (row + 1) * dw].iter().any(|&v| v != 0), "class {row} has a word");
        }
        assert!(field.theta[start + a * dw..start + (a + 1) * dw].iter().all(|&v| v == 0), "the unresolved row is silent");
    }
}

/// No site meets itself: at every tick and head its own weight is zero, and the peak of its row is
/// read over the others (some other site carries the whole of the peak, `2^40` on `2^(−40)`).
#[test]
fn no_site_meets_itself() {
    for still in [0usize, 1, 2] {
        let field = shaped(still);
        let pass = field.pass(&region(), true).unwrap();
        let (sites, heads) = (CLASSES.len(), field.declaration.heads);
        for cell in &pass.ticks {
            for h in 0..heads {
                for i in 0..sites {
                    let row = &cell.e[(h * sites + i) * sites..(h * sites + i + 1) * sites];
                    assert_eq!(row[i], 0, "still {still} head {h} site {i}");
                    assert_eq!(*row.iter().max().unwrap(), 1u64 << WEIGHT_BITS, "the peak is another site's, at the weights' whole grain");
                }
            }
        }
    }
    let one = [1usize];
    assert!(shaped(1).faces(&Region { classes: &one, unresolved: &[true] }).is_err(), "a lone site has no site to meet");
}

/// The contact's gain is the reach's: the largest shift at which two equal words' `2n` reals of
/// unit power still read the region's `⌈log₂ reach⌉` bits.
#[test]
fn the_contact_s_gain_is_the_reach_s() {
    let at = |modes: usize, reach: usize| FieldDeclaration { alphabet: 5, width: 8, heads: 2, modes, still: 1, contacts: 4, ticks: 2, frames: 2, reach }.score_shift();
    assert_eq!(at(8, 2221), 0);
    assert_eq!(at(16, 16), 3);
    assert_eq!(at(3, 16), 0);
    assert_eq!(at(8, 2), 4);
    for (modes, reach) in [(8usize, 2221usize), (16, 16), (3, 16), (8, 2), (16, 1 << 20)] {
        let (beta, bits) = (at(modes, reach), (usize::BITS - (reach - 1).leading_zeros()).max(1) as usize);
        assert!((2 * modes) >> beta >= bits || beta == 0, "modes {modes} reach {reach}");
        assert!((2 * modes) >> (beta + 1) < bits, "the largest such shift: modes {modes} reach {reach}");
    }
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

/// The share of row `i`'s weight at site `j` in still head `h` of a pass's first tick, on `2^(−20)`.
fn share(pass: &FieldPass, sites: usize, h: usize, i: usize, j: usize) -> u64 {
    let row = &pass.ticks[0].e[(h * sites + i) * sites..(h * sites + i + 1) * sites];
    ((row[j] as u128) << 20).div_euclid(row.iter().map(|&e| e as u128).sum::<u128>().max(1)) as u64
}

/// The founded contact meets the site whose word is its own: in a still set, a site's row peaks at
/// the one other site whose word (its class and both neighbours') is the same, in every region and
/// head, at the founding, before any learning (a word at unit power meets its equal at `2n`, the
/// most any pair reaches).
#[test]
fn the_founded_contact_meets_the_site_whose_word_is_its_own() {
    let d = FieldDeclaration { alphabet: 16, width: 32, heads: 2, modes: 8, still: 2, contacts: 8, ticks: 1, frames: 2, reach: 64 };
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
        let pass = field.pass(&Region { classes: &classes, unresolved: &open }, true).unwrap();
        for h in 0..d.heads {
            let row = &pass.ticks[0].e[(h * sites + i) * sites..(h * sites + i + 1) * sites];
            let peak = (0..sites).max_by_key(|&t| row[t]).unwrap();
            met += usize::from(peak == j);
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
    let d = FieldDeclaration { alphabet: 122, width: 32, heads: 4, modes: 8, still: 2, contacts: 32, ticks: 1, frames: 4, reach: 2221 };
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
            let pass = field.pass(&Region { classes: &classes, unresolved: &open }, true).unwrap();
            for h in 0..d.still {
                shares.push(share(&pass, sites, h, i, j));
                let row = &pass.ticks[0].e[(h * sites + i) * sites..(h * sites + i + 1) * sites];
                peaks += usize::from((0..sites).max_by_key(|&t| row[t]).unwrap() == j);
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
/// stayed at 3.3 bits after 2,000 sections.
#[test]
fn the_contact_finds_a_cue_s_successor() {
    let d = FieldDeclaration { alphabet: 11, width: 16, heads: 2, modes: 4, still: 2, contacts: 16, ticks: 2, frames: 2, reach: 16 };
    let mut learner = FieldLearner::new(Field::found(d, &keys(1 << 18)).unwrap(), 6);
    let open: Vec<bool> = (0..13).map(|t| t == 12).collect();
    let code = |learner: &FieldLearner| -> i64 {
        (0..64u64).map(|i| learner.field.code(&Region { classes: &cue_problem(1_000_000 + i), unresolved: &open }).unwrap().0).sum::<i64>() / 64
    };
    for s in 0..600u64 {
        let problems: Vec<Vec<usize>> = (0..16).map(|i| cue_problem(s * 16 + i)).collect();
        let regions: Vec<Region> = problems.iter().map(|c| Region { classes: c, unresolved: &open }).collect();
        learner.section(&regions).unwrap();
    }
    let held = code(&learner);
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
    let unheld = Region { classes: &unheld_classes, unresolved: &unheld_open };
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
    let d = FieldDeclaration { alphabet: 15, width: 16, heads: 4, modes: 4, still: 2, contacts: 16, ticks: 2, frames: 4, reach: n };
    let mut learner = FieldLearner::new(Field::found(d, &keys(1 << 18)).unwrap(), 6);
    let open: Vec<bool> = (0..n).map(|t| t + 2 >= n).collect();
    let code = |field: &Field| -> i64 { (0..64u64).map(|i| field.code(&Region { classes: &order_problem(1_000_000 + i, n), unresolved: &open }).unwrap().0).sum::<i64>() / 64 };
    let started = std::time::Instant::now();
    for s in 0..sections {
        let problems: Vec<Vec<usize>> = (0..16).map(|i| order_problem(s * 16 + i, n)).collect();
        let regions: Vec<Region> = problems.iter().map(|c| Region { classes: c, unresolved: &open }).collect();
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
    let d = FieldDeclaration { alphabet: 15, width: 16, heads: 4, modes: 4, still: 2, contacts: 16, ticks: 2, frames: 4, reach: n };
    let mut learner = FieldLearner::new(Field::found(d, &keys(1 << 18)).unwrap(), 6);
    let answer: Vec<bool> = (0..n).map(|t| t + 2 >= n).collect();
    let code = |field: &Field| -> i64 { (0..64u64).map(|i| field.code(&Region { classes: &repeated_order_problem(1_000_000 + i, n), unresolved: &answer }).unwrap().0).sum::<i64>() / 64 };
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
        let regions: Vec<Region> = problems.iter().zip(&opens).map(|(c, o)| Region { classes: c, unresolved: o }).collect();
        learner.section(&regions).unwrap();
        if s % 100 == 99 {
            eprintln!("REPEATED s={} held={} millibits ms={}", s + 1, code(&learner.field) * 1000 >> 20, started.elapsed().as_millis());
        }
    }
}
