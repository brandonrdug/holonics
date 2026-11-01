use super::*;

fn keys(n: usize) -> Vec<u8> {
    // A fixed exterior key stream for the fixtures: the bytes of a counter's squares.
    (0..n as u64).flat_map(|i| (i.wrapping_mul(2654435761) ^ (i * i)).to_be_bytes()[4..].to_vec()).collect()
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

fn covector_of(field: &Field, region: &Region) -> Vec<i128> {
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
    for (still, framed) in [(3usize, false), (1, true)] {
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
    for still in [0usize, 1, 3] {
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
                // A chart row is (real or imaginary part, mode c); mode c's local slot is c mod n.
                let turned = |i: usize| ((i - start) / dw) % m % n >= field.declaration.still;
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
    let field = silent_contacts(shaped(3));
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
    let field = shaped(3);
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
    let a = covector_of(&field, &regions[0]);
    let b = covector_of(&field, &regions[1]);
    let summed: Vec<i128> = a.iter().zip(&b).map(|(x, y)| x + y).collect();
    assert_eq!(g, summed);
    let (_, reversed) = field.read_and_return(&[regions[1], regions[0]]).unwrap();
    assert_eq!(reversed, g);
}

/// The release the law makes of one problem, sweep by sweep (the doc of [`Field::release`]): the
/// sites the field resolves, or the one with the most news, until the void or the last sweep; the
/// void only at the answer's first open site.
fn law_release(field: &Field, question: &[usize], answer: usize, sweeps: usize, void: usize) -> Vec<usize> {
    let start = question.len();
    let mut classes: Vec<usize> = question.iter().copied().chain(std::iter::repeat_n(void, answer)).collect();
    let mut open: Vec<bool> = (0..classes.len()).map(|t| t >= start).collect();
    for sweep in 0..sweeps {
        if !open.iter().any(|&u| u) {
            break;
        }
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
    let end = (start..classes.len()).find(|&t| open[t]).unwrap_or(classes.len());
    classes[start..end].to_vec()
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

/// The grown field reads the old faces exactly, on the framed and the still field, by two and
/// by three; the draws counted are the draws read; and one learned section parts the copies.
#[test]
fn the_grown_field_reads_the_old_faces() {
    for still in [0usize, 1, 3] {
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
    let mut read = |regions: &[Region]| -> Result<Vec<Vec<Option<TowerFace>>>> {
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
    assert_eq!((last.live, last.resolved, last.by_news, last.cut, last.cut_sites), (0, 2, 4, 1, 5), "the extent at the opening, four content sites by news, then the void at the first open site");
    assert_eq!(lengths[0], start + answer, "the opening reads the whole extent");
    assert!(lengths[1..].iter().all(|&n| n == start + 6), "every later read is of the bounded region: {lengths:?}");
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
                assert!(after.resolved + after.by_news >= before.resolved + before.by_news + before.live, "a sweep releases a site of every open problem");
            }
        }
    }
    let mut last = ReleaseSweep::default();
    field.release_realized(&problems, 7, 0, &mut HostField, &mut |s| {
        last = *s;
        true
    }).unwrap();
    assert_eq!(last.live, 0, "sweeps at the open sites end every problem");
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

