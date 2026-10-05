//! The located transport's laws (module header of `compression::keys::transport`).

use super::*;
use crate::geometry::winding::Odometer;
use crate::hnn::encoding::{Encoding, PassageChart};

fn helix(periods: &[u64]) -> CarryHelix {
    CarryHelix::new(periods.to_vec()).unwrap()
}

/// Every permutation of `ℤ/m`, in lexicographic order.
fn permutations(m: usize) -> Vec<Vec<usize>> {
    (0..factorial(m))
        .map(|rank| label_unrank(rank, m).into_iter().map(Option::unwrap).collect())
        .collect()
}

/// A terrain's read set: `count` passages of `length` cells from drawn keys.
fn read_set(terrain: &SteppedTerrain, draw: &mut Draw, count: usize, length: usize) -> Vec<Vec<usize>> {
    let period = terrain.helix().period() as usize;
    (0..count)
        .map(|_| terrain.passage(draw.below(period) as u64, length))
        .collect()
}

fn locate(helix: &CarryHelix, classes: usize, passages: &[Vec<usize>]) -> TransportLocation {
    TransportLocation::locate(helix.clone(), classes, passages).unwrap()
}

/// The residue chart's transport, `A_res(u) = Σ_g [u mod d_g ∈ {0}] ∏_(h<g) d_h`: the field's
/// single notch, chosen by the class's code (the refused chart, read here only as the comparison).
fn residue_advances(helix: &CarryHelix, classes: usize) -> Vec<u64> {
    (0..classes)
        .map(|u| {
            let mut weight = 1;
            helix
                .periods()
                .iter()
                .map(|&d| {
                    let term = if (u as u64) % d == 0 { weight } else { 0 };
                    weight *= d;
                    term
                })
                .sum()
        })
        .collect()
}

/// The residue chart's least residual over the declared label bijections and each passage's every
/// key.
fn residue_code_length(
    helix: &CarryHelix,
    classes: usize,
    passages: &[Vec<usize>],
    labellings: &[Vec<usize>],
) -> usize {
    let advances = residue_advances(helix, classes);
    labellings
        .iter()
        .cloned()
        .map(|labels| {
            let labels: Vec<Option<usize>> = labels.into_iter().map(Some).collect();
            let keys: Vec<u64> = passages
                .iter()
                .map(|passage| {
                    (0..helix.period())
                        .min_by_key(|&key| driven_patches(helix, &advances, &labels, passage, key).len())
                        .unwrap()
                })
                .collect();
            residual_code(helix, &advances, &labels, &keys, passages).unwrap().len()
        })
        .min()
        .unwrap()
}

/// [proved-derived; implemented-exact] **The odometer and CRT charts are one lift**: on the helix
/// `(3, 4, 5)`, for every lift and every advance, the odometer's step with carries gives the digits
/// of the sum, its last carry the joint clock's turn, and it agrees with `geometry::winding::Odometer`;
/// the CRT residues add with no carry; the receiving cell is the last digit.
#[test]
fn the_odometer_and_crt_charts_are_one_lift() {
    let helix = helix(&[3, 4, 5]);
    assert_eq!((helix.period(), helix.grain(), helix.cells()), (60, 12, 5));
    let radices: Vec<BigUint> = helix.periods().iter().map(|&d| BigUint::from(d)).collect();
    for lift in 0..60 {
        let digits = helix.digits(lift);
        assert_eq!(helix.of_digits(&digits), lift);
        assert_eq!(helix.cell(lift), digits[2]);
        for advance in 0..60 {
            let (stepped, carries) = helix.step_digits(&digits, &helix.digits(advance));
            assert_eq!(stepped, helix.digits((lift + advance) % 60));
            assert_eq!(carries[2], u64::from(lift + advance >= 60));
            let mut odometer = Odometer::from_value(radices.clone(), &BigUint::from(lift)).unwrap();
            odometer.advance(&BigUint::from(advance));
            let read: Vec<u64> = odometer
                .digits()
                .iter()
                .map(|digit| u64::try_from(digit).unwrap())
                .collect();
            assert_eq!(read, stepped);
            let residues: Vec<u64> = helix
                .residues(lift)
                .iter()
                .zip(helix.residues(advance))
                .zip(helix.periods())
                .map(|((r, a), d)| (r + a) % d)
                .collect();
            assert_eq!(residues, helix.residues((lift + advance) % 60));
        }
    }
    assert!(CarryHelix::new(vec![4, 6]).is_err());
    assert!(CarryHelix::new(vec![5]).is_err());
}

/// [proved-derived; implemented-exact] **The reflection is a gauge**: for drawn terrains on two
/// helices, the reflected transport regenerates every passage from the reflected key, and the
/// reflected key reads the receiving digit `−c`.
#[test]
fn the_reflection_is_a_gauge() {
    let mut draw = Draw::new(2_026_100_931);
    for periods in [[2u64, 3, 5], [3, 4, 5]] {
        let helix = helix(&periods);
        for _ in 0..8 {
            let terrain = SteppedTerrain::draw(helix.clone(), &mut draw);
            let truth = LocatedTransport::of_terrain(&terrain);
            let reflected = truth.reflected();
            assert_eq!(reflected.reflected(), truth);
            for key in 0..helix.period() {
                let image = truth.reflect_key(key);
                assert_eq!(
                    helix.cell(image),
                    (helix.cells() - helix.cell(key)) % helix.cells()
                );
                assert_eq!(
                    reflected.regenerate(image, 40),
                    Some(terrain.passage(key, 40)),
                    "periods {periods:?}, key {key}"
                );
            }
        }
    }
}

/// The brute-force fibre of a read set on a small helix: every transport, every label bijection
/// and each passage's every key (the first passage's key in cell 0, the rotation gauge), projected
/// to what the location reads (advances of stepped classes, labels of emitted classes) with the
/// last passage's admitted current lifts.
#[allow(clippy::type_complexity)]
fn brute_fibre(
    helix: &CarryHelix,
    classes: usize,
    passages: &[Vec<usize>],
) -> Vec<(Vec<Option<u64>>, Vec<Option<usize>>, Vec<u64>)> {
    let period = helix.period();
    let stepped: Vec<bool> = (0..classes)
        .map(|u| passages.iter().any(|p| p[..p.len() - 1].contains(&u)))
        .collect();
    let emitted: Vec<bool> = (0..classes)
        .map(|u| passages.iter().any(|p| p.contains(&u)))
        .collect();
    let mut fibre = Vec::new();
    let tables = (period as usize).pow(classes as u32);
    for table in 0..tables {
        let mut rest = table;
        let advances: Vec<u64> = (0..classes)
            .map(|_| {
                let a = (rest % period as usize) as u64;
                rest /= period as usize;
                a
            })
            .collect();
        for labels in permutations(classes) {
            let located = LocatedTransport::new(
                helix.clone(),
                advances.clone(),
                labels.iter().map(|&c| Some(c)).collect(),
            )
            .unwrap();
            let mut fits = true;
            let mut last = Vec::new();
            for (index, passage) in passages.iter().enumerate() {
                let keys: Vec<u64> = located
                    .keys(passage)
                    .into_iter()
                    .filter(|&key| index > 0 || helix.cell(key) == 0)
                    .collect();
                if keys.is_empty() {
                    fits = false;
                    break;
                }
                last = keys
                    .iter()
                    .map(|&key| {
                        passage[..passage.len() - 1]
                            .iter()
                            .fold(key, |lift, &u| (lift + advances[u]) % period)
                    })
                    .collect();
            }
            if fits {
                last.sort_unstable();
                fibre.push((
                    (0..classes).map(|u| stepped[u].then_some(advances[u])).collect(),
                    labels.iter().map(|&c| emitted[c].then_some(c)).collect(),
                    last,
                ));
            }
        }
    }
    fibre.sort();
    fibre.dedup();
    fibre
}

/// [implemented-exact] **Location equals the brute-force fibre**: on the helix `(2, 3)` over three
/// classes, for drawn terrains and read sets of one to three passages, the survivors (each partial
/// transport, partial labels and admitted lifts) are exactly the brute-force fibre's projection,
/// the truth survives, and the survivors come in reflection pairs.
#[test]
fn location_equals_the_brute_force_fibre() {
    let helix = helix(&[2, 3]);
    let mut draw = Draw::new(2_026_100_932);
    let mut located = 0;
    for trial in 0..24 {
        let terrain = SteppedTerrain::draw(helix.clone(), &mut draw);
        let passages = read_set(&terrain, &mut draw, 1 + trial % 3, 3 + trial % 5);
        // The rotation gauge reads the first passage's first emission at cell 0: carry the truth there.
        let location = locate(&helix, 3, &passages);
        let mut survivors: Vec<_> = location
            .survivors
            .iter()
            .map(|s| (s.advances.clone(), s.labels.clone(), s.lifts.clone()))
            .collect();
        survivors.sort();
        assert_eq!(survivors, brute_fibre(&helix, 3, &passages), "trial {trial}");
        let pairs = location.survivors();
        for (advances, labels) in &pairs {
            let reflected: (Vec<Option<u64>>, Vec<Option<usize>>) = (
                advances.iter().map(|a| a.map(|a| (6 - a) % 6)).collect(),
                (0..3).map(|c| labels[(3 - c) % 3]).collect(),
            );
            assert!(pairs.contains(&reflected), "trial {trial}");
        }
        if matches!(location.fibre(), TransportFibre::One(_)) {
            located += 1;
        }
    }
    assert!(located > 0);
}

/// Every key once, in a drawn order: the read set's passages from every opening of the helix.
fn every_key(terrain: &SteppedTerrain, draw: &mut Draw, length: usize) -> Vec<Vec<usize>> {
    let period = terrain.helix().period();
    let mut left: Vec<u64> = (0..period).collect();
    (0..period)
        .map(|_| terrain.passage(left.remove(draw.below(left.len())), length))
        .collect()
}

/// [implemented-exact] **The generator is a member and every member regenerates the read set**: on
/// the helix `(2, 3, 5)` over five classes, for drawn terrains read from every key for two turns of
/// the joint clock, the generator's gauge representative is a member of the fibre, every member
/// regenerates every passage from some key, the observations to lock are at least the unicity count
/// where the fibre is one class, and each member's odometer and CRT readings are one lift.
#[test]
fn the_generator_is_a_member_and_every_member_regenerates_the_read_set() {
    let helix = helix(&[2, 3, 5]);
    let mut draw = Draw::new(2_026_100_933);
    let mut ones = 0;
    for _ in 0..6 {
        let terrain = SteppedTerrain::draw(helix.clone(), &mut draw);
        let passages = every_key(&terrain, &mut draw, 60);
        let location = locate(&helix, 5, &passages);
        let members = location.members();
        assert!(!members.is_empty());
        // The truth carried to the rotation gauge (the first emission at cell 0).
        let truth = LocatedTransport::of_terrain(&terrain);
        let first = passages[0][0];
        let turn = truth.cell_of(first).unwrap() as usize;
        let gauged = LocatedTransport::new(
            helix.clone(),
            truth.advances().to_vec(),
            (0..5).map(|c| truth.labels()[(c + turn) % 5]).collect(),
        )
        .unwrap();
        assert!(members.contains(&gauge_representative(&location, &gauged)));
        for member in &members {
            assert!(passages.iter().all(|passage| !member.keys(passage).is_empty()));
            for class in 0..5 {
                assert_eq!(helix.of_digits(&member.digits(class)), member.advances()[class]);
            }
        }
        let n_star = location.located_from().unwrap();
        if let TransportFibre::One(_) = location.fibre() {
            ones += 1;
            assert!(n_star >= unicity_count(&helix, 5));
        }
    }
    assert!(ones > 0);
}

/// [implemented-exact] **The unicity count** of the record's terrain: `5^14 < 9,331,200,000 ≤ 5^15`
/// gives `n_U = 16` on the helix `(3, 4, 5)` over five classes.
#[test]
fn the_unicity_count_of_the_pinned_terrain_is_sixteen() {
    assert_eq!(unicity_count(&helix(&[3, 4, 5]), 5), 16);
}

/// [proved-derived; implemented-exact] **The relabelling law**: for twelve permutations `π` of five
/// classes (every tenth; the harness reads all 120), the location on `π∘x` returns the fibre on `x`
/// carried by `π` (each advance at `π u`, each label `π(λ(c))`), the same observations to lock and
/// the same code length; the residue chart, whose transport a class's code chooses, changes its
/// code length under some permutation.
#[test]
fn relabelling_carries_the_located_transport_and_keeps_the_code_length() {
    let helix = helix(&[2, 3, 5]);
    let mut draw = Draw::new(2_026_100_934);
    let terrain = SteppedTerrain::draw(helix.clone(), &mut draw);
    let passages = every_key(&terrain, &mut draw, 60);
    let location = locate(&helix, 5, &passages);
    let members = location.members();
    let located = members[0].clone();
    let length = located_code(&located, &passages).unwrap().len();
    // Every tenth permutation (the harness reads all 120); the residue chart's labels are read over
    // the same twelve.
    let some: Vec<Vec<usize>> = permutations(5).into_iter().step_by(10).collect();
    let residue = residue_code_length(&helix, 5, &passages, &some);
    let mut residue_moved = false;
    for pi in some.clone() {
        let relabelled: Vec<Vec<usize>> = passages
            .iter()
            .map(|p| p.iter().map(|&u| pi[u]).collect())
            .collect();
        let moved = locate(&helix, 5, &relabelled);
        let moved_members = moved.members();
        assert_eq!(moved_members.len(), members.len());
        let carry = |member: &LocatedTransport| {
            let mut advances = vec![0; 5];
            for u in 0..5 {
                advances[pi[u]] = member.advances()[u];
            }
            LocatedTransport::new(
                helix.clone(),
                advances,
                member.labels().iter().map(|label| label.map(|u| pi[u])).collect(),
            )
            .unwrap()
        };
        for member in &members {
            assert!(moved_members.contains(&carry(member)), "{pi:?}");
        }
        let carried = carry(&located);
        assert_eq!(moved.located_from(), location.located_from());
        assert_eq!(located_code(&carried, &relabelled).unwrap().len(), length);
        residue_moved |= residue_code_length(&helix, 5, &relabelled, &some) != residue;
    }
    assert!(residue_moved);
}

/// [implemented-exact] **The located code reopens its read set**: on the helix `(3, 4, 5)`, the
/// truth's transport codes sixteen passages of sixty cells in `5·6 + 7 + 16·6 + 10 = 143` bits
/// with no patch, and reads them back; the residue chart's residual also reads back, longer.
#[test]
fn the_located_code_reopens_its_read_set() {
    let helix = helix(&[3, 4, 5]);
    let mut draw = Draw::new(2_026_100_935);
    let terrain = SteppedTerrain::draw(helix.clone(), &mut draw);
    let passages = read_set(&terrain, &mut draw, 16, 60);
    let truth = LocatedTransport::of_terrain(&terrain);
    let code = located_code(&truth, &passages).unwrap();
    assert_eq!(code.len(), 143);
    let lengths = vec![60; 16];
    assert_eq!(read_located(&helix, 5, &code, &lengths).unwrap(), passages);
    let mut truncated = code.clone();
    truncated.pop();
    assert!(read_located(&helix, 5, &truncated, &lengths).is_err());
    let advances = residue_advances(&helix, 5);
    let labels: Vec<Option<usize>> = (0..5).map(Some).collect();
    let keys = vec![0; 16];
    let residual = residual_code(&helix, &advances, &labels, &keys, &passages).unwrap();
    assert_eq!(
        read_residual(&helix, &advances, &mut residual.iter().copied(), &lengths).unwrap(),
        passages
    );
    assert!(residual.len() > code.len());
}

/// [implemented-exact] **The encoding founds the helix on the located transports** (the consumer,
/// `hnn::encoding`, read-only): the passage chart `ℚ^D` with `T_u e_ℓ = e_(ℓ + A(u))`, the located
/// labels' receiving forms and the keys' openings; its squares `D E = ρ`, `E T_u = U_u E` hold
/// exactly on every reached state; where the advances generate `ℤ/D` every lift is reached and the
/// founded dimension is `D − (D_low − 1)`: the readings are the shifts of one cell's indicator, an
/// interval of `D_low` lifts, whose Fourier transform vanishes at the `D_low − 1` nonzero multiples
/// of `D/D_low`.
#[test]
fn the_encoding_founds_the_helix_on_the_located_transports() {
    let helix = helix(&[2, 3, 5]);
    let mut draw = Draw::new(2_026_100_936);
    let terrain = SteppedTerrain::draw(helix.clone(), &mut draw);
    let truth = LocatedTransport::of_terrain(&terrain);
    let (n, transports, coupling, openings) = truth.chart(&[0, 7]).unwrap();
    let chart = PassageChart::new(n, transports, Vec::new(), coupling, openings).unwrap();
    let encoding = Encoding::found(&chart).unwrap();
    let squares = encoding.squares(&chart).unwrap();
    assert_eq!(squares.transports, 5);
    let generated = truth
        .advances()
        .iter()
        .fold(helix.period(), |g, &a| gcd(g, a));
    assert_eq!(generated, 1);
    assert_eq!(encoding.reached(), 30);
    // The receiving grain is silent on the D_low − 1 Fourier modes where a cell's indicator (an
    // interval of D_low lifts) vanishes: k ∈ (D/D_low)ℤ, k ≢ 0.
    assert_eq!(encoding.dimension(), 30 - (6 - 1));
}

/// [implemented-exact] **Repair through the located navigator**: drawn passages on the helix
/// `(3, 4, 5)` with the record's damage; every family is certified (the joint fibre's projection),
/// every released cell is its truth, and every passage reopens from its residual; a navigator the
/// intact cells refuse is refused.
#[test]
fn the_repair_restores_through_the_located_navigator() {
    let helix = helix(&[3, 4, 5]);
    let mut draw = Draw::new(2_026_100_937);
    let terrain = SteppedTerrain::draw(helix.clone(), &mut draw);
    let truth = LocatedTransport::of_terrain(&terrain);
    let erased: Vec<usize> = std::iter::once(3)
        .chain(6..10)
        .chain(20..25)
        .chain(33..37)
        .chain(44..48)
        .chain(55..60)
        .collect();
    assert_eq!(erased.len(), 23);
    let mut released = 0;
    for passage in read_set(&terrain, &mut draw, 8, 60) {
        let damaged: Vec<Option<usize>> = passage
            .iter()
            .enumerate()
            .map(|(t, &u)| (!erased.contains(&t)).then_some(u))
            .collect();
        let restriction = truth.restrict(&damaged).unwrap();
        assert!(restriction.certified().iter().all(|&c| c));
        for (t, release) in restriction.release().unwrap().iter().enumerate() {
            match release {
                CellRelease::Released(class) => {
                    assert_eq!(*class, passage[t]);
                    released += 1;
                }
                CellRelease::Held(family) => assert!(family.contains(&passage[t])),
                CellRelease::Intact(class) => assert_eq!(*class, passage[t]),
            }
        }
        let members = std::slice::from_ref(&truth);
        let residual = lift_residual(members, &damaged, &passage).unwrap();
        assert_eq!(lift_reopen(members, &damaged, &residual).unwrap(), passage);
        // Through the fibre of the truth and its reflection, read alike.
        let fibre = [truth.clone(), truth.reflected()];
        assert_eq!(
            restrict_fibre(&fibre, &damaged).unwrap().release().unwrap(),
            restriction.release().unwrap()
        );
    }
    assert!(released > 0);
    // A navigator the intact cells refuse: every advance turned by one.
    let wrong = LocatedTransport::new(
        helix.clone(),
        truth.advances().iter().map(|&a| (a + 1) % 60).collect(),
        truth.labels().to_vec(),
    )
    .unwrap();
    let passage = terrain.passage(0, 60);
    let damaged: Vec<Option<usize>> = passage.iter().map(|&u| Some(u)).collect();
    if wrong.keys(&passage).is_empty() {
        assert!(matches!(
            wrong.restrict(&damaged),
            Err(CompressionError::Contradicted { .. })
        ));
    }
}

