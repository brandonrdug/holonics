use super::*;
use crate::holarchy::terrain::Draw;

/// Order-2's relation on `ℤ/n`: `y ↦ y + 1`.
fn order_two(classes: usize) -> PairRelation {
    PairRelation::new(2, (0..classes).map(|y| Some((y + 1) % classes)).collect()).unwrap()
}

/// A passage of `opening` declared cells, then `x_t = f(x_(t−δ))`, with the cells at `erased`
/// dropped.
fn damaged(truth: &[usize], erased: &[usize], classes: usize, opening: usize) -> DamagedPassage {
    let cells = (0..truth.len())
        .map(|t| (!erased.contains(&t)).then_some(truth[t]))
        .collect();
    DamagedPassage::new(cells, classes, opening).unwrap()
}

fn emitted(opening: &[usize], relation: &PairRelation, length: usize) -> Vec<usize> {
    let mut truth = opening.to_vec();
    while truth.len() < length {
        let antecedent = truth[truth.len() - relation.offset()];
        truth.push(relation.map()[antecedent].unwrap());
    }
    truth
}

/// [implemented-exact] **The located pair restores interior spans from both sides.** On order-2
/// (`ℤ/4`, opening 4, 16 cells) with a cell inside the opening beyond the rule's reach, a span
/// straddling the opening's end, an interior span and the tail erased: every cell a station joins to
/// an intact cell is released equal to its truth, the antecedents `2, 3` through `f⁻¹` two ticks
/// back from the stations `4, 5` (restored first from `6, 7` on the sweep's forward run, then
/// carried back on its return, so one sweep changes and a second changes nothing), and cell 1,
/// which no station joins, is held with the whole alphabet.
#[test]
fn the_located_pair_restores_interior_spans_from_both_sides() {
    let relation = order_two(4);
    let truth = emitted(&[3, 0, 2, 1], &relation, 16);
    let erased = [1, 2, 3, 4, 5, 9, 10, 14, 15];
    let passage = damaged(&truth, &erased, 4, 4);
    let restriction = restrict(&passage, &relation).unwrap();
    assert_eq!(restriction.sweeps(), 2);
    let releases = restriction.release().unwrap();
    for t in 0..truth.len() {
        match (&releases[t], erased.contains(&t)) {
            (CellRelease::Intact(class), false) => assert_eq!(*class, truth[t]),
            (CellRelease::Released(class), true) => assert_eq!(*class, truth[t], "cell {t}"),
            (CellRelease::Held(family), true) => {
                assert_eq!(t, 1);
                assert_eq!(family, &vec![0, 1, 2, 3]);
            }
            (other, _) => panic!("cell {t}: {other:?}"),
        }
    }
    assert_eq!(restriction.joint(), BigUint::from(4u32));
}

/// [implemented-exact] **Both sides plural: a chain with no intact cell is held with its joint
/// fibre.** Every odd cell from 3 erased on order-2 (opening 4): the edge `1 → 3` lies in the
/// opening, so the chain `3, 5, …, 11` reaches no intact cell, and at every one of its cells both
/// the antecedent's and the consequent's family are the whole alphabet. Every cell is held with
/// `ℤ/4`, certified (each class held by a member), and the joint fibre is 4, not `4⁵`: the
/// residual is one 2-bit patch, which reopens the whole chain.
#[test]
fn both_sides_plural_hold_the_chain_with_its_joint_fibre() {
    let relation = order_two(4);
    let truth = emitted(&[1, 2, 0, 3], &relation, 12);
    let erased = [3, 5, 7, 9, 11];
    let passage = damaged(&truth, &erased, 4, 4);
    let restriction = restrict(&passage, &relation).unwrap();
    let releases = restriction.release().unwrap();
    for &t in &erased {
        assert_eq!(releases[t], CellRelease::Held(vec![0, 1, 2, 3]), "cell {t}");
    }
    assert_eq!(restriction.support(), restriction.families());
    assert_eq!(restriction.joint(), BigUint::from(4u32));
    let residual = residual_code(&truth, &passage, &relation).unwrap();
    assert_eq!(residual.len(), 2);
    assert_eq!(reopen(&passage, &relation, &mut residual.into_iter()).unwrap(), truth);
}

/// [implemented-exact] **A consequence never read restricts nothing from its side.** On `ℤ/3` at
/// distance 1 with `0 ↦ 1`, `2 ↦ 0` and class 1's consequence unread: the erased cell between `1`
/// and `0` is unrestricted from its antecedent (class 1 is unread) and restricted to the classes
/// admitting `0` from its consequent (`1`, unread, and `2`); it is held with `{1, 2}`, and the joint
/// fibre is 2.
#[test]
fn an_unread_consequence_restricts_nothing_from_its_side() {
    let relation = PairRelation::new(1, vec![Some(1), None, Some(0)]).unwrap();
    let passage = DamagedPassage::new(vec![Some(1), None, Some(0)], 3, 1).unwrap();
    let restriction = restrict(&passage, &relation).unwrap();
    assert_eq!(restriction.release().unwrap()[1], CellRelease::Held(vec![1, 2]));
    assert_eq!(restriction.joint(), BigUint::from(2u32));
}

/// [implemented-exact] **A key that does not fit the intact cells is refused**, typed, never
/// repaired around: a constant passage read at stations from 0 against order-2.
#[test]
fn a_key_that_does_not_fit_the_intact_cells_is_refused() {
    let passage = DamagedPassage::new(vec![Some(0), Some(0), None, Some(0)], 4, 0).unwrap();
    assert!(matches!(
        restrict(&passage, &order_two(4)),
        Err(CompressionError::Contradicted { .. })
    ));
    assert_eq!(
        PairRelation::new(0, vec![Some(0)]),
        Err(CompressionError::ZeroOffset)
    );
}

/// [implemented-exact] **The restriction is the joint fibre's projection, and the codec reopens
/// every member** (the module's certificate, held to brute force). On 400 drawn passages (2 or 3
/// classes, 4 to 9 cells, any opening, distance 1 to 3, partial maps, drawn damage; mostly emitted by
/// the relation, some not): every assignment of the erased cells that every joined pair admits is
/// enumerated. The restriction refuses exactly when there is none; otherwise each family is the
/// enumerated members' classes at its cell, the joint fibre is their count, the certificate holds
/// at every cell, a cell is released exactly when its family is one class, and for every member
/// the residual reopens it exactly; the residuals are a prefix code (Kraft's sum at most one), so
/// the longest is at least `⌈log₂ N⌉` bits. The key's code reads back.
#[test]
fn the_restriction_is_the_joint_fibres_projection_and_the_codec_reopens() {
    let mut draw = Draw::new(2_026_100_741);
    let (mut fitting, mut refused, mut held) = (0, 0, 0);
    for _ in 0..400 {
        let classes = 2 + draw.below(2);
        let length = 4 + draw.below(6);
        let opening = draw.below(length + 1);
        let offset = 1 + draw.below(3);
        let map: Vec<Option<usize>> = (0..classes)
            .map(|_| (draw.below(4) != 0).then(|| draw.below(classes)))
            .collect();
        let relation = PairRelation::new(offset, map).unwrap();
        let mut truth = Vec::new();
        for t in 0..length {
            let follows = t >= opening.max(offset) && draw.below(5) != 0;
            let class = match (follows, follows.then(|| relation.map()[truth[t - offset]])) {
                (true, Some(Some(image))) => image,
                _ => draw.below(classes),
            };
            truth.push(class);
        }
        let erased: Vec<usize> = (0..length).filter(|_| draw.below(2) == 0).collect();
        let passage = damaged(&truth, &erased, classes, opening);
        // Brute force: every assignment of the erased cells.
        let mut members: Vec<Vec<usize>> = Vec::new();
        let total = classes.pow(erased.len() as u32);
        for code in 0..total {
            let mut cells = truth.clone();
            let mut rest = code;
            for &t in &erased {
                cells[t] = rest % classes;
                rest /= classes;
            }
            let admitted = (opening.max(offset)..length)
                .all(|t| relation.joins(cells[t - offset], cells[t]));
            if admitted {
                members.push(cells);
            }
        }
        let restriction = restrict(&passage, &relation);
        if members.is_empty() {
            assert!(matches!(restriction, Err(CompressionError::Contradicted { .. })));
            refused += 1;
            continue;
        }
        let restriction = restriction.unwrap();
        fitting += 1;
        assert_eq!(restriction.joint(), BigUint::from(members.len()));
        for t in 0..length {
            let mut projection: Vec<usize> = members.iter().map(|m| m[t]).collect();
            projection.sort_unstable();
            projection.dedup();
            assert_eq!(restriction.families()[t], projection, "cell {t}");
        }
        assert_eq!(restriction.support(), restriction.families());
        for (t, release) in restriction.release().unwrap().iter().enumerate() {
            match release {
                CellRelease::Intact(_) => assert!(!erased.contains(&t)),
                CellRelease::Released(_) => assert_eq!(restriction.families()[t].len(), 1),
                CellRelease::Held(family) => {
                    assert!(family.len() > 1);
                    held += 1;
                }
            }
        }
        // The residual is a prefix code over the joint fibre: its words are distinct and none is a
        // prefix of another (each reopens its member exactly, reading no further), so Kraft's sum
        // `Σ 2^(longest − |w|) ≤ 2^longest` holds and the longest word is at least `⌈log₂ N⌉`.
        let bound = crate::compression::cost::ceil_log2(&BigUint::from(members.len()));
        let mut words = Vec::new();
        for member in &members {
            let residual = residual_code(member, &passage, &relation).unwrap();
            let mut bits = residual.clone().into_iter();
            assert_eq!(&reopen(&passage, &relation, &mut bits).unwrap(), member);
            assert!(bits.next().is_none());
            words.push(residual);
        }
        let longest = words.iter().map(Vec::len).max().unwrap();
        assert!(longest as u64 >= bound);
        let kraft: BigUint = words
            .iter()
            .map(|word| BigUint::one() << (longest - word.len()))
            .sum();
        assert!(kraft <= BigUint::one() << longest);
        for (index, word) in words.iter().enumerate() {
            for other in &words[index + 1..] {
                let shorter = word.len().min(other.len());
                assert_ne!(word[..shorter], other[..shorter], "a prefix of another word");
            }
        }
        let key = key_code(&relation, 8).unwrap();
        assert_eq!(read_key(&mut key.into_iter(), classes, 8).unwrap(), relation);
    }
    assert!(fitting > 100 && refused > 0 && held > 0, "{fitting} {refused} {held}");
}
