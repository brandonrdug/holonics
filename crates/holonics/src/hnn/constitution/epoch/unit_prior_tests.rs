//! Exact witnesses of the declared first-reach unit prior (Refs #63, owed #62).
use super::*;
use crate::ratio::integer;

fn native(unit: bool) -> NormalLaw {
    let mut law = NormalLaw::with_receiving_prior(ExactRatMatrix::zero(2, 2).unwrap(), 1);
    law.unit_prior = unit;
    law
}

fn law(unit: bool) -> EpochLaw {
    EpochLaw::from_normal(&native(unit), 6).unwrap()
}

fn record(exponent: u32, feature: [i64; 2]) -> EpochRecord {
    EpochRecord {
        feature: EpochArray::new(
            1,
            2,
            exponent,
            feature.into_iter().map(BigInt::from).collect(),
        )
        .unwrap(),
        covector: EpochArray::new(2, 1, 3, vec![2.into(), (-1).into()]).unwrap(),
    }
}

fn incoming(epoch: u64) -> EpochFlow {
    // Two actual locus records in ten heard cells: the unit is a RECORD, not
    // the receiver's ten-cell partition or a guessed number of samples.
    EpochFlow::from_records(
        2,
        2,
        6,
        10,
        epoch,
        10,
        &[record(3, [1, 0]), record(3, [3, 0])],
    )
    .unwrap()
}

fn coordinate(array: &EpochArray, row: usize, column: usize) -> Rat {
    Rat::new(
        array.values[row * array.columns + column].clone(),
        (BigInt::one() << array.exponent as usize) * array.row_divisors[row],
    )
}

#[test]
fn unit_prior_is_exact_one_record_power_of_four_and_enters_once() {
    let opening = law(true);
    assert!(opening.gram.is_zero());
    let flow = incoming(0);
    let (h, priors) = opening.gram_after(&flow).unwrap();
    assert_eq!(priors, vec![(0, -2, rat(1, 16))]);
    let one_record = coordinate(&flow.gram, 0, 0) / integer(2);
    assert!(rat(1, 16) <= one_record && one_record < rat(1, 4));
    assert_eq!(coordinate(&h, 0, 0), rat(7, 32));
    let step = opening
        .deposit(&flow, &EpochArray::new(1, 1, 4, vec![1.into()]).unwrap())
        .unwrap();
    assert!(!step.step.is_zero());
    assert_eq!(step.successor.gram, h);
    assert_eq!(step.unit_priors, priors);
    let (again, additions) = step.successor.gram_after(&incoming(1)).unwrap();
    assert!(additions.is_empty());
    assert_eq!(coordinate(&again, 0, 0), rat(3, 8));
    for row in 0..2 {
        assert!(coordinate(&step.successor.map, row, 1).is_zero());
        assert!(coordinate(&step.successor.news, row, 1).is_zero());
        assert!(coordinate(&step.successor.gram, row, 1).is_zero());
        assert!(coordinate(&step.successor.gram, 1, row).is_zero());
    }
    let expected = opening
        .map
        .multiply(&h)
        .unwrap()
        .add(&opening.news)
        .unwrap()
        .add(
            &flow
                .covector
                .scalar_product(&EpochArray::new(1, 1, 4, vec![1.into()]).unwrap())
                .unwrap(),
        )
        .unwrap();
    assert_eq!(
        step.successor
            .map
            .multiply(&h)
            .unwrap()
            .add(&step.successor.news)
            .unwrap(),
        expected
    );
}

#[test]
fn unit_prior_gram_is_covariant_under_dyadic_feature_column_units() {
    let opening = law(true);
    let located = law(false);
    let make = |m: i32| {
        let extra = (-m).max(0) as u32;
        let scale = m.max(0) as u32;
        EpochFlow::from_records(
            2,
            2,
            6,
            2,
            0,
            2,
            &[
                record(5 + extra, [1 << scale, 2 << extra]),
                record(5 + extra, [-3 << scale, 4 << extra]),
            ],
        )
        .unwrap()
    };
    let (base, _) = opening.gram_after(&make(0)).unwrap();
    let (located_base, _) = located.gram_after(&make(0)).unwrap();
    for m in [-2, -1, 1, 2] {
        let (scaled, _) = opening.gram_after(&make(m)).unwrap();
        let (located_scaled, _) = located.gram_after(&make(m)).unwrap();
        for i in 0..2 {
            for j in 0..2 {
                let power = m * (i32::from(i == 0) + i32::from(j == 0));
                let factor = if power >= 0 {
                    integer(1_i64 << power)
                } else {
                    rat(1, 1_i64 << -power)
                };
                assert_eq!(coordinate(&scaled, i, j), coordinate(&base, i, j) * &factor);
                if i == 0 && j == 0 {
                    assert_ne!(
                        coordinate(&located_scaled, i, j),
                        coordinate(&located_base, i, j) * factor
                    );
                }
            }
        }
    }
}

#[test]
fn unit_prior_sparse_checkpoint_is_exact_and_continues_the_same_law() {
    let opening = law(true);
    let gain = EpochArray::new(1, 1, 4, vec![1.into()]).unwrap();
    let state = opening.deposit(&incoming(0), &gain).unwrap().successor;
    let text = state.encode_checkpoint();
    let cold = EpochLaw::decode_checkpoint(&text, &opening, 1 << 20).unwrap();
    assert_eq!(cold.encode_checkpoint(), text);
    assert!(cold.unit_prior);
    assert_eq!(
        cold.deposit(&incoming(1), &gain).unwrap().successor,
        state.deposit(&incoming(1), &gain).unwrap().successor
    );
    let empty = opening.encode_checkpoint();
    assert_eq!(
        EpochLaw::decode_checkpoint(&empty, &opening, 1 << 20).unwrap(),
        opening
    );
    assert!(EpochLaw::decode_checkpoint(&text, &law(false), 1 << 20).is_err());
    let mut foreign = state;
    foreign.gram = foreign
        .gram
        .add(&EpochArray::new(2, 2, 10, vec![0.into(), 1.into(), 1.into(), 0.into()]).unwrap())
        .unwrap();
    assert!(EpochLaw::decode_checkpoint(&foreign.encode_checkpoint(), &opening, 1 << 20).is_err());
}

#[test]
fn unit_prior_import_refuses_heard_or_nonfounding_native_gram() {
    let mut wrong = native(true);
    wrong.gram[0][0] = rat(3, 1);
    assert!(EpochLaw::from_normal(&wrong, 6).is_err());
    let mut moving = native(true);
    moving.map =
        ExactRatMatrix::new(vec![vec![rat(1, 64), rat(0, 1)], vec![rat(0, 1); 2]]).unwrap();
    assert!(EpochLaw::from_normal(&moving, 6).is_err());
}
