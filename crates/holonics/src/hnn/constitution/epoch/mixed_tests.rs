//! Synthetic controls for the receiving period, exact residual, and admission.
use super::*;

fn a(rows: usize, columns: usize, exponent: u32, values: &[i64]) -> EpochArray {
    EpochArray::new(
        rows,
        columns,
        exponent,
        values.iter().copied().map(BigInt::from).collect(),
    )
    .unwrap()
}
fn sample(phase: Rat) -> Sample {
    Sample {
        weight: Rat::one(),
        feature: vec![rat(1, 2), Rat::one()],
        covector: vec![rat(3, 4), phase],
        masses: None,
    }
}

#[test]
fn mixed_period_rows_preserve_the_exact_sample_and_refuse_foreign_denominators() {
    let original = sample(rat(-3, 22));
    let record = EpochRecord::from_sample_with_phase_rows(&original, &[1], 11).unwrap();
    assert_eq!(record.covector.row_divisors, vec![1, 11]);
    assert_eq!(
        record.covector.to_matrix().unwrap().entries(),
        &original.covector
    );
    assert_eq!(
        record.feature.to_matrix().unwrap().entries(),
        &original.feature
    );
    assert!(EpochRecord::from_sample(&original).is_err());
    assert!(EpochRecord::from_sample_with_phase_rows(&sample(rat(1, 13)), &[1], 11).is_err());
    assert!(EpochRecord::from_sample_with_phase_rows(&original, &[0], 11).is_err());
    assert!(EpochRecord::from_sample_with_phase_rows(&original, &[1, 1], 11).is_err());
    assert!(EpochRecord::from_sample_with_phase_rows(&original, &[2], 11).is_err());
    assert!(EpochRecord::from_sample_with_phase_rows(&original, &[1], 10).is_err());
}

#[test]
fn mixed_period_news_has_exact_invariant_fall_and_cold_continuation() {
    let declaration = EpochLaw::founded(2, 2, 12, 0)
        .unwrap()
        .with_phase_rows(&[1], 11)
        .unwrap();
    let mut law = declaration.clone();
    let gamma = EpochArray::from_dyadic_scalar(&rat(3, 8)).unwrap();
    let records =
        vec![EpochRecord::from_sample_with_phase_rows(&sample(rat(-3, 22)), &[1], 11).unwrap(); 3];
    for epoch in 0..3 {
        let flow = EpochFlow::from_records(2, 2, 12, 231, epoch, 1, &records).unwrap();
        assert_eq!((flow.cells, flow.records), (1, 3));
        let fresh = law.fresh(&flow).unwrap();
        assert_eq!(fresh.direction.row_divisors, vec![1, 11]);
        let certificate = fresh
            .certificate_face(&EpochSeries {
                rows: 1,
                columns: 1,
                numerators: vec![3.into()],
                denominator: 4.into(),
            })
            .unwrap();
        assert_eq!(
            certificate.unit.to_rows(),
            fresh.direction.to_matrix().unwrap().to_rows()
        );
        let deposited = law.deposit(&flow, &gamma).unwrap();
        let next = &deposited.successor;
        assert!(next.map.is_dyadic() && next.gram.is_dyadic() && deposited.step.is_dyadic());
        assert_eq!(next.news.row_divisors, vec![1, 11]);
        let left = next
            .map
            .multiply(&next.gram)
            .unwrap()
            .add(&next.news)
            .unwrap();
        let right = law
            .map
            .multiply(&next.gram)
            .unwrap()
            .add(&law.news)
            .unwrap()
            .add(&flow.covector.scalar_product(&gamma).unwrap())
            .unwrap();
        assert_eq!(left, right);
        let target = law
            .map
            .multiply(&next.gram)
            .unwrap()
            .add(&law.news)
            .unwrap()
            .add(&flow.covector.scalar_product(&gamma).unwrap())
            .unwrap();
        let phi = |w: &EpochArray| {
            w.multiply(&next.gram)
                .unwrap()
                .dot(w)
                .unwrap()
                .half()
                .unwrap()
                .subtract(&w.dot(&target).unwrap())
                .unwrap()
        };
        assert_eq!(
            phi(&law.map)
                .subtract(&phi(&next.map))
                .unwrap()
                .scalar_ratio()
                .unwrap(),
            deposited.fall.scalar_ratio().unwrap()
        );
        assert!(deposited.fall.scalar_ratio().unwrap() >= Rat::zero());
        let encoded = next.encode_checkpoint();
        assert_eq!(
            EpochLaw::decode_checkpoint(&encoded, &declaration).unwrap(),
            *next
        );
        let wrong = EpochLaw::founded(2, 2, 12, 0).unwrap();
        assert!(EpochLaw::decode_checkpoint(&encoded, &wrong).is_err());
        law = deposited.successor;
    }
}

#[test]
fn mixed_paired_news_preserves_each_row_group_and_outside_admission() {
    let symmetry =
        PortSymmetry::from_parts(vec![1, 0, 3, 2], vec![Some(1), Some(0), None], &[0]).unwrap();
    let law = EpochLaw::founded_paired(4, 3, 8, 0, symmetry.clone())
        .unwrap()
        .with_phase_rows(&[2, 3], 11)
        .unwrap();
    let s = Sample {
        weight: Rat::one(),
        feature: vec![Rat::one(), rat(1, 2), Rat::zero()],
        covector: vec![Rat::one(), rat(-1, 2), rat(2, 11), rat(-3, 22)],
        masses: None,
    };
    let record = EpochRecord::from_sample_with_phase_rows(&s, &[2, 3], 11).unwrap();
    let flow = EpochFlow::from_records(4, 3, 8, 231, 0, 1, &[record]).unwrap();
    let deposited = law.deposit(&flow, &a(1, 1, 2, &[3])).unwrap();
    let next = deposited.successor;
    assert_eq!(next.news.row_divisors, vec![1, 1, 11, 11]);
    assert_eq!(
        symmetry
            .first_failure(&next.map.to_matrix().unwrap())
            .unwrap(),
        None
    );
    assert_eq!(
        symmetry
            .first_failure(&next.news.to_matrix().unwrap())
            .unwrap(),
        None
    );
    let bad = Sample {
        feature: vec![Rat::one(), Rat::zero(), Rat::one()],
        ..s
    };
    let flow = EpochFlow::from_records(
        4,
        3,
        8,
        231,
        0,
        1,
        &[EpochRecord::from_sample_with_phase_rows(&bad, &[2, 3], 11).unwrap()],
    )
    .unwrap();
    assert!(matches!(
        law.deposit(&flow, &a(1, 1, 0, &[1])),
        Err(HnnError::PairedOutside { class: 2 })
    ));
    assert!(
        EpochLaw::founded_paired(4, 3, 8, 0, symmetry)
            .unwrap()
            .with_phase_rows(&[2], 11)
            .is_err()
    );
}

#[test]
fn odd_phase_news_below_the_map_grain_is_carried_whole() {
    let mut law = EpochLaw::founded(2, 1, 4, 0)
        .unwrap()
        .with_phase_rows(&[1], 11)
        .unwrap();
    let record = EpochRecord::from_sample_with_phase_rows(
        &Sample {
            weight: Rat::one(),
            feature: vec![Rat::one()],
            covector: vec![Rat::zero(), rat(1, 11)],
            masses: None,
        },
        &[1],
        11,
    )
    .unwrap();
    for crossing in 0..8 {
        let flow = EpochFlow::from_records(2, 1, 4, 1, crossing, 1, std::slice::from_ref(&record))
            .unwrap();
        let deposit = law.deposit(&flow, &a(1, 1, 3, &[3])).unwrap();
        assert!(deposit.step.is_zero());
        assert_eq!(
            deposit
                .successor
                .news
                .to_matrix()
                .unwrap()
                .get(1, 0)
                .unwrap(),
            &rat(3 * (crossing as i64 + 1), 88)
        );
        assert_eq!(
            deposit
                .successor
                .gram
                .to_matrix()
                .unwrap()
                .get(0, 0)
                .unwrap(),
            &Rat::from_integer(BigInt::from(crossing + 2))
        );
        law = deposit.successor;
    }
}

#[test]
fn receiving_ingress_c_may_skip_while_absorption_count_increments_once() {
    let mut law = EpochLaw::founded(1, 1, 6, 0).unwrap();
    let record = EpochRecord {
        feature: a(1, 1, 0, &[1]),
        covector: a(1, 1, 0, &[1]),
    };
    for (absorbed, c) in [0u64, 3, 11].into_iter().enumerate() {
        let flow =
            EpochFlow::from_records(1, 1, 6, 231, c, 1, std::slice::from_ref(&record)).unwrap();
        assert_eq!(
            flow.partition_exponent,
            partition_exponent(6, 231, c).unwrap()
        );
        law.fresh(&flow).unwrap();
        law = law.deposit(&flow, &a(1, 1, 2, &[1])).unwrap().successor;
        assert_eq!(law.crossings, absorbed as u64 + 1);
    }
}

#[test]
fn integral_owner_reads_mixed_rows_and_projects_unlike_groups_exactly() {
    let mixed = EpochArray::with_row_divisors(
        2,
        2,
        1,
        vec![2.into(), 4.into(), 3.into(), (-5).into()],
        vec![1, 11],
    )
    .unwrap();
    let vector = (vec![2.into(), (-1).into()], BigInt::from(4));
    let (read, denominator) = mixed.apply(&vector);
    assert_eq!(
        read.iter()
            .map(|n| Rat::new(n.clone(), denominator.clone()))
            .collect::<Vec<_>>(),
        vec![Rat::zero(), rat(1, 8)]
    );
    assert_eq!(mixed.schur_norms(), (rat(49, 22), rat(3, 1)));
    assert_eq!(mixed.to_rows(), mixed.to_matrix().unwrap().to_rows());
    let projected = mixed.projected(&[1, 0], &[Some(1), Some(0)]);
    let rows = mixed.to_rows();
    let expected: Vec<Vec<Rat>> = (0..2)
        .map(|i| {
            (0..2)
                .map(|j| (&rows[i][j] + &rows[1 - i][1 - j]) / Rat::from_integer(2.into()))
                .collect()
        })
        .collect();
    assert_eq!(projected.to_rows(), expected);
    // This result is a transient common integral chart, not a receiving
    // row-group declaration. Re-entry into grouped epoch arithmetic is typed.
    assert!(projected.add(&mixed).is_err());
    let legacy = IntegralMatrix::from_grouped(1, 1, vec![1.into()], 3.into()).unwrap();
    assert_eq!(legacy.to_rows(), vec![vec![rat(1, 3)]]);
    assert!(legacy.add(&a(1, 1, 0, &[1])).is_err());
    assert_eq!(legacy.to_matrix().unwrap().to_rows(), vec![vec![rat(1, 3)]]);
    assert!(
        EpochLaw::from_grouped(legacy, a(1, 1, 0, &[1]), a(1, 1, 0, &[0]), 6, 0, None).is_err()
    );
}

#[test]
fn integral_projection_keeps_large_odd_factors_without_machine_word_lcm_overflow() {
    let factors = vec![u64::MAX, u64::MAX - 2];
    let mixed =
        EpochArray::with_row_divisors(2, 1, 0, vec![1.into(), (-1).into()], factors.clone())
            .unwrap();
    let projected = mixed.projected(&[1, 0], &[Some(0)]);
    let expected = (Rat::new(1.into(), factors[0].into()) - Rat::new(1.into(), factors[1].into()))
        / Rat::from_integer(2.into());
    assert_eq!(
        projected.to_rows(),
        vec![vec![expected.clone()], vec![expected]]
    );
    assert!(projected.numerator_l1_bound >= BigInt::zero());
}
