use super::super::contact_tests::{calibrate, current, observe, phase, points, value, world};
use super::*;
use crate::embedding_fiber::ResidentReadout;
use num_traits::Zero;

fn compatible(r: ConstitutiveReading) -> (Vec<Rat>, Vec<Vec<Rat>>) {
    match r {
        ConstitutiveReading::Unique { current } => (current, vec![]),
        ConstitutiveReading::Plural {
            particular,
            directions,
        } => (particular, directions),
        other => panic!("expected affine fibre: {other:?}"),
    }
}
fn condition(p: &ResidentConditionPreimage<'_>) -> (Vec<Rat>, Vec<Vec<Rat>>) {
    match p.inspect().unwrap() {
        ConditionPreimageReading::Compatible {
            particular,
            directions,
        } => (particular, directions),
        other => panic!("{other:?}"),
    }
}

#[test]
#[ignore = "requires CUDA; a whole free condition family has a unique output without choosing a condition"]
fn free_conditions_transport_jointly_and_a_fixed_output_conducts() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let mut w = world(&s);
    let mut body = ResidentConstitutiveFibre::found_bilinear_contact(&s, 1, 1, 1).unwrap();
    calibrate(&s, &mut body, &mut w, None);
    let zero = points(&s, &[0, 0]);
    let one = points(&s, &[1, 0]);
    let f = body
        .read_condition_preimage(current(&zero), current(&zero))
        .unwrap();
    let before = body.census();
    let cut = body.occurrences();
    let silent = body.read_condition_image(current(&zero), &f).unwrap();
    assert_eq!(body.census().section_read_outs, before.section_read_outs);
    assert_eq!(body.census().ingress_octets, before.ingress_octets);
    assert_eq!(body.occurrences(), cut);
    let next = body
        .advance_bilinear_contact(silent.current(), current(&one), None)
        .unwrap();
    assert_eq!(value(&next), phase(0, 0, 1).current());
    let read = silent.inspect().unwrap();
    assert_eq!(read.coverage, ConditionCoverage::Complete);
    assert_eq!(compatible(read.supported_conditions).1.len(), 2);
    assert_eq!(
        compatible(read.supported_outputs),
        (vec![Rat::zero(); 2], vec![])
    );
    let moving = body.read_condition_image(current(&one), &f).unwrap();
    let read = moving.inspect().unwrap();
    assert_eq!(read.coverage, ConditionCoverage::Complete);
    let (_, directions) = compatible(read.joint);
    assert_eq!(directions.len(), 2);
    for d in directions {
        assert_eq!(d[0], d[2]);
        assert_eq!(d[1], d[3]);
    }
    assert_eq!(condition(moving.original_condition()).1.len(), 2);
}

#[test]
#[ignore = "requires CUDA; a later native return refines the joint family and its successor predicts"]
fn an_actual_return_refines_the_condition_without_host_selection() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let mut w = world(&s);
    let mut body = ResidentConstitutiveFibre::found_bilinear_contact(&s, 1, 1, 1).unwrap();
    calibrate(&s, &mut body, &mut w, None);
    let zero = points(&s, &[0, 0]);
    let one = points(&s, &[1, 0]);
    let f = body
        .read_condition_preimage(current(&zero), current(&zero))
        .unwrap();
    let image = body.read_condition_image(current(&one), &f).unwrap();
    let hidden = phase(-5, 12, 13);
    let measured = observe(&mut w, phase(1, 0, 1), hidden);
    let y = points(
        &s,
        &NativePhaseCurrent::from_current(&measured).unwrap().words(),
    );
    let before = body.census();
    let refined = image
        .receive(ResidentConstitutiveCurrent::rational(&y).unwrap())
        .unwrap();
    assert_eq!(body.census().section_read_outs, before.section_read_outs);
    let source = points(&s, &[4, 1]);
    let before = body.census();
    let predicted = body
        .read_condition_image(current(&source), &refined)
        .unwrap();
    let one = points(&s, &[1, 0]);
    let carried = body
        .advance_bilinear_contact(predicted.current(), current(&one), None)
        .unwrap();
    assert_eq!(body.census().section_read_outs, before.section_read_outs);
    assert_eq!(value(&carried), observe(&mut w, phase(4, 1, 1), hidden));
    assert_eq!(condition(&f).1.len(), 2);
    assert_eq!(
        condition(&refined),
        (
            vec![
                Rat::new((-5).into(), 13.into()),
                Rat::new(12.into(), 13.into())
            ],
            vec![]
        )
    );
}

#[test]
#[ignore = "requires CUDA; a strict supported domain cannot claim an unconditional constant output"]
fn partial_and_empty_domains_keep_their_witnesses_and_block_unqualified_use() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let mut body = ResidentConstitutiveFibre::found_bilinear_contact(&s, 1, 1, 1).unwrap();
    let z = points(&s, &[0, 0]);
    let one = points(&s, &[1, 0]);
    let i = points(&s, &[0, 1]);
    for c in [&one, &i] {
        body.advance_bilinear_contact(current(&z), current(c), Some(current(&z)))
            .unwrap();
    }
    body.advance_bilinear_contact(current(&one), current(&z), Some(current(&z)))
        .unwrap();
    let f = body
        .read_condition_preimage(current(&z), current(&z))
        .unwrap();
    let image = body.read_condition_image(current(&one), &f).unwrap();
    let reading = image.inspect().unwrap();
    match reading.coverage {
        ConditionCoverage::Partial {
            condition,
            residual,
            ..
        } => {
            assert!(condition.iter().any(|x| !x.is_zero()));
            assert!(residual.iter().any(|x| !x.is_zero()));
        }
        other => panic!("{other:?}"),
    }
    assert_eq!(
        compatible(reading.supported_conditions),
        (vec![Rat::zero(); 2], vec![])
    );
    assert_eq!(
        compatible(reading.supported_outputs),
        (vec![Rat::zero(); 2], vec![])
    );
    let cut = body.occurrences();
    assert!(
        body.advance_bilinear_contact(image.current(), current(&one), None)
            .is_err()
    );
    assert!(image.receive(current(&z)).is_err());
    assert_eq!(body.occurrences(), cut);
    let none = body.read_condition_image(current(&i), &f).unwrap();
    assert!(matches!(
        none.inspect().unwrap().coverage,
        ConditionCoverage::NoSupportedCondition { .. }
    ));
    let empty = body
        .read_condition_preimage(current(&z), current(&one))
        .unwrap();
    let image = body.read_condition_image(current(&one), &empty).unwrap();
    assert_eq!(
        image.inspect().unwrap().coverage,
        ConditionCoverage::EmptyConditionFibre
    );
    assert!(image.receive(current(&z)).is_err());
}

#[test]
#[ignore = "requires CUDA; reception uses the exact immutable joint family that produced the image"]
fn a_later_deposit_does_not_rewrite_an_earlier_joint_return() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let mut w = world(&s);
    let mut body = ResidentConstitutiveFibre::found_bilinear_contact(&s, 1, 1, 1).unwrap();
    calibrate(&s, &mut body, &mut w, None);
    let zero = points(&s, &[0, 0]);
    let one = points(&s, &[1, 0]);
    let y = points(&s, &[3, 4]);
    let f = body
        .read_condition_preimage(current(&zero), current(&zero))
        .unwrap();
    let earlier = body.read_condition_image(current(&one), &f).unwrap();
    let before = earlier.inspect().unwrap();
    body.advance_bilinear_contact(current(&zero), current(&zero), Some(current(&one)))
        .unwrap();
    let old = earlier.receive(current(&y)).unwrap();
    let later = body
        .read_condition_image(current(&one), &f)
        .unwrap()
        .receive(current(&y))
        .unwrap();
    assert!(condition(&old).1.is_empty());
    assert_eq!(condition(&later).1.len(), 1);
    assert_eq!(earlier.inspect().unwrap(), before);
}

#[test]
#[ignore = "requires CUDA; rational joint condition/output correlations survive refinement"]
fn rational_images_and_repeated_refinement_keep_correlated_directions() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let mut w = world(&s);
    let mut body = ResidentConstitutiveFibre::found_bilinear_contact(&s, 1, 1, 1).unwrap();
    calibrate(&s, &mut body, &mut w, None);
    let zero = points(&s, &[0, 0]);
    let x = points(&s, &[2, 3, 5]);
    let y = points(&s, &[1, 0, 13]);
    let f = body
        .read_condition_preimage(current(&zero), current(&zero))
        .unwrap();
    let image = body
        .read_condition_image(ResidentConstitutiveCurrent::rational(&x).unwrap(), &f)
        .unwrap();
    let (_, directions) = compatible(image.inspect().unwrap().joint);
    for d in directions {
        assert_eq!(
            &d[2] * Rat::from_integer(5.into()),
            &d[0] * Rat::from_integer(2.into()) - &d[1] * Rat::from_integer(3.into())
        );
        assert_eq!(
            &d[3] * Rat::from_integer(5.into()),
            &d[0] * Rat::from_integer(3.into()) + &d[1] * Rat::from_integer(2.into())
        );
    }
    let next = image
        .receive(ResidentConstitutiveCurrent::rational(&y).unwrap())
        .unwrap();
    assert_eq!(
        condition(&next).0,
        vec![
            Rat::new(10.into(), 169.into()),
            Rat::new((-15).into(), 169.into())
        ]
    );
    let again = body
        .read_condition_image(ResidentConstitutiveCurrent::rational(&x).unwrap(), &next)
        .unwrap();
    assert_eq!(
        condition(
            &again
                .receive(ResidentConstitutiveCurrent::rational(&y).unwrap())
                .unwrap()
        ),
        condition(&next)
    );
    let bad = points(&s, &[2, 0, 13]);
    assert!(matches!(
        again
            .receive(ResidentConstitutiveCurrent::rational(&bad).unwrap())
            .unwrap()
            .inspect()
            .unwrap(),
        ConditionPreimageReading::OutsideRepresentedRelation { .. }
    ));
}

#[test]
#[ignore = "requires CUDA; output receiver factors over a plural condition image"]
fn fixed_output_receivers_are_guarded_by_complete_condition_coverage() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let mut body = ResidentConstitutiveFibre::found_bilinear_contact(&s, 1, 1, 2).unwrap();
    // Exact algebra control Gamma(s,c)=(s+c*s,2*s+c*s).
    for (x, c, y) in [
        ([0, 0], [1, 0], [0, 0, 0, 0]),
        ([0, 0], [0, 1], [0, 0, 0, 0]),
        ([1, 0], [1, 0], [2, 0, 3, 0]),
        ([0, 1], [1, 0], [0, 2, 0, 3]),
        ([1, 0], [-1, 0], [0, 0, 1, 0]),
        ([0, 1], [-1, 0], [0, 0, 0, 1]),
    ] {
        let x = points(&s, &x);
        let c = points(&s, &c);
        let y = points(&s, &y);
        body.advance_bilinear_contact(current(&x), current(&c), Some(current(&y)))
            .unwrap();
    }
    let z = points(&s, &[0, 0]);
    let zero_y = points(&s, &[0, 0, 0, 0]);
    let one = points(&s, &[1, 0]);
    let f = body
        .read_condition_preimage(current(&z), current(&zero_y))
        .unwrap();
    let image = body.read_condition_image(current(&one), &f).unwrap();
    let reading = image.inspect().unwrap();
    assert_eq!(reading.coverage, ConditionCoverage::Complete);
    assert_eq!(compatible(reading.supported_outputs).1.len(), 2);
    let face = image.read_differential_pairs(0, 1).unwrap();
    assert_eq!((face.positive, face.unresolved), (1, 0));
    let mut partial = ResidentConstitutiveFibre::found_bilinear_contact(&s, 1, 1, 2).unwrap();
    let i = points(&s, &[0, 1]);
    for c in [&one, &i] {
        partial
            .advance_bilinear_contact(current(&z), current(c), Some(current(&zero_y)))
            .unwrap();
    }
    partial
        .advance_bilinear_contact(current(&one), current(&z), Some(current(&zero_y)))
        .unwrap();
    let f = partial
        .read_condition_preimage(current(&z), current(&zero_y))
        .unwrap();
    let image = partial.read_condition_image(current(&one), &f).unwrap();
    let face = image.read_differential_pairs(0, 1).unwrap();
    assert_eq!(
        (
            face.positive,
            face.negative,
            face.unresolved,
            face.exact_zero
        ),
        (0, 0, 1, 0)
    );
}

#[test]
#[ignore = "requires CUDA; image/refinement refusal preserves the original action and condition family"]
fn invalid_operands_and_word_overflow_preserve_the_input_family() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let other = ResidentSurface::on(&r).unwrap();
    let mut w = world(&s);
    let mut body = ResidentConstitutiveFibre::found_bilinear_contact(&s, 1, 1, 1).unwrap();
    calibrate(&s, &mut body, &mut w, None);
    let zero = points(&s, &[0, 0]);
    let one = points(&s, &[1, 0]);
    let huge = points(&s, &[i64::MAX, 0]);
    let f = body
        .read_condition_preimage(current(&zero), current(&zero))
        .unwrap();
    let original = f.inspect().unwrap();
    let basis = body.inspect_relation().unwrap();
    let cut = body.occurrences();
    let foreign = points(&other, &[1, 0]);
    assert!(body.read_condition_image(current(&foreign), &f).is_err());
    let bad = points(&s, &[1, 0, 0]);
    assert!(
        body.read_condition_image(ResidentConstitutiveCurrent::rational(&bad).unwrap(), &f)
            .is_err()
    );
    let big_condition = body
        .read_condition_preimage(current(&one), current(&huge))
        .unwrap();
    assert!(
        body.read_condition_image(current(&huge), &big_condition)
            .is_err()
    );
    let tiny = points(&s, &[1, 0, i64::MAX]);
    let image = body
        .read_condition_image(ResidentConstitutiveCurrent::rational(&tiny).unwrap(), &f)
        .unwrap();
    assert!(image.receive(current(&huge)).is_err());
    assert!(
        image
            .receive(ResidentConstitutiveCurrent::rational(&bad).unwrap())
            .is_err()
    );
    assert_eq!(f.inspect().unwrap(), original);
    assert_eq!(body.inspect_relation().unwrap(), basis);
    assert_eq!(body.occurrences(), cut);
    assert_eq!(
        image.inspect().unwrap().coverage,
        ConditionCoverage::Complete
    );
}

#[test]
#[ignore = "requires CUDA; a translated supported domain returns the unsupported affine origin"]
fn partial_coverage_can_exclude_the_original_affine_origin() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let mut body = ResidentConstitutiveFibre::found_bilinear_contact(&s, 1, 1, 1).unwrap();
    let zero = points(&s, &[0, 0]);
    let i = points(&s, &[0, 1]);
    let one_i = points(&s, &[1, 1]);
    for (source, condition) in [(&i, &i), (&i, &one_i), (&one_i, &one_i)] {
        body.advance_bilinear_contact(current(source), current(condition), Some(current(&zero)))
            .unwrap();
    }
    let f = body
        .read_condition_preimage(current(&i), current(&zero))
        .unwrap();
    let image = body.read_condition_image(current(&one_i), &f).unwrap();
    let read = image.inspect().unwrap();
    match read.coverage {
        ConditionCoverage::Partial {
            direction,
            condition,
            residual,
        } => {
            assert_eq!(direction, None);
            assert_eq!(condition, vec![Rat::zero(), Rat::from_integer(1.into())]);
            assert!(residual.iter().any(|x| !x.is_zero()));
        }
        other => panic!("{other:?}"),
    }
    assert_eq!(
        compatible(read.supported_conditions),
        (vec![Rat::from_integer(1.into()); 2], vec![])
    );
}
