use super::super::contact_tests::{calibrate, current, points, world};
use super::*;
use crate::embedding_fiber::ResidentReadout;

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

/// Host/device parity (condition-image kernel): every joint direction satisfies the exact complex
/// product law of the rational source, and refinement returns the exact rational condition.
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
