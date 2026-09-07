use super::super::contact_tests::{calibrate, current, observe, phase, points, value, world};
use super::*;
use crate::embedding_fiber::ResidentReadout;
use num_traits::Zero;

#[cfg(target_os = "macos")]
#[test]
#[ignore = "requires Metal; preimage scratch refusal precedes derived allocations"]
fn metal_preimage_admits_its_actual_carrier_before_allocating_evidence() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let available = s.declaration().max_sectiond_bytes as usize;
    // For one source and one target complex coordinate the preimage uses 12 + 16*c
    // wide carriers. Choose the first condition population beyond this Metal aperture,
    // still within the former erroneous sixteen-byte admission and the original basis.
    let conditions = (available / 20 - 12) / 16 + 1;
    assert!((12 + 16 * conditions) * 16 <= available);
    let body = ResidentConstitutiveFibre::found_bilinear_contact(&s, 1, conditions, 1).unwrap();
    let point = points(&s, &[1, 0]);
    let before = s.census();
    let result = body.read_condition_preimage(current(&point), current(&point));
    match result {
        Err(ConstitutiveFibreError::ScratchAperture {
            required,
            available,
        }) => {
            assert!(required > available as usize);
        }
        _ => panic!("expected actual Metal scratch refusal"),
    }
    assert_eq!(s.census(), before);
    assert_eq!(body.occurrences(), 0);
}

fn compatible(p: &ResidentConditionPreimage<'_>) -> (Vec<Rat>, Vec<Vec<Rat>>) {
    match p.inspect().unwrap() {
        ConditionPreimageReading::Compatible {
            particular,
            directions,
        } => (particular, directions),
        other => panic!("expected compatible conditions: {other:?}"),
    }
}

#[test]
#[ignore = "requires CUDA; an unprovided native phase is inferred from an actual later return"]
fn a_condition_preimage_from_native_observation_drives_a_new_current() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let mut w = world(&s);
    let mut body = ResidentConstitutiveFibre::found_bilinear_contact(&s, 1, 1, 1).unwrap();
    calibrate(&s, &mut body, &mut w, None);
    let hidden = phase(3, 4, 5);
    let actual = observe(&mut w, phase(2, 3, 1), hidden);
    let x = points(&s, &[2, 3]);
    let y = points(
        &s,
        &NativePhaseCurrent::from_current(&actual).unwrap().words(),
    );
    let before = body.census();
    let cut = body.occurrences();
    let preimage = body
        .read_condition_preimage(
            current(&x),
            ResidentConstitutiveCurrent::rational(&y).unwrap(),
        )
        .unwrap();
    assert_eq!(body.census().section_read_outs, before.section_read_outs);
    assert_eq!(body.census().ingress_octets, before.ingress_octets);
    assert_eq!(body.occurrences(), cut);
    let next = points(&s, &[7, -2]);
    let before = body.census();
    let predicted = body
        .advance_bilinear_contact(current(&next), preimage.current(), None)
        .unwrap();
    assert_eq!(body.census().section_read_outs, before.section_read_outs);
    // The hidden condition was never supplied to the learner. This second observation follows
    // prediction; its current is not developmental material for the preceding inference.
    let later = observe(&mut w, phase(7, -2, 1), hidden);
    assert_eq!(value(&predicted), later);
    let (condition, directions) = compatible(&preimage);
    assert!(directions.is_empty());
    assert_eq!(
        condition,
        vec![Rat::new(3.into(), 5.into()), Rat::new(4.into(), 5.into())]
    );
    assert_eq!(preimage.relation_cut(), cut);
}

#[test]
#[ignore = "requires CUDA; zero source retains free conditions and an incompatible return has no represented preimage"]
fn free_and_outside_preimages_are_distinct_and_neither_selects_a_condition() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let mut w = world(&s);
    let mut body = ResidentConstitutiveFibre::found_bilinear_contact(&s, 1, 1, 1).unwrap();
    calibrate(&s, &mut body, &mut w, None);
    let zero = points(&s, &[0, 0]);
    let one = points(&s, &[1, 0]);
    let before = body.inspect_relation().unwrap();
    let cut = body.occurrences();
    let free = body
        .read_condition_preimage(current(&zero), current(&zero))
        .unwrap();
    let (particular, directions) = compatible(&free);
    assert!(particular.iter().all(Zero::is_zero));
    assert_eq!(directions.len(), 2);
    assert!(
        body.advance_bilinear_contact(current(&one), free.current(), None)
            .is_err()
    );
    let outside = body
        .read_condition_preimage(current(&zero), current(&one))
        .unwrap();
    match outside.inspect().unwrap() {
        ConditionPreimageReading::OutsideRepresentedRelation { residual } => {
            assert!(residual.iter().any(|r| !r.is_zero()))
        }
        other => panic!("unexpected preimage: {other:?}"),
    }
    assert_eq!(body.inspect_relation().unwrap(), before);
    assert_eq!(body.occurrences(), cut);
}

#[test]
#[ignore = "requires CUDA; the original receiver's vertical fibre participates in condition inference"]
fn original_vertical_directions_are_quotiented_before_condition_constraints() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let mut w = world(&s);
    let mut body = ResidentConstitutiveFibre::found_bilinear_contact(&s, 1, 1, 1).unwrap();
    calibrate(&s, &mut body, &mut w, None);
    let zero = points(&s, &[0, 0]);
    let real = points(&s, &[1, 0]);
    let imaginary = points(&s, &[0, 1]);
    // This algebraic control widens the represented receiving fibre in the real direction.
    body.advance_bilinear_contact(current(&zero), current(&zero), Some(current(&real)))
        .unwrap();
    let observed = points(&s, &[3, 4]);
    let preimage = body
        .read_condition_preimage(current(&real), current(&observed))
        .unwrap();
    let original = preimage.inspect().unwrap();
    let (particular, directions) = compatible(&preimage);
    assert_eq!(particular, vec![Rat::zero(), Rat::from_integer(4.into())]);
    assert_eq!(
        directions,
        vec![vec![Rat::from_integer(1.into()), Rat::zero()]]
    );
    body.advance_bilinear_contact(current(&zero), current(&zero), Some(current(&imaginary)))
        .unwrap();
    assert_eq!(preimage.inspect().unwrap(), original);
    assert_eq!(
        compatible(
            &body
                .read_condition_preimage(current(&real), current(&observed))
                .unwrap()
        )
        .1
        .len(),
        2
    );
}

fn train_two_conditions<'c>(s: &'c ResidentSurface<'c>, body: &mut ResidentConstitutiveFibre<'c>) {
    // Independent exact algebra control for Gamma(s,c)=c0*s0+c1*s1. These supplied observation
    // rows test the general multiport preimage construction; they are not a production learner.
    for side in 0..2 {
        for coordinate in 0..4 {
            let mut x = [0; 4];
            let mut c = [0; 4];
            if side == 0 {
                x[coordinate] = 1;
            } else {
                c[coordinate] = 1;
            }
            let xs = points(s, &x);
            let cs = points(s, &c);
            let y = points(s, &[0, 0]);
            body.advance_bilinear_contact(current(&xs), current(&cs), Some(current(&y)))
                .unwrap();
        }
    }
    for left in 0..2 {
        for right in 0..2 {
            for imaginary in 0..2 {
                let mut x = [0; 4];
                let mut c = [0; 4];
                let mut y = [0; 2];
                x[2 * left + imaginary] = 1;
                c[2 * right] = 1;
                if left == right {
                    y[imaginary] = 1;
                }
                let xs = points(s, &x);
                let cs = points(s, &c);
                let ys = points(s, &y);
                body.advance_bilinear_contact(current(&xs), current(&cs), Some(current(&ys)))
                    .unwrap();
            }
        }
    }
}

#[test]
#[ignore = "requires CUDA; a multiple-condition preimage has a fixed receiver without unique conditions"]
fn partial_conditions_keep_a_fixed_receiver_and_complete_constraints() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let mut body = ResidentConstitutiveFibre::found_bilinear_contact(&s, 2, 2, 1).unwrap();
    train_two_conditions(&s, &mut body);
    let x = points(&s, &[-1, 0, 1, 0]);
    let y = points(&s, &[3, 4]);
    let preimage = body
        .read_condition_preimage(current(&x), current(&y))
        .unwrap();
    let (particular, directions) = compatible(&preimage);
    assert_eq!(&particular[2] - &particular[0], Rat::from_integer(3.into()));
    assert_eq!(&particular[3] - &particular[1], Rat::from_integer(4.into()));
    assert_eq!(directions.len(), 2);
    for v in &directions {
        assert_eq!(v[2], v[0]);
        assert_eq!(v[3], v[1]);
    }
    let face = preimage.read_differential_pairs(0, 1).unwrap();
    assert_eq!((face.positive, face.negative, face.unresolved), (1, 0, 0));
    assert_eq!(face.field_source, None);
    assert!(face.into_field_reading().is_err());
    let (graph, rhs) = preimage.inspect_constraints().unwrap();
    assert!(
        graph
            .intervals
            .iter()
            .chain(&rhs.intervals)
            .all(|(lo, hi)| lo == hi)
    );
    assert_eq!(graph.width, 22);
    assert_eq!(rhs.width, 19);
}

#[test]
#[ignore = "requires CUDA; invalid preimage operands and source charts leave learned standing unchanged"]
fn wrong_chart_foreign_surface_and_invalid_denominator_refuse_recoverably() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let other = ResidentSurface::on(&readout).unwrap();
    let linear = ResidentConstitutiveFibre::found(&s, 2, 2).unwrap();
    let x = points(&s, &[1, 0]);
    assert!(
        linear
            .read_condition_preimage(current(&x), current(&x))
            .is_err()
    );
    let mut w = world(&s);
    let mut body = ResidentConstitutiveFibre::found_bilinear_contact(&s, 1, 1, 1).unwrap();
    calibrate(&s, &mut body, &mut w, None);
    let before = body.inspect_relation().unwrap();
    let cut = body.occurrences();
    let foreign = points(&other, &[1, 0]);
    assert!(
        body.read_condition_preimage(current(&foreign), current(&x))
            .is_err()
    );
    let bad = points(&s, &[1, 0, 0]);
    assert!(
        body.read_condition_preimage(
            current(&x),
            ResidentConstitutiveCurrent::rational(&bad).unwrap()
        )
        .is_err()
    );
    let tiny = points(&s, &[1, 0, i64::MAX]);
    let huge = points(&s, &[i64::MAX, 0]);
    assert!(
        body.read_condition_preimage(
            ResidentConstitutiveCurrent::rational(&tiny).unwrap(),
            current(&huge)
        )
        .is_err()
    );
    assert_eq!(body.inspect_relation().unwrap(), before);
    assert_eq!(body.occurrences(), cut);
    assert!(
        compatible(
            &body
                .read_condition_preimage(current(&x), current(&x))
                .unwrap()
        )
        .1
        .is_empty()
    );
}

#[test]
#[ignore = "requires CUDA; the preimage retains the represented source domain of a partially known action"]
fn a_partial_original_relation_does_not_invent_missing_condition_directions() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let mut body = ResidentConstitutiveFibre::found_bilinear_contact(&s, 1, 1, 1).unwrap();
    let zero = points(&s, &[0, 0]);
    let one = points(&s, &[1, 0]);
    let two = points(&s, &[2, 0]);
    body.advance_bilinear_contact(current(&one), current(&one), Some(current(&one)))
        .unwrap();
    body.advance_bilinear_contact(current(&zero), current(&one), Some(current(&zero)))
        .unwrap();
    let inferred = body
        .read_condition_preimage(current(&two), current(&two))
        .unwrap();
    assert_eq!(
        compatible(&inferred),
        (vec![Rat::from_integer(1.into()), Rat::zero()], Vec::new())
    );
    let silent = body
        .read_condition_preimage(current(&zero), current(&zero))
        .unwrap();
    let (_, directions) = compatible(&silent);
    assert_eq!(
        directions,
        vec![vec![Rat::from_integer(1.into()), Rat::zero()]]
    );
    // No imaginary condition has entered this represented source domain. The test does not
    // declare such a condition physically impossible or constrain an unadmitted extension.
}
