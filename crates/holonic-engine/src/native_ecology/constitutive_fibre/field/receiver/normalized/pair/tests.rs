use super::*;
use crate::embedding_fiber::ResidentReadout;
use crate::resident_section::ResidentSectionRest;
use num_traits::Signed;

fn balls<'c>(
    surface: &'c ResidentSurface<'c>,
    rows: &[(Vec<i128>, i128)],
    dimensions: usize,
) -> ResidentNormalEnclosureSection<'c> {
    let flat = rows
        .iter()
        .flat_map(|(v, r)| v.iter().copied().chain([*r]))
        .flat_map(|v| [v as i64, (v >> 64) as i64])
        .map(|v| (v, v))
        .collect();
    let section = surface
        .mount_section_rest(
            &ResidentSectionRest::found(
                rows.len(),
                2 * (dimensions + 1),
                ResidentGrain(0),
                64,
                flat,
            )
            .unwrap(),
        )
        .unwrap();
    ResidentNormalEnclosureSection::from_resident(
        surface,
        section,
        rows.len(),
        dimensions,
        ResidentGrain(16),
    )
    .unwrap()
}
fn point(re: i64, im: i64, den: i64) -> ExactComplexWaveCurrent {
    ExactComplexWaveCurrent::new(
        Rat::new(re.into(), den.into()),
        Rat::new(im.into(), den.into()),
    )
}

#[test]
#[ignore = "requires CUDA; distinct geometric and value charts with complete adjoint"]
fn pair_chart_and_value_covectors_are_distinct_and_complete() {
    let device = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&device).unwrap();
    let u = 1i128 << 16;
    for (radius, enclosure) in [
        (0, NativeEnclosurePropagation::ComponentIntervals),
        (u / 256, NativeEnclosurePropagation::ComponentIntervals),
        (0, NativeEnclosurePropagation::JointBall),
        (u / 256, NativeEnclosurePropagation::JointBall),
    ] {
        let query = Rc::new(balls(&surface, &[(vec![0, 0, 5 * u, 0], radius)], 4));
        let neighbors = Rc::new(balls(
            &surface,
            &[
                (vec![-u, 0, 5 * u, 0], radius),
                (vec![u, 0, 5 * u, 0], radius),
            ],
            4,
        ));
        let values = Rc::new(balls(
            &surface,
            &[(vec![u, 0], radius), (vec![3 * u, 0], radius)],
            2,
        ));
        let pair = query
            .pair_quadrance_participation_with_enclosure(
                neighbors,
                values,
                2,
                Dyadic::ONE,
                SeriesAperture(40),
                enclosure,
            )
            .unwrap();
        assert!(
            pair.output()
                .row(0)
                .unwrap()
                .inspect()
                .unwrap()
                .contains(&[point(2, 0, 1)])
        );
        let gy = balls(&surface, &[(vec![u, 0], 0)], 2);
        let back = pair.pull_back(&gy, None).unwrap();
        assert!(
            back.query()
                .row(0)
                .unwrap()
                .inspect()
                .unwrap()
                .contains(&[point(1, 0, 1), point(0, 0, 1)])
        );
        for row in 0..2 {
            assert!(
                back.neighbors()
                    .row(row)
                    .unwrap()
                    .inspect()
                    .unwrap()
                    .contains(&[point(-1, 0, 2), point(0, 0, 1)])
            );
            assert!(
                back.values()
                    .row(row)
                    .unwrap()
                    .inspect()
                    .unwrap()
                    .contains(&[point(1, 0, 2)])
            );
        }
        // A receiving covector on p alone follows the same normalized producer.
        let zero = balls(&surface, &[(vec![0, 0], 0)], 2);
        let gp = balls(&surface, &[(vec![u, 0, 0, 0], 0)], 4);
        let gp_back = pair.pull_back(&zero, Some(&gp)).unwrap();
        assert!(
            gp_back
                .query()
                .row(0)
                .unwrap()
                .inspect()
                .unwrap()
                .contains(&[point(-1, 0, 2), point(0, 0, 1)])
        );
        assert!(
            gp_back
                .values()
                .row(0)
                .unwrap()
                .inspect()
                .unwrap()
                .contains(&[point(0, 0, 1)])
        );
    }
}

#[test]
#[ignore = "requires CUDA; axial difference changes pair weights and its geometric return"]
fn axial_quadrance_is_not_a_bilinear_unit_phase_score() {
    let device = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&device).unwrap();
    let u = 1i128 << 16;
    let query = Rc::new(balls(&surface, &[(vec![0, 0, 0, 0, 0, 0], 0)], 6));
    let neighbors = Rc::new(balls(
        &surface,
        &[(vec![u, 0, 0, 0, 0, 0], 0), (vec![u, 0, 0, 0, u, 0], 0)],
        6,
    ));
    let values = Rc::new(balls(&surface, &[(vec![u, 0], 0), (vec![0, 0], 0)], 2));
    let pair = query
        .pair_quadrance_participation(neighbors, values, 2, Dyadic::ONE, SeriesAperture(48))
        .unwrap();
    let logits = pair.logits().row(0).unwrap().inspect().unwrap();
    assert!(logits.contains(&[point(-1, 0, 2), point(-1, 0, 1)]));
    assert_eq!(logits.radius, Rat::zero());
    let output = pair.output().row(0).unwrap().inspect().unwrap();
    assert!(output.center[0].real.clone() - output.radius.clone() > Rat::new(1.into(), 2.into()));
    let gy = balls(&surface, &[(vec![u, 0], 0)], 2);
    let back = pair.pull_back(&gy, None).unwrap();
    let query = back.query().row(0).unwrap().inspect().unwrap();
    // Only the second neighbor carries axial offset, and its value is lower.
    assert!(query.center[2].real.clone() + query.radius.clone() < Rat::zero());
    assert!(query.center[0].real.clone().abs() <= query.radius);
}

#[test]
#[ignore = "requires CUDA; simplex mixing transports a common value ball without coordinate inflation"]
fn joint_pair_simplex_transports_a_common_ball_once() {
    let device = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&device).unwrap();
    let u = 1i128 << 16;
    let query = Rc::new(balls(&surface, &[(vec![0, 0], u / 8)], 2));
    let neighbors = Rc::new(balls(
        &surface,
        &[(vec![-u, 0], u / 8), (vec![u, 0], u / 8)],
        2,
    ));
    let values = Rc::new(balls(
        &surface,
        &[
            (vec![u, 2 * u, -u, 0], u / 16),
            (vec![u, 2 * u, -u, 0], u / 16),
        ],
        4,
    ));
    let expected = values.row(0).unwrap().inspect().unwrap();
    let joint = query
        .pair_quadrance_participation_with_enclosure(
            neighbors,
            values,
            2,
            Dyadic::ONE,
            SeriesAperture(40),
            NativeEnclosurePropagation::JointBall,
        )
        .unwrap();
    assert_eq!(joint.output().row(0).unwrap().inspect().unwrap(), expected);
    // The different uncertain geometry can only change simplex weights, not this ball.
    assert!(
        joint
            .participation()
            .row(0)
            .unwrap()
            .inspect()
            .unwrap()
            .radius
            > Rat::from_integer(0.into())
    );
}

#[test]
#[ignore = "requires CUDA; common receiver terms are a null direction of the normalized geometric return"]
fn joint_pair_constant_values_have_zero_geometric_return() {
    let device = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&device).unwrap();
    let u = 1i128 << 16;
    for count in [1, 2] {
        let query = Rc::new(balls(&surface, &[(vec![0, 0], u / 8)], 2));
        let neighbors = Rc::new(balls(&surface, &vec![(vec![u, 0], u / 8); count], 2));
        let values = Rc::new(balls(&surface, &vec![(vec![u, 2 * u, -u, 0], 0); count], 4));
        let joint = query
            .pair_quadrance_participation_with_enclosure(
                neighbors,
                values,
                count,
                Dyadic::ONE,
                SeriesAperture(40),
                NativeEnclosurePropagation::JointBall,
            )
            .unwrap();
        let gy = balls(&surface, &[(vec![2 * u, u, -u, u], u / 16)], 4);
        let returned = joint.pull_back(&gy, None).unwrap();
        for reading in returned
            .query()
            .inspect_rows()
            .unwrap()
            .into_iter()
            .chain(returned.neighbors().inspect_rows().unwrap())
        {
            assert_eq!(reading.radius, Rat::from_integer(0.into()));
            assert!(
                reading
                    .center
                    .iter()
                    .all(|z| z.real == Rat::from_integer(0.into())
                        && z.imaginary == Rat::from_integer(0.into()))
            );
        }
        if count == 1 {
            assert_eq!(
                returned.values().row(0).unwrap().inspect().unwrap(),
                gy.row(0).unwrap().inspect().unwrap()
            );
        }
    }
}

/// **Plan phase 7: the pair participation is an exterior-drive receiver element.** The declaration
/// reads only carried extents: the logits, participation and drive are the same before and after
/// it and the delivered-power enclosure, and the enclosure is the exact `⟨e_D, y⟩` bound of the
/// returned ball (`Holon/Law.lean::exterior_drive_balance`).
#[test]
#[ignore = "requires CUDA; the receiver declaration leaves the resident pair return unchanged"]
fn pair_receiver_element_declares_its_drive_without_changing_the_return() {
    use holonic_core::law::receiver::ReceiverPower;
    let device = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&device).unwrap();
    let u = 1i128 << 16;
    let query = Rc::new(balls(&surface, &[(vec![0, 0], u / 8)], 2));
    let neighbors = Rc::new(balls(
        &surface,
        &[(vec![-u, 0], u / 8), (vec![u, 0], u / 8)],
        2,
    ));
    let values = Rc::new(balls(
        &surface,
        &[
            (vec![u, 2 * u, -u, 0], u / 16),
            (vec![u, 2 * u, -u, 0], u / 16),
        ],
        4,
    ));
    let pair = query
        .pair_quadrance_participation_with_enclosure(
            neighbors,
            values,
            2,
            Dyadic::ONE,
            SeriesAperture(40),
            NativeEnclosurePropagation::JointBall,
        )
        .unwrap();
    let read = |pair: &NativePairParticipation<'_>| {
        (
            pair.logits().inspect_rows().unwrap(),
            pair.participation().inspect_rows().unwrap(),
            pair.output().inspect_rows().unwrap(),
        )
    };
    let before = read(&pair);
    let element = pair.receiver_element();
    assert_eq!(element.read_ports(), 2 + 4);
    assert_eq!(
        element.power(),
        &ReceiverPower::ExteriorDrive { drive_ports: 4 }
    );
    assert!(!element.is_passive());
    let one = Rat::from_integer(1.into());
    let zero = Rat::zero();
    let delivered = pair
        .delivered_power(&[one.clone(), zero.clone(), zero, one])
        .unwrap();
    // y is the common value ball (1, 2, −1, 0) with radius 1/16; ⟨e_D, centre⟩ = 1, ‖e_D‖₁ r = 1/8.
    assert_eq!(delivered.lower, Rat::new(7.into(), 8.into()));
    assert_eq!(delivered.upper, Rat::new(9.into(), 8.into()));
    assert!(pair.delivered_power(&[Rat::zero()]).is_err());
    assert_eq!(read(&pair), before);
    let gy = balls(&surface, &[(vec![u, 0, 0, 0], 0)], 4);
    let back = pair.pull_back(&gy, None).unwrap();
    let adjoint = back.receiver_element();
    assert_eq!(adjoint.power(), &ReceiverPower::Pullback);
    assert_eq!(adjoint.read_ports(), 2 + 4 + 8);
}
