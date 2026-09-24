use super::*;
use crate::embedding_fiber::ResidentReadout;
use crate::resident_section::ResidentSectionRest;

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

/// Pair-quadrance parity: on the symmetric two-neighbour chart the device output and its
/// query, neighbour, value and participation covectors contain the exact values of the
/// quadrance softmax and its adjoint, for both enclosure propagations.
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
