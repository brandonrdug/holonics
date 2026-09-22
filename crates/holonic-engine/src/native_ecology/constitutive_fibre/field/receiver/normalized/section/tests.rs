use super::*;
use crate::embedding_fiber::ResidentReadout;
use crate::exact_linear::ExactRatMatrix;
use crate::exponentiated_ratio::NormalizedKernel;
use crate::resident_section::ResidentSectionRest;

const GRAIN: u32 = 72;
const UNIT: i128 = 1i128 << GRAIN;

fn words(values: &[i128]) -> Vec<(i64, i64)> {
    values
        .iter()
        .flat_map(|v| [*v as i64, (*v >> 64) as i64])
        .map(|v| (v, v))
        .collect()
}

/// Mount a typed enclosure section: one row per region, its `2*nodes` real coordinates and its
/// common outward radius. This is the operand chart `preview_field_rows` already returns.
fn balls<'c>(
    surface: &'c ResidentSurface<'c>,
    rows: &[(Vec<i128>, i128)],
    components: usize,
) -> ResidentNormalEnclosureSection<'c> {
    let flat: Vec<i128> = rows
        .iter()
        .flat_map(|(values, radius)| {
            assert_eq!(values.len(), components);
            values.iter().copied().chain([*radius])
        })
        .collect();
    let section = surface
        .mount_section_rest(
            &ResidentSectionRest::found(
                rows.len(),
                2 * (components + 1),
                ResidentGrain(0),
                64,
                words(&flat),
            )
            .unwrap(),
        )
        .unwrap();
    ResidentNormalEnclosureSection::from_resident(
        surface,
        section,
        rows.len(),
        components,
        ResidentGrain(GRAIN),
    )
    .unwrap()
}

fn read_wides<'c>(surface: &ResidentSurface<'c>, section: &ResidentSection<'c>) -> Vec<i128> {
    material_transport::wides(&surface.detach_section(section, 64).unwrap().intervals).unwrap()
}

/// The single-occurrence owner on one row, through its own recorder and its own operand layout:
/// the prediction ball first, the observed ball after the report's three leading balls.
fn single_row_report<'c>(
    surface: &'c ResidentSurface<'c>,
    prediction: &[i128],
    prediction_radius: i128,
    observation: &[i128],
    observation_radius: i128,
    group_width: usize,
    packet: bool,
) -> Vec<i128> {
    let nodes = prediction.len() / 2;
    let mount = |values: Vec<i128>| {
        let w = words(&values);
        surface
            .mount_section_rest(
                &ResidentSectionRest::found(1, w.len(), ResidentGrain(0), 64, w).unwrap(),
            )
            .unwrap()
    };
    let predicted = mount(
        prediction
            .iter()
            .copied()
            .chain([prediction_radius])
            .collect(),
    );
    let observed = mount(
        std::iter::repeat_n(0, 2 * (2 * nodes + 1))
            .chain(observation.iter().copied())
            .chain([observation_radius])
            .collect(),
    );
    let output = surface
        .fresh_section(1, 20 * nodes, ResidentGrain(0))
        .unwrap();
    let mut passage = surface.begin_passage(&[vec![]]).unwrap();
    {
        let lane = passage.open(0, &[]).unwrap();
        surface
            .record_field_normalized_receiver(
                &lane,
                &predicted,
                &observed,
                nodes,
                group_width,
                GRAIN,
                SeriesAperture(32),
                packet,
                &output,
            )
            .unwrap();
    }
    passage.close(0, &output, 64).unwrap();
    let receipt = passage.finish().unwrap().launch().unwrap();
    assert!(receipt.obstruction.is_empty(), "{:?}", receipt.obstruction);
    read_wides(surface, &output)
}

fn rat(value: i64) -> Rat {
    Rat::from_integer(value.into())
}

fn matrix(rows: &[&[i64]]) -> ExactRatMatrix {
    ExactRatMatrix::new(
        rows.iter()
            .map(|r| r.iter().copied().map(rat).collect())
            .collect(),
    )
    .unwrap()
}

/// The values whose normalized transport is the face itself: `a I = a`.
fn identity(n: usize) -> ExactRatMatrix {
    ExactRatMatrix::new(
        (0..n)
            .map(|i| {
                (0..n)
                    .map(|j| if i == j { Rat::one() } else { Rat::zero() })
                    .collect()
            })
            .collect(),
    )
    .unwrap()
}

fn pairing(a: &ExactRatMatrix, b: &ExactRatMatrix) -> Rat {
    a.entries()
        .iter()
        .zip(b.entries())
        .map(|(a, b)| a * b)
        .sum()
}

#[test]
#[ignore = "requires CUDA; the row-sectioned receiver against the single-occurrence owner"]
fn row_sectioned_receiver_agrees_with_the_single_row_owner() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    // Four complex coordinates a row, two declared groups of two.
    let predicted: Vec<(Vec<i128>, i128)> = vec![
        (
            vec![0, 3 * UNIT, UNIT, -2 * UNIT, 5 * UNIT, 0, -UNIT, UNIT],
            0,
        ),
        (
            vec![2 * UNIT, 0, 2 * UNIT, UNIT, -4 * UNIT, 7 * UNIT, 0, 0],
            0,
        ),
        (
            vec![
                -3 * UNIT,
                UNIT,
                6 * UNIT,
                0,
                UNIT,
                -UNIT,
                2 * UNIT,
                3 * UNIT,
            ],
            0,
        ),
    ];
    let observed: Vec<(Vec<i128>, i128)> = vec![
        (vec![UNIT, 0, 0, 0, 2 * UNIT, UNIT, 3 * UNIT, 0], 0),
        (vec![0, UNIT, -UNIT, 0, UNIT, 0, 4 * UNIT, -2 * UNIT], 0),
        (vec![5 * UNIT, 0, UNIT, UNIT, 0, 0, -2 * UNIT, UNIT], 0),
    ];
    let prediction = balls(&surface, &predicted, 8);
    let observation = balls(&surface, &observed, 8);
    let face = prediction
        .normalized_section_return(
            &observation,
            2,
            SeriesAperture(32),
            NativeNormalizedFaceMeasure::ExponentialPotential,
        )
        .unwrap();
    assert_eq!(face.rows(), 3);
    assert_eq!(face.nodes(), 4);
    assert!(face.compared());
    let rows = face.inspect().unwrap();
    assert_eq!(rows.len(), 3);
    for (row, reading) in rows.iter().enumerate() {
        assert_eq!(reading.source, row);
        assert_eq!(reading.receiving, row);
        let owner = single_row_report(
            &surface,
            &predicted[row].0,
            predicted[row].1,
            &observed[row].0,
            observed[row].1,
            2,
            false,
        );
        let scale = num_bigint::BigInt::one() << GRAIN;
        let expect = |offset: usize| -> Vec<ExactInterval> {
            (0..4)
                .map(|i| {
                    ExactInterval::new(
                        Rat::new(owner[10 * i + offset].into(), scale.clone()),
                        Rat::new(owner[10 * i + offset + 1].into(), scale.clone()),
                    )
                    .unwrap()
                })
                .collect()
        };
        assert_eq!(reading.prediction, expect(0));
        assert_eq!(reading.observation, expect(2));
        assert_eq!(reading.returned_difference, expect(4));
        assert_eq!(reading.potential_pullback, expect(6));
        assert_eq!(reading.centered_difference, expect(8));
    }
    // The participation is also returned as an operand of the source's own chart: the face in
    // each real coordinate, exactly zero in each imaginary one.
    let operand = read_wides(&surface, face.participation().resident_section());
    assert_eq!(operand.len(), 3 * 9);
    for (row, reading) in rows.iter().enumerate() {
        let at = 9 * row;
        for (j, p) in reading.prediction.iter().enumerate() {
            let centre = Rat::new(
                operand[at + 2 * j].into(),
                num_bigint::BigInt::one() << GRAIN,
            );
            let radius = Rat::new(operand[at + 8].into(), num_bigint::BigInt::one() << GRAIN);
            assert_eq!(
                operand[at + 2 * j + 1],
                0,
                "imaginary coordinate is exactly zero"
            );
            assert!(&centre - &radius <= p.lower && p.upper <= &centre + &radius);
        }
    }
}

#[test]
#[ignore = "requires CUDA; exact rational control against NormalizedKernel, with its duality"]
fn row_sectioned_face_and_pullback_agree_with_the_normalized_kernel() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    // A packet face is exactly rational: squared moduli 1, 4, 9 and 2 over the group total 16.
    // Its exact kernel is that same mass, so NormalizedKernel reproduces the face without a
    // logarithm. The exponential face cannot supply a non-uniform exact control: only a common
    // potential returns a dyadic face there.
    let mass: [i64; 4] = [1, 4, 9, 2];
    let amplitudes = vec![UNIT, 0, 2 * UNIT, 0, 3 * UNIT, 0, UNIT, UNIT];
    let section = balls(&surface, &[(amplitudes.clone(), 0), (amplitudes, 0)], 8);
    let face = section
        .normalized_participation(
            4,
            SeriesAperture(32),
            NativeNormalizedFaceMeasure::PacketModulus,
        )
        .unwrap();
    assert!(!face.compared());
    assert!(face.inspect().is_err(), "no comparison face was taken");
    let kernel = NormalizedKernel::new(matrix(&[&mass])).unwrap();
    let exact = kernel.probabilities().unwrap();
    for row in face.read_participation().unwrap() {
        for (j, value) in row.iter().enumerate() {
            assert_eq!(
                value,
                &ExactInterval::point(exact.get(0, j).unwrap().clone())
            );
        }
    }
    // The covector on the normalized face, returned to the pre-normalization potentials.
    let covector_values: [i64; 4] = [2, -1, 3, 5];
    let covector = balls(
        &surface,
        &[
            (vec![2 * UNIT, 0, -UNIT, 0, 3 * UNIT, 0, 5 * UNIT, 0], 0),
            (vec![2 * UNIT, 0, -UNIT, 0, 3 * UNIT, 0, 5 * UNIT, 0], 0),
        ],
        8,
    );
    let returned = face.pull_back(&covector).unwrap();
    let (ds, _) = kernel
        .pullback(&identity(4), &matrix(&[&covector_values]))
        .unwrap();
    let readings = returned.inspect().unwrap();
    assert_eq!(readings.len(), 2);
    for reading in &readings {
        for (j, value) in reading.potential_covector.iter().enumerate() {
            assert_eq!(value, &ExactInterval::point(ds.get(0, j).unwrap().clone()));
        }
    }
    // <dY, g> = <ds, J_p g>: the device covector is the right-hand operand of the duality.
    let potential_delta = matrix(&[&[7, -3, 1, 4]]);
    let tangent = kernel
        .differential(
            &identity(4),
            &potential_delta,
            &ExactRatMatrix::new(vec![vec![Rat::zero(); 4]; 4]).unwrap(),
        )
        .unwrap();
    let device = ExactRatMatrix::new(vec![
        readings[0]
            .potential_covector
            .iter()
            .map(|v| {
                assert_eq!(v.lower, v.upper);
                v.lower.clone()
            })
            .collect(),
    ])
    .unwrap();
    assert_eq!(
        pairing(&matrix(&[&covector_values]), &tangent),
        pairing(&potential_delta, &device)
    );
    // The face has no imaginary dependence, so its returned covector has exactly none.
    let operand = read_wides(&surface, returned.potentials().resident_section());
    for row in 0..2 {
        for j in 0..4 {
            assert_eq!(operand[9 * row + 2 * j + 1], 0);
        }
        assert_eq!(
            operand[9 * row + 8],
            0,
            "an exact covector returns an exact covector"
        );
    }
}

#[test]
#[ignore = "requires CUDA; the declared gauge of every row and its retained open radii"]
fn row_sectioned_face_keeps_its_gauge_and_its_radii() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let base = vec![
        (
            vec![0, 3 * UNIT, UNIT, -2 * UNIT, 5 * UNIT, 0, -UNIT, UNIT],
            0,
        ),
        (
            vec![2 * UNIT, 0, 2 * UNIT, UNIT, -4 * UNIT, 7 * UNIT, 0, 0],
            0,
        ),
    ];
    // A common additive shift of each declared group, different per group and per row.
    let shifts: [[i128; 2]; 2] = [[11 * UNIT, -4 * UNIT], [-9 * UNIT, 6 * UNIT]];
    let shifted: Vec<(Vec<i128>, i128)> = base
        .iter()
        .enumerate()
        .map(|(row, (values, radius))| {
            let moved = values
                .iter()
                .enumerate()
                .map(|(k, v)| {
                    if k % 2 == 0 {
                        v + shifts[row][k / 4]
                    } else {
                        *v
                    }
                })
                .collect();
            (moved, *radius)
        })
        .collect();
    let measure = NativeNormalizedFaceMeasure::ExponentialPotential;
    let plain = balls(&surface, &base, 8)
        .normalized_participation(2, SeriesAperture(32), measure)
        .unwrap()
        .read_participation()
        .unwrap();
    let moved = balls(&surface, &shifted, 8)
        .normalized_participation(2, SeriesAperture(32), measure)
        .unwrap()
        .read_participation()
        .unwrap();
    assert_eq!(plain, moved, "a common group shift is exactly invisible");
    // A source ball with a nonzero radius returns an open face and a nonzero operand radius.
    let open = balls(&surface, &[(vec![0, 0, 0, 0], 1i128 << 80)], 4)
        .normalized_participation(2, SeriesAperture(32), measure)
        .unwrap();
    for row in open.read_participation().unwrap() {
        for value in row {
            assert!(
                value.lower < value.upper,
                "the open ball is not sealed to a point"
            );
        }
    }
    let operand = read_wides(&surface, open.participation().resident_section());
    assert!(
        operand[4] > 0,
        "a retained source radius returns a retained radius"
    );
}

#[test]
#[ignore = "requires CUDA; typed refusal of malformed groups, apertures and operand shapes"]
fn row_sectioned_receiver_refuses_malformed_declarations() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let measure = NativeNormalizedFaceMeasure::ExponentialPotential;
    let rows = vec![(vec![UNIT, 0, 0, UNIT, 2 * UNIT, 0], 0); 2];
    let section = balls(&surface, &rows, 6);
    let malformed = |group_width, terms| {
        section
            .normalized_participation(group_width, terms, measure)
            .is_err()
    };
    assert!(
        malformed(0, SeriesAperture(32)),
        "an empty group is not a declaration"
    );
    assert!(
        malformed(2, SeriesAperture(32)),
        "2 does not divide 3 coordinates"
    );
    assert!(malformed(3, SeriesAperture(0)), "an empty series aperture");
    assert!(
        malformed(3, SeriesAperture(u32::MAX)),
        "an unbounded series aperture"
    );
    assert!(
        section
            .normalized_participation(3, SeriesAperture(32), measure)
            .is_ok()
    );
    // A comparison operand must present the same rows, coordinates and grain.
    let wider = balls(&surface, &[(vec![UNIT, 0, 0, UNIT, 2 * UNIT, 0], 0)], 6);
    assert!(
        section
            .normalized_section_return(&wider, 3, SeriesAperture(32), measure)
            .is_err()
    );
    let narrow = balls(&surface, &vec![(vec![UNIT, 0, 0, UNIT], 0); 2], 4);
    assert!(
        section
            .normalized_section_return(&narrow, 3, SeriesAperture(32), measure)
            .is_err()
    );
    // A covector must be declared on the face it is returned through.
    let face = section
        .normalized_participation(3, SeriesAperture(32), measure)
        .unwrap();
    assert!(face.pull_back(&narrow).is_err());
    assert!(face.pull_back(&wider).is_err());
    assert!(face.pull_back(&section).is_ok());
    assert!(
        face.returned_difference().is_err(),
        "no comparison face was taken"
    );
    assert!(face.potential_return().is_err());
}

#[test]
#[ignore = "requires CUDA; the complex receiving potential's ratio return, exact on a common face"]
fn ratio_return_carries_the_phase_face_and_the_gap_weighted_covector() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    // One group of four classes with a common real potential, so p = 1/4 exactly (the only
    // exact exponential control), and distinct imaginary potentials: Im s = (2, -1, 6, 0).
    let produced = balls(
        &surface,
        &[(
            vec![UNIT, 2 * UNIT, UNIT, -UNIT, UNIT, 6 * UNIT, UNIT, 0],
            0,
        )],
        8,
    );
    // The observed packet: the one-hot target class 2.
    let observed = balls(&surface, &[(vec![0, 0, 0, 0, UNIT, 0, 0, 0], 0)], 8);
    // Target Holon potentials: Im s^T_2 = 4, so phi^T_2 = 2 against phi^H_2 = 3.
    let target_at = |im2: i128| {
        balls(
            &surface,
            &[(vec![0, 5 * UNIT, 0, 0, 0, im2, 0, -3 * UNIT], 0)],
            8,
        )
    };
    let target = target_at(4 * UNIT);
    let face = produced
        .normalized_ratio_return(&observed, &target, &[0], 4, SeriesAperture(32))
        .unwrap();
    let quarter = Rat::new(1.into(), 4.into());
    let half = Rat::new(1.into(), 2.into());
    let reading = face.inspect().unwrap().remove(0);
    for (c, p) in reading.prediction.iter().enumerate() {
        assert_eq!(p, &ExactInterval::point(quarter.clone()), "class {c}");
    }
    // phi = Im s / 2, exactly, for both Holons.
    let phase = face.read_phase().unwrap().remove(0);
    let expected_phase = [rat(1), Rat::new((-1).into(), 2.into()), rat(3), Rat::zero()];
    for (c, value) in phase.iter().enumerate() {
        assert_eq!(
            value,
            &ExactInterval::point(expected_phase[c].clone()),
            "phase {c}"
        );
    }
    let target_phase = NativeNormalizedSection::read_phase_ball(face.target_phase().unwrap())
        .unwrap()
        .remove(0);
    assert_eq!(target_phase[2], ExactInterval::point(rat(2)));
    // Exact reference: Re slot q - p; Im slot (1/2) q Delta with Delta_2 = 2 - 3 = -1; zero on
    // the unsupported classes whatever their phase gap.
    let covector = |face: &NativeNormalizedSection<'_>| {
        face.ratio_covector()
            .unwrap()
            .row(0)
            .unwrap()
            .inspect()
            .unwrap()
    };
    let value = covector(&face);
    assert_eq!(value.radius, Rat::zero());
    for (c, v) in value.center.iter().enumerate() {
        let q = if c == 2 { Rat::one() } else { Rat::zero() };
        assert_eq!(v.real, &q - &quarter, "real covector of class {c}");
        let phase_part = if c == 2 { -half.clone() } else { Rat::zero() };
        assert_eq!(v.imaginary, phase_part, "phase covector of class {c}");
    }
    let difference = face
        .returned_difference()
        .unwrap()
        .row(0)
        .unwrap()
        .inspect()
        .unwrap();
    for (a, b) in value.center.iter().zip(&difference.center) {
        assert_eq!(a.real, b.real);
    }
    // Agreeing phases: the phase covector vanishes.
    let agree = produced
        .normalized_ratio_return(&observed, &target_at(6 * UNIT), &[0], 4, SeriesAperture(32))
        .unwrap();
    assert!(
        covector(&agree)
            .center
            .iter()
            .all(|v| v.imaginary.is_zero())
    );
    // The gap reverses: phi^T_2 = 4 gives Delta_2 = +1 and the covector +1/2.
    let reversed = produced
        .normalized_ratio_return(&observed, &target_at(8 * UNIT), &[0], 4, SeriesAperture(32))
        .unwrap();
    assert_eq!(covector(&reversed).center[2].imaginary, half);
    // A winding branch n = 1 adds 2 pi to the gap: (1/2)(2 pi - 1), enclosed outward.
    let wound = produced
        .normalized_ratio_return(&observed, &target, &[1], 4, SeriesAperture(32))
        .unwrap();
    let wound = covector(&wound);
    let pi = relational_geometry::exact_analysis::pi_interval(GRAIN + 16);
    let lower = (&pi.lower * rat(2) - Rat::one()) * &half;
    let upper = (&pi.upper * rat(2) - Rat::one()) * &half;
    let centre = &wound.center[2].imaginary;
    assert!(centre - &wound.radius <= lower && upper <= centre + &wound.radius);
    assert!(wound.radius > Rat::zero() && wound.radius < Rat::new(1.into(), (1u64 << 40).into()));
    // Exact reference for the magnitude part: the principal log of the real amplitude ratio 2.
    let config = relational_geometry::exact_analysis::ExactSeriesConfig::default();
    let log_ratio =
        relational_geometry::exact_analysis::complex_log_point(&rat(2), &Rat::zero(), &config)
            .unwrap();
    let half_log_q_over_p = relational_geometry::exact_analysis::complex_log_point(
        &(Rat::one() / &quarter),
        &Rat::zero(),
        &config,
    )
    .unwrap()
    .re
    .scale(&half);
    assert!(
        log_ratio.re.lower <= half_log_q_over_p.upper
            && half_log_q_over_p.lower <= log_ratio.re.upper
    );
    // An open produced ball returns an open phase and an open covector radius.
    let open = balls(&surface, &[(vec![0; 8], 1i128 << 60)], 8)
        .normalized_ratio_return(&observed, &target, &[0], 4, SeriesAperture(32))
        .unwrap();
    assert!(
        open.read_phase().unwrap()[0]
            .iter()
            .all(|v| v.lower < v.upper)
    );
    assert!(covector(&open).radius > Rat::zero());
    // Shapes: the target and branch declare the same rows.
    assert!(
        produced
            .normalized_ratio_return(&observed, &target, &[0, 0], 4, SeriesAperture(32))
            .is_err()
    );
}
