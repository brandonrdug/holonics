use super::*;
use crate::embedding_fiber::ResidentReadout;
use holonics::exact_linear::ExactRatMatrix;
use holonics::ratio::exponentiated::NormalizedKernel;
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

/// Normalized-receiver parity: the device face and its potential pullback equal the exact
/// `NormalizedKernel` probabilities and pullback, and satisfy `⟨dY, g⟩ = ⟨ds, J_p g⟩`.
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
    // Plan phase 7: the face is a zero-power reading and its return a pullback on the same ports.
    use holonics::law::receiver::ReceiverPower;
    assert_eq!(face.receiver_element().power(), &ReceiverPower::Reading);
    assert_eq!(returned.receiver_element().power(), &ReceiverPower::Pullback);
    assert_eq!(
        returned.receiver_element().read_ports(),
        face.receiver_element().read_ports()
    );
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

/// Law: the loss is the logarithm of the Holon ratio; its return carries the phase face and the
/// gap-weighted covector (ELEMENTARY_OBJECTS §9).
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
    let pi = holonics::geometry::pi_interval(GRAIN + 16);
    let lower = (&pi.lower * rat(2) - Rat::one()) * &half;
    let upper = (&pi.upper * rat(2) - Rat::one()) * &half;
    let centre = &wound.center[2].imaginary;
    assert!(centre - &wound.radius <= lower && upper <= centre + &wound.radius);
    assert!(wound.radius > Rat::zero() && wound.radius < Rat::new(1.into(), (1u64 << 40).into()));
    // Exact reference for the magnitude part: the principal log of the real amplitude ratio 2.
    let config = holonics::geometry::ExactSeriesConfig::default();
    let log_ratio =
        holonics::geometry::complex_log_point(&rat(2), &Rat::zero(), &config)
            .unwrap();
    let half_log_q_over_p = holonics::geometry::complex_log_point(
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
