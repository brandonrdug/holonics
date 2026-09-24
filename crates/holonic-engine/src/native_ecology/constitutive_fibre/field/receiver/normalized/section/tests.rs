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
