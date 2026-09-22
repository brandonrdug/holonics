//! CUDA-scoped checks for rectangular declared-factor scale cotangents.

use super::*;
use crate::ExactRatMatrix;
use crate::embedding_fiber::ResidentReadout;
use crate::native_ecology::constitutive_fibre::{
    NativeConstitutiveField, NativeFieldContactOrigin, NativeFieldDeclaredIncidence,
    NativeJunctionSeed, NativePhaseCurrent, ResidentConstitutiveSection,
    ResidentNormalEnclosureSection,
};
use crate::resident_section::{
    ResidentGrain, ResidentSection, ResidentSectionRest, ResidentSurface,
};
use num_bigint::BigInt;
use num_traits::{Signed, Zero};
use relational_geometry::Rat;

fn packet<'c>(
    surface: &'c ResidentSurface<'c>,
    rows: usize,
    width: usize,
    values: Vec<i128>,
) -> ResidentSection<'c> {
    let words = values
        .into_iter()
        .flat_map(|value| [value as i64, (value >> 64) as i64].map(|word| (word, word)))
        .collect();
    surface
        .mount_section_rest(
            &ResidentSectionRest::found(rows, width, ResidentGrain(0), 64, words).unwrap(),
        )
        .unwrap()
}

fn current<'c>(
    surface: &'c ResidentSurface<'c>,
    values: &[i64],
    grain: ResidentGrain,
) -> ResidentNormalEnclosureSection<'c> {
    let raw = surface
        .mount_section_rest(
            &ResidentSectionRest::found(
                1,
                values.len(),
                ResidentGrain(0),
                64,
                values.iter().map(|value| (*value, *value)).collect(),
            )
            .unwrap(),
        )
        .unwrap();
    ResidentNormalEnclosureSection::from_points(
        ResidentConstitutiveSection::integers(&raw).unwrap(),
        grain,
    )
    .unwrap()
}

fn declared_field<'c>(
    surface: &'c ResidentSurface<'c>,
    grain: ResidentGrain,
    zero_last: bool,
    basis_radius: i128,
) -> NativeConstitutiveField<'c> {
    let seed = NativeJunctionSeed {
        incoming_admittance: 1,
        held_admittance: 1,
        incoming_transport: NativePhaseCurrent::unit(),
        initial_held: NativePhaseCurrent::zero(),
    };
    let mut field =
        NativeConstitutiveField::found_incident_source_only(surface, vec![seed], grain).unwrap();
    let scale = 1i128 << grain.0;
    // Six complex contact rows in two groups of three. The first fixture keeps both groups
    // genuinely complex; the structural-zero variant zeros only the final group.
    let coefficients = vec![
        (0usize, scale / 4, scale / 8),
        (1, scale / 4, -(scale / 8)),
        (2, scale / 8, scale / 4),
        (
            0,
            if zero_last { 0 } else { scale / 8 },
            if zero_last { 0 } else { scale / 16 },
        ),
        (
            1,
            if zero_last { 0 } else { scale / 16 },
            if zero_last { 0 } else { -(scale / 8) },
        ),
        (
            2,
            if zero_last { 0 } else { scale / 4 },
            if zero_last { 0 } else { scale / 8 },
        ),
    ];
    let columns: Vec<i128> = coefficients
        .iter()
        .map(|(column, _, _)| (2 * *column) as i128)
        .collect();
    let values: Vec<i128> = coefficients
        .iter()
        .flat_map(|(_, re, im)| [*re, *im])
        .collect();
    let mut transpose_rows = Vec::new();
    let mut transpose_values = Vec::new();
    for port in 0..3 {
        transpose_rows.extend([port, port + 3]);
        for row in [port, port + 3] {
            transpose_values.extend([coefficients[row].1, coefficients[row].2]);
        }
    }
    let incidence = NativeFieldDeclaredIncidence {
        row_offsets: packet(surface, 1, 14, vec![0, 1, 2, 3, 4, 5, 6]),
        columns: packet(
            surface,
            1,
            12,
            columns.into_iter().map(|v| v as i128).collect(),
        ),
        values: packet(surface, 1, 24, values.into_iter().map(i128::from).collect()),
        transpose_offsets: packet(surface, 1, 8, vec![0, 2, 4, 6]),
        transpose_rows: packet(
            surface,
            1,
            12,
            transpose_rows.into_iter().map(|v| v as i128).collect(),
        ),
        transpose_values: packet(surface, 1, 24, transpose_values),
        left: packet(surface, 1, 12, vec![0; 6]),
        right: packet(surface, 1, 24, vec![0; 12]),
        defects: packet(surface, 1, 2, vec![0]),
        rows: 6,
        boundary_components: 6,
        rank: 0,
        nonzeros: 6,
    };
    let b = packet(surface, 6, 4, vec![0; 12]);
    // One nonzero global basis radius exercises the complete enclosing return path.
    let bounds = packet(surface, 1, 4, vec![basis_radius, 0]);
    let origins = (0..6)
        .map(|column| NativeFieldContactOrigin::declared(column, 0, 0))
        .collect();
    field
        .register_declared_incidence(incidence, b, bounds, origins)
        .unwrap();
    field
}

fn dense_reference(
    coefficients: &[(usize, Rat, Rat)],
    input_a: &[Rat],
    input_b: &[Rat],
    covector: &[Rat],
) -> Vec<Rat> {
    let mut dr = vec![vec![Rat::zero(); 12]; 6];
    for (row, (column, re, im)) in coefficients.iter().enumerate() {
        dr[2 * *column][2 * row] = re.clone();
        dr[2 * *column][2 * row + 1] = -im.clone();
        dr[2 * *column + 1][2 * row] = im.clone();
        dr[2 * *column + 1][2 * row + 1] = re.clone();
    }
    let dr = ExactRatMatrix::new(dr).unwrap();
    let identity = ExactRatMatrix::identity(6).unwrap();
    let a = identity
        .add(&dr.multiply(&dr.transpose().unwrap()).unwrap())
        .unwrap();
    let rhs = input_a
        .iter()
        .zip(dr.apply(&input_b).unwrap())
        .map(|(a, b)| (a + b) * &Rat::from_integer(2.into()))
        .collect::<Vec<_>>();
    let v = a.inverse().unwrap().apply(&rhs).unwrap();
    let mut gradients = Vec::new();
    for group in 0..2 {
        let mut rows = vec![vec![Rat::zero(); 12]; 6];
        for (row, (column, re, im)) in coefficients.iter().enumerate() {
            if row / 3 != group {
                continue;
            }
            rows[2 * *column][2 * row] = re.clone();
            rows[2 * *column][2 * row + 1] = -im.clone();
            rows[2 * *column + 1][2 * row] = im.clone();
            rows[2 * *column + 1][2 * row + 1] = re.clone();
        }
        let ddr = ExactRatMatrix::new(rows).unwrap();
        let dv_rhs = ddr
            .apply(input_b)
            .unwrap()
            .iter()
            .map(|v| v * Rat::from_integer(2.into()))
            .collect::<Vec<_>>();
        let d_a = ddr
            .multiply(&dr.transpose().unwrap())
            .unwrap()
            .add(&dr.multiply(&ddr.transpose().unwrap()).unwrap())
            .unwrap();
        let correction = d_a.apply(&v).unwrap();
        let dv = a
            .inverse()
            .unwrap()
            .apply(
                &dv_rhs
                    .iter()
                    .zip(correction)
                    .map(|(a, b)| a - b)
                    .collect::<Vec<_>>(),
            )
            .unwrap();
        let d_out = dv
            .iter()
            .cloned()
            .chain(
                ddr.transpose()
                    .unwrap()
                    .apply(&v)
                    .unwrap()
                    .iter()
                    .zip(dr.transpose().unwrap().apply(&dv).unwrap())
                    .map(|(a, b)| a + b),
            )
            .collect::<Vec<_>>();
        gradients.push(covector.iter().zip(d_out).map(|(a, b)| a * b).sum());
    }
    gradients
}

#[test]
#[ignore = "requires CUDA; declared rectangular factor scale gradient and exact realified reference"]
fn declared_factor_scale_gradient_matches_two_group_reference() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let grain = ResidentGrain(32);
    let coefficients = vec![
        (
            0usize,
            Rat::new(1.into(), 4.into()),
            Rat::new(1.into(), 8.into()),
        ),
        (
            1,
            Rat::new(1.into(), 4.into()),
            Rat::new((-1).into(), 8.into()),
        ),
        (
            2,
            Rat::new(1.into(), 8.into()),
            Rat::new(1.into(), 4.into()),
        ),
        (
            0,
            Rat::new(1.into(), 8.into()),
            Rat::new(1.into(), 16.into()),
        ),
        (
            1,
            Rat::new(1.into(), 16.into()),
            Rat::new((-1).into(), 8.into()),
        ),
        (
            2,
            Rat::new(1.into(), 4.into()),
            Rat::new(1.into(), 8.into()),
        ),
    ];
    let mut field = declared_field(&surface, grain, false, 0);
    let source = field.read_current_source().unwrap();
    let input = current(
        &surface,
        &(1..=18).map(|value| value as i64).collect::<Vec<_>>(),
        grain,
    );
    let covector = current(
        &surface,
        &(1..=18).rev().map(|value| value as i64).collect::<Vec<_>>(),
        grain,
    );
    let action = source
        .action_matrix_free_auto(input.row(0).unwrap(), 128)
        .unwrap();
    let pullback = action
        .pullback_full_auto(covector.row(0).unwrap(), 128)
        .unwrap();
    let gradient = source.declared_factor_scale_gradient(&pullback, 3).unwrap();
    let rows = gradient.gradient().inspect_rows().unwrap();
    let input_a = (1..=6)
        .map(|value| Rat::from_integer(value.into()))
        .collect::<Vec<_>>();
    let input_b = (7..=18)
        .map(|value| Rat::from_integer(value.into()))
        .collect::<Vec<_>>();
    let covector_values = (1..=18)
        .rev()
        .map(|value| Rat::from_integer(value.into()))
        .collect::<Vec<_>>();
    let expected = dense_reference(&coefficients, &input_a, &input_b, &covector_values);
    for (row, wanted) in rows.iter().zip(expected.iter()) {
        let error = &row.center[0].real - wanted;
        assert!(
            error.abs() <= row.radius,
            "gradient {row:?} expected {wanted}"
        );
    }
}

#[test]
#[ignore = "requires CUDA; malformed declared factor grouping"]
fn declared_factor_scale_gradient_rejects_malformed_group_width() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let grain = ResidentGrain(32);
    let mut field = declared_field(&surface, grain, true, 1);
    let source = field.read_current_source().unwrap();
    let input = current(
        &surface,
        &(1..=18).map(|value| value as i64).collect::<Vec<_>>(),
        grain,
    );
    let covector = current(
        &surface,
        &(1..=18).map(|value| value as i64).collect::<Vec<_>>(),
        grain,
    );
    let action = source
        .action_matrix_free_auto(input.row(0).unwrap(), 128)
        .unwrap();
    let pullback = action
        .pullback_full_auto(covector.row(0).unwrap(), 128)
        .unwrap();
    assert!(source.declared_factor_scale_gradient(&pullback, 4).is_err());
    let gradient = source.declared_factor_scale_gradient(&pullback, 3).unwrap();
    let zero = gradient.gradient().row(1).unwrap().inspect().unwrap();
    assert!(zero.center[0].real.abs() <= zero.radius);
    assert!(
        zero.radius > Rat::zero(),
        "structural zero must retain basis uncertainty"
    );
}
