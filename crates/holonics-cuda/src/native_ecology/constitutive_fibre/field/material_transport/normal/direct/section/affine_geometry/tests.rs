//! Resident CUDA tests for the fixed complex3 geometry/action chart.
//!
//! These tests intentionally use the same certified row-ball mount as the
//! normalized and pair receivers. The Cayley rotation is checked at the
//! declaration boundary; the native primitive receives only its certified
//! dyadic coefficient packet and does not infer rigidness.

use super::*;
use crate::embedding_fiber::ResidentReadout;
use crate::resident_section::ResidentSectionRest;
use num_traits::Zero;
use holonics::geometry::{AffineMap3, Rat, RatVec3, cayley_rotation_z};
use std::rc::Rc;

fn balls<'c>(
    surface: &'c ResidentSurface<'c>,
    rows: &[(Vec<i128>, i128)],
    dimensions: usize,
) -> ResidentNormalEnclosureSection<'c> {
    balls_at_grain(surface, rows, dimensions, ResidentGrain(16))
}

fn balls_at_grain<'c>(
    surface: &'c ResidentSurface<'c>,
    rows: &[(Vec<i128>, i128)],
    dimensions: usize,
    grain: ResidentGrain,
) -> ResidentNormalEnclosureSection<'c> {
    let flat = rows
        .iter()
        .flat_map(|(values, radius)| values.iter().copied().chain([*radius]))
        .flat_map(|value| [value as i64, (value >> 64) as i64])
        .map(|value| (value, value))
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
    ResidentNormalEnclosureSection::from_resident(surface, section, rows.len(), dimensions, grain)
        .unwrap()
}

fn q(numerator: i64, denominator: i64) -> Rat {
    Rat::new(numerator.into(), denominator.into())
}

fn wave(real: i64, imaginary: i64, denominator: i64) -> ExactComplexWaveCurrent {
    ExactComplexWaveCurrent::new(q(real, denominator), q(imaginary, denominator))
}

fn dot(left: &[ExactComplexWaveCurrent], right: &[ExactComplexWaveCurrent]) -> Rat {
    left.iter()
        .zip(right)
        .map(|(a, b)| &a.real * &b.real + &a.imaginary * &b.imaginary)
        .sum()
}

fn cayley_map() -> AffineMap3 {
    AffineMap3 {
        linear: cayley_rotation_z(&q(1, 2)),
        translation: RatVec3::new(q(2, 1), q(-1, 1), q(2, 1)),
    }
}

/// Parity law (affine geometry): device forward rows contain the exact affine images and the
/// pullback satisfies the adjoint pairing ⟨Rx, g⟩ = ⟨x, Rᵀg⟩ with repeated source rows joined.
#[test]
#[ignore = "requires CUDA; resident affine forward/pullback and repeated-index join"]
fn affine_geometry_forward_and_transpose_use_the_same_certified_map() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let unit = 1_i128 << 16;
    let source_radius = unit / 256;
    let source = Rc::new(balls(
        &surface,
        &[
            (vec![unit, 0, 0, unit, 2 * unit, -unit], source_radius),
            (vec![0, unit, -unit, 0, unit, unit], source_radius),
            (
                vec![-unit, 2 * unit, unit, -unit, 0, 2 * unit],
                source_radius,
            ),
        ],
        AFFINE_GEOMETRY_COMPONENTS,
    ));
    let map = cayley_map();
    let rotation = map.linear.clone();
    assert!(rotation.is_special_orthogonal());
    assert_eq!(rotation.rows[0][0], q(3, 5));
    assert_eq!(rotation.rows[1][0], q(4, 5));
    let maps = vec![map.clone(), map.clone(), map];
    let coefficients =
        ResidentNormalEnclosureSection::affine_coefficients(&surface, &maps, ResidentGrain(16))
            .unwrap();
    assert!(coefficients.inspect_radii().unwrap()[0] > Rat::zero());

    // The repeated source index is part of the producing cut, not a value-chart
    // alias. The returned adjoint must join rows 0 and 2 at source row 2.
    let action = source
        .clone()
        .affine_geometry(&[2, 0, 2], coefficients.clone(), false)
        .unwrap();
    let output = action.output();
    assert!(output.row(0).unwrap().inspect().unwrap().contains(&[
        wave(3, 10, 5),
        wave(-6, 5, 5),
        wave(2, 2, 1),
    ]));
    assert!(output.row(1).unwrap().inspect().unwrap().contains(&[
        wave(13, -4, 5),
        wave(-1, 3, 5),
        wave(4, -1, 1),
    ]));
    assert!(output.row(2).unwrap().inspect().unwrap().contains(&[
        wave(3, 10, 5),
        wave(-6, 5, 5),
        wave(2, 2, 1),
    ]));
    assert!(output.row(0).unwrap().inspect().unwrap().radius > Rat::zero());

    // A real receiving covector on each output row. The exact linear face
    // (with the affine bias removed) and its R^T return have equal pairing.
    let gy = balls(
        &surface,
        &[
            (vec![unit, 0, 0, 0, 0, 0], 0),
            (vec![0, 0, unit, 0, 0, 0], 0),
            (vec![0, 0, 0, 0, unit, 0], 0),
        ],
        AFFINE_GEOMETRY_COMPONENTS,
    );
    let back = action.pull_back(&gy).unwrap();
    assert!(back.source().row(0).unwrap().inspect().unwrap().contains(&[
        wave(4, 0, 5),
        wave(3, 0, 5),
        wave(0, 0, 1),
    ]));
    assert!(back.source().row(1).unwrap().inspect().unwrap().contains(&[
        wave(0, 0, 1),
        wave(0, 0, 1),
        wave(0, 0, 1),
    ]));
    assert!(back.source().row(2).unwrap().inspect().unwrap().contains(&[
        wave(3, 0, 5),
        wave(-4, 0, 5),
        wave(1, 0, 1),
    ]));
    assert!(back.source().row(2).unwrap().inspect().unwrap().radius > Rat::zero());

    let source_zero = vec![wave(1, 0, 1), wave(0, 1, 1), wave(2, -1, 1)];
    let source_two = vec![wave(-1, 2, 1), wave(1, -1, 1), wave(0, 2, 1)];
    let returned_zero = vec![wave(4, 0, 5), wave(3, 0, 5), wave(0, 0, 1)];
    let returned_two = vec![wave(3, 0, 5), wave(-4, 0, 5), wave(1, 0, 1)];
    let target_pairing = q(-7, 5) + q(4, 5);
    let source_pairing = dot(&source_zero, &returned_zero) + dot(&source_two, &returned_two);
    assert_eq!(target_pairing, source_pairing);
}
