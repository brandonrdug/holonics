use super::*;
use crate::embedding_fiber::ResidentReadout;
use holonics::exact_linear::ExactRatMatrix;
use num_traits::Zero;

fn row_space(rows: Vec<Vec<Rat>>) -> Vec<Vec<Rat>> {
    ExactRatMatrix::new(rows)
        .unwrap()
        .reduced_row_echelon()
        .unwrap()
        .0
        .to_rows()
        .into_iter()
        .filter(|row| row.iter().any(|x| !x.is_zero()))
        .collect()
}

/// Host/device parity (constitutive-field formation kernel): the device relation rows span
/// exactly the presented rows, checked by an exact-rational RREF on the host.
#[test]
#[ignore = "requires CUDA; exact-rational observer compares all formed relation rows"]
fn native_row_formation_matches_the_complete_presented_span() {
    let readout = ResidentReadout::new().expect("CUDA apparatus required");
    let surface = ResidentSurface::on(&readout).unwrap();
    // The observer's arbitrary-precision RREF reads full row spaces; it is not called by the body.
    // Include rational pivots, negative hands, dependence, zero sources and contradictory returns.
    for offset in -2..=2 {
        let mut body = ResidentConstitutiveFibre::found(&surface, 3, 2).unwrap();
        let mut presented = Vec::new();
        for row in [
            [2, 1, 0, 3, offset],
            [1, -1, 1, 5, 2],
            [0, 2, -1, -1, 3],
            [4, 2, 0, 6, 2 * offset],
            [0, 0, 0, offset, 1],
            [2, 1, 0, -3, 2],
        ] {
            body.advance(&row[..3], Some(&row[3..])).unwrap();
            presented.push(
                row.into_iter()
                    .map(|v| Rat::from_integer(v.into()))
                    .collect(),
            );
            let native = body.inspect_relation().unwrap();
            let actual = native
                .intervals
                .chunks_exact(5)
                .map(|row| {
                    row.iter()
                        .map(|(lo, hi)| {
                            assert_eq!(lo, hi);
                            Rat::from_integer((*lo).into())
                        })
                        .collect()
                })
                .collect();
            assert_eq!(row_space(actual), row_space(presented.clone()));
        }
    }
}
