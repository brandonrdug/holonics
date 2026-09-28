//! The inverse charts' host-side laws (the lattice word): the layouts of the Newton–Schulz entries
//! derived from the census, and the exponent ceiling. The entries themselves run in `store`, and
//! their parity with the host's charts is the port's (`port_tests`). The carried tick's oracle and
//! its card tests were retired with the tick on September 28 (at `2d34b819`).

use super::card::CERTIFICATE_SHARED_PER_THREAD;
use super::tests::{census, entry};
use super::word::{CERTIFICATE_ENTRY, INVERSE_EXPONENT_CEILING, RESIDUAL_ENTRY};
use super::*;
use crate::cuda::Dim3;

/// The inverse's layout is the read's over rows × columns (one block per entry, one warp covering
/// a campaign ring's row); the certificate's is one block per chart, its threads covering the rows.
#[test]
fn the_inverse_layouts_are_derived_from_the_census() {
    let census = census();
    // The inverse over campaign 1's four rings: 72 rows × 26 columns, one block per entry.
    let residual = entry(RESIDUAL_ENTRY, 1024, 4);
    let layout = read_layout(&census, &residual, 72, 26, 26).unwrap();
    assert_eq!(
        (layout.grid, layout.block),
        (Dim3 { x: 72, y: 26, z: 1 }, Dim3::x(32))
    );
    // The certificate: one block per chart.
    let certificate = entry(CERTIFICATE_ENTRY, 1024, 4);
    let layout = certificate_layout(&census, &certificate, 4, 26).unwrap();
    assert_eq!(
        (layout.grid, layout.block, layout.shared),
        (Dim3::x(4), Dim3::x(32), 32 * CERTIFICATE_SHARED_PER_THREAD)
    );
    assert_eq!(
        layout.realization,
        Realization::ChartPerBlock {
            charts: 4,
            threads: 32,
            rows_per_thread: 1
        }
    );
    // More rows than the block carries loop: (49,152 − 4)/16 = 3,071 threads by shared, 1,024 by
    // the ceiling.
    assert_eq!(
        certificate_layout(&census, &certificate, 1, 3000)
            .unwrap()
            .realization,
        Realization::ChartPerBlock {
            charts: 1,
            threads: 1024,
            rows_per_thread: 3
        }
    );
    assert!(matches!(
        certificate_layout(&census, &certificate, 0, 4),
        Err(DeviceError::Launch { .. })
    ));
}

/// The ceiling is the carrier's: an inverse's `S ≤ 126` keeps `2^S` a carrier word.
#[test]
fn the_inverse_ceiling_is_the_carriers() {
    assert_eq!(INVERSE_EXPONENT_CEILING, 126);
    assert!(
        1i128
            .checked_shl(INVERSE_EXPONENT_CEILING)
            .is_some_and(|unit| unit > 0)
    );
    assert!(
        1i128
            .checked_shl(INVERSE_EXPONENT_CEILING + 1)
            .is_some_and(|unit| unit < 0)
    );
}
