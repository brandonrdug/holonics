//! Receiver and lattice applications of the exact winding operator.
//!
//! The portable symmetric-circulant operator lives in `holonics::geometry::winding_inertia`; this
//! module retains only growth/form receiver search and the crystallographic lattice application.

use crate::grown_cell::GrownComplex;
#[cfg(test)]
use holonics::geometry::Rat;
use holonics::geometry::winding_inertia::{
    CyclicReading, SymmetricCirculant, WindingError, rational_star_value,
};
#[cfg(test)]
use holonics::geometry::winding_inertia::{cycle_adjacency, winding_inertia};
use holonics::inertia::SymmetricForm;

/// Read grown arcs by displacement class on a declared cyclic receiver.
pub fn cyclic_receiver_of_growth(
    grown: &GrownComplex,
    extent: usize,
) -> Result<SymmetricCirculant, WindingError> {
    if extent == 0 {
        return Err(WindingError::EmptyCirculant);
    }
    let mut counts = vec![0_i64; extent];
    for arc in &grown.arcs {
        let tail = (arc.tail.0 as usize) % extent;
        let head = (arc.head.0 as usize) % extent;
        counts[(head + extent - tail) % extent] += 1;
        counts[(tail + extent - head) % extent] += 1;
    }
    SymmetricCirculant::from_integers(&counts)
}

/// A form together with the engine-side cyclic reading that exposes its windings.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CyclicReceiver {
    pub reading: CyclicReading,
    pub circulant: SymmetricCirculant,
    /// What [`SymmetricCirculant::from_symmetric_form`] returned on the form's arriving order.
    /// `None` means that order was already circulant and the walk had nothing to move.
    pub native_refusal: Option<WindingError>,
    /// How many placements the walk touched. A measurement of the search, never of the form.
    pub walked: u64,
}

/// Search for a cyclic ordering under which the declared form is circulant.
pub fn cyclic_receiver_of_form(
    form: &SymmetricForm,
    walk_aperture: u64,
) -> Result<CyclicReceiver, WindingError> {
    let extent = form.extent();
    if extent == 0 {
        return Err(WindingError::EmptyCirculant);
    }
    for direction in 1..extent {
        if form.at(direction, direction) != form.at(0, 0) {
            return Err(WindingError::DiagonalIsNotConstant { direction });
        }
    }
    let native_refusal = SymmetricCirculant::from_symmetric_form(form).err();
    let mut order = vec![0_usize];
    let mut placed = vec![false; extent];
    placed[0] = true;
    let mut walked = 0_u64;
    if !extend_cyclic_reading(form, &mut order, &mut placed, &mut walked, walk_aperture) {
        return if walked > walk_aperture {
            Err(WindingError::CyclicWalkPastItsAperture { walked })
        } else {
            Err(WindingError::NoCyclicReceiver { walked })
        };
    }
    let reading = CyclicReading::declare(order)?;
    let circulant = SymmetricCirculant::read_cyclically(form, &reading)?;
    Ok(CyclicReceiver {
        reading,
        circulant,
        native_refusal,
        walked,
    })
}

fn extend_cyclic_reading(
    form: &SymmetricForm,
    order: &mut Vec<usize>,
    placed: &mut [bool],
    walked: &mut u64,
    walk_aperture: u64,
) -> bool {
    let extent = placed.len();
    if order.len() == extent {
        // Circulance of a *symmetric* matrix also demands `c_d = c_{n−d}`; the forward constraints
        // below only reach the upper triangle, so the reversal is checked once the ring closes.
        return (1..extent)
            .all(|step| form.at(order[0], order[step]) == form.at(order[0], order[extent - step]));
    }
    let position = order.len();
    for candidate in 0..extent {
        if placed[candidate] {
            continue;
        }
        *walked += 1;
        if *walked > walk_aperture {
            return false;
        }
        // `form(order[i], candidate)` must be the entry at displacement `position − i`, and that
        // entry is already fixed by the direction sitting at position `position − i`.
        if (1..position).any(|index| {
            form.at(order[index], candidate) != form.at(order[0], order[position - index])
        }) {
            continue;
        }
        placed[candidate] = true;
        order.push(candidate);
        if extend_cyclic_reading(form, order, placed, walked, walk_aperture) {
            return true;
        }
        order.pop();
        placed[candidate] = false;
    }
    false
}

/// Euler's totient, used by the exact cyclotomic constructibility reading.
fn totient(n: usize) -> usize {
    if n == 0 {
        return 0;
    }
    let mut remaining = n;
    let mut result = n;
    let mut factor = 2usize;
    while factor * factor <= remaining {
        if remaining % factor == 0 {
            while remaining % factor == 0 {
                remaining /= factor;
            }
            result -= result / factor;
        }
        factor += 1;
    }
    if remaining > 1 {
        result -= result / remaining;
    }
    result
}

/// Degree over `Q` of the turn coordinate of a regular polygon.
pub fn polygon_turn_degree(sides: usize) -> usize {
    match sides {
        0 => 0,
        1 | 2 => 1,
        _ => totient(sides) / 2,
    }
}

/// Whether a periodic lattice admits a rotation of the declared order.
///
/// In two dimensions the trace is an integer, so Euler's totient characterization is exact:
/// orders one and two are rational, and for `n ≥ 3` the admissible cases satisfy `φ(n) = 2`.
pub fn lattice_admits_order(order: usize) -> bool {
    rational_star_value(1, order).is_some()
}

#[cfg(test)]
mod lattice_rung_tests {
    use super::*;

    /// The crystallographic restriction, read off the Niven carrier rather than written down.
    #[test]
    fn the_lattice_admits_exactly_one_two_three_four_and_six() {
        let admitted: Vec<usize> = (1..=24).filter(|n| lattice_admits_order(*n)).collect();
        assert_eq!(admitted, vec![1, 2, 3, 4, 6]);
        assert!(!lattice_admits_order(0));
    }

    /// `φ(n)/2`, checked against the values that decide the classical constructions.
    #[test]
    fn the_polygon_turn_degree_is_half_the_totient() {
        assert_eq!(polygon_turn_degree(3), 1);
        assert_eq!(polygon_turn_degree(4), 1);
        assert_eq!(polygon_turn_degree(5), 2);
        assert_eq!(polygon_turn_degree(6), 1);
        assert_eq!(polygon_turn_degree(7), 3);
        assert_eq!(polygon_turn_degree(9), 3);
        assert_eq!(polygon_turn_degree(17), 8);
        assert_eq!(polygon_turn_degree(257), 128);
    }

    /// **The pentagon divides the two instruments**, which is the whole content of the lattice rung.
    #[test]
    fn the_pentagon_is_compass_constructible_and_crystallographically_forbidden() {
        use crate::multiquadratic::admits_degree;
        // 5 is a Fermat prime, so φ(5)/2 = 2 is a power of two.
        assert!(admits_degree(polygon_turn_degree(5)));
        // and 5 is not in {1,2,3,4,6}.
        assert!(!lattice_admits_order(5));

        // The heptagon fails both: φ(7)/2 = 3.
        assert!(!admits_degree(polygon_turn_degree(7)));
        assert!(!lattice_admits_order(7));

        // The hexagon passes both.
        assert!(admits_degree(polygon_turn_degree(6)));
        assert!(lattice_admits_order(6));

        // And the 17-gon separates them the same way the pentagon does — Gauss's own case.
        assert!(admits_degree(polygon_turn_degree(17)));
        assert!(!lattice_admits_order(17));
    }
}

#[cfg(test)]
mod receiver_tests {
    use super::*;
    use crate::grown_cell::{ComplexAperture, Schedule, found_complex, grow, standard_cells};
    use holonics::inertia::{Inertia, congruence, inertia};
    use num_traits::{One, Zero};

    #[test]
    fn a_grown_circuit_read_on_a_cyclic_receiver_returns_its_passages_by_winding() {
        let table = standard_cells();
        let mut readings = Vec::new();
        for schedule in Schedule::ALL {
            let growth = grow(&table, "brent-kung-adder", &[8, 8, 1], schedule)
                .expect("the standard cells grow an eight-bit adder");
            let complex = found_complex(&growth, ComplexAperture::DIVISION)
                .expect("the growth founds its complex");
            assert!(
                complex.arcs.len() > 100,
                "the grown material must be substantial: {} arcs",
                complex.arcs.len()
            );
            for extent in [5_usize, 7, 9] {
                let receiver = cyclic_receiver_of_growth(&complex, extent).unwrap();
                assert!(
                    receiver.first_row().iter().any(|entry| *entry > Rat::one()),
                    "the grown receiver must carry entries beyond {{0,1}}: {:?}",
                    receiver.first_row()
                );
                let reading = winding_inertia(&receiver).unwrap();
                assert_eq!(
                    reading.split(),
                    inertia(&receiver.as_symmetric_form().unwrap()),
                    "grown extent {extent} under {}",
                    schedule.name()
                );
                assert_eq!(reading.passages.len(), extent);
                // Every passage is named, and the principal one carries the whole conduction.
                assert_eq!(reading.passage(0).unwrap().winding, Rat::zero());
                readings.push((schedule, extent, reading));
            }
        }

        // The law fires on this material rather than returning a trivial reading: at least one grown
        // receiver is genuinely indefinite, so both cones are occupied.
        assert!(
            readings
                .iter()
                .any(|(_, _, reading)| reading.split().is_indefinite()),
            "a grown family in which no receiver is indefinite exercises nothing"
        );
        assert!(
            readings
                .iter()
                .any(|(_, _, reading)| !reading.windings_past_the_hand().is_empty()),
            "no grown passage wound past the hand, so the naming was never exercised"
        );

        // The frame really moves. Folding a schedule-allocated net identifier modulo `n` reads the
        // schedule along with the conduction, so at least one extent must return different splits
        // under different schedules. If none did, this whole sweep would be one chart read three
        // times and the agreement above would carry no evidence about frames.
        let mut moved_with_the_schedule = Vec::new();
        for extent in [5_usize, 7, 9] {
            let splits: Vec<Inertia> = readings
                .iter()
                .filter(|(_, size, _)| *size == extent)
                .map(|(_, _, reading)| reading.split())
                .collect();
            assert_eq!(splits.len(), 3);
            if splits.windows(2).any(|pair| pair[0] != pair[1]) {
                moved_with_the_schedule.push((extent, splits));
            }
        }
        assert!(
            !moved_with_the_schedule.is_empty(),
            "no grown chart moved with the expansion schedule, so the three schedules produced one \
             frame and the cross-check never crossed anything"
        );
    }

    #[test]
    fn a_form_blind_in_one_reading_names_its_windings_in_another_and_the_split_does_not_move() {
        let hexagon = cycle_adjacency(6).unwrap();
        let form = hexagon.as_symmetric_form().unwrap();
        // An involution, so applying it twice returns the original form.
        let swap = CyclicReading::declare(vec![0, 2, 1, 3, 4, 5]).unwrap();
        let scrambled = congruence(&form, &swap.basis().unwrap()).unwrap();

        assert!(
            matches!(
                SymmetricCirculant::from_symmetric_form(&scrambled),
                Err(WindingError::NotCirculant { .. })
            ),
            "the permuted hexagon still reads as circulant in its own order, so this fixture \
             cannot separate the two readings"
        );
        assert!(
            matches!(
                SymmetricCirculant::read_cyclically(&scrambled, &CyclicReading::native(6).unwrap()),
                Err(WindingError::NotCirculant { .. })
            ),
            "the native reading must return exactly what the direct gate returns"
        );

        let recovered = SymmetricCirculant::read_cyclically(&scrambled, &swap).unwrap();
        assert_eq!(recovered, hexagon);
        assert_eq!(inertia(&scrambled), inertia(&form));

        // And the search finds a reading without being told which one.
        let receiver = cyclic_receiver_of_form(&scrambled, 10_000).unwrap();
        assert!(
            receiver.native_refusal.is_some(),
            "a receiver whose native order already worked proves nothing about the reading"
        );
        assert_eq!(
            winding_inertia(&receiver.circulant).unwrap().split(),
            winding_inertia(&hexagon).unwrap().split()
        );
        assert!(receiver.walked > 0);
    }

    #[test]
    fn a_form_whose_directions_self_pair_differently_is_circulant_under_no_reading() {
        let form =
            SymmetricForm::from_integers(&[vec![1, 0, 0], vec![0, 1, 0], vec![0, 0, 2]]).unwrap();
        assert_eq!(
            cyclic_receiver_of_form(&form, 10_000),
            Err(WindingError::DiagonalIsNotConstant { direction: 2 })
        );
    }

    #[test]
    fn an_exhausted_walk_is_reported_as_an_allowance_and_not_as_an_absence() {
        let form = cycle_adjacency(6).unwrap().as_symmetric_form().unwrap();
        assert!(matches!(
            cyclic_receiver_of_form(&form, 1),
            Err(WindingError::CyclicWalkPastItsAperture { .. })
        ));

        // A form with a constant diagonal that no reading can make circulant: the walk closes and
        // returns an absence with its own placement count.
        let stubborn = SymmetricForm::from_integers(&[
            vec![0, 1, 1, 0],
            vec![1, 0, 1, 1],
            vec![1, 1, 0, 1],
            vec![0, 1, 1, 0],
        ])
        .unwrap();
        assert!(
            matches!(
                cyclic_receiver_of_form(&stubborn, 10_000),
                Err(WindingError::NoCyclicReceiver { .. })
            ),
            "this fixture is supposed to close the walk without finding a reading"
        );
    }
}
