//! Keys lead learning: a declared rotor configuration is recovered from a synthetic crib as its full
//! gauge orbit, propagation equals brute force, gauge fixing picks one member per orbit, adding an
//! edge only shrinks the fibre, an empty fibre falls back, a ring is located under the earlier
//! rings' configurations, and re-keying leaves the open moment untouched.

use num_bigint::{BigInt, BigUint};

use super::support::{Draw, contact, ring};
use crate::compression::{Candidate, Menu, PortImages};
use crate::hnn::HnnError;
use crate::hnn::field::{CribDeclaration, Current, Field, FieldDeclaration, ReceiverDeclaration};
use crate::hnn::keys::{
    candidate_keys, crib_menu, crib_opening, crib_ticks, locate_closing, locate_keys, locate_ring,
    ring_steps,
};
use crate::hnn::moment::SourceMoment;
use crate::holon::contact::menu::PortPermutation;
use crate::navigator::Clock;
use crate::ratio::{integer, rat};

/// A field of rings with the declared periods and locks (in carry order), joined in a path, over
/// an exterior chart of 16 classes, so a cell's code is its port on every ring of period ≤ 16.
fn rotor_field(rings: &[(u64, Vec<u64>)]) -> Field {
    Field::declare(
        FieldDeclaration {
            rings: rings
                .iter()
                .map(|(period, lock)| ring(*period, lock.clone()))
                .collect(),
            contacts: (1..rings.len()).map(|g| contact(g - 1, g, 1, 0)).collect(),
            loops: Vec::new(),
            sources: vec![0],
            offsets: vec![1],
            alphabet: 16,
            step: integer(1),
            exponent_grain: 1,
            receivers: vec![ReceiverDeclaration {
                ring: rings.len() - 1,
                aperture: 1,
                tolerance: rat(1, 16),
            }],
            crib: CribDeclaration {
                window: 64,
                offset: 1,
            },
            population: 1 << 24,
            lattice: Default::default(),
        }
        .by_lattice_rule(),
    )
    .unwrap()
}

/// The stage `ρ^(−m) F ρ^m` of a ring at rotor position `m`.
fn stage(field: &Field, ring: usize, position: u64) -> PortPermutation {
    field
        .ring(ring)
        .machine()
        .unwrap()
        .stage(&BigUint::from(position))
        .unwrap()
}

/// A crib a true machine produces on ring `g`: `x_(k+1) = S⁻¹ W_(key + steps_g(k)) S x_k`, with
/// `steps_g(k)` ring `g`'s ticks on the cells before `k` from the declared configurations, stepped on
/// the cells as they are produced. Codes are ports (codes below `d_g`).
fn synthetic_crib(
    field: &Field,
    ring: usize,
    key: u64,
    board: &PortPermutation,
    configurations: &[u64],
    length: usize,
    start: usize,
) -> Vec<usize> {
    let mut lift: Vec<BigInt> = configurations.iter().map(|c| BigInt::from(*c)).collect();
    let mut taken = 0u64;
    let mut crib = vec![start];
    for k in 0..length - 1 {
        let image = stage(field, ring, key + taken)
            .apply(board.apply(crib[k]).unwrap())
            .unwrap();
        crib.push(board.inverse().apply(image).unwrap());
        taken += u64::from(field.selective_step(&mut lift, crib[k]).unwrap().ticks[ring]);
    }
    crib
}

fn key_class(candidate: &Candidate<Clock>, period: u64) -> u64 {
    u64::try_from(candidate.key.ticks() % BigUint::from(period)).unwrap()
}

/// Lean `HNN/Keys.{field_loop_fibre, gauge_fix_unique}`, `Keys.fibre_eq_orbit`: a declared rotor
/// configuration is recovered from a synthetic crib as its full consistent family, the truth's
/// rotor-gauge orbit (seven members, never a point), and the gauge fixing `S(p_0) = 0` publishes the
/// known key when the true plugboard fixes `p_0`.
#[test]
fn a_known_key_is_recovered_as_its_gauge_orbit_and_published_by_the_convention() {
    let field = rotor_field(&[(7, (0..7).collect()), (2, vec![])]);
    let board = PortPermutation::new(vec![0, 4, 6, 2, 1, 5, 3]).unwrap();
    let key = 3;
    let crib = synthetic_crib(&field, 0, key, &board, &[0, 0], 64, 0);
    let located = locate_ring(&field, 0, &crib, 1, &[0, 0], 0).unwrap();
    assert_eq!(
        located.fibre.len(),
        7,
        "the fibre is the orbit, not a point"
    );
    assert_eq!(located.orbits, 1);
    let mut keys: Vec<u64> = located.fibre.iter().map(|c| key_class(c, 7)).collect();
    keys.sort_unstable();
    assert_eq!(keys, (0..7).collect::<Vec<_>>());
    let truth = located
        .fibre
        .iter()
        .find(|c| key_class(c, 7) == key)
        .expect("the truth lies in the fibre");
    for port in &located.menu_ports {
        assert_eq!(truth.images.image(*port), Some(board.apply(*port).unwrap()));
    }
    assert_eq!(located.menu_ports[0], 0);
    assert_eq!(located.published, Some(key));
    assert_eq!(located.configuration, key);
    assert!(!located.fell_back);
    // A plugboard that does not fix the least port publishes the gauge-fixed member instead.
    let turned = PortPermutation::new(vec![2, 4, 6, 0, 1, 5, 3]).unwrap();
    let crib = synthetic_crib(&field, 0, key, &turned, &[0, 0], 64, 0);
    let located = locate_ring(&field, 0, &crib, 1, &[0, 0], 0).unwrap();
    // The gauge-fixed member is `(key + t, S − t)` with `S(0) − t = 0`, so `t = S(0) = 2`.
    assert_eq!(located.published, Some((key + 2) % 7));
}

/// Brute force over a ring's menu: every key with every injective image of the menu ports, kept
/// when every edge holds, with each edge's stage computed once per key.
fn brute_force(menu: &Menu<Clock>, keys: &[Clock]) -> Vec<(u64, Vec<Option<usize>>)> {
    let ports = menu.menu_ports();
    let images = PortImages::injections(menu.ports(), &ports).unwrap();
    let mut kept = Vec::new();
    for key in keys {
        let stages: Vec<_> = menu.edges().iter().map(|e| e.stage(key).unwrap()).collect();
        for image in &images {
            let holds = menu.edges().iter().zip(&stages).all(|(edge, stage)| {
                stage.apply(image.image(edge.from()).unwrap()).unwrap()
                    == image.image(edge.to()).unwrap()
            });
            if holds {
                kept.push((
                    u64::try_from(key.ticks() % BigUint::from(menu.ports() as u64)).unwrap(),
                    (0..menu.ports()).map(|p| image.image(p)).collect(),
                ));
            }
        }
    }
    kept.sort();
    kept
}

fn classes(fibre: &[Candidate<Clock>], period: u64) -> Vec<(u64, Vec<Option<usize>>)> {
    let mut classes: Vec<_> = fibre
        .iter()
        .map(|c| {
            (
                key_class(c, period),
                (0..period as usize).map(|p| c.images.image(p)).collect(),
            )
        })
        .collect();
    classes.sort();
    classes
}

/// Lean `HNN/Keys.propagation_eq_edge_fibre`: on ring menus below the image ceiling, the
/// propagated survivors are exactly the brute-force candidates satisfying every edge, on
/// machine-produced cribs and on random cribs.
#[test]
fn propagation_equals_brute_force_on_ring_menus() {
    let field = rotor_field(&[(7, vec![1, 4]), (2, vec![])]);
    let board = PortPermutation::new(vec![4, 0, 6, 2, 1, 5, 3]).unwrap();
    let mut draw = Draw::new(51);
    for length in [4usize, 6, 9] {
        let crib = synthetic_crib(&field, 0, 2, &board, &[0, 0], length, draw.below(7));
        let random: Vec<usize> = (0..length).map(|_| draw.below(7)).collect();
        for cells in [crib, random] {
            let menu = crib_menu(&field, 0, &cells, 1, &[0, 0]).unwrap();
            let keys = candidate_keys(&field, 0).unwrap();
            let propagated = menu.propagate(&keys).unwrap();
            assert_eq!(
                classes(&propagated.candidates, 7),
                brute_force(&menu, &keys)
            );
            assert!(propagated.work <= 7 * 7 * 2 * menu.edges().len() as u64);
        }
    }
}

/// Lean `HNN/Keys.gauge_fix_unique`: on a plural fibre, every rotor-gauge orbit has exactly one
/// member with `S(p_0) = 0` at the least menu port.
#[test]
fn gauge_fixing_picks_one_member_per_orbit() {
    let field = rotor_field(&[(7, vec![1, 4]), (2, vec![])]);
    let board = PortPermutation::new(vec![4, 0, 6, 2, 1, 5, 3]).unwrap();
    let crib = synthetic_crib(&field, 0, 5, &board, &[0, 0], 12, 1);
    let located = locate_ring(&field, 0, &crib, 1, &[0, 0], 0).unwrap();
    assert!(
        located.orbits > 1,
        "the δ = 1 chain leaves the fibre plural"
    );
    assert_eq!(located.published, None);
    assert!(located.fell_back);
    let least = located.menu_ports[0];
    let fixed = located
        .fibre
        .iter()
        .filter(|c| c.images.image(least) == Some(0))
        .count();
    assert_eq!(fixed, located.orbits);
    assert_eq!(located.fibre.len(), 7 * located.orbits);
}

/// Lean `Keys.fibre_cons`: adding an edge only shrinks the fibre (each survivor, restricted to the
/// earlier menu's ports, survived there), and the truth is never lost.
#[test]
fn adding_an_edge_only_shrinks_the_fibre() {
    let field = rotor_field(&[(7, vec![1, 4]), (2, vec![])]);
    let board = PortPermutation::new(vec![4, 0, 6, 2, 1, 5, 3]).unwrap();
    let crib = synthetic_crib(&field, 0, 1, &board, &[0, 0], 24, 2);
    let keys = candidate_keys(&field, 0).unwrap();
    let restrict = |class: &(u64, Vec<Option<usize>>), ports: &[usize]| {
        (
            class.0,
            ports.iter().map(|p| class.1[*p]).collect::<Vec<_>>(),
        )
    };
    let mut previous: Option<(Vec<usize>, Vec<(u64, Vec<Option<usize>>)>)> = None;
    for length in 2..=crib.len() {
        let menu = crib_menu(&field, 0, &crib[..length], 1, &[0, 0]).unwrap();
        let ports = menu.menu_ports();
        let fibre = classes(&menu.propagate(&keys).unwrap().candidates, 7);
        assert!(fibre.iter().any(|(key, images)| {
            *key == 1
                && ports
                    .iter()
                    .all(|p| images[*p] == Some(board.apply(*p).unwrap()))
        }));
        if let Some((earlier_ports, earlier)) = &previous {
            for class in &fibre {
                let restricted = restrict(class, earlier_ports);
                assert!(
                    earlier
                        .iter()
                        .any(|e| restrict(e, earlier_ports) == restricted)
                );
            }
        }
        previous = Some((ports, fibre));
    }
}

/// An empty fibre, reported with its shortest failing loop, falls back to the current
/// configuration.
#[test]
fn an_empty_fibre_falls_back_to_the_current_configuration() {
    let field = rotor_field(&[(7, (0..7).collect()), (2, vec![])]);
    // Two self-edges at port 0 at consecutive positions each force `S(0)` to their stage's one
    // fixed point, `−(key + m)`, which differ: no key closes both.
    let crib: Vec<usize> = vec![0, 0, 0, 3, 5];
    let located = locate_ring(&field, 0, &crib, 1, &[4, 0], 4).unwrap();
    assert!(located.fibre.is_empty());
    assert_eq!(located.orbits, 0);
    assert_eq!(located.published, None);
    assert_eq!(located.configuration, 4);
    assert!(located.fell_back);
    let failing = located.failing_loop.expect("a failing loop is reported");
    assert!(!failing.is_empty());
    let mut current = Current::at(&field, vec![4.into(), 0.into()]).unwrap();
    let location = locate_keys(&field, &current, &crib, 1).unwrap();
    assert_eq!(location.configurations()[0], 4);
    let before = current.clone();
    location.rekey(&field, &mut current).unwrap();
    assert_eq!(current, before);
}

/// Ring `g` is located under the earlier rings' published or fallen-back configurations: its step
/// positions come from their carries. A crib a true machine produced on ring 1 with ring 0 at
/// configuration 1 keeps the truth in ring 1's fibre under that configuration, which ring 0's own
/// (empty) fibre falls back to.
#[test]
fn a_ring_is_located_under_the_earlier_rings_configurations() {
    let field = rotor_field(&[(3, vec![0, 1, 2]), (5, vec![])]);
    let board = PortPermutation::new(vec![3, 0, 4, 1, 2]).unwrap();
    let crib = synthetic_crib(&field, 1, 2, &board, &[1, 0], 40, 0);
    let under_truth = locate_ring(&field, 1, &crib, 1, &[1, 0], 0).unwrap();
    let truth = |fibre: &[Candidate<Clock>]| {
        fibre
            .iter()
            .any(|c| key_class(c, 5) == 2 && c.images.image(0) == Some(board.apply(0).unwrap()))
    };
    assert!(truth(&under_truth.fibre));
    let under_other = locate_ring(&field, 1, &crib, 1, &[0, 0], 0).unwrap();
    assert!(!truth(&under_other.fibre));
    assert_ne!(
        ring_steps(&field, 1, &crib, &[1, 0]).unwrap(),
        ring_steps(&field, 1, &crib, &[0, 0]).unwrap()
    );
    let current = Current::at(&field, vec![1.into(), 0.into()]).unwrap();
    let location = locate_keys(&field, &current, &crib, 1).unwrap();
    assert!(location.rings[0].fell_back);
    assert_eq!(location.rings[0].configuration, 1);
    assert!(truth(&location.rings[1].fibre));
}

/// R3 K1: re-keying at a boundary moves only the lift point's phase classes, keeping windings, and
/// leaves the open moment's bins, offset counts and window unchanged.
#[test]
fn rekeying_leaves_the_open_moment_untouched() {
    let field = rotor_field(&[(7, (0..7).collect()), (2, vec![])]);
    let board = PortPermutation::new(vec![0, 4, 6, 2, 1, 5, 3]).unwrap();
    let mut current = Current::at_rest(&field);
    let mut moment = SourceMoment::open(&field, &current);
    let mut draw = Draw::new(61);
    let cells: Vec<usize> = (0..30).map(|_| draw.below(16)).collect();
    let mut fed = 0;
    while fed < cells.len() {
        fed += moment
            .ingest(&field, &mut current, &cells[fed..])
            .unwrap()
            .cells;
    }
    let kept = moment.clone();
    let windings: Vec<_> = (0..2)
        .map(|g| current.winding(&field, g).unwrap())
        .collect();
    let crib = synthetic_crib(&field, 0, 3, &board, &[0, 0], 64, 0);
    let location = locate_keys(&field, &current, &crib, 1).unwrap();
    assert_eq!(location.rings[0].published, Some(3));
    let jumps = location.rekey(&field, &mut current).unwrap();
    assert_eq!(current.phase(&field, 0).unwrap(), 3);
    // Ring 0 ticks once a cell from rest, so it stood at 30 mod 7 = 2 before the jump.
    assert_eq!(jumps[0], 1);
    assert_eq!(
        (0..2)
            .map(|g| current.winding(&field, g).unwrap())
            .collect::<Vec<_>>(),
        windings
    );
    assert_eq!(moment, kept);
}

/// Review D1: keys are located on the crib that closed an aeon, cells already ingested. The lift at
/// the crib's opening is recovered exactly by stepping back over it; the truth's gauge-fixed key is
/// located there and carried over the crib's ticks to the boundary, where re-keying applies it; a
/// crib that did not reach the lift is refused.
#[test]
fn a_closing_crib_is_stepped_back_and_its_key_carried_to_the_boundary() {
    let field = rotor_field(&[(7, (0..7).collect()), (2, vec![])]);
    let board = PortPermutation::new(vec![0, 4, 6, 2, 1, 5, 3]).unwrap();
    let crib = synthetic_crib(&field, 0, 3, &board, &[0, 0], 64, 0);
    let opening = Current::at(&field, vec![5.into(), 1.into()]).unwrap();
    let mut current = opening.clone();
    for &code in &crib {
        current.step(&field, code).unwrap();
    }
    assert_eq!(
        crib_opening(&field, current.lift(), &crib).unwrap(),
        opening.lift()
    );
    let location = locate_closing(&field, &current, &crib, 1).unwrap();
    assert_eq!(location.rings[0].published, Some(3));
    let ticks = crib_ticks(&field, 0, &crib, &location.configurations()).unwrap();
    assert_eq!(ticks, 64);
    assert_eq!(location.rings[0].carried, Some((3 + 64) % 7));
    location.rekey(&field, &mut current).unwrap();
    assert_eq!(current.phase(&field, 0).unwrap(), (3 + 64) % 7);
    assert_eq!(
        crib_opening(&field, Current::at_rest(&field).lift(), &crib).unwrap_err(),
        HnnError::NegativeLift { ring: 0 }
    );
}
