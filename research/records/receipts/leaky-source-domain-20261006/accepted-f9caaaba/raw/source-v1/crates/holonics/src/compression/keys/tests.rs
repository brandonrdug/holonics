//! The content of Lean `Compression/Core/Keys` beyond its definitions: pruning only shrinks the
//! fibre, the gauge law (the fibre is a union of gauge orbits, the truth is inseparable from its
//! gauge image, a pinned fibre is one orbit), and the reflector machine's counts.

use super::*;
use crate::ratio::integer;

fn permutation(images: &[usize]) -> PortPermutation {
    PortPermutation::new(images.to_vec()).unwrap()
}

/// Lean `Machine.rotor`, `reflector`: the one-step rotor `i ↦ i + 1` and the reflector exchanging
/// ports `0` and `1`, on three ports.
fn machine() -> ReflectorMachine {
    ReflectorMachine::new(
        permutation(&[1, 2, 0]),
        PortPermutation::swap(3, 0, 1).unwrap(),
    )
    .unwrap()
}

/// The key at rotor offset `k`: a ring clock of the rotor's period advanced `k` ticks from rest.
fn key(offset: u32) -> Clock {
    let mut clock = Clock::ring(integer(1), 3).unwrap();
    clock.advance(&BigUint::from(offset));
    clock
}

fn keys() -> Vec<Clock> {
    (0..3).map(key).collect()
}

/// Lean `menu₁ = [loopAt 2 0]`.
fn first_menu() -> Menu<Clock> {
    Menu::new(3, vec![machine().loop_at(2, BigUint::from(0u32))]).unwrap()
}

/// Lean `menu₂ = [loopAt 1 1, loopAt 2 0]`.
fn second_menu() -> Menu<Clock> {
    first_menu()
        .extended(machine().loop_at(1, BigUint::from(1u32)))
        .unwrap()
}

/// The true candidate at the given ports: rotor offset `0`, identity boundary.
fn truth(at: &[usize]) -> Candidate<Clock> {
    Candidate {
        key: key(0),
        images: PortImages::of(&PortPermutation::identity(3), at).unwrap(),
    }
}

fn offset(candidate: &Candidate<Clock>) -> BigUint {
    candidate.key.ticks() % BigUint::from(3u32)
}

/// Lean `Machine.stage_fixed_iff`, `Machine.loopAt_closes_iff`: the stage at position `m` fixes
/// exactly `2 − m`, so `loopAt a i` closes exactly when `s a = 2 − (k + i)`.
#[test]
fn a_loop_closes_exactly_when_its_stage_fixes_the_boundary_image() {
    let machine = machine();
    for m in 0u32..3 {
        let stage = machine.stage(&BigUint::from(m)).unwrap();
        for y in 0..3usize {
            assert_eq!(stage.apply(y).unwrap() == y, (y + m as usize) % 3 == 2);
        }
    }
    for port in 0..3usize {
        for step in 0u32..3 {
            let current = machine.loop_at(port, BigUint::from(step));
            for key in keys() {
                for images in PortImages::injections(3, &[port]).unwrap() {
                    let candidate = Candidate {
                        key: key.clone(),
                        images,
                    };
                    let k = usize::try_from(offset(&candidate)).unwrap();
                    let image = candidate.images.image(port).unwrap();
                    assert_eq!(
                        current.closes(&candidate).unwrap(),
                        (image + k + step as usize) % 3 == 2
                    );
                }
            }
        }
    }
}

/// Lean `fibre_cons`, `fibre_append_subset`, `truth_mem_fibre` and `Machine.pruning_counts`,
/// `Machine.second_loop_refutes`: over the `18` candidates at the ports `{1, 2}`, one observed loop
/// leaves `6` and two leave `3`; the second loop intersects the first fibre with its own
/// constraint, keeps the true key, and refutes `(0, swap 0 1)`, which the first admits.
#[test]
fn each_loop_only_shrinks_the_fibre_eighteen_six_three() {
    let (first, second) = (first_menu(), second_menu());
    assert_eq!(second.menu_ports(), vec![1, 2]);
    let truth = truth(&[1, 2]);
    assert!(first.observed(&truth).unwrap() && second.observed(&truth).unwrap());
    let candidates = second.candidates(&keys()).unwrap();
    assert_eq!(candidates.len(), 18);
    let pruned_once = first.fibre(&truth, &candidates).unwrap();
    let pruned_twice = second.fibre(&truth, &candidates).unwrap();
    assert_eq!((pruned_once.len(), pruned_twice.len()), (6, 3));
    assert!(pruned_twice.contains(&truth));
    assert!(pruned_twice.iter().all(|kept| pruned_once.contains(kept)));
    let added = machine().loop_at(1, BigUint::from(1u32));
    let truth_closes = added.closes(&truth).unwrap();
    let intersected: Vec<Candidate<Clock>> = pruned_once
        .iter()
        .filter(|candidate| added.closes(candidate).unwrap() == truth_closes)
        .cloned()
        .collect();
    assert_eq!(pruned_twice, intersected);
    let refuted = Candidate {
        key: key(0),
        images: PortImages::of(&PortPermutation::swap(3, 0, 1).unwrap(), &[1, 2]).unwrap(),
    };
    assert!(pruned_once.contains(&refuted) && !pruned_twice.contains(&refuted));
}

/// The candidates the machine's tests read: every key with every injective image of ports
/// `{1, 2}`, the ports of the two-loop menu.
fn candidates() -> Vec<Candidate<Clock>> {
    second_menu().candidates(&keys()).unwrap()
}

/// Whether two candidates agree up to the key clock's period: the same rotor offset and images.
fn same_reading(left: &Candidate<Clock>, right: &Candidate<Clock>) -> bool {
    offset(left) == offset(right) && left.images == right.images
}

/// Lean `Gauge.covariant`, `Machine.stage_succ`, `Machine.rotorGauge`: **a gauge must conjugate
/// every stage word.** The rotor gauge `(k, s) ↦ (k + 1, ρ⁻¹ ∘ s)` is a gauge of both menus,
/// checked at every declared key; advancing the key without turning the boundary is refused at
/// the first loop it breaks, and a turn on another port population is refused.
#[test]
fn a_gauge_must_conjugate_every_stage_word() {
    let machine = machine();
    let rotor = machine.rotor().clone();
    for m in 0u32..6 {
        let next = machine.stage(&BigUint::from(m + 1)).unwrap();
        let stage = machine.stage(&BigUint::from(m)).unwrap();
        let conjugated = rotor
            .inverse()
            .multiply(&stage)
            .unwrap()
            .multiply(&rotor)
            .unwrap();
        assert_eq!(next, conjugated);
    }
    for menu in [first_menu(), second_menu()] {
        let gauge = machine.gauge(&menu, &keys()).unwrap();
        assert_eq!(gauge.boundary(), &rotor);
    }
    let advance = |key: &Clock| {
        let mut advanced = key.clone();
        advanced.advance(&BigUint::from(1u32));
        advanced
    };
    assert_eq!(
        Gauge::new(
            &second_menu(),
            &keys(),
            advance,
            PortPermutation::identity(3)
        )
        .unwrap_err(),
        CompressionError::NotCovariant {
            loop_index: 0,
            key_index: 0
        }
    );
    assert!(matches!(
        Gauge::new(
            &second_menu(),
            &keys(),
            advance,
            PortPermutation::identity(4)
        ),
        Err(CompressionError::Extent { .. })
    ));
}

/// Lean `Gauge.closes_iff`, `Gauge.closureMap_act`, `fibre_gauge_invariant`,
/// `iterate_mem_fibre_iff`, `Machine.gauge_invariant`: **the fibre is a union of gauge orbits.**
/// For both menus, every candidate and each of its gauge iterates have one closure reading, so
/// they lie in the fibre together.
#[test]
fn the_fibre_is_a_union_of_gauge_orbits() {
    let machine = machine();
    let truth = truth(&[1, 2]);
    for menu in [first_menu(), second_menu()] {
        let gauge = machine.gauge(&menu, &keys()).unwrap();
        let reading = menu.closure_map(&truth).unwrap();
        for candidate in candidates() {
            let own = menu.closure_map(&candidate).unwrap();
            for member in gauge.orbit(&candidate, 7).unwrap() {
                assert_eq!(menu.closure_map(&member).unwrap(), own);
                assert_eq!(
                    own == reading,
                    menu.closure_map(&member).unwrap() == reading
                );
            }
        }
    }
}

/// Lean `fibre_gauge_truth`: **no menu separates the true key from its gauge image.** The fibre
/// over every gauge image of the true candidate is the fibre over the true candidate, for both
/// menus; loop closure locates the key only up to the gauge.
#[test]
fn no_menu_separates_the_truth_from_its_gauge_image() {
    let machine = machine();
    let truth = truth(&[1, 2]);
    for menu in [first_menu(), second_menu()] {
        let gauge = machine.gauge(&menu, &keys()).unwrap();
        let fibre = menu.fibre(&truth, &candidates()).unwrap();
        for image in gauge.orbit(&truth, 6).unwrap() {
            assert_eq!(menu.fibre(&image, &candidates()).unwrap(), fibre);
        }
    }
}

/// Lean `fibre_eq_orbit`, `Machine.two_loop_fibre_is_one_orbit`, `Machine.plural_fibre`,
/// `Machine.one_loop_fibre_is_not_one_orbit`: **a pinned fibre is one gauge orbit.** The gauge
/// reaches every key from the true one; with two loops the boundary images at `{1, 2}` are pinned
/// at each key, and the three survivors are exactly the orbit of the true candidate, among them
/// `(1, ρ⁻¹)`. With one loop the image at the unread port `1` is not pinned: `(0, swap 0 1)`
/// survives with the true offset, yet lies on no gauge image of the true candidate.
#[test]
fn a_pinned_fibre_is_one_gauge_orbit() {
    let machine = machine();
    let truth = truth(&[1, 2]);
    let two = second_menu();
    let gauge = machine.gauge(&two, &keys()).unwrap();
    let orbit = gauge.orbit(&truth, 3).unwrap();
    let offsets: Vec<BigUint> = orbit.iter().map(offset).collect();
    assert_eq!(
        offsets,
        (0u32..3).map(BigUint::from).collect::<Vec<BigUint>>()
    );
    let fibre = two.fibre(&truth, &candidates()).unwrap();
    for kept in &fibre {
        let pinned = fibre
            .iter()
            .filter(|other| offset(other) == offset(kept))
            .count();
        assert_eq!(pinned, 1, "one consistent boundary per key");
    }
    assert_eq!(fibre.len(), orbit.len());
    for member in &orbit {
        assert!(fibre.iter().any(|kept| same_reading(kept, member)));
    }
    let plural = Candidate {
        key: key(1),
        images: PortImages::of(&machine.rotor().inverse(), &[1, 2]).unwrap(),
    };
    assert!(fibre.contains(&plural));
    let one = first_menu();
    let unpinned = Candidate {
        key: key(0),
        images: PortImages::of(&PortPermutation::swap(3, 0, 1).unwrap(), &[1, 2]).unwrap(),
    };
    assert!(
        one.fibre(&truth, &candidates())
            .unwrap()
            .contains(&unpinned)
    );
    let orbit = machine
        .gauge(&one, &keys())
        .unwrap()
        .orbit(&truth, 9)
        .unwrap();
    assert!(orbit.iter().all(|member| !same_reading(member, &unpinned)));
}

/// Lean `Machine.known_boundary_locates_key`: with the boundary known to be the identity, one
/// loop leaves only the true rotor offset.
#[test]
fn a_known_boundary_locates_the_key() {
    let menu = first_menu();
    let truth = truth(&[2]);
    let fibre = menu
        .fibre(&truth, &menu.candidates(&keys()).unwrap())
        .unwrap();
    let located: Vec<BigUint> = fibre
        .iter()
        .filter(|candidate| candidate.images == truth.images)
        .map(offset)
        .collect();
    assert_eq!(located, vec![BigUint::from(0u32)]);
}

/// The rotor position is the key clock's odometer phase: the ring's carry keeps it in range.
#[test]
fn the_rotor_position_is_the_key_clock_phase() {
    let machine = machine();
    for offset in 0u32..7 {
        for step in 0u32..7 {
            let mut clock = key(offset);
            clock.advance(&BigUint::from(step));
            assert_eq!(
                machine.position(&key(offset), &BigUint::from(step)),
                clock.phase()[0]
            );
        }
    }
}

/// The images are partial injections: `n!/(n − m)!` of them, a repeated image is refused, and an
/// enumeration past the ceiling is refused before any allocation.
#[test]
fn candidates_are_partial_injections() {
    assert_eq!(PortImages::injections(5, &[0, 3]).unwrap().len(), 20);
    assert_eq!(PortImages::injections(3, &[]).unwrap().len(), 1);
    assert_eq!(
        PortImages::new(3, vec![(0, 1), (2, 1)]),
        Err(CompressionError::NotInjective { port: 2 })
    );
    let wide: Vec<usize> = (0..12).collect();
    assert!(matches!(
        PortImages::injections(12, &wide),
        Err(CompressionError::ImageFamilyCeiling { .. })
    ));
}

/// A loop port outside the menu, and a candidate without the image a loop reads, are refused.
#[test]
fn a_loop_outside_the_menu_is_refused() {
    assert!(matches!(
        Menu::new(3, vec![machine().loop_at(3, BigUint::from(0u32))]),
        Err(CompressionError::LoopPort { port: 3, ports: 3 })
    ));
    assert_eq!(
        second_menu().closure_map(&truth(&[2])),
        Err(CompressionError::MissingImage { port: 1 })
    );
}
