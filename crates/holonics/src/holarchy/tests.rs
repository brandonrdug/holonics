//! Tests of the Holarchy: one per stated law, one per load-bearing counterexample.

use std::collections::BTreeSet;

use num_bigint::{BigInt, BigUint};
use num_traits::Zero;

use super::gluing::turn_rate;
use super::*;
use crate::aeon::{AeonError, ClockLift, epochs};
use crate::geometry::complex::CellComplex;
use crate::geometry::screw::RationalPhase;
use crate::holon::conformance::check_tellegen;
use crate::holon::dirac::DiracStructure;
use crate::holon::element::{Pump, PumpSchedule, ResistiveRelation};
use crate::holon::law::{HolonLaw, ReferenceHolon, Scheme};
use crate::holon::port::{Dimension, Port, PortKind, PortUnits};
use crate::holon::{HolonState, PortCounts, PortHolon};
use crate::navigator::address::LockAddress;
use crate::navigator::{Clock, Navigator, PhaseLift, Transport};
use crate::ratio::linear::inertia::SymmetricForm;
use crate::ratio::linear::vector::{integer_matrix, ints, scale, sub};
use crate::ratio::{integer, rat};

fn zero(rows: usize, columns: usize) -> ExactRatMatrix {
    ExactRatMatrix::zero(rows, columns).unwrap()
}

fn diagonal(value: i64) -> SymmetricForm {
    SymmetricForm::from_diagonal(vec![integer(value)])
}

/// One storage, one resistive element, `inputs` external ports all driving the storage.
fn medium(g: i64, inputs: usize) -> Holon {
    let input = ExactRatMatrix::new(vec![vec![integer(1); inputs]]).unwrap();
    Holon::new(
        PortHolon::medium(
            &zero(1, 1),
            &integer_matrix(&[&[1]]).unwrap(),
            diagonal(g),
            &input,
            false,
        )
        .unwrap(),
    )
    .unwrap()
}

/// A Holon of external ports only, on a declared structure.
fn ports_only(dirac: DiracStructure) -> Holon {
    let external = dirac.ports();
    Holon::new(
        PortHolon::new(
            dirac,
            PortCounts {
                storage: 0,
                resistive: 0,
                external,
                active: 0,
            },
            SymmetricForm::zeros(0),
            ResistiveRelation::new(zero(0, 0)).unwrap(),
        )
        .unwrap(),
    )
    .unwrap()
}

fn shared(pairs: &[(usize, usize)]) -> Gluing {
    Gluing::at_ports(pairs.to_vec()).unwrap()
}

fn bond(flow: &[i64], effort: &[i64]) -> Bond {
    Bond::new(ints(flow), ints(effort)).unwrap()
}

/// A complex with no vertices, `faces` faces and the region boundary `d₂` (`faces × regions`).
fn strip_complex(faces: usize, d2: &[&[i64]]) -> CellComplex {
    let regions = d2[0].len();
    CellComplex::new(
        vec![0, faces, regions],
        vec![zero(0, faces), integer_matrix(d2).unwrap()],
    )
    .unwrap()
}

/// A cellular embedding of a complex with no vertices: faces `m1`, regions `m2`.
fn map(m1: &[&[i64]], m2: &[&[i64]]) -> CellularMap {
    CellularMap::new(vec![
        zero(0, 0),
        integer_matrix(m1).unwrap(),
        integer_matrix(m2).unwrap(),
    ])
    .unwrap()
}

/// A Holon placed on `complex` with its interior chain and the face of each external port.
fn placed(holon: Holon, complex: CellComplex, interior: &[i64], faces: &[usize]) -> Holon {
    holon
        .with_complex(complex, None)
        .with_interior(ints(interior))
        .unwrap()
        .with_port_faces(faces.to_vec())
        .unwrap()
}

/// Three regions in a row, `r_k = e_(k+1) − e_k`: the left Holon owns `r0, r1` (faces
/// `e0, e1, e2`) with its port on `e2`, the right owns `r2` (faces `e2, e3`) with its port on
/// `e2`, and they meet there.
fn strip_gluing() -> (Holon, Holon, Gluing) {
    let glued = strip_complex(4, &[&[-1, 0, 0], &[1, -1, 0], &[0, 1, -1], &[0, 0, 1]]);
    let left = placed(
        medium(2, 1),
        strip_complex(3, &[&[-1, 0], &[1, -1], &[0, 1]]),
        &[1, 1],
        &[2],
    );
    let right = placed(medium(3, 1), strip_complex(2, &[&[-1], &[1]]), &[1], &[0]);
    let cells = CellGluing::new(
        glued,
        None,
        (
            map(
                &[&[1, 0, 0], &[0, 1, 0], &[0, 0, 1], &[0, 0, 0]],
                &[&[1, 0], &[0, 1], &[0, 0]],
            ),
            map(&[&[0, 0], &[0, 0], &[1, 0], &[0, 1]], &[&[0], &[0], &[1]]),
        ),
    );
    (left, right, shared(&[(0, 0)]).with_cells(cells))
}

fn strip() -> Holarchy {
    let (left, right, gluing) = strip_gluing();
    left.interconnect(&right, &gluing).unwrap()
}

/// A passive coholon on one external port (Lean `coholonLeft`, `coholonRight`), placed on
/// `complex` with its port on face `0`.
fn coholon(complex: CellComplex, interior: &[i64]) -> Holon {
    placed(
        ports_only(DiracStructure::passive_coholon(1).unwrap()),
        complex,
        interior,
        &[0],
    )
}

/// One face bounding one region with coefficient `1` (Lean `faceComplex`).
fn face_complex() -> CellComplex {
    strip_complex(1, &[&[1]])
}

/// The two constituents of Lean `sharedDecl`: one face each, glued once into `d₂ = [[a, b]]`, the
/// left region on `r0`, the right on `r1`, the right face embedded with gauge `s`.
fn shared_face(a: i64, b: i64, s: i64) -> (Holon, Holon, Gluing) {
    let cells = CellGluing::new(
        strip_complex(1, &[&[a, b]]),
        None,
        (map(&[&[1]], &[&[1], &[0]]), map(&[&[s]], &[&[0], &[1]])),
    );
    (
        coholon(face_complex(), &[1]),
        coholon(face_complex(), &[1]),
        shared(&[(0, 0)]).with_cells(cells),
    )
}

fn block(cells: &[usize]) -> Block {
    cells.iter().copied().collect()
}

fn grain(blocks: &[&[usize]]) -> Grain {
    Grain::new(blocks.iter().map(|cells| block(cells)).collect())
}

/// Reads each block as itself.
struct Itself;

impl RegionReceiver for Itself {
    type State = ();
    type Face = Block;

    fn read(&self, _: &(), block: &Block) -> Block {
        block.clone()
    }
}

/// Reads a block's mass: how many regions it holds.
struct Mass;

impl RegionReceiver for Mass {
    type State = ();
    type Face = usize;

    fn read(&self, _: &(), block: &Block) -> usize {
        block.len()
    }
}

/// Reads whether a block lies in the left constituent's regions `r0, r1`.
struct Constituent;

impl RegionReceiver for Constituent {
    type State = ();
    type Face = bool;

    fn read(&self, _: &(), block: &Block) -> bool {
        block.iter().all(|cell| *cell < 2)
    }
}

// -------------------------------------------------------------------------------------------
// interconnect

/// `Holarchy/Join.interconnect_ok_retains`: the Holarchy retains both constituents and the gluing;
/// the whole carries both navigator families (`Holarchy.wholeConstituent`).
#[test]
fn interconnect_retains_the_constituents_and_joins_their_navigators() {
    let navigator = Navigator::new(
        Transport::Linear(zero(1, 1)),
        ints(&[1]),
        Clock::ring(integer(1), 3).unwrap(),
        PhaseLift::new(RationalPhase::new(rat(1, 2), 0), BigInt::zero()),
    )
    .unwrap();
    let (left, right) = (medium(2, 1).with_navigator(navigator.clone()), medium(3, 1));
    let gluing = shared(&[(0, 0)]);
    let holarchy = left.interconnect(&right, &gluing).unwrap();
    assert_eq!(
        (holarchy.left(), holarchy.right(), holarchy.gluing()),
        (&left, &right, &gluing)
    );
    assert_eq!(holarchy.whole().navigators(), &[navigator]);
}

/// `Holarchy/Join.Holarchy.parametric`: the whole's parametric orientation is the lift of its
/// navigators' joint clock torus, the left's circle first. A walk of it is an aeon of the whole:
/// each navigator's coordinate reaches its clock's phase, and the flux through its ring section is
/// the jumps its clock counts. A passage of no whole navigator is not a step of it.
#[test]
fn a_wholes_aeon_is_a_walk_of_its_parametric_orientation() {
    let navigator = |period: u64| {
        Navigator::new(
            Transport::Linear(zero(1, 1)),
            ints(&[1]),
            Clock::ring(integer(1), period).unwrap(),
            PhaseLift::new(RationalPhase::new(rat(1, 2), 0), BigInt::zero()),
        )
        .unwrap()
    };
    let (left, right) = (
        medium(2, 1).with_navigator(navigator(3)),
        medium(3, 1).with_navigator(navigator(2)),
    );
    let holarchy = left.interconnect(&right, &shared(&[(0, 0)])).unwrap();
    let lift = holarchy.parametric();
    assert_eq!(lift.periods(), &[BigUint::from(3u32), BigUint::from(2u32)]);
    let moves: Vec<(usize, bool)> = [0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1]
        .iter()
        .map(|navigator| (*navigator, true))
        .collect();
    let start = vec![BigInt::zero(); 2];
    let aeon = lift.walk(start.clone(), &moves).unwrap();
    let reached = lift.torus_point(aeon.end());
    for (index, navigator) in holarchy.whole().navigators().iter().enumerate() {
        let mut clock = navigator.clock().clone();
        let ticks = moves.iter().filter(|(moved, _)| *moved == index).count();
        let jumps = clock.advance(&BigUint::from(ticks));
        assert_eq!(clock.phase(), &reached[index..=index]);
        let section = lift.ring_section(index, clock.period()).unwrap();
        assert_eq!(epochs(&aeon, section).flux(), BigInt::from(jumps));
    }
    assert!(matches!(
        lift.walk(start, &[(2, true)]),
        Err(AeonError::NotAPassage { position: 0 })
    ));
}

/// `Holarchy/Join.interfacePower_cancels_iff`, `gainLink_isDirac`: a transformer join
/// `F = 2`, `E = 1/2` has `EᵀF = 1`, cancels the interface power of every shared bond and
/// composes a Dirac whole.
#[test]
fn a_join_with_et_f_one_cancels_the_interface_power() {
    let gluing = shared(&[(0, 0)])
        .with_gains(
            integer_matrix(&[&[2]]).unwrap(),
            ExactRatMatrix::new(vec![vec![rat(1, 2)]]).unwrap(),
        )
        .unwrap();
    for (flow, effort) in [(1, 0), (0, 1), (3, -2)] {
        assert!(
            gluing
                .interface_power(&bond(&[flow], &[effort]))
                .unwrap()
                .is_zero()
        );
    }
    let holarchy = medium(2, 1).interconnect(&medium(3, 1), &gluing).unwrap();
    assert!(check_tellegen(holarchy.whole().port_holon().dirac()).unwrap() > 0);
}

/// `Holarchy/Join.uncancelledPower_witness`, `interfacePower_same_orientation`: with both flows
/// oriented the same way (`F = −1`, `E = 1`) the join doubles the interface power instead of
/// cancelling it, and `interconnect` returns the witness bond with power `2⟨e, f⟩`.
#[test]
fn a_join_with_both_flows_oriented_alike_is_refused() {
    let gluing = shared(&[(0, 0)])
        .with_gains(
            integer_matrix(&[&[-1]]).unwrap(),
            integer_matrix(&[&[1]]).unwrap(),
        )
        .unwrap();
    let Err(GluingDefect::UncancelledPower { bond, power }) =
        medium(2, 1).interconnect(&medium(3, 1), &gluing)
    else {
        panic!("the same-orientation join must be refused by its interface power");
    };
    assert_eq!(power, integer(2) * bond.power());
    assert!(!power.is_zero());
}

/// `Holarchy/Join.joinHolon_one`, `gainLink_one`: at the equal-effort, opposite-flow join the
/// whole's structure is the Dirac interconnection of the two structures, kinds merged.
#[test]
fn the_unit_gain_join_is_the_dirac_interconnection() {
    let (left, right) = (medium(2, 2), medium(3, 1));
    let holarchy = left.interconnect(&right, &shared(&[(1, 0)])).unwrap();
    let (a, b) = (left.port_holon().counts(), right.port_holon().counts());
    let direct = left
        .port_holon()
        .dirac()
        .interconnect(
            right.port_holon().dirac(),
            &[(a.external_offset() + 1, b.external_offset())],
        )
        .unwrap()
        .relabel(&holarchy.join.layout.composed_order())
        .unwrap();
    assert!(holarchy.whole().port_holon().dirac().same_subspace(&direct));
}

/// `Holarchy/Join.Holarchy.whole` is a function of the retained join, so the whole joins again
/// (`Holarchy.wholeConstituent`) before its port Holon is assembled: three media chained through
/// the first join's unread whole have exactly the port Holon of the same chain joined through that
/// whole once it is read.
#[test]
fn a_whole_joins_again_before_its_port_holon_is_assembled() {
    let (a, b, c) = (medium(2, 2), medium(3, 2), medium(5, 1));
    let first = a.interconnect(&b, &shared(&[(1, 0)])).unwrap();
    let unread = first.whole().interconnect(&c, &shared(&[(1, 0)])).unwrap();
    assert_eq!(unread.whole().counts().storage, 3);
    let read = Holon::new(first.whole().port_holon().clone()).unwrap();
    let joined = read.interconnect(&c, &shared(&[(1, 0)])).unwrap();
    let (unread, joined) = (unread.whole().port_holon(), joined.whole().port_holon());
    assert_eq!(unread.counts(), joined.counts());
    assert!(unread.dirac().same_subspace(joined.dirac()));
    assert_eq!(
        (unread.storage(), unread.resistance()),
        (joined.storage(), joined.resistance())
    );
}

/// `Holarchy/Join.Holarchy.power_balance`, `Holarchy.balance_is_sum`: at an admitted point of the whole,
/// the constituents' port powers (shared ports included) sum to the whole's, the shared power
/// moving between them, and storage rate, dissipation and active power add.
#[test]
fn the_wholes_balance_is_the_sum_of_the_constituents() {
    let holarchy = medium(2, 2)
        .interconnect(&medium(3, 1), &shared(&[(1, 0)]))
        .unwrap();
    let law = ReferenceHolon::new(holarchy.whole().clone(), rat(1, 2), Scheme::Midpoint).unwrap();
    let state = HolonState::new(ints(&[3, -1]));
    let advance = law.advance(&state, &ints(&[2])).unwrap();
    let kinds = law.kinds(&advance).unwrap();
    let x = &state.configuration;
    let reached = &advance.state.configuration;
    let midpoint: Vec<Rat> = x
        .iter()
        .zip(reached)
        .map(|(a, b)| (a + b) / integer(2))
        .collect();
    let velocity = scale(&(integer(1) / law.step()), &sub(reached, x));
    let balance = holarchy
        .power_balance(
            &midpoint,
            &velocity,
            kinds.resistive.flow(),
            &kinds.external,
            &kinds.active,
        )
        .unwrap();
    let (whole, left, right) = (&balance.whole, &balance.left, &balance.right);
    assert_eq!(&left.port + &right.port, whole.port);
    assert_ne!(left.port, whole.port);
    assert_eq!(&left.storage_rate + &right.storage_rate, whole.storage_rate);
    assert_eq!(&left.dissipated + &right.dissipated, whole.dissipated);
    assert_eq!(&left.active + &right.active, whole.active);
    assert!(left.residual().is_zero() && right.residual().is_zero());
}

/// `Holarchy/Join.interface_obstructed_iff`, `interface_plural_iff` with
/// `plural_interface_witness`, `obstructed_interface_witness`, `unique_interface_witness`: two
/// passive coholons leave the shared effort free; a driven wire into a passive coholon is
/// obstructed, exactly where the whole refuses the bond; two wires in series force the shared
/// bond.
#[test]
fn interface_gluing_is_unique_plural_or_obstructed() {
    let coholon = ports_only(DiracStructure::passive_coholon(1).unwrap());
    let wire =
        ports_only(DiracStructure::kirchhoff(&integer_matrix(&[&[1], &[1]]).unwrap()).unwrap());
    let fibre = |left: &Holon, right: &Holon, pair: (usize, usize), whole: Bond| {
        let holarchy = left.interconnect(right, &shared(&[pair])).unwrap();
        let admitted = holarchy
            .whole()
            .port_holon()
            .dirac()
            .contains(&whole)
            .unwrap();
        (holarchy.interface_fibre(&whole).unwrap(), admitted)
    };
    let (plural, admitted) = fibre(&coholon, &coholon, (0, 0), Bond::zero(0));
    assert!(admitted);
    assert_eq!(
        plural,
        InterfaceGluing::Plural {
            particular: bond(&[0], &[0]),
            directions: vec![bond(&[0], &[1])],
        }
    );
    let (obstructed, admitted) = fibre(&wire, &coholon, (1, 0), bond(&[1], &[0]));
    assert!(!admitted);
    assert!(matches!(obstructed, InterfaceGluing::Obstructed { .. }));
    let (unique, admitted) = fibre(&wire, &wire, (1, 0), bond(&[1, -1], &[0, 0]));
    assert!(admitted);
    assert_eq!(unique, InterfaceGluing::Unique(bond(&[-1], &[0])));
}

/// `Holarchy/Join.unitMismatch_witness`, read from the Holons' own named ports:
/// a shared port carrying current on one side and charge on the other is refused.
#[test]
fn mismatched_port_units_are_a_gluing_defect() {
    let power = Dimension::base("W");
    let units = |flow: &str| PortUnits::from_flow_and_power(Dimension::base(flow), power.clone());
    let named = |g: i64, external: &str| {
        medium(g, 1)
            .with_ports(vec![
                Port {
                    name: "q".into(),
                    kind: PortKind::Storage,
                    units: units("C"),
                },
                Port {
                    name: "r".into(),
                    kind: PortKind::Resistive,
                    units: units("A"),
                },
                Port {
                    name: "u".into(),
                    kind: PortKind::External,
                    units: units(external),
                },
            ])
            .unwrap()
    };
    assert_eq!(
        named(2, "A").interconnect(&named(3, "C"), &shared(&[(0, 0)])),
        Err(GluingDefect::UnitMismatch {
            shared: 0,
            left: Some(units("A")),
            right: Some(units("C")),
        })
    );
    assert!(
        named(2, "A")
            .interconnect(&named(3, "A"), &shared(&[(0, 0)]))
            .is_ok()
    );
}

// -------------------------------------------------------------------------------------------
// cells

/// `Holarchy/Join.base_glues`, `Holarchy.sharedFace_silent`, `Holarchy.wholeConstituent`: two
/// coholons sharing their face, the right face reversed, glue; the whole's interior is both
/// regions, the shared face is silent in the whole's boundary, and no unshared port is left.
#[test]
fn two_holons_sharing_a_face_glue_and_the_face_is_silent() {
    let (left, right, gluing) = shared_face(1, -1, -1);
    let holarchy = left.interconnect(&right, &gluing).unwrap();
    let whole = holarchy.whole_interior().unwrap();
    assert_eq!(whole, ints(&[1, 1]));
    let (cells, d) = holarchy.regions().unwrap();
    assert_eq!(
        cells.glued_boundary(d).unwrap().apply(&whole).unwrap(),
        ints(&[0])
    );
    assert_eq!(holarchy.whole().port_faces(), Some(&[][..]));
}

/// `Holarchy/Join.Holarchy.whole_flux`, `CellEmbedding.flux_pullback`: the whole's flux is the
/// sum of the constituents' own fluxes, each read in its own complex; the shared face `e2`
/// enters them with opposite signs, so only the outer faces remain. The whole keeps the
/// constituents' interiors on the glued regions.
#[test]
fn the_wholes_flux_is_the_sum_of_the_constituents_own() {
    let holarchy = strip();
    assert_eq!(holarchy.whole_interior().unwrap(), ints(&[1, 1, 1]));
    let current = ints(&[2, 5, -3, 7]);
    let flux = holarchy.flux(&current).unwrap();
    assert_eq!(&flux.left + &flux.right, flux.whole);
    assert_eq!(flux.left, integer(-2 - 3));
    assert_eq!(flux.right, integer(3 + 7));
    assert_eq!(flux.whole, integer(7 - 2));
}

/// `Holarchy/Join.Holarchy.wholeConstituent`: the whole keeps each unshared port on the image of
/// its own face; the left Holon's second port sits on its face `e0`, so the whole's one external
/// port sits on glued face `0`.
#[test]
fn the_whole_keeps_the_unshared_ports_on_their_faces() {
    let (_, right, gluing) = strip_gluing();
    let left = placed(
        medium(2, 2),
        strip_complex(3, &[&[-1, 0], &[1, -1], &[0, 1]]),
        &[1, 1],
        &[2, 0],
    );
    let holarchy = left.interconnect(&right, &gluing).unwrap();
    assert_eq!(holarchy.whole().port_faces(), Some(&[0][..]));
    assert_eq!(holarchy.whole().interior(), Some(&ints(&[1, 1, 1])[..]));
}

/// `Holarchy/Join.CellEmbedding.m₂_ne_zero`: a zero map sends a cell to no glued cell, so it is
/// no cellular embedding and cannot be declared; it never commutes vacuously.
#[test]
fn a_zero_map_is_not_a_cellular_embedding() {
    assert_eq!(
        CellularMap::new(vec![zero(0, 0), zero(4, 3), zero(3, 2)]),
        Err(HolonError::NotACellularMap { degree: 1, cell: 0 })
    );
}

/// `Holarchy/Join.nonCommutingCells_witness`: the glued complex gives the right region the
/// coefficient `+1` while the right face is embedded reversed, so the right square fails.
#[test]
fn a_non_commuting_embedding_is_refused() {
    let (left, right, gluing) = shared_face(1, 1, -1);
    assert_eq!(
        left.interconnect(&right, &gluing),
        Err(GluingDefect::NonCommutingCells {
            side: Side::Right,
            degree: 2,
        })
    );
}

/// `Holarchy/Join.degenerateCells_witness`: an embedding that commutes but merges the left
/// constituent's two regions into one glued region is refused.
#[test]
fn a_degenerate_embedding_is_refused() {
    let left = coholon(strip_complex(1, &[&[1, 1]]), &[0, 1]);
    let cells = CellGluing::new(
        strip_complex(1, &[&[1, -1]]),
        None,
        (
            map(&[&[1]], &[&[1, 1], &[0, 0]]),
            map(&[&[-1]], &[&[0], &[1]]),
        ),
    );
    assert_eq!(
        left.interconnect(
            &coholon(face_complex(), &[1]),
            &shared(&[(0, 0)]).with_cells(cells)
        ),
        Err(GluingDefect::DegenerateCells {
            side: Side::Left,
            degree: 2,
            cells: (0, 1),
        })
    );
}

/// `Holarchy/Join.uncoveredCells_witness`: a third glued region that neither constituent
/// reaches is refused.
#[test]
fn an_uncovered_glued_cell_is_refused() {
    let cells = CellGluing::new(
        strip_complex(1, &[&[1, -1, 0]]),
        None,
        (
            map(&[&[1]], &[&[1], &[0], &[0]]),
            map(&[&[-1]], &[&[0], &[1], &[0]]),
        ),
    );
    assert_eq!(
        coholon(face_complex(), &[1]).interconnect(
            &coholon(face_complex(), &[1]),
            &shared(&[(0, 0)]).with_cells(cells)
        ),
        Err(GluingDefect::UncoveredCells { degree: 2, cell: 2 })
    );
}

/// `Holarchy/Join.unidentifiedSharedFace_witness`: the shared port sits on glued face `0` from
/// the left and on glued face `1` from the right.
#[test]
fn an_unidentified_shared_face_is_refused() {
    let cells = CellGluing::new(
        strip_complex(2, &[&[1, 0], &[0, -1]]),
        None,
        (
            map(&[&[1], &[0]], &[&[1], &[0]]),
            map(&[&[0], &[-1]], &[&[0], &[1]]),
        ),
    );
    assert_eq!(
        coholon(face_complex(), &[1]).interconnect(
            &coholon(face_complex(), &[1]),
            &shared(&[(0, 0)]).with_cells(cells)
        ),
        Err(GluingDefect::UnidentifiedSharedFace {
            shared: 0,
            left: 0,
            right: 1,
        })
    );
}

/// `Holarchy/Join.strayOverlap_witness`: two regions glued onto one region are refused; so are two
/// constituents that meet on a second face `e1` where no shared port sits, though their shared
/// port's faces meet correctly on `e0`.
#[test]
fn a_stray_overlap_is_refused() {
    let onto_one = CellGluing::new(
        face_complex(),
        None,
        (map(&[&[1]], &[&[1]]), map(&[&[1]], &[&[1]])),
    );
    assert_eq!(
        coholon(face_complex(), &[1]).interconnect(
            &coholon(face_complex(), &[1]),
            &shared(&[(0, 0)]).with_cells(onto_one)
        ),
        Err(GluingDefect::StrayOverlap { degree: 2, cell: 0 })
    );
    let two_faces = || strip_complex(2, &[&[1], &[1]]);
    let on_a_second_face = CellGluing::new(
        strip_complex(2, &[&[1, -1], &[1, -1]]),
        None,
        (
            map(&[&[1, 0], &[0, 1]], &[&[1], &[0]]),
            map(&[&[-1, 0], &[0, -1]], &[&[0], &[1]]),
        ),
    );
    assert_eq!(
        coholon(two_faces(), &[1]).interconnect(
            &coholon(two_faces(), &[1]),
            &shared(&[(0, 0)]).with_cells(on_a_second_face)
        ),
        Err(GluingDefect::StrayOverlap { degree: 1, cell: 1 })
    );
}

/// `Holarchy/Join.sharedFaceUncancelled_witness`, `faceFlows_join_iff`: the right face embedded
/// with the left one's orientation makes the shared face bound the whole with coefficient `2`.
#[test]
fn an_uncancelled_shared_face_is_refused() {
    let (left, right, gluing) = shared_face(1, 1, 1);
    assert_eq!(
        left.interconnect(&right, &gluing),
        Err(GluingDefect::SharedFaceUncancelled {
            shared: 0,
            face: 0,
            left: integer(1),
            right: integer(1),
        })
    );
}

// -------------------------------------------------------------------------------------------
// pumps

/// `Holarchy/Join.pumped_glues`, `OnJointClock.lock`, `pumped_pumps_lock`: pumps of rates `1` and
/// `3/2` join under the joint rate `1/2`; each turns a whole number of times (`2`, `3`) per joint
/// turn, they lock at the address of `2/3`, and the whole's storage in force is their block at
/// every commit, on the joint clock.
#[test]
fn pumps_join_under_a_compatible_joint_clock() {
    let left = medium(2, 1)
        .with_pump(Pump {
            schedule: PumpSchedule::new(vec![diagonal(2), diagonal(4)]).unwrap(),
            clock: Clock::ring(rat(1, 2), 2).unwrap(),
        })
        .unwrap();
    let right = medium(3, 1)
        .with_pump(Pump {
            schedule: PumpSchedule::new(vec![diagonal(3)]).unwrap(),
            clock: Clock::unwound(rat(2, 3)).unwrap(),
        })
        .unwrap();
    let joint = JointClock::new(Clock::unwound(integer(2)).unwrap());
    let holarchy = left
        .interconnect(&right, &shared(&[(0, 0)]).with_joint_clock(joint.clone()))
        .unwrap();
    let rate = |holon: &Holon| turn_rate(&holon.pump().unwrap().clock);
    assert_eq!(joint.multiple(&rate(&left)), Some(BigUint::from(2u32)));
    assert_eq!(joint.multiple(&rate(&right)), Some(BigUint::from(3u32)));
    assert_eq!(integer(3) * rate(&left), integer(2) * rate(&right));
    assert_eq!(
        holarchy.pump_lock().unwrap(),
        Some(LockAddress::from_ratio(&BigInt::from(2), &BigInt::from(3)).unwrap())
    );
    assert_eq!(&holarchy.whole().pump().unwrap().clock, joint.clock());
    for commit in 0..4 {
        assert_eq!(
            holarchy.whole().storage_at(commit),
            &left.storage_at(commit).direct_sum(right.storage_at(commit))
        );
    }
}

/// `Holarchy/Join.incompatibleClocks_witness`: under the joint rate `2`, a pump of rate `1` is no
/// whole multiple of it and is refused.
#[test]
fn incompatible_pump_clocks_are_refused() {
    let pumped = |g: i64, step: Rat| {
        medium(g, 1)
            .with_pump(Pump {
                schedule: PumpSchedule::new(vec![diagonal(g)]).unwrap(),
                clock: Clock::unwound(step).unwrap(),
            })
            .unwrap()
    };
    let joint = JointClock::new(Clock::unwound(rat(1, 2)).unwrap());
    assert_eq!(
        pumped(2, rat(1, 4)).interconnect(
            &pumped(3, integer(1)),
            &shared(&[(0, 0)]).with_joint_clock(joint)
        ),
        Err(GluingDefect::IncompatibleClocks {
            side: Side::Right,
            rate: integer(1),
            joint_rate: Some(integer(2)),
        })
    );
}

// -------------------------------------------------------------------------------------------
// view, count, refine

/// `Holarchy/View.shared_face_cancels`, `interior_face_silent`, `sum_blockFlux`,
/// `total_flux_grain_independent`: at the coarse and the fine grain, every face inside the whole
/// appears in exactly two block boundaries with opposite signs or in none, the block boundaries
/// sum to the whole's, and the block fluxes total the same flux at both grains.
#[test]
fn a_shared_face_cancels_exactly_once_at_every_grain() {
    let holarchy = strip();
    let (cells, d) = holarchy.regions().unwrap();
    let whole = cells
        .glued_boundary(d)
        .unwrap()
        .apply(&holarchy.whole_interior().unwrap())
        .unwrap();
    let current = ints(&[2, 5, -3, 7]);
    let total = holarchy.flux(&current).unwrap().whole;
    for grain in [grain(&[&[0, 1], &[2]]), grain(&[&[0], &[1], &[2]])] {
        let boundaries = holarchy.block_boundaries(&grain).unwrap();
        for (face, whole_coefficient) in whole.iter().enumerate() {
            let touching: Vec<&Rat> = boundaries
                .iter()
                .map(|boundary| &boundary[face])
                .filter(|coefficient| !coefficient.is_zero())
                .collect();
            let sum = touching.iter().fold(Rat::zero(), |sum, c| sum + *c);
            assert_eq!(&sum, whole_coefficient);
            if whole_coefficient.is_zero() {
                assert!(
                    touching.is_empty() || (touching.len() == 2 && *touching[0] == -touching[1])
                );
            }
        }
        let fluxes = holarchy.interface_flux(&grain, &current).unwrap();
        assert_eq!(fluxes.iter().fold(Rat::zero(), |sum, f| sum + f), total);
    }
}

/// `Holarchy/View.count_eq_counted_iff`, `certified_count_eq_faces`, `continents_and_islands`:
/// one receiver certifies two grains of the same three regions and counts `2` and `3`, each the
/// number of distinct faces it returns there.
#[test]
fn count_is_certified_and_counts_the_receivers_faces() {
    let holarchy = strip();
    for (grain, expected) in [
        (grain(&[&[0, 1], &[2]]), 2),
        (grain(&[&[0], &[1], &[2]]), 3),
    ] {
        let faces: BTreeSet<Block> = grain
            .blocks()
            .iter()
            .map(|block| Itself.read(&(), block))
            .collect();
        assert_eq!(
            holarchy.count(&Itself, &grain, &()).unwrap(),
            Count::Counted(expected)
        );
        assert_eq!(faces.len(), expected);
    }
}

/// `Holarchy/View.uncovered_witness`: a region in no block leaves the count unresolved.
#[test]
fn an_uncovered_region_leaves_the_count_unresolved() {
    assert_eq!(
        strip().count(&Itself, &grain(&[&[0], &[1]]), &()).unwrap(),
        Count::Unresolved(Unresolved::Uncovered { cell: 2 })
    );
}

/// `Holarchy/View.overlapping_witness`: overlapping blocks leave the count unresolved where the
/// bare number of blocks would count a region twice.
#[test]
fn overlapping_blocks_leave_the_count_unresolved() {
    assert_eq!(
        strip()
            .count(&Itself, &grain(&[&[0, 1, 2], &[0], &[1, 2]]), &())
            .unwrap(),
        Count::Unresolved(Unresolved::Overlapping {
            cell: 0,
            blocks: (0, 1),
        })
    );
}

/// `Holarchy/View.blind_witness`: a mass receiver reads every singleton alike, so it counts
/// nothing it cannot tell apart.
#[test]
fn a_blind_receiver_leaves_the_count_unresolved() {
    assert_eq!(
        strip()
            .count(&Mass, &grain(&[&[0], &[1], &[2]]), &())
            .unwrap(),
        Count::Unresolved(Unresolved::Indistinct { blocks: (0, 1) })
    );
}

/// `Holarchy/View.refine_flux`: the constituent reading of the fine singletons descends to the
/// coarse grain, and each coarse block's flux is the sum of its fine blocks'.
#[test]
fn refine_descends_and_the_flux_closes_its_square() {
    let holarchy = strip();
    let (fine, coarse) = (grain(&[&[0], &[1], &[2]]), grain(&[&[0, 1], &[2]]));
    let restriction = GrainRestriction::new(&fine, &coarse, vec![0, 0, 1]).unwrap();
    let descent = holarchy
        .refine(&Constituent, &(), &fine, &restriction)
        .unwrap();
    assert_eq!(
        descent.witness().unwrap().factored(),
        &[(0, true), (1, false)]
    );
    let current = ints(&[2, 5, -3, 7]);
    let fine_flux = holarchy.interface_flux(&fine, &current).unwrap();
    let coarse_flux = holarchy.interface_flux(&coarse, &current).unwrap();
    for (coarse_block, flux) in coarse_flux.iter().enumerate() {
        let summed = (0..fine_flux.len())
            .filter(|b| restriction.map()[*b] == coarse_block)
            .fold(Rat::zero(), |sum, b| sum + &fine_flux[b]);
        assert_eq!(&summed, flux);
    }
}

/// `Holarchy/View.refine_defect_witness`: a fine reading that separates two blocks the
/// restriction merges has no coarse reading; the defect retains the merged pair.
#[test]
fn a_reading_that_separates_a_merged_fibre_does_not_refine() {
    let (fine, coarse) = (grain(&[&[0], &[1], &[2]]), grain(&[&[0, 1], &[2]]));
    let restriction = GrainRestriction::new(&fine, &coarse, vec![0, 0, 1]).unwrap();
    let descent = strip().refine(&Itself, &(), &fine, &restriction).unwrap();
    assert!(!descent.descends());
    assert_eq!(descent.defect().unwrap().merged_pairs(), 1);
}

/// Reads a block at a lattice point: regions `r0`, `r1` weigh `1`, `2`, and region `r2` weighs the
/// point's first coordinate.
struct Placed;

impl RegionReceiver for Placed {
    type State = Vec<BigInt>;
    type Face = BigInt;

    fn read(&self, point: &Vec<BigInt>, block: &Block) -> BigInt {
        block
            .iter()
            .map(|cell| match cell {
                0 => BigInt::from(1),
                1 => BigInt::from(2),
                _ => point[0].clone(),
            })
            .sum()
    }
}

/// `Holarchy/View.view_ticks`, `view_unresolved_singleton_iff`, `holarchy_view_flux`: along an
/// aeon of the ring lift the receiver ticks at its section's crossings, forward and back (four
/// ticks, signed count two), each tick reading the occurrence reached and opening the next epoch;
/// at each tick the view's fluxes total the constituents' own fluxes, and its unresolved classes
/// are singletons exactly where the receiver distinguishes every block.
#[test]
fn the_view_ticks_at_the_aeons_crossings_and_totals_the_constituents_fluxes() {
    let holarchy = strip();
    let fine = grain(&[&[0], &[1], &[2]]);
    let lift = ClockLift::new(vec![BigUint::from(3u32)]).unwrap();
    let moves: Vec<(usize, bool)> = [true, true, false, true, true, true, true]
        .iter()
        .map(|forward| (0, *forward))
        .collect();
    let aeon = lift.walk(vec![BigInt::from(1)], &moves).unwrap();
    let current = |point: &Vec<BigInt>| {
        let x = Rat::from_integer(point[0].clone());
        vec![x.clone(), integer(1), -x.clone(), integer(2) * x]
    };
    let section = || lift.ring_section(0, BigUint::from(3u32)).unwrap();
    let views = holarchy
        .view(&Placed, &fine, &aeon, section(), current)
        .unwrap();
    let crossings = epochs(&aeon, section());
    assert_eq!(views.len(), crossings.ticks().len());
    assert_eq!(crossings.flux(), BigInt::from(2));
    assert_eq!(
        views.iter().map(|view| view.epoch).collect::<Vec<_>>(),
        vec![1, 2, 3, 4]
    );
    for (view, tick) in views.iter().zip(crossings.ticks()) {
        assert_eq!(Some(view.epoch), crossings.epoch_of(tick.step + 1));
    }
    assert_eq!(
        views
            .iter()
            .map(|view| view.occurrence[0].clone())
            .collect::<Vec<_>>(),
        [3, 2, 3, 6].map(BigInt::from).to_vec()
    );
    for view in &views {
        let flux = holarchy.flux(&current(&view.occurrence)).unwrap();
        let total = view
            .interface_flux
            .iter()
            .fold(Rat::zero(), |sum, f| sum + f);
        assert_eq!(total, &flux.left + &flux.right);
        let distinguishes =
            view.occurrence[0] != BigInt::from(1) && view.occurrence[0] != BigInt::from(2);
        assert_eq!(
            view.unresolved.iter().all(|class| class.len() == 1),
            distinguishes
        );
    }
    assert_eq!(views[1].unresolved[1], vec![1, 2]);
}
