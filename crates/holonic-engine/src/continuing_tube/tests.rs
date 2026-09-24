//! Laws of the continuing tube, and the measured grain square that fails.
//!
//! The synthetic tests state what the Lean owner
//! `formal/elementary-holonics/ElementaryHolonics/Transport/ContinuingTube.lean` proves. Every test
//! is always runnable: none depends on a fixture, and the grain tube builds its own exact
//! presentation whose shape is the M5 one — a residue pair carried only by non-representative
//! atoms, which is `grain_tower::GrainCensus::fine_only_inside` in the small.

use num_bigint::BigUint;
use num_traits::{One, Zero};
use relational_geometry::Rat;

use super::*;
use holonics::restriction::tower::Tower;
use holonics::restriction::tower::{
    HalvingMigration, ResidualMigration, ResidueTower, ReversePassageReceipt, SwapMigration,
    TwoChartTower, TwoCharts, check_reverse_passage,
};
use crate::grain_tower::GrainPair;
use crate::physical_constraint_complex::ContactClass;
use holonics::law::receiver::DiameterNorm;
use holonics::law::receiver::Horizon;
use holonics::law::receiver::Rung;

fn rational(value: i64) -> Rat {
    Rat::from_integer(num_bigint::BigInt::from(value))
}

fn atom_cell(component: u32, residue: u32, atom: u32) -> GrainCell {
    GrainAddress::new(component, residue, atom).cell(Grain::Atom)
}

fn atom_pair(left: (u32, u32, u32), right: (u32, u32, u32)) -> GrainPair {
    GrainPair::new(
        atom_cell(left.0, left.1, left.2),
        atom_cell(right.0, right.1, right.2),
    )
    .expect("two distinct atoms found a pair")
}

/// The presentation: two contacts, one between the two declared representatives and one between
/// two atoms neither of which is a representative. The second is the whole content — it is the
/// contact the alpha-carbon receiver never sees.
fn grain_reading_tube() -> GrainReadingTube {
    let atom_face = GrainFace::founded(
        Grain::Atom,
        [
            (atom_pair((0, 0, 0), (0, 1, 0)), ContactClass::Inside),
            (atom_pair((0, 0, 5), (0, 2, 7)), ContactClass::Inside),
        ],
    )
    .expect("the atom face is founded from non-Outside readings");
    GrainReadingTube::found(
        "synthetic alpha-carbon selection, label_atom_id == CA",
        rational(64),
        [
            GrainAddress::new(0, 0, 0),
            GrainAddress::new(0, 1, 0),
            GrainAddress::new(0, 2, 0),
        ],
        atom_face,
    )
    .expect("the selection declares one representative per residue")
}

#[test]
fn the_padic_tube_square_commutes() {
    let tower = ResidueTower::new(BigUint::from(2u32)).expect("base two founds a residue tower");
    let tube = ConstantTube::new(tower, 4);
    let charts = vec![0u32, 1, 2, 3];
    let faces = vec![
        (3u32, BigUint::from(5u32)),
        (3u32, BigUint::from(6u32)),
        (2u32, BigUint::from(3u32)),
    ];
    let verdict = check_commuting_square(&tube, &0, &4, &charts, &faces)
        .expect("the constant tube admits the step");
    assert!(
        verdict.commutes(),
        "the p-adic tube's transport is the identity, so every square commutes: {verdict:?}"
    );
    let SquareVerdict::Commutes(commuting) = &verdict else {
        unreachable!("the verdict was asserted to commute");
    };
    assert_eq!(commuting.faces_checked(), 3);
    assert_eq!(
        commuting.population_checked(),
        3,
        "a residue face is one exact value, so the population equals the container count here"
    );
    assert_eq!((commuting.earlier(), commuting.later()), (&0u32, &4u32));
    assert!(
        commuting.squares().contains(&(2u32, 3u32)),
        "the (2,3) square carried a declared face and must be named in the receipt"
    );
}

#[test]
fn the_padic_tube_cross_section_branches_by_p_to_the_k() {
    // Lean counterpart: `padicTube_crossSection_branching`, which is `padicFibre_card p m k = p^k`.
    // The count is cited from `ResidueTower::split_fibre`, not recomputed here.
    let tower = ResidueTower::new(BigUint::from(3u32)).expect("base three founds a residue tower");
    let splitting = tower
        .split_fibre(2, 5, &BigUint::from(4u32), 64)
        .expect("the level-2 face 4 splits over level 5");
    assert_eq!(
        splitting.coset_count(),
        &BigUint::from(3u32).pow(3),
        "three refinement steps branch into exactly p^3 = 27 cross-sections"
    );
    let adjacent = tower
        .split_fibre(2, 3, &BigUint::from(4u32), 64)
        .expect("one adjacent step splits the same face");
    assert_eq!(
        adjacent.coset_count(),
        &BigUint::from(3u32),
        "one refinement step branches into exactly p"
    );
}

#[test]
fn the_padic_tube_carries_its_end_unchanged() {
    // Lean counterpart: `padicTube_carryEnd` — the branching is entirely transverse, and the
    // longitudinal transport moves no continuing object.
    let tower = ResidueTower::new(BigUint::from(5u32)).expect("base five founds a residue tower");
    let tube = ConstantTube::new(tower, 3);
    let face = BigUint::from(17u32);
    for later in 0u32..=3 {
        let carried = tube
            .transport(&0, &later, &3, &face)
            .expect("every station of the constant tube is reachable");
        assert_eq!(carried, face);
    }
}

#[test]
fn a_face_the_section_does_not_carry_is_refused_by_the_transport() {
    let tower = ResidueTower::new(BigUint::from(2u32)).expect("base two founds a residue tower");
    let tube = ConstantTube::new(tower, 2);
    // 9 is not a face at chart 3 of the base-2 tower: the modulus there is 8.
    let refusal = tube
        .transport(&0, &1, &3, &BigUint::from(9u32))
        .expect_err("a face above the chart's modulus is not carried");
    assert!(matches!(
        refusal,
        TubeRefusal::Section(TowerRefusal::FaceNotCarried { .. })
    ));
}

#[test]
fn a_square_face_outside_the_declared_aperture_is_refused() {
    let tower = ResidueTower::new(BigUint::from(2u32)).expect("base two founds a residue tower");
    let tube = ConstantTube::new(tower, 2);
    assert!(matches!(
        check_commuting_square(&tube, &0, &1, &[0u32], &[(1u32, BigUint::zero())]),
        Err(TubeRefusal::FaceOutsideAperture { chart: 1 })
    ));
}

#[test]
fn a_circuit_face_outside_the_declared_aperture_is_refused() {
    let tower = ResidueTower::new(BigUint::from(2u32)).expect("base two founds a residue tower");
    let tube = ConstantTube::new(tower, 2);
    assert!(matches!(
        check_circuit_holonomy(&tube, &[0u32, 0], &[0u32], &[(1u32, BigUint::zero())]),
        Err(TubeRefusal::FaceOutsideAperture { chart: 1 })
    ));
}

#[test]
fn a_step_between_unordered_stations_is_refused() {
    let tower = ResidueTower::new(BigUint::from(2u32)).expect("base two founds a residue tower");
    let tube = ConstantTube::new(tower, 4);
    let refusal = check_commuting_square(&tube, &3, &1, &[0u32, 1], &[])
        .expect_err("station 1 does not follow station 3");
    assert!(matches!(
        refusal,
        TubeRefusal::NotAStep {
            earlier: 3,
            later: 1
        }
    ));
}

#[test]
fn an_absent_station_is_refused() {
    let tower = ResidueTower::new(BigUint::from(2u32)).expect("base two founds a residue tower");
    let tube = ConstantTube::new(tower, 2);
    let refusal = check_commuting_square(&tube, &0, &9, &[0u32], &[])
        .expect_err("station 9 is above the declared ceiling");
    assert!(matches!(refusal, TubeRefusal::NotAStep { .. }));
    assert!(tube.section(&9).is_none());
}

#[test]
fn a_declared_aperture_above_the_ceiling_is_refused_before_any_loop() {
    let tower = ResidueTower::new(BigUint::from(2u32)).expect("base two founds a residue tower");
    let tube = ConstantTube::new(tower, 1);
    let charts: Vec<u32> = (0..(DECLARED_CHART_CEILING as u32 + 1)).collect();
    let refusal = check_commuting_square(&tube, &0, &1, &charts, &[])
        .expect_err("an aperture above the ceiling is refused");
    assert_eq!(
        refusal,
        TubeRefusal::DeclarationAboveCeiling {
            declared: DECLARED_CHART_CEILING + 1,
            ceiling: DECLARED_CHART_CEILING,
        }
    );
}

/// Phase 6: the grain tube's square is the core restriction's descent. Its verdict read as a
/// `Descent` breaks, and the core tower descent through `GrainTower`'s own restriction residual
/// (`Foundation/ContinuingTower.lean::Tower.restrictTransition`) returns the same source and the
/// same two routes; the retained residual reopens the selected fine face, so the defect is not a
/// loss (`Transport/ContinuingTube.lean::grainSquare_defect_is_not_a_loss`).
#[test]
fn the_grain_tube_square_is_the_core_restriction_descent() {
    use holonics::restriction::tower::TowerRestrictTransition;
    use holonics::restriction::{Descent, tower_square_descent};
    let tube = grain_reading_tube();
    let atom_face = tube.complete().atom_face().clone();
    let verdict = check_commuting_square(
        &tube,
        &GrainStation::Complete,
        &GrainStation::Selected,
        &[Grain::Residue, Grain::Atom],
        &[(Grain::Atom, atom_face.clone())],
    )
    .expect("the two stations are ordered and both carry a section");
    let Descent::Defect(defect) = verdict.descent() else {
        panic!("the grain square does not descend");
    };
    let core = tower_square_descent(
        tube.complete(),
        &Grain::Residue,
        &Grain::Atom,
        |face| Ok(tube.select(Grain::Atom, face)),
        |face| Ok(tube.select(Grain::Residue, face)),
        std::slice::from_ref(&atom_face),
    )
    .expect("the grain restriction and its residual are defined on the atom face");
    let breaks = core
        .defect()
        .expect("the core descent breaks where the tube square does");
    let first = breaks.first();
    assert_eq!(first.source(), defect.source_face());
    assert_eq!(
        first.fine_then_restricted(),
        defect.transported_then_restricted()
    );
    assert_eq!(
        first.restricted_then_coarse(),
        defect.restricted_then_transported()
    );
    let reopened = tube
        .complete()
        .restriction_reopen(
            &Grain::Residue,
            &Grain::Atom,
            first.fine_then_restricted(),
            first.fine_residual(),
        )
        .expect("the retained residual reopens the selected fine face");
    assert_eq!(reopened, tube.select(Grain::Atom, &atom_face));
}

#[test]
fn the_grain_tube_square_returns_a_defect_with_its_witness() {
    // Lean counterpart: `grainSquareDefect`, whose witness is
    // `Foundation/GrainRestriction.lean::equal_aperture_is_not_lawful`.
    let tube = grain_reading_tube();
    let atom_face = tube.complete().atom_face().clone();
    let verdict = check_commuting_square(
        &tube,
        &GrainStation::Complete,
        &GrainStation::Selected,
        &[Grain::Residue, Grain::Atom],
        &[(Grain::Atom, atom_face)],
    )
    .expect("the two stations are ordered and both carry a section");
    let SquareVerdict::Defect(defect) = &verdict else {
        panic!("the alpha-carbon receiver does not commute with the atom-to-residue restriction");
    };
    assert_eq!(*defect.coarse(), Grain::Residue);
    assert_eq!(*defect.fine(), Grain::Atom);
    assert_eq!(defect.source_face().classified().len(), 2);
    assert_eq!(
        defect.transported_then_restricted().inside(),
        1,
        "selecting first keeps only the representative-to-representative contact"
    );
    assert_eq!(
        defect.restricted_then_transported().inside(),
        2,
        "restricting first keeps both contacts, because the join over a residue block sees every \
         atom pair"
    );
    assert_ne!(
        defect.transported_then_restricted(),
        defect.restricted_then_transported()
    );
}

#[test]
fn the_grain_square_defect_is_holonomy_and_not_a_loss() {
    // Lean counterpart: `grainSquare_defect_is_not_a_loss`, which cites
    // `grain_residual_reopens_the_source`. What the square loses is agreement between two routes;
    // the selection's own residual still returns the fine face exactly.
    use holonics::restriction::tower::Transition;
    let tube = grain_reading_tube();
    let atom_face = tube.complete().atom_face().clone();
    let receipt = tube
        .selection()
        .check_reopen(&atom_face)
        .expect("the grain selection reopens the fine face from its residual");
    assert_eq!(receipt.sources_reopened, 1);
}

#[test]
fn the_flip_tube_square_commutes_while_its_circuit_has_holonomy() {
    // Lean counterpart: `flipCircuit_hasDefect` beside `Tower.restrict_roundTrip`. The transverse
    // ladder carries no holonomy; the longitudinal axis closed on itself does.
    let tube = FlipTube::new();
    let charts = vec![TwoCharts::Left, TwoCharts::Right];
    let faces = vec![
        (TwoCharts::Left, BigUint::zero()),
        (TwoCharts::Right, BigUint::one()),
    ];
    let square = check_commuting_square(&tube, &0, &1, &charts, &faces)
        .expect("the flip tube admits every step");
    assert!(
        square.commutes(),
        "every transverse square of the flip tube commutes: {square:?}"
    );

    let holonomy = check_circuit_holonomy(&tube, &[0u32, 0], &charts, &faces)
        .expect("the one-step self-circuit is closed");
    assert!(!holonomy.is_identity());
    let HolonomyVerdict::Defect(defect) = &holonomy else {
        unreachable!("the verdict was asserted to be a defect");
    };
    assert_eq!(*defect.chart(), TwoCharts::Left);
    assert_eq!(*defect.entered(), BigUint::zero());
    assert_eq!(*defect.returned(), BigUint::one());
    assert_eq!(defect.circuit(), &[0u32, 0]);
}

#[test]
fn a_functorial_tube_returns_the_identity_around_every_circuit() {
    // Lean counterpart: `tube_circuit_has_no_defect` — a tube whose transports satisfy the functor
    // laws carries no more holonomy than a tower does.
    let tower = ResidueTower::new(BigUint::from(2u32)).expect("base two founds a residue tower");
    let tube = ConstantTube::new(tower, 3);
    let verdict = check_circuit_holonomy(
        &tube,
        &[0u32, 1, 2, 3],
        &[3u32],
        &[(3u32, BigUint::from(5u32))],
    );
    let refusal = verdict.expect_err("a word that does not return is not a circuit");
    assert!(matches!(refusal, TubeRefusal::CircuitNotClosed { .. }));

    let closed = check_circuit_holonomy(&tube, &[0u32, 0], &[3u32], &[(3u32, BigUint::from(5u32))])
        .expect("the self-circuit is closed");
    assert!(closed.is_identity());
}

#[test]
fn the_swap_migration_is_a_wormhole() {
    // Lean counterpart: `swapWormhole` over `twoCharts_no_common_refinement`.
    let migration = SwapMigration::new();
    let receipt = wormhole_receipt(&migration, &[TwoCharts::Left, TwoCharts::Right])
        .expect("two charts are inside the declared ceiling");
    assert!(receipt.is_wormhole());
    assert!(receipt.orders_agreed());
    assert_eq!(receipt.charts_checked(), 2);
    assert_eq!(receipt.crossings().len(), 2);
    assert!(
        receipt
            .crossings()
            .contains(&(TwoCharts::Left, TwoCharts::Right))
    );
}

#[test]
fn the_halving_migration_is_lossy_and_is_not_a_wormhole() {
    // Lean counterpart: `padicHalfMigration_factorsThroughRefinement` beside
    // `padicHalfMigration_face_not_injective` — lossiness and being a wormhole are independent.
    let tower = ResidueTower::new(BigUint::from(3u32)).expect("base three founds a residue tower");
    let migration = HalvingMigration::new(tower, 4).expect("a ceiling of four is admitted");
    let receipt = wormhole_receipt(&migration, &[0u32, 1, 2, 3, 4])
        .expect("five charts are inside the declared ceiling");
    assert!(
        !receipt.is_wormhole(),
        "the halving migration only ever reads a finer chart, so it adds no passage"
    );
    let reverse = check_reverse_passage(
        &migration,
        &1u32,
        &[BigUint::from(0u32), BigUint::from(3u32)],
    )
    .expect("both faces are carried at the source chart");
    assert!(
        matches!(reverse, ReversePassageReceipt::OnlyWithTheResidual { .. }),
        "and it is genuinely lossy: two level-2 faces land on one level-1 face"
    );
}

#[test]
fn the_lossy_swap_is_a_wormhole_and_is_lossy() {
    // Lean counterpart: `lossySwapMigration_connectsIncomparableCharts` and
    // `lossySwapMigration_face_not_injective` — the fourth cell of
    // `lossiness_is_independent_of_being_a_wormhole`.
    let migration = LossySwapMigration::new();
    let receipt = wormhole_receipt(&migration, &[TwoCharts::Left, TwoCharts::Right])
        .expect("two charts are inside the declared ceiling");
    assert!(receipt.is_wormhole());

    let reverse = check_reverse_passage(
        &migration,
        &TwoCharts::Left,
        &[BigUint::zero(), BigUint::one()],
    )
    .expect("both faces are carried");
    assert!(matches!(
        reverse,
        ReversePassageReceipt::OnlyWithTheResidual { .. }
    ));
}

#[test]
fn the_lossy_swap_residual_restores_the_reverse_passage() {
    // Lean counterpart: `lossySwapMigration_residual_restores_the_reverse_passage`, which is
    // `ResidualMigration.traversability_is_the_residual` at a wormhole.
    let migration = LossySwapMigration::new();
    for value in 0u32..8 {
        let receipt = migration
            .check_reopen(&TwoCharts::Left, &BigUint::from(value))
            .expect("the retained bit reopens the source face exactly");
        assert_eq!(receipt.sources_reopened, 1);
    }
}

#[test]
fn a_wormhole_aperture_above_the_ceiling_is_refused() {
    let migration = SwapMigration::new();
    let charts: Vec<TwoCharts> = (0..(DECLARED_CHART_CEILING + 1))
        .map(|index| {
            if index % 2 == 0 {
                TwoCharts::Left
            } else {
                TwoCharts::Right
            }
        })
        .collect();
    let refusal =
        wormhole_receipt(&migration, &charts).expect_err("an aperture above the ceiling is refused");
    assert_eq!(
        refusal,
        WormholeRefusal::DeclarationAboveCeiling {
            declared: DECLARED_CHART_CEILING + 1,
            ceiling: DECLARED_CHART_CEILING,
        }
    );
}

#[test]
fn the_empty_word_is_not_a_circuit() {
    let tower = ResidueTower::new(BigUint::from(2u32)).expect("base two founds a residue tower");
    let tube = ConstantTube::new(tower, 2);
    let refusal = check_circuit_holonomy(&tube, &[], &[0u32], &[])
        .expect_err("the empty word has no holonomy to read");
    assert_eq!(refusal, TubeRefusal::EmptyCircuit);
}

#[test]
fn a_declared_work_product_above_the_ceiling_is_refused_before_any_loop() {
    // The per-axis ceilings admit this declaration; their product does not. The square check is
    // quadratic in the aperture and linear in the face population, and that is what is bounded.
    let tower = ResidueTower::new(BigUint::from(2u32)).expect("base two founds a residue tower");
    let tube = ConstantTube::new(tower, 1);
    let charts: Vec<u32> = (0..1000u32).collect();
    let faces: Vec<(u32, BigUint)> = (0..10u32).map(|k| (0u32, BigUint::from(k))).collect();
    assert!(charts.len() <= DECLARED_CHART_CEILING);
    assert!(faces.len() <= DECLARED_FACE_CEILING);
    let refusal = check_commuting_square(&tube, &0, &1, &charts, &faces)
        .expect_err("ten million comparisons are above the declared work ceiling");
    assert_eq!(
        refusal,
        TubeRefusal::DeclarationAboveCeiling {
            declared: 1000 * 1000 * 10,
            ceiling: DECLARED_WORK_CEILING,
        }
    );
}

// ---------------------------------------------------------------------------------------------
// Declared size: the population inside the containers, and the circuit check's own ceilings
// ---------------------------------------------------------------------------------------------

/// A tube that counts every transport it is asked for and declares a face population of its own,
/// so a test can state what a refused declaration ran: nothing.
#[derive(Debug)]
struct CountingTube {
    section: TwoChartTower,
    population: usize,
    transports: std::cell::Cell<usize>,
}

impl CountingTube {
    fn declaring(population: usize) -> Self {
        Self {
            section: TwoChartTower,
            population,
            transports: std::cell::Cell::new(0),
        }
    }

    fn transports(&self) -> usize {
        self.transports.get()
    }
}

impl StationedTower for CountingTube {
    type Station = u32;
    type Section = TwoChartTower;

    fn follows(&self, _earlier: &u32, _later: &u32) -> bool {
        true
    }

    fn section(&self, _station: &u32) -> Option<&TwoChartTower> {
        Some(&self.section)
    }

    fn declared_face_population(&self, _chart: &TwoCharts, _face: &BigUint) -> usize {
        self.population
    }

    fn transport(
        &self,
        _earlier: &u32,
        _later: &u32,
        _chart: &TwoCharts,
        face: &BigUint,
    ) -> Result<BigUint, TubeRefusal<u32, TwoCharts, BigUint>> {
        self.transports.set(self.transports.get() + 1);
        Ok(face.clone())
    }
}

fn two_faces() -> Vec<(TwoCharts, BigUint)> {
    vec![
        (TwoCharts::Left, BigUint::zero()),
        (TwoCharts::Right, BigUint::one()),
    ]
}

#[test]
fn the_declared_work_counts_the_face_population_and_not_its_containers() {
    // Two containers — a count every per-axis ceiling admits — carrying a face population that no
    // ceiling admits. Counting the containers alone would start a check whose real work is the
    // population inside them, which a transport that copies a face whole actually moves.
    let charts = vec![TwoCharts::Left, TwoCharts::Right];
    let faces = two_faces();
    assert!(faces.len() <= DECLARED_FACE_CEILING);
    assert!(charts.len() <= DECLARED_CHART_CEILING);

    let tube = CountingTube::declaring(DECLARED_FACE_CEILING);
    assert_eq!(
        check_commuting_square(&tube, &0, &1, &charts, &faces)
            .expect_err("a face population above the ceiling is refused"),
        TubeRefusal::DeclarationAboveCeiling {
            declared: 2 * DECLARED_FACE_CEILING,
            ceiling: DECLARED_FACE_CEILING,
        }
    );
    assert_eq!(tube.transports(), 0, "nothing was transported");

    let tube = CountingTube::declaring(DECLARED_FACE_CEILING);
    assert_eq!(
        check_circuit_holonomy(&tube, &[0u32, 0], &charts, &faces)
            .expect_err("the holonomy check reads the same population"),
        TubeRefusal::DeclarationAboveCeiling {
            declared: 2 * DECLARED_FACE_CEILING,
            ceiling: DECLARED_FACE_CEILING,
        }
    );
    assert_eq!(tube.transports(), 0);

    // A population each ceiling admits, whose product with the aperture does not.
    let wide: Vec<TwoCharts> = (0..16)
        .map(|index| {
            if index % 2 == 0 {
                TwoCharts::Left
            } else {
                TwoCharts::Right
            }
        })
        .collect();
    let tube = CountingTube::declaring(60_000);
    let one_face = vec![(TwoCharts::Left, BigUint::zero())];
    assert_eq!(
        check_commuting_square(&tube, &0, &1, &wide, &one_face)
            .expect_err("sixteen charts over sixty thousand entries is above the work ceiling"),
        TubeRefusal::DeclarationAboveCeiling {
            declared: 16 * 16 * 60_000,
            ceiling: DECLARED_WORK_CEILING,
        }
    );
    assert_eq!(tube.transports(), 0);

    // A declared population whose sum overflows is refused, not wrapped.
    let tube = CountingTube::declaring(usize::MAX);
    assert_eq!(
        check_commuting_square(&tube, &0, &1, &charts, &faces)
            .expect_err("the summed population overflows usize"),
        TubeRefusal::DeclarationAboveCeiling {
            declared: usize::MAX,
            ceiling: DECLARED_FACE_CEILING,
        }
    );
    assert_eq!(tube.transports(), 0);

    // And a population the ceilings admit runs, with the receipt naming both counts.
    let tube = CountingTube::declaring(7);
    let verdict = check_commuting_square(&tube, &0, &1, &charts, &faces)
        .expect("fourteen entries over two charts is a small check");
    let SquareVerdict::Commutes(commuting) = &verdict else {
        unreachable!("the identity transport commutes with every restriction");
    };
    assert_eq!((commuting.faces_checked(), commuting.population_checked()), (2, 14));
}

#[test]
fn the_grain_tube_declares_the_population_inside_its_one_container() {
    // The measured case the container count misses: one declared `(chart, face)` pair whose face
    // carries every contact of the presentation, and `GrainReadingTube::select` clones that whole
    // map on the step. The population is read off a borrow, so bounding the check copies nothing.
    let tube = grain_reading_tube();
    let atom_face = tube.complete().atom_face().clone();
    let faces = [(Grain::Atom, atom_face.clone())];
    assert_eq!(faces.len(), 1, "one container");
    assert_eq!(
        tube.declared_face_population(&Grain::Atom, &atom_face),
        atom_face.classified().len(),
        "and the population inside it is the face's own classified count"
    );
    assert!(tube.declared_face_population(&Grain::Atom, &atom_face) > faces.len());
}

#[test]
fn the_circuit_check_refuses_each_of_its_ceilings_by_name_before_it_iterates() {
    let charts = vec![TwoCharts::Left, TwoCharts::Right];
    let faces = two_faces();

    // The circuit word.
    let tube = CountingTube::declaring(1);
    let long: Vec<u32> = vec![0u32; DECLARED_CIRCUIT_CEILING + 1];
    assert_eq!(
        check_circuit_holonomy(&tube, &long, &charts, &faces)
            .expect_err("a circuit word above the ceiling is refused"),
        TubeRefusal::DeclarationAboveCeiling {
            declared: DECLARED_CIRCUIT_CEILING + 1,
            ceiling: DECLARED_CIRCUIT_CEILING,
        }
    );
    assert_eq!(tube.transports(), 0);

    // The chart aperture.
    let tube = CountingTube::declaring(1);
    let many: Vec<TwoCharts> = vec![TwoCharts::Left; DECLARED_CHART_CEILING + 1];
    assert_eq!(
        check_circuit_holonomy(&tube, &[0u32, 0], &many, &faces)
            .expect_err("an aperture above the ceiling is refused"),
        TubeRefusal::DeclarationAboveCeiling {
            declared: DECLARED_CHART_CEILING + 1,
            ceiling: DECLARED_CHART_CEILING,
        }
    );
    assert_eq!(tube.transports(), 0);

    // The face containers.
    let tube = CountingTube::declaring(1);
    let crowd: Vec<(TwoCharts, BigUint)> =
        vec![(TwoCharts::Left, BigUint::zero()); DECLARED_FACE_CEILING + 1];
    assert_eq!(
        check_circuit_holonomy(&tube, &[0u32, 0], &charts, &crowd)
            .expect_err("a face list above the ceiling is refused"),
        TubeRefusal::DeclarationAboveCeiling {
            declared: DECLARED_FACE_CEILING + 1,
            ceiling: DECLARED_FACE_CEILING,
        }
    );
    assert_eq!(tube.transports(), 0);

    // The work product.
    let tube = CountingTube::declaring(1);
    let word: Vec<u32> = vec![0u32; 4000];
    let aperture: Vec<TwoCharts> = vec![TwoCharts::Left; 1000];
    assert_eq!(
        check_circuit_holonomy(&tube, &word, &aperture, &faces)
            .expect_err("four million steps over two entries is above the work ceiling"),
        TubeRefusal::DeclarationAboveCeiling {
            declared: 4000 * 1000 * 2,
            ceiling: DECLARED_WORK_CEILING,
        }
    );
    assert_eq!(tube.transports(), 0);

    // An open word and the empty word are refused after the ceilings and before any transport.
    let tube = CountingTube::declaring(1);
    assert!(matches!(
        check_circuit_holonomy(&tube, &[0u32, 1], &charts, &faces),
        Err(TubeRefusal::CircuitNotClosed { first: 0, last: 1 })
    ));
    assert_eq!(
        check_circuit_holonomy(&tube, &[], &charts, &faces)
            .expect_err("the empty word is not a circuit"),
        TubeRefusal::EmptyCircuit
    );
    assert_eq!(tube.transports(), 0);
}

// ---------------------------------------------------------------------------------------------
// The receipts are produced by their checkers and nowhere else
// ---------------------------------------------------------------------------------------------

#[test]
fn a_verdict_and_a_wormhole_receipt_come_only_from_their_checkers() {
    // Every field of `CommutingSquares`, `SquareDefect`, `IdentityCircuit`, `CircuitDefect` and
    // `WormholeReceipt` is private to `continuing_tube`, and none of the five carries a public
    // constructor, a `Default` or a `Deserialize`. Outside this module
    // `HolonomyVerdict::Identity(IdentityCircuit { .. })` and an empty-crossings `WormholeReceipt`
    // do not compile, so holding one of these values *is* the statement that its checker ran. What
    // a caller can still do is read it, which is what this exercises on genuinely produced ones.
    let tower = ResidueTower::new(BigUint::from(2u32)).expect("base two founds a residue tower");
    let tube = ConstantTube::new(tower, 3);

    let square = check_commuting_square(&tube, &0, &2, &[2u32, 3], &[(3u32, BigUint::from(5u32))])
        .expect("the constant tube admits the step");
    let commuting = square
        .commuting()
        .expect("the identity transport commutes with every restriction");
    assert_eq!((commuting.earlier(), commuting.later()), (&0u32, &2u32));
    assert!(commuting.squares().contains(&(2u32, 3u32)));
    assert_eq!(
        (commuting.faces_checked(), commuting.population_checked()),
        (1, 1)
    );
    assert!(square.defect().is_none(), "one verdict, not both arms");

    let holonomy =
        check_circuit_holonomy(&tube, &[0u32, 0], &[3u32], &[(3u32, BigUint::from(5u32))])
            .expect("the self-circuit is closed");
    let identity = holonomy
        .identity()
        .expect("a functorial tube returns every face");
    assert_eq!(identity.circuit(), &[0u32, 0]);
    assert_eq!(
        (
            identity.charts_checked(),
            identity.faces_checked(),
            identity.population_checked()
        ),
        (1, 1, 1)
    );
    assert!(holonomy.defect().is_none());

    let flip = FlipTube::new();
    let charts = vec![TwoCharts::Left, TwoCharts::Right];
    let faces = two_faces();
    let defect = check_circuit_holonomy(&flip, &[0u32, 0], &charts, &faces)
        .expect("the one-step self-circuit is closed");
    let witness = defect.defect().expect("the flip does not return its faces");
    assert_eq!(*witness.chart(), TwoCharts::Left);
    assert_eq!(*witness.entered(), BigUint::zero());
    assert_eq!(*witness.returned(), BigUint::one());
    assert!(defect.identity().is_none());

    let grain = grain_reading_tube();
    let atom_face = grain.complete().atom_face().clone();
    let grain_square = check_commuting_square(
        &grain,
        &GrainStation::Complete,
        &GrainStation::Selected,
        &[Grain::Residue, Grain::Atom],
        &[(Grain::Atom, atom_face)],
    )
    .expect("the two stations are ordered");
    let square_defect = grain_square
        .defect()
        .expect("the alpha-carbon receiver does not commute");
    assert_eq!(*square_defect.earlier(), GrainStation::Complete);
    assert_eq!(*square_defect.later(), GrainStation::Selected);
    assert!(grain_square.commuting().is_none());

    let receipt = wormhole_receipt(&SwapMigration::new(), &[TwoCharts::Left, TwoCharts::Right])
        .expect("two charts are inside the declared ceiling");
    assert!(receipt.is_wormhole());
    assert_eq!(receipt.charts_checked(), 2);
    assert!(receipt.orders_agreed());
    assert_eq!(receipt.crossings().len(), 2);
}

// ---------------------------------------------------------------------------------------------
// The citation table
// ---------------------------------------------------------------------------------------------

/// The Lean names this module's header correspondence table cites, parsed from the module's own
/// source exactly as an exterior citation test parses it: rows `//! | ` + backticked Lean names +
/// `| ` + the Rust owner, Lean names in the first column.
fn cited_lean_names(module_source: &str) -> Vec<String> {
    module_source
        .lines()
        .map(str::trim_start)
        .filter(|line| line.starts_with("//! | `"))
        .filter_map(|line| line.strip_prefix("//! |"))
        .filter_map(|row| row.split('|').next())
        .flat_map(|cell| {
            cell.split('`')
                .skip(1)
                .step_by(2)
                .map(|name| name.trim().to_owned())
                .collect::<Vec<String>>()
        })
        .collect()
}

/// Whether the Lean owner declares a cited name. Lean writes a declaration unqualified inside its
/// own `namespace`, so a qualified citation such as `Tube.square` is resolved by its final segment;
/// structure fields and inductive constructors are declarations too.
fn lean_declares(owner: &str, cited: &str) -> bool {
    let segment = cited.rsplit('.').next().unwrap_or(cited);
    owner.lines().any(|line| {
        let line = line.trim_start();
        let head = [
            "theorem ",
            "lemma ",
            "def ",
            "noncomputable def ",
            "structure ",
            "inductive ",
            "abbrev ",
            "class ",
            "instance ",
            "| ",
        ]
        .iter()
        .find_map(|keyword| line.strip_prefix(keyword))
        .unwrap_or(line);
        [cited, segment].iter().any(|name| {
            head.strip_prefix(*name).is_some_and(|rest| {
                !rest.starts_with(|character: char| {
                    character.is_alphanumeric() || character == '_' || character == '\''
                })
            })
        })
    })
}

#[test]
fn every_lean_name_the_header_cites_is_declared_by_the_lean_owner() {
    let module = include_str!("../continuing_tube.rs");
    let owner = include_str!(
        "../../../../formal/elementary-holonics/ElementaryHolonics/Transport/ContinuingTube.lean"
    );
    let names = cited_lean_names(module);
    assert!(
        names.len() >= 15,
        "the header's correspondence table went missing: {} names parsed",
        names.len()
    );
    for name in &names {
        assert!(
            lean_declares(owner, name),
            "Transport/ContinuingTube.lean declares no `{name}`, so the header cites a name that \
             does not exist"
        );
    }
}

// ---------------------------------------------------------------------------------------------
// T5 — the two-axis horizon
// ---------------------------------------------------------------------------------------------

use holonics::law::receiver::WidthWitness;

/// The `p`-adic cross-section as a tube: one residue tower at every station, carried by the
/// identity. Its restriction is a genuine many-to-one map, so its charts have real fibres.
fn residue_tube(base: u32, ceiling: u32) -> ConstantTube<ResidueTower> {
    ConstantTube::new(
        ResidueTower::new(BigUint::from(base)).expect("a base of at least two"),
        ceiling,
    )
}

/// Every residue at one chart of the residue tower, as a declared fibre population.
fn residue_candidates(base: u32, chart: u32) -> Vec<(u32, BigUint)> {
    let modulus = base.pow(chart);
    (0..modulus)
        .map(|value| (chart, BigUint::from(value)))
        .collect()
}

/// The residue itself, as an exact count. No float participates.
#[derive(Debug, Clone)]
struct ResidueReading;

impl<T: StationedTower<Section = ResidueTower>> FaceReading<T> for ResidueReading {
    fn name(&self) -> &str {
        "the residue itself, as an exact count"
    }

    fn read(
        &self,
        _station: &TubeStation<T>,
        _chart: &u32,
        face: &BigUint,
    ) -> Result<ExactFace, WidthRefusal> {
        Ok(ExactFace::Count(num_bigint::BigInt::from(face.clone())))
    }
}

/// A five-chart ladder of Boolean faces whose declared step is the identity at every chart but the
/// finest, where it is the flip. Its square with the restriction fails exactly at the pairs that
/// carry chart `4`. This is `Transport/ContinuingTube.lean::ladderStep`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct LadderTower;

impl Tower for LadderTower {
    type Index = u32;
    type Face = bool;

    fn refines(&self, coarse: &u32, fine: &u32) -> bool {
        coarse <= fine
    }

    fn carries(&self, _chart: &u32, _face: &bool) -> bool {
        true
    }

    fn restrict(
        &self,
        coarse: &u32,
        fine: &u32,
        face: &bool,
    ) -> Result<bool, TowerRefusal<u32, bool>> {
        if !self.refines(coarse, fine) {
            return Err(TowerRefusal::NotARefinement {
                coarse: *coarse,
                fine: *fine,
            });
        }
        Ok(*face)
    }
}

/// The ladder as a declared tube of two stations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct LadderTube {
    section: LadderTower,
}

impl StationedTower for LadderTube {
    type Station = u32;
    type Section = LadderTower;

    fn follows(&self, earlier: &u32, later: &u32) -> bool {
        earlier <= later && *later <= 1
    }

    fn section(&self, station: &u32) -> Option<&LadderTower> {
        if *station <= 1 { Some(&self.section) } else { None }
    }

    fn transport(
        &self,
        earlier: &u32,
        later: &u32,
        chart: &u32,
        face: &bool,
    ) -> Result<bool, TubeRefusal<u32, u32, bool>> {
        if !self.follows(earlier, later) {
            return Err(TubeRefusal::NotAStep {
                earlier: *earlier,
                later: *later,
            });
        }
        if earlier == later {
            return Ok(*face);
        }
        Ok(if *chart == 4 { !*face } else { *face })
    }
}

/// The identity receiver on a Boolean face: it separates the two routes of the ladder's failing
/// square exactly.
#[derive(Debug, Clone, Copy)]
struct LadderFlag;

impl FaceReading<LadderTube> for LadderFlag {
    fn name(&self) -> &str {
        "the Boolean face itself"
    }

    fn read(
        &self,
        _station: &u32,
        _chart: &u32,
        face: &bool,
    ) -> Result<ExactFace, WidthRefusal> {
        Ok(ExactFace::Flag(*face))
    }
}

/// A poorer receiver: it reads every face alike, so it reads the ladder's defect flat. This is
/// `Transport/ContinuingTube.lean::poorLadderReading`.
#[derive(Debug, Clone, Copy)]
struct BlindReading;

impl FaceReading<LadderTube> for BlindReading {
    fn name(&self) -> &str {
        "a receiver that reads every face alike"
    }

    fn read(
        &self,
        _station: &u32,
        _chart: &u32,
        _face: &bool,
    ) -> Result<ExactFace, WidthRefusal> {
        Ok(ExactFace::Flag(false))
    }
}

/// Three stations in a cycle whose closing step is the Boolean flip: every square commutes, the
/// circuit that stays inside longitudinal distance `1` returns the identity, and the circuit that
/// reaches distance `2` does not. This is `Transport/ContinuingTube.lean::cycleTube`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct CycleTube {
    section: TwoChartTower,
}

impl StationedTower for CycleTube {
    type Station = u32;
    type Section = TwoChartTower;

    fn follows(&self, _earlier: &u32, _later: &u32) -> bool {
        true
    }

    fn section(&self, _station: &u32) -> Option<&TwoChartTower> {
        Some(&self.section)
    }

    fn transport(
        &self,
        earlier: &u32,
        later: &u32,
        _chart: &TwoCharts,
        face: &BigUint,
    ) -> Result<BigUint, TubeRefusal<u32, TwoCharts, BigUint>> {
        if (*earlier, *later) == (2, 0) {
            return Ok((face + BigUint::one()) % BigUint::from(2u32));
        }
        Ok(face.clone())
    }
}

fn horizon(longitudinal: usize, index: usize) -> Horizon {
    Horizon::declare(longitudinal, index).expect("a horizon inside both ceilings")
}

/// `Foundation/ReceiverRelease.lean::chainDistance_symm` and the cover ladder: the index distance
/// counts covers, is symmetric, and names the direction each chart lies in.
#[test]
fn the_index_distance_counts_covers_and_is_symmetric() {
    let tube = residue_tube(3, 2);
    let charts = vec![0_u32, 1, 2];
    let down = index_distance(&tube, &0, &charts, &2, &0).expect("a reading");
    let up = index_distance(&tube, &0, &charts, &0, &2).expect("a reading");
    assert_eq!(down.steps(), Some(2));
    assert_eq!(up.steps(), Some(2), "the distance is symmetric");
    assert_eq!(down.direction(), Some(IndexDirection::Coarser));
    assert_eq!(up.direction(), Some(IndexDirection::Finer));
    assert_eq!(
        index_distance(&tube, &0, &charts, &1, &2)
            .expect("a reading")
            .steps(),
        Some(1),
        "one cover is one step"
    );
    // The aperture is part of the reading: without the intermediate chart the same two charts are
    // one cover apart, because there is no declared chart between them.
    let coarse_aperture = vec![0_u32, 2];
    assert_eq!(
        index_distance(&tube, &0, &coarse_aperture, &0, &2)
            .expect("a reading")
            .steps(),
        Some(1)
    );
}

/// A chart no chain reaches is the wormhole case, returned as a value. `continuing_tower`'s
/// two-chart index has no common refinement at all, so its charts are exactly that.
#[test]
fn a_chart_no_chain_reaches_is_the_wormhole_case_and_never_an_infinite_distance() {
    let tube = ConstantTube::new(TwoChartTower, 1);
    let charts = vec![TwoCharts::Left, TwoCharts::Right];
    let reading =
        index_distance(&tube, &0, &charts, &TwoCharts::Left, &TwoCharts::Right).expect("a reading");
    assert!(reading.is_wormhole());
    assert_eq!(reading.steps(), None);
    assert!(matches!(
        reading,
        IndexReading::NoChain {
            charts_declared: 2,
            ..
        }
    ));
}

/// `Foundation/ReceiverRelease.lean::looking_toward_the_coarse_is_determined_and_toward_the_fine_is_plural`.
/// One step toward the coarse returns a single determined face; one step toward the fine returns
/// the whole fibre, whose size is `padicFibre_card`'s `p ^ 1`.
#[test]
fn the_reach_is_a_face_toward_the_coarse_and_a_fibre_toward_the_fine() {
    let tube = residue_tube(3, 1);
    let charts = vec![0_u32, 1, 2];
    let declaration = HorizonDeclaration::declare(
        Observer::at(0_u32, 1_u32),
        horizon(0, 1),
        vec![0],
        charts,
        vec![(1_u32, BigUint::from(2u32))],
    )
    .expect("the declaration is inside every ceiling");
    let candidates = residue_candidates(3, 2);
    let reach = horizon_reach(&tube, &declaration, &BigUint::from(2u32), &candidates)
        .expect("the reach walks");

    assert_eq!(reach.toward_the_coarse(), 1, "one determined coarse face");
    assert_eq!(
        reach.toward_the_fine(),
        3,
        "the fibre over 2 mod 3 inside 9 is {{2, 5, 8}}: p ^ 1 members"
    );
    assert_eq!(reach.fibre_members(), 3);
    let coarse: Vec<&ReachEntry<u32, u32, BigUint>> = reach
        .entries()
        .iter()
        .filter(|entry| entry.direction() == IndexDirection::Coarser)
        .collect();
    assert_eq!(coarse.len(), 1);
    assert_eq!(coarse[0].plurality(), Plurality::Determined);
    assert_eq!(*coarse[0].face(), BigUint::zero());
    let fine: Vec<BigUint> = reach
        .entries()
        .iter()
        .filter(|entry| entry.direction() == IndexDirection::Finer)
        .map(|entry| entry.face().clone())
        .collect();
    assert_eq!(
        fine,
        vec![BigUint::from(2u32), BigUint::from(5u32), BigUint::from(8u32)]
    );
    assert!(
        reach
            .entries()
            .iter()
            .filter(|entry| entry.direction() == IndexDirection::Finer)
            .all(|entry| entry.plurality() == Plurality::FibreMember)
    );
    assert!(reach.unreachable_charts().is_empty());
}

/// `Foundation/ReceiverRelease.lean::twoAxisWidth_mono_longitudinal` and `twoAxisWidth_mono_index`:
/// the width is monotone in each coordinate separately, and the index-only step is what the
/// one-axis width could not read.
#[test]
fn the_two_axis_width_is_monotone_in_each_coordinate() {
    let tube = residue_tube(3, 2);
    let charts = vec![0_u32, 1, 2];
    let candidates = residue_candidates(3, 2);
    let width_at = |h: usize, k: usize| -> Rat {
        let declaration = HorizonDeclaration::declare(
            Observer::at(0_u32, 1_u32),
            horizon(h, k),
            vec![0, 1, 2],
            charts.clone(),
            vec![(1_u32, BigUint::from(2u32))],
        )
        .expect("the declaration is inside every ceiling");
        let reach = horizon_reach(&tube, &declaration, &BigUint::from(2u32), &candidates)
            .expect("the reach walks");
        two_axis_width::<ConstantTube<ResidueTower>>(&ResidueReading, &reach, DiameterNorm::Supremum)
            .expect("an exact width")
            .diameter()
            .clone()
    };
    let corner = width_at(0, 0);
    assert_eq!(corner, Rat::zero(), "the observer alone has no width");
    assert!(width_at(1, 0) >= corner);
    assert!(width_at(0, 1) >= corner);
    assert!(width_at(1, 1) >= width_at(1, 0));
    assert!(width_at(1, 1) >= width_at(0, 1));
    assert!(width_at(2, 2) >= width_at(1, 1));
    // The constant tube carries every face unchanged, so the longitudinal axis contributes nothing
    // and the whole width is the fibre's: the coarse face 0 against the fibre member 8.
    assert_eq!(width_at(1, 0), Rat::zero());
    assert_eq!(width_at(0, 1), Rat::from_integer(num_bigint::BigInt::from(8)));
}

/// `Foundation/ReceiverRelease.lean::twoAxisWidth_at_index_zero_is_the_longitudinal_width`: at
/// `k = 0` the two-axis width **is** the width `receiver_release` already owned over the
/// longitudinal family, so its theorems are that case and are not restated.
#[test]
fn the_longitudinal_only_case_is_the_existing_width() {
    let tube = LadderTube {
        section: LadderTower,
    };
    let charts = vec![0_u32, 1, 2, 3, 4];
    let declaration = HorizonDeclaration::declare(
        Observer::at(0_u32, 4_u32),
        Horizon::longitudinal_only(1).expect("inside the ceiling"),
        vec![0, 1],
        charts,
        vec![(4_u32, false)],
    )
    .expect("the declaration is inside every ceiling");
    let reach = horizon_reach(&tube, &declaration, &false, &[]).expect("the reach walks");
    let two_axis = two_axis_width(&LadderFlag, &reach, DiameterNorm::Supremum).expect("a width");

    // The same family, read through `receiver_release`'s own diameter.
    let faces = vec![ExactFace::Flag(false), ExactFace::Flag(true)];
    let one_axis = holonics::law::receiver::width_over_readings(
        "the Boolean face itself",
        two_axis.lineage(),
        &faces,
        DiameterNorm::Supremum,
    )
    .expect("a width");
    assert_eq!(two_axis.diameter(), one_axis.diameter());
    assert_eq!(two_axis.diameter(), &Rat::one());
    assert_eq!(two_axis.attaining(), &WidthWitness::Pair { left: 0, right: 1 });
    assert_eq!(
        reach.entries().len(),
        2,
        "at k = 0 the reach is the observer's own chart carried along the word"
    );
}

/// `Transport/ContinuingTube.lean::flat_near_curved_far`. One exact tube: every square commutes at
/// every horizon, the circuit inside longitudinal distance `1` returns the identity, and the circuit
/// that reaches distance `2` carries holonomy.
#[test]
fn a_tube_can_be_a_sharp_lattice_near_and_curved_far() {
    let tube = CycleTube {
        section: TwoChartTower,
    };
    let faces = vec![(TwoCharts::Left, BigUint::zero())];
    let charts = vec![TwoCharts::Left, TwoCharts::Right];
    let near = HorizonDeclaration::declare(
        Observer::at(0_u32, TwoCharts::Left),
        horizon(1, 1),
        vec![0, 1, 2],
        charts.clone(),
        faces.clone(),
    )
    .expect("inside every ceiling")
    .with_circuits(vec![vec![0, 1, 0], vec![0, 1, 2, 0]])
    .expect("two declared circuits");
    let far = HorizonDeclaration::declare(
        Observer::at(0_u32, TwoCharts::Left),
        horizon(2, 1),
        vec![0, 1, 2],
        charts,
        faces,
    )
    .expect("inside every ceiling")
    .with_circuits(vec![vec![0, 1, 0], vec![0, 1, 2, 0]])
    .expect("two declared circuits");

    let near_profile = defect_profile(
        &tube,
        &near,
        &BooleanResidueReading,
        &Rat::zero(),
        DiameterNorm::Supremum,
    )
    .expect("a profile");
    let far_profile = defect_profile(
        &tube,
        &far,
        &BooleanResidueReading,
        &Rat::zero(),
        DiameterNorm::Supremum,
    )
    .expect("a profile");

    assert!(near_profile.is_flat(), "inside (1, 1) the tube is flat");
    assert_eq!(near_profile.circuits_checked(), 1, "only the near circuit");
    assert!(!far_profile.is_flat());
    assert_eq!(far_profile.circuits_checked(), 2);
    assert_eq!(far_profile.holonomies().len(), 1);
    assert_eq!(
        far_profile.holonomies()[0].circuit(),
        &[0, 1, 2, 0],
        "the holonomy is the circuit that reaches station 2"
    );
    assert_eq!(far_profile.holonomies()[0].entered(), &BigUint::zero());
    assert_eq!(far_profile.holonomies()[0].returned(), &BigUint::one());
    // Every square commutes at both horizons: the curvature is in the declared longitudinal family
    // and never in the transverse ladder, which `Tower.restrict_roundTrip` excludes.
    assert_eq!(near_profile.non_commuting(), 0);
    assert_eq!(far_profile.non_commuting(), 0);
    // And the two charts of that index are joined by no chain at all.
    assert_eq!(far_profile.unreachable_charts(), &[TwoCharts::Right]);
}

/// The residue face of the two-chart tower, read as an exact count.
#[derive(Debug, Clone, Copy)]
struct BooleanResidueReading;

impl FaceReading<CycleTube> for BooleanResidueReading {
    fn name(&self) -> &str {
        "the exact residue of the two-chart face"
    }

    fn read(
        &self,
        _station: &u32,
        _chart: &TwoCharts,
        face: &BigUint,
    ) -> Result<ExactFace, WidthRefusal> {
        Ok(ExactFace::Count(num_bigint::BigInt::from(face.clone())))
    }
}

/// `Transport/ContinuingTube.lean::the_fine_observer_sees_at_one_step_what_the_coarse_one_sees_at_three`
/// and `visibleSquare_shift`. Two observers of one region read different profiles, and their
/// profiles are related by their own index distance.
#[test]
fn two_observers_of_one_region_read_different_profiles() {
    let tube = LadderTube {
        section: LadderTower,
    };
    let charts = vec![0_u32, 1, 2, 3, 4];
    let faces: Vec<(u32, bool)> = charts.iter().map(|chart| (*chart, false)).collect();
    let profile_at = |chart: u32, k: usize| {
        let declaration = HorizonDeclaration::declare(
            Observer::at(0_u32, chart),
            horizon(1, k),
            vec![0, 1],
            charts.clone(),
            faces.clone(),
        )
        .expect("inside every ceiling");
        defect_profile(
            &tube,
            &declaration,
            &LadderFlag,
            &Rat::zero(),
            DiameterNorm::Supremum,
        )
        .expect("a profile")
    };

    let fine = profile_at(4, 1);
    assert_eq!(
        fine.non_commuting(),
        1,
        "the observer at the finest chart reads the defect one step into its horizon"
    );
    assert_eq!(fine.charts_visible(), &[3, 4]);
    assert_eq!(fine.squares_with_no_declared_face(), 0);

    let coarse_two = profile_at(1, 2);
    assert!(
        coarse_two.is_flat(),
        "three cover steps below, two steps of horizon read a sharp lattice"
    );
    assert_eq!(coarse_two.charts_visible(), &[0, 1, 2, 3]);
    assert!(coarse_two.squares_checked() > 0, "and it read real squares");

    let coarse_three = profile_at(1, 3);
    assert_eq!(
        coarse_three.non_commuting(),
        4,
        "at three steps it reaches chart 4 and reads every square that carries it"
    );

    // The exact relation: the index distance between the two observers is 3, and every chart the
    // fine observer sees at k is one the coarse observer sees at k + 3.
    let distance = index_distance(&tube, &0, &charts, &1, &4)
        .expect("a reading")
        .steps()
        .expect("a chain");
    assert_eq!(distance, 3);
    for k in 0..=1 {
        let seen_by_the_fine = profile_at(4, k);
        let seen_by_the_coarse = profile_at(1, k + distance);
        assert!(
            seen_by_the_fine
                .charts_visible()
                .iter()
                .all(|chart| seen_by_the_coarse.charts_visible().contains(chart)),
            "the shift relation at k = {k}"
        );
    }
}

/// `Transport/ContinuingTube.lean::tube_profile_is_flat_at_every_horizon` and
/// `tube_circuit_has_no_defect`: a functorial tube has an identically zero profile, so curvature is
/// a property of declared circuits and non-commuting families and of nothing else.
#[test]
fn a_functorial_tube_has_an_identically_zero_profile() {
    let tube = residue_tube(3, 3);
    let charts = vec![0_u32, 1, 2];
    let faces = vec![(2_u32, BigUint::from(5u32)), (1_u32, BigUint::from(2u32))];
    for h in 0..=3 {
        for k in 0..=2 {
            let declaration = HorizonDeclaration::declare(
                Observer::at(0_u32, 2_u32),
                horizon(h, k),
                vec![0, 1, 2, 3],
                charts.clone(),
                faces.clone(),
            )
            .expect("inside every ceiling")
            // A functorial tube's own closed circuits are the ones its order admits: a station
            // to itself. `tube_circuit_has_no_defect` is exactly this case.
            .with_circuits(vec![vec![0, 0], vec![1, 1, 1]])
            .expect("declared circuits");
            let profile = defect_profile(
                &tube,
                &declaration,
                &ResidueReading,
                &Rat::zero(),
                DiameterNorm::Supremum,
            )
            .expect("a profile");
            assert!(
                profile.is_flat(),
                "a functorial tube is flat at ({h}, {k}): squares {} circuits {}",
                profile.squares_checked(),
                profile.circuits_checked()
            );
            assert_eq!(profile.maximal_discrepancy(), &Rat::zero());
        }
    }
}

/// `Transport/ContinuingTube.lean::a_poorer_receiver_reads_the_defect_flat` and
/// `receiver_defect_is_a_structural_defect`: the profile is a reading, not the identity of the
/// region. A richer receiver exposes what a poorer one reads flat, and never the other way round.
#[test]
fn a_poorer_receiver_reads_flat_what_a_richer_one_separates() {
    let tube = LadderTube {
        section: LadderTower,
    };
    let charts = vec![3_u32, 4];
    let declaration = HorizonDeclaration::declare(
        Observer::at(0_u32, 4_u32),
        horizon(1, 1),
        vec![0, 1],
        charts,
        vec![(4_u32, false)],
    )
    .expect("inside every ceiling");

    let rich = defect_profile(
        &tube,
        &declaration,
        &LadderFlag,
        &Rat::zero(),
        DiameterNorm::Supremum,
    )
    .expect("a profile");
    let poor = defect_profile(
        &tube,
        &declaration,
        &BlindReading,
        &Rat::zero(),
        DiameterNorm::Supremum,
    )
    .expect("a profile");

    assert_eq!(rich.non_commuting(), 1);
    assert_eq!(poor.non_commuting(), 1, "the structural defect is the same");
    assert_eq!(rich.seen_by_the_receiver(), 1);
    assert_eq!(poor.seen_by_the_receiver(), 0);
    assert!(poor.reads_flat_at_the_receiver());
    assert!(!rich.reads_flat_at_the_receiver());
    assert_eq!(rich.maximal_discrepancy(), &Rat::one());
    assert_eq!(poor.maximal_discrepancy(), &Rat::zero());
    assert!(
        poor.seen_by_the_receiver() <= poor.non_commuting(),
        "a receiver can only lose a defect, never invent one"
    );
    // The two routes stand on `relation_ladder`'s rungs, and no rung below identity is promoted.
    assert_eq!(rich.witnesses()[0].rung(), Rung::NoRelation);
    assert_eq!(poor.witnesses()[0].rung(), Rung::ReceiverEqual);
    let tolerant = defect_profile(
        &tube,
        &declaration,
        &LadderFlag,
        &Rat::one(),
        DiameterNorm::Supremum,
    )
    .expect("a profile");
    assert_eq!(tolerant.witnesses()[0].rung(), Rung::WithinTolerance);
    // And both routes are retained whole: the defect is never resolved by choosing one.
    let witness = &rich.witnesses()[0];
    assert_eq!(witness.defect().transported_then_restricted(), &true);
    assert_eq!(witness.defect().restricted_then_transported(), &false);
}

/// `Transport/ContinuingTube.lean::{descending_chain_is_the_tubes_own,
/// rising_step_needs_the_retained_residual, the_three_kinds_of_cross_rank_passage}`: the three
/// kinds of cross-rank passage, classified exactly.
#[test]
fn a_cross_rank_passage_is_the_tubes_own_a_retained_residual_or_a_wormhole() {
    let tube = residue_tube(3, 1);
    let charts = vec![0_u32, 1, 2];
    let descending = classify_cross_rank(&tube, &0, &charts, &2, &0).expect("a classification");
    assert!(matches!(descending, CrossRankPassage::TubesOwn { .. }));
    assert_eq!(descending.chain(), Some([2_u32, 1, 0].as_slice()));
    assert_eq!(descending.reopenings(), 0);

    let rising = classify_cross_rank(&tube, &0, &charts, &0, &2).expect("a classification");
    assert!(matches!(
        rising,
        CrossRankPassage::NeedsRetainedResidual { reopenings: 2, .. }
    ));
    assert_eq!(rising.chain(), Some([0_u32, 1, 2].as_slice()));

    let two_chart = ConstantTube::new(TwoChartTower, 1);
    let wormhole = classify_cross_rank(
        &two_chart,
        &0,
        &[TwoCharts::Left, TwoCharts::Right],
        &TwoCharts::Left,
        &TwoCharts::Right,
    )
    .expect("a classification");
    assert!(matches!(wormhole, CrossRankPassage::Wormhole { .. }));
    assert_eq!(wormhole.chain(), None);
}

/// Two routes to one address across a non-commuting square deliver two faces, and the plan returns
/// both. AGENTS.md: the structure is the return and a ranking is a receiver applied afterwards.
#[test]
fn two_routes_to_one_address_return_both_faces_and_never_pick() {
    let tube = LadderTube {
        section: LadderTower,
    };
    let charts = vec![3_u32, 4];
    let bound = RouteBound::declare(4, 8).expect("inside both ceilings");
    let plan = plan_routes(
        &tube,
        &Observer::at(0_u32, 4_u32),
        &false,
        &Observer::at(1_u32, 3_u32),
        bound,
        &[0, 1],
        &charts,
        &[],
    )
    .expect("a plan");
    let RoutePlan::Routes(routes) = plan else {
        panic!("two routes exist inside the bound");
    };
    assert_eq!(routes.routes().len(), 2);
    assert!(routes.address_is_plural());
    let mut faces = routes.delivered_faces();
    faces.sort_unstable();
    assert_eq!(faces, vec![false, true]);
    assert!(
        routes
            .routes()
            .iter()
            .any(|route| route.crosses_a_non_commuting_square()),
        "the route that transports at the finest chart crosses the failing square"
    );
    assert!(
        routes
            .routes()
            .iter()
            .all(|route| route.residuals_retained().is_empty()),
        "neither route rises, so neither needs a retained residual"
    );
    // A ranking is a declared receiver applied to the returned structure, never the law itself.
    let ranked = routes.ranked_by(|route| route.moves().len());
    assert_eq!(ranked.len(), 2);
}

/// A route that rises names the residual it must retain — `traversability_is_the_residual` as a
/// receipt — and a bound that finds nothing returns the bound, never "unreachable".
#[test]
fn a_rising_route_names_its_residuals_and_an_empty_search_returns_its_bound() {
    let tube = residue_tube(3, 1);
    let charts = vec![0_u32, 1, 2];
    let mut candidates = residue_candidates(3, 1);
    candidates.extend(residue_candidates(3, 2));
    let bound = RouteBound::declare(4, 32).expect("inside both ceilings");
    let plan = plan_routes(
        &tube,
        &Observer::at(0_u32, 0_u32),
        &BigUint::zero(),
        &Observer::at(0_u32, 2_u32),
        bound,
        &[0],
        &charts,
        &candidates,
    )
    .expect("a plan");
    let RoutePlan::Routes(routes) = plan else {
        panic!("the fibre is reachable by reopening");
    };
    assert_eq!(
        routes.routes().len(),
        9,
        "every lift of 0 mod 1 to a residue mod 9 is a route, and all nine are returned"
    );
    assert!(routes.routes().iter().all(|route| {
        route.residuals_retained().len() == 2
            && route
                .moves()
                .iter()
                .filter(|step| matches!(step, RouteMove::Reopen { .. }))
                .count()
                == 2
    }));

    // The same target with no declared candidate population: no route inside the bound, and the
    // return names the bound rather than claiming unreachability.
    let empty = plan_routes(
        &tube,
        &Observer::at(0_u32, 0_u32),
        &BigUint::zero(),
        &Observer::at(0_u32, 2_u32),
        bound,
        &[0],
        &charts,
        &[],
    )
    .expect("a plan");
    assert!(matches!(empty, RoutePlan::NoRouteWithinBound { .. }));
    if let RoutePlan::NoRouteWithinBound {
        bound: returned, ..
    } = empty
    {
        assert_eq!(returned.moves(), 4);
    }

    // And a route count bound too small is returned as too small, never as a truncated set.
    let narrow = RouteBound::declare(4, 2).expect("inside both ceilings");
    let overflowing = plan_routes(
        &tube,
        &Observer::at(0_u32, 0_u32),
        &BigUint::zero(),
        &Observer::at(0_u32, 2_u32),
        narrow,
        &[0],
        &charts,
        &candidates,
    )
    .expect("a plan");
    assert!(matches!(
        overflowing,
        RoutePlan::MoreRoutesThanDeclared { found: 2, .. }
    ));
}

/// Every declared population of a two-axis reading is bounded before the work it would size.
#[test]
fn every_declared_population_of_a_horizon_is_refused_above_its_ceiling() {
    let tube = residue_tube(3, 1);
    let charts = vec![0_u32, 1];
    let observer = Observer::at(0_u32, 1_u32);

    let too_many_charts: Vec<u32> = (0..=(DECLARED_CHART_CEILING as u32 + 1)).collect();
    assert!(matches!(
        HorizonDeclaration::declare(
            observer.clone(),
            horizon(0, 0),
            vec![0],
            too_many_charts,
            Vec::<(u32, BigUint)>::new(),
        ),
        Err(HorizonRefusal::DeclarationAboveCeiling {
            what: "chart aperture",
            ..
        })
    ));

    let long_word: Vec<u32> = (0..=(DECLARED_CIRCUIT_CEILING as u32 + 1)).collect();
    assert!(matches!(
        HorizonDeclaration::declare(
            observer.clone(),
            horizon(0, 0),
            long_word,
            charts.clone(),
            Vec::<(u32, BigUint)>::new(),
        ),
        Err(HorizonRefusal::DeclarationAboveCeiling {
            what: "station word",
            ..
        })
    ));

    assert!(matches!(
        HorizonDeclaration::declare(
            Observer::at(0_u32, 7_u32),
            horizon(0, 0),
            vec![0],
            charts.clone(),
            Vec::<(u32, BigUint)>::new(),
        ),
        Err(HorizonRefusal::ObserverChartNotDeclared { chart: 7 })
    ));

    assert!(matches!(
        HorizonDeclaration::declare(
            observer.clone(),
            horizon(0, 0),
            vec![9],
            charts.clone(),
            Vec::<(u32, BigUint)>::new(),
        ),
        Err(HorizonRefusal::WordDoesNotBeginAtTheObserver { .. })
    ));

    // The work product of the horizon's coordinates with the chart and face populations is formed
    // with checked arithmetic and compared before anything is walked.
    let wide_charts: Vec<u32> = (0..600).collect();
    let observer_wide = Observer::at(0_u32, 1_u32);
    assert!(matches!(
        HorizonDeclaration::declare(
            observer_wide,
            horizon(64, 64),
            vec![0],
            wide_charts,
            vec![(1_u32, BigUint::one())],
        ),
        Err(HorizonRefusal::WorkAboveCeiling { .. })
    ));

    // The fibre candidate population is bounded before the first fibre is opened.
    let declaration = HorizonDeclaration::declare(
        observer,
        horizon(0, 1),
        vec![0],
        charts,
        vec![(1_u32, BigUint::one())],
    )
    .expect("inside every ceiling");
    let too_many: Vec<(u32, BigUint)> = (0..=(DECLARED_CANDIDATE_CEILING as u32 + 1))
        .map(|value| (1_u32, BigUint::from(value)))
        .collect();
    assert!(matches!(
        horizon_reach(&tube, &declaration, &BigUint::one(), &too_many),
        Err(HorizonRefusal::DeclarationAboveCeiling {
            what: "candidate population",
            ..
        })
    ));

    // The cover walk is cubic in the declared aperture, so the aperture's own ceiling does not
    // bound it: a distance reading over 600 declared charts is refused before the first chart is
    // visited, and so is a cross-rank classification over the same aperture.
    let wide: Vec<u32> = (0..600).collect();
    assert!(matches!(
        index_distance(&tube, &0, &wide, &0, &1),
        Err(HorizonRefusal::WorkAboveCeiling { .. })
    ));
    assert!(matches!(
        classify_cross_rank(&tube, &0, &wide, &0, &1),
        Err(HorizonRefusal::WorkAboveCeiling { .. })
    ));

    assert_eq!(
        RouteBound::declare(DECLARED_ROUTE_LENGTH_CEILING + 1, 1),
        Err((DECLARED_ROUTE_LENGTH_CEILING + 1, DECLARED_ROUTE_LENGTH_CEILING))
    );
    assert_eq!(
        RouteBound::declare(1, DECLARED_ROUTE_CEILING + 1),
        Err((DECLARED_ROUTE_CEILING + 1, DECLARED_ROUTE_CEILING))
    );
}

/// A square asked with no face at its finer chart compared nothing, and the profile says so rather
/// than reporting a flatness it never read.
#[test]
fn a_square_with_no_declared_face_is_recorded_as_unread_and_never_as_flat() {
    let tube = LadderTube {
        section: LadderTower,
    };
    let declaration = HorizonDeclaration::declare(
        Observer::at(0_u32, 4_u32),
        horizon(1, 1),
        vec![0, 1],
        vec![3_u32, 4],
        Vec::<(u32, bool)>::new(),
    )
    .expect("inside every ceiling");
    let profile = defect_profile(
        &tube,
        &declaration,
        &LadderFlag,
        &Rat::zero(),
        DiameterNorm::Supremum,
    )
    .expect("a profile");
    assert_eq!(profile.squares_checked(), 0);
    assert_eq!(profile.squares_with_no_declared_face(), 1);
    assert_eq!(profile.non_commuting(), 0);
}

// ---------------------------------------------------------------------------------------------
// T5 (d) — the real instance: the M5 grain tower over three presentations of one object
// ---------------------------------------------------------------------------------------------

use crate::grain_tower::{ScaledAperture, ScaledOccurrence, found_atom_face};
use crate::physical_intake::mmcif::{ChainOccurrence, StructurePresentation};
use crate::physical_occurrence::fixture::{
    REPRESENTATIVE, RESIDENT_DECIMAL_PLACES, absent_structure_root_message, structure_root,
};

/// The declared 8 Å contact receiver on the same exact integer wire the M5 deed carries.
fn m5_aperture() -> ScaledAperture {
    let wire = i128::from(10_i64.pow(RESIDENT_DECIMAL_PLACES));
    ScaledAperture {
        lineage: "declared contact receiver: exact distance not greater than 8 angstroms"
            .to_owned(),
        denominator: 10_u64.pow(RESIDENT_DECIMAL_PLACES),
        aperture_squared_wire: 8 * 8 * wire * wire,
    }
}

/// One presented chain on the scaled wire, with its alpha carbons located. The intake is
/// `physical_intake::mmcif`'s own — no second mmCIF reader is founded here.
fn scaled_component(chain: &ChainOccurrence, component: u32) -> (Vec<ScaledOccurrence>, Vec<GrainAddress>) {
    let mut atoms = Vec::new();
    let mut alpha_carbons = Vec::new();
    for (residue_at, residue) in chain.residues.iter().enumerate() {
        let residue_id = residue_at as u32 + 1;
        let alpha_at = residue
            .labelled_atom(REPRESENTATIVE)
            .expect("a residue carries at most one representative")
            .expect("every protein residue of this release carries its alpha carbon");
        for (atom_at, atom) in residue.atoms.iter().enumerate() {
            let (lower, upper) = atom
                .projected_wire(RESIDENT_DECIMAL_PLACES)
                .expect("the coordinate lies on the exact wire");
            atoms.push(ScaledOccurrence {
                address: GrainAddress::new(component, residue_id, atom_at as u32 + 1),
                label: atom.label.clone(),
                lower,
                upper,
            });
        }
        alpha_carbons.push(GrainAddress::new(component, residue_id, alpha_at as u32 + 1));
    }
    (atoms, alpha_carbons)
}

/// The union of two contact families as one atom-grain face. The families are over disjoint
/// components, so no pair is contributed twice.
fn union_face(left: &GrainFace, right: &GrainFace) -> GrainFace {
    GrainFace::founded(
        Grain::Atom,
        left.classified()
            .iter()
            .chain(right.classified().iter())
            .map(|(pair, class)| (*pair, *class)),
    )
    .expect("two families over disjoint components")
}

/// One presentation's station pair: the complete atom-grain reading and its alpha-carbon selection.
fn presentation_station(
    lineage: &str,
    atom_face: GrainFace,
    alpha_carbons: Vec<GrainAddress>,
) -> (String, GrainReadingTube) {
    let tube = GrainReadingTube::found(
        format!("{lineage}: label_atom_id == CA, the receiver crates/holonic-life/examples/m5/cif.rs::REPRESENTATIVE enacts"),
        rational(64),
        alpha_carbons,
        atom_face,
    )
    .expect("one representative per residue");
    (lineage.to_owned(), tube)
}

/// The three charts of the grain tower, coarsest first.
fn grain_charts() -> Vec<Grain> {
    vec![Grain::Component, Grain::Residue, Grain::Atom]
}

/// The declared faces of one presentation: its complete atom face and the residue face it
/// restricts to, so no square inside the horizon is asked with nothing to compare.
fn declared_faces(tube: &PresentationTube, presentation: usize) -> Vec<(Grain, GrainFace)> {
    let station = PresentationStation::complete(presentation);
    let section = tube.section(&station).expect("the station presents a section");
    vec![
        (Grain::Atom, section.atom_face().clone()),
        (
            Grain::Residue,
            section
                .face(Grain::Residue)
                .expect("the residue face restricts"),
        ),
    ]
}

/// The profile of one observer over one presentation's selection step.
fn m5_profile(
    tube: &PresentationTube,
    presentation: usize,
    chart: Grain,
    index_steps: usize,
    receiver: &GrainContactCount,
) -> DefectProfile<PresentationStation, Grain, GrainFace> {
    let declaration = HorizonDeclaration::declare(
        Observer::at(PresentationStation::complete(presentation), chart),
        horizon(1, index_steps),
        vec![
            PresentationStation::complete(presentation),
            PresentationStation::selected(presentation),
        ],
        grain_charts(),
        declared_faces(tube, presentation),
    )
    .expect("the declaration is inside every ceiling");
    defect_profile(
        tube,
        &declaration,
        receiver,
        &Rat::zero(),
        DiameterNorm::Supremum,
    )
    .expect("a profile")
}

/// A synthetic two-presentation tube, built with no fixture: one residue pair carried only by
/// non-representative atoms in the first presentation and by the representatives in the second.
fn synthetic_presentation_tube() -> PresentationTube {
    let hidden = GrainFace::founded(
        Grain::Atom,
        [
            (atom_pair((0, 0, 0), (0, 1, 0)), ContactClass::Inside),
            (atom_pair((0, 0, 5), (0, 2, 7)), ContactClass::Inside),
        ],
    )
    .expect("non-Outside readings");
    let seen = GrainFace::founded(
        Grain::Atom,
        [
            (atom_pair((0, 0, 0), (0, 1, 0)), ContactClass::Inside),
            (atom_pair((0, 0, 0), (0, 2, 0)), ContactClass::Inside),
        ],
    )
    .expect("non-Outside readings");
    let representatives = [
        GrainAddress::new(0, 0, 0),
        GrainAddress::new(0, 1, 0),
        GrainAddress::new(0, 2, 0),
    ];
    PresentationTube::found(vec![
        presentation_station("synthetic environment one", hidden, representatives.to_vec()),
        presentation_station("synthetic environment two", seen, representatives.to_vec()),
    ])
}

/// The grain square fails and the environment square does not: the curvature of this tube is on the
/// grain axis, and moving between two environments of one object crosses no defect. Always
/// runnable; the fixture test below is the same statement on the measured deposit.
#[test]
fn the_presentation_tube_curves_across_the_grain_and_not_across_the_environment() {
    let tube = synthetic_presentation_tube();
    let inside = GrainContactCount::of(ContactClass::Inside);

    let grain_step = HorizonDeclaration::declare(
        Observer::at(PresentationStation::complete(0), Grain::Atom),
        horizon(1, 1),
        vec![
            PresentationStation::complete(0),
            PresentationStation::selected(0),
        ],
        grain_charts(),
        declared_faces(&tube, 0),
    )
    .expect("inside every ceiling");
    let grain_profile = defect_profile(
        &tube,
        &grain_step,
        &inside,
        &Rat::zero(),
        DiameterNorm::Supremum,
    )
    .expect("a profile");
    assert_eq!(grain_profile.non_commuting(), 1);
    assert_eq!(
        grain_profile.maximal_discrepancy(),
        &Rat::one(),
        "the one residue pair the alpha-carbon receiver never sees"
    );
    assert_eq!(grain_profile.witnesses()[0].rung(), Rung::NoRelation);

    let environment_step = HorizonDeclaration::declare(
        Observer::at(PresentationStation::selected(0), Grain::Atom),
        horizon(1, 1),
        vec![
            PresentationStation::selected(0),
            PresentationStation::selected(1),
        ],
        grain_charts(),
        declared_faces(&tube, 0),
    )
    .expect("inside every ceiling");
    let environment_profile = defect_profile(
        &tube,
        &environment_step,
        &inside,
        &Rat::zero(),
        DiameterNorm::Supremum,
    )
    .expect("a profile");
    assert!(
        environment_profile.is_flat(),
        "the environment transport is constant in its source, as a passage's apply is, so its \
         square with the restriction commutes"
    );
    assert!(environment_profile.squares_checked() > 0, "and it read real squares");

    // At k = 0 neither observer has a second chart inside its horizon, so there is no square to
    // read at all: flatness at k = 0 is the absence of a reading, and the profile says so.
    let alone = HorizonDeclaration::declare(
        Observer::at(PresentationStation::complete(0), Grain::Residue),
        horizon(1, 0),
        vec![
            PresentationStation::complete(0),
            PresentationStation::selected(0),
        ],
        grain_charts(),
        declared_faces(&tube, 0),
    )
    .expect("inside every ceiling");
    let alone_profile = defect_profile(
        &tube,
        &alone,
        &inside,
        &Rat::zero(),
        DiameterNorm::Supremum,
    )
    .expect("a profile");
    assert_eq!(alone_profile.squares_checked(), 0);
    assert_eq!(alone_profile.charts_visible(), &[Grain::Residue]);
}

/// **The measured instance.** The three M5 RBX1 presentations as three stations of one tube, with
/// the atom↔residue grain tower as the transverse section. The defect profile's content **is** the
/// measured census: 1,397 fine `Inside` contacts against 301 the alpha-carbon receiver sees, and the
/// 1,096 it never sees is the exact discrepancy between the two routes of the failing square,
/// summed over the three stations.
///
/// Hard-fails naming the fixture when the authenticated release is absent; the laws themselves are
/// checked without it by
/// `the_presentation_tube_curves_across_the_grain_and_not_across_the_environment`.
#[test]
fn the_m5_defect_profile_carries_the_measured_grain_census() {
    let root = structure_root();
    assert!(
        root.is_dir(),
        "{}",
        absent_structure_root_message(
            &root,
            "The two-axis horizon's laws are checked without it by \
             the_presentation_tube_curves_across_the_grain_and_not_across_the_environment."
        )
    );
    let read = |name: &str| {
        StructurePresentation::read(&root.join(name)).unwrap_or_else(|error| panic!("{name}: {error}"))
    };
    let designed = read("designed-free-rbx1.cif");
    let free = read("ptxv2-free-rbx1-seed2.cif");
    let complex = read("ptxv2-cul1-rbx1-seed0.cif");
    let aperture = m5_aperture();

    let station_of = |presentation: &StructurePresentation| {
        let (binder, binder_alphas) =
            scaled_component(presentation.chain_with_residue_count(96).expect("96 residues"), 1);
        let (target, target_alphas) = scaled_component(
            presentation.chain_with_residue_count(108).expect("108 residues"),
            2,
        );
        let face = found_atom_face(&binder, &target, &aperture).expect("the atom face founds");
        let mut alphas = binder_alphas;
        alphas.extend(target_alphas);
        (face, alphas)
    };

    let (designed_face, designed_alphas) = station_of(&designed);
    let (free_face, free_alphas) = station_of(&free);
    let (complex_binder_face, mut complex_alphas) = station_of(&complex);
    // The complex presentation admits a second contact family, because CUL1 is present there. Both
    // families are carried in one face over three components; nothing is dropped and nothing is
    // averaged.
    let (cul1, cul1_alphas) = scaled_component(
        complex.chain_with_residue_count(366).expect("366 residues"),
        3,
    );
    let (target, _) = scaled_component(
        complex.chain_with_residue_count(108).expect("108 residues"),
        2,
    );
    let cul1_face = found_atom_face(&cul1, &target, &aperture).expect("the atom face founds");
    let complex_face = union_face(&complex_binder_face, &cul1_face);
    complex_alphas.extend(cul1_alphas);

    let tube = PresentationTube::found(vec![
        presentation_station("designed free RBX1", designed_face, designed_alphas),
        presentation_station("Protenix free seed 2", free_face, free_alphas),
        presentation_station("Protenix CUL1-RBX1 seed 0", complex_face, complex_alphas),
    ]);

    let inside = GrainContactCount::of(ContactClass::Inside);
    let open = GrainContactCount::of(ContactClass::Open);

    let mut fine_total = 0_i64;
    let mut coarse_total = 0_i64;
    let mut discrepancy_total = Rat::zero();
    let expected: [(usize, i64, i64); 3] = [(0, 303, 64), (1, 366, 59), (2, 728, 178)];
    for (presentation, fine_inside, coarse_inside) in expected {
        // At k = 0 the observer's own chart is the only one inside its horizon, so there is no
        // square to read: neither grain reads curvature without a second chart.
        for chart in [Grain::Residue, Grain::Atom] {
            let alone = m5_profile(&tube, presentation, chart, 0, &inside);
            assert_eq!(alone.squares_checked(), 0, "{chart:?} at k = 0");
            assert_eq!(alone.charts_visible(), &[chart]);
        }

        // At k = 1 the atom observer reaches the residue chart and reads the one failing square;
        // the residue observer reaches both neighbours and reads three squares, of which that same
        // one fails.
        let at_the_atom = m5_profile(&tube, presentation, Grain::Atom, 1, &inside);
        assert_eq!(at_the_atom.charts_visible(), &[Grain::Residue, Grain::Atom]);
        assert_eq!(at_the_atom.squares_checked(), 1);
        assert_eq!(at_the_atom.non_commuting(), 1);

        let at_the_residue = m5_profile(&tube, presentation, Grain::Residue, 1, &inside);
        assert_eq!(
            at_the_residue.charts_visible(),
            &[Grain::Component, Grain::Residue, Grain::Atom]
        );
        assert_eq!(at_the_residue.squares_checked(), 3);
        assert_eq!(at_the_residue.non_commuting(), 1);

        // The profile's content is the census: the two routes of the failing square are the coarse
        // and the fine reading, and their exact discrepancy is the contacts the coarse receiver
        // never sees.
        let witness = &at_the_atom.witnesses()[0];
        assert_eq!(
            witness.defect().transported_then_restricted().inside() as i64,
            coarse_inside
        );
        assert_eq!(
            witness.defect().restricted_then_transported().inside() as i64,
            fine_inside
        );
        assert_eq!(
            witness.discrepancy(),
            &Rat::from_integer(num_bigint::BigInt::from(fine_inside - coarse_inside))
        );
        assert_eq!(witness.rung(), Rung::NoRelation);
        fine_total += fine_inside;
        coarse_total += coarse_inside;
        discrepancy_total += witness.discrepancy().clone();
        eprintln!(
            "m5 two-axis profile | presentation {presentation} | atom observer k=1: {} of {} \
             squares non-commuting | residue observer k=1: {} of {} | routes {coarse_inside} \
             against {fine_inside} inside | discrepancy {}",
            at_the_atom.non_commuting(),
            at_the_atom.squares_checked(),
            at_the_residue.non_commuting(),
            at_the_residue.squares_checked(),
            witness.discrepancy(),
        );
    }

    assert_eq!(fine_total, 1_397, "the measured fine Inside population");
    assert_eq!(coarse_total, 301, "the measured coarse Inside population");
    assert_eq!(
        discrepancy_total,
        Rat::from_integer(num_bigint::BigInt::from(1_096)),
        "the 1,096 fine contacts invisible to the coarse receiver, as the profile's own content"
    );

    // **The Open class does not transport, and a count receiver cannot see that.** At the designed
    // presentation the fine reading and the coarse reading each carry exactly one Open residue
    // pair, and they are not the same pair: the Open-counting receiver reads the square flat while
    // the structural defect is there and the Inside-counting receiver separates it.
    let open_profile = m5_profile(&tube, 0, Grain::Atom, 1, &open);
    assert_eq!(open_profile.non_commuting(), 1);
    assert_eq!(open_profile.seen_by_the_receiver(), 0);
    assert!(open_profile.reads_flat_at_the_receiver());
    assert_eq!(open_profile.witnesses()[0].rung(), Rung::ReceiverEqual);
    let witness = &open_profile.witnesses()[0];
    assert_eq!(witness.defect().transported_then_restricted().open(), 1);
    assert_eq!(witness.defect().restricted_then_transported().open(), 1);
    assert_ne!(
        witness.defect().transported_then_restricted(),
        witness.defect().restricted_then_transported(),
        "one Open pair on each route, and not the same pair: the class does not transport"
    );
}
