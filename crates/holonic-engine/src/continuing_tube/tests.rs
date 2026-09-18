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
use crate::continuing_tower::{
    HalvingMigration, ResidueTower, ReversePassageReceipt, SwapMigration, check_reverse_passage,
};
use crate::grain_tower::GrainPair;
use crate::physical_constraint_complex::ContactClass;

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
    use crate::continuing_tower::Transition;
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
