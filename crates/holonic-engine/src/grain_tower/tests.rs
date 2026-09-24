//! Laws of the grain tower, and the measured M5 pair table that motivates it.
//!
//! The synthetic tests state the laws the Lean owner
//! `formal/elementary-holonics/ElementaryHolonics/Foundation/GrainRestriction.lean` proves. The
//! last two tests are the fixture of `docs/plans/THE_BIOLOGICAL_ECOLOGY_INSTANTIATES_THE_CARRIER.md`
//! item **B0**: the complete atom-grain intake of the three authenticated M5 coordinate files, and
//! the exact pair table it returns against the alpha-carbon receiver the M5 deed enacts.
//!
//! The two claims that intake exists to carry — `reopen_apply` on a complete atom-grain
//! population, and the pair-table identity `fine_inside - coarse_inside = fine_only_inside` with
//! `coarse_only_inside = 0` — are checked twice, through the same `enact_family` path:
//!
//! * [`the_pair_table_identities_hold_on_a_synthetic_atom_grain_intake`] builds its own scaled
//!   intake and runs everywhere, with no fixture and no environment.
//! * [`the_m5_pair_table_reproduces_from_a_complete_atom_grain_intake`] reproduces the measured
//!   numbers from the authenticated release, and **fails** when that release is absent. A test
//!   that cannot run says so by failing: a `return` here would have reported `ok` while checking
//!   nothing, because cargo discards the output of a passing test.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use num_bigint::{BigInt, BigUint};
use num_traits::One;
use relational_geometry::Rat;

use super::*;
use holonics::restriction::tower::{CompatibleSection, check_restriction_laws};

fn atom(component: u32, residue: u32, at: u32) -> GrainCell {
    GrainAddress::new(component, residue, at).cell(Grain::Atom)
}

fn residue_cell(component: u32, residue: u32) -> GrainCell {
    GrainAddress::new(component, residue, 0).cell(Grain::Residue)
}

fn atom_pair(left: (u32, u32, u32), right: (u32, u32, u32)) -> GrainPair {
    GrainPair::new(
        atom(left.0, left.1, left.2),
        atom(right.0, right.1, right.2),
    )
    .expect("distinct atoms found a pair")
}

fn residue_pair(left: (u32, u32), right: (u32, u32)) -> GrainPair {
    GrainPair::new(residue_cell(left.0, left.1), residue_cell(right.0, right.1))
        .expect("distinct residues found a pair")
}

fn rational(numerator: i64, denominator: i64) -> Rat {
    Rat::new(BigInt::from(numerator), BigInt::from(denominator))
}

#[test]
fn the_grain_order_is_the_refinement_order() {
    assert!(Grain::refines(Grain::Component, Grain::Atom));
    assert!(Grain::refines(Grain::Residue, Grain::Atom));
    assert!(Grain::refines(Grain::Component, Grain::Residue));
    assert!(Grain::refines(Grain::Atom, Grain::Atom));
    assert!(!Grain::refines(Grain::Atom, Grain::Residue));
    assert!(!Grain::refines(Grain::Residue, Grain::Component));
    assert_eq!(
        Grain::ASCENDING.map(Grain::rank),
        [0, 1, 2],
        "the rank is the Lean `Grain.rank`"
    );
}

#[test]
fn the_contact_class_join_is_a_commutative_idempotent_semilattice_with_outside_at_the_bottom() {
    let classes = [
        ContactClass::Outside,
        ContactClass::Open,
        ContactClass::Inside,
    ];
    for left in classes {
        assert_eq!(join_contact_class(left, left), left, "idempotent");
        assert_eq!(
            join_contact_class(left, ContactClass::Outside),
            left,
            "Outside is the bottom"
        );
        for right in classes {
            assert_eq!(
                join_contact_class(left, right),
                join_contact_class(right, left),
                "commutative"
            );
            for third in classes {
                assert_eq!(
                    join_contact_class(join_contact_class(left, right), third),
                    join_contact_class(left, join_contact_class(right, third)),
                    "associative"
                );
            }
        }
    }
    assert_eq!(
        join_contact_class(ContactClass::Open, ContactClass::Inside),
        ContactClass::Inside,
        "one decided contact decides the coarse cell"
    );
}

#[test]
fn grain_face_wire_rechecks_pair_grain_and_outside_elision() {
    let pair = atom_pair((0, 0, 0), (0, 0, 1));
    assert!(matches!(
        GrainFace::try_from(GrainFaceWire {
            grain: Grain::Residue,
            classified: BTreeMap::from([(pair, ContactClass::Inside)]),
        }),
        Err(GrainRefusal::PairNotAtGrain { .. })
    ));
    assert!(matches!(
        GrainFace::try_from(GrainFaceWire {
            grain: Grain::Atom,
            classified: BTreeMap::from([(pair, ContactClass::Outside)]),
        }),
        Err(GrainRefusal::OutsideReadingStored { .. })
    ));
}

#[test]
fn grain_selection_wire_rechecks_projection_and_inverse() {
    let coarse = residue_cell(0, 0);
    let fine = atom(0, 0, 0);
    let mut representative = BTreeMap::from([(coarse, fine)]);
    let inverse = BTreeMap::from([(fine, coarse)]);
    let valid = GrainSelection::try_from(GrainSelectionWire {
        lineage: "wire".to_owned(),
        coarse: Grain::Residue,
        fine: Grain::Atom,
        representative: representative.clone(),
        inverse: inverse.clone(),
    })
    .expect("the wire's representative maps are coherent");
    assert_eq!(valid.represented(), 1);

    representative.insert(coarse, atom(0, 1, 0));
    assert!(matches!(
        GrainSelection::try_from(GrainSelectionWire {
            lineage: "wire".to_owned(),
            coarse: Grain::Residue,
            fine: Grain::Atom,
            representative,
            inverse,
        }),
        Err(GrainRefusal::RepeatedRepresentative { .. })
    ));

    assert!(matches!(
        GrainSelection::try_from(GrainSelectionWire {
            lineage: "wire".to_owned(),
            coarse: Grain::Residue,
            fine: Grain::Atom,
            representative: BTreeMap::from([(coarse, fine)]),
            inverse: BTreeMap::new(),
        }),
        Err(GrainRefusal::SelectionWireInconsistent)
    ));
}

/// The three-grain tower of one two-component presentation.
///
/// Component 1 carries residues 1..=2, component 2 carries residue 1. One atom pair is `Inside`,
/// one is `Open`, and one pair is internal to a single residue so that the collapsed projection has
/// a witness.
fn worked_atom_face() -> GrainFace {
    GrainFace::founded(
        Grain::Atom,
        [
            (atom_pair((1, 1, 2), (2, 1, 1)), ContactClass::Inside),
            (atom_pair((1, 2, 1), (2, 1, 3)), ContactClass::Open),
            (atom_pair((1, 1, 1), (1, 1, 4)), ContactClass::Open),
        ],
    )
    .expect("the worked atom face founds")
}

#[test]
fn restriction_takes_the_join_over_the_block() {
    let atom_face = worked_atom_face();
    let residue_face = atom_face
        .restricted(Grain::Residue)
        .expect("the residue face restricts");
    assert_eq!(
        residue_face.class(&residue_pair((1, 1), (2, 1))),
        ContactClass::Inside
    );
    assert_eq!(
        residue_face.class(&residue_pair((1, 2), (2, 1))),
        ContactClass::Open
    );
    assert_eq!(
        residue_face.classified().len(),
        2,
        "the intra-residue pair presents no residue incidence"
    );

    let component_face = atom_face
        .restricted(Grain::Component)
        .expect("the component face restricts");
    assert_eq!(component_face.classified().len(), 1);
    assert_eq!(
        component_face.class(
            &GrainPair::new(
                GrainAddress::new(1, 0, 0).cell(Grain::Component),
                GrainAddress::new(2, 0, 0).cell(Grain::Component)
            )
            .expect("distinct components")
        ),
        ContactClass::Inside,
        "the join of Inside and Open is Inside"
    );
}

fn worked_tower() -> GrainTower {
    GrainTower::found(
        "worked three-grain presentation",
        ApertureRelation::NativeFineWithRefusal(FineNativeDeclaration::declare(
            "the atom grain is the receiver",
            rational(64, 1),
        )),
        worked_atom_face(),
    )
    .expect("the worked tower founds")
}

#[test]
fn the_grain_tower_satisfies_restrict_refl_and_restrict_trans() {
    let tower = worked_tower();
    let faces = Grain::ASCENDING
        .iter()
        .map(|grain| {
            (
                *grain,
                tower.face(*grain).expect("every grain carries a face"),
            )
        })
        .collect::<Vec<_>>();
    let receipt = check_restriction_laws(&tower, &Grain::ASCENDING, &faces)
        .expect("the restriction laws hold");
    assert_eq!(receipt.faces_checked, 3);
    assert_eq!(receipt.reflexive_charts, Grain::ASCENDING.to_vec());
    assert!(
        receipt
            .transitive_triples
            .contains(&(Grain::Component, Grain::Residue, Grain::Atom)),
        "the atom -> residue -> component triple was actually checked: {:?}",
        receipt.transitive_triples
    );
}

#[test]
fn the_restriction_residual_reopens_the_fine_face_inside_the_tower() {
    let tower = worked_tower();
    let witnesses = Grain::ASCENDING
        .iter()
        .map(|grain| {
            (
                *grain,
                tower.face(*grain).expect("every grain carries a face"),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let section = CompatibleSection::check(&tower, witnesses).expect("the faces are compatible");
    let receipt = tower
        .check_section_reopen(&Grain::Residue, &Grain::Atom, &section)
        .expect("the residual reopens the atom face from the residue face");
    assert_eq!(receipt.sources_reopened, 1);

    let residual = tower
        .restriction_residual(&Grain::Residue, &Grain::Atom, tower.atom_face())
        .expect("the residual is retained");
    assert_eq!(
        residual.internal.len(),
        1,
        "the intra-residue pair is retained whole"
    );
    assert_eq!(residual.blocks.len(), 2);
    assert_eq!(residual.retained(), 3, "nothing was dropped");
}

#[test]
fn a_residual_block_under_a_refused_coarse_pair_is_a_typed_refusal() {
    let tower = worked_tower();
    let residual = tower
        .restriction_residual(&Grain::Residue, &Grain::Atom, tower.atom_face())
        .expect("the residual is retained");
    let empty = GrainFace::empty(Grain::Residue);
    let refusal = tower
        .restriction_reopen(&Grain::Residue, &Grain::Atom, &empty, &residual)
        .expect_err("a coarse face that refuses every pair cannot carry these blocks");
    assert!(matches!(
        refusal,
        holonics::restriction::tower::TowerRefusal::IncompatibleWitness { .. }
    ));
}

/// The selection receiver of the worked presentation: atom `1` of every residue.
fn worked_selection() -> GrainSelection {
    GrainSelection::declare(
        "atom 1 of every residue, the worked stand-in for label_atom_id == CA",
        Grain::Residue,
        Grain::Atom,
        [
            GrainAddress::new(1, 1, 1),
            GrainAddress::new(1, 2, 1),
            GrainAddress::new(2, 1, 1),
        ],
    )
    .expect("the selection declares")
}

#[test]
fn the_selection_is_not_the_restriction_and_the_disagreement_is_the_fine_only_population() {
    let atom_face = worked_atom_face();
    let selection = worked_selection();
    let fine = atom_face
        .restricted(Grain::Residue)
        .expect("the restriction takes");
    let coarse = selection.apply(&atom_face);

    // The selection reads atom 1 of residue (1,1) against atom 1 of residue (2,1); the only
    // Inside reading of that block sits on atom 2, which the selection never looks at.
    assert_eq!(coarse.classified().len(), 0);
    let disagreement = GrainDisagreement::between(&fine, &coarse).expect("both faces are residue");
    assert_eq!(disagreement.fine_only.len(), 2);
    assert!(
        disagreement.coarse_only.is_empty(),
        "coarse implies fine is a theorem: Foundation/GrainRestriction.lean::\
         selection_inside_implies_fine_inside"
    );
}

#[test]
fn the_coarse_face_together_with_the_residual_reopens_both_the_source_and_the_fine_reading() {
    let atom_face = worked_atom_face();
    let selection = worked_selection();
    let receipt = check_grain_reopen(&selection, &atom_face).expect("reopen_apply holds");
    assert_eq!(receipt.source_reopened, 1);
    assert_eq!(receipt.residual_retained, 3);
    assert_eq!(receipt.coarse_carried, 0);
    assert_eq!(receipt.fine_reading_carried, 2);
}

#[test]
fn deleting_the_fine_only_contacts_fixes_the_coarse_face_and_separates_the_residuals() {
    let atom_face = worked_atom_face();
    let selection = worked_selection();
    let fine = atom_face
        .restricted(Grain::Residue)
        .expect("the restriction takes");
    let coarse = selection.apply(&atom_face);
    let disagreement = GrainDisagreement::between(&fine, &coarse).expect("both faces are residue");

    let unselected = selection.residual(&atom_face);
    let deleted = unselected
        .unselected
        .keys()
        .filter(|pair| {
            pair.project(Grain::Residue)
                .ok()
                .flatten()
                .is_some_and(|coarse_pair| disagreement.fine_only.contains_key(&coarse_pair))
        })
        .copied()
        .collect::<Vec<_>>();
    assert!(!deleted.is_empty());

    let thinned = atom_face.without(deleted);
    assert_ne!(thinned, atom_face);
    assert_eq!(
        selection.apply(&thinned),
        coarse,
        "the coarse receiver cannot see the deletion"
    );
    assert_ne!(
        thinned
            .restricted(Grain::Residue)
            .expect("the restriction takes"),
        fine,
        "the fine restriction can"
    );
    let (left, right) = selection
        .separating_residuals(&atom_face, &thinned)
        .expect("two distinct sources with one coarse face");
    assert_ne!(
        left, right,
        "Foundation/ContinuingTower.lean::Transition.residual_separates on measured faces"
    );
}

#[test]
fn the_open_class_moves_in_both_directions_between_grains_and_is_never_shared() {
    // Residue pair (1,1)x(2,1): the selected atom pair is Open and a non-selected atom pair is
    // Inside, so the finer grain decides what the coarse one could not.
    // Residue pair (1,2)x(2,1): the selected atom pair is absent (Outside) and a non-selected pair
    // is Open, so the finer grain opens what the coarse one had decided.
    let atom_face = GrainFace::founded(
        Grain::Atom,
        [
            (atom_pair((1, 1, 1), (2, 1, 1)), ContactClass::Open),
            (atom_pair((1, 1, 2), (2, 1, 2)), ContactClass::Inside),
            (atom_pair((1, 2, 3), (2, 1, 3)), ContactClass::Open),
        ],
    )
    .expect("the open face founds");
    let selection = worked_selection();
    let fine = atom_face
        .restricted(Grain::Residue)
        .expect("the restriction takes");
    let coarse = selection.apply(&atom_face);
    let census = GrainCensus::measure("open transport", 2, &fine, &coarse).expect("the census");
    assert_eq!(census.coarse_open, 1);
    assert_eq!(census.fine_open, 1);
    assert_eq!(
        census.open_shared, 0,
        "the Open class does not transport: the two open sets are disjoint"
    );
    assert_eq!(census.fine_inside, 1);
    assert_eq!(census.coarse_inside, 0);
    assert_eq!(census.fine_only_inside, 1);
    assert_eq!(census.coarse_only_inside, 0);
}

#[test]
fn an_exact_rational_root_bound_is_an_upper_bound_and_is_least_at_its_denominator() {
    let denominator = BigUint::from(1_000_u32);
    let two = rational(2, 1);
    let bound = rational_root_upper_bound(&two, &denominator).expect("2 has a root bound");
    assert!(&bound * &bound >= two, "it is an upper bound");
    let under = &bound - &rational(1, 1_000);
    assert!(
        &under * &under < rational(2, 1),
        "and it is the least such at this denominator"
    );
    assert_eq!(bound, rational(1_415, 1_000));

    let four = rational(4, 1);
    assert_eq!(
        rational_root_upper_bound(&four, &denominator).expect("4 has a root bound"),
        rational(2, 1),
        "an exact square returns its exact root"
    );
    assert!(rational_root_upper_bound(&rational(-1, 1), &denominator).is_err());
}

fn worked_readings() -> Vec<CoarseReading> {
    vec![
        CoarseReading {
            pair: residue_pair((1, 1), (2, 1)),
            fine_class: ContactClass::Inside,
            coarse_squared_distance: ExactInterval {
                lower: rational(100, 1),
                upper: rational(121, 1),
            },
            forcing_fine_pair: Some(atom_pair((1, 1, 2), (2, 1, 1))),
            lower_grain_radius: rational(4, 1),
            upper_grain_radius: rational(5, 1),
        },
        CoarseReading {
            pair: residue_pair((1, 2), (2, 1)),
            fine_class: ContactClass::Open,
            coarse_squared_distance: ExactInterval {
                lower: rational(80, 1),
                upper: rational(81, 1),
            },
            forcing_fine_pair: None,
            lower_grain_radius: rational(3, 1),
            upper_grain_radius: rational(5, 1),
        },
        CoarseReading {
            pair: residue_pair((1, 2), (2, 1)),
            fine_class: ContactClass::Outside,
            coarse_squared_distance: ExactInterval {
                lower: rational(900, 1),
                upper: rational(901, 1),
            },
            forcing_fine_pair: None,
            lower_grain_radius: rational(3, 1),
            upper_grain_radius: rational(5, 1),
        },
    ]
}

#[test]
fn the_inflation_is_the_attained_maximum_and_carries_its_forcing_witness() {
    let witness = InflationWitness::measure("worked", rational(64, 1), &worked_readings())
        .expect("an inflation is measured");
    assert_eq!(witness.coarse_aperture_squared, rational(121, 1));
    assert_eq!(witness.inflation_ratio_squared, rational(121, 64));
    assert_eq!(witness.carried, 2, "the Outside reading is not carried");
    assert_eq!(witness.examined, 3);
    assert_eq!(witness.extremal.pair, residue_pair((1, 1), (2, 1)));
    assert_eq!(
        witness.extremal.forcing_fine_pair,
        Some(atom_pair((1, 1, 2), (2, 1, 1))),
        "the pair that forces the inflation travels with it"
    );
    // (8 + 4 + 5)^2 = 289 >= 121: the triangle-inequality certificate of
    // Foundation/GrainRestriction.lean::coarse_distance_le_fine_aperture_add_radii.
    assert_eq!(witness.certified_bound_squared, rational(289, 1));
    assert!(witness.certified_bound_squared >= witness.coarse_aperture_squared);

    witness
        .check_declared(&rational(121, 1))
        .expect("the attained maximum is itself admissible");
    witness
        .check_declared(&rational(200, 1))
        .expect("anything larger is admissible");
    let refusal = witness
        .check_declared(&rational(64, 1))
        .expect_err("the equal aperture does not carry");
    assert!(matches!(refusal, GrainRefusal::CoarseApertureTooSmall(_)));
}

#[test]
fn an_inflation_with_no_fine_contact_is_refused_rather_than_guessed() {
    let readings = vec![worked_readings()[2].clone()];
    assert!(matches!(
        InflationWitness::measure("worked", rational(64, 1), &readings),
        Err(GrainRefusal::NoFineContactToCarry { examined: 1 })
    ));
}

#[test]
fn a_grain_radius_that_is_not_an_upper_bound_refutes_its_own_certificate() {
    let mut readings = worked_readings();
    readings[0].lower_grain_radius = Rat::from_integer(BigInt::from(0));
    readings[0].upper_grain_radius = Rat::from_integer(BigInt::from(0));
    let refusal = InflationWitness::measure("worked", rational(64, 1), &readings).expect_err(
        "a zero radius cannot certify an 11-unit coarse distance at an 8-unit aperture",
    );
    assert!(matches!(
        refusal,
        GrainRefusal::CertificateBelowMeasurement(_)
    ));
}

#[test]
fn independence_must_be_earned_by_a_measured_separation() {
    let fine = GrainFace::founded(
        Grain::Residue,
        [(residue_pair((1, 1), (2, 1)), ContactClass::Inside)],
    )
    .expect("the fine face founds");
    let agreeing = fine.clone();
    assert!(matches!(
        IndependenceDeclaration::declare(
            "worked",
            rational(64, 1),
            rational(64, 1),
            &GrainDisagreement::between(&fine, &agreeing).expect("same grain"),
        ),
        Err(GrainRefusal::IndependenceWithoutSeparation)
    ));

    let separated = GrainFace::empty(Grain::Residue);
    let declaration = IndependenceDeclaration::declare(
        "worked",
        rational(64, 1),
        rational(64, 1),
        &GrainDisagreement::between(&fine, &separated).expect("same grain"),
    )
    .expect("a measured separation earns the declaration");
    assert_eq!(declaration.fine_only, 1);
    assert_eq!(declaration.coarse_only, 0);
    assert_eq!(declaration.separators, vec![residue_pair((1, 1), (2, 1))]);
}

#[test]
fn the_native_fine_declaration_refuses_on_the_first_disagreement() {
    let declaration = FineNativeDeclaration::declare("worked", rational(64, 1));
    let fine = GrainFace::founded(
        Grain::Residue,
        [(residue_pair((1, 1), (2, 1)), ContactClass::Inside)],
    )
    .expect("the fine face founds");
    let coarse = GrainFace::empty(Grain::Residue);
    let refusal = declaration
        .admit_coarse(&fine, &coarse)
        .expect_err("a disagreement is a refusal, never a reading");
    assert!(matches!(
        refusal,
        GrainRefusal::CoarseReadingDisagrees {
            fine: ContactClass::Inside,
            coarse: ContactClass::Outside,
            ..
        }
    ));
    declaration
        .admit_coarse(&fine, &fine)
        .expect("an agreeing reading is admitted");
}

#[test]
fn the_declared_relation_travels_with_the_tower() {
    let tower = worked_tower();
    assert_eq!(tower.relation().name(), "native-fine-with-refusal");
    assert_eq!(tower.relation().fine_aperture_squared(), &rational(64, 1));
    // The whole tower round-trips through a codec that carries structured map keys; the receipt
    // types a report actually publishes — `GrainCensus` and `InflationWitness` — carry none, so
    // they round-trip through JSON as well.
    let round_trip: GrainTower =
        ron::from_str(&ron::to_string(&tower).expect("the tower serializes")).expect("remounts");
    assert_eq!(round_trip.relation(), tower.relation());
    assert_eq!(round_trip.atom_face(), tower.atom_face());
    let mut unknown_schema = tower.clone();
    unknown_schema.schema = "holonic-engine.grain-tower.future".to_owned();
    assert!(ron::from_str::<GrainTower>(&ron::to_string(&unknown_schema).unwrap()).is_err());

    let witness = InflationWitness::measure("worked", rational(64, 1), &worked_readings())
        .expect("an inflation is measured");
    let published: InflationWitness =
        serde_json::from_str(&serde_json::to_string(&witness).expect("the witness serializes"))
            .expect("the witness remounts");
    assert_eq!(published, witness);
}

#[test]
fn the_scaled_wire_agrees_with_the_exact_rational_aperture() {
    let aperture = ScaledAperture {
        lineage: "8 units at denominator 1000".to_owned(),
        denominator: 1_000,
        aperture_squared_wire: 64 * 1_000 * 1_000,
    };
    let exact = aperture.exact().expect("the exact aperture recovers");
    assert_eq!(exact.squared, rational(64, 1));
    let denominator = BigUint::from(1_000_u32);
    for offset in -3_i64..=3 {
        let left = ScaledOccurrence {
            address: GrainAddress::new(1, 1, 1),
            label: "left".to_owned(),
            lower: [0, 0, 0],
            upper: [0, 0, 0],
        };
        let right = ScaledOccurrence {
            address: GrainAddress::new(2, 1, 1),
            label: "right".to_owned(),
            lower: [8_000 + offset, 0, 0],
            upper: [8_000 + offset + 1, 0, 0],
        };
        let (low, high) =
            ScaledAperture::squared_distance(&left, &right).expect("the wire carries the distance");
        let wire_class = aperture.classify(low, high);
        let rational_class = exact.classify(
            &left
                .position(&denominator)
                .expect("the left box recovers")
                .squared_distance(
                    &right
                        .position(&denominator)
                        .expect("the right box recovers"),
                ),
        );
        assert_eq!(
            wire_class, rational_class,
            "the i128 wire and the exact rational classifier agree at offset {offset}"
        );
    }
}

// ---------------------------------------------------------------------------------------------
// The measured M5 fixture.
// ---------------------------------------------------------------------------------------------

const STRUCTURE_ROOT_ENV: &str = "HOLONICS_M5_STRUCTURE_ROOT";
const DEFAULT_STRUCTURE_ROOT: &str = "/home/b/Downloads/holonics-m5-rbx1-rank05";
/// The resident decimal grain `crates/holonic-life/examples/m5/fold.rs::derive_resident_places`
/// derives for this family. Reproduced here so the coarse column is the M5 deed's own.
const RESIDENT_DECIMAL_PLACES: u32 = 7;
const CONTACT_RADIUS: i128 = 8;

#[derive(Clone, Debug)]
struct CifAtom {
    label: String,
    lower: [i64; 3],
    upper: [i64; 3],
}

type CifChains = BTreeMap<String, BTreeMap<i32, Vec<CifAtom>>>;

fn parse_decimal(token: &str) -> Result<(i64, u32), String> {
    let token = token
        .strip_prefix('\'')
        .and_then(|body| body.strip_suffix('\''))
        .unwrap_or(token);
    let negative = token.starts_with('-');
    let unsigned = token.trim_start_matches(['-', '+']);
    let (whole, fraction) = unsigned.split_once('.').unwrap_or((unsigned, ""));
    if whole.is_empty()
        || !whole.chars().all(|ch| ch.is_ascii_digit())
        || !fraction.chars().all(|ch| ch.is_ascii_digit())
    {
        return Err(format!("coordinate token {token:?} is not a plain decimal"));
    }
    let places = fraction.len() as u32;
    let scale = 10_i64
        .checked_pow(places)
        .ok_or_else(|| format!("{token:?} exceeds the exact decimal wire"))?;
    let whole = whole.parse::<i64>().map_err(|error| error.to_string())?;
    let fraction = if fraction.is_empty() {
        0
    } else {
        fraction.parse::<i64>().map_err(|error| error.to_string())?
    };
    let magnitude = whole
        .checked_mul(scale)
        .and_then(|value| value.checked_add(fraction))
        .ok_or_else(|| format!("{token:?} overflows"))?;
    Ok((if negative { -magnitude } else { magnitude }, places))
}

/// `physical_intake::mmcif::DecimalToken::projected_wire`, replayed on every atom rather than only
/// on the alpha carbon. The outward last-place law is the same: one complete last-decimal unit
/// on each side, projected outward onto the coarser resident denominator.
fn outward_wire(significand: i64, places: u32) -> Result<(i64, i64), String> {
    if RESIDENT_DECIMAL_PLACES >= places {
        let multiplier = 10_i64
            .checked_pow(RESIDENT_DECIMAL_PLACES - places)
            .ok_or_else(|| "the coordinate scale exceeds the exact i64 wire".to_owned())?;
        let center = significand
            .checked_mul(multiplier)
            .ok_or_else(|| "the coordinate center exceeds the exact i64 wire".to_owned())?;
        Ok((center - multiplier, center + multiplier))
    } else {
        let divisor = 10_i64
            .checked_pow(places - RESIDENT_DECIMAL_PLACES)
            .ok_or_else(|| "the coordinate divisor exceeds the exact i64 wire".to_owned())?;
        let lower = (significand - 1).div_euclid(divisor);
        let upper = -((-(significand + 1)).div_euclid(divisor));
        Ok((lower, upper))
    }
}

fn read_all_atoms(path: &Path) -> Result<CifChains, String> {
    let text = std::fs::read_to_string(path).map_err(|error| error.to_string())?;
    let lines = text.lines().collect::<Vec<_>>();
    let mut headers = Vec::<String>::new();
    let mut rows = Vec::<Vec<&str>>::new();
    let mut at = 0usize;
    while at < lines.len() {
        if lines[at].trim() != "loop_" {
            at += 1;
            continue;
        }
        let mut cursor = at + 1;
        let mut candidate = Vec::<String>::new();
        while cursor < lines.len() && lines[cursor].trim_start().starts_with('_') {
            candidate.push(lines[cursor].trim().to_owned());
            cursor += 1;
        }
        if !candidate.iter().any(|name| name.starts_with("_atom_site.")) {
            at = cursor;
            continue;
        }
        headers = candidate;
        while cursor < lines.len() {
            let line = lines[cursor].trim();
            if line == "#" || line == "loop_" || line.starts_with('_') {
                break;
            }
            if !line.is_empty() {
                let fields = line.split_whitespace().collect::<Vec<_>>();
                if fields.len() != headers.len() {
                    return Err(format!(
                        "{} atom_site row {} has {} fields under {} headers",
                        path.display(),
                        cursor + 1,
                        fields.len(),
                        headers.len()
                    ));
                }
                rows.push(fields);
            }
            cursor += 1;
        }
        break;
    }
    if headers.is_empty() || rows.is_empty() {
        return Err(format!("{} has no atom_site loop", path.display()));
    }
    let column = |name: &str| -> Result<usize, String> {
        headers
            .iter()
            .position(|candidate| candidate == name)
            .ok_or_else(|| format!("{} has no {name} atom_site face", path.display()))
    };
    let atom = column("_atom_site.label_atom_id")?;
    let chain = column("_atom_site.label_asym_id")?;
    let residue = column("_atom_site.label_seq_id")?;
    let x = column("_atom_site.Cartn_x")?;
    let y = column("_atom_site.Cartn_y")?;
    let z = column("_atom_site.Cartn_z")?;

    let mut chains: CifChains = BTreeMap::new();
    for row in rows {
        let ordinal = row[residue]
            .parse::<i32>()
            .map_err(|error| format!("{}: {error}", row[residue]))?;
        let mut lower = [0_i64; 3];
        let mut upper = [0_i64; 3];
        for (axis, at) in [x, y, z].into_iter().enumerate() {
            let (significand, places) = parse_decimal(row[at])?;
            let (low, high) = outward_wire(significand, places)?;
            lower[axis] = low;
            upper[axis] = high;
        }
        chains
            .entry(row[chain].to_owned())
            .or_default()
            .entry(ordinal)
            .or_default()
            .push(CifAtom {
                label: row[atom].to_owned(),
                lower,
                upper,
            });
    }
    Ok(chains)
}

/// One presented component on the scaled wire, with its residue ordering fixed and its alpha
/// carbons located.
struct ScaledComponent {
    atoms: Vec<ScaledOccurrence>,
    residues: usize,
    /// The address of the alpha carbon of each residue, in residue order.
    alpha_carbons: Vec<GrainAddress>,
}

fn scale_component(
    chain: &BTreeMap<i32, Vec<CifAtom>>,
    component: u32,
) -> Result<ScaledComponent, String> {
    let mut atoms = Vec::new();
    let mut alpha_carbons = Vec::new();
    for (residue_at, (_, members)) in chain.iter().enumerate() {
        let residue = residue_at as u32 + 1;
        let mut alpha = None;
        for (atom_at, member) in members.iter().enumerate() {
            let address = GrainAddress::new(component, residue, atom_at as u32 + 1);
            if member.label == "CA" {
                if alpha.is_some() {
                    return Err(format!("residue {residue} carries two alpha carbons"));
                }
                alpha = Some(address);
            }
            atoms.push(ScaledOccurrence {
                address,
                label: member.label.clone(),
                lower: member.lower,
                upper: member.upper,
            });
        }
        alpha_carbons.push(alpha.ok_or_else(|| format!("residue {residue} has no alpha carbon"))?);
    }
    Ok(ScaledComponent {
        residues: chain.len(),
        atoms,
        alpha_carbons,
    })
}

struct FamilyReturn {
    census: GrainCensus,
    witness: InflationWitness,
    reopen: GrainReopenReceipt,
}

fn enact_family(
    lineage: &str,
    left: &ScaledComponent,
    right: &ScaledComponent,
    aperture: &ScaledAperture,
    denominator: &BigUint,
) -> Result<FamilyReturn, String> {
    let atom_face =
        found_atom_face(&left.atoms, &right.atoms, aperture).map_err(|error| error.to_string())?;
    let fine = atom_face
        .restricted(Grain::Residue)
        .map_err(|error| error.to_string())?;

    let selection = GrainSelection::declare(
        "label_atom_id == CA, the receiver crates/holonic-life/examples/m5/cif.rs::REPRESENTATIVE enacts",
        Grain::Residue,
        Grain::Atom,
        left.alpha_carbons
            .iter()
            .chain(right.alpha_carbons.iter())
            .copied(),
    )
    .map_err(|error| error.to_string())?;
    let coarse = selection.apply(&atom_face);

    let census = GrainCensus::measure(lineage, left.residues * right.residues, &fine, &coarse)
        .map_err(|error| error.to_string())?;
    let reopen = check_grain_reopen(&selection, &atom_face).map_err(|error| error.to_string())?;

    // The forcing witness of each coarse pair: the fine pair whose class the join took.
    let mut forcing: BTreeMap<GrainPair, GrainPair> = BTreeMap::new();
    for (pair, class) in atom_face.classified() {
        let Some(coarse_pair) = pair.project(Grain::Residue).map_err(|e| e.to_string())? else {
            continue;
        };
        if *class == fine.class(&coarse_pair) {
            forcing.entry(coarse_pair).or_insert(*pair);
        }
    }

    // Positions of the representatives, and the measured grain radius of every residue.
    let mut positions: BTreeMap<GrainCell, ScaledOccurrence> = BTreeMap::new();
    let mut radii: BTreeMap<GrainCell, Rat> = BTreeMap::new();
    let root_denominator = BigUint::from(1_000_000_u32);
    let squared_denominator = {
        let den = BigInt::from(denominator.clone());
        Rat::new(BigInt::one(), &den * &den)
    };
    for component in [left, right] {
        let alphas = component
            .alpha_carbons
            .iter()
            .map(|address| (address.cell(Grain::Residue), *address))
            .collect::<BTreeMap<_, _>>();
        for occurrence in &component.atoms {
            let residue_cell = occurrence.address.cell(Grain::Residue);
            let alpha = alphas[&residue_cell];
            if occurrence.address == alpha {
                positions.insert(occurrence.address.cell(Grain::Atom), occurrence.clone());
            }
        }
        for occurrence in &component.atoms {
            let residue_cell = occurrence.address.cell(Grain::Residue);
            let alpha_position = &positions[&alphas[&residue_cell].cell(Grain::Atom)];
            let (_, high) = ScaledAperture::squared_distance(alpha_position, occurrence)
                .map_err(|error| error.to_string())?;
            let squared = &Rat::from_integer(BigInt::from(high)) * &squared_denominator;
            let bound = rational_root_upper_bound(&squared, &root_denominator)
                .map_err(|error| error.to_string())?;
            let entry = radii.entry(residue_cell).or_insert_with(|| bound.clone());
            if bound > *entry {
                *entry = bound;
            }
        }
    }

    let readings = coarse_readings(&selection, &fine, &positions, &radii, denominator, &forcing)
        .map_err(|error| error.to_string())?;
    let fine_aperture_squared = Rat::from_integer(BigInt::from(CONTACT_RADIUS * CONTACT_RADIUS));
    let witness = InflationWitness::measure(lineage, fine_aperture_squared, &readings)
        .map_err(|error| error.to_string())?;

    Ok(FamilyReturn {
        census,
        witness,
        reopen,
    })
}

/// One residue of a synthetic component: three atoms on the `x` axis, the alpha carbon at the
/// residue centre and one atom one angstrom to each side of it.
fn synthetic_residue(
    component: u32,
    residue: u32,
    centre_angstroms: i64,
    toward: i64,
) -> (Vec<ScaledOccurrence>, GrainAddress) {
    let unit = 10_i64.pow(RESIDENT_DECIMAL_PLACES);
    let alpha = GrainAddress::new(component, residue, 2);
    let atoms = [
        ("SIDE", centre_angstroms + toward),
        ("CA", centre_angstroms),
        ("AWAY", centre_angstroms - toward),
    ]
    .into_iter()
    .enumerate()
    .map(|(at, (label, x))| ScaledOccurrence {
        address: GrainAddress::new(component, residue, at as u32 + 1),
        label: label.to_owned(),
        lower: [x * unit, 0, 0],
        upper: [x * unit, 0, 0],
    })
    .collect();
    (atoms, alpha)
}

/// Two synthetic components on the `x` axis, on the same exact wire the M5 intake uses.
///
/// Component one carries residues at 0, 20 and 40 angstroms; component two carries residues at 9,
/// 29 and 46. Every residue carries one atom one angstrom toward its partner, so the first two
/// residue pairs are 9 angstroms apart at their alpha carbons — outside the 8 angstrom aperture —
/// and 7 angstroms apart at those atoms, inside it. The third pair is 6 angstroms apart at its
/// alpha carbons, so the coarse receiver reads it too. That is exactly the situation the fixture
/// measures: a coarse population strictly inside a fine one.
fn synthetic_intake() -> (ScaledComponent, ScaledComponent) {
    let build = |component: u32, centres: [i64; 3], toward: i64| -> ScaledComponent {
        let mut atoms = Vec::new();
        let mut alpha_carbons = Vec::new();
        for (at, centre) in centres.into_iter().enumerate() {
            let (members, alpha) = synthetic_residue(component, at as u32 + 1, centre, toward);
            atoms.extend(members);
            alpha_carbons.push(alpha);
        }
        ScaledComponent {
            residues: centres.len(),
            atoms,
            alpha_carbons,
        }
    };
    (
        build(1, [0, 20, 40], 1),
        build(2, [9, 29, 46], -1),
    )
}

/// The two claims the M5 fixture exists to carry, on an intake this test builds itself: no
/// fixture, no environment, and therefore no run in which they go unchecked.
///
/// * `reopen_apply` on a complete atom-grain population — `check_grain_reopen` returns
///   `source_reopened == 1`, which is
///   `Foundation/GrainRestriction.lean::grain_residual_reopens_the_source`.
/// * The pair-table identity `fine_inside - coarse_inside = fine_only_inside` with
///   `coarse_only_inside = 0`, which is
///   `Foundation/GrainRestriction.lean::selection_inside_implies_fine_inside` measured rather than
///   assumed.
#[test]
fn the_pair_table_identities_hold_on_a_synthetic_atom_grain_intake() {
    let (left, right) = synthetic_intake();
    let denominator = BigUint::from(10_u64.pow(RESIDENT_DECIMAL_PLACES));
    let wire = i128::from(10_i64.pow(RESIDENT_DECIMAL_PLACES));
    let aperture = ScaledAperture {
        lineage: format!(
            "declared contact receiver: exact distance not greater than {CONTACT_RADIUS} angstroms"
        ),
        denominator: 10_u64.pow(RESIDENT_DECIMAL_PLACES),
        aperture_squared_wire: CONTACT_RADIUS * CONTACT_RADIUS * wire * wire,
    };

    let returned = enact_family(
        "synthetic two-component intake",
        &left,
        &right,
        &aperture,
        &denominator,
    )
    .expect("the synthetic family enacts");
    let census = &returned.census;

    assert_eq!(
        [
            census.pairs,
            census.fine_inside,
            census.fine_open,
            census.coarse_inside,
            census.coarse_open,
            census.fine_only_inside,
            census.coarse_only_inside,
            census.open_shared,
        ],
        [9, 3, 0, 1, 0, 2, 0, 0],
        "pairs / fine inside / fine open / coarse inside / coarse open / fine-only / coarse-only \
         / open-shared"
    );
    assert_eq!(
        census.coarse_only_inside, 0,
        "coarse implies fine is a theorem, checked not assumed"
    );
    assert_eq!(
        census.fine_inside - census.coarse_inside,
        census.fine_only_inside,
        "with no coarse-only pair the fine-only count is forced"
    );
    assert_eq!(
        returned.reopen.source_reopened, 1,
        "reopen_apply on the complete atom-grain source"
    );
    assert!(
        returned.witness.certified_bound_squared >= returned.witness.coarse_aperture_squared,
        "the grain-radius certificate bounds the measured requirement"
    );
    // The two 9-angstrom alpha-carbon separations are the extremal requirement, and the
    // triangle-inequality certificate is (8 + 1 + 1)^2 = 100.
    assert_eq!(
        returned.witness.coarse_aperture_squared,
        Rat::from_integer(BigInt::from(81)),
    );
    assert_eq!(
        returned.witness.certified_bound_squared,
        Rat::from_integer(BigInt::from(100)),
    );
    returned
        .witness
        .check_declared(&Rat::from_integer(BigInt::from(64)))
        .expect_err("the equal 8 angstrom coarse aperture does not carry the fine contacts");
}

/// `ScaledOccurrence` is public and `Deserialize`, so its `i64` numerators arrive unbounded. A
/// squared distance that leaves the exact `i128` wire the aperture is carried on is a named
/// refusal, never a wrapped product that would read a distant pair `Inside`.
#[test]
fn a_scaled_coordinate_that_leaves_the_exact_wire_is_a_typed_refusal() {
    let hostile = |lower: [i64; 3], upper: [i64; 3], component: u32| ScaledOccurrence {
        address: GrainAddress::new(component, 1, 1),
        label: "hostile".to_owned(),
        lower,
        upper,
    };
    let aperture = ScaledAperture {
        lineage: "one unit squared".to_owned(),
        denominator: 1,
        aperture_squared_wire: 1,
    };

    // i64::MIN against i64::MAX on one axis: the difference is 2^64 - 1 and its square is outside
    // i128 by a single bit.
    let left = hostile([i64::MIN, 0, 0], [i64::MIN, 0, 0], 1);
    let right = hostile([i64::MAX, 0, 0], [i64::MAX, 0, 0], 2);
    assert!(matches!(
        ScaledAperture::squared_distance(&left, &right),
        Err(GrainRefusal::ScaledDistanceLeavesTheWire {
            axis: 0,
            left: address,
            ..
        }) if address == left.address
    ));
    assert!(matches!(
        found_atom_face(
            std::slice::from_ref(&left),
            std::slice::from_ref(&right),
            &aperture
        ),
        Err(GrainRefusal::ScaledDistanceLeavesTheWire { axis: 0, .. })
    ));

    // Each per-axis square fits on its own and the accumulation does not: an axis difference of
    // 2^63 squares to 2^126, and the second axis already carries the running sum past i128::MAX.
    let spread = hostile([0, 0, 0], [0, 0, 0], 1);
    let far = hostile(
        [i64::MIN, i64::MIN, i64::MIN],
        [i64::MIN, i64::MIN, i64::MIN],
        2,
    );
    assert!(matches!(
        ScaledAperture::squared_distance(&spread, &far),
        Err(GrainRefusal::ScaledDistanceLeavesTheWire { axis: 1, .. }),
    ));

    // Nothing that does fit is refused: the wire is used to its end. An axis difference of 2^62 on
    // each of three axes is 3 * 2^124, which is inside i128, and it is returned exactly.
    let half = 1_i64 << 61;
    let inside = hostile([-half, -half, -half], [-half, -half, -half], 1);
    let other = hostile([half, half, half], [half, half, half], 2);
    let square = (i128::from(half) * 2).pow(2);
    assert_eq!(square, 1_i128 << 124);
    assert_eq!(
        ScaledAperture::squared_distance(&inside, &other).expect("3 * 2^124 is inside the wire"),
        (3 * square, 3 * square)
    );
}

#[test]
fn the_m5_pair_table_reproduces_from_a_complete_atom_grain_intake() {
    let root = std::env::var_os(STRUCTURE_ROOT_ENV)
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(DEFAULT_STRUCTURE_ROOT));
    assert!(
        root.is_dir(),
        "the authenticated M5 structure root {} is absent, so the measured pair table cannot be \
         checked, and this test refuses to report success without checking it. Place the \
         authenticated release at that path, or set {STRUCTURE_ROOT_ENV} to the directory \
         carrying designed-free-rbx1.cif, ptxv2-free-rbx1-seed2.cif and \
         ptxv2-cul1-rbx1-seed0.cif. The grain laws and the pair-table identities themselves are \
         checked without any fixture by \
         the_pair_table_identities_hold_on_a_synthetic_atom_grain_intake.",
        root.display()
    );

    let designed = read_all_atoms(&root.join("designed-free-rbx1.cif")).expect("designed reads");
    let free = read_all_atoms(&root.join("ptxv2-free-rbx1-seed2.cif")).expect("free reads");
    let complex = read_all_atoms(&root.join("ptxv2-cul1-rbx1-seed0.cif")).expect("complex reads");

    // Components are bound by residue count exactly as the M5 deed binds them by ordered sequence:
    // the binder carries 96 residues, RBX1 carries 108 and CUL1 carries 366. The single-residue
    // chains are the zinc occurrences, which carry no alpha carbon and are not protein components.
    let pick = |chains: &CifChains, residues: usize, component: u32| -> ScaledComponent {
        let selected = chains
            .iter()
            .filter(|(_, chain)| chain.len() == residues)
            .collect::<Vec<_>>();
        assert_eq!(
            selected.len(),
            1,
            "exactly one chain carries {residues} residues"
        );
        scale_component(selected[0].1, component).expect("the component scales")
    };

    let denominator = BigUint::from(10_u64.pow(RESIDENT_DECIMAL_PLACES));
    let wire = i128::from(10_i64.pow(RESIDENT_DECIMAL_PLACES));
    let aperture = ScaledAperture {
        lineage: format!(
            "declared contact receiver: exact distance not greater than {CONTACT_RADIUS} angstroms"
        ),
        denominator: 10_u64.pow(RESIDENT_DECIMAL_PLACES),
        aperture_squared_wire: CONTACT_RADIUS * CONTACT_RADIUS * wire * wire,
    };

    let families: [(&str, ScaledComponent, ScaledComponent, [usize; 8]); 4] = [
        (
            "designed free RBX1 / binder x RBX1",
            pick(&designed, 96, 1),
            pick(&designed, 108, 2),
            [10_368, 303, 1, 64, 1, 239, 0, 0],
        ),
        (
            "Protenix free seed 2 / binder x RBX1",
            pick(&free, 96, 1),
            pick(&free, 108, 2),
            [10_368, 366, 0, 59, 0, 307, 0, 0],
        ),
        (
            "Protenix CUL1-RBX1 seed 0 / binder x RBX1",
            pick(&complex, 96, 1),
            pick(&complex, 108, 2),
            [10_368, 260, 0, 45, 0, 215, 0, 0],
        ),
        (
            "Protenix CUL1-RBX1 seed 0 / CUL1 x RBX1",
            pick(&complex, 366, 1),
            pick(&complex, 108, 2),
            [39_528, 468, 0, 133, 0, 335, 0, 0],
        ),
    ];

    let mut total = [0_usize; 8];
    let mut required = Rat::from_integer(BigInt::from(0));
    let mut required_lineage = String::new();
    for (lineage, left, right, expected) in &families {
        let returned = enact_family(lineage, left, right, &aperture, &denominator)
            .unwrap_or_else(|error| panic!("{lineage}: {error}"));
        let census = &returned.census;
        let measured = [
            census.pairs,
            census.fine_inside,
            census.fine_open,
            census.coarse_inside,
            census.coarse_open,
            census.fine_only_inside,
            census.coarse_only_inside,
            census.open_shared,
        ];
        assert_eq!(
            measured, *expected,
            "{lineage}: pairs / fine inside / fine open / coarse inside / coarse open / fine-only \
             / coarse-only / open-shared"
        );
        assert_eq!(
            census.coarse_only_inside, 0,
            "{lineage}: coarse implies fine is a theorem, checked not assumed"
        );
        assert_eq!(
            census.fine_inside - census.coarse_inside,
            census.fine_only_inside,
            "{lineage}: with no coarse-only pair the fine-only count is forced"
        );
        assert_eq!(
            returned.reopen.source_reopened, 1,
            "{lineage}: reopen_apply"
        );
        assert!(
            returned.witness.certified_bound_squared >= returned.witness.coarse_aperture_squared,
            "{lineage}: the grain-radius certificate bounds the measured requirement"
        );
        returned
            .witness
            .check_declared(&Rat::from_integer(BigInt::from(64)))
            .expect_err(&format!(
                "{lineage}: the equal 8 angstrom coarse aperture does not carry the fine contacts"
            ));
        let row_root = rational_root_upper_bound(
            &returned.witness.coarse_aperture_squared,
            &BigUint::from(10_000_u32),
        )
        .expect("the row's required aperture has a rational root bound");
        eprintln!(
            "grain_tower fixture | {lineage} | pairs {} | fine inside {} | coarse inside {} | \
             fine-only {} | coarse-only {} | open fine/coarse/shared {}/{}/{} | required coarse \
             aperture {row_root} (squared {}) | inflation squared {} | extremal {:?} forced by \
             {:?}",
            census.pairs,
            census.fine_inside,
            census.coarse_inside,
            census.fine_only_inside,
            census.coarse_only_inside,
            census.fine_open,
            census.coarse_open,
            census.open_shared,
            returned.witness.coarse_aperture_squared,
            returned.witness.inflation_ratio_squared,
            returned.witness.extremal.pair,
            returned.witness.extremal.forcing_fine_pair,
        );
        if returned.witness.coarse_aperture_squared > required {
            required = returned.witness.coarse_aperture_squared.clone();
            required_lineage = format!("{lineage} at {:?}", returned.witness.extremal.pair);
        }
        for (slot, value) in total.iter_mut().zip(measured) {
            *slot += value;
        }
    }

    assert_eq!(
        total,
        [70_632, 1_397, 1, 301, 1, 1_096, 0, 0],
        "the complete M5 pair table"
    );
    // 116656202097359145 / 10^14 exactly: CUL1 residue 366 against RBX1 residue 60, forced by a
    // carbonyl oxygen 27.6 angstroms from its own alpha carbon. The inflation is measured, and the
    // witness is what shows why it must be exhibited rather than guessed.
    assert_eq!(
        required,
        Rat::new(
            BigInt::from(116_656_202_097_359_145_i128),
            BigInt::from(100_000_000_000_000_i128)
        ),
        "the least coarse aperture squared that carries every fine contact, attained at \
         {required_lineage}"
    );
    let root_bound = rational_root_upper_bound(&required, &BigUint::from(10_000_u32))
        .expect("the required aperture has a rational root bound");
    assert_eq!(
        root_bound,
        Rat::new(BigInt::from(341_550_i64), BigInt::from(10_000_i64)),
        "34.1550 angstroms, 4.2694 times the 8 angstrom fine aperture"
    );
}
