//! The laws of B7's physicochemical receiver, and the measured M5 exhibition.
//!
//! The synthetic tests state what the Lean owner
//! `formal/elementary-holonics/ElementaryHolonics/Foundation/PhysicochemicalReceiver.lean` proves,
//! and they run everywhere with no fixture and no environment variable. The fixture tests
//! reproduce the authenticated release and **fail** when it is absent: a test that cannot run says
//! so by failing, because cargo discards the output of a passing test.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigInt;
use num_traits::{One, Zero};
use relational_geometry::Rat;

use super::*;
use crate::EventId;
use crate::physical_constraint_complex::{
    ComponentMaterial, ConstraintComponentId, ConstraintVertexId, CoordinateBox3,
    DistanceAperture, PairUncertainty, PhysicalConstraintComplex, ResidueMaterial,
};
use crate::physical_intake::mmcif::{AtomOccurrence, ChainOccurrence, DecimalToken, ResidueOccurrence};
use crate::physical_intake::{
    ComponentGrain, PresentedFamily, enacted_classes, enacted_within_component_classes,
    found_constraint_complex,
};
use crate::physical_occurrence::fixture::{
    absent_structure_root_message, complete_environment, complete_environment_with,
    eight_angstrom_aperture, m5_occurrences, structure_root, RESIDENT_DECIMAL_PLACES,
    REPRESENTATIVE,
};
use crate::physical_occurrence::{
    Occurrence, OccurrenceId, OccurrenceKind,
};

// ---------------------------------------------------------------------------------------------
// Synthetic material: a chain for the chemistry and a material for the exact geometry
// ---------------------------------------------------------------------------------------------

/// One synthetic residue: its monomer name and its atoms, each with a label, an element and an
/// exact integer place.
struct SyntheticResidue {
    monomer: &'static str,
    atoms: Vec<(&'static str, &'static str, [i64; 3])>,
}

fn residue(monomer: &'static str, atoms: &[(&'static str, &'static str, [i64; 3])]) -> SyntheticResidue {
    SyntheticResidue {
        monomer,
        atoms: atoms.to_vec(),
    }
}

fn integer(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn point(place: [i64; 3]) -> CoordinateBox3 {
    CoordinateBox3::point(integer(place[0]), integer(place[1]), integer(place[2]))
}

/// The presented chain, whose coordinate tokens are never read by [`SiteTable::found`]: the site
/// table declares chemistry and the complex declares geometry, and the founding ties the two by
/// name.
fn synthetic_chain(label: &str, residues: &[SyntheticResidue]) -> ChainOccurrence {
    let token = DecimalToken::parse("0.0").expect("a plain decimal");
    let presented = residues
        .iter()
        .enumerate()
        .map(|(at, residue)| ResidueOccurrence {
            source_ordinal: at as i32 + 1,
            monomer: residue.monomer.to_owned(),
            atoms: residue
                .atoms
                .iter()
                .map(|(label, element, _)| AtomOccurrence {
                    label: (*label).to_owned(),
                    element: Some((*element).to_owned()),
                    alternate: None,
                    x: token.clone(),
                    y: token.clone(),
                    z: token.clone(),
                    occupancy: None,
                    temperature_factor: None,
                })
                .collect(),
        })
        .collect::<Vec<_>>();
    let atom_occurrences = presented.iter().map(|residue| residue.atoms.len()).sum();
    ChainOccurrence {
        label_asym_id: label.to_owned(),
        entity: None,
        residues: presented,
        atom_occurrences,
    }
}

/// The exact material at a declared grain, with **point** coordinates so the rigid-motion law can
/// be stated on it.
fn synthetic_material(
    lineage: &str,
    residues: &[SyntheticResidue],
    grain: &ComponentGrain,
) -> ComponentMaterial {
    let mut material = Vec::new();
    for (at, residue) in residues.iter().enumerate() {
        let source_ordinal = at as i32 + 1;
        match grain {
            ComponentGrain::Atom => {
                for (label, _, place) in &residue.atoms {
                    material.push(ResidueMaterial {
                        source_ordinal,
                        monomer: format!("{}:{label}", residue.monomer),
                        position: point(*place),
                    });
                }
            }
            ComponentGrain::Representative { atom_label } => {
                let (_, _, place) = residue
                    .atoms
                    .iter()
                    .find(|(label, _, _)| label == atom_label)
                    .expect("the synthetic residue carries its representative");
                material.push(ResidueMaterial {
                    source_ordinal,
                    monomer: residue.monomer.to_owned(),
                    position: point(*place),
                });
            }
        }
    }
    ComponentMaterial {
        lineage: lineage.to_owned(),
        residues: material,
    }
}

fn uncertainty_grid(left: usize, right: usize) -> BTreeMap<(u32, u32), PairUncertainty> {
    let mut grid = BTreeMap::new();
    for a in 1..=left as u32 {
        for b in 1..=right as u32 {
            grid.insert((a, b), synthetic_uncertainty());
        }
    }
    grid
}

fn uncertainty_for(pairs: &[(u32, u32)]) -> BTreeMap<(u32, u32), PairUncertainty> {
    pairs
        .iter()
        .map(|pair| (*pair, synthetic_uncertainty()))
        .collect()
}

fn synthetic_uncertainty() -> PairUncertainty {
    PairUncertainty {
        source_lineage: "synthetic: this receiver reads no uncertainty".to_owned(),
        row_given_column_bits: 0,
        column_given_row_bits: 0,
        row_given_column: ExactInterval::point(Rat::zero()),
        column_given_row: ExactInterval::point(Rat::zero()),
        row_given_column_ulp: Rat::zero(),
        column_given_row_ulp: Rat::zero(),
    }
}

fn aperture(squared: i64) -> DistanceAperture {
    DistanceAperture {
        lineage: format!("synthetic aperture, squared {squared}"),
        squared: integer(squared),
    }
}


/// A two-component complex over declared materials, with one cross family at a declared aperture.
fn cross_complex(
    lineage: &str,
    left: ComponentMaterial,
    right: ComponentMaterial,
    aperture: DistanceAperture,
) -> PhysicalConstraintComplex {
    let left_extent = left.residues.len();
    let right_extent = right.residues.len();
    let mut complex = PhysicalConstraintComplex::found(lineage, EventId(1), vec![left, right])
        .expect("the complex founds");
    let enacted = enacted_classes(
        &complex,
        ConstraintComponentId(1),
        ConstraintComponentId(2),
        &aperture,
    )
    .expect("the classes enact");
    complex
        .found_contact_family(
            ConstraintComponentId(1),
            ConstraintComponentId(2),
            aperture,
            &enacted,
            &uncertainty_grid(left_extent, right_extent),
        )
        .expect("the family founds");
    complex
}

/// The same, founded through `found_constraint_complex` so the library path is exercised.
fn cross_complex_through_intake(
    lineage: &str,
    left: ComponentMaterial,
    right: ComponentMaterial,
    aperture: DistanceAperture,
) -> PhysicalConstraintComplex {
    let left_extent = left.residues.len();
    let right_extent = right.residues.len();
    found_constraint_complex(
        lineage,
        EventId(1),
        vec![left, right],
        vec![PresentedFamily {
            left: ConstraintComponentId(1),
            right: ConstraintComponentId(2),
            aperture,
            uncertainty: uncertainty_grid(left_extent, right_extent),
        }],
    )
    .expect("the complex founds through the library intake")
}

// ---------------------------------------------------------------------------------------------
// The worked synthetic presentation
// ---------------------------------------------------------------------------------------------

/// Four binder residues against four target residues, at exact integer places, at the CA grain.
///
/// | binder | target | separation | class pair |
/// |---|---|---|---|
/// | `LEU` at `(0,0,0)` | `ILE` at `(3,0,0)` | 3 | hydrophobic–hydrophobic |
/// | `ASP` at `(0,6,0)` | `LYS` at `(3,6,0)` | 3 | negative–positive |
/// | `LYS` at `(0,12,0)` | `ARG` at `(3,12,0)` | 3 | positive–positive |
/// | `SER` at `(0,18,0)` | `PHE` at `(3,18,0)` | 3 | polar–aromatic |
///
/// The columns are `18` apart, so at an aperture squared of `16` exactly the four facing pairs are
/// `Inside` and everything else is `Outside`.
fn worked_binder() -> Vec<SyntheticResidue> {
    vec![
        residue("LEU", &[("CA", "C", [0, 0, 0]), ("CB", "C", [0, 1, 0])]),
        residue("ASP", &[("CA", "C", [0, 6, 0]), ("CB", "C", [0, 7, 0])]),
        residue("LYS", &[("CA", "C", [0, 12, 0]), ("CB", "C", [0, 13, 0])]),
        residue("SER", &[("CA", "C", [0, 18, 0]), ("CB", "C", [0, 19, 0])]),
    ]
}

fn worked_target() -> Vec<SyntheticResidue> {
    vec![
        residue("ILE", &[("CA", "C", [3, 0, 0]), ("CB", "C", [3, 1, 0])]),
        residue("LYS", &[("CA", "C", [3, 6, 0]), ("CB", "C", [3, 7, 0])]),
        residue("ARG", &[("CA", "C", [3, 12, 0]), ("CB", "C", [3, 13, 0])]),
        residue("PHE", &[("CA", "C", [3, 18, 0]), ("CB", "C", [3, 19, 0])]),
    ]
}

fn representative_grain() -> ComponentGrain {
    ComponentGrain::Representative {
        atom_label: "CA".to_owned(),
    }
}

fn worked_complex() -> PhysicalConstraintComplex {
    cross_complex(
        "worked synthetic presentation",
        synthetic_material("binder", &worked_binder(), &representative_grain()),
        synthetic_material("target", &worked_target(), &representative_grain()),
        aperture(16),
    )
}

fn worked_sites(complex: &PhysicalConstraintComplex) -> SiteTable {
    let binder = synthetic_chain("A", &worked_binder());
    let target = synthetic_chain("B", &worked_target());
    SiteTable::found(
        "worked synthetic presentation",
        complex,
        &[&binder, &target],
        &representative_grain(),
    )
    .expect("the site table founds and agrees with the complex")
}

fn declared_basis() -> ProtonationBasis {
    declared_protonation(
        ExteriorDeclaration::declare(
            "the reading is taken under a declared protonation in which aspartate and glutamate \
             are deprotonated and lysine, arginine are protonated",
            "declared by this test, because the synthetic environment records no pH",
        )
        .expect("a stated declaration"),
    )
}

fn declared_bound(ceiling: u64) -> PairWorkBound {
    PairWorkBound::declare(
        ceiling,
        "declared by this test: the synthetic presentation's pair population is known exactly and \
         the ceiling is above it",
    )
    .expect("a stated bound")
}

// ---------------------------------------------------------------------------------------------
// 1. The typed units
// ---------------------------------------------------------------------------------------------

/// **Every reading carries its unit, and adding unlike units is a typed refusal.**
#[test]
fn the_unit_algebra_refuses_to_add_unlike_units() {
    let length = UnitedInterval::point(integer(3), length_dimension());
    let charge = UnitedInterval::point(integer(3), charge_dimension());
    let count = UnitedInterval::count(3);
    assert_eq!(
        length.sum(&length).expect("like units add").enclosure().lower,
        integer(6)
    );
    let refusal = length.sum(&charge).expect_err("unlike units refuse");
    assert!(
        matches!(refusal, PhysicochemicalRefusal::UnlikeUnits { .. }),
        "{refusal}"
    );
    assert!(count.sum(&length).is_err(), "a count is not a length");
    // The product is always lawful and the exponent words add.
    let area = length.times(&length).expect("a product is lawful");
    assert_eq!(
        *area.dimension(),
        length_dimension().powed(&integer(2)),
        "the exponent words add"
    );
    // The Coulomb dimension is `e^2 / angstrom`, built from the declared base and nothing else.
    let coulomb = charge
        .times(&charge)
        .expect("a product is lawful")
        .times(&UnitedInterval::point(
            Rat::one(),
            length_dimension().inverted(),
        ))
        .expect("a product is lawful");
    assert_eq!(*coulomb.dimension(), coulomb_dimension());
    assert!(!coulomb_dimension().is_dimensionless());
    assert!(count_dimension().is_dimensionless());
}

/// **A cast into the declared energy unit is a declared chart change, and a dimensionless one is
/// refused by its own owner.**
#[test]
fn the_coulomb_cast_is_declared_and_a_dimensionless_cast_is_refused() {
    let cast = declared_coulomb_cast().expect("the named declaration");
    assert!(!cast.dimension().is_dimensionless());
    let base = physicochemical_base();
    let refusal = Cast::declare(
        "a cast that erases the dimension",
        Quantity::dimensionless(Rat::one(), &base),
    )
    .expect_err("quantity.rs refuses a dimensionless cast");
    assert!(format!("{refusal}").contains("dimension"), "{refusal}");
}

// ---------------------------------------------------------------------------------------------
// 2. The declared tables, and the refusals that keep them declarations
// ---------------------------------------------------------------------------------------------

/// **A table needs a named source and a stated scope; without both it is a default wearing a name.**
#[test]
fn a_table_needs_a_named_source_and_a_stated_scope() {
    assert!(matches!(
        TableGround::declare("", "a scope").expect_err("an unnamed source refuses"),
        PhysicochemicalRefusal::TableGroundNotStated
    ));
    assert!(matches!(
        TableGround::declare("a source", "   ").expect_err("an unstated scope refuses"),
        PhysicochemicalRefusal::TableGroundNotStated
    ));
    let ground = TableGround::declare("a source", "a scope").expect("both stated");
    assert!(matches!(
        ResidueClassTable::declare("", ground.clone(), []).expect_err("an unnamed table refuses"),
        PhysicochemicalRefusal::TableNotNamed
    ));
    assert!(matches!(
        ResidueClassTable::declare("named", ground, []).expect_err("an empty table refuses"),
        PhysicochemicalRefusal::TableIsEmpty { .. }
    ));
    assert!(matches!(
        Dielectric::declare(
            Rat::zero(),
            TableGround::declare("a source", "a scope").expect("stated")
        )
        .expect_err("a zero permittivity refuses"),
        PhysicochemicalRefusal::DielectricNotPositive
    ));
}

/// **A residue outside a table's scope is refused by name and never filed under a default class.**
#[test]
fn a_residue_outside_a_table_is_refused_and_never_defaulted() {
    let tables = tables_histidine_neutral();
    assert_eq!(
        tables
            .residue_class()
            .class_of("ALA")
            .expect("a named residue"),
        ResidueClass::Hydrophobic
    );
    let refusal = tables
        .residue_class()
        .class_of("SEP")
        .expect_err("a phosphoserine is outside the declared scope");
    assert!(
        matches!(refusal, PhysicochemicalRefusal::ResidueNotInTable { .. }),
        "{refusal}"
    );
    let radii = tables.radii();
    assert_eq!(radii.raw_radius("C").expect("carbon"), hundredths(170));
    assert!(radii.raw_radius("SE").is_err(), "selenium is not declared");
    // The ground travels with the table and states what it does not cover.
    assert!(tables.residue_class().ground().scope().contains("refused"));
    assert!(tables.radii().ground().scope().contains("truncation"));
}

/// **Two shipped tables differ at exactly one residue, and that residue is a pH claim.**
#[test]
fn the_two_shipped_residue_class_tables_differ_at_histidine_alone() {
    let neutral = residue_classes_histidine_polar();
    let protonated = residue_classes_histidine_positive();
    assert_eq!(
        neutral.divergence(&protonated),
        BTreeSet::from(["HIS".to_owned()])
    );
    assert_eq!(neutral.class_of("HIS").expect("named"), ResidueClass::Polar);
    assert_eq!(
        protonated.class_of("HIS").expect("named"),
        ResidueClass::PositivelyCharged
    );
}

// ---------------------------------------------------------------------------------------------
// 3. The pH gate
// ---------------------------------------------------------------------------------------------

/// **An undeclared acidity axis refuses the charged reading, naming the axis and carrying the
/// environment's own stated reason.**
#[test]
fn an_undeclared_acidity_refuses_the_charged_reading_naming_the_axis() {
    let environment =
        complete_environment("synthetic", "free", "0").expect("every axis is stated");
    let refusal = protonation_basis(&environment).expect_err("the synthetic fixture records no pH");
    let PhysicochemicalRefusal::AcidityUndeclared { axis, why, .. } = &refusal else {
        panic!("the refusal names the axis: {refusal}");
    };
    assert_eq!(*axis, CoordinateName::Acidity);
    assert!(why.contains("no pH"), "{why}");
    assert!(
        format!("{refusal}").contains("pH and protonation assumption"),
        "the refusal renders the axis by its label: {refusal}"
    );
    // The situated entry point is the one that enforces the gate.
    let complex = worked_complex();
    let sites = worked_sites(&complex);
    let occurrence = Occurrence::found(
        OccurrenceId(1),
        OccurrenceKind::Designed {
            generator: "the synthetic fixture".to_owned(),
            rounds: 0,
        },
        "worked synthetic presentation",
        environment,
        complex,
    );
    let refusal = situated_composition(&occurrence, &sites, &tables_histidine_neutral(), 0)
        .expect_err("a charged reading is refused at an undeclared acidity");
    assert!(
        matches!(refusal, PhysicochemicalRefusal::AcidityUndeclared { .. }),
        "{refusal}"
    );
    // And the reading is obtained only under an explicit declaration, whose ground travels.
    let reading = composition_under_declared_protonation(
        occurrence.face(),
        &sites,
        &tables_histidine_neutral(),
        &declared_basis(),
        0,
    )
    .expect("the declared assumption admits the reading");
    assert!(
        matches!(reading.protonation, ProtonationBasis::DeclaredAssumption(_)),
        "the declaration travels with the reading"
    );
    assert!(reading.protonation.render().contains("undeclared"));
}

/// **A declared acidity axis gives the basis from the environment, with its pH enclosure.**
#[test]
fn a_declared_acidity_gives_the_basis_from_the_environment() {
    let environment = complete_environment_with(
        "synthetic",
        "free",
        "0",
        &[("SYN", 1)],
        Some((7, "every acid is deprotonated and every base protonated at pH 7")),
    )
    .expect("every axis is stated");
    let basis = protonation_basis(&environment).expect("the axis is declared");
    let ProtonationBasis::FromEnvironment(acidity) = &basis else {
        panic!("the basis comes from the environment");
    };
    assert_eq!(acidity.p_h().lower, integer(7));
    assert_eq!(acidity.p_h().upper, integer(7));
    assert!(acidity.assumption().contains("deprotonated"));
    assert!(acidity.ground().contains("synthetic"));
}

// ---------------------------------------------------------------------------------------------
// 4. The composition, and its laws
// ---------------------------------------------------------------------------------------------

/// **The worked composition, counted exactly.**
#[test]
fn the_worked_composition_counts_every_admitted_class_pair() {
    let complex = worked_complex();
    let sites = worked_sites(&complex);
    let tables = tables_histidine_neutral();
    let reading = composition_under_declared_protonation(
        &complex,
        &sites,
        &tables,
        &declared_basis(),
        0,
    )
    .expect("the composition reads");
    assert_eq!(reading.population, 16, "four binder residues against four");
    assert_eq!(reading.admitted_total, 4, "the four facing pairs");
    assert_eq!(reading.open_total, 0);
    assert_eq!(reading.excluded_total, 12);
    assert_eq!(reading.hydrophobic_pairs(), 1);
    assert_eq!(reading.salt_bridge_candidates(), 1);
    assert_eq!(reading.like_charge_contacts(), 1);
    assert_eq!(reading.aromatic_pairs(), 0);
    assert_eq!(
        reading.count(ClassPair::of(ResidueClass::Polar, ResidueClass::Aromatic)),
        1
    );
    // The ratios are exact rationals and carry the two counts they came from; a ratio with no
    // denominator is absent rather than zero.
    assert_eq!(
        reading.hydrophobic_fraction(),
        Some(Rat::new(BigInt::one(), BigInt::from(4)))
    );
    assert_eq!(reading.charge_complementarity(), Some(Rat::one()));
    assert_eq!(CompositionReading::ratio(3, 0), None);
    // The counts account for the whole population: source accountability, computed.
    let by_pair: u64 = reading.admitted.values().sum();
    assert_eq!(by_pair, reading.admitted_total);
    assert_eq!(
        reading.admitted_total + reading.open_total + reading.excluded_total,
        reading.population
    );
    // The reading carries its unit.
    assert_eq!(*reading.admitted_count().dimension(), count_dimension());
    assert_eq!(reading.admitted_count().enclosure().lower, integer(4));
    // And it carries the declared tables it was taken under.
    assert_eq!(reading.tables, tables.identity());
    assert_eq!(reading.role, FamilyRole::Interface);
}

/// **An `Open` contact makes the composition a family of readings between two bounds.**
///
/// The facing pairs sit at exact distance `3`, so an aperture squared of `9` decides them; the
/// `LEU`/`ILE` pair is moved onto a box whose squared-distance interval straddles that aperture,
/// and the composition then carries it in `open` and on neither bound.
#[test]
fn an_open_contact_makes_the_composition_a_family_between_two_bounds() {
    let binder = worked_binder();
    let target = worked_target();
    let mut left = synthetic_material("binder", &binder, &representative_grain());
    // A box one unit wide on `x`, so the squared distance to `(3,0,0)` encloses `9`.
    left.residues[0].position = CoordinateBox3 {
        x: ExactInterval::new(integer(-1), integer(1)).expect("ordered"),
        y: ExactInterval::point(Rat::zero()),
        z: ExactInterval::point(Rat::zero()),
    };
    let right = synthetic_material("target", &target, &representative_grain());
    let complex = cross_complex("open presentation", left, right, aperture(9));
    let chain_a = synthetic_chain("A", &binder);
    let chain_b = synthetic_chain("B", &target);
    let sites = SiteTable::found(
        "open presentation",
        &complex,
        &[&chain_a, &chain_b],
        &representative_grain(),
    )
    .expect("the site table founds");
    let reading = composition_under_declared_protonation(
        &complex,
        &sites,
        &tables_histidine_neutral(),
        &declared_basis(),
        0,
    )
    .expect("the composition reads");
    assert_eq!(reading.open_total, 1, "the widened pair is undecided");
    assert!(reading.bounds_differ());
    let refusing = reading.refusing_bound();
    let admitting = reading.admitting_bound();
    let key = ClassPair::of(ResidueClass::Hydrophobic, ResidueClass::Hydrophobic);
    assert_eq!(refusing.get(&key).copied().unwrap_or_default(), 0);
    assert_eq!(admitting.get(&key).copied().unwrap_or_default(), 1);
    // Every other class pair is the same on both bounds, so the plurality is exactly the open set.
    for (pair, count) in &refusing {
        if *pair != key {
            assert_eq!(admitting.get(pair), Some(count));
        }
    }
}

/// **The composition is additive over the interface and the fold, which are disjoint populations.**
#[test]
fn the_composition_is_additive_over_the_interface_and_the_fold() {
    let binder = worked_binder();
    let target = worked_target();
    let mut complex = cross_complex(
        "additive presentation",
        synthetic_material("binder", &binder, &representative_grain()),
        synthetic_material("target", &target, &representative_grain()),
        aperture(16),
    );
    // The fold family of the binder at a declared separation of two: `(1,3)`, `(1,4)`, `(2,4)`,
    // whose separations are 12, 18 and 12, so at an aperture squared of 160 exactly two stand.
    let fold_aperture = aperture(160);
    let enacted = enacted_within_component_classes(
        &complex,
        ConstraintComponentId(1),
        2,
        &fold_aperture,
    )
    .expect("the intra-chain classes enact");
    let pairs = complex
        .within_component_pairs(ConstraintComponentId(1), 2)
        .expect("the addressed pairs");
    complex
        .found_within_component_contact_family(
            ConstraintComponentId(1),
            2,
            fold_aperture,
            &enacted,
            &uncertainty_for(&pairs),
        )
        .expect("the fold family founds");
    let chain_a = synthetic_chain("A", &binder);
    let chain_b = synthetic_chain("B", &target);
    let sites = SiteTable::found(
        "additive presentation",
        &complex,
        &[&chain_a, &chain_b],
        &representative_grain(),
    )
    .expect("the site table founds");
    let tables = tables_histidine_neutral();
    let interface = composition_under_declared_protonation(
        &complex,
        &sites,
        &tables,
        &declared_basis(),
        0,
    )
    .expect("the interface composition reads");
    let fold =
        composition_under_declared_protonation(&complex, &sites, &tables, &declared_basis(), 1)
            .expect("the fold composition reads");
    assert_eq!(interface.role, FamilyRole::Interface);
    assert_eq!(
        fold.role,
        FamilyRole::Fold {
            minimum_separation: 2
        }
    );
    assert_eq!(fold.population, 3, "C(4 - 2 + 1, 2) = 3");
    assert_eq!(fold.admitted_total, 2, "two of the three are within 160");
    let total = interface.sum(&fold).expect("the two families add");
    assert_eq!(
        total.admitted_total,
        interface.admitted_total + fold.admitted_total
    );
    assert_eq!(total.population, interface.population + fold.population);
    for pair in total.admitted.keys() {
        assert_eq!(
            total.count(*pair),
            interface.count(*pair) + fold.count(*pair),
            "the class-pair counts add exactly at {}",
            pair.render()
        );
    }
}

/// **Every reading is unchanged by an exact rational rigid motion of the whole configuration.**
///
/// The rotation is the product of two Pythagorean rotations, rational and exactly orthogonal, and
/// the constructor checks `RᵀR = I` over `Q` before the motion can be applied at all.
#[test]
fn the_readings_are_unchanged_by_an_exact_rational_rigid_motion() {
    let binder = worked_binder();
    let target = worked_target();
    let grain = ComponentGrain::Atom;
    let motion = RigidMotion::declared_pythagorean([integer(7), integer(-3), integer(11)])
        .expect("the composed Pythagorean rotation is exactly orthogonal");
    let moved = |material: ComponentMaterial| -> ComponentMaterial {
        ComponentMaterial {
            lineage: format!("{} / moved", material.lineage),
            residues: material
                .residues
                .into_iter()
                .map(|residue| ResidueMaterial {
                    position: motion.act(&residue.position).expect("a point box moves"),
                    ..residue
                })
                .collect(),
        }
    };
    let before = cross_complex_through_intake(
        "before the motion",
        synthetic_material("binder", &binder, &grain),
        synthetic_material("target", &target, &grain),
        aperture(16),
    );
    let after = cross_complex_through_intake(
        "after the motion",
        moved(synthetic_material("binder", &binder, &grain)),
        moved(synthetic_material("target", &target, &grain)),
        aperture(16),
    );
    let chain_a = synthetic_chain("A", &binder);
    let chain_b = synthetic_chain("B", &target);
    let tables = tables_histidine_neutral();
    let window = HydrogenBondWindow::conventional();
    let bound = declared_bound(10_000);
    let mut readings = Vec::new();
    for complex in [&before, &after] {
        let sites = SiteTable::found("motion law", complex, &[&chain_a, &chain_b], &grain)
            .expect("the site table founds");
        let all = sites.sites().keys().copied().collect::<BTreeSet<_>>();
        let population = PairPopulation::AmongSites {
            sites: all,
            minimum_residue_separation: 1,
        };
        let composition = composition_under_declared_protonation(
            complex,
            &sites,
            &tables,
            &declared_basis(),
            0,
        )
        .expect("the composition reads");
        let hydrogen =
            hydrogen_bond_candidates(complex, &sites, &tables, &window, &population, &bound)
                .expect("the candidate reading runs");
        let steric = steric_overlaps(
            complex,
            &sites,
            &tables,
            &Rat::new(BigInt::from(4), BigInt::from(10)),
            &population,
            &bound,
        )
        .expect("the steric reading runs");
        let burial = neighbour_count_proxy(complex, &sites, &integer(8), &population, &bound)
            .expect("the burial proxy runs");
        readings.push((
            composition.admitted.clone(),
            composition.admitted_total,
            hydrogen.candidates.len(),
            steric.clashes.len(),
            burial
                .per_site
                .values()
                .map(|count| count.inside)
                .collect::<Vec<_>>(),
        ));
    }
    assert_eq!(readings[0], readings[1], "a rigid motion moves no reading");
    assert!(readings[0].1 > 0, "the reading is not vacuously equal");
}

/// **A translation acts exactly on an interval coordinate box; a rotation of one is refused.**
///
/// A rotated axis-aligned box is not an axis-aligned box, and re-enclosing it would widen the
/// presentation into a different occurrence. The owner refuses instead.
#[test]
fn a_translation_acts_on_a_box_and_a_rotation_of_a_box_is_refused() {
    let box_with_width = CoordinateBox3 {
        x: ExactInterval::new(integer(-1), integer(1)).expect("ordered"),
        y: ExactInterval::point(Rat::zero()),
        z: ExactInterval::point(Rat::zero()),
    };
    let translation = RigidMotion::rotation_free([integer(5), integer(0), integer(0)]);
    assert!(translation.is_translation());
    let moved = translation.act(&box_with_width).expect("a translation acts");
    assert_eq!(moved.x.lower, integer(4));
    assert_eq!(moved.x.upper, integer(6));
    let rotation = RigidMotion::declared_pythagorean([Rat::zero(), Rat::zero(), Rat::zero()])
        .expect("orthogonal");
    assert!(!rotation.is_translation());
    assert!(matches!(
        rotation
            .act(&box_with_width)
            .expect_err("a rotation of a box refuses"),
        PhysicochemicalRefusal::RotationOfABoxIsNotABox
    ));
    assert!(rotation.act(&point([1, 2, 3])).is_ok(), "a point rotates");
    // And a non-orthogonal declaration never becomes a motion at all.
    let scaled = [
        [integer(2), Rat::zero(), Rat::zero()],
        [Rat::zero(), Rat::one(), Rat::zero()],
        [Rat::zero(), Rat::zero(), Rat::one()],
    ];
    assert!(matches!(
        RigidMotion::declare(scaled, [Rat::zero(), Rat::zero(), Rat::zero()])
            .expect_err("a dilation is not a rigid motion"),
        PhysicochemicalRefusal::RotationNotOrthogonal { .. }
    ));
}

/// **The composition is unchanged by relabelling: presenting the two components in the opposite
/// order gives the same unordered class-pair table under different addresses.**
#[test]
fn the_composition_is_unchanged_by_relabelling_the_components() {
    let binder = worked_binder();
    let target = worked_target();
    let grain = representative_grain();
    let forward = cross_complex(
        "forward",
        synthetic_material("binder", &binder, &grain),
        synthetic_material("target", &target, &grain),
        aperture(16),
    );
    let reverse = cross_complex(
        "reverse",
        synthetic_material("target", &target, &grain),
        synthetic_material("binder", &binder, &grain),
        aperture(16),
    );
    let chain_a = synthetic_chain("A", &binder);
    let chain_b = synthetic_chain("B", &target);
    let tables = tables_histidine_neutral();
    let forward_sites = SiteTable::found("forward", &forward, &[&chain_a, &chain_b], &grain)
        .expect("founds");
    let reverse_sites = SiteTable::found("reverse", &reverse, &[&chain_b, &chain_a], &grain)
        .expect("founds");
    let a = composition_under_declared_protonation(
        &forward,
        &forward_sites,
        &tables,
        &declared_basis(),
        0,
    )
    .expect("reads");
    let b = composition_under_declared_protonation(
        &reverse,
        &reverse_sites,
        &tables,
        &declared_basis(),
        0,
    )
    .expect("reads");
    // The addresses are different — component 1 is the target in the reverse presentation — and
    // the reading is the same.
    assert_ne!(
        forward_sites.site(ConstraintVertexId(1)).expect("a site").residue,
        reverse_sites.site(ConstraintVertexId(1)).expect("a site").residue
    );
    assert_eq!(a.admitted, b.admitted);
    assert_eq!(a.admitted_total, b.admitted_total);
    let comparison = compare_across_tables(&a, &b, None).expect("one table, no passage needed");
    assert!(comparison.agrees());
}

/// **A second parameter table changes the reading, and the comparison refuses without a passage.**
#[test]
fn a_second_table_changes_the_reading_and_the_comparison_refuses() {
    // A histidine on each side, so the two shipped tables disagree about the class pair.
    let binder = vec![residue("HIS", &[("CA", "C", [0, 0, 0])])];
    let target = vec![residue("ASP", &[("CA", "C", [3, 0, 0])])];
    let grain = representative_grain();
    let complex = cross_complex(
        "histidine presentation",
        synthetic_material("binder", &binder, &grain),
        synthetic_material("target", &target, &grain),
        aperture(16),
    );
    let chain_a = synthetic_chain("A", &binder);
    let chain_b = synthetic_chain("B", &target);
    let sites = SiteTable::found("histidine", &complex, &[&chain_a, &chain_b], &grain)
        .expect("founds");
    let neutral = tables_histidine_neutral();
    let protonated = tables_histidine_protonated();
    let a = composition_under_declared_protonation(
        &complex,
        &sites,
        &neutral,
        &declared_basis(),
        0,
    )
    .expect("reads");
    let b = composition_under_declared_protonation(
        &complex,
        &sites,
        &protonated,
        &declared_basis(),
        0,
    )
    .expect("reads");
    assert_eq!(
        a.count(ClassPair::of(
            ResidueClass::Polar,
            ResidueClass::NegativelyCharged
        )),
        1
    );
    assert_eq!(a.salt_bridge_candidates(), 0);
    assert_eq!(b.salt_bridge_candidates(), 1, "the table decides the reading");
    // Without a passage the comparison refuses, naming both sets.
    let refusal = compare_across_tables(&a, &b, None).expect_err("two sets, no passage");
    assert!(
        matches!(refusal, PhysicochemicalRefusal::TablesDiffer { .. }),
        "{refusal}"
    );
    // A passage that does not account for histidine is refused at its own constructor.
    let unaccounted = TablePassage::declare("a ground", &neutral, &protonated, [])
        .expect_err("HIS is unaccounted");
    assert!(
        matches!(
            &unaccounted,
            PhysicochemicalRefusal::ResiduesUnaccounted { unaccounted } if unaccounted == &["HIS".to_owned()]
        ),
        "{unaccounted}"
    );
    // One that accounts for it admits the comparison, and the divergence is returned.
    let passage = TablePassage::declare(
        "the two tables differ only at histidine, and the reading is carried under the declared \
         statement that the imidazole is protonated",
        &neutral,
        &protonated,
        ["HIS".to_owned()],
    )
    .expect("an accounted passage");
    let comparison = compare_across_tables(&a, &b, Some(&passage)).expect("the passage carries it");
    assert!(!comparison.agrees());
    assert_eq!(comparison.divergence.len(), 2, "one class pair leaves and one arrives");
    assert_eq!(comparison.carried_by.as_deref(), Some(passage.ground()));
    // A passage between the wrong two sets is refused by name.
    let wrong = compare_across_tables(&b, &a, Some(&passage)).expect_err("the passage runs one way");
    assert!(
        matches!(wrong, PhysicochemicalRefusal::PassageDoesNotJoinTheseTables { .. }),
        "{wrong}"
    );
}

// ---------------------------------------------------------------------------------------------
// 5. Hydrogen-bond candidates, steric overlaps, burial
// ---------------------------------------------------------------------------------------------

/// A two-residue atom-grain presentation with a declared donor and a declared acceptor at an exact
/// separation of `3`.
fn donor_acceptor_complex(separation: i64) -> (PhysicalConstraintComplex, SiteTable) {
    let left = vec![residue(
        "SER",
        &[("CA", "C", [0, 0, 0]), ("OG", "O", [0, 1, 0])],
    )];
    let right = vec![residue(
        "ASP",
        &[
            ("CA", "C", [separation, 0, 0]),
            ("OD1", "O", [separation, 1, 0]),
        ],
    )];
    let grain = ComponentGrain::Atom;
    let complex = cross_complex(
        "donor-acceptor presentation",
        synthetic_material("left", &left, &grain),
        synthetic_material("right", &right, &grain),
        aperture(64),
    );
    let chain_a = synthetic_chain("A", &left);
    let chain_b = synthetic_chain("B", &right);
    let sites = SiteTable::found("donor-acceptor", &complex, &[&chain_a, &chain_b], &grain)
        .expect("founds");
    (complex, sites)
}

/// **A candidate is a candidate: the donor–acceptor pair is inside the declared window and no bond
/// is claimed, because the model carries no hydrogen.**
#[test]
fn hydrogen_bond_candidates_are_candidates_and_carry_no_hydrogen() {
    let (complex, sites) = donor_acceptor_complex(3);
    let tables = tables_histidine_neutral();
    let window = HydrogenBondWindow::conventional();
    let population = PairPopulation::AmongSites {
        sites: sites.sites().keys().copied().collect(),
        minimum_residue_separation: 1,
    };
    let reading = hydrogen_bond_candidates(
        &complex,
        &sites,
        &tables,
        &window,
        &population,
        &declared_bound(1_000),
    )
    .expect("the reading runs");
    assert_eq!(reading.candidates.len(), 1, "OG against OD1 at exactly 3");
    assert!(reading.undecided.is_empty());
    let candidate = &reading.candidates[0];
    assert_eq!(candidate.donor_atom, "SER:OG");
    assert_eq!(candidate.acceptor_atom, "ASP:OD1");
    assert_eq!(candidate.squared_distance.lower, integer(9));
    assert!(reading.reading_law.contains("not a hydrogen bond"));
    assert!(window.ground().scope().contains("no angular criterion"));
    // Outside the window there is no candidate, and nothing is returned in its place.
    let (far, far_sites) = donor_acceptor_complex(6);
    let far_population = PairPopulation::AmongSites {
        sites: far_sites.sites().keys().copied().collect(),
        minimum_residue_separation: 1,
    };
    let far_reading = hydrogen_bond_candidates(
        &far,
        &far_sites,
        &tables,
        &window,
        &far_population,
        &declared_bound(1_000),
    )
    .expect("the reading runs");
    assert!(far_reading.candidates.is_empty());
    assert!(far_reading.undecided.is_empty());
    assert!(far_reading.pairs_read > 0, "the reading is not vacuous");
}

/// **A pair straddling a window bound is undecided, carried apart and counted on neither side.**
#[test]
fn a_pair_straddling_the_window_is_undecided_and_carried_apart() {
    let left = vec![residue("SER", &[("CA", "C", [0, 0, 0]), ("OG", "O", [0, 1, 0])])];
    let right = vec![residue(
        "ASP",
        &[("CA", "C", [4, 0, 0]), ("OD1", "O", [4, 1, 0])],
    )];
    let grain = ComponentGrain::Atom;
    let mut material = synthetic_material("right", &right, &grain);
    // The `OD1` box straddles the window's upper bound of `7/2`: `x` in `[3, 4]` puts the squared
    // separation from `(0,1,0)` in `[9, 16]`, which encloses `49/4`.
    material.residues[1].position = CoordinateBox3 {
        x: ExactInterval::new(integer(3), integer(4)).expect("ordered"),
        y: ExactInterval::point(Rat::one()),
        z: ExactInterval::point(Rat::zero()),
    };
    let complex = cross_complex(
        "straddling presentation",
        synthetic_material("left", &left, &grain),
        material,
        aperture(64),
    );
    let chain_a = synthetic_chain("A", &left);
    let chain_b = synthetic_chain("B", &right);
    let sites = SiteTable::found("straddling", &complex, &[&chain_a, &chain_b], &grain)
        .expect("founds");
    let population = PairPopulation::AmongSites {
        sites: sites.sites().keys().copied().collect(),
        minimum_residue_separation: 1,
    };
    let reading = hydrogen_bond_candidates(
        &complex,
        &sites,
        &tables_histidine_neutral(),
        &HydrogenBondWindow::conventional(),
        &population,
        &declared_bound(1_000),
    )
    .expect("the reading runs");
    assert!(reading.candidates.is_empty(), "nothing is decided a candidate");
    assert_eq!(reading.undecided.len(), 1, "the straddling pair is carried");
}

/// **A steric overlap is read against the declared radii less the declared tolerance, exactly.**
#[test]
fn a_steric_overlap_is_read_against_the_declared_radii_and_tolerance() {
    // Two carbons at exact separation 2: `1.70 + 1.70 - 0.40 = 3.00`, so they overlap.
    let left = vec![residue("ALA", &[("CA", "C", [0, 0, 0])])];
    let right = vec![residue("ALA", &[("CA", "C", [2, 0, 0])])];
    let grain = ComponentGrain::Atom;
    let complex = cross_complex(
        "overlap presentation",
        synthetic_material("left", &left, &grain),
        synthetic_material("right", &right, &grain),
        aperture(64),
    );
    let chain_a = synthetic_chain("A", &left);
    let chain_b = synthetic_chain("B", &right);
    let sites = SiteTable::found("overlap", &complex, &[&chain_a, &chain_b], &grain)
        .expect("founds");
    let tables = tables_histidine_neutral();
    let population = PairPopulation::AmongSites {
        sites: sites.sites().keys().copied().collect(),
        minimum_residue_separation: 1,
    };
    let tolerance = Rat::new(BigInt::from(4), BigInt::from(10));
    let reading = steric_overlaps(
        &complex,
        &sites,
        &tables,
        &tolerance,
        &population,
        &declared_bound(1_000),
    )
    .expect("the reading runs");
    assert_eq!(reading.clashes.len(), 1);
    assert_eq!(reading.clashes[0].radius_sum, hundredths(340));
    assert_eq!(reading.clashes[0].threshold, integer(3));
    assert!(reading.reading_law.contains("too far"));
    // A larger tolerance decides the same pair the other way, exactly.
    let generous = steric_overlaps(
        &complex,
        &sites,
        &tables,
        &hundredths(150),
        &population,
        &declared_bound(1_000),
    )
    .expect("the reading runs");
    assert!(generous.clashes.is_empty(), "1.70+1.70-1.50 = 1.90 < 2");
    // A negative tolerance and a tolerance above the radius sum are refused by name.
    assert!(matches!(
        steric_overlaps(
            &complex,
            &sites,
            &tables,
            &-Rat::one(),
            &population,
            &declared_bound(1_000)
        )
        .expect_err("a negative tolerance refuses"),
        PhysicochemicalRefusal::ToleranceIsNegative
    ));
    assert!(matches!(
        steric_overlaps(
            &complex,
            &sites,
            &tables,
            &integer(5),
            &population,
            &declared_bound(1_000)
        )
        .expect_err("a tolerance above the radius sum refuses"),
        PhysicochemicalRefusal::ToleranceExceedsRadii { .. }
    ));
}

/// **The burial proxy is an exact integer count and says it is a proxy.**
#[test]
fn the_burial_proxy_is_an_exact_integer_count() {
    let complex = worked_complex();
    let sites = worked_sites(&complex);
    let population = PairPopulation::AmongSites {
        sites: sites.sites().keys().copied().collect(),
        minimum_residue_separation: 0,
    };
    let reading = neighbour_count_proxy(
        &complex,
        &sites,
        &integer(8),
        &population,
        &declared_bound(1_000),
    )
    .expect("the reading runs");
    assert_eq!(reading.per_site.len(), 8, "eight addressed sites");
    // The binder's first residue sits at `(0,0,0)`; within 8 it reaches `(0,6,0)`, `(3,0,0)` and
    // `(3,6,0)` — three neighbours, exactly.
    let first = reading
        .per_site
        .get(&ConstraintVertexId(1))
        .copied()
        .expect("addressed");
    assert_eq!(first.inside, 3);
    assert_eq!(first.undecided, 0);
    assert!(reading.reading_law.contains("not a solvent-accessible"));
    let (least, most) = reading.extremes().expect("a nonempty reading");
    assert!(least.1 <= most.1);
}

/// **Half-sphere exposure splits the neighbours exactly and carries the undecided apart.**
#[test]
fn half_sphere_exposure_splits_the_neighbours_exactly() {
    // One directed residue with `CA` at the origin and `CB` on `+y`; two neighbours, one on each
    // side of the plane `y = 0`, and one exactly in it.
    let left = vec![
        residue("ALA", &[("CA", "C", [0, 0, 0]), ("CB", "C", [0, 1, 0])]),
        residue("ALA", &[("CA", "C", [2, 3, 0]), ("CB", "C", [2, 4, 0])]),
        residue("ALA", &[("CA", "C", [2, -3, 0]), ("CB", "C", [2, -4, 0])]),
        residue("ALA", &[("CA", "C", [3, 0, 0]), ("CB", "C", [3, 1, 0])]),
    ];
    let right = vec![residue("ALA", &[("CA", "C", [40, 0, 0]), ("CB", "C", [40, 1, 0])])];
    let grain = ComponentGrain::Atom;
    let complex = cross_complex(
        "exposure presentation",
        synthetic_material("left", &left, &grain),
        synthetic_material("right", &right, &grain),
        aperture(4),
    );
    let chain_a = synthetic_chain("A", &left);
    let chain_b = synthetic_chain("B", &right);
    let sites = SiteTable::found("exposure", &complex, &[&chain_a, &chain_b], &grain)
        .expect("founds");
    let directions = side_chain_directions(&complex, &sites, "CA", "CB").expect("the directions");
    assert_eq!(directions.directions().len(), 5, "every residue has a CB");
    assert!(directions.undirected.is_empty());
    let origin = ConstraintVertexId(1);
    let population = PairPopulation::SitesAgainstPresentation {
        sites: BTreeSet::from([origin]),
        minimum_residue_separation: 1,
    };
    let reading = half_sphere_exposure(
        &complex,
        &sites,
        &directions,
        &integer(8),
        &population,
        &declared_bound(1_000),
    )
    .expect("the reading runs");
    let count = reading.per_site.get(&origin).copied().expect("addressed");
    // Within 8 of `(0,0,0)` and outside residue 1: `(2,3,0)`, `(2,4,0)`, `(2,-3,0)`, `(2,-4,0)`,
    // `(3,0,0)` and `(3,1,0)`. The direction is `+y`, so the first two are up, the next two down,
    // `(3,0,0)` is exactly in the plane and `(3,1,0)` is up.
    assert_eq!(count.up, 3);
    assert_eq!(count.down, 2);
    assert_eq!(count.undecided_side, 1, "the site exactly in the plane");
    assert_eq!(count.undecided_radius, 0);
    assert!(reading.reading_law.contains("not an area"));
    // A residue with no `CB` carries no direction and is named rather than given one.
    let glycine = vec![residue("GLY", &[("CA", "C", [0, 0, 0])])];
    let glycine_complex = cross_complex(
        "glycine presentation",
        synthetic_material("left", &glycine, &grain),
        synthetic_material("right", &right, &grain),
        aperture(4),
    );
    let glycine_chain = synthetic_chain("A", &glycine);
    let glycine_sites = SiteTable::found(
        "glycine",
        &glycine_complex,
        &[&glycine_chain, &chain_b],
        &grain,
    )
    .expect("founds");
    let glycine_directions =
        side_chain_directions(&glycine_complex, &glycine_sites, "CA", "CB").expect("directions");
    assert_eq!(glycine_directions.undirected.len(), 1);
    assert!(
        glycine_directions
            .direction(ConstraintVertexId(1))
            .is_err(),
        "no direction is imputed"
    );
}

// ---------------------------------------------------------------------------------------------
// 6. The declared finite electrostatic model
// ---------------------------------------------------------------------------------------------

/// **The reciprocal-distance enclosure contains the true value and narrows with the declared
/// grain.**
#[test]
fn the_reciprocal_distance_enclosure_contains_and_narrows() {
    // `r² = 2`, so `1/r = 1/√2`, irrational.
    let squared = ExactInterval::point(integer(2));
    let coarse = reciprocal_distance_enclosure(&squared, 8).expect("an enclosure");
    let fine = reciprocal_distance_enclosure(&squared, 40).expect("an enclosure");
    assert_eq!(*coarse.dimension(), length_dimension().inverted());
    // `1/√2` squared is `1/2`: the enclosure brackets it exactly, checked without any square root.
    for enclosure in [&coarse, &fine] {
        let lower = &enclosure.enclosure().lower;
        let upper = &enclosure.enclosure().upper;
        assert!(lower * lower <= Rat::new(BigInt::one(), BigInt::from(2)));
        assert!(upper * upper >= Rat::new(BigInt::one(), BigInt::from(2)));
    }
    assert!(
        fine.contained_in(&coarse).expect("same dimension"),
        "a finer declared grain narrows the enclosure"
    );
    assert!(fine.width() < coarse.width());
    // A rational root comes back as a tight enclosure containing it.
    let exact = reciprocal_distance_enclosure(&ExactInterval::point(integer(25)), 20)
        .expect("an enclosure");
    assert!(
        exact
            .contains(&Quantity::new(
                Rat::new(BigInt::one(), BigInt::from(5)),
                length_dimension().inverted()
            ))
            .expect("same dimension")
    );
    // A wider coordinate enclosure gives a wider reading, and a zero separation is refused.
    let wide = reciprocal_distance_enclosure(
        &ExactInterval::new(integer(1), integer(9)).expect("ordered"),
        40,
    )
    .expect("an enclosure");
    assert!(wide.width() > fine.width());
    assert!(matches!(
        reciprocal_distance_enclosure(
            &ExactInterval::new(Rat::zero(), integer(9)).expect("ordered"),
            40
        )
        .expect_err("a coincident pair refuses"),
        PhysicochemicalRefusal::CoincidentSites
    ));
    // The declared dyadic grain sizes an integer square root's shift, so it is bounded before the
    // shift is taken: zero and anything above the ceiling are refused by name.
    for declared in [0, OCTAVE_CEILING + 1, u32::MAX] {
        assert!(
            matches!(
                reciprocal_distance_enclosure(&squared, declared)
                    .expect_err("an unbounded grain refuses"),
                PhysicochemicalRefusal::OctavesTooWide { .. }
            ),
            "a declared grain of {declared} must be refused before it sizes anything"
        );
    }
}

/// A charged presentation whose separations are exact integers, so the true Coulomb sum is a
/// rational the enclosure must contain.
fn charged_presentation() -> (PhysicalConstraintComplex, SiteTable) {
    let left = vec![
        residue("ASP", &[("CA", "C", [0, 0, 0])]),
        residue("LYS", &[("CA", "C", [0, 0, 12])]),
    ];
    let right = vec![
        residue("LYS", &[("CA", "C", [3, 4, 0])]),
        residue("ALA", &[("CA", "C", [0, 0, 40])]),
    ];
    let grain = representative_grain();
    let complex = cross_complex(
        "charged presentation",
        synthetic_material("left", &left, &grain),
        synthetic_material("right", &right, &grain),
        aperture(400),
    );
    let chain_a = synthetic_chain("A", &left);
    let chain_b = synthetic_chain("B", &right);
    let sites = SiteTable::found("charged", &complex, &[&chain_a, &chain_b], &grain)
        .expect("founds");
    (complex, sites)
}

/// **The electrostatic enclosure contains the exact rational sum of a worked configuration, and
/// it carries its unit, its dielectric and its approximations.**
#[test]
fn the_electrostatic_enclosure_contains_the_exact_sum() {
    let (complex, sites) = charged_presentation();
    let tables = tables_histidine_neutral();
    let population = PairPopulation::AmongSites {
        sites: sites.sites().keys().copied().collect(),
        minimum_residue_separation: 1,
    };
    let reading = electrostatic_enclosure(
        &complex,
        &sites,
        &tables,
        &declared_basis(),
        &population,
        &declared_bound(1_000),
        40,
    )
    .expect("the reading runs");
    // Three charged pairs contribute: ASP(0,0,0)–LYS(3,4,0) at `r = 5` with `q q = −1`,
    // ASP(0,0,0)–LYS(0,0,12) at `r = 12` with `q q = −1`, and LYS(0,0,12)–LYS(3,4,0) at
    // `r = 13` with `q q = +1`. At `ε = 4` the exact sum is
    // `−1/20 − 1/48 + 1/52 = −161/3120`.
    assert_eq!(reading.contributing_pairs, 3);
    assert_eq!(reading.dielectric, integer(4));
    assert_eq!(*reading.enclosure.dimension(), coulomb_dimension());
    let truth = Quantity::new(
        Rat::new(BigInt::from(-161), BigInt::from(3120)),
        coulomb_dimension(),
    );
    assert!(
        reading
            .enclosure
            .contains(&truth)
            .expect("the same dimension"),
        "the enclosure {} must contain −161/3120",
        reading.enclosure.render()
    );
    assert!(reading.approximations.len() >= 6);
    assert!(
        reading
            .approximations
            .iter()
            .any(|line| line.contains("no solvent"))
    );
    assert!(reading.equation.contains("epsilon"));
    // The chart change into a declared energy unit is returned, never performed silently.
    let cast = declared_coulomb_cast().expect("the named declaration");
    let (lower, upper) = reading.cast_into_energy(&cast).expect("the cast applies");
    assert_eq!(*lower.returned.dimension(), energy_dimension());
    assert_eq!(lower.cast, cast.symbol());
    assert!(!upper.returned.dimension().is_dimensionless());
    assert!(lower.returned.parts().0 <= upper.returned.parts().0);
    // A negative cast is lawful in `quantity` and reverses the endpoints: the pair still returns
    // in the order its name promises.
    let base = physicochemical_base();
    let coulomb = |magnitude: i64| {
        base.dimension_of(&[
            (ENERGY_SYMBOL, Rat::one()),
            (LENGTH_SYMBOL, Rat::one()),
            (CHARGE_SYMBOL, -Rat::from_integer(BigInt::from(2))),
        ])
        .map(|dimension| Quantity::new(Rat::from_integer(BigInt::from(magnitude)), dimension))
        .expect("the declared base carries these generators")
    };
    let reversed = Cast::declare("negative-coulomb", coulomb(-7)).expect("a lawful cast");
    let (low, high) = reading.cast_into_energy(&reversed).expect("the cast applies");
    assert!(low.returned.parts().0 <= high.returned.parts().0);
    // A cast that does not land in the energy dimension is refused by name.
    let length_only = base
        .dimension_of(&[(LENGTH_SYMBOL, Rat::one())])
        .map(|dimension| Quantity::new(Rat::one(), dimension))
        .expect("length");
    let elsewhere = Cast::declare("not-an-energy", length_only).expect("a lawful cast");
    assert!(matches!(
        reading.cast_into_energy(&elsewhere),
        Err(PhysicochemicalRefusal::UnlikeUnits { .. })
    ));
    // A finer declared grain narrows the enclosure and still contains the truth.
    let finer = electrostatic_enclosure(
        &complex,
        &sites,
        &tables,
        &declared_basis(),
        &population,
        &declared_bound(1_000),
        80,
    )
    .expect("the reading runs");
    assert!(
        finer
            .enclosure
            .contained_in(&reading.enclosure)
            .expect("the same dimension")
    );
    assert!(finer.enclosure.contains(&truth).expect("same dimension"));
    assert!(finer.enclosure.width() < reading.enclosure.width());
}

/// **The electrostatic enclosure is additive over a partition of its pair population.**
///
/// This is the exact balance the receiver owes: the parts recombine to the whole, entry for entry,
/// because interval addition over a fixed set of terms is associative and commutative.
#[test]
fn the_electrostatic_enclosure_is_additive_over_a_partition() {
    let (complex, sites) = charged_presentation();
    let tables = tables_histidine_neutral();
    let every: Vec<ConstraintVertexId> = sites.sites().keys().copied().collect();
    let whole = PairPopulation::AmongSites {
        sites: every.iter().copied().collect(),
        minimum_residue_separation: 1,
    };
    let bound = declared_bound(1_000);
    let total = electrostatic_enclosure(
        &complex, &sites, &tables, &declared_basis(), &whole, &bound, 40,
    )
    .expect("the whole reading");
    // Partition the pairs by splitting the site set: pairs inside the left half, inside the right
    // half, and across. The three sums must recombine to the whole exactly.
    let left_half: BTreeSet<_> = every[..2].iter().copied().collect();
    let right_half: BTreeSet<_> = every[2..].iter().copied().collect();
    let mut parts = Vec::new();
    for sites_of_part in [left_half.clone(), right_half.clone()] {
        parts.push(
            electrostatic_enclosure(
                &complex,
                &sites,
                &tables,
                &declared_basis(),
                &PairPopulation::AmongSites {
                    sites: sites_of_part,
                    minimum_residue_separation: 1,
                },
                &bound,
                40,
            )
            .expect("a part reads")
            .enclosure,
        );
    }
    // The cross part: each left site against the presentation, minus the within-left pairs.
    let cross = electrostatic_enclosure(
        &complex,
        &sites,
        &tables,
        &declared_basis(),
        &PairPopulation::SitesAgainstPresentation {
            sites: left_half,
            minimum_residue_separation: 1,
        },
        &bound,
        40,
    )
    .expect("the cross part reads")
    .enclosure;
    // `SitesAgainstPresentation` over the left half covers the within-left pairs and the cross
    // pairs, so whole = (cross part) + (within right).
    let recombined = cross.sum(&parts[1]).expect("like units add");
    assert_eq!(
        recombined.enclosure(),
        total.enclosure.enclosure(),
        "the parts recombine to the whole exactly"
    );
}

// ---------------------------------------------------------------------------------------------
// 7. Hostile input and declared-size discipline
// ---------------------------------------------------------------------------------------------

/// **A declared pair population above its declared ceiling is refused before anything is sized.**
#[test]
fn a_pair_population_above_its_ceiling_is_refused_before_anything_is_sized() {
    let complex = worked_complex();
    let sites = worked_sites(&complex);
    let population = PairPopulation::AmongSites {
        sites: sites.sites().keys().copied().collect(),
        minimum_residue_separation: 0,
    };
    let tight = PairWorkBound::declare(
        3,
        "declared by this test: a ceiling below the population's own extent",
    )
    .expect("a stated bound");
    let refusal = neighbour_count_proxy(&complex, &sites, &integer(8), &population, &tight)
        .expect_err("the population is above the ceiling");
    let PhysicochemicalRefusal::PairPopulationTooWide { pairs, ceiling, .. } = &refusal else {
        panic!("the refusal names the counts: {refusal}");
    };
    assert_eq!(*pairs, 28, "C(8,2)");
    assert_eq!(*ceiling, 3);
    // A bound with no ceiling and one with no ground are refused at the constructor.
    assert!(matches!(
        PairWorkBound::declare(0, "a ground").expect_err("a zero ceiling refuses"),
        PhysicochemicalRefusal::WorkBoundNotStated
    ));
    assert!(matches!(
        PairWorkBound::declare(10, "  ").expect_err("an unstated ground refuses"),
        PhysicochemicalRefusal::WorkBoundNotStated
    ));
}

/// **A site table that disagrees with its complex is refused rather than read onto it.**
#[test]
fn a_site_table_that_disagrees_with_its_complex_is_refused() {
    let complex = worked_complex();
    let binder = worked_binder();
    let target = worked_target();
    let chain_a = synthetic_chain("A", &binder);
    let chain_b = synthetic_chain("B", &target);
    // One chain too few.
    let refusal = SiteTable::found("short", &complex, &[&chain_a], &representative_grain())
        .expect_err("the component populations disagree");
    assert!(
        matches!(refusal, PhysicochemicalRefusal::ComponentPopulationDisagrees { .. }),
        "{refusal}"
    );
    // The right number of chains with the wrong chemistry.
    let wrong = synthetic_chain(
        "B",
        &[
            residue("TRP", &[("CA", "C", [3, 0, 0])]),
            residue("TRP", &[("CA", "C", [3, 6, 0])]),
            residue("TRP", &[("CA", "C", [3, 12, 0])]),
            residue("TRP", &[("CA", "C", [3, 18, 0])]),
        ],
    );
    let refusal = SiteTable::found(
        "mismatched",
        &complex,
        &[&chain_a, &wrong],
        &representative_grain(),
    )
    .expect_err("the founded monomer disagrees");
    assert!(
        matches!(refusal, PhysicochemicalRefusal::SiteChemistryDisagrees { .. }),
        "{refusal}"
    );
    // A chain with the right names but the wrong extent.
    let short = synthetic_chain("B", &target[..3]);
    let refusal = SiteTable::found(
        "short chain",
        &complex,
        &[&chain_a, &short],
        &representative_grain(),
    )
    .expect_err("the site populations disagree");
    assert!(
        matches!(refusal, PhysicochemicalRefusal::SitePopulationDisagrees { .. }),
        "{refusal}"
    );
    assert!(chain_b.residues.len() == 4);
}

/// **A reading addressed to a founding that does not exist is refused by name.**
#[test]
fn a_reading_of_an_absent_founding_is_refused() {
    let complex = worked_complex();
    let sites = worked_sites(&complex);
    let refusal = composition_under_declared_protonation(
        &complex,
        &sites,
        &tables_histidine_neutral(),
        &declared_basis(),
        7,
    )
    .expect_err("there is no seventh founding");
    assert!(
        matches!(refusal, PhysicochemicalRefusal::NoSuchFounding { founding: 7 }),
        "{refusal}"
    );
}

// ---------------------------------------------------------------------------------------------
// 8. The M5 exhibition
// ---------------------------------------------------------------------------------------------

/// The declared RBX1 window this receiver measures at atom grain. It is the same five-residue
/// window `receiver_atlas`'s R7 measurement and `causal_chord` use, so the readings are comparable.
const M5_WINDOW: usize = 5;

fn m5_note() -> String {
    "The synthetic laws above run without it: the unit algebra, the table refusals, the pH gate, \
     the open family, additivity, the rigid-motion law, the cross-table refusal and the \
     electrostatic enclosure are all checked on exact synthetic material."
        .to_owned()
}

/// Read the three M5 presentations as `(chain pair, all-atom presentation)` at a declared grain.
fn m5_atom_grain(
) -> Vec<(&'static str, PhysicalConstraintComplex, SiteTable, Vec<ConstraintVertexId>)> {
    use crate::physical_intake::mmcif::StructurePresentation;
    let root = structure_root();
    let names = [
        ("designed", "designed-free-rbx1.cif"),
        ("free", "ptxv2-free-rbx1-seed2.cif"),
        ("cul1-bound", "ptxv2-cul1-rbx1-seed0.cif"),
    ];
    let grain = ComponentGrain::Atom;
    let mut out = Vec::new();
    for (label, file) in names {
        let presentation =
            StructurePresentation::read(&root.join(file)).expect("the release reads");
        let binder = presentation
            .chain_with_residue_count(96)
            .expect("the 96-residue binder")
            .clone();
        let target = presentation
            .chain_with_residue_count(108)
            .expect("the 108-residue RBX1 chain")
            .clone();
        let left = crate::physical_intake::component_material(
            &binder,
            &presentation.source_lineage,
            &grain,
            RESIDENT_DECIMAL_PLACES,
        )
        .expect("the binder material");
        let right = crate::physical_intake::component_material(
            &target,
            &presentation.source_lineage,
            &grain,
            RESIDENT_DECIMAL_PLACES,
        )
        .expect("the target material");
        let complex = found_constraint_complex(
            &format!("{label} / all-atom binder x RBX1"),
            EventId(1),
            vec![left, right],
            Vec::new(),
        )
        .expect("the complex founds");
        let sites = SiteTable::found(
            format!("{label} / all-atom"),
            &complex,
            &[&binder, &target],
            &grain,
        )
        .expect("the site table founds and agrees with the complex");
        // The window: every atom of the first `M5_WINDOW` residues of the RBX1 chain.
        let window = sites
            .sites()
            .values()
            .filter(|site| {
                site.component == ConstraintComponentId(2)
                    && site.residue_ordinal as usize <= M5_WINDOW
            })
            .map(|site| site.vertex)
            .collect::<Vec<_>>();
        out.push((label, complex, sites, window));
    }
    out
}

/// **On the M5 release every charged reading refuses, because no release records a pH.**
///
/// [established-bounded; measured] This is the receiver's primary result on the mounted data and
/// it is not a defect: the three occurrences leave the acidity axis undeclared with a stated
/// reason, and a residue-class table that files aspartate negatively is a protonation claim.
#[test]
fn the_m5_release_refuses_every_charged_reading_because_no_release_records_a_ph() {
    let root = structure_root();
    assert!(
        root.is_dir(),
        "{}",
        absent_structure_root_message(&root, &m5_note())
    );
    let occurrences = m5_occurrences();
    for occurrence in &occurrences {
        let refusal = protonation_basis(occurrence.environment())
            .expect_err("no M5 release records a pH");
        let PhysicochemicalRefusal::AcidityUndeclared { axis, why, .. } = &refusal else {
            panic!("the refusal names the axis: {refusal}");
        };
        assert_eq!(*axis, CoordinateName::Acidity);
        assert!(
            why.contains("no pH and no protonation assumption is recorded"),
            "the environment's own stated reason travels into the refusal: {why}"
        );
    }
}

/// **The M5 interface composition, measured, and what separates the three presentations.**
#[test]
fn the_m5_interface_composition_separates_the_three_presentations() {
    let root = structure_root();
    assert!(
        root.is_dir(),
        "{}",
        absent_structure_root_message(&root, &m5_note())
    );
    let occurrences = m5_occurrences();
    let tables = tables_histidine_neutral();
    let basis = declared_protonation(
        ExteriorDeclaration::declare(
            "the release records no pH, so the reading is taken under the declared assumption that \
             aspartate and glutamate are deprotonated, lysine and arginine protonated and \
             histidine neutral",
            "declared by this measurement, not by the release",
        )
        .expect("a stated declaration"),
    );
    let aperture = eight_angstrom_aperture();
    let mut measured = Vec::new();
    for occurrence in &occurrences {
        // The occurrence's complex carries no founded family, so the interface family is founded
        // here at the declared aperture through the library path.
        let mut complex = rebuild_ca_complex(occurrence, &aperture);
        let sites = ca_sites(occurrence, &mut complex);
        let reading = composition_under_declared_protonation(
            &complex,
            &sites,
            &tables,
            &basis,
            0,
        )
        .expect("the composition reads");
        measured.push(reading);
    }
    let [designed, free, bound] = [&measured[0], &measured[1], &measured[2]];
    // The formed-contact totals reproduce `design_selection`'s recorded 64 / 59 / 45 exactly.
    assert_eq!(
        (
            designed.admitted_total,
            free.admitted_total,
            bound.admitted_total
        ),
        (64, 59, 45)
    );
    assert_eq!((designed.open_total, free.open_total, bound.open_total), (1, 0, 0));
    assert_eq!(designed.population, 10_368);
    // The class composition separates all three.
    assert_eq!(
        (
            designed.hydrophobic_pairs(),
            free.hydrophobic_pairs(),
            bound.hydrophobic_pairs()
        ),
        (7, 6, 3)
    );
    assert_eq!(
        (
            designed.salt_bridge_candidates(),
            free.salt_bridge_candidates(),
            bound.salt_bridge_candidates()
        ),
        (3, 3, 3)
    );
    assert_eq!(
        (
            designed.like_charge_contacts(),
            free.like_charge_contacts(),
            bound.like_charge_contacts()
        ),
        (1, 1, 1)
    );
    assert_eq!(
        (
            designed.polar_pairs(),
            free.polar_pairs(),
            bound.polar_pairs()
        ),
        (0, 0, 2)
    );
    assert_eq!(
        (
            designed.aromatic_pairs(),
            free.aromatic_pairs(),
            bound.aromatic_pairs()
        ),
        (0, 0, 0)
    );
    // Exact rational ratios, never a scalar standing for the interface.
    assert_eq!(
        designed.hydrophobic_fraction(),
        Some(Rat::new(BigInt::from(7), BigInt::from(64)))
    );
    assert_eq!(
        bound.hydrophobic_fraction(),
        Some(Rat::new(BigInt::from(3), BigInt::from(45)))
    );
    assert_eq!(
        designed.charge_complementarity(),
        Some(Rat::from_integer(BigInt::from(3)))
    );
    // The designed presentation carries the only undecided reading, and the composition is a
    // family there: its two bounds differ.
    assert!(designed.bounds_differ());
    assert!(!free.bounds_differ() && !bound.bounds_differ());
    for reading in &measured {
        println!(
            "B7 physicochemical | M5 interface | {} | admitted {} open {} | {:?}",
            reading.lineage,
            reading.admitted_total,
            reading.open_total,
            reading
                .admitted
                .iter()
                .map(|(pair, count)| (pair.render(), *count))
                .collect::<Vec<_>>()
        );
    }
}

/// Rebuild one M5 occurrence's alpha-carbon complex with the interface family founded.
fn rebuild_ca_complex(
    occurrence: &Occurrence,
    aperture: &DistanceAperture,
) -> PhysicalConstraintComplex {
    let face = occurrence.face();
    let left = ComponentMaterial {
        lineage: format!("{} / binder", face.presentation_lineage),
        residues: face
            .component(ConstraintComponentId(1))
            .expect("the binder")
            .vertices
            .iter()
            .map(|vertex| {
                let presented = &face.vertices[vertex];
                ResidueMaterial {
                    source_ordinal: presented.source_ordinal,
                    monomer: presented.monomer.clone(),
                    position: presented.position.clone(),
                }
            })
            .collect(),
    };
    let right = ComponentMaterial {
        lineage: format!("{} / RBX1", face.presentation_lineage),
        residues: face
            .component(ConstraintComponentId(2))
            .expect("the target")
            .vertices
            .iter()
            .map(|vertex| {
                let presented = &face.vertices[vertex];
                ResidueMaterial {
                    source_ordinal: presented.source_ordinal,
                    monomer: presented.monomer.clone(),
                    position: presented.position.clone(),
                }
            })
            .collect(),
    };
    let left_extent = left.residues.len();
    let right_extent = right.residues.len();
    found_constraint_complex(
        &face.presentation_lineage,
        EventId(1),
        vec![left, right],
        vec![PresentedFamily {
            left: ConstraintComponentId(1),
            right: ConstraintComponentId(2),
            aperture: aperture.clone(),
            uncertainty: uncertainty_grid(left_extent, right_extent),
        }],
    )
    .expect("the interface family founds")
}

/// The site table of a rebuilt alpha-carbon complex, read from the presented chains.
fn ca_sites(occurrence: &Occurrence, complex: &mut PhysicalConstraintComplex) -> SiteTable {
    use crate::physical_intake::mmcif::StructurePresentation;
    let root = structure_root();
    let file = match occurrence.id.0 {
        1 => "designed-free-rbx1.cif",
        2 => "ptxv2-free-rbx1-seed2.cif",
        _ => "ptxv2-cul1-rbx1-seed0.cif",
    };
    let presentation = StructurePresentation::read(&root.join(file)).expect("the release reads");
    let binder = presentation
        .chain_with_residue_count(96)
        .expect("the binder")
        .clone();
    let target = presentation
        .chain_with_residue_count(108)
        .expect("RBX1")
        .clone();
    SiteTable::found(
        format!("{file} / alpha-carbon"),
        complex,
        &[&binder, &target],
        &ComponentGrain::Representative {
            atom_label: REPRESENTATIVE.to_owned(),
        },
    )
    .expect("the site table founds and agrees with the complex")
}

/// **The M5 atom-grain window readings, and the predictor defect this receiver does and does not
/// surface.**
///
/// [established-bounded; measured] The declared window is the same five N-terminal RBX1 residues
/// R3, R4, R5 and R1 are measured on, where the two predictions carry the *same seven* alpha-carbon
/// contacts. The combinatorial half of this receiver is blind there for exactly that reason — the
/// composition is a function of the contact set and the residue names, and both are identical —
/// and the **atom-grain burial proxy separates them**, because it reads heavy-atom geometry rather
/// than the alpha-carbon contact set.
#[test]
fn the_m5_atom_grain_window_separates_what_the_contact_set_cannot() {
    let root = structure_root();
    assert!(
        root.is_dir(),
        "{}",
        absent_structure_root_message(&root, &m5_note())
    );
    let tables = tables_histidine_neutral();
    let window_table = HydrogenBondWindow::conventional();
    let bound = PairWorkBound::declare(
        4_000_000,
        "the declared window's site set against the whole all-atom presentation; the extent is \
         checked against this ceiling before any pair is enumerated",
    )
    .expect("a stated bound");
    let mut measured = Vec::new();
    for (label, complex, sites, window) in m5_atom_grain() {
        let among = PairPopulation::AmongSites {
            sites: window.iter().copied().collect(),
            minimum_residue_separation: 1,
        };
        let against = PairPopulation::SitesAgainstPresentation {
            sites: window.iter().copied().collect(),
            minimum_residue_separation: 1,
        };
        let hydrogen = hydrogen_bond_candidates(
            &complex,
            &sites,
            &tables,
            &window_table,
            &among,
            &bound,
        )
        .expect("the candidate reading runs");
        let steric = steric_overlaps(
            &complex,
            &sites,
            &tables,
            &hundredths(40),
            &PairPopulation::AmongSites {
                sites: window.iter().copied().collect(),
                minimum_residue_separation: 2,
            },
            &bound,
        )
        .expect("the steric reading runs");
        let burial =
            neighbour_count_proxy(&complex, &sites, &integer(8), &against, &bound)
                .expect("the burial proxy runs");
        let per_residue = residue_burial(&sites, &burial);
        println!(
            "B7 physicochemical | M5 window {M5_WINDOW} | {label} | hbond candidates {} | \
             clashes {} | burial {:?}",
            hydrogen.candidates.len(),
            steric.clashes.len(),
            per_residue
        );
        measured.push((
            label,
            hydrogen.candidates.len(),
            steric.clashes.len(),
            per_residue,
        ));
    }
    let candidates = (measured[0].1, measured[1].1, measured[2].1);
    let clashes = (measured[0].2, measured[1].2, measured[2].2);
    assert_eq!(candidates, (2, 3, 3), "the candidate count separates the designed structure from both predictions and not the two predictions");
    assert_eq!(clashes, (1, 0, 0), "the designed window carries one overlap");
    // The burial proxy separates all three, including the two predictions.
    assert_ne!(measured[0].3, measured[1].3);
    assert_ne!(measured[1].3, measured[2].3, "the burial proxy separates the two predictions where the alpha-carbon contact set does not");
    assert_eq!(measured[1].3, vec![59, 88, 110, 132, 175]);
    assert_eq!(measured[2].3, vec![66, 90, 117, 137, 179]);
    assert_eq!(measured[0].3, vec![493, 254, 152, 229, 379]);
}

/// The summed decided neighbour count per residue of a window reading, in residue order.
fn residue_burial(sites: &SiteTable, reading: &BurialProxyReading) -> Vec<u64> {
    let mut by_residue: BTreeMap<u32, u64> = BTreeMap::new();
    for (vertex, count) in &reading.per_site {
        let site = sites.site(*vertex).expect("an addressed site");
        *by_residue.entry(site.residue_ordinal).or_default() += count.inside;
    }
    by_residue.into_values().collect()
}

/// **What this receiver does and does not surface of the wave-1 predictor defect.**
///
/// [established-bounded; measured] Wave 1 found that the Protenix predictions carry a stray
/// terminal oxygen, one of them `27.6` angstroms from its own alpha carbon. Two readings are taken
/// here and they answer differently.
///
/// The **burial proxy at a declared two-angstrom radius surfaces three of the four** in-scope
/// cases: a carbonyl oxygen bonded to its own carbonyl carbon carries exactly one neighbour there,
/// and three of the four chain-terminal carbonyl oxygens of the two predictions carry **none** —
/// no atom at all within two angstroms, which for a heavy-atom model is no bonded partner. Both of
/// the designed structure's terminal carbonyl oxygens carry one.
///
/// The **steric overlap reading is blind to the defect as a defect**. Of the three unbonded
/// oxygens it reports exactly one, and it reports it as an *overlap* with whatever the stray atom
/// landed beside — not as a broken bond. The other two are invisible to it: the CUL1-bound
/// prediction's two unbonded terminal oxygens appear in no overlap at all. A reading of atoms that
/// are too close cannot see an atom that is too far, and where it does see one it misattributes it.
///
/// [definition] The fourth case is not surfaced by either reading, and the receiver says so rather
/// than claiming the detection: the free prediction's RBX1 terminal oxygen sits `21.8` angstroms
/// from its own alpha carbon and still lands within two angstroms of another atom. **The reading
/// that surfaces every one of them is the intra-residue covalent radius**, which `grain_tower`'s
/// measured grain radius already owns and already reported as item B0's inflation witness. This
/// receiver does not duplicate it.
#[test]
fn the_burial_proxy_surfaces_three_of_four_stray_terminal_oxygens() {
    let root = structure_root();
    assert!(
        root.is_dir(),
        "{}",
        absent_structure_root_message(&root, &m5_note())
    );
    let tables = tables_histidine_neutral();
    let work = PairWorkBound::declare(
        4_000_000,
        "the C-terminal residues' atoms against the whole all-atom presentation",
    )
    .expect("a stated bound");
    let mut measured = Vec::new();
    for (label, complex, sites, _) in m5_atom_grain() {
        // The last residue of each presented component.
        let mut last: BTreeMap<ConstraintComponentId, u32> = BTreeMap::new();
        for site in sites.sites().values() {
            let entry = last.entry(site.component).or_default();
            *entry = (*entry).max(site.residue_ordinal);
        }
        let terminal = sites
            .sites()
            .values()
            .filter(|site| last.get(&site.component) == Some(&site.residue_ordinal))
            .map(|site| site.vertex)
            .collect::<BTreeSet<_>>();
        // Two angstroms: a heavy atom bonded to another carries at least one neighbour there, and
        // the same-residue atoms are in scope because the declared separation is zero.
        let bonded = neighbour_count_proxy(
            &complex,
            &sites,
            &integer(2),
            &PairPopulation::SitesAgainstPresentation {
                sites: terminal.clone(),
                minimum_residue_separation: 0,
            },
            &work,
        )
        .expect("the burial proxy runs");
        let steric = steric_overlaps(
            &complex,
            &sites,
            &tables,
            &hundredths(40),
            &PairPopulation::SitesAgainstPresentation {
                sites: terminal.clone(),
                minimum_residue_separation: 2,
            },
            &work,
        )
        .expect("the steric reading runs");
        let mut carbonyl_oxygens = Vec::new();
        let mut unbonded_sites = BTreeSet::new();
        for (vertex, count) in &bonded.per_site {
            let site = sites.site(*vertex).expect("addressed");
            if site.atom.as_deref() == Some("O") {
                carbonyl_oxygens.push((
                    format!("{}:{}:O", site.residue, site.residue_ordinal),
                    count.inside,
                ));
                if count.inside == 0 {
                    unbonded_sites.insert(*vertex);
                }
            }
        }
        carbonyl_oxygens.sort();
        // Clashes mentioning one of the *unbonded* terminal oxygens — the stray ones.
        let stray_clashes = steric
            .clashes
            .iter()
            .filter(|clash| {
                unbonded_sites.contains(&clash.left) || unbonded_sites.contains(&clash.right)
            })
            .count();
        println!(
            "B7 physicochemical | M5 C-terminal | {label} | terminal carbonyl oxygens with their \
             two-angstrom neighbour counts {carbonyl_oxygens:?} | overlaps mentioning an unbonded \
             one {stray_clashes} of {} clashes read",
            steric.clashes.len()
        );
        measured.push((label, carbonyl_oxygens, stray_clashes));
    }
    // The designed structure's two terminal carbonyl oxygens are both bonded; the free
    // prediction's binder terminus is not and its RBX1 terminus is; the CUL1-bound prediction's
    // two are both unbonded.
    let counts = |at: usize| -> Vec<(String, u64)> { measured[at].1.clone() };
    assert_eq!(
        counts(0),
        vec![("GLU:96:O".to_owned(), 1), ("HIS:108:O".to_owned(), 1)]
    );
    assert_eq!(
        counts(1),
        vec![("GLU:96:O".to_owned(), 0), ("HIS:108:O".to_owned(), 1)]
    );
    assert_eq!(
        counts(2),
        vec![("GLU:96:O".to_owned(), 0), ("HIS:108:O".to_owned(), 0)]
    );
    let unbonded: usize = measured[1..]
        .iter()
        .map(|(_, oxygens, _)| oxygens.iter().filter(|(_, count)| *count == 0).count())
        .sum();
    assert_eq!(
        unbonded, 3,
        "three of the two predictions' four chain-terminal carbonyl oxygens carry no atom within \
         two angstroms; the fourth is not surfaced by this reading and the receiver says so"
    );
    // The clash reading sees exactly one of the three, and sees it as an overlap rather than as a
    // broken bond. The other two appear in no overlap at all.
    assert_eq!(
        (measured[0].2, measured[1].2, measured[2].2),
        (0, 1, 0),
        "the steric reading surfaces one of the three unbonded terminal oxygens, and \
         misattributes it: it is reported as an overlap with whatever the stray atom landed beside"
    );
}

/// **The M5 electrostatic enclosure, under an explicitly declared protonation.**
#[test]
fn the_m5_electrostatic_enclosure_under_a_declared_protonation() {
    let root = structure_root();
    assert!(
        root.is_dir(),
        "{}",
        absent_structure_root_message(&root, &m5_note())
    );
    let occurrences = m5_occurrences();
    let tables = tables_histidine_neutral();
    let basis = declared_protonation(
        ExteriorDeclaration::declare(
            "the release records no pH; the reading is taken under the declared assumption that \
             aspartate and glutamate are deprotonated, lysine and arginine protonated and \
             histidine neutral",
            "declared by this measurement, not by the release",
        )
        .expect("a stated declaration"),
    );
    let aperture = eight_angstrom_aperture();
    let bound = PairWorkBound::declare(
        200_000,
        "the binder's alpha carbons against the whole alpha-carbon presentation; the extent is \
         checked before any pair is enumerated",
    )
    .expect("a stated bound");
    let mut readings = Vec::new();
    for occurrence in &occurrences {
        let mut complex = rebuild_ca_complex(occurrence, &aperture);
        let sites = ca_sites(occurrence, &mut complex);
        let binder = sites
            .of_component(ConstraintComponentId(1))
            .into_iter()
            .collect::<BTreeSet<_>>();
        let population = PairPopulation::SitesAgainstPresentation {
            sites: binder,
            minimum_residue_separation: 1,
        };
        let reading = electrostatic_enclosure(
            &complex, &sites, &tables, &basis, &population, &bound, 24,
        )
        .expect("the enclosure reads");
        println!(
            "B7 physicochemical | M5 electrostatic | {} | pairs {} contributing {} | {}",
            reading.lineage,
            reading.pairs_read,
            reading.contributing_pairs,
            reading.enclosure.render()
        );
        readings.push(reading);
    }
    // Every reading carries its unit, its dielectric, its declared protonation and its
    // approximations; none is a bare number.
    for reading in &readings {
        assert_eq!(*reading.enclosure.dimension(), coulomb_dimension());
        assert_eq!(reading.dielectric, integer(4));
        assert!(matches!(
            reading.protonation,
            ProtonationBasis::DeclaredAssumption(_)
        ));
        assert!(reading.contributing_pairs > 0);
        assert!(reading.enclosure.width().is_positive());
    }
    // The three enclosures are disjoint pairwise, so the receiver separates all three exactly.
    for (at, left) in readings.iter().enumerate() {
        for right in &readings[at + 1..] {
            let a = left.enclosure.enclosure();
            let b = right.enclosure.enclosure();
            assert!(
                a.upper < b.lower || b.upper < a.lower,
                "the enclosures {} and {} overlap, so the separation is not exact",
                left.enclosure.render(),
                right.enclosure.render()
            );
        }
    }
}
