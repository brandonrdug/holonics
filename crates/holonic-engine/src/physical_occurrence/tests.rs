//! The laws of the typed environment index and of contact status, and the measured M5 exhibition.
//!
//! The synthetic tests state what the Lean owner
//! `formal/elementary-holonics/ElementaryHolonics/Foundation/PhysicalOccurrence.lean` proves, and
//! they run everywhere with no fixture and no environment variable. The fixture tests reproduce the
//! authenticated release and **fail** when it is absent: a test that cannot run says so by failing,
//! because cargo discards the output of a passing test.

use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;

use num_bigint::BigInt;
use relational_geometry::Rat;

use super::*;
use crate::EventId;
use crate::continuing_tower::check_restriction_laws;
use crate::exact_value::ExactInterval;
use crate::physical_intake::mmcif::{ChainOccurrence, StructurePresentation};
use crate::physical_intake::numpy::UncertaintyWordFormat;
use crate::physical_intake::{
    AddressedOccurrence, AddressedUncertainty, ComponentGrain, ContactPresentation, DesignLineage,
    TargetEcology, TokenAddress, component_material, found_constraint_complex,
};

// ---------------------------------------------------------------------------------------------
// Fixture addresses, following the pattern `physical_intake/tests.rs` established.
// ---------------------------------------------------------------------------------------------

const STRUCTURE_ROOT_ENV: &str = "HOLONICS_M5_STRUCTURE_ROOT";
const DEFAULT_STRUCTURE_ROOT: &str = "/home/b/Downloads/holonics-m5-rbx1-rank05";
const BOLTZ_ROOT_ENV: &str = "HOLONICS_BOLTZ_PREDICTION_ROOT";
const DEFAULT_BOLTZ_ROOT: &str = ".local/boltz-smoke/out/boltz_results_test/predictions/test";

/// The resident decimal grain the M5 family is carried on.
const RESIDENT_DECIMAL_PLACES: u32 = 7;
/// The alpha-carbon representative the M5 deed selects.
const REPRESENTATIVE: &str = "CA";

fn structure_root() -> PathBuf {
    std::env::var_os(STRUCTURE_ROOT_ENV)
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(DEFAULT_STRUCTURE_ROOT))
}

fn boltz_root() -> PathBuf {
    std::env::var_os(BOLTZ_ROOT_ENV)
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("../..")
                .join(DEFAULT_BOLTZ_ROOT)
        })
}

/// The declared contact receiver: exact distance not greater than 8 angstroms.
fn eight_angstrom_aperture() -> DistanceAperture {
    DistanceAperture {
        lineage: "declared contact receiver: exact distance not greater than 8 angstroms"
            .to_owned(),
        squared: Rat::from_integer(BigInt::from(64)),
    }
}

// ---------------------------------------------------------------------------------------------
// Synthetic environments
// ---------------------------------------------------------------------------------------------

fn synthetic_presented(seed: &str, form: &str) -> PresentedEnvironmentIndex {
    PresentedEnvironmentIndex::declared(
        "declared by the test for a synthetic run that emits no environment arrays",
        TargetEcology {
            target: "SYN".to_owned(),
            target_form: form.to_owned(),
            stoichiometry: "1to1".to_owned(),
            cofolding_model: "synthetic".to_owned(),
        },
        DesignLineage {
            design_uuid: "synthetic-uuid".to_owned(),
            design_name: "synthetic".to_owned(),
            seed: seed.to_owned(),
        },
        vec![TokenAddress {
            chain: "A".to_owned(),
            residue: 1,
            entity: None,
        }],
    )
    .expect("a declaration with a stated ground is admitted")
}

/// Every axis declared, so the environment sits at the complete aperture.
fn complete_environment(
    lineage: &str,
    conformation: &str,
    seed: &str,
) -> Result<Environment, EnvironmentRefusal> {
    Environment::found(
        lineage,
        synthetic_presented(seed, conformation),
        [
            (
                CoordinateName::Species,
                Coordinate::declared(
                    CoordinateValue::Species(SpeciesHomolog {
                        species: "Homo sapiens".to_owned(),
                        homolog: "SYN-1".to_owned(),
                    }),
                    "the synthetic fixture declares its own species",
                )?,
            ),
            (
                CoordinateName::Conformation,
                Coordinate::declared(
                    CoordinateValue::Conformation(conformation.to_owned()),
                    "declared by the synthetic fixture",
                )?,
            ),
            (
                CoordinateName::OligomericState,
                Coordinate::declared(
                    CoordinateValue::OligomericState(OligomericState {
                        copies: BTreeMap::from([("SYN-1".to_owned(), 1_u32)]),
                    }),
                    "one copy, declared",
                )?,
            ),
            (
                CoordinateName::Acidity,
                Coordinate::declared(
                    CoordinateValue::Acidity(Acidity {
                        p_h: ExactInterval::new(
                            Rat::new(BigInt::from(74), BigInt::from(10)),
                            Rat::new(BigInt::from(74), BigInt::from(10)),
                        )
                        .expect("an ordered pH enclosure"),
                        protonation_assumption: "standard residue pKa, histidine neutral"
                            .to_owned(),
                    }),
                    "declared by the synthetic fixture",
                )?,
            ),
            (
                CoordinateName::Solvation,
                Coordinate::declared(
                    CoordinateValue::Solvation(Solvation::Soluble {
                        buffer: "declared buffer".to_owned(),
                    }),
                    "declared by the synthetic fixture",
                )?,
            ),
            (
                CoordinateName::Cofactors,
                Coordinate::declared(
                    CoordinateValue::Cofactors(LigandComplement {
                        copies: BTreeMap::new(),
                    }),
                    "the synthetic presentation carries no heteroatom component",
                )?,
            ),
            (
                CoordinateName::Assay,
                Coordinate::declared(
                    CoordinateValue::Assay(AssayFormat::InSilicoPrediction {
                        predictor: "synthetic".to_owned(),
                        seed: seed.to_owned(),
                    }),
                    "declared by the synthetic fixture",
                )?,
            ),
            (
                CoordinateName::Partners,
                Coordinate::declared(
                    CoordinateValue::Partners(PartnerPanel {
                        intended: BTreeSet::from(["SYN-1".to_owned()]),
                        unintended: BTreeSet::new(),
                    }),
                    "declared by the synthetic fixture",
                )?,
            ),
        ],
    )
}

// ---------------------------------------------------------------------------------------------
// B3: the coordinate, declared with a ground or explicitly undeclared
// ---------------------------------------------------------------------------------------------

#[test]
fn a_coordinate_is_declared_with_a_ground_or_explicitly_undeclared_and_never_defaulted() {
    let value = CoordinateValue::Conformation("free".to_owned());
    assert!(matches!(
        Coordinate::declared(value.clone(), "   "),
        Err(EnvironmentRefusal::GroundNotStated {
            name: CoordinateName::Conformation
        })
    ));
    assert!(matches!(
        Coordinate::undeclared(""),
        Err(EnvironmentRefusal::UndeclarationNotStated)
    ));
    let declared = Coordinate::declared(value, "the wire declared it").expect("a stated ground");
    assert!(declared.is_declared());
    assert_eq!(declared.name(), Some(CoordinateName::Conformation));
    let undeclared =
        Coordinate::undeclared("the predictor emits no pH").expect("a stated reason");
    assert!(!undeclared.is_declared());
    assert_eq!(undeclared.name(), None);
    assert_eq!(undeclared.value(), None);
}

#[test]
fn agreement_requires_a_declaration_on_both_sides() {
    let value = CoordinateValue::Conformation("free".to_owned());
    let left = Coordinate::declared(value.clone(), "left ground").expect("stated");
    let right = Coordinate::declared(value, "right ground").expect("stated");
    let other =
        Coordinate::declared(CoordinateValue::Conformation("bound".to_owned()), "g").expect("g");
    let absent_left = Coordinate::undeclared("nobody said").expect("stated");
    let absent_right = Coordinate::undeclared("nobody said").expect("stated");

    // Lean: `Coordinate.agrees_iff`. Equal declared values agree whatever their grounds.
    assert!(left.agrees(&right));
    assert!(!left.agrees(&other));
    // Lean: `Coordinate.agreement_is_declared_on_both_sides` and `undeclared_never_agrees`.
    assert!(!left.agrees(&absent_right));
    assert!(!absent_left.agrees(&right));
    assert!(
        !absent_left.agrees(&absent_right),
        "two undeclared coordinates do not agree: neither states anything, so nothing licenses \
         the claim that they name the same condition"
    );
}

#[test]
fn an_environment_cannot_be_founded_with_an_unstated_axis() {
    let presented = synthetic_presented("0", "free");
    let one = (
        CoordinateName::Conformation,
        Coordinate::declared(
            CoordinateValue::Conformation("free".to_owned()),
            "declared",
        )
        .expect("stated"),
    );
    match Environment::found("partial", presented.clone(), [one.clone()]) {
        Err(EnvironmentRefusal::CoordinatesAbsent { absent }) => {
            assert_eq!(absent.len(), 7, "seven axes are unstated: {absent:?}");
            assert!(absent.contains(&CoordinateName::Acidity));
            assert!(absent.contains(&CoordinateName::Partners));
            assert!(!absent.contains(&CoordinateName::Conformation));
        }
        other => panic!("an incomplete environment must refuse: {other:?}"),
    }
    // A value filed under the wrong axis is refused by name rather than silently re-filed.
    let misfiled = Environment::found(
        "misfiled",
        presented.clone(),
        [(
            CoordinateName::Acidity,
            Coordinate::declared(
                CoordinateValue::Conformation("free".to_owned()),
                "declared",
            )
            .expect("stated"),
        )],
    );
    assert!(matches!(
        misfiled,
        Err(EnvironmentRefusal::CoordinateMisfiled {
            filed_under: CoordinateName::Acidity,
            belongs_to: CoordinateName::Conformation
        })
    ));
    // The same axis twice is refused rather than last-writer-wins.
    let repeated = Environment::found("repeated", presented, [one.clone(), one]);
    assert!(matches!(
        repeated,
        Err(EnvironmentRefusal::CoordinateRepeated {
            name: CoordinateName::Conformation
        })
    ));
}

#[test]
fn an_environment_disagrees_with_itself_exactly_at_its_undeclared_axes() {
    let complete = complete_environment("complete", "free", "0").expect("a complete environment");
    assert!(
        complete.disagreement(&complete).is_empty(),
        "a fully declared environment agrees with itself at every axis"
    );

    let mut coordinates = complete
        .coordinates()
        .iter()
        .map(|(name, coordinate)| (*name, coordinate.clone()))
        .collect::<Vec<_>>();
    for entry in &mut coordinates {
        if entry.0 == CoordinateName::Acidity || entry.0 == CoordinateName::Solvation {
            entry.1 =
                Coordinate::undeclared("the predictor emits no such context").expect("stated");
        }
    }
    let partial = Environment::found(
        "two axes undeclared",
        complete.presented().clone(),
        coordinates,
    )
    .expect("every axis is still present, two of them as explicit undeclarations");

    // Lean: `disagreement_self_is_exactly_the_undeclared`.
    assert_eq!(
        partial.disagreement(&partial).names(),
        partial.undeclared_names(),
        "an undeclared axis does not agree even with itself"
    );
    assert_eq!(
        partial.undeclared_names(),
        BTreeSet::from([CoordinateName::Acidity, CoordinateName::Solvation])
    );
    assert_eq!(partial.declared_names().len(), 6);
}

// ---------------------------------------------------------------------------------------------
// B3: the vertical index as a tower, and its residual
// ---------------------------------------------------------------------------------------------

#[test]
fn the_environment_tower_satisfies_the_restriction_laws_over_a_declared_aperture() {
    let tower = EnvironmentTower {
        lineage: "the vertical environment index of the M5 carrier".to_owned(),
    };
    let complete = complete_environment("complete", "free", "0").expect("complete");
    let fine = EnvironmentAperture::complete();
    let middle = EnvironmentAperture::of([
        CoordinateName::Species,
        CoordinateName::Conformation,
        CoordinateName::OligomericState,
        CoordinateName::Assay,
    ]);
    let coarse = EnvironmentAperture::of([CoordinateName::Species]);
    assert!(tower.refines(&coarse, &middle));
    assert!(tower.refines(&middle, &fine));
    assert!(!tower.refines(&fine, &coarse));
    assert!(tower.carries(&fine, &complete));

    let restricted = tower
        .restrict(&middle, &fine, &complete)
        .expect("the restriction is lawful");
    assert!(
        tower.carries(&middle, &restricted),
        "the restricted face sits at the coarser chart"
    );
    assert_eq!(restricted.declared_names(), middle.0);

    let receipt = check_restriction_laws(
        &tower,
        &[coarse.clone(), middle.clone(), fine.clone()],
        &[
            (fine.clone(), complete.clone()),
            (middle.clone(), restricted.clone()),
        ],
    )
    .expect("restrict_refl and restrict_trans hold on this aperture");
    assert_eq!(receipt.reflexive_charts.len(), 2);
    assert!(
        receipt
            .transitive_triples
            .contains(&(coarse.clone(), middle.clone(), fine.clone())),
        "the three-chart triple was actually checked: {:?}",
        receipt.transitive_triples
    );
    assert_eq!(receipt.faces_checked, 2);

    // A face offered at a chart it does not sit at is a typed refusal, never a silent repair.
    assert!(matches!(
        tower.restrict(&coarse, &middle, &complete),
        Err(TowerRefusal::FaceNotCarried { .. })
    ));
    // And so is a restriction taken the wrong way along the refinement order.
    let coarse_face = tower
        .restrict(&coarse, &fine, &complete)
        .expect("the restriction to the coarsest chart is lawful");
    assert!(tower.carries(&coarse, &coarse_face));
    assert!(matches!(
        tower.restrict(&fine, &coarse, &coarse_face),
        Err(TowerRefusal::NotARefinement { .. })
    ));
}

#[test]
fn restriction_along_the_vertical_index_reopens_its_source_exactly() {
    let complete = complete_environment("complete", "free", "0").expect("complete");
    let restriction = EnvironmentRestriction {
        coarse: EnvironmentAperture::of([CoordinateName::Species, CoordinateName::Conformation]),
        lineage: "forget everything but species and conformation".to_owned(),
    };
    let dropped = restriction.residual(&complete);
    assert_eq!(dropped.len(), 6, "six declared axes are dropped");
    assert!(dropped.contains_key(&CoordinateName::Acidity));
    assert!(!dropped.contains_key(&CoordinateName::Species));
    assert!(
        dropped
            .values()
            .all(super::Coordinate::is_declared),
        "the residual carries the dropped values with their grounds, not placeholders"
    );

    // Lean/`ContinuingTower`: `Transition.reopen_apply`. Equality, not a bound.
    let receipt = restriction
        .check_reopen(&complete)
        .expect("the residual is exactly the dropped part");
    assert_eq!(receipt.sources_reopened, 1);

    // Two environments that differ only outside the coarse aperture become one face, and the two
    // residuals are what still separates them. They share the presented intake index, because the
    // vertical aperture is over the *typed* coordinates: forgetting one of them never forgets the
    // exterior testimony the intake recorded.
    let other = {
        let mut coordinates = complete
            .coordinates()
            .iter()
            .map(|(name, coordinate)| (*name, coordinate.clone()))
            .collect::<Vec<_>>();
        for entry in &mut coordinates {
            if entry.0 == CoordinateName::Assay {
                entry.1 = Coordinate::declared(
                    CoordinateValue::Assay(AssayFormat::InSilicoPrediction {
                        predictor: "synthetic".to_owned(),
                        seed: "1".to_owned(),
                    }),
                    "declared by the synthetic fixture",
                )
                .expect("a stated ground");
            }
        }
        Environment::found("complete", complete.presented().clone(), coordinates)
            .expect("complete")
    };
    assert_ne!(complete, other, "the two differ in their assay seed");
    assert_eq!(
        complete.disagreement(&other).names(),
        BTreeSet::from([CoordinateName::Assay])
    );
    assert_eq!(
        restriction.apply(&complete),
        restriction.apply(&other),
        "the restriction merges them"
    );
    let separating = restriction
        .separating_residuals(&complete, &other)
        .expect("the merge is witnessed");
    assert_ne!(
        separating.0, separating.1,
        "the retained residuals still tell the two sources apart"
    );
}

// ---------------------------------------------------------------------------------------------
// B3: the passage, and the refusal to transport without one
// ---------------------------------------------------------------------------------------------

#[test]
fn a_passage_must_account_for_every_divergent_coordinate() {
    let from = complete_environment("free", "free", "0").expect("complete");
    let to = complete_environment("bound", "bound", "1").expect("complete");
    let divergent = from.disagreement(&to).names();
    assert_eq!(
        divergent,
        BTreeSet::from([CoordinateName::Conformation, CoordinateName::Assay]),
        "the two environments differ in conformation and assay seed"
    );

    match EnvironmentPassage::declare(
        "a passage that says nothing about the conformation",
        from.clone(),
        to.clone(),
        [CoordinateName::Assay],
    ) {
        Err(EnvironmentRefusal::CoordinatesUnaccounted { unaccounted }) => {
            assert_eq!(unaccounted, vec![CoordinateName::Conformation]);
        }
        other => panic!("an unaccounted coordinate must refuse: {other:?}"),
    }
    assert!(matches!(
        EnvironmentPassage::declare("  ", from.clone(), to.clone(), divergent.clone()),
        Err(EnvironmentRefusal::PassageGroundNotStated)
    ));

    let passage = EnvironmentPassage::declare(
        "the two predictions were run on the same target file and differ only in the declared \
         conformation and the sampling seed; a contact claim is carried across both, and both are \
         named here",
        from,
        to,
        divergent.clone(),
    )
    .expect("a passage that accounts for every divergent axis is admitted");
    for name in &divergent {
        assert!(passage.accounts_for(*name));
    }
    assert!(!passage.accounts_for(CoordinateName::Species));
}

#[test]
fn transport_drops_the_environment_and_the_residual_is_exactly_it() {
    let from = complete_environment("free", "free", "0").expect("complete");
    let to = complete_environment("bound", "bound", "1").expect("complete");
    let passage = EnvironmentPassage::declare(
        "declared for the test",
        from.clone(),
        to.clone(),
        from.disagreement(&to).names(),
    )
    .expect("admitted");

    let read_here = SituatedReading {
        environment: from.clone(),
        pair: (3, 7),
        class: ContactClass::Inside,
    };
    let carried = passage.apply(&read_here);
    assert_eq!(carried.environment, to, "the claim now sits at the target");
    assert_eq!(carried.class, ContactClass::Inside);
    // The residual *is* the environment the claim was read at.
    assert_eq!(passage.residual(&read_here), from);
    let receipt = passage
        .check_reopen(&read_here)
        .expect("reopen(apply(x), residual(x)) = x");
    assert_eq!(receipt.sources_reopened, 1);

    // Two claims read at two different environments become one transported claim, and their
    // residuals are exactly what still separates them.
    let elsewhere = complete_environment("third", "third", "2").expect("complete");
    let read_elsewhere = SituatedReading {
        environment: elsewhere.clone(),
        pair: (3, 7),
        class: ContactClass::Inside,
    };
    assert_eq!(passage.apply(&read_here), passage.apply(&read_elsewhere));
    let (left, right) = passage
        .separating_residuals(&read_here, &read_elsewhere)
        .expect("the transport merged them");
    assert_eq!(left, from);
    assert_eq!(right, elsewhere);
    assert_ne!(left, right);
}

// ---------------------------------------------------------------------------------------------
// B4: the static exact law, and the three states it cannot reach
// ---------------------------------------------------------------------------------------------

fn interval(lower: i64, upper: i64) -> ExactInterval {
    ExactInterval::new(
        Rat::from_integer(BigInt::from(lower)),
        Rat::from_integer(BigInt::from(upper)),
    )
    .expect("an ordered interval")
}

#[test]
fn the_static_exact_law_reaches_exactly_three_states() {
    let aperture = Rat::from_integer(BigInt::from(64));
    let mut labels = BTreeSet::new();
    for (class, distance) in [
        (ContactClass::Inside, interval(1, 4)),
        (ContactClass::Outside, interval(100, 121)),
        (ContactClass::Open, interval(49, 81)),
    ] {
        let status = static_status(class, &aperture, &distance);
        assert!(
            status.is_static(),
            "the static law reaches only static states: {status:?}"
        );
        assert!(
            !matches!(
                status,
                ContactStatus::KineticallyInaccessible(_)
                    | ContactStatus::EnvironmentDependent(_)
                    | ContactStatus::Competing(_)
            ),
            "no static structure produces {}",
            status.label()
        );
        labels.insert(status.label());
    }
    // Lean: `static_law_reaches_exactly_three`. The image is exactly three, and all three are
    // attained by the exact interval law.
    assert_eq!(
        labels,
        BTreeSet::from(["formed", "excluded", "open"]),
        "the image of the static exact law"
    );

    // `Open` is derived from the exact interval law and carries what would be needed to decide it.
    match static_status(ContactClass::Open, &aperture, &interval(49, 81)) {
        ContactStatus::Open {
            aperture_squared,
            squared_distance,
        } => {
            assert_eq!(aperture_squared, aperture);
            assert!(squared_distance.lower <= aperture && aperture < squared_distance.upper);
        }
        other => panic!("an open reading must stay open: {other:?}"),
    }
}

#[test]
fn kinetic_inaccessibility_is_admitted_only_from_an_exterior_declaration() {
    assert!(matches!(
        ExteriorDeclaration::declare("", "stopped-flow kinetics"),
        Err(StatusRefusal::ExteriorDeclarationNotStated)
    ));
    assert!(matches!(
        ExteriorDeclaration::declare("the loop does not open on the association timescale", "  "),
        Err(StatusRefusal::ExteriorDeclarationNotStated)
    ));
    let declaration = ExteriorDeclaration::declare(
        "the buried loop does not open on the association timescale, so this contact cannot form \
         however close the static coordinates put the two residues",
        "stopped-flow kinetics, exterior to this repository",
    )
    .expect("a declaration with a statement and an apparatus");
    let status = ContactStatus::kinetically_inaccessible(declaration);
    assert_eq!(status.label(), "kinetically-inaccessible");
    assert!(
        !status.is_static(),
        "kinetic inaccessibility is not a geometric fact"
    );
    match &status {
        ContactStatus::KineticallyInaccessible(ground) => {
            assert!(!ground.statement().is_empty());
            assert!(!ground.apparatus().is_empty());
        }
        other => panic!("{other:?}"),
    }
}

#[test]
fn competition_is_exactly_a_declared_valence_being_exceeded_by_formed_contenders() {
    let site = ConstraintVertexId(7);
    let edge = |other: u64| ConstraintEdge::new(site, ConstraintVertexId(other)).expect("distinct").0;
    let aperture = Rat::from_integer(BigInt::from(64));
    let declaration = ValenceDeclaration::declare(
        site,
        2,
        "the zinc site of RBX1 is declared four-coordinate; two of its positions are taken by the \
         structural cysteines, leaving a declared valence of two for the contacts in question",
    )
    .expect("a valence with a stated ground");
    assert!(matches!(
        ValenceDeclaration::declare(site, 2, "   "),
        Err(StatusRefusal::ValenceGroundNotStated { .. })
    ));

    // Two formed contenders sit within the declared valence: no competition is derived.
    let within = BTreeMap::from([
        (edge(1), ContactStatus::Formed),
        (edge(2), ContactStatus::Formed),
        (edge(3), ContactStatus::Excluded),
        (
            ConstraintEdge::new(ConstraintVertexId(11), ConstraintVertexId(12))
                .expect("distinct")
                .0,
            ContactStatus::Formed,
        ),
    ]);
    let occupancy = site_occupancy(&declaration, &within);
    assert_eq!(occupancy.formed.len(), 2, "the far edge is not at this site");
    assert!(occupancy.competition.is_none());

    // An open contender neither creates nor dissolves a competition, and is retained apart.
    let with_open = BTreeMap::from([
        (edge(1), ContactStatus::Formed),
        (edge(2), ContactStatus::Formed),
        (
            edge(3),
            ContactStatus::Open {
                aperture_squared: aperture.clone(),
                squared_distance: interval(49, 81),
            },
        ),
    ]);
    let occupancy = site_occupancy(&declaration, &with_open);
    assert_eq!(occupancy.formed.len(), 2);
    assert_eq!(occupancy.open, vec![edge(3)]);
    assert!(
        occupancy.competition.is_none(),
        "an undecided reading is never counted as a contender"
    );

    // Three formed contenders exceed the declared valence of two: every one of them competes.
    let exceeding = BTreeMap::from([
        (edge(1), ContactStatus::Formed),
        (edge(2), ContactStatus::Formed),
        (edge(3), ContactStatus::Formed),
    ]);
    let occupancy = site_occupancy(&declaration, &exceeding);
    let competition = occupancy
        .competition
        .as_ref()
        .expect("three formed contenders exceed a valence of two");
    assert_eq!(competition.declared_valence, 2);
    assert_eq!(competition.contenders.len(), 3);
    assert!(
        competition.ground.contains("four-coordinate"),
        "the valence's ground is carried into the verdict"
    );
    assert!(!ContactStatus::Competing(competition.clone()).is_static());
}

#[test]
fn directional_uncertainty_is_never_symmetrized() {
    let asymmetric = DirectionalUncertainty {
        receiver: "synthetic".to_owned(),
        source_lineage: "synthetic".to_owned(),
        forward: interval(3, 3),
        forward_ulp: Rat::new(BigInt::from(1), BigInt::from(1024)),
        reverse: interval(11, 11),
        reverse_ulp: Rat::new(BigInt::from(1), BigInt::from(1024)),
    };
    assert!(asymmetric.is_asymmetric());
    // Lean: `retention_does_not_factor_through_symmetrization`. Transposing is an involution and
    // is not the identity on an asymmetric reading.
    assert_ne!(asymmetric.transposed(), asymmetric);
    assert_eq!(asymmetric.transposed().transposed(), asymmetric);
    assert_eq!(asymmetric.transposed().forward, asymmetric.reverse);
    assert_eq!(asymmetric.transposed().reverse, asymmetric.forward);

    let symmetric = DirectionalUncertainty {
        reverse: asymmetric.forward.clone(),
        reverse_ulp: asymmetric.forward_ulp.clone(),
        ..asymmetric.clone()
    };
    assert!(!symmetric.is_asymmetric());
    assert_eq!(symmetric.transposed(), symmetric);
}

// ---------------------------------------------------------------------------------------------
// B3/B4: the vertical and horizontal families, and the across-environment status
// ---------------------------------------------------------------------------------------------

fn synthetic_family(
    occurrence: u64,
    environment: &Environment,
    classes: &[ContactClass],
) -> SituatedFamily {
    SituatedFamily {
        schema: "holonic-engine.situated-contact-family.v1".to_owned(),
        occurrence: OccurrenceId(occurrence),
        lineage: format!("synthetic family {occurrence}"),
        environment: environment.clone(),
        left: ConstraintComponentId(1),
        right: ConstraintComponentId(2),
        left_sequence: vec!["ALA".to_owned()],
        right_sequence: vec!["GLY".to_owned(), "SER".to_owned(), "THR".to_owned()],
        aperture: eight_angstrom_aperture(),
        readings: classes
            .iter()
            .enumerate()
            .map(|(at, class)| SituatedPairReading {
                pair: (1, at as u32 + 1),
                class: *class,
                squared_distance: interval(1, 4),
                uncertainty: None,
            })
            .collect(),
    }
}

#[test]
fn the_vertical_and_horizontal_families_are_kept_apart_by_type() {
    let first = complete_environment("first", "free", "0").expect("complete");
    let second = complete_environment("second", "bound", "1").expect("complete");
    let a = synthetic_family(
        1,
        &first,
        &[ContactClass::Inside, ContactClass::Outside, ContactClass::Open],
    );
    let b = synthetic_family(
        2,
        &second,
        &[ContactClass::Inside, ContactClass::Inside, ContactClass::Open],
    );

    // Vertical: one object, several environments.
    let vertical = VerticalFamily::over_one_object(vec![a.clone(), b.clone()])
        .expect("two environments over one object");
    assert_eq!(vertical.members().len(), 2);
    assert!(matches!(
        VerticalFamily::over_one_object(vec![a.clone(), a.clone()]),
        Err(StatusRefusal::EnvironmentRepeatedAlongTheVerticalIndex { .. })
    ));
    let mut different_object = b.clone();
    different_object.right_sequence = vec!["GLY".to_owned()];
    assert!(matches!(
        VerticalFamily::over_one_object(vec![a.clone(), different_object]),
        Err(StatusRefusal::ObjectDiffersAlongTheVerticalIndex { .. })
    ));
    assert!(matches!(
        VerticalFamily::over_one_object(Vec::new()),
        Err(StatusRefusal::EmptyFamily)
    ));

    // Horizontal: one environment, several objects. It refuses the vertical family's population.
    let mut sibling = a.clone();
    sibling.occurrence = OccurrenceId(3);
    sibling.right_sequence = vec!["GLY".to_owned()];
    sibling.readings.truncate(1);
    let horizontal = HorizontalFamily::at_one_environment(vec![a.clone(), sibling])
        .expect("two objects at one environment");
    assert_eq!(horizontal.members().len(), 2);
    assert!(matches!(
        HorizontalFamily::at_one_environment(vec![a, b]),
        Err(StatusRefusal::Environment(
            EnvironmentRefusal::EnvironmentsDiffer { .. }
        ))
    ));
}

#[test]
fn the_across_environment_status_lifts_agreement_and_separates_disagreement() {
    let first = complete_environment("first", "free", "0").expect("complete");
    let second = complete_environment("second", "bound", "1").expect("complete");
    let third = complete_environment("third", "third", "2").expect("complete");
    let vertical = VerticalFamily::over_one_object(vec![
        synthetic_family(
            1,
            &first,
            &[ContactClass::Inside, ContactClass::Outside, ContactClass::Open],
        ),
        synthetic_family(
            2,
            &second,
            &[ContactClass::Inside, ContactClass::Inside, ContactClass::Open],
        ),
        synthetic_family(
            3,
            &third,
            &[ContactClass::Inside, ContactClass::Outside, ContactClass::Open],
        ),
    ])
    .expect("three environments over one object");

    let status = vertical.status_across().expect("the status of every pair");
    assert_eq!(status.len(), 3);
    // Lean: `acrossEnvironments_constant`. A family that agrees everywhere is the static status.
    assert_eq!(status[&(1, 1)], ContactStatus::Formed);
    assert!(matches!(status[&(1, 3)], ContactStatus::Open { .. }));
    // Lean: `acrossEnvironments_dependent_of_two_classes`.
    match &status[&(1, 2)] {
        ContactStatus::EnvironmentDependent(dependence) => {
            assert_eq!(dependence.pair, (1, 2));
            assert_eq!(dependence.formed_at.len(), 1);
            assert_eq!(dependence.excluded_at.len(), 2);
            assert!(dependence.open_at.is_empty());
            assert_eq!(dependence.formed_at[0].occurrence, OccurrenceId(2));
        }
        other => panic!("a pair read two ways is environment-dependent: {other:?}"),
    }
    assert_eq!(
        vertical
            .environment_dependent_pairs()
            .expect("the dependent pairs"),
        vec![(1, 2)]
    );
}

#[test]
fn a_comparison_without_a_passage_is_a_typed_refusal_naming_the_coordinates() {
    let first = complete_environment("free", "free", "0").expect("complete");
    let second = complete_environment("bound", "bound", "1").expect("complete");
    let a = synthetic_family(
        1,
        &first,
        &[ContactClass::Inside, ContactClass::Outside, ContactClass::Open],
    );
    let b = synthetic_family(
        2,
        &second,
        &[ContactClass::Inside, ContactClass::Inside, ContactClass::Open],
    );

    // Lean: `compareReadings_refuses_naming_the_coordinates`.
    match compare_here(&a, &b) {
        Err(EnvironmentRefusal::EnvironmentsDiffer { disagreement }) => {
            assert_eq!(
                disagreement.names(),
                BTreeSet::from([CoordinateName::Conformation, CoordinateName::Assay])
            );
            let rendered = EnvironmentRefusal::EnvironmentsDiffer {
                disagreement: disagreement.clone(),
            }
            .to_string();
            assert!(rendered.contains("target conformation"), "{rendered}");
            assert!(rendered.contains("assay format"), "{rendered}");
        }
        other => panic!("two claims at two environments must refuse: {other:?}"),
    }

    // At one environment the comparison is lawful with no passage at all.
    let sibling = synthetic_family(
        3,
        &first,
        &[ContactClass::Inside, ContactClass::Open, ContactClass::Open],
    );
    let here = compare_here(&a, &sibling).expect("one environment, no passage needed");
    assert_eq!(here.pairs, 3);
    assert_eq!(here.agreeing, 2);
    assert_eq!(here.separating.len(), 1);
    assert_eq!(here.separating[0].pair, (1, 2));

    // Across environments a supplied passage makes the same comparison lawful, and the environment
    // the left claim was read at comes back in the return rather than being dropped.
    let passage = EnvironmentPassage::declare(
        "declared for the test: the two runs differ in conformation and seed, and a contact claim \
         is carried across both",
        first.clone(),
        second.clone(),
        first.disagreement(&second).names(),
    )
    .expect("admitted");
    let carried = compare_through(&a, &b, &passage).expect("a supplied passage admits it");
    assert_eq!(carried.read_at, first);
    assert_eq!(carried.carried_to, second);
    assert_eq!(
        carried.accounted,
        vec![CoordinateName::Conformation, CoordinateName::Assay]
    );
    assert_eq!(carried.comparison.pairs, 3);
    assert_eq!(carried.comparison.separating.len(), 1);
    assert_eq!(carried.comparison.separating[0].pair, (1, 2));

    // A passage that does not leave this claim's environment is refused by name.
    let wrong = EnvironmentPassage::declare(
        "declared for the test",
        second.clone(),
        first.clone(),
        first.disagreement(&second).names(),
    )
    .expect("admitted");
    assert!(matches!(
        compare_through(&a, &b, &wrong),
        Err(EnvironmentRefusal::PassageDoesNotLeaveThisEnvironment { .. })
    ));
}

// ---------------------------------------------------------------------------------------------
// Hostile input: a remounted environment that lost an axis
// ---------------------------------------------------------------------------------------------

/// **The remount law.** `Environment` derives `Deserialize` through
/// `#[serde(try_from = "EnvironmentWire")]`, so the wire is routed through `Environment::found`
/// and a remount that lost an axis is refused **at the boundary**. Before this repair the derive
/// reconstructed the private `coordinates` map directly, which is exactly the constructor bypass
/// the module header forbids and which `ContactStatus` / `ExteriorDeclaration` avoid by not
/// deriving `Deserialize` at all; the value that came back could not have been founded here.
#[test]
fn an_environment_remounted_without_an_axis_is_refused_at_the_boundary() {
    let complete = complete_environment("complete", "free", "0").expect("complete");
    let mut wire: serde_json::Value =
        serde_json::to_value(&complete).expect("the environment serializes");
    wire["coordinates"]
        .as_object_mut()
        .expect("the coordinates are an object")
        .remove("Acidity")
        .expect("the axis was there");
    let refusal = serde_json::from_value::<Environment>(wire)
        .expect_err("a wire missing an axis is not an environment");
    assert!(
        refusal.to_string().contains("Acidity"),
        "the refusal names the lost axis: {refusal}"
    );

    // The complete wire still round-trips exactly, so the repair closed the bypass without
    // closing the door: consumers that remount an environment keep doing so.
    let round: Environment = serde_json::from_value(
        serde_json::to_value(&complete).expect("the environment serializes"),
    )
    .expect("a complete wire is a complete environment");
    assert_eq!(round, complete);
    assert!(round.coordinate(CoordinateName::Acidity).is_ok());
    assert!(complete.disagreement(&round).is_empty() || !complete.undeclared_names().is_empty());
}

/// Every hostile wire the review named, refused by the constructor the wire is routed through.
#[test]
fn hostile_wires_are_refused_by_the_constructors_they_are_routed_through() {
    let complete = complete_environment("complete", "free", "0").expect("complete");

    // (1) a misfiled value: a Species value filed under the Conformation axis.
    let mut misfiled: serde_json::Value =
        serde_json::to_value(&complete).expect("serializes");
    let species = misfiled["coordinates"]["Species"].clone();
    misfiled["coordinates"]["Conformation"] = species;
    let refusal = serde_json::from_value::<Environment>(misfiled)
        .expect_err("a misfiled value is not an environment");
    assert!(
        refusal.to_string().contains("filed under"),
        "the refusal names the misfiling: {refusal}"
    );

    // (2) an empty ground: a declaration with nothing licensing it.
    let mut empty_ground: serde_json::Value =
        serde_json::to_value(&complete).expect("serializes");
    empty_ground["coordinates"]["Species"]["Declared"]["ground"] =
        serde_json::Value::String(String::from("   "));
    let refusal = serde_json::from_value::<Environment>(empty_ground)
        .expect_err("an unstated ground is a default wearing a name");
    assert!(
        refusal.to_string().contains("no stated ground"),
        "the refusal names the missing ground: {refusal}"
    );

    // (3) an empty undeclaration reason.
    let mut coordinates = complete
        .coordinates()
        .iter()
        .map(|(name, coordinate)| (*name, coordinate.clone()))
        .collect::<Vec<_>>();
    for entry in &mut coordinates {
        if entry.0 == CoordinateName::Solvation {
            entry.1 = Coordinate::undeclared("the predictor emits no such context")
                .expect("a stated reason");
        }
    }
    let sparse = Environment::found("sparse", complete.presented().clone(), coordinates)
        .expect("every axis is present, one as an explicit undeclaration");
    let mut empty_why: serde_json::Value = serde_json::to_value(&sparse).expect("serializes");
    empty_why["coordinates"]["Solvation"]["Undeclared"]["why"] =
        serde_json::Value::String(String::new());
    let refusal = serde_json::from_value::<Environment>(empty_why)
        .expect_err("an unstated reason is a default wearing a name");
    assert!(
        refusal.to_string().contains("stated reason"),
        "the refusal names the missing reason: {refusal}"
    );

    // (4) a schema this owner does not found.
    let mut foreign: serde_json::Value = serde_json::to_value(&complete).expect("serializes");
    foreign["schema"] = serde_json::Value::String(String::from("someone-else.v9"));
    let refusal = serde_json::from_value::<Environment>(foreign)
        .expect_err("a foreign schema is not this owner's value");
    assert!(
        refusal.to_string().contains("someone-else.v9"),
        "the refusal names the foreign schema: {refusal}"
    );
}

/// A passage wire that leaves a divergent axis unaccounted is refused, exactly as
/// `EnvironmentPassage::declare` refuses it.
#[test]
fn a_passage_wire_with_an_unaccounted_divergent_axis_is_refused() {
    let first = complete_environment("first", "free", "0").expect("first");
    let second = complete_environment("second", "bound", "1").expect("second");
    let divergent = first.disagreement(&second).names();
    assert!(!divergent.is_empty(), "the two environments diverge");
    let passage = EnvironmentPassage::declare(
        "declared for the test",
        first.clone(),
        second.clone(),
        divergent.iter().copied(),
    )
    .expect("a complete passage is admitted");

    // The complete passage round-trips.
    let round: EnvironmentPassage =
        serde_json::from_value(serde_json::to_value(&passage).expect("serializes"))
            .expect("a complete passage wire is a passage");
    assert_eq!(round, passage);

    // Dropping one accounted axis from the wire is refused by name.
    let mut stripped: serde_json::Value = serde_json::to_value(&passage).expect("serializes");
    stripped["accounted"] = serde_json::Value::Array(Vec::new());
    let refusal = serde_json::from_value::<EnvironmentPassage>(stripped)
        .expect_err("an unaccounted divergent axis is not a passage");
    assert!(
        refusal.to_string().contains("does not account for"),
        "the refusal names the unaccounted axes: {refusal}"
    );
}

/// A vertical-family wire whose members sit at the same environment twice, or whose members are
/// about different objects, is refused by `VerticalFamily::over_one_object` rather than remounted
/// around it.
#[test]
fn a_vertical_family_wire_repeating_an_environment_is_refused() {
    let first = complete_environment("one", "free", "0").expect("complete");
    let second = complete_environment("two", "bound", "1").expect("complete");
    let classes = [ContactClass::Inside, ContactClass::Outside, ContactClass::Open];
    let left = synthetic_family(1, &first, &classes);
    let right = synthetic_family(2, &second, &classes);
    let family = VerticalFamily::over_one_object(vec![left.clone(), right])
        .expect("two environments, one object");

    // The lawful family round-trips.
    let round: VerticalFamily =
        serde_json::from_value(serde_json::to_value(&family).expect("serializes"))
            .expect("a lawful family wire is a family");
    assert_eq!(round.members().len(), 2);

    // A wire with two members at the same environment value is refused by the constructor it is
    // routed through, rather than remounted around it.
    let mut repeated: serde_json::Value = serde_json::to_value(&family).expect("serializes");
    repeated["members"] =
        serde_json::to_value(vec![left.clone(), left]).expect("serializes");
    let refusal = serde_json::from_value::<VerticalFamily>(repeated)
        .expect_err("two members at one environment is not a vertical family");
    assert!(
        refusal.to_string().contains("environment"),
        "the refusal names the repeated environment: {refusal}"
    );

    // And a wire with no members at all.
    let mut empty: serde_json::Value = serde_json::to_value(&family).expect("serializes");
    empty["members"] = serde_json::Value::Array(Vec::new());
    assert!(
        serde_json::from_value::<VerticalFamily>(empty).is_err(),
        "a family over no members is not a measurement"
    );
}

// ---------------------------------------------------------------------------------------------
// The measured M5 exhibition
// ---------------------------------------------------------------------------------------------

/// The typed environment of one M5 presentation, built on the presented index the wire carried or
/// the caller declared.
#[allow(clippy::too_many_arguments)]
fn m5_environment(
    lineage: &str,
    presented: PresentedEnvironmentIndex,
    conformation: &str,
    conformation_ground: &str,
    oligomeric: &[(&str, u32)],
    assay: AssayFormat,
    assay_ground: &str,
) -> Environment {
    let coordinate = |value: CoordinateValue, ground: &str| {
        Coordinate::declared(value, ground).expect("a stated ground")
    };
    let undeclared = |why: &str| Coordinate::undeclared(why).expect("a stated reason");
    Environment::found(
        lineage,
        presented,
        [
            (
                CoordinateName::Species,
                coordinate(
                    CoordinateValue::Species(SpeciesHomolog {
                        species: "Homo sapiens".to_owned(),
                        homolog: "RBX1 (RING-box protein 1)".to_owned(),
                    }),
                    "the M5 release names its target as human RBX1",
                ),
            ),
            (
                CoordinateName::Conformation,
                coordinate(
                    CoordinateValue::Conformation(conformation.to_owned()),
                    conformation_ground,
                ),
            ),
            (
                CoordinateName::OligomericState,
                coordinate(
                    CoordinateValue::OligomericState(OligomericState {
                        copies: oligomeric
                            .iter()
                            .map(|(entity, copies)| ((*entity).to_owned(), *copies))
                            .collect(),
                    }),
                    "the chains actually present in the mounted mmCIF",
                ),
            ),
            (
                CoordinateName::Acidity,
                undeclared(
                    "no pH and no protonation assumption is recorded anywhere in this release; a \
                     structure predictor emits none, and inventing one would be a default",
                ),
            ),
            (
                CoordinateName::Solvation,
                undeclared(
                    "the release records no membrane or buffer context; the absence of a lipid \
                     component in a predicted file is not a declaration of solubility",
                ),
            ),
            (
                CoordinateName::Cofactors,
                coordinate(
                    CoordinateValue::Cofactors(LigandComplement {
                        copies: BTreeMap::from([("ZN".to_owned(), 3_u32)]),
                    }),
                    "the three zinc heteroatom occurrences actually present in the mounted mmCIF",
                ),
            ),
            (CoordinateName::Assay, coordinate(CoordinateValue::Assay(assay), assay_ground)),
            (
                CoordinateName::Partners,
                coordinate(
                    CoordinateValue::Partners(PartnerPanel {
                        intended: BTreeSet::from(["RBX1".to_owned()]),
                        unintended: BTreeSet::new(),
                    }),
                    "the design's declared target is RBX1; the release names no counter-target, \
                     and the empty unintended panel is that statement rather than a default",
                ),
            ),
        ],
    )
    .expect("every axis is stated")
}

/// The alpha-carbon representative complex of one chain pair, with no contact family founded: the
/// classes come from the exact interval law through `enacted_family`.
fn m5_complex(
    presentation: &StructurePresentation,
    left: &ChainOccurrence,
    right: &ChainOccurrence,
    lineage: &str,
) -> PhysicalConstraintComplex {
    let grain = ComponentGrain::Representative {
        atom_label: REPRESENTATIVE.to_owned(),
    };
    let left_material =
        component_material(left, &presentation.source_lineage, &grain, RESIDENT_DECIMAL_PLACES)
            .expect("the binder presents its representatives");
    let right_material =
        component_material(right, &presentation.source_lineage, &grain, RESIDENT_DECIMAL_PLACES)
            .expect("the target presents its representatives");
    found_constraint_complex(
        lineage,
        EventId(1),
        vec![left_material, right_material],
        Vec::new(),
    )
    .expect("the complex founds")
}

#[test]
fn the_three_m5_presentations_are_three_occurrences_at_three_environment_indices() {
    let root = structure_root();
    assert!(
        root.is_dir(),
        "the authenticated M5 structure root {} is absent, so the three-environment exhibition \
         cannot be checked, and this test refuses to report success without checking it. Set \
         {STRUCTURE_ROOT_ENV} to the directory carrying designed-free-rbx1.cif, \
         ptxv2-free-rbx1-seed2.cif, ptxv2-cul1-rbx1-seed0.cif and their -pae.npz siblings. The \
         environment and status laws themselves are checked without any fixture by \
         a_comparison_without_a_passage_is_a_typed_refusal_naming_the_coordinates and \
         the_across_environment_status_lifts_agreement_and_separates_disagreement.",
        root.display()
    );

    let read = |name: &str| {
        StructurePresentation::read(&root.join(name))
            .unwrap_or_else(|error| panic!("{name}: {error}"))
    };
    let designed = read("designed-free-rbx1.cif");
    let free = read("ptxv2-free-rbx1-seed2.cif");
    let bound = read("ptxv2-cul1-rbx1-seed0.cif");

    // The two Protenix runs carry their own environment arrays; the designed structure carries no
    // uncertainty array at all, so its presented index is declared with a stated ground.
    let free_pae = AddressedUncertainty::read_self_indexed(&root.join("ptxv2-free-rbx1-seed2-pae.npz"))
        .expect("the free npz carries its own environment");
    let bound_pae =
        AddressedUncertainty::read_self_indexed(&root.join("ptxv2-cul1-rbx1-seed0-pae.npz"))
            .expect("the complex npz carries its own environment");

    let designed_binder = designed.chain_with_residue_count(96).expect("96 residues");
    let designed_target = designed.chain_with_residue_count(108).expect("108 residues");
    let designed_presented = PresentedEnvironmentIndex::declared(
        "declared for the designed structure, which carries no uncertainty array at all: the token \
         population is the designed mmCIF's own two protein chains",
        TargetEcology {
            target: "RBX1".to_owned(),
            target_form: "designed_free".to_owned(),
            stoichiometry: "1to1".to_owned(),
            cofolding_model: "none: this is a designed structure, not a prediction".to_owned(),
        },
        DesignLineage {
            design_uuid: free_pae.environment().lineage.design_uuid.clone(),
            design_name: free_pae.environment().lineage.design_name.clone(),
            seed: "none".to_owned(),
        },
        designed_binder
            .residues
            .iter()
            .map(|residue| TokenAddress {
                chain: designed_binder.label_asym_id.clone(),
                residue: residue.source_ordinal,
                entity: designed_binder.entity.clone(),
            })
            .chain(designed_target.residues.iter().map(|residue| TokenAddress {
                chain: designed_target.label_asym_id.clone(),
                residue: residue.source_ordinal,
                entity: designed_target.entity.clone(),
            }))
            .collect(),
    )
    .expect("a declaration with a stated ground");

    let designed_environment = m5_environment(
        "designed free RBX1",
        designed_presented,
        "designed binder complex with free RBX1; no cullin present",
        "the designed release presents the binder and RBX1 alone",
        &[("binder", 1), ("RBX1", 1)],
        AssayFormat::Declared {
            description: "design generator output; neither a prediction nor a measurement"
                .to_owned(),
        },
        "the designed structure is the generator's own emission",
    );
    let free_environment = m5_environment(
        "Protenix free RBX1 seed 2",
        free_pae.environment().clone(),
        "predicted binder complex with free RBX1; no cullin present",
        "the released free wire leaves target_form blank and the file carries two protein chains",
        &[("binder", 1), ("RBX1", 1)],
        AssayFormat::InSilicoPrediction {
            predictor: "ptxv2".to_owned(),
            seed: "2".to_owned(),
        },
        "the npz carries cofolding_model ptxv2 and seed 2",
    );
    let bound_environment = m5_environment(
        "Protenix CUL1-bound RBX1 seed 0",
        bound_pae.environment().clone(),
        "rbx1_cul1_zn",
        "the released wire's own target_form, and the file carries a third protein chain",
        &[("binder", 1), ("RBX1", 1), ("CUL1", 1)],
        AssayFormat::InSilicoPrediction {
            predictor: "ptxv2".to_owned(),
            seed: "0".to_owned(),
        },
        "the npz carries cofolding_model ptxv2 and seed 0",
    );

    // Three occurrences, three environments. Every environment is complete: every axis is either
    // declared with a ground or explicitly undeclared.
    assert_eq!(
        designed_environment.undeclared_names(),
        BTreeSet::from([CoordinateName::Acidity, CoordinateName::Solvation]),
        "no pH and no solvent context is recorded anywhere in this release"
    );

    let designed_occurrence = Occurrence::found(
        OccurrenceId(1),
        OccurrenceKind::Designed {
            generator: "the M5 design generator".to_owned(),
            rounds: 0,
        },
        "designed-free-rbx1.cif",
        designed_environment.clone(),
        m5_complex(
            &designed,
            designed_binder,
            designed_target,
            "designed free RBX1 / binder x RBX1",
        ),
    );
    let free_binder = free.chain_with_residue_count(96).expect("96 residues");
    let free_target = free.chain_with_residue_count(108).expect("108 residues");
    let free_occurrence = Occurrence::found(
        OccurrenceId(2),
        OccurrenceKind::Predicted {
            predictor: "ptxv2".to_owned(),
            seed: "2".to_owned(),
        },
        "ptxv2-free-rbx1-seed2.cif",
        free_environment.clone(),
        m5_complex(&free, free_binder, free_target, "Protenix free seed 2 / binder x RBX1"),
    );
    let bound_binder = bound.chain_with_residue_count(96).expect("96 residues");
    let bound_target = bound.chain_with_residue_count(108).expect("108 residues");
    let bound_occurrence = Occurrence::found(
        OccurrenceId(3),
        OccurrenceKind::Predicted {
            predictor: "ptxv2".to_owned(),
            seed: "0".to_owned(),
        },
        "ptxv2-cul1-rbx1-seed0.cif",
        bound_environment.clone(),
        m5_complex(
            &bound,
            bound_binder,
            bound_target,
            "Protenix CUL1-RBX1 seed 0 / binder x RBX1",
        ),
    );

    let aperture = eight_angstrom_aperture();
    let families = [&designed_occurrence, &free_occurrence, &bound_occurrence]
        .iter()
        .map(|occurrence| {
            occurrence
                .enacted_family(ConstraintComponentId(1), ConstraintComponentId(2), &aperture)
                .expect("the family enacts")
        })
        .collect::<Vec<_>>();
    for family in &families {
        assert_eq!(family.readings.len(), 10_368, "96 residues against 108");
    }

    // ----- the refusal -----
    let designed_against_free = designed_environment.disagreement(&free_environment);
    assert_eq!(
        designed_against_free.names(),
        BTreeSet::from([
            CoordinateName::Conformation,
            CoordinateName::Acidity,
            CoordinateName::Solvation,
            CoordinateName::Assay,
        ]),
        "the designed structure and the free prediction are claims at two sites"
    );
    let designed_against_bound = designed_environment.disagreement(&bound_environment);
    assert_eq!(
        designed_against_bound.names(),
        BTreeSet::from([
            CoordinateName::Conformation,
            CoordinateName::OligomericState,
            CoordinateName::Acidity,
            CoordinateName::Solvation,
            CoordinateName::Assay,
        ]),
        "and the CUL1-bound prediction adds the oligomeric state"
    );
    match compare_here(&families[0], &families[1]) {
        Err(EnvironmentRefusal::EnvironmentsDiffer { disagreement }) => {
            assert_eq!(disagreement.names(), designed_against_free.names());
        }
        other => panic!("comparing two M5 environments without a passage must refuse: {other:?}"),
    }

    // ----- the lawful comparison -----
    let passage = EnvironmentPassage::declare(
        "both presentations are of the same designed binder against the same RBX1 target file, so \
         an alpha-carbon contact claim is carried from the designed structure to the free \
         prediction. The conformation and the assay format change and are named; the pH and the \
         solvent context are undeclared on both sides and the passage carries the claim across \
         that ignorance explicitly rather than assuming they match",
        designed_environment.clone(),
        free_environment.clone(),
        designed_against_free.names(),
    )
    .expect("a passage that accounts for every divergent axis");
    let carried = compare_through(&families[0], &families[1], &passage)
        .expect("the supplied passage admits the comparison");
    assert_eq!(
        carried.read_at, designed_environment,
        "the environment the claim was read at is the passage's residual and is retained"
    );
    assert_eq!(carried.carried_to, free_environment);
    assert_eq!(carried.comparison.pairs, 10_368);
    eprintln!(
        "physical_occurrence fixture | designed -> free | pairs {} | agreeing {} | separating {}",
        carried.comparison.pairs,
        carried.comparison.agreeing,
        carried.comparison.separating.len()
    );
    assert_eq!(
        carried.comparison.agreeing + carried.comparison.separating.len(),
        10_368
    );
    assert_eq!(
        (carried.comparison.agreeing, carried.comparison.separating.len()),
        (10_338, 30),
        "the designed structure and the free prediction separate on exactly 30 of the 10,368 \
         alpha-carbon pairs, once a passage makes the comparison lawful"
    );

    // ----- environment dependence on the real data -----
    let vertical = VerticalFamily::over_one_object(families.clone())
        .expect("three environments over one object");
    assert_eq!(vertical.members().len(), 3);
    let status = vertical.status_across().expect("the status of every pair");
    assert_eq!(status.len(), 10_368);
    let mut counts: BTreeMap<&'static str, usize> = BTreeMap::new();
    for value in status.values() {
        *counts.entry(value.label()).or_default() += 1;
    }
    eprintln!("physical_occurrence fixture | M5 three-environment status | {counts:?}");
    assert!(
        counts.values().copied().sum::<usize>() == 10_368,
        "every pair carries exactly one status"
    );
    assert_eq!(
        counts.get("kinetically-inaccessible"),
        None,
        "no static structure produces kinetic inaccessibility"
    );
    assert_eq!(counts.get("competing"), None, "no valence was declared here");
    let dependent = vertical
        .environment_dependent_pairs()
        .expect("the dependent pairs");
    assert_eq!(
        dependent.len(),
        *counts.get("environment-dependent").unwrap_or(&0)
    );
    // [established-bounded; measured] Over the 10,368 alpha-carbon pairs of the binder against
    // RBX1, the three presentations agree `Formed` on 38, agree `Excluded` on 10,288, and read 42
    // differently. Those 42 are exactly the pairs whose status is a fact about the environment and
    // not about the geometry of any one file.
    assert_eq!(
        (
            counts.get("formed").copied().unwrap_or(0),
            counts.get("excluded").copied().unwrap_or(0),
            counts.get("open").copied().unwrap_or(0),
            dependent.len()
        ),
        (38, 10_288, 0, 42),
        "the M5 three-environment status table"
    );
    // Exactly one of the dependent pairs has an undecided reading somewhere: the single
    // alpha-carbon pair the designed presentation leaves `Open` at the 8 angstrom aperture. An
    // open reading is never resolved by the across-environment derivation; it is placed.
    let with_open = dependent
        .iter()
        .filter(|pair| match &status[pair] {
            ContactStatus::EnvironmentDependent(dependence) => !dependence.open_at.is_empty(),
            _ => false,
        })
        .count();
    assert_eq!(
        with_open, 1,
        "the one open alpha-carbon reading of the designed presentation is placed, not resolved"
    );

    // One environment-dependent pair, named, with where each class was read.
    let witness = dependent.first().copied().expect("at least one");
    match &status[&witness] {
        ContactStatus::EnvironmentDependent(dependence) => {
            assert_eq!(dependence.pair, witness);
            assert_eq!(
                dependence.formed_at.len()
                    + dependence.excluded_at.len()
                    + dependence.open_at.len(),
                3,
                "every one of the three occurrences is placed"
            );
            eprintln!(
                "physical_occurrence fixture | environment-dependent witness {witness:?} | \
                 formed at {:?} | excluded at {:?} | open at {:?}",
                dependence
                    .formed_at
                    .iter()
                    .map(|at| at.occurrence)
                    .collect::<Vec<_>>(),
                dependence
                    .excluded_at
                    .iter()
                    .map(|at| at.occurrence)
                    .collect::<Vec<_>>(),
                dependence
                    .open_at
                    .iter()
                    .map(|at| at.occurrence)
                    .collect::<Vec<_>>(),
            );
        }
        other => panic!("{other:?}"),
    }

    // The horizontal family refuses this population: three environments is not one.
    assert!(matches!(
        HorizontalFamily::at_one_environment(families),
        Err(StatusRefusal::Environment(
            EnvironmentRefusal::EnvironmentsDiffer { .. }
        ))
    ));
}

#[test]
fn the_m5_pae_arrays_carry_asymmetric_ordered_pairs() {
    let root = structure_root();
    assert!(
        root.is_dir(),
        "the authenticated M5 structure root {} is absent, so the directional-uncertainty \
         exhibition cannot be checked, and this test refuses to report success without checking \
         it. Set {STRUCTURE_ROOT_ENV} to the directory carrying ptxv2-free-rbx1-seed2.cif, \
         ptxv2-free-rbx1-seed2-pae.npz and ptxv2-cul1-rbx1-seed0-pae.npz. The asymmetry law \
         itself is checked without any fixture by directional_uncertainty_is_never_symmetrized.",
        root.display()
    );

    // [established-bounded; measured] Both released arrays are overwhelmingly directional: of the
    // unordered pairs, 21,094 of 21,321 and 163,345 of 163,878 carry two different cells.
    for (name, extent, format, expected_asymmetric) in [
        (
            "ptxv2-free-rbx1-seed2-pae.npz",
            207_usize,
            UncertaintyWordFormat::Binary16,
            21_094_usize,
        ),
        (
            "ptxv2-cul1-rbx1-seed0-pae.npz",
            573_usize,
            UncertaintyWordFormat::Binary16,
            163_345_usize,
        ),
    ] {
        let occurrence = AddressedUncertainty::read_self_indexed(&root.join(name))
            .unwrap_or_else(|error| panic!("{name}: {error}"));
        let array = occurrence.array();
        assert_eq!(array.extent, extent);
        assert_eq!(array.format, format);
        let mut asymmetric = 0_usize;
        let mut widest: Option<(usize, usize, Rat, Rat)> = None;
        for row in 0..extent {
            for column in (row + 1)..extent {
                let forward = array.word(row, column).expect("in range").value;
                let reverse = array.word(column, row).expect("in range").value;
                if forward != reverse {
                    asymmetric += 1;
                    let gap = if forward > reverse {
                        &forward - &reverse
                    } else {
                        &reverse - &forward
                    };
                    let is_wider = widest.as_ref().is_none_or(|(_, _, f, r)| {
                        let previous = if f > r { f - r } else { r - f };
                        gap > previous
                    });
                    if is_wider {
                        widest = Some((row, column, forward.clone(), reverse.clone()));
                    }
                }
            }
        }
        let unordered = extent * (extent - 1) / 2;
        let (row, column, forward, reverse) =
            widest.expect("a directional array carries at least one asymmetric ordered pair");
        eprintln!(
            "physical_occurrence fixture | {name} | extent {extent} | asymmetric unordered pairs \
             {asymmetric} of {unordered} | widest at ({row},{column}): forward {forward} reverse \
             {reverse}"
        );
        assert_eq!(
            asymmetric, expected_asymmetric,
            "{name} is a directional array: PAE(i->j) and PAE(j->i) differ on this many unordered \
             pairs, and symmetrizing it would destroy testimony the predictor gave"
        );
        assert_ne!(forward, reverse);
    }
}

#[test]
fn the_m5_founded_family_carries_directional_uncertainty_on_every_contact_pair() {
    let root = structure_root();
    assert!(
        root.is_dir(),
        "the authenticated M5 structure root {} is absent, so the founded-family exhibition \
         cannot be checked, and this test refuses to report success without checking it. Set \
         {STRUCTURE_ROOT_ENV} to the directory carrying ptxv2-free-rbx1-seed2.cif and \
         ptxv2-free-rbx1-seed2-pae.npz. The retention law itself is checked without any fixture \
         by directional_uncertainty_is_never_symmetrized.",
        root.display()
    );

    let structure = StructurePresentation::read(&root.join("ptxv2-free-rbx1-seed2.cif"))
        .expect("the free structure reads");
    let uncertainty =
        AddressedUncertainty::read_self_indexed(&root.join("ptxv2-free-rbx1-seed2-pae.npz"))
            .expect("the free npz carries its own environment");
    let environment = m5_environment(
        "Protenix free RBX1 seed 2",
        uncertainty.environment().clone(),
        "predicted binder complex with free RBX1; no cullin present",
        "the released free wire leaves target_form blank",
        &[("binder", 1), ("RBX1", 1)],
        AssayFormat::InSilicoPrediction {
            predictor: "ptxv2".to_owned(),
            seed: "2".to_owned(),
        },
        "the npz carries cofolding_model ptxv2 and seed 2",
    );
    let addressed = AddressedOccurrence::found(structure, uncertainty);
    let binder = addressed.structure.chain("B").expect("chain B").clone();
    let target = addressed.structure.chain("A").expect("chain A").clone();
    let complex = addressed
        .constraint_complex(
            "Protenix free seed 2 / binder x RBX1, through the library intake",
            EventId(1),
            &binder,
            &target,
            &ContactPresentation {
                grain: ComponentGrain::Representative {
                    atom_label: REPRESENTATIVE.to_owned(),
                },
                resident_decimal_places: RESIDENT_DECIMAL_PLACES,
                aperture: eight_angstrom_aperture(),
            },
        )
        .expect("the constraint complex founds");

    let occurrence = Occurrence::found(
        OccurrenceId(2),
        OccurrenceKind::Predicted {
            predictor: "ptxv2".to_owned(),
            seed: "2".to_owned(),
        },
        "ptxv2-free-rbx1-seed2.cif",
        environment,
        complex,
    );
    let family = occurrence
        .founded_family(
            "ptxv2 predicted aligned error",
            ConstraintComponentId(1),
            ConstraintComponentId(2),
        )
        .expect("the founded family carries its uncertainty");
    assert_eq!(family.readings.len(), 10_368);
    assert!(
        family
            .readings
            .iter()
            .all(|reading| reading.uncertainty.is_some()),
        "every addressed pair carries its directional uncertainty"
    );
    let asymmetric = family
        .readings
        .iter()
        .filter(|reading| {
            reading
                .uncertainty
                .as_ref()
                .is_some_and(DirectionalUncertainty::is_asymmetric)
        })
        .count();
    let formed = family
        .readings
        .iter()
        .filter(|reading| reading.class == ContactClass::Inside)
        .count();
    eprintln!(
        "physical_occurrence fixture | ptxv2 free seed 2 binder x RBX1 | pairs {} | formed {} | \
         asymmetric directional readings {}",
        family.readings.len(),
        formed,
        asymmetric
    );
    assert_eq!(formed, 59, "the alpha-carbon selection's contact count");
    // [established-bounded; measured] 10,314 of the 10,368 addressed pairs carry two different
    // directional readings. Symmetrizing would discard a distinction on 99.5 per cent of them.
    assert_eq!(
        asymmetric, 10_314,
        "the predictor's uncertainty is directional on the contact population too"
    );

    // Transposing one of them exhibits the asymmetry without erasing it.
    let witness = family
        .readings
        .iter()
        .find_map(|reading| {
            reading
                .uncertainty
                .as_ref()
                .filter(|uncertainty| uncertainty.is_asymmetric())
        })
        .expect("at least one asymmetric pair");
    assert_ne!(witness.transposed(), *witness);
    assert_eq!(witness.transposed().transposed(), *witness);
    assert_eq!(witness.transposed().forward, witness.reverse);
}

#[test]
fn the_boltz_pae_array_carries_asymmetric_ordered_pairs() {
    let root = boltz_root();
    assert!(
        root.is_dir(),
        "the Boltz-2 prediction root {} is absent, so the external-predictor asymmetry cannot be \
         checked, and this test refuses to report success without checking it. Set \
         {BOLTZ_ROOT_ENV} to the directory carrying pae_test_model_0.npz and test_model_0.cif. \
         The asymmetry law itself is checked without any fixture by \
         directional_uncertainty_is_never_symmetrized.",
        root.display()
    );

    let structure = StructurePresentation::read(&root.join("test_model_0.cif"))
        .expect("the Boltz structure reads");
    let chain = structure
        .chain_with_residue_count(330)
        .expect("one chain of 330 residues");
    let presented = PresentedEnvironmentIndex::declared(
        "declared for a Boltz-2 run that emits only pae: the token population is the prediction's \
         own mmCIF chain",
        TargetEcology {
            target: "boltz-smoke".to_owned(),
            target_form: "free".to_owned(),
            stoichiometry: "1to0".to_owned(),
            cofolding_model: "boltz2".to_owned(),
        },
        DesignLineage {
            design_uuid: "boltz-smoke-test".to_owned(),
            design_name: "test_model_0".to_owned(),
            seed: "0".to_owned(),
        },
        chain
            .residues
            .iter()
            .map(|residue| TokenAddress {
                chain: chain.label_asym_id.clone(),
                residue: residue.source_ordinal,
                entity: chain.entity.clone(),
            })
            .collect(),
    )
    .expect("a declaration with a stated ground");
    let occurrence = AddressedUncertainty::read_with_declared_environment(
        &root.join("pae_test_model_0.npz"),
        presented,
    )
    .expect("the Boltz occurrence founds once an environment is supplied");
    let array = occurrence.array();
    assert_eq!(array.extent, 330);
    assert_eq!(array.format, UncertaintyWordFormat::Binary32);

    let mut asymmetric = 0_usize;
    let mut witness = None;
    for row in 0..array.extent {
        for column in (row + 1)..array.extent {
            let forward = array.word(row, column).expect("in range").value;
            let reverse = array.word(column, row).expect("in range").value;
            if forward != reverse {
                asymmetric += 1;
                if witness.is_none() {
                    witness = Some((row, column, forward, reverse));
                }
            }
        }
    }
    let (row, column, forward, reverse) = witness.expect("a directional <f4 array");
    eprintln!(
        "physical_occurrence fixture | boltz-2 pae_test_model_0.npz | extent 330 | asymmetric \
         unordered pairs {asymmetric} of {} | witness ({row},{column}): forward {forward} reverse \
         {reverse}",
        330 * 329 / 2
    );
    // [established-bounded; measured] Every one of the 54,285 unordered pairs of the Boltz-2 `<f4`
    // array is directional. Not most of them: all of them.
    assert_eq!(
        asymmetric,
        330 * 329 / 2,
        "every unordered pair of Boltz-2's <f4 PAE array carries two different cells"
    );

    // And the retained pair is not the transposed one.
    let retained = DirectionalUncertainty {
        receiver: "boltz-2 predicted aligned error".to_owned(),
        source_lineage: "pae_test_model_0.npz".to_owned(),
        forward: ExactInterval::point(forward),
        forward_ulp: Rat::new(BigInt::from(1), BigInt::from(1)),
        reverse: ExactInterval::point(reverse),
        reverse_ulp: Rat::new(BigInt::from(1), BigInt::from(1)),
    };
    assert!(retained.is_asymmetric());
    assert_ne!(retained.transposed(), retained);
}
