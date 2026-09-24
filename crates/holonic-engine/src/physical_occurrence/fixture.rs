//! Shared synthetic and authenticated fixtures for the B5 and B6 test modules.
//!
//! [definition] `physical_occurrence/plural_fibre/tests.rs` and `physical_occurrence/passage/tests.rs`
//! both need the three M5 RBX1 presentations as situated families and both need a complete
//! synthetic environment that depends on no file. Building them twice would let the two copies
//! drift, so they are built once here. The M5 builders reproduce the addresses
//! `physical_occurrence/tests.rs` established; a consolidation of that module onto these builders
//! is a separate increment and is named in this owner's report rather than done mid-flight.

use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;

use num_bigint::BigInt;
use relational_geometry::Rat;

use super::{
    Acidity, AssayFormat, Coordinate, CoordinateName, CoordinateValue, Environment,
    EnvironmentRefusal, LigandComplement, Occurrence, OccurrenceId, OccurrenceKind,
    OligomericState, PartnerPanel, SituatedFamily, SituatedPairReading, Solvation, SpeciesHomolog,
};
use crate::EventId;
use holonics::exact_value::ExactInterval;
use crate::physical_constraint_complex::{
    ConstraintComponentId, ContactClass, DistanceAperture, PhysicalConstraintComplex,
};
use crate::physical_intake::mmcif::{ChainOccurrence, StructurePresentation};
use crate::physical_intake::{
    AddressedUncertainty, ComponentGrain, DesignLineage,
    EnvironmentIndex as PresentedEnvironmentIndex, TargetEcology, TokenAddress,
    component_material, found_constraint_complex,
};

// ---------------------------------------------------------------------------------------------
// Fixture addresses, following the pattern `physical_intake/tests.rs` established.
// ---------------------------------------------------------------------------------------------

/// The environment variable that relocates the authenticated M5 structure root.
pub const STRUCTURE_ROOT_ENV: &str = "HOLONICS_M5_STRUCTURE_ROOT";
/// Where the authenticated M5 release lives on this workstation.
pub const DEFAULT_STRUCTURE_ROOT: &str = "/home/b/Downloads/holonics-m5-rbx1-rank05";
/// The environment variable that relocates the Boltz-2 smoke prediction.
pub const BOLTZ_ROOT_ENV: &str = "HOLONICS_BOLTZ_PREDICTION_ROOT";
/// Where the Boltz-2 smoke prediction lives in the repository.
pub const DEFAULT_BOLTZ_ROOT: &str = ".local/boltz-smoke/out/boltz_results_test/predictions/test";

/// The resident decimal grain the M5 family is carried on.
pub const RESIDENT_DECIMAL_PLACES: u32 = 7;
/// The alpha-carbon representative the M5 deed selects.
pub const REPRESENTATIVE: &str = "CA";

/// The authenticated M5 structure root.
pub fn structure_root() -> PathBuf {
    std::env::var_os(STRUCTURE_ROOT_ENV)
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(DEFAULT_STRUCTURE_ROOT))
}

/// The Boltz-2 smoke prediction root.
pub fn boltz_root() -> PathBuf {
    std::env::var_os(BOLTZ_ROOT_ENV)
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("../..")
                .join(DEFAULT_BOLTZ_ROOT)
        })
}

/// The declared contact receiver: exact distance not greater than 8 angstroms.
pub fn eight_angstrom_aperture() -> DistanceAperture {
    DistanceAperture {
        lineage: "declared contact receiver: exact distance not greater than 8 angstroms"
            .to_owned(),
        squared: Rat::from_integer(BigInt::from(64)),
    }
}

/// An exact rational interval between two integers.
pub fn interval(lower: i64, upper: i64) -> ExactInterval {
    ExactInterval::new(
        Rat::from_integer(BigInt::from(lower)),
        Rat::from_integer(BigInt::from(upper)),
    )
    .expect("an ordered interval")
}

// ---------------------------------------------------------------------------------------------
// Synthetic fixtures, which depend on no file
// ---------------------------------------------------------------------------------------------

/// A presented environment index for a synthetic run that emits no environment arrays.
pub fn synthetic_presented(seed: &str, form: &str) -> PresentedEnvironmentIndex {
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
pub fn complete_environment(
    lineage: &str,
    conformation: &str,
    seed: &str,
) -> Result<Environment, EnvironmentRefusal> {
    complete_environment_with(lineage, conformation, seed, &[("SYN", 1)], None)
}

/// Every axis declared, with the oligomeric state and the protonation assumption under caller
/// control so a binding and a protonation have something to move.
pub fn complete_environment_with(
    lineage: &str,
    conformation: &str,
    seed: &str,
    oligomeric: &[(&str, u32)],
    protonation: Option<(i64, &str)>,
) -> Result<Environment, EnvironmentRefusal> {
    let ground = "declared by the synthetic fixture";
    let acidity = match protonation {
        Some((p_h, assumption)) => Coordinate::declared(
            CoordinateValue::Acidity(Acidity {
                p_h: interval(p_h, p_h),
                protonation_assumption: assumption.to_owned(),
            }),
            ground,
        )?,
        None => Coordinate::undeclared("the synthetic fixture records no pH")?,
    };
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
                    ground,
                )?,
            ),
            (
                CoordinateName::Conformation,
                Coordinate::declared(
                    CoordinateValue::Conformation(conformation.to_owned()),
                    ground,
                )?,
            ),
            (
                CoordinateName::OligomericState,
                Coordinate::declared(
                    CoordinateValue::OligomericState(OligomericState {
                        copies: oligomeric
                            .iter()
                            .map(|(entity, copies)| ((*entity).to_owned(), *copies))
                            .collect(),
                    }),
                    ground,
                )?,
            ),
            (CoordinateName::Acidity, acidity),
            (
                CoordinateName::Solvation,
                Coordinate::declared(
                    CoordinateValue::Solvation(Solvation::Soluble {
                        buffer: "synthetic buffer".to_owned(),
                    }),
                    ground,
                )?,
            ),
            (
                CoordinateName::Cofactors,
                Coordinate::declared(
                    CoordinateValue::Cofactors(LigandComplement {
                        copies: BTreeMap::new(),
                    }),
                    ground,
                )?,
            ),
            (
                CoordinateName::Assay,
                Coordinate::declared(
                    CoordinateValue::Assay(AssayFormat::InSilicoPrediction {
                        predictor: "synthetic".to_owned(),
                        seed: seed.to_owned(),
                    }),
                    ground,
                )?,
            ),
            (
                CoordinateName::Partners,
                Coordinate::declared(
                    CoordinateValue::Partners(PartnerPanel {
                        intended: BTreeSet::from(["SYN".to_owned()]),
                        unintended: BTreeSet::new(),
                    }),
                    ground,
                )?,
            ),
        ],
    )
}

/// A situated family over one binder monomer and `classes.len()` target monomers.
pub fn synthetic_family(
    occurrence: u64,
    environment: &Environment,
    classes: &[ContactClass],
) -> SituatedFamily {
    synthetic_family_named(occurrence, environment, classes, &["ALA".to_owned()])
}

/// The same, with the left component's monomer sequence under caller control so a mutation has a
/// site to move.
pub fn synthetic_family_named(
    occurrence: u64,
    environment: &Environment,
    classes: &[ContactClass],
    left_sequence: &[String],
) -> SituatedFamily {
    SituatedFamily {
        schema: "holonic-engine.situated-contact-family.v1".to_owned(),
        occurrence: OccurrenceId(occurrence),
        lineage: format!("synthetic family {occurrence}"),
        environment: environment.clone(),
        left: ConstraintComponentId(1),
        right: ConstraintComponentId(2),
        left_sequence: left_sequence.to_vec(),
        right_sequence: (0..classes.len())
            .map(|at| format!("R{}", at + 1))
            .collect(),
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

// ---------------------------------------------------------------------------------------------
// The authenticated M5 presentations
// ---------------------------------------------------------------------------------------------

/// The typed environment of one M5 presentation, on the presented index the wire carried or the
/// caller declared.
#[allow(clippy::too_many_arguments)]
pub fn m5_environment(
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
            (
                CoordinateName::Assay,
                coordinate(CoordinateValue::Assay(assay), assay_ground),
            ),
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
pub fn m5_complex(
    presentation: &StructurePresentation,
    left: &ChainOccurrence,
    right: &ChainOccurrence,
    lineage: &str,
) -> PhysicalConstraintComplex {
    let grain = ComponentGrain::Representative {
        atom_label: REPRESENTATIVE.to_owned(),
    };
    let left_material = component_material(
        left,
        &presentation.source_lineage,
        &grain,
        RESIDENT_DECIMAL_PLACES,
    )
    .expect("the binder presents its representatives");
    let right_material = component_material(
        right,
        &presentation.source_lineage,
        &grain,
        RESIDENT_DECIMAL_PLACES,
    )
    .expect("the target presents its representatives");
    found_constraint_complex(
        lineage,
        EventId(1),
        vec![left_material, right_material],
        Vec::new(),
    )
    .expect("the complex founds")
}

/// The message a fixture-dependent test fails with when the authenticated release is absent.
pub fn absent_structure_root_message(root: &std::path::Path, laws_checked_without_it: &str) -> String {
    format!(
        "the authenticated M5 structure root {} is absent, so this exhibition cannot be checked, \
         and this test refuses to report success without checking it. Set {STRUCTURE_ROOT_ENV} to \
         the directory carrying designed-free-rbx1.cif, ptxv2-free-rbx1-seed2.cif, \
         ptxv2-cul1-rbx1-seed0.cif and their -pae.npz siblings. {laws_checked_without_it}",
        root.display()
    )
}

/// The three M5 RBX1 presentations as three situated families over the same 10,368 alpha-carbon
/// pairs, in the order designed, free, CUL1-bound.
///
/// Panics with a message naming the absent path when the release is not mounted; callers assert
/// `structure_root().is_dir()` first so the failure names the fixture rather than a read error.
pub fn m5_situated_families() -> [SituatedFamily; 3] {
    let [designed, free, bound] = m5_occurrences();
    let aperture = eight_angstrom_aperture();
    [&designed, &free, &bound].map(|occurrence| {
        occurrence
            .enacted_family(
                ConstraintComponentId(1),
                ConstraintComponentId(2),
                &aperture,
            )
            .expect("the family enacts")
    })
}

/// The three M5 RBX1 presentations as three occurrences at three environment indices.
pub fn m5_occurrences() -> [Occurrence; 3] {
    let root = structure_root();
    let read = |name: &str| {
        StructurePresentation::read(&root.join(name))
            .unwrap_or_else(|error| panic!("{name}: {error}"))
    };
    let designed = read("designed-free-rbx1.cif");
    let free = read("ptxv2-free-rbx1-seed2.cif");
    let bound = read("ptxv2-cul1-rbx1-seed0.cif");

    let free_pae =
        AddressedUncertainty::read_self_indexed(&root.join("ptxv2-free-rbx1-seed2-pae.npz"))
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

    let designed_occurrence = Occurrence::found(
        OccurrenceId(1),
        OccurrenceKind::Designed {
            generator: "the M5 design generator".to_owned(),
            rounds: 0,
        },
        "designed-free-rbx1.cif",
        designed_environment,
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
        free_environment,
        m5_complex(
            &free,
            free_binder,
            free_target,
            "Protenix free seed 2 / binder x RBX1",
        ),
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
        bound_environment,
        m5_complex(
            &bound,
            bound_binder,
            bound_target,
            "Protenix CUL1-RBX1 seed 0 / binder x RBX1",
        ),
    );
    [designed_occurrence, free_occurrence, bound_occurrence]
}
