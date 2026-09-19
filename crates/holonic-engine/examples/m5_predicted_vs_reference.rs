//! **The M5 design's predicted structures read against its reference presentations, through the
//! library's own receivers.**
//!
//! [definition] This example **founds nothing**. Every reading below is an existing public owner's,
//! composed here in one place so that a real predictor's output and an authenticated reference
//! stand at the same receivers and the difference is a measurement rather than a story. The four
//! slots of the reading, in the notation of `docs/HOLONIC_NOTATION.md`:
//!
//! | slot | what stands in it |
//! |---|---|
//! | source geometry | one presented alpha-carbon complex per presentation, `physical_intake` |
//! | receiver map | the 8 Å contact aperture, the rigidity Jacobian, the cut section |
//! | transport | `EnvironmentPassage`, declared per ordered pair, naming every divergent axis |
//! | returned residual | the environment the claim was read at, carried back by the passage |
//!
//! `|presentation⟩` is the construction; `⟨receiver|` is one of the three receivers below; the
//! bracket `⟨receiver|presentation⟩` is the face this example prints. A comparison of two
//! presentations **without** a passage is a typed refusal by design, and this example exhibits that
//! refusal before it declares the passage that lifts it.
//!
//! # The three receivers
//!
//! 1. **Contact.** The cross family of the 96-monomer binder against the 108-monomer target at the
//!    exact 8 Å aperture — 10,368 addressed alpha-carbon pairs — read as one
//!    [`PluralFibre`](holonic_engine::physical_occurrence::plural_fibre::PluralFibre) over every
//!    presentation that carries both chains. The `(agreeing, separating, open-carrying)` counts are
//!    **computed by that owner** from the declared receiver family; none is supplied.
//! 2. **Rigidity.** [`rigidity_reading`], [`rigid_clusters`] and [`removal_sensitivity`] on a
//!    declared residue window of the target chain, on the same window for every presentation.
//! 3. **Chain.** [`hinge_by_minimal_section`] over the same window, then [`elastic_chain`] at the
//!    interior hinge and the whole-chain reading: the neck coupling's rank, the cross-domain rank
//!    bound, the power balance's residuals, the Markov relative degree and the analytic width's
//!    scope.
//!
//! # The exterior float baseline
//!
//! [definition] `mod exterior_float_baseline` is the **only** `f64` in this file, it reads the
//! mmCIF decimal tokens' own retained strings rather than any library value, and nothing it returns
//! enters a library call. It exists because a reader who has never met this repository knows what a
//! Cα RMSD is; it decides nothing. Every `f64` in this example is inside that module or is a wall
//! clock printed in seconds.
//!
//! # Run
//!
//! ```sh
//! cargo run --release -p holonic-engine --example m5_predicted_vs_reference -- \
//!   --structure-root /home/b/Downloads/holonics-m5-rbx1-rank05 \
//!   --boltz-root .local/m5-prediction-2026-09-19/presentations \
//!   --out research/experiments/m5_predicted_vs_reference/results.json
//! ```

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::time::Instant;

use holonic_engine::EventId;
use holonic_engine::holonic_chain::{
    ANALYTIC_EXTENT_CEILING, AnalyticScope, CUT_CEILING, HingeVerdict, elastic_chain,
    hinge_by_minimal_section,
};
use holonic_engine::neck::{ConstitutiveLink, WidthFace};
use holonic_engine::physical_constraint_complex::{
    ConstraintComponentId, ConstraintEdge, ConstraintVertexId, ContactClass, DistanceAperture,
};
use holonic_engine::physical_constraint_grading::EdgeProvenance;
use holonic_engine::physical_intake::mmcif::{ChainOccurrence, StructurePresentation};
use holonic_engine::physical_intake::{
    AddressedUncertainty, ComponentGrain, DesignLineage, EnvironmentIndex as PresentedIndex,
    TargetEcology, TokenAddress, component_material, found_constraint_complex,
};
use holonic_engine::physical_occurrence::plural_fibre::PluralFibre;
use holonic_engine::physical_occurrence::{
    AssayFormat, Coordinate, CoordinateName, CoordinateValue, Environment, EnvironmentPassage,
    LigandComplement, Occurrence, OccurrenceId, OccurrenceKind, OligomericState, PartnerPanel,
    SituatedFamily, SpeciesHomolog, compare_here, compare_through,
};
use holonic_engine::rigidity_receiver::{
    ExactConfiguration, RigidityJacobian, removal_sensitivity, rigid_clusters, rigidity_reading,
};
use num_bigint::BigInt;
use num_traits::Zero;
use relational_geometry::Rat;
use serde_json::{Value, json};

// ==============================================================================================
// declared scopes — every one of these is a scope, not a law
// ==============================================================================================

/// The binder's monomer count in the M5 object.
const BINDER_RESIDUES: usize = 96;
/// The target chain's (RBX1's) monomer count. The one component present in every presentation.
const TARGET_RESIDUES: usize = 108;
/// The alpha carbon is the residue's representative. The M5 receiver's own choice.
const REPRESENTATIVE: &str = "CA";
/// The resident decimal grain the presented boxes are projected outward onto.
const RESIDENT_DECIMAL_PLACES: u32 = 7;
/// Eight angstroms, squared, on the exact wire.
const CONTACT_SQUARED: i64 = 64;
/// The short window the whole chain reading is taken on.
const CHAIN_WINDOW: usize = 12;
/// The long window the hinge section profile is scanned on.
const SCAN_WINDOW: usize = 40;
/// Where the windows start along the target chain. **Offset 0 is RBX1's N-terminal arm**, which
/// every presentation places differently; offset 40 is inside the RING core. Reading both is what
/// keeps "the predictions disagree here" from being read as "the predictions disagree".
const WINDOW_OFFSETS: [usize; 2] = [0, 40];
/// The residue from which the exterior core baseline is taken: RBX1's first twenty monomers are a
/// long arm and a whole-chain superposition is dominated by it.
const CORE_FROM: usize = 20;
/// The margin that excludes terminal cuts: a cut leaving fewer than this many residues on a side
/// is narrow because one residue has few neighbours, not because anything hinges there.
const INTERIOR_MARGIN: usize = 4;
/// The cluster enumeration ceiling.
const CLUSTER_BOUND: usize = 1 << 16;

fn int(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn aperture() -> DistanceAperture {
    DistanceAperture {
        lineage: "declared contact receiver: exact distance not greater than 8 angstroms"
            .to_owned(),
        squared: int(CONTACT_SQUARED),
    }
}

// ==============================================================================================
// the presentations
// ==============================================================================================

/// What a presentation is, before it is read: a file, a kind of testimony, and the declarations
/// that its environment index needs and that no file supplies.
struct Declared {
    name: &'static str,
    file: PathBuf,
    /// The Protenix releases carry their own uncertainty array with its environment; Boltz-2 and
    /// the designed structure do not, so the index is declared with a stated ground.
    pae: Option<PathBuf>,
    kind: OccurrenceKind,
    conformation: &'static str,
    conformation_ground: &'static str,
    assay: AssayFormat,
    assay_ground: &'static str,
    cofactors: BTreeMap<String, u32>,
    cofactor_ground: &'static str,
    /// `false` for a prediction of the target alone: it carries no binder, so the 96 × 108 cross
    /// family cannot be addressed and the object check refuses it at the contact receiver.
    carries_binder: bool,
    /// The stated ground of the presented index when the file supplies none.
    declaration: &'static str,
    ecology: TargetEcology,
    lineage: DesignLineage,
}

fn declared_presentations(structure_root: &Path, boltz_root: &Path) -> Vec<Declared> {
    let zinc = |copies: u32| BTreeMap::from([("ZN".to_owned(), copies)]);
    vec![
        Declared {
            name: "designed",
            file: structure_root.join("designed-free-rbx1.cif"),
            pae: None,
            kind: OccurrenceKind::Designed {
                generator: "the M5 release's own design generator".to_owned(),
                rounds: 0,
            },
            conformation: "designed_free",
            conformation_ground: "the M5 release names this file the designed free structure",
            assay: AssayFormat::Declared {
                description: "a design generator's emitted structure, not a prediction".to_owned(),
            },
            assay_ground: "the designed structure is emitted by the design pipeline itself",
            cofactors: zinc(3),
            cofactor_ground: "the zinc heteroatom occurrences actually present in the mounted mmCIF",
            carries_binder: true,
            declaration: "declared for the designed structure, which carries no uncertainty array \
                          at all: the token population is the designed mmCIF's own two protein \
                          chains",
            ecology: TargetEcology {
                target: "RBX1".to_owned(),
                target_form: "designed_free".to_owned(),
                stoichiometry: "1to1".to_owned(),
                cofolding_model: "none: this is a designed structure, not a prediction".to_owned(),
            },
            lineage: DesignLineage {
                design_uuid: "m5-rbx1-rank05".to_owned(),
                design_name: "m5-rbx1-rank05".to_owned(),
                seed: "none".to_owned(),
            },
        },
        Declared {
            name: "protenix-free",
            file: structure_root.join("ptxv2-free-rbx1-seed2.cif"),
            pae: Some(structure_root.join("ptxv2-free-rbx1-seed2-pae.npz")),
            kind: OccurrenceKind::Predicted {
                predictor: "Protenix v2".to_owned(),
                seed: "2".to_owned(),
            },
            conformation: "predicted_free",
            conformation_ground: "the release names this run the free prediction",
            assay: AssayFormat::InSilicoPrediction {
                predictor: "Protenix v2 cofolding".to_owned(),
                seed: "2".to_owned(),
            },
            assay_ground: "the release names Protenix v2 as the predictor",
            cofactors: zinc(3),
            cofactor_ground: "the zinc heteroatom occurrences actually present in the mounted mmCIF",
            carries_binder: true,
            declaration: "the npz carries its own environment arrays; this text is unused",
            ecology: TargetEcology {
                target: "RBX1".to_owned(),
                target_form: "predicted_free".to_owned(),
                stoichiometry: "1to1".to_owned(),
                cofolding_model: "protenix-v2".to_owned(),
            },
            lineage: DesignLineage {
                design_uuid: "m5-rbx1-rank05".to_owned(),
                design_name: "m5-rbx1-rank05".to_owned(),
                seed: "2".to_owned(),
            },
        },
        Declared {
            name: "protenix-cul1",
            file: structure_root.join("ptxv2-cul1-rbx1-seed0.cif"),
            pae: Some(structure_root.join("ptxv2-cul1-rbx1-seed0-pae.npz")),
            kind: OccurrenceKind::Predicted {
                predictor: "Protenix v2".to_owned(),
                seed: "0".to_owned(),
            },
            conformation: "predicted_cul1_bound",
            conformation_ground: "the release names this run the CUL1-bound prediction",
            assay: AssayFormat::InSilicoPrediction {
                predictor: "Protenix v2 cofolding".to_owned(),
                seed: "0".to_owned(),
            },
            assay_ground: "the release names Protenix v2 as the predictor",
            cofactors: zinc(3),
            cofactor_ground: "the zinc heteroatom occurrences actually present in the mounted mmCIF",
            carries_binder: true,
            declaration: "the npz carries its own environment arrays; this text is unused",
            ecology: TargetEcology {
                target: "RBX1".to_owned(),
                target_form: "predicted_cul1_bound".to_owned(),
                stoichiometry: "1to1to1".to_owned(),
                cofolding_model: "protenix-v2".to_owned(),
            },
            lineage: DesignLineage {
                design_uuid: "m5-rbx1-rank05".to_owned(),
                design_name: "m5-rbx1-rank05".to_owned(),
                seed: "0".to_owned(),
            },
        },
        Declared {
            name: "boltz2-complex-seed0",
            file: boltz_root.join("boltz2-complex-seed0.cif"),
            pae: None,
            kind: OccurrenceKind::Predicted {
                predictor: "Boltz-2 2.2.1".to_owned(),
                seed: "0".to_owned(),
            },
            conformation: "predicted_free",
            conformation_ground: "the binder and the target were cofolded with no third partner, \
                                  which is the same presented form as the free Protenix run",
            assay: AssayFormat::InSilicoPrediction {
                predictor: "Boltz-2 2.2.1 cofolding, MSA: colabfold MMseqs2 paired+unpaired for \
                            the target, single-sequence for the de novo binder"
                    .to_owned(),
                seed: "0".to_owned(),
            },
            assay_ground: "the run's own command line and its emitted MSA row counts",
            cofactors: BTreeMap::new(),
            cofactor_ground: "no ligand was supplied to this predictor and none is present in its \
                              output; the empty complement is that statement and not a default",
            carries_binder: true,
            declaration: "declared for a Boltz-2 run, which emits confidence arrays but none of \
                          the eleven environment arrays this intake reads: the token population is \
                          the predicted mmCIF's own two protein chains",
            ecology: TargetEcology {
                target: "RBX1".to_owned(),
                target_form: "predicted_free".to_owned(),
                stoichiometry: "1to1".to_owned(),
                cofolding_model: "boltz2-2.2.1".to_owned(),
            },
            lineage: DesignLineage {
                design_uuid: "m5-rbx1-rank05".to_owned(),
                design_name: "m5-rbx1-rank05".to_owned(),
                seed: "0".to_owned(),
            },
        },
        Declared {
            name: "boltz2-complex-seed1",
            file: boltz_root.join("boltz2-complex-seed1.cif"),
            pae: None,
            kind: OccurrenceKind::Predicted {
                predictor: "Boltz-2 2.2.1".to_owned(),
                seed: "1".to_owned(),
            },
            conformation: "predicted_free",
            conformation_ground: "the binder and the target were cofolded with no third partner, \
                                  which is the same presented form as the free Protenix run",
            assay: AssayFormat::InSilicoPrediction {
                predictor: "Boltz-2 2.2.1 cofolding, MSA reused from the seed-0 run".to_owned(),
                seed: "1".to_owned(),
            },
            assay_ground: "the run's own command line, which names the seed-0 MSA files",
            cofactors: BTreeMap::new(),
            cofactor_ground: "no ligand was supplied to this predictor and none is present in its \
                              output; the empty complement is that statement and not a default",
            carries_binder: true,
            declaration: "declared for a Boltz-2 run, which emits confidence arrays but none of \
                          the eleven environment arrays this intake reads: the token population is \
                          the predicted mmCIF's own two protein chains",
            ecology: TargetEcology {
                target: "RBX1".to_owned(),
                target_form: "predicted_free".to_owned(),
                stoichiometry: "1to1".to_owned(),
                cofolding_model: "boltz2-2.2.1".to_owned(),
            },
            lineage: DesignLineage {
                design_uuid: "m5-rbx1-rank05".to_owned(),
                design_name: "m5-rbx1-rank05".to_owned(),
                seed: "1".to_owned(),
            },
        },
        Declared {
            name: "boltz2-target-seed0",
            file: boltz_root.join("boltz2-target-seed0.cif"),
            pae: None,
            kind: OccurrenceKind::Predicted {
                predictor: "Boltz-2 2.2.1".to_owned(),
                seed: "0".to_owned(),
            },
            conformation: "predicted_target_alone",
            conformation_ground: "the target sequence was folded with no partner at all",
            assay: AssayFormat::InSilicoPrediction {
                predictor: "Boltz-2 2.2.1 single-chain folding, MSA: colabfold MMseqs2 unpaired"
                    .to_owned(),
                seed: "0".to_owned(),
            },
            assay_ground: "the run's own command line and its emitted MSA row count",
            cofactors: BTreeMap::new(),
            cofactor_ground: "no ligand was supplied to this predictor and none is present in its \
                              output; the empty complement is that statement and not a default",
            carries_binder: false,
            declaration: "declared for a Boltz-2 single-chain run: the token population is the \
                          predicted mmCIF's one protein chain",
            ecology: TargetEcology {
                target: "RBX1".to_owned(),
                target_form: "predicted_target_alone".to_owned(),
                stoichiometry: "1".to_owned(),
                cofolding_model: "boltz2-2.2.1".to_owned(),
            },
            lineage: DesignLineage {
                design_uuid: "m5-rbx1-rank05".to_owned(),
                design_name: "m5-rbx1-rank05".to_owned(),
                seed: "0".to_owned(),
            },
        },
        Declared {
            name: "boltz2-target-seed1",
            file: boltz_root.join("boltz2-target-seed1.cif"),
            pae: None,
            kind: OccurrenceKind::Predicted {
                predictor: "Boltz-2 2.2.1".to_owned(),
                seed: "1".to_owned(),
            },
            conformation: "predicted_target_alone",
            conformation_ground: "the target sequence was folded with no partner at all",
            assay: AssayFormat::InSilicoPrediction {
                predictor: "Boltz-2 2.2.1 single-chain folding, MSA reused from the seed-0 run"
                    .to_owned(),
                seed: "1".to_owned(),
            },
            assay_ground: "the run's own command line, which names the seed-0 MSA file",
            cofactors: BTreeMap::new(),
            cofactor_ground: "no ligand was supplied to this predictor and none is present in its \
                              output; the empty complement is that statement and not a default",
            carries_binder: false,
            declaration: "declared for a Boltz-2 single-chain run: the token population is the \
                          predicted mmCIF's one protein chain",
            ecology: TargetEcology {
                target: "RBX1".to_owned(),
                target_form: "predicted_target_alone".to_owned(),
                stoichiometry: "1".to_owned(),
                cofolding_model: "boltz2-2.2.1".to_owned(),
            },
            lineage: DesignLineage {
                design_uuid: "m5-rbx1-rank05".to_owned(),
                design_name: "m5-rbx1-rank05".to_owned(),
                seed: "1".to_owned(),
            },
        },
    ]
}

/// One presentation, mounted: its structure, its occurrence, and the exact places the rigidity and
/// chain receivers read. `family` is `None` exactly when the presentation carries no binder.
struct Mounted {
    name: &'static str,
    structure: StructurePresentation,
    environment: Environment,
    family: Option<SituatedFamily>,
    /// The target chain's alpha carbons as exact rationals, in residue order. The library's own
    /// exact decimal decoding (`DecimalToken::exact_centre`), never a float.
    target_places: Vec<Vec<Rat>>,
    /// The binder's, when it has one.
    binder_places: Vec<Vec<Rat>>,
    intake_nanos: u128,
    object_check: Value,
}

fn typed_environment(declared: &Declared, presented: PresentedIndex) -> Result<Environment, String> {
    let with_ground = |value: CoordinateValue, ground: &str| {
        Coordinate::declared(value, ground).map_err(|error| error.to_string())
    };
    let undeclared = |why: &str| Coordinate::undeclared(why).map_err(|error| error.to_string());
    Environment::found(
        format!("{} / typed environment index", declared.name),
        presented,
        [
            (
                CoordinateName::Species,
                with_ground(
                    CoordinateValue::Species(SpeciesHomolog {
                        species: "Homo sapiens".to_owned(),
                        homolog: "RBX1 (RING-box protein 1)".to_owned(),
                    }),
                    "the M5 release names its target as human RBX1, and every presentation here \
                     carries that exact 108-monomer sequence",
                )?,
            ),
            (
                CoordinateName::Conformation,
                with_ground(
                    CoordinateValue::Conformation(declared.conformation.to_owned()),
                    declared.conformation_ground,
                )?,
            ),
            (
                CoordinateName::OligomericState,
                with_ground(
                    CoordinateValue::OligomericState(OligomericState {
                        copies: oligomeric_copies(declared),
                    }),
                    "the protein chains actually present in the mounted mmCIF",
                )?,
            ),
            (
                CoordinateName::Acidity,
                undeclared(
                    "no pH and no protonation assumption is recorded anywhere in this \
                     presentation; a structure predictor emits none and the design pipeline \
                     records none, and inventing one would be a default",
                )?,
            ),
            (
                CoordinateName::Solvation,
                undeclared(
                    "the presentation records no membrane or buffer context; the absence of a \
                     lipid component in a predicted file is not a declaration of solubility",
                )?,
            ),
            (
                CoordinateName::Cofactors,
                with_ground(
                    CoordinateValue::Cofactors(LigandComplement {
                        copies: declared.cofactors.clone(),
                    }),
                    declared.cofactor_ground,
                )?,
            ),
            (
                CoordinateName::Assay,
                with_ground(
                    CoordinateValue::Assay(declared.assay.clone()),
                    declared.assay_ground,
                )?,
            ),
            (
                CoordinateName::Partners,
                with_ground(
                    CoordinateValue::Partners(PartnerPanel {
                        intended: BTreeSet::from(["RBX1".to_owned()]),
                        unintended: BTreeSet::new(),
                    }),
                    "the design's declared target is RBX1; no presentation here names a \
                     counter-target, and the empty unintended panel is that statement rather than \
                     a default",
                )?,
            ),
        ],
    )
    .map_err(|error| error.to_string())
}

fn oligomeric_copies(declared: &Declared) -> BTreeMap<String, u32> {
    let mut copies = BTreeMap::from([("RBX1".to_owned(), 1_u32)]);
    if declared.carries_binder {
        copies.insert("binder".to_owned(), 1);
    }
    if declared.conformation == "predicted_cul1_bound" {
        copies.insert("CUL1".to_owned(), 1);
    }
    copies
}

/// The exact alpha-carbon places of one chain, through the library's own decimal decoder.
fn exact_places(chain: &ChainOccurrence) -> Result<Vec<Vec<Rat>>, String> {
    let mut places = Vec::with_capacity(chain.residues.len());
    for residue in &chain.residues {
        let at = residue
            .labelled_atom(REPRESENTATIVE)
            .map_err(|error| error.to_string())?
            .ok_or_else(|| {
                format!(
                    "residue {} of chain {} carries no {REPRESENTATIVE}",
                    residue.source_ordinal, chain.label_asym_id
                )
            })?;
        let atom = &residue.atoms[at];
        places.push(vec![
            atom.x.exact_centre().map_err(|e| e.to_string())?,
            atom.y.exact_centre().map_err(|e| e.to_string())?,
            atom.z.exact_centre().map_err(|e| e.to_string())?,
        ]);
    }
    Ok(places)
}

fn mount(declared: &Declared, ordinal: u64) -> Result<Mounted, String> {
    let started = Instant::now();
    let structure = StructurePresentation::read(&declared.file).map_err(|error| {
        format!("{}: {error}", declared.file.display())
    })?;

    // The object check: the presentation must carry the M5 object's chains at their declared
    // lengths. An ambiguous or absent chain is a refusal naming the counts, not a first match.
    let target = structure
        .chain_with_residue_count(TARGET_RESIDUES)
        .map_err(|error| format!("target chain ({TARGET_RESIDUES} residues): {error}"))?
        .clone();
    let binder = if declared.carries_binder {
        Some(
            structure
                .chain_with_residue_count(BINDER_RESIDUES)
                .map_err(|error| format!("binder chain ({BINDER_RESIDUES} residues): {error}"))?
                .clone(),
        )
    } else {
        None
    };
    // The refusal, exhibited rather than described: a presentation that carries no binder cannot
    // be addressed at the 96 × 108 cross receiver at all, and the intake says so by name. This is
    // the object check doing its work — the fibre is about **one** object, and a prediction of the
    // target alone is a prediction of a different object.
    let cross_receiver_refusal = if declared.carries_binder {
        None
    } else {
        Some(
            structure
                .chain_with_residue_count(BINDER_RESIDUES)
                .err()
                .map(|error| error.to_string())
                .unwrap_or_else(|| {
                    "a binder chain is present although none was declared".to_owned()
                }),
        )
    };
    let object_check = json!({
        "chains_present": structure.chains.iter().map(|chain| json!({
            "label_asym_id": chain.label_asym_id,
            "residues": chain.residues.len(),
            "atom_occurrences": chain.atom_occurrences,
        })).collect::<Vec<_>>(),
        "target_chain": target.label_asym_id,
        "binder_chain": binder.as_ref().map(|chain| chain.label_asym_id.clone()),
        "carries_the_cross_family": binder.is_some(),
        "cross_receiver_refusal": cross_receiver_refusal,
    });

    let target_places = exact_places(&target)?;
    let binder_places = match &binder {
        Some(chain) => exact_places(chain)?,
        None => Vec::new(),
    };

    // The presented environment index. Where the predictor wrote one, it is read; where it did not,
    // it is declared with a stated ground and the declaration travels with it.
    let presented = match &declared.pae {
        Some(path) => AddressedUncertainty::read_self_indexed(path)
            .map_err(|error| format!("{}: {error}", path.display()))?
            .environment()
            .clone(),
        None => {
            let mut tokens = Vec::new();
            if let Some(chain) = &binder {
                tokens.extend(chain.residues.iter().map(|residue| TokenAddress {
                    chain: chain.label_asym_id.clone(),
                    residue: residue.source_ordinal,
                    entity: chain.entity.clone(),
                }));
            }
            tokens.extend(target.residues.iter().map(|residue| TokenAddress {
                chain: target.label_asym_id.clone(),
                residue: residue.source_ordinal,
                entity: target.entity.clone(),
            }));
            PresentedIndex::declared(
                declared.declaration,
                declared.ecology.clone(),
                declared.lineage.clone(),
                tokens,
            )
            .map_err(|error| error.to_string())?
        }
    };
    let environment = typed_environment(declared, presented)?;

    // The alpha-carbon complex. Component 1 is the binder and component 2 the target, so the
    // object kinship — the two ordered monomer sequences — is the same object across presentations.
    let family = match &binder {
        Some(binder_chain) => {
            let grain = ComponentGrain::Representative {
                atom_label: REPRESENTATIVE.to_owned(),
            };
            let materials = vec![
                component_material(
                    binder_chain,
                    &structure.source_lineage,
                    &grain,
                    RESIDENT_DECIMAL_PLACES,
                )
                .map_err(|error| error.to_string())?,
                component_material(
                    &target,
                    &structure.source_lineage,
                    &grain,
                    RESIDENT_DECIMAL_PLACES,
                )
                .map_err(|error| error.to_string())?,
            ];
            let complex = found_constraint_complex(
                declared.name,
                EventId(ordinal),
                materials,
                Vec::new(),
            )
            .map_err(|error| error.to_string())?;
            let occurrence = Occurrence::found(
                OccurrenceId(ordinal),
                declared.kind.clone(),
                declared.name,
                environment.clone(),
                complex,
            );
            Some(
                occurrence
                    .enacted_family(
                        ConstraintComponentId(1),
                        ConstraintComponentId(2),
                        &aperture(),
                    )
                    .map_err(|error| error.to_string())?,
            )
        }
        None => None,
    };

    Ok(Mounted {
        name: declared.name,
        structure,
        environment,
        family,
        target_places,
        binder_places,
        intake_nanos: started.elapsed().as_nanos(),
        object_check,
    })
}

// ==============================================================================================
// receiver 2 and 3: the rigidity Jacobian of one declared window
// ==============================================================================================

fn squared_distance(left: &[Rat], right: &[Rat]) -> Rat {
    left.iter().zip(right).fold(Rat::from_integer(BigInt::from(0)), |sum, (a, b)| {
        let difference = a - b;
        sum + &difference * &difference
    })
}

/// The rigidity Jacobian of a declared residue window: backbone steps are polygonal rows, and every
/// pair inside the exact 8 Å aperture is an admitted contact row. The same receiver for every
/// presentation, so what differs between them is geometry and nothing else.
fn window_jacobian(
    lineage: &str,
    places: &[Vec<Rat>],
    offset: usize,
    window: usize,
) -> Result<RigidityJacobian, String> {
    if places.len() < offset + window {
        return Err(format!(
            "the chain carries {} residues, fewer than the declared window [{offset}, {})",
            places.len(),
            offset + window
        ));
    }
    let places = &places[offset..offset + window];
    let configuration = ExactConfiguration::declared(
        3,
        places
            .iter()
            .enumerate()
            .map(|(at, point)| (ConstraintVertexId(at as u64 + 1), point.clone())),
    )
    .map_err(|error| error.to_string())?;
    let squared = int(CONTACT_SQUARED);
    let mut constraints = BTreeMap::new();
    for left in 0..window {
        for right in (left + 1)..window {
            let backbone = right == left + 1;
            if !backbone && squared_distance(&places[left], &places[right]) > squared {
                continue;
            }
            let (edge, _) = ConstraintEdge::new(
                ConstraintVertexId(left as u64 + 1),
                ConstraintVertexId(right as u64 + 1),
            )
            .map_err(|error| error.to_string())?;
            constraints.insert(
                edge,
                if backbone {
                    EdgeProvenance::Polygonal
                } else {
                    EdgeProvenance::AdmittedContact
                },
            );
        }
    }
    RigidityJacobian::found(lineage.to_owned(), &configuration, &constraints)
        .map_err(|error| error.to_string())
}

/// The rigidity reading, the cluster reading and the removal sensitivity of one window. The
/// cluster membership is returned beside the receipt because the hinge reading cross-reads it.
fn rigidity_block(
    name: &str,
    jacobian: &RigidityJacobian,
) -> Result<(Value, Vec<Vec<usize>>), String> {
    let started = Instant::now();
    let reading = rigidity_reading(jacobian).map_err(|error| error.to_string())?;
    let reading_nanos = started.elapsed().as_nanos();

    let started = Instant::now();
    let clusters =
        rigid_clusters(jacobian, &reading, CLUSTER_BOUND).map_err(|error| error.to_string())?;
    let clusters_nanos = started.elapsed().as_nanos();

    let started = Instant::now();
    let sensitivity = removal_sensitivity(jacobian, &reading).map_err(|error| error.to_string())?;
    let sensitivity_nanos = started.elapsed().as_nanos();

    // The occurrences a cluster boundary falls between: a hinge in the rigidity receiver's own
    // terms is two clusters sharing an occurrence, so the interior boundaries are where one
    // cluster ends and the next begins.
    let cluster_spans = clusters
        .clusters
        .iter()
        .map(|cluster| {
            json!({
                "first": cluster.first().copied(),
                "last": cluster.last().copied(),
                "size": cluster.len(),
            })
        })
        .collect::<Vec<_>>();

    let receipt = json!({
        "presentation": name,
        "coordinates": reading.dimension * reading.occurrences,
        "occurrences": reading.occurrences,
        "constraints": reading.constraint_count,
        "rank_jacobian": reading.rank,
        "motion_dimension": reading.motion_dimension,
        "internal_motion_dimension": reading.internal_motion_dimension,
        "self_stress_dimension": reading.self_stress_dimension,
        "infinitesimally_rigid": reading.is_infinitesimally_rigid(),
        "redundant": reading.is_redundant(),
        "trivial_motion_dimension": reading.motion_dimension - reading.internal_motion_dimension,
        "rigid_clusters": clusters.clusters.len(),
        "cluster_spans": cluster_spans,
        "implied_pairs": clusters.pairs.implied_pairs.len(),
        "implied_without_constraint": clusters.pairs.implied_without_constraint.len(),
        "load_bearing_constraints": sensitivity.load_bearing.len(),
        "redundant_constraints": sensitivity.redundant.len(),
        "nanos": {
            "rigidity_reading": reading_nanos,
            "rigid_clusters": clusters_nanos,
            "removal_sensitivity": sensitivity_nanos,
        },
    });
    Ok((receipt, clusters.clusters))
}

/// How many maximal rigid clusters **straddle** a cut: a cluster with an occurrence on each side.
///
/// [definition] This is the reading issue #38 asks for. A cut with zero straddling clusters
/// separates rigid bodies and is a candidate conformational hinge. A cut that lies inside a rigid
/// cluster cannot be a hinge whatever its section is: the two sides move together under every
/// admissible infinitesimal motion, and the narrow section is then a statement about the contact
/// graph's connectivity at the declared aperture — a packing reading — and not about motion.
fn clusters_straddling(clusters: &[Vec<usize>], cut: usize) -> usize {
    clusters
        .iter()
        .filter(|cluster| {
            cluster.iter().any(|at| *at < cut) && cluster.iter().any(|at| *at >= cut)
        })
        .count()
}

/// The hinge section profile of one window, at the declared interior margin.
fn hinge_block(
    name: &str,
    jacobian: &RigidityJacobian,
    clusters: &[Vec<usize>],
) -> Result<Value, String> {
    let started = Instant::now();
    let search = hinge_by_minimal_section(jacobian, INTERIOR_MARGIN, CUT_CEILING)
        .map_err(|error| error.to_string())?;
    let nanos = started.elapsed().as_nanos();
    let profile = search
        .scanned()
        .iter()
        .map(|candidate| {
            json!({
                "cut": candidate.cut,
                "section": candidate.section,
                "crossing": candidate.crossing_constraints,
                "upstream": candidate.upstream_constraints,
                "downstream": candidate.downstream_constraints,
            })
        })
        .collect::<Vec<_>>();
    // A **local minimum** of the section profile: a cut whose section is no greater than either
    // neighbour's, reported once per maximal run of such cuts, at the run's first cut. A strict
    // inequality would miss every plateau, and the profiles here are mostly plateaus. Beside each
    // one, how many rigid clusters straddle it — the reading that tells a hinge from packing.
    let scanned = search.scanned();
    let mut in_run = false;
    let mut local_minima = Vec::new();
    for at in 1..scanned.len().saturating_sub(1) {
        let is_minimum = scanned[at].section <= scanned[at - 1].section
            && scanned[at].section <= scanned[at + 1].section;
        if is_minimum && !in_run {
            local_minima.push(json!({
                "cut": scanned[at].cut,
                "section": scanned[at].section,
                "clusters_straddling": clusters_straddling(clusters, scanned[at].cut),
                "crossing_constraints": scanned[at].crossing_constraints,
            }));
        }
        in_run = is_minimum;
    }
    let verdict = match search.verdict() {
        HingeVerdict::Minimal { cut, section } => json!({
            "kind": "Minimal", "cut": cut, "section": section,
        }),
        HingeVerdict::NotDecidedWithinBound { cut, section, scanned, sites } => json!({
            "kind": "NotDecidedWithinBound",
            "cut": cut, "section": section, "scanned": scanned, "sites": sites,
        }),
    };
    Ok(json!({
        "presentation": name,
        "margin": search.margin(),
        "verdict": verdict,
        "minimal_cut": search.cut(),
        "minimal_section": search.section(),
        "ties": search.ties(),
        "widest_section": scanned.iter().map(|c| c.section).max(),
        "clusters_straddling_minimal_cut": clusters_straddling(clusters, search.cut()),
        "local_minima": local_minima,
        "profile": profile,
        "nanos": nanos,
    }))
}

/// The whole chain reading at the interior hinge of one window.
fn chain_block(name: &str, jacobian: &RigidityJacobian) -> Result<Value, String> {
    let started = Instant::now();
    let search = hinge_by_minimal_section(jacobian, INTERIOR_MARGIN, CUT_CEILING)
        .map_err(|error| error.to_string())?;
    let cut = search.cut();
    let chain = elastic_chain(format!("{name}|rbx1|hinge"), jacobian, cut)
        .map_err(|error| error.to_string())?;
    let coupling = chain.neck_coupling().map_err(|error| error.to_string())?;

    let bound = chain
        .rank_bound(&[int(1), int(7)])
        .map_err(|error| error.to_string())?;

    let extent = chain.interaction().joint_dimension();
    let state: Vec<Rat> = (0..extent).map(|at| int(at as i64 % 7 - 3)).collect();
    let ports = chain.interaction().source().ports().len();
    let input: Vec<Rat> = (0..ports).map(|at| int(at as i64 % 5 - 2)).collect();
    let stations = chain
        .power_stations(&state, &input)
        .map_err(|error| error.to_string())?;

    let tube = chain
        .tube_profile(&stations)
        .map_err(|error| error.to_string())?;
    let neck = chain
        .neck_reading(&stations, &int(2))
        .map_err(|error| error.to_string())?;
    let staircase = chain
        .markov_staircase(4, 0, 0)
        .map_err(|error| error.to_string())?;

    let link = ConstitutiveLink::declare(
        format!("{name}|link"),
        "the declared receiving scope of this window",
        WidthFace::Geometric,
        WidthFace::Analytic,
        int(1),
    )
    .map_err(|error| error.to_string())?;
    let widths = chain
        .chain_widths(&stations, None, link)
        .map_err(|error| error.to_string())?;
    let analytic_scope = match widths.scope() {
        AnalyticScope::Taken => json!({"kind": "Taken"}),
        AnalyticScope::NotDecidedWithinBound { extent, ceiling } => json!({
            "kind": "NotDecidedWithinBound", "extent": extent, "ceiling": ceiling,
        }),
    };

    Ok(json!({
        "presentation": name,
        "cut": cut,
        "section": search.section(),
        "joint_dimension": extent,
        "neck_coupling_rank": coupling.rank(),
        "interconnection_rank": coupling.interconnection_rank(),
        "is_pinhole": coupling.is_pinhole(),
        "is_dissipative": coupling.is_dissipative(),
        "rank_bound": bound.bound(),
        "rank_attained": bound.attained(),
        "bound_is_attained": bound.bound_is_attained(),
        "measured_ranks": bound.measured().iter().map(|(_, rank)| *rank).collect::<Vec<_>>(),
        "transport_residual_is_zero": stations.transport_residual().is_zero(),
        "rate_form_residual_is_zero": stations.rate_form_residual().is_zero(),
        "balances": stations.balances(),
        "neck_is_lossless": stations.neck_is_lossless(),
        "tube_sections": tube.sections(),
        "narrowest_station": tube.narrowest_station(),
        "neck_reading": neck.arm(),
        "relative_degree": staircase.relative_degree(),
        "read_to": staircase.read_to(),
        "no_direct_feedthrough": staircase.has_no_direct_feedthrough(),
        "analytic_scope": analytic_scope,
        "analytic_width_invented": widths.analytic().is_some(),
        "analytic_extent_ceiling": ANALYTIC_EXTENT_CEILING,
        "nanos": started.elapsed().as_nanos(),
    }))
}

// ==============================================================================================
// receiver 1: the contact fibre, and the passage the comparison needs
// ==============================================================================================

/// The ordered pair's declared passage: it must name every divergent axis or `declare` refuses it.
fn passage_between(left: &Mounted, right: &Mounted) -> Result<EnvironmentPassage, String> {
    let divergent = left
        .environment
        .disagreement(&right.environment)
        .names()
        .into_iter()
        .collect::<Vec<_>>();
    EnvironmentPassage::declare(
        format!(
            "the two presentations are the same RBX1 object read under different declarations; \
             the passage from {} to {} accounts for exactly the axes on which they diverge, and \
             the environment the left claim was read at is returned as the passage's own residual",
            left.name, right.name
        ),
        left.environment.clone(),
        right.environment.clone(),
        divergent,
    )
    .map_err(|error| error.to_string())
}

fn class_counts(family: &SituatedFamily) -> Value {
    let mut inside = 0usize;
    let mut outside = 0usize;
    let mut open = 0usize;
    for reading in &family.readings {
        match reading.class {
            ContactClass::Inside => inside += 1,
            ContactClass::Outside => outside += 1,
            ContactClass::Open => open += 1,
        }
    }
    json!({"pairs": family.readings.len(), "inside": inside, "outside": outside, "open": open})
}

// ==============================================================================================
// the exterior float baseline — the only f64 in this file, and it decides nothing
// ==============================================================================================

/// [definition] **Exterior, float, and load-bearing for nothing.** This module reads the mmCIF
/// decimal tokens' own retained strings as `f64` and returns a Cα RMSD after a Kabsch
/// superposition. It takes no library value as input and no library call takes its output. It
/// exists so a reader who has never met this repository has a familiar number beside the exact
/// ones, and it is labelled `exterior_float_rmsd_angstrom` everywhere it appears.
mod exterior_float_baseline {
    use holonic_engine::physical_intake::mmcif::ChainOccurrence;

    /// The alpha-carbon coordinates as written, parsed as `f64` from the token strings.
    pub fn float_places(chain: &ChainOccurrence, label: &str) -> Option<Vec<[f64; 3]>> {
        let mut places = Vec::with_capacity(chain.residues.len());
        for residue in &chain.residues {
            let atom = residue.atoms.iter().find(|atom| atom.label == label)?;
            places.push([
                atom.x.token.parse::<f64>().ok()?,
                atom.y.token.parse::<f64>().ok()?,
                atom.z.token.parse::<f64>().ok()?,
            ]);
        }
        Some(places)
    }

    fn centroid(points: &[[f64; 3]]) -> [f64; 3] {
        let n = points.len() as f64;
        let mut c = [0.0; 3];
        for p in points {
            for axis in 0..3 {
                c[axis] += p[axis];
            }
        }
        [c[0] / n, c[1] / n, c[2] / n]
    }

    /// Root mean square deviation after optimal rigid superposition, by the quaternion form of
    /// Kabsch (Horn 1987): the largest eigenvalue of the 4×4 key matrix, found by Jacobi rotation.
    pub fn rmsd_after_superposition(left: &[[f64; 3]], right: &[[f64; 3]]) -> Option<f64> {
        if left.len() != right.len() || left.is_empty() {
            return None;
        }
        let n = left.len() as f64;
        let cl = centroid(left);
        let cr = centroid(right);
        let mut correlation = [[0.0f64; 3]; 3];
        let mut inner = 0.0f64;
        for (a, b) in left.iter().zip(right) {
            let a = [a[0] - cl[0], a[1] - cl[1], a[2] - cl[2]];
            let b = [b[0] - cr[0], b[1] - cr[1], b[2] - cr[2]];
            for axis in 0..3 {
                inner += a[axis] * a[axis] + b[axis] * b[axis];
                for other in 0..3 {
                    correlation[axis][other] += a[axis] * b[other];
                }
            }
        }
        let r = correlation;
        let key = [
            [
                r[0][0] + r[1][1] + r[2][2],
                r[1][2] - r[2][1],
                r[2][0] - r[0][2],
                r[0][1] - r[1][0],
            ],
            [
                r[1][2] - r[2][1],
                r[0][0] - r[1][1] - r[2][2],
                r[0][1] + r[1][0],
                r[0][2] + r[2][0],
            ],
            [
                r[2][0] - r[0][2],
                r[0][1] + r[1][0],
                -r[0][0] + r[1][1] - r[2][2],
                r[1][2] + r[2][1],
            ],
            [
                r[0][1] - r[1][0],
                r[0][2] + r[2][0],
                r[1][2] + r[2][1],
                -r[0][0] - r[1][1] + r[2][2],
            ],
        ];
        let largest = largest_eigenvalue_symmetric_4(key);
        let squared = (inner - 2.0 * largest) / n;
        Some(if squared > 0.0 { squared.sqrt() } else { 0.0 })
    }

    /// Cyclic Jacobi on a 4×4 symmetric matrix; the largest diagonal entry at convergence is the
    /// largest eigenvalue.
    fn largest_eigenvalue_symmetric_4(mut a: [[f64; 4]; 4]) -> f64 {
        for _ in 0..100 {
            let mut off = 0.0;
            for row in 0..4 {
                for column in (row + 1)..4 {
                    off += a[row][column] * a[row][column];
                }
            }
            if off < 1e-24 {
                break;
            }
            for p in 0..3 {
                for q in (p + 1)..4 {
                    if a[p][q].abs() < 1e-18 {
                        continue;
                    }
                    let theta = (a[q][q] - a[p][p]) / (2.0 * a[p][q]);
                    let t = theta.signum() / (theta.abs() + (theta * theta + 1.0).sqrt());
                    let c = 1.0 / (t * t + 1.0).sqrt();
                    let s = t * c;
                    let mut next = a;
                    for k in 0..4 {
                        next[p][k] = c * a[p][k] - s * a[q][k];
                        next[q][k] = s * a[p][k] + c * a[q][k];
                    }
                    let mid = next;
                    for k in 0..4 {
                        next[k][p] = c * mid[k][p] - s * mid[k][q];
                        next[k][q] = s * mid[k][p] + c * mid[k][q];
                    }
                    a = next;
                }
            }
        }
        let mut largest = a[0][0];
        for at in 1..4 {
            if a[at][at] > largest {
                largest = a[at][at];
            }
        }
        largest
    }
}

// ==============================================================================================
// the driver
// ==============================================================================================

fn argument(args: &[String], flag: &str, fallback: &str) -> String {
    args.windows(2)
        .find(|pair| pair[0] == flag)
        .map(|pair| pair[1].clone())
        .unwrap_or_else(|| fallback.to_owned())
}

fn main() -> Result<(), String> {
    let args = std::env::args().collect::<Vec<_>>();
    let structure_root = PathBuf::from(argument(
        &args,
        "--structure-root",
        "/home/b/Downloads/holonics-m5-rbx1-rank05",
    ));
    let boltz_root = PathBuf::from(argument(
        &args,
        "--boltz-root",
        ".local/m5-prediction-2026-09-19/presentations",
    ));
    let out = argument(
        &args,
        "--out",
        "research/experiments/m5_predicted_vs_reference/results.json",
    );
    let whole = Instant::now();

    let declared = declared_presentations(&structure_root, &boltz_root);
    let mut mounted = Vec::new();
    let mut intake_rows = Vec::new();
    for (at, one) in declared.iter().enumerate() {
        match mount(one, at as u64 + 1) {
            Ok(presentation) => {
                intake_rows.push(json!({
                    "presentation": one.name,
                    "file": one.file.display().to_string(),
                    "admitted": true,
                    "object_check": presentation.object_check.clone(),
                    "environment_undeclared_axes": presentation
                        .environment
                        .undeclared_names()
                        .iter()
                        .map(|name| name.label())
                        .collect::<Vec<_>>(),
                    "nanos": presentation.intake_nanos,
                }));
                eprintln!("[intake] {} admitted", one.name);
                mounted.push(presentation);
            }
            Err(refusal) => {
                eprintln!("[intake] {} REFUSED: {refusal}", one.name);
                intake_rows.push(json!({
                    "presentation": one.name,
                    "file": one.file.display().to_string(),
                    "admitted": false,
                    "refusal": refusal,
                }));
            }
        }
    }

    // ------------------------------------------------------------------------------------------
    // Receiver 1: the contact fibre over every presentation that carries the object's two chains.
    // ------------------------------------------------------------------------------------------
    let complex_members = mounted
        .iter()
        .filter(|one| one.family.is_some())
        .collect::<Vec<_>>();
    let names = complex_members.iter().map(|one| one.name).collect::<Vec<_>>();
    let families = complex_members
        .iter()
        .map(|one| one.family.clone().expect("filtered"))
        .collect::<Vec<_>>();

    let per_presentation = complex_members
        .iter()
        .map(|one| {
            json!({
                "presentation": one.name,
                "classes": class_counts(one.family.as_ref().expect("filtered")),
            })
        })
        .collect::<Vec<_>>();

    let started = Instant::now();
    let fibre = PluralFibre::over_one_candidate(families.clone())
        .map_err(|error| format!("the plural fibre refuses: {error}"))?;
    let partition = fibre.partition();
    let separators = fibre
        .pairwise_separators()
        .map_err(|error| error.to_string())?;
    let fibre_nanos = started.elapsed().as_nanos();

    let mut role_totals: BTreeMap<&'static str, usize> = BTreeMap::new();
    for pair in fibre.addressed() {
        let role = fibre.role_of(pair).map_err(|error| error.to_string())?;
        *role_totals.entry(role.label()).or_default() += 1;
    }

    // The (agreeing, separating, open-carrying) counts of every ordered pair, **computed** by the
    // fibre owner from the declared receiver family.
    let name_of: BTreeMap<OccurrenceId, &str> = complex_members
        .iter()
        .map(|one| {
            (
                one.family.as_ref().expect("filtered").occurrence,
                one.name,
            )
        })
        .collect();
    let mut pair_rows = Vec::new();
    for separator in &separators {
        pair_rows.push(json!({
            "left": name_of.get(&separator.left),
            "right": name_of.get(&separator.right),
            "agreeing": separator.agreeing,
            "separating": separator.separating.len(),
            "open_carrying": separator.open_carrying.len(),
            "total_pairs": fibre.contacts(),
            "indistinguishable": separator.is_empty(),
        }));
    }

    // The typed refusal, exhibited: two presentations at different environment indices do not
    // compare without a passage, and the refusal names the axes.
    let mut passage_rows = Vec::new();
    for right in 1..complex_members.len() {
        let left_one = complex_members[0];
        let right_one = complex_members[right];
        let refusal = compare_here(
            left_one.family.as_ref().expect("filtered"),
            right_one.family.as_ref().expect("filtered"),
        )
        .err()
        .map(|error| error.to_string());
        let passage = passage_between(left_one, right_one)?;
        let accounted = passage
            .accounted()
            .iter()
            .map(|name| name.label())
            .collect::<Vec<_>>();
        let carried = compare_through(
            left_one.family.as_ref().expect("filtered"),
            right_one.family.as_ref().expect("filtered"),
            &passage,
        )
        .map_err(|error| error.to_string())?;
        passage_rows.push(json!({
            "left": left_one.name,
            "right": right_one.name,
            "refusal_without_a_passage": refusal,
            "axes_the_passage_accounts_for": accounted,
            "read_at_residual": carried.read_at.lineage,
            "carried_to": carried.carried_to.lineage,
            "pairs": carried.comparison.pairs,
            "agreeing": carried.comparison.agreeing,
            "separating": carried.comparison.separating.len(),
        }));
    }

    // ------------------------------------------------------------------------------------------
    // Receivers 2 and 3: rigidity, hinge profile and the whole chain, on the target chain.
    // ------------------------------------------------------------------------------------------
    let mut rigidity_rows = Vec::new();
    let mut hinge_rows = Vec::new();
    let mut chain_rows = Vec::new();
    for offset in WINDOW_OFFSETS {
        for one in &mounted {
            let scan = window_jacobian(
                &format!("{}|rbx1|[{offset},{})", one.name, offset + SCAN_WINDOW),
                &one.target_places,
                offset,
                SCAN_WINDOW,
            )?;
            eprintln!("[rigidity] {} target residues {}..{}", one.name, offset + 1, offset + SCAN_WINDOW);
            let (mut receipt, clusters) = rigidity_block(one.name, &scan)?;
            receipt["window_first_residue"] = json!(offset + 1);
            receipt["window_last_residue"] = json!(offset + SCAN_WINDOW);
            rigidity_rows.push(receipt);
            let mut hinge = hinge_block(one.name, &scan, &clusters)?;
            hinge["window_first_residue"] = json!(offset + 1);
            hinge["window_last_residue"] = json!(offset + SCAN_WINDOW);
            hinge_rows.push(hinge);

            let short = window_jacobian(
                &format!("{}|rbx1|[{offset},{})", one.name, offset + CHAIN_WINDOW),
                &one.target_places,
                offset,
                CHAIN_WINDOW,
            )?;
            eprintln!("[chain] {} target residues {}..{}", one.name, offset + 1, offset + CHAIN_WINDOW);
            let mut chain = chain_block(one.name, &short)?;
            chain["window_first_residue"] = json!(offset + 1);
            chain["window_last_residue"] = json!(offset + CHAIN_WINDOW);
            chain_rows.push(chain);
        }
    }

    // The binder chain, where present, read at the same short window: the designed binder is a de
    // novo sequence and the predictors had no homologs for it.
    let mut binder_rigidity = Vec::new();
    for one in &mounted {
        if one.binder_places.len() < CHAIN_WINDOW {
            continue;
        }
        let jacobian = window_jacobian(
            &format!("{}|binder|{CHAIN_WINDOW}", one.name),
            &one.binder_places,
            0,
            CHAIN_WINDOW,
        )?;
        binder_rigidity.push(rigidity_block(one.name, &jacobian)?.0);
    }

    // ------------------------------------------------------------------------------------------
    // The exterior float baseline.
    // ------------------------------------------------------------------------------------------
    let reference = mounted
        .iter()
        .find(|one| one.name == "designed")
        .ok_or("the designed reference is absent")?;
    let reference_target = reference
        .structure
        .chain_with_residue_count(TARGET_RESIDUES)
        .map_err(|error| error.to_string())?;
    let reference_binder = reference
        .structure
        .chain_with_residue_count(BINDER_RESIDUES)
        .map_err(|error| error.to_string())?;
    let reference_target_float =
        exterior_float_baseline::float_places(reference_target, REPRESENTATIVE)
            .ok_or("the reference target has no complete alpha-carbon trace")?;
    let reference_binder_float =
        exterior_float_baseline::float_places(reference_binder, REPRESENTATIVE)
            .ok_or("the reference binder has no complete alpha-carbon trace")?;

    let mut baseline_rows = Vec::new();
    for one in &mounted {
        let target = one
            .structure
            .chain_with_residue_count(TARGET_RESIDUES)
            .map_err(|error| error.to_string())?;
        let target_float = exterior_float_baseline::float_places(target, REPRESENTATIVE)
            .ok_or("an incomplete alpha-carbon trace")?;
        let target_rmsd = exterior_float_baseline::rmsd_after_superposition(
            &reference_target_float,
            &target_float,
        );
        let binder_rmsd = one
            .structure
            .chain_with_residue_count(BINDER_RESIDUES)
            .ok()
            .and_then(|chain| exterior_float_baseline::float_places(chain, REPRESENTATIVE))
            .and_then(|places| {
                exterior_float_baseline::rmsd_after_superposition(
                    &reference_binder_float,
                    &places,
                )
            });
        let both_rmsd = one
            .structure
            .chain_with_residue_count(BINDER_RESIDUES)
            .ok()
            .and_then(|chain| exterior_float_baseline::float_places(chain, REPRESENTATIVE))
            .and_then(|binder| {
                let mut left = reference_binder_float.clone();
                left.extend(reference_target_float.iter().copied());
                let mut right = binder;
                right.extend(target_float.iter().copied());
                exterior_float_baseline::rmsd_after_superposition(&left, &right)
            });
        let core_rmsd = exterior_float_baseline::rmsd_after_superposition(
            &reference_target_float[CORE_FROM..],
            &target_float[CORE_FROM..],
        );
        let mut window_rmsd = Vec::new();
        for offset in WINDOW_OFFSETS {
            window_rmsd.push(json!({
                "first_residue": offset + 1,
                "last_residue": offset + SCAN_WINDOW,
                "exterior_float_rmsd_angstrom": exterior_float_baseline::rmsd_after_superposition(
                    &reference_target_float[offset..offset + SCAN_WINDOW],
                    &target_float[offset..offset + SCAN_WINDOW],
                ),
            }));
        }
        baseline_rows.push(json!({
            "presentation": one.name,
            "exterior_float_rmsd_angstrom_target_108": target_rmsd,
            "exterior_float_rmsd_angstrom_target_core_21_108": core_rmsd,
            "exterior_float_rmsd_angstrom_binder_96": binder_rmsd,
            "exterior_float_rmsd_angstrom_both_204": both_rmsd,
            "exterior_float_rmsd_angstrom_scan_windows": window_rmsd,
        }));
    }

    let results = json!({
        "schema": "holonics.m5-predicted-vs-reference.v1",
        "declared_scopes": {
            "binder_residues": BINDER_RESIDUES,
            "target_residues": TARGET_RESIDUES,
            "representative_atom": REPRESENTATIVE,
            "resident_decimal_places": RESIDENT_DECIMAL_PLACES,
            "contact_aperture_squared_angstrom": CONTACT_SQUARED,
            "chain_window_residues": CHAIN_WINDOW,
            "scan_window_residues": SCAN_WINDOW,
            "window_offsets": WINDOW_OFFSETS,
            "interior_margin": INTERIOR_MARGIN,
            "exterior_core_from_residue": CORE_FROM + 1,
        },
        "intake": intake_rows,
        "contact_receiver": {
            "members": names,
            "addressed_pairs": fibre.contacts(),
            "per_presentation_classes": per_presentation,
            "fibre_roles": role_totals,
            "fibre_is_a_partition": partition.is_a_partition(),
            "pairwise": pair_rows,
            "passages": passage_rows,
            "nanos": fibre_nanos,
        },
        "rigidity_receiver_target_scan_window": rigidity_rows,
        "rigidity_receiver_binder_short_window": binder_rigidity,
        "hinge_section_profile_target_scan_window": hinge_rows,
        "chain_reading_target_short_window": chain_rows,
        "exterior_float_baseline": baseline_rows,
        "whole_run_nanos": whole.elapsed().as_nanos(),
    });

    let out = Path::new(&out);
    if let Some(parent) = out.parent() {
        std::fs::create_dir_all(parent).map_err(|error| error.to_string())?;
    }
    std::fs::write(
        out,
        serde_json::to_string_pretty(&results).map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())?;
    eprintln!(
        "[done] {} in {:.1} s",
        out.display(),
        whole.elapsed().as_secs_f64()
    );
    Ok(())
}
