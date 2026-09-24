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
//! Cα RMSD is; it decides nothing. Every `f64` in this example is inside that module, or is a wall
//! clock printed in seconds, or is `IndexedPresentation::float_places_by_m5` — which is filled from
//! the mmCIF decimal tokens' own strings, is read by that module and by nothing else, and whose
//! only output is a JSON field named `exterior_float_rmsd_angstrom_*`.
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
use holonic_engine::evaluation_discipline::{
    DisagreementClass, disagreement_subsets, performance_on,
};
use holonics::exact_value::ExactInterval;
use holonic_engine::holonic_chain::{
    ANALYTIC_EXTENT_CEILING, AnalyticScope, CUT_CEILING, HingeVerdict, elastic_chain,
    hinge_by_minimal_section,
};
use holonic_engine::neck::{ConstitutiveLink, WidthFace};
use holonic_engine::physical_constraint_complex::{
    ConstraintComponentId, ConstraintEdge, ConstraintVertexId, ContactClass, DistanceAperture,
    PairUncertainty,
};
use holonic_engine::physical_constraint_grading::EdgeProvenance;
use holonic_engine::physical_intake::mmcif::{ChainOccurrence, StructurePresentation};
use holonic_engine::physical_intake::{
    AddressedUncertainty, ComponentGrain, DesignLineage, EnvironmentIndex as PresentedIndex,
    TargetEcology, TokenAddress, component_material, enacted_within_component_classes,
    found_constraint_complex,
};
use holonic_engine::physical_occurrence::plural_fibre::{DecidedClass, PluralFibre};
use holonic_engine::physical_occurrence::{
    Acidity, AssayFormat, Coordinate, CoordinateName, CoordinateValue, Environment,
    EnvironmentPassage, LigandComplement, Occurrence, OccurrenceId, OccurrenceKind,
    OligomericState, PartnerPanel, SituatedFamily, SpeciesHomolog, compare_here, compare_through,
};
use holonic_engine::rigidity_receiver::{
    ExactConfiguration, RigidityJacobian, removal_sensitivity, rigid_clusters, rigidity_reading,
};
use holonic_engine::topological_receiver::{
    ApertureFiltration, Coefficients, FiltrationOrder, OrderLaw, persistence,
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
        // Wave 9 worker L added `AnalyticScope::StructurallyPlaced { licence }` to
        // `holonic_chain` while this ran. This example may not repair that owner, so the arm
        // records the variant by its own `Debug` rather than reaching into a type it does not
        // own; the 2026-09-19 reading is otherwise unchanged and still reports
        // `NotDecidedWithinBound` wherever the chain reading returns it.
        other => json!({"kind": format!("{other:?}")}),
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
        // Which route produced the rank: the nullity theorem (no resolvent, `measured_ranks`
        // empty) or a measurement at the declared probes.
        "rank_is_determined_by_theorem": bound.is_determined(),
        "rank_licence": format!("{:?}", bound.licence()),
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
        // Present either because the pole atlas was taken or because structure placed the
        // spectrum; `analytic_scope` says which. Nothing is invented in either case.
        "analytic_width_present": widths.analytic().is_some(),
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
// 2026-09-20 — measured presentations, the zinc runs and the seed population
//
// [definition] Everything below is the **same three receivers** read on three new kinds of
// presentation: a measured RBX1 structure, a prediction made WITH the zinc cofactor, and a seed
// population instead of one seed. It founds nothing and adds no receiver. It adds one declared
// scope — the **commonly resolved residue range** — because a measured structure does not resolve
// every residue, and one declared receiver the M5 object check already licenses but yesterday did
// not use: the target chain's **within-component** contact family, `left == right`, which is the
// only contact receiver a target-only presentation can be addressed at.
//
// The whole section is skipped unless `--manifest` names a file, so the 2026-09-19 run above is
// reproduced unchanged by the 2026-09-19 command line.
// ==============================================================================================

/// The within-component receiver's declared chain separation. Two occurrences one or two positions
/// apart are inside any protein aperture whatever the fold does, so they carry no reading; the
/// owner refuses a separation below 2 as covalent and this scope declares 3.
const DEFAULT_MINIMUM_SEPARATION: u32 = 3;
/// The cell ceiling of the aperture filtration. The topological receiver is taken at top grade 1 —
/// vertices and edges — so the cell population is at most `n + C(n,2)`.
const TOPOLOGY_CELL_BOUND: usize = 1 << 20;
/// The persistence reduction's declared work ceiling.
const PERSISTENCE_WORK_BOUND: usize = 1 << 24;

/// One presentation, mounted and addressed by the **M5 target's own residue index**.
///
/// [definition] `residue_by_m5` is keyed by the M5 target's 1-based residue index, so a measured
/// entry whose `label_seq_id` starts at 2 and a prediction whose chain starts at 1 are addressed
/// identically and a comparison between them is a comparison of the same residues. A residue the
/// presentation does not resolve is simply absent from the map — never a zero, never a gap filled.
struct IndexedPresentation {
    name: String,
    group: String,
    seed: Option<i64>,
    measured_entry: Option<String>,
    ensemble_model: Option<i64>,
    environment: Environment,
    kind: OccurrenceKind,
    residue_by_m5: BTreeMap<u32, holonic_engine::physical_intake::mmcif::ResidueOccurrence>,
    places_by_m5: BTreeMap<u32, Vec<Rat>>,
    float_places_by_m5: BTreeMap<u32, [f64; 3]>,
    carries_binder: bool,
    intake_nanos: u128,
}

/// A decimal string as an exact rational: `"8.0"` is `80/10`, never `8.0f64`. The only decimal
/// this example parses outside the library's own `DecimalToken`, and it parses a *declaration*
/// (a deposited pH) rather than a coordinate.
fn exact_decimal(token: &str) -> Option<Rat> {
    let token = token.trim();
    let (sign, token) = match token.strip_prefix('-') {
        Some(rest) => (-1i64, rest),
        None => (1i64, token.strip_prefix('+').unwrap_or(token)),
    };
    let (whole, fraction) = match token.split_once('.') {
        Some((whole, fraction)) => (whole, fraction),
        None => (token, ""),
    };
    if whole.is_empty() && fraction.is_empty() {
        return None;
    }
    let digits = format!("{whole}{fraction}");
    if digits.is_empty() || !digits.bytes().all(|byte| byte.is_ascii_digit()) {
        return None;
    }
    let numerator = digits.parse::<BigInt>().ok()? * BigInt::from(sign);
    let denominator = BigInt::from(10u32).pow(fraction.len() as u32);
    Some(Rat::new(numerator, denominator))
}

fn field<'a>(entry: &'a Value, key: &str) -> Result<&'a Value, String> {
    entry
        .get(key)
        .ok_or_else(|| format!("the manifest entry carries no {key:?}"))
}

fn text(entry: &Value, key: &str) -> Result<String, String> {
    field(entry, key)?
        .as_str()
        .map(str::to_owned)
        .ok_or_else(|| format!("the manifest entry's {key:?} is not a string"))
}

fn copies_of(entry: &Value, key: &str) -> BTreeMap<String, u32> {
    entry
        .get(key)
        .and_then(Value::as_object)
        .map(|map| {
            map.iter()
                .filter_map(|(name, count)| {
                    count.as_u64().map(|count| (name.clone(), count as u32))
                })
                .collect()
        })
        .unwrap_or_default()
}

fn manifest_kind(entry: &Value) -> Result<OccurrenceKind, String> {
    let kind = field(entry, "occurrence_kind")?;
    if let Some(one) = kind.get("measured") {
        return Ok(OccurrenceKind::Measured {
            apparatus: one["apparatus"].as_str().unwrap_or_default().to_owned(),
        });
    }
    if let Some(one) = kind.get("predicted") {
        return Ok(OccurrenceKind::Predicted {
            predictor: one["predictor"].as_str().unwrap_or_default().to_owned(),
            seed: one["seed"].as_str().unwrap_or_default().to_owned(),
        });
    }
    if let Some(one) = kind.get("designed") {
        return Ok(OccurrenceKind::Designed {
            generator: one["generator"].as_str().unwrap_or_default().to_owned(),
            rounds: 0,
        });
    }
    Err("the manifest entry names no occurrence kind".to_owned())
}

fn manifest_assay(entry: &Value) -> Result<AssayFormat, String> {
    let assay = field(entry, "assay")?;
    if let Some(one) = assay.get("in_silico") {
        return Ok(AssayFormat::InSilicoPrediction {
            predictor: one["predictor"].as_str().unwrap_or_default().to_owned(),
            seed: one["seed"].as_str().unwrap_or_default().to_owned(),
        });
    }
    if let Some(one) = assay.get("declared") {
        return Ok(AssayFormat::Declared {
            description: one["description"].as_str().unwrap_or_default().to_owned(),
        });
    }
    Err("the manifest entry names no assay format".to_owned())
}

/// The typed environment index of one manifest entry. The same eight axes as above; the two the
/// 2026-09-19 presentations all left undeclared are **declared here wherever the deposition states
/// them**, so a measured crystal's pH really does enter and really does make the passage name that
/// axis.
fn manifest_environment(entry: &Value, presented: PresentedIndex) -> Result<Environment, String> {
    let with_ground = |value: CoordinateValue, ground: &str| {
        Coordinate::declared(value, ground).map_err(|error| error.to_string())
    };
    let undeclared = |why: &str| Coordinate::undeclared(why).map_err(|error| error.to_string());
    let name = text(entry, "name")?;
    let acidity = match entry.get("acidity").filter(|value| !value.is_null()) {
        Some(one) => {
            let p_h = one["p_h"].as_str().unwrap_or_default();
            let exact = exact_decimal(p_h)
                .ok_or_else(|| format!("{name}: the declared pH {p_h:?} is not an exact decimal"))?;
            with_ground(
                CoordinateValue::Acidity(Acidity {
                    p_h: ExactInterval::point(exact),
                    protonation_assumption: one["protonation_assumption"]
                        .as_str()
                        .unwrap_or_default()
                        .to_owned(),
                }),
                one["ground"].as_str().unwrap_or_default(),
            )?
        }
        None => undeclared(
            "this presentation records no pH and no protonation assumption: a structure predictor \
             emits none, the design pipeline records none, and a cryo-EM or NMR deposition states \
             none in the fields this intake reads. Inventing one would be a default",
        )?,
    };
    Environment::found(
        format!("{name} / typed environment index"),
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
                     carries that sequence over the residues it resolves, up to the monomer \
                     disagreements the staging record names one by one",
                )?,
            ),
            (
                CoordinateName::Conformation,
                with_ground(
                    CoordinateValue::Conformation(text(entry, "conformation")?),
                    &text(entry, "conformation_ground")?,
                )?,
            ),
            (
                CoordinateName::OligomericState,
                with_ground(
                    CoordinateValue::OligomericState(OligomericState {
                        copies: copies_of(entry, "oligomeric_copies"),
                    }),
                    "the polymer entities the source states are present — for a measured entry the \
                     whole deposited assembly, not only the chain that was staged for this receiver",
                )?,
            ),
            (CoordinateName::Acidity, acidity),
            (
                CoordinateName::Solvation,
                undeclared(
                    "no membrane or buffer context is recorded: a crystallisation liquor is the \
                     condition the crystal grew in and not a solvation context of the refined \
                     coordinates, and the absence of a lipid component in a predicted file is not \
                     a declaration of solubility",
                )?,
            ),
            (
                CoordinateName::Cofactors,
                with_ground(
                    CoordinateValue::Cofactors(LigandComplement {
                        copies: copies_of(entry, "cofactors"),
                    }),
                    &text(entry, "cofactor_ground")?,
                )?,
            ),
            (
                CoordinateName::Assay,
                with_ground(CoordinateValue::Assay(manifest_assay(entry)?), &text(entry, "assay_ground")?)?,
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

/// Mount one manifest entry and index it by the M5 target's residue numbering.
fn mount_indexed(entry: &Value, ordinal: u64) -> Result<IndexedPresentation, String> {
    let started = Instant::now();
    let name = text(entry, "name")?;
    let path = PathBuf::from(text(entry, "file")?);
    let structure = StructurePresentation::read(&path)
        .map_err(|error| format!("{}: {error}", path.display()))?;

    // The object check. A prediction or the design is addressed exactly as it was yesterday, by
    // the M5 object's own monomer count; a measured entry, which resolves fewer residues than the
    // object has, is addressed by the deposition's own `label_asym_id` and the staging record's
    // ungapped offset — both of which the staging script checked monomer by monomer.
    let target = match entry
        .get("target_chain_label_asym_id")
        .and_then(Value::as_str)
    {
        Some(label) => structure
            .chain(label)
            .map_err(|error| format!("{name}: chain {label}: {error}"))?
            .clone(),
        None => structure
            .chain_with_residue_count(TARGET_RESIDUES)
            .map_err(|error| format!("{name}: target chain ({TARGET_RESIDUES} residues): {error}"))?
            .clone(),
    };
    let offset = entry
        .get("label_seq_id_to_m5_offset")
        .and_then(Value::as_i64)
        .unwrap_or(0) as i32;
    let carries_binder = entry
        .get("carries_binder")
        .and_then(Value::as_bool)
        .unwrap_or(false);

    let mut residue_by_m5 = BTreeMap::new();
    let mut places_by_m5 = BTreeMap::new();
    let mut float_places_by_m5 = BTreeMap::new();
    for residue in &target.residues {
        let at = residue.source_ordinal + offset;
        if at < 1 || at as usize > TARGET_RESIDUES {
            continue;
        }
        let Some(position) = residue
            .labelled_atom(REPRESENTATIVE)
            .map_err(|error| format!("{name}: {error}"))?
        else {
            continue;
        };
        let atom = &residue.atoms[position];
        places_by_m5.insert(
            at as u32,
            vec![
                atom.x.exact_centre().map_err(|e| e.to_string())?,
                atom.y.exact_centre().map_err(|e| e.to_string())?,
                atom.z.exact_centre().map_err(|e| e.to_string())?,
            ],
        );
        if let (Ok(x), Ok(y), Ok(z)) = (
            atom.x.token.parse::<f64>(),
            atom.y.token.parse::<f64>(),
            atom.z.token.parse::<f64>(),
        ) {
            float_places_by_m5.insert(at as u32, [x, y, z]);
        }
        residue_by_m5.insert(at as u32, residue.clone());
    }

    let tokens = residue_by_m5
        .values()
        .map(|residue| TokenAddress {
            chain: target.label_asym_id.clone(),
            residue: residue.source_ordinal,
            entity: target.entity.clone(),
        })
        .collect::<Vec<_>>();
    let ecology = field(entry, "ecology")?;
    let lineage = field(entry, "lineage")?;
    let presented = PresentedIndex::declared(
        text(entry, "declaration")?,
        TargetEcology {
            target: ecology["target"].as_str().unwrap_or_default().to_owned(),
            target_form: ecology["target_form"].as_str().unwrap_or_default().to_owned(),
            stoichiometry: ecology["stoichiometry"].as_str().unwrap_or_default().to_owned(),
            cofolding_model: ecology["cofolding_model"].as_str().unwrap_or_default().to_owned(),
        },
        DesignLineage {
            design_uuid: lineage["design_uuid"].as_str().unwrap_or_default().to_owned(),
            design_name: lineage["design_name"].as_str().unwrap_or_default().to_owned(),
            seed: lineage["seed"].as_str().unwrap_or_default().to_owned(),
        },
        tokens,
    )
    .map_err(|error| format!("{name}: {error}"))?;

    Ok(IndexedPresentation {
        name: name.clone(),
        group: text(entry, "group")?,
        seed: entry.get("seed").and_then(Value::as_i64),
        measured_entry: entry
            .get("measured_entry")
            .and_then(Value::as_str)
            .map(str::to_owned),
        ensemble_model: entry.get("ensemble_model").and_then(Value::as_i64),
        environment: manifest_environment(entry, presented)?,
        kind: manifest_kind(entry)?,
        residue_by_m5,
        places_by_m5,
        float_places_by_m5,
        carries_binder,
        intake_nanos: started.elapsed().as_nanos(),
    })
    .map(|mut one| {
        let _ = ordinal;
        one.name = name;
        one
    })
}

/// The presentation's chain restricted to a declared M5 residue list, renumbered so that the
/// component's own ordinals **are** the M5 residue indices.
fn restricted_chain(
    one: &IndexedPresentation,
    residues: &[u32],
) -> Result<ChainOccurrence, String> {
    let mut kept = Vec::with_capacity(residues.len());
    for at in residues {
        let residue = one
            .residue_by_m5
            .get(at)
            .ok_or_else(|| format!("{}: M5 residue {at} is not resolved", one.name))?;
        let mut residue = residue.clone();
        residue.source_ordinal = *at as i32;
        kept.push(residue);
    }
    let atom_occurrences = kept.iter().map(|residue| residue.atoms.len()).sum();
    Ok(ChainOccurrence {
        label_asym_id: "RBX1".to_owned(),
        entity: None,
        residues: kept,
        atom_occurrences,
    })
}

fn no_uncertainty(pairs: &[(u32, u32)]) -> BTreeMap<(u32, u32), PairUncertainty> {
    pairs
        .iter()
        .map(|pair| {
            (
                *pair,
                PairUncertainty {
                    source_lineage: "declared: this receiver reads no directional uncertainty, \
                                     and a zero-width statement of that is not an uncertainty claim"
                        .to_owned(),
                    row_given_column_bits: 0,
                    column_given_row_bits: 0,
                    row_given_column: ExactInterval::point(Rat::from_integer(BigInt::from(0))),
                    column_given_row: ExactInterval::point(Rat::from_integer(BigInt::from(0))),
                    row_given_column_ulp: Rat::from_integer(BigInt::from(0)),
                    column_given_row_ulp: Rat::from_integer(BigInt::from(0)),
                },
            )
        })
        .collect()
}

/// One presentation's **within-component** alpha-carbon contact family over a declared residue
/// list, together with the topological receiver's reading of the same complex.
///
/// [definition] The classes are enacted by `enacted_within_component_classes` and audited by
/// `found_within_component_contact_family`; nothing about them is supplied here. The pair
/// population is `C(n − k + 1, 2)` for the declared separation `k`, computed by the owner.
fn within_component_reading(
    one: &IndexedPresentation,
    residues: &[u32],
    separation: u32,
    ordinal: u64,
    scope: &str,
) -> Result<(SituatedFamily, Value), String> {
    let chain = restricted_chain(one, residues)?;
    let grain = ComponentGrain::Representative {
        atom_label: REPRESENTATIVE.to_owned(),
    };
    let lineage = format!("{} / {scope}", one.name);
    let material = component_material(&chain, &lineage, &grain, RESIDENT_DECIMAL_PLACES)
        .map_err(|error| format!("{}: {error}", one.name))?;
    let mut complex = found_constraint_complex(&lineage, EventId(ordinal), vec![material], Vec::new())
        .map_err(|error| format!("{}: {error}", one.name))?;
    let component = ConstraintComponentId(1);
    let aperture = aperture();
    let started = Instant::now();
    let enacted = enacted_within_component_classes(&complex, component, separation, &aperture)
        .map_err(|error| format!("{}: {error}", one.name))?;
    let pairs = complex
        .within_component_pairs(component, separation)
        .map_err(|error| format!("{}: {error}", one.name))?;
    complex
        .found_within_component_contact_family(
            component,
            separation,
            aperture.clone(),
            &enacted,
            &no_uncertainty(&pairs),
        )
        .map_err(|error| format!("{}: {error}", one.name))?;
    let family_nanos = started.elapsed().as_nanos();

    // Receiver 4 — the topological one, on exactly this complex: the aperture filtration truncated
    // at the same 8 Å squared ceiling and at top grade 1, so the reading is the contact graph's
    // own connected components and independent cycles, exactly, over ℚ.
    let started = Instant::now();
    let topology = match ApertureFiltration::from_presented(
        &complex,
        int(CONTACT_SQUARED),
        1,
        TOPOLOGY_CELL_BOUND,
    ) {
        Ok(filtration) => match FiltrationOrder::found(&filtration, &OrderLaw::ByLowerBound) {
            Ok(order) => match persistence(
                &filtration,
                &order,
                &Coefficients::Rational,
                PERSISTENCE_WORK_BOUND,
            ) {
                Ok(reading) => json!({
                    "cells": filtration.cell_count(),
                    "order_is_determinate": filtration.order_is_determinate(),
                    "connected_components": reading.essential_count(0),
                    "independent_cycles": reading.essential_count(1),
                    "finite_pairs_grade_0": reading.pairs_at_grade(0).len(),
                    "nanos": started.elapsed().as_nanos(),
                }),
                Err(error) => json!({"refusal": error.to_string()}),
            },
            Err(error) => json!({"refusal": error.to_string()}),
        },
        Err(error) => json!({"refusal": error.to_string()}),
    };

    let occurrence = Occurrence::found(
        OccurrenceId(ordinal),
        one.kind.clone(),
        lineage.clone(),
        one.environment.clone(),
        complex,
    );
    let family = occurrence
        .founded_family(
            format!("the target chain's within-component alpha-carbon family at {scope}"),
            component,
            component,
        )
        .map_err(|error| format!("{}: {error}", one.name))?;
    let receipt = json!({
        "presentation": one.name,
        "scope": scope,
        "occurrences": residues.len(),
        "addressed_pairs": family.readings.len(),
        "classes": class_counts(&family),
        "topological_receiver": topology,
        "family_nanos": family_nanos,
    });
    Ok((family, receipt))
}

/// The rigidity Jacobian over a declared M5 residue list. A step is **polygonal only when the two
/// occurrences are consecutive in the M5 index**: a measured structure with an unresolved loop has
/// a jump there, and calling that jump a backbone bond would invent a constraint no presentation
/// carries. Every other pair inside the exact aperture is an admitted contact, as above.
fn indexed_jacobian(
    lineage: &str,
    one: &IndexedPresentation,
    residues: &[u32],
) -> Result<RigidityJacobian, String> {
    let places = residues
        .iter()
        .map(|at| {
            one.places_by_m5
                .get(at)
                .cloned()
                .ok_or_else(|| format!("{}: M5 residue {at} is not resolved", one.name))
        })
        .collect::<Result<Vec<_>, String>>()?;
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
    for left in 0..residues.len() {
        for right in (left + 1)..residues.len() {
            let backbone = residues[right] == residues[left] + 1;
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

/// `(agreeing, separating, open-carrying)` between two members of one fibre, by name.
fn separator_row(
    fibre: &PluralFibre,
    names: &[String],
    left: usize,
    right: usize,
) -> Result<Value, String> {
    let separator = fibre
        .separator_between(left, right)
        .map_err(|error| error.to_string())?;
    Ok(json!({
        "left": names[left],
        "right": names[right],
        "agreeing": separator.agreeing,
        "separating": separator.separating.len(),
        "open_carrying": separator.open_carrying.len(),
        "indistinguishable": separator.is_empty(),
    }))
}

/// The five-number summary of a population of separating counts. Integers throughout: these are
/// counts of exactly classified contacts, not statistics of a float.
fn spread(values: &mut Vec<usize>) -> Value {
    values.sort_unstable();
    if values.is_empty() {
        return json!({"population": 0});
    }
    let at = |q: usize| values[(values.len() - 1) * q / 4];
    json!({
        "population": values.len(),
        "minimum": values[0],
        "lower_quartile": at(1),
        "median": at(2),
        "upper_quartile": at(3),
        "maximum": values[values.len() - 1],
        "total": values.iter().sum::<usize>(),
    })
}

fn argument(args: &[String], flag: &str, fallback: &str) -> String {
    args.windows(2)
        .find(|pair| pair[0] == flag)
        .map(|pair| pair[1].clone())
        .unwrap_or_else(|| fallback.to_owned())
}

/// **The 2026-09-20 reading**: measured presentations, zinc, and the seed population, at the
/// within-component contact receiver, the rigidity receiver, the topological receiver and the
/// exterior baseline, over the declared commonly resolved residue range.
fn measured_and_population(manifest_path: &Path, whole_range: bool) -> Result<Value, String> {
    let whole = Instant::now();
    let manifest: Value = serde_json::from_str(
        &std::fs::read_to_string(manifest_path).map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())?;
    let separation = manifest
        .get("minimum_chain_separation")
        .and_then(Value::as_u64)
        .unwrap_or(DEFAULT_MINIMUM_SEPARATION as u64) as u32;
    let residues_of = |key: &str| -> Vec<u32> {
        manifest
            .get(key)
            .and_then(Value::as_array)
            .map(|rows| rows.iter().filter_map(Value::as_u64).map(|at| at as u32).collect())
            .unwrap_or_default()
    };
    // Two declared scopes. `resolved` is every M5 residue every measured model resolves; `typed`
    // additionally drops the residues at which some measured entry carries a different monomer —
    // the solution-NMR construct's four solubilizing substitutions and its N-terminal linker.
    let resolved = residues_of("commonly_resolved_m5_residues");
    let typed = residues_of("commonly_resolved_and_identically_typed_m5_residues");
    let differing = residues_of("m5_residues_whose_monomer_differs_in_some_measured_entry");

    // ------------------------------------------------------------------------------- the intake
    let entries = manifest
        .get("presentations")
        .and_then(Value::as_array)
        .ok_or("the manifest carries no presentations")?;
    let mut mounted: Vec<IndexedPresentation> = Vec::new();
    let mut intake_rows = Vec::new();
    for (at, entry) in entries.iter().enumerate() {
        match mount_indexed(entry, at as u64 + 1) {
            Ok(one) => {
                intake_rows.push(json!({
                    "presentation": one.name,
                    "group": one.group,
                    "admitted": true,
                    "seed": one.seed,
                    "ensemble_model": one.ensemble_model,
                    "file": entry.get("file"),
                    "residues_resolved_in_the_m5_index": one.places_by_m5.len(),
                    "first_m5_residue": one.places_by_m5.keys().next(),
                    "last_m5_residue": one.places_by_m5.keys().next_back(),
                    "carries_the_binder_chain": one.carries_binder,
                    "environment_undeclared_axes": one.environment.undeclared_names().iter()
                        .map(|name| name.label()).collect::<Vec<_>>(),
                    "nanos": one.intake_nanos,
                }));
                eprintln!("[2026-09-20 intake] {} admitted", one.name);
                mounted.push(one);
            }
            Err(refusal) => {
                eprintln!("[2026-09-20 intake] REFUSED: {refusal}");
                intake_rows.push(json!({
                    "presentation": entry.get("name"),
                    "admitted": false,
                    "refusal": refusal,
                }));
            }
        }
    }

    // ------------------------------------------------- the within-component family at each scope
    // ------------------------------------------------ the join: the chain reading, measured too
    //
    // `--chain-join` takes ONLY this reading and returns: the theorem-backed chain reading (wave 9)
    // on three consecutive, commonly resolved M5 windows — arm 21–32, core 41–52, core 41–63 — for
    // every measured reference (first model of an ensemble), the design, both Protenix runs and
    // seed 0 of each predicted condition. The hinge is each presentation's own minimal-section cut.
    if std::env::args().any(|flag| flag == "--chain-join") {
        let windows: [(&str, Vec<u32>); 3] = [
            ("arm-21-32", (21..=32).collect()),
            ("core-41-52", (41..=52).collect()),
            ("core-41-63", (41..=63).collect()),
        ];
        let mut rows = Vec::new();
        for (label, residues) in &windows {
            for one in &mounted {
                if !(one.seed.unwrap_or(0) == 0 && one.ensemble_model.unwrap_or(1) == 1) {
                    continue;
                }
                let lineage = format!("{}|rbx1|{label}", one.name);
                eprintln!("[chain-join] {} {label}", one.name);
                let row = indexed_jacobian(&lineage, one, residues)
                    .and_then(|jacobian| chain_block(&one.name, &jacobian));
                rows.push(match row {
                    Ok(mut receipt) => {
                        receipt["window"] = json!(label);
                        receipt["group"] = json!(one.group);
                        receipt
                    }
                    Err(refusal) => json!({
                        "presentation": one.name, "window": label, "refusal": refusal,
                    }),
                });
            }
        }
        return Ok(json!({ "schema": "m5-chain-join/1", "intake": intake_rows, "chain_join": rows }));
    }

    let mut scope_rows = Vec::new();
    let mut ordinal = 1_000_u64;
    let mut typed_families: Vec<(String, String, SituatedFamily)> = Vec::new();
    for (scope, residues) in [
        ("commonly-resolved", &resolved),
        ("commonly-resolved-and-identically-typed", &typed),
    ] {
        if residues.is_empty() {
            continue;
        }
        let started = Instant::now();
        let mut per_presentation = Vec::new();
        let mut families: Vec<(String, String, SituatedFamily)> = Vec::new();
        for one in &mounted {
            ordinal += 1;
            match within_component_reading(one, residues, separation, ordinal, scope) {
                Ok((family, receipt)) => {
                    per_presentation.push(receipt);
                    families.push((one.name.clone(), one.group.clone(), family));
                }
                Err(refusal) => per_presentation.push(json!({
                    "presentation": one.name, "scope": scope, "refusal": refusal,
                })),
            }
        }
        let intake_nanos = started.elapsed().as_nanos();

        // The typed refusal first: at the commonly-resolved scope the NMR construct's monomers
        // differ, so the fibre is not over one object and the owner says so by name.
        let whole_fibre =
            PluralFibre::over_one_candidate(families.iter().map(|(_, _, f)| f.clone()).collect());
        let refusal = whole_fibre.as_ref().err().map(|error| error.to_string());

        // The fibre over the members that do share one kinship with the design.
        let reference_kinship = families
            .iter()
            .find(|(name, _, _)| name == "designed")
            .map(|(_, _, family)| family.kinship());
        let admitted: Vec<(String, String, SituatedFamily)> = match &reference_kinship {
            Some(kinship) => families
                .iter()
                .filter(|(_, _, family)| family.kinship() == *kinship)
                .cloned()
                .collect(),
            None => families.clone(),
        };
        let excluded: Vec<&str> = families
            .iter()
            .filter(|(name, _, _)| !admitted.iter().any(|(other, _, _)| other == name))
            .map(|(name, _, _)| name.as_str())
            .collect();

        let names: Vec<String> = admitted.iter().map(|(name, _, _)| name.clone()).collect();
        let groups: Vec<String> = admitted.iter().map(|(_, group, _)| group.clone()).collect();
        let fibre = PluralFibre::over_one_candidate(
            admitted.iter().map(|(_, _, family)| family.clone()).collect(),
        )
        .map_err(|error| format!("the {scope} fibre refuses: {error}"))?;
        let started = Instant::now();
        let partition = fibre.partition();
        let mut role_totals: BTreeMap<&'static str, usize> = BTreeMap::new();
        for pair in fibre.addressed() {
            *role_totals
                .entry(fibre.role_of(pair).map_err(|e| e.to_string())?.label())
                .or_default() += 1;
        }
        // Every ordered pair's separator, by name, plus the three spreads the question needs.
        let mut pairwise = Vec::new();
        let mut within_group: BTreeMap<String, Vec<usize>> = BTreeMap::new();
        let mut between_groups: BTreeMap<String, Vec<usize>> = BTreeMap::new();
        for left in 0..names.len() {
            for right in (left + 1)..names.len() {
                let row = separator_row(&fibre, &names, left, right)?;
                let count = row["separating"].as_u64().unwrap_or(0) as usize;
                if groups[left] == groups[right] {
                    within_group.entry(groups[left].clone()).or_default().push(count);
                } else {
                    let key = if groups[left] <= groups[right] {
                        format!("{} vs {}", groups[left], groups[right])
                    } else {
                        format!("{} vs {}", groups[right], groups[left])
                    };
                    between_groups.entry(key).or_default().push(count);
                }
                pairwise.push(row);
            }
        }
        let pairwise_nanos = started.elapsed().as_nanos();

        // Systematic against sampling: for each measured reference and each predicted group, the
        // contacts on which EVERY member of the group differs from the reference (a systematic
        // disagreement of that condition) against those on which the members split (sampling).
        let mut systematic = Vec::new();
        for (reference_at, reference_name) in names.iter().enumerate() {
            if !reference_name.starts_with("measured-") {
                continue;
            }
            let mut by_group: BTreeMap<&str, Vec<usize>> = BTreeMap::new();
            for (at, group) in groups.iter().enumerate() {
                if group.starts_with("boltz2-") || group == "designed" || group.starts_with("protenix") {
                    by_group.entry(group.as_str()).or_default().push(at);
                }
            }
            for (group, members) in by_group {
                if members.len() < 2 {
                    continue;
                }
                let reference = &admitted[reference_at].2;
                let mut unanimous = 0usize;
                let mut flipping = 0usize;
                let mut open = 0usize;
                for at in 0..reference.readings.len() {
                    let Some(base) = DecidedClass::of(reference.readings[at].class) else {
                        open += 1;
                        continue;
                    };
                    let mut differs = 0usize;
                    let mut decided = 0usize;
                    for member in &members {
                        match DecidedClass::of(admitted[*member].2.readings[at].class) {
                            None => {}
                            Some(class) => {
                                decided += 1;
                                if class != base {
                                    differs += 1;
                                }
                            }
                        }
                    }
                    if differs == 0 {
                        continue;
                    }
                    if differs == decided {
                        unanimous += 1;
                    } else {
                        flipping += 1;
                    }
                }
                systematic.push(json!({
                    "measured_reference": reference_name,
                    "group": group,
                    "members": members.len(),
                    "separating_unanimously_across_the_population": unanimous,
                    "separating_but_flipping_between_members": flipping,
                    "reference_open_readings": open,
                }));
            }
        }

        // Issue #9 — the held-out agreement count over a declared receiver FAMILY, taken over the
        // seed population by `evaluation_discipline`'s own leave-one-out shape: the disagreement
        // subsets are computed on the development side (the population minus the held-out member)
        // and the held-out member is scored at them, so nothing it carries entered the fitting.
        let mut held_out_rows = Vec::new();
        let mut by_group: BTreeMap<&str, Vec<usize>> = BTreeMap::new();
        for (at, group) in groups.iter().enumerate() {
            by_group.entry(group.as_str()).or_default().push(at);
        }
        for (group, members) in &by_group {
            if members.len() < 3 {
                continue;
            }
            for held in members {
                let development: Vec<SituatedFamily> = members
                    .iter()
                    .filter(|at| *at != held)
                    .map(|at| admitted[*at].2.clone())
                    .collect();
                let development_fibre = PluralFibre::over_one_candidate(development)
                    .map_err(|error| error.to_string())?;
                let subsets = disagreement_subsets(&development_fibre);
                let held_family = &admitted[*held].2;
                let classes: BTreeMap<(u32, u32), Option<DecidedClass>> = held_family
                    .readings
                    .iter()
                    .map(|reading| (reading.pair, DecidedClass::of(reading.class)))
                    .collect();
                // `performance_on` takes a total map; a held-out reading that is itself open is a
                // reading the held-out member does not decide, and it is counted separately below
                // rather than being given a class it does not have.
                let held_open = classes.values().filter(|class| class.is_none()).count();
                let predictor = |pair: (u32, u32)| -> DecidedClass {
                    classes
                        .get(&pair)
                        .copied()
                        .flatten()
                        .unwrap_or(DecidedClass::Excluded)
                };
                let mut per_subset = Vec::new();
                for subset in [DisagreementClass::Unanimous, DisagreementClass::Separating] {
                    let performance =
                        performance_on(&development_fibre, &subsets, subset, &predictor)
                            .map_err(|error| error.to_string())?;
                    per_subset.push(json!({
                        "subset": format!("{subset:?}"),
                        "population": performance.population,
                        "agreeing": performance.agreeing,
                        "disagreeing": performance.disagreeing,
                        "carried_open": performance.carried_open,
                    }));
                }
                held_out_rows.push(json!({
                    "group": group,
                    "held_out": names[*held],
                    "development_members": members.len() - 1,
                    "contact_receiver": per_subset,
                    "held_out_open_readings": held_open,
                }));
            }
        }

        scope_rows.push(json!({
            "scope": scope,
            "residues": residues.len(),
            "first_residue": residues.first(),
            "last_residue": residues.last(),
            "minimum_chain_separation": separation,
            "addressed_pairs": fibre.contacts(),
            "members": names,
            "refused_at_the_whole_fibre": refusal,
            "excluded_by_object_kinship": excluded,
            "per_presentation": per_presentation,
            "fibre_roles": role_totals,
            "fibre_is_a_partition": partition.is_a_partition(),
            "pairwise": pairwise,
            "seed_spread_within_each_group": within_group
                .iter()
                .map(|(group, values)| json!({"group": group, "separating": spread(&mut values.clone())}))
                .collect::<Vec<_>>(),
            "separation_between_groups": between_groups
                .iter()
                .map(|(pair, values)| json!({"pair": pair, "separating": spread(&mut values.clone())}))
                .collect::<Vec<_>>(),
            "systematic_against_sampling": systematic,
            "held_out_agreement_contact_receiver": held_out_rows,
            "nanos": {"intake_and_families": intake_nanos, "pairwise": pairwise_nanos},
        }));
        if scope == "commonly-resolved-and-identically-typed" {
            typed_families = families;
        }
    }

    // --------------------------------------------- the rigidity and topological receivers, windowed
    let arm: Vec<u32> = typed.iter().copied().filter(|at| *at <= 40).collect();
    let core: Vec<u32> = typed.iter().copied().filter(|at| *at > 40 && *at <= 80).collect();
    let mut windows: Vec<(&str, Vec<u32>)> = vec![
        ("arm-1-40-intersect-common", arm),
        ("core-41-80-intersect-common", core),
    ];
    if whole_range {
        windows.push(("whole-commonly-resolved-and-typed", typed.clone()));
    }
    let mut rigidity_rows = Vec::new();
    for (label, residues) in &windows {
        if residues.len() < 4 {
            continue;
        }
        for one in &mounted {
            // The whole commonly resolved range is 237 exact coordinates and the exact RREF's cost
            // grows with the elimination work AND with coefficient growth, so it is taken on a
            // declared short list — every measured reference, the design, both Protenix runs and
            // seed 0 of each predicted condition — and the cost of that is the reported cost.
            if *label == "whole-commonly-resolved-and-typed"
                && !(one.seed.unwrap_or(0) == 0 && one.ensemble_model.unwrap_or(1) == 1)
            {
                continue;
            }
            let jacobian = match indexed_jacobian(
                &format!("{}|rbx1|{label}", one.name),
                one,
                residues,
            ) {
                Ok(jacobian) => jacobian,
                Err(refusal) => {
                    rigidity_rows.push(json!({
                        "presentation": one.name, "window": label, "refusal": refusal,
                    }));
                    continue;
                }
            };
            eprintln!("[2026-09-20 rigidity] {} {label}", one.name);
            match rigidity_block(&one.name, &jacobian) {
                Ok((mut receipt, _)) => {
                    receipt["window"] = json!(label);
                    receipt["group"] = json!(one.group);
                    receipt["window_residues"] = json!(residues.len());
                    rigidity_rows.push(receipt);
                }
                Err(refusal) => rigidity_rows.push(json!({
                    "presentation": one.name, "window": label, "refusal": refusal,
                })),
            }
        }
    }

    // #9's family fold: at each window, which rigidity invariants the development side is
    // unanimous on, and whether the held-out member agrees at every one of them. The family count
    // is the conjunction of the contact receiver's held-out agreement and this one.
    let mut rigidity_family = Vec::new();
    for (label, _) in &windows {
        let mut by_group: BTreeMap<String, Vec<&Value>> = BTreeMap::new();
        for row in &rigidity_rows {
            if row.get("window").and_then(Value::as_str) != Some(label) {
                continue;
            }
            if let Some(group) = row.get("group").and_then(Value::as_str) {
                by_group.entry(group.to_owned()).or_default().push(row);
            }
        }
        let invariants = [
            "rank_jacobian",
            "motion_dimension",
            "internal_motion_dimension",
            "self_stress_dimension",
            "rigid_clusters",
            "constraints",
        ];
        for (group, rows) in by_group {
            if rows.len() < 3 {
                continue;
            }
            for held in 0..rows.len() {
                let mut unanimous = 0usize;
                let mut agreeing = 0usize;
                let mut per_invariant = BTreeMap::new();
                for name in invariants {
                    let values: BTreeSet<i64> = rows
                        .iter()
                        .enumerate()
                        .filter(|(at, _)| *at != held)
                        .filter_map(|(_, row)| row.get(name).and_then(Value::as_i64))
                        .collect();
                    if values.len() != 1 {
                        per_invariant.insert(name, "development-side-is-not-unanimous");
                        continue;
                    }
                    unanimous += 1;
                    if rows[held].get(name).and_then(Value::as_i64) == values.iter().next().copied()
                    {
                        agreeing += 1;
                        per_invariant.insert(name, "agrees");
                    } else {
                        per_invariant.insert(name, "separates");
                    }
                }
                rigidity_family.push(json!({
                    "window": label,
                    "group": group,
                    "held_out": rows[held].get("presentation"),
                    "development_members": rows.len() - 1,
                    "invariants_addressed": invariants.len(),
                    "invariants_the_development_side_is_unanimous_on": unanimous,
                    "held_out_agrees_at": agreeing,
                    "held_out_separates_at": unanimous - agreeing,
                    "per_invariant": per_invariant,
                }));
            }
        }
    }

    // ---------------------------------------------------------------------------------- issue #9
    // **The held-out agreement count over the declared receiver FAMILY.**
    //
    // [definition] The family is `contact ∧ rigidity ∧ topological`, all three read on the same
    // 79 commonly resolved and identically typed residues of the target chain. For each held-out
    // member `h` of a population `P`, the development side is `P \ {h}`; an *addressed family
    // item* is a contact the development side classifies unanimously, or a rigidity invariant it
    // reads unanimously, or a topological invariant it reads unanimously. The count is how many of
    // those items `h` agrees at. Nothing about the three receivers' readings is supplied: the
    // contact subsets come from `evaluation_discipline::disagreement_subsets` over the development
    // fibre and the score from `performance_on`; the rigidity and topological readings are the
    // owners' own.
    //
    // **What it cannot say.** It is agreement between presentations of one object, never
    // realization: nothing here says any member is right. The development side's unanimity is a
    // property of this finite sample, so an item it splits on is excluded from the count by
    // construction — and on the development-*separating* subset `performance_on` necessarily
    // returns zero agreeing, because a single class cannot equal two different ones. That zero is
    // a structural fact about the subset and is not a result.
    let mut family_rows = Vec::new();
    {
        let typed_scope = scope_rows
            .iter()
            .find(|row| row["scope"] == "commonly-resolved-and-identically-typed");
        let contact_rows: Vec<&Value> = typed_scope
            .and_then(|row| row["held_out_agreement_contact_receiver"].as_array())
            .map(|rows| rows.iter().collect())
            .unwrap_or_default();
        // The topological receiver's two integer invariants, by presentation.
        let mut topology: BTreeMap<String, (Option<i64>, Option<i64>)> = BTreeMap::new();
        let mut group_of: BTreeMap<String, String> = BTreeMap::new();
        for one in &mounted {
            group_of.insert(one.name.clone(), one.group.clone());
        }
        if let Some(rows) = typed_scope.and_then(|row| row["per_presentation"].as_array()) {
            for row in rows {
                let Some(name) = row["presentation"].as_str() else {
                    continue;
                };
                let reading = &row["topological_receiver"];
                topology.insert(
                    name.to_owned(),
                    (
                        reading["connected_components"].as_i64(),
                        reading["independent_cycles"].as_i64(),
                    ),
                );
            }
        }
        for contact in &contact_rows {
            let Some(held) = contact["held_out"].as_str() else {
                continue;
            };
            let Some(group) = contact["group"].as_str() else {
                continue;
            };
            let unanimous_subset = contact["contact_receiver"]
                .as_array()
                .and_then(|rows| rows.iter().find(|row| row["subset"] == "Unanimous"))
                .cloned()
                .unwrap_or(Value::Null);
            let contact_addressed = unanimous_subset["population"].as_u64().unwrap_or(0) as usize;
            let contact_agreeing = unanimous_subset["agreeing"].as_u64().unwrap_or(0) as usize;

            let mut rigidity_addressed = 0usize;
            let mut rigidity_agreeing = 0usize;
            for row in &rigidity_family {
                if row["held_out"].as_str() == Some(held) {
                    rigidity_addressed += row["invariants_the_development_side_is_unanimous_on"]
                        .as_u64()
                        .unwrap_or(0) as usize;
                    rigidity_agreeing += row["held_out_agrees_at"].as_u64().unwrap_or(0) as usize;
                }
            }

            let siblings: Vec<&String> = group_of
                .iter()
                .filter(|(name, other)| other.as_str() == group && name.as_str() != held)
                .map(|(name, _)| name)
                .collect();
            let mut topological_addressed = 0usize;
            let mut topological_agreeing = 0usize;
            for axis in 0..2 {
                let values: BTreeSet<i64> = siblings
                    .iter()
                    .filter_map(|name| topology.get(*name))
                    .filter_map(|reading| if axis == 0 { reading.0 } else { reading.1 })
                    .collect();
                if values.len() != 1 {
                    continue;
                }
                topological_addressed += 1;
                let mine = topology
                    .get(held)
                    .and_then(|reading| if axis == 0 { reading.0 } else { reading.1 });
                if mine == values.iter().next().copied() {
                    topological_agreeing += 1;
                }
            }

            family_rows.push(json!({
                "receiver_family": ["contact", "rigidity", "topological"],
                "group": group,
                "held_out": held,
                "development_members": contact["development_members"],
                "contact": {"addressed": contact_addressed, "agreeing": contact_agreeing},
                "rigidity": {"addressed": rigidity_addressed, "agreeing": rigidity_agreeing},
                "topological": {
                    "addressed": topological_addressed, "agreeing": topological_agreeing,
                },
                "family_addressed": contact_addressed + rigidity_addressed + topological_addressed,
                "family_agreeing": contact_agreeing + rigidity_agreeing + topological_agreeing,
                "family_separating": (contact_addressed + rigidity_addressed
                    + topological_addressed)
                    - (contact_agreeing + rigidity_agreeing + topological_agreeing),
            }));
        }
    }

    // ------------------------------------------------------------- the exterior float baseline
    // Exterior, float, load-bearing for nothing: Cα RMSD after Kabsch superposition against each
    // measured reference over exactly the commonly resolved and identically typed residues.
    let mut baseline_rows = Vec::new();
    let references: Vec<&IndexedPresentation> = mounted
        .iter()
        .filter(|one| {
            one.measured_entry.is_some() && one.ensemble_model.unwrap_or(1) == 1
        })
        .collect();
    let float_on = |one: &IndexedPresentation, residues: &[u32]| -> Option<Vec<[f64; 3]>> {
        residues
            .iter()
            .map(|at| one.float_places_by_m5.get(at).copied())
            .collect()
    };
    for one in &mounted {
        let mut against = Vec::new();
        for reference in &references {
            let (Some(left), Some(right)) = (float_on(reference, &typed), float_on(one, &typed))
            else {
                continue;
            };
            let whole_rmsd = exterior_float_baseline::rmsd_after_superposition(&left, &right);
            let core_only: Vec<u32> = typed.iter().copied().filter(|at| *at > 40 && *at <= 80).collect();
            let arm_only: Vec<u32> = typed.iter().copied().filter(|at| *at <= 40).collect();
            let window_rmsd = |window: &[u32]| -> Option<f64> {
                let left = float_on(reference, window)?;
                let right = float_on(one, window)?;
                exterior_float_baseline::rmsd_after_superposition(&left, &right)
            };
            against.push(json!({
                "measured_reference": reference.name,
                "exterior_float_rmsd_angstrom_common_range": whole_rmsd,
                "exterior_float_rmsd_angstrom_core_41_80": window_rmsd(&core_only),
                "exterior_float_rmsd_angstrom_arm_1_40": window_rmsd(&arm_only),
            }));
        }
        baseline_rows.push(json!({
            "presentation": one.name,
            "group": one.group,
            "against_each_measured_reference": against,
        }));
    }

    // ------------------------------------------------ the typed refusal and the passage that lifts it
    let mut passage_rows = Vec::new();
    if let Some((reference_name, _, reference_family)) = typed_families
        .iter()
        .find(|(name, _, _)| name.starts_with("measured-3DPL"))
    {
        let reference_environment = mounted
            .iter()
            .find(|one| &one.name == reference_name)
            .map(|one| one.environment.clone());
        let mut seen: BTreeSet<&str> = BTreeSet::new();
        for (name, group, family) in &typed_families {
            if name == reference_name || !seen.insert(group.as_str()) {
                continue;
            }
            let Some(left_environment) = reference_environment.clone() else {
                continue;
            };
            let Some(right) = mounted.iter().find(|one| &one.name == name) else {
                continue;
            };
            let refusal = compare_here(reference_family, family)
                .err()
                .map(|error| error.to_string());
            let divergent = left_environment
                .disagreement(&right.environment)
                .names()
                .into_iter()
                .collect::<Vec<_>>();
            let passage = EnvironmentPassage::declare(
                format!(
                    "the measured RBX1 and {name} are the same target chain read under different \
                     declarations; the passage accounts for exactly the axes on which they diverge \
                     and returns the environment the measured claim was read at as its own residual"
                ),
                left_environment,
                right.environment.clone(),
                divergent,
            )
            .map_err(|error| error.to_string())?;
            let carried = compare_through(reference_family, family, &passage)
                .map_err(|error| error.to_string())?;
            passage_rows.push(json!({
                "left": reference_name,
                "right": name,
                "refusal_without_a_passage": refusal,
                "axes_the_passage_accounts_for": passage.accounted().iter()
                    .map(|name| name.label()).collect::<Vec<_>>(),
                "read_at_residual": carried.read_at.lineage,
                "pairs": carried.comparison.pairs,
                "agreeing": carried.comparison.agreeing,
                "separating": carried.comparison.separating.len(),
            }));
        }
    }

    Ok(json!({
        "schema": "holonics.m5-measured-zinc-and-seed-population.v1",
        "dated": "2026-09-20",
        "declared_scopes": {
            "minimum_chain_separation": separation,
            "commonly_resolved_m5_residues": resolved,
            "commonly_resolved_and_identically_typed_m5_residues": typed,
            "m5_residues_whose_monomer_differs_in_some_measured_entry": differing,
            "contact_aperture_squared_angstrom": CONTACT_SQUARED,
            "representative_atom": REPRESENTATIVE,
            "topology_top_grade": 1,
        },
        "intake": intake_rows,
        "within_component_contact_receiver": scope_rows,
        "rigidity_receiver_windows": rigidity_rows,
        "held_out_agreement_rigidity_receiver": rigidity_family,
        "held_out_agreement_over_the_receiver_family": family_rows,
        "what_the_family_count_cannot_say": [
            "it is agreement between presentations of one object at three receivers, never \
             realization: no member is said to be right",
            "an item the development side splits on is excluded by construction, so the count is \
             conditioned on this finite sample's unanimity",
            "on the development-separating contact subset `performance_on` necessarily returns \
             zero agreeing, because one class cannot equal two different ones; that zero is \
             structural and is not a result",
            "it is taken at one aperture, one representative atom, one residue range and one \
             chain separation, and says nothing outside them",
        ],
        "measured_passages": passage_rows,
        "exterior_float_baseline_against_the_measured_structures": baseline_rows,
        "whole_run_nanos": whole.elapsed().as_nanos(),
    }))
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
    // The 2026-09-20 section. It runs only when a manifest is named, so the 2026-09-19 command
    // line reproduces the 2026-09-19 reading unchanged.
    let manifest = argument(&args, "--manifest", "");
    if !manifest.is_empty() {
        let out2 = argument(
            &args,
            "--out-measured",
            "research/experiments/m5_predicted_vs_reference/measured_readings.json",
        );
        let started = Instant::now();
        let results = measured_and_population(
            Path::new(&manifest),
            args.iter().any(|flag| flag == "--whole-range-rigidity"),
        )?;
        let out2 = Path::new(&out2);
        if let Some(parent) = out2.parent() {
            std::fs::create_dir_all(parent).map_err(|error| error.to_string())?;
        }
        std::fs::write(
            out2,
            serde_json::to_string_pretty(&results).map_err(|error| error.to_string())?,
        )
        .map_err(|error| error.to_string())?;
        eprintln!(
            "[done 2026-09-20] {} in {:.1} s",
            out2.display(),
            started.elapsed().as_secs_f64()
        );
        if args.iter().any(|flag| flag == "--skip-2026-09-19") {
            return Ok(());
        }
    }
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
