//! **The conditioned RBX1 static response: a force this program declares, a displacement it
//! generates, and the measured quadrance change it is scored against.**
//!
//! Issue **#55**. Contract:
//! `docs/plans/THE_CONTINUING_OBJECT_IS_THE_SHARED_CARRIER.md#the-conditioned-structural-response-consumer`.
//! Experiment directory: `research/experiments/conditioned_rbx1_static_response/`.
//!
//! What this is: a **bounded elastic experiment**. The program declares a source configuration, an
//! elastic energy with its stiffness and units, a metric, a gauge and a forcing family; it solves
//! `K δq = f` on the complement of the *full* kernel; and it reads the result through an oriented
//! pairwise-quadrance receiver against structures already on disk. It is not general structure
//! prediction and it is not an admission test. **A failure is a result.**
//!
//! The order of this file is the order of the contract, and it is not an accident: everything in
//! §1–§4 is declared and printed **before** §5 reads a single comparison coordinate.
//!
//! ```text
//! cargo run --release -p holonic-engine \
//!     --example the_declared_force_returns_its_null_fibre_and_its_residual -- \
//!     --structure-root <M5_STRUCTURE_ROOT> \
//!     --contact-support research/experiments/conditioned_rbx1_static_response/contact_support.json \
//!     --out research/experiments/conditioned_rbx1_static_response/results.json
//! ```
//!
//! **No `f32` and no `f64` occurs anywhere in this file.** Exterior decimals are rendered from
//! exact rationals by integer division and are labelled `exterior_decimal_*`; costs are whole
//! milliseconds. Nothing exterior decides anything.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::time::Instant;

use num_bigint::BigInt;
use num_traits::{One, Zero};
use relational_geometry::Rat;
use serde_json::{json, Map, Value};

use holonic_engine::conditioned_static_response::{
    BlockCorrespondence, ConditionedStiffness, DeclaredMetric, ElasticDeclaration,
    ForcingDeclaration, NullFibre, OrientedAgreement, QuadranceResponse, ResponseFamilyReading,
    ResponseGauge, StaticResponse,
};
use holonic_engine::physical_constraint_complex::{ConstraintEdge, ConstraintVertexId};
use holonic_engine::physical_constraint_grading::EdgeProvenance;
use holonic_engine::physical_intake::mmcif::{ChainOccurrence, StructurePresentation};
use holonic_engine::rigidity_receiver::{
    rigidity_reading, ExactConfiguration, RigidityJacobian, TrivialMotionReading,
};

// -------------------------------------------------------------------------------------------
// §0. the declared constants, all of them before anything runs
// -------------------------------------------------------------------------------------------

/// The representative atom. One alpha carbon per residue, exactly as the M5 experiment's intake.
const REPRESENTATIVE: &str = "CA";

/// The elastic contact aperture **inside** the window, in angstroms. The same exact 8 Å alpha-carbon
/// aperture the M5 experiment declares for its contact receiver, reused here as the support of the
/// elastic network so the two readings address the same contacts.
const ELASTIC_APERTURE: i64 = 8;

/// The source: 2LGV, solution NMR, RBX1 **alone** — the only measured presentation in the M5
/// search with no cullin partner, which is what makes it a free-state source configuration.
const SOURCE_ENTRY: &str = "2LGV";
const SOURCE_CHAIN: &str = "A";
const SOURCE_OFFSET: i32 = 8;
const SOURCE_MODELS: u32 = 20;

/// The comparison structures, held out until §5.
const HELD_OUT: [(&str, &str, i32, &str); 2] = [
    (
        "3DPL",
        "B",
        2,
        "X-ray 2.6 A, RBX1 bound to cullin-5, pH 8.0 at 277 K",
    ),
    (
        "7Z8R",
        "C",
        2,
        "cryo-EM 2.7 A, RBX1 in the CUL1/CAND1 assembly, pH undeclared",
    ),
];

/// The two established windows, in M5 residue numbering.
const WINDOWS: [(&str, i32, i32); 2] = [("n_terminal_arm", 21, 38), ("ring_core", 41, 80)];

/// The residues 2LGV substitutes to keep RBX1 soluble without a cullin: `W27S, V30S, L32Q, W33S`
/// (and the `GGG` linker at 9–11, outside both windows). A pair touching one of these is a
/// *chemical* difference as well as a conformational one, and the receiver reports a scope with
/// them and a scope without them rather than smoothing the difference away.
const SOURCE_SUBSTITUTIONS: [i32; 4] = [27, 30, 32, 33];

/// The minimum chain separation the M5 receiver declares: `i,i+1` and `i,i+2` are inside any
/// protein aperture whatever the fold does.
const MINIMUM_SEPARATION: i32 = 3;

fn integer(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

/// An **exterior** decimal rendering of an exact rational, by integer division. No float is formed
/// and nothing downstream reads it.
fn exterior_decimal(value: &Rat, places: u32) -> String {
    let scale = BigInt::from(10u32).pow(places);
    let numerator = value.numer() * &scale;
    let denominator = value.denom();
    let scaled = &numerator / denominator;
    let negative = scaled.sign() == num_bigint::Sign::Minus;
    let magnitude = if negative { -&scaled } else { scaled.clone() };
    let text = magnitude.to_string();
    let text = if text.len() as u32 <= places {
        format!("{}{}", "0".repeat((places as usize) + 1 - text.len()), text)
    } else {
        text
    };
    let split = text.len() - places as usize;
    format!(
        "{}{}.{}",
        if negative { "-" } else { "" },
        &text[..split],
        &text[split..]
    )
}

fn rational(value: &Rat) -> Value {
    json!(format!("{}/{}", value.numer(), value.denom()))
}

fn rationals(values: &[Rat]) -> Value {
    Value::Array(values.iter().map(rational).collect())
}

// -------------------------------------------------------------------------------------------
// §1. the source configuration and the residue correspondence
// -------------------------------------------------------------------------------------------

/// One presentation's alpha carbons, addressed by **M5 residue index**, exact.
fn alpha_carbons(
    path: &Path,
    chain_label: &str,
    offset: i32,
) -> Result<BTreeMap<i32, Vec<Rat>>, String> {
    let structure = StructurePresentation::read(path)
        .map_err(|error| format!("{}: {error}", path.display()))?;
    let chain: &ChainOccurrence = structure
        .chain(chain_label)
        .map_err(|error| format!("{}: {error}", path.display()))?;
    let mut places = BTreeMap::new();
    for residue in &chain.residues {
        let Some(at) = residue
            .labelled_atom(REPRESENTATIVE)
            .map_err(|error| error.to_string())?
        else {
            continue;
        };
        let atom = &residue.atoms[at];
        places.insert(
            residue.source_ordinal + offset,
            vec![
                atom.x.exact_centre().map_err(|e| e.to_string())?,
                atom.y.exact_centre().map_err(|e| e.to_string())?,
                atom.z.exact_centre().map_err(|e| e.to_string())?,
            ],
        );
    }
    Ok(places)
}

fn configuration_over(
    window: &[i32],
    places: &BTreeMap<i32, Vec<Rat>>,
) -> Result<ExactConfiguration, String> {
    let declared = window
        .iter()
        .enumerate()
        .map(|(block, residue)| (ConstraintVertexId(block as u64), places[residue].clone()));
    ExactConfiguration::declared(3, declared).map_err(|error| error.to_string())
}

/// The elastic contact set of one window at the declared aperture, as block pairs.
fn elastic_contacts(window: &[i32], places: &BTreeMap<i32, Vec<Rat>>) -> Vec<(usize, usize)> {
    let aperture = integer(ELASTIC_APERTURE * ELASTIC_APERTURE);
    let mut contacts = Vec::new();
    for lower in 0..window.len() {
        for upper in (lower + 1)..window.len() {
            let a = &places[&window[lower]];
            let b = &places[&window[upper]];
            let mut quadrance = Rat::zero();
            for axis in 0..3 {
                let difference = &a[axis] - &b[axis];
                quadrance += &difference * &difference;
            }
            if quadrance <= aperture {
                contacts.push((lower, upper));
            }
        }
    }
    contacts
}

fn jacobian_of(
    lineage: &str,
    configuration: &ExactConfiguration,
    contacts: &[(usize, usize)],
) -> Result<RigidityJacobian, String> {
    let mut edges = BTreeMap::new();
    for (lower, upper) in contacts {
        let (edge, _) = ConstraintEdge::new(
            ConstraintVertexId(*lower as u64),
            ConstraintVertexId(*upper as u64),
        )
        .map_err(|error| error.to_string())?;
        edges.insert(edge, EdgeProvenance::AdmittedContact);
    }
    RigidityJacobian::found(lineage, configuration, &edges).map_err(|error| error.to_string())
}

// -------------------------------------------------------------------------------------------
// the run
// -------------------------------------------------------------------------------------------

struct Arguments {
    structure_root: PathBuf,
    contact_support: PathBuf,
    out: Option<PathBuf>,
    windows: Vec<String>,
    family_bound: usize,
}

fn arguments() -> Result<Arguments, String> {
    let mut structure_root = None;
    let mut contact_support = None;
    let mut out = None;
    let mut windows = Vec::new();
    let mut family_bound = 8_usize;
    let mut raw = std::env::args().skip(1);
    while let Some(flag) = raw.next() {
        let mut value = || raw.next().ok_or_else(|| format!("{flag} wants a value"));
        match flag.as_str() {
            "--structure-root" => structure_root = Some(PathBuf::from(value()?)),
            "--contact-support" => contact_support = Some(PathBuf::from(value()?)),
            "--out" => out = Some(PathBuf::from(value()?)),
            "--window" => windows.push(value()?),
            "--family-bound" => {
                family_bound = value()?
                    .parse()
                    .map_err(|_| "--family-bound wants a whole number".to_owned())?;
            }
            other => return Err(format!("unknown flag {other}")),
        }
    }
    if windows.is_empty() {
        windows = WINDOWS
            .iter()
            .map(|(name, _, _)| (*name).to_owned())
            .collect();
    }
    Ok(Arguments {
        structure_root: structure_root
            .ok_or_else(|| "--structure-root is required; see the experiment README".to_owned())?,
        contact_support: contact_support
            .ok_or_else(|| "--contact-support is required".to_owned())?,
        out,
        windows,
        family_bound,
    })
}

fn main() {
    match run() {
        Ok(report) => {
            println!(
                "{}",
                serde_json::to_string_pretty(&report).unwrap_or_default()
            );
        }
        Err(refusal) => {
            eprintln!("refused: {refusal}");
            std::process::exit(1);
        }
    }
}

fn run() -> Result<Value, String> {
    let arguments = arguments()?;
    let started = Instant::now();
    let root = &arguments.structure_root;

    // ---------------------------------------------------------------------------------------
    // §0b. the known intake defect, probed rather than assumed
    // ---------------------------------------------------------------------------------------
    let defect_probe = {
        let deposited = root.join("3DPL.cif");
        match StructurePresentation::read(&deposited) {
            Ok(structure) => json!({
                "issue": 52,
                "bit": false,
                "detail": format!(
                    "the deposited ion-bearing mmCIF read: {} chains, {} atoms",
                    structure.chains.len(),
                    structure.atom_occurrences
                ),
            }),
            Err(error) => json!({
                "issue": 52,
                "bit": true,
                "detail": error.to_string(),
                "route_around":
                    "research/experiments/conditioned_rbx1_static_response/stage_partner_contacts.py \
                     reads only the ATOM rows with exact fractions and never constructs a float; \
                     the elastic run below reads the M5 experiment's already-staged single-chain \
                     files, which carry no HETATM row",
            }),
        }
    };

    // ---------------------------------------------------------------------------------------
    // §1. the source |q0>, before any comparison structure is opened
    // ---------------------------------------------------------------------------------------
    let source_models: Vec<BTreeMap<i32, Vec<Rat>>> = (1..=SOURCE_MODELS)
        .map(|model| {
            alpha_carbons(
                &root.join(format!("{SOURCE_ENTRY}-{SOURCE_CHAIN}-model{model}.cif")),
                SOURCE_CHAIN,
                SOURCE_OFFSET,
            )
        })
        .collect::<Result<_, _>>()?;
    let source = &source_models[0];

    let support: Value = serde_json::from_str(
        &std::fs::read_to_string(&arguments.contact_support)
            .map_err(|error| format!("{}: {error}", arguments.contact_support.display()))?,
    )
    .map_err(|error| error.to_string())?;
    let contact_sets: BTreeMap<String, BTreeSet<i32>> = support["entries"]
        .as_object()
        .ok_or_else(|| "the contact support carries no entries".to_owned())?
        .iter()
        .map(|(entry, reading)| {
            let residues = reading["m5_residues_in_contact"]
                .as_array()
                .map(|rows| {
                    rows.iter()
                        .filter_map(Value::as_i64)
                        .map(|value| value as i32)
                        .collect::<BTreeSet<i32>>()
                })
                .unwrap_or_default();
            (entry.clone(), residues)
        })
        .collect();

    // ---------------------------------------------------------------------------------------
    // §5's material, opened only after every declaration below is fixed.
    // ---------------------------------------------------------------------------------------
    let mut held_out = BTreeMap::new();
    for (entry, chain, offset, environment) in HELD_OUT {
        let places = alpha_carbons(
            &root.join(format!("{entry}-{chain}-model1.cif")),
            chain,
            offset,
        )?;
        held_out.insert(entry.to_owned(), (places, environment));
    }

    let mut windows = Vec::new();
    for (name, first, last) in WINDOWS {
        if !arguments.windows.iter().any(|declared| declared == name) {
            continue;
        }
        windows.push(run_window(
            name,
            first,
            last,
            source,
            &source_models,
            &held_out,
            &contact_sets,
            arguments.family_bound,
        )?);
    }

    let report = json!({
        "schema": "holonics.conditioned-rbx1-static-response.v1",
        "issue": 55,
        "contract":
            "docs/plans/THE_CONTINUING_OBJECT_IS_THE_SHARED_CARRIER.md#the-conditioned-structural-response-consumer",
        "what_this_is":
            "a bounded elastic experiment: a source-conditioned static response this program \
             generates, scored against measurement already on disk. Not general structure \
             prediction, and not an admission test for whether a generated response counts as \
             prediction. A failure is a result.",
        "no_float_on_any_path": true,
        "intake_defect_probe": defect_probe,
        "source": {
            "entry": SOURCE_ENTRY,
            "chain": SOURCE_CHAIN,
            "method": "solution NMR, 20 deposited models",
            "environment": "RBX1 alone: no cullin partner. 3 ZN in the deposition. pH undeclared.",
            "label_seq_id_to_m5_offset": SOURCE_OFFSET,
            "representative_atom": REPRESENTATIVE,
            "models_read": SOURCE_MODELS,
            "known_substitutions_against_the_m5_target": SOURCE_SUBSTITUTIONS,
            "substitutions_are_carried_not_smoothed":
                "2LGV is the solubilised construct W27S/V30S/L32Q/W33S. Those four residues sit \
                 inside the arm window. The receiver reports a scope that includes their pairs and \
                 a scope that excludes them; neither is suppressed.",
        },
        "held_out_comparison_structures": HELD_OUT
            .iter()
            .map(|(entry, chain, offset, environment)| json!({
                "entry": entry, "chain": chain,
                "label_seq_id_to_m5_offset": offset,
                "environment": environment,
            }))
            .collect::<Vec<_>>(),
        "windows": windows,
        "cost_milliseconds": started.elapsed().as_millis(),
    });

    if let Some(path) = &arguments.out {
        std::fs::write(
            path,
            serde_json::to_string_pretty(&report).unwrap_or_default(),
        )
        .map_err(|error| format!("{}: {error}", path.display()))?;
        eprintln!("wrote {}", path.display());
    }
    Ok(report)
}

#[allow(clippy::too_many_arguments)]
fn run_window(
    name: &str,
    first: i32,
    last: i32,
    source: &BTreeMap<i32, Vec<Rat>>,
    source_models: &[BTreeMap<i32, Vec<Rat>>],
    held_out: &BTreeMap<String, (BTreeMap<i32, Vec<Rat>>, &'static str)>,
    contact_sets: &BTreeMap<String, BTreeSet<i32>>,
    family_bound: usize,
) -> Result<Value, String> {
    let started = Instant::now();

    // -------- the window, and the coordinates that are NOT resolved everywhere --------------
    let declared: Vec<i32> = (first..=last).collect();
    let mut window = Vec::new();
    let mut unresolved: BTreeMap<i32, Vec<String>> = BTreeMap::new();
    for residue in &declared {
        let mut absent = Vec::new();
        for (model, places) in source_models.iter().enumerate() {
            if !places.contains_key(residue) {
                absent.push(format!("{SOURCE_ENTRY} model {}", model + 1));
            }
        }
        for (entry, (places, _)) in held_out {
            if !places.contains_key(residue) {
                absent.push(entry.clone());
            }
        }
        if absent.is_empty() {
            window.push(*residue);
        } else {
            unresolved.insert(*residue, absent);
        }
    }
    if window.len() < 4 {
        return Err(format!(
            "window {name} resolves fewer than four residues everywhere"
        ));
    }

    // -------- §2. the source configuration and the declared elastic energy ------------------
    let configuration = configuration_over(&window, source)?;
    let contacts = elastic_contacts(&window, source);
    let jacobian = jacobian_of(
        &format!("{SOURCE_ENTRY}-{SOURCE_CHAIN}-model1/{name}"),
        &configuration,
        &contacts,
    )?;
    let rigidity = rigidity_reading(&jacobian).map_err(|error| error.to_string())?;
    let trivial = TrivialMotionReading::measure(&jacobian).map_err(|error| error.to_string())?;

    let declaration = ElasticDeclaration::uniform(
        contacts.len(),
        Rat::one(),
        "gamma_0, one declared stiffness unit per admitted contact (energy / angstrom^2)",
        "angstrom",
        "gamma_0 * angstrom^2",
    )
    .map_err(|error| error.to_string())?;
    let stiffness_started = Instant::now();
    let stiffness = ConditionedStiffness::declared(&jacobian, declaration)
        .map_err(|error| error.to_string())?;
    let stiffness_milliseconds = stiffness_started.elapsed().as_millis();
    // The coefficient width of `K`, which is what decides whether an exact reading of it is cheap:
    // `W = diag(gamma / (4 l^2))` puts one squared length into the denominator of every entry, so
    // K's entries are much wider than the Jacobian's coordinate differences. Reported so the cost
    // of a solve is attributable rather than guessed at.
    let widest_entry_bits = |matrix: &holonic_engine::exact_linear::ExactRatMatrix| -> u64 {
        matrix
            .entries()
            .iter()
            .map(|entry| entry.numer().bits().max(entry.denom().bits()))
            .max()
            .unwrap_or(0)
    };
    let stiffness_entry_bits = widest_entry_bits(stiffness.matrix());
    let jacobian_entry_bits = widest_entry_bits(&jacobian.matrix);
    let rank_started = Instant::now();
    let stiffness_rank = stiffness
        .matrix()
        .rank()
        .map_err(|error| error.to_string())?;
    let rank_milliseconds = rank_started.elapsed().as_millis();

    // -------- §3. the full null fibre, the metric and the gauge -----------------------------
    let null_started = Instant::now();
    let null_fibre =
        NullFibre::measure(&stiffness, &jacobian).map_err(|error| error.to_string())?;
    let null_milliseconds = null_started.elapsed().as_millis();
    let metric = DeclaredMetric::cartesian_identity(stiffness.coordinate_freedoms(), "angstrom")
        .map_err(|error| error.to_string())?;

    // -------- §4. the forcing map and the force family --------------------------------------
    // The SUPPORT is conditioned on the bound structures; the DIRECTIONS come from |q0> alone
    // and the MAGNITUDES are declared. No held-out displacement enters any of the three.
    let mut supports: Vec<(String, Vec<(usize, usize)>, String)> = Vec::new();
    for (entry, residues) in contact_sets {
        let loaded: Vec<(usize, usize)> = contacts
            .iter()
            .copied()
            .filter(|(lower, upper)| {
                residues.contains(&window[*lower]) && residues.contains(&window[*upper])
            })
            .collect();
        if !loaded.is_empty() {
            supports.push((
                format!("interface_{entry}"),
                loaded,
                format!(
                    "CONDITIONED: the window's elastic contacts whose BOTH endpoints lie within \
                     the declared 10 A alpha-carbon aperture of a partner chain in the deposited \
                     {entry} bound frame. The support and nothing else comes from {entry}."
                ),
            ));
        }
        let interior: Vec<(usize, usize)> = contacts
            .iter()
            .copied()
            .filter(|(lower, upper)| {
                !residues.contains(&window[*lower]) && !residues.contains(&window[*upper])
            })
            .collect();
        if !interior.is_empty() {
            supports.push((
                format!("interior_control_{entry}"),
                interior,
                format!(
                    "SUPPORT CONTROL: the window's elastic contacts with NEITHER endpoint at the \
                     {entry} interface. Same elastic operator, same magnitude law, different \
                     support: an agreement that survives here was never about the interface."
                ),
            ));
        }
        // A forcing that is deliberately NOT along an existing bar. A pinch along a contact `c`
        // is exactly `−½ J* e_c`, so it lies in `image J* = image K` and its compatibility is a
        // theorem rather than a finding. A long-range pinch between two interface residues that
        // are *not* in contact is the case where `Z* f` can genuinely fail, and it is declared
        // here so the incompatible branch is exercised on measured material.
        let far: Vec<(usize, usize)> = {
            let mut declared = Vec::new();
            let loaded_blocks: Vec<usize> = (0..window.len())
                .filter(|block| residues.contains(&window[*block]))
                .collect();
            for (at, lower) in loaded_blocks.iter().enumerate() {
                for upper in loaded_blocks.iter().skip(at + 1) {
                    if !contacts.contains(&(*lower, *upper)) {
                        declared.push((*lower, *upper));
                    }
                }
            }
            // Declared bound, fixed before the work it sizes: the widest separations first, and
            // at most four of them.
            declared.sort_by_key(|(lower, upper)| std::cmp::Reverse(upper - lower));
            declared.truncate(4);
            declared
        };
        if !far.is_empty() {
            supports.push((
                format!("long_range_interface_{entry}"),
                far,
                format!(
                    "CONDITIONED, AND DELIBERATELY OFF THE BARS: pinches between {entry}-interface \
                     residues of the window that are NOT elastic contacts. A pinch along a bar is \
                     -1/2 J* e_c and therefore compatible by construction; these are the forcings \
                     whose Z* f can fail, and the refusal they meet is a result."
                ),
            ));
        }
    }

    // -------- §5. the held-out measurement, opened now and not before ----------------------
    let pairs: Vec<(usize, usize)> = (0..window.len())
        .flat_map(|lower| ((lower + 1)..window.len()).map(move |upper| (lower, upper)))
        .collect();
    let correspondence = BlockCorrespondence::identity(window.len(), window.len())
        .map_err(|error| error.to_string())?;
    let separated: Vec<usize> = pairs
        .iter()
        .enumerate()
        .filter(|(_, (lower, upper))| (window[*upper] - window[*lower]) >= MINIMUM_SEPARATION)
        .map(|(at, _)| at)
        .collect();
    let typed: Vec<usize> = separated
        .iter()
        .copied()
        .filter(|at| {
            let (lower, upper) = pairs[*at];
            !SOURCE_SUBSTITUTIONS.contains(&window[lower])
                && !SOURCE_SUBSTITUTIONS.contains(&window[upper])
        })
        .collect();
    let scopes: Vec<(&str, Vec<usize>)> = vec![
        ("all_pairs", (0..pairs.len()).collect()),
        ("separation_at_least_3", separated.clone()),
        ("identically_typed_and_separated", typed.clone()),
    ];

    let mut measured: BTreeMap<String, Vec<Rat>> = BTreeMap::new();
    for (entry, (places, _)) in held_out {
        let target = configuration_over(&window, places)?;
        measured.insert(
            entry.clone(),
            QuadranceResponse::between_with_correspondence(
                &configuration,
                &target,
                &correspondence,
                &pairs,
            )
            .map_err(|error| error.to_string())?,
        );
    }
    // The source ensemble's own spread: the same receiver, model 1 against each other model.
    let mut ensemble: Vec<Vec<Rat>> = Vec::new();
    for places in source_models.iter().skip(1) {
        let target = configuration_over(&window, places)?;
        ensemble.push(
            QuadranceResponse::between_with_correspondence(
                &configuration,
                &target,
                &correspondence,
                &pairs,
            )
            .map_err(|error| error.to_string())?,
        );
    }

    // -------- the responses ------------------------------------------------------------------
    let mut readings = Vec::new();
    for (support_name, loaded, provenance) in &supports {
        let mut forcing = ForcingDeclaration::pinch_family(
            &configuration,
            loaded,
            provenance.clone(),
            "caller-declared uniform and per-generator magnitude laws below; the caller reports no \
             held-out displacement fitting, and the scale diagnostic enters no score",
        )
        .map_err(|error| error.to_string())?;
        let equilibrated = forcing
            .self_equilibrated(&trivial)
            .map_err(|error| error.to_string())?;

        let generators = loaded.len();
        let laws: Vec<(&str, Vec<Rat>)> = vec![
            ("uniform_compression_u_plus_1", vec![Rat::one(); generators]),
            ("uniform_expansion_u_minus_1", vec![integer(-1); generators]),
            (
                "alternating_by_generator_index",
                (0..generators)
                    .map(|at| if at % 2 == 0 { Rat::one() } else { integer(-1) })
                    .collect(),
            ),
            (
                "single_generator_zero_elsewhere",
                (0..generators)
                    .map(|at| if at == 0 { Rat::one() } else { Rat::zero() })
                    .collect(),
            ),
        ];

        let mut force_readings = Vec::new();
        for (law, magnitudes) in &laws {
            let force = forcing
                .force(magnitudes)
                .map_err(|error| error.to_string())?;
            // The exact solve alone, timed beside the whole response so the cost of this consumer
            // is attributable rather than guessed at. Above `DECLARED_PRIME_IMAGE_CROSSOVER` this
            // is the certified prime-image reading; the rest of `solve` — the gauge fix, the
            // equilibrium application and the two residual checks — runs over the wide rationals
            // that reading returns.
            let fibre_started = Instant::now();
            let fibre_probe = stiffness.matrix().preimage_fibre_with_work(&force);
            let fibre_milliseconds = fibre_started.elapsed().as_millis();
            let fibre_returned = fibre_probe
                .map(|(fibre, _)| fibre.is_some())
                .unwrap_or(false);
            let solve_started = Instant::now();
            let response = StaticResponse::solve(
                &stiffness,
                &null_fibre,
                &metric,
                ResponseGauge::MetricComplement,
                &force,
            )
            .map_err(|error| error.to_string())?;
            let solve_milliseconds = solve_started.elapsed().as_millis();

            let mut entry = Map::new();
            entry.insert("magnitude_law".into(), json!(law));
            entry.insert("compatible".into(), json!(response.compatible));
            entry.insert(
                "compatibility_pairing_Z_star_f".into(),
                rationals(&response.compatibility_pairing),
            );
            entry.insert("gauge".into(), json!(response.gauge));
            entry.insert("metric".into(), json!(response.metric));
            entry.insert(
                "null_fibre_dimension".into(),
                json!(response.null_fibre_dimension),
            );
            entry.insert("solve_milliseconds".into(), json!(solve_milliseconds));
            entry.insert("exact_solve_milliseconds".into(), json!(fibre_milliseconds));
            entry.insert("exact_solve_returned_a_fibre".into(), json!(fibre_returned));
            entry.insert(
                "what_the_remaining_time_is".into(),
                json!(
                    "the gauge fix, the equilibrium application and the two residual checks, all \
                     over the wide rationals the exact solve returns — NOT the elimination"
                ),
            );

            if !response.compatible {
                let retained = &response.retained_incompatible_force;
                let quadrance = retained
                    .iter()
                    .fold(Rat::zero(), |sum, value| sum + value * value);
                entry.insert(
                    "refusal".into(),
                    json!({
                        "why": "Z* f does not vanish: no static equilibrium of the free window \
                                answers this forcing",
                        "retained_incompatible_force_quadrance": rational(&quadrance),
                        "obstruction_covector_returned": response.obstruction.is_some(),
                        "a_least_squares_projection_would_be_a_different_receiver": true,
                    }),
                );
                force_readings.push(Value::Object(entry));
                continue;
            }

            let displacement = response
                .displacement
                .clone()
                .ok_or_else(|| "a compatible response returned no displacement".to_owned())?;
            let quadrance = QuadranceResponse::measure(
                &configuration,
                &displacement,
                &pairs,
                "angstrom^2 per gamma_0",
            )
            .map_err(|error| error.to_string())?;
            let displacement_quadrance = displacement
                .iter()
                .fold(Rat::zero(), |sum, value| sum + value * value);
            entry.insert(
                "elastic_energy".into(),
                rational(&response.elastic_energy.clone().unwrap_or_else(Rat::zero)),
            );
            entry.insert(
                "displacement_quadrance".into(),
                rational(&displacement_quadrance),
            );
            entry.insert(
                "equilibrium_residual_is_exactly_zero".into(),
                json!(response.equilibrium_residual.iter().all(Rat::is_zero)),
            );
            entry.insert(
                "gauge_residual_is_exactly_zero".into(),
                json!(response.gauge_residual.iter().all(Rat::is_zero)),
            );

            // The linearized change is the model's first-order content; the finite change adds
            // the quadratic term the linearization drops. They are reported apart.
            let quadratic_weight = quadrance
                .quadratic_term
                .iter()
                .fold(Rat::zero(), |sum, value| sum + value);
            let linear_weight = quadrance
                .linearized
                .iter()
                .fold(Rat::zero(), |sum, value| sum + value * value);
            entry.insert(
                "linearized_quadrance_change_norm_square".into(),
                rational(&linear_weight),
            );
            entry.insert(
                "dropped_quadratic_term_total".into(),
                rational(&quadratic_weight),
            );

            let mut scope_readings = Map::new();
            for (scope, selection) in &scopes {
                let predicted: Vec<Rat> = selection
                    .iter()
                    .map(|at| quadrance.linearized[*at].clone())
                    .collect();
                let predicted_finite: Vec<Rat> = selection
                    .iter()
                    .map(|at| quadrance.finite[*at].clone())
                    .collect();
                let mut against = Map::new();
                for (measurement, changes) in &measured {
                    let observed: Vec<Rat> =
                        selection.iter().map(|at| changes[*at].clone()).collect();
                    let agreement = OrientedAgreement::between(&predicted, &observed)
                        .map_err(|error| error.to_string())?;
                    let finite_agreement = OrientedAgreement::between(&predicted_finite, &observed)
                        .map_err(|error| error.to_string())?;
                    against.insert(
                        measurement.clone(),
                        agreement_value(&agreement, &finite_agreement),
                    );
                }

                // The control: the same predicted response against the source ensemble's own
                // spread. If the response agrees with a random sibling NMR model as well as it
                // agrees with the bound structure, the reading is null.
                let mut ensemble_signs = (0usize, 0usize, 0usize);
                let mut best: Option<Rat> = None;
                for changes in &ensemble {
                    let observed: Vec<Rat> =
                        selection.iter().map(|at| changes[*at].clone()).collect();
                    let agreement = OrientedAgreement::between(&predicted, &observed)
                        .map_err(|error| error.to_string())?;
                    match agreement.sign {
                        1 => ensemble_signs.0 += 1,
                        -1 => ensemble_signs.1 += 1,
                        _ => ensemble_signs.2 += 1,
                    }
                    if let Some(cosine) = agreement.cosine_square {
                        best = Some(match best {
                            Some(current) if current >= cosine => current,
                            _ => cosine,
                        });
                    }
                }
                against.insert(
                    "control_source_nmr_ensemble_spread".into(),
                    json!({
                        "models": ensemble.len(),
                        "signed_agreement_positive": ensemble_signs.0,
                        "signed_agreement_negative": ensemble_signs.1,
                        "signed_agreement_zero": ensemble_signs.2,
                        "largest_cosine_square": best.as_ref().map(rational),
                        "largest_cosine_square_exterior_decimal":
                            best.as_ref().map(|value| exterior_decimal(value, 6)),
                        "what_it_controls":
                            "the spread the source ensemble already has without any forcing. A \
                             predicted response that does not beat this is not reading the bound \
                             state.",
                    }),
                );
                scope_readings.insert((*scope).to_owned(), Value::Object(against));
            }
            entry.insert("receiver_scopes".into(), Value::Object(scope_readings));
            force_readings.push(Value::Object(entry));
        }

        // A bounded family reading, for the rank statement that a single displacement cannot make.
        let bounded: Vec<(usize, usize)> = loaded.iter().copied().take(family_bound).collect();
        let bounded_forcing = ForcingDeclaration::pinch_family(
            &configuration,
            &bounded,
            provenance.clone(),
            "the declared family, bounded before it runs",
        )
        .map_err(|error| error.to_string())?;
        let family_started = Instant::now();
        let family = ResponseFamilyReading::read(
            &stiffness,
            &null_fibre,
            &metric,
            ResponseGauge::MetricComplement,
            &bounded_forcing,
        )
        .map_err(|error| error.to_string())?;
        let family_milliseconds = family_started.elapsed().as_millis();

        readings.push(json!({
            "support": support_name,
            "support_provenance": provenance,
            "direction_provenance": forcing.direction_provenance,
            "magnitude_provenance": forcing.magnitude_provenance,
            "held_out_displacement_used": forcing.held_out_displacement_used,
            "generators": generators,
            "self_equilibrated_against_every_trivial_motion": equilibrated,
            "forces": force_readings,
            "bounded_family_reading": {
                "declared_bound": family_bound,
                "generators_read": bounded.len(),
                "admissible_generators": family.admissible_generators,
                "inadmissible_generators": family.inadmissible_generators,
                "force_rank": family.force_rank,
                "response_rank": family.response_rank,
                "stiffness_rank": family.stiffness_rank,
                "response_rank_equals_force_rank": family.response_rank_equals_force_rank,
                "neck_identification": "WITHHELD: K is singular, so H(0) = C(-A)^{-1} B does not \
                                        exist and C K^+ B is a different operator. The four-site \
                                        counterexample is checked in the module's own tests.",
                "one_displacement_does_not_read_a_rank":
                    family.one_displacement_does_not_read_a_rank,
                "milliseconds": family_milliseconds,
            },
        }));
    }

    // The measurement's own magnitude, so a residual can be read against something.
    let mut measured_scale = Map::new();
    for (entry, changes) in &measured {
        for (scope, selection) in &scopes {
            let quadrance = selection
                .iter()
                .fold(Rat::zero(), |sum, at| sum + &changes[*at] * &changes[*at]);
            measured_scale.insert(
                format!("{entry}/{scope}"),
                json!({
                    "quadrance_change_norm_square": rational(&quadrance),
                    "exterior_decimal": exterior_decimal(&quadrance, 3),
                    "entries": selection.len(),
                }),
            );
        }
    }
    let mut ensemble_scale = Vec::new();
    for changes in &ensemble {
        let quadrance = changes
            .iter()
            .fold(Rat::zero(), |sum, value| sum + value * value);
        ensemble_scale.push(exterior_decimal(&quadrance, 3));
    }

    Ok(json!({
        "window": name,
        "declared_residues": [first, last],
        "residues_resolved_everywhere": window.len(),
        "residues_excised_and_why": unresolved
            .iter()
            .map(|(residue, absent)| json!({"m5_residue": residue, "unresolved_in": absent}))
            .collect::<Vec<_>>(),
        "coordinate_freedoms": stiffness.coordinate_freedoms(),
        "elastic_network": {
            "aperture_angstrom": ELASTIC_APERTURE,
            "contacts": contacts.len(),
            "jacobian_rank": rigidity.rank,
            "self_stress_dimension": rigidity.self_stress_dimension,
            "bounded_window_caveat":
                "the window is cut out of the chain, so its boundary residues lose the contacts \
                 their neighbours outside the window would supply. That is a declared property of \
                 the bounded experiment, not a property of RBX1.",
        },
        "elastic_declaration": {
            "energy_law": stiffness.declaration().energy_law,
            "weight_law": stiffness.declaration().weight_law,
            "pairing": stiffness.declaration().pairing,
            "stiffness_unit": stiffness.declaration().stiffness_unit,
            "length_unit": stiffness.declaration().length_unit,
            "energy_unit": stiffness.declaration().energy_unit,
            "not_inherited_from_the_dissipation_form":
                stiffness.declaration().not_inherited_from_the_dissipation_form,
            "K_is_self_adjoint_defect": rational(stiffness.self_adjoint_defect()),
            "K_rank": stiffness.rank(),
            "build_milliseconds": stiffness_milliseconds,
            "widest_jacobian_entry_bits": jacobian_entry_bits,
            "widest_stiffness_entry_bits": stiffness_entry_bits,
            "why_the_width_matters":
                "W = diag(gamma / (4 l^2)) puts one squared length into every entry's denominator, \
                 so K's coefficients are an order of magnitude wider than the Jacobian's coordinate \
                 differences. The exact algebra absorbs that; the arithmetic downstream of it does not.",
            "certified_rank_milliseconds": rank_milliseconds,
            "certified_rank": stiffness_rank,
        },
        "null_fibre": {
            "dimension": null_fibre.dimension,
            "trivial_dimension": null_fibre.trivial_dimension,
            "internal_floppy_dimension": null_fibre.internal_floppy_dimension,
            "configuration_degeneracy": format!("{:?}", null_fibre.degeneracy),
            "ker_K_equals_ker_J_verified": null_fibre.equals_constraint_kernel,
            "measure_milliseconds": null_milliseconds,
            "why_the_full_kernel":
                "Z spans the whole of ker K. A reading that took it to be the six rigid motions \
                 would be wrong by exactly internal_floppy_dimension, and would call an \
                 incompatible forcing compatible.",
        },
        "gauge": ResponseGauge::MetricComplement.name(),
        "metric": metric.name(),
        "receiver_scopes_declared": scopes
            .iter()
            .map(|(scope, selection)| json!({"scope": scope, "pairs": selection.len()}))
            .collect::<Vec<_>>(),
        "measured_quadrance_change_scale": measured_scale,
        "control_source_ensemble_quadrance_change_norm_square_exterior_decimal": ensemble_scale,
        "responses": readings,
        "window_milliseconds": started.elapsed().as_millis(),
    }))
}

fn agreement_value(linearized: &OrientedAgreement, finite: &OrientedAgreement) -> Value {
    json!({
        "linearized": {
            "signed_agreement": linearized.sign,
            "pairing": rational(&linearized.pairing),
            "predicted_quadrance": rational(&linearized.predicted_quadrance),
            "measured_quadrance": rational(&linearized.measured_quadrance),
            "cosine_square": linearized.cosine_square.as_ref().map(rational),
            "cosine_square_exterior_decimal": linearized
                .cosine_square
                .as_ref()
                .map(|value| exterior_decimal(value, 6)),
            "residual_quadrance_at_declared_scale": rational(&linearized.residual_quadrance),
            "scale_diagnostic_enters_no_score": linearized
                .scale_diagnostic
                .as_ref()
                .map(|value| exterior_decimal(value, 9)),
            "residual_quadrance_at_diagnostic_scale": linearized
                .residual_quadrance_at_diagnostic_scale
                .as_ref()
                .map(|value| exterior_decimal(value, 3)),
        },
        "finite_including_the_quadratic_term": {
            "signed_agreement": finite.sign,
            "cosine_square_exterior_decimal": finite
                .cosine_square
                .as_ref()
                .map(|value| exterior_decimal(value, 6)),
        },
        "the_unoriented_face_is_not_sufficient": linearized.unoriented_face_is_not_sufficient,
    })
}
