use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Debug;
use std::io::Write;
use std::path::PathBuf;

use body::incidence::IncidenceHand;
use body::num::Cog;
use life::form_mouth::deposit_form_or_message;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use soma_abi::active::{ActionCurrent, RelationAtom};
use soma_membrane::{
    ContemporaryEvent, CurrentBoundaryPort, CurrentEvent, CurrentGeometry, CurrentLineage,
    InterfaceCapability, LiveConstituent, LiveCurrentMachine, LiveCurrentRestImage, LiveMemory,
    RegionalRelationArc, RegionalRelationCell, SparseStandingSurface,
};

/// This driver's name at the plate mouth: `output/eros_transformer_translation_atlas/<name>-<sha256>.form`.
const FORM_DRIVER: &str = "eros_transformer_translation_atlas";
/// The live-current rest this driver seals. `ERST` is the schema `holon-plate` holds for it.
const MACHINE_REST_FORM: &str = "machine-rest";
const SOURCE_SCHEMA: &str = "eros.transformer-translation-atlas.source.v1";
const REPORT_SCHEMA: &str = "eros.transformer-translation-atlas.report.v1";
const LAW_MAGIC: [u8; 4] = *b"ATLS";
const QUERY_MAGIC: [u8; 4] = *b"ATQY";
const CARRIER_VERSION: u8 = 1;
const RECRUIT_LOCAL: u64 = 0;
const PRIMING_VALUES: [i64; 8] = [13, 29, 17, 31, -63_245, 47, 71, -89];

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
struct SiteKey {
    family: Family,
    direction: Direction,
    boundary: u8,
}

impl SiteKey {
    fn from_source(source: &SourceKey) -> Result<Self, String> {
        let boundary = u8::try_from(source.boundary).map_err(|_| {
            format!(
                "boundary {} does not fit the atlas carrier",
                source.boundary
            )
        })?;
        if boundary > 16 {
            return Err(format!(
                "boundary {boundary} lies outside the source transformer"
            ));
        }
        Ok(Self {
            family: Family::parse(&source.family)?,
            direction: Direction::parse(&source.direction)?,
            boundary,
        })
    }

    fn bytes(self) -> [u8; 3] {
        [self.family as u8, self.direction as u8, self.boundary]
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "snake_case")]
enum Family {
    InformantAbsence = 1,
    InformantReposition = 2,
    InformantSpecificity = 3,
}

impl Family {
    fn parse(value: &str) -> Result<Self, String> {
        match value {
            "informant_absence" => Ok(Self::InformantAbsence),
            "informant_reposition" => Ok(Self::InformantReposition),
            "informant_specificity" => Ok(Self::InformantSpecificity),
            _ => Err(format!("unknown atlas family {value:?}")),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "snake_case")]
enum Direction {
    SourceToTarget = 1,
    TargetToSource = 2,
}

impl Direction {
    fn parse(value: &str) -> Result<Self, String> {
        match value {
            "source_to_target" => Ok(Self::SourceToTarget),
            "target_to_source" => Ok(Self::TargetToSource),
            _ => Err(format!("unknown atlas direction {value:?}")),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
enum LineageFace {
    SourceExpression = 1,
    TargetExpression = 2,
    SourceAndTargetExpression = 3,
    ThirdExpression = 4,
}

impl LineageFace {
    fn parse(value: &str) -> Result<Self, String> {
        match value {
            "source_expression" => Ok(Self::SourceExpression),
            "target_expression" => Ok(Self::TargetExpression),
            "source_and_target_expression" => Ok(Self::SourceAndTargetExpression),
            "third_expression" => Ok(Self::ThirdExpression),
            _ => Err(format!("unknown lineage face {value:?}")),
        }
    }

    fn decode(value: u8) -> Result<Option<Self>, String> {
        match value {
            0 => Ok(None),
            1 => Ok(Some(Self::SourceExpression)),
            2 => Ok(Some(Self::TargetExpression)),
            3 => Ok(Some(Self::SourceAndTargetExpression)),
            4 => Ok(Some(Self::ThirdExpression)),
            _ => Err(format!("unknown encoded lineage face {value}")),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct AtlasLaw {
    ordinal: u16,
    key: SiteKey,
    lineage: Option<LineageFace>,
    affordance: Option<bool>,
}

impl AtlasLaw {
    fn encode(&self) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(12);
        bytes.extend(LAW_MAGIC);
        bytes.push(CARRIER_VERSION);
        bytes.extend(self.ordinal.to_le_bytes());
        bytes.extend(self.key.bytes());
        bytes.push(self.lineage.map_or(0, |face| face as u8));
        bytes.push(match self.affordance {
            None => 0,
            Some(false) => 1,
            Some(true) => 2,
        });
        bytes
    }

    fn decode(bytes: &[u8]) -> Result<Self, String> {
        let mut cursor = 0;
        if take(bytes, &mut cursor, 4)? != LAW_MAGIC {
            return Err("atlas-law carrier magic changed".to_owned());
        }
        if take(bytes, &mut cursor, 1)?[0] != CARRIER_VERSION {
            return Err("atlas-law carrier version changed".to_owned());
        }
        let ordinal = read_u16(bytes, &mut cursor)?;
        let family = match take(bytes, &mut cursor, 1)?[0] {
            1 => Family::InformantAbsence,
            2 => Family::InformantReposition,
            3 => Family::InformantSpecificity,
            value => return Err(format!("unknown encoded atlas family {value}")),
        };
        let direction = match take(bytes, &mut cursor, 1)?[0] {
            1 => Direction::SourceToTarget,
            2 => Direction::TargetToSource,
            value => return Err(format!("unknown encoded atlas direction {value}")),
        };
        let boundary = take(bytes, &mut cursor, 1)?[0];
        let lineage = LineageFace::decode(take(bytes, &mut cursor, 1)?[0])?;
        let affordance = match take(bytes, &mut cursor, 1)?[0] {
            0 => None,
            1 => Some(false),
            2 => Some(true),
            value => return Err(format!("unknown encoded affordance face {value}")),
        };
        if cursor != bytes.len() {
            return Err("atlas-law carrier has trailing material".to_owned());
        }
        if lineage.is_none() && affordance.is_none() {
            return Err("an atlas law carries no translation map".to_owned());
        }
        Ok(Self {
            ordinal,
            key: SiteKey {
                family,
                direction,
                boundary,
            },
            lineage,
            affordance,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct QueryCarrier {
    ordinal: u16,
    key: SiteKey,
}

impl QueryCarrier {
    fn encode(&self) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(10);
        bytes.extend(QUERY_MAGIC);
        bytes.push(CARRIER_VERSION);
        bytes.extend(self.ordinal.to_le_bytes());
        bytes.extend(self.key.bytes());
        bytes
    }

    fn decode(bytes: &[u8]) -> Result<Self, String> {
        let mut cursor = 0;
        if take(bytes, &mut cursor, 4)? != QUERY_MAGIC {
            return Err("atlas-query carrier magic changed".to_owned());
        }
        if take(bytes, &mut cursor, 1)?[0] != CARRIER_VERSION {
            return Err("atlas-query carrier version changed".to_owned());
        }
        let ordinal = read_u16(bytes, &mut cursor)?;
        let family = match take(bytes, &mut cursor, 1)?[0] {
            1 => Family::InformantAbsence,
            2 => Family::InformantReposition,
            3 => Family::InformantSpecificity,
            value => return Err(format!("unknown query family {value}")),
        };
        let direction = match take(bytes, &mut cursor, 1)?[0] {
            1 => Direction::SourceToTarget,
            2 => Direction::TargetToSource,
            value => return Err(format!("unknown query direction {value}")),
        };
        let boundary = take(bytes, &mut cursor, 1)?[0];
        if cursor != bytes.len() {
            return Err("atlas-query carrier has trailing material".to_owned());
        }
        Ok(Self {
            ordinal,
            key: SiteKey {
                family,
                direction,
                boundary,
            },
        })
    }
}

#[derive(Clone, Copy, Debug)]
struct LawHandle {
    data_namespace: u64,
    recruit_namespace: u64,
}

impl LawHandle {
    fn new(source_sha256: &str, law: &AtlasLaw) -> Self {
        let encoded = law.encode();
        Self {
            data_namespace: namespace(&[
                b"eros-transformer-translation-atlas-data-v1",
                source_sha256.as_bytes(),
                &law.ordinal.to_le_bytes(),
                &law.key.bytes(),
                &encoded,
            ]),
            recruit_namespace: namespace(&[
                b"eros-transformer-translation-atlas-recruit-v1",
                source_sha256.as_bytes(),
                &law.ordinal.to_le_bytes(),
                &law.key.bytes(),
            ]),
        }
    }

    fn renewed(self, query_identity: u64) -> Self {
        Self {
            data_namespace: self.data_namespace,
            recruit_namespace: namespace(&[
                b"eros-transformer-translation-atlas-renew-v1",
                &self.recruit_namespace.to_le_bytes(),
                &query_identity.to_le_bytes(),
            ]),
        }
    }
}

#[derive(Deserialize)]
struct Source {
    schema: String,
    observation_id: String,
    source_observation: String,
    model: serde_json::Value,
    input_artifacts: serde_json::Value,
    summary: SourceSummary,
    sites: Vec<SourceSite>,
}

#[derive(Deserialize)]
struct SourceSummary {
    sites: usize,
    lineage_maps: usize,
    lineage_held_out_commutations: usize,
    lineage_held_out_residuals: usize,
    lineage_training_opens: usize,
    affordance_maps: usize,
    affordance_held_out_commutations: usize,
    affordance_held_out_residuals: usize,
    affordance_training_opens: usize,
    union_maps: usize,
    no_maps: usize,
}

#[derive(Deserialize)]
struct SourceSite {
    ordinal: usize,
    key: SourceKey,
    charts: BTreeMap<String, SourceChart>,
    overlap: SourceOverlap,
    held_out_comparison: SourceHeldOutComparison,
}

#[derive(Deserialize)]
struct SourceKey {
    family: String,
    direction: String,
    boundary: usize,
    patch_surface: String,
}

#[derive(Deserialize)]
struct SourceChart {
    lineage_relation: String,
    affords_declared_world_action: bool,
}

#[derive(Deserialize)]
struct SourceOverlap {
    lineage: SourceMap<String>,
    affordance: SourceMap<bool>,
}

#[derive(Deserialize)]
struct SourceMap<T> {
    available: bool,
    prediction: Option<T>,
}

#[derive(Deserialize)]
struct SourceHeldOutComparison {
    lineage_commutes: bool,
    affordance_commutes: bool,
}

#[derive(Clone)]
struct Ecology {
    body: LiveCurrentRestImage,
    handles: BTreeMap<u16, LawHandle>,
    law_constituents: BTreeMap<u16, LiveConstituent>,
}

struct DepositOutcome {
    ecology: Ecology,
    read: DepositRead,
}

struct ProbeOutcome {
    recovered: BTreeMap<u16, Option<AtlasLaw>>,
    queries_exact: bool,
    machine: MachineRead,
}

struct ComparisonOutcome {
    sites: BTreeMap<u16, ComparisonCarrierRead>,
    machine: MachineRead,
}

struct ComparisonCarrierRead {
    expected_open_bits: Vec<u64>,
    carried_open_bits: Vec<u64>,
    open_bits_exact: bool,
    found_pins: usize,
}

#[derive(Serialize)]
struct Report {
    schema: &'static str,
    status: &'static str,
    question: &'static str,
    theory_to_structure: &'static str,
    stopping_condition: &'static str,
    source: SourceRead,
    deposit: DepositRead,
    held_out: HeldOutRead,
    sites: Vec<SiteRead>,
    acceptance: AcceptanceRead,
    conclusion: &'static str,
}

#[derive(Serialize)]
struct SourceRead {
    source_sha256: String,
    source_observation: String,
    model: serde_json::Value,
    input_artifacts: serde_json::Value,
    sites: usize,
    training_charts: [&'static str; 2],
    held_out_chart: &'static str,
}

#[derive(Serialize)]
struct DepositRead {
    laws: usize,
    encoded_bits: usize,
    returned_exact: bool,
    source_lineages_departed: bool,
    rest_remount_exact: bool,
    standing_before: usize,
    standing_after: usize,
    machine: MachineRead,
}

#[derive(Serialize)]
struct HeldOutRead {
    queries: usize,
    recovered_maps: usize,
    absent_maps: usize,
    query_carriers_exact: bool,
    no_ecology_recovered_maps: usize,
    machine: MachineRead,
    no_ecology_machine: MachineRead,
    comparison_machine: MachineRead,
}

#[derive(Serialize)]
struct SiteRead {
    ordinal: u16,
    key: SiteKey,
    patch_surface: String,
    recovered_map: bool,
    lineage: FaceRead<LineageFace>,
    affordance: FaceRead<bool>,
    comparison: ComparisonRead,
}

#[derive(Serialize)]
struct FaceRead<T: Serialize> {
    training_overlap: &'static str,
    prediction: Option<T>,
    held_out_actual: T,
    held_out_relation: &'static str,
}

#[derive(Serialize)]
struct ComparisonRead {
    expected_open_bits: Vec<u64>,
    carried_open_bits: Vec<u64>,
    open_bits_exact: bool,
    found_pins: usize,
}

#[derive(Serialize)]
struct AcceptanceRead {
    all_source_counts_exact: bool,
    all_laws_returned_bit_exact: bool,
    every_available_map_recovered: bool,
    no_unavailable_map_invented: bool,
    no_ecology_control_recovered_nothing: bool,
    lineage_maps: usize,
    lineage_held_out_commutations: usize,
    lineage_held_out_residuals: usize,
    lineage_training_opens: usize,
    affordance_maps: usize,
    affordance_held_out_commutations: usize,
    affordance_held_out_residuals: usize,
    affordance_training_opens: usize,
    receiver_relative_outcome_differences: usize,
    comparison_commuting_sites: usize,
    comparison_residual_sites: usize,
    comparison_open_bits_exact: bool,
    comparison_created_no_found_pins: bool,
}

#[derive(Serialize)]
struct MachineRead {
    standing_rank: u64,
    standing_cells: usize,
    standing_constituents: usize,
    constituent_cells: usize,
    constituent_incidences: usize,
    constituent_pins: usize,
    constituent_paths: usize,
    constituent_transport_terms: usize,
    live_lineages: usize,
    rest_sha256: String,
}

fn main() {
    if let Err(error) = run() {
        eprintln!("eros transformer translation atlas: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let source_path = PathBuf::from(arguments.next().ok_or_else(|| usage().to_owned())?);
    let report_path = PathBuf::from(arguments.next().ok_or_else(|| usage().to_owned())?);
    if arguments.next().is_some() {
        return Err(usage().to_owned());
    }
    let source_bytes = std::fs::read(&source_path)
        .map_err(|error| format!("{} reads: {error}", source_path.display()))?;
    let source_sha256 = sha256(&source_bytes);
    let source: Source = serde_json::from_slice(&source_bytes)
        .map_err(|error| format!("{} parses: {error}", source_path.display()))?;
    let report = run_cpu(source, source_sha256)?;
    let mut report_bytes = serde_json::to_vec_pretty(&report)
        .map_err(|error| format!("translation-atlas report encodes: {error}"))?;
    report_bytes.push(b'\n');
    let mut output = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&report_path)
        .map_err(|error| format!("{} opens as a new report: {error}", report_path.display()))?;
    output
        .write_all(&report_bytes)
        .map_err(|error| format!("{} writes completely: {error}", report_path.display()))?;
    output
        .sync_all()
        .map_err(|error| format!("{} syncs completely: {error}", report_path.display()))?;
    eprintln!(
        "eros transformer translation atlas: {} · {} bytes · {}",
        report.status,
        report_bytes.len(),
        report_path.display()
    );
    Ok(())
}

fn run_cpu(source: Source, source_sha256: String) -> Result<Report, String> {
    if source.schema != SOURCE_SCHEMA {
        return Err(format!("source schema changed: {}", source.schema));
    }
    if source.observation_id != "eros-transformer-translation-atlas-01" {
        return Err(format!(
            "source observation changed: {}",
            source.observation_id
        ));
    }
    let (laws, keys) = validate_source(&source)?;
    let base = empty_ecology()?;
    let DepositOutcome { ecology, read } = deposit_laws(base.clone(), &source_sha256, &laws)?;
    let held_out_probe = probe(&ecology, &source_sha256, &source.sites, &keys)?;
    let no_ecology_probe = probe(&base, &source_sha256, &source.sites, &keys)?;
    let comparison = compare_held_out(&ecology, &laws, &source.sites, &keys)?;

    let mut lineage_maps = 0usize;
    let mut lineage_commutations = 0usize;
    let mut lineage_residuals = 0usize;
    let mut lineage_training_opens = 0usize;
    let mut affordance_maps = 0usize;
    let mut affordance_commutations = 0usize;
    let mut affordance_residuals = 0usize;
    let mut affordance_training_opens = 0usize;
    let mut receiver_relative_outcome_differences = 0usize;
    let mut comparison_commuting_sites = 0usize;
    let mut comparison_residual_sites = 0usize;
    let mut comparison_open_bits_exact = true;
    let mut comparison_created_no_found_pins = true;
    let mut sites = Vec::with_capacity(source.sites.len());

    for site in &source.sites {
        let ordinal = u16::try_from(site.ordinal).map_err(debug)?;
        let key = *keys
            .get(&ordinal)
            .ok_or_else(|| format!("source site {ordinal} has no validated key"))?;
        let held = site
            .charts
            .get("code_comment")
            .ok_or_else(|| format!("source site {ordinal} has no held-out chart"))?;
        let held_lineage = LineageFace::parse(&held.lineage_relation)?;
        let recovered = held_out_probe
            .recovered
            .get(&ordinal)
            .ok_or_else(|| format!("held-out probe omitted site {ordinal}"))?;
        let recovered_map = recovered.is_some();

        let (lineage_overlap, lineage_prediction, lineage_relation) = match recovered {
            Some(law) if law.lineage.is_some() => {
                lineage_maps += 1;
                let prediction = law.lineage;
                let relation = if prediction == Some(held_lineage) {
                    lineage_commutations += 1;
                    "RIDE"
                } else {
                    lineage_residuals += 1;
                    "OPEN_RESIDUAL"
                };
                ("MAP", prediction, relation)
            }
            _ => {
                lineage_training_opens += 1;
                ("OPEN", None, "NO_MAP")
            }
        };
        let (affordance_overlap, affordance_prediction, affordance_relation) = match recovered {
            Some(law) if law.affordance.is_some() => {
                affordance_maps += 1;
                let prediction = law.affordance;
                let relation = if prediction == Some(held.affords_declared_world_action) {
                    affordance_commutations += 1;
                    "RIDE"
                } else {
                    affordance_residuals += 1;
                    "OPEN_RESIDUAL"
                };
                ("MAP", prediction, relation)
            }
            _ => {
                affordance_training_opens += 1;
                ("OPEN", None, "NO_MAP")
            }
        };
        if lineage_overlap == "MAP"
            && affordance_overlap == "MAP"
            && lineage_relation != affordance_relation
        {
            receiver_relative_outcome_differences += 1;
        }
        let comparison_read = match (recovered, comparison.sites.get(&ordinal)) {
            (Some(_), Some(read)) => {
                comparison_open_bits_exact &= read.open_bits_exact;
                comparison_created_no_found_pins &= read.found_pins == 0;
                if read.carried_open_bits.is_empty() {
                    comparison_commuting_sites += 1;
                } else {
                    comparison_residual_sites += 1;
                }
                ComparisonRead {
                    expected_open_bits: read.expected_open_bits.clone(),
                    carried_open_bits: read.carried_open_bits.clone(),
                    open_bits_exact: read.open_bits_exact,
                    found_pins: read.found_pins,
                }
            }
            (None, None) => ComparisonRead {
                expected_open_bits: Vec::new(),
                carried_open_bits: Vec::new(),
                open_bits_exact: true,
                found_pins: 0,
            },
            _ => {
                return Err(format!(
                    "site {ordinal} disagrees about whether a comparison map exists"
                ))
            }
        };
        sites.push(SiteRead {
            ordinal,
            key,
            patch_surface: site.key.patch_surface.clone(),
            recovered_map,
            lineage: FaceRead {
                training_overlap: lineage_overlap,
                prediction: lineage_prediction,
                held_out_actual: held_lineage,
                held_out_relation: lineage_relation,
            },
            affordance: FaceRead {
                training_overlap: affordance_overlap,
                prediction: affordance_prediction,
                held_out_actual: held.affords_declared_world_action,
                held_out_relation: affordance_relation,
            },
            comparison: comparison_read,
        });
    }

    let recovered_maps = held_out_probe
        .recovered
        .values()
        .filter(|law| law.is_some())
        .count();
    let absent_maps = held_out_probe.recovered.len() - recovered_maps;
    let no_ecology_recovered_maps = no_ecology_probe
        .recovered
        .values()
        .filter(|law| law.is_some())
        .count();
    let available_ordinals = laws.iter().map(|law| law.ordinal).collect::<BTreeSet<_>>();
    let recovered_ordinals = held_out_probe
        .recovered
        .iter()
        .filter_map(|(ordinal, law)| law.as_ref().map(|_| *ordinal))
        .collect::<BTreeSet<_>>();
    let absent_ordinals = held_out_probe
        .recovered
        .iter()
        .filter_map(|(ordinal, law)| law.is_none().then_some(*ordinal))
        .collect::<BTreeSet<_>>();
    let expected_absent = keys
        .keys()
        .copied()
        .filter(|ordinal| !available_ordinals.contains(ordinal))
        .collect::<BTreeSet<_>>();

    let counts_exact = source.summary.sites == 102
        && source.summary.lineage_maps == 38
        && source.summary.lineage_held_out_commutations == 34
        && source.summary.lineage_held_out_residuals == 4
        && source.summary.lineage_training_opens == 64
        && source.summary.affordance_maps == 68
        && source.summary.affordance_held_out_commutations == 64
        && source.summary.affordance_held_out_residuals == 4
        && source.summary.affordance_training_opens == 34
        && source.summary.union_maps == 74
        && source.summary.no_maps == 28;
    let acceptance = AcceptanceRead {
        all_source_counts_exact: counts_exact,
        all_laws_returned_bit_exact: read.returned_exact,
        every_available_map_recovered: recovered_ordinals == available_ordinals,
        no_unavailable_map_invented: absent_ordinals == expected_absent,
        no_ecology_control_recovered_nothing: no_ecology_recovered_maps == 0,
        lineage_maps,
        lineage_held_out_commutations: lineage_commutations,
        lineage_held_out_residuals: lineage_residuals,
        lineage_training_opens,
        affordance_maps,
        affordance_held_out_commutations: affordance_commutations,
        affordance_held_out_residuals: affordance_residuals,
        affordance_training_opens,
        receiver_relative_outcome_differences,
        comparison_commuting_sites,
        comparison_residual_sites,
        comparison_open_bits_exact,
        comparison_created_no_found_pins,
    };
    let accepted = acceptance.all_source_counts_exact
        && acceptance.all_laws_returned_bit_exact
        && acceptance.every_available_map_recovered
        && acceptance.no_unavailable_map_invented
        && acceptance.no_ecology_control_recovered_nothing
        && held_out_probe.queries_exact
        && no_ecology_probe.queries_exact
        && lineage_maps == 38
        && lineage_commutations == 34
        && lineage_residuals == 4
        && lineage_training_opens == 64
        && affordance_maps == 68
        && affordance_commutations == 64
        && affordance_residuals == 4
        && affordance_training_opens == 34
        && receiver_relative_outcome_differences == 3
        && comparison_commuting_sites == 66
        && comparison_residual_sites == 8
        && comparison_open_bits_exact
        && comparison_created_no_found_pins;
    if !accepted {
        return Err("the fixed translation-atlas acceptance did not close".to_owned());
    }

    Ok(Report {
        schema: REPORT_SCHEMA,
        status: "accepted",
        question: "Can two exact contextual charts cultivate partial transformer-to-consequence maps which stand after source departure and lawfully commute or remain open in a third chart?",
        theory_to_structure: "Each site is an actual transformer carrier intervention keyed by family, direction, and typed residual boundary. Conversation and prose found a local map only where their downstream receiver face agrees. That map becomes cellular Standing; code-comment is later Current and is compared independently at lineage and world-affordance receivers.",
        stopping_condition: "One source-derived 102-site atlas; every two-chart overlap deposited once; one source-absent held-out query population; one no-ecology sibling; exact counts of maps, commutations, residuals, and absent maps.",
        source: SourceRead {
            source_sha256,
            source_observation: source.source_observation,
            model: source.model,
            input_artifacts: source.input_artifacts,
            sites: source.summary.sites,
            training_charts: ["conversation", "prose"],
            held_out_chart: "code_comment",
        },
        deposit: read,
        held_out: HeldOutRead {
            queries: held_out_probe.recovered.len(),
            recovered_maps,
            absent_maps,
            query_carriers_exact: held_out_probe.queries_exact,
            no_ecology_recovered_maps,
            machine: held_out_probe.machine,
            no_ecology_machine: no_ecology_probe.machine,
            comparison_machine: comparison.machine,
        },
        sites,
        acceptance,
        conclusion: "The atlas is a partial ecology of translations, not one universal coordinate map. The same inherited site can RIDE at one receiver and remain OPEN at another; disagreement between the training charts creates no map, and disagreement in the held-out chart preserves an oriented residual instead of rewriting the prior overlap.",
    })
}

fn validate_source(source: &Source) -> Result<(Vec<AtlasLaw>, BTreeMap<u16, SiteKey>), String> {
    if source.sites.len() != 102 {
        return Err(format!(
            "source contains {} sites instead of 102",
            source.sites.len()
        ));
    }
    let mut laws = Vec::new();
    let mut keys = BTreeMap::new();
    for (expected_ordinal, site) in source.sites.iter().enumerate() {
        if site.ordinal != expected_ordinal {
            return Err(format!(
                "source site ordinal {} appears at position {expected_ordinal}",
                site.ordinal
            ));
        }
        let ordinal = u16::try_from(site.ordinal).map_err(debug)?;
        let key = SiteKey::from_source(&site.key)?;
        if keys.insert(ordinal, key).is_some() {
            return Err(format!("source repeats ordinal {ordinal}"));
        }
        let conversation = site
            .charts
            .get("conversation")
            .ok_or_else(|| format!("site {ordinal} omits conversation"))?;
        let prose = site
            .charts
            .get("prose")
            .ok_or_else(|| format!("site {ordinal} omits prose"))?;
        let held = site
            .charts
            .get("code_comment")
            .ok_or_else(|| format!("site {ordinal} omits code-comment"))?;
        if site.charts.len() != 3 {
            return Err(format!("site {ordinal} has an undeclared chart"));
        }
        let conversation_lineage = LineageFace::parse(&conversation.lineage_relation)?;
        let prose_lineage = LineageFace::parse(&prose.lineage_relation)?;
        let held_lineage = LineageFace::parse(&held.lineage_relation)?;
        let lineage = (conversation_lineage == prose_lineage).then_some(conversation_lineage);
        let affordance = (conversation.affords_declared_world_action
            == prose.affords_declared_world_action)
            .then_some(conversation.affords_declared_world_action);
        let declared_lineage = site
            .overlap
            .lineage
            .prediction
            .as_deref()
            .map(LineageFace::parse)
            .transpose()?;
        if site.overlap.lineage.available != lineage.is_some() || declared_lineage != lineage {
            return Err(format!("site {ordinal} changed its lineage overlap"));
        }
        if site.overlap.affordance.available != affordance.is_some()
            || site.overlap.affordance.prediction != affordance
        {
            return Err(format!("site {ordinal} changed its affordance overlap"));
        }
        if site.held_out_comparison.lineage_commutes
            != lineage.is_some_and(|prediction| prediction == held_lineage)
            || site.held_out_comparison.affordance_commutes
                != affordance
                    .is_some_and(|prediction| prediction == held.affords_declared_world_action)
        {
            return Err(format!("site {ordinal} changed its held-out comparison"));
        }
        if lineage.is_some() || affordance.is_some() {
            laws.push(AtlasLaw {
                ordinal,
                key,
                lineage,
                affordance,
            });
        }
    }
    if keys.values().copied().collect::<BTreeSet<_>>().len() != keys.len() {
        return Err("two atlas ordinals name the same source-native site".to_owned());
    }
    if laws.len() != 74 {
        return Err(format!("source forms {} maps instead of 74", laws.len()));
    }
    Ok((laws, keys))
}

fn empty_ecology() -> Result<Ecology, String> {
    let mut machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).map_err(debug)?);
    let pair = prime_pairs(&mut machine, 1)?
        .into_iter()
        .next()
        .ok_or_else(|| "one empty-ecology pair remains".to_owned())?;
    let currents = [
        CurrentEvent::ending(pair[0], relation(97)?, action()),
        CurrentEvent::ending(pair[1], relation(101)?, action()),
    ];
    machine
        .receive(ContemporaryEvent::unrelated(&currents))
        .map_err(debug)?;
    Ok(Ecology {
        body: machine.rest_image().map_err(debug)?,
        handles: BTreeMap::new(),
        law_constituents: BTreeMap::new(),
    })
}

fn deposit_laws(
    ecology: Ecology,
    source_sha256: &str,
    laws: &[AtlasLaw],
) -> Result<DepositOutcome, String> {
    let mut machine = LiveCurrentMachine::from_rest_image(ecology.body).map_err(debug)?;
    let standing_before = machine.memory().standing_constituents;
    let pairs = prime_pairs(&mut machine, laws.len())?;
    let handles = laws
        .iter()
        .map(|law| LawHandle::new(source_sha256, law))
        .collect::<Vec<_>>();
    let encoded = laws.iter().map(AtlasLaw::encode).collect::<Vec<_>>();
    let arc_populations = pairs
        .iter()
        .zip(&handles)
        .zip(&encoded)
        .map(|((pair, handle), bytes)| law_seed_arcs(*pair, *handle, bytes))
        .collect::<Vec<_>>();
    let regional = pairs
        .iter()
        .zip(&arc_populations)
        .map(|(pair, arcs)| RegionalRelationCell::new(pair[1], arcs))
        .collect::<Vec<_>>();
    let currents = pairs
        .iter()
        .flat_map(|pair| {
            [
                CurrentEvent::ending(pair[0], relation(103).expect("fixed relation"), action()),
                CurrentEvent::ending(pair[1], relation(107).expect("fixed relation"), action()),
            ]
        })
        .collect::<Vec<_>>();
    let radiation = machine
        .receive(ContemporaryEvent::with_regional(&currents, &[], &regional))
        .map_err(debug)?;
    if radiation.regional().len() != laws.len() {
        return Err("every atlas law must emit one constituent".to_owned());
    }
    let mut returned_exact = true;
    let mut next_handles = BTreeMap::new();
    let mut next_constituents = BTreeMap::new();
    for ((law, handle), returned) in laws.iter().zip(&handles).zip(radiation.regional()) {
        returned_exact &=
            decode_law(returned.constituent(), handle.data_namespace)?.as_ref() == Some(law);
        if next_handles.insert(law.ordinal, *handle).is_some() {
            return Err(format!("atlas law {} was deposited twice", law.ordinal));
        }
        if next_constituents
            .insert(law.ordinal, returned.constituent().clone())
            .is_some()
        {
            return Err(format!("atlas law {} returned twice", law.ordinal));
        }
    }
    let body = machine.rest_image().map_err(debug)?;
    let next = Ecology {
        body: body.clone(),
        handles: next_handles,
        law_constituents: next_constituents,
    };
    let remounted = LiveCurrentMachine::from_rest_image(body.clone()).map_err(debug)?;
    let rest_remount_exact = remounted.rest_image().map_err(debug)? == body;
    let memory = remounted.memory();
    let read = DepositRead {
        laws: laws.len(),
        encoded_bits: encoded.iter().map(|bytes| bytes.len() * 8).sum(),
        returned_exact,
        source_lineages_departed: memory.live_lineages == 0,
        rest_remount_exact,
        standing_before,
        standing_after: memory.standing_constituents,
        machine: machine_read(&remounted)?,
    };
    Ok(DepositOutcome {
        ecology: next,
        read,
    })
}

fn probe(
    ecology: &Ecology,
    source_sha256: &str,
    sites: &[SourceSite],
    keys: &BTreeMap<u16, SiteKey>,
) -> Result<ProbeOutcome, String> {
    let mut machine = LiveCurrentMachine::from_rest_image(ecology.body.clone()).map_err(debug)?;
    let pairs = prime_pairs(&mut machine, sites.len())?;
    let queries = sites
        .iter()
        .map(|site| {
            let ordinal = u16::try_from(site.ordinal).map_err(debug)?;
            Ok(QueryCarrier {
                ordinal,
                key: *keys
                    .get(&ordinal)
                    .ok_or_else(|| format!("query site {ordinal} has no key"))?,
            })
        })
        .collect::<Result<Vec<_>, String>>()?;
    let query_bytes = queries.iter().map(QueryCarrier::encode).collect::<Vec<_>>();
    let query_namespaces = queries
        .iter()
        .zip(&query_bytes)
        .map(|(query, bytes)| {
            namespace(&[
                b"eros-transformer-translation-atlas-query-v1",
                source_sha256.as_bytes(),
                &query.ordinal.to_le_bytes(),
                &query.key.bytes(),
                bytes,
            ])
        })
        .collect::<Vec<_>>();
    let arc_populations = pairs
        .iter()
        .zip(&queries)
        .zip(&query_bytes)
        .zip(&query_namespaces)
        .map(|(((pair, query), bytes), query_namespace)| {
            query_arcs(
                *pair,
                *query_namespace,
                bytes,
                ecology.handles.get(&query.ordinal).copied(),
                namespace(&[
                    b"eros-transformer-translation-atlas-query-identity-v1",
                    source_sha256.as_bytes(),
                    &query.ordinal.to_le_bytes(),
                    &query.key.bytes(),
                ]),
            )
        })
        .collect::<Vec<_>>();
    let regional = pairs
        .iter()
        .zip(&arc_populations)
        .map(|(pair, arcs)| RegionalRelationCell::new(pair[1], arcs))
        .collect::<Vec<_>>();
    let currents = pairs
        .iter()
        .flat_map(|pair| {
            [
                CurrentEvent::ending(pair[0], relation(109).expect("fixed relation"), action()),
                CurrentEvent::ending(pair[1], relation(113).expect("fixed relation"), action()),
            ]
        })
        .collect::<Vec<_>>();
    let radiation = machine
        .receive(ContemporaryEvent::with_regional(&currents, &[], &regional))
        .map_err(debug)?;
    if radiation.regional().len() != sites.len() {
        return Err("every held-out site must emit one query constituent".to_owned());
    }
    let mut recovered = BTreeMap::new();
    let mut queries_exact = true;
    for ((((query, query_namespace), expected_bytes), returned), site) in queries
        .iter()
        .zip(&query_namespaces)
        .zip(&query_bytes)
        .zip(radiation.regional())
        .zip(sites)
    {
        let constituent = returned.constituent();
        let recovered_query = decode_query(constituent, *query_namespace)?;
        queries_exact &= recovered_query.as_ref() == Some(query)
            && query.encode() == *expected_bytes
            && usize::from(query.ordinal) == site.ordinal;
        let law = match ecology.handles.get(&query.ordinal) {
            Some(handle) => decode_law(constituent, handle.data_namespace)?,
            None => None,
        };
        if recovered.insert(query.ordinal, law).is_some() {
            return Err(format!("query ordinal {} returned twice", query.ordinal));
        }
    }
    Ok(ProbeOutcome {
        recovered,
        queries_exact,
        machine: machine_read(&machine)?,
    })
}

fn compare_held_out(
    ecology: &Ecology,
    laws: &[AtlasLaw],
    sites: &[SourceSite],
    keys: &BTreeMap<u16, SiteKey>,
) -> Result<ComparisonOutcome, String> {
    let mut machine = LiveCurrentMachine::from_rest_image(ecology.body.clone()).map_err(debug)?;
    let pairs = prime_pairs(&mut machine, laws.len())?;
    let mut actual_laws = Vec::with_capacity(laws.len());
    for law in laws {
        let site = sites
            .get(usize::from(law.ordinal))
            .ok_or_else(|| format!("comparison site {} is absent", law.ordinal))?;
        let key = *keys
            .get(&law.ordinal)
            .ok_or_else(|| format!("comparison site {} has no key", law.ordinal))?;
        if key != law.key {
            return Err(format!("comparison site {} changed key", law.ordinal));
        }
        let held = site
            .charts
            .get("code_comment")
            .ok_or_else(|| format!("comparison site {} omits code-comment", law.ordinal))?;
        actual_laws.push(AtlasLaw {
            ordinal: law.ordinal,
            key,
            lineage: law
                .lineage
                .map(|_| LineageFace::parse(&held.lineage_relation))
                .transpose()?,
            affordance: law.affordance.map(|_| held.affords_declared_world_action),
        });
    }
    let expected_open_bits = laws
        .iter()
        .zip(&actual_laws)
        .map(|(expected, actual)| differing_bits(&expected.encode(), &actual.encode()))
        .collect::<Vec<_>>();
    let actual_bytes = actual_laws.iter().map(AtlasLaw::encode).collect::<Vec<_>>();
    let arc_populations = pairs
        .iter()
        .zip(laws)
        .zip(&actual_bytes)
        .map(|((pair, law), bytes)| {
            let handle = ecology
                .handles
                .get(&law.ordinal)
                .copied()
                .ok_or_else(|| format!("comparison law {} has no handle", law.ordinal))?;
            Ok(bit_arcs(*pair, handle.data_namespace, bytes, 0))
        })
        .collect::<Result<Vec<_>, String>>()?;
    let regional = pairs
        .iter()
        .zip(&arc_populations)
        .map(|(pair, arcs)| RegionalRelationCell::new(pair[1], arcs))
        .collect::<Vec<_>>();
    let currents = pairs
        .iter()
        .flat_map(|pair| {
            [
                CurrentEvent::ending(pair[0], relation(127).expect("fixed relation"), action()),
                CurrentEvent::ending(pair[1], relation(131).expect("fixed relation"), action()),
            ]
        })
        .collect::<Vec<_>>();
    let radiation = machine
        .receive(ContemporaryEvent::with_regional(&currents, &[], &regional))
        .map_err(debug)?;
    if radiation.regional().len() != laws.len() {
        return Err("every held-out map must emit one comparison constituent".to_owned());
    }
    let mut reads = BTreeMap::new();
    for (((law, expected), returned), handle) in laws
        .iter()
        .zip(&expected_open_bits)
        .zip(radiation.regional())
        .zip(laws.iter().map(|law| {
            ecology
                .handles
                .get(&law.ordinal)
                .copied()
                .expect("validated atlas handle")
        }))
    {
        let constituent = returned.constituent();
        let prior = ecology
            .law_constituents
            .get(&law.ordinal)
            .ok_or_else(|| format!("comparison law {} has no standing body", law.ordinal))?;
        let prior_bits = prior
            .pins()
            .iter()
            .filter_map(|pin| {
                pin.interface()
                    .filter(|interface| interface.namespace() == handle.data_namespace)
                    .map(|interface| (interface.local(), pin.clone()))
            })
            .collect::<BTreeMap<_, _>>();
        if prior_bits.len() != law.encode().len() * 8 {
            return Err(format!(
                "comparison law {} does not retain one standing pin per encoded bit",
                law.ordinal
            ));
        }
        let mut carried_open_bits = Vec::new();
        let mut found_pins = 0usize;
        for (local, prior_pin) in prior_bits {
            let comparison_pins = constituent
                .pins()
                .iter()
                .filter(|pin| !prior.pins().contains(pin))
                .filter(|pin| {
                    pin.interface().is_some_and(|interface| {
                        interface.namespace() == handle.data_namespace && interface.local() == local
                    })
                })
                .filter(|pin| pin.held() == prior_pin.meeting())
                .collect::<Vec<_>>();
            if comparison_pins.len() != 1 {
                return Err(format!(
                    "comparison law {} bit {local} returned {} comparison pins instead of one",
                    law.ordinal,
                    comparison_pins.len()
                ));
            }
            let comparison_pin = comparison_pins[0];
            if comparison_pin.is_open() {
                carried_open_bits.push(local);
            }
            found_pins += usize::from(comparison_pin.is_found());
        }
        let read = ComparisonCarrierRead {
            expected_open_bits: expected.clone(),
            open_bits_exact: carried_open_bits == *expected,
            carried_open_bits,
            found_pins,
        };
        if reads.insert(law.ordinal, read).is_some() {
            return Err(format!("comparison site {} returned twice", law.ordinal));
        }
    }
    Ok(ComparisonOutcome {
        sites: reads,
        machine: machine_read(&machine)?,
    })
}

fn law_seed_arcs(
    pair: [CurrentLineage; 2],
    handle: LawHandle,
    bytes: &[u8],
) -> Vec<RegionalRelationArc> {
    let mut arcs = bit_arcs(pair, handle.data_namespace, bytes, 0);
    let slot = u32::try_from(arcs.len()).expect("bounded atlas-law carrier");
    arcs.push(interface_arc(
        pair,
        handle.recruit_namespace,
        RECRUIT_LOCAL,
        slot,
        IncidenceHand::Against,
    ));
    arcs
}

fn query_arcs(
    pair: [CurrentLineage; 2],
    query_namespace: u64,
    query_bytes: &[u8],
    handle: Option<LawHandle>,
    query_identity: u64,
) -> Vec<RegionalRelationArc> {
    let mut arcs = bit_arcs(pair, query_namespace, query_bytes, 0);
    if let Some(handle) = handle {
        let slot = u32::try_from(arcs.len()).expect("bounded atlas query");
        arcs.push(interface_arc(
            pair,
            handle.recruit_namespace,
            RECRUIT_LOCAL,
            slot,
            IncidenceHand::Against,
        ));
        let renewed = handle.renewed(query_identity);
        let slot = u32::try_from(arcs.len()).expect("bounded atlas query");
        arcs.push(interface_arc(
            pair,
            renewed.recruit_namespace,
            RECRUIT_LOCAL,
            slot,
            IncidenceHand::With,
        ));
    }
    arcs
}

fn bit_arcs(
    pair: [CurrentLineage; 2],
    namespace: u64,
    bytes: &[u8],
    first_slot: u32,
) -> Vec<RegionalRelationArc> {
    bytes
        .iter()
        .flat_map(|byte| (0..8).map(move |bit| byte >> bit & 1 != 0))
        .enumerate()
        .map(|(at, bit)| {
            interface_arc(
                pair,
                namespace,
                at as u64,
                first_slot + u32::try_from(at).expect("bounded bit carrier"),
                if bit {
                    IncidenceHand::With
                } else {
                    IncidenceHand::Against
                },
            )
        })
        .collect()
}

fn differing_bits(left: &[u8], right: &[u8]) -> Vec<u64> {
    assert_eq!(
        left.len(),
        right.len(),
        "typed atlas carriers have equal extent"
    );
    left.iter()
        .zip(right)
        .enumerate()
        .flat_map(|(octet, (left, right))| {
            let difference = left ^ right;
            (0..8).filter_map(move |bit| {
                (difference >> bit & 1 != 0).then_some((octet * 8 + bit) as u64)
            })
        })
        .collect()
}

fn interface_arc(
    pair: [CurrentLineage; 2],
    namespace: u64,
    local: u64,
    boundary_slot: u32,
    hand: IncidenceHand,
) -> RegionalRelationArc {
    RegionalRelationArc::new(
        pair[0],
        CurrentBoundaryPort::Cell,
        pair[1],
        CurrentBoundaryPort::Cell,
        InterfaceCapability::new(namespace, local),
        boundary_slot,
        0,
        hand,
    )
}

fn decode_law(constituent: &LiveConstituent, namespace: u64) -> Result<Option<AtlasLaw>, String> {
    decode_bytes(constituent, namespace)?
        .as_deref()
        .map(AtlasLaw::decode)
        .transpose()
}

fn decode_query(
    constituent: &LiveConstituent,
    namespace: u64,
) -> Result<Option<QueryCarrier>, String> {
    decode_bytes(constituent, namespace)?
        .as_deref()
        .map(QueryCarrier::decode)
        .transpose()
}

fn decode_bytes(constituent: &LiveConstituent, namespace: u64) -> Result<Option<Vec<u8>>, String> {
    let exposed: BTreeSet<u32> = constituent.exposed().iter().copied().collect();
    let mut bits = BTreeMap::new();
    for pin_at in exposed {
        let pin = constituent
            .pins()
            .get(usize::try_from(pin_at).map_err(debug)?)
            .ok_or_else(|| "an exposed pin remains in the constituent".to_owned())?;
        let Some(interface) = pin.interface() else {
            continue;
        };
        if interface.namespace() != namespace {
            continue;
        }
        let mut hand = None;
        for incidence in constituent
            .incidences()
            .iter()
            .copied()
            .filter(|incidence| incidence.pin() == pin_at)
        {
            match hand {
                None => hand = Some(incidence.hand()),
                Some(prior) if prior == incidence.hand() => {}
                Some(_) => return Err("one carried bit has mixed residual hands".to_owned()),
            }
        }
        let hand = hand.ok_or_else(|| "one carried bit has no incidence".to_owned())?;
        if bits
            .insert(interface.local(), hand == IncidenceHand::With)
            .is_some()
        {
            return Err("one carried bit position is exposed twice".to_owned());
        }
    }
    if bits.is_empty() {
        return Ok(None);
    }
    let extent = bits.keys().next_back().copied().expect("nonempty bits") + 1;
    if bits.len() as u64 != extent || !extent.is_multiple_of(8) {
        return Err("carried bit positions are not one complete octet sequence".to_owned());
    }
    let mut bytes = Vec::with_capacity(usize::try_from(extent / 8).map_err(debug)?);
    for octet in 0..extent / 8 {
        let mut byte = 0u8;
        for bit in 0..8 {
            if bits
                .get(&(octet * 8 + bit))
                .copied()
                .ok_or_else(|| "one carried bit position is absent".to_owned())?
            {
                byte |= 1 << bit;
            }
        }
        bytes.push(byte);
    }
    Ok(Some(bytes))
}

fn prime_pairs(
    machine: &mut LiveCurrentMachine,
    count: usize,
) -> Result<Vec<[CurrentLineage; 2]>, String> {
    let first = relation(PRIMING_VALUES[0])?;
    let mut pairs = Vec::with_capacity(count);
    for _ in 0..count {
        pairs.push([
            machine
                .attach(CurrentGeometry::Cell(first))
                .map_err(debug)?,
            machine
                .attach(CurrentGeometry::Cell(first))
                .map_err(debug)?,
        ]);
    }
    for value in PRIMING_VALUES {
        let currents = pairs
            .iter()
            .flat_map(|pair| {
                [
                    CurrentEvent::continuing(
                        pair[0],
                        relation(value).expect("fixed relation"),
                        action(),
                    ),
                    CurrentEvent::continuing(
                        pair[1],
                        relation(value).expect("fixed relation"),
                        action(),
                    ),
                ]
            })
            .collect::<Vec<_>>();
        machine
            .receive(ContemporaryEvent::unrelated(&currents))
            .map_err(debug)?;
    }
    Ok(pairs)
}

fn machine_read(machine: &LiveCurrentMachine) -> Result<MachineRead, String> {
    let LiveMemory {
        standing_cells,
        standing_constituents,
        constituent_cells,
        constituent_incidences,
        constituent_pins,
        constituent_paths,
        constituent_transport_terms,
        live_lineages,
        ..
    } = machine.memory();
    let rest_octets = machine
        .rest_image()
        .map_err(debug)?
        .encode_native_bytes()
        .map_err(debug)?;
    // THE_ASSEMBLY.md step 5, loop (d): *the signal is the octets*. The hash below is untouched and
    // still reported; these are the same octets reaching `holon-plate deposit --from ERST:` instead
    // of being hashed and dropped. This site sits inside a helper the driver calls at every read.
    // The address is the content, so every distinct rest it seals is deposited at its own address
    // instead of all but the last being overwritten, and the file name carries the reported hash.
    let deposited = deposit_form_or_message(FORM_DRIVER, MACHINE_REST_FORM, &rest_octets)?;
    eprintln!("form deposited: {}", deposited.path.display());
    Ok(MachineRead {
        standing_rank: machine.standing().rank(),
        standing_cells,
        standing_constituents,
        constituent_cells,
        constituent_incidences,
        constituent_pins,
        constituent_paths,
        constituent_transport_terms,
        live_lineages,
        rest_sha256: sha256(&rest_octets),
    })
}

fn relation(value: i64) -> Result<RelationAtom, String> {
    RelationAtom::new(Cog::lit(value))
        .ok_or_else(|| format!("relation value {value} remains nonzero"))
}

fn action() -> ActionCurrent {
    ActionCurrent::new(Cog::lit(1)).expect("one is a resolving action")
}

fn take<'a>(bytes: &'a [u8], cursor: &mut usize, count: usize) -> Result<&'a [u8], String> {
    let end = cursor
        .checked_add(count)
        .ok_or_else(|| "carrier cursor overflowed".to_owned())?;
    let slice = bytes
        .get(*cursor..end)
        .ok_or_else(|| "carrier ended before its declared extent".to_owned())?;
    *cursor = end;
    Ok(slice)
}

fn read_u16(bytes: &[u8], cursor: &mut usize) -> Result<u16, String> {
    Ok(u16::from_le_bytes(
        take(bytes, cursor, 2)?.try_into().map_err(debug)?,
    ))
}

fn namespace(parts: &[&[u8]]) -> u64 {
    let mut digest = Sha256::new();
    for part in parts {
        digest.update(part);
        digest.update([0]);
    }
    u64::from_le_bytes(
        digest.finalize()[..8]
            .try_into()
            .expect("SHA-256 has eight bytes"),
    )
}

fn sha256(bytes: &[u8]) -> String {
    hex_digest(Sha256::digest(bytes))
}

fn hex_digest(bytes: impl IntoIterator<Item = u8>) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut result = String::new();
    for byte in bytes {
        result.push(HEX[(byte >> 4) as usize] as char);
        result.push(HEX[(byte & 15) as usize] as char);
    }
    result
}

fn usage() -> &'static str {
    "usage: eros_transformer_translation_atlas <source.json> <new-report.json>"
}

fn debug(error: impl Debug) -> String {
    format!("{error:?}")
}
