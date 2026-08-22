//! Mount M2's exterior chart as a finite caused action without using foreign architecture names as
//! receiver classes.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use holonic_engine::exact_work::ExactWork;
use holonic_engine::receiver_exact_compression::{
    InputId, ItemId, Observation, ObservedSystem, ReceiverId,
};
use serde::{Deserialize, Serialize};

pub const CHRONOLOGY: InputId = InputId(0);
pub const REFLOW_CHART: InputId = InputId(1);
pub const BOUNDARY_RECEIVER: ReceiverId = ReceiverId(0);
pub const SUPPORT_RECEIVER: ReceiverId = ReceiverId(1);
pub const PREFIX_RECEIVER: ReceiverId = ReceiverId(2);

const M2_ARTIFACT: &str =
    "output/the_mathematics_codec_excites_the_active_transport_cover/active-transport-cover.json";

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Deserialize)]
struct Address {
    ordinal: usize,
    source_layer: Option<usize>,
    local_boundary_ordinal: usize,
    /// Retained as source lineage but deliberately absent from every receiver signature.
    lineage: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Deserialize)]
struct Run {
    start: usize,
    end: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Deserialize)]
struct Separator {
    #[allow(dead_code)]
    face: Address,
    cell: usize,
    base: [i64; 2],
    candidate: [i64; 2],
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Deserialize)]
struct Difference {
    #[allow(dead_code)]
    face: Address,
    cells: usize,
    identical: usize,
    separated: usize,
    unresolved_overlap: usize,
    separated_support: Vec<Run>,
    unresolved_support: Vec<Run>,
    first_separator: Option<Separator>,
}

#[derive(Deserialize)]
struct Support {
    differences: Vec<Difference>,
}

#[derive(Deserialize)]
struct Face {
    address: Address,
    cells: usize,
    /// Parsed for audit only. A digest never participates in receiver equality.
    #[allow(dead_code)]
    exact_cells_sha256: String,
    inherited_from_base: bool,
}

#[derive(Deserialize)]
struct Cochain {
    occurrence: String,
    faces: Vec<Face>,
}

#[derive(Deserialize)]
struct Response {
    occurrence: String,
    tower: usize,
    declaration_lineage: String,
    cochain: Cochain,
    support: Support,
    exact_work: ExactWork,
}

#[derive(Deserialize)]
struct Excitation {
    occurrence: String,
}

#[derive(Deserialize)]
struct OpenFibre {
    occurrence: String,
    question: String,
}

#[derive(Deserialize)]
struct Family {
    excitation: Excitation,
    apparatus: Apparatus,
    responses: Vec<Response>,
    open_fibres: Vec<OpenFibre>,
}

#[derive(Deserialize)]
struct Apparatus {
    graph_launches: u64,
    terminal_synchronizations: u64,
    asynchronous_copy_octets: u64,
    host_ingress_octets: u64,
    host_egress_section_octets: u64,
    resident_octets_peak: u64,
}

#[derive(Deserialize)]
struct Control {
    occurrence: String,
    left: String,
    right: String,
    held: bool,
    first_separator: Option<Separator>,
}

#[derive(Deserialize)]
struct M2Chart {
    schema: String,
    native_rest: String,
    families: Vec<Family>,
    cross_occurrence_controls: Vec<Control>,
    m2_open_fibres: Vec<OpenFibre>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum BoundarySignature {
    Face {
        ordinal: usize,
        source_layer: Option<usize>,
        local_boundary_ordinal: usize,
        cells: usize,
    },
    /// Pointed completion of M2's open exterior. This turns the partial chronology into the total
    /// `T : X -> X` required by M3 without identifying the final face with its terminus.
    ExteriorTerminus,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum SupportSignature {
    Face(Difference),
    ExteriorTerminus,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct StateAddress {
    pub source: ItemId,
    pub excitation_occurrence: String,
    pub response_occurrence: String,
    pub tower: usize,
    pub receiver_history_ordinal: Option<usize>,
    pub adjoined_exterior_terminus: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct GeneratorDeclaration {
    pub generator: InputId,
    pub source_port: String,
    pub receiving_port: String,
    pub constitutive_law: String,
    pub evidence: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct UnclosedComposition {
    pub left_occurrence: String,
    pub right_occurrence: String,
    pub reason: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct OpenDomainReceipt {
    pub source_open_fibres: Vec<(String, String)>,
    pub unclosed_intervention_pairs: Vec<UnclosedComposition>,
}

pub struct ActiveCoverSystem {
    items: Vec<ItemId>,
    observations: BTreeMap<(ItemId, ReceiverId), Observation>,
    successors: BTreeMap<(ItemId, InputId), ItemId>,
}

impl ObservedSystem for ActiveCoverSystem {
    fn items(&self) -> Vec<ItemId> {
        self.items.clone()
    }

    fn receivers(&self) -> Vec<ReceiverId> {
        vec![BOUNDARY_RECEIVER, SUPPORT_RECEIVER, PREFIX_RECEIVER]
    }

    fn inputs(&self) -> Vec<InputId> {
        vec![CHRONOLOGY, REFLOW_CHART]
    }

    fn observation(&self, item: ItemId, receiver: ReceiverId) -> Observation {
        self.observations[&(item, receiver)]
    }

    fn successor(&self, item: ItemId, input: InputId) -> Option<ItemId> {
        self.successors.get(&(item, input)).copied()
    }

    fn admitted(&self, input: InputId) -> Option<Vec<(ItemId, ItemId)>> {
        Some(
            self.items
                .iter()
                .map(|item| (*item, self.successors[&(*item, input)]))
                .collect(),
        )
    }
}

pub struct Recovery {
    pub source_path: PathBuf,
    pub source_octets: u64,
    pub source_schema: String,
    pub system: ActiveCoverSystem,
    pub states: Vec<StateAddress>,
    pub generators: Vec<GeneratorDeclaration>,
    pub open_domain: OpenDomainReceipt,
    pub source_exact_work: ExactWork,
    pub source_decoder_path: PathBuf,
    pub source_decoder_octets: u64,
    pub source_apparatus: SourceApparatus,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize)]
pub struct SourceApparatus {
    pub graph_launches: u64,
    pub terminal_synchronizations: u64,
    pub host_ingress_octets: u64,
    pub host_egress_octets: u64,
    pub device_copy_octets: u64,
    pub resident_octets_peak: u64,
}

pub fn recover(root: &Path) -> Result<Recovery, String> {
    let source_path = root.join(M2_ARTIFACT);
    let bytes = std::fs::read(&source_path).map_err(|error| error.to_string())?;
    let chart: M2Chart = serde_json::from_slice(&bytes).map_err(|error| error.to_string())?;
    if chart.families.is_empty() {
        return Err("M2 returned no active-transport families".to_owned());
    }

    let reflow = chart
        .cross_occurrence_controls
        .iter()
        .find(|control| control.held && control.first_separator.is_none())
        .ok_or_else(|| "M2 returned no exact cross-occurrence chart control".to_owned())?;
    let (left_family, left_response) = locate_response(&chart.families, &reflow.left)?;
    let (right_family, right_response) = locate_response(&chart.families, &reflow.right)?;

    let mut items = Vec::new();
    let mut source_exact_work = ExactWork::nothing();
    let mut source_apparatus = SourceApparatus::default();
    let mut states = Vec::new();
    let mut item_at = BTreeMap::<(usize, usize, usize), ItemId>::new();
    let mut boundary_keys = Vec::new();
    let mut support_keys = Vec::new();
    let mut prefix_keys = Vec::new();
    for (family_at, family) in chart.families.iter().enumerate() {
        source_apparatus.graph_launches += family.apparatus.graph_launches;
        source_apparatus.terminal_synchronizations += family.apparatus.terminal_synchronizations;
        source_apparatus.host_ingress_octets += family.apparatus.host_ingress_octets;
        source_apparatus.host_egress_octets += family.apparatus.host_egress_section_octets;
        source_apparatus.device_copy_octets += family.apparatus.asynchronous_copy_octets;
        source_apparatus.resident_octets_peak = source_apparatus
            .resident_octets_peak
            .max(family.apparatus.resident_octets_peak);
        for (response_at, response) in family.responses.iter().enumerate() {
            source_exact_work = source_exact_work.then(&response.exact_work);
            if response.cochain.faces.len() != response.support.differences.len() {
                return Err(format!(
                    "{} cochain/support extents disagree",
                    response.occurrence
                ));
            }
            for (face_at, (face, difference)) in response
                .cochain
                .faces
                .iter()
                .zip(&response.support.differences)
                .enumerate()
            {
                if face.address.ordinal != face_at || difference.face.ordinal != face_at {
                    return Err(format!(
                        "{} receiver chronology is not addressed in order",
                        response.occurrence
                    ));
                }
                let source = ItemId(items.len() as u64);
                items.push(source);
                item_at.insert((family_at, response_at, face_at), source);
                states.push(StateAddress {
                    source,
                    excitation_occurrence: family.excitation.occurrence.clone(),
                    response_occurrence: response.occurrence.clone(),
                    tower: response.tower,
                    receiver_history_ordinal: Some(face_at),
                    adjoined_exterior_terminus: false,
                });
                boundary_keys.push((
                    source,
                    BoundarySignature::Face {
                        ordinal: face.address.ordinal,
                        source_layer: face.address.source_layer,
                        local_boundary_ordinal: face.address.local_boundary_ordinal,
                        cells: face.cells,
                    },
                ));
                support_keys.push((source, SupportSignature::Face(difference.clone())));
                prefix_keys.push((source, face.inherited_from_base));
            }
            let terminus_at = response.cochain.faces.len();
            let source = ItemId(items.len() as u64);
            items.push(source);
            item_at.insert((family_at, response_at, terminus_at), source);
            states.push(StateAddress {
                source,
                excitation_occurrence: family.excitation.occurrence.clone(),
                response_occurrence: response.occurrence.clone(),
                tower: response.tower,
                receiver_history_ordinal: None,
                adjoined_exterior_terminus: true,
            });
            boundary_keys.push((source, BoundarySignature::ExteriorTerminus));
            support_keys.push((source, SupportSignature::ExteriorTerminus));
            prefix_keys.push((source, false));
        }
    }

    let boundary = identities(boundary_keys);
    let support = identities(support_keys);
    let prefix = identities(prefix_keys);
    let mut observations = BTreeMap::new();
    for item in &items {
        observations.insert((*item, BOUNDARY_RECEIVER), boundary[item]);
        observations.insert((*item, SUPPORT_RECEIVER), support[item]);
        observations.insert((*item, PREFIX_RECEIVER), prefix[item]);
    }

    let mut successors = BTreeMap::new();
    for (family_at, family) in chart.families.iter().enumerate() {
        for (response_at, response) in family.responses.iter().enumerate() {
            let terminus = response.cochain.faces.len();
            for face_at in 0..=terminus {
                let item = item_at[&(family_at, response_at, face_at)];
                let next = item_at[&(family_at, response_at, (face_at + 1).min(terminus))];
                successors.insert((item, CHRONOLOGY), next);
                let charted = if family_at == left_family && response_at == left_response {
                    item_at[&(right_family, right_response, face_at)]
                } else if family_at == right_family && response_at == right_response {
                    item_at[&(left_family, left_response, face_at)]
                } else {
                    item
                };
                successors.insert((item, REFLOW_CHART), charted);
            }
        }
    }

    // M2 ran singleton interventions. Their pairwise composites were never conducted and hence
    // cannot be inserted into the total generator family by declaration.
    let interventions = chart
        .families
        .iter()
        .flat_map(|family| {
            family
                .responses
                .iter()
                .filter(|response| response.tower >= 2)
        })
        .map(|response| {
            (
                response.occurrence.clone(),
                response.declaration_lineage.clone(),
            )
        })
        .collect::<Vec<_>>();
    let mut unclosed_intervention_pairs = Vec::new();
    for (at, left) in interventions.iter().enumerate() {
        for right in &interventions[at + 1..] {
            unclosed_intervention_pairs.push(UnclosedComposition {
                left_occurrence: left.0.clone(),
                right_occurrence: right.0.clone(),
                reason: "M2 conducted each perturbation against the base but did not conduct this composite; order and interaction remain an open transport fibre".to_owned(),
            });
        }
    }
    let mut source_open_fibres = chart
        .families
        .iter()
        .flat_map(|family| &family.open_fibres)
        .chain(&chart.m2_open_fibres)
        .map(|fibre| (fibre.occurrence.clone(), fibre.question.clone()))
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    source_open_fibres.sort();

    let source_decoder_path = root.join(&chart.native_rest);
    let source_decoder_octets = std::fs::metadata(&source_decoder_path)
        .map_err(|error| format!("source decoder {}: {error}", source_decoder_path.display()))?
        .len();
    Ok(Recovery {
        source_path,
        source_octets: bytes.len() as u64,
        source_schema: chart.schema,
        system: ActiveCoverSystem {
            items,
            observations,
            successors,
        },
        states,
        generators: vec![
            GeneratorDeclaration {
                generator: CHRONOLOGY,
                source_port: "one addressed receiver-history face or exterior terminus".to_owned(),
                receiving_port: "its immediate caused successor in the same response cochain".to_owned(),
                constitutive_law: "advance one face; the explicitly adjoined exterior terminus rests on itself".to_owned(),
                evidence: "all ninety-five complete M2 response cochains".to_owned(),
            },
            GeneratorDeclaration {
                generator: REFLOW_CHART,
                source_port: reflow.left.clone(),
                receiving_port: reflow.right.clone(),
                constitutive_law: "the exact harmless chart involution exchanges the two witnessed base cochains and fixes every unposed branch".to_owned(),
                evidence: reflow.occurrence.clone(),
            },
        ],
        open_domain: OpenDomainReceipt {
            source_open_fibres,
            unclosed_intervention_pairs,
        },
        source_exact_work,
        source_decoder_path,
        source_decoder_octets,
        source_apparatus,
    })
}

fn locate_response(families: &[Family], occurrence: &str) -> Result<(usize, usize), String> {
    families
        .iter()
        .enumerate()
        .find_map(|(family_at, family)| {
            family
                .responses
                .iter()
                .position(|response| response.cochain.occurrence == occurrence)
                .map(|response_at| (family_at, response_at))
        })
        .ok_or_else(|| format!("cross-occurrence control endpoint {occurrence} is absent"))
}

fn identities<K: Ord>(keyed: Vec<(ItemId, K)>) -> BTreeMap<ItemId, Observation> {
    let mut dictionary = BTreeMap::<K, Observation>::new();
    let mut returned = BTreeMap::new();
    for (item, key) in keyed {
        let next = Observation(dictionary.len() as u64);
        let identity = *dictionary.entry(key).or_insert(next);
        returned.insert(item, identity);
    }
    returned
}
