use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::causal::EventId;
use crate::evolution::EvolutionLawId;
use crate::ported_operation::{OperationSpecies, PortedOperationComplex, SourceTestimony};
use crate::resident_law::ResidentLaw;

use super::errors::CorrespondenceRefusal;

/// A source operation occurrence.  `id` is stable across deeds and is never an address.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SourceOperationOccurrence {
    pub id: String,
    /// Content identity of the complete source deed topology.  Event ids are local, so the
    /// fingerprint is part of the identity rather than an optional diagnostic.
    pub source_identity: String,
    pub deed: String,
    /// Parametric law family (for example a layer/species/role family), kept apart from one
    /// concrete graph instance.  `parameters` are the generator's declared shape axes; an empty
    /// map is valid for a genuinely generic source deed but never supplies a runtime extent.
    pub family: String,
    pub parameters: BTreeMap<String, String>,
    pub event: EventId,
    pub law: EvolutionLawId,
    pub operation: String,
    pub species: OperationSpecies,
    pub inputs: Vec<String>,
    pub outputs: Vec<String>,
    pub carrier: Option<String>,
}

impl SourceOperationOccurrence {
    /// Enumerate all occurrences in one admitted source deed, preserving port lineage by name.
    /// The caller supplies the deed name because event ids are local to a complex.
    pub fn from_complex(
        deed: impl Into<String>,
        complex: &PortedOperationComplex,
    ) -> Result<Vec<Self>, CorrespondenceRefusal> {
        let deed = deed.into();
        Self::from_complex_family(deed.clone(), deed, BTreeMap::new(), complex)
    }

    /// Enumerate one parametric family while retaining the concrete deed as lineage.  Runtime
    /// extents belong to a later graph instance; they are not silently inferred from this record.
    pub fn from_complex_family(
        deed: impl Into<String>,
        family: impl Into<String>,
        parameters: BTreeMap<String, String>,
        complex: &PortedOperationComplex,
    ) -> Result<Vec<Self>, CorrespondenceRefusal> {
        let deed = deed.into();
        let family = family.into();
        if deed.is_empty() {
            return Err(CorrespondenceRefusal::EmptyDeed);
        }
        if family.is_empty() {
            return Err(CorrespondenceRefusal::EmptyFamily);
        }
        let source_identity = topology_identity(complex);
        let family_identity = format!(
            "{:x}",
            Sha256::digest(
                serde_json::to_vec(&(&family, &parameters))
                    .expect("family witness is serializable")
            )
        );
        let mut occurrences = Vec::with_capacity(complex.shape.occurrences.len());
        for (event, occurrence) in &complex.shape.occurrences {
            let operation = complex.operations.get(&occurrence.law).ok_or(
                CorrespondenceRefusal::MissingOperation {
                    event: *event,
                    law: occurrence.law,
                },
            )?;
            let law = complex.shape.laws.get(&occurrence.law).ok_or(
                CorrespondenceRefusal::MissingLaw {
                    event: *event,
                    law: occurrence.law,
                },
            )?;
            let port_name = |port| {
                complex
                    .shape
                    .boundaries
                    .objects
                    .get(port)
                    .map(|boundary| boundary.name.clone())
                    .ok_or(CorrespondenceRefusal::MissingBoundary {
                        event: *event,
                        law: occurrence.law,
                        boundary: port.0,
                    })
            };
            let inputs = law
                .inputs
                .iter()
                .map(port_name)
                .collect::<Result<Vec<_>, _>>()?;
            let outputs = law
                .outputs
                .iter()
                .map(port_name)
                .collect::<Result<Vec<_>, _>>()?;
            occurrences.push(Self {
                id: format!(
                    "{deed}::{family_identity}::{}::event-{}",
                    source_identity, event.0
                ),
                source_identity: source_identity.clone(),
                deed: deed.clone(),
                family: family.clone(),
                parameters: parameters.clone(),
                event: *event,
                law: occurrence.law,
                operation: law.name.clone(),
                species: operation.species,
                inputs,
                outputs,
                carrier: operation.carrier.clone(),
            });
        }
        Ok(occurrences)
    }
}

/// Content identity of the complete admitted operation complex, including its shape, operation
/// species/carriers/testimony, realization witness and retained open questions. This proves that
/// same-shape bodies with different law evidence cannot silently become one record.
pub fn topology_identity(complex: &PortedOperationComplex) -> String {
    // Source locators are exterior apparatus addresses.  They must not become identity:
    // relocating the same authenticated implementation cannot change the operation topology.
    let mut normalized = complex.clone();
    for operation in normalized.operations.values_mut() {
        for testimony in &mut operation.testimony {
            if let SourceTestimony::Implementation { locator, .. } = testimony {
                locator.clear();
            }
        }
    }
    let bytes = serde_json::to_vec(&normalized).expect("PortedOperationComplex is serializable");
    format!("{:x}", Sha256::digest(bytes))
}

/// One source/native port correspondence.  Equal extents do not imply equal identity; both names
/// remain in the receipt.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PortCorrespondence {
    pub ordinal: usize,
    pub source: String,
    pub native: String,
}

/// Stable graph identity for a native resident realization.  These are identity receipts, not a
/// claim that the graph has run.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeGraphIdentity {
    pub key: String,
    pub nodes: u64,
    pub edges: u64,
    pub tiling: String,
    pub reductions: Vec<String>,
    /// Addressed native law chronology for this concrete graph instance.
    pub chronology: Vec<String>,
    /// Complete operation-topology witness for this concrete graph instance.
    pub topology: Vec<String>,
}

impl NativeGraphIdentity {
    /// Derive an identity from the graph receipt's complete named topology.  A caller cannot
    /// choose an unrelated key and have it accepted as graph evidence.
    pub fn derived(
        nodes: u64,
        edges: u64,
        tiling: impl Into<String>,
        reductions: Vec<String>,
    ) -> Self {
        Self::derived_with_topology(nodes, edges, tiling, reductions, Vec::new(), Vec::new())
    }

    /// Derive an identity from the graph's addressed law chronology and operation topology in
    /// addition to the apparatus census. Counts alone deliberately cannot identify a graph.
    pub fn derived_with_topology(
        nodes: u64,
        edges: u64,
        tiling: impl Into<String>,
        reductions: Vec<String>,
        chronology: Vec<String>,
        topology: Vec<String>,
    ) -> Self {
        let tiling = tiling.into();
        let witness = (nodes, edges, &tiling, &reductions, &chronology, &topology);
        let key = format!(
            "{:x}",
            Sha256::digest(serde_json::to_vec(&witness).expect("graph witness is serializable"))
        );
        Self {
            key,
            nodes,
            edges,
            tiling,
            reductions,
            chronology,
            topology,
        }
    }

    pub(crate) fn is_derived(&self) -> bool {
        let derived = Self::derived_with_topology(
            self.nodes,
            self.edges,
            self.tiling.clone(),
            self.reductions.clone(),
            self.chronology.clone(),
            self.topology.clone(),
        );
        derived.key == self.key
    }

    pub(super) fn has_complete_topology(&self) -> bool {
        !self.chronology.is_empty()
            && !self.topology.is_empty()
            && self
                .reductions
                .iter()
                .all(|reduction| !reduction.is_empty())
    }
}

/// A source occurrence bound to one native law and one resident graph.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeOperationBinding {
    pub source_id: String,
    pub resident_law: String,
    pub species: OperationSpecies,
    /// Native population corresponding to the source operation's carrier, when it has one.
    pub native_population: Option<String>,
    pub inputs: Vec<PortCorrespondence>,
    pub outputs: Vec<PortCorrespondence>,
    /// Key into [`OperationCorrespondenceSeal::graphs`].  The graph registry is the sole owner
    /// of concrete graph identities; bindings carry only the addressed relation so a large
    /// chronology/topology is not serialized once per operation.
    pub graph_key: String,
}

impl NativeOperationBinding {
    /// Capture the serializable identity exposed by a resident law.  Graph and port names remain
    /// caller-supplied because this owner does not inspect a live graph or schedule a deed.
    pub fn from_law(
        source_id: impl Into<String>,
        law: &dyn ResidentLaw,
        inputs: Vec<PortCorrespondence>,
        outputs: Vec<PortCorrespondence>,
        graph_key: impl Into<String>,
    ) -> Self {
        Self {
            source_id: source_id.into(),
            resident_law: law.name().to_owned(),
            species: law.species(),
            native_population: None,
            inputs,
            outputs,
            graph_key: graph_key.into(),
        }
    }
}

/// Why a source occurrence has not yet received a native law.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OpenRemainder {
    pub name: String,
    pub reason: String,
    pub reopening: String,
}

/// Exactly one native binding or one named open remainder is owed by every source occurrence.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum OperationResolution {
    Native(NativeOperationBinding),
    Open(OpenRemainder),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OperationCorrespondence {
    pub source_id: String,
    pub resolution: OperationResolution,
}

/// One source population's complete disposition.  A population can be shared by several source
/// operations; it is listed once here and its operation uses remain in the occurrence records.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum PopulationResolution {
    Native { native_population: String },
    Open(OpenRemainder),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PopulationCorrespondence {
    pub source_population: String,
    pub resolution: PopulationResolution,
}

/// A complete, deterministic W1 correspondence seal.  `source_operations` and
/// `source_populations` are the admitted source closure; the two correspondence vectors are the
/// complete returned coverage of that closure.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OperationCorrespondenceSeal {
    pub schema: String,
    pub source_operations: Vec<SourceOperationOccurrence>,
    pub operations: Vec<OperationCorrespondence>,
    pub source_populations: Vec<String>,
    pub populations: Vec<PopulationCorrespondence>,
    /// Canonical, unique concrete graph identities addressed by native bindings and law records.
    pub graphs: Vec<NativeGraphIdentity>,
}
