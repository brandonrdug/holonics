use std::collections::{BTreeMap, BTreeSet};

use super::errors::{CorrespondenceRefusal, CoverageReceipt};
use super::schema::{
    NativeOperationBinding, OpenRemainder, OperationCorrespondence, OperationCorrespondenceSeal,
    OperationResolution, PopulationCorrespondence, PopulationResolution, PortCorrespondence,
    SourceOperationOccurrence,
};

impl OperationCorrespondenceSeal {
    pub const SCHEMA: &'static str = "holonic-engine.operation-correspondence.v1";

    pub fn new(
        source_operations: Vec<SourceOperationOccurrence>,
        operations: Vec<OperationCorrespondence>,
        source_populations: Vec<String>,
        populations: Vec<PopulationCorrespondence>,
        graphs: Vec<super::schema::NativeGraphIdentity>,
    ) -> Self {
        Self {
            schema: Self::SCHEMA.to_owned(),
            source_operations,
            operations,
            source_populations,
            populations,
            graphs,
        }
    }

    /// Validate and canonicalize the seal.  Canonical ordering is by the stable source id/name,
    /// so serialization does not depend on how parallel deed construction inserted records.
    pub fn seal(mut self) -> Result<Self, CorrespondenceRefusal> {
        self.validate()?;
        self.source_operations
            .sort_by(|left, right| left.id.cmp(&right.id));
        self.operations
            .sort_by(|left, right| left.source_id.cmp(&right.source_id));
        self.source_populations.sort();
        self.populations
            .sort_by(|left, right| left.source_population.cmp(&right.source_population));
        self.graphs.sort_by(|left, right| left.key.cmp(&right.key));
        Ok(self)
    }

    pub fn validate(&self) -> Result<CoverageReceipt, CorrespondenceRefusal> {
        if self.schema != Self::SCHEMA {
            return Err(CorrespondenceRefusal::WrongSchema {
                expected: Self::SCHEMA.to_owned(),
                found: self.schema.clone(),
            });
        }
        let graph_keys = validate_graph_registry(&self.graphs)?;
        let expected = unique_source_operations(&self.source_operations)?;
        let mut actual = BTreeMap::<&str, &OperationCorrespondence>::new();
        for correspondence in &self.operations {
            if actual
                .insert(correspondence.source_id.as_str(), correspondence)
                .is_some()
            {
                return Err(CorrespondenceRefusal::DuplicateOccurrence {
                    source_id: correspondence.source_id.clone(),
                });
            }
            if !expected.contains_key(correspondence.source_id.as_str()) {
                return Err(CorrespondenceRefusal::ForeignOccurrence {
                    source_id: correspondence.source_id.clone(),
                });
            }
            match &correspondence.resolution {
                OperationResolution::Native(binding) => {
                    if binding.source_id != correspondence.source_id {
                        return Err(CorrespondenceRefusal::BindingIdDisagrees {
                            source_id: correspondence.source_id.clone(),
                            binding_id: binding.source_id.clone(),
                        });
                    }
                    if !graph_keys.contains(binding.graph_key.as_str()) {
                        return Err(CorrespondenceRefusal::GraphIdentityMissing {
                            source_id: correspondence.source_id.clone(),
                            graph_key: binding.graph_key.clone(),
                        });
                    }
                }
                OperationResolution::Open(remainder) => validate_remainder(remainder)?,
            }
        }
        for source_id in expected.keys() {
            if !actual.contains_key(source_id) {
                return Err(CorrespondenceRefusal::MissingOccurrence {
                    source_id: (*source_id).to_owned(),
                });
            }
        }
        let expected_populations = unique_populations(&self.source_populations)?;
        let mut population_actual = BTreeMap::<&str, &PopulationCorrespondence>::new();
        for correspondence in &self.populations {
            if population_actual
                .insert(correspondence.source_population.as_str(), correspondence)
                .is_some()
            {
                return Err(CorrespondenceRefusal::DuplicatePopulation {
                    source_population: correspondence.source_population.clone(),
                });
            }
            if !expected_populations.contains(correspondence.source_population.as_str()) {
                return Err(CorrespondenceRefusal::ForeignPopulation {
                    source_population: correspondence.source_population.clone(),
                });
            }
            match &correspondence.resolution {
                PopulationResolution::Native { native_population }
                    if native_population.is_empty() =>
                {
                    return Err(CorrespondenceRefusal::EmptyNativePopulation {
                        source_population: correspondence.source_population.clone(),
                    });
                }
                PopulationResolution::Native { .. } => {}
                PopulationResolution::Open(remainder) => validate_remainder(remainder)?,
            }
        }
        for source_population in &expected_populations {
            if !population_actual.contains_key(source_population) {
                return Err(CorrespondenceRefusal::MissingPopulation {
                    source_population: (*source_population).to_owned(),
                });
            }
        }
        // Validate native operation bindings only after the population ledger exists, so a
        // source carrier cannot be paired with an unrelated native population by assertion.
        for correspondence in &self.operations {
            if let OperationResolution::Native(binding) = &correspondence.resolution {
                let source = expected[correspondence.source_id.as_str()];
                validate_native_binding(source, binding, &population_actual)?;
            }
        }
        Ok(CoverageReceipt {
            source_occurrences: expected.len(),
            native_occurrences: self
                .operations
                .iter()
                .filter(|entry| matches!(entry.resolution, OperationResolution::Native(_)))
                .count(),
            open_occurrences: self
                .operations
                .iter()
                .filter(|entry| matches!(entry.resolution, OperationResolution::Open(_)))
                .count(),
            source_populations: expected_populations.len(),
            native_populations: self
                .populations
                .iter()
                .filter(|entry| matches!(entry.resolution, PopulationResolution::Native { .. }))
                .count(),
            open_populations: self
                .populations
                .iter()
                .filter(|entry| matches!(entry.resolution, PopulationResolution::Open(_)))
                .count(),
        })
    }

    pub fn stable_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string_pretty(self)
    }

    /// Read a stable record only through the same coverage gate used before mounting it.
    pub fn from_stable_json(text: &str) -> Result<Self, CorrespondenceRefusal> {
        let seal: Self =
            serde_json::from_str(text).map_err(|error| CorrespondenceRefusal::InvalidJson {
                reason: error.to_string(),
            })?;
        seal.seal()
    }
}

fn unique_source_operations<'a>(
    operations: &'a [SourceOperationOccurrence],
) -> Result<BTreeMap<&'a str, &'a SourceOperationOccurrence>, CorrespondenceRefusal> {
    let mut unique = BTreeMap::new();
    for operation in operations {
        if operation.id.is_empty() {
            return Err(CorrespondenceRefusal::DuplicateSourceOccurrence {
                source_id: operation.id.clone(),
            });
        }
        if operation.source_identity.is_empty()
            || !operation.id.contains(&operation.source_identity)
        {
            return Err(CorrespondenceRefusal::MissingSourceIdentity {
                source_id: operation.id.clone(),
            });
        }
        if operation.family.is_empty() {
            return Err(CorrespondenceRefusal::EmptyFamily);
        }
        if unique.insert(operation.id.as_str(), operation).is_some() {
            return Err(CorrespondenceRefusal::DuplicateSourceOccurrence {
                source_id: operation.id.clone(),
            });
        }
    }
    Ok(unique)
}

fn unique_populations(populations: &[String]) -> Result<BTreeSet<&str>, CorrespondenceRefusal> {
    let mut unique = BTreeSet::new();
    for population in populations {
        if population.is_empty() {
            return Err(CorrespondenceRefusal::EmptySourcePopulation {
                source_population: population.clone(),
            });
        }
        if !unique.insert(population.as_str()) {
            return Err(CorrespondenceRefusal::DuplicateSourcePopulation {
                source_population: population.clone(),
            });
        }
    }
    Ok(unique)
}

fn validate_remainder(remainder: &OpenRemainder) -> Result<(), CorrespondenceRefusal> {
    if remainder.name.is_empty() || remainder.reason.is_empty() || remainder.reopening.is_empty() {
        return Err(CorrespondenceRefusal::InvalidRemainder {
            name: remainder.name.clone(),
        });
    }
    Ok(())
}

fn validate_native_binding(
    source: &SourceOperationOccurrence,
    binding: &NativeOperationBinding,
    populations: &BTreeMap<&str, &PopulationCorrespondence>,
) -> Result<(), CorrespondenceRefusal> {
    if binding.resident_law.is_empty() || binding.graph_key.is_empty() {
        return Err(CorrespondenceRefusal::IncompleteNativeBinding {
            source_id: source.id.clone(),
            reason: "resident law and graph key are required".to_owned(),
        });
    }
    if binding.species != source.species {
        return Err(CorrespondenceRefusal::NativeBindingDisagrees {
            source_id: source.id.clone(),
            reason: format!("species {:?} versus {:?}", binding.species, source.species),
        });
    }
    match (&source.carrier, &binding.native_population) {
        (Some(source_population), Some(native)) if !native.is_empty() => {
            let Some(population) = populations.get(source_population.as_str()) else {
                return Err(CorrespondenceRefusal::CarrierPopulationUnlisted {
                    source_id: source.id.clone(),
                    source_population: source_population.clone(),
                });
            };
            match &population.resolution {
                PopulationResolution::Native { native_population }
                    if native_population == native => {}
                PopulationResolution::Native { native_population } => {
                    return Err(CorrespondenceRefusal::NativeBindingDisagrees {
                        source_id: source.id.clone(),
                        reason: format!(
                            "carrier maps to {native_population:?}, binding names {native:?}"
                        ),
                    });
                }
                PopulationResolution::Open(_) => {
                    return Err(CorrespondenceRefusal::CarrierPopulationNotNative {
                        source_id: source.id.clone(),
                        source_population: source_population.clone(),
                    });
                }
            }
        }
        (Some(_), _) => {
            return Err(CorrespondenceRefusal::CarrierPopulationMissing {
                source_id: source.id.clone(),
            });
        }
        (None, Some(_)) => {
            return Err(CorrespondenceRefusal::UnexpectedCarrierPopulation {
                source_id: source.id.clone(),
            });
        }
        (None, None) => {}
    }
    validate_ports(&source.id, &source.inputs, &binding.inputs, "input")?;
    validate_ports(&source.id, &source.outputs, &binding.outputs, "output")?;
    Ok(())
}

fn validate_graph_registry(
    graphs: &[super::schema::NativeGraphIdentity],
) -> Result<BTreeSet<&str>, CorrespondenceRefusal> {
    let mut keys = BTreeSet::new();
    for graph in graphs {
        if graph.key.is_empty() || graph.tiling.is_empty() {
            return Err(CorrespondenceRefusal::IncompleteGraphIdentity {
                graph_key: graph.key.clone(),
                reason: "graph key and tiling are required".to_owned(),
            });
        }
        if !graph.is_derived() {
            return Err(CorrespondenceRefusal::GraphIdentityNotDerived {
                source_id: graph.key.clone(),
            });
        }
        if !graph.has_complete_topology() {
            return Err(CorrespondenceRefusal::GraphTopologyAbsent {
                source_id: graph.key.clone(),
            });
        }
        if !keys.insert(graph.key.as_str()) {
            return Err(CorrespondenceRefusal::DuplicateGraphIdentity {
                graph_key: graph.key.clone(),
            });
        }
    }
    Ok(keys)
}

fn validate_ports(
    source_id: &str,
    source: &[String],
    native: &[PortCorrespondence],
    hand: &str,
) -> Result<(), CorrespondenceRefusal> {
    if source.len() != native.len() {
        return Err(CorrespondenceRefusal::NativeBindingDisagrees {
            source_id: source_id.to_owned(),
            reason: format!("{hand} arity {} versus {}", native.len(), source.len()),
        });
    }
    for (ordinal, (expected, port)) in source.iter().zip(native).enumerate() {
        if port.ordinal != ordinal || port.source != *expected || port.native.is_empty() {
            return Err(CorrespondenceRefusal::IncompleteNativeBinding {
                source_id: source_id.to_owned(),
                reason: format!("{hand} port {ordinal} has no exact source/native identity"),
            });
        }
    }
    Ok(())
}
