use std::collections::{BTreeMap, BTreeSet};

use thiserror::Error;

use crate::exact_json;
use crate::foreign_map::ForeignContainer;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ForeignJsonField {
    pub name: String,
    pub raw_value: String,
}

/// A lossless vendor configuration chart. Parsed fields never govern native transport.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ForeignConfigurationChart {
    pub address: String,
    pub raw: Vec<u8>,
    pub root_fields: Vec<ForeignJsonField>,
}

/// A sharded tensor index as storage lineage, not a model topology.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShardedWeightIndexChart {
    pub address: String,
    pub raw: Vec<u8>,
    pub total_size: u64,
    pub metadata: Vec<ForeignJsonField>,
    pub weight_map: BTreeMap<String, String>,
    pub declaration_order: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShardedArchiveReconstruction {
    pub indexed_tensor_population: usize,
    pub manifested_tensor_population: usize,
    pub indexed_shards: BTreeSet<String>,
    pub manifested_shards: BTreeSet<String>,
    pub missing_shards: BTreeSet<String>,
    pub missing_tensors: BTreeSet<String>,
    pub refused_indexed_tensors: BTreeSet<String>,
    pub unindexed_manifested_tensors: BTreeSet<String>,
    pub declared_weight_octets: u64,
    pub manifested_payload_octets: u64,
}

impl ShardedArchiveReconstruction {
    pub fn complete(&self) -> bool {
        self.missing_shards.is_empty()
            && self.missing_tensors.is_empty()
            && self.refused_indexed_tensors.is_empty()
            && self.unindexed_manifested_tensors.is_empty()
            && self.indexed_shards == self.manifested_shards
    }
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum ForeignJsonChartError {
    #[error("{address}: the configuration is not UTF-8: {reason}")]
    NotText { address: String, reason: String },
    #[error("{address}: malformed JSON chart: {reason}")]
    Malformed { address: String, reason: String },
    #[error("{address}: repeated root field {field:?}")]
    RepeatedField { address: String, field: String },
    #[error("{address}: the sharded index has no {field}")]
    MissingIndexField {
        address: String,
        field: &'static str,
    },
}

impl ForeignConfigurationChart {
    pub fn read(address: impl Into<String>, raw: Vec<u8>) -> Result<Self, ForeignJsonChartError> {
        let address = address.into();
        let text = std::str::from_utf8(&raw).map_err(|error| ForeignJsonChartError::NotText {
            address: address.clone(),
            reason: error.to_string(),
        })?;
        validate_json_value(&address, text)?;
        let root_fields = parse_fields(&address, text)?;
        if root_fields.is_empty() {
            return Err(ForeignJsonChartError::Malformed {
                address,
                reason: "the root object is empty".to_owned(),
            });
        }
        Ok(Self {
            address,
            raw,
            root_fields,
        })
    }

    pub fn field(&self, name: &str) -> Option<&str> {
        self.root_fields
            .iter()
            .find(|field| field.name == name)
            .map(|field| field.raw_value.as_str())
    }
}

impl ShardedWeightIndexChart {
    pub fn read(address: impl Into<String>, raw: Vec<u8>) -> Result<Self, ForeignJsonChartError> {
        let address = address.into();
        let text = std::str::from_utf8(&raw).map_err(|error| ForeignJsonChartError::NotText {
            address: address.clone(),
            reason: error.to_string(),
        })?;
        validate_json_value(&address, text)?;
        let root = parse_fields(&address, text)?;
        let metadata_raw = root
            .iter()
            .find(|field| field.name == "metadata")
            .ok_or_else(|| ForeignJsonChartError::MissingIndexField {
                address: address.clone(),
                field: "metadata",
            })?;
        let metadata = parse_fields(&address, &metadata_raw.raw_value)?;
        let total_size = metadata
            .iter()
            .find(|field| field.name == "total_size")
            .and_then(|field| field.raw_value.trim().parse::<u64>().ok())
            .ok_or_else(|| ForeignJsonChartError::MissingIndexField {
                address: address.clone(),
                field: "metadata.total_size",
            })?;
        let weight_map_raw = root
            .iter()
            .find(|field| field.name == "weight_map")
            .ok_or_else(|| ForeignJsonChartError::MissingIndexField {
                address: address.clone(),
                field: "weight_map",
            })?;
        let weight_fields = parse_fields(&address, &weight_map_raw.raw_value)?;
        if weight_fields.is_empty() {
            return Err(ForeignJsonChartError::Malformed {
                address,
                reason: "the weight map is empty".to_owned(),
            });
        }
        let mut weight_map = BTreeMap::new();
        let mut declaration_order = Vec::with_capacity(weight_fields.len());
        for field in weight_fields {
            let shard = exact_json::as_string(&field.raw_value).ok_or_else(|| {
                ForeignJsonChartError::Malformed {
                    address: address.clone(),
                    reason: format!("weight {:?} does not name a shard string", field.name),
                }
            })?;
            if shard.is_empty() {
                return Err(ForeignJsonChartError::Malformed {
                    address,
                    reason: format!("weight {:?} names an empty shard", field.name),
                });
            }
            declaration_order.push(field.name.clone());
            weight_map.insert(field.name, shard);
        }
        Ok(Self {
            address,
            raw,
            total_size,
            metadata,
            weight_map,
            declaration_order,
        })
    }

    pub fn shards(&self) -> BTreeSet<String> {
        self.weight_map.values().cloned().collect()
    }

    pub fn reconcile(
        &self,
        containers: &BTreeMap<String, ForeignContainer>,
    ) -> ShardedArchiveReconstruction {
        let indexed_shards = self.shards();
        let manifested_shards = containers.keys().cloned().collect::<BTreeSet<_>>();
        let missing_shards = indexed_shards
            .difference(&manifested_shards)
            .cloned()
            .collect::<BTreeSet<_>>();
        let mut missing_tensors = BTreeSet::new();
        let mut refused_indexed_tensors = BTreeSet::new();
        for (tensor, shard) in &self.weight_map {
            let Some(container) = containers.get(shard) else {
                continue;
            };
            if container.tensors.contains_key(tensor) {
                continue;
            }
            if container.refused.iter().any(|(name, _)| name == tensor) {
                refused_indexed_tensors.insert(tensor.clone());
            } else {
                missing_tensors.insert(tensor.clone());
            }
        }
        let manifested_names = containers
            .iter()
            .flat_map(|(shard, container)| {
                container
                    .tensors
                    .keys()
                    .map(move |tensor| (tensor.clone(), shard.clone()))
            })
            .collect::<BTreeMap<_, _>>();
        let unindexed_manifested_tensors = manifested_names
            .keys()
            .filter(|tensor| !self.weight_map.contains_key(*tensor))
            .cloned()
            .collect::<BTreeSet<_>>();
        ShardedArchiveReconstruction {
            indexed_tensor_population: self.weight_map.len(),
            manifested_tensor_population: manifested_names.len(),
            indexed_shards,
            manifested_shards,
            missing_shards,
            missing_tensors,
            refused_indexed_tensors,
            unindexed_manifested_tensors,
            declared_weight_octets: self.total_size,
            manifested_payload_octets: containers
                .values()
                .map(|container| container.payload_octets)
                .sum(),
        }
    }
}

fn parse_fields(
    address: &str,
    object: &str,
) -> Result<Vec<ForeignJsonField>, ForeignJsonChartError> {
    let pairs =
        exact_json::top_level_pairs(object).map_err(|reason| ForeignJsonChartError::Malformed {
            address: address.to_owned(),
            reason,
        })?;
    let mut seen = BTreeSet::new();
    let mut fields = Vec::with_capacity(pairs.len());
    for (name, raw_value) in pairs {
        if !seen.insert(name.clone()) {
            return Err(ForeignJsonChartError::RepeatedField {
                address: address.to_owned(),
                field: name,
            });
        }
        fields.push(ForeignJsonField {
            name,
            raw_value: raw_value.to_owned(),
        });
    }
    Ok(fields)
}

fn validate_json_value(address: &str, value: &str) -> Result<(), ForeignJsonChartError> {
    serde_json::from_str::<serde_json::Value>(value).map_err(|error| {
        ForeignJsonChartError::Malformed {
            address: address.to_owned(),
            reason: error.to_string(),
        }
    })?;
    let trimmed = value.trim();
    if trimmed.starts_with('{') {
        let pairs = exact_json::top_level_pairs(trimmed).map_err(|reason| {
            ForeignJsonChartError::Malformed {
                address: address.to_owned(),
                reason,
            }
        })?;
        let mut seen = BTreeSet::new();
        for (name, nested) in pairs {
            if !seen.insert(name.clone()) {
                return Err(ForeignJsonChartError::RepeatedField {
                    address: address.to_owned(),
                    field: name,
                });
            }
            validate_json_value(address, nested)?;
        }
    } else if trimmed.starts_with('[') {
        for nested in exact_json::array_elements(trimmed).map_err(|reason| {
            ForeignJsonChartError::Malformed {
                address: address.to_owned(),
                reason,
            }
        })? {
            validate_json_value(address, nested)?;
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::foreign_map::{ContainerSpecies, ForeignDtype, ForeignTensor};

    #[test]
    fn configuration_retains_nested_vendor_fields_without_interpreting_them() {
        let raw = br#"{
          "model_type":"hybrid",
          "layer_types":["linear","full"],
          "quantization_config":{"fmt":"e4m3","scale":1e-6}
        }"#
        .to_vec();
        let chart = ForeignConfigurationChart::read("config.json", raw.clone()).expect("chart");
        assert_eq!(chart.raw, raw);
        assert_eq!(chart.root_fields.len(), 3);
        assert_eq!(chart.field("model_type"), Some("\"hybrid\""));
        assert!(chart.field("quantization_config").unwrap().contains("1e-6"));
    }

    #[test]
    fn shard_reconstruction_retains_missing_refused_and_unindexed_populations() {
        let index = ShardedWeightIndexChart::read(
            "model.safetensors.index.json",
            br#"{
              "metadata":{"total_size":6},
              "weight_map":{
                "dense.weight":"a.safetensors",
                "expert.weight":"a.safetensors",
                "missing.weight":"b.safetensors"
              }
            }"#
            .to_vec(),
        )
        .expect("index");
        let container = ForeignContainer {
            address: "a.safetensors".to_owned(),
            species: ContainerSpecies::Safetensors {
                header_octets: 1,
                base: 9,
            },
            file_octets: 15,
            payload_octets: 6,
            container_metadata: BTreeMap::new(),
            tensors: BTreeMap::from([
                (
                    "dense.weight".to_owned(),
                    ForeignTensor {
                        name: "dense.weight".to_owned(),
                        dtype: ForeignDtype::Bf16,
                        shape: vec![1],
                        start: 0,
                        end: 2,
                    },
                ),
                (
                    "unindexed.weight".to_owned(),
                    ForeignTensor {
                        name: "unindexed.weight".to_owned(),
                        dtype: ForeignDtype::Bf16,
                        shape: vec![2],
                        start: 2,
                        end: 6,
                    },
                ),
            ]),
            refused: vec![(
                "expert.weight".to_owned(),
                crate::foreign_map::ManifestRefusal::WidthUnknown {
                    dtype: "F4".to_owned(),
                },
            )],
        };
        let receipt = index.reconcile(&BTreeMap::from([("a.safetensors".to_owned(), container)]));
        assert_eq!(
            receipt.missing_shards,
            BTreeSet::from(["b.safetensors".to_owned()])
        );
        assert_eq!(
            receipt.refused_indexed_tensors,
            BTreeSet::from(["expert.weight".to_owned()])
        );
        assert_eq!(
            receipt.unindexed_manifested_tensors,
            BTreeSet::from(["unindexed.weight".to_owned()])
        );
        assert!(!receipt.complete());
    }

    #[test]
    fn repeated_configuration_field_is_refused_instead_of_overwritten() {
        let error = ForeignConfigurationChart::read(
            "config.json",
            br#"{"hidden_size":4,"hidden_size":8}"#.to_vec(),
        )
        .expect_err("duplicate");
        assert!(matches!(
            error,
            ForeignJsonChartError::RepeatedField { field, .. } if field == "hidden_size"
        ));
    }

    #[test]
    fn repeated_nested_configuration_field_is_refused_instead_of_hidden_in_raw_json() {
        let error = ForeignConfigurationChart::read(
            "config.json",
            br#"{"quantization":{"fmt":"e4m3","fmt":"e5m2"}}"#.to_vec(),
        )
        .expect_err("nested duplicate");
        assert!(matches!(
            error,
            ForeignJsonChartError::RepeatedField { field, .. } if field == "fmt"
        ));
    }
}
