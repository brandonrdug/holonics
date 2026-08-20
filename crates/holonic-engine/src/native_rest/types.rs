//! A source-detached native rest for a complete foreign operation passage.
//!
//! `SourceOccurrence` is the mouth of a foreign model: its implementation, configuration and
//! container are deliberately addressed by paths.  That is the right admission witness and the
//! wrong rest.  This owner composes the already admitted `PortedOperationComplex` with the source
//! regions and the resident identities, then emits a native wire which contains no source
//! locator.  A population crosses as its exact source-region bytes or as an explicit open
//! reconstruction fibre; an omitted population is a seal refusal, never an implicit zero.
//!
//! This is a schema and a seal/remount seam.  It does not conduct a law, mount a CUDA section, or
//! choose a condensation.  Those remain the owners named by the live passage.

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

use crate::ported_operation::{CandidateDiagrams, OperationSpecies, PortedOperationComplex};
use crate::source_occurrence::{RegionIdentity, SourceOccurrence};

/// Path-free identity of the foreign occurrence which founded this rest.  It carries content
/// testimony and declared sibling roles, never the locators used at the apparatus boundary.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeSourceIdentity {
    pub implementation_sha256: String,
    pub implementation_octets: u64,
    pub implementation_version: Option<String>,
    pub configuration_sha256: String,
    pub configuration_octets: u64,
    pub configuration_version: Option<String>,
    pub container_octets: u64,
    pub container_header_octets: u64,
    pub container_header_sha256: String,
    pub container_content_sha256: Option<String>,
    pub assets: Vec<NativeAssetIdentity>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeAssetIdentity {
    pub role: String,
    pub sha256: Option<String>,
    pub used: bool,
}

impl NativeSourceIdentity {
    pub(super) fn from_source(source: &SourceOccurrence) -> Self {
        Self {
            implementation_sha256: source.implementation.sha256.clone(),
            implementation_octets: source.implementation.octets,
            implementation_version: source.implementation.version.clone(),
            configuration_sha256: source.configuration.sha256.clone(),
            configuration_octets: source.configuration.octets,
            configuration_version: source.configuration.version.clone(),
            container_octets: source.container.octets,
            container_header_octets: source.container.header_octets,
            container_header_sha256: source.container.header_sha256.clone(),
            container_content_sha256: source.container.content_sha256.clone(),
            assets: {
                let mut assets = source
                    .assets
                    .iter()
                    .map(|asset| NativeAssetIdentity {
                        role: asset.role.clone(),
                        sha256: asset.sha256.clone(),
                        used: asset.used,
                    })
                    .collect::<Vec<_>>();
                assets.sort_by(|left, right| left.role.cmp(&right.role));
                assets
            },
        }
    }

    pub(super) fn validate(&self) -> Result<(), NativeRestRefusal> {
        if self.implementation_sha256.is_empty()
            || self.configuration_sha256.is_empty()
            || self.container_header_sha256.is_empty()
            || self.container_octets < 8
            || self.container_header_octets > self.container_octets
        {
            return Err(NativeRestRefusal::EmptyIdentity {
                owner: "native-source".to_owned(),
            });
        }
        if self
            .container_content_sha256
            .as_ref()
            .is_none_or(String::is_empty)
        {
            return Err(NativeRestRefusal::EmptyIdentity {
                owner: "native-source.container-content".to_owned(),
            });
        }
        let mut roles = BTreeSet::new();
        for asset in &self.assets {
            if asset.role.is_empty() || !roles.insert(asset.role.as_str()) {
                return Err(NativeRestRefusal::EmptyIdentity {
                    owner: "native-source.asset".to_owned(),
                });
            }
            if let Some(hash) = &asset.sha256 {
                if hash.is_empty() {
                    return Err(NativeRestRefusal::EmptyIdentity {
                        owner: format!("native-source.asset.{}", asset.role),
                    });
                }
                if asset.used && asset.sha256.is_none() {
                    return Err(NativeRestRefusal::EmptyIdentity {
                        owner: format!("native-source.asset.{}", asset.role),
                    });
                }
            }
        }
        Ok(())
    }
}

pub use crate::operation_correspondence::NativeGraphIdentity;

/// A source population's exact bytes, or the complete fibre retained when those bytes were not
/// admitted.  The source region remains alongside either arm, so the open arm is not a silent
/// absence and a later deed knows exactly what evidence would reopen it.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum NativePopulationPayload {
    Exact {
        bytes: Vec<u8>,
    },
    /// Seal-time source only. This variant is never emitted in the native wire; the locator is
    /// consumed while streaming and is absent from the resulting manifest.
    External {
        locator: String,
    },
    Open {
        fibre: CandidateDiagrams,
    },
}

/// One population in the source-shaped native rest.  `source` contains no locator: its offsets,
/// dtype, shape and region digest are the source's own exact testimony without its apparatus path.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativePopulation {
    pub native_name: String,
    pub source: RegionIdentity,
    pub payload: NativePopulationPayload,
}

impl NativePopulation {
    pub fn exact(source: RegionIdentity, bytes: Vec<u8>) -> Self {
        Self {
            native_name: source.population.clone(),
            source,
            payload: NativePopulationPayload::Exact { bytes },
        }
    }

    pub fn open(source: RegionIdentity, fibre: CandidateDiagrams) -> Self {
        Self {
            native_name: source.population.clone(),
            source,
            payload: NativePopulationPayload::Open { fibre },
        }
    }
}

/// Source testimony after the source has departed.  Implementation/configuration locators are
/// intentionally not representable here; their source-local symbol/field remains correspondence
/// evidence, while the path itself does not cross the seal.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum NativeTestimony {
    Implementation {
        symbol: String,
    },
    Configuration {
        field: String,
        value: String,
    },
    DeclaredShape {
        population: String,
        shape: Vec<usize>,
    },
    AuthoritativeDescription {
        statement: String,
    },
    Intervention {
        statement: String,
    },
    Undecided {
        question: String,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeOperation {
    pub law: crate::evolution::EvolutionLawId,
    pub species: OperationSpecies,
    pub carrier: Option<String>,
    pub testimony: Vec<NativeTestimony>,
}

/// The complete operation topology, with source-bearing testimony normalized to path-free forms.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeTopology {
    pub schema: String,
    /// Content identity of this concrete normalized operation complex. Parametric family names
    /// remain in the correspondence ledger and are never collapsed into this instance key.
    pub identity: String,
    pub name: String,
    pub shape: crate::evolution::EvolutionShape,
    pub witness: crate::realization::RealizationWitness,
    pub operations: BTreeMap<crate::evolution::EvolutionLawId, NativeOperation>,
    pub undecided: Vec<CandidateDiagrams>,
}

/// A resident law identity remains an addressed identity, not a recomputed name or count.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeLawIdentity {
    pub law: String,
    pub species: OperationSpecies,
    pub owner: String,
    pub graph_identity: String,
}

/// Tiling/reduction identities are supplied by their existing owners and carried opaquely here;
/// this rest owner does not reinterpret either receipt.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeOwnerIdentity {
    pub owner: String,
    pub identity: String,
}

#[derive(Debug, PartialEq, Eq)]
pub struct NativeRestInput {
    /// Every concrete admitted operation complex, retained separately. A family correspondence
    /// is not a substitute for these source-shaped instances.
    pub topology: Vec<PortedOperationComplex>,
    pub source: SourceOccurrence,
    pub populations: Vec<NativePopulation>,
    pub laws: Vec<NativeLawIdentity>,
    pub tilings: Vec<NativeOwnerIdentity>,
    pub reductions: Vec<NativeOwnerIdentity>,
    pub correspondence: crate::operation_correspondence::OperationCorrespondenceSeal,
    pub codebook: crate::foreign_codec_rest::ExteriorCodebookRest,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NativeRestRefusal {
    SourceRegionMissing {
        population: String,
    },
    DuplicatePopulation {
        population: String,
    },
    PopulationShapeDiffers {
        population: String,
    },
    PopulationExtentDiffers {
        population: String,
        expected: usize,
        supplied: usize,
    },
    PopulationDigest {
        population: String,
        expected: String,
        actual: String,
    },
    DuplicateNativePopulation {
        native_name: String,
    },
    ActivePopulationMissing {
        population: String,
    },
    DuplicateIdentity {
        owner: String,
        identity: String,
    },
    LawIdentityMissing {
        law: String,
    },
    EmptyIdentity {
        owner: String,
    },
    WirePrefix {
        opened: Vec<u8>,
    },
    WireSchema {
        schema: String,
    },
    WireDecode(String),
    WireTrailingOctets,
    PayloadDigest {
        expected: String,
        actual: String,
    },
    ManifestDigest {
        expected: String,
        actual: String,
    },
    ExternalRequiresStreaming {
        population: String,
    },
    Correspondence(String),
    CorrespondencePopulationMismatch {
        population: String,
    },
    Codebook(String),
    EmptyTopology,
    DuplicateTopology {
        identity: String,
    },
    TopologyIdentityMissing {
        identity: String,
    },
    GraphIdentityMissing {
        graph_key: String,
    },
}

impl std::fmt::Display for NativeRestRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::SourceRegionMissing { population }
            | Self::DuplicatePopulation { population }
            | Self::PopulationShapeDiffers { population }
            | Self::ActivePopulationMissing { population }
            | Self::ExternalRequiresStreaming { population }
            | Self::CorrespondencePopulationMismatch { population } => f.write_str(population),
            Self::PopulationExtentDiffers {
                population,
                expected,
                supplied,
            } => write!(
                f,
                "{population}: expected {expected} octets, supplied {supplied}"
            ),
            Self::PopulationDigest {
                population,
                expected,
                actual,
            } => write!(f, "{population}: expected digest {expected}, got {actual}"),
            Self::DuplicateNativePopulation { native_name } => f.write_str(native_name),
            Self::DuplicateIdentity { owner, identity } => write!(f, "{owner}: {identity}"),
            Self::LawIdentityMissing { law } => f.write_str(law),
            Self::EmptyIdentity { owner } => f.write_str(owner),
            Self::WirePrefix { opened } => write!(f, "wire prefix {:?}", opened),
            Self::WireSchema { schema } => f.write_str(schema),
            Self::WireDecode(reason) | Self::Correspondence(reason) | Self::Codebook(reason) => {
                f.write_str(reason)
            }
            Self::WireTrailingOctets => f.write_str("wire has trailing octets"),
            Self::PayloadDigest { expected, actual } => {
                write!(f, "payload digest: expected {expected}, got {actual}")
            }
            Self::ManifestDigest { expected, actual } => {
                write!(f, "manifest digest: expected {expected}, got {actual}")
            }
            Self::EmptyTopology => f.write_str("topology is empty"),
            Self::DuplicateTopology { identity } => f.write_str(identity),
            Self::TopologyIdentityMissing { identity } => f.write_str(identity),
            Self::GraphIdentityMissing { graph_key } => f.write_str(graph_key),
        }
    }
}

impl std::error::Error for NativeRestRefusal {}
