use std::io::{Read, Write};
use std::path::{Path, PathBuf};

use sha2::{Digest, Sha256};

use super::manifest::{
    NativePayloadDescriptor, NativePopulationDescriptor, NativeRestWire, mount_external_evidence,
    validate_manifest_digest, validate_manifest_shape,
};
use super::types::*;
use super::{MANIFEST_DIGEST_OCTETS, NATIVE_REST_PREFIX};
use crate::foreign_map::FileIdentity;
use crate::ported_operation::{OperationSpecies, PortedOperationComplex, SourceTestimony};
use crate::source_occurrence::{BindingValidation, OccurrenceWitness, SourceRefusal, parse_symbol};

/// File-backed remount. Only the manifest is retained; exact population bytes remain in the
/// sealed native rest file and are streamed when a named population is requested.
pub struct MountedNativeRest {
    path: PathBuf,
    wire: NativeRestWire,
    payload_offset: u64,
    identity: FileIdentity,
}

/// A zero-copy staging locator. The offsets are absolute file offsets, while shape and dtype are
/// the authenticated descriptor fields. It deliberately carries no payload bytes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MountedPopulationExtent {
    pub population: String,
    pub start: u64,
    pub end: u64,
    pub shape: Vec<usize>,
    pub dtype: String,
}

impl std::fmt::Debug for MountedNativeRest {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("MountedNativeRest")
            .field("path", &self.path)
            .field("payload_offset", &self.payload_offset)
            .finish()
    }
}

impl MountedNativeRest {
    pub fn open(path: impl AsRef<Path>) -> Result<Self, NativeRestRefusal> {
        use std::io::Seek;
        let path = path.as_ref().to_owned();
        let mut file =
            std::fs::File::open(&path).map_err(|e| NativeRestRefusal::WireDecode(e.to_string()))?;
        let mut prefix = vec![0u8; NATIVE_REST_PREFIX.len()];
        file.read_exact(&mut prefix)
            .map_err(|e| NativeRestRefusal::WireDecode(e.to_string()))?;
        if prefix != NATIVE_REST_PREFIX {
            return Err(NativeRestRefusal::WirePrefix { opened: prefix });
        }
        let mut len = [0u8; 8];
        file.read_exact(&mut len)
            .map_err(|e| NativeRestRefusal::WireDecode(e.to_string()))?;
        let manifest_len = usize::try_from(u64::from_le_bytes(len)).map_err(|_| {
            NativeRestRefusal::WireDecode("manifest extent exceeds process".to_owned())
        })?;
        let mut expected_digest = [0u8; MANIFEST_DIGEST_OCTETS];
        file.read_exact(&mut expected_digest)
            .map_err(|e| NativeRestRefusal::WireDecode(e.to_string()))?;
        let mut manifest = vec![0u8; manifest_len];
        file.read_exact(&mut manifest)
            .map_err(|e| NativeRestRefusal::WireDecode(e.to_string()))?;
        validate_manifest_digest(&expected_digest, &manifest)?;
        let wire: NativeRestWire = serde_json::from_slice(&manifest)
            .map_err(|e| NativeRestRefusal::WireDecode(e.to_string()))?;
        let wire = mount_external_evidence(wire)?;
        let payload_offset =
            (NATIVE_REST_PREFIX.len() + 8 + MANIFEST_DIGEST_OCTETS + manifest_len) as u64;
        let file_len = file
            .metadata()
            .map_err(|e| NativeRestRefusal::WireDecode(e.to_string()))?
            .len();
        let identity = FileIdentity::of(&file, path.to_string_lossy().as_ref())
            .map_err(|e| NativeRestRefusal::WireDecode(e.to_string()))?;
        let payload_len = file_len.saturating_sub(payload_offset);
        validate_manifest_shape(&wire, payload_len)?;
        file.seek(std::io::SeekFrom::Start(payload_offset))
            .map_err(|e| NativeRestRefusal::WireDecode(e.to_string()))?;
        let actual = digest_stream(&mut file, payload_len)?;
        if actual != wire.payload_sha256 {
            return Err(NativeRestRefusal::PayloadDigest {
                expected: wire.payload_sha256.clone(),
                actual,
            });
        }
        Ok(Self {
            path,
            wire,
            payload_offset,
            identity,
        })
    }

    /// Refuse when the mounted rest at its locator is not the same file occurrence authenticated
    /// at open. A hard-link or a caller-only locator rebasing preserves the occurrence; a copied
    /// or replaced rest does not.
    pub fn verify_still(&self) -> Result<(), NativeRestRefusal> {
        let now = FileIdentity::at(self.path.to_string_lossy().as_ref())
            .map_err(|e| NativeRestRefusal::WireDecode(e.to_string()))?;
        if now != self.identity {
            return Err(NativeRestRefusal::WireDecode(
                "mounted native rest file occurrence drifted".to_owned(),
            ));
        }
        Ok(())
    }

    /// Open the authenticated rest for a streaming staging deed. The caller receives no semantic
    /// scheduler or executor, only the exterior file handle.
    pub fn open_file(&self) -> Result<std::fs::File, NativeRestRefusal> {
        self.verify_still()?;
        let file = std::fs::File::open(&self.path)
            .map_err(|e| NativeRestRefusal::WireDecode(e.to_string()))?;
        let now = FileIdentity::of(&file, self.path.to_string_lossy().as_ref())
            .map_err(|e| NativeRestRefusal::WireDecode(e.to_string()))?;
        if now != self.identity {
            return Err(NativeRestRefusal::WireDecode(
                "mounted native rest file occurrence drifted".to_owned(),
            ));
        }
        Ok(file)
    }

    pub fn total_file_octets(&self) -> u64 {
        self.identity.octets
    }

    pub fn payload_offset(&self) -> u64 {
        self.payload_offset
    }

    /// Resolve one exact population to its absolute file extent and authenticated tensor shape.
    pub fn population_extent(
        &self,
        population: &str,
    ) -> Result<MountedPopulationExtent, NativeRestRefusal> {
        let descriptor = self
            .wire
            .populations
            .iter()
            .find(|entry| entry.source.population == population)
            .ok_or_else(|| NativeRestRefusal::ActivePopulationMissing {
                population: population.to_owned(),
            })?;
        let NativePayloadDescriptor::Exact { start, end } = &descriptor.payload else {
            return Err(NativeRestRefusal::PopulationOpen {
                population: population.to_owned(),
            });
        };
        let start = self.payload_offset.checked_add(*start).ok_or_else(|| {
            NativeRestRefusal::WireDecode("population offset overflow".to_owned())
        })?;
        let end = self.payload_offset.checked_add(*end).ok_or_else(|| {
            NativeRestRefusal::WireDecode("population offset overflow".to_owned())
        })?;
        Ok(MountedPopulationExtent {
            population: population.to_owned(),
            start,
            end,
            shape: descriptor.source.shape.clone(),
            dtype: descriptor.source.dtype.clone(),
        })
    }

    pub fn topology(&self) -> &NativeTopology {
        &self.wire.topology[0]
    }
    pub fn topologies(&self) -> &[NativeTopology] {
        &self.wire.topology
    }

    pub fn source(&self) -> &NativeSourceIdentity {
        &self.wire.source
    }

    pub fn populations(&self) -> &[NativePopulationDescriptor] {
        &self.wire.populations
    }

    pub fn laws(&self) -> &[NativeLawIdentity] {
        &self.wire.laws
    }

    /// Resolve a concrete graph through the correspondence registry; the mounted rest does not
    /// duplicate graph chronology/topology outside that registry.
    pub fn graph(&self, key: &str) -> Option<&NativeGraphIdentity> {
        self.wire
            .correspondence
            .graphs
            .iter()
            .find(|graph| graph.key == key)
    }

    pub fn graphs(&self) -> &[NativeGraphIdentity] {
        &self.wire.correspondence.graphs
    }

    pub fn tilings(&self) -> &[NativeOwnerIdentity] {
        &self.wire.tilings
    }

    pub fn reductions(&self) -> &[NativeOwnerIdentity] {
        &self.wire.reductions
    }
    pub fn correspondence(&self) -> &crate::operation_correspondence::OperationCorrespondenceSeal {
        &self.wire.correspondence
    }
    pub fn codebook(&self) -> &crate::foreign_codec_rest::ExteriorCodebookRest {
        &self.wire.codebook
    }

    /// Stream one exact population to a receiver. Open fibres return no bytes and are reported by
    /// the caller through the descriptor; this method never allocates the whole payload.
    pub fn read_population_to<W: Write>(
        &self,
        population: &str,
        output: &mut W,
    ) -> Result<(), NativeRestRefusal> {
        let descriptor = self
            .wire
            .populations
            .iter()
            .find(|p| p.source.population == population)
            .ok_or_else(|| NativeRestRefusal::ActivePopulationMissing {
                population: population.to_owned(),
            })?;
        let NativePayloadDescriptor::Exact { start, end } = &descriptor.payload else {
            return Ok(());
        };
        let (start, end) = (*start, *end);
        let mut file = self.open_file()?;
        use std::io::Seek;
        file.seek(std::io::SeekFrom::Start(self.payload_offset + start))
            .map_err(|e| NativeRestRefusal::WireDecode(e.to_string()))?;
        let mut remaining = (end - start) as usize;
        let mut chunk = vec![0u8; 1 << 20];
        while remaining > 0 {
            let take = remaining.min(chunk.len());
            file.read_exact(&mut chunk[..take])
                .map_err(|e| NativeRestRefusal::WireDecode(e.to_string()))?;
            output
                .write_all(&chunk[..take])
                .map_err(|e| NativeRestRefusal::WireDecode(e.to_string()))?;
            remaining -= take;
        }
        Ok(())
    }
}

impl OccurrenceWitness for MountedNativeRest {
    fn witness(&self) -> &'static str {
        "mounted native rest"
    }

    fn validate(
        &self,
        complex: &PortedOperationComplex,
    ) -> Result<Vec<BindingValidation>, SourceRefusal> {
        self.verify_still()
            .map_err(|error| SourceRefusal::Drifted {
                locator: self.path.to_string_lossy().into_owned(),
                declared: format!("{:?}", self.identity),
                measured: error.to_string(),
            })?;
        let identity = crate::operation_correspondence::topology_identity(complex);
        let named = self
            .wire
            .topology
            .iter()
            .filter(|topology| topology.name == complex.name)
            .collect::<Vec<_>>();
        let topology = match named.as_slice() {
            [topology] => *topology,
            _ => {
                return Err(SourceRefusal::TopologyAbsent {
                    identity: format!("{} ({})", complex.name, identity),
                });
            }
        };
        let exact_identity = topology.identity == identity;
        let mut stored_names = std::collections::BTreeSet::new();
        for (law_id, stored) in &topology.operations {
            let name = topology
                .shape
                .laws
                .get(law_id)
                .map(|law| law.name.as_str())
                .ok_or_else(|| SourceRefusal::OperationForeign {
                    operation: format!("stored-law-{}", law_id.0),
                })?;
            if !stored_names.insert(name) {
                return Err(SourceRefusal::OperationForeign {
                    operation: name.to_owned(),
                });
            }
            let Some(source_law) = topology.shape.laws.get(law_id) else {
                return Err(SourceRefusal::OperationForeign {
                    operation: format!("stored-law-{}", law_id.0),
                });
            };
            if stored.law != *law_id
                || port_names(&topology.shape, &source_law.inputs).is_none()
                || port_names(&topology.shape, &source_law.outputs).is_none()
            {
                return Err(SourceRefusal::OperationForeign {
                    operation: name.to_owned(),
                });
            }
        }
        let mut runtime_names = std::collections::BTreeSet::new();
        for operation in complex.operations.values() {
            let name = complex
                .shape
                .laws
                .get(&operation.law)
                .map(|law| law.name.as_str())
                .ok_or_else(|| SourceRefusal::OperationForeign {
                    operation: format!("runtime-law-{}", operation.law.0),
                })?;
            if !runtime_names.insert(name) {
                return Err(SourceRefusal::OperationForeign {
                    operation: name.to_owned(),
                });
            }
        }
        let mut source_pairs = Vec::with_capacity(topology.operations.len());
        let mut replacement_pairs = Vec::new();
        let mut matched_runtime = std::collections::BTreeSet::new();
        for (stored_law, stored) in &topology.operations {
            let stored_law_shape = topology.shape.laws.get(stored_law).ok_or_else(|| {
                SourceRefusal::OperationForeign {
                    operation: format!("stored-law-{}", stored_law.0),
                }
            })?;
            let candidates = complex
                .operations
                .iter()
                .filter(|(runtime_law, runtime)| {
                    let Some(runtime_law_shape) = complex.shape.laws.get(runtime_law) else {
                        return false;
                    };
                    runtime_law_shape.name == stored_law_shape.name
                        && runtime.species == stored.species
                        && runtime.carrier == stored.carrier
                        && same_ports(
                            &topology.shape,
                            stored_law_shape,
                            &complex.shape,
                            runtime_law_shape,
                        )
                        && same_testimony(&runtime.testimony, &stored.testimony)
                })
                .collect::<Vec<_>>();
            match candidates.as_slice() {
                [(runtime_law, runtime)] => {
                    if !matched_runtime.insert(**runtime_law) {
                        return Err(SourceRefusal::OperationForeign {
                            operation: stored_law_shape.name.clone(),
                        });
                    }
                    source_pairs.push((*runtime, stored));
                }
                [] => {
                    let replacement_name = format!("{} (intervention)", stored_law_shape.name);
                    let replacements = complex
                        .operations
                        .iter()
                        .filter(|(runtime_law, runtime)| {
                            let Some(runtime_law_shape) = complex.shape.laws.get(runtime_law)
                            else {
                                return false;
                            };
                            runtime_law_shape.name == replacement_name
                                && runtime.species == stored.species
                                && runtime.carrier.is_none()
                                && same_ports(
                                    &topology.shape,
                                    stored_law_shape,
                                    &complex.shape,
                                    runtime_law_shape,
                                )
                                && intervention_only(&runtime.testimony)
                        })
                        .collect::<Vec<_>>();
                    let [(runtime_law, runtime)] = replacements.as_slice() else {
                        return Err(SourceRefusal::OperationForeign {
                            operation: stored_law_shape.name.clone(),
                        });
                    };
                    if !matched_runtime.insert(**runtime_law) {
                        return Err(SourceRefusal::OperationForeign {
                            operation: replacement_name,
                        });
                    }
                    replacement_pairs.push((*runtime, stored.species));
                }
                _ => {
                    return Err(SourceRefusal::OperationForeign {
                        operation: stored_law_shape.name.clone(),
                    });
                }
            }
        }
        if exact_identity {
            // The content identity is the cheap exact control. The signature match above remains
            // the authority because midpoint insertion can shift local law ids.
            debug_assert_eq!(source_pairs.len(), topology.operations.len());
        }
        let mut validated = Vec::with_capacity(complex.operations.len());
        for (operation, stored) in source_pairs {
            let name = complex
                .shape
                .laws
                .get(&operation.law)
                .map(|law| law.name.clone())
                .unwrap_or_else(|| format!("law-{}", operation.law.0));
            let mut validation = BindingValidation {
                operation: name.clone(),
                species: stored.species,
                symbols: Vec::new(),
                fields: Vec::new(),
                shapes: Vec::new(),
                interventions: Vec::new(),
                descriptions: Vec::new(),
            };
            let mut exterior = false;
            for testimony in &stored.testimony {
                match testimony {
                    NativeTestimony::Implementation { symbol } => {
                        validation.symbols.push(parse_symbol(&name, symbol)?);
                        exterior = true;
                    }
                    NativeTestimony::Configuration { field, value } => {
                        validation.fields.push((field.clone(), value.clone()));
                        exterior = true;
                    }
                    NativeTestimony::DeclaredShape { population, shape } => {
                        let descriptor = self
                            .wire
                            .populations
                            .iter()
                            .find(|entry| entry.source.population == *population)
                            .ok_or_else(|| SourceRefusal::PopulationNotIdentified {
                                operation: name.clone(),
                                population: population.clone(),
                            })?;
                        if descriptor.source.shape != *shape {
                            return Err(SourceRefusal::ShapeDiffers {
                                operation: name.clone(),
                                population: population.clone(),
                                declared: shape.clone(),
                                measured: descriptor.source.shape.clone(),
                            });
                        }
                        if descriptor.source.dtype != "BF16" && descriptor.source.dtype != "Bf16" {
                            return Err(SourceRefusal::DtypeDiffers {
                                operation: name.clone(),
                                population: population.clone(),
                                declared: "BF16".to_owned(),
                                measured: descriptor.source.dtype.clone(),
                            });
                        }
                        validation.shapes.push((population.clone(), shape.clone()));
                        exterior = true;
                    }
                    NativeTestimony::AuthoritativeDescription { statement } => {
                        validation.descriptions.push(statement.clone());
                        exterior = true;
                    }
                    NativeTestimony::Intervention { statement } => {
                        validation.interventions.push(statement.clone());
                    }
                    NativeTestimony::Undecided { .. } => {}
                }
            }
            if let Some(carrier) = &stored.carrier {
                let descriptor = self
                    .wire
                    .populations
                    .iter()
                    .find(|entry| entry.source.population == *carrier)
                    .ok_or_else(|| SourceRefusal::PopulationNotIdentified {
                        operation: name.clone(),
                        population: carrier.clone(),
                    })?;
                if descriptor.source.dtype != "BF16" && descriptor.source.dtype != "Bf16" {
                    return Err(SourceRefusal::DtypeDiffers {
                        operation: name.clone(),
                        population: carrier.clone(),
                        declared: "BF16".to_owned(),
                        measured: descriptor.source.dtype.clone(),
                    });
                }
            }
            if !validation.interventions.is_empty()
                && exterior
                && stored.species != OperationSpecies::Quotient
            {
                return Err(SourceRefusal::InterventionOnSourceLaw {
                    operation: name,
                    species: stored.species,
                });
            }
            if !exterior && validation.interventions.is_empty() {
                return Err(SourceRefusal::TestimonyNotExterior {
                    operation: name,
                    testimony: stored
                        .testimony
                        .iter()
                        .map(|testimony| format!("{testimony:?}"))
                        .collect(),
                });
            }
            validated.push(validation);
        }
        for (operation, species) in replacement_pairs {
            let name = complex
                .shape
                .laws
                .get(&operation.law)
                .map(|law| law.name.clone())
                .unwrap_or_else(|| format!("law-{}", operation.law.0));
            let interventions = operation
                .testimony
                .iter()
                .map(|testimony| match testimony {
                    SourceTestimony::Intervention { statement } => statement.clone(),
                    _ => unreachable!("replacement was checked as intervention-only"),
                })
                .collect();
            validated.push(BindingValidation {
                operation: name,
                species,
                symbols: Vec::new(),
                fields: Vec::new(),
                shapes: Vec::new(),
                interventions,
                descriptions: Vec::new(),
            });
        }
        for operation in complex.operations.values() {
            if matched_runtime.contains(&operation.law) {
                continue;
            }
            let name = complex
                .shape
                .laws
                .get(&operation.law)
                .map(|law| law.name.clone())
                .unwrap_or_else(|| format!("law-{}", operation.law.0));
            if operation.carrier.is_some()
                || operation.testimony.is_empty()
                || operation
                    .testimony
                    .iter()
                    .any(|testimony| !matches!(testimony, SourceTestimony::Intervention { .. }))
            {
                return Err(SourceRefusal::OperationForeign { operation: name });
            }
            let interventions = operation
                .testimony
                .iter()
                .map(|testimony| match testimony {
                    SourceTestimony::Intervention { statement } => statement.clone(),
                    _ => unreachable!("the addition was checked as intervention-only"),
                })
                .collect();
            validated.push(BindingValidation {
                operation: name,
                species: operation.species,
                symbols: Vec::new(),
                fields: Vec::new(),
                shapes: Vec::new(),
                interventions,
                descriptions: Vec::new(),
            });
        }
        Ok(validated)
    }
}

fn port_names(
    shape: &crate::evolution::EvolutionShape,
    ports: &[crate::category::BoundaryId],
) -> Option<Vec<String>> {
    ports
        .iter()
        .map(|port| {
            shape
                .boundaries
                .objects
                .get(port)
                .map(|boundary| boundary.name.clone())
        })
        .collect()
}

fn same_ports(
    left_shape: &crate::evolution::EvolutionShape,
    left: &crate::evolution::EvolutionLaw,
    right_shape: &crate::evolution::EvolutionShape,
    right: &crate::evolution::EvolutionLaw,
) -> bool {
    port_names(left_shape, &left.inputs) == port_names(right_shape, &right.inputs)
        && port_names(left_shape, &left.outputs) == port_names(right_shape, &right.outputs)
}

fn same_testimony(runtime: &[SourceTestimony], stored: &[NativeTestimony]) -> bool {
    runtime.len() == stored.len()
        && runtime
            .iter()
            .zip(stored)
            .all(|(runtime, stored)| match (runtime, stored) {
                (
                    SourceTestimony::Implementation { symbol: left, .. },
                    NativeTestimony::Implementation { symbol: right },
                ) => left == right,
                (
                    SourceTestimony::Configuration {
                        field: left_field,
                        value: left_value,
                    },
                    NativeTestimony::Configuration {
                        field: right_field,
                        value: right_value,
                    },
                ) => left_field == right_field && left_value == right_value,
                (
                    SourceTestimony::DeclaredShape {
                        population: left_population,
                        shape: left_shape,
                    },
                    NativeTestimony::DeclaredShape {
                        population: right_population,
                        shape: right_shape,
                    },
                ) => left_population == right_population && left_shape == right_shape,
                (
                    SourceTestimony::AuthoritativeDescription { statement: left },
                    NativeTestimony::AuthoritativeDescription { statement: right },
                ) => left == right,
                (
                    SourceTestimony::Intervention { statement: left },
                    NativeTestimony::Intervention { statement: right },
                ) => left == right,
                (
                    SourceTestimony::Undecided { question: left },
                    NativeTestimony::Undecided { question: right },
                ) => left == right,
                _ => false,
            })
}

fn intervention_only(testimony: &[SourceTestimony]) -> bool {
    !testimony.is_empty()
        && testimony
            .iter()
            .all(|testimony| matches!(testimony, SourceTestimony::Intervention { .. }))
}

fn digest_stream(
    file: &mut std::fs::File,
    mut remaining: u64,
) -> Result<String, NativeRestRefusal> {
    let mut hasher = Sha256::new();
    let mut chunk = vec![0u8; 1 << 20];
    while remaining > 0 {
        let take = remaining.min(chunk.len() as u64) as usize;
        file.read_exact(&mut chunk[..take])
            .map_err(|e| NativeRestRefusal::WireDecode(e.to_string()))?;
        hasher.update(&chunk[..take]);
        remaining -= take as u64;
    }
    Ok(format!("{:x}", hasher.finalize()))
}
