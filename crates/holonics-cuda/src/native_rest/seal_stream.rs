use std::collections::{BTreeMap, BTreeSet};
use std::io::{Seek, SeekFrom, Write};

use sha2::{Digest, Sha256};

use super::manifest::{
    NativePayloadDescriptor, NativePopulationDescriptor, NativeRest, NativeRestWire, digest,
    into_native_topology, stream_external, validate_external_evidence, validate_manifest,
    validate_manifest_shape, validate_owner_identities,
};
use super::types::*;
use super::{MANIFEST_DIGEST_OCTETS, NATIVE_REST_PREFIX};

impl NativeRest {
    pub const SCHEMA: &'static str = "holonic-engine.foreign-native-rest.v1";

    pub fn seal(input: NativeRestInput) -> Result<Self, NativeRestRefusal> {
        validate_external_evidence(&input.correspondence, &input.codebook)?;
        if input.topology.is_empty() {
            return Err(NativeRestRefusal::EmptyTopology);
        }
        let admitted = &input.source.container.regions;
        if admitted.is_empty() {
            return Err(NativeRestRefusal::ActivePopulationMissing {
                population: "<source closure>".to_owned(),
            });
        }
        let mut populations = BTreeMap::new();
        for population in input.populations {
            let name = population.source.population.clone();
            let Some(region) = admitted.get(&name) else {
                return Err(NativeRestRefusal::SourceRegionMissing { population: name });
            };
            if populations.insert(name.clone(), population).is_some() {
                return Err(NativeRestRefusal::DuplicatePopulation { population: name });
            }
            let current = populations.get(&name).expect("inserted population");
            if current.source != *region || current.native_name.is_empty() {
                return Err(NativeRestRefusal::PopulationShapeDiffers { population: name });
            }
            if let NativePopulationPayload::Exact { bytes } = &current.payload {
                let expected = region.end.saturating_sub(region.start) as usize;
                if bytes.len() != expected {
                    return Err(NativeRestRefusal::PopulationExtentDiffers {
                        population: current.source.population.clone(),
                        expected,
                        supplied: bytes.len(),
                    });
                }
            }
            if matches!(current.payload, NativePopulationPayload::External { .. }) {
                return Err(NativeRestRefusal::ExternalRequiresStreaming { population: name });
            }
        }
        // Every admitted source region crosses as exact material or an explicit fibre. This is
        // the complete inventory gate; active law carriers are checked separately for readability.
        for name in admitted.keys() {
            if !populations.contains_key(name) {
                return Err(NativeRestRefusal::ActivePopulationMissing {
                    population: name.clone(),
                });
            }
        }
        for topology in &input.topology {
            for operation in topology.operations.values() {
                if let Some(carrier) = &operation.carrier {
                    let Some(population) = populations.get(carrier) else {
                        return Err(NativeRestRefusal::ActivePopulationMissing {
                            population: carrier.clone(),
                        });
                    };
                    if population.native_name.is_empty() {
                        return Err(NativeRestRefusal::ActivePopulationMissing {
                            population: carrier.clone(),
                        });
                    }
                }
            }
        }
        let mut law_names = BTreeSet::new();
        for law in &input.laws {
            if law.owner.is_empty() || law.graph_identity.is_empty() {
                return Err(NativeRestRefusal::EmptyIdentity {
                    owner: law.owner.clone(),
                });
            }
            if !law_names.insert(law.law.clone()) {
                return Err(NativeRestRefusal::DuplicateIdentity {
                    owner: "law".to_owned(),
                    identity: law.law.clone(),
                });
            }
        }
        let declared_laws: BTreeSet<&str> = input
            .topology
            .iter()
            .flat_map(|topology| topology.shape.laws.values())
            .map(|law| law.name.as_str())
            .collect();
        for law in declared_laws {
            if !law_names.contains(law) {
                return Err(NativeRestRefusal::LawIdentityMissing {
                    law: law.to_owned(),
                });
            }
        }
        validate_owner_identities(&input.tilings)?;
        validate_owner_identities(&input.reductions)?;
        let mut topology = input
            .topology
            .into_iter()
            .map(into_native_topology)
            .collect::<Vec<_>>();
        topology.sort_by(|left, right| left.identity.cmp(&right.identity));
        if topology
            .windows(2)
            .any(|pair| pair[0].identity == pair[1].identity)
        {
            return Err(NativeRestRefusal::DuplicateTopology {
                identity: topology[0].identity.clone(),
            });
        }
        let mut payload = Vec::new();
        let mut descriptors = Vec::new();
        for population in populations.into_values() {
            let descriptor = match population.payload {
                NativePopulationPayload::Exact { bytes } => {
                    let start = payload.len() as u64;
                    super::manifest::validate_region_digest(&population.source, &bytes)?;
                    payload.extend_from_slice(&bytes);
                    NativePayloadDescriptor::Exact {
                        start,
                        end: payload.len() as u64,
                    }
                }
                NativePopulationPayload::Open { fibre } => NativePayloadDescriptor::Open { fibre },
                NativePopulationPayload::External { .. } => {
                    unreachable!("external payloads are refused by seal; use seal_streamed")
                }
            };
            descriptors.push(NativePopulationDescriptor {
                native_name: population.native_name,
                source: population.source,
                payload: descriptor,
            });
        }
        let payload_sha256 = digest(&payload);
        let wire = NativeRestWire {
            schema: Self::SCHEMA.to_owned(),
            source: NativeSourceIdentity::from_source(&input.source),
            topology,
            populations: descriptors,
            laws: input.laws,
            tilings: input.tilings,
            reductions: input.reductions,
            correspondence: input.correspondence,
            codebook: input.codebook,
            payload_octets: payload.len() as u64,
            payload_sha256,
        };
        validate_manifest(&wire, &payload)?;
        Ok(Self { wire, payload })
    }

    /// Seal a complete source inventory without retaining it in memory. The output is seekable so
    /// the fixed-size manifest placeholder can be authenticated and backpatched after every exact
    /// population has crossed once. An external locator is therefore opened and read exactly once;
    /// it is never retained in the emitted wire.
    pub fn seal_streamed<W: Write + Seek>(
        input: NativeRestInput,
        output: &mut W,
    ) -> Result<(), NativeRestRefusal> {
        validate_external_evidence(&input.correspondence, &input.codebook)?;
        if input.topology.is_empty() {
            return Err(NativeRestRefusal::EmptyTopology);
        }
        let admitted = &input.source.container.regions;
        if admitted.is_empty() {
            return Err(NativeRestRefusal::ActivePopulationMissing {
                population: "<source closure>".to_owned(),
            });
        }
        let source_identity = NativeSourceIdentity::from_source(&input.source);
        let mut populations = input.populations;
        populations.sort_by(|a, b| a.source.population.cmp(&b.source.population));
        let mut descriptors = Vec::with_capacity(populations.len());
        let mut admitted_names = BTreeSet::new();
        let mut payload_len = 0u64;
        for population in &populations {
            let name = &population.source.population;
            if !admitted_names.insert(name.clone()) {
                return Err(NativeRestRefusal::DuplicatePopulation {
                    population: name.clone(),
                });
            }
            let region =
                admitted
                    .get(name)
                    .ok_or_else(|| NativeRestRefusal::SourceRegionMissing {
                        population: name.clone(),
                    })?;
            if *region != population.source {
                return Err(NativeRestRefusal::PopulationShapeDiffers {
                    population: name.clone(),
                });
            }
            if region != &population.source {
                return Err(NativeRestRefusal::PopulationShapeDiffers {
                    population: name.clone(),
                });
            }
            let expected = region.end.saturating_sub(region.start);
            let descriptor = match &population.payload {
                NativePopulationPayload::Exact { bytes } => {
                    if bytes.len() as u64 != expected {
                        return Err(NativeRestRefusal::PopulationExtentDiffers {
                            population: name.clone(),
                            expected: expected as usize,
                            supplied: bytes.len(),
                        });
                    }
                    let start = payload_len;
                    payload_len += expected;
                    NativePayloadDescriptor::Exact {
                        start,
                        end: payload_len,
                    }
                }
                NativePopulationPayload::External { locator: _ } => {
                    let start = payload_len;
                    payload_len += expected;
                    NativePayloadDescriptor::Exact {
                        start,
                        end: payload_len,
                    }
                }
                NativePopulationPayload::Open { fibre } => NativePayloadDescriptor::Open {
                    fibre: fibre.clone(),
                },
            };
            descriptors.push(NativePopulationDescriptor {
                native_name: population.native_name.clone(),
                source: population.source.clone(),
                payload: descriptor,
            });
        }
        if admitted_names.len() != admitted.len() {
            let missing = admitted
                .keys()
                .find(|name| !admitted_names.contains(*name))
                .cloned()
                .unwrap_or_else(|| "<unknown>".to_owned());
            return Err(NativeRestRefusal::ActivePopulationMissing {
                population: missing,
            });
        }
        let mut topology = input
            .topology
            .into_iter()
            .map(into_native_topology)
            .collect::<Vec<_>>();
        topology.sort_by(|left, right| left.identity.cmp(&right.identity));
        if topology
            .windows(2)
            .any(|pair| pair[0].identity == pair[1].identity)
        {
            return Err(NativeRestRefusal::DuplicateTopology {
                identity: topology[0].identity.clone(),
            });
        }
        let wire = NativeRestWire {
            schema: Self::SCHEMA.to_owned(),
            source: source_identity,
            topology,
            populations: descriptors,
            laws: input.laws,
            tilings: input.tilings,
            reductions: input.reductions,
            correspondence: input.correspondence,
            codebook: input.codebook,
            payload_octets: payload_len,
            // The payload digest is exactly 64 ASCII hex octets, so replacing this value after
            // the one source pass cannot change the serialized manifest extent.
            payload_sha256: "0".repeat(64),
        };
        validate_manifest_shape(&wire, payload_len)?;
        let placeholder_manifest =
            serde_json::to_vec(&wire).map_err(|e| NativeRestRefusal::WireDecode(e.to_string()))?;
        let start = output
            .stream_position()
            .map_err(|e| NativeRestRefusal::WireDecode(e.to_string()))?;
        if start != 0 {
            return Err(NativeRestRefusal::WireDecode(
                "native rest output must begin at offset zero".to_owned(),
            ));
        }
        output
            .write_all(NATIVE_REST_PREFIX)
            .map_err(|e| NativeRestRefusal::WireDecode(e.to_string()))?;
        output
            .write_all(&(placeholder_manifest.len() as u64).to_le_bytes())
            .map_err(|e| NativeRestRefusal::WireDecode(e.to_string()))?;
        output
            .write_all(&[0u8; MANIFEST_DIGEST_OCTETS])
            .map_err(|e| NativeRestRefusal::WireDecode(e.to_string()))?;
        output
            .write_all(&placeholder_manifest)
            .map_err(|e| NativeRestRefusal::WireDecode(e.to_string()))?;
        let mut payload_digest = Sha256::new();
        for population in &populations {
            match &population.payload {
                NativePopulationPayload::Exact { bytes } => {
                    super::manifest::validate_region_digest(&population.source, bytes)?;
                    output
                        .write_all(bytes)
                        .map_err(|e| NativeRestRefusal::WireDecode(e.to_string()))?;
                    payload_digest.update(bytes);
                    Ok(())
                }
                NativePopulationPayload::External { locator } => {
                    stream_external(locator, &input.source, &population.source, |chunk| {
                        payload_digest.update(chunk);
                        output
                            .write_all(chunk)
                            .map_err(|e| NativeRestRefusal::WireDecode(e.to_string()))
                    })
                }
                NativePopulationPayload::Open { .. } => Ok(()),
            }?;
        }
        let payload_sha256 = format!("{:x}", payload_digest.finalize());
        let mut final_wire = wire;
        final_wire.payload_sha256 = payload_sha256;
        let final_manifest = serde_json::to_vec(&final_wire)
            .map_err(|e| NativeRestRefusal::WireDecode(e.to_string()))?;
        if final_manifest.len() != placeholder_manifest.len() {
            return Err(NativeRestRefusal::WireDecode(
                "manifest extent changed during payload backpatch".to_owned(),
            ));
        }
        let payload_end = output
            .stream_position()
            .map_err(|e| NativeRestRefusal::WireDecode(e.to_string()))?;
        output
            .seek(SeekFrom::Start(NATIVE_REST_PREFIX.len() as u64))
            .map_err(|e| NativeRestRefusal::WireDecode(e.to_string()))?;
        output
            .write_all(&(final_manifest.len() as u64).to_le_bytes())
            .map_err(|e| NativeRestRefusal::WireDecode(e.to_string()))?;
        output
            .write_all(&super::manifest::manifest_digest(&final_manifest))
            .map_err(|e| NativeRestRefusal::WireDecode(e.to_string()))?;
        output
            .write_all(&final_manifest)
            .map_err(|e| NativeRestRefusal::WireDecode(e.to_string()))?;
        output
            .seek(SeekFrom::Start(payload_end))
            .map_err(|e| NativeRestRefusal::WireDecode(e.to_string()))?;
        Ok(())
    }
}
