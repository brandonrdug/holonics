//! Incremental source mounting and the resident exact scalar quotient.

use std::{
    collections::BTreeMap,
    fs::File,
    io::{BufRead, BufReader, Read},
    ops::Range,
    path::PathBuf,
};

use holonic_engine::cuda_refine::CudaRefineExecutor;
use sha2::{Digest, Sha256};
use thiserror::Error;

use super::{
    json_record::parse_record, ContainerLineageFaces, CorrespondenceFibres, DeviceContactReceipt,
    Digest32, ExchangeContainer, ExchangeRecord, ExchangeWorldTube, ExcludedPopulation,
    GlobalFieldFace, GlobalNode, ScalarContactSite,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExchangeContainerSpec {
    pub locator: PathBuf,
    pub provider_face: String,
    pub material_kind_face: String,
}

#[derive(Debug, Error)]
pub enum ExchangeMountError {
    #[error("the exchange source declares no containers")]
    EmptySource,
    #[error("inspect {path}: {message}")]
    Inspect { path: String, message: String },
    #[error("read {path}: {message}")]
    Read { path: String, message: String },
    #[error("parse {path} record {record} raw[{from}..{to}]: {message}")]
    Parse {
        path: String,
        record: u64,
        from: u64,
        to: u64,
        message: String,
    },
    #[error("the exchange population exceeded an exact wire: {0}")]
    Extent(String),
    #[error("the resident scalar quotient refused: {0}")]
    Device(String),
}

struct StagedMount {
    containers: Vec<ExchangeContainer>,
    records: Vec<ExchangeRecord>,
    nodes: Vec<GlobalNode>,
    fields: Vec<GlobalFieldFace>,
    scalar_nodes: Vec<u64>,
    blank_records: u64,
    incomplete_tails: u64,
}

/// Mount exact prefixes of every declared container, one record at a time, then found the scalar
/// contact classes through the card's material-free quotient. The raw store is never held whole.
pub fn mount_exchange_world_tube_on_device(
    specs: &[ExchangeContainerSpec],
) -> Result<ExchangeWorldTube, ExchangeMountError> {
    if specs.is_empty() {
        return Err(ExchangeMountError::EmptySource);
    }
    // One chronology boundary for the occurrence: every extent is captured before any read.
    let mut captured = Vec::with_capacity(specs.len());
    for spec in specs {
        let metadata = spec
            .locator
            .metadata()
            .map_err(|error| ExchangeMountError::Inspect {
                path: spec.locator.display().to_string(),
                message: error.to_string(),
            })?;
        if !metadata.is_file() {
            return Err(ExchangeMountError::Inspect {
                path: spec.locator.display().to_string(),
                message: "the declared container is not a regular file".to_owned(),
            });
        }
        captured.push(metadata.len());
    }
    let staged = stream_mount(specs, &captured)?;
    let source_occurrence = source_occurrence_digest(&staged.containers);

    let mut cuda =
        CudaRefineExecutor::new().map_err(|error| ExchangeMountError::Device(error.to_string()))?;
    let before = cuda.launches();
    let mut classes = vec![1u32; staged.scalar_nodes.len()];
    for word in 0..4usize {
        let keys = staged
            .scalar_nodes
            .iter()
            .map(|node| {
                let digest = staged.nodes[*node as usize].local.content.octets();
                let from = word * 8;
                u64::from_le_bytes(
                    digest[from..from + 8]
                        .try_into()
                        .expect("eight digest octets"),
                )
            })
            .collect::<Vec<_>>();
        classes = cuda
            .quotient_on_device(&classes, &keys)
            .map_err(|error| ExchangeMountError::Device(error.to_string()))?
            .cell_class;
    }
    // Device slot identities are apparatus coordinates. Rebase the returned partition by first
    // situated occurrence so identical partitions receive one stable numbering without replaying
    // or recomputing a single equality.
    let mut canonical = BTreeMap::<u32, u32>::new();
    for class in &mut classes {
        let next = canonical.len() as u32 + 1;
        *class = *canonical.entry(*class).or_insert(next);
    }
    let launches = cuda.launches().saturating_sub(before);
    let mut scalar_sites = Vec::with_capacity(staged.scalar_nodes.len());
    let mut class_members: BTreeMap<u32, Vec<u64>> = BTreeMap::new();
    for (node, class) in staged.scalar_nodes.iter().zip(&classes) {
        let content = staged.nodes[*node as usize].local.content;
        scalar_sites.push(ScalarContactSite {
            node: *node,
            content,
            class: *class,
        });
        class_members.entry(*class).or_default().push(*node);
    }
    let singleton_classes = class_members
        .values()
        .filter(|members| members.len() == 1)
        .count();
    let repeated_classes = class_members
        .values()
        .filter(|members| members.len() > 1)
        .count();
    let repeated_sites = class_members
        .values()
        .filter(|members| members.len() > 1)
        .try_fold(0u64, |total, members| {
            total.checked_add(members.len() as u64)
        })
        .ok_or_else(|| ExchangeMountError::Extent("repeated scalar population".to_owned()))?;

    let mut world = ExchangeWorldTube {
        schema: "soma-life.exchange-world-tube.v1".to_owned(),
        source_occurrence_sha256: source_occurrence,
        content_law_sha256: Digest32::ZERO,
        containers: staged.containers,
        records: staged.records,
        nodes: staged.nodes,
        fields: staged.fields,
        scalar_sites,
        visible_messages: Vec::new(),
        fibres: CorrespondenceFibres {
            singleton_classes: singleton_classes as u64,
            repeated_classes: repeated_classes as u64,
            repeated_sites,
            class_members,
        },
        excluded: ExcludedPopulation {
            blank_records: staged.blank_records,
            incomplete_tails: staged.incomplete_tails,
            visible_membrane_controls: 0,
            unavailable_private_reasoning_required: false,
        },
        device: DeviceContactReceipt {
            schema: "soma-life.exchange-scalar-contact-device.v1".to_owned(),
            device: cuda.device_name().to_owned(),
            scalar_sites: staged.scalar_nodes.len(),
            contact_classes: canonical.len(),
            launches,
            block_threads: cuda.block_threads(),
            warp_size: cuda.warp_size(),
            cpu_semantic_replay: false,
        },
    };
    world.content_law_sha256 = super::receiver::content_law_digest(&world);
    Ok(world)
}

fn stream_mount(
    specs: &[ExchangeContainerSpec],
    captured: &[u64],
) -> Result<StagedMount, ExchangeMountError> {
    let mut containers = Vec::with_capacity(specs.len());
    let mut records = Vec::new();
    let mut nodes = Vec::new();
    let mut fields = Vec::new();
    let mut scalar_nodes = Vec::new();
    let mut blank_records = 0u64;
    let mut incomplete_tails = 0u64;

    for (container_at, (spec, extent)) in specs.iter().zip(captured).enumerate() {
        let container = u32::try_from(container_at)
            .map_err(|_| ExchangeMountError::Extent("container population".to_owned()))?;
        let input = File::open(&spec.locator).map_err(|error| ExchangeMountError::Read {
            path: spec.locator.display().to_string(),
            message: error.to_string(),
        })?;
        let mut input = BufReader::new(input.take(*extent));
        let mut prefix = Sha256::new();
        let mut raw = Vec::new();
        let mut raw_at = 0u64;
        let record_from = records.len() as u64;
        let mut local_record = 0u64;
        let mut blank_ranges = Vec::new();
        let mut incomplete_tail = None;
        loop {
            raw.clear();
            let read =
                input
                    .read_until(b'\n', &mut raw)
                    .map_err(|error| ExchangeMountError::Read {
                        path: spec.locator.display().to_string(),
                        message: error.to_string(),
                    })?;
            if read == 0 {
                break;
            }
            prefix.update(&raw);
            let raw_end = raw_at
                .checked_add(read as u64)
                .ok_or_else(|| ExchangeMountError::Extent("raw source range".to_owned()))?;
            let range = raw_at..raw_end;
            if raw.iter().all(u8::is_ascii_whitespace) {
                blank_records = blank_records.checked_add(1).ok_or_else(|| {
                    ExchangeMountError::Extent("blank record population".to_owned())
                })?;
                blank_ranges.push(range);
            } else {
                let parsed = match parse_record(&raw) {
                    Ok(parsed) => parsed,
                    Err(message) if raw_end == *extent && raw.last() != Some(&b'\n') => {
                        incomplete_tails = incomplete_tails.checked_add(1).ok_or_else(|| {
                            ExchangeMountError::Extent("incomplete tail population".to_owned())
                        })?;
                        incomplete_tail = Some(range);
                        raw_at = raw_end;
                        break;
                    }
                    Err(message) => {
                        return Err(ExchangeMountError::Parse {
                            path: spec.locator.display().to_string(),
                            record: local_record,
                            from: raw_at,
                            to: raw_end,
                            message,
                        });
                    }
                };
                let global_record = records.len() as u64;
                let node_from = nodes.len() as u64;
                let field_from = fields.len() as u64;
                for (local, node) in parsed.nodes.into_iter().enumerate() {
                    let global_node = nodes.len() as u64;
                    if parsed.scalar_nodes.binary_search(&(local as u32)).is_ok() {
                        scalar_nodes.push(global_node);
                    }
                    nodes.push(GlobalNode {
                        record: global_record,
                        local: node,
                    });
                }
                fields.extend(parsed.fields.into_iter().map(|local| GlobalFieldFace {
                    record: global_record,
                    local,
                }));
                records.push(ExchangeRecord {
                    container,
                    ordinal: local_record,
                    raw_range: range,
                    raw_sha256: Digest32::of(&raw),
                    root_sha256: parsed.root_digest,
                    node_from,
                    node_extent: u32::try_from(nodes.len() as u64 - node_from).map_err(|_| {
                        ExchangeMountError::Extent("record node population".to_owned())
                    })?,
                    field_from,
                    field_extent: u32::try_from(fields.len() as u64 - field_from).map_err(
                        |_| ExchangeMountError::Extent("record field population".to_owned()),
                    )?,
                });
                local_record = local_record
                    .checked_add(1)
                    .ok_or_else(|| ExchangeMountError::Extent("record population".to_owned()))?;
            }
            raw_at = raw_end;
        }
        if raw_at != *extent {
            return Err(ExchangeMountError::Read {
                path: spec.locator.display().to_string(),
                message: format!("captured {extent} octets but read {raw_at}"),
            });
        }
        containers.push(ExchangeContainer {
            ordinal: container,
            captured_extent: *extent,
            prefix_sha256: Digest32::from_sha(prefix.finalize()),
            record_from,
            record_extent: records.len() as u64 - record_from,
            incomplete_tail,
            blank_records: blank_ranges,
            lineage: ContainerLineageFaces {
                locator: spec.locator.clone(),
                provider: spec.provider_face.clone(),
                material_kind: spec.material_kind_face.clone(),
            },
        });
    }
    Ok(StagedMount {
        containers,
        records,
        nodes,
        fields,
        scalar_nodes,
        blank_records,
        incomplete_tails,
    })
}

fn source_occurrence_digest(containers: &[ExchangeContainer]) -> Digest32 {
    let mut digest = Sha256::new();
    digest.update(b"exchange-source-occurrence/v1");
    digest.update((containers.len() as u64).to_le_bytes());
    for container in containers {
        digest.update(container.ordinal.to_le_bytes());
        digest.update(container.captured_extent.to_le_bytes());
        digest.update(container.prefix_sha256.octets());
        digest.update(container.record_extent.to_le_bytes());
    }
    Digest32::from_sha(digest.finalize())
}

#[allow(dead_code)]
fn _range_is_typed(_: Range<u64>) {}
