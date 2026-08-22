//! Source-detached rest wire for the exchange world-tube.

use std::{
    collections::BTreeMap,
    ffi::OsString,
    fs,
    os::unix::ffi::{OsStrExt, OsStringExt},
    path::{Path, PathBuf},
};

use super::{
    ContainerLineageFaces, CorrespondenceFibres, DeviceContactReceipt, Digest32, ExchangeContainer,
    ExchangeRecord, ExchangeWorldTube, ExcludedPopulation, FieldFace, GlobalFieldFace, GlobalNode,
    NodeKind, RecordNode, ScalarContactSite, VisibleMessageFace,
};

pub const EXCHANGE_REST_PREFIX: [u8; 8] = *b"EWTB\0\0\0\x01";

pub fn write_exchange_world_tube_rest(
    world: &ExchangeWorldTube,
    path: &Path,
) -> Result<Digest32, String> {
    let bytes = encode(world)?;
    fs::write(path, &bytes).map_err(|error| format!("write {}: {error}", path.display()))?;
    Ok(Digest32::of(&bytes))
}

pub fn remount_exchange_world_tube(path: &Path) -> Result<ExchangeWorldTube, String> {
    let bytes = fs::read(path).map_err(|error| format!("read {}: {error}", path.display()))?;
    decode(&bytes)
}

/// Re-encode a remounted atlas and address the complete deterministic rest testimony. This is the
/// detached-process equality receiver: it covers every retained population, not only the native
/// content-law face.
pub fn exchange_world_tube_rest_digest(world: &ExchangeWorldTube) -> Result<Digest32, String> {
    Ok(Digest32::of(&encode(world)?))
}

fn encode(world: &ExchangeWorldTube) -> Result<Vec<u8>, String> {
    let mut out = Vec::new();
    out.extend_from_slice(&EXCHANGE_REST_PREFIX);
    put_string(&mut out, &world.schema)?;
    put_digest(&mut out, world.source_occurrence_sha256);
    put_digest(&mut out, world.content_law_sha256);
    put_u64(&mut out, world.containers.len())?;
    for container in &world.containers {
        put_u32(&mut out, container.ordinal);
        put_u64_raw(&mut out, container.captured_extent);
        put_digest(&mut out, container.prefix_sha256);
        put_u64_raw(&mut out, container.record_from);
        put_u64_raw(&mut out, container.record_extent);
        put_range_option(&mut out, &container.incomplete_tail);
        put_u64(&mut out, container.blank_records.len())?;
        for range in &container.blank_records {
            put_range(&mut out, range);
        }
        put_bytes(&mut out, container.lineage.locator.as_os_str().as_bytes())?;
        put_string(&mut out, &container.lineage.provider)?;
        put_string(&mut out, &container.lineage.material_kind)?;
    }
    put_u64(&mut out, world.records.len())?;
    for record in &world.records {
        put_u32(&mut out, record.container);
        put_u64_raw(&mut out, record.ordinal);
        put_range(&mut out, &record.raw_range);
        put_digest(&mut out, record.raw_sha256);
        put_digest(&mut out, record.root_sha256);
        put_u64_raw(&mut out, record.node_from);
        put_u32(&mut out, record.node_extent);
        put_u64_raw(&mut out, record.field_from);
        put_u32(&mut out, record.field_extent);
    }
    put_u64(&mut out, world.nodes.len())?;
    for node in &world.nodes {
        put_u64_raw(&mut out, node.record);
        put_option_u32(&mut out, node.local.parent);
        put_u32(&mut out, node.local.position);
        out.push(node.local.kind.wire());
        put_digest(&mut out, node.local.content);
    }
    put_u64(&mut out, world.fields.len())?;
    for field in &world.fields {
        put_u64_raw(&mut out, field.record);
        put_u32(&mut out, field.local.key_node);
        put_u32(&mut out, field.local.value_node);
        put_string(&mut out, &field.local.key)?;
        put_digest(&mut out, field.local.raw_key_sha256);
    }
    put_u64(&mut out, world.scalar_sites.len())?;
    for site in &world.scalar_sites {
        put_u64_raw(&mut out, site.node);
        put_digest(&mut out, site.content);
        put_u32(&mut out, site.class);
    }
    put_u64(&mut out, world.visible_messages.len())?;
    for face in &world.visible_messages {
        put_u32(&mut out, face.container);
        put_u64_raw(&mut out, face.record);
        put_range(&mut out, &face.raw_range);
        put_string(&mut out, &face.occurrence)?;
        put_digest(&mut out, face.text_sha256);
        put_string(&mut out, &face.text)?;
        put_string(&mut out, &face.provider_face)?;
        put_string(&mut out, &face.speaker_face)?;
        put_string(&mut out, &face.phase_face)?;
    }
    put_u64_raw(&mut out, world.excluded.blank_records);
    put_u64_raw(&mut out, world.excluded.incomplete_tails);
    put_u64_raw(&mut out, world.excluded.visible_membrane_controls);
    out.push(u8::from(
        world.excluded.unavailable_private_reasoning_required,
    ));
    put_string(&mut out, &world.device.schema)?;
    put_string(&mut out, &world.device.device)?;
    put_u64(&mut out, world.device.scalar_sites)?;
    put_u64(&mut out, world.device.contact_classes)?;
    put_u64_raw(&mut out, world.device.launches);
    put_u32(&mut out, world.device.block_threads);
    put_u32(&mut out, world.device.warp_size);
    out.push(u8::from(world.device.cpu_semantic_replay));
    Ok(out)
}

fn decode(bytes: &[u8]) -> Result<ExchangeWorldTube, String> {
    let mut input = Reader { bytes, at: 0 };
    if input.take(EXCHANGE_REST_PREFIX.len())? != EXCHANGE_REST_PREFIX {
        return Err("the exchange rest carries the wrong schema prefix".to_owned());
    }
    let schema = input.string()?;
    let source_occurrence_sha256 = input.digest()?;
    let content_law_sha256 = input.digest()?;
    let mut containers = Vec::new();
    for _ in 0..input.len()? {
        let ordinal = input.u32()?;
        let captured_extent = input.u64()?;
        let prefix_sha256 = input.digest()?;
        let record_from = input.u64()?;
        let record_extent = input.u64()?;
        let incomplete_tail = input.range_option()?;
        let mut blank_records = Vec::new();
        for _ in 0..input.len()? {
            blank_records.push(input.range()?);
        }
        let locator = PathBuf::from(OsString::from_vec(input.bytes()?.to_vec()));
        containers.push(ExchangeContainer {
            ordinal,
            captured_extent,
            prefix_sha256,
            record_from,
            record_extent,
            incomplete_tail,
            blank_records,
            lineage: ContainerLineageFaces {
                locator,
                provider: input.string()?,
                material_kind: input.string()?,
            },
        });
    }
    let mut records = Vec::new();
    for _ in 0..input.len()? {
        records.push(ExchangeRecord {
            container: input.u32()?,
            ordinal: input.u64()?,
            raw_range: input.range()?,
            raw_sha256: input.digest()?,
            root_sha256: input.digest()?,
            node_from: input.u64()?,
            node_extent: input.u32()?,
            field_from: input.u64()?,
            field_extent: input.u32()?,
        });
    }
    let mut nodes = Vec::new();
    for _ in 0..input.len()? {
        nodes.push(GlobalNode {
            record: input.u64()?,
            local: RecordNode {
                parent: input.option_u32()?,
                position: input.u32()?,
                kind: NodeKind::from_wire(input.u8()?)?,
                content: input.digest()?,
            },
        });
    }
    let mut fields = Vec::new();
    for _ in 0..input.len()? {
        fields.push(GlobalFieldFace {
            record: input.u64()?,
            local: FieldFace {
                key_node: input.u32()?,
                value_node: input.u32()?,
                key: input.string()?,
                raw_key_sha256: input.digest()?,
            },
        });
    }
    let mut scalar_sites = Vec::new();
    let mut class_members = BTreeMap::<u32, Vec<u64>>::new();
    for _ in 0..input.len()? {
        let site = ScalarContactSite {
            node: input.u64()?,
            content: input.digest()?,
            class: input.u32()?,
        };
        class_members.entry(site.class).or_default().push(site.node);
        scalar_sites.push(site);
    }
    let mut visible_messages = Vec::new();
    for _ in 0..input.len()? {
        visible_messages.push(VisibleMessageFace {
            container: input.u32()?,
            record: input.u64()?,
            raw_range: input.range()?,
            occurrence: input.string()?,
            text_sha256: input.digest()?,
            text: input.string()?,
            provider_face: input.string()?,
            speaker_face: input.string()?,
            phase_face: input.string()?,
        });
    }
    let excluded = ExcludedPopulation {
        blank_records: input.u64()?,
        incomplete_tails: input.u64()?,
        visible_membrane_controls: input.u64()?,
        unavailable_private_reasoning_required: input.boolean()?,
    };
    let device = DeviceContactReceipt {
        schema: input.string()?,
        device: input.string()?,
        scalar_sites: input.usize()?,
        contact_classes: input.usize()?,
        launches: input.u64()?,
        block_threads: input.u32()?,
        warp_size: input.u32()?,
        cpu_semantic_replay: input.boolean()?,
    };
    if input.at != bytes.len() {
        return Err(format!(
            "the exchange rest carries {} trailing octets",
            bytes.len() - input.at
        ));
    }
    let singleton_classes = class_members
        .values()
        .filter(|members| members.len() == 1)
        .count() as u64;
    let repeated_classes = class_members
        .values()
        .filter(|members| members.len() > 1)
        .count() as u64;
    let repeated_sites = class_members
        .values()
        .filter(|members| members.len() > 1)
        .map(|members| members.len() as u64)
        .sum();
    let world = ExchangeWorldTube {
        schema,
        source_occurrence_sha256,
        content_law_sha256,
        containers,
        records,
        nodes,
        fields,
        scalar_sites,
        visible_messages,
        fibres: CorrespondenceFibres {
            singleton_classes,
            repeated_classes,
            repeated_sites,
            class_members,
        },
        excluded,
        device,
    };
    let recomputed = super::receiver::content_law_digest(&world);
    if recomputed != world.content_law_sha256 {
        return Err(format!(
            "the exchange rest content law changed: stored {}, remounted {}",
            world.content_law_sha256.render(),
            recomputed.render()
        ));
    }
    Ok(world)
}

fn put_u32(out: &mut Vec<u8>, value: u32) {
    out.extend_from_slice(&value.to_le_bytes());
}

fn put_u64_raw(out: &mut Vec<u8>, value: u64) {
    out.extend_from_slice(&value.to_le_bytes());
}

fn put_u64(out: &mut Vec<u8>, value: usize) -> Result<(), String> {
    put_u64_raw(
        out,
        u64::try_from(value).map_err(|_| "a rest extent exceeds u64".to_owned())?,
    );
    Ok(())
}

fn put_digest(out: &mut Vec<u8>, digest: Digest32) {
    out.extend_from_slice(&digest.octets());
}

fn put_bytes(out: &mut Vec<u8>, bytes: &[u8]) -> Result<(), String> {
    put_u64(out, bytes.len())?;
    out.extend_from_slice(bytes);
    Ok(())
}

fn put_string(out: &mut Vec<u8>, text: &str) -> Result<(), String> {
    put_bytes(out, text.as_bytes())
}

fn put_range(out: &mut Vec<u8>, range: &std::ops::Range<u64>) {
    put_u64_raw(out, range.start);
    put_u64_raw(out, range.end);
}

fn put_range_option(out: &mut Vec<u8>, range: &Option<std::ops::Range<u64>>) {
    out.push(u8::from(range.is_some()));
    if let Some(range) = range {
        put_range(out, range);
    }
}

fn put_option_u32(out: &mut Vec<u8>, value: Option<u32>) {
    out.push(u8::from(value.is_some()));
    if let Some(value) = value {
        put_u32(out, value);
    }
}

struct Reader<'a> {
    bytes: &'a [u8],
    at: usize,
}

impl<'a> Reader<'a> {
    fn take(&mut self, extent: usize) -> Result<&'a [u8], String> {
        let end = self
            .at
            .checked_add(extent)
            .ok_or_else(|| "a rest range overflowed".to_owned())?;
        let slice = self
            .bytes
            .get(self.at..end)
            .ok_or_else(|| "the exchange rest is truncated".to_owned())?;
        self.at = end;
        Ok(slice)
    }

    fn u8(&mut self) -> Result<u8, String> {
        Ok(self.take(1)?[0])
    }

    fn boolean(&mut self) -> Result<bool, String> {
        match self.u8()? {
            0 => Ok(false),
            1 => Ok(true),
            other => Err(format!("a rest boolean carries {other}")),
        }
    }

    fn u32(&mut self) -> Result<u32, String> {
        Ok(u32::from_le_bytes(
            self.take(4)?.try_into().expect("four octets"),
        ))
    }

    fn u64(&mut self) -> Result<u64, String> {
        Ok(u64::from_le_bytes(
            self.take(8)?.try_into().expect("eight octets"),
        ))
    }

    fn usize(&mut self) -> Result<usize, String> {
        usize::try_from(self.u64()?).map_err(|_| "a rest extent exceeds usize".to_owned())
    }

    fn len(&mut self) -> Result<usize, String> {
        let extent = self.usize()?;
        if extent > self.bytes.len().saturating_sub(self.at) {
            return Err("a rest population exceeds the remaining wire".to_owned());
        }
        Ok(extent)
    }

    fn digest(&mut self) -> Result<Digest32, String> {
        Ok(Digest32::from_sha(self.take(32)?))
    }

    fn bytes(&mut self) -> Result<&'a [u8], String> {
        let extent = self.len()?;
        self.take(extent)
    }

    fn string(&mut self) -> Result<String, String> {
        String::from_utf8(self.bytes()?.to_vec())
            .map_err(|_| "a rest string is not UTF-8".to_owned())
    }

    fn range(&mut self) -> Result<std::ops::Range<u64>, String> {
        let start = self.u64()?;
        let end = self.u64()?;
        if start > end {
            return Err("a rest range is reversed".to_owned());
        }
        Ok(start..end)
    }

    fn range_option(&mut self) -> Result<Option<std::ops::Range<u64>>, String> {
        Ok(if self.boolean()? {
            Some(self.range()?)
        } else {
            None
        })
    }

    fn option_u32(&mut self) -> Result<Option<u32>, String> {
        Ok(if self.boolean()? {
            Some(self.u32()?)
        } else {
            None
        })
    }
}
