//! Cold, source-qualified conversation occurrences. No native current or learned response is
//! manufactured here. A frame contains one declared occurrence's captured views, never a
//! request with its future response. Relation targets carry coordinates, not their material.

use crate::{CheckpointError, HnaBaseDependency, HnaFileDependency};
use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::{
    collections::{BTreeMap, BTreeSet},
    fs::File,
    io::{self, BufRead, BufReader, Read, Seek, SeekFrom},
    path::Path,
};
use thiserror::Error;

pub const EXPOSURE_SCHEMA: &str = "holonics.conversation-exposure.v1";

#[derive(Debug, Error)]
pub enum ExposureError {
    #[error("conversation exposure I/O: {0}")]
    Io(#[from] io::Error),
    #[error("conversation exposure wire: {0}")]
    Json(#[from] serde_json::Error),
    #[error(transparent)]
    Source(#[from] CheckpointError),
    #[error("conversation exposure boundary: {0}")]
    Boundary(String),
    #[error("conversation exposure is open: {0}")]
    Open(&'static str),
}

fn boundary(message: impl Into<String>) -> ExposureError {
    ExposureError::Boundary(message.into())
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExposureSource {
    pub source: u64,
    pub provider: String,
    pub private_path: String,
    pub captured_octets: u64,
    pub records: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExposureManifest {
    pub schema: String,
    pub kind: String,
    /// Cold capture and presentation declarations. These never select native conduct.
    pub temporal_cut: String,
    pub temporal_cut_normalized: String,
    pub private_sources: Vec<ExposureSource>,
    pub boundary: BTreeMap<String, String>,
    pub visible_parts: BTreeMap<String, Vec<String>>,
}

impl ExposureManifest {
    fn cut(&self) -> Result<&str, ExposureError> {
        normalized_time(&self.temporal_cut_normalized)
            .then_some(self.temporal_cut_normalized.as_str())
            .ok_or_else(|| boundary("missing or malformed normalized development cut"))
    }

    fn validate(&self) -> Result<(), ExposureError> {
        if self.schema != EXPOSURE_SCHEMA || self.kind != "manifest" {
            return Err(boundary("unsupported manifest schema/kind"));
        }
        self.cut()?;
        let mut sources = BTreeSet::new();
        for source in &self.private_sources {
            if source.source == 0 || source.provider.is_empty() || !sources.insert(source.source) {
                return Err(boundary("absent or repeated source coordinate"));
            }
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExposureFamily {
    pub provider: String,
    /// A provider-declared record view group or one captured record; not native holon identity.
    pub record_group: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum ExposurePartition {
    Development,
    Evaluation,
    Deferred,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExposureRecordAddress {
    pub number: u64,
    pub byte_start: u64,
    pub byte_end: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExposurePart {
    pub ordinal: u64,
    pub pointer: String,
    pub kind: String,
    pub text: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExposurePartReference {
    pub ordinal: u64,
    pub pointer: String,
    pub kind: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExposureTarget {
    pub event: u64,
    pub source: u64,
    pub provider: String,
    pub record_group: String,
    pub timestamp: Option<String>,
    pub normalized_timestamp: Option<String>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum ExposureAvailability {
    Prior,
    NotPrior,
    Ambiguous,
    Unresolved,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExposureLink {
    pub kind: String,
    pub target_event: Option<u64>,
    pub reference: Option<String>,
    pub evidence: String,
    pub target: Option<ExposureTarget>,
    pub availability: ExposureAvailability,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExposureView {
    pub event: u64,
    pub source: u64,
    pub provider: String,
    pub record: ExposureRecordAddress,
    pub timestamp: Option<String>,
    pub normalized_timestamp: Option<String>,
    pub native_id: Option<String>,
    pub parent_id: Option<String>,
    pub session_id: Option<String>,
    pub branch_id: Option<String>,
    pub workspace: Option<String>,
    pub phase: Option<String>,
    pub turn_id: Option<String>,
    pub model: Option<String>,
    pub author_class: String,
    pub record_kind: String,
    pub flags: Vec<String>,
    /// Provider API generation, parent-session/agent-path and original attribution testimony.
    /// This cold metadata never becomes material amplitude or a native route selector.
    pub provider_metadata: BTreeMap<String, Value>,
    pub previous_record: Option<u64>,
    pub visible_parts: Vec<ExposurePart>,
    pub nonvisible_part_references: Vec<ExposurePartReference>,
    pub links: Vec<ExposureLink>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExposureCapturePosition {
    pub first_source: u64,
    pub first_record: u64,
    pub first_event: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExposureOrderConflict {
    pub event: u64,
    pub request_event: Option<u64>,
    pub availability: ExposureAvailability,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "kebab-case", deny_unknown_fields)]
pub enum ExposureConflict {
    Timestamp {
        views: Vec<(u64, Option<String>, Option<String>)>,
    },
    AuthorRole {
        views: Vec<(u64, String)>,
    },
    Material {
        events: Vec<u64>,
    },
    RequestResponseOrder {
        views: Vec<ExposureOrderConflict>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExposureOccurrence {
    pub schema: String,
    pub kind: String,
    pub sequence: u64,
    pub position: ExposureCapturePosition,
    pub family: ExposureFamily,
    pub partition: ExposurePartition,
    pub partition_reasons: Vec<String>,
    pub conflicts: Vec<ExposureConflict>,
    pub views: Vec<ExposureView>,
}

impl ExposureOccurrence {
    /// One prior parent common to every captured view of a validated exposure occurrence.
    /// The reader/manifest validation owns source and availability verification. The first native text
    /// attachment has one contextual source port; differing parents or unavailable relations
    /// remain open rather than selecting a link by order or provider preference.
    pub fn shared_prior_parent(&self) -> Result<Option<ExposureFamily>, ExposureError> {
        Ok(self
            .shared_prior_parent_targets()?
            .map(|(family, _)| family))
    }

    /// The common prior parent family and all captured event aliases naming that family. Event
    /// aliases stay attached to the lookup so a repeated provider family cannot silently select
    /// its latest occurrence by sequence alone.
    pub fn shared_prior_parent_targets(
        &self,
    ) -> Result<Option<(ExposureFamily, BTreeSet<u64>)>, ExposureError> {
        let mut common: Option<BTreeSet<ExposureFamily>> = None;
        let mut aliases = BTreeSet::new();
        for view in &self.views {
            let mut parents = BTreeSet::new();
            for link in &view.links {
                if !matches!(
                    link.kind.as_str(),
                    "provider-parent" | "comparison-request" | "later-human-after-agent"
                ) || link.availability != ExposureAvailability::Prior
                {
                    return Err(ExposureError::Open(
                        "parent relation is unavailable or outside the admitted source port",
                    ));
                }
                let target = link
                    .target
                    .as_ref()
                    .ok_or(ExposureError::Open("prior parent has no source coordinate"))?;
                parents.insert(ExposureFamily {
                    provider: target.provider.clone(),
                    record_group: target.record_group.clone(),
                });
                aliases.insert(target.event);
            }
            if common.as_ref().is_some_and(|previous| *previous != parents) {
                return Err(ExposureError::Open(
                    "captured views disagree on the available parent",
                ));
            }
            common = Some(parents);
        }
        let parents = common.ok_or(ExposureError::Open("no captured views"))?;
        if parents.len() > 1 {
            return Err(ExposureError::Open(
                "several parent families require a wider contextual source port",
            ));
        }
        Ok(parents.into_iter().next().map(|family| (family, aliases)))
    }

    /// The one author role every captured view of this declared occurrence testifies to. The
    /// role admits or refuses material at an exterior boundary; it never becomes a native
    /// amplitude, a route selector or evidence that the occurrence answered anything.
    pub fn shared_author_class(&self) -> Result<&str, ExposureError> {
        let first = self
            .views
            .first()
            .ok_or(ExposureError::Open("no captured views"))?;
        if self.views[1..]
            .iter()
            .any(|view| view.author_class != first.author_class)
        {
            return Err(ExposureError::Open(
                "captured views disagree on the author role",
            ));
        }
        Ok(&first.author_class)
    }

    /// The request family this responding occurrence records as its own comparison partner.
    /// `comparison-request` belongs to the actual responding occurrence, so this reads that one
    /// relation kind and ignores every other; a tool or candidate link elsewhere in the family
    /// neither supplies a partner nor refuses this one. An absent relation stays absent.
    pub fn recorded_comparison_request(&self) -> Result<Option<ExposureFamily>, ExposureError> {
        Ok(self
            .recorded_comparison_request_targets()?
            .map(|(family, _)| family))
    }

    /// The common recorded comparison family and all event coordinates named by its captured
    /// views. Captured providers may expose different event aliases for one family; preserving
    /// their union avoids choosing the first view by order.
    pub fn recorded_comparison_request_targets(
        &self,
    ) -> Result<Option<(ExposureFamily, BTreeSet<u64>)>, ExposureError> {
        let mut common_family: Option<Option<ExposureFamily>> = None;
        let mut aliases = BTreeSet::new();
        for view in &self.views {
            let mut view_family: Option<ExposureFamily> = None;
            for link in &view.links {
                if link.kind != "comparison-request" {
                    continue;
                }
                if link.availability != ExposureAvailability::Prior {
                    return Err(ExposureError::Open(
                        "recorded comparison request is not an available prior occurrence",
                    ));
                }
                let target = link.target.as_ref().ok_or(ExposureError::Open(
                    "recorded comparison request has no source coordinate",
                ))?;
                let family = ExposureFamily {
                    provider: target.provider.clone(),
                    record_group: target.record_group.clone(),
                };
                if view_family
                    .as_ref()
                    .is_some_and(|previous| *previous != family)
                {
                    return Err(ExposureError::Open(
                        "several recorded comparison families require a wider source port",
                    ));
                }
                view_family = Some(family);
                aliases.insert(target.event);
            }
            if common_family
                .as_ref()
                .is_some_and(|previous| previous != &view_family)
            {
                return Err(ExposureError::Open(
                    "captured views disagree on the recorded comparison family",
                ));
            }
            common_family = Some(view_family);
        }
        if self.views.is_empty() {
            return Err(ExposureError::Open("no captured views"));
        }
        Ok(common_family.flatten().map(|family| (family, aliases)))
    }

    /// The same visible material in every captured view of this declared occurrence. This
    /// compares exterior presentations only; it neither chooses an incompatible view nor
    /// identifies equal text from distinct occurrences. Source/context views remain attached.
    pub fn shared_visible_parts(&self) -> Result<&[ExposurePart], ExposureError> {
        let first = self
            .views
            .first()
            .ok_or(ExposureError::Open("no captured views"))?;
        if first.visible_parts.is_empty() {
            return Err(ExposureError::Open("no visible material"));
        }
        for other in &self.views[1..] {
            if other.author_class != first.author_class
                || other.visible_parts.len() != first.visible_parts.len()
                || other
                    .visible_parts
                    .iter()
                    .zip(&first.visible_parts)
                    .any(|(a, b)| a.kind != b.kind || a.text != b.text || a.ordinal != b.ordinal)
            {
                return Err(ExposureError::Open("captured presentations disagree"));
            }
        }
        Ok(&first.visible_parts)
    }

    /// Explicit exterior population boundary for a cultivation consumer. Evaluation/deferred
    /// material stays readable as evidence, but cannot enter this developmental projection.
    pub fn development_parts(&self) -> Result<&[ExposurePart], ExposureError> {
        if self.partition != ExposurePartition::Development {
            return Err(ExposureError::Open(
                "occurrence is outside the development population",
            ));
        }
        self.shared_visible_parts()
    }

    pub fn validate(&self, manifest: &ExposureManifest) -> Result<(), ExposureError> {
        let sources: BTreeMap<_, _> = manifest
            .private_sources
            .iter()
            .enumerate()
            .map(|(i, s)| (s.source, i))
            .collect();
        self.validate_with_sources(manifest, &sources)
    }

    fn validate_with_sources(
        &self,
        manifest: &ExposureManifest,
        sources: &BTreeMap<u64, usize>,
    ) -> Result<(), ExposureError> {
        if self.schema != EXPOSURE_SCHEMA || self.kind != "occurrence-family" {
            return Err(boundary("unsupported occurrence schema/kind"));
        }
        self.sequence
            .checked_add(1)
            .ok_or_else(|| boundary("exposure sequence exhausted"))?;
        if self.views.is_empty() || self.family.provider.is_empty() {
            return Err(boundary("occurrence has no source views"));
        }
        if self.partition == ExposurePartition::Deferred && self.partition_reasons.is_empty() {
            return Err(boundary("deferred occurrence has no retained reason"));
        }
        let actual = self
            .views
            .iter()
            .map(|v| (v.source, v.record.number, v.event))
            .min();
        if actual
            != Some((
                self.position.first_source,
                self.position.first_record,
                self.position.first_event,
            ))
        {
            return Err(boundary(
                "first capture position is not an actual retained view",
            ));
        }
        let mut events = BTreeSet::new();
        for view in &self.views {
            let source = sources
                .get(&view.source)
                .and_then(|i| manifest.private_sources.get(*i))
                .ok_or_else(|| boundary("view names an absent source"))?;
            let group = match &view.native_id {
                Some(id) => format!("declared:{id}"),
                None => format!("capture:{}", view.event),
            };
            if view.event == 0
                || !events.insert(view.event)
                || source.provider != view.provider
                || view.provider != self.family.provider
                || group != self.family.record_group
                || view.record.number == 0
                || view.record.number > source.records
                || view.record.byte_start >= view.record.byte_end
                || view.record.byte_end > source.captured_octets
            {
                return Err(boundary(
                    "view source, family or captured byte range disagrees",
                ));
            }
            if let Some(time) = &view.normalized_timestamp {
                if !normalized_time(time) {
                    return Err(boundary("malformed normalized occurrence time"));
                }
            }
            let mut parts = BTreeSet::new();
            for part in &view.visible_parts {
                let admitted = match view.author_class.as_str() {
                    "human" => matches!(
                        part.kind.as_str(),
                        "human-text" | "human-material" | "human-command"
                    ),
                    "agent-visible" => {
                        matches!(part.kind.as_str(), "agent-text" | "agent-material")
                    }
                    _ => false,
                };
                if !admitted || !part.pointer.starts_with('/') || !parts.insert(part.ordinal) {
                    return Err(boundary("visible part escaped its actual source role"));
                }
            }
            for part in &view.nonvisible_part_references {
                if !part.pointer.starts_with('/') || !parts.insert(part.ordinal) {
                    return Err(boundary(
                        "part reference is malformed or repeats a visible part",
                    ));
                }
            }
            for link in &view.links {
                if link.kind.is_empty() || link.evidence.is_empty() {
                    return Err(boundary("relation has no kind/evidence"));
                }
                if let Some(target) = &link.target {
                    let source = sources
                        .get(&target.source)
                        .and_then(|i| manifest.private_sources.get(*i));
                    if Some(target.event) != link.target_event
                        || target.event == 0
                        || source.is_none_or(|s| s.provider != target.provider)
                        || !(target.record_group.starts_with("declared:")
                            || target.record_group == format!("capture:{}", target.event))
                        || target
                            .normalized_timestamp
                            .as_ref()
                            .is_some_and(|t| !normalized_time(t))
                    {
                        return Err(boundary("relation target metadata disagrees"));
                    }
                }
                let expected = if link.target_event.is_none() || link.target.is_none() {
                    ExposureAvailability::Unresolved
                } else if link.kind.ends_with("-candidate") {
                    ExposureAvailability::Ambiguous
                } else {
                    match (
                        link.target
                            .as_ref()
                            .and_then(|t| t.normalized_timestamp.as_deref()),
                        view.normalized_timestamp.as_deref(),
                    ) {
                        (Some(prior), Some(now)) if prior < now => ExposureAvailability::Prior,
                        (Some(_), Some(_)) => ExposureAvailability::NotPrior,
                        _ => ExposureAvailability::Unresolved,
                    }
                };
                if link.availability != expected {
                    return Err(boundary(
                        "relation availability disagrees with retained metadata",
                    ));
                }
            }
        }
        if self.partition == ExposurePartition::Development {
            if !self.conflicts.is_empty() || !self.partition_reasons.is_empty() {
                return Err(boundary(
                    "development occurrence carries unresolved partition evidence",
                ));
            }
            let cut = manifest.cut()?;
            let first_time = self.views[0].normalized_timestamp.as_deref();
            for view in &self.views {
                let time = view.normalized_timestamp.as_deref();
                if time.is_none() || time != first_time || time.is_some_and(|time| time >= cut) {
                    return Err(boundary(
                        "development occurrence crosses its known temporal boundary",
                    ));
                }
            }
            self.shared_visible_parts()?;
        }
        Ok(())
    }
}

/// A cold file position, to be persisted alongside the native successor once that application
/// binding exists. This cursor alone is not evidence that native development occurred.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExposureCursor {
    pub source: HnaFileDependency,
    pub next_sequence: u64,
    pub byte_offset: u64,
}

/// Bounded cost of reconstructing recorded context from the pinned exposure wire. The index is
/// exterior metadata: it retains offsets and family/sequence coordinates, never native state or
/// message material. A reader builds it once, lazily, and seeks the verified wire for each frame
/// needed by a context chain.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExposureContextStats {
    pub index_entries: u64,
    pub index_scan_octets: u64,
    pub lookup_frames: u64,
    pub lookup_octets: u64,
}

#[derive(Clone, Debug)]
struct ExposureIndexEntry {
    sequence: u64,
    byte_offset: u64,
    family: ExposureFamily,
    octets: u64,
}

#[derive(Clone, Copy, Debug)]
enum ExposureAliasResolution {
    Entry(usize),
    Ambiguous,
}

#[derive(Default)]
struct ExposureContextIndex {
    by_alias: BTreeMap<(ExposureFamily, u64), ExposureAliasResolution>,
    entries: Vec<ExposureIndexEntry>,
    next_sequence: u64,
    next_offset: u64,
    blocked_at: Option<u64>,
    stats: ExposureContextStats,
}

struct PendingOccurrence {
    frame: ExposureOccurrence,
    after: u64,
}

/// One immutable exposure file. `peek` retains a frame until explicit acknowledgment; a saved
/// cursor still names that frame while it is pending. Source verification is a wire integrity
/// boundary, not semantic identity or authentication of an externally authored history.
pub struct ExposureReader {
    input: BufReader<File>,
    manifest: ExposureManifest,
    cursor: ExposureCursor,
    header_end: u64,
    pending: Option<PendingOccurrence>,
    stopped: bool,
    source_positions: BTreeMap<u64, usize>,
    context_index: Option<ExposureContextIndex>,
}

impl ExposureReader {
    pub fn open(path: impl AsRef<Path>) -> Result<Self, ExposureError> {
        let (base, file) = HnaBaseDependency::capture_with_open_handle(path, None)?;
        let source = HnaFileDependency {
            path: base.path,
            octets: base.octets,
            sha256: base.sha256,
        };
        Self::from_file(file, source, None)
    }

    pub fn resume(cursor: ExposureCursor) -> Result<Self, ExposureError> {
        let file = cursor.source.open_verified()?;
        Self::from_file(file, cursor.source.clone(), Some(cursor))
    }

    fn from_file(
        file: File,
        source: HnaFileDependency,
        cursor: Option<ExposureCursor>,
    ) -> Result<Self, ExposureError> {
        let mut input = BufReader::new(file);
        let mut line = Vec::new();
        input.read_until(b'\n', &mut line)?;
        if !line.ends_with(b"\n") {
            return Err(boundary("manifest is incomplete"));
        }
        let manifest: ExposureManifest = serde_json::from_slice(&line)?;
        manifest.validate()?;
        let header_end = input.stream_position()?;
        let cursor = cursor.unwrap_or(ExposureCursor {
            source,
            next_sequence: 0,
            byte_offset: header_end,
        });
        if cursor.byte_offset < header_end || cursor.byte_offset > cursor.source.octets {
            return Err(boundary("cursor is outside the occurrence wire"));
        }
        if cursor.byte_offset > header_end {
            input.seek(SeekFrom::Start(cursor.byte_offset - 1))?;
            let mut previous = [0];
            input.read_exact(&mut previous)?;
            if previous[0] != b'\n' {
                return Err(boundary("cursor does not follow a complete frame"));
            }
        }
        input.seek(SeekFrom::Start(cursor.byte_offset))?;
        let source_positions = manifest
            .private_sources
            .iter()
            .enumerate()
            .map(|(i, s)| (s.source, i))
            .collect();
        Ok(Self {
            input,
            manifest,
            cursor,
            header_end,
            pending: None,
            stopped: false,
            source_positions,
            context_index: None,
        })
    }

    pub fn manifest(&self) -> &ExposureManifest {
        &self.manifest
    }
    pub fn cursor(&self) -> ExposureCursor {
        self.cursor.clone()
    }

    /// Return the recorded prior exposure chain for `request` from the immutable source wire.
    /// Context bytes are the cumulative receiving aperture. Zero returns an empty context; a
    /// positive value admits only a complete recorded chain whose visible material fits that
    /// byte aperture. The exterior index scans the pinned source prefix through this request once,
    /// then seeks each admitted parent.
    pub fn recorded_context(
        &mut self,
        request: &ExposureOccurrence,
        context_bytes: usize,
    ) -> Result<Vec<ExposureOccurrence>, ExposureError> {
        if context_bytes == 0 {
            return Ok(Vec::new());
        }
        self.ensure_context_index(request.sequence)?;
        let mut next_parent = request.shared_prior_parent_targets()?;
        let mut next_sequence = request.sequence;
        let mut chain = Vec::new();
        let mut context_octets = 0usize;
        while let Some((family, aliases)) = next_parent {
            if self.alias_is_ambiguous(&family, &aliases) {
                return Err(ExposureError::Open(
                    "recorded context aliases resolve ambiguously",
                ));
            }
            let entry_index =
                self.context_index
                    .as_ref()
                    .map(|index| {
                        aliases
                            .iter()
                            .filter_map(|event| {
                                index.by_alias.get(&(family.clone(), *event)).and_then(
                                    |resolution| match resolution {
                                        ExposureAliasResolution::Entry(index) => Some(*index),
                                        ExposureAliasResolution::Ambiguous => None,
                                    },
                                )
                            })
                            .collect::<BTreeSet<_>>()
                    })
                    .ok_or(ExposureError::Open(
                        "recorded context is unavailable in the pinned source",
                    ))?;
            let entry_index = match entry_index.len() {
                0 => {
                    return Err(ExposureError::Open(
                        "recorded context is unavailable in the pinned source",
                    ));
                }
                1 => *entry_index.iter().next().expect("one entry"),
                _ => {
                    return Err(ExposureError::Open(
                        "recorded context aliases resolve to several prior occurrences",
                    ));
                }
            };
            let entry = self
                .context_index
                .as_ref()
                .and_then(|index| index.entries.get(entry_index))
                .filter(|entry| entry.sequence < next_sequence)
                .cloned()
                .ok_or(ExposureError::Open(
                    "recorded context is unavailable in the pinned source",
                ))?;
            let parent = self.read_indexed(&entry)?;
            let parent_octets = parent
                .development_parts()?
                .iter()
                .map(|part| {
                    part.text
                        .as_deref()
                        .map(str::len)
                        .ok_or(ExposureError::Open("recorded context has no visible text"))
                })
                .try_fold(0usize, |total, octets| {
                    octets?
                        .checked_add(total)
                        .ok_or_else(|| boundary("recorded context byte aperture overflow"))
                })?;
            context_octets = context_octets
                .checked_add(parent_octets)
                .ok_or_else(|| boundary("recorded context byte aperture overflow"))?;
            if context_octets > context_bytes {
                return Err(ExposureError::Open(
                    "recorded context exceeds the declared byte aperture",
                ));
            }
            next_sequence = parent.sequence;
            next_parent = parent.shared_prior_parent_targets()?;
            chain.push(parent);
        }
        chain.reverse();
        Ok(chain)
    }

    pub fn context_stats(&self) -> ExposureContextStats {
        self.context_index
            .as_ref()
            .map_or_else(ExposureContextStats::default, |index| index.stats)
    }

    fn alias_is_ambiguous(&self, family: &ExposureFamily, aliases: &BTreeSet<u64>) -> bool {
        aliases.iter().any(|event| {
            matches!(
                self.context_index
                    .as_ref()
                    .and_then(|index| index.by_alias.get(&(family.clone(), *event))),
                Some(ExposureAliasResolution::Ambiguous)
            )
        })
    }

    fn ensure_context_index(&mut self, through_sequence: u64) -> Result<(), ExposureError> {
        let mut index = self
            .context_index
            .take()
            .unwrap_or_else(|| ExposureContextIndex {
                next_offset: self.header_end,
                ..ExposureContextIndex::default()
            });
        if index.next_sequence >= through_sequence {
            self.context_index = Some(index);
            return Ok(());
        }
        if index
            .blocked_at
            .is_some_and(|sequence| sequence < through_sequence)
        {
            self.context_index = Some(index);
            return Err(boundary(
                "recorded context index stopped at a malformed source frame",
            ));
        }
        let saved = match self.input.stream_position() {
            Ok(saved) => saved,
            Err(error) => {
                self.context_index = Some(index);
                return Err(error.into());
            }
        };
        if let Err(error) = self.input.seek(SeekFrom::Start(index.next_offset)) {
            self.context_index = Some(index);
            return Err(error.into());
        }
        let result = (|| {
            while index.next_sequence < through_sequence {
                let offset = self.input.stream_position()?;
                let mut line = Vec::new();
                if self.input.read_until(b'\n', &mut line)? == 0 {
                    return Err(boundary("recorded context source prefix is incomplete"));
                }
                if !line.ends_with(b"\n") {
                    return Err(boundary("occurrence frame is incomplete"));
                }
                let frame: ExposureOccurrence = serde_json::from_slice(&line)?;
                if frame.sequence != index.next_sequence {
                    return Err(boundary("occurrence sequence disagrees with source index"));
                }
                frame.validate_with_sources(&self.manifest, &self.source_positions)?;
                let entry_index = index.entries.len();
                let after = self.input.stream_position()?;
                let entry = ExposureIndexEntry {
                    sequence: frame.sequence,
                    byte_offset: offset,
                    family: frame.family.clone(),
                    octets: u64::try_from(line.len())
                        .map_err(|_| boundary("occurrence frame extent overflow"))?,
                };
                index.entries.push(entry);
                for event in frame.views.iter().map(|view| view.event) {
                    let key = (frame.family.clone(), event);
                    match index.by_alias.entry(key) {
                        std::collections::btree_map::Entry::Vacant(slot) => {
                            slot.insert(ExposureAliasResolution::Entry(entry_index));
                        }
                        std::collections::btree_map::Entry::Occupied(mut slot) => {
                            *slot.get_mut() = ExposureAliasResolution::Ambiguous;
                        }
                    }
                }
                index.next_sequence = index
                    .next_sequence
                    .checked_add(1)
                    .ok_or_else(|| boundary("exposure sequence exhausted"))?;
                index.next_offset = after;
                index.stats.index_entries = index.next_sequence;
                index.stats.index_scan_octets = index.next_offset - self.header_end;
            }
            Ok(())
        })();
        if result.is_err() {
            index.blocked_at = Some(index.next_sequence);
        }
        let restore = self.input.seek(SeekFrom::Start(saved));
        self.context_index = Some(index);
        match (result, restore) {
            (Err(error), _) => return Err(error),
            (Ok(()), Err(error)) => return Err(error.into()),
            (Ok(()), Ok(_)) => {}
        }
        Ok(())
    }

    fn read_indexed(
        &mut self,
        entry: &ExposureIndexEntry,
    ) -> Result<ExposureOccurrence, ExposureError> {
        let saved = self.input.stream_position()?;
        self.input.seek(SeekFrom::Start(entry.byte_offset))?;
        let mut line = Vec::new();
        let result = (|| {
            if self.input.read_until(b'\n', &mut line)? == 0 || !line.ends_with(b"\n") {
                return Err(boundary("indexed occurrence frame is incomplete"));
            }
            let frame: ExposureOccurrence = serde_json::from_slice(&line)?;
            if frame.sequence != entry.sequence
                || frame.family != entry.family
                || u64::try_from(line.len()).unwrap_or(u64::MAX) != entry.octets
            {
                return Err(boundary(
                    "indexed occurrence disagrees with source metadata",
                ));
            }
            frame.validate_with_sources(&self.manifest, &self.source_positions)?;
            Ok(frame)
        })();
        let restore = self.input.seek(SeekFrom::Start(saved));
        let frame = match (result, restore) {
            (Err(error), _) => return Err(error),
            (Ok(_), Err(error)) => return Err(error.into()),
            (Ok(frame), Ok(_)) => frame,
        };
        if let Some(index) = &mut self.context_index {
            index.stats.lookup_frames = index.stats.lookup_frames.saturating_add(1);
            index.stats.lookup_octets = index
                .stats
                .lookup_octets
                .saturating_add(u64::try_from(line.len()).unwrap_or(u64::MAX));
        }
        Ok(frame)
    }

    pub fn peek(&mut self) -> Result<Option<&ExposureOccurrence>, ExposureError> {
        if self.stopped {
            return Err(boundary(
                "reader stopped at an invalid frame; its prior cursor remains retained",
            ));
        }
        if self.pending.is_none() {
            let returned = self.read_next();
            match returned {
                Ok(pending) => self.pending = pending,
                Err(error) => {
                    self.stopped = true;
                    return Err(error);
                }
            }
        }
        Ok(self.pending.as_ref().map(|pending| &pending.frame))
    }

    fn read_next(&mut self) -> Result<Option<PendingOccurrence>, ExposureError> {
        let mut line = Vec::new();
        if self.input.read_until(b'\n', &mut line)? == 0 {
            return Ok(None);
        }
        if !line.ends_with(b"\n") {
            return Err(boundary("occurrence frame is incomplete"));
        }
        let frame: ExposureOccurrence = serde_json::from_slice(&line)?;
        if frame.sequence != self.cursor.next_sequence {
            return Err(boundary("occurrence sequence disagrees with cursor"));
        }
        frame.validate_with_sources(&self.manifest, &self.source_positions)?;
        let after = self.input.stream_position()?;
        Ok(Some(PendingOccurrence { frame, after }))
    }

    /// Commit only this cold delivery position. The eventual native consumer must pair this
    /// acknowledgment with its actual successful successor, not treat it as a learning verdict.
    pub fn acknowledge(&mut self, sequence: u64) -> Result<(), ExposureError> {
        let pending = self
            .pending
            .as_ref()
            .ok_or_else(|| boundary("no pending exposure"))?;
        if pending.frame.sequence != sequence {
            return Err(boundary("acknowledgment names another exposure"));
        }
        let next = sequence
            .checked_add(1)
            .ok_or_else(|| boundary("exposure sequence exhausted"))?;
        self.cursor.next_sequence = next;
        self.cursor.byte_offset = pending.after;
        self.pending = None;
        Ok(())
    }
}

/// The exporter normalizes aware timestamps to this fixed UTC chart; lexical order is then
/// chronological. The original provider timestamp is retained separately. No native clock is
/// inferred from this exterior data-partition receiver.
fn normalized_time(value: &str) -> bool {
    let b = value.as_bytes();
    if b.len() != 32 || &b[26..] != b"+00:00" {
        return false;
    }
    for (at, marker) in [
        (4, b'-'),
        (7, b'-'),
        (10, b'T'),
        (13, b':'),
        (16, b':'),
        (19, b'.'),
    ] {
        if b[at] != marker {
            return false;
        }
    }
    let number = |begin: usize, end: usize| -> Option<u32> {
        b[begin..end].iter().try_fold(0, |n, d| {
            d.is_ascii_digit().then(|| n * 10 + u32::from(d - b'0'))
        })
    };
    let (Some(year), Some(month), Some(day), Some(hour), Some(minute), Some(second), Some(_)) = (
        number(0, 4),
        number(5, 7),
        number(8, 10),
        number(11, 13),
        number(14, 16),
        number(17, 19),
        number(20, 26),
    ) else {
        return false;
    };
    if year == 0 || !(1..=12).contains(&month) || hour >= 24 || minute >= 60 || second >= 60 {
        return false;
    }
    let leap = year % 4 == 0 && (year % 100 != 0 || year % 400 == 0);
    let days = match month {
        2 => {
            if leap {
                29
            } else {
                28
            }
        }
        4 | 6 | 9 | 11 => 30,
        _ => 31,
    };
    (1..=days).contains(&day)
}

/// Exterior code lengths of the exposure stream an observer has seen, in bits. These are
/// observer readings like a timing or a byte count: nothing native reads them, and they never
/// enter a field, a comparison or a learning covector. Symbols are exterior codec ordinals.
#[derive(Clone, Debug, Default, Serialize)]
pub struct ExposureCodeLength {
    symbols: u64,
    order0: BTreeMap<usize, u64>,
    contexts: BTreeMap<Option<usize>, u64>,
    order1: BTreeMap<(Option<usize>, usize), u64>,
    last: Option<usize>,
}

impl ExposureCodeLength {
    /// Append symbols in the order the observer saw them. `context` is the order-1 context of
    /// the first symbol; `None` keeps the stream's own previous symbol.
    pub fn ingest(&mut self, symbols: &[usize], context: Option<Option<usize>>) {
        let mut previous = context.unwrap_or(self.last);
        for &symbol in symbols {
            self.symbols += 1;
            *self.order0.entry(symbol).or_default() += 1;
            *self.contexts.entry(previous).or_default() += 1;
            *self.order1.entry((previous, symbol)).or_default() += 1;
            previous = Some(symbol);
        }
        if !symbols.is_empty() {
            self.last = previous;
        }
    }

    pub fn symbols(&self) -> u64 {
        self.symbols
    }

    pub fn last(&self) -> Option<usize> {
        self.last
    }

    /// Static order-0 empirical code length `Σ_s c_s log2(N/c_s)` of the stream so far, bits.
    pub fn order0_bits(&self) -> f64 {
        let n = self.symbols as f64;
        self.order0
            .values()
            .map(|&c| c as f64 * (n / c as f64).log2())
            .sum()
    }

    /// Static order-1 empirical code length `Σ_(x,s) c_(x,s) log2(c_x/c_(x,s))`, bits.
    pub fn order1_bits(&self) -> f64 {
        self.order1
            .iter()
            .map(|((context, _), &c)| c as f64 * (self.contexts[context] as f64 / c as f64).log2())
            .sum()
    }

    /// Predictive code length of `symbols` under the counts seen before them, with add-one
    /// (Laplace) smoothing over an alphabet of `alphabet` classes, bits: `(order0, order1)`.
    /// Counts are not updated inside the target, as the producing face is fixed across it.
    pub fn predictive_bits(
        &self,
        symbols: &[usize],
        first_context: Option<usize>,
        alphabet: usize,
    ) -> (f64, f64) {
        let a = alphabet.max(1) as f64;
        let n = self.symbols as f64;
        let mut previous = first_context;
        let (mut zero, mut one) = (0.0, 0.0);
        for &symbol in symbols {
            let c0 = self.order0.get(&symbol).copied().unwrap_or(0) as f64;
            zero -= ((c0 + 1.0) / (n + a)).log2();
            let cx = self.contexts.get(&previous).copied().unwrap_or(0) as f64;
            let c1 = self.order1.get(&(previous, symbol)).copied().unwrap_or(0) as f64;
            one -= ((c1 + 1.0) / (cx + a)).log2();
            previous = Some(symbol);
        }
        (zero, one)
    }
}

/// The exterior request-side reading held by an observer until its comparison is observed.
#[derive(Clone, Debug, Serialize)]
pub struct ExteriorRequestMeasure {
    pub source_cells: usize,
    pub alphabet: usize,
    pub source_bits: f64,
    pub last_source_symbol: Option<usize>,
    pub committed: bool,
    pub source_clock_start: u64,
    pub source_clock_end: u64,
    pub request_seconds: f64,
    pub request_launches: u64,
    pub request_census: BTreeMap<String, i128>,
    pub checkpoint_octets_before: u64,
    pub checkpoint_octets_after: u64,
}

/// Exterior observer of an exposure run: the stream's empirical code lengths, the cumulative
/// source code length and each outstanding request's measure. It is not session state and is
/// never checkpointed; a resumed run starts a new observer.
#[derive(Clone, Debug, Default, Serialize)]
pub struct ExteriorReturnObserver {
    pub stream: ExposureCodeLength,
    pub source_bits_total: f64,
    pub source_cells_total: u64,
    pub committed_source_steps: u64,
    pub requests: BTreeMap<u64, ExteriorRequestMeasure>,
    pub returns: u64,
}
