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
        let mut common: Option<BTreeSet<ExposureFamily>> = None;
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
        Ok(parents.into_iter().next())
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
    pending: Option<PendingOccurrence>,
    stopped: bool,
    source_positions: BTreeMap<u64, usize>,
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
            pending: None,
            stopped: false,
            source_positions,
        })
    }

    pub fn manifest(&self) -> &ExposureManifest {
        &self.manifest
    }
    pub fn cursor(&self) -> ExposureCursor {
        self.cursor.clone()
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

#[cfg(test)]
mod tests;
