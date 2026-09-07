//! Consume a bounded AC0 exposure through one 16-port native constitutive field.
//!
//! This is a material/current study, not text emission or a language-quality evaluation. Raw
//! message strings never enter the report or stdout. The private exact excitation witness does
//! reconstruct their octets. The field owner is kept across every selected
//! development family and every visible text part; only the actual returned field emission links
//! adjacent UTF-8 octets within one part.

use holonic_engine::{
    native_ecology::constitutive_fibre::{
        ConstitutiveFibreError, NativeConstitutiveField, NativeFieldEmission,
        NativeFieldInternalCurrent, NativeFieldInternalCurrentBall,
        NativeFieldJunctionRepresentation, NativeFieldLineage, NativeFieldOccurrence,
        NativeFieldReceiverStatus,
    },
    resident_section::ResidentSectionRest,
};
use holonics_hna::{
    alpha::{
        exposure::{
            ExposureLink, ExposureOccurrence, ExposurePart, ExposurePartition, ExposureReader,
        },
        material::{
            with_enclosed_octet_field, with_octet_field, with_paired_octet_field,
            AlphaMaterialError, OctetExcitation, OCTET_INPUT_CHANNELS,
        },
    },
    publish_new,
};
use serde::Serialize;
use std::{
    io::{self, Write},
    path::{Path, PathBuf},
    time::Instant,
};

#[derive(Clone, Debug, Serialize)]
struct PartCoordinate {
    sequence: u64,
    event: u64,
    source: u64,
    provider: String,
    record_group: String,
    record_number: u64,
    byte_start: u64,
    byte_end: u64,
    part_ordinal: u64,
    pointer: String,
    kind: String,
}

#[derive(Clone, Debug, Serialize)]
struct FailureCoordinate {
    kind: String,
    error: String,
    sequence: Option<u64>,
    event: Option<u64>,
    source: Option<u64>,
    record_number: Option<u64>,
    byte_start: Option<u64>,
    byte_end: Option<u64>,
    part_ordinal: Option<u64>,
    pointer: Option<String>,
    octet_index: Option<u64>,
    octet: Option<u8>,
    native_occurrences: u64,
}

#[derive(Clone, Debug, Serialize)]
struct SectionObserver {
    rows: usize,
    width: usize,
    grain: u32,
    bound_octaves: u32,
    intervals: Vec<(i64, i64)>,
}

impl From<ResidentSectionRest> for SectionObserver {
    fn from(rest: ResidentSectionRest) -> Self {
        Self {
            rows: rest.rows,
            width: rest.width,
            grain: rest.grain.0,
            bound_octaves: rest.bound_octaves,
            intervals: rest.intervals,
        }
    }
}

#[derive(Debug, Serialize)]
struct BodyObserver {
    occurrence_count: usize,
    lineage: Vec<NativeFieldLineage>,
    last_source: Option<SectionObserver>,
    requested_sources: Vec<(usize, SectionObserver)>,
    held: Option<SectionObserver>,
    relation: Option<SectionObserver>,
    pending_lineage: Option<NativeFieldLineage>,
    observer_error: Option<String>,
    junction_covariance: Option<SectionObserver>,
    junction_history: Vec<(usize, SectionObserver)>,
    internal_currents: Option<Vec<NativeFieldInternalCurrent>>,
    junction_representation: Option<NativeFieldJunctionRepresentation>,
    internal_current_enclosures: Option<Vec<NativeFieldInternalCurrentBall>>,
}

#[derive(Clone, Debug, Serialize)]
struct UnboundSourceRelation {
    sequence: u64,
    event: u64,
    relation: ExposureLink,
}

#[derive(Clone, Debug, Serialize)]
struct PartNativeRange {
    sequence: u64,
    part_ordinal: u64,
    native_from: usize,
    native_until: usize,
    source_octets: usize,
    complete: bool,
}

#[derive(Clone, Debug, Serialize)]
struct VerticalFormation {
    sequence: u64,
    part_ordinal: u64,
    octet_index: usize,
    native_occurrence: usize,
    formed_pivot: usize,
    source_occurrence: Option<usize>,
    paired_source: Option<SectionObserver>,
    relation_after: SectionObserver,
}

#[derive(Debug, Serialize)]
struct Report {
    schema: &'static str,
    profile: &'static str,
    observation_mode: &'static str,
    exposure_path: String,
    families_aperture: u64,
    frames_seen: u64,
    development_families_acknowledged: u64,
    nondevelopment_families_skipped: u64,
    parts_presented: u64,
    octets_presented: u64,
    native_occurrences: u64,
    formed_pivots: u64,
    unique_readings: u64,
    outside_domain_readings: u64,
    plural_readings: u64,
    exact_failure_count: u64,
    last_cursor_sequence: u64,
    last_cursor_byte_offset: u64,
    source_part_coordinates: Vec<PartCoordinate>,
    part_native_ranges: Vec<PartNativeRange>,
    unbound_source_relations: Vec<UnboundSourceRelation>,
    opaque_parts: Vec<(u64, u64)>,
    first_vertical_formation: Option<VerticalFormation>,
    final_rank: usize,
    native_census_before_observers: Option<holonic_engine::resident_section::TransferCensus>,
    body: Option<BodyObserver>,
    failure: Option<FailureCoordinate>,
    material_wall_seconds: f64,
    observer_wall_seconds: f64,
}

impl Report {
    fn new(exposure_path: &Path, families_aperture: u64, paired: bool) -> Self {
        Self {
            schema: "holonics.athena-alpha-material-study.v1",
            profile: if paired {
                "matched-unit-octet-field-with-paired-junction"
            } else {
                "matched-unit-octet-excitation-native-field"
            },
            observation_mode: "per-occurrence",
            exposure_path: exposure_path.display().to_string(),
            families_aperture,
            frames_seen: 0,
            development_families_acknowledged: 0,
            nondevelopment_families_skipped: 0,
            parts_presented: 0,
            octets_presented: 0,
            native_occurrences: 0,
            formed_pivots: 0,
            unique_readings: 0,
            outside_domain_readings: 0,
            plural_readings: 0,
            exact_failure_count: 0,
            last_cursor_sequence: 0,
            last_cursor_byte_offset: 0,
            source_part_coordinates: Vec::new(),
            part_native_ranges: Vec::new(),
            unbound_source_relations: Vec::new(),
            opaque_parts: Vec::new(),
            first_vertical_formation: None,
            final_rank: 0,
            native_census_before_observers: None,
            body: None,
            failure: None,
            material_wall_seconds: 0.0,
            observer_wall_seconds: 0.0,
        }
    }
}

fn record_coordinates(report: &mut Report, frame: &ExposureOccurrence) {
    for view in &frame.views {
        for relation in &view.links {
            report.unbound_source_relations.push(UnboundSourceRelation {
                sequence: frame.sequence,
                event: view.event,
                relation: relation.clone(),
            });
        }
        for part in &view.visible_parts {
            report.source_part_coordinates.push(PartCoordinate {
                sequence: frame.sequence,
                event: view.event,
                source: view.source,
                provider: view.provider.clone(),
                record_group: frame.family.record_group.clone(),
                record_number: view.record.number,
                byte_start: view.record.byte_start,
                byte_end: view.record.byte_end,
                part_ordinal: part.ordinal,
                pointer: part.pointer.clone(),
                kind: part.kind.clone(),
            });
        }
    }
}

fn coordinate_for(
    frame: &ExposureOccurrence,
    part: &ExposurePart,
    octet_index: usize,
    kind: &str,
    error: String,
    native_occurrences: u64,
) -> FailureCoordinate {
    let view = frame.views.first();
    FailureCoordinate {
        kind: kind.to_owned(),
        error,
        sequence: Some(frame.sequence),
        event: view.map(|value| value.event),
        source: view.map(|value| value.source),
        record_number: view.map(|value| value.record.number),
        byte_start: view.map(|value| value.record.byte_start),
        byte_end: view.map(|value| value.record.byte_end),
        part_ordinal: Some(part.ordinal),
        pointer: Some(part.pointer.clone()),
        octet_index: Some(octet_index as u64),
        octet: part
            .text
            .as_ref()
            .and_then(|text| text.as_bytes().get(octet_index).copied()),
        native_occurrences,
    }
}

fn record_reading(report: &mut Report, reading: NativeFieldReceiverStatus) {
    match reading {
        NativeFieldReceiverStatus::Unique => report.unique_readings += 1,
        NativeFieldReceiverStatus::OutsideDomain => report.outside_domain_readings += 1,
        NativeFieldReceiverStatus::Plural => report.plural_readings += 1,
    }
}

fn observe_body(field: &NativeConstitutiveField<'_>, inspect_sources: &[usize]) -> BodyObserver {
    let occurrence_count = field.occurrence_count();
    let mut errors = Vec::new();
    let last_source = occurrence_count.checked_sub(1).and_then(|last| {
        field
            .inspect_source(last)
            .map(SectionObserver::from)
            .map_err(|error| errors.push(error.to_string()))
            .ok()
    });
    let held = field
        .inspect_held()
        .map(SectionObserver::from)
        .map_err(|error| errors.push(error.to_string()))
        .ok();
    let relation = field
        .inspect_relation()
        .map(SectionObserver::from)
        .map_err(|error| errors.push(error.to_string()))
        .ok();
    let requested_sources = inspect_sources
        .iter()
        .filter_map(|&at| {
            field
                .inspect_source(at)
                .map(|section| (at, section.into()))
                .map_err(|error| errors.push(format!("source {at}: {error}")))
                .ok()
        })
        .collect();
    let junction_covariance = field
        .inspect_junction_covariance()
        .map_err(|error| errors.push(error.to_string()))
        .ok()
        .flatten()
        .map(Into::into);
    let mut junction_history = Vec::new();
    if field.has_paired_junction() {
        for at in 0..occurrence_count {
            match field.inspect_junction(at) {
                Ok(Some(section)) => junction_history.push((at, section.into())),
                Ok(None) => errors.push(format!("junction history missing at {at}")),
                Err(error) => errors.push(error.to_string()),
            }
        }
    }
    let junction_representation = field.junction_representation();
    let internal_currents = if matches!(
        junction_representation,
        Some(NativeFieldJunctionRepresentation::EnclosedDyadic { .. })
    ) {
        None
    } else {
        field
            .inspect_internal_currents()
            .map_err(|error| errors.push(error.to_string()))
            .ok()
            .flatten()
    };
    let internal_current_enclosures = field
        .inspect_internal_current_enclosures()
        .map_err(|error| errors.push(error.to_string()))
        .ok()
        .flatten();
    BodyObserver {
        occurrence_count,
        lineage: (0..occurrence_count)
            .filter_map(|i| field.lineage(i).cloned())
            .collect(),
        pending_lineage: field.pending_lineage().cloned(),
        last_source,
        requested_sources,
        held,
        relation,
        observer_error: (!errors.is_empty()).then(|| errors.join("; ")),
        junction_covariance,
        junction_history,
        internal_currents,
        junction_representation,
        internal_current_enclosures,
    }
}

fn capture_failure(
    report: &mut Report,
    frame: &ExposureOccurrence,
    part: &ExposurePart,
    octet_index: usize,
    error: AlphaMaterialError,
    native_occurrences: u64,
) {
    let kind = match &error {
        AlphaMaterialError::Native(ConstitutiveFibreError::Arithmetic(_)) => {
            "native-arithmetic-refusal"
        }
        AlphaMaterialError::Native(_) => "native-refusal",
        AlphaMaterialError::Excitation(_) => "excitation-refusal",
        AlphaMaterialError::Exposure(_) => "exposure-refusal",
        AlphaMaterialError::Apparatus(_) => "apparatus-refusal",
    };
    report.exact_failure_count += 1;
    report.failure = Some(coordinate_for(
        frame,
        part,
        octet_index,
        kind,
        error.to_string(),
        native_occurrences,
    ));
}

fn process_exposure(
    reader: &mut ExposureReader,
    field: &mut NativeConstitutiveField<'_>,
    families_aperture: u64,
    report: &mut Report,
    resident: bool,
) -> Result<(), AlphaMaterialError> {
    while report.development_families_acknowledged < families_aperture {
        let frame = reader
            .peek()
            .map_err(|error| AlphaMaterialError::Exposure(error.to_string()))?;
        let Some(frame) = frame else {
            break;
        };
        report.frames_seen += 1;
        record_coordinates(report, frame);
        if frame.partition != ExposurePartition::Development {
            let sequence = frame.sequence;
            reader
                .acknowledge(sequence)
                .map_err(|error| AlphaMaterialError::Exposure(error.to_string()))?;
            report.nondevelopment_families_skipped += 1;
            continue;
        }
        let parts = frame
            .development_parts()
            .map_err(|error| AlphaMaterialError::Exposure(error.to_string()))?;
        for part in parts {
            if !matches!(
                part.kind.as_str(),
                "human-text" | "human-command" | "agent-text"
            ) {
                report.opaque_parts.push((frame.sequence, part.ordinal));
                continue;
            }
            let Some(text) = part.text.as_ref() else {
                report.opaque_parts.push((frame.sequence, part.ordinal));
                continue;
            };
            let native_from = field.occurrence_count();
            report.parts_presented += 1;
            let mut previous: Option<NativeFieldEmission> = None;
            for (octet_index, octet) in text.as_bytes().iter().copied().enumerate() {
                let excitation = OctetExcitation::from_octet(octet);
                let incoming = excitation.inputs();
                debug_assert_eq!(incoming.len(), OCTET_INPUT_CHANNELS);
                let mut occurrence = match previous.take() {
                    Some(source) => NativeFieldOccurrence::through(source, incoming),
                    None => NativeFieldOccurrence::entering(incoming),
                };
                let advanced = if resident {
                    field
                        .advance_resident(&mut occurrence)
                        .map(|step| step.source)
                } else {
                    field.advance_status(&mut occurrence).and_then(|step| {
                        if report.first_vertical_formation.is_none() {
                            if let Some(pivot) =
                                step.formed_pivot.filter(|p| *p >= 4 * field.nodes())
                            {
                                report.first_vertical_formation = Some(VerticalFormation {
                                    sequence: frame.sequence,
                                    part_ordinal: part.ordinal,
                                    octet_index,
                                    native_occurrence: step.lineage.occurrence,
                                    formed_pivot: pivot,
                                    source_occurrence: step.lineage.received_from,
                                    paired_source: step
                                        .lineage
                                        .received_from
                                        .map(|i| field.inspect_source(i).map(SectionObserver::from))
                                        .transpose()?,
                                    relation_after: field.inspect_relation()?.into(),
                                });
                            }
                        }
                        report.final_rank = step.successor_rank;
                        report.formed_pivots += u64::from(step.formed_pivot.is_some());
                        record_reading(report, step.receiver);
                        Ok(step.source)
                    })
                };
                let source = match advanced {
                    Ok(source) => source,
                    Err(error) => {
                        capture_failure(
                            report,
                            &frame,
                            part,
                            octet_index,
                            AlphaMaterialError::Native(error),
                            field.occurrence_count() as u64,
                        );
                        report.part_native_ranges.push(PartNativeRange {
                            sequence: frame.sequence,
                            part_ordinal: part.ordinal,
                            native_from,
                            native_until: field.occurrence_count(),
                            source_octets: text.len(),
                            complete: false,
                        });
                        return Ok(());
                    }
                };
                previous = Some(source);
                report.octets_presented += 1;
                report.native_occurrences += 1;
            }
            // A part boundary is an actual source boundary; no emission is linked into the next part.
            drop(previous);
            report.part_native_ranges.push(PartNativeRange {
                sequence: frame.sequence,
                part_ordinal: part.ordinal,
                native_from,
                native_until: field.occurrence_count(),
                source_octets: text.len(),
                complete: true,
            });
        }
        let sequence = frame.sequence;
        reader
            .acknowledge(sequence)
            .map_err(|error| AlphaMaterialError::Exposure(error.to_string()))?;
        report.development_families_acknowledged += 1;
    }
    Ok(())
}

fn usage() -> &'static str {
    "usage: alpha_material EXPOSURE --families N --report NEW.json [--inspect-source N ...] [--paired-junction | --enclosed-junction FRACTIONAL_BITS] [--resident]"
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = std::env::args().skip(1);
    let source = PathBuf::from(args.next().ok_or(usage())?);
    let mut families = None;
    let mut report_path = None;
    let mut inspect_sources = Vec::new();
    let mut paired = false;
    let mut enclosed = None;
    let mut resident = false;
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--resident" => resident = true,
            "--paired-junction" => paired = true,
            "--enclosed-junction" => {
                enclosed = Some(
                    args.next()
                        .ok_or("missing fractional bits")?
                        .parse::<u32>()?,
                )
            }
            "--families" => {
                families = Some(
                    args.next()
                        .ok_or("missing --families value")?
                        .parse::<u64>()?,
                )
            }
            "--report" => {
                report_path = Some(PathBuf::from(args.next().ok_or("missing --report path")?))
            }
            "--inspect-source" => inspect_sources.push(
                args.next()
                    .ok_or("missing --inspect-source value")?
                    .parse::<usize>()?,
            ),
            _ => return Err(format!("unknown option {arg}; {}", usage()).into()),
        }
    }
    let families = families
        .filter(|value| *value > 0)
        .ok_or("--families must be a positive explicit aperture")?;
    let report_path = report_path.ok_or("--report is required for the private report")?;
    if paired && enclosed.is_some() {
        return Err("choose one declared junction representation".into());
    }
    let mut reader = ExposureReader::open(&source)?;
    let mut report = Report::new(&source, families, paired);
    if enclosed.is_some() {
        report.profile = "matched-unit-octet-field-with-enclosed-junction";
    }
    if resident {
        report.observation_mode = "terminal";
    }
    let operation = |field: &mut NativeConstitutiveField<'_>| {
        let start = Instant::now();
        let result = process_exposure(&mut reader, field, families, &mut report, resident);
        report.material_wall_seconds = start.elapsed().as_secs_f64();
        report.native_census_before_observers = Some(field.census());
        let start = Instant::now();
        let status_result = if resident {
            // Read immutable historical receipts after the material run. No intermediate
            // relation snapshot is claimed; first_vertical_formation is deliberately absent.
            (0..field.occurrence_count()).try_for_each(|at| {
                let status = field.inspect_occurrence_status(at)?;
                report.final_rank = status.successor_rank;
                report.formed_pivots += u64::from(status.formed_pivot.is_some());
                record_reading(&mut report, status.receiver);
                Ok::<_, ConstitutiveFibreError>(())
            })
        } else {
            Ok(())
        };
        report.body = Some(observe_body(field, &inspect_sources));
        report.observer_wall_seconds = start.elapsed().as_secs_f64();
        result.and(status_result.map_err(AlphaMaterialError::Native))
    };
    let native_result = if let Some(grain) = enclosed {
        with_enclosed_octet_field(grain, operation)
    } else if paired {
        with_paired_octet_field(operation)
    } else {
        with_octet_field(operation)
    };
    if let Err(error) = &native_result {
        if report.failure.is_none() {
            report.failure = Some(FailureCoordinate {
                kind: "application-refusal".to_owned(),
                error: error.to_string(),
                sequence: None,
                event: None,
                source: None,
                record_number: None,
                byte_start: None,
                byte_end: None,
                part_ordinal: None,
                pointer: None,
                octet_index: None,
                octet: None,
                native_occurrences: report.native_occurrences,
            });
        }
    }
    let cursor = reader.cursor();
    report.last_cursor_sequence = cursor.next_sequence;
    report.last_cursor_byte_offset = cursor.byte_offset;
    let publication_start = Instant::now();
    publish_new(&report_path, |file| {
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            file.set_permissions(std::fs::Permissions::from_mode(0o600))?;
        }
        let mut writer = io::BufWriter::new(file);
        serde_json::to_writer_pretty(&mut writer, &report).map_err(io::Error::other)?;
        writer.flush()
    })?;
    let publication_seconds = publication_start.elapsed().as_secs_f64();
    println!(
        "{}",
        serde_json::json!({
            "schema": report.schema,
            "profile": report.profile,
            "observation_mode": report.observation_mode,
            "families_aperture": report.families_aperture,
            "development_families_acknowledged": report.development_families_acknowledged,
            "parts_presented": report.parts_presented,
            "octets_presented": report.octets_presented,
            "native_occurrences": report.native_occurrences,
            "formed_pivots": report.formed_pivots,
            "unique_readings": report.unique_readings,
            "outside_domain_readings": report.outside_domain_readings,
            "plural_readings": report.plural_readings,
            "exact_failure_count": report.exact_failure_count,
            "final_rank":report.final_rank,
            "unbound_source_relations":report.unbound_source_relations.len(),
            "record_context_is_operative":false,
            "learned_text_emitted":false,
            "report_published": true,
            "material_wall_seconds":report.material_wall_seconds,
            "observer_wall_seconds":report.observer_wall_seconds,
            "publication_wall_seconds":publication_seconds
        })
    );
    if let Some(failure) = &report.failure {
        return Err(failure.error.clone().into());
    }
    if let Err(error) = native_result {
        return Err(error.to_string().into());
    }
    if let Some(error) = report
        .body
        .as_ref()
        .and_then(|body| body.observer_error.as_ref())
    {
        return Err(format!("private native witness is incomplete: {error}").into());
    }
    Ok(())
}
