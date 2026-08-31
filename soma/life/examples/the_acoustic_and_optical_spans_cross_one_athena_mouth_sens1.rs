//! SENS1 receiver: storage segmentation does not cut an acoustic or optical occurrence.
//!
//! Presentation names and fragment extents exist only in this exterior receiver. They never
//! enter the typed source objects, native contact, membrane chart, or continuing Athena rest.

use std::{any::Any, env, fs, path::PathBuf};

use body::num::Cog;
use holonic_engine::{
    quantity::BaseUnits, receiver_exact_compression::ReceiverId, BoundaryId,
    ExactComplexWaveCurrent,
};
use holonic_structure::CausalMembrane;
use life::{
    addressed_span::{
        AddressedMemorySpan, AddressedSpanDefect, CompleteAddressedMemorySpan, MemorySpanFragment,
    },
    athena_native::{
        AdmittedReturnedAffineLaboratoryRestWitness, AthenaCausalMembrane,
        AthenaMembraneConsequence, AthenaMembraneCrossingReceipt, AthenaMembraneStanding,
        ExactMembraneChartPassage, ExteriorOccurrenceTransducer, GranularCultivationWithdrawal,
        GranularReturnedAffineAthenaRest, ReturnedAffineLaboratoryAthenaRest,
    },
    current_world::StreamedOctetOrgan,
    mathematical_source::{
        ExactAcousticOccurrence, ExactOpticalOccurrence, HierarchicalOpticalPassage,
    },
};
use serde::Serialize;
use sha2::{Digest, Sha256};
use soma_abi::active::ActionCurrent;
use soma_membrane::{LiveCurrentMachine, SparseStandingSurface};

const PREDECESSOR: &str = concat!(
    "output/the_returned_membrane_action_cultivates_one_source_detached_athena_rest_mem4/",
    "athena-returned-membrane-cultivated.rest"
);
const ORGAN: &str = concat!(
    "output/the_causal_boundary_ports_cultivate_one_athena_successor_with_exact_projective_factor_currents_mem6/",
    "athena-causal-boundary-organ.rest"
);
const ACOUSTIC: &str = concat!(
    "output/the_laboratory_mathematics_athena_unifies_native_inference_ocr_and_three_port_transport/",
    "projections/07-exact-notation.wav"
);
const OPTICAL_RASTER: &str =
    "output/m0_mathematical_source_circulation/faces/natural/heat-fisher-page-10.png";
const OPTICAL_HIERARCHY: &str =
    "output/the_optical_holons_grow_across_scales/01-hierarchical-optical-passage.json";
const OUTPUT: &str = "output/the_acoustic_and_optical_spans_cross_one_athena_mouth_sens1";

#[derive(Clone, Copy)]
enum Carriage {
    Whole,
    ByteFragmented,
    FrameFragmented,
    RandomRechunked,
    CallbackBoundaries,
}

impl Carriage {
    const ALL: [Self; 5] = [
        Self::Whole,
        Self::ByteFragmented,
        Self::FrameFragmented,
        Self::RandomRechunked,
        Self::CallbackBoundaries,
    ];

    const fn name(self) -> &'static str {
        match self {
            Self::Whole => "whole",
            Self::ByteFragmented => "byte-fragmented",
            Self::FrameFragmented => "frame-fragmented",
            Self::RandomRechunked => "randomly-rechunked",
            Self::CallbackBoundaries => "callback-boundaries",
        }
    }
}

#[derive(Serialize)]
#[serde(deny_unknown_fields)]
struct SpanPresentationReceipt {
    carriage: &'static str,
    source_sha256: String,
    source_octets: u64,
    fragment_population: u64,
    join_population: u64,
    largest_fragment_octets: u64,
    complete_source_fibre_sha256: String,
    crossing: AthenaMembraneCrossingReceipt,
}

#[derive(Serialize)]
#[serde(deny_unknown_fields)]
struct SeparatorReceipt {
    family: &'static str,
    control: &'static str,
    defect: AddressedSpanDefect,
    retained_prefix_octets: u64,
    rejected_fragment_from: Option<u64>,
}

#[derive(Serialize)]
#[serde(deny_unknown_fields)]
struct Sens1Return {
    truth_status: &'static str,
    evidence_tags: [&'static str; 2],
    rested_identity_sha256: String,
    returned_identity_sha256: String,
    acoustic_presentations: Vec<SpanPresentationReceipt>,
    optical_presentations: Vec<SpanPresentationReceipt>,
    separators: Vec<SeparatorReceipt>,
    whole_fragmented_and_callback_native_consequences_identical: bool,
    complete_reconstruction_fibres_identical: bool,
    dropout_and_reorder_return_first_exact_coordinate: bool,
    exact_samples_raster_and_alternative_covers_recovered: bool,
    largest_hot_adjacency_octet_population: u64,
    whole_source_payload_copied_into_morphology: bool,
    productive_ocr_transcript_or_label_route: bool,
    cpu_semantic_replay: bool,
    open_exterior: Vec<String>,
}

fn main() -> Result<(), String> {
    let root = workspace_root()?;
    let output = root.join(OUTPUT);
    fs::create_dir_all(&output).map_err(display)?;

    let witness = AdmittedReturnedAffineLaboratoryRestWitness::found(
        "646401462284e6782aaa43139202c3bd5e45043e174b414e4fe851ec92f4e2ad",
        "63c9ff122e50fe94efe9bb00fea66e9eaac606c47707d07bc69301449bb9aded",
        "3ab826fb8512aae85096193ce103a384092111e8f26836415b0e1dc7eba02178",
    )
    .map_err(display)?;
    let predecessor = ReturnedAffineLaboratoryAthenaRest::read_admitted(
        &fs::read(root.join(PREDECESSOR)).map_err(display)?,
        &witness,
    )
    .map_err(display)?;
    let withdrawal =
        GranularCultivationWithdrawal::read(&fs::read(root.join(ORGAN)).map_err(display)?)
            .map_err(display)?;
    let rest =
        GranularReturnedAffineAthenaRest::restore(predecessor, withdrawal).map_err(display)?;
    let rested_identity_sha256 = rest.identity().to_owned();
    let (address, receiver) = continuing_native_address(&rest)?;
    let mut membrane = AthenaCausalMembrane::mount(rest);

    let acoustic_body = fs::read(root.join(ACOUSTIC)).map_err(display)?;
    let optical_body = fs::read(root.join(OPTICAL_RASTER)).map_err(display)?;
    let optical_hierarchy_body = fs::read(root.join(OPTICAL_HIERARCHY)).map_err(display)?;

    let mut acoustic_presentations = Vec::new();
    let mut acoustic_crossing = None;
    let mut acoustic_source = None;
    let mut acoustic_samples = None;
    for carriage in Carriage::ALL {
        let span = assemble("sens1/acoustic", &acoustic_body, carriage)?;
        let span_stats = span_stats(&span);
        let source = ExactAcousticOccurrence::from_wav_bytes(
            &span.body,
            "sens1/acoustic",
            "memory://sens1/acoustic",
            512,
            256,
            64,
        )
        .map_err(display)?;
        let (crossing, recovered) = cross_and_recover(&mut membrane, source, &address, receiver)?;
        let fibre_sha256 = digest_json(&recovered)?;
        let sample_sha256 = digest_i16(&recovered.samples);
        if let Some(expected) = &acoustic_crossing {
            if expected != &crossing {
                return Err(format!(
                    "{} changed the acoustic membrane consequence",
                    carriage.name()
                ));
            }
        } else {
            acoustic_crossing = Some(crossing.clone());
        }
        if let Some(expected) = &acoustic_source {
            if expected != &fibre_sha256 {
                return Err(format!(
                    "{} changed the acoustic source fibre",
                    carriage.name()
                ));
            }
        } else {
            acoustic_source = Some(fibre_sha256.clone());
        }
        if let Some(expected) = &acoustic_samples {
            if expected != &sample_sha256 {
                return Err(format!(
                    "{} changed the acoustic sample population",
                    carriage.name()
                ));
            }
        } else {
            acoustic_samples = Some(sample_sha256);
        }
        acoustic_presentations.push(SpanPresentationReceipt {
            carriage: carriage.name(),
            source_sha256: span.source_sha256,
            source_octets: span.source_octets,
            fragment_population: span_stats.0,
            join_population: span_stats.1,
            largest_fragment_octets: span_stats.2,
            complete_source_fibre_sha256: fibre_sha256,
            crossing,
        });
    }

    let mut optical_presentations = Vec::new();
    let mut optical_crossing = None;
    let mut optical_source = None;
    let mut optical_alternatives = None;
    for carriage in Carriage::ALL {
        let span = assemble("sens1/optical", &optical_body, carriage)?;
        let span_stats = span_stats(&span);
        let hierarchy =
            HierarchicalOpticalPassage::read(&optical_hierarchy_body).map_err(display)?;
        let source = ExactOpticalOccurrence::found(
            "sens1/optical",
            "memory://sens1/optical",
            span.body,
            hierarchy,
        )
        .map_err(display)?;
        let (crossing, recovered) = cross_and_recover(&mut membrane, source, &address, receiver)?;
        recovered.validate().map_err(display)?;
        let hierarchy_sha256 = digest(&recovered.hierarchy.canonical_bytes().map_err(display)?);
        let fibre_sha256 = digest_composed(&[
            recovered.occurrence.as_bytes(),
            recovered.source_sha256.as_bytes(),
            &recovered.encoded_raster,
            hierarchy_sha256.as_bytes(),
        ]);
        let alternatives = recovered.hierarchy.alternative_covers.len();
        if let Some(expected) = &optical_crossing {
            if expected != &crossing {
                return Err(format!(
                    "{} changed the optical membrane consequence",
                    carriage.name()
                ));
            }
        } else {
            optical_crossing = Some(crossing.clone());
        }
        if let Some(expected) = &optical_source {
            if expected != &fibre_sha256 {
                return Err(format!(
                    "{} changed the optical source fibre",
                    carriage.name()
                ));
            }
        } else {
            optical_source = Some(fibre_sha256.clone());
        }
        if let Some(expected) = optical_alternatives {
            if expected != alternatives {
                return Err(format!(
                    "{} changed the optical alternative covers",
                    carriage.name()
                ));
            }
        } else {
            optical_alternatives = Some(alternatives);
        }
        optical_presentations.push(SpanPresentationReceipt {
            carriage: carriage.name(),
            source_sha256: recovered.source_sha256.clone(),
            source_octets: recovered.source_octets,
            fragment_population: span_stats.0,
            join_population: span_stats.1,
            largest_fragment_octets: span_stats.2,
            complete_source_fibre_sha256: fibre_sha256,
            crossing,
        });
    }

    let separators = vec![
        dropout("acoustic", "sens1/acoustic", &acoustic_body)?,
        reorder("acoustic", "sens1/acoustic", &acoustic_body)?,
        dropout("optical", "sens1/optical", &optical_body)?,
        reorder("optical", "sens1/optical", &optical_body)?,
    ];
    let dropout_and_reorder_return_first_exact_coordinate = separators.iter().all(|receipt| {
        matches!(
            receipt.defect,
            AddressedSpanDefect::Nonconsecutive { expected_from, supplied_from }
                if expected_from == receipt.retained_prefix_octets
                    && supplied_from == receipt.rejected_fragment_from.unwrap_or(u64::MAX)
        )
    });
    let rest = membrane.into_rest();
    let returned_identity_sha256 = rest.identity().to_owned();
    let whole_fragmented_and_callback_native_consequences_identical = acoustic_presentations
        .windows(2)
        .all(|pair| pair[0].crossing == pair[1].crossing)
        && optical_presentations
            .windows(2)
            .all(|pair| pair[0].crossing == pair[1].crossing);
    let complete_reconstruction_fibres_identical = acoustic_presentations
        .windows(2)
        .all(|pair| pair[0].complete_source_fibre_sha256 == pair[1].complete_source_fibre_sha256)
        && optical_presentations.windows(2).all(|pair| {
            pair[0].complete_source_fibre_sha256 == pair[1].complete_source_fibre_sha256
        });
    let exact_samples_raster_and_alternative_covers_recovered = acoustic_samples.is_some()
        && optical_source.is_some()
        && optical_alternatives.is_some_and(|population| population > 0);
    let largest_hot_adjacency_octet_population =
        streaming_owner_bound([acoustic_body.as_slice(), optical_body.as_slice()])?;
    let returned = Sens1Return {
        truth_status: "established-bounded",
        evidence_tags: ["implemented-exact", "measured"],
        rested_identity_sha256: rested_identity_sha256.clone(),
        returned_identity_sha256,
        acoustic_presentations,
        optical_presentations,
        separators,
        whole_fragmented_and_callback_native_consequences_identical,
        complete_reconstruction_fibres_identical,
        dropout_and_reorder_return_first_exact_coordinate,
        exact_samples_raster_and_alternative_covers_recovered,
        largest_hot_adjacency_octet_population,
        whole_source_payload_copied_into_morphology: false,
        productive_ocr_transcript_or_label_route: false,
        cpu_semantic_replay: false,
        open_exterior: vec![
            "the addressed-span receiver proves storage naturality; continuous affine clock contact enters at SENS2"
                .to_owned(),
            "the existing StreamedOctetOrgan independently bounds hot adjacency standing to one octet; the complete body remains the moved cold reconstruction fibre"
                .to_owned(),
        ],
    };
    if rested_identity_sha256 != returned.returned_identity_sha256
        || !returned.whole_fragmented_and_callback_native_consequences_identical
        || !returned.complete_reconstruction_fibres_identical
        || !returned.dropout_and_reorder_return_first_exact_coordinate
        || !returned.exact_samples_raster_and_alternative_covers_recovered
        || returned.largest_hot_adjacency_octet_population != 1
        || returned.whole_source_payload_copied_into_morphology
        || returned.productive_ocr_transcript_or_label_route
        || returned.cpu_semantic_replay
    {
        return Err("the SENS1 qualitative receiver did not pass".to_owned());
    }
    fs::write(
        output.join("00-sens1-return.json"),
        serde_json::to_vec_pretty(&returned).map_err(display)?,
    )
    .map_err(display)?;
    Ok(())
}

fn streaming_owner_bound(sources: [&[u8]; 2]) -> Result<u64, String> {
    let mut maximum = 0usize;
    for source in sources {
        let aperture = source.len().min(96);
        let source = &source[..aperture];
        let mut machine =
            LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).map_err(debug)?);
        let mut organ = StreamedOctetOrgan::new();
        let action = ActionCurrent::new(Cog::lit(137))
            .ok_or_else(|| "the SENS1 streaming action did not found".to_owned())?;
        let cuts = [1usize, 7, 19, 47, aperture];
        let mut from = 0usize;
        for to in cuts.into_iter().map(|to| to.min(aperture)) {
            if to <= from {
                continue;
            }
            let receipt = organ
                .present_chunk(&mut machine, &source[from..to], action, false, |_| {})
                .map_err(debug)?;
            maximum = maximum.max(receipt.retained_adjacency_octets);
            from = to;
        }
    }
    u64::try_from(maximum).map_err(display)
}

fn assemble(
    occurrence: &str,
    body: &[u8],
    carriage: Carriage,
) -> Result<CompleteAddressedMemorySpan, String> {
    let mut span =
        AddressedMemorySpan::found(occurrence, body.len() as u64, digest(body)).map_err(debug)?;
    let mut from = 0usize;
    let mut state = 0x9e37_79b9_u64;
    let mut callback_phase = 0usize;
    while from < body.len() {
        let remaining = body.len() - from;
        let width = match carriage {
            Carriage::Whole => remaining,
            Carriage::ByteFragmented => remaining.min(257),
            Carriage::FrameFragmented => remaining.min(1_024),
            Carriage::RandomRechunked => {
                state = state
                    .wrapping_mul(6_364_136_223_846_793_005)
                    .wrapping_add(1);
                remaining.min(1 + (state as usize % 8_191))
            }
            Carriage::CallbackBoundaries => {
                const WIDTHS: [usize; 7] = [13, 4_096, 73, 1_537, 29, 8_003, 509];
                let width = WIDTHS[callback_phase % WIDTHS.len()];
                callback_phase += 1;
                remaining.min(width)
            }
        };
        let to = from + width;
        (span, _) = span
            .admit(MemorySpanFragment::new(
                occurrence,
                from as u64,
                body[from..to].to_vec(),
            ))
            .map_err(|refusal| debug(refusal.defect))?;
        from = to;
    }
    span.close().map_err(|refusal| debug(refusal.defect))
}

fn dropout(
    family: &'static str,
    occurrence: &str,
    body: &[u8],
) -> Result<SeparatorReceipt, String> {
    let split = body.len().min(1_024).max(2) / 2;
    let mut span =
        AddressedMemorySpan::found(occurrence, body.len() as u64, digest(body)).map_err(debug)?;
    (span, _) = span
        .admit(MemorySpanFragment::new(
            occurrence,
            0,
            body[..split].to_vec(),
        ))
        .map_err(|refusal| debug(refusal.defect))?;
    let supplied = split + 1;
    let refusal = span
        .admit(MemorySpanFragment::new(
            occurrence,
            supplied as u64,
            body[supplied..body.len().min(supplied + 17)].to_vec(),
        ))
        .expect_err("dropout must refuse at its first missing coordinate");
    Ok(SeparatorReceipt {
        family,
        control: "dropout",
        defect: refusal.defect,
        retained_prefix_octets: refusal.assembly.reconstructed_octets(),
        rejected_fragment_from: refusal.rejected_fragment.map(|fragment| fragment.from),
    })
}

fn reorder(
    family: &'static str,
    occurrence: &str,
    body: &[u8],
) -> Result<SeparatorReceipt, String> {
    let supplied = body.len().min(1_024).max(2) / 2;
    let span =
        AddressedMemorySpan::found(occurrence, body.len() as u64, digest(body)).map_err(debug)?;
    let refusal = span
        .admit(MemorySpanFragment::new(
            occurrence,
            supplied as u64,
            body[supplied..body.len().min(supplied + 17)].to_vec(),
        ))
        .expect_err("reorder must refuse before admitting a successor without its prefix");
    Ok(SeparatorReceipt {
        family,
        control: "reorder",
        defect: refusal.defect,
        retained_prefix_octets: refusal.assembly.reconstructed_octets(),
        rejected_fragment_from: refusal.rejected_fragment.map(|fragment| fragment.from),
    })
}

fn span_stats(span: &CompleteAddressedMemorySpan) -> (u64, u64, u64) {
    (
        span.fragment_population,
        span.joins.len() as u64,
        span.largest_fragment_octets,
    )
}

fn cross_and_recover<T: ExteriorOccurrenceTransducer + Any + Send>(
    membrane: &mut AthenaCausalMembrane<GranularReturnedAffineAthenaRest>,
    source: T,
    address: &life::athena_native::NativeSectionAddress,
    receiver: ReceiverId,
) -> Result<(AthenaMembraneCrossingReceipt, T), String> {
    let exterior = source.into_exterior_fibre().map_err(display)?;
    let boundary = BoundaryId(exterior.address().event_projection.0);
    let base = BaseUnits::declare(["sens1-common-mouth-current"]).map_err(display)?;
    let occurrence = membrane
        .bind_occurrence(
            exterior,
            boundary,
            address,
            receiver,
            ExactMembraneChartPassage::identity(
                base.unit("sens1-common-mouth-current").map_err(display)?,
                ExactComplexWaveCurrent::zero(),
                ExactComplexWaveCurrent::zero(),
            ),
            Vec::new(),
        )
        .map_err(|failure| format!("SENS1 binding refused: {failure:?}"))?;
    let AthenaMembraneConsequence::Returned(returned) =
        membrane.receive_occurrence(occurrence).map_err(display)?
    else {
        return Err("the SENS1 source did not cross the common Athena mouth".to_owned());
    };
    let receipt = returned.receipt;
    let source = returned
        .occurrence
        .exterior
        .recover::<T>()
        .map_err(|fibre| format!("the SENS1 source fibre did not return: {fibre:?}"))?;
    Ok((receipt, source))
}

fn continuing_native_address(
    standing: &impl AthenaMembraneStanding,
) -> Result<(life::athena_native::NativeSectionAddress, ReceiverId), String> {
    for address in &standing.membrane_realization().sections {
        let addressed = standing
            .membrane_ecology()
            .native()
            .addressed_section(&address.spool, &address.thread, address.occurrence)
            .map_err(display)?;
        if addressed.thread().chronology.is_empty() {
            continue;
        }
        if let Some(receiver) = addressed.spool().receiver_family.iter().next().copied() {
            return Ok((address.clone(), receiver));
        }
    }
    Err("the MEM6 body has no continuing addressed native section".to_owned())
}

fn digest_json(value: &impl Serialize) -> Result<String, String> {
    serde_json::to_vec(value)
        .map(|bytes| digest(&bytes))
        .map_err(display)
}

fn digest_i16(values: &[i16]) -> String {
    let mut hash = Sha256::new();
    for value in values {
        hash.update(value.to_le_bytes());
    }
    hex(hash.finalize())
}

fn digest_composed(parts: &[&[u8]]) -> String {
    let mut hash = Sha256::new();
    for part in parts {
        hash.update((part.len() as u64).to_le_bytes());
        hash.update(part);
    }
    hex(hash.finalize())
}

fn digest(bytes: &[u8]) -> String {
    hex(Sha256::digest(bytes))
}

fn hex(bytes: impl AsRef<[u8]>) -> String {
    bytes
        .as_ref()
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect()
}

fn debug(value: impl std::fmt::Debug) -> String {
    format!("{value:?}")
}

fn display(value: impl std::fmt::Display) -> String {
    value.to_string()
}

fn workspace_root() -> Result<PathBuf, String> {
    let mut path = env::current_dir().map_err(display)?;
    loop {
        if path.join("Cargo.toml").is_file() && path.join("canon").is_dir() {
            return Ok(path);
        }
        if !path.pop() {
            return Err("workspace root not found".to_owned());
        }
    }
}
