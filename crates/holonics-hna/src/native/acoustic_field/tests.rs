use super::*;
use holonic_engine::{
    embedding_fiber::ResidentReadout,
    native_ecology::constitutive_fibre::{
        ConstitutiveReading, NativeJunctionSeed, ResidentConstitutiveFibre,
    },
    resident_section::ResidentSurface,
};

fn source(samples: &[i16]) -> ExactAcousticOccurrence {
    let bytes = (samples.len() * 2) as u32;
    let mut wav = Vec::new();
    wav.extend(b"RIFF");
    wav.extend((36 + bytes).to_le_bytes());
    wav.extend(b"WAVEfmt ");
    wav.extend(16u32.to_le_bytes());
    wav.extend(1u16.to_le_bytes());
    wav.extend(1u16.to_le_bytes());
    wav.extend(16000u32.to_le_bytes());
    wav.extend(32000u32.to_le_bytes());
    wav.extend(2u16.to_le_bytes());
    wav.extend(16u16.to_le_bytes());
    wav.extend(b"data");
    wav.extend(bytes.to_le_bytes());
    for s in samples {
        wav.extend(s.to_le_bytes());
    }
    ExactAcousticOccurrence::from_wav_bytes(&wav, "source", "memory.wav", 2, 2, 1).unwrap()
}

fn chart(samples: &[i16], width: usize) -> AcousticFieldChart {
    AcousticFieldChart::from_acoustic(
        &source(samples),
        PhaseCurrentReceiverId(1),
        PhaseCurrentLineageId(2),
        BigRational::new(7.into(), 3.into()),
        width,
        32768,
    )
    .unwrap()
}
fn material(n: usize) -> Vec<NativeJunctionSeed> {
    (0..n)
        .map(|_| NativeJunctionSeed {
            incoming_admittance: 1,
            held_admittance: 1,
            incoming_transport: NativePhaseCurrent::unit(),
            initial_held: NativePhaseCurrent::zero(),
        })
        .collect()
}

#[test]
fn temporal_chart_reconstructs_extremes_zeros_and_padding() {
    let values = [i16::MIN, 0, i16::MAX, -1, 9];
    for width in [1, 2, 4, 9] {
        let mut c = chart(&values, width);
        assert_eq!(c.reconstruct_samples(), values);
        let first = c.next_support().unwrap();
        assert_eq!(first.begin, BigRational::new(7.into(), 3.into()));
        c.cursor = c.section.cells.len() - 1;
        let last = c.next_support().unwrap();
        assert_eq!(last.coefficient_until, values.len());
        assert_eq!(
            last.end,
            BigRational::new(7.into(), 3.into()) + BigRational::new(5.into(), 16000.into())
        );
        assert_eq!(
            last.structural_padding,
            width * c.section.cells.len() - values.len()
        );
    }
}

#[test]
fn equal_integrated_faces_retain_different_temporal_fibres() {
    let a = chart(&[1, -1, 4, 0], 2);
    let b = chart(&[-1, 1, 0, 4], 2);
    assert_eq!(a.section.integrated_cells(), b.section.integrated_cells());
    assert_ne!(a.section.flat_values(), b.section.flat_values());
    assert_ne!(a.prepare(None).incoming(), b.prepare(None).incoming());
}

#[test]
fn chosen_cell_support_is_exact_and_does_not_advance_the_chart() {
    let c = chart(&[-7, 0, 9], 2);
    assert!(c.support_at(usize::MAX).is_err());
    let support = c.support_at(1).unwrap();
    assert_eq!(support.source_occurrence, "source");
    assert_eq!(support.cell, 1);
    assert_eq!(support.coefficient_from, 2);
    assert_eq!(support.coefficient_until, 3);
    assert_eq!(support.structural_padding, 1);
    assert_eq!(
        support.begin,
        BigRational::new(7.into(), 3.into()) + BigRational::new(2.into(), 16000.into())
    );
    assert_eq!(
        support.end,
        BigRational::new(7.into(), 3.into()) + BigRational::new(3.into(), 16000.into())
    );
    assert_eq!(c.cursor(), 0);
    assert_eq!(c.reconstruct_samples(), vec![-7, 0, 9]);
    assert!(c.support_at(2).is_err());
}

#[test]
fn a_recording_interval_retains_parent_coordinates_and_exact_clock_offset() {
    let recording = source(&[13, -7, 0, 9, 21]);
    let origin = BigRational::new(7.into(), 3.into());
    let c = AcousticFieldChart::from_acoustic_range(
        &recording,
        PhaseCurrentReceiverId(4),
        PhaseCurrentLineageId(8),
        origin.clone(),
        1..4,
        2,
        32768,
    )
    .unwrap();
    assert_eq!(c.source_range(), 1..4);
    assert_eq!(c.recording_samples(), 5);
    assert_eq!(c.reconstruct_samples(), vec![-7, 0, 9]);
    assert_eq!(c.source_sha256(), recording.source_sha256);
    assert_eq!(c.source_octets(), recording.source_octets);
    let first = c.support_at(0).unwrap();
    let tail = c.support_at(1).unwrap();
    assert_eq!((first.coefficient_from, first.coefficient_until), (1, 3));
    assert_eq!(
        (
            tail.coefficient_from,
            tail.coefficient_until,
            tail.structural_padding
        ),
        (3, 4, 1)
    );
    assert_eq!(
        first.begin,
        &origin + BigRational::new(1.into(), 16000.into())
    );
    assert_eq!(first.end, tail.begin);
    assert_eq!(tail.end, &origin + BigRational::new(4.into(), 16000.into()));
    assert_eq!(c.cursor(), 0);
    assert_eq!(recording.samples, vec![13, -7, 0, 9, 21]);
}

#[test]
fn empty_reversed_and_outside_recording_intervals_are_refused() {
    let recording = source(&[1, 0, -1]);
    for range in [0..0, 2..1, 0..4, usize::MAX..usize::MAX] {
        assert!(AcousticFieldChart::from_acoustic_range(
            &recording,
            PhaseCurrentReceiverId(1),
            PhaseCurrentLineageId(1),
            BigRational::from_integer(0.into()),
            range,
            2,
            32768,
        )
        .is_err());
    }
}

#[test]
#[ignore = "requires resident native field backend"]
fn acoustic_field_returns_complete_branches_and_preserves_refused_source() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut field = NativeConstitutiveField::found(&surface, material(2)).unwrap();
    let mut chart = chart(&[3, -7, 0, 9, 2], 2);
    let (_, first) = chart.advance_status(&mut field, &mut None).unwrap();
    assert_eq!(first.lineage.incoming.len(), 2);
    assert_eq!(first.outgoing.len(), 2);
    assert_eq!(
        first.held_successor,
        first
            .lineage
            .incoming
            .iter()
            .map(|v| v.current())
            .collect::<Vec<_>>()
    );
    assert_eq!(field.occurrence_count(), 1);
    let mut source = Some(first.source);
    let mut foreign = NativeConstitutiveField::found(&surface, material(2)).unwrap();
    assert!(chart.advance_status(&mut foreign, &mut source).is_err());
    assert_eq!(chart.cursor(), 1);
    assert!(source.is_some());
    let (_, second) = chart.advance_status(&mut field, &mut source).unwrap();
    assert!(source.is_none());
    assert_eq!(second.lineage.received_from, Some(0));
    assert_eq!(second.outgoing, first.held_successor);
    assert_eq!(second.received_difference.unwrap().arrived.len(), 2);
    let (tail, third) = chart.advance_status(&mut field, &mut None).unwrap();
    assert_eq!(tail.structural_padding, 1);
    assert_eq!(third.lineage.received_from, None);
    assert!(chart.is_complete());
    assert_eq!(field.occurrence_count(), 3);
}

#[test]
#[ignore = "requires resident native field backend"]
fn mounted_cells_keep_exact_pcm_support_and_feed_rational_current_without_readback() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let c = chart(&[-7, 0, 9], 2);
    let before = surface.census();
    assert!(c.mount_cell(&surface, usize::MAX).is_err());
    assert_eq!(surface.census(), before);
    let negative_zero = c.mount_cell(&surface, 0).unwrap();
    let padded = c.mount_cell(&surface, 1).unwrap();
    assert_eq!(negative_zero.support().structural_padding, 0);
    assert_eq!(padded.support().structural_padding, 1);
    assert_eq!(padded.receiver(), PhaseCurrentReceiverId(1));
    assert_eq!(padded.lineage(), PhaseCurrentLineageId(2));
    let decoded = source(&[-7, 0, 9]);
    assert_eq!(padded.chart().source_locator(), decoded.locator);
    assert_eq!(padded.chart().source_sha256(), decoded.source_sha256);
    assert_eq!(padded.chart().source_octets(), decoded.source_octets);
    assert_eq!(padded.chart().reconstruct_samples(), decoded.samples);
    assert_eq!(padded.divisor(), 32768);
    assert_eq!(
        padded.sample_step(),
        &BigRational::new(1.into(), 16000.into())
    );
    assert_eq!(c.cursor(), 0);

    let mut body = ResidentConstitutiveFibre::found(&surface, 4, 4).unwrap();
    let before = surface.census();
    // Identity-receiver control: the native relation must transport the common denominator
    // to a new magnitude while preserving every zero quadrature and padded source coordinate.
    body.advance_resident(
        negative_zero.rational().unwrap(),
        Some(negative_zero.rational().unwrap()),
    )
    .unwrap();
    let returned = body
        .advance_resident(padded.rational().unwrap(), None)
        .unwrap();
    let after = surface.census();
    assert_eq!(after.section_read_outs, before.section_read_outs);
    assert_eq!(after.egress_section_octets, before.egress_section_octets);
    assert_eq!(after.ingress_octets, before.ingress_octets);
    match returned.inspect().unwrap().predecessor_reading {
        ConstitutiveReading::Unique { current } => assert_eq!(
            current,
            vec![
                BigRational::new(9.into(), 32768.into()),
                BigRational::from_integer(0.into()),
                BigRational::from_integer(0.into()),
                BigRational::from_integer(0.into())
            ]
        ),
        other => panic!("expected exact rational current: {other:?}"),
    }

    let negative_words = surface.read_out(negative_zero.section()).unwrap();
    assert_eq!(
        negative_words,
        vec![(-7, -7), (0, 0), (0, 0), (0, 0), (32768, 32768)]
    );
    let padded_words = surface.read_out(padded.section()).unwrap();
    assert_eq!(
        padded_words,
        vec![(9, 9), (0, 0), (0, 0), (0, 0), (32768, 32768)]
    );
}
