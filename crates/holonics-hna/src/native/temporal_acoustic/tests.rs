use super::*;
use holonic_engine::{
    embedding_fiber::ResidentReadout,
    native_ecology::constitutive_fibre::{
        ConditionContactMetric, ResidentTemporalConditionCurrent, TemporalResponseChart,
    },
    phase_current::PhaseCurrentLineageId,
    resident_section::{ResidentGrain, ResidentSectionRest, ResidentSurface},
};
use life::mathematical_source::ExactAcousticOccurrence;
use num_rational::BigRational as Rat;
use sha2::{Digest, Sha256};
use std::result::Result as StdResult;

fn wav_bytes(sample_rate: u32, samples: &[i16]) -> Vec<u8> {
    let data_len = (samples.len() * 2) as u32;
    let mut bytes = Vec::new();
    bytes.extend_from_slice(b"RIFF");
    bytes.extend_from_slice(&(36 + data_len).to_le_bytes());
    bytes.extend_from_slice(b"WAVEfmt ");
    bytes.extend_from_slice(&16_u32.to_le_bytes());
    bytes.extend_from_slice(&1_u16.to_le_bytes());
    bytes.extend_from_slice(&1_u16.to_le_bytes());
    bytes.extend_from_slice(&sample_rate.to_le_bytes());
    bytes.extend_from_slice(&(sample_rate * 2).to_le_bytes());
    bytes.extend_from_slice(&2_u16.to_le_bytes());
    bytes.extend_from_slice(&16_u16.to_le_bytes());
    bytes.extend_from_slice(b"data");
    bytes.extend_from_slice(&data_len.to_le_bytes());
    for sample in samples {
        bytes.extend_from_slice(&sample.to_le_bytes());
    }
    bytes
}

fn occurrence(name: &str, sample_rate: u32, samples: &[i16]) -> ExactAcousticOccurrence {
    let bytes = wav_bytes(sample_rate, samples);
    ExactAcousticOccurrence::from_wav_bytes(&bytes, name, format!("memory://{name}"), 2, 2, 2)
        .unwrap()
}

fn surface() -> &'static ResidentSurface<'static> {
    let readout = Box::leak(Box::new(ResidentReadout::new().unwrap()));
    Box::leak(Box::new(ResidentSurface::on(readout).unwrap()))
}

fn response(
    surface: &'static ResidentSurface<'static>,
) -> ResidentTemporalConditionCurrent<'static> {
    let initial = surface
        .mount_section_rest(
            &ResidentSectionRest::found(
                1,
                5,
                ResidentGrain(0),
                64,
                vec![(1, 1), (0, 0), (0, 0), (0, 0), (1, 1)],
            )
            .unwrap(),
        )
        .unwrap();
    ResidentTemporalConditionCurrent::retain(
        surface,
        initial,
        TemporalResponseChart {
            receiver: holonic_engine::phase_current::PhaseCurrentReceiverId(8),
            origin: Rat::from_integer(0.into()),
            sample_step: Rat::new(1.into(), 16_000.into()),
            phase_extent: 2,
            raw_extent: 2,
        },
        PhaseCurrentLineageId(3),
        4,
        ConditionContactMetric::UnitAdmittanceRealification,
    )
    .unwrap()
}

fn session(surface: &'static ResidentSurface<'static>) -> TemporalAcousticSession<'static> {
    TemporalAcousticSession::retain(
        surface,
        response(surface),
        TemporalAcousticChart {
            sample_rate: 16_000,
            pcm_divisor: 32_768,
            source_receiver: holonic_engine::phase_current::PhaseCurrentReceiverId(1),
            output_receiver: holonic_engine::phase_current::PhaseCurrentReceiverId(9),
        },
    )
    .unwrap()
}

fn pair(index: usize) -> (ExactAcousticOccurrence, ExactAcousticOccurrence) {
    (
        occurrence(
            &format!("source-{index}"),
            16_000,
            if index == 0 {
                &[1, 2, 3, 4]
            } else {
                &[-3, 4, 2, -1]
            },
        ),
        occurrence(
            &format!("observed-{index}"),
            16_000,
            if index == 0 {
                &[4, 3, 2, 1]
            } else {
                &[7, -3, 2, -4]
            },
        ),
    )
}

fn record_pair(
    session: &mut TemporalAcousticSession<'static>,
    source: &ExactAcousticOccurrence,
    observed: &ExactAcousticOccurrence,
) {
    session
        .receive(
            source,
            Rat::from_integer(0.into()),
            observed,
            Rat::from_integer(0.into()),
            |_| (),
        )
        .unwrap();
}

#[test]
#[ignore = "requires native Metal or CUDA resident execution"]
fn pair_checkpoint_remount_then_next_pair_matches_uninterrupted_owner() {
    let first = pair(0);
    let second = pair(1);
    let resumed_surface = surface();
    let mut resumed = session(resumed_surface);
    record_pair(&mut resumed, &first.0, &first.1);
    let directory = tempfile::tempdir().unwrap();
    let checkpoint = directory.path().join("first.temporal");
    resumed.save(&checkpoint).unwrap();
    let saved = SavedTemporalAcousticSession::read(&checkpoint).unwrap();
    drop(resumed);
    let mut remounted = saved.remount(resumed_surface).unwrap();
    record_pair(&mut remounted, &second.0, &second.1);

    let uninterrupted_surface = surface();
    let mut uninterrupted = session(uninterrupted_surface);
    record_pair(&mut uninterrupted, &first.0, &first.1);
    record_pair(&mut uninterrupted, &second.0, &second.1);
    assert_eq!(remounted.contacts(), uninterrupted.contacts());
    assert_eq!(
        remounted
            .snapshot()
            .view()
            .inspect(resumed_surface)
            .unwrap(),
        uninterrupted
            .snapshot()
            .view()
            .inspect(uninterrupted_surface)
            .unwrap()
    );
    assert_eq!(
        serde_json::to_vec(remounted.history()).unwrap(),
        serde_json::to_vec(uninterrupted.history()).unwrap()
    );
    assert_eq!(
        remounted.snapshot().inspect(resumed_surface).unwrap(),
        uninterrupted
            .snapshot()
            .inspect(uninterrupted_surface)
            .unwrap()
    );
}

#[test]
#[ignore = "requires native Metal or CUDA resident execution"]
fn input_clock_refusal_preserves_owner_cut_and_history() {
    let source = occurrence("source", 16_000, &[1, 2, 3, 4]);
    let observed = occurrence("observed", 16_000, &[4, 3, 2, 1]);
    let wrong_clock = occurrence("wrong-clock", 8_000, &[4, 3, 2, 1]);
    let native_surface = surface();
    let mut current = session(native_surface);
    let before = current.snapshot().inspect(native_surface).unwrap();
    assert!(
        current
            .receive(
                &source,
                Rat::from_integer(0.into()),
                &wrong_clock,
                Rat::from_integer(0.into()),
                |_| ()
            )
            .is_err()
    );
    assert_eq!(current.contacts(), 0);
    assert!(current.history().is_empty());
    assert_eq!(current.snapshot().inspect(native_surface).unwrap(), before);
    record_pair(&mut current, &source, &observed);
    assert_eq!(current.contacts(), 1);
}

#[test]
#[ignore = "requires native Metal or CUDA resident execution"]
fn callback_error_after_contact_keeps_advanced_response_and_saves() {
    let (source, observed) = pair(0);
    let native_surface = surface();
    let mut current = session(native_surface);
    let result: StdResult<StdResult<(), &str>, TemporalAcousticError> = current.receive(
        &source,
        Rat::from_integer(0.into()),
        &observed,
        Rat::from_integer(0.into()),
        |_| Err("output callback refused"),
    );
    assert_eq!(result.unwrap().unwrap_err(), "output callback refused");
    assert_eq!(current.contacts(), 1);
    assert_eq!(current.history().len(), 1);
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("advanced.temporal");
    current.save(&path).unwrap();
    assert_eq!(
        SavedTemporalAcousticSession::read(&path)
            .unwrap()
            .history()
            .len(),
        1
    );
}

#[test]
#[ignore = "requires native Metal or CUDA resident execution"]
fn existing_publication_refusal_leaves_owner_and_file_unchanged() {
    let (source, observed) = pair(0);
    let native_surface = surface();
    let mut current = session(native_surface);
    record_pair(&mut current, &source, &observed);
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("single.temporal");
    current.save(&path).unwrap();
    let original = std::fs::read(&path).unwrap();
    let contacts = current.contacts();
    let history = serde_json::to_vec(current.history()).unwrap();
    assert!(current.save(&path).is_err());
    assert_eq!(std::fs::read(&path).unwrap(), original);
    assert_eq!(current.contacts(), contacts);
    assert_eq!(serde_json::to_vec(current.history()).unwrap(), history);
}

fn rewrite_checksum(bytes: &mut [u8]) {
    let footer = bytes.len() - END.len() - 32;
    let digest = Sha256::digest(&bytes[..footer]);
    bytes[footer..footer + 32].copy_from_slice(&digest);
}

#[test]
#[ignore = "requires native Metal or CUDA resident execution"]
fn truncated_and_checksum_valid_but_corrupt_header_checkpoints_are_refused() {
    let (source, observed) = pair(0);
    let native_surface = surface();
    let mut current = session(native_surface);
    record_pair(&mut current, &source, &observed);
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("valid.temporal");
    current.save(&path).unwrap();
    let original = std::fs::read(&path).unwrap();

    let truncated = directory.path().join("truncated.temporal");
    std::fs::write(&truncated, &original[..original.len() - 1]).unwrap();
    assert!(SavedTemporalAcousticSession::read(&truncated).is_err());

    let header_len =
        u64::from_le_bytes(original[MAGIC.len()..MAGIC.len() + 8].try_into().unwrap()) as usize;
    let header_start = MAGIC.len() + 8;
    let native_start = header_start + header_len;
    let header: serde_json::Value =
        serde_json::from_slice(&original[header_start..native_start]).unwrap();
    for (name, mutate) in [
        (
            "support",
            (|h: &mut serde_json::Value| {
                h["history"][0]["support"]["predicted"]["end"] = serde_json::json!(2)
            }) as fn(&mut serde_json::Value),
        ),
        ("lineage", |h: &mut serde_json::Value| {
            h["history"][0]["contact_lineage"] = serde_json::json!(99)
        }),
        ("clock", |h: &mut serde_json::Value| {
            h["chart"]["sample_rate"] = serde_json::json!(8000)
        }),
    ] {
        let mut changed = header.clone();
        mutate(&mut changed);
        let bytes = serde_json::to_vec(&changed).unwrap();
        let mut corrupt = MAGIC.to_vec();
        corrupt.extend_from_slice(&(bytes.len() as u64).to_le_bytes());
        corrupt.extend_from_slice(&bytes);
        corrupt.extend_from_slice(&original[native_start..]);
        rewrite_checksum(&mut corrupt);
        let corrupt_path = directory.path().join(format!("corrupt-{name}.temporal"));
        std::fs::write(&corrupt_path, corrupt).unwrap();
        assert!(
            SavedTemporalAcousticSession::read(&corrupt_path).is_err(),
            "{name}"
        );
    }
}
