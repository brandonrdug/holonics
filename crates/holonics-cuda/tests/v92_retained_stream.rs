//! Synthetic retained-fibre observed-stream parity against the native executor.
//!
//! This is source-scoped CUDA CODE coverage only. It uses a small declared field and ten
//! synthetic source classes; it reads no external corpus or model output.

use std::sync::atomic::{AtomicUsize, Ordering};

use holonics::geometry::RatVec3;
use holonics::geometry::screw::ScrewGenerator;
use holonics::hnn::constitution::{
    Constitution, ContinuingState, EpochProducerRecordReading, EpochRecordFlowReading, LinearLocus,
};
use holonics::hnn::encoding::observed::PairedObservation;
use holonics::hnn::field::{
    ContactDeclaration, CribDeclaration, Field, FieldDeclaration, ReceiverDeclaration,
    RingDeclaration,
};
use holonics::hnn::paired::{PairedCarrier, PairingDeclaration};
use holonics::hnn::pending::PendingRatio;
use holonics::hnn::port::WordReturn;
use holonics::hnn::ratio::RatioCovector;
use holonics::hnn::receiving::{ReceivingLaw, ReceivingPhases};
use holonics::hnn::reference::observed::{
    HostObservedEpochExecution, ObservedCrib, ObservedEpochDepositionScope, ObservedEpochExecution,
    ObservedEpochForwardContext, ObservedEpochForwardWord, ObservedStream,
};
use holonics::hnn::word::{Word, WordOpening};
use holonics::hnn::{Current, ExecutionPort, HnnError, Reference};
use holonics::ratio::linear::ExactRatMatrix;
use holonics::ratio::{integer, rat};
use holonics_cuda::hnn::ObservedEpochDevice;

const CIRCLE: [(i64, i64); 16] = [
    (8, 1),
    (7, 4),
    (4, 7),
    (1, 8),
    (-1, 8),
    (-4, 7),
    (-7, 4),
    (-8, 1),
    (-8, -1),
    (-7, -4),
    (-4, -7),
    (-1, -8),
    (1, -8),
    (4, -7),
    (7, -4),
    (8, -1),
];

fn ring(period: u64, lock: Vec<u64>) -> RingDeclaration {
    RingDeclaration {
        period,
        screw: ScrewGenerator::new(RatVec3::from_i64(0, 0, 1), RatVec3::zero()),
        placements: (0..period)
            .map(|node| RatVec3::from_i64(CIRCLE[node as usize].0, CIRCLE[node as usize].1, 0))
            .collect(),
        lock,
        reflector: (0..period)
            .map(|phase| ((period - phase) % period) as usize)
            .collect(),
        admittance: integer(2),
        initial: 0,
    }
}

fn contact(from: usize, to: usize, node: usize) -> ContactDeclaration {
    ContactDeclaration {
        from,
        to,
        channel: vec![(node, node)],
        admittance: integer(2),
        exponent: integer(0),
    }
}

fn opening() -> (Reference, ObservedStream, PairingDeclaration, Constitution) {
    let field = Field::declare(
        FieldDeclaration {
            founded: Vec::new(),
            founding: false,
            rings: vec![
                ring(5, (0..5).collect()),
                ring(2, Vec::new()),
                ring(3, Vec::new()),
            ],
            contacts: vec![contact(0, 1, 0), contact(1, 2, 0)],
            loops: Vec::new(),
            sources: vec![0],
            offsets: vec![1],
            alphabet: 4,
            step: integer(1),
            exponent_grain: 1,
            receivers: vec![ReceiverDeclaration {
                ring: 2,
                aperture: 1,
                tolerance: rat(1, 16),
                depth: 2,
                prior: holonics::compression::landmark::context::StopPrior::half(),
                mass: 1,
                base: holonics::compression::landmark::context::BaseMeasure::Even,
                receiving_prior: 0,
                ratio: holonics::compression::landmark::context::RatioLaw::Carried,
            }],
            crib: CribDeclaration {
                window: 16,
                offset: 1,
            },
            population: 1 << 16,
            lattice: Default::default(),
        }
        .by_lattice_rule(),
    )
    .unwrap();
    let pairing = PairingDeclaration::Family {
        table: (0..4).map(|class| (class, class ^ 1)).collect(),
    };
    let initial = Constitution::initial(&field, 1 << 40).unwrap();
    let (material, _, _) = PairedCarrier::found(&field, initial, 0, &pairing).unwrap();
    let reference = Reference::new(16, 1 << 40);
    let mut resident = reference
        .mount_with(&field, &Current::at_rest(&field), material.clone())
        .unwrap();
    resident
        .select_receiving_law(ReceivingLaw::RetainedFibreV1)
        .unwrap();
    let boundary = PairedObservation::admit(&field, &material, &pairing).unwrap();
    reference
        .ingest(&mut resident, None, &boundary.encode(&[]).unwrap())
        .unwrap();
    let stream = ObservedStream::new(
        resident,
        ObservedCrib::new(0),
        ObservedEpochDepositionScope::NormalMaps,
    )
    .unwrap();
    (reference, stream, pairing, material)
}

fn cold_restore(
    reference: &Reference,
    stream: &ObservedStream,
    opening_material: Constitution,
) -> ObservedStream {
    let saved = stream.resident().continuing_state(0).unwrap();
    let parsed = ContinuingState::from_text(&saved.to_text(), 1 << 40).unwrap();
    let field = stream.resident().field().clone();
    let resident = reference
        .mount_continued(&field, &Current::at_rest(&field), opening_material, &parsed)
        .unwrap();
    let crib = ObservedCrib::from_unplaced_checkpoint(
        &field,
        resident.current(),
        stream.crib().next_position(),
        &stream.crib().unplaced_checkpoint().unwrap(),
    )
    .unwrap();
    ObservedStream::restore_checkpoint(resident, crib, &stream.pending_checkpoint()).unwrap()
}

struct RejectAfterCardReturn {
    device: ObservedEpochDevice,
    forwards: AtomicUsize,
    aggregate_calls: AtomicUsize,
}

impl RejectAfterCardReturn {
    fn new(device: ObservedEpochDevice) -> Self {
        Self {
            device,
            forwards: AtomicUsize::new(0),
            aggregate_calls: AtomicUsize::new(0),
        }
    }
}

impl ObservedEpochExecution for RejectAfterCardReturn {
    fn forward(
        &self,
        field: &Field,
        constitution: &Constitution,
        ratio: &PendingRatio,
        charts: &mut holonics::hnn::chart::Charts,
        opening: &WordOpening,
    ) -> Result<ObservedEpochForwardWord, HnnError> {
        self.forwards.fetch_add(1, Ordering::Relaxed);
        self.device
            .forward(field, constitution, ratio, charts, opening)
    }

    fn forward_scoped(
        &self,
        context: &mut ObservedEpochForwardContext<'_, '_>,
        ratio: &PendingRatio,
        charts: &mut holonics::hnn::chart::Charts,
        opening: &WordOpening,
    ) -> Result<ObservedEpochForwardWord, HnnError> {
        self.forwards.fetch_add(1, Ordering::Relaxed);
        self.device.forward_scoped(context, ratio, charts, opening)
    }

    fn pull_back(
        &self,
        word: Word<'_>,
        covector: &RatioCovector,
        map: &ExactRatMatrix,
        phases: &ReceivingPhases,
    ) -> Result<WordReturn, HnnError> {
        self.device.pull_back(word, covector, map, phases)
    }

    fn aggregate_records(
        &self,
        _locus: LinearLocus,
        _rows: usize,
        _columns: usize,
        _receiver_grain: u32,
        _epoch_cells: u64,
        _epoch: u64,
        _heard_cells: u64,
        _records: &[EpochProducerRecordReading],
    ) -> Result<EpochRecordFlowReading, HnnError> {
        self.aggregate_calls.fetch_add(1, Ordering::Relaxed);
        Err(HnnError::Unadmitted {
            reason: "synthetic refusal after the card-owned forward and retained return",
        })
    }
}

#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn retained_fibre_stream_card_matches_host_source_tree_population_and_code() {
    let device = ObservedEpochDevice::open(0).expect("a CUDA card with observed kernels");
    let (host_reference, mut host, host_pairing, host_opening) = opening();
    let (card_reference, mut card_stream, card_pairing, card_opening) = opening();
    assert_eq!(host_pairing, card_pairing);
    let classes = [0, 1, 2, 3, 0, 1, 2, 3, 0, 1];

    let host_receipt = host
        .receive_with_execution(
            &host_reference,
            &host_pairing,
            &classes,
            &HostObservedEpochExecution,
        )
        .unwrap();
    let card_receipt = card_stream
        .receive_with_execution(&card_reference, &card_pairing, &classes, &device)
        .unwrap();
    assert_eq!(host_receipt.accepted, card_receipt.accepted);
    assert_eq!(host_receipt.published, card_receipt.published);
    assert_eq!(host_receipt.pending, card_receipt.pending);
    assert_eq!(host_receipt.epochs.len(), card_receipt.epochs.len());
    assert_eq!(host_receipt.epochs.len(), 1);
    for (host_epoch, card_epoch) in host_receipt.epochs.iter().zip(&card_receipt.epochs) {
        assert_eq!(host_epoch.receiving_law, ReceivingLaw::RetainedFibreV1);
        assert_eq!(card_epoch.receiving_law, ReceivingLaw::RetainedFibreV1);
        assert_eq!(host_epoch.consumed, card_epoch.consumed);
        assert_eq!(host_epoch.cells, card_epoch.cells);
        assert_eq!(host_epoch.comparison_commit, card_epoch.comparison_commit);
        assert_eq!(host_epoch.partition_exponent, card_epoch.partition_exponent);
        assert_eq!(host_epoch.closed_section, card_epoch.closed_section);
        assert_eq!(host_epoch.terminal_partial, card_epoch.terminal_partial);
        assert_eq!(host_epoch.carry_out, card_epoch.carry_out);
        assert_eq!(host_epoch.reads, card_epoch.reads);
        assert_eq!(host_epoch.outcome, card_epoch.outcome);
        assert_eq!(
            host_epoch.retained_section_return,
            card_epoch.retained_section_return
        );
    }
    assert_eq!(
        host.resident().receiving_law(),
        card_stream.resident().receiving_law()
    );
    assert_eq!(host.resident().current(), card_stream.resident().current());
    assert_eq!(host.resident().carried(), card_stream.resident().carried());
    assert_eq!(
        host.resident().constitution(),
        card_stream.resident().constitution()
    );
    assert_eq!(
        host.resident().continuing_state(0).unwrap().to_text(),
        card_stream
            .resident()
            .continuing_state(0)
            .unwrap()
            .to_text(),
    );
    assert_eq!(host.crib(), card_stream.crib());
    assert_eq!(host.pending_classes(), card_stream.pending_classes());
    let host_cold = cold_restore(&host_reference, &host, host_opening);
    let card_cold = cold_restore(&card_reference, &card_stream, card_opening);
    assert_eq!(
        host_cold.resident().receiving_law(),
        ReceivingLaw::RetainedFibreV1
    );
    assert_eq!(
        card_cold.resident().receiving_law(),
        ReceivingLaw::RetainedFibreV1
    );
    assert_eq!(
        host_cold.resident().continuing_state(0).unwrap().to_text(),
        card_cold.resident().continuing_state(0).unwrap().to_text(),
    );
    assert_eq!(host_cold.crib(), card_cold.crib());
    assert_eq!(
        host_cold.pending_checkpoint(),
        card_cold.pending_checkpoint()
    );
    drop(device);
}

#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn late_executor_refusal_after_card_return_rolls_back_the_retained_stream() {
    let device = ObservedEpochDevice::open(0).expect("a CUDA card with observed kernels");
    let (reference, mut stream, pairing, _) = opening();
    let before_state = stream.resident().continuing_state(0).unwrap();
    let before_crib = stream.crib().clone();
    let before_pending = stream.pending_checkpoint();
    let execution = RejectAfterCardReturn::new(device);
    let classes = [0, 1, 2, 3, 0, 1, 2, 3, 0, 1];

    assert!(
        stream
            .receive_with_execution(&reference, &pairing, &classes, &execution)
            .is_err()
    );
    assert!(execution.forwards.load(Ordering::Relaxed) > 0);
    assert!(execution.aggregate_calls.load(Ordering::Relaxed) > 0);
    assert_eq!(stream.resident().continuing_state(0).unwrap(), before_state);
    assert_eq!(stream.crib(), &before_crib);
    assert_eq!(stream.pending_checkpoint(), before_pending);
    assert!(stream.pending_classes().is_empty());
}
