//! ONE synthetic high-first base4 command replay. No corpus, model pilot or language claim.
use super::*;
use holonics::hnn::reference::prepared_input::{PrefixMode, PrefixRole};

#[test]
fn unified_prepared_command_crosses_sections_aeon_and_cold_prefix() -> Result<()> {
    let root = std::env::var_os("V93_PREPARED_CODE_DIR")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| {
            std::env::temp_dir().join(format!("holonics-v93-unified-{}", std::process::id()))
        });
    std::fs::create_dir(&root)?;
    let data = vec![0x1bu8; 10];
    let classes = digits(&data);
    assert_eq!(classes, (0..40).map(|n| n % 4).collect::<Vec<_>>());
    let cuts = b"0\topening\n13\tthree-actual-pending\n40\tfour-sections-no-flush\n";
    write_new(&root.join("input.bin"), &data)?;
    write_new(&root.join("cuts.tsv"), cuts)?;
    let out = root.join("training");
    let args = vec![
        "train-prepared-local-retained-fibre-v1".into(),
        "host-reference".into(),
        root.join("input.bin").display().to_string(),
        sha256(&data)?,
        root.join("cuts.tsv").display().to_string(),
        sha256(cuts)?,
        "16384".into(),
        "40".into(),
        "4".into(),
        out.display().to_string(),
    ];
    let mut unavailable = args.clone();
    unavailable[1] = "cuda-observed-epoch-device0".into();
    let refusal = run_with_execution(
        &unavailable,
        &HostObservedEpochExecution,
        CompleteLanguageTrainingBackend::CudaObservedEpochDevice0,
    )
    .unwrap_err();
    assert!(refusal.to_string().contains("no selected-device adapter"));
    assert!(!out.exists());
    let execution = CountedHost::default();
    let started = Instant::now();
    run_with_execution(
        &args,
        &execution,
        CompleteLanguageTrainingBackend::HostReference,
    )?;
    assert_eq!(execution.counts(), [40, 40, 4]);
    let training_ns = started.elapsed().as_nanos();
    let (fresh, _) = Checkpoint::load(out.join("fresh.state").to_str().unwrap(), READ_BUDGET)?;
    let (trained, trained_hash) =
        Checkpoint::load(out.join("trained.state").to_str().unwrap(), READ_BUDGET)?;
    let (mut resumed, cut_hash) =
        Checkpoint::load(out.join("cut-00013.state").to_str().unwrap(), READ_BUDGET)?;
    assert_eq!(
        (
            resumed.stream.accepted_cells()?,
            total(resumed.stream.resident())?,
            resumed.stream.pending_classes().len()
        ),
        (13, 10, 3)
    );
    let pairing = declaration(16384)?.2;
    let resumed_receipt = resumed.stream.receive_with_execution(
        &port(),
        &pairing,
        &classes[13..],
        &HostObservedEpochExecution,
    )?;
    assert_eq!(resumed_receipt.epochs.len(), 3);
    assert_eq!(
        resumed.stream.resident().continuing_state(0)?,
        trained.stream.resident().continuing_state(0)?
    );
    assert_eq!(
        resumed.stream.pending_checkpoint(),
        trained.stream.pending_checkpoint()
    );
    assert_eq!(resumed.stream.crib(), trained.stream.crib());
    let trained_resident = trained.stream.resident();
    let material = trained_resident
        .prepared_input()
        .ok_or("prepared state missing")?;
    assert_eq!(material.mode(), PrefixMode::Training);
    assert_eq!(material.frontiers(), (40, 0, 0));
    assert_eq!(material.material().observations(), 38);
    assert!(material.outstanding().is_empty());
    assert_ne!(
        material.material(),
        fresh.stream.resident().prepared_input().unwrap().material()
    );
    let phases = trained_resident.admitted()[0].clone();
    assert_ne!(
        trained_resident.constitution().receiving_law(phases.ring()),
        fresh
            .stream
            .resident()
            .constitution()
            .receiving_law(phases.ring()),
        "founding R must actually receive a local return"
    );
    let epoch_log = std::fs::read_to_string(out.join("epochs.jsonl"))?;
    assert_eq!(epoch_log.lines().count(), 4);
    assert!(!epoch_log.contains("Some(EpochComparison"));
    let output = root.join("continuation");
    // Same sampler used by the explicit128-cell command;8cell CODE replay includes
    // partial-octet cut1/cold next4, not a128cell or language performance claim.
    let sample_started = Instant::now();
    let sample = continuation::sample_continuing(
        &trained,
        &[0x1b],
        continuation::SamplingPolicy::NativeFullFibre,
        &[0x55; 64],
        8,
        &[0, 1, 4, 8],
        Some(1),
        &output,
    )?;
    let sampling_ns = sample_started.elapsed().as_nanos();
    assert_eq!(sample.classes.len(), 8);
    assert!(
        sample
            .cold_continuation
            .as_ref()
            .unwrap()
            .matched_warm_state_and_crib
    );
    let (partial, _) = Checkpoint::load(&sample.cuts[1].checkpoint_path, READ_BUDGET)?;
    let partial_state = partial.stream.resident().prepared_input().unwrap();
    assert_eq!(partial_state.mode(), PrefixMode::Forecast);
    assert_eq!(partial_state.frontiers(), (40, 4, 1));
    assert_eq!(partial_state.unfinished_generated().len(), 1);
    assert_eq!(
        partial_state.history().last().unwrap().1,
        PrefixRole::Hypothesized
    );
    let (final_output, _) =
        Checkpoint::load(&sample.cuts.last().unwrap().checkpoint_path, READ_BUDGET)?;
    let final_state = final_output.stream.resident().prepared_input().unwrap();
    assert_eq!(final_state.frontiers(), (40, 4, 8));
    assert_eq!(
        final_state.material(),
        material.material(),
        "hypotheses do not become empirical testimony"
    );
    let forecast = final_output.stream.resident().constitution();
    let observed = trained_resident.constitution();
    assert_eq!(forecast.commit(), observed.commit());
    for ring in 0..3 {
        assert_eq!(
            forecast.receiving_law(ring),
            observed.receiving_law(ring),
            "full R normal law is frozen"
        );
        assert_eq!(
            forecast.source_law(ring),
            observed.source_law(ring),
            "full source normal law is frozen"
        );
        assert_eq!(
            forecast.contrast_law(ring),
            observed.contrast_law(ring),
            "full contrast normal law is frozen"
        );
        assert_eq!(
            forecast.receiving_phase_statistics(ring),
            observed.receiving_phase_statistics(ring)
        );
        assert_eq!(forecast.standing(ring), observed.standing(ring));
        assert_eq!(forecast.passive_factor(ring), observed.passive_factor(ring));
        assert_eq!(forecast.slices(ring), observed.slices(ring));
        assert_eq!(
            forecast.source_symmetry(ring),
            observed.source_symmetry(ring)
        );
        assert_eq!(forecast.ring_resonator(ring), observed.ring_resonator(ring));
        assert_eq!(forecast.transport(ring), observed.transport(ring));
    }
    for contact in 0..2 {
        assert_eq!(
            forecast.contact_storage(contact),
            observed.contact_storage(contact)
        );
        assert_eq!(
            forecast.contact_stiffness(contact),
            observed.contact_stiffness(contact)
        );
        assert_eq!(
            forecast.contact_dissipation(contact),
            observed.contact_dissipation(contact)
        );
    }
    // Training and forecast use the same producer/read on exactly the same native opening.
    let reference = port();
    let mut training_read = trained_resident.clone();
    let (mut forecast_read, _) = trained.stream.query_fork(&reference, &pairing)?;
    let moment = training_read.continuing().unwrap().0;
    let (tp, tr) = reference.refine(&mut training_read, &moment, &phases)?;
    let (fp, fr) = reference.refine(&mut forecast_read, &moment, &phases)?;
    assert_eq!(exact(&tr.forward), exact(&fr.forward));
    assert_eq!(training_read.carried(), forecast_read.carried());
    assert_eq!(exact(&tr.receipt.detail), exact(&fr.receipt.detail));
    reference.discard(&mut training_read, Handle::Pending(tp))?;
    reference.discard(&mut forecast_read, Handle::Pending(fp))?;
    assert_eq!(sha256(&trained.bytes()?)?, trained_hash);
    let trace = object(&[
        (
            "kind",
            quoted("synthetic CODE one prepared command; no language/model run"),
        ),
        ("input_bytes", format!("{data:?}")),
        ("actual_classes", exact_classes(&classes)),
        ("scope", exact(&trained.stream.scope())),
        ("input_law", quoted(material.law())),
        (
            "backend",
            quoted(
                "host-reference; prepared device adapter UNJOINED; refusal verified before files",
            ),
        ),
        (
            "training_dispatch_forward_return_aggregate",
            format!("{:?}", execution.counts()),
        ),
        ("training_cells", "40".into()),
        ("actual_sections", "4".into()),
        ("whole_aeon_crossed_at", "30".into()),
        ("cut13_checkpoint_sha256", quoted(&cut_hash)),
        ("cut13_accepted_published_pending", "[13,10,3]".into()),
        ("cold_remaining_source_span", "[13,40]".into()),
        ("training_cold_exact", "true".into()),
        ("class_material", exact(material)),
        (
            "R_before",
            exact(
                &fresh
                    .stream
                    .resident()
                    .constitution()
                    .receiving_law(phases.ring()),
            ),
        ),
        (
            "R_after",
            exact(&trained_resident.constitution().receiving_law(phases.ring())),
        ),
        ("actual_current", exact(trained_resident.current())),
        ("actual_carried", exact(&trained_resident.carried())),
        ("sample_cells_requested", "8".into()),
        ("sample_classes", exact_classes(&sample.classes)),
        ("raw_bytes", format!("{:?}", sample.raw_bytes)),
        ("sample_cold", exact(&sample.cold_continuation)),
        ("training_forecast_same_prepared_read", "true".into()),
        ("forecast_tree_population_advance", "true".into()),
        ("forecast_material_frozen", "true".into()),
        ("generated_guesses_are_observations", "false".into()),
        ("training_wall_ns", training_ns.to_string()),
        ("sampling_wall_ns", sampling_ns.to_string()),
        (
            "operation_scope",
            quoted(
                "40unique actual classes/4sections; cold replay adds27executed classes/3sections; prompt4+output8+cold4; causal cuts have additional explicit query reads. Not global kernel/root census.",
            ),
        ),
    ]);
    write_new(
        &root.join("INSPECTABLE_UNIFIED_TRACE.json"),
        trace.as_bytes(),
    )?;
    println!("V93_UNIFIED_PREPARED_TRACE {trace}");
    Ok(())
}

#[derive(Default)]
struct CountedHost([std::sync::atomic::AtomicUsize; 3]);
impl CountedHost {
    fn counts(&self) -> [usize; 3] {
        self.0
            .each_ref()
            .map(|n| n.load(std::sync::atomic::Ordering::Relaxed))
    }
    fn add(&self, n: usize) {
        self.0[n].fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    }
}
impl ObservedEpochExecution for CountedHost {
    fn admit_prepared_input(&self) -> std::result::Result<(), HnnError> {
        HostObservedEpochExecution.admit_prepared_input()
    }
    fn forward(
        &self,
        f: &Field,
        c: &Constitution,
        r: &holonics::hnn::pending::PendingRatio,
        ch: &mut holonics::hnn::chart::Charts,
        o: &holonics::hnn::word::WordOpening,
    ) -> std::result::Result<holonics::hnn::reference::observed::ObservedEpochForwardWord, HnnError>
    {
        let out = HostObservedEpochExecution.forward(f, c, r, ch, o)?;
        self.add(0);
        Ok(out)
    }
    fn forward_scoped(
        &self,
        c: &mut holonics::hnn::reference::observed::ObservedEpochForwardContext<'_, '_>,
        r: &holonics::hnn::pending::PendingRatio,
        ch: &mut holonics::hnn::chart::Charts,
        o: &holonics::hnn::word::WordOpening,
    ) -> std::result::Result<holonics::hnn::reference::observed::ObservedEpochForwardWord, HnnError>
    {
        let out = HostObservedEpochExecution.forward_scoped(c, r, ch, o)?;
        self.add(0);
        Ok(out)
    }
    fn pull_back(
        &self,
        w: holonics::hnn::word::Word<'_>,
        g: &holonics::hnn::ratio::RatioCovector,
        m: &ExactRatMatrix,
        p: &holonics::hnn::receiving::ReceivingPhases,
    ) -> std::result::Result<holonics::hnn::port::WordReturn, HnnError> {
        let out = HostObservedEpochExecution.pull_back(w, g, m, p)?;
        self.add(1);
        Ok(out)
    }
    fn aggregate_records(
        &self,
        l: holonics::hnn::constitution::LinearLocus,
        r: usize,
        c: usize,
        g: u32,
        n: u64,
        e: u64,
        h: u64,
        records: &[holonics::hnn::constitution::EpochProducerRecordReading],
    ) -> std::result::Result<holonics::hnn::constitution::EpochRecordFlowReading, HnnError> {
        assert_eq!(l, holonics::hnn::constitution::LinearLocus::Receiving(2));
        let out = HostObservedEpochExecution.aggregate_records(l, r, c, g, n, e, h, records)?;
        self.add(2);
        Ok(out)
    }
}
