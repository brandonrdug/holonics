//! Bounded synthetic CODE parity controls; no corpus, subject data or capability claim.
use super::*;
use std::path::PathBuf;

fn fixture_classes(root: &Path, classes: &[usize]) -> Result<String> {
    let mut checkpoint = fresh_checkpoint_at_law(
        16384,
        holonics::hnn::receiving::ReceivingLaw::RetainedFibreV1,
    )?;
    assert_eq!(checkpoint.stream.accepted_cells()?, 0);
    assert_eq!(
        checkpoint.stream.resident().receiving_law(),
        holonics::hnn::receiving::ReceivingLaw::RetainedFibreV1
    );
    let fresh = checkpoint.bytes()?;
    let fresh_hash = sha256(&fresh)?;
    let (_, _, pairing) = declaration(16384)?;
    let received = checkpoint.stream.receive_with_execution(
        &port(),
        &pairing,
        classes,
        &HostObservedEpochExecution,
    )?;
    assert_eq!(received.epochs.len(), 1);
    assert_eq!((received.published, received.pending), (10, 0));
    let epoch = &received.epochs[0];
    assert_eq!(
        epoch.receiving_law,
        holonics::hnn::receiving::ReceivingLaw::RetainedFibreV1
    );
    assert!(epoch.retained_section_return.is_some());
    let training_hash = sha256(&checkpoint.bytes()?)?;
    let prefix = root.join("sample");
    let reading = continuation::sample_continuing(
        &checkpoint,
        &[],
        continuation::SamplingPolicy::NativeFullFibre,
        &[0x55u8; 64],
        8,
        &[0, 4, 8],
        Some(4),
        &prefix,
    )?;
    assert_eq!(reading.classes.len(), 8);
    assert!(
        reading
            .cold_continuation
            .as_ref()
            .unwrap()
            .matched_warm_state_and_crib
    );
    assert_eq!(sha256(&checkpoint.bytes()?)?, training_hash);
    let semantic = object(&[
        (
            "fixture",
            quoted("synthetic10arrivals8output4cold; no dataset"),
        ),
        (
            "receiving_law",
            quoted(checkpoint.stream.resident().receiving_law().as_str()),
        ),
        ("fresh_cells", "0".into()),
        ("fresh_checkpoint_sha256", quoted(&fresh_hash)),
        ("training_checkpoint_sha256", quoted(&training_hash)),
        ("epoch_outcome", exact(&epoch.outcome)),
        ("actual_class_return", exact(&epoch.retained_section_return)),
        ("whole_comparison", exact(&epoch.comparison)),
        ("joint_comparison", exact(&epoch.joint_comparison)),
        (
            "receiving_only_comparison",
            exact(&epoch.receiving_only_comparison),
        ),
        ("output_classes", exact_classes(&reading.classes)),
        ("output_bytes", format!("{:?}", reading.raw_bytes)),
        ("final_state_sha256", quoted(&reading.final_state_sha256)),
        ("final_crib_sha256", quoted(&reading.final_crib_sha256)),
        (
            "cold_matched",
            reading
                .cold_continuation
                .as_ref()
                .unwrap()
                .matched_warm_state_and_crib
                .to_string(),
        ),
    ]);
    write_new(&root.join("semantic.json"), semantic.as_bytes())?;
    Ok(semantic)
}
fn run(workers: usize, root: &Path) -> String {
    std::fs::create_dir(root).unwrap();
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(workers)
        .build()
        .unwrap();
    let result = pool
        .install(|| {
            assert_eq!(rayon::current_num_threads(), workers);
            fixture_classes(root, &[0; 10]).map_err(|error| error.to_string())
        })
        .unwrap();
    write_new(
        &root.join("workers.json"),
        object(&[("actual_workers", workers.to_string())]).as_bytes(),
    )
    .unwrap();
    result
}
fn root(label: &str) -> std::path::PathBuf {
    match std::env::var_os("V92_CODE_FIXTURE_DIR") {
        Some(path) => PathBuf::from(path),
        None => {
            std::env::temp_dir().join(format!("holonics-v92-code-{label}-{}", std::process::id()))
        }
    }
}
#[test]
fn native_one_vs_four_workers_are_exact() {
    let root = root("one-vs-four");
    std::fs::create_dir(&root).unwrap();
    let one = run(1, &root.join("one"));
    let four = run(4, &root.join("four"));
    assert_eq!(
        one, four,
        "native law/state differs across the explicit Rayon pools"
    );
}
#[test]
fn real_hnn_process_fixture() {
    let root = root("pool-child");
    run(1, &root);
}

#[test]
fn one_varied_native_section_records_positive_gain_or_refusal() {
    let root = root("one-varied-section");
    std::fs::create_dir(&root).unwrap();
    let result = fixture_classes(&root, &[0, 1, 2, 3, 0, 1, 2, 3, 0, 1]);
    let report = match result {
        Ok(semantic) => semantic,
        Err(error) => object(&[
            ("status", quoted("POSITIVE_NATIVE_GAIN_UNESTABLISHED")),
            ("typed_refusal", quoted(&error.to_string())),
        ]),
    };
    write_new(
        &root.join("POSITIVE_NATIVE_GAIN_CONTROL.json"),
        report.as_bytes(),
    )
    .unwrap();
    eprintln!("V92_SINGLE_VARIED_NATIVE_CONTROL {}", report);
}
#[test]
fn fresh_native_cli_refuses_nonfresh_selected_checkpoint_before_prompt_read() {
    let root = root("fresh-reject");
    std::fs::create_dir(&root).unwrap();
    let mut checkpoint = fresh_checkpoint_at_law(
        16384,
        holonics::hnn::receiving::ReceivingLaw::RetainedFibreV1,
    )
    .unwrap();
    checkpoint
        .stream
        .receive_with_execution(
            &port(),
            &declaration(16384).unwrap().2,
            &[0],
            &HostObservedEpochExecution,
        )
        .unwrap();
    assert_eq!(checkpoint.stream.accepted_cells().unwrap(), 1);
    let state = root.join("nonfresh.state");
    checkpoint.publish(state.to_str().unwrap()).unwrap();
    let args = vec![
        "sample".into(),
        "host-reference".into(),
        state.to_str().unwrap().into(),
        "not-opened-prompt".into(),
        "unset".into(),
        "not-opened-keys".into(),
        "unset".into(),
        "fresh-native".into(),
        "no-replay".into(),
        root.join("never-created").to_str().unwrap().into(),
    ];
    let error = sample(&args).unwrap_err();
    assert!(error.to_string().contains("fresh-native requires"));
    assert!(!root.join("never-created").exists());
}
