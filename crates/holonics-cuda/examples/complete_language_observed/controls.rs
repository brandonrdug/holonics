//! Twenty fixed synthetic arrivals through the actual shared training exterior; no dataset.
use super::*;

#[test]
fn unknown_backend_refuses_before_input_or_output_access() {
    assert!(
        run(&[
            "complete-language".into(),
            "train-retained-fibre-v1".into(),
            "implicit".into()
        ])
        .is_err()
    );
    assert!(
        run(&[
            "complete-language".into(),
            "sample".into(),
            "cuda-observed-epoch-device0".into()
        ])
        .is_err()
    );
}

fn exercise_fixture(label: &str, bytes: &[u8]) {
    let root = std::env::var_os("V92_ADAPTER_FIXTURE_DIR")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| {
            std::env::temp_dir().join(format!("v92-adapter-{}", std::process::id()))
        });
    std::fs::create_dir_all(&root).unwrap();
    let root = root.join(label);
    std::fs::create_dir(&root).unwrap();
    let corpus = root.join("synthetic.bin");
    let cuts = root.join("synthetic-cuts.tsv");
    std::fs::write(&corpus, bytes).unwrap();
    std::fs::write(&cuts, b"0\tsynthetic-opening\n20\tsynthetic-closed\n").unwrap();
    fn hash(path: &Path) -> String {
        let out = std::process::Command::new("sha256sum")
            .arg(path)
            .output()
            .unwrap();
        assert!(out.status.success());
        String::from_utf8(out.stdout)
            .unwrap()
            .split_whitespace()
            .next()
            .unwrap()
            .into()
    }
    for backend in ["host-reference", "cuda-observed-epoch-device0"] {
        let args = vec![
            "complete-language".into(),
            "train-retained-fibre-v1".into(),
            backend.into(),
            corpus.to_str().unwrap().into(),
            hash(&corpus),
            cuts.to_str().unwrap().into(),
            hash(&cuts),
            "16384".into(),
            "20".into(),
            "2".into(),
            root.join(backend).to_str().unwrap().into(),
        ];
        run(&args).unwrap();
        let complete =
            std::fs::read_to_string(root.join(backend).join("TRAINING_COMPLETE.json")).unwrap();
        assert!(complete.contains("\"cold_exact\":true"));
        assert!(complete.contains("\"accepted_cells\":20"));
        assert!(complete.contains("\"actual_epochs\":2"));
    }
    for checkpoint in [
        "fresh.state",
        "trained.state",
        "cut-00000.state",
        "cut-00020.state",
    ] {
        let host = exterior::code_checkpoint_native_bytes(
            root.join("host-reference")
                .join(checkpoint)
                .to_str()
                .unwrap(),
        )
        .unwrap();
        let card = exterior::code_checkpoint_native_bytes(
            root.join("cuda-observed-epoch-device0")
                .join(checkpoint)
                .to_str()
                .unwrap(),
        )
        .unwrap();
        assert_eq!(
            host, card,
            "complete native checkpoint differs: {checkpoint}"
        );
    }
    let receipt =
        std::fs::read_to_string(root.join("cuda-observed-epoch-device0/CUDA_EXECUTION.json"))
            .unwrap();
    assert!(receipt.contains("\"completed\":true"));
    eprintln!("SHARED_EXTERIOR_CUDA_PARITY {}", receipt.trim());
}

#[test]
#[ignore = "exclusive host CUDA guard; neutral synthetic CODE only"]
fn shared_complete_language_training_host_card_and_cold_parity() {
    exercise_fixture("neutral", &[0; 5]);
}
#[test]
#[ignore = "exclusive host CUDA guard; ORIGINAL varied synthetic CODE only"]
fn original_varied_complete_language_host_card_and_cold_parity() {
    exercise_fixture("original-varied", &[0x1b, 0xe4, 0x1b, 0xe4, 0x00]);
}
