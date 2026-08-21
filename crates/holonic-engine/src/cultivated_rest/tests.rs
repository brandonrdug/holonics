use super::directory::DirectoryManifest;
use super::*;
use crate::native_occurrence::NativeOccurrence;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};

static TEST_NONCE: AtomicU64 = AtomicU64::new(0);

fn unique_temp_path(prefix: &str, suffix: &str) -> PathBuf {
    let nonce = TEST_NONCE.fetch_add(1, Ordering::Relaxed);
    let timestamp = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("system clock after unix epoch")
        .as_nanos();
    std::env::temp_dir().join(format!(
        "{prefix}-{}-{timestamp}-{nonce}{suffix}",
        std::process::id()
    ))
}

fn receipt_fixture() -> DerivationAdjointRankReceipt {
    DerivationAdjointRankReceipt {
        derivation: ExactCertificate::from_canonical_bytes(b"canonical-derivation".to_vec()),
        adjoint: ExactCertificate::from_canonical_bytes(b"canonical-adjoint".to_vec()),
        rank: ExactCertificate::from_canonical_bytes(b"canonical-rank".to_vec()),
    }
}

fn factor_fixture() -> (CultivatedRestInput, Vec<u8>, NativeOccurrence, PathBuf) {
    let predecessor = crate::native_rest::tests::tests::fixture_bytes();
    let hash = |value: &[u8]| digest(value);
    let constitutive = hash(b"law");
    let predecessor_id = PredecessorProductIdentity::from_bytes(&predecessor);
    let predecessor_rest = crate::native_rest::NativeRest::read(&predecessor).unwrap();
    let graph_bytes = serde_json::to_vec(predecessor_rest.graphs()).unwrap();
    let payload = MorphologyPayload::AlignedFactor(AlignedFactor {
        rows: 2,
        columns: 2,
        rank: 1,
        resident_grain: 48,
        left_exponent: 1,
        right_exponent: -1,
        entry_octets: 8,
        left: vec![1, -2],
        right: vec![3, 4],
    });
    let (_, payload_bytes) = payload.descriptor_and_bytes().unwrap();
    let laws = vec![TypedLaw {
        name: "cultivate".to_owned(),
        inputs: vec!["input".to_owned()],
        outputs: vec!["output".to_owned()],
        constitutive_digest: constitutive.clone(),
        extent_agreements: Vec::new(),
    }];
    let input = CultivatedRestInput {
        predecessor: predecessor_id.clone(),
        codebook_graph: CodebookGraphIdentity {
            codebook_sha256: predecessor_rest.codebook().codebook_sha256.clone(),
            graph_identity: hash(&graph_bytes),
        },
        material_lineage_sha256: hash(b"material"),
        ports: vec![
            TypedPort {
                name: "input".to_owned(),
                direction: PortDirection::Input,
                carrier: "exact-i64".to_owned(),
                rows: ExtentOrigin::Runtime,
                width: 2,
                octave_bound: OctaveBoundOrigin::Rested(8),
            },
            TypedPort {
                name: "output".to_owned(),
                direction: PortDirection::Output,
                carrier: "exact-i64".to_owned(),
                rows: ExtentOrigin::Runtime,
                width: 2,
                octave_bound: OctaveBoundOrigin::Rested(8),
            },
        ],
        laws,
        payload,
        receipt: receipt_fixture(),
        reconstruction_fibre: ReconstructionFibre {
            candidates: vec![ReconstructionCandidate {
                identity: "fibre-0".to_owned(),
                payload_sha256: hash(b"candidate"),
                support: vec![1, 5],
            }],
            omitted_sha256: None,
        },
        ablation: TargetedAblation {
            target: "cultivation.delta".to_owned(),
            removed_payload_sha256: hash(&payload_bytes),
            predecessor: predecessor_id,
        },
        runtime_law: RuntimeLawReceipt {
            schema: "holonic-engine.phoenix.runtime-law.v1".to_owned(),
            grain: 48,
            series_aperture: 14,
            band_terms: 40,
            vocabulary_extent: 2,
            hidden_extent: 2,
            rank: 1,
            left_population: "left.factor".to_owned(),
            right_population: "right.factor".to_owned(),
            chart: RuntimeChart::Midpoint,
            fuse: true,
            add_special_tokens: false,
        },
    };
    let path = unique_temp_path("holonic-native-factor", ".safetensors");
    write_native_morphology(
        &path,
        &NativeMorphologyInput {
            left_population: "left.factor".to_owned(),
            right_population: "right.factor".to_owned(),
            left_shape: vec![2, 1],
            right_shape: vec![1, 2],
            left_exponent: 1,
            right_exponent: -1,
            rank: 1,
            resident_grain: 48,
            predecessor: input.predecessor.clone(),
            laws: input.laws.clone(),
            left: vec![1, -2],
            right: vec![3, 4],
        },
    )
    .unwrap();
    let occurrence = NativeOccurrence::read(path.to_str().unwrap()).unwrap();
    (input, predecessor, occurrence, path)
}

fn fixture() -> (CultivatedRestInput, Vec<u8>) {
    let predecessor = b"immutable W1 predecessor".to_vec();
    let payload = MorphologyPayload::SparseDelta(SparseDelta {
        rows: 2,
        columns: 3,
        entries: vec![
            SparseDeltaEntry { index: 1, value: 7 },
            SparseDeltaEntry {
                index: 5,
                value: -2,
            },
        ],
    });
    let (_, payload_bytes) = payload.descriptor_and_bytes().unwrap();
    let hash = |value: &[u8]| digest(value);
    let ports = vec![
        TypedPort {
            name: "input".to_owned(),
            direction: PortDirection::Input,
            carrier: "exact-i64".to_owned(),
            rows: ExtentOrigin::Runtime,
            width: 2,
            octave_bound: OctaveBoundOrigin::Rested(8),
        },
        TypedPort {
            name: "output".to_owned(),
            direction: PortDirection::Output,
            carrier: "exact-i64".to_owned(),
            rows: ExtentOrigin::Runtime,
            width: 2,
            octave_bound: OctaveBoundOrigin::Rested(8),
        },
    ];
    let laws = vec![TypedLaw {
        name: "cultivate".to_owned(),
        inputs: vec!["input".to_owned()],
        outputs: vec!["output".to_owned()],
        constitutive_digest: hash(b"law"),
        extent_agreements: Vec::new(),
    }];
    let predecessor_id = PredecessorProductIdentity::from_bytes(&predecessor);
    let input = CultivatedRestInput {
        predecessor: predecessor_id.clone(),
        codebook_graph: CodebookGraphIdentity::from_canonical(b"codebook", b"w1.graph"),
        material_lineage_sha256: hash(b"material"),
        ports,
        laws,
        payload,
        receipt: receipt_fixture(),
        reconstruction_fibre: ReconstructionFibre {
            candidates: vec![ReconstructionCandidate {
                identity: "fibre-0".to_owned(),
                payload_sha256: hash(b"candidate"),
                support: vec![1, 5],
            }],
            omitted_sha256: None,
        },
        ablation: TargetedAblation {
            target: "cultivation.delta".to_owned(),
            removed_payload_sha256: hash(&payload_bytes),
            predecessor: predecessor_id,
        },
        runtime_law: RuntimeLawReceipt {
            schema: "holonic-engine.phoenix.runtime-law.v1".to_owned(),
            grain: 48,
            series_aperture: 14,
            band_terms: 40,
            vocabulary_extent: 2,
            hidden_extent: 3,
            rank: 1,
            left_population: "left.factor".to_owned(),
            right_population: "right.factor".to_owned(),
            chart: RuntimeChart::Midpoint,
            fuse: true,
            add_special_tokens: false,
        },
    };
    (input, predecessor)
}

#[test]
fn seal_mount_seal_is_byte_identical_and_ablation_returns_predecessor() {
    let (input, predecessor) = fixture();
    let rest = CultivatedRest::seal(input).unwrap();
    let bytes = rest.encode().unwrap();
    let remounted = CultivatedRest::mount(&bytes, &predecessor).unwrap();
    assert_eq!(bytes, remounted.encode().unwrap());
    assert_eq!(
        remounted.ablation_predecessor_identity(),
        PredecessorProductIdentity::from_bytes(&predecessor)
    );
}

#[test]
fn drift_tamper_and_trailing_octets_refuse() {
    let (input, predecessor) = fixture();
    let rest = CultivatedRest::seal(input).unwrap();
    let bytes = rest.encode().unwrap();
    assert!(matches!(
        CultivatedRest::mount(&bytes, b"drift"),
        Err(CultivatedRestRefusal::PredecessorExtent { .. }
            | CultivatedRestRefusal::PredecessorDrift { .. })
    ));
    let mut trailing = bytes.clone();
    trailing.push(0);
    assert!(CultivatedRest::read(&trailing).is_err());
    let mut tampered = bytes;
    let last = tampered.len() - 1;
    tampered[last] ^= 1;
    assert!(matches!(
        CultivatedRest::read(&tampered),
        Err(CultivatedRestRefusal::PayloadDigestMismatch)
    ));
    assert!(!String::from_utf8_lossy(&rest.encode().unwrap()).contains("/home/"));
    let _ = predecessor;
}

#[test]
fn tampered_certificate_is_refused_at_seal() {
    let (mut input, _) = fixture();
    input.receipt.derivation.sha256 = digest(b"tampered");
    assert!(
        matches!(CultivatedRest::seal(input), Err(CultivatedRestRefusal::InvalidDigest(name)) if name == "derivation")
    );
}

#[test]
fn row_only_agreement_does_not_bind_width() {
    let (mut input, _) = fixture();
    input.ports[0].rows = ExtentOrigin::Declared(7);
    input.ports[1].rows = ExtentOrigin::Declared(7);
    input.ports[0].width = 2;
    input.ports[1].width = 9;
    input.laws[0].extent_agreements = vec![PortExtentAgreement::Rows {
        left: "input".to_owned(),
        right: "output".to_owned(),
    }];
    assert!(CultivatedRest::seal(input).is_ok());
}

#[test]
fn one_directory_path_resolves_relative_base_and_rejects_escape() {
    let (input, predecessor, occurrence, morphology_path) = factor_fixture();
    let rest = CultivatedRest::seal_with_native_occurrence(input, &occurrence).unwrap();
    let directory = unique_temp_path("holonic-cultivated-rest", "");
    let _ = std::fs::remove_dir_all(&directory);
    std::fs::create_dir_all(&directory).unwrap();
    std::fs::write(directory.join("cultivated.rest"), rest.encode().unwrap()).unwrap();
    std::fs::write(directory.join("base.rest"), &predecessor).unwrap();
    std::fs::copy(&morphology_path, directory.join("morphology.safetensors")).unwrap();
    let manifest = DirectoryManifest {
        schema: DIRECTORY_SCHEMA.to_owned(),
        rest: "cultivated.rest".to_owned(),
        predecessor: "base.rest".to_owned(),
        identity: PredecessorProductIdentity::from_bytes(&predecessor),
        morphology: "morphology.safetensors".to_owned(),
        codec_companions: Vec::new(),
    };
    std::fs::write(
        directory.join("manifest.json"),
        serde_json::to_vec(&manifest).unwrap(),
    )
    .unwrap();
    let mounted = CultivatedRest::mount_directory(&directory).unwrap();
    assert_eq!(mounted.product.encode().unwrap(), rest.encode().unwrap());
    assert!(mounted.verify_still().is_ok());
    let escape = DirectoryManifest {
        schema: DIRECTORY_SCHEMA.to_owned(),
        rest: "cultivated.rest".to_owned(),
        predecessor: "../base.rest".to_owned(),
        identity: PredecessorProductIdentity::from_bytes(&predecessor),
        morphology: "morphology.safetensors".to_owned(),
        codec_companions: Vec::new(),
    };
    std::fs::write(
        directory.join("manifest.json"),
        serde_json::to_vec(&escape).unwrap(),
    )
    .unwrap();
    assert!(matches!(
        CultivatedRest::mount_directory(&directory),
        Err(CultivatedRestRefusal::DirectoryEscape(_))
    ));
    std::fs::remove_dir_all(directory).unwrap();
    std::fs::remove_file(morphology_path).unwrap();
}

#[test]
fn native_factor_binds_two_raw_i64_regions_and_mismatch_refuses() {
    let (input, predecessor, occurrence, path) = factor_fixture();
    let rest = CultivatedRest::seal_with_native_occurrence(input.clone(), &occurrence).unwrap();
    let payload = rest.morphology_payload().unwrap();
    assert!(matches!(payload, MorphologyPayload::AlignedFactor(_)));
    assert_eq!(rest.native_morphology().unwrap().left_shape, vec![2, 1]);
    assert_eq!(rest.native_morphology().unwrap().right_shape, vec![1, 2]);
    assert_eq!(
        CultivatedRest::mount(&rest.encode().unwrap(), &predecessor)
            .unwrap()
            .morphology_payload()
            .unwrap(),
        payload
    );
    let mut wrong = input;
    if let MorphologyPayload::AlignedFactor(factor) = &mut wrong.payload {
        factor.left[0] = 99;
    }
    assert!(CultivatedRest::seal_with_native_occurrence(wrong, &occurrence).is_err());
    std::fs::remove_file(path).unwrap();
}

#[test]
fn resident_grain_drift_between_factor_and_native_occurrence_refuses() {
    let (mut input, _, occurrence, path) = factor_fixture();
    if let MorphologyPayload::AlignedFactor(factor) = &mut input.payload {
        factor.resident_grain += 1;
    }
    assert!(matches!(
        CultivatedRest::seal_with_native_occurrence(input, &occurrence),
        Err(CultivatedRestRefusal::InvalidIdentity(_))
    ));
    std::fs::remove_file(path).unwrap();
}

#[test]
fn sparse_native_composition_is_an_explicit_refusal() {
    let (input, _, occurrence, path) = factor_fixture();
    let mut sparse = input;
    sparse.payload = MorphologyPayload::SparseDelta(SparseDelta {
        rows: 2,
        columns: 2,
        entries: vec![SparseDeltaEntry { index: 0, value: 1 }],
    });
    let (_, bytes) = sparse.payload.descriptor_and_bytes().unwrap();
    sparse.ablation.removed_payload_sha256 = digest(&bytes);
    assert!(matches!(
        CultivatedRest::seal_with_native_occurrence(sparse, &occurrence),
        Err(CultivatedRestRefusal::NativeMorphologyUnsupported(_))
    ));
    std::fs::remove_file(path).unwrap();
}

#[test]
fn native_writer_rejects_wrong_extent_and_reserved_metadata_names() {
    let (input, _, _, path) = factor_fixture();
    let mut writer = NativeMorphologyInput {
        left_population: "left.factor".to_owned(),
        right_population: "right.factor".to_owned(),
        left_shape: vec![3, 1],
        right_shape: vec![1, 2],
        left_exponent: 1,
        right_exponent: -1,
        rank: 1,
        resident_grain: 48,
        predecessor: input.predecessor.clone(),
        laws: input.laws.clone(),
        left: vec![1, -2],
        right: vec![3, 4],
    };
    assert!(matches!(
        native_morphology_bytes(&writer),
        Err(CultivatedRestRefusal::PayloadShape)
    ));
    writer.left_shape = vec![2, 1];
    writer.left_population = "phoenix.morphology.constitutive".to_owned();
    assert!(matches!(
        native_morphology_bytes(&writer),
        Err(CultivatedRestRefusal::PayloadShape)
    ));
    std::fs::remove_file(path).unwrap();
}
