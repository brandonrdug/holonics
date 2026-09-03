use std::path::PathBuf;

use athena_alpha::{
    render_material_artifact, AthenaAlphaApplication, ProcessArtifactWorld,
};
use holonic_engine::{
    native_ecology::holonic_intelligence::{
        direct_source_neutral_rest, NativeInferenceAddress, NativeInferenceRequest,
    },
    receiver_exact_compression::ReceiverId,
    EventId,
};
use life::native_intelligence::{
    InferenceConfigurationAddress, MorphologyLineage, NativeCirculationConfiguration,
    NativeEcologyRest, NativeMorphologyArtifact,
};

fn application() -> AthenaAlphaApplication {
    let package = NativeMorphologyArtifact::found(
        NativeEcologyRest::found(direct_source_neutral_rest().expect("direct rest"))
            .expect("ecology rest"),
        MorphologyLineage::origin(),
        Vec::new(),
        Vec::new(),
        Vec::new(),
    )
    .expect("package");
    AthenaAlphaApplication::mount(
        package,
        NativeCirculationConfiguration::found(InferenceConfigurationAddress {
            ingress_aperture: "declared-native-occurrence".to_owned(),
            occurrence: EventId(1),
            receiver: ReceiverId(9),
            continuation_receiver: "issued-world-face-family".to_owned(),
            world_return_law: "session-constituted-return".to_owned(),
            emission_codec: "application-octet-face".to_owned(),
            apparatus: "resident-native-word".to_owned(),
            stochastic_current: None,
        })
        .expect("configuration"),
    )
    .expect("application")
}

fn request() -> NativeInferenceRequest {
    NativeInferenceRequest {
        address: NativeInferenceAddress {
            spool: "spool/direct-cycle".to_owned(),
            thread: "thread/outward".to_owned(),
            occurrence: EventId(1),
        },
        receiver: ReceiverId(9),
    }
}

#[test]
fn changed_fine_current_collapses_to_one_artifact_and_real_rust_and_lean_worlds_reject_it() {
    let application = application();
    let artifact = |octets: &[u8]| {
        let ingress = application
            .ingress_octets(request(), "hna5/unseen-material", octets)
            .expect("ingress");
        let fine = ingress.current().occurrences.clone();
        let native = application
            .conduct_material(ingress)
            .expect("native emission");
        let artifact = render_material_artifact(native).expect("artifact");
        (fine, artifact)
    };
    let (left_current, left) = artifact(&[3, 8, 2]);
    let (right_current, right) = artifact(&[4, 8, 2]);
    assert_ne!(left_current, right_current);
    assert_eq!(left.octets, b"eee");
    assert_eq!(right.octets, left.octets);

    let rust = ProcessArtifactWorld {
        program: PathBuf::from("/home/b/.cargo/bin/rustc"),
        arguments: vec![
            "--crate-type".to_owned(),
            "lib".to_owned(),
            "--emit".to_owned(),
            "metadata".to_owned(),
            "{artifact}".to_owned(),
            "-o".to_owned(),
            "{artifact}.rmeta".to_owned(),
        ],
        artifact_name: "emission.rs".to_owned(),
    }
    .act(&left.octets)
    .expect("rust world");
    let lean = ProcessArtifactWorld {
        program: PathBuf::from("/home/b/.local/bin/lean"),
        arguments: vec!["{artifact}".to_owned()],
        artifact_name: "Emission.lean".to_owned(),
    }
    .act(&left.octets)
    .expect("Lean world");
    assert!(!rust.admitted);
    assert!(!lean.admitted);
    assert!(!rust.stderr.is_empty());
    assert!(!lean.stdout.is_empty() || !lean.stderr.is_empty());
}
