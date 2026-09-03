use athena_alpha::{
    render_material_artifact, AthenaAlphaApplication, ExactReadbackWorld,
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
    NativeEcologyRest, NativeMorphologyArtifact, NativeWorldStage,
};

fn configuration() -> NativeCirculationConfiguration {
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
    .expect("configuration")
}

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
    AthenaAlphaApplication::mount(package, configuration()).expect("application")
}

fn request(thread: &str, occurrence: u64) -> NativeInferenceRequest {
    NativeInferenceRequest {
        address: NativeInferenceAddress {
            spool: "spool/direct-cycle".to_owned(),
            thread: thread.to_owned(),
            occurrence: EventId(occurrence),
        },
        receiver: ReceiverId(9),
    }
}

#[test]
fn actual_world_return_commits_remounts_withdraws_and_replays_one_material_cycle() {
    let application = application();
    let unrelated_before = application
        .conduct(request("thread/return", 2))
        .expect("unrelated before");
    let ingress = application
        .ingress_octets(
            request("thread/outward", 1),
            "application/material",
            &[3, 8, 2],
        )
        .expect("ingress");
    let native = application
        .conduct_material(ingress)
        .expect("native material emission");
    let artifact = render_material_artifact(native).expect("artifact");
    assert_eq!(artifact.octets, b"eee");
    let world = ExactReadbackWorld
        .act(&artifact.octets)
        .expect("actual readback world");
    let faces = world
        .faces_for(&artifact.native.circulation)
        .expect("issued faces");
    let NativeWorldStage::Candidate { candidate, .. } = application
        .stage_world_return(&artifact.native.circulation, faces, EventId(100))
        .expect("world return")
    else {
        panic!("readback admission must stage")
    };
    let candidate_wire = serde_json::to_vec(&candidate).expect("candidate wire");
    assert!(!candidate_wire
        .windows(b"application/material".len())
        .any(|window| window == b"application/material"));
    drop(artifact);

    let (application, commit) = application.commit(candidate).expect("commit");
    assert_eq!(application.generation(), 1);
    assert_eq!(commit.returned_occurrence, EventId(100));
    assert!(!commit.causal_cone.is_empty());
    let unrelated_after = application
        .conduct(request("thread/return", 2))
        .expect("unrelated after");
    assert_eq!(
        unrelated_before.emission.address,
        unrelated_after.emission.address
    );
    assert_eq!(
        unrelated_before
            .futures
            .iter()
            .map(|future| future.future)
            .collect::<Vec<_>>(),
        unrelated_after
            .futures
            .iter()
            .map(|future| future.future)
            .collect::<Vec<_>>()
    );
    assert_eq!(unrelated_before.lineage, unrelated_after.lineage);
    assert_ne!(
        unrelated_before.emission.grains,
        unrelated_after.emission.grains
    );

    let later_request = request(&commit.deposit_receipt.thread_address, 100);
    let later = application
        .conduct(later_request.clone())
        .expect("later conduct");
    let snapshot = application.snapshot().expect("snapshot");
    let snapshot_wire = snapshot.canonical_bytes().expect("snapshot wire");
    let remounted = AthenaAlphaApplication::remount(
        life::native_intelligence::NativeCirculationSnapshot::read(&snapshot_wire)
            .expect("read snapshot"),
    )
    .expect("remount");
    assert_eq!(
        remounted
            .snapshot()
            .expect("remounted snapshot")
            .canonical_bytes()
            .expect("remounted wire"),
        snapshot_wire
    );

    let (withdrawn, moved_commit) = remounted
        .withdraw_last_commit()
        .expect("withdraw commit");
    assert!(withdrawn.conduct(later_request.clone()).is_err());
    let replayed = withdrawn
        .replay_commit(moved_commit)
        .expect("replay commit");
    let restored = replayed.conduct(later_request).expect("restored conduct");
    assert_eq!(restored, later);
}
