use std::collections::BTreeMap;

use athena_alpha::{
    addressed_ingress, declared_diffusion_law, AthenaAlphaApplication, BASE_CONFIGURATION,
};
use holonic_engine::{
    native_ecology::holonic_intelligence::NativeInferenceRequest,
    native_spool::fixture,
    EventId,
};
use holonics_circulation_abi::{
    dispatch_bytes, AbiCommand, AbiDisposition, AbiEnvelope, AbiResponse,
    HOLONICS_CIRCULATION_ABI_SCHEMA,
};
use life::native_intelligence::{
    NativeCirculationConfiguration, NativeCirculationEvent, NativeCirculationSession,
    NativeDiffusionIngress, NativeDiffusionStanding, NativeMorphologyArtifact, NativeWorldFace,
    NativeWorldStage,
};
use num_rational::BigRational as Rat;
use num_traits::{One, Zero};

fn application() -> AthenaAlphaApplication {
    let mut configuration: NativeCirculationConfiguration =
        serde_json::from_str(BASE_CONFIGURATION).expect("configuration");
    configuration.address.receiver = fixture::FIXTURE_RECEIVER;
    AthenaAlphaApplication::from_dismantling_return(fixture::detached_returned(), configuration)
        .expect("admission")
        .application
}

fn request(application: &AthenaAlphaApplication, occurrence: EventId) -> NativeInferenceRequest {
    let native = application.package().hot().native();
    let (spool, thread) = native
        .spools
        .iter()
        .flat_map(|spool| spool.threads.iter().map(move |thread| (spool, thread)))
        .find(|(_, thread)| {
            thread
                .occurrences
                .iter()
                .any(|candidate| candidate.occurrence == occurrence)
        })
        .expect("addressed occurrence");
    addressed_ingress(
        spool.address.clone(),
        thread.address.clone(),
        occurrence,
        fixture::FIXTURE_RECEIVER,
    )
}

fn dispatch(request_id: u64, command: AbiCommand) -> AbiResponse {
    let envelope = AbiEnvelope {
        schema: HOLONICS_CIRCULATION_ABI_SCHEMA.to_owned(),
        request_id,
        command,
    };
    serde_json::from_slice(&dispatch_bytes(
        &serde_json::to_vec(&envelope).expect("request wire"),
    ))
    .expect("response wire")
}

#[test]
fn exact_alpha_matrix_returns_the_complete_dynamic_lifecycle() {
    let application = application();
    let base_snapshot = application.snapshot().expect("base snapshot");
    let base_package = base_snapshot.package_wire.clone();

    // 1--3. One package boundary, plural ingress, and exact actual-successor lineage.
    let first_request = request(&application, EventId(1));
    let first = application
        .conduct(first_request.clone())
        .expect("first boundary");
    assert_eq!(first.actual_successors.len(), 1);
    assert_eq!(first.actual_successors[0].address.occurrence, EventId(2));
    let second = application
        .continue_from(&first, &first.actual_successors[0].address)
        .expect("actual continuation");
    assert_eq!(second.lineage.predecessor, Some(EventId(1)));
    let independent_before = application
        .conduct(request(&application, EventId(3)))
        .expect("independent before");

    // 7. Decline is exact and leaves the same package owner.
    let before_decline = application
        .package()
        .canonical_bytes()
        .expect("before decline");
    let (application, declined) = application.decline(&first).expect("decline");
    assert!(declined.morphology_unchanged);
    assert_eq!(
        application
            .package()
            .canonical_bytes()
            .expect("after decline"),
        before_decline
    );

    // 4--5. A genuinely later return changes only its causal cone and survives remount.
    let first = application
        .conduct(request(&application, EventId(1)))
        .expect("commit boundary");
    let faces = first
        .issued_world_faces()
        .into_iter()
        .map(|issued| {
            NativeWorldFace::report(
                issued.clone(),
                true,
                issued.support().clone(),
                b"alpha-matrix-world-admitted".to_vec(),
            )
            .expect("world face")
        })
        .collect();
    let NativeWorldStage::Candidate { candidate, .. } = application
        .stage_world_return(&first, faces, EventId(100))
        .expect("world stage")
    else {
        panic!("the complete admitted family must stage a candidate")
    };
    let (application, commit) = application.commit(candidate).expect("commit");
    assert_eq!(commit.predecessor_lineage.generation, 0);
    assert_eq!(commit.successor_lineage.generation, 1);
    assert_eq!(commit.returned_occurrence, EventId(100));
    assert!(!commit.causal_cone.is_empty());
    assert!(commit.interchange_population > 0);
    let independent_after = application
        .conduct(request(&application, EventId(3)))
        .expect("independent after");
    assert_eq!(independent_after.emission, independent_before.emission);
    assert_eq!(independent_after.lineage, independent_before.lineage);
    assert_eq!(independent_after.futures, independent_before.futures);

    let later_request = request(&application, EventId(100));
    let later = application
        .conduct(later_request.clone())
        .expect("later cultivated conduct");
    let generation_one = application
        .package()
        .canonical_bytes()
        .expect("generation one");
    let snapshot = application.snapshot().expect("snapshot");
    let remounted = AthenaAlphaApplication::remount(
        life::native_intelligence::NativeCirculationSnapshot::read(
            &snapshot.canonical_bytes().expect("snapshot wire"),
        )
        .expect("snapshot read"),
    )
    .expect("remount");
    assert_eq!(remounted.generation(), 1);
    assert_eq!(
        remounted.conduct(later_request).expect("remounted conduct"),
        later
    );

    // 8. Discrete and exact diffusive conduct share the neutral event family.
    let native = remounted.package().hot().native();
    let spool = &native.spools[0];
    let diffusion = declared_diffusion_law(
        native,
        &spool.address,
        spool
            .native_population
            .iter()
            .map(|native| (*native, Rat::one()))
            .collect(),
        spool
            .threads
            .iter()
            .flat_map(|thread| &thread.incidence)
            .map(|term| (term.occurrence, Rat::one()))
            .collect(),
        spool.native_population.clone(),
    )
    .expect("diffusion law");
    let first_native = *spool.native_population.iter().next().expect("native");
    let standing = NativeDiffusionStanding {
        content: spool
            .native_population
            .iter()
            .map(|native| {
                (
                    *native,
                    if *native == first_native {
                        Rat::one()
                    } else {
                        Rat::zero()
                    },
                )
            })
            .collect(),
    };
    let NativeCirculationEvent::ConstitutedDiffusion(diffusive) = remounted
        .diffuse(
            &diffusion,
            &standing,
            NativeDiffusionIngress {
                occurrence: EventId(200),
                interval: Rat::one(),
                source: BTreeMap::new(),
            },
        )
        .expect("diffusive event")
    else {
        panic!("diffusive event kind");
    };
    assert!(diffusive.receipt.conservation_residual.is_zero());
    assert!(diffusive
        .receipt
        .balances
        .iter()
        .all(|balance| balance.exact_residual.is_zero()));
    assert!(matches!(
        remounted
            .conduct_event(request(&remounted, EventId(3)))
            .expect("addressed event"),
        NativeCirculationEvent::AddressedSuccessor(_)
    ));

    // 6 and 9. Exact withdrawal/replay and snapshot/remount preserve both generations.
    let (predecessor, replayable) = remounted.withdraw_last_commit().expect("withdraw commit");
    assert_eq!(predecessor.generation(), 0);
    assert_eq!(
        predecessor
            .package()
            .canonical_bytes()
            .expect("withdrawn package"),
        base_package
    );
    let replayed = predecessor
        .replay_commit(replayable)
        .expect("replay commit");
    assert_eq!(
        replayed
            .package()
            .canonical_bytes()
            .expect("replayed package"),
        generation_one
    );

    // 10--11. Direct and ABI conduct agree at the complete configuration.
    let direct = NativeCirculationSession::mount(
        NativeMorphologyArtifact::read(&base_snapshot.package_wire).expect("direct package"),
        base_snapshot.configuration.clone(),
    )
    .expect("direct session");
    let direct_boundary = direct
        .conduct(first_request.clone())
        .expect("direct boundary");
    let AbiDisposition::Opened { handle, .. } = dispatch(
        1,
        AbiCommand::Open {
            package_wire: base_snapshot.package_wire,
            configuration: base_snapshot.configuration,
        },
    )
    .disposition
    else {
        panic!("ABI open");
    };
    let AbiDisposition::Boundary { boundary } = dispatch(
        2,
        AbiCommand::Conduct {
            handle,
            request: first_request,
        },
    )
    .disposition
    else {
        panic!("ABI boundary");
    };
    assert_eq!(boundary, direct_boundary);
    assert!(!boundary.configuration.ingress_aperture.is_empty());
    assert!(!boundary.configuration.continuation_receiver.is_empty());
    assert!(!boundary.configuration.world_return_law.is_empty());
    assert!(!boundary.configuration.emission_codec.is_empty());
    assert!(!boundary.configuration.apparatus.is_empty());
    assert!(matches!(
        dispatch(3, AbiCommand::Close { handle }).disposition,
        AbiDisposition::Closed { .. }
    ));

    // 12. Structural grades are attached to caused returns, not an expected surface. The declared
    // body's shared generator is active at states 0 and 1, so the admitted face family reaches
    // states 0, 1 and 4; the detached winding over states 2 and 3 stays outside the cone.
    assert_eq!(commit.causal_cone.len(), 3);
    assert_eq!(commit.reconstruction_fibre_population, 1);
    assert!(!later.futures.is_empty());
}
