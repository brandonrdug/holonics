use std::collections::BTreeSet;

use athena_alpha::{addressed_ingress, inspect_cycle, BASE_CONFIGURATION};
use holonic_engine::{
    native_ecology::holonic_intelligence::{
        Bf16ExcitationDismantling, ExteriorModality, ForeignBf16Excitation,
    },
    receiver_exact_compression::ReceiverId,
    soulkiller::dismantle,
    BoundaryId, EventId,
};
use life::native_intelligence::{
    NativeCirculationConfiguration, NativeWorldFace, NativeWorldStage,
};

fn excitation(event: u64, entering: u16, returned: u16) -> ForeignBf16Excitation {
    ForeignBf16Excitation {
        event: EventId(event),
        predecessor: None,
        entering_boundary: BoundaryId(event * 2),
        emitting_boundary: BoundaryId(event * 2 + 1),
        source_occurrence: format!("cold/{event}"),
        exterior_modality: ExteriorModality::Text,
        entering_codewords: vec![entering],
        returned_codewords: vec![returned],
        interventions: BTreeSet::from([format!("intervention/{event}")]),
        receiver_consequences: BTreeSet::from([format!("consequence/{event}")]),
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let configuration: NativeCirculationConfiguration = serde_json::from_str(BASE_CONFIGURATION)?;
    let returned = dismantle(Bf16ExcitationDismantling {
        receiver: ReceiverId(7),
        excitations: vec![excitation(1, 0x3f80, 0x4000), excitation(2, 0x4040, 0x4080)],
    })?;
    let admission =
        athena_alpha::AthenaAlphaApplication::from_dismantling_return(returned, configuration)?;
    let application = admission.application;
    let native = application.package().hot().native();
    let request = addressed_ingress(
        native.spools[0].address.clone(),
        native.spools[0].threads[0].address.clone(),
        EventId(1),
        ReceiverId(7),
    );
    let boundary = application.conduct(request)?;
    let faces = boundary
        .issued_world_faces()
        .into_iter()
        .map(|issued| {
            NativeWorldFace::report(
                issued.clone(),
                true,
                issued.support().clone(),
                b"alpha-cycle-world-admitted".to_vec(),
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    let NativeWorldStage::Candidate { candidate, .. } =
        application.stage_world_return(&boundary, faces, EventId(100))?
    else {
        return Err("the alpha-cycle world return was obstructed".into());
    };
    let (application, commit) = application.commit(candidate)?;
    let later = addressed_ingress(
        commit.source.spool.clone(),
        commit.deposit_receipt.thread_address.clone(),
        commit.returned_occurrence,
        ReceiverId(7),
    );
    let later_boundary = application.conduct(later)?;
    let snapshot = application.snapshot()?;
    let application = athena_alpha::AthenaAlphaApplication::remount(
        life::native_intelligence::NativeCirculationSnapshot::read(&snapshot.canonical_bytes()?)?,
    )?;
    let remount_generation = application.generation();
    assert_eq!(remount_generation, 1);
    let receipt = inspect_cycle(&commit, later_boundary, &snapshot, remount_generation);
    println!("{}", serde_json::to_string_pretty(&receipt)?);
    Ok(())
}
