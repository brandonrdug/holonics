//! MEM1 receiver: four exterior source bodies cross the same move-owned Athena membrane.

use std::{any::Any, env, fs, path::PathBuf};

use holonic_engine::{
    quantity::BaseUnits, receiver_exact_compression::ReceiverId, BoundaryId,
    ExactComplexWaveCurrent,
};
use holonic_structure::CausalMembrane;
use life::{
    athena_native::{
        AddressedMaterialOccurrence, AdmittedAffineLaboratoryRestWitness,
        AffineLaboratoryCultivatedAthenaRest, AthenaCausalMembrane, AthenaMembraneConsequence,
        AthenaMembraneCrossingReceipt, ExactMembraneChartPassage, ExteriorOccurrenceTransducer,
        MaterialSourceCodec, MaterialSourceRealization, MATERIAL_SOURCE_REALIZATION_SCHEMA,
    },
    mathematical_source::{ExactAcousticOccurrence, HierarchicalOpticalPassage},
};
use serde::Serialize;
use sha2::{Digest, Sha256};

const REST: &str = concat!(
    "output/the_affine_laboratory_returns_one_relational_organ_over_four_cycle_fibres_l5_repair/",
    "athena-affine-laboratory-cultivated.rest"
);
const REST_WIRE_SHA256: &str = "026cbeba471ff00262b0ddc07596d602007fa3c672bb2ab96cafb3a5c0ff7fbc";
const REST_IDENTITY_SHA256: &str =
    "5b9a09396d0924ef1a5499737a1c609d943be38ec0647d394d35d79b7d460b2b";
const VALIDATION_RECEIPT_SHA256: &str =
    "c5220f4b1bfb52eb630f9b269f9688bd79ce35754f1eaa4fda3830faec4093e7";
const OPTICAL: &str =
    "output/the_optical_holons_grow_across_scales/01-hierarchical-optical-passage.json";
const ACOUSTIC: &str =
    "output/the_laboratory_mathematics_athena_unifies_native_inference_ocr_and_three_port_transport/projections/07-exact-notation.wav";
const OUTPUT: &str = "output/the_one_athena_membrane_receives_arbitrary_exterior_occurrences_mem1";

#[derive(Serialize)]
struct MembraneGrade {
    truth_status: &'static str,
    admission_witness: AdmittedAffineLaboratoryRestWitness,
    rest_identity_sha256: String,
    crossing_receipts: Vec<AthenaMembraneCrossingReceipt>,
    exact_source_fibres_recovered: bool,
    one_public_mouth: bool,
    native_contact_derived_from_standing: bool,
    media_enum_in_native_occurrence: bool,
    source_identity_changed_after_crossing: bool,
    open_exterior: Vec<String>,
}

fn main() -> Result<(), String> {
    let root = workspace_root()?;
    let witness = AdmittedAffineLaboratoryRestWitness::found(
        REST_WIRE_SHA256,
        REST_IDENTITY_SHA256,
        VALIDATION_RECEIPT_SHA256,
    )
    .map_err(display)?;
    let rest = AffineLaboratoryCultivatedAthenaRest::read_admitted(
        &fs::read(root.join(REST)).map_err(display)?,
        &witness,
    )
    .map_err(display)?;
    let predecessor_identity = rest.identity().to_owned();
    let address = rest
        .body()
        .realization()
        .sections
        .first()
        .cloned()
        .ok_or_else(|| "the affine body has no addressed native section".to_owned())?;
    let addressed = rest
        .body()
        .ecology()
        .native()
        .addressed_section(&address.spool, &address.thread, address.occurrence)
        .map_err(display)?;
    let receiver: ReceiverId = addressed
        .spool()
        .receiver_family
        .iter()
        .next()
        .copied()
        .ok_or_else(|| "the addressed spool has no dependent receiver".to_owned())?;
    let mut membrane = AthenaCausalMembrane::mount(rest);

    let material = AddressedMaterialOccurrence::found(
        "mem1/exterior/material",
        b"one caused material population",
        None,
        vec!["renamable material delivery".to_owned()],
        vec!["the original material bytes remain an exterior source aperture".to_owned()],
    )
    .map_err(display)?;
    let optical = HierarchicalOpticalPassage::read(&fs::read(root.join(OPTICAL)).map_err(display)?)
        .map_err(display)?;
    let acoustic =
        ExactAcousticOccurrence::read(&root.join(ACOUSTIC), "mem1/exterior/acoustic", 512, 256, 64)
            .map_err(display)?;
    let payload = "pub fn returned_sum(left: i64, right: i64) -> i64 { left + right }\n";
    let code = MaterialSourceRealization {
        schema: MATERIAL_SOURCE_REALIZATION_SCHEMA.to_owned(),
        truth_status: "implemented-exact".to_owned(),
        factorization_occurrence: "mem1/exterior/code".to_owned(),
        native_operation_identity_sha256: sha256(b"disjoint-union-operation"),
        source_boundary_occurrences: vec!["code/source/left".to_owned()],
        target_boundary_occurrences: vec!["code/target/sum".to_owned()],
        codec: MaterialSourceCodec::Rust,
        media_type: "text/x-rust".to_owned(),
        suggested_extension: "rs".to_owned(),
        payload: payload.to_owned(),
        payload_sha256: sha256(payload.as_bytes()),
        payload_octets: payload.len() as u64,
        exterior_codec_routes_native_law: false,
        open_exterior: vec![
            "compiler execution and its world return remain outside this crossing".to_owned(),
        ],
    };

    let mut crossing_receipts = Vec::new();
    crossing_receipts.push(cross::<AddressedMaterialOccurrence>(
        &mut membrane,
        material,
        &address,
        receiver,
    )?);
    crossing_receipts.push(cross::<HierarchicalOpticalPassage>(
        &mut membrane,
        optical,
        &address,
        receiver,
    )?);
    crossing_receipts.push(cross::<ExactAcousticOccurrence>(
        &mut membrane,
        acoustic,
        &address,
        receiver,
    )?);
    crossing_receipts.push(cross::<MaterialSourceRealization>(
        &mut membrane,
        code,
        &address,
        receiver,
    )?);

    let returned_rest = membrane.into_rest();
    let grade = MembraneGrade {
        truth_status: "implemented-exact",
        admission_witness: witness,
        rest_identity_sha256: returned_rest.identity().to_owned(),
        crossing_receipts,
        exact_source_fibres_recovered: true,
        one_public_mouth: true,
        native_contact_derived_from_standing: true,
        media_enum_in_native_occurrence: false,
        source_identity_changed_after_crossing: returned_rest.identity() != predecessor_identity,
        open_exterior: vec![
            "MEM1 founds a common exact mouth; morphology-derived cross-organ contact begins at MEM2"
                .to_owned(),
            "MEM1 does not claim durable cultivation or inferred exterior response".to_owned(),
        ],
    };
    if grade.source_identity_changed_after_crossing || grade.crossing_receipts.len() != 4 {
        return Err("the MEM1 crossing changed standing or lost an exterior family".to_owned());
    }
    let output = root.join(OUTPUT);
    fs::create_dir_all(&output).map_err(display)?;
    fs::write(
        output.join("00-common-membrane-crossings.json"),
        serde_json::to_vec_pretty(&grade).map_err(display)?,
    )
    .map_err(display)?;
    Ok(())
}

fn cross<T: ExteriorOccurrenceTransducer + Any + Send>(
    membrane: &mut AthenaCausalMembrane,
    source: T,
    address: &life::athena_native::NativeSectionAddress,
    receiver: ReceiverId,
) -> Result<AthenaMembraneCrossingReceipt, String> {
    let exterior = source.into_exterior_fibre().map_err(display)?;
    let exterior_boundary = BoundaryId(exterior.address().event_projection.0);
    let base = BaseUnits::declare(["membrane-current"]).map_err(display)?;
    let chart = ExactMembraneChartPassage::identity(
        base.unit("membrane-current").map_err(display)?,
        ExactComplexWaveCurrent::zero(),
        ExactComplexWaveCurrent::zero(),
    );
    let occurrence = membrane
        .bind_occurrence(
            exterior,
            exterior_boundary,
            address,
            receiver,
            chart,
            Vec::new(),
        )
        .map_err(|insufficiency| format!("binding insufficiency: {insufficiency:?}"))?;
    let returned = membrane.receive_occurrence(occurrence).map_err(display)?;
    let AthenaMembraneConsequence::Returned(returned) = returned else {
        return Err(format!("crossing insufficiency: {returned:?}"));
    };
    let receipt = returned.receipt;
    returned
        .occurrence
        .exterior
        .recover::<T>()
        .map_err(|fibre| format!("source fibre did not downcast: {fibre:?}"))?;
    Ok(receipt)
}

fn sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn workspace_root() -> Result<PathBuf, String> {
    let mut path = env::current_dir().map_err(display)?;
    loop {
        if path.join("Cargo.toml").is_file() && path.join("canon").is_dir() {
            return Ok(path);
        }
        if !path.pop() {
            return Err("workspace root not found".to_owned());
        }
    }
}

fn display(error: impl std::fmt::Display) -> String {
    error.to_string()
}
