//! MEM5 receiver: three ordinary exterior occurrences perturb one returned Athena body, native
//! GPU radiation returns first, and only then does the cold codec render the frozen participant
//! receiver fibre.

use std::{env, fs, path::PathBuf};

use holonic_engine::{
    quantity::{BaseUnits, Dimension},
    receiver_exact_compression::ReceiverId,
    BoundaryId, ExactUnitConicPhase,
};
use holonic_structure::CausalMembrane;
use life::athena_native::{
    AddressedMaterialOccurrence, AdmittedReturnedAffineLaboratoryRestWitness, AthenaCausalMembrane,
    AthenaMembraneConsequence, AthenaMembraneStanding, ExactMembraneChartPassage,
    ExteriorActionCurrent, ExteriorOccurrenceTransducer, ExteriorRadiationSurface,
    NativeRadiationAperture, NativeRadiationSection, ReturnedAffineLaboratoryAthenaRest,
};
use num_bigint::BigInt;
use num_rational::BigRational as Rat;
use serde::Serialize;

const REST: &str = concat!(
    "output/the_returned_membrane_action_cultivates_one_source_detached_athena_rest_mem4/",
    "athena-returned-membrane-cultivated.rest"
);
const REST_WIRE_SHA256: &str = "646401462284e6782aaa43139202c3bd5e45043e174b414e4fe851ec92f4e2ad";
const REST_IDENTITY_SHA256: &str =
    "63c9ff122e50fe94efe9bb00fea66e9eaac606c47707d07bc69301449bb9aded";
const VALIDATION_RECEIPT_SHA256: &str =
    "3ab826fb8512aae85096193ce103a384092111e8f26836415b0e1dc7eba02178";
const OUTPUT: &str =
    "output/the_native_radiation_precedes_three_inferred_participant_surfaces_mem5";

#[derive(Serialize)]
#[serde(deny_unknown_fields)]
struct Mem5Grade {
    truth_status: &'static str,
    evidence_tags: [&'static str; 2],
    aperture: NativeRadiationAperture,
    native_sections: Vec<NativeRadiationSection>,
    surfaces: Vec<ExteriorRadiationSurface>,
    three_distinct_request_currents: bool,
    three_distinct_native_successors: bool,
    three_distinct_surfaces: bool,
    participant_fibre_rendered_without_search: bool,
    receiver_projection_faithful: bool,
    native_radiation_preceded_rendering: bool,
    target_withdrawal_changed_response: bool,
    restoration_recovered_response: bool,
    lawful_phase_rebase_commuted: bool,
    internal_deed_or_semantic_mode_present: bool,
    query_selected_cultivation_or_topology: bool,
    open_exterior: Vec<String>,
}

fn main() -> Result<(), String> {
    let root = workspace_root()?;
    let witness = admitted_witness()?;
    let rest = ReturnedAffineLaboratoryAthenaRest::read_admitted(
        &fs::read(root.join(REST)).map_err(display)?,
        &witness,
    )
    .map_err(display)?;

    // The receiver is frozen before any target request is materialized below.
    let aperture = NativeRadiationAperture::found(&rest).map_err(display)?;
    let (native_address, receiver) = continuing_native_address(&rest)?;
    let base = BaseUnits::declare(["athena-exterior-action"]).map_err(display)?;
    let dimension = base.unit("athena-exterior-action").map_err(display)?;
    let mut membrane = AthenaCausalMembrane::mount(rest)
        .constitute_interior()
        .map_err(display)?
        .mount_resident_interior()
        .map_err(display)?;

    let requests = [
        ("mem5/request/describe", "Describe Brandon."),
        ("mem5/request/identify", "Identify Brandon."),
        (
            "mem5/request/infer",
            "What can be inferred about Brandon from the laboratory's continuing history?",
        ),
    ];
    let mut exterior_currents = Vec::new();
    let mut native_sections = Vec::new();
    for (occurrence, text) in requests {
        let exterior =
            ExteriorActionCurrent::transduce(occurrence, text.as_bytes()).map_err(display)?;
        let section = conduct_request(
            &mut membrane,
            &aperture,
            &native_address,
            receiver,
            &dimension,
            text.as_bytes(),
            exterior.clone(),
        )?;
        exterior_currents.push(exterior.current.clone());
        native_sections.push(section);
    }

    // A quarter-turn chart presents the identical third request.  Pulling the returned radiation
    // back by the inverse quarter-turn must recover the unrebased native section exactly.
    let rebase_source =
        ExteriorActionCurrent::transduce("mem5/request/infer-rebased", requests[2].1.as_bytes())
            .map_err(display)?;
    let phase = ExactUnitConicPhase::new(rat(0), rat(1)).map_err(display)?;
    let rebased_return = conduct_rebased_request(
        &mut membrane,
        &aperture,
        &native_address,
        receiver,
        &dimension,
        requests[2].1.as_bytes(),
        &rebase_source,
        &phase,
    )?;
    let pulled_back = rebased_return.returned_radiation.rotate(&rat(0), &rat(-1));
    let lawful_phase_rebase_commuted = pulled_back == native_sections[2].returned_radiation
        && rebased_return.native_radiation == native_sections[2].native_radiation;

    let rest = membrane.into_rest();
    let surfaces = native_sections
        .iter()
        .cloned()
        .map(|section| section.render(&rest, &aperture).map_err(display))
        .collect::<Result<Vec<_>, _>>()?;

    let three_distinct_request_currents = exterior_currents
        .iter()
        .collect::<std::collections::BTreeSet<_>>()
        .len()
        == exterior_currents.len();
    let three_distinct_native_successors = native_sections
        .iter()
        .map(|section| section.identity_sha256.as_str())
        .collect::<std::collections::BTreeSet<_>>()
        .len()
        == native_sections.len();
    let three_distinct_surfaces = surfaces
        .iter()
        .map(|surface| surface.text_sha256.as_str())
        .collect::<std::collections::BTreeSet<_>>()
        .len()
        == surfaces.len();
    let participant_fibre_rendered_without_search =
        surfaces
            .iter()
            .zip(&native_sections)
            .all(|(surface, section)| {
                !surface.rendered_cell_addresses.is_empty()
                    && surface.rendered_cell_addresses == section.emitted_relational_cell_addresses
                    && !surface.candidate_search_performed
                    && !surface.stored_sentence_selected
                    && !surface.expected_answer_consulted
            });
    let receiver_projection_faithful =
        surfaces
            .iter()
            .zip(&native_sections)
            .all(|(surface, section)| {
                let Some(chart) = aperture.participant_receiver_charts.iter().find(|chart| {
                    chart.identity_sha256 == section.participant_receiver_chart_identity_sha256
                }) else {
                    return false;
                };
                let returned = surface.text.to_lowercase();
                chart
                    .receiver_region
                    .iter()
                    .all(|face| returned.contains(&face.to_lowercase()))
            });
    let native_radiation_preceded_rendering = native_sections
        .iter()
        .all(|section| section.renderer_has_not_run);

    // Targeted ablation removes the returned situated passage, not a query-selected relation.
    let baseline = native_sections[0].clone();
    let (predecessor, withdrawal) = rest.withdraw_returned_difference().map_err(display)?;
    let predecessor_aperture =
        NativeRadiationAperture::found_predecessor(&predecessor).map_err(display)?;
    let (predecessor_address, predecessor_receiver) = continuing_native_address(&predecessor)?;
    let mut predecessor_membrane = AthenaCausalMembrane::mount(predecessor)
        .constitute_interior()
        .map_err(display)?
        .mount_resident_interior()
        .map_err(display)?;
    let baseline_exterior =
        ExteriorActionCurrent::transduce(requests[0].0, requests[0].1.as_bytes())
            .map_err(display)?;
    let ablated = conduct_request(
        &mut predecessor_membrane,
        &predecessor_aperture,
        &predecessor_address,
        predecessor_receiver,
        &dimension,
        requests[0].1.as_bytes(),
        baseline_exterior.clone(),
    )?;
    let target_withdrawal_changed_response = ablated.native_radiation != baseline.native_radiation
        || ablated.returned_radiation != baseline.returned_radiation;
    let predecessor = predecessor_membrane.into_rest();
    let restored =
        ReturnedAffineLaboratoryAthenaRest::restore_returned_difference(predecessor, withdrawal)
            .map_err(display)?;
    let restored_aperture = NativeRadiationAperture::found(&restored).map_err(display)?;
    let (restored_address, restored_receiver) = continuing_native_address(&restored)?;
    let mut restored_membrane = AthenaCausalMembrane::mount(restored)
        .constitute_interior()
        .map_err(display)?
        .mount_resident_interior()
        .map_err(display)?;
    let restored_section = conduct_request(
        &mut restored_membrane,
        &restored_aperture,
        &restored_address,
        restored_receiver,
        &dimension,
        requests[0].1.as_bytes(),
        baseline_exterior,
    )?;
    let restoration_recovered_response = restored_section == baseline;

    let internal_deed_or_semantic_mode_present = aperture.deed_or_semantic_mode_supplied;
    let query_selected_cultivation_or_topology = aperture.target_query_was_visible_when_frozen;
    if !three_distinct_request_currents
        || !three_distinct_native_successors
        || !three_distinct_surfaces
        || !participant_fibre_rendered_without_search
        || !receiver_projection_faithful
        || !native_radiation_preceded_rendering
        || !target_withdrawal_changed_response
        || !restoration_recovered_response
        || !lawful_phase_rebase_commuted
        || internal_deed_or_semantic_mode_present
        || query_selected_cultivation_or_topology
    {
        return Err(format!(
            "MEM5 refused: currents={three_distinct_request_currents}, native={three_distinct_native_successors}, surfaces={three_distinct_surfaces}, fibre={participant_fibre_rendered_without_search}, receiver={receiver_projection_faithful}, order={native_radiation_preceded_rendering}, ablation={target_withdrawal_changed_response}, restoration={restoration_recovered_response}, rebase={lawful_phase_rebase_commuted}, mode={internal_deed_or_semantic_mode_present}, query_route={query_selected_cultivation_or_topology}"
        ));
    }
    let grade = Mem5Grade {
        truth_status: "established-bounded",
        evidence_tags: ["implemented-exact", "measured"],
        aperture,
        native_sections,
        surfaces,
        three_distinct_request_currents,
        three_distinct_native_successors,
        three_distinct_surfaces,
        participant_fibre_rendered_without_search,
        receiver_projection_faithful,
        native_radiation_preceded_rendering,
        target_withdrawal_changed_response,
        restoration_recovered_response,
        lawful_phase_rebase_commuted,
        internal_deed_or_semantic_mode_present,
        query_selected_cultivation_or_topology,
        open_exterior: vec![
            "MEM5 returns a bounded participant receiver; the complete unchanged cross-codec family remains MEM6"
                .to_owned(),
            "the exterior current is an exact octet-population chart and does not claim universal language transduction"
                .to_owned(),
        ],
    };
    let output = root.join(OUTPUT);
    fs::create_dir_all(&output).map_err(display)?;
    fs::write(
        output.join("00-native-radiation-and-surfaces.json"),
        serde_json::to_vec_pretty(&grade).map_err(display)?,
    )
    .map_err(display)?;
    for (at, surface) in grade.surfaces.iter().enumerate() {
        fs::write(
            output.join(format!("{:02}-surface.md", at + 1)),
            &surface.text,
        )
        .map_err(display)?;
    }
    Ok(())
}

fn conduct_request<Standing: AthenaMembraneStanding>(
    membrane: &mut AthenaCausalMembrane<Standing>,
    aperture: &NativeRadiationAperture,
    address: &life::athena_native::NativeSectionAddress,
    receiver: ReceiverId,
    dimension: &Dimension,
    payload: &[u8],
    exterior: ExteriorActionCurrent,
) -> Result<NativeRadiationSection, String> {
    let source = AddressedMaterialOccurrence::found(
        exterior.occurrence.clone(),
        payload,
        None,
        Vec::new(),
        vec!["later world consequence remains open".to_owned()],
    )
    .map_err(display)?;
    let fibre = source.into_exterior_fibre().map_err(display)?;
    let boundary = BoundaryId(fibre.address().event_projection.0);
    let occurrence = membrane
        .bind_occurrence(
            fibre,
            boundary,
            address,
            receiver,
            ExactMembraneChartPassage::identity(
                dimension.clone(),
                exterior.section.clone(),
                exterior.current.clone(),
            ),
            Vec::new(),
        )
        .map_err(|failure| format!("request binding refused: {failure:?}"))?;
    let AthenaMembraneConsequence::Returned(returned) =
        membrane.receive_occurrence(occurrence).map_err(display)?
    else {
        return Err("the ordinary request did not cross the membrane".to_owned());
    };
    let receipt = returned.receipt.clone();
    returned
        .occurrence
        .exterior
        .recover::<AddressedMaterialOccurrence>()
        .map_err(|fibre| format!("the request source fibre was not exact: {fibre:?}"))?;
    let resident = membrane
        .conduct_resident_interior(
            &aperture.left_contact_cell,
            &aperture.right_contact_cell,
            &exterior.current,
        )
        .map_err(display)?;
    NativeRadiationSection::found(membrane.standing(), aperture, &exterior, &receipt, resident)
        .map_err(display)
}

fn conduct_rebased_request<Standing: AthenaMembraneStanding>(
    membrane: &mut AthenaCausalMembrane<Standing>,
    aperture: &NativeRadiationAperture,
    address: &life::athena_native::NativeSectionAddress,
    receiver: ReceiverId,
    dimension: &Dimension,
    payload: &[u8],
    exterior: &ExteriorActionCurrent,
    phase: &ExactUnitConicPhase,
) -> Result<holonic_engine::cuda_refine::ResidentMembraneInteriorReturn, String> {
    let source = AddressedMaterialOccurrence::found(
        exterior.occurrence.clone(),
        payload,
        None,
        Vec::new(),
        vec!["later world consequence remains open".to_owned()],
    )
    .map_err(display)?;
    let fibre = source.into_exterior_fibre().map_err(display)?;
    let boundary = BoundaryId(fibre.address().event_projection.0);
    let transported_section = exterior.section.rotate(&phase.cosine, &phase.sine);
    let transported_current = exterior.current.rotate(&phase.cosine, &phase.sine);
    let occurrence = membrane
        .bind_occurrence(
            fibre,
            boundary,
            address,
            receiver,
            ExactMembraneChartPassage {
                exterior_dimension: dimension.clone(),
                interior_dimension: dimension.clone(),
                presented_section: exterior.section.clone(),
                presented_current: exterior.current.clone(),
                phase: phase.clone(),
                transported_section,
                transported_current: transported_current.clone(),
            },
            Vec::new(),
        )
        .map_err(|failure| format!("rebased request binding refused: {failure:?}"))?;
    let AthenaMembraneConsequence::Returned(returned) =
        membrane.receive_occurrence(occurrence).map_err(display)?
    else {
        return Err("the rebased request did not cross the membrane".to_owned());
    };
    returned
        .occurrence
        .exterior
        .recover::<AddressedMaterialOccurrence>()
        .map_err(|fibre| format!("the rebased source fibre was not exact: {fibre:?}"))?;
    membrane
        .conduct_resident_interior(
            &aperture.left_contact_cell,
            &aperture.right_contact_cell,
            &transported_current,
        )
        .map_err(display)
}

fn continuing_native_address(
    standing: &impl AthenaMembraneStanding,
) -> Result<(life::athena_native::NativeSectionAddress, ReceiverId), String> {
    for address in &standing.membrane_realization().sections {
        let addressed = standing
            .membrane_ecology()
            .native()
            .addressed_section(&address.spool, &address.thread, address.occurrence)
            .map_err(display)?;
        if addressed.thread().chronology.is_empty() {
            continue;
        }
        if let Some(receiver) = addressed.spool().receiver_family.iter().next().copied() {
            return Ok((address.clone(), receiver));
        }
    }
    Err("the body has no continuing addressed native section".to_owned())
}

fn admitted_witness() -> Result<AdmittedReturnedAffineLaboratoryRestWitness, String> {
    AdmittedReturnedAffineLaboratoryRestWitness::found(
        REST_WIRE_SHA256,
        REST_IDENTITY_SHA256,
        VALIDATION_RECEIPT_SHA256,
    )
    .map_err(display)
}

fn rat(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
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
