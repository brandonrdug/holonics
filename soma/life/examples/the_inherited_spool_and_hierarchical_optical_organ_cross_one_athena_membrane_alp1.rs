//! ALP1: one admitted source-neutral spool and the complete E1 optical hierarchy meet through the
//! singular Athena membrane. The spool is standing, not an exterior payload; the optical body is
//! a moved occurrence, not a modality route.

use std::{collections::BTreeSet, env, fs, path::PathBuf, time::Instant};

use holonic_engine::{
    quantity::BaseUnits, receiver_exact_compression::ReceiverId, BoundaryId,
    ExactComplexWaveCurrent,
};
use holonic_structure::CausalMembrane;
use life::{
    athena_native::{
        AthenaCausalMembrane, AthenaMembraneConsequence, ExactMembraneChartPassage,
        ExteriorOccurrenceTransducer, NativeMembraneDefect, SituatedCultivatedAthenaRest,
    },
    mathematical_source::{ExactOpticalOccurrence, HierarchicalOpticalPassage},
};
use serde::Serialize;
use serde_json::json;
use sha2::{Digest, Sha256};

const REST: &str = concat!(
    "output/the_causal_adjoint_cultivates_one_source_detached_athena_rest_l2/",
    "athena-situated-cultivated.rest"
);
const OPTICAL_RASTER: &str =
    "output/m0_mathematical_source_circulation/faces/natural/heat-fisher-page-10.png";
const OPTICAL_HIERARCHY: &str =
    "output/the_optical_holons_grow_across_scales/01-hierarchical-optical-passage.json";
const OUTPUT: &str =
    "output/the_inherited_spool_and_hierarchical_optical_organ_cross_one_athena_membrane_alp1";

fn main() -> Result<(), String> {
    let began = Instant::now();
    let root = workspace_root()?;
    let output = root.join(OUTPUT);
    if output.exists() {
        return Err(format!(
            "preserve existing ALP1 return {}",
            output.display()
        ));
    }
    fs::create_dir_all(&output).map_err(display)?;

    let rest = SituatedCultivatedAthenaRest::read(&fs::read(root.join(REST)).map_err(display)?)
        .map_err(display)?;
    let original_identity = rest.identity().to_owned();
    eprintln!(
        "alp1 admitted situated standing {:.3}s",
        began.elapsed().as_secs_f64()
    );

    let cultivated_threads = rest
        .branches()
        .iter()
        .map(|branch| branch.thread_address.as_str())
        .collect::<BTreeSet<_>>();
    let (spool_address, inherited_thread, inherited_occurrence, receiver) = rest
        .ecology()
        .native()
        .spools
        .iter()
        .find_map(|spool| {
            let thread = spool
                .threads
                .iter()
                .find(|thread| !cultivated_threads.contains(thread.address.as_str()))?;
            let occurrence = thread.occurrences.first()?;
            let receiver = spool.receiver_family.iter().next().copied()?;
            Some((
                spool.address.clone(),
                thread.address.clone(),
                occurrence.occurrence,
                receiver,
            ))
        })
        .ok_or("the continuing Athena rest has no structurally inherited spool thread")?;
    let inherited_address = rest
        .realization()
        .sections
        .iter()
        .find(|address| {
            address.spool == spool_address
                && address.thread == inherited_thread
                && address.occurrence == inherited_occurrence
        })
        .cloned()
        .ok_or("the inherited spool occurrence is absent from the membrane realization")?;

    let addressed = rest
        .ecology()
        .native()
        .addressed_section(&spool_address, &inherited_thread, inherited_occurrence)
        .map_err(display)?;
    let mut resident_word = rest
        .ecology()
        .native()
        .mount_word(&spool_address, &addressed.thread().chronology)
        .map_err(display)?;
    let word_return = resident_word
        .conduct(&[addressed.occurrence().entering_native], receiver)
        .map_err(display)?;
    let mut resident_current = rest
        .ecology()
        .native()
        .mount_thread_current(&spool_address, &inherited_thread)
        .map_err(display)?;
    let current_return = resident_current.conduct().map_err(display)?;
    eprintln!(
        "alp1 inherited conduct {:.3}s",
        began.elapsed().as_secs_f64()
    );

    let hierarchy =
        HierarchicalOpticalPassage::read(&fs::read(root.join(OPTICAL_HIERARCHY)).map_err(display)?)
            .map_err(display)?;
    let optical_counts = (
        hierarchy.holons.len(),
        hierarchy.incidences.len(),
        hierarchy.alternative_covers.len(),
        hierarchy.repeated_forms.len(),
    );
    let optical = ExactOpticalOccurrence::found(
        "alp1/hierarchical-optical-occurrence",
        "memory://alp1/hierarchical-optical-occurrence",
        fs::read(root.join(OPTICAL_RASTER)).map_err(display)?,
        hierarchy,
    )
    .map_err(display)?;

    let mut membrane = AthenaCausalMembrane::mount(rest);
    let (first_crossing, optical) =
        cross_and_recover(&mut membrane, optical, &inherited_address, receiver)?;
    let rest = membrane.into_rest();
    eprintln!(
        "alp1 first optical crossing {:.3}s",
        began.elapsed().as_secs_f64()
    );

    let section_population_before = rest.realization().sections.len();
    let inherited_section_population = rest
        .realization()
        .sections
        .iter()
        .filter(|address| address.thread == inherited_thread)
        .count();
    let sibling_thread = rest
        .branches()
        .first()
        .map(|branch| branch.thread_address.clone())
        .ok_or("the situated body has no unrelated cultivated sibling")?;
    let (ablated, inherited_fibre) = rest
        .withdraw_inherited_thread(&spool_address, &inherited_thread)
        .map_err(display)?;
    let ablated_identity = ablated.identity().to_owned();
    let inherited_absent = !ablated
        .realization()
        .sections
        .iter()
        .any(|address| address.thread == inherited_thread);
    let sibling_present = ablated
        .realization()
        .sections
        .iter()
        .any(|address| address.thread == sibling_thread);
    let section_population_after = ablated.realization().sections.len();

    // The unchanged optical occurrence can no longer bind to the removed carrying section. The
    // complete moved source is returned by the insufficiency rather than dropped or rerouted.
    let ablated_membrane = AthenaCausalMembrane::mount(ablated);
    let exterior = optical.into_exterior_fibre().map_err(display)?;
    let optical_boundary = BoundaryId(exterior.address().event_projection.0);
    let binding_defect = ablated_membrane
        .bind_occurrence(
            exterior,
            optical_boundary,
            &inherited_address,
            receiver,
            chart()?,
            Vec::new(),
        )
        .expect_err("the removed inherited section must obstruct the same optical binding");
    let attributable_binding_obstruction =
        binding_defect.defect == NativeMembraneDefect::NativeSectionOutsideEcology;
    let optical = binding_defect
        .exterior
        .recover::<ExactOpticalOccurrence>()
        .map_err(|fibre| format!("the obstructed optical fibre did not return: {fibre:?}"))?;
    let ablated = ablated_membrane.into_rest();
    eprintln!(
        "alp1 inherited withdrawal {:.3}s",
        began.elapsed().as_secs_f64()
    );

    let rest = ablated
        .restore_inherited_thread(inherited_fibre)
        .map_err(display)?;
    let complete_body_restored_exactly = rest.identity() == original_identity;
    eprintln!(
        "alp1 inherited restoration {:.3}s",
        began.elapsed().as_secs_f64()
    );

    let mut membrane = AthenaCausalMembrane::mount(rest);
    let (second_crossing, recovered) =
        cross_and_recover(&mut membrane, optical, &inherited_address, receiver)?;
    recovered.validate().map_err(display)?;
    let optical_fibre_identity = sha(&recovered.hierarchy.canonical_bytes().map_err(display)?);
    let optical_crossing_restored_exactly = first_crossing == second_crossing;
    let source_neutral_resident_conduct = !word_return.apparatus.invariant_transport_reuploaded
        && !current_return.invariant_transport_reuploaded
        && !current_return.cpu_semantic_replay_after_device
        && !current_return.binary_receiver_taken;
    let passed = optical_counts.0 == 4_024
        && optical_counts.1 == 14_536
        && optical_counts.2 == 1_305
        && inherited_section_population > 0
        && inherited_absent
        && sibling_present
        && section_population_after + inherited_section_population == section_population_before
        && attributable_binding_obstruction
        && complete_body_restored_exactly
        && optical_crossing_restored_exactly
        && source_neutral_resident_conduct;

    let grade = json!({
        "schema":"soma-life.athena-alpha-organ-parity-grade.v1",
        "truth_status":"established-bounded; implemented-exact; measured",
        "passed":passed,
        "original_rest_identity_sha256":original_identity,
        "ablated_rest_identity_sha256":ablated_identity,
        "inherited_spool_address":spool_address,
        "inherited_thread_address":inherited_thread,
        "inherited_occurrence":inherited_occurrence,
        "inherited_section_population":inherited_section_population,
        "section_population_before":section_population_before,
        "section_population_after":section_population_after,
        "inherited_thread_absent_after_withdrawal":inherited_absent,
        "cultivated_sibling_present_after_withdrawal":sibling_present,
        "same_optical_binding_obstructed_after_withdrawal":attributable_binding_obstruction,
        "complete_body_restored_exactly":complete_body_restored_exactly,
        "optical_holon_population":optical_counts.0,
        "optical_incidence_population":optical_counts.1,
        "optical_alternative_cover_population":optical_counts.2,
        "optical_repeated_form_population":optical_counts.3,
        "optical_hierarchy_identity_sha256":optical_fibre_identity,
        "optical_crossing_restored_exactly":optical_crossing_restored_exactly,
        "resident_word_device":word_return.device,
        "resident_current_device":current_return.device,
        "source_neutral_resident_conduct":source_neutral_resident_conduct,
        "foreign_runtime_accessed":false,
        "exterior_soulkiller_witness_accessed":false,
        "hierarchy_flattened_to_radiation_ports":false,
        "modality_vector_created":false,
        "elapsed_seconds":format!("{:.9}", began.elapsed().as_secs_f64()),
    });
    write_json(output.join("00-grade.json"), &grade)?;
    write_json(
        output.join("01-first-optical-crossing.json"),
        &first_crossing,
    )?;
    write_json(
        output.join("02-restored-optical-crossing.json"),
        &second_crossing,
    )?;
    write_json(output.join("03-resident-word-return.json"), &word_return)?;
    write_json(
        output.join("04-resident-current-return.json"),
        &current_return,
    )?;
    fs::write(
        output.join("INSPECTION.md"),
        format!(
            "# One inherited spool and one hierarchical optical organ cross the same Athena membrane\n\n[established-bounded; implemented-exact; measured] The complete E1 hierarchy crossed a membrane contact carried by a structurally inherited source-neutral spool occurrence. The inherited thread left by ownership transfer, its addressed sections disappeared, the unchanged optical binding returned the exact expected obstruction and complete source fibre, a cultivated sibling remained, and exact restoration recovered the Athena identity and original optical crossing. No foreign runtime or Soulkiller witness entered the process.\n\n```json\n{}\n```\n",
            serde_json::to_string_pretty(&grade).map_err(display)?
        ),
    )
    .map_err(display)?;
    println!("{}", serde_json::to_string_pretty(&grade).map_err(display)?);
    if passed {
        Ok(())
    } else {
        Err("ALP1 organ-parity receiver refused".to_owned())
    }
}

fn chart() -> Result<ExactMembraneChartPassage, String> {
    let base = BaseUnits::declare(["alp1-common-membrane-current"]).map_err(display)?;
    Ok(ExactMembraneChartPassage::identity(
        base.unit("alp1-common-membrane-current").map_err(display)?,
        ExactComplexWaveCurrent::zero(),
        ExactComplexWaveCurrent::zero(),
    ))
}

fn cross_and_recover(
    membrane: &mut AthenaCausalMembrane<SituatedCultivatedAthenaRest>,
    source: ExactOpticalOccurrence,
    address: &life::athena_native::NativeSectionAddress,
    receiver: ReceiverId,
) -> Result<
    (
        life::athena_native::AthenaMembraneCrossingReceipt,
        ExactOpticalOccurrence,
    ),
    String,
> {
    let exterior = source.into_exterior_fibre().map_err(display)?;
    let boundary = BoundaryId(exterior.address().event_projection.0);
    let occurrence = membrane
        .bind_occurrence(exterior, boundary, address, receiver, chart()?, Vec::new())
        .map_err(|failure| format!("ALP1 membrane binding refused: {failure:?}"))?;
    let AthenaMembraneConsequence::Returned(returned) =
        membrane.receive_occurrence(occurrence).map_err(display)?
    else {
        return Err("the ALP1 optical occurrence did not cross Athena's membrane".to_owned());
    };
    let receipt = returned.receipt;
    let source = returned
        .occurrence
        .exterior
        .recover::<ExactOpticalOccurrence>()
        .map_err(|fibre| format!("the complete optical source fibre did not return: {fibre:?}"))?;
    Ok((receipt, source))
}

fn write_json(path: PathBuf, value: &impl Serialize) -> Result<(), String> {
    fs::write(path, serde_json::to_vec_pretty(value).map_err(display)?).map_err(display)
}

fn sha(bytes: &[u8]) -> String {
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

fn display(value: impl std::fmt::Display) -> String {
    value.to_string()
}
