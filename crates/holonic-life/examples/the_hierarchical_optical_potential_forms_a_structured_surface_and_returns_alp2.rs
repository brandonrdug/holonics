//! ALP2 focused receiver: the admitted E1 hierarchy, rather than the diagnostic radiation-port
//! grid, owns optical space while native Athena radiation transports its sections.

use std::{
    env, fs,
    path::{Path, PathBuf},
    time::Instant,
};

use holonic_engine::{
    cuda_refine::CudaRefineExecutor,
    image::{ExactRaster, ExactRgb, ImageExtent},
    quantity::BaseUnits,
    receiver_exact_compression::ReceiverId,
    BoundaryId, ExactComplexWaveCurrent,
};
use holonic_structure::CausalMembrane;
use image::ImageReader;
use life::{
    mathematical_source::{
        grow_optical_holons, recover_optical_passage, ExactOpticalOccurrence,
        HierarchicalOpticalPassage, OpticalHolonIntervention,
    },
    native_intelligence::{
        ExactMembraneChartPassage, ExteriorOccurrenceTransducer, MembraneConsequence,
        MembraneStanding, NativeCausalMembrane, NativeOpticalPotentialField,
        SituatedCultivatedEcologyRest,
    },
};
use serde::Serialize;
use serde_json::json;
use sha2::{Digest, Sha256};

const REST: &str = concat!(
    ".local/artifacts/the_causal_adjoint_cultivates_one_source_detached_athena_rest_l2/",
    "athena-situated-cultivated.rest"
);
const SOURCE_RASTER: &str =
    ".local/artifacts/m0_mathematical_source_circulation/faces/natural/heat-fisher-page-10.png";
const SOURCE_HIERARCHY: &str =
    ".local/artifacts/the_optical_holons_grow_across_scales/01-hierarchical-optical-passage.json";
const PRIMARY_FIELD: &str = concat!(
    ".local/artifacts/the_athena_radiation_forms_an_optical_field_and_its_image_returns_sens5/",
    "03-primary-native-optical-field.json"
);
const HELD_FIELD: &str = concat!(
    ".local/artifacts/the_athena_radiation_forms_an_optical_field_and_its_image_returns_sens5/",
    "04-held-out-native-optical-field.json"
);
const OUTPUT: &str =
    ".local/artifacts/the_hierarchical_optical_potential_forms_a_structured_surface_and_returns_alp2";

fn main() -> Result<(), String> {
    let began = Instant::now();
    let root = workspace_root()?;
    let output = root.join(OUTPUT);
    if output.exists() {
        return Err(format!(
            "preserve existing ALP2 return {}",
            output.display()
        ));
    }
    fs::create_dir_all(&output).map_err(display)?;

    let hierarchy =
        HierarchicalOpticalPassage::read(&fs::read(root.join(SOURCE_HIERARCHY)).map_err(display)?)
            .map_err(display)?;
    let raster = fs::read(root.join(SOURCE_RASTER)).map_err(display)?;
    let primary: NativeOpticalPotentialField =
        serde_json::from_slice(&fs::read(root.join(PRIMARY_FIELD)).map_err(display)?)
            .map_err(display)?;
    let held: NativeOpticalPotentialField =
        serde_json::from_slice(&fs::read(root.join(HELD_FIELD)).map_err(display)?)
            .map_err(display)?;
    primary.validate().map_err(display)?;
    held.validate().map_err(display)?;

    let primary_formation = primary.form_hierarchical(&hierarchy).map_err(display)?;
    let held_formation = held.form_hierarchical(&hierarchy).map_err(display)?;
    let (primary_png, primary_projection) =
        primary_formation.render_png(&raster).map_err(display)?;
    let (held_png, held_projection) = held_formation.render_png(&raster).map_err(display)?;
    if primary_formation == held_formation || primary_png == held_png {
        return Err("held-out radiation collapsed after hierarchical optical formation".to_owned());
    }
    fs::write(
        output.join("01-primary-hierarchical-formation.png"),
        &primary_png,
    )
    .map_err(display)?;
    fs::write(
        output.join("02-held-out-hierarchical-formation.png"),
        &held_png,
    )
    .map_err(display)?;
    write_json(
        &output.join("03-primary-hierarchical-formation.json"),
        &primary_formation,
    )?;
    write_json(
        &output.join("04-held-out-hierarchical-formation.json"),
        &held_formation,
    )?;
    write_json(
        &output.join("05-primary-projection.json"),
        &primary_projection,
    )?;
    write_json(
        &output.join("06-held-out-projection.json"),
        &held_projection,
    )?;

    // The formed surface returns through the standing raw/hierarchical optical transducer before
    // it meets the singular membrane. Its recovered hierarchy is not an OCR string.
    let mut card = CudaRefineExecutor::new().map_err(display)?;
    let returned_hierarchy = recover_hierarchy(&mut card, &primary_png)?;
    let returned_holon_population = returned_hierarchy.holons.len();
    let returned_incidence_population = returned_hierarchy.incidences.len();
    let returned_alternative_cover_population = returned_hierarchy.alternative_covers.len();
    let returned = ExactOpticalOccurrence::found(
        "alp2/returned-hierarchical-optical-formation",
        "memory://alp2/returned-hierarchical-optical-formation",
        primary_png,
        returned_hierarchy,
    )
    .map_err(display)?;
    let expected_source = returned.source_sha256.clone();
    let expected_hierarchy = sha(&returned.hierarchy.canonical_bytes().map_err(display)?);

    let rest = SituatedCultivatedEcologyRest::read(&fs::read(root.join(REST)).map_err(display)?)
        .map_err(display)?;
    let rested_identity = rest.identity().to_owned();
    let (address, receiver) = continuing_native_address(&rest)?;
    let exterior = returned.into_exterior_fibre().map_err(display)?;
    let boundary = BoundaryId(exterior.address().event_projection.0);
    let dimension = BaseUnits::declare(["alp2-returned-optical-current"])
        .map_err(display)?
        .unit("alp2-returned-optical-current")
        .map_err(display)?;
    let mut membrane = NativeCausalMembrane::mount(rest);
    let occurrence = membrane
        .bind_occurrence(
            exterior,
            boundary,
            &address,
            receiver,
            ExactMembraneChartPassage::identity(
                dimension,
                ExactComplexWaveCurrent::zero(),
                ExactComplexWaveCurrent::zero(),
            ),
            Vec::new(),
        )
        .map_err(|failure| format!("ALP2 returned optical binding refused: {failure:?}"))?;
    let MembraneConsequence::Returned(returned) =
        membrane.receive_occurrence(occurrence).map_err(display)?
    else {
        return Err(
            "the formed optical surface did not return through Athena's membrane".to_owned(),
        );
    };
    let recovered = returned
        .occurrence
        .exterior
        .recover::<ExactOpticalOccurrence>()
        .map_err(|_| "the formed optical surface lost its complete fibre".to_owned())?;
    let complete_returned_fibre = recovered.source_sha256 == expected_source
        && sha(&recovered.hierarchy.canonical_bytes().map_err(display)?) == expected_hierarchy;
    let rest = membrane.into_rest();
    let rest_unchanged_before_physical_cultivation = rest.identity() == rested_identity;

    let passed = primary_formation.source_holon_population == hierarchy.holons.len()
        && primary_formation.source_incidence_population == hierarchy.incidences.len()
        && primary_formation.source_alternative_cover_population
            == hierarchy.alternative_covers.len()
        && primary_formation.source_repeated_form_population == hierarchy.repeated_forms.len()
        && primary_formation.complete_source_hierarchy_fibre_retained
        && !primary_formation.rectangular_port_lattice_used_as_optical_space
        && !primary_formation.source_transcript_used
        && primary_projection.complete_formation_fibre_retained
        && held_projection.complete_formation_fibre_retained
        && primary_projection.png_sha256 != held_projection.png_sha256
        && returned_holon_population > 0
        && returned_incidence_population > 0
        && returned_alternative_cover_population > 0
        && complete_returned_fibre
        && rest_unchanged_before_physical_cultivation;
    let grade = json!({
        "schema":"soma-life.athena-alpha-hierarchical-optical-formation-grade.v1",
        "truth_status":"established-bounded; implemented-exact; measured",
        "passed":passed,
        "source_holon_population":hierarchy.holons.len(),
        "source_incidence_population":hierarchy.incidences.len(),
        "source_alternative_cover_population":hierarchy.alternative_covers.len(),
        "source_repeated_form_population":hierarchy.repeated_forms.len(),
        "primary_formation_identity_sha256":primary_formation.identity_sha256,
        "held_out_formation_identity_sha256":held_formation.identity_sha256,
        "primary_png_sha256":primary_projection.png_sha256,
        "held_out_png_sha256":held_projection.png_sha256,
        "formed_surfaces_distinct":primary_projection.png_sha256 != held_projection.png_sha256,
        "rectangular_port_lattice_used_as_optical_space":false,
        "transcript_or_object_class_routed_formation":false,
        "returned_holon_population":returned_holon_population,
        "returned_incidence_population":returned_incidence_population,
        "returned_alternative_cover_population":returned_alternative_cover_population,
        "complete_returned_optical_fibre":complete_returned_fibre,
        "membrane_rest_identity_sha256":rested_identity,
        "rest_unchanged_before_physical_cultivation":rest_unchanged_before_physical_cultivation,
        "resident_optical_recovery_device":card.device_name(),
        "physical_optical_cultivation_open":true,
        "elapsed_seconds":format!("{:.9}", began.elapsed().as_secs_f64()),
    });
    write_json(&output.join("00-grade.json"), &grade)?;
    fs::write(
        output.join("INSPECTION.md"),
        format!(
            "# Hierarchical optical formation\n\n[established-bounded; implemented-exact; measured] Athena radiation transported every E1 optical holon through its existing hierarchy and complete field-cover fibre before the cold renderer acted. Primary and held-out radiation formed distinct full-resolution mathematical-page surfaces; the primary surface returned through resident optical recovery and the singular membrane with a new nonempty hierarchy. The same-body physical cultivation return remains the one open ALP2 deed.\n\n```json\n{}\n```\n",
            serde_json::to_string_pretty(&grade).map_err(display)?
        ),
    )
    .map_err(display)?;
    println!("{}", serde_json::to_string_pretty(&grade).map_err(display)?);
    if passed {
        Ok(())
    } else {
        Err("ALP2 hierarchical optical formation receiver refused".to_owned())
    }
}

fn recover_hierarchy(
    card: &mut CudaRefineExecutor,
    encoded: &[u8],
) -> Result<HierarchicalOpticalPassage, String> {
    let visible = ImageReader::new(std::io::Cursor::new(encoded))
        .with_guessed_format()
        .map_err(display)?
        .decode()
        .map_err(display)?
        .to_rgb8();
    let exact = ExactRaster::new(
        ImageExtent {
            width: visible.width(),
            height: visible.height(),
        },
        visible
            .pixels()
            .map(|pixel| ExactRgb {
                red: pixel[0],
                green: pixel[1],
                blue: pixel[2],
            })
            .collect(),
    )
    .map_err(display)?;
    let background = exact.sample(0, 0).ok_or("formed optical raster is empty")?;
    let raw = recover_optical_passage(
        card,
        format!("alp2/formed-optical/{}", sha(encoded)),
        "memory://alp2/formed-optical",
        encoded,
        &exact,
        background,
    )
    .map_err(display)?;
    let (hierarchy, device) =
        grow_optical_holons(card, &raw, OpticalHolonIntervention::None).map_err(display)?;
    if raw.components.is_empty()
        || raw.device.launches == 0
        || raw.device.cpu_semantic_fallback
        || hierarchy.holons.is_empty()
        || device.launches == 0
        || device.cpu_semantic_fallback
    {
        return Err(format!(
            "the formed optical surface did not return resident hierarchy: components={} relations={} raw_launches={} raw_cpu={} holons={} covers={} hierarchy_launches={} hierarchy_cpu={}",
            raw.components.len(),
            raw.relations.len(),
            raw.device.launches,
            raw.device.cpu_semantic_fallback,
            hierarchy.holons.len(),
            hierarchy.alternative_covers.len(),
            device.launches,
            device.cpu_semantic_fallback,
        ));
    }
    Ok(hierarchy)
}

fn continuing_native_address(
    rest: &impl MembraneStanding,
) -> Result<(life::native_intelligence::NativeSectionAddress, ReceiverId), String> {
    for address in &rest.membrane_realization().sections {
        let addressed = rest
            .membrane_ecology()
            .native()
            .addressed_section(&address.spool, &address.thread, address.occurrence)
            .map_err(display)?;
        if !addressed.thread().chronology.is_empty() {
            if let Some(receiver) = addressed.spool().receiver_family.iter().next().copied() {
                return Ok((address.clone(), receiver));
            }
        }
    }
    Err("the ALP2 body has no continuing native address".to_owned())
}

fn write_json(path: &Path, value: &impl Serialize) -> Result<(), String> {
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
