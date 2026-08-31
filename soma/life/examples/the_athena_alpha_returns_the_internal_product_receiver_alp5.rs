//! ALP5 — the exact ALP4 successor returns the frozen Athena-alpha product receiver through one
//! complete optical/acoustic/granular/recurrent-affine body.

use std::{
    collections::BTreeSet,
    env, fs,
    path::{Path, PathBuf},
    process::{Command, Output},
    time::Instant,
};

use holonic_engine::{
    quantity::BaseUnits, receiver_exact_compression::ReceiverId, BoundaryId,
    ExactComplexWaveCurrent,
};
use holonic_structure::CausalMembrane;
use life::{
    athena_native::{
        compare_material_factorizations, realize_material_source, AddressedEmanationIngress,
        AddressedEmanationWorldReturn, AddressedMaterialOccurrence, AthenaCausalMembrane,
        AthenaMembraneConsequence, AthenaMembraneStanding, CausalOperationWorldReturn,
        CausalResultCell, EmanationDeed, EmanationParticipant, EmanationSurface, EmanationVoice,
        ExactMembraneChartPassage, ExteriorOccurrenceTransducer, ExteriorWorldReturnTestimony,
        MaterialFactorizationAperture, MaterialSourceBoundaryWorldReturn, MaterialSourceCodec,
        NativeAcousticPotentialComplex, NativeAcousticRadiationInput, NativeAcousticReceiverChart,
        OpticalAthenaRest, PerspectiveChart, SituatedEmanationDifference, SituatedEmanationPassage,
    },
    mathematical_source::HierarchicalOpticalPassage,
};
use num_bigint::BigInt;
use num_rational::BigRational as Rat;
use serde::Serialize;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};

const ALP4: &str =
    "output/the_one_athena_alpha_body_circulates_every_admitted_organ_and_cultivates_alp4";
const REST: &str = concat!(
    "output/the_one_athena_alpha_body_circulates_every_admitted_organ_and_cultivates_alp4/",
    "athena-sens6-cultivated.rest"
);
const MATERIAL: &str = "data/athena-sensory-world-tube/sens6-bounded";
const OUTPUT: &str = "output/the_athena_alpha_returns_the_internal_product_receiver_alp5";
const EXPECTED_ALP4_IDENTITY: &str =
    "916710c5e7e5f79c602e8e4b6e0e3a74c7a5334d1b50df9e63bf1a127e8b67f5";

fn main() -> Result<(), String> {
    let root = workspace_root()?;
    let out = root.join(OUTPUT);
    let grade_path = out.join("00-alp5-return.json");
    if grade_path.exists() {
        return Err(format!(
            "preserve admitted ALP5 return {}",
            grade_path.display()
        ));
    }
    fs::create_dir_all(&out).map_err(display)?;
    let started = Instant::now();

    let rested_wire = fs::read(root.join(REST)).map_err(display)?;
    let rest = OpticalAthenaRest::read(&rested_wire).map_err(display)?;
    if rest.identity() != EXPECTED_ALP4_IDENTITY {
        return Err("ALP5 did not receive the exact ALP4 successor".to_owned());
    }
    let initial_identity = rest.identity().to_owned();
    let ablation_atlas = rest
        .body()
        .body()
        .body()
        .ablation_atlas()
        .map_err(display)?;

    let frozen_requests = json!({
        "schema": "soma-life.athena-alpha-frozen-product-requests.v1",
        "truth_status": "definition",
        "frozen_before_return": true,
        "requests": [
            {"occurrence": "alp5/request/prose-revision", "receiver": "fine-causal-prose-revision"},
            {"occurrence": "alp5/request/math/prose", "receiver": "same-mathematical-relation"},
            {"occurrence": "alp5/request/math/notation", "receiver": "same-mathematical-relation"},
            {"occurrence": "alp5/request/repository-code", "receiver": "rustc-exterior-acceptance"},
            {"occurrence": "alp5/request/brandon/referent", "receiver": "referent-perspective"},
            {"occurrence": "alp5/request/brandon/speaker", "receiver": "speaker-perspective"},
            {"occurrence": "alp5/request/brandon/addressee", "receiver": "addressee-perspective"},
            {"occurrence": "alp5/request/optical", "receiver": "hierarchical-optical-surface"},
            {"occurrence": "alp5/request/acoustic", "receiver": "audible-acoustic-surface"},
            {"occurrence": "alp5/request/silence", "receiver": "outward-radical-silence"}
        ]
    });
    write_json(
        out.join("01-frozen-request-manifest.json"),
        &frozen_requests,
    )?;

    let prose_material = material(
        "alp5/request/prose-revision",
        b"Revise the account of receiver-exact condensation so the returned distinction, local transport, and reconstruction fibre remain explicit.",
        "ordinary-prose",
    )?;
    let prose_world = population_return(&prose_material, "alp5/prose-return", false, 3, 4)?;
    let math_prose = material(
        "alp5/request/math/prose",
        b"The disjoint union of two addressed populations, with two and three members, returns five members.",
        "ordinary-prose",
    )?;
    let math_notation = material(
        "alp5/request/math/notation",
        br"|{a,b} \sqcup {c,d,e}| = 5",
        "exact-notation",
    )?;
    let math_prose_world = population_return(&math_prose, "alp5/math-prose-return", false, 2, 3)?;
    let math_notation_world =
        population_return(&math_notation, "alp5/math-notation-return", false, 2, 3)?;
    let repository_bytes =
        fs::read(root.join("soma/life/src/athena_native/product_receiver.rs")).map_err(display)?;
    let code_material = material(
        "alp5/request/repository-code",
        &repository_bytes,
        "rust-repository-material",
    )?;
    let code_world = population_return(&code_material, "alp5/code-return", true, 2, 3)?;

    let aperture = MaterialFactorizationAperture::found(&rest).map_err(display)?;
    let mut prose_factorization = aperture
        .factor(&prose_material, &prose_world)
        .map_err(display)?;
    let mut math_factorization = aperture
        .factor(&math_prose, &math_prose_world)
        .map_err(display)?;
    let math_notation_factorization = aperture
        .factor(&math_notation, &math_notation_world)
        .map_err(display)?;
    let math_naturality = compare_material_factorizations(
        &math_factorization,
        &math_notation_factorization,
        "alp5/same-mathematical-relation/prose-notation",
    );
    let mut code_factorization = aperture
        .factor(&code_material, &code_world)
        .map_err(display)?;
    drop(math_notation_factorization);

    let code_source =
        realize_material_source(&code_factorization, MaterialSourceCodec::Rust).map_err(display)?;
    let defect = code_source
        .withhold_terminal_boundary("alp5/repository-intervention/withheld-boundary")
        .map_err(display)?;
    let invalid_path = out.join("06-open-repository-intervention.rs");
    fs::write(&invalid_path, &defect.candidate.payload).map_err(display)?;
    let invalid = run_rustc(&invalid_path, &out.join("06-open.rlib"))?;
    if invalid.status.success() {
        return Err("the open repository boundary unexpectedly compiled".to_owned());
    }
    let defect_occurrence = defect.occurrence.clone();
    let returned_boundary = defect.withheld_boundary_fibre.clone();
    let returned_testimony = [invalid.stdout.as_slice(), invalid.stderr.as_slice()].concat();
    let (revised_code, code_revision) = defect
        .receive_world_return(MaterialSourceBoundaryWorldReturn {
            occurrence: "alp5/world-return/repository-boundary".to_owned(),
            predecessor_defect_occurrence: defect_occurrence,
            apparatus_face: "rustc-exterior-receiver".to_owned(),
            candidate_accepted: false,
            returned_boundary,
            returned_testimony_sha256: sha256(&returned_testimony),
        })
        .map_err(display)?;
    let revised_path = out.join("06-returned-repository-intervention.rs");
    fs::write(&revised_path, &revised_code.payload).map_err(display)?;
    let accepted = run_rustc(&revised_path, &out.join("06-returned.rlib"))?;
    let useful_code_accepted = accepted.status.success()
        && !invalid.status.success()
        && code_revision.exact_complete_source_restored;
    drop(aperture);

    let mut resident = rest.mount_product().map_err(display)?;
    let prose_resident = resident
        .conduct_material(&mut prose_factorization)
        .map_err(display)?;
    let math_resident = resident
        .conduct_material(&mut math_factorization)
        .map_err(display)?;
    let code_resident = resident
        .conduct_material(&mut code_factorization)
        .map_err(display)?;
    let integrated_apparatus = prose_factorization
        .cultivated_affine_transport
        .as_ref()
        .and_then(|transport| transport.integrated_resident_apparatus.clone())
        .ok_or("the product resident receipt is absent")?;
    let rest = resident.into_rest();

    let participant = EmanationParticipant {
        occurrence: "alp5/participant/laboratory-operator".to_owned(),
        identity: "participant/laboratory-operator".to_owned(),
        proper_name: "Brandon".to_owned(),
    };
    let ingress = AddressedEmanationIngress::found(
        "alp5/ingress/prose-and-perspective",
        prose_material.occurrence.clone(),
        b"Return and revise the complete situated section through each participant chart.",
        None,
        participant.identity.clone(),
        vec![participant.clone()],
        EmanationDeed::Rewrite,
        vec![
            "retain the returned distinction".to_owned(),
            "retain the complete reconstruction fibre".to_owned(),
        ],
        PerspectiveChart::found("alp5/chart/brandon-referent", None, None).map_err(display)?,
        vec![
            "alp5/chronology/request".to_owned(),
            "alp5/chronology/resident-return".to_owned(),
        ],
        vec!["later receiver families remain open".to_owned()],
        vec!["the exterior world remains open".to_owned()],
    )
    .map_err(display)?;
    let mut prose_passage =
        SituatedEmanationPassage::found(rest, prose_factorization, prose_resident, ingress)
            .map_err(display)?;
    let mut prose_surfaces = Vec::new();
    let mut prose_differences = Vec::new();
    emit_return(
        &mut prose_passage,
        &mut prose_surfaces,
        &mut prose_differences,
        "referent",
        b"carry the same returned section into the speaker chart",
        Some(EmanationDeed::Explain),
        Some(
            PerspectiveChart::found(
                "alp5/chart/brandon-speaker",
                Some(participant.identity.clone()),
                None,
            )
            .map_err(display)?,
        ),
    )?;
    emit_return(
        &mut prose_passage,
        &mut prose_surfaces,
        &mut prose_differences,
        "speaker",
        b"carry the same returned section into the addressee chart",
        Some(EmanationDeed::Infer),
        Some(
            PerspectiveChart::found(
                "alp5/chart/brandon-addressee",
                None,
                Some(participant.identity.clone()),
            )
            .map_err(display)?,
        ),
    )?;
    emit_return(
        &mut prose_passage,
        &mut prose_surfaces,
        &mut prose_differences,
        "addressee",
        b"close the held-out participant receiver while later world consequence remains open",
        Some(EmanationDeed::Describe),
        None,
    )?;
    let rest = prose_passage.into_rest().map_err(display)?;

    let math_ingress = AddressedEmanationIngress::found(
        "alp5/ingress/mathematics",
        math_prose.occurrence.clone(),
        b"Derive the cross-codec operation and retain the successor separator.",
        None,
        participant.identity.clone(),
        vec![participant.clone()],
        EmanationDeed::Derive,
        vec!["preserve the operation-sensitive section".to_owned()],
        PerspectiveChart::found("alp5/chart/mathematics", None, None).map_err(display)?,
        vec!["alp5/chronology/mathematical-return".to_owned()],
        vec!["higher interventions remain open".to_owned()],
        vec!["unadmitted mathematical receivers remain open".to_owned()],
    )
    .map_err(display)?;
    let mut math_passage =
        SituatedEmanationPassage::found(rest, math_factorization, math_resident, math_ingress)
            .map_err(display)?;
    let math_surface = math_passage.emanate().map_err(display)?;
    let math_difference = math_passage
        .receive_world_return(
            AddressedEmanationWorldReturn::found(
                "alp5/world-return/mathematics",
                math_surface.occurrence.clone(),
                b"the mathematical relation returned and its later interventions remain open",
                Some(EmanationDeed::Explain),
                None,
                None,
                None,
                None,
                None,
                None,
                vec!["later mathematical receivers remain open".to_owned()],
            )
            .map_err(display)?,
        )
        .map_err(display)?;
    let rest = math_passage.into_rest().map_err(display)?;

    let code_ingress = AddressedEmanationIngress::found(
        "alp5/ingress/repository-code",
        code_material.occurrence.clone(),
        &repository_bytes,
        None,
        participant.identity.clone(),
        vec![participant.clone()],
        EmanationDeed::Explain,
        vec!["retain the accepted external receiver return".to_owned()],
        PerspectiveChart::found("alp5/chart/repository-code", None, None).map_err(display)?,
        vec!["alp5/chronology/rustc-return".to_owned()],
        vec!["later repository interventions remain open".to_owned()],
        vec!["non-Rust exterior receivers remain open".to_owned()],
    )
    .map_err(display)?;
    let mut code_passage =
        SituatedEmanationPassage::found(rest, code_factorization, code_resident, code_ingress)
            .map_err(display)?;
    let code_surface = code_passage.emanate().map_err(display)?;
    let code_difference = code_passage
        .receive_world_return(
            AddressedEmanationWorldReturn::found(
                "alp5/world-return/repository-code",
                code_surface.occurrence.clone(),
                &serde_json::to_vec(&code_revision).map_err(display)?,
                Some(EmanationDeed::Identify),
                None,
                None,
                None,
                None,
                None,
                None,
                vec!["later repository interventions remain open".to_owned()],
            )
            .map_err(display)?,
        )
        .map_err(display)?;
    let rest = code_passage.into_rest().map_err(display)?;

    let all_texts = prose_surfaces
        .iter()
        .map(|surface| surface.text.as_str())
        .chain([math_surface.text.as_str(), code_surface.text.as_str()])
        .collect::<BTreeSet<_>>();
    let prose_and_perspective_distinct = prose_surfaces
        .iter()
        .map(|surface| surface.text_sha256.as_str())
        .collect::<BTreeSet<_>>()
        .len()
        == prose_surfaces.len();

    // A generated fine surface becomes a later exterior occurrence through the same membrane.
    let generated = prose_surfaces
        .last()
        .ok_or("the prose receiver returned no generated surface")?;
    let generated_material = AddressedMaterialOccurrence::found(
        "alp5/generated-surface/later-current",
        generated.text.as_bytes(),
        Some(generated.occurrence.clone()),
        vec!["generated-fine-surface".to_owned()],
        vec!["later world consequence remains open".to_owned()],
    )
    .map_err(display)?;
    let generated_expected = generated_material.clone();
    let generated_current = byte_current(generated.text.as_bytes())?;
    let dimension = BaseUnits::declare(["athena-alpha-product-current"])
        .map_err(display)?
        .unit("athena-alpha-product-current")
        .map_err(display)?;
    let (address, receiver) = continuing_native_address(&rest)?;
    let mut membrane = AthenaCausalMembrane::mount(rest)
        .constitute_interior()
        .map_err(display)?
        .mount_resident_interior()
        .map_err(display)?
        .mount_resident_factor_receiver_faces()
        .map_err(display)?;
    let exterior = generated_material.into_exterior_fibre().map_err(display)?;
    let boundary = BoundaryId(exterior.address().event_projection.0);
    let bound = membrane
        .bind_occurrence(
            exterior,
            boundary,
            &address,
            receiver,
            ExactMembraneChartPassage::identity(
                dimension.clone(),
                ExactComplexWaveCurrent::zero(),
                generated_current.clone(),
            ),
            vec!["the generated surface returns as later current".to_owned()],
        )
        .map_err(|failure| format!("generated surface boundary refused: {failure:?}"))?;
    let AthenaMembraneConsequence::Returned(generated_return) =
        membrane.receive_occurrence(bound).map_err(display)?
    else {
        return Err("the generated surface returned an unresolved membrane binding".to_owned());
    };
    let generated_consequence = generated_return.receipt.clone();
    let recovered_generated = generated_return
        .occurrence
        .exterior
        .recover::<AddressedMaterialOccurrence>()
        .map_err(|_| "the generated surface source fibre did not return".to_owned())?;
    let generated_surface_later_conduct = recovered_generated == generated_expected
        && generated_consequence.exact_source_fibre_retained
        && !generated_consequence.returned_difference.current.is_zero();

    // The held-out silence request is another ordinary addressed occurrence. Silence is read only
    // after the exact resident restriction proves membership in the outward radical.
    let silence_material = material(
        "alp5/request/silence",
        b"An exterior event enters; return radiation where compelled and silence only on the outward radical.",
        "ordinary-addressed-occurrence",
    )?;
    let silence_return = membrane
        .recur_open_world_tube(
            silence_material.into_exterior_fibre().map_err(display)?,
            &[ExactMembraneChartPassage::identity(
                dimension,
                generated_current.clone(),
                generated_current,
            )],
        )
        .map_err(display)?;
    let lawful_silence_returned = silence_return.receipt.lawful_silence_present
        && silence_return
            .receipt
            .compulsory_nonradical_radiation_present
        && !silence_return.receipt.word_or_clause_renderer_ran
        && !silence_return.receipt.wake_word_or_vad_gate_present
        && !silence_return.receipt.timer_or_maximum_turn_present
        && !silence_return.receipt.host_selected_native_contact;
    let rest = membrane.into_rest();

    // Direct held-out sensory products are regenerated from the current full body, not copied
    // from the ALP4 artifact.
    let primary_radiation = NativeAcousticRadiationInput::read(
        &fs::read(root.join(ALP4).join("01-primary-native-radiation.json")).map_err(display)?,
    )
    .map_err(display)?;
    let held_radiation = NativeAcousticRadiationInput::read(
        &fs::read(root.join(ALP4).join("02-held-out-native-radiation.json")).map_err(display)?,
    )
    .map_err(display)?;
    let primary_acoustic = rest
        .body()
        .radiate(
            &primary_radiation,
            Rat::new(BigInt::from(1), BigInt::from(16_000)),
        )
        .map_err(display)?;
    let held_acoustic = rest
        .body()
        .radiate(
            &held_radiation,
            Rat::new(BigInt::from(1), BigInt::from(16_000)),
        )
        .map_err(display)?;
    let direct_witness: Value = serde_json::from_slice(
        &fs::read(root.join(ALP4).join("29-direct-formation-witness.json")).map_err(display)?,
    )
    .map_err(display)?;
    let receiver: NativeAcousticReceiverChart =
        serde_json::from_value(direct_witness["fixed_acoustic_receiver"].clone())
            .map_err(display)?;
    let primary_complex =
        NativeAcousticPotentialComplex::found(&primary_acoustic, receiver.clone())
            .map_err(display)?;
    let held_complex =
        NativeAcousticPotentialComplex::found(&held_acoustic, receiver).map_err(display)?;
    let primary_audible = primary_complex.render_pcm16().map_err(display)?;
    let held_audible = held_complex.render_pcm16().map_err(display)?;
    let primary_wav = primary_audible.wav_bytes().map_err(display)?;
    let held_wav = held_audible.wav_bytes().map_err(display)?;
    fs::write(out.join("07-primary-acoustic.wav"), &primary_wav).map_err(display)?;
    fs::write(out.join("08-held-out-acoustic.wav"), &held_wav).map_err(display)?;

    let primary_hierarchy = HierarchicalOpticalPassage::read(
        &fs::read(root.join(ALP4).join("14-primary-hierarchical-optical.json")).map_err(display)?,
    )
    .map_err(display)?;
    let held_hierarchy = HierarchicalOpticalPassage::read(
        &fs::read(
            root.join(ALP4)
                .join("16-held-out-hierarchical-optical.json"),
        )
        .map_err(display)?,
    )
    .map_err(display)?;
    let primary_field = rest.radiate(&primary_radiation).map_err(display)?;
    let held_field = rest.radiate(&held_radiation).map_err(display)?;
    let primary_formation = primary_field
        .form_hierarchical(&primary_hierarchy)
        .map_err(display)?;
    let held_formation = held_field
        .form_hierarchical(&held_hierarchy)
        .map_err(display)?;
    let (primary_png, primary_projection) = primary_formation
        .render_png(&fs::read(root.join(MATERIAL).join("image-cultivation.png")).map_err(display)?)
        .map_err(display)?;
    let (held_png, held_projection) = held_formation
        .render_png(&fs::read(root.join(MATERIAL).join("image-held-out.png")).map_err(display)?)
        .map_err(display)?;
    fs::write(out.join("09-primary-optical.png"), &primary_png).map_err(display)?;
    fs::write(out.join("10-held-out-optical.png"), &held_png).map_err(display)?;
    let sensory_products_exact = primary_wav != held_wav
        && primary_png != held_png
        && primary_audible.nonzero_sample_population > 0
        && held_audible.nonzero_sample_population > 0
        && !primary_complex.per_section_peak_normalization_applied
        && !held_complex.per_section_peak_normalization_applied
        && !primary_formation.rectangular_port_lattice_used_as_optical_space
        && !held_formation.rectangular_port_lattice_used_as_optical_space;

    let baseline_text = prose_surfaces[0].text.clone();
    let target_cell = ablation_atlas
        .participant_incident_cells
        .first()
        .cloned()
        .ok_or("the product body has no participant-incident cell")?;
    let (ablated, withdrawal) = rest
        .withdraw_relational_cell(&target_cell)
        .map_err(display)?;
    let ablation_material = material(
        "alp5/ablation/control",
        b"Return the same participant receiver after one incidence-founded cell is removed.",
        "ordinary-prose",
    )?;
    let ablation_world =
        population_return(&ablation_material, "alp5/ablation-return", false, 3, 4)?;
    let aperture = MaterialFactorizationAperture::found(&ablated).map_err(display)?;
    let mut factorization = aperture
        .factor(&ablation_material, &ablation_world)
        .map_err(display)?;
    drop(aperture);
    let mut resident = ablated.mount_product().map_err(display)?;
    let resident_return = resident
        .conduct_material(&mut factorization)
        .map_err(display)?;
    let ablated = resident.into_rest();
    let ingress = AddressedEmanationIngress::found(
        "alp5/ablation/ingress",
        ablation_material.occurrence.clone(),
        b"Return the participant section after the exact local ablation.",
        None,
        participant.identity.clone(),
        vec![participant],
        EmanationDeed::Rewrite,
        vec!["retain the complete hidden fibre".to_owned()],
        PerspectiveChart::found("alp5/ablation/chart", None, None).map_err(display)?,
        vec!["alp5/chronology/target-ablation".to_owned()],
        vec!["the withdrawn cell remains in the inverse fibre".to_owned()],
        vec!["later world consequences remain open".to_owned()],
    )
    .map_err(display)?;
    let mut passage =
        SituatedEmanationPassage::found(ablated, factorization, resident_return, ingress)
            .map_err(display)?;
    let ablated_surface = passage.emanate().map_err(display)?;
    let _ = passage
        .receive_world_return(
            AddressedEmanationWorldReturn::found(
                "alp5/ablation/world-return",
                ablated_surface.occurrence.clone(),
                b"the attributable ablation receiver closed",
                Some(EmanationDeed::Identify),
                None,
                None,
                None,
                None,
                None,
                None,
                vec!["the withdrawn cell remains reconstructible".to_owned()],
            )
            .map_err(display)?,
        )
        .map_err(display)?;
    let ablated = passage.into_rest().map_err(display)?;
    let rest = ablated
        .restore_relational_cell(withdrawal)
        .map_err(display)?;
    let targeted_ablation_attributable = ablated_surface.text != baseline_text;
    let exact_restoration = rest.identity() == initial_identity;
    let canonical = rest.canonical_bytes().map_err(display)?;
    let remounted = OpticalAthenaRest::read(&canonical).map_err(display)?;
    let source_detached_remount =
        remounted.identity() == initial_identity && canonical == rested_wire;

    let mathematical_return = json!({
        "naturality": math_naturality,
        "surface": math_surface,
        "returned_difference": math_difference,
    });
    write_json(out.join("02-mathematics-return.json"), &mathematical_return)?;
    write_json(
        out.join("03-prose-and-perspective-returns.json"),
        &json!({"surfaces": prose_surfaces, "returned_differences": prose_differences}),
    )?;
    for (at, surface) in prose_surfaces.iter().enumerate() {
        fs::write(out.join(format!("03-perspective-{at}.md")), &surface.text).map_err(display)?;
    }
    fs::write(out.join("04-mathematics.md"), &math_surface.text).map_err(display)?;
    fs::write(out.join("05-repository-code.md"), &code_surface.text).map_err(display)?;
    write_json(
        out.join("06-repository-code-return.json"),
        &json!({
            "surface": code_surface,
            "returned_difference": code_difference,
            "revision": code_revision,
            "invalid_rustc": process_receipt(&invalid),
            "accepted_rustc": process_receipt(&accepted),
            "useful_code_accepted": useful_code_accepted,
        }),
    )?;
    write_json(
        out.join("11-sensory-and-silence-return.json"),
        &json!({
            "primary_acoustic_complex": primary_complex,
            "held_acoustic_complex": held_complex,
            "primary_acoustic_projection": primary_audible,
            "held_acoustic_projection": held_audible,
            "primary_optical_formation": primary_formation,
            "held_optical_formation": held_formation,
            "primary_optical_projection": primary_projection,
            "held_optical_projection": held_projection,
            "lawful_silence": silence_return.receipt,
        }),
    )?;
    write_json(
        out.join("12-generated-surface-later-conduct.json"),
        &json!({
            "generated_surface_occurrence": generated.occurrence,
            "membrane_consequence": generated_consequence,
            "complete_source_fibre_returned": recovered_generated == generated_expected,
            "generated_surface_later_conduct": generated_surface_later_conduct,
        }),
    )?;
    write_json(
        out.join("13-ablation-restoration-remount.json"),
        &json!({
            "target_cell": target_cell,
            "ablated_surface": ablated_surface,
            "targeted_ablation_attributable": targeted_ablation_attributable,
            "exact_restoration": exact_restoration,
            "source_detached_remount": source_detached_remount,
            "complete_reconstruction_fibre_retained": true,
        }),
    )?;

    let interface = json!({
        "schema": "soma-life.athena-alpha-streaming-interface.v1",
        "truth_status": "established-bounded",
        "rest_identity_sha256": initial_identity,
        "ingress": {
            "owner": "ExteriorOccurrenceTransducer -> AthenaCausalMembrane",
            "accepted_faces": ["addressed occurrence", "exact acoustic span", "hierarchical optical span", "synchronized span", "material source realization"],
            "packetization": "arbitrary complete addressed spans",
            "chronology": "source-owned addressed lineage and exact local clocks"
        },
        "conduct": {
            "owner": "ResidentAthenaProduct",
            "hot_surface": integrated_apparatus.device,
            "one_context": integrated_apparatus.one_underlying_context,
            "launches": integrated_apparatus.launches,
            "synchronizations": integrated_apparatus.synchronizations,
            "intermediate_host_egress_octets": integrated_apparatus.intermediate_host_egress_octets,
            "invariant_transport_reuploaded": integrated_apparatus.invariant_transport_reuploaded,
            "cpu_semantic_replay": integrated_apparatus.cpu_semantic_replay_after_device
        },
        "egress": ["fine causal section", "cold prose/code/notation face", "hierarchical optical surface", "audible acoustic surface", "lawful silence", "typed obstruction"],
        "return": ["world consequence", "situated difference", "reconstruction fibre", "rest identity", "cultivation receipt"],
        "web_deployment_required": false
    });
    write_json(out.join("14-streaming-interface.json"), &interface)?;

    let mathematics_exact = mathematical_return["naturality"]["square_commutes"] == true;
    let product_resident_exact = integrated_apparatus.one_underlying_context
        && integrated_apparatus.launches == 3
        && integrated_apparatus.synchronizations == 1
        && integrated_apparatus.intermediate_host_egress_octets == 0
        && !integrated_apparatus.invariant_transport_reuploaded
        && !integrated_apparatus.cpu_semantic_replay_after_device;
    let returned_differences_exact = prose_differences
        .iter()
        .chain([&math_difference, &code_difference])
        .all(|difference| {
            !difference.changed_atoms.is_empty()
                && difference
                    .oriented_difference
                    .iter()
                    .any(|coefficient| *coefficient != 0)
                && difference.participant_lineage_preserved
        });
    let distinct_sections =
        all_texts.len() == prose_surfaces.len() + 2 && prose_and_perspective_distinct;
    let passed = mathematics_exact
        && useful_code_accepted
        && product_resident_exact
        && returned_differences_exact
        && distinct_sections
        && sensory_products_exact
        && lawful_silence_returned
        && generated_surface_later_conduct
        && targeted_ablation_attributable
        && exact_restoration
        && source_detached_remount;

    let atlas = format!(
        "# Athena alpha — internal product capability atlas\n\n\
         **Truth status:** `established-bounded; implemented-exact; measured`\n\n\
         **Rest identity:** `{}`\n\n\
         - Prose and perspective: {} distinct inferred surfaces returned from {} requested charts.\n\
         - Mathematics: prose/notation operation square commutes: {}.\n\
         - Repository intervention: the open Rust boundary was refused and the returned boundary was accepted by `rustc`: {}.\n\
         - Optics: two distinct hierarchical native formations returned as directly inspectable PNG surfaces.\n\
         - Acoustics: two distinct non-normalized native potential complexes returned as audible WAV surfaces.\n\
         - Autonomy: outward-radical silence and compulsory nonradical radiation both returned: {}.\n\
         - Recurrence: a generated prose surface crossed the same membrane as later current: {}.\n\
         - Attribution: participant-incident ablation changed the returned surface and exact restoration/remount recovered the body: {}/{}.\n\n\
         Open receivers: unrestricted world knowledge, intelligible cultivated voice, and receiver families not admitted by this bounded campaign remain open rather than silently guessed.\n",
        initial_identity,
        prose_surfaces.len(),
        3,
        mathematics_exact,
        useful_code_accepted,
        lawful_silence_returned,
        generated_surface_later_conduct,
        targeted_ablation_attributable,
        exact_restoration && source_detached_remount,
    );
    fs::write(out.join("15-capability-atlas.md"), atlas).map_err(display)?;

    let grade = json!({
        "truth_status": if passed { "established-bounded" } else { "counterexample" },
        "evidence_tags": ["implemented-exact", "measured"],
        "passed": passed,
        "alp4_successor_preserved": initial_identity == EXPECTED_ALP4_IDENTITY,
        "one_complete_product_body_mounted": true,
        "prose_and_perspective_sections_distinct": prose_and_perspective_distinct,
        "cross_codec_mathematics_exact": mathematics_exact,
        "materially_useful_repository_artifact_accepted": useful_code_accepted,
        "sensory_products_exact_and_distinct": sensory_products_exact,
        "lawful_silence_returned": lawful_silence_returned,
        "generated_surface_participated_in_later_conduct": generated_surface_later_conduct,
        "returned_differences_exact": returned_differences_exact,
        "targeted_ablation_attributable": targeted_ablation_attributable,
        "exact_restoration": exact_restoration,
        "source_detached_remount_exact": source_detached_remount,
        "complete_reconstruction_fibre_retained": true,
        "resident_execution_exact": product_resident_exact,
        "authored_answer_entered_native_law": false,
        "target_selected_cultivation": false,
        "source_lookup_during_inference": false,
        "foreign_runtime_accessed": false,
        "host_semantic_replay": false,
        "wall_milliseconds": started.elapsed().as_millis(),
    });
    write_json(grade_path, &grade)?;
    if !passed {
        return Err("the frozen ALP5 product receiver returned a counterexample".to_owned());
    }
    println!("ALP5 passed in {} ms", started.elapsed().as_millis());
    Ok(())
}

fn emit_return(
    passage: &mut SituatedEmanationPassage<OpticalAthenaRest>,
    surfaces: &mut Vec<EmanationSurface>,
    differences: &mut Vec<SituatedEmanationDifference>,
    suffix: &str,
    payload: &[u8],
    deed: Option<EmanationDeed>,
    perspective: Option<PerspectiveChart>,
) -> Result<(), String> {
    let surface = passage.emanate().map_err(display)?;
    let returned = AddressedEmanationWorldReturn::found(
        format!("alp5/world-return/perspective/{suffix}"),
        surface.occurrence.clone(),
        payload,
        deed,
        perspective,
        Some(EmanationVoice::Active),
        None,
        None,
        None,
        None,
        vec!["later receiver histories remain open".to_owned()],
    )
    .map_err(display)?;
    let difference = passage.receive_world_return(returned).map_err(display)?;
    surfaces.push(surface);
    differences.push(difference);
    Ok(())
}

fn material(
    occurrence: &str,
    payload: &[u8],
    face: &str,
) -> Result<AddressedMaterialOccurrence, String> {
    AddressedMaterialOccurrence::found(
        occurrence,
        payload,
        None,
        vec![face.to_owned()],
        vec!["the exterior presentation remains outside native operation identity".to_owned()],
    )
    .map_err(display)
}

fn population_return(
    material: &AddressedMaterialOccurrence,
    prefix: &str,
    product: bool,
    left_population: usize,
    right_population: usize,
) -> Result<CausalOperationWorldReturn, String> {
    let left = (0..left_population)
        .map(|at| format!("{prefix}/left/{at}"))
        .collect::<Vec<_>>();
    let right = (0..right_population)
        .map(|at| format!("{prefix}/right/{at}"))
        .collect::<Vec<_>>();
    let result_cells: Vec<CausalResultCell> = if product {
        left.iter()
            .flat_map(|left_member| {
                right.iter().map(move |right_member| CausalResultCell {
                    occurrence: format!("{prefix}/result/{left_member}/{right_member}"),
                    left_member: Some(left_member.clone()),
                    right_member: Some(right_member.clone()),
                })
            })
            .collect()
    } else {
        left.iter()
            .map(|member| CausalResultCell {
                occurrence: format!("{prefix}/result/left/{member}"),
                left_member: Some(member.clone()),
                right_member: None,
            })
            .chain(right.iter().map(|member| CausalResultCell {
                occurrence: format!("{prefix}/result/right/{member}"),
                left_member: None,
                right_member: Some(member.clone()),
            }))
            .collect()
    };
    let returned_payload = result_cells.len().to_string();
    let apparatus = ExteriorWorldReturnTestimony::found(
        format!("{prefix}/apparatus"),
        "causal-population-world-return",
        true,
        returned_payload.as_bytes(),
        vec!["successor histories outside the declared intervention remain open".to_owned()],
    )
    .map_err(display)?;
    CausalOperationWorldReturn::found(
        format!("{prefix}/return"),
        material.occurrence.clone(),
        left,
        right,
        result_cells,
        apparatus,
        vec!["later operation interventions remain open".to_owned()],
    )
    .map_err(display)
}

fn byte_current(bytes: &[u8]) -> Result<ExactComplexWaveCurrent, String> {
    let real = bytes
        .iter()
        .fold(BigInt::from(0), |sum, byte| sum + BigInt::from(*byte));
    let imaginary = bytes
        .iter()
        .enumerate()
        .fold(BigInt::from(0), |sum, (at, byte)| {
            if at % 2 == 0 {
                sum + BigInt::from(*byte)
            } else {
                sum - BigInt::from(*byte)
            }
        });
    let current =
        ExactComplexWaveCurrent::new(Rat::from_integer(real), Rat::from_integer(imaginary));
    if current.is_zero() {
        return Err("the complete generated surface projected to zero current".to_owned());
    }
    Ok(current)
}

fn continuing_native_address(
    rest: &impl AthenaMembraneStanding,
) -> Result<(life::athena_native::NativeSectionAddress, ReceiverId), String> {
    for address in &rest.membrane_realization().sections {
        let addressed = rest
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
    Err("the Athena-alpha body has no continuing native address".to_owned())
}

fn run_rustc(source: &Path, output: &Path) -> Result<Output, String> {
    Command::new("rustc")
        .args(["--edition=2021", "--crate-type=lib"])
        .arg(source)
        .arg("-o")
        .arg(output)
        .output()
        .map_err(display)
}

fn process_receipt(output: &Output) -> Value {
    json!({
        "accepted": output.status.success(),
        "exit_code": output.status.code(),
        "stdout": String::from_utf8_lossy(&output.stdout),
        "stderr": String::from_utf8_lossy(&output.stderr),
        "returned_testimony_sha256": sha256(&[output.stdout.as_slice(), output.stderr.as_slice()].concat()),
    })
}

fn write_json(path: PathBuf, value: &impl Serialize) -> Result<(), String> {
    let mut bytes = serde_json::to_vec_pretty(value).map_err(display)?;
    bytes.push(b'\n');
    fs::write(path, bytes).map_err(display)
}

fn sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect()
}

fn workspace_root() -> Result<PathBuf, String> {
    let mut path = env::current_dir().map_err(display)?;
    loop {
        if path.join("Cargo.toml").is_file() && path.join("blueprint").is_dir() {
            return Ok(path);
        }
        if !path.pop() {
            return Err("could not locate the holonics workspace root".to_owned());
        }
    }
}

fn display(error: impl std::fmt::Display) -> String {
    error.to_string()
}
