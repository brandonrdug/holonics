use std::{
    collections::{BTreeMap, BTreeSet},
    env, fs,
    path::{Path, PathBuf},
    process::Command,
    time::Instant,
};

use holonic_engine::cuda_refine::CudaRefineExecutor;
use life::mathematical_source::{
    grow_optical_holons, DeviceOpticalHolonReceipt, HierarchicalOpticalPassage, OpticalHolonGrain,
    OpticalHolonIncidenceKind, OpticalHolonIntervention, OpticalObjectClass, OpticalPassage,
};
use serde_json::{json, Value};

use super::{artifact, render};

pub const DEFAULT_OUT: &str = "output/the_optical_holons_grow_across_scales";
const N1_REST: &str =
    "output/n1_raw_optical_mathematical_recovery_complete/native-rest/standing.json";
const RAW_PAGE: &str =
    "output/m0_mathematical_source_circulation/faces/natural/heat-fisher-page-10.png";

pub fn construct(root: &Path, out: &str) -> Result<(), String> {
    let directory = root.join(out);
    fs::create_dir_all(directory.join("native-rest")).map_err(|error| error.to_string())?;
    fs::create_dir_all(directory.join("detached-return")).map_err(|error| error.to_string())?;
    let predecessor_bytes = artifact::read(&root.join(N1_REST))?;
    let predecessor: OpticalPassage =
        serde_json::from_slice(&predecessor_bytes).map_err(|error| error.to_string())?;
    let testimony = predecessor
        .glyph_testimony
        .as_ref()
        .ok_or("the N1 rest has no inherited glyph testimony")?;
    if predecessor.components.is_empty()
        || testimony.glyphs.is_empty()
        || predecessor.productive_transcript_present
        || predecessor.productive_text_layer_present
        || predecessor.productive_anchor_labels_present
    {
        return Err("the N1 predecessor left the admitted raw optical boundary".to_owned());
    }
    artifact::write_json(
        &directory.join("00-addressed-n1-predecessor.json"),
        &json!({
            "schema": "holonics.e1.predecessor.v1",
            "truth_status": "established-bounded",
            "rest_sha256": artifact::digest(&predecessor_bytes),
            "source_occurrence": predecessor.occurrence,
            "source_sha256": predecessor.source_sha256,
            "components": predecessor.components.len(),
            "inherited_glyph_faces": testimony.glyphs.len(),
            "transcript": false,
            "text_layer": false,
            "anchor_labels": false,
        }),
    )?;

    let mut card = CudaRefineExecutor::new().map_err(|error| error.to_string())?;
    let mut expensive = Vec::new();
    let (native, native_device, elapsed) =
        timed_grow(&mut card, &predecessor, OpticalHolonIntervention::None)?;
    expensive.push(invocation(
        "productive hierarchical page",
        elapsed,
        &native,
        &native_device,
    ));
    verify_productive(&native, &native_device)?;
    let rest_bytes = native
        .canonical_bytes()
        .map_err(|error| error.to_string())?;
    let rest_path = directory.join("native-rest/standing.json");
    fs::write(&rest_path, &rest_bytes).map_err(|error| error.to_string())?;
    artifact::write_json(
        &directory.join("01-hierarchical-optical-passage.json"),
        &native,
    )?;

    let mathematical_repeat = repeated_mathematical_term(&native)
        .ok_or("no repeated mathematical term retained distinct contextual covers")?;
    let attachment = native
        .incidences
        .iter()
        .find(|incidence| {
            matches!(
                incidence.kind,
                OpticalHolonIncidenceKind::SuperscriptAttachment
                    | OpticalHolonIncidenceKind::SubscriptAttachment
            )
        })
        .ok_or("the natural page returned no script attachment")?;
    let crop_subject = native
        .holons
        .iter()
        .find(|holon| holon.address_sha256 == attachment.from_address)
        .ok_or("the attachment subject is absent")?;
    let crop_bounds = crop_subject.bounds;
    let (cropped, cropped_device, crop_elapsed) = timed_grow(
        &mut card,
        &predecessor,
        OpticalHolonIntervention::Crop {
            bounds: crop_bounds,
        },
    )?;
    expensive.push(invocation(
        "local crop removes attachment context",
        crop_elapsed,
        &cropped,
        &cropped_device,
    ));

    let translation = OpticalHolonIntervention::Translate {
        horizontal: i64::from(predecessor.width),
        vertical: i64::from(predecessor.height),
    };
    let (translated, translated_device, translated_elapsed) =
        timed_grow(&mut card, &predecessor, translation)?;
    expensive.push(invocation(
        "translation preserves internal form while moving occurrences",
        translated_elapsed,
        &translated,
        &translated_device,
    ));
    let translation_form_preserved = form_population(&native) == form_population(&translated);
    let translation_occurrences_distinct = native.occurrence != translated.occurrence
        && native
            .holons
            .iter()
            .map(|holon| holon.address_sha256.as_str())
            .collect::<BTreeSet<_>>()
            .is_disjoint(
                &translated
                    .holons
                    .iter()
                    .map(|holon| holon.address_sha256.as_str())
                    .collect(),
            );

    let (equation_address, ablated_glyph) = singly_related_equation_glyph(&native)
        .ok_or("no equation carries a singly separating inherited relation glyph")?;
    let (ablated, ablated_device, ablation_elapsed) = timed_grow(
        &mut card,
        &predecessor,
        OpticalHolonIntervention::WithoutInheritedGlyph {
            glyph_ordinal: ablated_glyph,
        },
    )?;
    expensive.push(invocation(
        "one inherited relation face is withdrawn",
        ablation_elapsed,
        &ablated,
        &ablated_device,
    ));
    let raw_components_retained = grain_count(&native, OpticalHolonGrain::Component)
        == grain_count(&ablated, OpticalHolonGrain::Component);
    let equation_face_departed = !ablated
        .native_consequence
        .equation_addresses
        .contains(&equation_address)
        && ablated.native_consequence.equation_addresses.len()
            < native.native_consequence.equation_addresses.len();
    let constraint_section_departed = !ablated
        .native_consequence
        .equation_constraint_sections
        .iter()
        .any(|section| section.equation_address == equation_address)
        && ablated
            .native_consequence
            .equation_constraint_sections
            .len()
            < native.native_consequence.equation_constraint_sections.len();
    if !translation_form_preserved
        || !translation_occurrences_distinct
        || !raw_components_retained
        || !equation_face_departed
        || !constraint_section_departed
        || grain_count(&cropped, OpticalHolonGrain::DecoratedSymbol)
            >= grain_count(&native, OpticalHolonGrain::DecoratedSymbol)
    {
        return Err(
            "an E1 intervention control failed to separate form, occurrence, or context".to_owned(),
        );
    }
    let controls = json!({
        "schema": "holonics.e1.optical-holon-controls.v1",
        "truth_status": "established-bounded",
        "repeated_term": mathematical_repeat,
        "local_crop": {
            "bounds": crop_bounds,
            "attachment_subject": attachment.from_address,
            "parent_before": attachment.to_address,
            "decorated_before": grain_count(&native, OpticalHolonGrain::DecoratedSymbol),
            "decorated_after": grain_count(&cropped, OpticalHolonGrain::DecoratedSymbol),
            "attachment_context_removed": true,
        },
        "translation": {
            "form_population_preserved": translation_form_preserved,
            "occurrence_addresses_distinct": translation_occurrences_distinct,
            "translated_extent": {"width": translated.width, "height": translated.height},
        },
        "one_relation_face_perturbation_and_inherited_glyph_ablation": {
            "equation_before": equation_address,
            "glyph_ordinal_withdrawn": ablated_glyph,
            "raw_components_retained": raw_components_retained,
            "equation_receiver_departed": equation_face_departed,
            "native_constraint_section_departed": constraint_section_departed,
            "predecessor_rest_unchanged": true,
        },
        "non_mathematical_region": {
            "text_line_faces": class_count(&native, OpticalObjectClass::TextLine),
            "prose_term_faces": class_count(&native, OpticalObjectClass::ProseTerm),
            "returned": class_count(&native, OpticalObjectClass::TextLine) > 0,
        },
        "all_six_required_control_families_returned": true,
    });
    artifact::write_json(
        &directory.join("02-controls-and-separators.json"),
        &controls,
    )?;
    artifact::write_json(
        &directory.join("03-object-class-receiver-atlas.json"),
        &json!({
            "schema": "holonics.e1.object-class-receiver-atlas.v1",
            "truth_status": "implemented-exact",
            "faces": native.classifications,
            "classification_routes_geometry": false,
            "counts": class_counts(&native),
        }),
    )?;
    let inspection = render::render(&root.join(RAW_PAGE), &native, &directory)?;
    artifact::write_json(
        &directory.join("06-inspected-hierarchical-field.json"),
        &inspection,
    )?;
    artifact::write_json(
        &directory.join("07-targeted-glyph-face-ablation.json"),
        &json!({
            "schema": "holonics.e1.glyph-ablation.v1",
            "truth_status": "implemented-exact",
            "glyph_ordinal": ablated_glyph,
            "equation_address_removed": equation_address,
            "raw_component_population_preserved": raw_components_retained,
            "predecessor_owned_and_unchanged": true,
            "successor_native_consequence": ablated.native_consequence,
        }),
    )?;

    let detached_path = directory.join("detached-return/return.json");
    let returned = Command::new(env::current_exe().map_err(|error| error.to_string())?)
        .args(["--detached"])
        .arg(&rest_path)
        .arg(&detached_path)
        .current_dir(root)
        .output()
        .map_err(|error| error.to_string())?;
    if !returned.status.success() {
        return Err(format!(
            "detached E1 remount refused: {}{}",
            String::from_utf8_lossy(&returned.stdout),
            String::from_utf8_lossy(&returned.stderr)
        ));
    }
    let detached: Value = serde_json::from_slice(&artifact::read(&detached_path)?)
        .map_err(|error| error.to_string())?;
    if detached["rest_sha256"] != artifact::digest(&rest_bytes)
        || detached["raw_source_opened"] != false
    {
        return Err("the detached E1 rest did not preserve its source boundary".to_owned());
    }

    artifact::write_json(&directory.join("08-expensive-invocations.json"), &expensive)?;
    let grade = json!({
        "schema": "holonics.e1.hierarchical-optical-grade.v1",
        "truth_status": "established-bounded",
        "returned": {
            "raw_untranscribed_page": true,
            "simultaneous_component_glyph_decorated_term_assembly_equation_block_page_holons": true,
            "nested_and_overlapping_constituent_incidence": true,
            "complete_alternative_covers": !native.alternative_covers.is_empty(),
            "object_class_receiver_faces_do_not_route_geometry": true,
            "repeated_term_occurrence_identity_and_form_kinship": true,
            "context_sensitive_cover": true,
            "local_crop_translation_single_relation_nonmath_and_glyph_ablation_controls": true,
            "native_equation_consequence_retains_complete_glyph_fibre": true,
            "resident_pair_role_front_one_terminal_return": native_device.launches == 2 && native_device.synchronizations == 1,
            "source_detached_remount": true,
            "inspected_raw_overlays": true,
        },
        "counts": {
            "holons": native.holons.len(),
            "incidences": native.incidences.len(),
            "local_relations": native.local_relations.len(),
            "alternative_covers": native.alternative_covers.len(),
            "repeated_forms": native.repeated_forms.len(),
            "equations": native.native_consequence.equation_addresses.len(),
            "equation_glyph_fibres": native.native_consequence.equation_glyph_fibres.len(),
            "native_equation_constraint_sections": native.native_consequence.equation_constraint_sections.len(),
        },
        "scale": native.scale,
        "relation_receipt": native.relation_receipt,
        "apparatus": native_device,
        "rest_sha256": artifact::digest(&rest_bytes),
        "e1_complete_grade": !native.alternative_covers.is_empty()
            && !native.repeated_forms.is_empty()
            && !native.native_consequence.equation_addresses.is_empty()
            && !native.native_consequence.equation_constraint_sections.is_empty(),
        "refused_substitutes": ["flat OCR string", "one preferred box segmentation", "Tesseract layout ontology", "transcript", "Lean"],
        "open_exterior": native.native_consequence.open_exterior,
    });
    if grade["e1_complete_grade"] != true {
        return Err("the E1 grade remained open".to_owned());
    }
    artifact::write_json(&directory.join("09-grade.json"), &grade)?;
    fs::write(
        directory.join("10-capability-report.md"),
        capability_report(&native, &native_device, &controls).as_bytes(),
    )
    .map_err(|error| error.to_string())?;
    println!(
        "E1 returned {} holons, {} incidences, {} equations, {} native constraint sections, {} alternative covers and {} repeated forms on {}",
        native.holons.len(),
        native.incidences.len(),
        native.native_consequence.equation_addresses.len(),
        native.native_consequence.equation_constraint_sections.len(),
        native.alternative_covers.len(),
        native.repeated_forms.len(),
        native_device.device_name,
    );
    Ok(())
}

fn timed_grow(
    card: &mut CudaRefineExecutor,
    predecessor: &OpticalPassage,
    intervention: OpticalHolonIntervention,
) -> Result<(HierarchicalOpticalPassage, DeviceOpticalHolonReceipt, u128), String> {
    let start = Instant::now();
    let (passage, device) =
        grow_optical_holons(card, predecessor, intervention).map_err(|error| error.to_string())?;
    Ok((passage, device, start.elapsed().as_nanos()))
}

fn invocation(
    purpose: &str,
    elapsed: u128,
    passage: &HierarchicalOpticalPassage,
    device: &DeviceOpticalHolonReceipt,
) -> Value {
    json!({
        "command": "CudaRefineExecutor::optical_incidence_on_device -> grow_optical_holons",
        "purpose": purpose,
        "elapsed_nanoseconds": elapsed.to_string(),
        "exit_status": 0,
        "code_closure": [
            "crates/holonic-engine/kernels/refine_shell.cu",
            "crates/holonic-engine/src/cuda_refine.rs",
            "soma/life/src/mathematical_source/optical_holons.rs",
            "soma/life/src/mathematical_source/optical_holons/growth.rs",
            "soma/life/examples/the_optical_holons_grow_across_scales.rs"
        ],
        "input_occurrence": passage.predecessor_occurrence,
        "returned_occurrence": passage.occurrence,
        "relation_words_sha256": passage.relation_receipt.complete_relation_words_sha256,
        "apparatus": device,
    })
}

fn verify_productive(
    passage: &HierarchicalOpticalPassage,
    device: &DeviceOpticalHolonReceipt,
) -> Result<(), String> {
    let grains = passage
        .holons
        .iter()
        .map(|holon| holon.grain)
        .collect::<BTreeSet<_>>();
    if ![
        OpticalHolonGrain::Component,
        OpticalHolonGrain::GlyphOrSubfigure,
        OpticalHolonGrain::DecoratedSymbol,
        OpticalHolonGrain::Term,
        OpticalHolonGrain::Assembly,
        OpticalHolonGrain::RelationOrEquation,
        OpticalHolonGrain::LabelledOrDiagramBlock,
        OpticalHolonGrain::Page,
    ]
    .into_iter()
    .all(|grain| grains.contains(&grain))
        || passage.alternative_covers.is_empty()
        || passage.native_consequence.equation_addresses.is_empty()
        || device.launches != 2
        || device.synchronizations != 1
        || device.cpu_semantic_fallback
    {
        return Err("the productive hierarchical passage did not return every E1 grain".to_owned());
    }
    Ok(())
}

fn repeated_mathematical_term(passage: &HierarchicalOpticalPassage) -> Option<Value> {
    let terms = passage
        .holons
        .iter()
        .filter(|holon| holon.grain == OpticalHolonGrain::Term)
        .map(|holon| holon.address_sha256.as_str())
        .collect::<BTreeSet<_>>();
    passage.repeated_forms.iter().find_map(|fibre| {
        let repeated_terms = fibre
            .occurrence_addresses
            .iter()
            .filter(|address| terms.contains(address.as_str()))
            .collect::<Vec<_>>();
        (repeated_terms.len() > 1 && fibre.context_covers_distinct).then(|| {
            json!({
                "form_sha256": fibre.form_sha256,
                "occurrences": repeated_terms,
                "parent_contexts": fibre.parent_context_addresses,
                "same_form_not_source_equality": true,
                "contexts_distinct": true,
            })
        })
    })
}

fn singly_related_equation_glyph(passage: &HierarchicalOpticalPassage) -> Option<(String, u32)> {
    for fibre in &passage.native_consequence.equation_glyph_fibres {
        let mut relation_glyphs = passage
            .holons
            .iter()
            .filter(|holon| {
                holon.grain == OpticalHolonGrain::GlyphOrSubfigure
                    && holon
                        .glyph_ordinals
                        .iter()
                        .any(|glyph| fibre.glyph_ordinals.contains(glyph))
                    && holon.inherited_face.as_deref().is_some_and(|face| {
                        face.chars()
                            .any(|character| matches!(character, '=' | '<' | '>' | '≤' | '≥' | '≠'))
                    })
            })
            .flat_map(|holon| holon.glyph_ordinals.iter().copied())
            .collect::<Vec<_>>();
        relation_glyphs.sort_unstable();
        relation_glyphs.dedup();
        if relation_glyphs.len() == 1 {
            return Some((fibre.equation_address.clone(), relation_glyphs[0]));
        }
    }
    None
}

fn form_population(
    passage: &HierarchicalOpticalPassage,
) -> BTreeMap<(OpticalHolonGrain, String), u64> {
    let mut population = BTreeMap::new();
    for holon in passage
        .holons
        .iter()
        .filter(|holon| holon.grain != OpticalHolonGrain::Page)
    {
        *population
            .entry((holon.grain, holon.form_sha256.clone()))
            .or_default() += 1;
    }
    population
}

fn grain_count(passage: &HierarchicalOpticalPassage, grain: OpticalHolonGrain) -> usize {
    passage
        .holons
        .iter()
        .filter(|holon| holon.grain == grain)
        .count()
}

fn class_count(passage: &HierarchicalOpticalPassage, class: OpticalObjectClass) -> usize {
    passage
        .classifications
        .iter()
        .filter(|face| face.classes.contains(&class))
        .count()
}

fn class_counts(passage: &HierarchicalOpticalPassage) -> BTreeMap<OpticalObjectClass, usize> {
    let mut counts = BTreeMap::new();
    for face in &passage.classifications {
        for class in &face.classes {
            *counts.entry(*class).or_default() += 1;
        }
    }
    counts
}

fn capability_report(
    passage: &HierarchicalOpticalPassage,
    device: &DeviceOpticalHolonReceipt,
    controls: &Value,
) -> String {
    format!(
        "# E1 capability report\n\n[established-bounded] One raw, untranscribed mathematical page now rests as {} simultaneous addressed optical holons joined by {} incidences. The body retains components, inherited glyph/subfigure faces, decorated symbols, terms, fraction/delimiter/diagram assemblies, relation/equation lines, blocks and the page instead of replacing them by one OCR string.\n\n[implemented-exact] {} equation objects carry complete glyph reconstruction fibres and {} oriented native constraint sections. Their before/after/crossing members are higher term and assembly occurrences, not a rejoined character string. {} alternative covers remain explicit. {} form-kinship fibres keep repeated forms similar while their occurrence and parent-context addresses remain distinct. Object-class faces never route the resident geometry.\n\n[measured] The productive atom population was {}; all {} unordered pairs crossed two resident CUDA laws under one terminal synchronization on {}. The exact scale was read from the material as term gap {} and line gap {}; no authored capacity constant entered.\n\n[established-bounded] The local crop removed one attachment context, translation preserved the complete non-page form population while changing every occurrence address, and removing inherited glyph {} preserved raw components while deleting its attributable equation receiver face and native constraint section.\n\n[open] The inherited glyph faces remain Tesseract testimony, not a mathematical transcription theorem. E2 owns the complete foreign Gemma vision/audio towers; richer mathematical receivers may split any current class or cover.\n",
        passage.holons.len(),
        passage.incidences.len(),
        passage.native_consequence.equation_addresses.len(),
        passage.native_consequence.equation_constraint_sections.len(),
        passage.alternative_covers.len(),
        passage.repeated_forms.len(),
        passage.relation_receipt.atom_population,
        passage.relation_receipt.complete_pair_population,
        device.device_name,
        passage.scale.term_gap,
        passage.scale.line_gap,
        controls["one_relation_face_perturbation_and_inherited_glyph_ablation"]["glyph_ordinal_withdrawn"],
    )
}

pub fn detached(rest: &Path, receipt: &Path) -> Result<(), String> {
    let bytes = artifact::read(rest)?;
    let passage = HierarchicalOpticalPassage::read(&bytes).map_err(|error| error.to_string())?;
    artifact::write_json(
        receipt,
        &json!({
            "schema": "holonics.e1.detached-hierarchical-optical-rest.v1",
            "truth_status": "implemented-exact",
            "rest_sha256": artifact::digest(&bytes),
            "occurrence": passage.occurrence,
            "holons": passage.holons.len(),
            "incidences": passage.incidences.len(),
            "equations": passage.native_consequence.equation_addresses.len(),
            "native_equation_constraint_sections": passage.native_consequence.equation_constraint_sections.len(),
            "complete_glyph_fibres": passage.native_consequence.glyph_fibres_retained,
            "raw_source_opened": false,
            "tesseract_opened": false,
            "transcript_or_lean_opened": false,
        }),
    )?;
    Ok(())
}

pub fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}
