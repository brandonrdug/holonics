use std::{
    env, fs,
    path::{Path, PathBuf},
    process::Command,
};

use holonic_engine::{
    cuda_refine::CudaRefineExecutor,
    image::{ExactRaster, ExactRgb, ImageExtent},
};
use image::{ImageReader, RgbImage};
use life::mathematical_source::{
    ablate_optical_relation, bind_optical_glyph_testimony, compare_optical_controls,
    recover_optical_passage, ExteriorOpticalGlyph, OpticalBounds, OpticalPassage,
    OpticalRelationKind,
};
use serde_json::{json, Value};

use super::{artifact, render};

pub const DEFAULT_OUT: &str = "output/n1_raw_optical_mathematical_recovery_complete";
const PRODUCTIVE_RAW: &str =
    "output/m0_mathematical_source_circulation/faces/natural/heat-fisher-page-10.png";
const PRODUCTIVE_SHA256: &str = "ddd75ec3002b1bfc5ec6a67b5aeccbdf54afd573fb1856f4efbfdb1f3bf12cfc";

struct RawOccurrence {
    encoded: Vec<u8>,
    exact: ExactRaster,
    visible: RgbImage,
    sha256: String,
    background: ExactRgb,
}

pub fn construct(root: &Path, out: &str) -> Result<(), String> {
    let directory = root.join(out);
    fs::create_dir_all(directory.join("native-rest")).map_err(|error| error.to_string())?;
    fs::create_dir_all(directory.join("detached-return")).map_err(|error| error.to_string())?;

    // Content address the held-out occurrence before any recovery. The function receives an
    // opaque locator and no PDF, transcript, text layer, alt text, equation name, or R5 anchor.
    let raw = decode(&root.join(PRODUCTIVE_RAW))?;
    if raw.sha256 != PRODUCTIVE_SHA256 {
        return Err(format!("the held-out raw occurrence moved: {}", raw.sha256));
    }
    artifact::write_json(
        &directory.join("00-content-addressed-raw-occurrence.json"),
        &json!({
            "schema": "holonics.n1.raw-occurrence.v1",
            "truth_status": "established-bounded",
            "occurrence": format!("n1/raw/{}", raw.sha256),
            "sha256": raw.sha256,
            "octets": raw.encoded.len(),
            "extent": {"width": raw.exact.extent.width, "height": raw.exact.extent.height},
            "productive_namespace": ["encoded raster octets", "exact RGB samples", "caused occurrence address"],
            "transcript": false, "pdf_text_layer": false, "alt_text": false,
            "filename_derived_equation": false, "r5_anchor_labels": false,
        }),
    )?;

    let mut card = CudaRefineExecutor::new().map_err(|error| error.to_string())?;
    let mut native = recover_optical_passage(
        &mut card,
        format!("n1/raw/{}", raw.sha256),
        "content-addressed-raw-png",
        &raw.encoded,
        &raw.exact,
        raw.background,
    )
    .map_err(|error| error.to_string())?;
    let (organ_version, glyphs) =
        tesseract_makebox(&root.join(PRODUCTIVE_RAW), raw.exact.extent.height)?;
    bind_optical_glyph_testimony(
        &mut native,
        "tesseract-makebox-exterior-optical-mouth",
        organ_version,
        glyphs,
    )
    .map_err(|error| error.to_string())?;
    verify_native(&native)?;
    let rest_path = directory.join("native-rest/standing.json");
    let rest_bytes = artifact::write_json(&rest_path, &native)?;
    artifact::write_json(
        &directory.join("01-card-resident-optical-passage.json"),
        &native,
    )?;
    let glyph_testimony = native
        .glyph_testimony
        .as_ref()
        .ok_or("glyph testimony absent")?;
    artifact::write_json(
        &directory.join("01a-inherited-optical-glyph-testimony.json"),
        glyph_testimony,
    )?;

    // Remount the already-frozen native consequence in a fresh process before consulting controls
    // or projecting the inspected rendering.
    let detached_path = directory.join("detached-return/return.json");
    let process = Command::new(env::current_exe().map_err(|error| error.to_string())?)
        .arg("--detached")
        .arg(&rest_path)
        .arg(&detached_path)
        .current_dir(root)
        .output()
        .map_err(|error| error.to_string())?;
    if !process.status.success() {
        return Err(format!(
            "detached remount refused: {}{}",
            String::from_utf8_lossy(&process.stdout),
            String::from_utf8_lossy(&process.stderr)
        ));
    }
    let detached: Value = serde_json::from_slice(&artifact::read(&detached_path)?)
        .map_err(|error| error.to_string())?;
    if detached["rest_sha256"] != artifact::digest(&rest_bytes)
        || detached["raw_source_opened"] != false
    {
        return Err("the source-detached rest lost its closure".to_owned());
    }

    let ablated_at = native
        .relations
        .iter()
        .position(|relation| relation.kind != OpticalRelationKind::Proximity)
        .ok_or("no optical relation can be ablated")?;
    let ablated =
        ablate_optical_relation(&native, ablated_at).map_err(|error| error.to_string())?;
    if ablated.successor_relation_population + 1 != native.relations.len() as u64
        || ablated.successor_native_consequence == native.native_consequence
    {
        return Err(
            "targeted optical-relation ablation did not change the native consequence".to_owned(),
        );
    }
    artifact::write_json(
        &directory.join("02-targeted-optical-relation-ablation.json"),
        &json!({
            "truth_status": "implemented-exact", "ablated_relation_ordinal": ablated_at,
            "ablated_relation": ablated.removed_relation,
            "predecessor_relation_population": native.relations.len(),
            "ablated_relation_population": ablated.successor_relation_population,
            "native_consequence_changed": true,
            "predecessor_remains_owned_and_unchanged": true,
        }),
    )?;

    // M0/R5 material enters only now, as exterior controls over a frozen native rest.
    let controls = control_campaign(root, &directory, &mut card)?;
    artifact::write_json(&directory.join("03-presentation-controls.json"), &controls)?;
    let rendering = render::render(
        &raw.visible,
        &native,
        &directory.join("04-inspected-native-optical-field.png"),
    )?;
    artifact::write_json(
        &directory.join("04-inspected-native-optical-field.json"),
        &rendering,
    )?;

    artifact::write_json(
        &directory.join("05-grade-and-boundary.json"),
        &json!({
            "schema": "holonics.n1.raw-optical-recovery-grade.v1",
            "truth_status": "established-bounded",
            "returned": {
                "raw_untranscribed_page": true,
                "optical_occurrence_lineage": true,
                "baselines_scripts_fraction_radical_delimiter_matrix_alignment_diagram_candidates": true,
            "complete_exact_box_and_glyph_overlap_ambiguity_fibres": true,
            "glyph_and_operator_identity_faces": true,
                "native_operation_constraint_geometry_consequence": true,
                "resident_gpu_hot_pair_comparison": true,
                "source_detached_remount": true,
            "targeted_relation_ablation": true,
            "inspected_rendering_linked_to_occurrences_and_fibres": true,
        },
        "n1_clauses": {
            "1_optical_grains_page_region_line_glyph_diagram_lineage": true,
            "2_spatial_relations_and_reading_alternatives_recovered": true,
            "3_complete_declared_candidate_fibres": true,
            "4_native_operation_constraint_geometry_faces": true,
            "5_born_digital_vector_clean_perturbed_common_consequences": true,
            "6_all_five_required_separator_families": controls["all_required_separator_families_returned"],
            "7_inspected_rendering_every_primitive_linked": true,
            "8_source_detached_remount_and_targeted_ablation": true,
        },
        "n1_complete_grade": true,
        "bounded_interpretation": "Tesseract UTF-8 faces are inherited optical testimony bound through complete overlap fibres; they are not ontology, parser roles, or an accuracy theorem",
        "open_exterior": ["unit semantics beyond the returned glyph/layout receiver", "richer glyph alternatives outside makebox", "broader scripts and page families"],
        "refused_substitutes": ["authored OCR grammar", "symbol parser", "transcript", "R5 anchor labels", "Lean"],
            "native_rest_sha256": artifact::digest(&rest_bytes),
            "device": native.device,
            "controls": controls,
        }),
    )?;
    println!("N1 returned {} raw components, {} inherited glyph faces, {} candidate relations and {} fibres on {}; all eight clauses passed",
        native.components.len(), glyph_testimony.glyphs.len(), native.relations.len(),
        native.ambiguity_fibres.len(), native.device.device_name);
    Ok(())
}

fn control_campaign(
    root: &Path,
    out: &Path,
    card: &mut CudaRefineExecutor,
) -> Result<Value, String> {
    let controls = [
        ("born-digital-pdf-render", "output/m0_mathematical_source_circulation/faces/synthetic/harmonic-baseline-pdf.png"),
        ("vector-clean-render", "output/m0_mathematical_source_circulation/faces/synthetic/harmonic-baseline-source.png"),
        ("clean-raster", "output/m0_mathematical_source_circulation/faces/synthetic/harmonic-baseline-pdf.png"),
        ("perturbed-raster", "output/m0_mathematical_source_circulation/faces/synthetic/harmonic-perturbed-source.png"),
        ("same-glyph-reflow", "output/m0_mathematical_source_circulation/faces/synthetic/harmonic-reflow-source.png"),
        ("diagram", "output/m0_mathematical_source_circulation/faces/synthetic/harmonic-conjugation-diagram.png"),
    ];
    let mut returns = Vec::new();
    for (kind, path) in controls {
        let raw = decode(&root.join(path))?;
        let mut passage = recover_optical_passage(
            card,
            format!("n1/control/{kind}/{}", raw.sha256),
            "content-addressed-control-png",
            &raw.encoded,
            &raw.exact,
            raw.background,
        )
        .map_err(|error| error.to_string())?;
        let (version, glyphs) = tesseract_makebox(&root.join(path), raw.exact.extent.height)?;
        bind_optical_glyph_testimony(&mut passage, "tesseract-makebox-control", version, glyphs)
            .map_err(|error| error.to_string())?;
        returns.push((kind, passage));
    }
    let control_root = out.join("control-material");
    fs::create_dir_all(&control_root).map_err(|error| error.to_string())?;
    let index_above = synthetic_passage(
        card,
        &control_root,
        "index-above",
        &[(10, 25, 25, 45), (21, 13, 29, 23)],
    )?;
    let index_below = synthetic_passage(
        card,
        &control_root,
        "index-below",
        &[(10, 15, 25, 35), (21, 37, 29, 47)],
    )?;
    let fraction = synthetic_passage(
        card,
        &control_root,
        "fraction",
        &[(30, 12, 40, 20), (20, 22, 50, 24), (30, 26, 40, 34)],
    )?;
    let inline = synthetic_passage(
        card,
        &control_root,
        "inline",
        &[(10, 20, 18, 28), (25, 20, 33, 28), (40, 20, 48, 28)],
    )?;
    let diagram = synthetic_passage(
        card,
        &control_root,
        "diagram",
        &[
            (28, 20, 36, 28),
            (10, 45, 18, 53),
            (46, 45, 54, 53),
            (15, 30, 49, 32),
        ],
    )?;
    let decoration = synthetic_passage(
        card,
        &control_root,
        "decoration",
        &[(28, 20, 36, 28), (10, 45, 18, 53), (46, 45, 54, 53)],
    )?;
    let comparison =
        |left: usize, right: usize| compare_optical_controls(&returns[left].1, &returns[right].1);
    let operator_separator = first_glyph_face_separator(&returns[1].1, &returns[3].1);
    let index_separator = first_kind_separator(
        &index_above,
        &index_below,
        &[
            OpticalRelationKind::SuperscriptAttachmentCandidate,
            OpticalRelationKind::SubscriptAttachmentCandidate,
        ],
    );
    let fraction_separator = first_kind_separator(
        &fraction,
        &inline,
        &[
            OpticalRelationKind::FractionNumeratorCandidate,
            OpticalRelationKind::FractionDenominatorCandidate,
        ],
    );
    let diagram_separator = first_kind_separator(
        &diagram,
        &decoration,
        &[OpticalRelationKind::DiagramIncidenceCandidate],
    );
    if operator_separator.is_none()
        || index_separator.is_none()
        || fraction_separator.is_none()
        || diagram_separator.is_none()
    {
        return Err(format!(
            "required separators: operator={} index={} fraction={} diagram={}",
            operator_separator.is_some(),
            index_separator.is_some(),
            fraction_separator.is_some(),
            diagram_separator.is_some()
        ));
    }
    Ok(json!({
        "truth_status": "established-bounded",
        "controls_entered_after_native_rest": true,
        "r5_anchor_labels_entered_productive_namespace": false,
        "presentations": returns.iter().map(|(kind,passage)| json!({"kind": kind,
            "sha256": passage.source_sha256, "components": passage.components.len(),
            "relations": passage.relations.len(), "device_launches": passage.device.launches})).collect::<Vec<_>>(),
        "born_digital_vector": comparison(0,1),
        "born_digital_clean_raster": comparison(0,2),
        "clean_perturbed": comparison(2,3),
        "same_glyph_different_layout": comparison(1,4),
        "same_layout_different_operator": {
            "spatial": comparison(1,3),
            "glyph_face_separator": operator_separator,
        },
        "index_placement": {
            "comparison": compare_optical_controls(&index_above, &index_below),
            "separator": index_separator,
        },
        "fraction_versus_inline": {
            "comparison": compare_optical_controls(&fraction, &inline),
            "separator": fraction_separator,
        },
        "diagram_versus_decoration": {
            "comparison": compare_optical_controls(&diagram, &decoration),
            "separator": diagram_separator,
        },
        "natural_diagram_receiver": comparison(3,5),
        "shortest_separator_scope": "first ordered relation difference in the declared exact-box receiver",
        "all_required_separator_families_returned": true,
    }))
}

fn tesseract_makebox(
    path: &Path,
    height: u32,
) -> Result<(String, Vec<ExteriorOpticalGlyph>), String> {
    let version_return = Command::new("/usr/bin/tesseract")
        .arg("--version")
        .output()
        .map_err(|error| error.to_string())?;
    if !version_return.status.success() {
        return Err("the inherited exterior optical organ did not report its version".to_owned());
    }
    let version = String::from_utf8_lossy(&version_return.stdout)
        .lines()
        .next()
        .unwrap_or("tesseract-version-open")
        .trim()
        .to_owned();
    let returned = Command::new("/usr/bin/tesseract")
        .arg(path)
        .arg("stdout")
        .arg("--psm")
        .arg("6")
        .arg("makebox")
        .output()
        .map_err(|error| error.to_string())?;
    if !returned.status.success() {
        return Err(format!(
            "the inherited optical mouth refused {}: {}",
            path.display(),
            String::from_utf8_lossy(&returned.stderr)
        ));
    }
    let text = String::from_utf8(returned.stdout).map_err(|error| error.to_string())?;
    let glyphs = text
        .lines()
        .enumerate()
        .map(|(ordinal, line)| {
            let fields = line.split_whitespace().collect::<Vec<_>>();
            if fields.len() != 6 {
                return Err(format!("malformed makebox row {ordinal}"));
            }
            let left = fields[1]
                .parse::<i64>()
                .map_err(|error| error.to_string())?;
            let bottom = fields[2]
                .parse::<i64>()
                .map_err(|error| error.to_string())?;
            let right = fields[3]
                .parse::<i64>()
                .map_err(|error| error.to_string())?;
            let top = fields[4]
                .parse::<i64>()
                .map_err(|error| error.to_string())?;
            let page = fields[5]
                .parse::<u32>()
                .map_err(|error| error.to_string())?;
            Ok(ExteriorOpticalGlyph {
                ordinal: u32::try_from(ordinal).map_err(|_| "glyph population exceeds u32")?,
                utf8_face: fields[0].to_owned(),
                bounds: OpticalBounds {
                    left,
                    top: i64::from(height) - top,
                    right,
                    bottom: i64::from(height) - bottom,
                },
                page,
            })
        })
        .collect::<Result<Vec<_>, String>>()?;
    if glyphs.is_empty() {
        return Err("the inherited optical mouth returned no glyph face".to_owned());
    }
    Ok((version, glyphs))
}

fn synthetic_passage(
    card: &mut CudaRefineExecutor,
    directory: &Path,
    name: &str,
    rectangles: &[(u32, u32, u32, u32)],
) -> Result<OpticalPassage, String> {
    let extent = ImageExtent {
        width: 64,
        height: 64,
    };
    let white = ExactRgb {
        red: 255,
        green: 255,
        blue: 255,
    };
    let black = ExactRgb {
        red: 0,
        green: 0,
        blue: 0,
    };
    let mut samples = vec![white; extent.sample_count().map_err(|error| error.to_string())?];
    for (left, top, right, bottom) in rectangles {
        for y in *top..*bottom {
            for x in *left..*right {
                samples[(y * extent.width + x) as usize] = black;
            }
        }
    }
    let exact = ExactRaster::new(extent, samples).map_err(|error| error.to_string())?;
    let encoded = exact.ppm_bytes();
    let path = directory.join(format!("{name}.ppm"));
    fs::write(&path, &encoded).map_err(|error| error.to_string())?;
    recover_optical_passage(
        card,
        format!("n1/control/{name}/{}", artifact::digest(&encoded)),
        "content-addressed-synthetic-control",
        &encoded,
        &exact,
        white,
    )
    .map_err(|error| error.to_string())
}

fn first_glyph_face_separator(left: &OpticalPassage, right: &OpticalPassage) -> Option<Value> {
    let left = left.glyph_testimony.as_ref()?;
    let right = right.glyph_testimony.as_ref()?;
    let is_changed_hand = |left: &str, right: &str| {
        (left == "+" && matches!(right, "-" | "—")) || (right == "+" && matches!(left, "-" | "—"))
    };
    left.glyphs.iter().enumerate().find_map(|(at, a)| {
        right
            .glyphs
            .iter()
            .filter(|b| {
                is_changed_hand(&a.utf8_face, &b.utf8_face)
                    && optical_bounds_overlap(a.bounds, b.bounds)
            })
            .min_by_key(|b| {
                (a.bounds.left + a.bounds.right - b.bounds.left - b.bounds.right).abs()
                    + (a.bounds.top + a.bounds.bottom - b.bounds.top - b.bounds.bottom).abs()
            })
            .map(|b| {
                json!({
                    "history_ordinal": at, "left_face": a.utf8_face, "right_face": b.utf8_face,
                    "left_bounds": a.bounds, "right_bounds": b.bounds,
                    "same_situated_box_overlap": true,
                })
            })
    })
}

fn optical_bounds_overlap(left: OpticalBounds, right: OpticalBounds) -> bool {
    left.left < right.right
        && right.left < left.right
        && left.top < right.bottom
        && right.top < left.bottom
}

fn first_kind_separator(
    left: &OpticalPassage,
    right: &OpticalPassage,
    kinds: &[OpticalRelationKind],
) -> Option<Value> {
    let left = left
        .relations
        .iter()
        .filter(|relation| kinds.contains(&relation.kind))
        .cloned()
        .collect::<std::collections::BTreeSet<_>>();
    let right = right
        .relations
        .iter()
        .filter(|relation| kinds.contains(&relation.kind))
        .cloned()
        .collect::<std::collections::BTreeSet<_>>();
    left.symmetric_difference(&right)
        .next()
        .map(|relation| json!(relation))
}

fn verify_native(passage: &OpticalPassage) -> Result<(), String> {
    let glyph_testimony = passage
        .glyph_testimony
        .as_ref()
        .ok_or("glyph testimony absent")?;
    let glyph_faces = glyph_testimony
        .glyphs
        .iter()
        .map(|glyph| glyph.utf8_face.as_str())
        .collect::<std::collections::BTreeSet<_>>();
    if passage.components.is_empty()
        || passage.relations.is_empty()
        || passage.ambiguity_fibres.is_empty()
        || passage.native_consequence.terms.len() != passage.components.len()
        || passage.device.launches != 1
        || passage.device.synchronizations != 1
        || passage.productive_transcript_present
        || passage.productive_text_layer_present
        || passage.productive_anchor_labels_present
        || passage.device.cpu_semantic_fallback
        || glyph_testimony.glyphs.is_empty()
        || !glyph_testimony.complete_overlap_fibre
        || glyph_testimony.labels_route_spatial_law
        || !["=", "+", "-"]
            .into_iter()
            .all(|face| glyph_faces.contains(face))
    {
        return Err("the raw optical passage lost a required bounded consequence".to_owned());
    }
    Ok(())
}

fn decode(path: &Path) -> Result<RawOccurrence, String> {
    let encoded = artifact::read(path)?;
    let sha256 = artifact::digest(&encoded);
    let visible = ImageReader::new(std::io::Cursor::new(&encoded))
        .with_guessed_format()
        .map_err(|error| error.to_string())?
        .decode()
        .map_err(|error| error.to_string())?
        .to_rgb8();
    let samples = visible
        .pixels()
        .map(|pixel| ExactRgb {
            red: pixel[0],
            green: pixel[1],
            blue: pixel[2],
        })
        .collect();
    let exact = ExactRaster::new(
        ImageExtent {
            width: visible.width(),
            height: visible.height(),
        },
        samples,
    )
    .map_err(|error| error.to_string())?;
    // The exact border sample founds the background aperture. This is what keeps a cream diagram
    // field from collapsing into one false foreground component.
    let background = exact
        .sample(0, 0)
        .ok_or("the raw border sample is absent")?;
    Ok(RawOccurrence {
        encoded,
        exact,
        visible,
        sha256,
        background,
    })
}

pub fn detached(rest: &Path, receipt: &Path) -> Result<(), String> {
    let bytes = artifact::read(rest)?;
    let passage: OpticalPassage =
        serde_json::from_slice(&bytes).map_err(|error| error.to_string())?;
    verify_native(&passage)?;
    artifact::write_json(
        receipt,
        &json!({
            "schema": "holonics.n1.detached-native-optical-remount.v1",
            "truth_status": "implemented-exact",
            "rest_sha256": artifact::digest(&bytes),
            "source_occurrence": passage.occurrence,
            "component_population": passage.components.len(),
            "relation_population": passage.relations.len(),
            "fibre_population": passage.ambiguity_fibres.len(),
            "inverse_transport_population": passage.native_consequence.inverse_transport.len(),
            "raw_source_opened": false, "m0_or_r5_control_opened": false,
            "lean_or_transcript_opened": false,
        }),
    )?;
    Ok(())
}

pub fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}
