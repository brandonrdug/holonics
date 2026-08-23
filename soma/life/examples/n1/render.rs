use std::{collections::BTreeSet, path::Path};

use image::{Rgb, RgbImage};
use life::mathematical_source::{OpticalPassage, OpticalRelationKind};
use serde_json::{json, Value};

use super::artifact;

const TERM: Rgb<u8> = Rgb([255, 92, 92]);
const STRUCTURE: Rgb<u8> = Rgb([30, 190, 255]);
const AMBIGUOUS: Rgb<u8> = Rgb([246, 201, 69]);

pub fn render(raw: &RgbImage, passage: &OpticalPassage, path: &Path) -> Result<Value, String> {
    if raw.width() != passage.width || raw.height() != passage.height {
        return Err("raw raster and native optical extent disagree".to_owned());
    }
    let mut image = raw.clone();
    let mut primitives = Vec::with_capacity(passage.components.len());
    for (ordinal, component) in passage.components.iter().enumerate() {
        let fibre_subjects = passage
            .ambiguity_fibres
            .iter()
            .filter(|fibre| {
                fibre.alternatives.iter().any(|alternative| {
                    alternative.from as usize == ordinal || alternative.to as usize == ordinal
                })
            })
            .map(|fibre| fibre.subject.clone())
            .collect::<BTreeSet<_>>();
        let structural = passage.relations.iter().any(|relation| {
            (relation.from as usize == ordinal || relation.to as usize == ordinal)
                && !matches!(
                    relation.kind,
                    OpticalRelationKind::Proximity
                        | OpticalRelationKind::BaselineCandidate
                        | OpticalRelationKind::ReadingOrderAlternative
                )
        });
        let color = if !fibre_subjects.is_empty() {
            AMBIGUOUS
        } else if structural {
            STRUCTURE
        } else {
            TERM
        };
        draw_box(
            &mut image,
            component.bounds.left,
            component.bounds.top,
            component.bounds.right,
            component.bounds.bottom,
            color,
        );
        primitives.push(json!({
            "primitive": ordinal,
            "occurrence": component.address,
            "bounds": component.bounds,
            "region": component.region,
            "baseline_component": component.baseline_component,
            "four_connected_fibre": component.four_connected_fibre,
            "ambiguity_fibres": fibre_subjects,
        }));
    }
    image.save(path).map_err(|error| error.to_string())?;
    let bytes = artifact::read(path)?;
    Ok(json!({
        "schema": "holonics.n1.inspected-optical-rendering.v1",
        "truth_status": "implemented-exact",
        "source_occurrence": passage.occurrence,
        "source_sha256": passage.source_sha256,
        "png_sha256": artifact::digest(&bytes),
        "extent": {"width": passage.width, "height": passage.height},
        "legend": {"term": [255,92,92], "structural-candidate": [30,190,255], "ambiguity-fibre": [246,201,69]},
        "visible_primitives": primitives,
        "every_overlay_primitive_has_occurrence_lineage": true,
        "every_ambiguous_primitive_names_its_complete_declared_fibre": true,
        "caption_ocr_or_alt_text_used": false,
    }))
}

fn draw_box(image: &mut RgbImage, left: i64, top: i64, right: i64, bottom: i64, color: Rgb<u8>) {
    let width = i64::from(image.width());
    let height = i64::from(image.height());
    if width == 0 || height == 0 {
        return;
    }
    let left = left.clamp(0, width - 1) as u32;
    let right = (right - 1).clamp(0, width - 1) as u32;
    let top = top.clamp(0, height - 1) as u32;
    let bottom = (bottom - 1).clamp(0, height - 1) as u32;
    for x in left..=right {
        image.put_pixel(x, top, color);
        image.put_pixel(x, bottom, color);
    }
    for y in top..=bottom {
        image.put_pixel(left, y, color);
        image.put_pixel(right, y, color);
    }
}
