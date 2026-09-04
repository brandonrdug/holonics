use std::fmt::Write as _;
use std::fs;
use std::path::Path;

use image::{ImageReader, Rgb, RgbImage};
use life::mathematical_particle::AnchorSection;
use serde_json::{json, Value};

use super::artifact;

const BACKGROUND: Rgb<u8> = Rgb([7, 12, 23]);
const FOUR: Rgb<u8> = Rgb([244, 113, 181]);
const EIGHT: Rgb<u8> = Rgb([96, 165, 250]);
const EQUAL: Rgb<u8> = Rgb([52, 211, 153]);
const BOUNDARY: Rgb<u8> = Rgb([226, 232, 240]);

pub fn exact_difference_field(
    sections: &[AnchorSection],
    directory: &Path,
) -> Result<Value, String> {
    if sections.is_empty() {
        return Err("the exact difference field has no anchor sections".to_owned());
    }
    let width = (sections.len() as u32)
        .checked_mul(2)
        .and_then(|width| width.checked_add(2))
        .ok_or("difference-field width overflow")?;
    let maximum = sections
        .iter()
        .map(|section| {
            section
                .raster_four_candidates
                .max(section.raster_eight_candidates)
        })
        .max()
        .ok_or("difference-field height absent")?;
    let height = maximum
        .checked_add(3)
        .ok_or("difference-field height overflow")?;
    let mesh = json!({
        "schema": "holonics.r6.exact-raster-difference-mesh.v1",
        "truth_status": "implemented-exact",
        "extent": {"width": width, "height": height},
        "boundary_hand": {"anchor": 1, "candidate_incidence": -1},
        "cells": sections.iter().map(|section| json!({
            "anchor": section.ordinal,
            "raster_four": section.raster_four_candidates,
            "raster_eight": section.raster_eight_candidates,
            "oriented_difference": i64::from(section.raster_four_candidates) - i64::from(section.raster_eight_candidates),
        })).collect::<Vec<_>>(),
        "open_exterior": ["candidate identities remain in the R5 reconstruction fibre"],
    });
    let mesh_bytes = artifact::write_json(directory.join("06-exact-difference.mesh.json"), &mesh)?;

    let mut image = RgbImage::from_pixel(width, height, BACKGROUND);
    for x in 0..width {
        image.put_pixel(x, 0, BOUNDARY);
        image.put_pixel(x, height - 1, BOUNDARY);
    }
    for section in sections {
        let x = section.ordinal * 2 + 1;
        let four = section.raster_four_candidates;
        let eight = section.raster_eight_candidates;
        for step in 0..four {
            image.put_pixel(x, height - 2 - step, FOUR);
        }
        for step in 0..eight {
            image.put_pixel(x + 1, height - 2 - step, EIGHT);
        }
        if four == eight {
            image.put_pixel(x, 1, EQUAL);
            image.put_pixel(x + 1, 1, EQUAL);
        }
    }
    let png_path = directory.join("08-exact-difference.png");
    image.save(&png_path).map_err(|error| error.to_string())?;
    let decoded = ImageReader::open(&png_path)
        .map_err(|error| error.to_string())?
        .decode()
        .map_err(|error| error.to_string())?
        .to_rgb8();
    if decoded.width() != width || decoded.height() != height {
        return Err("the decoded exact difference raster changed extent".to_owned());
    }

    let mut svg = format!(
        "<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 {width} {height}\" shape-rendering=\"crispEdges\"><rect width=\"{width}\" height=\"{height}\" fill=\"#070c17\"/><g id=\"raster-four\">"
    );
    for section in sections {
        let x = section.ordinal * 2 + 1;
        let y = height - 1 - section.raster_four_candidates;
        writeln!(svg, "<rect x=\"{x}\" y=\"{y}\" width=\"1\" height=\"{}\" fill=\"#f471b5\"><title>anchor {}: four-connected {}</title></rect>", section.raster_four_candidates, section.ordinal, section.raster_four_candidates).map_err(|error| error.to_string())?;
    }
    svg.push_str("</g><g id=\"raster-eight\">");
    for section in sections {
        let x = section.ordinal * 2 + 2;
        let y = height - 1 - section.raster_eight_candidates;
        writeln!(svg, "<rect x=\"{x}\" y=\"{y}\" width=\"1\" height=\"{}\" fill=\"#60a5fa\"><title>anchor {}: eight-connected {}</title></rect>", section.raster_eight_candidates, section.ordinal, section.raster_eight_candidates).map_err(|error| error.to_string())?;
    }
    svg.push_str("</g></svg>\n");
    let svg_path = directory.join("07-exact-difference.svg");
    fs::write(&svg_path, svg.as_bytes()).map_err(|error| error.to_string())?;
    let html = format!(
        "<!doctype html><meta charset=\"utf-8\"><title>R6 exact selectable atlas</title><style>body{{background:#070c17;color:#e2e8f0;font-family:system-ui}}label{{margin-right:1rem}}svg{{width:100%;image-rendering:pixelated}}body:not(.show-four) #raster-four{{display:none}}body:not(.show-eight) #raster-eight{{display:none}}</style><label><input id=\"four\" type=\"checkbox\" checked> four-connected</label><label><input id=\"eight\" type=\"checkbox\" checked> eight-connected</label>{svg}<script>const b=document.body;function r(){{b.classList.toggle('show-four',four.checked);b.classList.toggle('show-eight',eight.checked)}}four.onchange=eight.onchange=r;r()</script>"
    );
    fs::write(directory.join("09-interactive-atlas.html"), html.as_bytes())
        .map_err(|error| error.to_string())?;
    Ok(json!({
        "schema": "holonics.r6.exact-rendering-receipt.v1",
        "truth_status": "implemented-exact",
        "extent": {"width": width, "height": height},
        "mesh_sha256": artifact::digest(&mesh_bytes),
        "svg_sha256": artifact::digest(svg.as_bytes()),
        "png_sha256": artifact::digest(&fs::read(png_path).map_err(|error| error.to_string())?),
        "mesh_svg_png_share_one_exact_typed_object": true,
        "raster_extent_reopened_after_decode": true,
        "selectable_layers": ["raster-four", "raster-eight"],
    }))
}
