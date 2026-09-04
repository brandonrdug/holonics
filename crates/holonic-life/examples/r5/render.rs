use std::fmt::Write as _;
use std::fs;
use std::path::Path;

use image::{ImageReader, Rgb, RgbImage};
use life::mathematical_particle::AnchorSection;
use serde_json::{json, Value};

use super::artifact;

const BACKGROUND: Rgb<u8> = Rgb([8, 13, 24]);
const NOTATION: Rgb<u8> = Rgb([240, 230, 140]);
const VECTOR: Rgb<u8> = Rgb([71, 190, 255]);
const RASTER_FOUR: Rgb<u8> = Rgb([244, 113, 181]);
const RASTER_EIGHT: Rgb<u8> = Rgb([167, 139, 250]);
const BOUNDARY: Rgb<u8> = Rgb([226, 232, 240]);

pub fn render(
    sections: &[AnchorSection],
    mesh_path: &Path,
    svg_path: &Path,
    png_path: &Path,
) -> Result<Value, String> {
    if sections.is_empty()
        || sections
            .iter()
            .enumerate()
            .any(|(at, section)| section.ordinal != at as u32)
    {
        return Err("the held-out anchor field is absent or noncontiguous".to_owned());
    }
    let width = u32::try_from(sections.len())
        .map_err(|_| "render width exceeds u32".to_owned())?
        .checked_add(2)
        .ok_or("render width overflow")?;
    let height = sections
        .iter()
        .map(total_height)
        .collect::<Result<Vec<_>, _>>()?
        .into_iter()
        .max()
        .ok_or("render height absent")?
        .checked_add(2)
        .ok_or("render height overflow")?;
    let mesh = exact_mesh(sections, width, height)?;
    let mesh_bytes = artifact::write_json(mesh_path, &mesh)?;

    let mut image = RgbImage::from_pixel(width, height, BACKGROUND);
    for x in 0..width {
        image.put_pixel(x, 0, BOUNDARY);
        image.put_pixel(x, height - 1, BOUNDARY);
    }
    for y in 0..height {
        image.put_pixel(0, y, BOUNDARY);
        image.put_pixel(width - 1, y, BOUNDARY);
    }
    for section in sections {
        let x = section.ordinal + 1;
        let mut y = height - 2;
        image.put_pixel(x, y, NOTATION);
        for (count, color) in [
            (section.vector_candidates, VECTOR),
            (section.raster_four_candidates, RASTER_FOUR),
            (section.raster_eight_candidates, RASTER_EIGHT),
        ] {
            for _ in 0..count {
                y = y
                    .checked_sub(1)
                    .ok_or("render bar crossed its exact boundary")?;
                image.put_pixel(x, y, color);
            }
        }
    }
    image.save(png_path).map_err(|error| error.to_string())?;
    verify_png(png_path, sections, width, height)?;

    let mut svg = format!(
        "<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 {width} {height}\" shape-rendering=\"crispEdges\">\n<rect width=\"{width}\" height=\"{height}\" fill=\"#080d18\"/>\n"
    );
    writeln!(
        svg,
        "<path d=\"M0 0H{width}V{height}H0Z\" fill=\"none\" stroke=\"#e2e8f0\" stroke-width=\"1\"/>"
    )
    .map_err(|error| error.to_string())?;
    for section in sections {
        let x = section.ordinal + 1;
        let mut y = height - 2;
        writeln!(
            svg,
            "<rect x=\"{x}\" y=\"{y}\" width=\"1\" height=\"1\" fill=\"#f0e68c\"/>"
        )
        .map_err(|error| error.to_string())?;
        for (count, color) in [
            (section.vector_candidates, "#47beff"),
            (section.raster_four_candidates, "#f471b5"),
            (section.raster_eight_candidates, "#a78bfa"),
        ] {
            y = y
                .checked_sub(count)
                .ok_or("SVG bar crossed its exact boundary")?;
            writeln!(
                svg,
                "<rect x=\"{x}\" y=\"{y}\" width=\"1\" height=\"{count}\" fill=\"{color}\"/>"
            )
            .map_err(|error| error.to_string())?;
        }
    }
    svg.push_str("</svg>\n");
    fs::write(svg_path, svg.as_bytes()).map_err(|error| error.to_string())?;
    if !svg.contains(&format!("viewBox=\"0 0 {width} {height}\"")) {
        return Err("the vector face lost its exact derived extent".to_owned());
    }
    let png_bytes = fs::read(png_path).map_err(|error| error.to_string())?;
    let svg_bytes = fs::read(svg_path).map_err(|error| error.to_string())?;
    Ok(json!({
        "schema": "holonics.r5.exact-joint-rendering-receipt.v1",
        "truth_status": "implemented-exact",
        "heldout_anchor_population": sections.len(),
        "extent": {"width": width, "height": height, "derived_only_from_retained_sections": true},
        "oriented_chart": {"x": "anchor order advances right", "y": "candidate incidence advances upward from the notation boundary"},
        "typed_incidence": {
            "notation": sections.len(),
            "vector": sections.iter().map(|section| u64::from(section.vector_candidates)).sum::<u64>(),
            "raster_four": sections.iter().map(|section| u64::from(section.raster_four_candidates)).sum::<u64>(),
            "raster_eight": sections.iter().map(|section| u64::from(section.raster_eight_candidates)).sum::<u64>(),
        },
        "mesh_sha256": artifact::digest(&mesh_bytes),
        "svg_sha256": artifact::digest(&svg_bytes),
        "png_sha256": artifact::digest(&png_bytes),
        "mesh_svg_png_share_one_exact_typed_object": true,
        "raster_pixels_recounted_after_decode": true,
        "caption_or_ocr_mediation": false,
    }))
}

fn total_height(section: &AnchorSection) -> Result<u32, String> {
    section
        .vector_candidates
        .checked_add(section.raster_four_candidates)
        .and_then(|value| value.checked_add(section.raster_eight_candidates))
        .and_then(|value| value.checked_add(1))
        .ok_or_else(|| "render section extent overflow".to_owned())
}

fn exact_mesh(sections: &[AnchorSection], width: u32, height: u32) -> Result<Value, String> {
    let cells = sections
        .iter()
        .map(|section| {
            Ok(json!({
                "anchor": section.ordinal,
                "x": section.ordinal + 1,
                "oriented_boundary": [height - 2, 1],
                "typed_segments": [
                    {"port": "notation", "multiplicity": 1},
                    {"port": "vector", "multiplicity": section.vector_candidates},
                    {"port": "raster-four", "multiplicity": section.raster_four_candidates},
                    {"port": "raster-eight", "multiplicity": section.raster_eight_candidates},
                ],
            }))
        })
        .collect::<Result<Vec<_>, String>>()?;
    Ok(json!({
        "schema": "holonics.r5.exact-joint-media-mesh.v1",
        "truth_status": "implemented-exact",
        "extent": {"width": width, "height": height},
        "boundary_hand": {"x": 1, "y": -1},
        "cells": cells,
        "open_exterior": ["a richer media receiver can reopen each retained candidate identity"],
    }))
}

fn verify_png(
    path: &Path,
    sections: &[AnchorSection],
    width: u32,
    height: u32,
) -> Result<(), String> {
    let decoded = ImageReader::open(path)
        .map_err(|error| error.to_string())?
        .decode()
        .map_err(|error| error.to_string())?
        .to_rgb8();
    if decoded.width() != width || decoded.height() != height {
        return Err("the decoded raster extent differs from the exact mesh".to_owned());
    }
    let count = |color: Rgb<u8>| decoded.pixels().filter(|pixel| **pixel == color).count() as u64;
    let expected_vector: u64 = sections
        .iter()
        .map(|section| u64::from(section.vector_candidates))
        .sum();
    let expected_four: u64 = sections
        .iter()
        .map(|section| u64::from(section.raster_four_candidates))
        .sum();
    let expected_eight: u64 = sections
        .iter()
        .map(|section| u64::from(section.raster_eight_candidates))
        .sum();
    if count(NOTATION) != sections.len() as u64
        || count(VECTOR) != expected_vector
        || count(RASTER_FOUR) != expected_four
        || count(RASTER_EIGHT) != expected_eight
    {
        return Err(
            "the decoded raster incidence differs from the exact typed sections".to_owned(),
        );
    }
    Ok(())
}
