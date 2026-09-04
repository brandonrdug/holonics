use std::{collections::BTreeSet, path::Path};

use image::{imageops, ImageReader, Rgb, RgbImage};
use life::mathematical_source::{
    HierarchicalOpticalPassage, OpticalBounds, OpticalHolonGrain, OpticalObjectClass,
};
use serde_json::{json, Value};

use super::artifact;

const DECORATED: Rgb<u8> = Rgb([30, 190, 255]);
const TERM: Rgb<u8> = Rgb([40, 210, 110]);
const ASSEMBLY: Rgb<u8> = Rgb([220, 70, 255]);
const EQUATION: Rgb<u8> = Rgb([255, 60, 80]);
const BLOCK: Rgb<u8> = Rgb([255, 170, 30]);
const GLYPH: Rgb<u8> = Rgb([246, 201, 69]);

pub fn render(
    raw_path: &Path,
    passage: &HierarchicalOpticalPassage,
    directory: &Path,
) -> Result<Value, String> {
    let raw = ImageReader::open(raw_path)
        .map_err(|error| error.to_string())?
        .decode()
        .map_err(|error| error.to_string())?
        .to_rgb8();
    if raw.width() != passage.width || raw.height() != passage.height {
        return Err("the raw page and E1 rest have different extents".to_owned());
    }
    let equation_addresses = passage
        .classifications
        .iter()
        .filter(|face| face.classes.contains(&OpticalObjectClass::Equation))
        .map(|face| face.holon_address.as_str())
        .collect::<BTreeSet<_>>();
    let fraction_addresses = passage
        .classifications
        .iter()
        .filter(|face| face.classes.contains(&OpticalObjectClass::FractionAssembly))
        .map(|face| face.holon_address.as_str())
        .collect::<BTreeSet<_>>();

    let mut page = raw.clone();
    let mut page_primitives = Vec::new();
    for holon in passage.holons.iter().filter(|holon| {
        matches!(
            holon.grain,
            OpticalHolonGrain::GlyphOrSubfigure
                | OpticalHolonGrain::DecoratedSymbol
                | OpticalHolonGrain::Term
                | OpticalHolonGrain::Assembly
                | OpticalHolonGrain::RelationOrEquation
                | OpticalHolonGrain::LabelledOrDiagramBlock
        )
    }) {
        let color = color(
            holon.grain,
            equation_addresses.contains(holon.address_sha256.as_str()),
        );
        draw_box(&mut page, holon.bounds, color);
        page_primitives.push(json!({
            "address": holon.address_sha256,
            "grain": holon.grain,
            "bounds": holon.bounds,
            "constituents": holon.constituents.len(),
            "glyph_fibre": holon.glyph_ordinals,
        }));
    }
    let page_path = directory.join("04-hierarchical-page-overlay.png");
    page.save(&page_path).map_err(|error| error.to_string())?;

    let equation = passage
        .holons
        .iter()
        .filter(|holon| equation_addresses.contains(holon.address_sha256.as_str()))
        .max_by_key(|holon| {
            let fractions = holon
                .constituents
                .iter()
                .filter(|address| fraction_addresses.contains(address.as_str()))
                .count();
            (fractions, holon.glyph_ordinals.len())
        })
        .ok_or("the natural page returned no equation holon")?;
    let padding =
        i64::try_from(passage.scale.line_gap.saturating_mul(2)).map_err(|_| "focus padding")?;
    let focus = OpticalBounds {
        left: equation.bounds.left.saturating_sub(padding).max(0),
        top: equation.bounds.top.saturating_sub(padding).max(0),
        right: equation
            .bounds
            .right
            .saturating_add(padding)
            .min(i64::from(raw.width())),
        bottom: equation
            .bounds
            .bottom
            .saturating_add(padding)
            .min(i64::from(raw.height())),
    };
    let focus_width = u32::try_from(focus.right - focus.left).map_err(|_| "focus width")?;
    let focus_height = u32::try_from(focus.bottom - focus.top).map_err(|_| "focus height")?;
    if focus_width == 0 || focus_height == 0 {
        return Err("the equation focus collapsed".to_owned());
    }
    let mut focused = imageops::crop_imm(
        &raw,
        u32::try_from(focus.left).map_err(|_| "focus left")?,
        u32::try_from(focus.top).map_err(|_| "focus top")?,
        focus_width,
        focus_height,
    )
    .to_image();
    let mut focus_primitives = Vec::new();
    for holon in passage.holons.iter().filter(|holon| {
        overlaps(holon.bounds, focus)
            && matches!(
                holon.grain,
                OpticalHolonGrain::GlyphOrSubfigure
                    | OpticalHolonGrain::DecoratedSymbol
                    | OpticalHolonGrain::Term
                    | OpticalHolonGrain::Assembly
                    | OpticalHolonGrain::RelationOrEquation
            )
    }) {
        let color = match holon.grain {
            OpticalHolonGrain::GlyphOrSubfigure => GLYPH,
            _ => color(
                holon.grain,
                equation_addresses.contains(holon.address_sha256.as_str()),
            ),
        };
        let local = OpticalBounds {
            left: holon.bounds.left - focus.left,
            top: holon.bounds.top - focus.top,
            right: holon.bounds.right - focus.left,
            bottom: holon.bounds.bottom - focus.top,
        };
        draw_box(&mut focused, local, color);
        focus_primitives.push(json!({
            "address": holon.address_sha256,
            "grain": holon.grain,
            "local_bounds": local,
            "face": holon.inherited_face,
        }));
    }
    let focus_path = directory.join("05-focused-equation-incidence.png");
    let scale_factor = if focus_width < 400 {
        3
    } else if focus_width < 800 {
        2
    } else {
        1
    };
    let focused = imageops::resize(
        &focused,
        focus_width.saturating_mul(scale_factor),
        focus_height.saturating_mul(scale_factor),
        imageops::FilterType::Nearest,
    );
    focused
        .save(&focus_path)
        .map_err(|error| error.to_string())?;

    Ok(json!({
        "schema": "holonics.e1.hierarchical-optical-inspection.v1",
        "truth_status": "implemented-exact",
        "source_occurrence": passage.predecessor_occurrence,
        "hierarchical_occurrence": passage.occurrence,
        "page_overlay": {
            "path": "04-hierarchical-page-overlay.png",
            "sha256": artifact::digest(&artifact::read(&page_path)?),
            "primitives": page_primitives,
        },
        "focused_equation": {
            "equation_address": equation.address_sha256,
            "bounds": focus,
            "scale_factor": scale_factor,
            "path": "05-focused-equation-incidence.png",
            "sha256": artifact::digest(&artifact::read(&focus_path)?),
            "primitives": focus_primitives,
        },
        "legend": {
            "glyph-or-subfigure": [246,201,69],
            "decorated-symbol": [30,190,255],
            "term": [40,210,110],
            "assembly": [220,70,255],
            "equation": [255,60,80],
            "block": [255,170,30],
        },
        "larger_holons_retain_visible_constituents": true,
        "layout_boxes_are_receiver_faces_not_source_identity": true,
    }))
}

fn color(grain: OpticalHolonGrain, equation: bool) -> Rgb<u8> {
    if equation {
        return EQUATION;
    }
    match grain {
        OpticalHolonGrain::DecoratedSymbol => DECORATED,
        OpticalHolonGrain::Term => TERM,
        OpticalHolonGrain::Assembly => ASSEMBLY,
        OpticalHolonGrain::RelationOrEquation => TERM,
        OpticalHolonGrain::LabelledOrDiagramBlock => BLOCK,
        _ => GLYPH,
    }
}

fn draw_box(image: &mut RgbImage, bounds: OpticalBounds, color: Rgb<u8>) {
    if image.width() == 0 || image.height() == 0 {
        return;
    }
    let width = i64::from(image.width());
    let height = i64::from(image.height());
    let left = bounds.left.clamp(0, width - 1) as u32;
    let right = (bounds.right - 1).clamp(0, width - 1) as u32;
    let top = bounds.top.clamp(0, height - 1) as u32;
    let bottom = (bounds.bottom - 1).clamp(0, height - 1) as u32;
    for x in left..=right {
        image.put_pixel(x, top, color);
        image.put_pixel(x, bottom, color);
    }
    for y in top..=bottom {
        image.put_pixel(left, y, color);
        image.put_pixel(right, y, color);
    }
}

fn overlaps(left: OpticalBounds, right: OpticalBounds) -> bool {
    left.left < right.right
        && right.left < left.right
        && left.top < right.bottom
        && right.top < left.bottom
}
