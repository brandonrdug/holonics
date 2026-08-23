use std::fs;
use std::path::Path;

use image::{Rgb, RgbImage};
use serde_json::{json, Value};

use super::artifact;

fn evaluate(section: [i64; 3], x: i64, y: i64) -> Result<i64, String> {
    section[0]
        .checked_mul(x)
        .and_then(|value| value.checked_mul(x))
        .and_then(|value| {
            section[1]
                .checked_mul(x)
                .and_then(|mixed| mixed.checked_mul(y))
                .and_then(|mixed| value.checked_add(mixed))
        })
        .and_then(|value| {
            section[2]
                .checked_mul(y)
                .and_then(|term| term.checked_mul(y))
                .and_then(|term| value.checked_add(term))
        })
        .ok_or("quadratic rendering extent overflow".to_owned())
}

pub fn exact_quadratic_faces(
    section: [i64; 3],
    chart: [i64; 4],
    directory: &Path,
) -> Result<Value, String> {
    let width = 512_u32;
    let height = 512_u32;
    let mut raster = RgbImage::new(width, height);
    for py in 0..height {
        for px in 0..width {
            let x = i64::from(px) - i64::from(width / 2);
            let y = i64::from(height / 2) - i64::from(py);
            let value = evaluate(section, x, y)?;
            let axis = x == 0 || y == 0;
            let color = if axis {
                Rgb([238, 238, 246])
            } else if value == 0 {
                Rgb([255, 211, 77])
            } else if value > 0 {
                Rgb([55, 112, 176])
            } else {
                Rgb([183, 66, 92])
            };
            raster.put_pixel(px, py, color);
        }
    }
    let png_path = directory.join("08-quadratic-section.png");
    raster.save(&png_path).map_err(|error| error.to_string())?;

    let grid = 32_i64;
    let cell = 16_i64;
    let mut cells = String::new();
    for gy in -grid / 2..grid / 2 {
        for gx in -grid / 2..grid / 2 {
            let value = evaluate(section, gx, gy)?;
            let fill = if value == 0 {
                "#ffd34d"
            } else if value > 0 {
                "#3770b0"
            } else {
                "#b7425c"
            };
            let x = (gx + grid / 2) * cell;
            let y = (grid / 2 - gy - 1) * cell;
            cells.push_str(&format!(
                "<rect x=\"{x}\" y=\"{y}\" width=\"{cell}\" height=\"{cell}\" fill=\"{fill}\"/>"
            ));
        }
    }
    let svg = format!(
        "<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 512 512\" role=\"img\" aria-label=\"Exact integer sample chart of a homogeneous quadratic section\"><rect width=\"512\" height=\"512\" fill=\"#11151d\"/>{cells}<path d=\"M256 0V512M0 256H512\" stroke=\"#f4f4f8\" stroke-width=\"2\"/><text x=\"16\" y=\"30\" fill=\"white\" font-family=\"monospace\" font-size=\"15\">Q=[{},{},{}], chart=[{},{},{},{}]</text></svg>\n",
        section[0], section[1], section[2], chart[0], chart[1], chart[2], chart[3]
    );
    let svg_path = directory.join("07-quadratic-section.svg");
    fs::write(&svg_path, svg.as_bytes()).map_err(|error| error.to_string())?;

    let mesh_extent = 10_i64;
    let stride = (mesh_extent * 2 + 1) as u32;
    let mut vertices = Vec::new();
    for y in -mesh_extent..=mesh_extent {
        for x in -mesh_extent..=mesh_extent {
            vertices.push([x, y, evaluate(section, x, y)?]);
        }
    }
    let mut triangles = Vec::new();
    for y in 0..stride - 1 {
        for x in 0..stride - 1 {
            let at = y * stride + x;
            triangles.push([at, at + 1, at + stride]);
            triangles.push([at + 1, at + stride + 1, at + stride]);
        }
    }
    let mesh_path = directory.join("06-quadratic-section.mesh.json");
    let mesh_bytes = artifact::write_json(
        &mesh_path,
        &json!({
            "schema": "holonics.l0.exact-quadratic-mesh.v1",
            "truth_status": "implemented-exact",
            "coordinate_carrier": "integer",
            "vertices": vertices,
            "triangles": triangles,
        }),
    )?;
    let html = format!(
        "<!doctype html><meta charset=\"utf-8\"><title>L0 quadratic section atlas</title><style>body{{margin:0;background:#11151d;color:#f4f4f8;font:16px system-ui;display:grid;grid-template-columns:minmax(360px,1fr) 340px;min-height:100vh}}object{{width:100%;height:100vh}}aside{{padding:24px}}code{{color:#ffd34d}}li{{margin:.8rem 0}}</style><object data=\"07-quadratic-section.svg\" type=\"image/svg+xml\"></object><aside><h1>Quadratic section transport</h1><p>The colored cells are exact integer evaluations, not a floating interpolation.</p><ul><li><code>blue</code>: positive receiver face</li><li><code>rose</code>: negative receiver face</li><li><code>gold</code>: zero locus</li></ul><p>Central inversion transports every homogeneous degree-two section back to the same coefficient face. Single-axis reflection separates a nonzero mixed coefficient.</p></aside>\n"
    );
    let html_path = directory.join("09-interactive-atlas.html");
    fs::write(&html_path, html.as_bytes()).map_err(|error| error.to_string())?;
    let png_bytes = fs::read(&png_path).map_err(|error| error.to_string())?;
    Ok(json!({
        "schema": "holonics.l0.rendering-receipt.v1",
        "truth_status": "implemented-exact",
        "png_sha256": artifact::digest(&png_bytes),
        "svg_sha256": artifact::digest(svg.as_bytes()),
        "mesh_sha256": artifact::digest(&mesh_bytes),
        "html_sha256": artifact::digest(html.as_bytes()),
        "raster_samples": u64::from(width) * u64::from(height),
        "mesh_vertices": vertices.len(),
        "mesh_triangles": triangles.len(),
        "floating_semantic_coordinates": 0,
    }))
}
