use std::fs;
use std::path::Path;
use std::process::Command;

use life::mathematical_particle::LongHorizonRetainedBoundary;
use serde_json::{json, Value};

use super::artifact;

pub fn render(
    boundary: &LongHorizonRetainedBoundary,
    svg_path: &Path,
    png_path: &Path,
) -> Result<Value, String> {
    let native_x = 1050u64;
    let height = 140 + boundary.decoder.interiors.len() as u64 * 92;
    let mut svg = format!(
        "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"1280\" height=\"{height}\" viewBox=\"0 0 1280 {height}\">\n<rect width=\"1280\" height=\"{height}\" fill=\"#07111f\"/>\n<text x=\"50\" y=\"48\" fill=\"#e2e8f0\" font-family=\"sans-serif\" font-size=\"24\">Exact historical interiors → retained causal boundary</text>\n<text x=\"50\" y=\"78\" fill=\"#94a3b8\" font-family=\"monospace\" font-size=\"14\">payloads depart from hot standing; complete fibres remain selectable</text>\n"
    );
    for (at, interior) in boundary.decoder.interiors.iter().enumerate() {
        let y = 120 + at as u64 * 92;
        svg.push_str(&format!(
            "<rect x=\"50\" y=\"{}\" width=\"420\" height=\"56\" rx=\"10\" fill=\"#10243f\" stroke=\"#60a5fa\" stroke-width=\"2\"/>\n<text x=\"70\" y=\"{}\" fill=\"#dbeafe\" font-family=\"monospace\" font-size=\"15\">h{at} · {} octets · {}…</text>\n",
            y - 28,
            y + 5,
            interior.payload.len(),
            &interior.payload_sha256[..12],
        ));
        if let Some(predecessor) = interior.predecessor.as_deref() {
            let predecessor_at = boundary
                .decoder
                .interiors
                .iter()
                .position(|candidate| candidate.occurrence == predecessor)
                .ok_or("render predecessor absent")?;
            let predecessor_y = 120 + predecessor_at as u64 * 92;
            svg.push_str(&format!(
                "<path d=\"M260 {} C520 {},520 {},500 {y}\" fill=\"none\" stroke=\"#334155\" stroke-width=\"2\"/>\n",
                predecessor_y + 28,
                predecessor_y + 28,
                y,
            ));
        }
    }
    for state in &boundary.standing.native_states {
        let y = 160 + state.0 * 260;
        svg.push_str(&format!(
            "<circle cx=\"{native_x}\" cy=\"{y}\" r=\"52\" fill=\"#0f766e\" stroke=\"#99f6e4\" stroke-width=\"3\"/>\n<text x=\"{native_x}\" y=\"{}\" text-anchor=\"middle\" fill=\"#ecfeff\" font-family=\"monospace\" font-size=\"18\">q{}</text>\n",
            y + 6,
            state.0,
        ));
    }
    let member = boundary
        .decoder
        .source_members
        .iter()
        .map(|member| (member.item, member))
        .collect::<std::collections::BTreeMap<_, _>>();
    let mut fibre_lines = 0usize;
    for (native, sources) in &boundary.fibres.fibres {
        let target_y = 160 + native.0 * 260;
        for source in sources {
            let source = member.get(source).ok_or("render fibre member absent")?;
            let source_y = 120 + source.interior as u64 * 92;
            let source_x = 540 + source.physical_state as u64 * 115;
            svg.push_str(&format!(
                "<line x1=\"{source_x}\" y1=\"{source_y}\" x2=\"{}\" y2=\"{target_y}\" stroke=\"#f59e0b\" stroke-width=\"1\" opacity=\"0.55\"/>\n<circle cx=\"{source_x}\" cy=\"{source_y}\" r=\"5\" fill=\"#fbbf24\"/>\n",
                native_x - 55,
            ));
            fibre_lines += 1;
        }
    }
    svg.push_str("</svg>\n");
    fs::write(svg_path, svg.as_bytes()).map_err(|error| error.to_string())?;
    let output = Command::new("rsvg-convert")
        .arg(svg_path)
        .arg("-o")
        .arg(png_path)
        .output()
        .map_err(|error| error.to_string())?;
    if !output.status.success() {
        return Err(format!(
            "rsvg-convert refused: {}",
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    let png = fs::read(png_path).map_err(|error| error.to_string())?;
    Ok(json!({
        "schema": "holonics.r4.exact-boundary-rendering.v1",
        "truth_status": "implemented-exact",
        "svg_sha256": artifact::digest(svg.as_bytes()),
        "png_sha256": artifact::digest(&png),
        "historical_interior_nodes": boundary.decoder.interiors.len(),
        "native_boundary_nodes": boundary.standing.native_states.len(),
        "source_to_boundary_fibre_lines": fibre_lines,
        "line_population_certified_from_complete_fibres": fibre_lines,
        "render_exit_status": output.status.code().unwrap_or(-1),
    }))
}
