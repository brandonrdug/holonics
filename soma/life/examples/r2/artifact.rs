use std::fs;
use std::path::Path;
use std::process::Command;

use life::mathematical_particle::MaterialDerivationPassage;
use serde::Serialize;
use sha2::{Digest, Sha256};

#[derive(Debug, Serialize)]
pub struct LeanReturn {
    pub schema: String,
    pub command: String,
    pub exit_status: i32,
    pub accepted: bool,
    pub stdout: String,
    pub stderr: String,
    pub source_sha256: String,
    pub source_octets: u64,
    pub sorry_occurrences: usize,
    pub theorem_faces: Vec<String>,
}

#[derive(Debug, Serialize)]
pub struct RenderingReturn {
    pub schema: String,
    pub command: String,
    pub exit_status: i32,
    pub accepted: bool,
    pub svg_sha256: String,
    pub png_sha256: String,
    pub source_states: usize,
    pub source_edges: usize,
    pub certified_circle_population: usize,
    pub certified_line_population: usize,
}

pub fn lean_source(passage: &MaterialDerivationPassage) -> String {
    let source_action = naturals(passage.source_action());
    let quotient = passage
        .source_states()
        .iter()
        .map(|state| state.remaining_to_terminal)
        .collect::<Vec<_>>();
    let quotient_after_source = passage
        .source_action()
        .iter()
        .map(|state| passage.source_states()[*state as usize].remaining_to_terminal)
        .collect::<Vec<_>>();
    let native_after_quotient = quotient
        .iter()
        .map(|state| passage.rest().native_action[*state as usize])
        .collect::<Vec<_>>();
    format!(
        "import Mathlib\n\nnamespace HolonicsR2ReturnedConstraint\n\ndef sourceAction : List Nat := {source_action}\ndef quotient : List Nat := {}\ndef quotientAfterSource : List Nat := {}\ndef nativeAfterQuotient : List Nat := {}\ndef sourceStarts : List Nat := {}\ndef nativeStarts : List Nat := {}\ndef receiverFactorPopulation : Nat := {}\ndef terminalPopulation : Nat := {}\ndef receiverOccurrencePopulation : Nat := {}\n\ntheorem sourceActionIsClosed : ∀ x ∈ sourceAction, x < sourceAction.length := by native_decide\ntheorem quotientSquareCommutes : quotientAfterSource = nativeAfterQuotient := by native_decide\ntheorem everySourceStartHasANativeStart : sourceStarts.length = nativeStarts.length := by native_decide\ntheorem everyRequestedFactorReturned : receiverFactorPopulation = terminalPopulation * receiverOccurrencePopulation := by native_decide\n\nend HolonicsR2ReturnedConstraint\n",
        naturals(&quotient),
        naturals(&quotient_after_source),
        naturals(&native_after_quotient),
        naturals(passage.source_starts()),
        naturals(&passage.rest().native_starts),
        passage.receiver_factors().len(),
        passage.source_states().iter().filter(|state| state.terminal).count(),
        passage.receiver_factors().len()
            / passage.source_states().iter().filter(|state| state.terminal).count(),
    )
}

pub fn run_lean(formal_root: &Path, source_path: &Path) -> Result<LeanReturn, String> {
    let source = fs::read(source_path).map_err(|error| error.to_string())?;
    let output = Command::new("lake")
        .args(["env", "lean"])
        .arg(source_path)
        .current_dir(formal_root)
        .output()
        .map_err(|error| error.to_string())?;
    Ok(LeanReturn {
        schema: "holonics.r2.lean-return.v1".to_owned(),
        command: format!("lake env lean {}", source_path.display()),
        exit_status: output.status.code().unwrap_or(-1),
        accepted: output.status.success(),
        stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
        source_sha256: digest(&source),
        source_octets: source.len() as u64,
        sorry_occurrences: String::from_utf8_lossy(&source).matches("sorry").count(),
        theorem_faces: vec![
            "sourceActionIsClosed".to_owned(),
            "quotientSquareCommutes".to_owned(),
            "everySourceStartHasANativeStart".to_owned(),
            "everyRequestedFactorReturned".to_owned(),
        ],
    })
}

pub fn svg(passage: &MaterialDerivationPassage) -> String {
    let branches = passage
        .source_states()
        .iter()
        .map(|state| state.branch)
        .collect::<std::collections::BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let max_remaining = passage
        .source_states()
        .iter()
        .map(|state| state.remaining_to_terminal)
        .max()
        .unwrap_or(0);
    let title =
        "R2 material derivation recurrence — source events → remaining-to-terminal quotient";
    let graph_width = (u64::from(max_remaining) + 1) * 260 + 220;
    let title_width = title.chars().count() as u64 * 14 + 80;
    let width = graph_width.max(title_width);
    let height = branches.len() as u64 * 120 + 220;
    let mut out = format!(
        "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"{width}\" height=\"{height}\" viewBox=\"0 0 {width} {height}\">\n<rect width=\"100%\" height=\"100%\" fill=\"#111827\"/>\n<text x=\"40\" y=\"42\" fill=\"#f9fafb\" font-family=\"monospace\" font-size=\"22\">{title}</text>\n<defs><marker id=\"arrow\" markerWidth=\"10\" markerHeight=\"10\" refX=\"9\" refY=\"3\" orient=\"auto\"><path d=\"M0,0 L0,6 L9,3 z\" fill=\"#60a5fa\"/></marker></defs>\n"
    );
    let coordinate = |state: u32| {
        let source = &passage.source_states()[state as usize];
        let branch_at = branches
            .iter()
            .position(|branch| *branch == source.branch)
            .unwrap_or(0);
        let x = 100 + u64::from(max_remaining - source.remaining_to_terminal) * 260;
        let y = 100 + branch_at as u64 * 120;
        (x, y)
    };
    for edge in passage.source_edges() {
        let (x1, y1) = coordinate(edge.from);
        let (x2, y2) = coordinate(edge.to);
        out.push_str(&format!("<line x1=\"{x1}\" y1=\"{y1}\" x2=\"{x2}\" y2=\"{y2}\" stroke=\"#60a5fa\" stroke-width=\"4\" marker-end=\"url(#arrow)\"/>\n"));
    }
    for state in passage.source_states() {
        let (x, y) = coordinate(state.state);
        let fill = if state.terminal { "#34d399" } else { "#f59e0b" };
        out.push_str(&format!("<circle cx=\"{x}\" cy=\"{y}\" r=\"31\" fill=\"{fill}\" stroke=\"#f9fafb\" stroke-width=\"3\"/>\n<text x=\"{x}\" y=\"{}\" text-anchor=\"middle\" fill=\"#111827\" font-family=\"monospace\" font-size=\"14\">e{}</text>\n<text x=\"{x}\" y=\"{}\" text-anchor=\"middle\" fill=\"#d1d5db\" font-family=\"monospace\" font-size=\"13\">q={}</text>\n", y + 5, state.event, y + 52, state.remaining_to_terminal));
    }
    out.push_str("</svg>\n");
    out
}

pub fn render(
    svg_path: &Path,
    png_path: &Path,
    passage: &MaterialDerivationPassage,
) -> Result<RenderingReturn, String> {
    let output = Command::new("rsvg-convert")
        .arg(svg_path)
        .arg("-o")
        .arg(png_path)
        .output()
        .map_err(|error| error.to_string())?;
    let svg_bytes = fs::read(svg_path).map_err(|error| error.to_string())?;
    let png_bytes = fs::read(png_path).map_err(|error| error.to_string())?;
    let svg_text = String::from_utf8_lossy(&svg_bytes);
    Ok(RenderingReturn {
        schema: "holonics.r2.rendering-return.v1".to_owned(),
        command: format!(
            "rsvg-convert {} -o {}",
            svg_path.display(),
            png_path.display()
        ),
        exit_status: output.status.code().unwrap_or(-1),
        accepted: output.status.success(),
        svg_sha256: digest(&svg_bytes),
        png_sha256: digest(&png_bytes),
        source_states: passage.source_states().len(),
        source_edges: passage.source_edges().len(),
        certified_circle_population: svg_text.matches("<circle ").count(),
        certified_line_population: svg_text.matches("<line ").count(),
    })
}

fn naturals(values: &[u32]) -> String {
    format!(
        "[{}]",
        values
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join(", ")
    )
}

fn digest(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect()
}
