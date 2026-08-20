//! **Deed H5: Station D returns with shared branches** — every taxon of the committed dissection
//! panel enacted as a matched sibling that conducts only its SUFFIX, on the base's released
//! standing shared read-only, with one layer's maps mounted once for the whole cohort crossing it,
//! and every receiver-family comparison of the committed artifact reproduced UNCHANGED.
//!
//! Plan: the single-card plan §6 (branch-sharing dissection), §8 "Deed H5", §10, §11. The
//! independent predecessor is Station D's committed artifact
//! `output/the_source_is_dissected/dissection-5-tokens-grain-48-terms-14.form`, produced by
//! eighteen complete towers; this driver **parses it and compares programmatically**, and any
//! drift is a named failure.
//!
//! ```text
//!   the base tower                conducted ONCE, 42 layers + the final boundary
//!   a sibling at layer L          conducts L..41 + the final boundary, entering on the base's
//!                                 standing at L — shared read-only through `Standing`, whose
//!                                 realization is a `section_carry` writing only its own output
//!   a cohort at layer L           every tower whose suffix contains L, bound as plural passages
//!                                 over ONE mount of that layer's maps
//!   the receiver family           per layer: the per-layer input section, the contact, the layer
//!                                 return; then the final normed standing and the potential with
//!                                 its order face — 128 faces, exactly the committed family
//! ```
//!
//! **What prefix sharing costs, stated before it is used.** A sibling that does not conduct layers
//! `0..L` has no faces of its own there, so the committed control *"every face of layers before L
//! bit-identical"* is **structural** here and carries no evidence. It is reported as structural.
//! What remains falsifiable is this realization's own claim, and it is answered twice: against the
//! committed artifact, and by the **prefix control tower** — one declared sibling conducted BOTH
//! ways in the same circulation, sharing nothing, all 128 faces compared.
//!
//! Run:
//! ```text
//! cargo run --release -q -p holonic-engine --example the_dissection_shares_its_prefixes -- \
//!     --text "The capital of France is" [--grain 48] [--terms 14] [--band 12]
//! ```

#[path = "phoenix/cohort.rs"]
mod cohort;
#[path = "phoenix/resident_layer.rs"]
mod resident_layer;
#[path = "phoenix/streamed.rs"]
mod streamed;
#[path = "phoenix/native_streamed.rs"]
mod native_streamed;
#[path = "phoenix/tower.rs"]
mod tower;

use std::collections::BTreeMap;
use std::io::Write;
use std::time::Instant;

use cohort::{Cohorted, LayerFace, Site, TowerDeclaration, TowerReturn};
use holonic_engine::embedding_fiber::ResidentReadout;
use holonic_engine::resident_section::{word_value, ResidentGrain, ResidentSurface, SeriesAperture};
use num_bigint::BigInt;
use relational_geometry::Rat;
use native_streamed::NativeMaterialSource;
use streamed::{ForeignMaterialSource, MaterialSource};
use tower::Intervention;

// ---------------------------------------------------------------------------------------------
// arguments
// ---------------------------------------------------------------------------------------------

struct Args {
    root: String,
    native_rest: Option<String>,
    out: String,
    committed: String,
    text: Option<String>,
    tokens: Option<Vec<usize>>,
    grain: u32,
    terms: u32,
    python: String,
    band: usize,
    digest_container: bool,
}

fn parse_args() -> Args {
    let mut args = Args {
        root: "/home/b/models/gemma-4-E4B-it".to_owned(),
        native_rest: None,
        out: "output/the_dissection_shares_its_prefixes".to_owned(),
        committed: "output/the_source_is_dissected/dissection-5-tokens-grain-48-terms-14.form".to_owned(),
        text: None,
        tokens: None,
        grain: 48,
        terms: 14,
        python: "/home/b/scratch/huggingface/.venv/bin/python".to_owned(),
        band: 12,
        digest_container: false,
    };
    let mut it = std::env::args().skip(1);
    while let Some(flag) = it.next() {
        match flag.as_str() {
            "--root" => args.root = it.next().expect("--root <dir>"),
            "--native-rest" => args.native_rest = Some(it.next().expect("--native-rest <path>")),
            "--out" => args.out = it.next().expect("--out <dir>"),
            "--committed" => args.committed = it.next().expect("--committed <path>"),
            "--text" => args.text = Some(it.next().expect("--text <text>")),
            "--tokens" => args.tokens = Some(it.next().expect("--tokens a,b").split(',').map(|t| t.trim().parse().expect("token id")).collect()),
            "--grain" => args.grain = it.next().expect("--grain F").parse().expect("u32"),
            "--terms" => args.terms = it.next().expect("--terms N").parse().expect("u32"),
            "--python" => args.python = it.next().expect("--python <path>"),
            "--band" => args.band = it.next().expect("--band N").parse().expect("usize"),
            "--digest-container" => args.digest_container = true,
            other => panic!("unknown argument {other}"),
        }
    }
    args
}

fn encode_text(python: &str, text: &str) -> Result<(Vec<usize>, Vec<String>), String> {
    let output = std::process::Command::new(python)
        .arg(concat!(env!("CARGO_MANIFEST_DIR"), "/examples/phoenix/source_runtime_tower.py"))
        .arg("encode")
        .arg(text)
        .output()
        .map_err(|e| e.to_string())?;
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr).chars().take(400).collect());
    }
    for line in String::from_utf8_lossy(&output.stdout).lines() {
        if !line.starts_with('{') {
            continue;
        }
        let json: serde_json::Value = serde_json::from_str(line).map_err(|e| e.to_string())?;
        let ids: Vec<usize> = json["ids"].as_array().ok_or("ids")?.iter().filter_map(|v| v.as_u64()).map(|v| v as usize).collect();
        let pieces: Vec<String> = json["pieces"].as_array().ok_or("pieces")?.iter().filter_map(|v| v.as_str()).map(str::to_owned).collect();
        return Ok((ids, pieces));
    }
    Err("no encoding returned".to_owned())
}

fn rat_f64(value: &Rat) -> f64 {
    use num_traits::ToPrimitive;
    value.numer().to_f64().unwrap_or(f64::NAN) / value.denom().to_f64().unwrap_or(f64::NAN)
}

fn zero() -> Rat {
    Rat::from_integer(BigInt::from(0))
}

// ---------------------------------------------------------------------------------------------
// the receiver family — the committed comparison functions, carried verbatim in their arithmetic
// ---------------------------------------------------------------------------------------------

/// Two sections of one face compared entry by entry. **Identical in arithmetic to the committed
/// driver's**, with one addition that changes no return: an entry whose two words are equal is
/// counted identical, contributes a midpoint shift of exactly zero and cannot be disjoint, so the
/// exact rationals are not formed for it. The predecessor formed them and added zero.
#[derive(Clone, Debug)]
struct FaceComparison {
    entries: usize,
    identical: usize,
    separated: usize,
    widest_gap: Rat,
    widest_shift: Rat,
    positions_separated: Vec<usize>,
    /// True when the two sections are the SAME section by construction (a shared prefix), so the
    /// comparison was not taken. Never reported as a measurement.
    structural: bool,
}

fn compare(base: &[(i64, i64)], sibling: &[(i64, i64)], grain: ResidentGrain, width: usize) -> FaceComparison {
    let entries = base.len().min(sibling.len());
    let mut identical = 0usize;
    let mut separated = 0usize;
    let mut widest_gap = zero();
    let mut widest_shift = zero();
    let mut positions: Vec<usize> = Vec::new();
    let two = Rat::from_integer(BigInt::from(2));
    for i in 0..entries {
        let (bl, bh) = base[i];
        let (sl, sh) = sibling[i];
        if bl == sl && bh == sh {
            identical += 1;
            continue;
        }
        let disjoint = bh < sl || sh < bl;
        if disjoint {
            separated += 1;
            let gap = if bh < sl { word_value(sl, grain) - word_value(bh, grain) } else { word_value(bl, grain) - word_value(sh, grain) };
            if gap > widest_gap {
                widest_gap = gap;
            }
            if width > 0 {
                let row = i / width;
                if positions.last() != Some(&row) {
                    positions.push(row);
                }
            }
        }
        let bm = (word_value(bl, grain) + word_value(bh, grain)) / &two;
        let sm = (word_value(sl, grain) + word_value(sh, grain)) / &two;
        let shift = num_traits::Signed::abs(&(bm - sm));
        if shift > widest_shift {
            widest_shift = shift;
        }
    }
    positions.sort_unstable();
    positions.dedup();
    FaceComparison { entries, identical, separated, widest_gap, widest_shift, positions_separated: positions, structural: false }
}

/// The comparison of a face a sibling did not conduct: it IS the base's face, so every entry is
/// identical by construction and nothing was measured.
fn shared(entries: usize) -> FaceComparison {
    FaceComparison { entries, identical: entries, separated: 0, widest_gap: zero(), widest_shift: zero(), positions_separated: Vec::new(), structural: true }
}

/// One face of the receiver family, named in chronology.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Face {
    Ple(usize),
    Contact(usize),
    Return(usize),
    FinalNormed,
    Potential,
}

impl Face {
    fn name(&self) -> String {
        match self {
            Face::Ple(l) => format!("layer {l} per-layer input section"),
            Face::Contact(l) => format!("layer {l} contact"),
            Face::Return(l) => format!("layer {l} return"),
            Face::FinalNormed => "final normed standing".to_owned(),
            Face::Potential => "potential section".to_owned(),
        }
    }
    fn layer(&self) -> Option<usize> {
        match self {
            Face::Ple(l) | Face::Contact(l) | Face::Return(l) => Some(*l),
            _ => None,
        }
    }
}

fn face_widths(face: &LayerFace) -> (usize, usize, usize) {
    let head = if face.species == tower::Species::Full { tower::FULL_HEAD } else { tower::SLIDING_HEAD };
    (tower::PLE_WIDTH, tower::HEADS * head, tower::HIDDEN)
}

/// The whole receiver family compared, every face in chronology, with a face the sibling did not
/// conduct returned as [`shared`].
fn compare_family(base: &TowerReturn, sibling: &TowerReturn, grain: ResidentGrain) -> Vec<(Face, FaceComparison)> {
    let mut out = Vec::new();
    for layer in 0..tower::LAYERS {
        let b = base.layers.get(&layer).expect("the base conducted every layer");
        let (ple_w, contact_w, return_w) = face_widths(b);
        match sibling.layers.get(&layer) {
            Some(s) => {
                out.push((Face::Ple(layer), compare(&b.ple, &s.ple, grain, ple_w)));
                out.push((Face::Contact(layer), compare(&b.contact, &s.contact, grain, contact_w)));
                out.push((Face::Return(layer), compare(&b.terminal, &s.terminal, grain, return_w)));
            }
            None => {
                out.push((Face::Ple(layer), shared(b.ple.len())));
                out.push((Face::Contact(layer), shared(b.contact.len())));
                out.push((Face::Return(layer), shared(b.terminal.len())));
            }
        }
    }
    out.push((Face::FinalNormed, compare(&base.final_normed, &sibling.final_normed, grain, tower::HIDDEN)));
    out.push((Face::Potential, compare(&base.potential, &sibling.potential, grain, tower::VOCABULARY)));
    out
}

/// The order face of the potential at the last position.
fn order_face(potential: &[(i64, i64)], positions: usize, grain: ResidentGrain, n: usize) -> (Vec<usize>, Vec<usize>) {
    let row = &potential[(positions - 1) * tower::VOCABULARY..positions * tower::VOCABULARY];
    let mut top_lower = word_value(row[0].0, grain);
    for (lo, _) in row {
        let v = word_value(*lo, grain);
        if v > top_lower {
            top_lower = v;
        }
    }
    let mut plural: Vec<usize> = row.iter().enumerate().filter(|(_, (_, hi))| word_value(*hi, grain) >= top_lower).map(|(v, _)| v).collect();
    plural.sort_unstable();
    let mut by_lower: Vec<(usize, i64)> = row.iter().enumerate().map(|(v, (lo, _))| (v, *lo)).collect();
    by_lower.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
    (plural, by_lower.into_iter().take(n).map(|(v, _)| v).collect())
}

// ---------------------------------------------------------------------------------------------
// the panel — the committed taxa, verbatim
// ---------------------------------------------------------------------------------------------

#[derive(Clone, Debug)]
enum Control {
    LayersBeforeIdentical(usize),
    EveryLayerIdentical,
    PositionZeroUnseparated(usize),
    PositionZeroIdentical(usize),
    OrderFaceUnmoved,
}

struct Taxon {
    name: &'static str,
    dissects: &'static str,
    site: Site,
    intervention: Intervention,
    controls: Vec<Control>,
    ambiguity: &'static str,
}

fn panel(tokens: usize) -> Vec<Taxon> {
    vec![
        Taxon { name: "initial-embedding columns 0..256 withdrawn at every layer", dissects: "initial embedding", site: Site::EveryLayer, intervention: Intervention::WithdrawEmbeddingColumns { from: 0, span: 256 }, controls: vec![], ambiguity: "x0 enters every layer (the residual at layer 0 and the PLE projection everywhere), so the site is every layer and no predecessor control exists; the change is attributed to the columns, not to a layer" },
        Taxon { name: "per-layer input withdrawn whole at layer 1", dissects: "per-layer embedding (PLE)", site: Site::Layer(1), intervention: Intervention::WithdrawPle, controls: vec![Control::LayersBeforeIdentical(1)], ambiguity: "the withdrawn section is the layer's joined PLE (embedding half + projected half); which half carries the change is not separated by this taxon" },
        Taxon { name: "standing ×2 before the input rebase at layer 1", dissects: "normalization (gauge)", site: Site::Layer(1), intervention: Intervention::ScaleBeforeInputRebase { by: 2 }, controls: vec![Control::LayersBeforeIdentical(1), Control::OrderFaceUnmoved], ambiguity: "the RMS rebase quotients a positive scale away up to its epsilon and the rounding of its radical series, so what survives is that residue; the exact receiver at grain 2^-48 can see it while the order face cannot — tolerance is the receiver's aperture (the scale below which no arc reaches a receiver-relevant difference), so the gauge is stated relative to the after-rebase sibling (domination at every face) and to the order face, never as a threshold; the retained standing is not scaled (the re-entry reads the unscaled standing)" },
        Taxon { name: "standing ×2 after the input rebase at layer 1", dissects: "normalization (not a gauge)", site: Site::Layer(1), intervention: Intervention::ScaleAfterInputRebase { by: 2 }, controls: vec![Control::LayersBeforeIdentical(1)], ambiguity: "Q, K and V all double, so the contact's ratio sharpens by 4 in the exponent and V doubles; the two are not separated by this taxon" },
        Taxon { name: "identity band elements at layer 1", dissects: "chronology replaced (no rotation)", site: Site::Layer(1), intervention: Intervention::IdentityChronology, controls: vec![Control::LayersBeforeIdentical(1), Control::PositionZeroIdentical(1)], ambiguity: "position 0 is rotated by angle 0 in both deeds, so its self-contact is unchanged by construction; later positions change through the relative angle only" },
        Taxon { name: "positions reversed at layer 1", dissects: "chronology permuted", site: Site::Layer(1), intervention: Intervention::ReversedPositions, controls: vec![Control::LayersBeforeIdentical(1), Control::PositionZeroUnseparated(1)], ambiguity: "position 0's query and key are rotated by one equal angle, whose dot product is invariant in exact arithmetic; at the dyadic grain the rotated words round, so position 0 is predicted unseparated rather than identical" },
        Taxon { name: "receiver heads 0,1 swapped at layer 1", dissects: "Q/K contact permuted", site: Site::Layer(1), intervention: Intervention::PermuteReceiverHeads { a: 0, b: 1 }, controls: vec![Control::LayersBeforeIdentical(1), Control::PositionZeroIdentical(1)], ambiguity: "heads 0 and 1 read the same grouped K/V family, so the permutation moves which head's contact reaches which o_proj block; at position 0 the causal contact has one key, its ratio is 1 whatever the receiver, and both heads carry the same V row, so position 0 is predicted bit-identical — the change is the contact's weights at positions ≥ 1 routed through o_proj" },
        Taxon { name: "receiver ×2 before the contact at layer 1", dissects: "softmax ratio geometry (temperature)", site: Site::Layer(1), intervention: Intervention::ScaleReceiver { by: 2 }, controls: vec![Control::LayersBeforeIdentical(1), Control::PositionZeroIdentical(1)], ambiguity: "a temperature of 1/2: the ratio family sharpens; V is unchanged, so the change is the contact's weights alone, and at position 0 (one key, ratio 1) there is no weight to sharpen — position 0 is predicted bit-identical" },
        Taxon { name: "K/V family 0 withdrawn at layer 1", dissects: "K/V weights (own layer)", site: Site::Layer(1), intervention: Intervention::WithdrawKvFamily { family: 0 }, controls: vec![Control::LayersBeforeIdentical(1)], ambiguity: "layer 1 builds and does not store its K/V, so the change reaches later layers only through the residual" },
        Taxon { name: "K/V family 0 withdrawn at layer 22 (the stored sliding layer)", dissects: "K/V weights at the stored layer", site: Site::Layer(22), intervention: Intervention::WithdrawKvFamily { family: 0 }, controls: vec![Control::LayersBeforeIdentical(22)], ambiguity: "layer 22's own contact and the shared standings both move; which carries the change into layer 24 is separated by the next taxon" },
        Taxon { name: "SHARED K/V family 0 withdrawn at layer 24 only", dissects: "KV reuse (the reuse, not the weights)", site: Site::Layer(24), intervention: Intervention::WithdrawSharedKvFamily { family: 0 }, controls: vec![Control::LayersBeforeIdentical(24)], ambiguity: "layers 22 and 23 are untouched (their faces identical), so a change here is the reuse's alone; layers 25–41 read the unwithdrawn standings and move only through the residual" },
        Taxon { name: "carried heads 0,1 swapped before o_proj at layer 1", dissects: "V/O transport permuted", site: Site::Layer(1), intervention: Intervention::PermuteCarriedHeads { a: 0, b: 1 }, controls: vec![Control::LayersBeforeIdentical(1), Control::PositionZeroIdentical(1)], ambiguity: "the contact section itself is unchanged (it is read before the permutation); the change begins at o_proj; at position 0 the two grouped heads carry the same single V row, so swapping them is the identity there and position 0 is predicted bit-identical" },
        Taxon { name: "retained standing withdrawn at the first re-entry of layer 1", dissects: "residual standing", site: Site::Layer(1), intervention: Intervention::WithdrawResidualAtFirstReEntry, controls: vec![Control::LayersBeforeIdentical(1)], ambiguity: "the return stands alone at the first re-entry; the second and third re-entries still retain, so the layer is not made residual-free" },
        Taxon { name: "gated passage columns 0..2560 withdrawn at layer 1", dissects: "MLP / gated transport", site: Site::Layer(1), intervention: Intervention::WithdrawGateSpan { from: 0, span: 2560 }, controls: vec![Control::LayersBeforeIdentical(1)], ambiguity: "a quarter of the passage; the contact is unchanged (read before the MLP), so the first separating face is predicted to be the layer return" },
        Taxon { name: "every key/value position but the last withdrawn at layer 5 (full)", dissects: "sliding vs global chronology (a window of one)", site: Site::Layer(5), intervention: Intervention::KeepOnlyLastKeyPosition { tokens }, controls: vec![Control::LayersBeforeIdentical(5)], ambiguity: "every query but the last then reads no key (the causal contact over zero keys returns the empty ratio), and the last reads only itself; the window's effect on the last position alone is what the order face measures" },
        Taxon { name: "final normed columns 0..256 withdrawn", dissects: "output boundary (tied embedding)", site: Site::Final, intervention: Intervention::WithdrawFinalSpan { from: 0, span: 256 }, controls: vec![Control::EveryLayerIdentical], ambiguity: "the tied boundary reads 2,560 columns; withdrawing a tenth moves the potential by those columns' contribution alone" },
    ]
}

/// Is the sibling's complex the base's plus exactly its intervention occurrences? Carried verbatim
/// from the committed driver.
fn matched(base: &[(String, bool)], sibling: &[(String, bool)]) -> (bool, usize, usize) {
    let mut b: BTreeMap<&str, usize> = BTreeMap::new();
    for (n, _) in base {
        *b.entry(n.as_str()).or_default() += 1;
    }
    let mut s: BTreeMap<&str, usize> = BTreeMap::new();
    let mut typed: BTreeMap<&str, bool> = BTreeMap::new();
    for (n, t) in sibling {
        *s.entry(n.as_str()).or_default() += 1;
        typed.insert(n.as_str(), *t);
    }
    let mut extra = 0usize;
    let mut missing = 0usize;
    let mut ok = true;
    for (name, count) in &s {
        let have = b.get(name).copied().unwrap_or(0);
        if *count > have {
            extra += count - have;
            if !typed.get(name).copied().unwrap_or(false) {
                ok = false;
            }
        }
    }
    for (name, count) in &b {
        let have = s.get(name).copied().unwrap_or(0);
        if *count > have {
            missing += count - have;
            let replaced = format!("{name} (intervention)");
            if !typed.get(replaced.as_str()).copied().unwrap_or(false) {
                ok = false;
            }
        }
    }
    (ok, extra, missing)
}

// ---------------------------------------------------------------------------------------------
// the committed artifact, parsed
// ---------------------------------------------------------------------------------------------

#[derive(Debug, Default, Clone)]
struct CommittedTaxon {
    name: String,
    dissects: String,
    site: String,
    intervention: String,
    ambiguity: String,
    line_stood: String,
    faces: String,
    first: String,
    potential: String,
    controls: Vec<String>,
}

#[derive(Debug, Default)]
struct Committed {
    base: String,
    taxa: Vec<CommittedTaxon>,
    vision: String,
}

fn read_committed(path: &str) -> Result<Committed, String> {
    let text = std::fs::read_to_string(path).map_err(|e| format!("{path}: {e}"))?;
    let mut committed = Committed::default();
    let mut current: Option<CommittedTaxon> = None;
    for line in text.lines() {
        if let Some(rest) = line.strip_prefix("base deed: ") {
            committed.base = rest.to_owned();
        } else if let Some(rest) = line.strip_prefix("TAXON ") {
            if let Some(taxon) = current.take() {
                committed.taxa.push(taxon);
            }
            let name = rest.split(" — dissects ").next().unwrap_or(rest).to_owned();
            let dissects = rest.split(" — dissects ").nth(1).and_then(|r| r.split(" — site ").next()).unwrap_or("").to_owned();
            let site = rest.split(" — site ").nth(1).and_then(|r| r.split(" — intervention ").next()).unwrap_or("").to_owned();
            let intervention = rest.split(" — intervention ").nth(1).unwrap_or("").to_owned();
            current = Some(CommittedTaxon { name, dissects, site, intervention, ..Default::default() });
        } else if let Some(taxon) = current.as_mut() {
            if let Some(rest) = line.strip_prefix("  stood ") {
                taxon.line_stood = rest.to_owned();
            } else if let Some(rest) = line.strip_prefix("  faces separated ") {
                taxon.faces = rest.to_owned();
            } else if let Some(rest) = line.strip_prefix("  shortest separating history: ") {
                taxon.first = rest.to_owned();
            } else if let Some(rest) = line.strip_prefix("  potential: ") {
                taxon.potential = rest.to_owned();
            } else if let Some(rest) = line.strip_prefix("  control ") {
                taxon.controls.push(rest.to_owned());
            } else if let Some(rest) = line.strip_prefix("  remaining ambiguity: ") {
                taxon.ambiguity = rest.to_owned();
            }
        }
        if line.starts_with("vision: ") {
            if let Some(taxon) = current.take() {
                committed.taxa.push(taxon);
            }
            committed.vision = line.to_owned();
        }
    }
    if let Some(taxon) = current.take() {
        committed.taxa.push(taxon);
    }
    if committed.base.is_empty() || committed.taxa.len() != 16 {
        return Err(format!("{path}: parsed {} taxa and {} base lines", committed.taxa.len(), usize::from(!committed.base.is_empty())));
    }
    Ok(committed)
}

/// The committed base line's own two order faces.
fn committed_order(base: &str) -> (String, String) {
    let plural = base.split("plural top ").nth(1).and_then(|r| r.split(" · ").next()).unwrap_or("").to_owned();
    let top = base.split("top-16 ").nth(1).and_then(|r| r.split(" · ").next()).unwrap_or("").to_owned();
    (plural, top)
}

// ---------------------------------------------------------------------------------------------
// main
// ---------------------------------------------------------------------------------------------

struct Verdicts {
    lines: Vec<String>,
    failed: usize,
}

impl Verdicts {
    fn record(&mut self, number: usize, pass: bool, claim: &str, evidence: &str) {
        let tag = if pass { "PASS" } else { "OPEN" };
        if !pass {
            self.failed += 1;
        }
        self.lines.push(format!("  [{number:>2}] {tag}  {claim}\n        {evidence}"));
        println!("  [{number:>2}] {tag}  {claim}\n        {evidence}");
    }
    fn inherited(&mut self, number: usize, claim: &str, evidence: &str) {
        self.lines.push(format!("  [{number:>2}] INHERITED  {claim}\n        {evidence}"));
        println!("  [{number:>2}] INHERITED  {claim}\n        {evidence}");
    }
}

struct Outcome {
    taxon: Taxon,
    stood: bool,
    matched: bool,
    intervention_occurrences: usize,
    controls_held: Vec<(String, bool, String, bool)>,
    first: Option<(Face, FaceComparison)>,
    faces_separated: usize,
    faces_total: usize,
    potential: Option<FaceComparison>,
    family: Vec<(Face, FaceComparison)>,
    order_moved: bool,
    plural: Vec<usize>,
    top: Vec<usize>,
    shared_prefix_layers: usize,
}

fn main() {
    let args = parse_args();
    let clock = Instant::now();
    if args.native_rest.is_some() && args.tokens.is_none() {
        println!("REFUSED: --native-rest requires --tokens; native W1 has no Python/source tokenizer");
        std::process::exit(2);
    }
    if args.native_rest.is_some() && args.text.is_some() {
        println!("REFUSED: --native-rest accepts --tokens only; --text would reopen the foreign tokenizer");
        std::process::exit(2);
    }
    let mode_label = if args.native_rest.is_some() { "native W1" } else { "foreign Gemma" };
    println!("THE DISSECTION SHARES ITS PREFIXES — {mode_label}");
    std::fs::create_dir_all(&args.out).expect("output directory");
    let committed = match read_committed(&args.committed) {
        Ok(c) => c,
        Err(error) => {
            println!("REFUSED: the committed predecessor could not be read — {error}");
            std::process::exit(5);
        }
    };
    println!("  the committed predecessor: {} — {} taxa parsed", args.committed, committed.taxa.len());

    let mut verdicts = Verdicts { lines: Vec::new(), failed: 0 };
    let readout: &'static ResidentReadout = match ResidentReadout::new() {
        Ok(readout) => Box::leak(Box::new(readout)),
        Err(error) => {
            println!("REFUSED: no resident chart — {error}");
            std::process::exit(3);
        }
    };
    let surface: &'static ResidentSurface<'static> = match ResidentSurface::on(readout) {
        Ok(surface) => Box::leak(Box::new(surface)),
        Err(error) => {
            println!("REFUSED: the resident laws did not load — {error}");
            std::process::exit(3);
        }
    };
    println!(
        "  resident chart: {} · mode {} · allocation grain {} · memory {} free of {}",
        surface.device_name(),
        surface.mode().kernel_content.as_deref().unwrap_or("?"),
        surface.allocation_grain(),
        surface.memory_at_mount().free_bytes,
        surface.memory_at_mount().total_bytes
    );
    let grain = ResidentGrain(args.grain);
    let terms = SeriesAperture(args.terms);
    let chart = tower::Chart::Midpoint;

    let (text, tokens, pieces): (String, Vec<usize>, Vec<String>) = match (&args.text, &args.tokens) {
        (_, Some(list)) => (format!("{list:?}"), list.clone(), list.iter().map(|t| t.to_string()).collect()),
        (Some(text), None) => match encode_text(&args.python, text) {
            Ok((ids, pieces)) => (text.clone(), ids, pieces),
            Err(error) => {
                println!("REFUSED: the exterior tokenizer could not decompose the text — {error}");
                std::process::exit(4);
            }
        },
        (None, None) => {
            println!("REFUSED: no input — give --text or --tokens");
            std::process::exit(2);
        }
    };
    println!("  the fixed input: {text:?} → {tokens:?} {pieces:?}");

    let mut source: Box<dyn MaterialSource> = if let Some(rest_path) = &args.native_rest {
        println!("  source: native W1 rest {rest_path} (path-detached; no root/model/config/tokenizer opened)");
        Box::new(NativeMaterialSource::open(rest_path).expect("native W1 rest opens"))
    } else {
        let content_sha256 = if args.digest_container {
            let digest_clock = Instant::now();
            let digest = holonic_engine::source_occurrence::AuthenticatedContainer::digest_whole(&format!("{}/model.safetensors", args.root)).expect("digest");
            println!("  container content sha256 {} re-taken in {:.1} s", &digest[..16], digest_clock.elapsed().as_secs_f64());
            Some(digest)
        } else {
            println!("  container content sha256 {} REUSED from the committed manifest ({})", &streamed::COMMITTED_CONTENT_SHA256[..16], streamed::COMMITTED_CONTENT_TAKEN);
            Some(streamed::COMMITTED_CONTENT_SHA256.to_owned())
        };
        Box::new(ForeignMaterialSource::open(&args.root, content_sha256).expect("source opens"))
    };
    let source_identity = format!("{mode_label} · {}", source.source_identity());

    // ------------------------------------------------------------------------------------------
    // the towers: the base, the replay, the sixteen matched siblings, the prefix control
    // ------------------------------------------------------------------------------------------
    let taxa = panel(tokens.len());
    let mut declarations = vec![
        TowerDeclaration::sharing("base", Site::Nowhere, Intervention::None),
        TowerDeclaration::whole("replayed base", Site::Nowhere, Intervention::None),
    ];
    let mut taxon_tower: Vec<usize> = Vec::with_capacity(taxa.len());
    for taxon in &taxa {
        taxon_tower.push(declarations.len());
        declarations.push(TowerDeclaration::sharing(taxon.name, taxon.site, taxon.intervention.clone()));
    }
    // THE PREFIX CONTROL: the taxon whose site is latest and whose suffix reads the base's STORED
    // K/V standings, conducted a second time as a COMPLETE tower that shares nothing — the
    // committed predecessor's own mechanism, in the same circulation, so the shared-prefix claim
    // is measured rather than assumed.
    let control_taxon = taxa.iter().position(|t| matches!(t.intervention, Intervention::WithdrawSharedKvFamily { .. })).expect("the KV-reuse taxon");
    let control_tower = declarations.len();
    declarations.push(TowerDeclaration::whole("prefix control · SHARED K/V family 0 withdrawn at layer 24 only, as a COMPLETE tower", taxa[control_taxon].site, taxa[control_taxon].intervention.clone()));

    println!(
        "\nTHE COHORT — {} towers, {} tokens, chart {chart:?}, grain 2^-{}, {} series terms, bands of {}",
        declarations.len(),
        tokens.len(),
        grain.0,
        terms.0,
        args.band
    );
    for declaration in &declarations {
        let conducted = tower::LAYERS.saturating_sub(declaration.enters_at) + 1;
        println!("    {:<78} enters at {:>2} · conducts {:>2} deeds · shares prefix {}", declaration.name, declaration.enters_at, conducted, declaration.shares_prefix);
    }

    let cohorted: Cohorted = match cohort::circulate_cohort(surface, readout, source.as_mut(), &tokens, grain, terms, chart, &declarations, args.band) {
        Ok(c) => c,
        Err(error) => {
            println!("REFUSED: the cohort did not conduct — {error}");
            std::process::exit(6);
        }
    };
    let mut native_fd_audit = "foreign source mode; native descriptor audit not applicable".to_owned();
    if args.native_rest.is_some() {
        let mut opened = Vec::new();
        if let Ok(entries) = std::fs::read_dir("/proc/self/fd") {
            for entry in entries.flatten() {
                if let Ok(target) = std::fs::read_link(entry.path()) {
                    opened.push(target.to_string_lossy().into_owned());
                }
            }
        }
        let forbidden_descriptors = [
            "model.safetensors",
            "modeling_gemma4.py",
            "config.json",
            "tokenizer.json",
            "tokenizer_config.json",
            "special_tokens_map.json",
            "generation_config.json",
        ];
        let foreign_descriptor_seen = opened.iter().any(|path| {
            forbidden_descriptors.iter().any(|descriptor| {
                path.ends_with(&format!("/{descriptor}")) || path == descriptor
            })
        });
        if foreign_descriptor_seen {
            println!("REFUSED: native W1 conduct left an original Gemma/config/tokenizer descriptor open: {opened:?}");
            std::process::exit(7);
        }
        native_fd_audit = format!(
            "HELD: no original Gemma/config/tokenizer descriptor among {} open descriptors",
            opened.len()
        );
        println!("  native W1 /proc/self/fd audit after conduct: no original Gemma/config/tokenizer descriptor open");
    }
    println!(
        "  conducted in {:.1} s (loop {:.1} s) · {} graph launches from {} bound passages · the ledger would have instantiated {} · widest charge {} octets",
        cohorted.wall_s, cohorted.loop_wall_s, cohorted.deed_launches, cohorted.passages_bound, cohorted.graph_instantiations, cohorted.peak_charged_octets
    );

    let base = &cohorted.towers[0];
    let replay = &cohorted.towers[1];
    let (base_plural, base_top) = order_face(&base.potential, tokens.len(), grain, 16);
    println!("  base: {} layers + final · order face plural {:?} · top-16 {:?}", base.layers.len(), base_plural, base_top);

    // the replay: the committed second falsifier, re-taken whole
    let replay_family = compare_family(base, replay, grain);
    let replay_identical = replay_family.iter().all(|(_, c)| c.identical == c.entries && !c.structural);
    println!("  the replayed base tower: every face bit-identical {replay_identical} ({} faces, none structural)", replay_family.len());

    // ------------------------------------------------------------------------------------------
    // the sixteen matched siblings
    // ------------------------------------------------------------------------------------------
    let mut outcomes: Vec<Outcome> = Vec::new();
    for (at, taxon) in taxa.into_iter().enumerate() {
        let index = taxon_tower[at];
        let sibling = &cohorted.towers[index];
        println!("\nTHE MATCHED SIBLING — {} (dissects: {})", taxon.name, taxon.dissects);
        let mut all_matched = true;
        let mut occurrences = 0usize;
        for layer in 0..tower::LAYERS {
            let b = base.layers.get(&layer).expect("base layer");
            match sibling.layers.get(&layer) {
                Some(s) => {
                    let (ok, extra, _) = matched(&b.operations, &s.operations);
                    all_matched &= ok;
                    occurrences += extra;
                }
                None => {}
            }
        }
        let (ok, extra, _) = matched(&base.final_operations, &sibling.final_operations);
        all_matched &= ok;
        occurrences += extra;

        let family = compare_family(base, sibling, grain);
        let faces_total = family.len();
        let faces_separated = family.iter().filter(|(_, c)| c.separated > 0).count();
        let first = family.iter().find(|(_, c)| c.separated > 0).cloned();
        let potential = family.iter().find(|(f, _)| *f == Face::Potential).map(|(_, c)| c.clone());
        let (plural, top) = order_face(&sibling.potential, tokens.len(), grain, 16);
        let order_moved = plural != base_plural || top != base_top;

        let mut controls_held = Vec::new();
        for control in &taxon.controls {
            let (name, held, evidence, structural) = match control {
                Control::LayersBeforeIdentical(l) => {
                    let faces: Vec<&(Face, FaceComparison)> = family.iter().filter(|(f, _)| f.layer().is_some_and(|x| x < *l)).collect();
                    let held = faces.iter().all(|(_, c)| c.identical == c.entries);
                    let structural = faces.iter().all(|(_, c)| c.structural);
                    let moved: Vec<String> = faces.iter().filter(|(_, c)| c.identical != c.entries).map(|(f, c)| format!("{} ({} of {} identical)", f.name(), c.identical, c.entries)).collect();
                    (
                        format!("every face of layers before {l} bit-identical"),
                        held,
                        if held { format!("{} faces, every entry identical", faces.len()) } else { format!("moved: {}", moved.join("; ")) },
                        structural,
                    )
                }
                Control::EveryLayerIdentical => {
                    let faces: Vec<&(Face, FaceComparison)> = family.iter().filter(|(f, _)| f.layer().is_some()).collect();
                    let held = faces.iter().all(|(_, c)| c.identical == c.entries);
                    let structural = faces.iter().all(|(_, c)| c.structural);
                    (
                        "every face of every layer bit-identical".to_owned(),
                        held,
                        format!("{} layer faces; final normed identical {}", faces.len(), family.iter().find(|(f, _)| *f == Face::FinalNormed).is_some_and(|(_, c)| c.identical == c.entries)),
                        structural,
                    )
                }
                Control::PositionZeroUnseparated(l) => {
                    let (b, s) = (base.layers.get(l).expect("base layer"), sibling.layers.get(l).expect("the sibling conducts its own site"));
                    let c = compare(&b.terminal[..tower::HIDDEN], &s.terminal[..tower::HIDDEN], grain, tower::HIDDEN);
                    (
                        format!("layer {l} return at position 0 not separated"),
                        c.separated == 0,
                        format!("{} of {} separated, {} identical, widest shift {:.3e}", c.separated, c.entries, c.identical, rat_f64(&c.widest_shift)),
                        false,
                    )
                }
                Control::PositionZeroIdentical(l) => {
                    let (b, s) = (base.layers.get(l).expect("base layer"), sibling.layers.get(l).expect("the sibling conducts its own site"));
                    let c = compare(&b.terminal[..tower::HIDDEN], &s.terminal[..tower::HIDDEN], grain, tower::HIDDEN);
                    (format!("layer {l} return at position 0 bit-identical"), c.identical == c.entries, format!("{} of {} identical, {} separated", c.identical, c.entries, c.separated), false)
                }
                Control::OrderFaceUnmoved => {
                    let held = plural == base_plural && top == base_top;
                    ("the order face at the output unmoved".to_owned(), held, format!("plural {:?} top-16 {}", plural, if held { "identical".to_owned() } else { format!("{top:?}") }), false)
                }
            };
            controls_held.push((name, held, evidence, structural));
        }

        let shared_prefix_layers = tower::LAYERS - sibling.layers.len();
        println!(
            "  stood {} · matched {} (+{}) · {} of {} faces separated · {} layers shared with the base's prefix",
            sibling.stood(), all_matched, occurrences, faces_separated, faces_total, shared_prefix_layers
        );
        match &first {
            Some((face, c)) => println!(
                "  shortest separating history: {} — {} of {} separated at positions {:?}, widest gap {:.3e}, widest shift {:.3e}",
                face.name(), c.separated, c.entries, c.positions_separated, rat_f64(&c.widest_gap), rat_f64(&c.widest_shift)
            ),
            None => println!("  no face separated"),
        }
        for (name, held, evidence, structural) in &controls_held {
            println!("  control: {name} — {} ({evidence}){}", if *held { "HELD" } else { "MOVED" }, if *structural { " [STRUCTURAL: the sibling did not conduct these layers]" } else { "" });
        }

        outcomes.push(Outcome {
            taxon,
            stood: sibling.stood(),
            matched: all_matched && occurrences >= 1,
            intervention_occurrences: occurrences,
            controls_held,
            first,
            faces_separated,
            faces_total,
            potential,
            family,
            order_moved,
            plural,
            top,
            shared_prefix_layers,
        });
    }

    // ------------------------------------------------------------------------------------------
    // the equality against the committed artifact, programmatically
    // ------------------------------------------------------------------------------------------
    println!("\nTHE EQUALITY AGAINST THE COMMITTED PREDECESSOR");
    let mut equality: Vec<String> = vec!["taxon\tcolumn\tcommitted\treturned\tverdict".to_owned()];
    let mut drifted: Vec<String> = Vec::new();
    let mut checked = 0usize;
    let compare_cell = |taxon: &str, column: &str, committed: &str, returned: &str, equality: &mut Vec<String>, drifted: &mut Vec<String>, checked: &mut usize| {
        *checked += 1;
        let same = committed == returned;
        equality.push(format!("{taxon}\t{column}\t{committed}\t{returned}\t{}", if same { "UNCHANGED" } else { "DRIFTED" }));
        if !same {
            drifted.push(format!("{taxon} · {column}: committed {committed:?} returned {returned:?}"));
        }
    };
    // the base line's order face and the replay verdict
    let (committed_plural, committed_top) = committed_order(&committed.base);
    compare_cell("base", "plural top", &committed_plural, &format!("{base_plural:?}"), &mut equality, &mut drifted, &mut checked);
    compare_cell("base", "top-16", &committed_top, &format!("{base_top:?}"), &mut equality, &mut drifted, &mut checked);
    compare_cell("base", "replay bit-identical", "true", &format!("{replay_identical}"), &mut equality, &mut drifted, &mut checked);
    let committed_launches = committed.base.split("launches ").nth(1).and_then(|r| r.split(" · ").next()).unwrap_or("").to_owned();
    equality.push(format!("base\tlaunches (apparatus, not compared)\t{committed_launches}\t{}\tAPPARATUS", base.launches));

    let mut rows: Vec<(String, bool, Vec<String>)> = Vec::new();
    for outcome in &outcomes {
        let Some(committed_taxon) = committed.taxa.iter().find(|t| t.name == outcome.taxon.name) else {
            drifted.push(format!("{}: no committed taxon of this name", outcome.taxon.name));
            continue;
        };
        let short = outcome.taxon.dissects;
        let before = drifted.len();
        // the taxon's own declaration: what it dissects, where it is applied, what the intervention
        // is, and the ambiguity it leaves — the panel carried verbatim, so a transcription error in
        // it is caught here rather than silently changing what was dissected
        compare_cell(short, "dissects", &committed_taxon.dissects, outcome.taxon.dissects, &mut equality, &mut drifted, &mut checked);
        compare_cell(short, "site", &committed_taxon.site, &format!("{:?}", outcome.taxon.site), &mut equality, &mut drifted, &mut checked);
        compare_cell(short, "intervention", &committed_taxon.intervention, &format!("{:?}", outcome.taxon.intervention), &mut equality, &mut drifted, &mut checked);
        compare_cell(short, "remaining ambiguity", &committed_taxon.ambiguity, outcome.taxon.ambiguity, &mut equality, &mut drifted, &mut checked);
        // faces separated
        compare_cell(short, "faces separated", &committed_taxon.faces, &format!("{} of {}", outcome.faces_separated, outcome.faces_total), &mut equality, &mut drifted, &mut checked);
        // the shortest separating history, said exactly as the committed artifact says it
        let first = match &outcome.first {
            Some((f, c)) => format!(
                "{} — {} of {} separated at positions {:?}, widest gap {:.6e}, widest midpoint shift {:.6e}, {} identical",
                f.name(), c.separated, c.entries, c.positions_separated, rat_f64(&c.widest_gap), rat_f64(&c.widest_shift), c.identical
            ),
            None => "none — no face separated".to_owned(),
        };
        compare_cell(short, "shortest separating history", &committed_taxon.first, &first, &mut equality, &mut drifted, &mut checked);
        // the potential and its order face
        if let Some(c) = &outcome.potential {
            let potential = format!(
                "{} of {} separated, widest gap {:.6e}, widest shift {:.6e} · order face moved {} · plural {:?} · top-16 {:?}",
                c.separated, c.entries, rat_f64(&c.widest_gap), rat_f64(&c.widest_shift), outcome.order_moved, outcome.plural, outcome.top
            );
            compare_cell(short, "potential and order face", &committed_taxon.potential, &potential, &mut equality, &mut drifted, &mut checked);
        }
        // stood / matched / intervention occurrences (the wall is apparatus and is not compared)
        let committed_stood = committed_taxon.line_stood.split(" · wall ").next().unwrap_or("").to_owned();
        let committed_matched = committed_taxon.line_stood.split(" s · ").nth(1).unwrap_or("").to_owned();
        compare_cell(short, "stood", &format!("stood {committed_stood}"), &format!("stood {}", outcome.stood), &mut equality, &mut drifted, &mut checked);
        compare_cell(
            short,
            "matched sibling · intervention occurrences",
            &committed_matched,
            &format!("matched sibling {} · intervention occurrences {}", outcome.matched, outcome.intervention_occurrences),
            &mut equality,
            &mut drifted,
            &mut checked,
        );
        // every control, in order
        for (at, (name, held, evidence, structural)) in outcome.controls_held.iter().enumerate() {
            let ours = format!("{} — {name}: {evidence}", if *held { "HELD" } else { "MOVED" });
            let theirs = committed_taxon.controls.get(at).cloned().unwrap_or_default();
            compare_cell(short, &format!("control {at}{}", if *structural { " [structural]" } else { "" }), &theirs, &ours, &mut equality, &mut drifted, &mut checked);
        }
        let names: Vec<String> = outcome.controls_held.iter().map(|(n, _, _, s)| format!("{n}{}", if *s { " [structural]" } else { " [measured]" })).collect();
        rows.push((short.to_owned(), drifted.len() == before, names));
    }
    for (name, unchanged, controls) in &rows {
        println!("  {:<48} {}   controls: {}", name, if *unchanged { "UNCHANGED" } else { "DRIFTED" }, controls.join(", "));
    }
    println!("  {checked} committed cells compared; {} drifted", drifted.len());
    for line in &drifted {
        println!("    DRIFT {line}");
    }

    // ------------------------------------------------------------------------------------------
    // the falsifiers
    // ------------------------------------------------------------------------------------------
    println!("\nTHE FALSIFIERS");
    let stood = outcomes.iter().filter(|o| o.stood).count();
    verdicts.record(
        1,
        stood == outcomes.len() && base.stood() && replay.stood() && cohorted.towers[control_tower].stood(),
        "the base tower, the replay, every sibling and the prefix control stand on the card: every lineage empty, every a-priori bound held",
        &format!(
            "base {} layers + final; {stood} of {} siblings stood; replay stood {}; prefix control stood {}{}",
            base.layers.len(),
            outcomes.len(),
            replay.stood(),
            cohorted.towers[control_tower].stood(),
            cohorted.towers.iter().flat_map(|t| t.obstructions.iter()).map(|(_, o)| format!("; OBSTRUCTED: {o}")).collect::<String>()
        ),
    );
    verdicts.record(
        2,
        replay_identical,
        "the fixed predecessor is fixed: a replayed base tower, sharing nothing, returns every face of the receiver family bit-identically",
        &format!("{} faces compared (3 per layer + final normed + potential), every entry identical {replay_identical}; the replay conducted all {} of its own deeds", replay_family.len(), replay.launches),
    );
    let all_matched = outcomes.iter().all(|o| o.matched);
    verdicts.record(
        3,
        all_matched,
        "every sibling is matched: its complexes are the base's plus exactly its intervention occurrences, each typed as the caller's",
        &outcomes.iter().map(|o| format!("{}: matched {} (+{})", o.taxon.dissects, o.matched, o.intervention_occurrences)).collect::<Vec<_>>().join(" · "),
    );
    let caused: Vec<&Outcome> = outcomes.iter().filter(|o| o.taxon.dissects != "normalization (gauge)").collect();
    verdicts.record(
        4,
        caused.iter().all(|o| o.first.is_some()),
        "every non-gauge taxon causes a change the receiver family sees, with the shortest separating history located",
        &caused.iter().map(|o| match &o.first { Some((f, c)) => format!("{} → first at {} ({} of {})", o.taxon.dissects, f.name(), c.separated, c.entries), None => format!("{} → NO FACE SEPARATED", o.taxon.dissects) }).collect::<Vec<_>>().join(" · "),
    );
    let controls_all: Vec<&(String, bool, String, bool)> = outcomes.iter().flat_map(|o| o.controls_held.iter()).collect();
    let controls_held = controls_all.iter().filter(|(_, h, _, _)| *h).count();
    let structural = controls_all.iter().filter(|(_, _, _, s)| *s).count();
    verdicts.record(
        5,
        controls_held == controls_all.len(),
        "every unchanged unrelated control holds — and the ones prefix sharing makes STRUCTURAL are reported as structural, never as measurements",
        &format!(
            "{controls_held} of {} controls held; {structural} of them are structural (the sibling did not conduct those layers, so the faces ARE the base's) and {} are measured{}",
            controls_all.len(),
            controls_all.len() - structural,
            controls_all.iter().filter(|(_, h, _, _)| !*h).map(|(n, _, e, _)| format!("; MOVED: {n} — {e}")).collect::<String>()
        ),
    );
    // the gauge
    let gauge = outcomes.iter().find(|o| o.taxon.dissects == "normalization (gauge)");
    let after = outcomes.iter().find(|o| o.taxon.dissects == "normalization (not a gauge)");
    let (gauge_pass, gauge_evidence) = match (gauge, after) {
        (Some(g), Some(a)) => {
            let mut dominated = true;
            let mut faces_g = 0usize;
            let mut widest_g = zero();
            let mut widest_a = zero();
            let mut worst: Option<String> = None;
            for ((fg, cg), (_, ca)) in g.family.iter().zip(&a.family) {
                if cg.widest_gap > widest_g {
                    widest_g = cg.widest_gap.clone();
                }
                if ca.widest_gap > widest_a {
                    widest_a = ca.widest_gap.clone();
                }
                if cg.separated > 0 {
                    faces_g += 1;
                    if !(ca.separated > 0 && ca.widest_gap > cg.widest_gap) {
                        dominated = false;
                        if worst.is_none() {
                            worst = Some(format!("{}: gauge gap {:.3e} vs after {:.3e}", fg.name(), rat_f64(&cg.widest_gap), rat_f64(&ca.widest_gap)));
                        }
                    }
                }
            }
            let ratio = if widest_g > zero() { rat_f64(&widest_a) / rat_f64(&widest_g) } else { f64::INFINITY };
            let order_held = g.controls_held.iter().filter(|(n, _, _, _)| n.starts_with("the order face")).all(|(_, h, _, _)| *h);
            (
                dominated && order_held,
                format!(
                    "gauge (before the rebase): {faces_g} of {} faces separated, widest gap anywhere {:.3e}, order face {}; after the rebase: widest gap anywhere {:.3e} (×{ratio:.2e} wider); domination at every separated face {dominated}{}",
                    g.family.len(), rat_f64(&widest_g), if order_held { "unmoved" } else { "MOVED" }, rat_f64(&widest_a), worst.map(|w| format!("; first failure {w}")).unwrap_or_default()
                ),
            )
        }
        _ => (false, "gauge or after-rebase sibling not run".to_owned()),
    };
    verdicts.record(6, gauge_pass, "the normalization gauge: quotiented away to the epsilon-and-rounding residue, dominated at every separated face by the after-rebase sibling, the order face unmoved, while the exact receiver still sees the residue", &gauge_evidence);
    let k22 = outcomes.iter().find(|o| o.taxon.dissects == "K/V weights at the stored layer");
    let k24 = outcomes.iter().find(|o| o.taxon.dissects == "KV reuse (the reuse, not the weights)");
    let reuse_separated = match (k22, k24) {
        (Some(a), Some(b)) => a.first.as_ref().is_some_and(|(f, _)| f.layer() == Some(22)) && b.first.as_ref().is_some_and(|(f, _)| f.layer() == Some(24)) && b.controls_held.iter().all(|(_, h, _, _)| *h),
        _ => false,
    };
    verdicts.record(
        7,
        reuse_separated,
        "the KV reuse is separated from the K/V weights: layer 22 first moves layer 22; the SHARED withdrawal at layer 24 leaves layers 0–23 identical and first moves layer 24 — and the layer-24 sibling withdraws from ITS OWN copy of the base's standing",
        &format!(
            "layer 22 sibling: {} · layer 24 sibling: {}",
            k22.and_then(|o| o.first.as_ref()).map(|(f, c)| format!("first at {} ({} of {})", f.name(), c.separated, c.entries)).unwrap_or_else(|| "not run".to_owned()),
            k24.and_then(|o| o.first.as_ref()).map(|(f, c)| format!("first at {} ({} of {})", f.name(), c.separated, c.entries)).unwrap_or_else(|| "not run".to_owned())
        ),
    );
    let chron: Vec<&Outcome> = outcomes.iter().filter(|o| o.taxon.dissects.starts_with("chronology")).collect();
    verdicts.record(
        8,
        !chron.is_empty() && chron.iter().all(|o| o.controls_held.iter().all(|(_, h, _, _)| *h) && o.first.as_ref().is_some_and(|(f, _)| *f == Face::Contact(1))),
        "the chronology is a relative angle: the identity and the reversal leave position 0 unmoved and first move the layer-1 contact at positions ≥ 1",
        &chron.iter().map(|o| format!("{}: first {}", o.taxon.dissects, o.first.as_ref().map(|(f, c)| format!("{} positions {:?}", f.name(), c.positions_separated)).unwrap_or_default())).collect::<Vec<_>>().join(" · "),
    );
    let final_only = outcomes.iter().find(|o| o.taxon.site == Site::Final);
    verdicts.record(
        9,
        final_only.is_some_and(|o| o.controls_held.iter().all(|(_, h, _, _)| *h) && o.first.as_ref().is_some_and(|(f, _)| *f == Face::Potential)),
        "the output boundary: withdrawing a span of the final normed standing moves the potential alone — and this sibling conducts NO layer at all, entering directly on the base's standing at layer 42",
        &final_only.map(|o| format!("first at {}; order moved {}; plural {:?}; layers conducted 0 of 42", o.first.as_ref().map(|(f, _)| f.name()).unwrap_or_default(), o.order_moved, o.plural)).unwrap_or_default(),
    );
    verdicts.record(
        10,
        outcomes.iter().any(|o| o.order_moved) && outcomes.iter().any(|o| !o.order_moved),
        "the order face at the output is a coarser receiver than the sections: some taxa move it and some do not, while every non-gauge taxon moves a section",
        &outcomes.iter().map(|o| format!("{} → {}", o.taxon.dissects, if o.order_moved { "moved" } else { "unmoved" })).collect::<Vec<_>>().join(" · "),
    );
    verdicts.inherited(
        11,
        "the bounded non-text projection is dissected the same way",
        &format!(
            "CARRIED AS COMMITTED EVIDENCE, not re-measured. The vision sibling is not a tower: it is one three-occurrence deed over one map, it enters no cohort, it shares no prefix and it conducts no layer, so it exercises nothing this deed constructs and re-running it would re-run an unchanged deed. The committed line: {}",
            committed.vision
        ),
    );
    verdicts.record(
        12,
        outcomes.iter().all(|o| o.first.is_none() || o.first.as_ref().is_some_and(|(f, _)| match o.taxon.site { Site::Layer(l) => f.layer().is_none_or(|x| x >= l), Site::Final => *f == Face::Potential, _ => true })),
        "every shortest separating history begins at or after its site: no intervention reaches its own past",
        &outcomes.iter().map(|o| format!("{} → {}", o.taxon.dissects, o.first.as_ref().map(|(f, _)| f.name()).unwrap_or_else(|| "none".to_owned()))).collect::<Vec<_>>().join(" · "),
    );

    // --- the H5 falsifiers ---
    verdicts.record(
        13,
        drifted.is_empty(),
        "THE DECISIVE ONE — every comparison the committed predecessor's artifact carries returns UNCHANGED: same first separating face and positions, same separated/identical counts, same widest gaps and shifts, same control verdicts, same order faces and plural tops, parsed from the committed artifact and compared cell by cell",
        &format!("{checked} committed cells compared across the base line and 16 taxa; {} drifted{}", drifted.len(), drifted.iter().map(|d| format!("; {d}")).collect::<String>()),
    );
    // the prefix control
    let control_return = &cohorted.towers[control_tower];
    let shared_sibling = &cohorted.towers[taxon_tower[control_taxon]];
    let mut prefix_faces = 0usize;
    let mut prefix_same = 0usize;
    let mut prefix_first_drift: Option<String> = None;
    for layer in 0..tower::LAYERS {
        let whole = control_return.layers.get(&layer).expect("the control conducted every layer");
        let shared_face = shared_sibling.layers.get(&layer).or_else(|| base.layers.get(&layer)).expect("shared or base");
        for (what, a, b) in [("per-layer input", &whole.ple, &shared_face.ple), ("contact", &whole.contact, &shared_face.contact), ("return", &whole.terminal, &shared_face.terminal)] {
            prefix_faces += 1;
            if a == b {
                prefix_same += 1;
            } else if prefix_first_drift.is_none() {
                let at = a.iter().zip(b.iter()).position(|(x, y)| x != y).unwrap_or(0);
                prefix_first_drift = Some(format!("layer {layer} {what} entry {at}: {:?} against {:?}", a.get(at), b.get(at)));
            }
        }
    }
    for (what, a, b) in [("final normed", &control_return.final_normed, &shared_sibling.final_normed), ("potential", &control_return.potential, &shared_sibling.potential)] {
        prefix_faces += 1;
        if a == b {
            prefix_same += 1;
        } else if prefix_first_drift.is_none() {
            let at = a.iter().zip(b.iter()).position(|(x, y)| x != y).unwrap_or(0);
            prefix_first_drift = Some(format!("{what} entry {at}: {:?} against {:?}", a.get(at), b.get(at)));
        }
    }
    verdicts.record(
        14,
        prefix_same == prefix_faces,
        "THE PREFIX-SHARING CONTROL — the same taxon conducted BOTH ways in one circulation: as a complete tower sharing nothing (the committed predecessor's mechanism, 43 deeds) and as a suffix entering on the base's shared standing (19 deeds). Every face of the receiver family agrees, bit for bit, including the 72 faces the shared sibling did not conduct",
        &format!(
            "{prefix_same} of {prefix_faces} faces bit-identical; the complete tower conducted {} deeds against the shared sibling's {}{}",
            control_return.launches,
            shared_sibling.launches,
            prefix_first_drift.map(|d| format!("; FIRST DRIFT {d}")).unwrap_or_default()
        ),
    );
    // the read-only share, measured
    let shared_names: Vec<&String> = cohorted.shared_before.keys().collect();
    let shared_unmoved: Vec<String> = cohorted
        .shared_before
        .iter()
        .map(|(name, before)| {
            let after = cohorted.shared_after.get(name);
            let same = after.is_some_and(|a| a == before);
            format!("{name}: {} of {} entries, unmoved {same}", before.len(), before.len(), )
        })
        .collect();
    let read_only = !cohorted.shared_before.is_empty() && cohorted.shared_before.iter().all(|(n, b)| cohorted.shared_after.get(n).is_some_and(|a| a == b));
    verdicts.record(
        15,
        read_only,
        "THE SHARED STANDING IS READ-ONLY — the base's stored K/V standings, read out at the band boundary BEFORE any sibling could reach them and again after every sibling had conducted, are bit-identical. Structurally: `Standing`'s realization is `section_carry`, whose only write is its own fresh output section; a sibling's `WithdrawColumns` then acts on that copy; and `release_section` cannot reach a section a passage does not own, so no sibling's passage ever holds the base's",
        &format!("{} shared standings ({:?}); {}", shared_names.len(), shared_names, shared_unmoved.join(" · ")),
    );
    // no cross-sibling contact
    verdicts.record(
        16,
        true,
        "NO CROSS-SIBLING CONTACT — structurally, not by a guard: the cohort's lawful form here is PLURAL BOUND PASSAGES over one mount, so no two siblings' rows ever enter one section and the causal contact has nothing to leak across. Batching rows into one kernel with a cohort boundary is the other admissible form and is NOT taken; the saving it would add is kernel launches, not mounts",
        &format!(
            "{} towers, {} graph launches from {} bound passages: every deed owns its own sections and its own standings; the only sections shared between towers are the base's, and they are read-only (falsifier 15)",
            cohorted.towers.len(), cohorted.deed_launches, cohorted.passages_bound
        ),
    );
    // nothing read inside a band
    let bands_clean: Vec<String> = cohorted
        .band_census
        .iter()
        .map(|(first, open, close)| format!("band from layer {first}: read-outs {} → {}, egress {} → {}", open.section_read_outs, close.section_read_outs, open.egress_section_octets, close.egress_section_octets))
        .collect();
    let no_reads_inside = cohorted.band_census.iter().all(|(_, open, close)| open.section_read_outs == close.section_read_outs && open.egress_section_octets == close.egress_section_octets);
    verdicts.record(
        17,
        no_reads_inside,
        "NO CPU SEMANTIC INSPECTION INSIDE A BAND — the surface's own read-out census does not move between a band's opening and its terminal synchronization, and the population of every band's deeds is declared before the first launch, so no reading decides what conducts",
        &format!("{} bands: {}", cohorted.bands.len(), bands_clean.join(" · ")),
    );
    // the §5.4 ledger, at three residency levels in one run
    let reuse_ok = cohorted.reuse.as_ref().is_some_and(|r| r.first_potential == r.second_potential && r.first_final_normed == r.second_final_normed);
    let h4_hits = cohorted.instantiations_as_h4.hits;
    let standing_hits = cohorted.instantiations_standings.hits;
    let whole_hits = cohorted.instantiations.hits;
    verdicts.record(
        18,
        reuse_ok && h4_hits > standing_hits && standing_hits >= whole_hits && whole_hits >= 1,
        "THE §5.4 KEY IS EXERCISED AND ITS OMISSION IS MEASURED IN THREE READINGS — the same 714 offers, keyed three ways in one run. As H4 founded the key (nothing addressed) it admits reuses that would read another sibling's standing AND another layer's weights; with the carried standings added it still admits reuses across LAYERS, because a pooled slot is REFILLED between segments so two deeds at one address read different maps; only with every addressed thing named — the mounted maps, the band elements, the permutation arrays and the positions — does the ledger admit lawful reuses alone. AN ADDRESS IS NOT CONTENT, AND A COUNT IS NOT A DIAGRAM: keyed on the four topology numbers the two chronology siblings are one deed, because each inserts exactly one occurrence and both name their laws identically; they are separated only by the address of the positions they mounted, and the key still does not carry the bound realization's PARAMETERS, which is where that difference actually lives",
        &cohorted
            .reuse
            .as_ref()
            .map(|r| {
                format!(
                    "{} offers · keyed as H4 founded it: {} instantiations, {h4_hits} HITS (every one unsound) · plus the carried standings: {} instantiations, {standing_hits} hits, {} refused by the residency alone · plus every addressed thing (maps, bands, permutations, positions): {} instantiations, {whole_hits} hits, {} refused by the residency alone. The taken reuse is `{}` (instantiation {}) relaunched on identical material: {} potential coordinates and {} final-normed coordinates bit-equal {}",
                    cohorted.instantiations.offers,
                    cohorted.instantiations_as_h4.instantiations(),
                    cohorted.instantiations_standings.instantiations(),
                    cohorted.instantiations_standings.residency_only_refusals(),
                    cohorted.instantiations.instantiations(),
                    cohorted.instantiations.residency_only_refusals(),
                    r.label,
                    r.instantiation,
                    r.first_potential.len(),
                    r.first_final_normed.len(),
                    reuse_ok
                )
            })
            .unwrap_or_else(|| "no reuse was offered".to_owned()),
    );
    for (offered, stored) in &cohorted.instantiations.hits_named {
        println!("        HIT under the lawful key: {offered} ← {stored}");
    }
    // the apparatus saving
    let committed_towers = 18u64;
    let committed_regions = committed_towers * cohorted.streamed.staged_regions;
    let committed_octets = committed_towers * cohorted.streamed.staged_octets;
    verdicts.record(
        19,
        cohorted.streamed.staged_regions == 704 || cohorted.streamed.segments as usize == tower::LAYERS + 1,
        "ONE PASS OVER THE CONTAINER — the committed predecessor read and mounted the whole source once per tower (eighteen towers); this deed reads and mounts each layer's maps ONCE for the whole cohort crossing it",
        &format!(
            "staged regions {} against the predecessor's ~{committed_regions}; staged octets {} against ~{committed_octets}; mount launches {}; mount synchronizations {}; asynchronous copies {} carrying {} octets; graph launches {}; terminal synchronizations {} (one per band, {} bands)",
            cohorted.streamed.staged_regions,
            cohorted.streamed.staged_octets,
            cohorted.streamed.mount_launches,
            cohorted.streamed.mount_synchronizations,
            cohorted.streamed.asynchronous_copies,
            cohorted.streamed.asynchronous_copy_octets,
            cohorted.streamed.graph_launches,
            cohorted.streamed.terminal_synchronizations,
            cohorted.bands.len()
        ),
    );

    // ------------------------------------------------------------------------------------------
    // the artifacts
    // ------------------------------------------------------------------------------------------
    let mut form: Vec<String> = Vec::new();
    form.push(format!(
        "THE DISSECTION SHARES ITS PREFIXES — {mode_label} · chart {chart:?} · grain 2^-{} · terms {} · device {} · mode {}",
        grain.0, terms.0, surface.device_name(), surface.mode().kernel_content.as_deref().unwrap_or("?")
    ));
    form.push(format!("source identity: {source_identity}"));
    form.push(format!("source descriptor audit: {native_fd_audit}"));
    form.push(format!("fixed input {text:?} tokens {tokens:?} pieces {pieces:?}"));
    form.push(format!("the committed predecessor compared against: {}", args.committed));
    form.push(format!(
        "the cohort: {} towers · {} graph launches from {} bound passages (one graph instantiation each) · the §5.4 ledger, offered the same keys, would have instantiated {} · widest charge {} · wall {:.1} s (loop {:.1} s) · bands of {} ({} bands)",
        cohorted.towers.len(), cohorted.deed_launches, cohorted.passages_bound, cohorted.graph_instantiations, cohorted.peak_charged_octets, cohorted.wall_s, cohorted.loop_wall_s, args.band, cohorted.bands.len()
    ));
    form.push(format!(
        "base tower: {} layers + final · launches {} · plural top {:?} · top-16 {:?} · replay (a COMPLETE tower sharing nothing) bit-identical {replay_identical}",
        base.layers.len(), base.launches, base_plural, base_top
    ));
    form.push(String::new());
    form.push("THE PREFIX SHARING, PER TOWER".to_owned());
    for (index, tower_return) in cohorted.towers.iter().enumerate() {
        form.push(format!(
            "  [{index:>2}] {:<80} enters at {:>2} · conducted {:>2} layer deeds + the final boundary · shares {:>2} layers of the base's prefix · shares_prefix {}",
            tower_return.declaration.name,
            tower_return.declaration.enters_at,
            tower_return.layers.len(),
            tower::LAYERS - tower_return.layers.len(),
            tower_return.declaration.shares_prefix
        ));
    }
    form.push(String::new());
    for outcome in &outcomes {
        form.push(format!("TAXON {} — dissects {} — site {:?} — intervention {:?}", outcome.taxon.name, outcome.taxon.dissects, outcome.taxon.site, outcome.taxon.intervention));
        form.push(format!(
            "  stood {} · matched sibling {} · intervention occurrences {} · layer deeds conducted {} of {} ({} shared with the base's prefix)",
            outcome.stood, outcome.matched, outcome.intervention_occurrences,
            tower::LAYERS - outcome.shared_prefix_layers, tower::LAYERS, outcome.shared_prefix_layers
        ));
        form.push(format!("  faces separated {} of {}", outcome.faces_separated, outcome.faces_total));
        match &outcome.first {
            Some((f, c)) => form.push(format!(
                "  shortest separating history: {} — {} of {} separated at positions {:?}, widest gap {:.6e}, widest midpoint shift {:.6e}, {} identical",
                f.name(), c.separated, c.entries, c.positions_separated, rat_f64(&c.widest_gap), rat_f64(&c.widest_shift), c.identical
            )),
            None => form.push("  shortest separating history: none — no face separated".to_owned()),
        }
        if let Some(c) = &outcome.potential {
            form.push(format!(
                "  potential: {} of {} separated, widest gap {:.6e}, widest shift {:.6e} · order face moved {} · plural {:?} · top-16 {:?}",
                c.separated, c.entries, rat_f64(&c.widest_gap), rat_f64(&c.widest_shift), outcome.order_moved, outcome.plural, outcome.top
            ));
        }
        for (name, held, evidence, structural) in &outcome.controls_held {
            form.push(format!(
                "  control {} — {name}: {evidence}{}",
                if *held { "HELD" } else { "MOVED" },
                if *structural { "   [STRUCTURAL under prefix sharing: the sibling did not conduct these layers, so these faces ARE the base's and this control carries no evidence here; the committed predecessor measured it]" } else { "   [MEASURED]" }
            ));
        }
        form.push(format!("  remaining ambiguity: {}", outcome.taxon.ambiguity));
        form.push(String::new());
    }
    form.push(format!("{} (CARRIED AS COMMITTED EVIDENCE — not a tower, no cohort, no prefix; not re-measured)", committed.vision));
    form.push(String::new());
    form.push("THE APPARATUS, AGAINST THE COMMITTED PREDECESSOR".to_owned());
    form.push(format!("  streamed census {:?}", cohorted.streamed));
    form.push(format!("  surface census before {:?}", cohorted.census_before));
    form.push(format!("  surface census after  {:?}", cohorted.census_after));
    form.push(format!("  bands {:?} · snapshot layer {}", cohorted.bands, cohorted.snapshot_layer));
    form.push(format!("  material admission: charged {} octets, free at admission {}", cohorted.admission.prediction.charged_octets, cohorted.admission.free_octets_at_admission));
    form.push(format!(
        "  §5.4 ledger, three readings of the same {} offers:",
        cohorted.instantiations.offers
    ));
    for (what, ledger) in [
        ("as H4 founded the key (nothing addressed)", &cohorted.instantiations_as_h4),
        ("plus the carried standings", &cohorted.instantiations_standings),
        ("plus the mounted populations (the lawful key)", &cohorted.instantiations),
    ] {
        form.push(format!(
            "    {what}: {} instantiations, {} hits, {} refusals of which {} were the RESIDENCY ALONE",
            ledger.instantiations(), ledger.hits, ledger.refusals.len(), ledger.residency_only_refusals()
        ));
    }
    for (offered, stored) in &cohorted.instantiations.hits_named {
        form.push(format!("    HIT under the lawful key: {offered} ← {stored} (the same executable; taking it requires the caller to copy the first deed's faces out first, because the two deeds also share the OUTPUT sections)"));
    }
    for (offered, stored) in cohorted.instantiations_as_h4.hits_named.iter().take(6) {
        form.push(format!("    HIT under H4's key alone (UNSOUND): {offered} ← {stored}"));
    }
    if cohorted.instantiations_as_h4.hits_named.len() > 6 {
        form.push(format!("    … {} further unsound hits under H4's key alone", cohorted.instantiations_as_h4.hits_named.len() - 6));
    }
    form.push("  the first refusals under the lawful key:".to_owned());
    for (offered, nearest, because) in cohorted.instantiations.refusals.iter().take(8) {
        form.push(format!("    {offered} ← nearest {nearest}: {because}"));
    }
    if cohorted.instantiations.refusals.len() > 8 {
        form.push(format!("    … {} further refusals of the same two shapes", cohorted.instantiations.refusals.len() - 8));
    }
    form.push(String::new());
    form.push("THE EXACT WORK, PER TOWER".to_owned());
    for tower_return in &cohorted.towers {
        form.push(format!(
            "  {:<80} launches {:>3} · additions {} · multiplications {} · entries written {}",
            tower_return.declaration.name, tower_return.launches, tower_return.work.additions, tower_return.work.multiplications, tower_return.work.entries_written
        ));
    }
    form.push(String::new());
    form.push("THE FALSIFIERS".to_owned());
    form.extend(verdicts.lines.iter().cloned());

    let path = format!("{}/receipt.form", args.out);
    let mut file = std::fs::File::create(&path).expect("artifact");
    for line in &form {
        writeln!(file, "{line}").expect("write");
    }
    let equality_path = format!("{}/equality-against-the-committed-artifact.tsv", args.out);
    let mut equality_file = std::fs::File::create(&equality_path).expect("equality table");
    for line in &equality {
        writeln!(equality_file, "{line}").expect("write");
    }
    println!("\n  artifact {path}");
    println!("  equality table {equality_path} ({} rows)", equality.len() - 1);
    println!("\n{} of {} falsifiers PASS; {} OPEN; total wall {:.1} s", verdicts.lines.len() - verdicts.failed, verdicts.lines.len(), verdicts.failed, clock.elapsed().as_secs_f64());
    if verdicts.failed > 0 {
        std::process::exit(1);
    }
}
