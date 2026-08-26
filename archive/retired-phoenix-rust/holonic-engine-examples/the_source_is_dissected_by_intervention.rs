//! **Station D of the complete Phoenix sequence: the source dissected by intervention — every taxon
//! of the panel enacted as a matched sibling of one fixed base deed, compared under one declared
//! receiver family, with the shortest separating history, the unchanged unrelated control and the
//! remaining ambiguity returned per taxon.**
//!
//! Plan: the Gemma instance blueprint's dissection station and the Phoenix master's *source
//! dissection by intervention*. The base deed is Station C's tower on one runtime-supplied input under
//! the declared midpoint chart; every sibling is the same tower with exactly one intervention
//! occurrence inserted at one declared site, typed as the caller's (a quotient or an
//! intervention-only transport), never as source law. The receiver family is declared once and
//! read for every deed:
//!
//! ```text
//!   per layer ℓ, in chronology:   the per-layer input section · the contact section · the layer return
//!   then:                          the final normed standing · the potential section (order face: top-16)
//! ```
//!
//! Two enclosures are *separated* when they are disjoint; *identical* when bit-identical. A caused
//! change is a face the sibling separates from the base; the shortest separating history is the first
//! such face in chronology with its positions; the unchanged unrelated control is the face the taxon
//! predicts unmoved, measured; the remaining ambiguity is stated per taxon — chiefly that the tower is
//! carried under the midpoint chart, whose composition is not certified (Station C), so a separation
//! past layer 0 is read at the chart's collapsed points with the enclosure retained per occurrence.
//!
//! The panel (site · kind · the source-law taxon it dissects):
//!
//! ```text
//!   every layer · initial-embedding columns withdrawn         initial embedding
//!   layer 1     · per-layer input withdrawn whole              per-layer embedding (PLE)
//!   layer 1     · standing ×2 before the input rebase          normalization (a gauge, eps-bounded)
//!   layer 1     · standing ×2 after the input rebase           normalization (not a gauge)
//!   layer 1     · identity band elements                       chronology replaced (no rotation)
//!   layer 1     · positions reversed                           chronology permuted
//!   layer 1     · receiver heads 0,1 swapped                   Q/K contact permuted
//!   layer 1     · receiver ×2 before the contact               softmax ratio geometry (temperature)
//!   layer 1     · K/V family 0 withdrawn                       K/V weights (own layer)
//!   layer 22    · K/V family 0 withdrawn                       K/V weights at the stored layer
//!   layer 24    · SHARED K/V family 0 withdrawn                KV reuse (the reuse, not the weights)
//!   layer 1     · carried heads 0,1 swapped before o_proj      V/O transport permuted
//!   layer 1     · retained standing withdrawn at re-entry 1    residual standing (the return alone)
//!   layer 1     · gated passage columns 0..2560 withdrawn      MLP / gated transport
//!   layer 5     · every key/value position but the last        sliding vs global chronology (a window of one)
//!   final       · final normed columns 0..256 withdrawn        output boundary (tied embedding)
//!   vision      · soft-token columns 0..256 withdrawn          the bounded non-text projection
//! ```
//!
//! Run:
//! ```text
//! cargo run --release -q -p holonic-engine --example the_source_is_dissected_by_intervention -- \
//!     --text "The capital of France is" [--grain 48] [--terms 14] [--no-vision]
//! ```

#[path = "phoenix/conduct.rs"]
mod conduct;
#[path = "phoenix/resident_layer.rs"]
mod resident_layer;
#[path = "phoenix/tower.rs"]
mod tower;

use std::collections::BTreeMap;
use std::io::Write;
use std::time::Instant;

use conduct::{Conducted, Site, describe};
use holonic_engine::causal::EventId;
use holonic_engine::embedding_fiber::ResidentReadout;
use holonic_engine::foreign_map::FileIdentity;
use holonic_engine::front_passage::{DeedReceiver, FrontPassage, ResidentMaterial};
use holonic_engine::resident_section::{
    Dyadic, ResidentGrain, ResidentSurface, SeriesAperture, word_value,
};
use holonic_engine::source_occurrence::{RegionIdentity, SourceOccurrence};
use num_bigint::BigInt;
use relational_geometry::Rat;
use resident_layer::Source;
use tower::Intervention;

struct Args {
    root: String,
    out: String,
    text: Option<String>,
    tokens: Option<Vec<usize>>,
    grain: u32,
    terms: u32,
    python: String,
    vision: bool,
    only: Option<String>,
}

fn parse_args() -> Args {
    let mut args = Args {
        root: "/home/b/models/gemma-4-E4B-it".to_owned(),
        out: "output/the_source_is_dissected".to_owned(),
        text: None,
        tokens: None,
        grain: 48,
        terms: 14,
        python: "/home/b/scratch/huggingface/.venv/bin/python".to_owned(),
        vision: true,
        only: None,
    };
    let mut it = std::env::args().skip(1);
    while let Some(flag) = it.next() {
        match flag.as_str() {
            "--root" => args.root = it.next().expect("--root <dir>"),
            "--out" => args.out = it.next().expect("--out <dir>"),
            "--text" => args.text = Some(it.next().expect("--text <text>")),
            "--tokens" => {
                args.tokens = Some(
                    it.next()
                        .expect("--tokens a,b")
                        .split(',')
                        .map(|t| t.trim().parse().expect("token id"))
                        .collect(),
                )
            }
            "--grain" => args.grain = it.next().expect("--grain F").parse().expect("u32"),
            "--terms" => args.terms = it.next().expect("--terms N").parse().expect("u32"),
            "--python" => args.python = it.next().expect("--python <path>"),
            "--no-vision" => args.vision = false,
            "--only" => args.only = Some(it.next().expect("--only <taxon substring>")),
            other => panic!("unknown argument {other}"),
        }
    }
    args
}

fn encode_text(python: &str, text: &str) -> Result<(Vec<usize>, Vec<String>), String> {
    let output = std::process::Command::new(python)
        .arg(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/phoenix/source_runtime_tower.py"
        ))
        .arg("encode")
        .arg(text)
        .output()
        .map_err(|e| e.to_string())?;
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr)
            .chars()
            .take(400)
            .collect());
    }
    for line in String::from_utf8_lossy(&output.stdout).lines() {
        if !line.starts_with('{') {
            continue;
        }
        let json: serde_json::Value = serde_json::from_str(line).map_err(|e| e.to_string())?;
        let ids: Vec<usize> = json["ids"]
            .as_array()
            .ok_or("ids")?
            .iter()
            .filter_map(|v| v.as_u64())
            .map(|v| v as usize)
            .collect();
        let pieces: Vec<String> = json["pieces"]
            .as_array()
            .ok_or("pieces")?
            .iter()
            .filter_map(|v| v.as_str())
            .map(str::to_owned)
            .collect();
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
// the receiver family
// ---------------------------------------------------------------------------------------------

/// Two sections of one face compared entry by entry.
#[derive(Clone, Debug)]
struct FaceComparison {
    entries: usize,
    identical: usize,
    /// enclosures disjoint
    separated: usize,
    /// the widest gap between two separated enclosures
    widest_gap: Rat,
    /// the widest shift of midpoints over every entry (separated or not)
    widest_shift: Rat,
    /// positions (rows) with at least one separated entry, when the face is positional
    positions_separated: Vec<usize>,
}

fn compare(
    base: &[(i64, i64)],
    sibling: &[(i64, i64)],
    grain: ResidentGrain,
    width: usize,
) -> FaceComparison {
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
        }
        let disjoint = bh < sl || sh < bl;
        if disjoint {
            separated += 1;
            let gap = if bh < sl {
                word_value(sl, grain) - word_value(bh, grain)
            } else {
                word_value(bl, grain) - word_value(sh, grain)
            };
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
    FaceComparison {
        entries,
        identical,
        separated,
        widest_gap,
        widest_shift,
        positions_separated: positions,
    }
}

/// One face of the receiver family, named in chronology.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
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

/// The whole receiver family compared: every face in chronology.
fn compare_family(
    base: &Conducted,
    sibling: &Conducted,
    grain: ResidentGrain,
) -> Vec<(Face, FaceComparison)> {
    let mut out = Vec::new();
    for (b, s) in base.layers.iter().zip(&sibling.layers) {
        let head = if b.species == tower::Species::Full {
            tower::FULL_HEAD
        } else {
            tower::SLIDING_HEAD
        };
        out.push((
            Face::Ple(b.layer),
            compare(&b.ple, &s.ple, grain, tower::PLE_WIDTH),
        ));
        out.push((
            Face::Contact(b.layer),
            compare(&b.contact, &s.contact, grain, tower::HEADS * head),
        ));
        out.push((
            Face::Return(b.layer),
            compare(&b.terminal, &s.terminal, grain, tower::HIDDEN),
        ));
    }
    out.push((
        Face::FinalNormed,
        compare(
            &base.final_normed,
            &sibling.final_normed,
            grain,
            tower::HIDDEN,
        ),
    ));
    out.push((
        Face::Potential,
        compare(
            &base.potential,
            &sibling.potential,
            grain,
            tower::VOCABULARY,
        ),
    ));
    out
}

/// The order face of the potential at the last position: the plural top (tokens not separated from
/// the top lower bound) and the top-`n` by lower bound.
fn order_face(
    potential: &[(i64, i64)],
    positions: usize,
    grain: ResidentGrain,
    n: usize,
) -> (Vec<usize>, Vec<usize>) {
    let row = &potential[(positions - 1) * tower::VOCABULARY..positions * tower::VOCABULARY];
    let mut top_lower = word_value(row[0].0, grain);
    for (lo, _) in row {
        let v = word_value(*lo, grain);
        if v > top_lower {
            top_lower = v;
        }
    }
    let mut plural: Vec<usize> = row
        .iter()
        .enumerate()
        .filter(|(_, (_, hi))| word_value(*hi, grain) >= top_lower)
        .map(|(v, _)| v)
        .collect();
    plural.sort_unstable();
    let mut by_lower: Vec<(usize, i64)> = row
        .iter()
        .enumerate()
        .map(|(v, (lo, _))| (v, *lo))
        .collect();
    by_lower.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
    (
        plural,
        by_lower.into_iter().take(n).map(|(v, _)| v).collect(),
    )
}

// ---------------------------------------------------------------------------------------------
// the panel
// ---------------------------------------------------------------------------------------------

/// What the taxon predicts unmoved, measured after the deed.
#[derive(Clone, Debug)]
enum Control {
    /// every face of every layer before `l` bit-identical (the intervention cannot reach its past)
    LayersBeforeIdentical(usize),
    /// every layer's every face bit-identical (only the final graph was touched)
    EveryLayerIdentical,
    /// layer `l`'s return at position 0 not separated (a self-contact under equal rotation)
    PositionZeroUnseparated(usize),
    /// layer `l`'s return at position 0 bit-identical (no rotation at position 0 in either deed)
    PositionZeroIdentical(usize),
    /// the order face at the output unmoved (plural top and top-16 identical)
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
        Taxon {
            name: "initial-embedding columns 0..256 withdrawn at every layer",
            dissects: "initial embedding",
            site: Site::EveryLayer,
            intervention: Intervention::WithdrawEmbeddingColumns { from: 0, span: 256 },
            controls: vec![],
            ambiguity: "x0 enters every layer (the residual at layer 0 and the PLE projection everywhere), so the site is every layer and no predecessor control exists; the change is attributed to the columns, not to a layer",
        },
        Taxon {
            name: "per-layer input withdrawn whole at layer 1",
            dissects: "per-layer embedding (PLE)",
            site: Site::Layer(1),
            intervention: Intervention::WithdrawPle,
            controls: vec![Control::LayersBeforeIdentical(1)],
            ambiguity: "the withdrawn section is the layer's joined PLE (embedding half + projected half); which half carries the change is not separated by this taxon",
        },
        Taxon {
            name: "standing ×2 before the input rebase at layer 1",
            dissects: "normalization (gauge)",
            site: Site::Layer(1),
            intervention: Intervention::ScaleBeforeInputRebase { by: 2 },
            controls: vec![Control::LayersBeforeIdentical(1), Control::OrderFaceUnmoved],
            ambiguity: "the RMS rebase quotients a positive scale away up to its epsilon and the rounding of its radical series, so what survives is that residue; the exact receiver at grain 2^-48 can see it while the order face cannot — tolerance is the receiver's aperture (the scale below which no arc reaches a receiver-relevant difference), so the gauge is stated relative to the after-rebase sibling (domination at every face) and to the order face, never as a threshold; the retained standing is not scaled (the re-entry reads the unscaled standing)",
        },
        Taxon {
            name: "standing ×2 after the input rebase at layer 1",
            dissects: "normalization (not a gauge)",
            site: Site::Layer(1),
            intervention: Intervention::ScaleAfterInputRebase { by: 2 },
            controls: vec![Control::LayersBeforeIdentical(1)],
            ambiguity: "Q, K and V all double, so the contact's ratio sharpens by 4 in the exponent and V doubles; the two are not separated by this taxon",
        },
        Taxon {
            name: "identity band elements at layer 1",
            dissects: "chronology replaced (no rotation)",
            site: Site::Layer(1),
            intervention: Intervention::IdentityChronology,
            controls: vec![
                Control::LayersBeforeIdentical(1),
                Control::PositionZeroIdentical(1),
            ],
            ambiguity: "position 0 is rotated by angle 0 in both deeds, so its self-contact is unchanged by construction; later positions change through the relative angle only",
        },
        Taxon {
            name: "positions reversed at layer 1",
            dissects: "chronology permuted",
            site: Site::Layer(1),
            intervention: Intervention::ReversedPositions,
            controls: vec![
                Control::LayersBeforeIdentical(1),
                Control::PositionZeroUnseparated(1),
            ],
            ambiguity: "position 0's query and key are rotated by one equal angle, whose dot product is invariant in exact arithmetic; at the dyadic grain the rotated words round, so position 0 is predicted unseparated rather than identical",
        },
        Taxon {
            name: "receiver heads 0,1 swapped at layer 1",
            dissects: "Q/K contact permuted",
            site: Site::Layer(1),
            intervention: Intervention::PermuteReceiverHeads { a: 0, b: 1 },
            controls: vec![
                Control::LayersBeforeIdentical(1),
                Control::PositionZeroIdentical(1),
            ],
            ambiguity: "heads 0 and 1 read the same grouped K/V family, so the permutation moves which head's contact reaches which o_proj block; at position 0 the causal contact has one key, its ratio is 1 whatever the receiver, and both heads carry the same V row, so position 0 is predicted bit-identical — the change is the contact's weights at positions ≥ 1 routed through o_proj",
        },
        Taxon {
            name: "receiver ×2 before the contact at layer 1",
            dissects: "softmax ratio geometry (temperature)",
            site: Site::Layer(1),
            intervention: Intervention::ScaleReceiver { by: 2 },
            controls: vec![
                Control::LayersBeforeIdentical(1),
                Control::PositionZeroIdentical(1),
            ],
            ambiguity: "a temperature of 1/2: the ratio family sharpens; V is unchanged, so the change is the contact's weights alone, and at position 0 (one key, ratio 1) there is no weight to sharpen — position 0 is predicted bit-identical",
        },
        Taxon {
            name: "K/V family 0 withdrawn at layer 1",
            dissects: "K/V weights (own layer)",
            site: Site::Layer(1),
            intervention: Intervention::WithdrawKvFamily { family: 0 },
            controls: vec![Control::LayersBeforeIdentical(1)],
            ambiguity: "layer 1 builds and does not store its K/V, so the change reaches later layers only through the residual",
        },
        Taxon {
            name: "K/V family 0 withdrawn at layer 22 (the stored sliding layer)",
            dissects: "K/V weights at the stored layer",
            site: Site::Layer(22),
            intervention: Intervention::WithdrawKvFamily { family: 0 },
            controls: vec![Control::LayersBeforeIdentical(22)],
            ambiguity: "layer 22's own contact and the shared standings both move; which carries the change into layer 24 is separated by the next taxon",
        },
        Taxon {
            name: "SHARED K/V family 0 withdrawn at layer 24 only",
            dissects: "KV reuse (the reuse, not the weights)",
            site: Site::Layer(24),
            intervention: Intervention::WithdrawSharedKvFamily { family: 0 },
            controls: vec![Control::LayersBeforeIdentical(24)],
            ambiguity: "layers 22 and 23 are untouched (their faces identical), so a change here is the reuse's alone; layers 25–41 read the unwithdrawn standings and move only through the residual",
        },
        Taxon {
            name: "carried heads 0,1 swapped before o_proj at layer 1",
            dissects: "V/O transport permuted",
            site: Site::Layer(1),
            intervention: Intervention::PermuteCarriedHeads { a: 0, b: 1 },
            controls: vec![
                Control::LayersBeforeIdentical(1),
                Control::PositionZeroIdentical(1),
            ],
            ambiguity: "the contact section itself is unchanged (it is read before the permutation); the change begins at o_proj; at position 0 the two grouped heads carry the same single V row, so swapping them is the identity there and position 0 is predicted bit-identical",
        },
        Taxon {
            name: "retained standing withdrawn at the first re-entry of layer 1",
            dissects: "residual standing",
            site: Site::Layer(1),
            intervention: Intervention::WithdrawResidualAtFirstReEntry,
            controls: vec![Control::LayersBeforeIdentical(1)],
            ambiguity: "the return stands alone at the first re-entry; the second and third re-entries still retain, so the layer is not made residual-free",
        },
        Taxon {
            name: "gated passage columns 0..2560 withdrawn at layer 1",
            dissects: "MLP / gated transport",
            site: Site::Layer(1),
            intervention: Intervention::WithdrawGateSpan {
                from: 0,
                span: 2560,
            },
            controls: vec![Control::LayersBeforeIdentical(1)],
            ambiguity: "a quarter of the passage; the contact is unchanged (read before the MLP), so the first separating face is predicted to be the layer return",
        },
        Taxon {
            name: "every key/value position but the last withdrawn at layer 5 (full)",
            dissects: "sliding vs global chronology (a window of one)",
            site: Site::Layer(5),
            intervention: Intervention::KeepOnlyLastKeyPosition { tokens },
            controls: vec![Control::LayersBeforeIdentical(5)],
            ambiguity: "every query but the last then reads no key (the causal contact over zero keys returns the empty ratio), and the last reads only itself; the window's effect on the last position alone is what the order face measures",
        },
        Taxon {
            name: "final normed columns 0..256 withdrawn",
            dissects: "output boundary (tied embedding)",
            site: Site::Final,
            intervention: Intervention::WithdrawFinalSpan { from: 0, span: 256 },
            controls: vec![Control::EveryLayerIdentical],
            ambiguity: "the tied boundary reads 2,560 columns; withdrawing a tenth moves the potential by those columns' contribution alone",
        },
    ]
}

/// Is the sibling's complex the base's plus exactly its intervention occurrences? Every extra
/// occurrence must be typed as the caller's intervention (its testimony wholly `Intervention`), and
/// every base occurrence the sibling lacks must be replaced by one such typed occurrence (the
/// chronology laws under the identity / reversed interventions). No base occurrence typed as source
/// law may be an extra.
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
    // the replaced occurrences are not extras beyond their replacement: extra must equal the typed
    // interventions the sibling carries
    (ok, extra, missing)
}

// ---------------------------------------------------------------------------------------------
// the vision projection, with and without the span withdrawn
// ---------------------------------------------------------------------------------------------

#[allow(clippy::too_many_arguments)]
fn vision_projection(
    surface: &'static ResidentSurface<'static>,
    readout: &'static ResidentReadout,
    source: &mut Source,
    root: &str,
    header_regions: &BTreeMap<String, RegionIdentity>,
    content_sha256: &str,
    python: &str,
    out: &str,
    grain: ResidentGrain,
    chart: tower::Chart,
    withdraw: Option<(usize, usize)>,
) -> Result<(Vec<(i64, i64)>, usize, ResidentGrain, Vec<(String, bool)>), String> {
    use holonic_engine::exact_value::ieee754::round_into_bfloat16;
    use holonic_engine::front_passage::{
        Contract, Enter, EnteringRows, MountedPopulation, ResidentRealization, RmsRebase,
        WithdrawColumns,
    };
    use holonic_engine::ported_operation::{OperationSpecies, PortedOperationComplex};
    let emit = format!("{out}/vision-soft-tokens.tsv");
    if !std::path::Path::new(&emit).exists() {
        let output = std::process::Command::new(python)
            .arg(concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/examples/phoenix/source_runtime_tower.py"
            ))
            .args(["vision", "--emit", &emit])
            .output()
            .map_err(|e| e.to_string())?;
        if !output.status.success() {
            return Err(format!(
                "the exterior vision tower refused: {}",
                String::from_utf8_lossy(&output.stderr)
                    .chars()
                    .take(400)
                    .collect::<String>()
            ));
        }
    }
    let text = std::fs::read_to_string(&emit).map_err(|e| e.to_string())?;
    let mut soft: BTreeMap<usize, Vec<(usize, Rat)>> = BTreeMap::new();
    for line in text.lines() {
        if line.starts_with('#') || line.trim().is_empty() {
            continue;
        }
        let parts: Vec<&str> = line.splitn(4, '\t').collect();
        if parts.len() < 4 || parts[0] != "soft" {
            continue;
        }
        let index: usize = parts[1].parse().map_err(|_| format!("bad index: {line}"))?;
        let position: usize = parts[2]
            .parse()
            .map_err(|_| format!("bad position: {line}"))?;
        let bits =
            u64::from_str_radix(parts[3].trim(), 16).map_err(|_| format!("bad hex: {line}"))?;
        let value = Dyadic::of_binary64_bits(bits)
            .map_err(|e| e.to_string())?
            .value();
        soft.entry(position).or_default().push((index, value));
    }
    let rows = soft.len();
    let width = soft.values().next().map(Vec::len).unwrap_or(0);
    if rows == 0 || width != 768 {
        return Err(format!(
            "the soft tokens did not read: {rows} rows of {width}"
        ));
    }
    let mut words: Vec<u16> = Vec::with_capacity(rows * width);
    for position in 0..rows {
        let mut row = soft[&position].clone();
        row.sort_by_key(|(i, _)| *i);
        for (_, value) in row {
            let (word, _) = round_into_bfloat16(&value).map_err(|e| format!("{e:?}"))?;
            words.push(word);
        }
    }
    let widest_soft = soft
        .values()
        .flat_map(|row| row.iter().map(|(_, v)| num_traits::Signed::abs(v)))
        .max()
        .unwrap_or_else(|| Rat::from_integer(BigInt::from(1)));
    let widest_octaves = widest_soft.ceil().to_integer().bits() as u32;
    let vision_grain = ResidentGrain(62u32.saturating_sub(widest_octaves + 8).min(grain.0));
    let passage = FrontPassage::new(surface, vision_grain);
    let population = "model.embed_vision.embedding_projection.weight";
    let plan = holonic_engine::front_passage::MaterialPlan {
        maps: vec![(population.to_owned(), tower::HIDDEN, 768)],
        band_elements: 0,
        positions: 0,
    };
    let admission = passage
        .admit_material(&passage.predict_material(&plan))
        .map_err(|o| describe(&o))?;
    let (map_words, shape) = source.whole(population)?;
    let mut material = ResidentMaterial::empty();
    let mounted = readout
        .mount_bfloat16(&map_words, *shape.last().ok_or("shape")?)
        .map_err(|e| format!("{e:?}"))?;
    let masses = mounted.absolute_row_mass().map_err(|e| format!("{e:?}"))?;
    let widest = masses.iter().map(|m| m.unsigned_abs()).max().unwrap_or(0);
    let mass_octaves = i64::from(128 - widest.leading_zeros()) + i64::from(mounted.exponent());
    material.populations.insert(
        population.to_owned(),
        MountedPopulation {
            readout: mounted,
            mass_value_octaves: u32::try_from(mass_octaves.max(0)).unwrap_or(0),
        },
    );
    material.entering.insert(
        "vision soft tokens".to_owned(),
        EnteringRows { words, rows, width },
    );
    let mut regions = header_regions.clone();
    regions.insert(
        population.to_owned(),
        source.region(population, Some(resident_layer::digest_words(&map_words)))?,
    );
    let implementation = holonic_engine::source_occurrence::AuthenticatedText::read(
        resident_layer::IMPLEMENTATION,
        resident_layer::implementation_version().as_deref(),
    )
    .map_err(|e| e.to_string())?;
    let configuration = holonic_engine::source_occurrence::AuthenticatedText::read(
        &format!("{root}/config.json"),
        None,
    )
    .map_err(|e| e.to_string())?;
    let locator = format!("{root}/model.safetensors");
    let (octets, header_octets, header_sha256) =
        holonic_engine::source_occurrence::AuthenticatedContainer::read_header(&locator)
            .map_err(|e| e.to_string())?;
    let occurrence = SourceOccurrence {
        implementation,
        configuration,
        configuration_scope: vec!["vision_config".to_owned()],
        container: holonic_engine::source_occurrence::AuthenticatedContainer {
            identity: FileIdentity::at(&locator).ok(),
            locator,
            octets,
            header_octets,
            header_sha256,
            content_sha256: Some(content_sha256.to_owned()),
            regions,
        },
        assets: Vec::new(),
    };
    let eps_text = occurrence
        .configuration_span("rms_norm_eps")
        .ok_or("vision rms_norm_eps")?;
    let eps = Dyadic::of_binary64_bits(resident_layer::EPS_BITS).map_err(|e| e.to_string())?;
    let mut complex =
        PortedOperationComplex::new("vision soft tokens projected into the shared stream");
    let modality_port = complex.port("vision tower output, 768");
    let standing = complex.port("continuing standing, 2560");
    let mut realization = ResidentRealization::default();
    let enter = resident_layer::law(
        &mut complex,
        "vision soft tokens",
        OperationSpecies::Construction,
        vec![],
        vec![modality_port],
        None,
        vec![
            resident_layer::implementation(
                "Gemma4Model.get_image_features (vision_outputs.pooler_output = self.embed_vision(inputs_embeds=last_hidden_state))",
            ),
            resident_layer::configuration("hidden_size", "768"),
        ],
    )?;
    realization.bind(
        enter,
        Enter {
            population: "vision soft tokens".to_owned(),
            scale: Dyadic::ONE,
        },
    );
    let entered = if let Some((from, span)) = withdraw {
        let w = resident_layer::law(
            &mut complex,
            "soft-token columns withdrawn (intervention)",
            OperationSpecies::Quotient,
            vec![modality_port],
            vec![modality_port],
            None,
            vec![resident_layer::intervention(&format!(
                "matched sibling: vision soft-token columns {from}..{} withdrawn before the rebase; the caller's intervention, not a source law",
                from + span
            ))],
        )?;
        realization.bind(w, WithdrawColumns { from, span });
        resident_layer::bond(
            &mut complex,
            "soft tokens withdrawn",
            modality_port,
            enter,
            w,
            0,
        )?;
        w
    } else {
        enter
    };
    let rebase = resident_layer::law(
        &mut complex,
        "vision pre-projection rebase, no gain",
        OperationSpecies::Transport,
        vec![modality_port],
        vec![modality_port],
        None,
        vec![
            resident_layer::implementation(
                "Gemma4MultimodalEmbedder.forward (embs_normed = self.embedding_pre_projection_norm(inputs_embeds))",
            ),
            resident_layer::implementation(
                "Gemma4MultimodalEmbedder.__init__ (self.embedding_pre_projection_norm = Gemma4RMSNorm(self.multimodal_hidden_size, eps=self.eps, with_scale=False))",
            ),
            resident_layer::implementation(
                "Gemma4RMSNorm._norm (return hidden_states * torch.pow(mean_squared, -0.5))",
            ),
            resident_layer::configuration("rms_norm_eps", &eps_text),
            resident_layer::configuration("hidden_size", "768"),
        ],
    )?;
    realization.bind(
        rebase,
        RmsRebase {
            group: 768,
            gain: None,
            eps,
        },
    );
    resident_layer::bond(
        &mut complex,
        "soft tokens rebase",
        modality_port,
        entered,
        rebase,
        0,
    )?;
    let rebase = tower::seal(
        chart,
        &mut complex,
        &mut realization,
        rebase,
        modality_port,
        "vision rebase",
    )?;
    let projection = resident_layer::law(
        &mut complex,
        "vision projection",
        OperationSpecies::Transport,
        vec![modality_port],
        vec![standing],
        Some(population.to_owned()),
        vec![
            resident_layer::implementation(
                "Gemma4MultimodalEmbedder.forward (return self.embedding_projection(embs_normed))",
            ),
            resident_layer::shape(population, &[tower::HIDDEN, 768]),
        ],
    )?;
    realization.bind(
        projection,
        Contract {
            population: population.to_owned(),
        },
    );
    resident_layer::bond(
        &mut complex,
        "projects into the stream",
        modality_port,
        rebase,
        projection,
        0,
    )?;
    let names: Vec<(String, bool)> = conduct::names_of(&complex);
    let bound = passage
        .bind(
            &complex,
            &realization,
            &material,
            &occurrence,
            &DeedReceiver::unbounded(),
            Some(&admission),
            projection,
        )
        .map_err(|o| describe(&o))?;
    let returned = bound.launch(&surface.mode()).map_err(|o| describe(&o))?;
    bound.standing(&returned).map_err(|o| describe(&o))?;
    let native = bound.read_terminal(&returned).map_err(|o| describe(&o))?;
    Ok((native, rows, vision_grain, names))
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
        self.lines.push(format!(
            "  [{number:>2}] {tag}  {claim}\n        {evidence}"
        ));
        println!("  [{number:>2}] {tag}  {claim}\n        {evidence}");
    }
}

fn main() {
    let args = parse_args();
    println!("THE SOURCE IS DISSECTED BY INTERVENTION — {}", args.root);
    std::fs::create_dir_all(&args.out).expect("output directory");
    let mut verdicts = Verdicts {
        lines: Vec::new(),
        failed: 0,
    };
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

    let (text, tokens, pieces): (String, Vec<usize>, Vec<String>) = match (&args.text, &args.tokens)
    {
        (_, Some(list)) => (
            format!("{list:?}"),
            list.clone(),
            list.iter().map(|t| t.to_string()).collect(),
        ),
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

    let mut source = Source::open(&args.root).expect("source opens");
    let mut header_regions: BTreeMap<String, RegionIdentity> = BTreeMap::new();
    for name in source.container.names() {
        if let Ok(region) = source.region(name, None) {
            header_regions.insert(name.to_owned(), region);
        }
    }
    let digest_clock = Instant::now();
    let content_sha256 = holonic_engine::source_occurrence::AuthenticatedContainer::digest_whole(
        &format!("{}/model.safetensors", args.root),
    )
    .expect("digest");
    println!(
        "  container content sha256 {} ({:.1} s) · {} regions identified from the header",
        &content_sha256[..16],
        digest_clock.elapsed().as_secs_f64(),
        header_regions.len()
    );

    // ------------------------------------------------------------------------------------------
    // the fixed predecessor: the base deed
    // ------------------------------------------------------------------------------------------
    println!(
        "\nTHE BASE DEED (fixed predecessor) — {} tokens, chart {:?}, grain 2^-{}, {} series terms",
        tokens.len(),
        chart,
        grain.0,
        terms.0
    );
    let base = match conduct::conduct(
        surface,
        readout,
        &mut source,
        &args.root,
        &header_regions,
        &content_sha256,
        &tokens,
        grain,
        terms,
        chart,
        Site::Nowhere,
        &Intervention::None,
    ) {
        Ok(c) => c,
        Err(error) => {
            println!("REFUSED: the base deed did not stand — {error}");
            std::process::exit(6);
        }
    };
    println!(
        "  {} layers + final in {:.1} s · launches {} · widest charge {} octets · every lineage empty {} · every a-priori bound held {}",
        base.layers.len(),
        base.wall_s,
        base.deed_launches,
        base.peak_charged_octets,
        base.layers.iter().all(|l| l.lineage_empty),
        base.layers.iter().all(|l| l.a_priori_held)
    );
    let (base_plural, base_top) = order_face(&base.potential, tokens.len(), grain, 16);
    println!(
        "  order face at the last position: plural top {:?} · top-16 by lower bound {:?}",
        base_plural, base_top
    );
    // the base's own determinism: a second base deed must be bit-identical on every face
    let replay = match conduct::conduct(
        surface,
        readout,
        &mut source,
        &args.root,
        &header_regions,
        &content_sha256,
        &tokens,
        grain,
        terms,
        chart,
        Site::Nowhere,
        &Intervention::None,
    ) {
        Ok(c) => c,
        Err(error) => {
            println!("REFUSED: the replayed base deed did not stand — {error}");
            std::process::exit(6);
        }
    };
    let replay_family = compare_family(&base, &replay, grain);
    let replay_identical = replay_family.iter().all(|(_, c)| c.identical == c.entries);
    println!(
        "  the replayed base deed: every face bit-identical {replay_identical} ({} faces)",
        replay_family.len()
    );

    // ------------------------------------------------------------------------------------------
    // the siblings
    // ------------------------------------------------------------------------------------------
    let mut form: Vec<String> = Vec::new();
    form.push(format!("THE SOURCE IS DISSECTED BY INTERVENTION — {} · chart {:?} · grain 2^-{} · terms {} · device {} · mode {}", args.root, chart, grain.0, terms.0, surface.device_name(), surface.mode().kernel_content.as_deref().unwrap_or("?")));
    form.push(format!(
        "fixed input {text:?} tokens {tokens:?} pieces {pieces:?}"
    ));
    form.push(format!("base deed: {} layers + final · wall {:.1} s · launches {} · widest charge {} · plural top {:?} · top-16 {:?} · replay bit-identical {replay_identical}", base.layers.len(), base.wall_s, base.deed_launches, base.peak_charged_octets, base_plural, base_top));
    form.push(String::new());

    struct Outcome {
        taxon: Taxon,
        stood: bool,
        refusal: Option<String>,
        matched: bool,
        intervention_occurrences: usize,
        controls_held: Vec<(String, bool, String)>,
        first: Option<(Face, FaceComparison)>,
        faces_separated: usize,
        faces_total: usize,
        potential: Option<FaceComparison>,
        family: Vec<(Face, FaceComparison)>,
        order_moved: bool,
        plural: Vec<usize>,
        top: Vec<usize>,
        wall_s: f64,
    }
    let mut outcomes: Vec<Outcome> = Vec::new();
    for taxon in panel(tokens.len()) {
        if let Some(only) = &args.only {
            if !taxon.name.contains(only.as_str()) {
                continue;
            }
        }
        println!(
            "\nTHE MATCHED SIBLING — {} (dissects: {})",
            taxon.name, taxon.dissects
        );
        let sibling = conduct::conduct(
            surface,
            readout,
            &mut source,
            &args.root,
            &header_regions,
            &content_sha256,
            &tokens,
            grain,
            terms,
            chart,
            taxon.site,
            &taxon.intervention,
        );
        let mut outcome = Outcome {
            taxon,
            stood: false,
            refusal: None,
            matched: false,
            intervention_occurrences: 0,
            controls_held: Vec::new(),
            first: None,
            faces_separated: 0,
            faces_total: 0,
            potential: None,
            family: Vec::new(),
            order_moved: false,
            plural: Vec::new(),
            top: Vec::new(),
            wall_s: 0.0,
        };
        match sibling {
            Err(error) => {
                println!("  the sibling did not stand: {error}");
                outcome.refusal = Some(error);
            }
            Ok(sibling) => {
                outcome.stood = true;
                outcome.wall_s = sibling.wall_s;
                // matched: every layer's complex and the final's differ from the base's by exactly the intervention occurrences
                let mut all_matched = true;
                let mut occurrences = 0usize;
                // the intervention occurrences are the sibling's typed extras over the base — the
                // declared chart's quotient seals are typed as the caller's too, and both deeds carry them
                for (b, s) in base.layers.iter().zip(&sibling.layers) {
                    let (ok, extra, _) = matched(&b.operations, &s.operations);
                    all_matched &= ok;
                    occurrences += extra;
                }
                let (ok, extra, _) = matched(&base.final_operations, &sibling.final_operations);
                all_matched &= ok;
                occurrences += extra;
                outcome.matched = all_matched && occurrences >= 1;
                outcome.intervention_occurrences = occurrences;
                // the receiver family
                let family = compare_family(&base, &sibling, grain);
                outcome.faces_total = family.len();
                outcome.faces_separated = family.iter().filter(|(_, c)| c.separated > 0).count();
                outcome.first = family.iter().find(|(_, c)| c.separated > 0).cloned();
                outcome.potential = family
                    .iter()
                    .find(|(f, _)| *f == Face::Potential)
                    .map(|(_, c)| c.clone());
                outcome.family = family.clone();
                let (plural, top) = order_face(&sibling.potential, tokens.len(), grain, 16);
                outcome.order_moved = plural != base_plural || top != base_top;
                outcome.plural = plural;
                outcome.top = top;
                // the controls
                for control in &outcome.taxon.controls {
                    let (name, held, evidence) = match control {
                        Control::LayersBeforeIdentical(l) => {
                            let faces: Vec<&(Face, FaceComparison)> = family
                                .iter()
                                .filter(|(f, _)| f.layer().is_some_and(|x| x < *l))
                                .collect();
                            let held = faces.iter().all(|(_, c)| c.identical == c.entries);
                            let moved: Vec<String> = faces
                                .iter()
                                .filter(|(_, c)| c.identical != c.entries)
                                .map(|(f, c)| {
                                    format!(
                                        "{} ({} of {} identical)",
                                        f.name(),
                                        c.identical,
                                        c.entries
                                    )
                                })
                                .collect();
                            (
                                format!("every face of layers before {l} bit-identical"),
                                held,
                                if held {
                                    format!("{} faces, every entry identical", faces.len())
                                } else {
                                    format!("moved: {}", moved.join("; "))
                                },
                            )
                        }
                        Control::EveryLayerIdentical => {
                            let faces: Vec<&(Face, FaceComparison)> =
                                family.iter().filter(|(f, _)| f.layer().is_some()).collect();
                            let held = faces.iter().all(|(_, c)| c.identical == c.entries);
                            (
                                format!("every face of every layer bit-identical"),
                                held,
                                format!(
                                    "{} layer faces; final normed identical {}",
                                    faces.len(),
                                    family
                                        .iter()
                                        .find(|(f, _)| *f == Face::FinalNormed)
                                        .is_some_and(|(_, c)| c.identical == c.entries)
                                ),
                            )
                        }
                        Control::PositionZeroUnseparated(l) => {
                            let (b, s) = (&base.layers[*l], &sibling.layers[*l]);
                            let c = compare(
                                &b.terminal[..tower::HIDDEN],
                                &s.terminal[..tower::HIDDEN],
                                grain,
                                tower::HIDDEN,
                            );
                            (
                                format!("layer {l} return at position 0 not separated"),
                                c.separated == 0,
                                format!(
                                    "{} of {} separated, {} identical, widest shift {:.3e}",
                                    c.separated,
                                    c.entries,
                                    c.identical,
                                    rat_f64(&c.widest_shift)
                                ),
                            )
                        }
                        Control::PositionZeroIdentical(l) => {
                            let (b, s) = (&base.layers[*l], &sibling.layers[*l]);
                            let c = compare(
                                &b.terminal[..tower::HIDDEN],
                                &s.terminal[..tower::HIDDEN],
                                grain,
                                tower::HIDDEN,
                            );
                            (
                                format!("layer {l} return at position 0 bit-identical"),
                                c.identical == c.entries,
                                format!(
                                    "{} of {} identical, {} separated",
                                    c.identical, c.entries, c.separated
                                ),
                            )
                        }
                        Control::OrderFaceUnmoved => {
                            let (plural, top) =
                                order_face(&sibling.potential, tokens.len(), grain, 16);
                            let held = plural == base_plural && top == base_top;
                            (
                                "the order face at the output unmoved".to_owned(),
                                held,
                                format!(
                                    "plural {:?} top-16 {}",
                                    plural,
                                    if held {
                                        "identical".to_owned()
                                    } else {
                                        format!("{top:?}")
                                    }
                                ),
                            )
                        }
                    };
                    outcome.controls_held.push((name, held, evidence));
                }
                println!(
                    "  stood in {:.1} s · matched sibling {} ({} intervention occurrences) · {} of {} faces separated",
                    sibling.wall_s,
                    outcome.matched,
                    occurrences,
                    outcome.faces_separated,
                    outcome.faces_total
                );
                match &outcome.first {
                    Some((face, c)) => println!(
                        "  shortest separating history: {} — {} of {} separated at positions {:?}, widest gap {:.3e}, widest shift {:.3e}",
                        face.name(),
                        c.separated,
                        c.entries,
                        c.positions_separated,
                        rat_f64(&c.widest_gap),
                        rat_f64(&c.widest_shift)
                    ),
                    None => println!("  no face separated"),
                }
                if let Some(c) = &outcome.potential {
                    println!(
                        "  potential: {} of {} separated, widest gap {:.3e} · order face moved {} · plural {:?} · top-16 {:?}",
                        c.separated,
                        c.entries,
                        rat_f64(&c.widest_gap),
                        outcome.order_moved,
                        outcome.plural,
                        outcome.top
                    );
                }
                for (name, held, evidence) in &outcome.controls_held {
                    println!(
                        "  control: {name} — {} ({evidence})",
                        if *held { "HELD" } else { "MOVED" }
                    );
                }
                println!("  remaining ambiguity: {}", outcome.taxon.ambiguity);
            }
        }
        outcomes.push(outcome);
    }

    // ------------------------------------------------------------------------------------------
    // the vision projection sibling
    // ------------------------------------------------------------------------------------------
    let mut vision_line = String::from("vision: not run");
    let mut vision_ok: Option<(bool, bool)> = None;
    if args.vision {
        println!("\nTHE VISION PROJECTION — the soft-token span withdrawn");
        let base_v = vision_projection(
            surface,
            readout,
            &mut source,
            &args.root,
            &header_regions,
            &content_sha256,
            &args.python,
            &args.out,
            grain,
            chart,
            None,
        );
        let sib_v = vision_projection(
            surface,
            readout,
            &mut source,
            &args.root,
            &header_regions,
            &content_sha256,
            &args.python,
            &args.out,
            grain,
            chart,
            Some((0, 256)),
        );
        match (base_v, sib_v) {
            (Ok((bn, rows, vgrain, bnames)), Ok((sn, _, _, snames))) => {
                let c = compare(&bn, &sn, vgrain, tower::HIDDEN);
                let (m, extra, _) = matched(&bnames, &snames);
                vision_line = format!(
                    "vision: {rows} soft tokens × 768 → 2560 at grain 2^-{}: sibling matched {m} (+{extra} intervention occurrence); projected rows separated {} of {} entries at {} of {rows} positions, widest gap {:.3e}, {} identical",
                    vgrain.0,
                    c.separated,
                    c.entries,
                    c.positions_separated.len(),
                    rat_f64(&c.widest_gap),
                    c.identical
                );
                vision_ok = Some((m && extra == 1, c.separated > 0));
                println!("  {vision_line}");
            }
            (Err(e), _) | (_, Err(e)) => {
                vision_line = format!("vision: refused — {e}");
                println!("  {vision_line}");
            }
        }
    }

    // ------------------------------------------------------------------------------------------
    // the falsifiers
    // ------------------------------------------------------------------------------------------
    println!("\nTHE FALSIFIERS");
    let ran = outcomes.len();
    let stood = outcomes.iter().filter(|o| o.stood).count();
    verdicts.record(1, ran > 0 && stood == ran && base.layers.iter().all(|l| l.lineage_empty && l.a_priori_held), "the base deed and every sibling stand on the card: every lineage empty, every a-priori bound held, no sibling refused", &format!("base {} layers + final; {stood} of {ran} siblings stood{}", base.layers.len(), outcomes.iter().filter(|o| !o.stood).map(|o| format!("; {} refused: {}", o.taxon.name, o.refusal.clone().unwrap_or_default())).collect::<String>()));
    verdicts.record(2, replay_identical, "the fixed predecessor is fixed: a replayed base deed returns every face of the receiver family bit-identically", &format!("{} faces compared (3 per layer + final normed + potential), every entry identical {replay_identical}", replay_family.len()));
    let all_matched = outcomes.iter().filter(|o| o.stood).all(|o| o.matched);
    verdicts.record(3, ran > 0 && all_matched, "every sibling is matched: its complexes are the base's plus exactly its intervention occurrences, each named and typed as the caller's (a quotient or an intervention-only transport), none as source law", &outcomes.iter().filter(|o| o.stood).map(|o| format!("{}: matched {} (+{})", o.taxon.dissects, o.matched, o.intervention_occurrences)).collect::<Vec<_>>().join(" · "));
    let caused: Vec<&Outcome> = outcomes
        .iter()
        .filter(|o| o.stood && o.taxon.dissects != "normalization (gauge)")
        .collect();
    let caused_ok = caused.iter().all(|o| o.first.is_some());
    verdicts.record(4, !caused.is_empty() && caused_ok, "every non-gauge taxon causes a change the receiver family sees: at least one face separated (enclosures disjoint), with the shortest separating history located", &caused.iter().map(|o| match &o.first { Some((f, c)) => format!("{} → first at {} ({} of {}, positions {:?})", o.taxon.dissects, f.name(), c.separated, c.entries, c.positions_separated), None => format!("{} → NO FACE SEPARATED", o.taxon.dissects) }).collect::<Vec<_>>().join(" · "));
    let controls_all = outcomes
        .iter()
        .filter(|o| o.stood)
        .flat_map(|o| o.controls_held.iter())
        .collect::<Vec<_>>();
    let controls_held = controls_all.iter().filter(|(_, h, _)| *h).count();
    verdicts.record(5, !controls_all.is_empty() && controls_held == controls_all.len(), "every unchanged unrelated control holds: the faces each taxon predicts unmoved are measured unmoved (layers before the site bit-identical; position 0 under a single-key contact or equal rotation; every layer under the final-only intervention; the order face under the gauge)", &format!("{controls_held} of {} controls held{}", controls_all.len(), controls_all.iter().filter(|(_, h, _)| !*h).map(|(n, _, e)| format!("; MOVED: {n} — {e}")).collect::<String>()));
    let gauge = outcomes
        .iter()
        .find(|o| o.taxon.dissects == "normalization (gauge)");
    let after = outcomes
        .iter()
        .find(|o| o.taxon.dissects == "normalization (not a gauge)");
    let (gauge_pass, gauge_evidence) = match (gauge, after) {
        (Some(g), Some(a)) if g.stood && a.stood => {
            // domination: every face the gauge separates, the after-rebase sibling separates more widely
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
                            worst = Some(format!(
                                "{}: gauge gap {:.3e} vs after {:.3e}",
                                fg.name(),
                                rat_f64(&cg.widest_gap),
                                rat_f64(&ca.widest_gap)
                            ));
                        }
                    }
                }
            }
            let ratio = if widest_g > zero() {
                rat_f64(&widest_a) / rat_f64(&widest_g)
            } else {
                f64::INFINITY
            };
            let order_held = g
                .controls_held
                .iter()
                .filter(|(n, _, _)| n.starts_with("the order face"))
                .all(|(_, h, _)| *h);
            (
                dominated && order_held,
                format!(
                    "gauge (before the rebase): {faces_g} of {} faces separated, widest gap anywhere {:.3e}, order face {}; after the rebase: widest gap anywhere {:.3e} (×{ratio:.2e} wider), first separation at {}; domination at every separated face {dominated}{}",
                    g.family.len(),
                    rat_f64(&widest_g),
                    if order_held { "unmoved" } else { "MOVED" },
                    rat_f64(&widest_a),
                    a.first
                        .as_ref()
                        .map(|(f, c)| format!("{} ({} of {})", f.name(), c.separated, c.entries))
                        .unwrap_or_default(),
                    worst
                        .map(|w| format!("; first failure {w}"))
                        .unwrap_or_default()
                ),
            )
        }
        _ => (false, "gauge or after-rebase sibling not run".to_owned()),
    };
    verdicts.record(6, gauge_pass, "the normalization gauge: a rebase of the standing BEFORE the input rebase is quotiented away to the epsilon-and-rounding residue — every face it separates, the same rebase AFTER the input rebase separates more widely, and the order face is unmoved — while the exact receiver at the word's grain still sees the residue: tolerance is the receiver's aperture, not the gauge's", &gauge_evidence);
    let k22 = outcomes
        .iter()
        .find(|o| o.taxon.dissects == "K/V weights at the stored layer");
    let k24 = outcomes
        .iter()
        .find(|o| o.taxon.dissects == "KV reuse (the reuse, not the weights)");
    let reuse_separated = match (k22, k24) {
        (Some(a), Some(b)) => {
            a.stood
                && b.stood
                && a.first.as_ref().is_some_and(|(f, _)| f.layer() == Some(22))
                && b.first.as_ref().is_some_and(|(f, _)| f.layer() == Some(24))
                && b.controls_held.iter().all(|(_, h, _)| *h)
        }
        _ => false,
    };
    verdicts.record(7, reuse_separated, "the KV reuse is separated from the KV weights: withdrawing family 0 at the stored layer 22 first moves layer 22, while withdrawing the same family from the SHARED standings at layer 24 leaves layers 0–23 bit-identical and first moves layer 24", &format!("layer 22 sibling: {} · layer 24 sibling: {}", k22.and_then(|o| o.first.as_ref()).map(|(f, c)| format!("first at {} ({} of {})", f.name(), c.separated, c.entries)).unwrap_or_else(|| "not run".to_owned()), k24.and_then(|o| o.first.as_ref()).map(|(f, c)| format!("first at {} ({} of {})", f.name(), c.separated, c.entries)).unwrap_or_else(|| "not run".to_owned())));
    let chron: Vec<&Outcome> = outcomes
        .iter()
        .filter(|o| o.taxon.dissects.starts_with("chronology"))
        .collect();
    verdicts.record(8, !chron.is_empty() && chron.iter().all(|o| o.stood && o.controls_held.iter().all(|(_, h, _)| *h) && o.first.as_ref().is_some_and(|(f, _)| matches!(f, Face::Contact(1)))), "the chronology is a relative angle: replacing it by the identity or reversing the positions leaves position 0 unmoved (identical / unseparated) and first moves the layer-1 contact at positions ≥ 1", &chron.iter().map(|o| format!("{}: {}; first {}", o.taxon.dissects, o.controls_held.iter().map(|(n, h, e)| format!("{n} {} ({e})", if *h { "held" } else { "moved" })).collect::<Vec<_>>().join("; "), o.first.as_ref().map(|(f, c)| format!("{} positions {:?}", f.name(), c.positions_separated)).unwrap_or_default())).collect::<Vec<_>>().join(" · "));
    let final_only = outcomes.iter().find(|o| o.taxon.site == Site::Final);
    verdicts.record(9, final_only.is_some_and(|o| o.stood && o.controls_held.iter().all(|(_, h, _)| *h) && o.first.as_ref().is_some_and(|(f, _)| *f == Face::Potential)), "the output boundary: withdrawing a span of the final normed standing moves the potential alone — every layer face and the final normed standing bit-identical — and the order face is reported", &final_only.map(|o| format!("first at {}; order moved {}; plural {:?}", o.first.as_ref().map(|(f, _)| f.name()).unwrap_or_default(), o.order_moved, o.plural)).unwrap_or_default());
    let order: Vec<String> = outcomes
        .iter()
        .filter(|o| o.stood)
        .map(|o| {
            format!(
                "{} → {}",
                o.taxon.dissects,
                if o.order_moved { "moved" } else { "unmoved" }
            )
        })
        .collect();
    verdicts.record(10, outcomes.iter().any(|o| o.stood && o.order_moved) && outcomes.iter().any(|o| o.stood && !o.order_moved), "the order face at the output is a coarser receiver than the sections: some taxa move it and some do not, while every non-gauge taxon moves a section — a separation invisible to the top-16 is not absent", &order.join(" · "));
    verdicts.record(11, vision_ok.is_some_and(|(m, s)| m && s), "the bounded non-text projection is dissected the same way: withdrawing a span of the soft tokens before the rebase is one typed intervention occurrence and separates the projected rows", &vision_line);
    let shortest: Vec<String> = outcomes
        .iter()
        .filter(|o| o.stood)
        .map(|o| match &o.first {
            Some((f, c)) => format!(
                "{} → {} at positions {:?}",
                o.taxon.dissects,
                f.name(),
                c.positions_separated
            ),
            None => format!("{} → none", o.taxon.dissects),
        })
        .collect();
    verdicts.record(12, outcomes.iter().filter(|o| o.stood).all(|o| o.first.is_none() || o.first.as_ref().is_some_and(|(f, _)| match o.taxon.site { Site::Layer(l) => f.layer().is_none_or(|x| x >= l), Site::Final => *f == Face::Potential, _ => true })), "every shortest separating history begins at or after its site: no intervention reaches its own past, and the first separating face names where the taxon's change enters the receiver family", &shortest.join(" · "));

    // ------------------------------------------------------------------------------------------
    // the artifact
    // ------------------------------------------------------------------------------------------
    for o in &outcomes {
        form.push(format!(
            "TAXON {} — dissects {} — site {:?} — intervention {:?}",
            o.taxon.name, o.taxon.dissects, o.taxon.site, o.taxon.intervention
        ));
        form.push(format!(
            "  stood {} · wall {:.1} s · matched sibling {} · intervention occurrences {}{}",
            o.stood,
            o.wall_s,
            o.matched,
            o.intervention_occurrences,
            o.refusal
                .as_ref()
                .map(|r| format!(" · refusal {r}"))
                .unwrap_or_default()
        ));
        form.push(format!(
            "  faces separated {} of {}",
            o.faces_separated, o.faces_total
        ));
        match &o.first {
            Some((f, c)) => form.push(format!("  shortest separating history: {} — {} of {} separated at positions {:?}, widest gap {:.6e}, widest midpoint shift {:.6e}, {} identical", f.name(), c.separated, c.entries, c.positions_separated, rat_f64(&c.widest_gap), rat_f64(&c.widest_shift), c.identical)),
            None => form.push("  shortest separating history: none — no face separated".to_owned()),
        }
        if let Some(c) = &o.potential {
            form.push(format!("  potential: {} of {} separated, widest gap {:.6e}, widest shift {:.6e} · order face moved {} · plural {:?} · top-16 {:?}", c.separated, c.entries, rat_f64(&c.widest_gap), rat_f64(&c.widest_shift), o.order_moved, o.plural, o.top));
        }
        for (name, held, evidence) in &o.controls_held {
            form.push(format!(
                "  control {} — {name}: {evidence}",
                if *held { "HELD" } else { "MOVED" }
            ));
        }
        form.push(format!("  remaining ambiguity: {}", o.taxon.ambiguity));
        form.push(String::new());
    }
    form.push(vision_line.clone());
    form.push(String::new());
    form.push("THE FALSIFIERS".to_owned());
    form.extend(verdicts.lines.iter().cloned());
    let path = format!(
        "{}/dissection-{}-tokens-grain-{}-terms-{}.form",
        args.out,
        tokens.len(),
        grain.0,
        terms.0
    );
    let mut file = std::fs::File::create(&path).expect("artifact");
    for line in &form {
        writeln!(file, "{line}").expect("write");
    }
    println!("\n  artifact {path}");
    println!(
        "\n{} of {} falsifiers PASS; {} OPEN",
        verdicts.lines.len() - verdicts.failed,
        verdicts.lines.len(),
        verdicts.failed
    );
    if verdicts.failed > 0 {
        std::process::exit(1);
    }
}

fn _unused(_: EventId) {}
