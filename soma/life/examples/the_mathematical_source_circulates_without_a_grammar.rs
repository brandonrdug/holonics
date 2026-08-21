//! M0 — heterogeneous mathematical source circulation without a mathematical grammar.
//!
//! The exterior fixture builder has already produced independently addressed PDF-text, SVG and
//! PNG faces from the fixed harmonic calibration and pages 5/10 of Ge's arXiv source. This driver
//! reads those exact bytes, decodes only their exterior container syntax, and hands placed
//! occurrences or exact pixels to `life::mathematical_source`. It never supplies a contact and it
//! never interprets a mathematical spelling.

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

use holonic_engine::image::{ExactRaster, ExactRgb, ImageExtent};
use life::mathematical_source::{
    admit_raster_components, compare_presentations, correspond, correspondence_demand,
    derive_layout, derive_raster_fiber, derive_serial_layout, exact_decimal, layout_demand,
    raster_component_admission_demand, raster_demand, serial_layout_demand, ArtifactIdentity,
    ExactBox, ExactExtent, PlacedCarrier, Rat, SourceLayoutTestimony, SourceLayoutWorkCover,
    TestimonyChart,
};
use num_bigint::BigInt;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};

const OUT: &str = "output/m0_mathematical_source_circulation";
const DEFAULT_OUT: &str =
    "output/m0_mathematical_source_circulation/m0-mathematical-source-circulation.json";
const FACE_ROOT: &str = "output/m0_mathematical_source_circulation/faces";
const NATURAL_SOURCE: &str = "tmp/pdfs/2608.13553-heat-kernel-geometry.pdf";
const NATURAL_SHA256: &str = "9518ea5939a53650f82d7b016e017df5e7cacfc1d8728e0ac2aaa25bf68fc4e5";
const DECIMAL_DIGIT_APERTURE: usize = 32;

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn integer(value: impl Into<BigInt>) -> Rat {
    Rat::from_integer(value.into())
}

fn digest(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect()
}

fn read(root: &Path, relative: &str) -> Result<Vec<u8>, String> {
    fs::read(root.join(relative)).map_err(|error| format!("read {relative}: {error}"))
}

fn attribute<'a>(tag: &'a str, name: &str) -> Option<&'a str> {
    let bytes = tag.as_bytes();
    let needle = name.as_bytes();
    let mut at = 0usize;
    while at + needle.len() <= bytes.len() {
        let found = tag[at..].find(name)? + at;
        let before_ok = found == 0
            || bytes
                .get(found.wrapping_sub(1))
                .is_some_and(|octet| octet.is_ascii_whitespace() || *octet == b'<');
        let after = found + needle.len();
        if before_ok && bytes.get(after) == Some(&b'=') {
            let quote = *bytes.get(after + 1)?;
            if quote != b'\'' && quote != b'"' {
                at = after + 1;
                continue;
            }
            let start = after + 2;
            let end = bytes[start..].iter().position(|octet| *octet == quote)? + start;
            return tag.get(start..end);
        }
        at = after.max(at + 1);
    }
    None
}

fn exact_attribute(tag: &str, name: &str) -> Result<Rat, String> {
    exact_decimal(
        attribute(tag, name).ok_or_else(|| format!("attribute {name} absent"))?,
        DECIMAL_DIGIT_APERTURE,
    )
    .map_err(|error| format!("exact attribute {name}: {error}"))
}

fn admitted_layout(
    chart: TestimonyChart,
    artifact: ArtifactIdentity,
    extent: ExactExtent,
    occurrences: Vec<PlacedCarrier>,
) -> Result<SourceLayoutTestimony, String> {
    let demand = layout_demand(&occurrences).map_err(|error| error.to_string())?;
    derive_layout(
        chart,
        artifact,
        extent,
        occurrences,
        &SourceLayoutWorkCover::exactly(&demand),
    )
    .map_err(|error| error.to_string())
}

fn co_testimony(
    left: &SourceLayoutTestimony,
    right: &SourceLayoutTestimony,
) -> Result<life::mathematical_source::CoTestimonyFiber, String> {
    let demand = correspondence_demand(left, right).map_err(|error| error.to_string())?;
    correspond(left, right, &SourceLayoutWorkCover::exactly(&demand))
        .map_err(|error| error.to_string())
}

fn admitted_serial_layout(
    chart: TestimonyChart,
    artifact: ArtifactIdentity,
    extent: ExactExtent,
    occurrences: Vec<PlacedCarrier>,
) -> Result<SourceLayoutTestimony, String> {
    let demand = serial_layout_demand(&occurrences).map_err(|error| error.to_string())?;
    derive_serial_layout(
        chart,
        artifact,
        extent,
        occurrences,
        &SourceLayoutWorkCover::exactly(&demand),
    )
    .map_err(|error| error.to_string())
}

fn tag_name(tag: &str) -> &str {
    tag.trim_start_matches(['<', '/', '?', '!'])
        .split(|character: char| {
            character.is_ascii_whitespace() || character == '>' || character == '/'
        })
        .next()
        .unwrap_or_default()
}

fn xml_tags(text: &str) -> Result<Vec<&str>, String> {
    let bytes = text.as_bytes();
    let mut tags = Vec::new();
    let mut at = 0usize;
    while let Some(offset) = text[at..].find('<') {
        let start = at + offset;
        let mut cursor = start + 1;
        let mut quote = None;
        while cursor < bytes.len() {
            let octet = bytes[cursor];
            if let Some(open) = quote {
                if octet == open {
                    quote = None;
                }
            } else if octet == b'\'' || octet == b'"' {
                quote = Some(octet);
            } else if octet == b'>' {
                tags.push(
                    text.get(start..=cursor)
                        .ok_or_else(|| "XML tag boundary is not UTF-8".to_owned())?,
                );
                at = cursor + 1;
                break;
            }
            cursor += 1;
        }
        if cursor == bytes.len() {
            return Err("unterminated XML tag".to_owned());
        }
    }
    Ok(tags)
}

fn bbox_layout(
    root: &Path,
    run: &str,
    relative: &str,
    chart: TestimonyChart,
) -> Result<SourceLayoutTestimony, String> {
    let bytes = read(root, relative)?;
    let text = std::str::from_utf8(&bytes).map_err(|error| format!("{relative}: {error}"))?;
    let page_start = text
        .find("<page ")
        .ok_or_else(|| format!("{relative}: page absent"))?;
    let page_end = text[page_start..]
        .find('>')
        .map(|offset| page_start + offset + 1)
        .ok_or_else(|| format!("{relative}: page tag open"))?;
    let page = &text[page_start..page_end];
    let extent = ExactExtent::new(
        exact_attribute(page, "width")?,
        exact_attribute(page, "height")?,
    )
    .map_err(|error| format!("{relative}: {error}"))?;
    let artifact = ArtifactIdentity::of_bytes(format!("{run}:{relative}"), relative, &bytes)
        .map_err(|error| error.to_string())?;
    let mut occurrences = Vec::new();
    let mut cursor = 0usize;
    while let Some(offset) = text[cursor..].find("<word ") {
        let start = cursor + offset;
        let open_end = text[start..]
            .find('>')
            .map(|found| start + found)
            .ok_or_else(|| format!("{relative}: word tag open"))?;
        let close = text[open_end + 1..]
            .find("</word>")
            .map(|found| open_end + 1 + found)
            .ok_or_else(|| format!("{relative}: word tag close"))?;
        let tag = &text[start..=open_end];
        let payload = text.as_bytes()[open_end + 1..close].to_vec();
        let ordinal = u64::try_from(occurrences.len()).map_err(|_| "word extent".to_owned())?;
        occurrences.push(
            PlacedCarrier::new(
                &artifact,
                ordinal,
                payload,
                Some(ordinal),
                ExactBox::new(
                    exact_attribute(tag, "xMin")?,
                    exact_attribute(tag, "yMin")?,
                    exact_attribute(tag, "xMax")?,
                    exact_attribute(tag, "yMax")?,
                )
                .map_err(|error| error.to_string())?,
            )
            .map_err(|error| error.to_string())?,
        );
        cursor = close + "</word>".len();
    }
    admitted_layout(chart, artifact, extent, occurrences)
}

#[derive(Clone)]
struct Matrix {
    a: Rat,
    b: Rat,
    c: Rat,
    d: Rat,
    e: Rat,
    f: Rat,
}

impl Matrix {
    fn identity() -> Self {
        Self {
            a: integer(1),
            b: integer(0),
            c: integer(0),
            d: integer(1),
            e: integer(0),
            f: integer(0),
        }
    }

    fn then(&self, local: &Self) -> Self {
        Self {
            a: &self.a * &local.a + &self.c * &local.b,
            b: &self.b * &local.a + &self.d * &local.b,
            c: &self.a * &local.c + &self.c * &local.d,
            d: &self.b * &local.c + &self.d * &local.d,
            e: &self.a * &local.e + &self.c * &local.f + &self.e,
            f: &self.b * &local.e + &self.d * &local.f + &self.f,
        }
    }

    fn point(&self, x: &Rat, y: &Rat) -> (Rat, Rat) {
        (
            &self.a * x + &self.c * y + &self.e,
            &self.b * x + &self.d * y + &self.f,
        )
    }
}

fn transform(tag: &str) -> Result<Matrix, String> {
    let Some(source) = attribute(tag, "transform") else {
        return Ok(Matrix::identity());
    };
    let (kind, body) = source
        .split_once('(')
        .ok_or_else(|| format!("transform open: {source}"))?;
    let body = body
        .strip_suffix(')')
        .ok_or_else(|| format!("transform close: {source}"))?;
    let values = body
        .split(|character: char| character.is_ascii_whitespace() || character == ',')
        .filter(|part| !part.is_empty())
        .map(|part| exact_decimal(part, DECIMAL_DIGIT_APERTURE).map_err(|error| error.to_string()))
        .collect::<Result<Vec<_>, _>>()?;
    match (kind.trim(), values.as_slice()) {
        ("matrix", [a, b, c, d, e, f]) => Ok(Matrix {
            a: a.clone(),
            b: b.clone(),
            c: c.clone(),
            d: d.clone(),
            e: e.clone(),
            f: f.clone(),
        }),
        ("translate", [x]) => Ok(Matrix {
            e: x.clone(),
            ..Matrix::identity()
        }),
        ("translate", [x, y]) => Ok(Matrix {
            e: x.clone(),
            f: y.clone(),
            ..Matrix::identity()
        }),
        ("scale", [scale]) => Ok(Matrix {
            a: scale.clone(),
            d: scale.clone(),
            ..Matrix::identity()
        }),
        ("scale", [x, y]) => Ok(Matrix {
            a: x.clone(),
            d: y.clone(),
            ..Matrix::identity()
        }),
        _ => Err(format!("unsupported exterior transform: {source}")),
    }
}

fn first_path_point(source: &str) -> Option<(Rat, Rat)> {
    let at = source.find(['M', 'm'])? + 1;
    let mut values = Vec::new();
    let bytes = source.as_bytes();
    let mut cursor = at;
    while cursor < bytes.len() && values.len() < 2 {
        while cursor < bytes.len()
            && !bytes[cursor].is_ascii_digit()
            && bytes[cursor] != b'-'
            && bytes[cursor] != b'+'
            && bytes[cursor] != b'.'
        {
            cursor += 1;
        }
        let start = cursor;
        if cursor < bytes.len() && (bytes[cursor] == b'-' || bytes[cursor] == b'+') {
            cursor += 1;
        }
        while cursor < bytes.len() && (bytes[cursor].is_ascii_digit() || bytes[cursor] == b'.') {
            cursor += 1;
        }
        if start < cursor {
            values.push(exact_decimal(&source[start..cursor], DECIMAL_DIGIT_APERTURE).ok()?);
        }
    }
    (values.len() == 2).then(|| (values.remove(0), values.remove(0)))
}

fn svg_local_point(tag: &str) -> Result<Option<(Rat, Rat)>, String> {
    let named = match tag_name(tag) {
        "use" | "text" => Some(("x", "y")),
        "circle" => Some(("cx", "cy")),
        _ => None,
    };
    if let Some((x, y)) = named {
        return match (attribute(tag, x), attribute(tag, y)) {
            (Some(x), Some(y)) => Ok(Some((
                exact_decimal(x, DECIMAL_DIGIT_APERTURE).map_err(|error| error.to_string())?,
                exact_decimal(y, DECIMAL_DIGIT_APERTURE).map_err(|error| error.to_string())?,
            ))),
            _ => Ok(None),
        };
    }
    if tag_name(tag) == "path" {
        return Ok(attribute(tag, "d").and_then(first_path_point));
    }
    if tag_name(tag) == "image" {
        return Ok(Some((integer(0), integer(0))));
    }
    Ok(None)
}

fn svg_layout(root: &Path, run: &str, relative: &str) -> Result<SourceLayoutTestimony, String> {
    let bytes = read(root, relative)?;
    let text = std::str::from_utf8(&bytes).map_err(|error| format!("{relative}: {error}"))?;
    let tags = xml_tags(text)?;
    let svg = tags
        .iter()
        .find(|tag| tag_name(tag) == "svg")
        .ok_or_else(|| format!("{relative}: svg root absent"))?;
    let view_box =
        attribute(svg, "viewBox").ok_or_else(|| format!("{relative}: viewBox absent"))?;
    let view = view_box
        .split_ascii_whitespace()
        .map(|part| exact_decimal(part, DECIMAL_DIGIT_APERTURE).map_err(|error| error.to_string()))
        .collect::<Result<Vec<_>, _>>()?;
    if view.len() != 4 {
        return Err(format!("{relative}: viewBox extent"));
    }
    let extent =
        ExactExtent::new(view[2].clone(), view[3].clone()).map_err(|error| error.to_string())?;
    let artifact = ArtifactIdentity::of_bytes(format!("{run}:{relative}"), relative, &bytes)
        .map_err(|error| error.to_string())?;
    let mut matrix = Matrix::identity();
    let mut defs_depth = 0usize;
    let mut stack = Vec::<(String, Matrix, usize)>::new();
    let mut occurrences = Vec::new();
    for tag in tags {
        let name = tag_name(tag);
        if tag.starts_with("</") {
            let Some((opened, previous_matrix, previous_defs)) = stack.pop() else {
                return Err(format!("{relative}: close without open {name}"));
            };
            if opened != name {
                return Err(format!("{relative}: closed {name} over {opened}"));
            }
            matrix = previous_matrix;
            defs_depth = previous_defs;
            continue;
        }
        if tag.starts_with("<?") || tag.starts_with("<!") {
            continue;
        }
        let self_closing = tag.trim_end_matches('>').trim_end().ends_with('/');
        let previous_matrix = matrix.clone();
        let previous_defs = defs_depth;
        if name == "defs" {
            defs_depth += 1;
        }
        matrix = matrix.then(&transform(tag)?);
        if defs_depth == 0 {
            if let Some((x, y)) = svg_local_point(tag)? {
                let (placed_x, placed_y) = matrix.point(&x, &y);
                if placed_x < integer(0)
                    || placed_y < integer(0)
                    || &placed_x >= extent.width()
                    || &placed_y >= extent.height()
                {
                    if !self_closing {
                        stack.push((name.to_owned(), previous_matrix, previous_defs));
                    } else {
                        matrix = previous_matrix;
                        defs_depth = previous_defs;
                    }
                    continue;
                }
                let right = (&placed_x + integer(1)).min(extent.width().clone());
                let bottom = (&placed_y + integer(1)).min(extent.height().clone());
                let ordinal = u64::try_from(occurrences.len())
                    .map_err(|_| format!("{relative}: occurrence extent"))?;
                occurrences.push(
                    PlacedCarrier::new(
                        &artifact,
                        ordinal,
                        tag.as_bytes().to_vec(),
                        Some(ordinal),
                        ExactBox::new(placed_x.clone(), placed_y.clone(), right, bottom)
                            .map_err(|error| error.to_string())?,
                    )
                    .map_err(|error| error.to_string())?,
                );
            }
        }
        if self_closing {
            matrix = previous_matrix;
            defs_depth = previous_defs;
        } else {
            stack.push((name.to_owned(), previous_matrix, previous_defs));
        }
    }
    if !stack.is_empty() {
        return Err(format!("{relative}: unclosed XML elements"));
    }
    admitted_serial_layout(TestimonyChart::Vector, artifact, extent, occurrences)
}

fn atlas_layout(root: &Path, run: &str, relative: &str) -> Result<SourceLayoutTestimony, String> {
    let bytes = read(root, relative)?;
    let artifact = ArtifactIdentity::of_bytes(format!("{run}:{relative}"), relative, &bytes)
        .map_err(|error| error.to_string())?;
    let lines = bytes
        .split(|octet| *octet == b'\n')
        .filter(|line| !line.is_empty())
        .collect::<Vec<_>>();
    let width = lines.iter().map(|line| line.len()).max().unwrap_or(0);
    let extent = ExactExtent::new(integer(width), integer(lines.len()))
        .map_err(|error| error.to_string())?;
    let mut occurrences = Vec::with_capacity(lines.len());
    for (at, line) in lines.into_iter().enumerate() {
        let ordinal = u64::try_from(at).map_err(|_| format!("{relative}: line extent"))?;
        occurrences.push(
            PlacedCarrier::new(
                &artifact,
                ordinal,
                line.to_vec(),
                Some(ordinal),
                ExactBox::new(
                    integer(0),
                    integer(at),
                    integer(line.len()),
                    integer(at + 1),
                )
                .map_err(|error| error.to_string())?,
            )
            .map_err(|error| error.to_string())?,
        );
    }
    admitted_layout(TestimonyChart::ExteriorAtlas, artifact, extent, occurrences)
}

fn decoded_raster(bytes: &[u8]) -> Result<ExactRaster, String> {
    let decoded = image::load_from_memory(bytes)
        .map_err(|error| format!("PNG decode: {error}"))?
        .to_rgb8();
    let extent = ImageExtent {
        width: decoded.width(),
        height: decoded.height(),
    };
    let samples = decoded
        .pixels()
        .map(|pixel| ExactRgb {
            red: pixel.0[0],
            green: pixel.0[1],
            blue: pixel.0[2],
        })
        .collect();
    ExactRaster::new(extent, samples).map_err(|error| error.to_string())
}

fn raster_extent(raster: &ExactRaster) -> Result<ExactExtent, String> {
    ExactExtent::new(integer(raster.extent.width), integer(raster.extent.height))
        .map_err(|error| error.to_string())
}

struct RasterReturn {
    extent: ExactExtent,
    fiber: life::mathematical_source::RasterSourceFiber,
    four_testimony: SourceLayoutTestimony,
    eight_testimony: SourceLayoutTestimony,
}

fn raster_return(root: &Path, run: &str, name: &str, path: &str) -> Result<RasterReturn, String> {
    let encoded = read(root, path)?;
    let raster = decoded_raster(&encoded)?;
    let background = raster
        .sample(0, 0)
        .ok_or_else(|| format!("{path}: top-left background sample absent"))?;
    let extent = raster_extent(&raster)?;
    let demand = raster_demand(&raster).map_err(|error| error.to_string())?;
    let fiber = derive_raster_fiber(
        format!("{run}:raster:{name}"),
        path,
        &encoded,
        &raster,
        background,
        &SourceLayoutWorkCover::exactly(&demand),
    )
    .map_err(|error| error.to_string())?;
    let four_demand = raster_component_admission_demand(&fiber.four_connected)
        .map_err(|error| error.to_string())?;
    let four_testimony = admit_raster_components(
        &fiber.four_connected,
        extent.clone(),
        &SourceLayoutWorkCover::exactly(&four_demand),
    )
    .map_err(|error| error.to_string())?;
    let eight_demand = raster_component_admission_demand(&fiber.eight_connected)
        .map_err(|error| error.to_string())?;
    let eight_testimony = admit_raster_components(
        &fiber.eight_connected,
        extent.clone(),
        &SourceLayoutWorkCover::exactly(&eight_demand),
    )
    .map_err(|error| error.to_string())?;
    Ok(RasterReturn {
        extent,
        fiber,
        four_testimony,
        eight_testimony,
    })
}

fn layout_value(testimony: &SourceLayoutTestimony) -> Value {
    let complex = testimony.complex.as_ref().map(|complex| {
        json!({
            "sites": complex.sites().len(),
            "bonds": complex.bonds().len(),
            "compounds": complex.compounds().len(),
            "ingress": complex.ingress(),
            "body_validation": complex.validate_with_body(false).map(|_| "held").map_err(|error| format!("{error:?}")),
        })
    });
    json!({
        "schema": testimony.schema,
        "chart": testimony.chart,
        "artifact": testimony.artifact,
        "extent": testimony.extent,
        "occurrences": testimony.occurrences.iter().map(occurrence_value).collect::<Vec<_>>(),
        "contacts": testimony.contacts,
        "complex": complex,
        "work": testimony.work,
        "outside_declared_artifact_open": testimony.outside_declared_artifact_open,
    })
}

fn occurrence_value(occurrence: &PlacedCarrier) -> Value {
    json!({
        "address": occurrence.address,
        "payload_sha256": occurrence.payload_sha256,
        "payload_octets": occurrence.payload_octets,
        "serial_ordinal": occurrence.serial_ordinal,
        "bounds": occurrence.bounds,
    })
}

fn raster_component_value(component: &life::mathematical_source::RasterComponentFiber) -> Value {
    json!({
        "artifact": component.artifact,
        "connectivity": component.connectivity,
        "occurrences": component.occurrences.iter().map(occurrence_value).collect::<Vec<_>>(),
    })
}

fn raster_fiber_value(fiber: &life::mathematical_source::RasterSourceFiber) -> Value {
    json!({
        "artifact": fiber.artifact,
        "background": fiber.background,
        "four_connected": raster_component_value(&fiber.four_connected),
        "eight_connected": raster_component_value(&fiber.eight_connected),
        "work": fiber.work,
        "omitted_background_alternatives_open": fiber.omitted_background_alternatives_open,
    })
}

fn serial_difference_count(left: &SourceLayoutTestimony, right: &SourceLayoutTestimony) -> usize {
    let serial = |testimony: &SourceLayoutTestimony| {
        let mut population = testimony
            .occurrences
            .iter()
            .filter_map(|occurrence| {
                occurrence
                    .serial_ordinal
                    .map(|ordinal| (ordinal, occurrence.payload_sha256.clone()))
            })
            .collect::<Vec<_>>();
        population.sort_unstable();
        population
    };
    let left = serial(left);
    let right = serial(right);
    left.iter()
        .zip(&right)
        .filter(|(left, right)| left != right)
        .count()
        + left.len().abs_diff(right.len())
}

fn manifest_holds(root: &Path, paths: &[&str]) -> Result<Value, String> {
    let manifest_path = format!("{OUT}/face-identities.sha256");
    let text = String::from_utf8(read(root, &manifest_path)?)
        .map_err(|error| format!("identity ledger UTF-8: {error}"))?;
    let rows = text
        .lines()
        .filter_map(|line| line.split_once("  "))
        .map(|(hash, path)| (path.to_owned(), hash.to_owned()))
        .collect::<BTreeMap<_, _>>();
    let mut returned = Vec::new();
    for path in paths {
        let bytes = read(root, path)?;
        let observed = digest(&bytes);
        let declared = rows
            .get(*path)
            .ok_or_else(|| format!("identity ledger omitted {path}"))?;
        if declared != &observed {
            return Err(format!(
                "identity ledger moved {path}: {declared} != {observed}"
            ));
        }
        returned.push(json!({"path": path, "sha256": observed, "octets": bytes.len()}));
    }
    Ok(json!(returned))
}

fn main() -> Result<(), String> {
    let root = root();
    let run = format!(
        "m0-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map_err(|error| error.to_string())?
            .as_nanos()
    );
    let natural_bytes = read(&root, NATURAL_SOURCE)?;
    let natural_identity = ArtifactIdentity::of_bytes(
        format!("{run}:natural-source"),
        NATURAL_SOURCE,
        &natural_bytes,
    )
    .map_err(|error| error.to_string())?;
    if natural_identity.sha256 != NATURAL_SHA256 {
        return Err(format!("natural source moved: {}", natural_identity.sha256));
    }

    let baseline_text = bbox_layout(
        &root,
        &run,
        &format!("{FACE_ROOT}/synthetic/harmonic-baseline-pdf-bbox.html"),
        TestimonyChart::BornDigital,
    )?;
    let reflow_text = bbox_layout(
        &root,
        &run,
        &format!("{FACE_ROOT}/synthetic/harmonic-reflow-control-bbox.html"),
        TestimonyChart::BornDigital,
    )?;
    let perturb_text = bbox_layout(
        &root,
        &run,
        &format!("{FACE_ROOT}/synthetic/harmonic-perturbed-control-bbox.html"),
        TestimonyChart::BornDigital,
    )?;
    let baseline_vector = svg_layout(
        &root,
        &run,
        &format!("{FACE_ROOT}/synthetic/harmonic-baseline-pdf.svg"),
    )?;
    let diagram_vector = svg_layout(
        &root,
        &run,
        "research/fixtures/m0_mathematical_source_circulation/harmonic-conjugation.svg",
    )?;

    let page5_text = bbox_layout(
        &root,
        &run,
        &format!("{FACE_ROOT}/natural/heat-fisher-page-5-bbox.html"),
        TestimonyChart::BornDigital,
    )?;
    let page10_text = bbox_layout(
        &root,
        &run,
        &format!("{FACE_ROOT}/natural/heat-fisher-page-10-bbox.html"),
        TestimonyChart::BornDigital,
    )?;
    let page5_vector = svg_layout(
        &root,
        &run,
        &format!("{FACE_ROOT}/natural/heat-fisher-page-5.svg"),
    )?;
    let page10_vector = svg_layout(
        &root,
        &run,
        &format!("{FACE_ROOT}/natural/heat-fisher-page-10.svg"),
    )?;

    let equations = atlas_layout(&root, &run, "research/equation-atlas/equations.jsonl")?;
    let relations = atlas_layout(&root, &run, "research/equation-atlas/relations.jsonl")?;

    let raster_paths = [
        (
            "synthetic_baseline",
            format!("{FACE_ROOT}/synthetic/harmonic-baseline-pdf.png"),
        ),
        (
            "synthetic_diagram",
            format!("{FACE_ROOT}/synthetic/harmonic-conjugation-diagram.png"),
        ),
        (
            "natural_page_5",
            format!("{FACE_ROOT}/natural/heat-fisher-page-5.png"),
        ),
        (
            "natural_page_10",
            format!("{FACE_ROOT}/natural/heat-fisher-page-10.png"),
        ),
    ];
    let mut raster_returns = BTreeMap::new();
    for (name, path) in &raster_paths {
        raster_returns.insert((*name).to_owned(), raster_return(&root, &run, name, path)?);
    }

    let baseline_reflow = compare_presentations(&baseline_text, &reflow_text);
    let baseline_perturbation = compare_presentations(&baseline_text, &perturb_text);
    if !baseline_reflow.serial_payload_face_equal {
        return Err("harmless reflow moved the serial payload face".to_owned());
    }
    if baseline_reflow.departed_contacts.is_empty() && baseline_reflow.arrived_contacts.is_empty() {
        return Err("harmless reflow failed to move any layout incidence".to_owned());
    }
    if baseline_perturbation.serial_payload_face_equal
        || baseline_perturbation.first_payload_separator.is_none()
        || serial_difference_count(&baseline_text, &perturb_text) != 1
    {
        return Err("the relation-hand perturbation was not one localized separator".to_owned());
    }

    let baseline_raster = &raster_returns["synthetic_baseline"];
    let diagram_raster = &raster_returns["synthetic_diagram"];
    let page5_raster = &raster_returns["natural_page_5"];
    let page10_raster = &raster_returns["natural_page_10"];

    let baseline_text_vector = co_testimony(&baseline_text, &baseline_vector)?;
    let page5_text_vector = co_testimony(&page5_text, &page5_vector)?;
    let page10_text_vector = co_testimony(&page10_text, &page10_vector)?;
    if baseline_text_vector.candidates.is_empty()
        || page5_text_vector.candidates.is_empty()
        || page10_text_vector.candidates.is_empty()
    {
        return Err("a born-digital/vector co-testimony returned no overlap candidate".to_owned());
    }
    let diagram_vector_raster_four = co_testimony(&diagram_vector, &diagram_raster.four_testimony)?;
    let diagram_vector_raster_eight =
        co_testimony(&diagram_vector, &diagram_raster.eight_testimony)?;
    let diagram_four_population = diagram_raster.fiber.four_connected.occurrences.len();
    let diagram_eight_population = diagram_raster.fiber.eight_connected.occurrences.len();
    let diagram_counts_differ = diagram_four_population != diagram_eight_population;
    let diagram_plural_candidate = diagram_vector_raster_four
        .left_candidates
        .values()
        .chain(diagram_vector_raster_eight.left_candidates.values())
        .any(|candidates| candidates.len() > 1);
    let diagram_unmatched = !diagram_vector_raster_four.unmatched_left.is_empty()
        || !diagram_vector_raster_four.unmatched_right.is_empty()
        || !diagram_vector_raster_eight.unmatched_left.is_empty()
        || !diagram_vector_raster_eight.unmatched_right.is_empty();
    let diagram_disagreement_witness =
        diagram_counts_differ || diagram_plural_candidate || diagram_unmatched;
    if diagram_four_population <= 1
        || diagram_eight_population <= 1
        || !diagram_disagreement_witness
    {
        return Err(
            "the synthetic diagram returned a vacuous raster/correspondence population".to_owned(),
        );
    }
    let co_testimony = json!({
        "synthetic": {
            "text_vector": baseline_text_vector,
            "text_raster_four": co_testimony(&baseline_text, &baseline_raster.four_testimony)?,
            "text_raster_eight": co_testimony(&baseline_text, &baseline_raster.eight_testimony)?,
            "diagram_vector_raster_four": diagram_vector_raster_four,
            "diagram_vector_raster_eight": diagram_vector_raster_eight,
        },
        "natural_page_5": {
            "text_vector": page5_text_vector,
            "text_raster_four": co_testimony(&page5_text, &page5_raster.four_testimony)?,
            "text_raster_eight": co_testimony(&page5_text, &page5_raster.eight_testimony)?,
            "vector_raster_receiver_pair": "not declared: born-digital testimony connects vector and both raster fibres without a redundant all-pairs product",
        },
        "natural_page_10": {
            "text_vector": page10_text_vector,
            "text_raster_four": co_testimony(&page10_text, &page10_raster.four_testimony)?,
            "text_raster_eight": co_testimony(&page10_text, &page10_raster.eight_testimony)?,
            "vector_raster_receiver_pair": "not declared: born-digital testimony connects vector and both raster fibres without a redundant all-pairs product",
        },
        "equation_atlas": {
            "equations_relations": co_testimony(&equations, &relations)?,
        },
    });

    let identity_paths = [
        NATURAL_SOURCE,
        "research/fixtures/m0_mathematical_source_circulation/harmonic-source.typ",
        "research/fixtures/m0_mathematical_source_circulation/harmonic-baseline.typ",
        "research/fixtures/m0_mathematical_source_circulation/harmonic-reflow.typ",
        "research/fixtures/m0_mathematical_source_circulation/harmonic-perturbed.typ",
        "research/fixtures/m0_mathematical_source_circulation/harmonic-conjugation.svg",
        "output/m0_mathematical_source_circulation/faces/synthetic/harmonic-calibration.pdf",
        "output/m0_mathematical_source_circulation/faces/natural/heat-fisher-page-5-bbox.html",
        "output/m0_mathematical_source_circulation/faces/natural/heat-fisher-page-5.svg",
        "output/m0_mathematical_source_circulation/faces/natural/heat-fisher-page-5.png",
        "output/m0_mathematical_source_circulation/faces/natural/heat-fisher-page-10-bbox.html",
        "output/m0_mathematical_source_circulation/faces/natural/heat-fisher-page-10.svg",
        "output/m0_mathematical_source_circulation/faces/natural/heat-fisher-page-10.png",
    ];
    let identities = manifest_holds(&root, &identity_paths)?;
    let apparatus_path = format!("{OUT}/apparatus.txt");
    let apparatus_bytes = read(&root, &apparatus_path)?;
    let apparatus_identity = ArtifactIdentity::of_bytes(
        format!("{run}:exterior-apparatus"),
        &apparatus_path,
        &apparatus_bytes,
    )
    .map_err(|error| error.to_string())?;

    let report = json!({
        "schema": "eros.m0-mathematical-source-circulation.v1",
        "grade": "established-bounded",
        "boundary": "source/layout incidence only; no operation complex, proof, group action, manifold, or mathematical truth is inferred",
        "natural_source": natural_identity,
        "identity_ledger_population": identities,
        "apparatus_receipt": {
            "identity": apparatus_identity,
            "separate_from_deterministic_semantic_receipts": true,
        },
        "placement_receipt": {
            "grade": "established-bounded",
            "cpu_role": "bounded exterior/offline source-admission audit",
            "hot_mathematical_semantic_deed": "none in M0",
            "gpu_requirement": "begins with resident mathematical navigation and operation conduct in M1+",
            "cpu_fallback_or_replay_claimed": false,
            "deterministic_semantic_receipts_are_separate_from_apparatus": true,
        },
        "testimony": {
            "synthetic_baseline_text": layout_value(&baseline_text),
            "synthetic_reflow_text": layout_value(&reflow_text),
            "synthetic_perturbation_text": layout_value(&perturb_text),
            "synthetic_pdf_vector": layout_value(&baseline_vector),
            "synthetic_diagram_vector": layout_value(&diagram_vector),
            "natural_page_5_text": layout_value(&page5_text),
            "natural_page_5_vector": layout_value(&page5_vector),
            "natural_page_10_text": layout_value(&page10_text),
            "natural_page_10_vector": layout_value(&page10_vector),
            "equation_atlas_equations": layout_value(&equations),
            "equation_atlas_relations": layout_value(&relations),
        },
        "raster_reconstruction_fibers": raster_returns.iter().map(|(name, returned)| (name.clone(), json!({
            "extent": returned.extent,
            "fiber": raster_fiber_value(&returned.fiber),
            "four_testimony": layout_value(&returned.four_testimony),
            "eight_testimony": layout_value(&returned.eight_testimony),
        }))).collect::<BTreeMap<_, _>>(),
        "co_testimony": co_testimony,
        "controls": {
            "harmless_reflow": baseline_reflow,
            "semantic_perturbation": baseline_perturbation,
            "semantic_perturbation_payload_differences": serial_difference_count(&baseline_text, &perturb_text),
            "links_were_caller_supplied": false,
            "bbox_decimal_passed_through_float": false,
            "raster_four_and_eight_both_retained": true,
            "raster_background_receiver": "exact top-left pixel sample (0,0); alternatives remain open",
            "synthetic_diagram_raster_disagreement": {
                "four_population": diagram_four_population,
                "eight_population": diagram_eight_population,
                "population_counts_differ": diagram_counts_differ,
                "left_occurrence_has_plural_candidates": diagram_plural_candidate,
                "unmatched_population_nonempty": diagram_unmatched,
                "nontrivial_witness": diagram_disagreement_witness,
            },
            "outside_declared_sources_open": true,
        },
    });

    let encoded = serde_json::to_vec_pretty(&report).map_err(|error| error.to_string())?;
    let out = root.join(DEFAULT_OUT);
    fs::write(&out, &encoded).map_err(|error| format!("write {}: {error}", out.display()))?;
    println!("M0 MATHEMATICAL SOURCE CIRCULATION RETURNED");
    println!("  artifact: {}", out.display());
    println!("  octets: {}", encoded.len());
    println!("  sha256: {}", digest(&encoded));
    println!(
        "  synthetic text/vector/raster: {}/{}/{}-{}",
        baseline_text.occurrences.len(),
        baseline_vector.occurrences.len(),
        baseline_raster.fiber.four_connected.occurrences.len(),
        baseline_raster.fiber.eight_connected.occurrences.len(),
    );
    println!(
        "  natural page 5 text/vector/raster: {}/{}/{}-{}",
        page5_text.occurrences.len(),
        page5_vector.occurrences.len(),
        page5_raster.fiber.four_connected.occurrences.len(),
        page5_raster.fiber.eight_connected.occurrences.len(),
    );
    println!(
        "  natural page 10 text/vector/raster: {}/{}/{}-{}",
        page10_text.occurrences.len(),
        page10_vector.occurrences.len(),
        page10_raster.fiber.four_connected.occurrences.len(),
        page10_raster.fiber.eight_connected.occurrences.len(),
    );
    println!(
        "  atlas equations/relations: {}/{}",
        equations.occurrences.len(),
        relations.occurrences.len(),
    );
    println!("  reflow serial invariant: true; perturbation separator: one");
    Ok(())
}
