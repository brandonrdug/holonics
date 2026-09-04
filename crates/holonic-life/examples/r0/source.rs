use std::collections::BTreeSet;
use std::fs;
use std::path::Path;

use life::exchange_world_tube::{
    mount_exchange_world_tube_on_device, Digest32, ExchangeContainerSpec, VisibleMessageFace,
};
use life::mathematical_source::{
    compare_presentations, correspond, correspondence_demand, derive_layout, layout_demand,
    ArtifactIdentity, ExactBox, ExactExtent, LayoutContact, PlacedCarrier, PresentationComparison,
    Rat, SourceLayoutTestimony, SourceLayoutWorkCover, SourceLayoutWorkDemand, TestimonyChart,
};
use num_bigint::BigInt;
use serde::Serialize;
use serde_json::Value;
use sha2::{Digest, Sha256};

pub const FROZEN_SOURCE_COMMIT: &str = "ac170966c987948b9b09c9479e1bfe932eec6a3b";
const FIXTURE_ROOT: &str = "research/fixtures/r0_rich_inquiry";
const M1_PASSAGE: &str =
    ".local/artifacts/the_mathematical_particle_is_an_addressed_passage/addressed-passages.form";
const M6_PRODUCT: &str = ".local/artifacts/the_total_descent_route_cultivates_the_first_athena_variant/product/19-athena-product.json";
const M6_ROUTE_FIBRE: &str = ".local/artifacts/the_total_descent_route_cultivates_the_first_athena_variant/product/18-exact-route-work-and-fibre.json";
const EQUATION_ATLAS: [&str; 3] = [
    "archive/equation-atlas/equations.jsonl",
    "archive/equation-atlas/relations.jsonl",
    "archive/equation-atlas/manifest.json",
];

const FORMAL_CLOSURE: [(&str, &str, &str); 12] = [
    (
        "ElementaryHolonics/Millennium/ChordFace.lean",
        "97344fa59a486bbe7704326b6462b15fe9a0a4e1",
        "a65e68a4156aecf94be98cd402b6e04ebb56f96048c11cf8f9c3c97b40a9ceba",
    ),
    (
        "ElementaryHolonics/Millennium/Descent.lean",
        "2ec504d12fd8089e619bf8ce7f9de69fa91df2d0",
        "01cfbfc8c2b7aa0dfb6766578f4fca379a42016b58bb8ddbff042d976ec26396",
    ),
    (
        "ElementaryHolonics/Millennium/DistantWindings.lean",
        "05c7b03a73022bb023aa99558a145e67e5ee8163",
        "8dcd34e43efc23e4a6e5e4faf160aeb6f0b74f72cc10337503a1c385b252f453",
    ),
    (
        "ElementaryHolonics/Millennium/FaceHomomorphism.lean",
        "452d3508780005c82f6b3d99301ae68fd5e0c57d",
        "1f46d1b8198d494a4a54e2589c1fd1f37d062457f39889c3941ea412ff440c49",
    ),
    (
        "ElementaryHolonics/Millennium/FaithfulFace.lean",
        "a722c924560fb30a51d631a28f5b545d17c2d0c7",
        "060bd44e1a8a3688236693fa57d67762d09513146f9d47cbc3fb3582328b5bb1",
    ),
    (
        "ElementaryHolonics/Millennium/FamilyFace.lean",
        "f5c2d32d6c02de39f5a0858cbf7dcb7a803bfd2e",
        "b3d5d0ae4ed8bd27458f325821de069e783fba3e63d89d3e9728e96353b46bfb",
    ),
    (
        "ElementaryHolonics/Millennium/FamilyHalving.lean",
        "8fc037b06bc8477f7da12fb80324fd1d0ba0d378",
        "de1b3c8240d5c9684cf87f78ff3eee78f4e0b4ae3cbac366e29fd33b8ae74c6a",
    ),
    (
        "ElementaryHolonics/Millennium/FamilyKernel.lean",
        "8d5a64099d6f5630d6d4c5b01566d4838591f11e",
        "e567430f86f68be8a8b619eb3c0134eb1d0d6fe4c7de1f33cb394c3c59507c03",
    ),
    (
        "ElementaryHolonics/Millennium/FamilySupport.lean",
        "607d7a92f1e83f19ba0db1e7e090216faccbe3d2",
        "ae9e9e4da4335e55478df1fba34e17159ae01c14e866ef4e974631db36cba60a",
    ),
    (
        "ElementaryHolonics/Millennium/FrameDescent.lean",
        "c93605ecc32eb70ac5968a58db08bf961fd03911",
        "ca13f1c1dcf106230e651b231c792626ef19bc4f9179df5da327f94ae4541864",
    ),
    (
        "ElementaryHolonics/Millennium/RankOne.lean",
        "9b1eef88344485c71e48e4e4944ff1be7fa8524e",
        "ae888c43b09de6a1fadfdd3205182a950a5792f37691c15950611bdab6ea111f",
    ),
    (
        "ElementaryHolonics/Millennium/WindingCensus.lean",
        "c58ac9c5c7a4f1d522561096bee46200da0cd486",
        "d4ba57422976fc9d722bb4c5bf67ac07468a783f3137e984c54a53b227d55d22",
    ),
];

#[derive(Clone, Debug, Serialize)]
pub struct FileIdentity {
    pub relative_path: String,
    pub sha256: String,
    pub octets: u64,
}

#[derive(Clone, Debug, Serialize)]
pub struct FormalSourceIdentity {
    pub relative_path: String,
    pub git_blob_at_frozen_commit: String,
    pub sha256: String,
    pub octets: u64,
}

#[derive(Debug, Serialize)]
pub struct A1MountReceipt {
    pub source_occurrence_sha256: String,
    pub content_law_sha256: String,
    pub records: usize,
    pub nodes: usize,
    pub scalar_sites: usize,
    pub visible_messages: usize,
    pub primary_record_occurrence_sha256: String,
    pub device: String,
    pub launches: u64,
    pub block_threads: u32,
    pub cpu_semantic_replay: bool,
}

#[derive(Debug, Serialize)]
pub struct OccurrenceFace {
    pub address: String,
    pub payload_sha256: String,
    pub payload_octets: u64,
    pub serial_ordinal: Option<u64>,
}

#[derive(Debug, Serialize)]
pub struct LayoutFaceReceipt {
    pub artifact: ArtifactIdentity,
    pub chart: TestimonyChart,
    pub occurrences: Vec<OccurrenceFace>,
    pub contacts: Vec<LayoutContact>,
    pub work: SourceLayoutWorkDemand,
    pub outside_declared_artifact_open: bool,
}

#[derive(Debug, Serialize)]
pub struct M0Return {
    pub language: LayoutFaceReceipt,
    pub lean: LayoutFaceReceipt,
    pub diagram_a: LayoutFaceReceipt,
    pub diagram_b: LayoutFaceReceipt,
    pub cross_codec_candidate_pairs: usize,
    pub cross_codec_unmatched_language: usize,
    pub cross_codec_unmatched_lean: usize,
    pub layout_control: PresentationComparison,
}

#[derive(Debug, Serialize)]
pub struct ProductOwnerReceipt {
    pub identity: FileIdentity,
    pub declared_schema: Option<String>,
    pub addressed_source_population: usize,
    pub source_intersection_with_inquiry: usize,
}

#[derive(Debug, Serialize)]
pub struct SourceReturn {
    pub frozen_source_commit: String,
    pub formal_dependency_rule: String,
    pub formal_source_closure: Vec<FormalSourceIdentity>,
    pub excluded_uncommitted_occurrences: Vec<String>,
    pub later_commits_excluded: bool,
    pub inquiry_files: Vec<FileIdentity>,
    pub equation_atlas: Vec<FileIdentity>,
    pub source_accessed_paths: Vec<String>,
    pub forbidden_source_access_observed: bool,
    pub a1: A1MountReceipt,
    pub m0: M0Return,
    pub m1: ProductOwnerReceipt,
    pub m6_product: ProductOwnerReceipt,
    pub m6_route_fibre: FileIdentity,
    pub inquiry_source_addresses: Vec<String>,
}

pub fn mount(root: &Path) -> Result<SourceReturn, String> {
    let mut accessed = Vec::new();
    let inquiry_jsonl = format!("{FIXTURE_ROOT}/inquiry.jsonl");
    let inquiry_jsonl_path = root.join(&inquiry_jsonl);
    let inquiry_jsonl_bytes = read(root, &inquiry_jsonl, &mut accessed)?;
    let mut exchange = mount_exchange_world_tube_on_device(&[ExchangeContainerSpec {
        locator: inquiry_jsonl_path,
        provider_face: "operator".to_owned(),
        material_kind_face: "rich-inquiry-control-cohort".to_owned(),
    }])
    .map_err(|error| error.to_string())?;
    let primary = exchange
        .records
        .first()
        .ok_or_else(|| "A1 mounted no inquiry record".to_owned())?;
    let primary_value: Value = serde_json::from_slice(
        inquiry_jsonl_bytes
            .get(primary.raw_range.start as usize..primary.raw_range.end as usize)
            .ok_or_else(|| "primary inquiry range left its container".to_owned())?,
    )
    .map_err(|error| error.to_string())?;
    let primary_text = primary_value
        .get("text")
        .and_then(Value::as_str)
        .ok_or_else(|| "primary inquiry exterior text face is absent".to_owned())?
        .to_owned();
    let primary_record_occurrence = exchange.record_occurrence(0);
    exchange
        .attach_visible_messages(
            vec![VisibleMessageFace {
                container: 0,
                record: 0,
                raw_range: primary.raw_range.clone(),
                occurrence: "r0/operator/primary-inquiry".to_owned(),
                text_sha256: Digest32::of(primary_text.as_bytes()),
                text: primary_text,
                provider_face: "operator".to_owned(),
                speaker_face: "operator".to_owned(),
                phase_face: "received".to_owned(),
            }],
            0,
        )
        .map_err(|error| error.to_string())?;
    let a1 = A1MountReceipt {
        source_occurrence_sha256: exchange.source_occurrence_sha256.render(),
        content_law_sha256: exchange.content_law_sha256.render(),
        records: exchange.records.len(),
        nodes: exchange.nodes.len(),
        scalar_sites: exchange.scalar_sites.len(),
        visible_messages: exchange.visible_messages.len(),
        primary_record_occurrence_sha256: primary_record_occurrence.render(),
        device: exchange.device.device.clone(),
        launches: exchange.device.launches,
        block_threads: exchange.device.block_threads,
        cpu_semantic_replay: exchange.device.cpu_semantic_replay,
    };

    let language = line_layout(
        root,
        &format!("{FIXTURE_ROOT}/inquiry.md"),
        "r0/inquiry/language",
        TestimonyChart::BornDigital,
        &mut accessed,
    )?;
    let lean = line_layout(
        root,
        &format!("{FIXTURE_ROOT}/inquiry.lean"),
        "r0/inquiry/lean",
        TestimonyChart::BornDigital,
        &mut accessed,
    )?;
    let diagram_a = diagram_layout(
        root,
        &format!("{FIXTURE_ROOT}/support-route-a.svg"),
        "r0/inquiry/diagram-a",
        false,
        &mut accessed,
    )?;
    let diagram_b = diagram_layout(
        root,
        &format!("{FIXTURE_ROOT}/support-route-b.svg"),
        "r0/inquiry/diagram-b",
        true,
        &mut accessed,
    )?;
    let cross_demand =
        correspondence_demand(&language, &lean).map_err(|error| error.to_string())?;
    let cross = correspond(
        &language,
        &lean,
        &SourceLayoutWorkCover::exactly(&cross_demand),
    )
    .map_err(|error| error.to_string())?;
    let layout_control = compare_presentations(&diagram_a, &diagram_b);
    let inquiry_source_addresses = language
        .occurrences
        .iter()
        .chain(&lean.occurrences)
        .chain(&diagram_a.occurrences)
        .chain(&diagram_b.occurrences)
        .map(|occurrence| occurrence.address.clone())
        .collect::<Vec<_>>();
    let m0 = M0Return {
        language: layout_receipt(language),
        lean: layout_receipt(lean),
        diagram_a: layout_receipt(diagram_a),
        diagram_b: layout_receipt(diagram_b),
        cross_codec_candidate_pairs: cross.candidates.len(),
        cross_codec_unmatched_language: cross.unmatched_left.len(),
        cross_codec_unmatched_lean: cross.unmatched_right.len(),
        layout_control,
    };

    let m1_bytes = read(root, M1_PASSAGE, &mut accessed)?;
    let m1_value: Value = serde_json::from_slice(&m1_bytes).map_err(|error| error.to_string())?;
    let m1_sources = addressed_m0_sources(&m1_value);
    let inquiry_set = inquiry_source_addresses.iter().collect::<BTreeSet<_>>();
    let m1 = ProductOwnerReceipt {
        identity: identity(M1_PASSAGE, &m1_bytes)?,
        declared_schema: None,
        addressed_source_population: m1_sources.len(),
        source_intersection_with_inquiry: m1_sources
            .iter()
            .filter(|source| inquiry_set.contains(source))
            .count(),
    };

    let m6_bytes = read(root, M6_PRODUCT, &mut accessed)?;
    let m6_value: Value = serde_json::from_slice(&m6_bytes).map_err(|error| error.to_string())?;
    let m6_product = ProductOwnerReceipt {
        identity: identity(M6_PRODUCT, &m6_bytes)?,
        declared_schema: m6_value
            .get("schema")
            .and_then(Value::as_str)
            .map(str::to_owned),
        addressed_source_population: m6_value
            .get("variants")
            .and_then(Value::as_array)
            .map_or(0, Vec::len),
        source_intersection_with_inquiry: 0,
    };
    let m6_route_bytes = read(root, M6_ROUTE_FIBRE, &mut accessed)?;
    let m6_route_fibre = identity(M6_ROUTE_FIBRE, &m6_route_bytes)?;

    let equation_atlas = EQUATION_ATLAS
        .iter()
        .map(|relative| {
            let bytes = read(root, relative, &mut accessed)?;
            identity(relative, &bytes)
        })
        .collect::<Result<Vec<_>, String>>()?;
    let inquiry_files = [
        format!("{FIXTURE_ROOT}/inquiry.jsonl"),
        format!("{FIXTURE_ROOT}/inquiry.md"),
        format!("{FIXTURE_ROOT}/inquiry.lean"),
        format!("{FIXTURE_ROOT}/support-route-a.svg"),
        format!("{FIXTURE_ROOT}/support-route-b.svg"),
    ]
    .iter()
    .map(|relative| {
        let bytes = fs::read(root.join(relative)).map_err(|error| error.to_string())?;
        identity(relative, &bytes)
    })
    .collect::<Result<Vec<_>, String>>()?;

    let formal_root = root.join("formal/elementary-holonics");
    let formal_source_closure = FORMAL_CLOSURE
        .iter()
        .map(|(relative, blob, expected)| {
            let path = formal_root.join(relative);
            let bytes =
                fs::read(&path).map_err(|error| format!("read {}: {error}", path.display()))?;
            let actual = digest(&bytes);
            if actual != *expected {
                return Err(format!(
                    "formal source {relative} moved outside frozen commit: {actual}"
                ));
            }
            accessed.push(format!("formal/elementary-holonics/{relative}"));
            Ok(FormalSourceIdentity {
                relative_path: relative.to_string(),
                git_blob_at_frozen_commit: blob.to_string(),
                sha256: actual,
                octets: bytes.len() as u64,
            })
        })
        .collect::<Result<Vec<_>, String>>()?;
    accessed.sort();
    accessed.dedup();
    let excluded =
        "formal/elementary-holonics/ElementaryHolonics/Millennium/FamilyMordell.lean";
    let forbidden_source_access_observed = accessed.iter().any(|path| path == excluded);
    if forbidden_source_access_observed {
        return Err("the uncommitted FamilyMordell occurrence entered R0".to_owned());
    }

    Ok(SourceReturn {
        frozen_source_commit: FROZEN_SOURCE_COMMIT.to_owned(),
        formal_dependency_rule: "recursive local source closure returned by `lake env lean --src-deps`, frozen before R0 construction; imported Mathlib/Init stand as exterior package rests".to_owned(),
        formal_source_closure,
        excluded_uncommitted_occurrences: vec![excluded.to_owned()],
        later_commits_excluded: true,
        inquiry_files,
        equation_atlas,
        source_accessed_paths: accessed,
        forbidden_source_access_observed,
        a1,
        m0,
        m1,
        m6_product,
        m6_route_fibre,
        inquiry_source_addresses,
    })
}

fn line_layout(
    root: &Path,
    relative: &str,
    occurrence: &str,
    chart: TestimonyChart,
    accessed: &mut Vec<String>,
) -> Result<SourceLayoutTestimony, String> {
    let bytes = read(root, relative, accessed)?;
    let artifact = ArtifactIdentity::of_bytes(occurrence, relative, &bytes)
        .map_err(|error| error.to_string())?;
    let lines = bytes
        .split(|octet| *octet == b'\n')
        .filter(|line| !line.is_empty())
        .collect::<Vec<_>>();
    let width = lines.iter().map(|line| line.len()).max().unwrap_or(1);
    let extent = ExactExtent::new(integer(width), integer(lines.len().max(1)))
        .map_err(|error| error.to_string())?;
    let occurrences = lines
        .iter()
        .enumerate()
        .map(|(at, line)| {
            PlacedCarrier::new(
                &artifact,
                at as u64,
                line.to_vec(),
                Some(at as u64),
                ExactBox::new(
                    integer(0),
                    integer(at),
                    integer(line.len()),
                    integer(at + 1),
                )
                .map_err(|error| error.to_string())?,
            )
            .map_err(|error| error.to_string())
        })
        .collect::<Result<Vec<_>, String>>()?;
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

fn diagram_layout(
    root: &Path,
    relative: &str,
    occurrence: &str,
    reflow: bool,
    accessed: &mut Vec<String>,
) -> Result<SourceLayoutTestimony, String> {
    let bytes = read(root, relative, accessed)?;
    let artifact = ArtifactIdentity::of_bytes(occurrence, relative, &bytes)
        .map_err(|error| error.to_string())?;
    let labels = ["E_n(Q)", "slots", "valuations", "squarefree", "support 2n"];
    let text = std::str::from_utf8(&bytes).map_err(|error| error.to_string())?;
    if labels.iter().any(|label| !text.contains(label)) {
        return Err(format!("{relative} lost one addressed diagram carrier"));
    }
    let boxes = if reflow {
        [
            (20, 40, 160, 140),
            (240, 40, 360, 140),
            (440, 160, 560, 260),
            (640, 280, 760, 380),
            (840, 280, 980, 380),
        ]
    } else {
        [
            (20, 70, 160, 170),
            (240, 70, 360, 170),
            (440, 70, 560, 170),
            (640, 70, 760, 170),
            (840, 70, 980, 170),
        ]
    };
    let occurrences = labels
        .iter()
        .zip(boxes)
        .enumerate()
        .map(|(at, (label, (left, top, right, bottom)))| {
            PlacedCarrier::new(
                &artifact,
                at as u64,
                label.as_bytes().to_vec(),
                Some(at as u64),
                ExactBox::new(integer(left), integer(top), integer(right), integer(bottom))
                    .map_err(|error| error.to_string())?,
            )
            .map_err(|error| error.to_string())
        })
        .collect::<Result<Vec<_>, String>>()?;
    let extent = ExactExtent::new(integer(1000), integer(if reflow { 420 } else { 240 }))
        .map_err(|error| error.to_string())?;
    let demand = layout_demand(&occurrences).map_err(|error| error.to_string())?;
    derive_layout(
        TestimonyChart::Vector,
        artifact,
        extent,
        occurrences,
        &SourceLayoutWorkCover::exactly(&demand),
    )
    .map_err(|error| error.to_string())
}

fn layout_receipt(testimony: SourceLayoutTestimony) -> LayoutFaceReceipt {
    LayoutFaceReceipt {
        artifact: testimony.artifact,
        chart: testimony.chart,
        occurrences: testimony
            .occurrences
            .into_iter()
            .map(|occurrence| OccurrenceFace {
                address: occurrence.address,
                payload_sha256: occurrence.payload_sha256,
                payload_octets: occurrence.payload_octets,
                serial_ordinal: occurrence.serial_ordinal,
            })
            .collect(),
        contacts: testimony.contacts,
        work: testimony.work,
        outside_declared_artifact_open: testimony.outside_declared_artifact_open,
    }
}

fn addressed_m0_sources(value: &Value) -> BTreeSet<String> {
    fn visit(value: &Value, out: &mut BTreeSet<String>) {
        match value {
            Value::String(text) if text.starts_with("m0-") => {
                out.insert(text.clone());
            }
            Value::Array(values) => values.iter().for_each(|value| visit(value, out)),
            Value::Object(values) => values.values().for_each(|value| visit(value, out)),
            _ => {}
        }
    }
    let mut out = BTreeSet::new();
    visit(value, &mut out);
    out
}

fn read(root: &Path, relative: &str, accessed: &mut Vec<String>) -> Result<Vec<u8>, String> {
    let path = root.join(relative);
    let bytes = fs::read(&path).map_err(|error| format!("read {}: {error}", path.display()))?;
    accessed.push(relative.to_owned());
    Ok(bytes)
}

fn identity(relative: &str, bytes: &[u8]) -> Result<FileIdentity, String> {
    Ok(FileIdentity {
        relative_path: relative.to_owned(),
        sha256: digest(bytes),
        octets: u64::try_from(bytes.len()).map_err(|_| "file extent overflow".to_owned())?,
    })
}

fn digest(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect()
}

fn integer(value: usize) -> Rat {
    Rat::from_integer(BigInt::from(value))
}
