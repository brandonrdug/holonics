//! Bind the sealed-candidate station's categorical returned defects into free exact receiver
//! modules, derive their complete local factor covers, and enact one derived-rank cover as a single
//! resident GPU front.

use std::{
    collections::{BTreeMap, BTreeSet},
    env, fs,
    path::{Path, PathBuf},
    time::Instant,
};

use holonic_engine::{
    derived_factor_cover::{
        DefectMetrics, DerivedFactorCover, FactorDisposition, LocalFactorReceipt, OverlapKind,
        OverlapReceipt, SupportedDefectSection,
    },
    embedding_fiber::{AlignedMaterial, ResidentReadout},
    exact_linear::ExactRatMatrix,
    resident_section::{Dyadic, ResidentGrain, ResidentSurface, TransferCensus},
};
use num_bigint::BigInt;
use num_traits::ToPrimitive;
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use serde_json::json;
use sha2::{Digest, Sha256};

const DEFECTS: &str = "output/the_candidate_departs_before_sibling_testimony_returns/02-returned-sibling-defects.json";
const OUTPUT: &str = "output/the_returned_defect_founds_a_derived_local_factor_cover";
const ONE: u16 = 0x3f80;

#[derive(Clone, Debug, Deserialize)]
struct ReturnedDefect {
    proposal: String,
    candidate_occurrence: String,
    sibling_occurrence: String,
    additive_residual_assumed: bool,
    graded_faces: Vec<ReturnedFace>,
}

#[derive(Clone, Debug, Deserialize)]
struct ReturnedFace {
    grain: String,
    resident_candidate_class: u64,
    resident_sibling_class: u64,
}

#[derive(Clone, Debug, Serialize)]
struct SourceCoverArtifact {
    schema: String,
    source_path: String,
    additive_completion: String,
    row_basis: Vec<String>,
    column_basis: Vec<String>,
    cover: DerivedFactorCover,
}

#[derive(Clone, Debug, Serialize)]
struct ControlArtifact {
    schema: String,
    rank_zero: LocalFactorReceipt,
    rank_one: LocalFactorReceipt,
    rank_higher_singular: LocalFactorReceipt,
    compatible_overlap: OverlapReceipt,
    commuting_overlap: OverlapReceipt,
    noncommuting_overlap: OverlapReceipt,
    disjoint_interchange: OverlapReceipt,
}

#[derive(Clone, Debug, Serialize)]
struct ResidentFrontArtifact {
    schema: String,
    device: String,
    ptx_sha256: String,
    derived_rank: usize,
    factor_atoms: usize,
    input_width: usize,
    output_width: usize,
    returned_intervals: Vec<(i64, i64)>,
    exact_expected: Vec<i64>,
    matches_exact_reconstruction: bool,
    obstruction_population: usize,
    graph_nodes: usize,
    graph_edges: usize,
    semantic_kernel_nodes: usize,
    census: TransferCensus,
    cpu_semantic_replay_after_device: bool,
}

#[derive(Clone, Debug, Serialize)]
struct Invocation {
    schema: String,
    command: String,
    purpose: String,
    closure_sha256: String,
    elapsed_milliseconds: u128,
    exit_status: i32,
}

fn main() -> Result<(), String> {
    let started = Instant::now();
    let command = env::args().collect::<Vec<_>>().join(" ");
    let mut args = env::args_os().skip(1).map(PathBuf::from);
    let defects_path = args.next().unwrap_or_else(|| DEFECTS.into());
    let output = args.next().unwrap_or_else(|| OUTPUT.into());
    if args.next().is_some() {
        return Err("usage: [RETURNED_DEFECTS.json] [OUTPUT]".to_owned());
    }
    fs::create_dir_all(&output).map_err(display)?;
    let returned: Vec<ReturnedDefect> = read_json(&defects_path)?;
    let (row_basis, column_basis, sections) = source_sections(&returned)?;
    let source_cover = DerivedFactorCover::derive(sections).map_err(display)?;
    let source_artifact = SourceCoverArtifact {
        schema: "holonic-engine.returned-defect-source-cover.v1".to_owned(),
        source_path: defects_path.display().to_string(),
        additive_completion: "free exact module on typed candidate/sibling receiver faces; class ordinals are basis labels and are never subtracted".to_owned(),
        row_basis,
        column_basis,
        cover: source_cover,
    };
    let controls = controls()?;
    let resident = conduct_resident(
        source_artifact
            .cover
            .locals
            .first()
            .ok_or("the returned-defect cover is empty")?,
    )?;

    let source_every_reconstructs = source_artifact.cover.locals.iter().all(|local| {
        local.reconstructed_defect == local.section.supported
            && local.derived_rank == local.factors.len()
    });
    let source_every_parent_addressed = source_artifact.cover.locals.iter().all(|local| {
        local.factors.iter().all(|factor| {
            factor.parent_defect == local.section.address
                && !factor.ablation_address.is_empty()
                && factor.withdrawal.factor_address == factor.address
        })
    });
    let compatible = matches!(
        controls.compatible_overlap.kind,
        OverlapKind::CompatibleGlue { .. }
    );
    let commuting = matches!(
        controls.commuting_overlap.kind,
        OverlapKind::CommutingCocycle { .. }
    );
    let noncommuting = matches!(
        controls.noncommuting_overlap.kind,
        OverlapKind::PathOrderedHolonomy { .. }
    );
    let disjoint = matches!(
        controls.disjoint_interchange.kind,
        OverlapKind::DisjointInterchange { .. }
    );
    let passed = !returned.is_empty()
        && returned
            .iter()
            .all(|defect| !defect.additive_residual_assumed)
        && source_every_reconstructs
        && source_every_parent_addressed
        && controls.rank_zero.disposition == FactorDisposition::NoChange
        && controls.rank_zero.derived_rank == 0
        && controls.rank_one.derived_rank == 1
        && controls.rank_higher_singular.derived_rank > 1
        && !controls.rank_higher_singular.radical_fibre.is_empty()
        && !controls.rank_higher_singular.open_exterior.is_empty()
        && compatible
        && commuting
        && noncommuting
        && disjoint
        && resident.matches_exact_reconstruction
        && resident.obstruction_population == 0
        && !resident.cpu_semantic_replay_after_device;
    let grade = json!({
        "schema":"holonic-engine.returned-defect-factor-cover-grade.v1",
        "truth_status":"established-bounded",
        "passed":passed,
        "returned_defect_population":returned.len(),
        "source_local_sections":source_artifact.cover.locals.len(),
        "source_derived_factor_population":source_artifact.cover.factor_order.len(),
        "source_every_defect_reconstructs_exactly":source_every_reconstructs,
        "source_every_factor_has_parent_ablation_and_withdrawal":source_every_parent_addressed,
        "rank_zero_returned_as_no_change":controls.rank_zero.disposition == FactorDisposition::NoChange,
        "rank_one_returned":controls.rank_one.derived_rank == 1,
        "rank_greater_than_one_returned":controls.rank_higher_singular.derived_rank > 1,
        "singular_radical_and_open_exterior_retained":!controls.rank_higher_singular.radical_fibre.is_empty() && !controls.rank_higher_singular.open_exterior.is_empty(),
        "compatible_overlap_glued":compatible,
        "overlapping_commuting_cocycle_retained":commuting,
        "overlapping_noncommuting_holonomy_retained":noncommuting,
        "disjoint_interchange_returned":disjoint,
        "resident_derived_rank_front_matches_exact_reconstruction":resident.matches_exact_reconstruction,
        "gpu_device":resident.device,
        "gpu_deed_launches":resident.census.deed_launches,
        "cpu_semantic_replay_after_device":resident.cpu_semantic_replay_after_device,
    });
    write_json(
        &output.join("00-source-defect-cover.json"),
        &source_artifact,
    )?;
    write_json(&output.join("01-exact-controls.json"), &controls)?;
    write_json(
        &output.join("02-resident-derived-rank-front.json"),
        &resident,
    )?;
    write_json(&output.join("03-grade.json"), &grade)?;
    write_json(
        &output.join("04-expensive-invocation.json"),
        &Invocation {
            schema: "holonics.expensive-invocation.v1".to_owned(),
            command,
            purpose: "derive returned defects into exact local factor covers and enact one higher-rank cover on the resident GPU".to_owned(),
            closure_sha256: code_closure(),
            elapsed_milliseconds: started.elapsed().as_millis(),
            exit_status: i32::from(!passed),
        },
    )?;
    write_inspection(&output, &source_artifact, &controls, &resident, passed)?;
    write_manifest(&output)?;
    if !passed {
        return Err("the derived local factor-cover station refused its grade".to_owned());
    }
    println!("{}", serde_json::to_string_pretty(&grade).map_err(display)?);
    Ok(())
}

fn source_sections(
    returned: &[ReturnedDefect],
) -> Result<(Vec<String>, Vec<String>, Vec<SupportedDefectSection>), String> {
    if returned.is_empty() || returned.iter().any(|defect| defect.graded_faces.is_empty()) {
        return Err("the predecessor returned no graded defect sections".to_owned());
    }
    let column_basis = returned[0]
        .graded_faces
        .iter()
        .map(|face| face.grain.clone())
        .collect::<Vec<_>>();
    if returned.iter().any(|defect| {
        defect
            .graded_faces
            .iter()
            .map(|face| &face.grain)
            .ne(column_basis.iter())
    }) {
        return Err("returned defects do not share one declared receiver-grain chart".to_owned());
    }
    let row_basis = returned
        .iter()
        .flat_map(|defect| {
            defect.graded_faces.iter().flat_map(|face| {
                [
                    face_basis(&face.grain, face.resident_candidate_class),
                    face_basis(&face.grain, face.resident_sibling_class),
                ]
            })
        })
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let row_addresses = row_basis
        .iter()
        .enumerate()
        .map(|(index, name)| (name.clone(), index))
        .collect::<BTreeMap<_, _>>();
    let sections = returned
        .iter()
        .map(|defect| {
            let mut entries = vec![vec![rat(0); column_basis.len()]; row_basis.len()];
            for (column, face) in defect.graded_faces.iter().enumerate() {
                let candidate =
                    row_addresses[&face_basis(&face.grain, face.resident_candidate_class)];
                let sibling = row_addresses[&face_basis(&face.grain, face.resident_sibling_class)];
                entries[candidate][column] -= rat(1);
                entries[sibling][column] += rat(1);
            }
            let supported = ExactRatMatrix::new(entries).map_err(display)?;
            Ok(SupportedDefectSection {
                address: format!(
                    "defect:{}:{}",
                    defect.candidate_occurrence, defect.sibling_occurrence
                ),
                parent_candidate: defect.candidate_occurrence.clone(),
                receiver: "free-boundary-module-over-graded-receiver-family".to_owned(),
                successor_word: std::iter::once(format!("proposal:{}", defect.proposal))
                    .chain(
                        defect
                            .graded_faces
                            .iter()
                            .map(|face| format!("receiver-grain:{}", face.grain)),
                    )
                    .collect(),
                chart: "athena-returned-defect-free-module".to_owned(),
                ambient_rows: row_basis.len(),
                ambient_columns: column_basis.len(),
                support_rows: (0..row_basis.len()).collect(),
                support_columns: (0..column_basis.len()).collect(),
                metrics: DefectMetrics {
                    domain: ExactRatMatrix::identity(column_basis.len()).map_err(display)?,
                    codomain: ExactRatMatrix::identity(row_basis.len()).map_err(display)?,
                },
                supported,
            })
        })
        .collect::<Result<Vec<_>, String>>()?;
    Ok((row_basis, column_basis, sections))
}

fn controls() -> Result<ControlArtifact, String> {
    let rank_zero = control_section("rank-zero", vec![0, 1], &[&[0, 0], &[0, 0]])?
        .derive()
        .map_err(display)?;
    let rank_one = control_section("rank-one", vec![0, 1], &[&[2, 4], &[3, 6]])?
        .derive()
        .map_err(display)?;
    let rank_higher_singular = control_section(
        "rank-two-singular",
        vec![0, 1, 2],
        &[&[1, 0, 1], &[0, 1, 1], &[1, 1, 2]],
    )?
    .derive()
    .map_err(display)?;
    let compatible_overlap = sole_overlap(DerivedFactorCover::derive(vec![
        control_section("compatible-left", vec![0, 1], &[&[1, 0], &[0, 2]])?,
        control_section("compatible-right", vec![1, 2], &[&[2, 0], &[0, 3]])?,
    ]))?;
    let commuting_overlap = sole_overlap(DerivedFactorCover::derive(vec![
        control_section("commuting-left", vec![0, 1], &[&[1, 0], &[0, 2]])?,
        control_section("commuting-right", vec![0, 1], &[&[3, 0], &[0, 4]])?,
    ]))?;
    let noncommuting_overlap = sole_overlap(DerivedFactorCover::derive(vec![
        control_section("ordered-left", vec![0, 1], &[&[0, 1], &[0, 0]])?,
        control_section("ordered-right", vec![0, 1], &[&[0, 0], &[1, 0]])?,
    ]))?;
    let disjoint_interchange = sole_overlap(DerivedFactorCover::derive(vec![
        control_section("disjoint-left", vec![0], &[&[2]])?,
        control_section("disjoint-right", vec![3], &[&[5]])?,
    ]))?;
    Ok(ControlArtifact {
        schema: "holonic-engine.derived-factor-cover-controls.v1".to_owned(),
        rank_zero,
        rank_one,
        rank_higher_singular,
        compatible_overlap,
        commuting_overlap,
        noncommuting_overlap,
        disjoint_interchange,
    })
}

fn control_section(
    address: &str,
    support: Vec<usize>,
    values: &[&[i64]],
) -> Result<SupportedDefectSection, String> {
    let supported = ExactRatMatrix::new(
        values
            .iter()
            .map(|row| row.iter().map(|value| rat(*value)).collect())
            .collect(),
    )
    .map_err(display)?;
    Ok(SupportedDefectSection {
        address: address.to_owned(),
        parent_candidate: format!("control-parent:{address}"),
        receiver: "exact-control-receiver".to_owned(),
        successor_word: vec![format!("control-word:{address}")],
        chart: "factor-cover-control-chart".to_owned(),
        ambient_rows: 4,
        ambient_columns: 4,
        support_rows: support.clone(),
        support_columns: support,
        metrics: DefectMetrics {
            domain: ExactRatMatrix::identity(supported.columns()).map_err(display)?,
            codomain: ExactRatMatrix::identity(supported.rows()).map_err(display)?,
        },
        supported,
    })
}

fn sole_overlap(
    cover: Result<DerivedFactorCover, holonic_engine::derived_factor_cover::FactorCoverError>,
) -> Result<OverlapReceipt, String> {
    let mut overlaps = cover.map_err(display)?.overlaps;
    if overlaps.len() != 1 {
        return Err("a two-section control did not return exactly one overlap".to_owned());
    }
    Ok(overlaps.remove(0))
}

fn conduct_resident(local: &LocalFactorReceipt) -> Result<ResidentFrontArtifact, String> {
    if local.derived_rank == 0 {
        return Err("rank zero has no resident factor contraction".to_owned());
    }
    let readout = ResidentReadout::new().map_err(debug)?;
    let surface = ResidentSurface::on(&readout).map_err(display)?;
    let before = surface.census();
    let left_entries = integral_entries(&local.factorization.left)?;
    let right_entries = integral_entries(&local.factorization.right)?;
    let left = readout
        .mount(&aligned(left_entries), local.factorization.left.columns())
        .map_err(debug)?;
    let right = readout
        .mount(&aligned(right_entries), local.factorization.right.columns())
        .map_err(debug)?;
    let input_width = local.factorization.columns;
    let input_words = vec![ONE; input_width];
    let grain = ResidentGrain(0);
    let staged = surface
        .stage_words(&input_words, 1, input_width)
        .map_err(display)?;
    let enter_shape = surface
        .shape_enter(1, input_width, Dyadic::ONE, grain, &input_words)
        .map_err(display)?;
    let factor_shape = surface
        .shape_factorized_contract(
            1,
            input_width,
            enter_shape.needed,
            &left,
            &right,
            local.derived_rank,
        )
        .map_err(display)?;
    let input = surface
        .fresh_section(1, input_width, grain)
        .map_err(display)?;
    let output = surface
        .fresh_section(1, local.factorization.rows, grain)
        .map_err(display)?;
    let mut builder = surface.begin_passage(&[vec![], vec![0]]).map_err(display)?;
    let lane = builder.open(0, &[]).map_err(display)?;
    surface
        .record_enter(&lane, &staged, Dyadic::ONE, &input)
        .map_err(display)?;
    builder
        .close(0, &input, enter_shape.needed)
        .map_err(display)?;
    let lane = builder.open(1, &[0]).map_err(display)?;
    surface
        .record_factorized_contract(&lane, &input, &left, &right, &factor_shape, &output)
        .map_err(display)?;
    builder
        .close(1, &output, factor_shape.needed)
        .map_err(display)?;
    let passage = builder.finish().map_err(display)?;
    let graph = passage.graph_census().clone();
    let reading = passage.launch().map_err(display)?;
    let intervals = surface.read_out(&output).map_err(display)?;
    let expected = local
        .section
        .supported
        .apply(&vec![rat(1); input_width])
        .map_err(display)?
        .iter()
        .map(rational_integer)
        .collect::<Result<Vec<_>, _>>()?;
    let matches = intervals
        .iter()
        .zip(&expected)
        .all(|((lower, upper), expected)| lower == expected && upper == expected);
    let after = surface.census();
    Ok(ResidentFrontArtifact {
        schema: "holonic-engine.resident-derived-rank-factor-front.v1".to_owned(),
        device: surface.device_name().to_owned(),
        ptx_sha256: surface.ptx_sha256().to_owned(),
        derived_rank: local.derived_rank,
        factor_atoms: local.factors.len(),
        input_width,
        output_width: local.factorization.rows,
        returned_intervals: intervals,
        exact_expected: expected,
        matches_exact_reconstruction: matches,
        obstruction_population: reading.obstruction.refusals.len(),
        graph_nodes: graph.nodes,
        graph_edges: graph.edges,
        semantic_kernel_nodes: graph.kernel_nodes,
        census: census_delta(&before, &after),
        cpu_semantic_replay_after_device: false,
    })
}

fn aligned(entries: Vec<i64>) -> AlignedMaterial {
    AlignedMaterial {
        entry_octaves: entries
            .iter()
            .map(|value| i64::BITS - value.unsigned_abs().leading_zeros())
            .max()
            .unwrap_or(0),
        negatives: entries.iter().filter(|value| **value < 0).count() as u64,
        entries,
        exponent: 0,
    }
}

fn integral_entries(matrix: &ExactRatMatrix) -> Result<Vec<i64>, String> {
    matrix.entries().iter().map(rational_integer).collect()
}

fn rational_integer(value: &Rat) -> Result<i64, String> {
    if value.denom() != &BigInt::from(1) {
        return Err(format!(
            "resident control {value} is not in the exact integer aperture"
        ));
    }
    value
        .numer()
        .to_i64()
        .ok_or_else(|| format!("resident control {value} exceeds i64"))
}

fn face_basis(grain: &str, class: u64) -> String {
    format!("receiver:{grain}/class:{class}")
}

fn rat(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn census_delta(before: &TransferCensus, after: &TransferCensus) -> TransferCensus {
    TransferCensus {
        ingress_octets: after.ingress_octets.saturating_sub(before.ingress_octets),
        egress_section_octets: after
            .egress_section_octets
            .saturating_sub(before.egress_section_octets),
        egress_receipt_octets: after
            .egress_receipt_octets
            .saturating_sub(before.egress_receipt_octets),
        device_to_device_octets: after
            .device_to_device_octets
            .saturating_sub(before.device_to_device_octets),
        captured_launches: after
            .captured_launches
            .saturating_sub(before.captured_launches),
        deed_launches: after.deed_launches.saturating_sub(before.deed_launches),
        control_launches: after
            .control_launches
            .saturating_sub(before.control_launches),
        synchronizations: after
            .synchronizations
            .saturating_sub(before.synchronizations),
        allocations: after.allocations.saturating_sub(before.allocations),
        resident_octets_now: after.resident_octets_now,
        resident_octets_peak: after.resident_octets_peak,
        section_read_outs: after
            .section_read_outs
            .saturating_sub(before.section_read_outs),
    }
}

fn write_inspection(
    output: &Path,
    source: &SourceCoverArtifact,
    controls: &ControlArtifact,
    resident: &ResidentFrontArtifact,
    passed: bool,
) -> Result<(), String> {
    let text = format!(
        "# The returned defect founded a derived local factor cover\n\n- Returned defect sections: {}.\n- Derived source factors: {}.\n- First source rank: {}.\n- Rank-zero control: {}.\n- Rank-one control: {}.\n- Singular higher-rank control: rank {}, radical {}, open exterior {}.\n- Resident device: {}.\n- Resident derived-rank front: {} factors, {} deed launch, exact reconstruction {}.\n- Compatible glue, commuting cocycle, noncommuting holonomy and disjoint interchange are retained in 01-exact-controls.json.\n- Station grade: {passed}.\n",
        source.cover.locals.len(),
        source.cover.factor_order.len(),
        source
            .cover
            .locals
            .first()
            .map_or(0, |local| local.derived_rank),
        controls.rank_zero.derived_rank,
        controls.rank_one.derived_rank,
        controls.rank_higher_singular.derived_rank,
        controls.rank_higher_singular.radical_fibre.len(),
        controls.rank_higher_singular.open_exterior.len(),
        resident.device,
        resident.factor_atoms,
        resident.census.deed_launches,
        resident.matches_exact_reconstruction,
    );
    fs::write(output.join("INSPECTION.md"), text).map_err(display)
}

fn write_manifest(output: &Path) -> Result<(), String> {
    let mut files = fs::read_dir(output)
        .map_err(display)?
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| {
            path.is_file() && path.file_name().is_some_and(|name| name != "MANIFEST.json")
        })
        .collect::<Vec<_>>();
    files.sort();
    let entries = files
        .iter()
        .map(|path| {
            let bytes = fs::read(path).map_err(display)?;
            Ok(json!({
                "path":path.file_name().unwrap().to_string_lossy(),
                "octets":bytes.len(),
                "sha256":sha(&bytes),
            }))
        })
        .collect::<Result<Vec<_>, String>>()?;
    let identity = sha(&serde_json::to_vec(&entries).map_err(display)?);
    write_json(
        &output.join("MANIFEST.json"),
        &json!({
            "schema":"holonics.derived-factor-cover-manifest.v1",
            "identity":identity,
            "files":entries,
        }),
    )
}

fn read_json<T: for<'de> Deserialize<'de>>(path: &Path) -> Result<T, String> {
    serde_json::from_slice(&fs::read(path).map_err(display)?)
        .map_err(|error| format!("{}: {error}", path.display()))
}

fn write_json(path: &Path, value: &impl Serialize) -> Result<(), String> {
    fs::write(path, serde_json::to_vec_pretty(value).map_err(display)?).map_err(display)
}

fn sha(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn code_closure() -> String {
    sha([
        include_str!("the_returned_defect_founds_a_derived_local_factor_cover.rs"),
        include_str!("../src/derived_factor_cover.rs"),
        include_str!("../src/exact_linear.rs"),
        include_str!("../src/resident_law.rs"),
        include_str!("../src/resident_section.rs"),
        include_str!("../kernels/exact_resident_section.cu"),
    ]
    .concat()
    .as_bytes())
}

fn display(error: impl std::fmt::Display) -> String {
    error.to_string()
}

fn debug(error: impl std::fmt::Debug) -> String {
    format!("{error:?}")
}
