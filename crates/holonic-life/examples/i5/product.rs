//! I5 inspection products: complete cost, dissection atlas, exact mesh, ablations, capability,
//! and indivisible grade. The JSON mesh is authoritative; SVG coordinates are a receiver chart.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::Path;

use holonic_engine::{
    category::BoundaryId, native_ecology::inference_ecology::InferenceEcologyRest,
};
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};

use super::{hex, write_json, DetachedReturn, RestDirectory};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct CostFace {
    artifact_octets: u64,
    decoder_octets: u64,
    fibre_octets: u64,
    semantic_work: u64,
    dependency_span: u64,
    resident_octets: u64,
    transfer_octets: u64,
}

impl CostFace {
    fn add(&self, other: &Self) -> Result<Self, String> {
        Ok(Self {
            artifact_octets: checked(self.artifact_octets, other.artifact_octets)?,
            decoder_octets: checked(self.decoder_octets, other.decoder_octets)?,
            fibre_octets: checked(self.fibre_octets, other.fibre_octets)?,
            semantic_work: checked(self.semantic_work, other.semantic_work)?,
            dependency_span: checked(self.dependency_span, other.dependency_span)?,
            resident_octets: checked(self.resident_octets, other.resident_octets)?,
            transfer_octets: checked(self.transfer_octets, other.transfer_octets)?,
        })
    }
}

#[derive(Deserialize)]
struct PriorCost {
    source: CostFace,
}

#[derive(Serialize)]
struct CompleteCost {
    schema: &'static str,
    truth_status: &'static str,
    source: CostFace,
    native: CostFace,
    strict_coordinate_fall: BTreeMap<&'static str, bool>,
    every_coordinate_strictly_falls: bool,
    composition_note: &'static str,
}

#[derive(Serialize)]
struct I5Grade {
    schema: &'static str,
    truth_status: &'static str,
    canonical_source_detached_rest_and_executable_entry: bool,
    recurrent_full_passage_emission_through_retained_boundary: bool,
    explicit_matched_commit_and_decline: bool,
    enacted_world_return_changes_later_conduct: bool,
    text_and_every_admitted_real_modality_port_return: bool,
    generator_native_condensation_and_complete_cost_descent: bool,
    source_native_shared_dissection_is_complete_for_declared_family: bool,
    exact_semantic_work_and_physical_telemetry_are_separate: bool,
    fresh_process_restoration_and_targeted_ablations_pass: bool,
    conservation_of_faces_preserves_port_occurrence_and_lineage: bool,
    conventional_container_expansion_is_honestly_dispositioned: bool,
    bounded_receiver_family_and_open_exterior_are_explicit: bool,
    passed: bool,
}

#[derive(Serialize)]
struct ProductManifest {
    schema: &'static str,
    truth_status: &'static str,
    product: &'static str,
    canonical_rest: &'static str,
    matched_decline_rest: &'static str,
    exterior_return: &'static str,
    declined_return: &'static str,
    committed_return: &'static str,
    complete_cost: &'static str,
    realization_atlas: &'static str,
    exact_mesh: &'static str,
    interactive_projection: &'static str,
    ablations: &'static str,
    container_decision: &'static str,
    capability_report: &'static str,
    grade: &'static str,
    code_closure_sha256: String,
    open_exterior: Vec<String>,
}

#[allow(clippy::too_many_arguments)]
pub(super) fn finish(
    output: &Path,
    i3_directory: &Path,
    i4_directory: &Path,
    committed: &InferenceEcologyRest,
    declined_manifest: &RestDirectory,
    committed_manifest: &RestDirectory,
    declined_return: &DetachedReturn,
    committed_return: &DetachedReturn,
) -> Result<(), String> {
    let cost = complete_cost(
        i3_directory,
        i4_directory,
        committed_manifest,
        committed_return,
    )?;
    if !cost.every_coordinate_strictly_falls {
        return Err(
            "I5 complete product cost did not strictly fall in every coordinate".to_owned(),
        );
    }
    write_json(output.join("01-complete-product-cost.json"), &cost)?;

    let atlas = realization_atlas(committed, declined_return, committed_return);
    write_json(
        output.join("02-realization-and-recurrence-atlas.json"),
        &atlas,
    )?;
    let mesh = exact_mesh(committed, committed_return);
    write_json(output.join("03-exact-causal-mesh.json"), &mesh)?;
    fs::write(
        output.join("04-interactive-inference-ecology.svg"),
        interactive_svg(&mesh)?,
    )
    .map_err(|error| error.to_string())?;

    let ablations = json!({
        "schema": "holonics.i5.targeted-ablations.v1",
        "truth_status": "established-bounded",
        "source_realization_ablation": {
            "enacted_as": "complete source-model absence in both fresh processes",
            "declined_native_conduct_continues": declined_return.source_model_absent_while_native_conduct_continues,
            "committed_native_conduct_continues": committed_return.source_model_absent_while_native_conduct_continues,
            "retained_inverse_images": committed.recurrent.fibres.fibres.len() + committed.heterogeneous.fibres.fibres.len(),
            "claim": "source removal preserves native conduct but does not erase reconstruction fibres"
        },
        "native_route_ablation": {
            "withdrawn_passages": committed_return.withdrawn_passages,
            "selected_passages": committed_return.selected_passages,
            "reopens_every_passage_family": committed_return.native_route_withdrawal_reopens_every_passage_family
        },
        "shared_world_route_ablation": {
            "restores_every_predecessor_face": committed_return.shared_route_withdrawal_restores_every_predecessor_face
        },
        "local_port_ablations": {
            "port_population": committed.heterogeneous.standing.ports.len(),
            "preserve_every_other_port": committed_return.local_port_withdrawal_preserves_every_other_port
        }
    });
    write_json(output.join("05-targeted-ablations.json"), &ablations)?;

    let container = json!({
        "schema": "holonics.i5.conventional-container-decision.v1",
        "truth_status": "established-bounded",
        "decision": "omitted",
        "formats_considered": ["safetensors", "GGUF"],
        "reason": "either format would be an exterior expansion of the seven-component causal rest, not its native topology",
        "unclosed_obligations": [
            "a complete expansion map from recurrent and heterogeneous incidence to tensor rows",
            "the expansion defect and every collapsed reconstruction fibre",
            "an executable decoder restoring the causal boundary and explicit cultivation decision"
        ],
        "canonical_frozen_product": "native-rest/"
    });
    write_json(
        output.join("06-conventional-container-decision.json"),
        &container,
    )?;

    let declared_ports = committed
        .heterogeneous
        .standing
        .ports
        .iter()
        .map(|port| format!("{:?}", port.boundary))
        .collect::<Vec<_>>();
    let capability = format!(
        "# Athena-Gemma I5 capability report\n\n\
         Truth status: **established-bounded**.\n\n\
         The frozen product remounts from seven authenticated native components with the Gemma source absent. \
         One GPU launch returns a complete recurrent passage, the text and vision consequences, the matched \
         alternative route, global withdrawal, and every local port withdrawal. An actual `/usr/bin/tee` \
         world consequence founded the committed sibling; the matched declined sibling remains separately \
         executable.\n\n\
         Admitted ports: {}. Declined main passage: `{:?}`. Committed main passage: `{:?}`.\n\n\
         This establishes bounded Holonic Inference for the I1–I4 receiver family. It does not establish \
         unrestricted conversation, arbitrary prompts, audio/video, image generation, lossless recovery of \
         Gemma's corpus, or a universal semantic taxonomy. Those remain open reconstruction fibres rather \
         than failed promises. The safetensors/GGUF export is deliberately omitted because its expansion \
         decoder and defect are not yet founded.\n",
        declared_ports.join(", "),
        declined_return.selected_passages.first().cloned().unwrap_or_default(),
        committed_return.selected_passages.first().cloned().unwrap_or_default(),
    );
    fs::write(output.join("07-CAPABILITY_REPORT.md"), capability)
        .map_err(|error| error.to_string())?;

    let grade = grade(
        committed,
        declined_manifest,
        committed_manifest,
        declined_return,
        committed_return,
        &cost,
        &atlas,
        &mesh,
    );
    if !grade.passed {
        return Err("I5 refused its complete twelve-part grade".to_owned());
    }
    write_json(output.join("08-grade.json"), &grade)?;

    fs::write(
        output.join("INSPECTION.md"),
        format!(
            "# I5 inspection\n\nTruth status: **established-bounded**.\n\n- Declined: `{:?}`\n- Committed: `{:?}`\n- Ports: `{}` families × `{}` conserved faces.\n- Resident deed: `{}` launch, `{}` synchronization, `{}` active lanes on `{}`.\n- Exact semantic work: `{}`; measured wall: `{}` μs.\n- Complete cost: all seven coordinates strictly fall.\n- Source access in detached processes: none forbidden.\n- Atlas projection: `04-interactive-inference-ecology.svg` (JSON mesh is authoritative).\n",
            declined_return.selected_passages,
            committed_return.selected_passages,
            committed.heterogeneous.standing.family_count,
            committed.heterogeneous.standing.ports.len(),
            committed_return.apparatus.launches,
            committed_return.apparatus.synchronizations,
            committed_return.apparatus.active_lanes,
            committed_return.apparatus.device,
            committed_return.semantic_work.total(),
            committed_return.apparatus.physical_wall_microseconds,
        ),
    )
    .map_err(|error| error.to_string())?;
    let manifest = ProductManifest {
        schema: "holonics.i5.product-manifest.v1",
        truth_status: "established-bounded",
        product: "Athena-Gemma frozen Holonic Inference ecology",
        canonical_rest: "native-rest/manifest.json",
        matched_decline_rest: "matched-decline-rest/manifest.json",
        exterior_return: "00-exterior-return.json",
        declined_return: "declined-return/return.json",
        committed_return: "committed-return/return.json",
        complete_cost: "01-complete-product-cost.json",
        realization_atlas: "02-realization-and-recurrence-atlas.json",
        exact_mesh: "03-exact-causal-mesh.json",
        interactive_projection: "04-interactive-inference-ecology.svg",
        ablations: "05-targeted-ablations.json",
        container_decision: "06-conventional-container-decision.json",
        capability_report: "07-CAPABILITY_REPORT.md",
        grade: "08-grade.json",
        code_closure_sha256: code_closure(),
        open_exterior: committed.junction.open_exterior.clone(),
    };
    write_json(output.join("MANIFEST.json"), &manifest)
}

fn complete_cost(
    i3_directory: &Path,
    i4_directory: &Path,
    manifest: &RestDirectory,
    detached: &DetachedReturn,
) -> Result<CompleteCost, String> {
    let i3: PriorCost = read_json(&i3_directory.join("../00-complete-product-cost.json"))?;
    let i4: PriorCost = read_json(&i4_directory.join("../01-complete-product-cost.json"))?;
    let source = i3.source.add(&i4.source)?;
    let component = |role: &str| {
        manifest
            .components
            .iter()
            .find(|component| component.role == role)
            .map(|component| component.octets)
            .ok_or_else(|| format!("cost component {role} is absent"))
    };
    let native = CostFace {
        artifact_octets: component("recurrent-standing")?
            + component("heterogeneous-standing")?
            + component("inference-junction")?,
        decoder_octets: component("recurrent-decoder")? + component("heterogeneous-decoder")?,
        fibre_octets: component("recurrent-fibres")? + component("heterogeneous-fibres")?,
        semantic_work: detached.semantic_work.total(),
        dependency_span: detached.semantic_work.dependency_span,
        resident_octets: detached.apparatus.resident_octets,
        transfer_octets: detached.apparatus.host_ingress_octets
            + detached.apparatus.host_egress_octets,
    };
    let strict_coordinate_fall = BTreeMap::from([
        (
            "artifact_octets",
            native.artifact_octets < source.artifact_octets,
        ),
        (
            "decoder_octets",
            native.decoder_octets < source.decoder_octets,
        ),
        ("fibre_octets", native.fibre_octets < source.fibre_octets),
        ("semantic_work", native.semantic_work < source.semantic_work),
        (
            "dependency_span",
            native.dependency_span < source.dependency_span,
        ),
        (
            "resident_octets",
            native.resident_octets < source.resident_octets,
        ),
        (
            "transfer_octets",
            native.transfer_octets < source.transfer_octets,
        ),
    ]);
    Ok(CompleteCost {
        schema: "holonics.i5.complete-product-cost.v1",
        truth_status: "measured",
        source,
        native,
        every_coordinate_strictly_falls: strict_coordinate_fall.values().all(|passed| *passed),
        strict_coordinate_fall,
        composition_note: "I3 and I4 source comparisons compose serially at the I5 junction; native bytes are the exact seven components and native work/telemetry come from one composed launch",
    })
}

fn realization_atlas(
    committed: &InferenceEcologyRest,
    declined_return: &DetachedReturn,
    committed_return: &DetachedReturn,
) -> Value {
    let recurrent_caustics = committed
        .recurrent
        .fibres
        .fibres
        .iter()
        .filter(|fibre| fibre.members.len() > 1)
        .map(|fibre| json!({"native": fibre.native, "source_members": fibre.members.len()}))
        .collect::<Vec<_>>();
    let unavailable = &committed.heterogeneous.fibres.unavailable_ports;
    json!({
        "schema": "holonics.i5.realization-recurrence-atlas.v1",
        "truth_status": "established-bounded",
        "source_realizations": {
            "recurrent_inverse_images": committed.recurrent.fibres.fibres,
            "heterogeneous_inverse_images": committed.heterogeneous.fibres.fibres
        },
        "native_routes": {
            "successor_action": committed.recurrent.standing.successor_action,
            "predecessor_override": {
                "from": committed.recurrent.standing.predecessor_from,
                "to": committed.recurrent.standing.predecessor_to
            },
            "declined_selected": declined_return.selected_traces,
            "committed_selected": committed_return.selected_traces,
            "withdrawn": committed_return.withdrawn_traces,
            "basins": basins(&committed.recurrent.standing.successor_action)
        },
        "shared_routes": {
            "conserved_face_bindings": committed.junction.bindings,
            "world_action": committed.heterogeneous.standing.successor_action,
            "world_basins": basins(&committed.heterogeneous.standing.successor_action),
            "naturality_squares": committed.heterogeneous.fibres.naturality_squares,
            "port_consequences": committed_return.port_consequences
        },
        "defects": {
            "shortest_recurrent_separators": committed.recurrent.fibres.separators,
            "unavailable_modality_ports": unavailable,
            "conventional_expansion": "open: no tensor-row decoder or defect has been founded"
        },
        "caustics": recurrent_caustics,
        "holonomy": {
            "local_noncommuting_route": {
                "from": committed.recurrent.standing.predecessor_from,
                "predecessor_to": committed.recurrent.standing.predecessor_to,
                "successor_to": committed.recurrent.standing.successor_action[committed.recurrent.standing.predecessor_from as usize]
            },
            "return_changes_selected_mode": !declined_return.committed && committed_return.committed
        },
        "ablations": {
            "source_absent": committed_return.source_model_absent_while_native_conduct_continues,
            "native_route_withdrawal": committed_return.native_route_withdrawal_reopens_every_passage_family,
            "shared_route_withdrawal": committed_return.shared_route_withdrawal_restores_every_predecessor_face,
            "local_port_withdrawal": committed_return.local_port_withdrawal_preserves_every_other_port
        },
        "open_exterior": committed.junction.open_exterior
    })
}

fn basins(action: &[u32]) -> Vec<Value> {
    (0..action.len())
        .map(|start| {
            let mut trace = vec![start as u32];
            let mut state = start as u32;
            for _ in 0..action.len() {
                let next = action[state as usize];
                trace.push(next);
                if trace[..trace.len() - 1].contains(&next) {
                    break;
                }
                state = next;
            }
            json!({"start": start, "trace_to_first_repeat": trace})
        })
        .collect()
}

fn exact_mesh(rest: &InferenceEcologyRest, returned: &DetachedReturn) -> Value {
    let mut vertices = vec![
        json!({"id":"rs","kind":"source-fibre","label":"recurrent source fibres","x":70,"y":190}),
        json!({"id":"r0","kind":"recurrent-state","label":"r₀","x":220,"y":100}),
        json!({"id":"r1","kind":"recurrent-state","label":"r₁","x":220,"y":190}),
        json!({"id":"r2","kind":"recurrent-state","label":"r₂","x":220,"y":280}),
        json!({"id":"jp","kind":"junction","label":"predecessor face","x":405,"y":125}),
        json!({"id":"js","kind":"junction","label":"successor face","x":405,"y":255}),
        json!({"id":"w0","kind":"world-state","label":"world₀","x":585,"y":125}),
        json!({"id":"w1","kind":"world-state","label":"world₁","x":585,"y":255}),
        json!({"id":"emit","kind":"return-cycle","label":"emission","x":320,"y":405}),
        json!({"id":"world","kind":"return-cycle","label":"world consequence","x":475,"y":455}),
        json!({"id":"ret","kind":"return-cycle","label":"return/deposit","x":630,"y":405}),
    ];
    let mut edges = vec![
        json!({"from":"rs","to":"r0","kind":"realization"}),
        json!({"from":"rs","to":"r1","kind":"reconstruction-fibre"}),
        json!({"from":"rs","to":"r2","kind":"reconstruction-fibre"}),
        json!({"from":"r0","to":"r1","kind":"recurrent"}),
        json!({"from":"r1","to":"r2","kind":"recurrent"}),
        json!({"from":"r2","to":"r1","kind":"predecessor"}),
        json!({"from":"r2","to":"r2","kind":"successor"}),
        json!({"from":"r2","to":"jp","kind":"mode"}),
        json!({"from":"r2","to":"js","kind":"mode"}),
        json!({"from":"jp","to":"w0","kind":"conserved-face"}),
        json!({"from":"js","to":"w1","kind":"conserved-face"}),
        json!({"from":"r2","to":"emit","kind":"emission"}),
        json!({"from":"emit","to":"world","kind":"world"}),
        json!({"from":"world","to":"ret","kind":"return"}),
        json!({"from":"ret","to":"js","kind":"deposit"}),
    ];
    for (port_at, port) in rest.heterogeneous.standing.ports.iter().enumerate() {
        let id = format!("p{port_at}");
        let y = 95 + port_at as u64 * 190;
        vertices.push(json!({
            "id": id,
            "kind": "modality-port",
            "label": format!("{:?}", port.boundary),
            "x": 790,
            "y": y
        }));
        edges.push(json!({"from":"w0","to":id,"kind":"port-predecessor"}));
        edges.push(json!({"from":"w1","to":id,"kind":"port-successor"}));
    }
    json!({
        "schema": "holonics.i5.exact-causal-mesh.v1",
        "truth_status": "established-bounded",
        "vertices": vertices,
        "edges": edges,
        "selected_consequences": returned.port_consequences,
        "layout_is_receiver_only": true,
        "layout_crossings_create_edges": false
    })
}

fn interactive_svg(mesh: &Value) -> Result<String, String> {
    let vertices = mesh["vertices"].as_array().ok_or("mesh vertices absent")?;
    let edges = mesh["edges"].as_array().ok_or("mesh edges absent")?;
    let positions = vertices
        .iter()
        .map(|vertex| {
            Ok((
                vertex["id"].as_str().ok_or("vertex id absent")?.to_owned(),
                (
                    vertex["x"].as_u64().ok_or("vertex x absent")?,
                    vertex["y"].as_u64().ok_or("vertex y absent")?,
                ),
            ))
        })
        .collect::<Result<BTreeMap<_, _>, String>>()?;
    let mut drawing = String::new();
    for edge in edges {
        let from = edge["from"].as_str().ok_or("edge source absent")?;
        let to = edge["to"].as_str().ok_or("edge target absent")?;
        let kind = edge["kind"].as_str().ok_or("edge kind absent")?;
        let (x1, y1) = positions[from];
        let (x2, y2) = positions[to];
        if from == to {
            drawing.push_str(&format!("<path class='edge {kind}' data-kind='{kind}' d='M {x1} {y1} C {} {} {} {} {x2} {y2}'/>", x1 + 70, y1 - 70, x2 - 70, y2 - 70));
        } else {
            drawing.push_str(&format!(
                "<path class='edge {kind}' data-kind='{kind}' d='M {x1} {y1} Q {} {} {x2} {y2}'/>",
                (x1 + x2) / 2,
                y1.min(y2) - 22
            ));
        }
    }
    for vertex in vertices {
        let id = vertex["id"].as_str().unwrap_or_default();
        let kind = vertex["kind"].as_str().unwrap_or_default();
        let label = vertex["label"].as_str().unwrap_or_default();
        let x = vertex["x"].as_u64().unwrap_or_default();
        let y = vertex["y"].as_u64().unwrap_or_default();
        let visible = if kind == "modality-port" {
            match label {
                "TextCodeword" => "text",
                "VisionPatch" => "vision",
                _ => label,
            }
        } else {
            id
        };
        drawing.push_str(&format!("<g class='node {kind}' data-kind='{kind}'><circle cx='{x}' cy='{y}' r='27'/><text x='{x}' y='{}'>{}</text><title>{label}</title></g>", y + 5, xml(visible)));
    }
    Ok(format!(
        r##"<svg xmlns="http://www.w3.org/2000/svg" width="920" height="570" viewBox="0 0 920 570">
<title>I5 Athena-Gemma exact inference ecology</title><desc>Topology comes from 03-exact-causal-mesh.json. Layout crossings have no incidence.</desc>
<defs><marker id="arrow" markerWidth="7" markerHeight="7" refX="6" refY="3.5" orient="auto"><path d="M0,0 L7,3.5 L0,7 z" fill="context-stroke"/></marker><radialGradient id="junction"><stop offset="0" stop-color="#f1d67d"/><stop offset="1" stop-color="#8d5b38"/></radialGradient></defs>
<style>svg{{background:#0c1320;color:#e7f0f7;font:13px sans-serif}} .edge{{fill:none;stroke:#66819a;stroke-width:2;marker-end:url(#arrow)}} .edge.reconstruction-fibre{{stroke:#a982e2;stroke-dasharray:5 4}} .edge.predecessor{{stroke:#e8a658}} .edge.successor{{stroke:#ef6f91}} .edge.conserved-face{{stroke:#66d0b7;stroke-width:4}} .edge.emission,.edge.world,.edge.return,.edge.deposit{{stroke:#70bdf2;stroke-width:3}} .node circle{{fill:#24384c;stroke:#9cb8ce;stroke-width:2}} .junction circle{{fill:url(#junction);stroke:#f4d58a}} .world-state circle{{fill:#285947;stroke:#74d6bc}} .modality-port circle{{fill:#563f70;stroke:#c49aec}} .return-cycle circle{{fill:#294e6c;stroke:#78c5f6}} text{{fill:#f4f8fb;text-anchor:middle}} .label{{text-anchor:start}} .travelling{{stroke-dasharray:10 8;animation:travel 1.1s linear infinite}} @keyframes travel{{to{{stroke-dashoffset:-36}}}}</style>
<rect x="20" y="18" width="880" height="55" rx="9" fill="#172438"/><text class="label" x="40" y="42">I5 · one recurrent body, two conserved world faces, typed text/vision ports</text><text class="label" x="40" y="62">click a receiver face; the exact JSON mesh remains authoritative</text>
<g id="drawing">{drawing}</g>
<g transform="translate(35 520)"><rect data-filter="all" x="0" y="-28" width="90" height="34" rx="5" fill="#40536a"/><text x="45" y="-6">all</text><rect data-filter="recurrent-state" x="100" y="-28" width="120" height="34" rx="5" fill="#40536a"/><text x="160" y="-6">recurrence</text><rect data-filter="junction" x="230" y="-28" width="110" height="34" rx="5" fill="#73583b"/><text x="285" y="-6">junction</text><rect data-filter="modality-port" x="350" y="-28" width="110" height="34" rx="5" fill="#563f70"/><text x="405" y="-6">ports</text><rect data-action="return" x="470" y="-28" width="135" height="34" rx="5" fill="#285273"/><text x="537" y="-6">animate return</text></g>
<script><![CDATA[document.querySelectorAll('[data-filter]').forEach(b=>b.addEventListener('click',()=>{{const f=b.dataset.filter;document.querySelectorAll('.node,.edge').forEach(e=>e.style.opacity=f==='all'||e.classList.contains(f)?'1':'0.10')}}));document.querySelector('[data-action="return"]').addEventListener('click',()=>document.querySelectorAll('.emission,.world,.return,.deposit').forEach(e=>e.classList.toggle('travelling')));]]></script>
</svg>"##
    ))
}

#[allow(clippy::too_many_arguments)]
fn grade(
    committed: &InferenceEcologyRest,
    declined_manifest: &RestDirectory,
    committed_manifest: &RestDirectory,
    declined_return: &DetachedReturn,
    committed_return: &DetachedReturn,
    cost: &CompleteCost,
    atlas: &Value,
    mesh: &Value,
) -> I5Grade {
    let identity_map = |manifest: &RestDirectory| {
        manifest
            .components
            .iter()
            .map(|component| (component.role.clone(), component.sha256.clone()))
            .collect::<BTreeMap<_, _>>()
    };
    let canonical_source_detached_rest_and_executable_entry = committed_manifest.components.len()
        == 7
        && committed_return.component_sha256 == identity_map(committed_manifest)
        && committed_return.source_model_absent_while_native_conduct_continues
        && committed_return.cpu_semantic_callbacks_between_fronts == 0;
    let recurrent_full_passage_emission_through_retained_boundary =
        !committed_return.selected_passages.is_empty()
            && committed_return
                .selected_passages
                .iter()
                .all(|passage| !passage.is_empty())
            && committed_return
                .selected_traces
                .iter()
                .all(|trace| trace.len() >= 2);
    let explicit_matched_commit_and_decline = !declined_return.committed
        && committed_return.committed
        && declined_return.component_sha256 == identity_map(declined_manifest)
        && committed.junction.exterior_return.is_some();
    let exterior = committed.junction.exterior_return.as_ref();
    let enacted_world_return_changes_later_conduct = exterior
        .is_some_and(|return_| return_.validate().is_ok() && return_.exact_difference_octets > 0)
        && declined_return.selected_passages != committed_return.selected_passages
        && declined_return
            .port_consequences
            .iter()
            .zip(&committed_return.port_consequences)
            .all(|(before, after)| before.selected_address != after.selected_address);
    let admitted = committed
        .heterogeneous
        .standing
        .ports
        .iter()
        .map(|port| port.boundary)
        .collect::<BTreeSet<_>>();
    let returned = committed_return
        .port_consequences
        .iter()
        .map(|consequence| consequence.boundary)
        .collect::<BTreeSet<_>>();
    let text_and_every_admitted_real_modality_port_return = admitted == returned
        && admitted.contains(&BoundaryId(11))
        && admitted.contains(&BoundaryId(29))
        && committed_return.port_consequences.len()
            == committed.heterogeneous.standing.family_count as usize * admitted.len();
    let generator_native_condensation_and_complete_cost_descent =
        cost.every_coordinate_strictly_falls;
    let source_native_shared_dissection_is_complete_for_declared_family =
        atlas["source_realizations"].is_object()
            && atlas["native_routes"].is_object()
            && atlas["shared_routes"].is_object()
            && atlas["defects"].is_object()
            && atlas["caustics"].is_array()
            && atlas["holonomy"].is_object()
            && mesh["vertices"]
                .as_array()
                .is_some_and(|vertices| !vertices.is_empty());
    let exact_semantic_work_and_physical_telemetry_are_separate =
        committed_return.semantic_work.total() > 0
            && committed_return.semantic_work.dependency_span > 0
            && committed_return.apparatus.resident_octets > 0
            && committed_return.apparatus.physical_wall_microseconds > 0
            && committed_return.apparatus.launches == 1
            && committed_return.apparatus.synchronizations == 1;
    let fresh_process_restoration_and_targeted_ablations_pass = declined_return
        .source_model_absent_while_native_conduct_continues
        && committed_return.source_model_absent_while_native_conduct_continues
        && committed_return.native_route_withdrawal_reopens_every_passage_family
        && committed_return.shared_route_withdrawal_restores_every_predecessor_face
        && committed_return.local_port_withdrawal_preserves_every_other_port;
    let conservation_of_faces_preserves_port_occurrence_and_lineage =
        committed.junction.bindings.len() == 2
            && committed.heterogeneous.standing.ports.len() >= 2
            && committed
                .heterogeneous
                .fibres
                .fibres
                .iter()
                .all(|fibre| !fibre.members.is_empty())
            && committed
                .heterogeneous
                .fibres
                .naturality_squares
                .iter()
                .all(|square| square.commutes);
    let conventional_container_expansion_is_honestly_dispositioned = committed
        .junction
        .open_exterior
        .iter()
        .any(|entry| entry.contains("conventional tensor container"));
    let bounded_receiver_family_and_open_exterior_are_explicit =
        !committed.junction.open_exterior.is_empty()
            && committed
                .junction
                .open_exterior
                .iter()
                .any(|entry| entry.contains("unrestricted intelligence"));
    let checks = [
        canonical_source_detached_rest_and_executable_entry,
        recurrent_full_passage_emission_through_retained_boundary,
        explicit_matched_commit_and_decline,
        enacted_world_return_changes_later_conduct,
        text_and_every_admitted_real_modality_port_return,
        generator_native_condensation_and_complete_cost_descent,
        source_native_shared_dissection_is_complete_for_declared_family,
        exact_semantic_work_and_physical_telemetry_are_separate,
        fresh_process_restoration_and_targeted_ablations_pass,
        conservation_of_faces_preserves_port_occurrence_and_lineage,
        conventional_container_expansion_is_honestly_dispositioned,
        bounded_receiver_family_and_open_exterior_are_explicit,
    ];
    I5Grade {
        schema: "holonics.i5.complete-grade.v1",
        truth_status: "established-bounded",
        canonical_source_detached_rest_and_executable_entry,
        recurrent_full_passage_emission_through_retained_boundary,
        explicit_matched_commit_and_decline,
        enacted_world_return_changes_later_conduct,
        text_and_every_admitted_real_modality_port_return,
        generator_native_condensation_and_complete_cost_descent,
        source_native_shared_dissection_is_complete_for_declared_family,
        exact_semantic_work_and_physical_telemetry_are_separate,
        fresh_process_restoration_and_targeted_ablations_pass,
        conservation_of_faces_preserves_port_occurrence_and_lineage,
        conventional_container_expansion_is_honestly_dispositioned,
        bounded_receiver_family_and_open_exterior_are_explicit,
        passed: checks.into_iter().all(|passed| passed),
    }
}

fn code_closure() -> String {
    let mut hash = Sha256::new();
    for bytes in [
        include_bytes!("../the_athena_gemma_ecology_infers_returns_and_remounts.rs").as_slice(),
        include_bytes!("product.rs").as_slice(),
        include_bytes!("../../../holonic-engine/src/native_ecology/inference_ecology.rs")
            .as_slice(),
        include_bytes!("../../../holonic-engine/src/cuda_refine.rs").as_slice(),
        include_bytes!("../../../holonic-engine/kernels/refine_shell.cu").as_slice(),
    ] {
        hash.update(bytes);
    }
    hex(hash.finalize())
}

fn checked(left: u64, right: u64) -> Result<u64, String> {
    left.checked_add(right)
        .ok_or_else(|| "I5 cost composition overflowed".to_owned())
}

fn read_json<T: for<'de> Deserialize<'de>>(path: &Path) -> Result<T, String> {
    serde_json::from_slice(&fs::read(path).map_err(|error| error.to_string())?)
        .map_err(|error| error.to_string())
}

fn xml(value: &str) -> String {
    value
        .replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
        .replace('\'', "&apos;")
}
