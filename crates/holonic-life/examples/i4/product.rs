//! I4 inspection products. The JSON mesh is authoritative; SVG coordinates are a receiver chart.

use std::collections::BTreeMap;

use holonic_engine::native_ecology::heterogeneous_fusion::HeterogeneousFusionRest;
use serde_json::{json, Value};

use super::source::SourceConduct;
use super::{CostProduct, DetachedReturn};

pub fn atlas(
    source: &SourceConduct,
    rest: &HeterogeneousFusionRest,
    detached: &DetachedReturn,
) -> Result<Value, String> {
    let ports = rest.standing.ports.len();
    let mut pullbacks = Vec::new();
    for family in 0..rest.standing.family_count as usize {
        for state in 0..rest.standing.state_count as usize {
            let base = family * ports * rest.standing.state_count as usize;
            let text = base + state;
            let vision = base + rest.standing.state_count as usize + state;
            pullbacks.push(json!({
                "family": family,
                "state": state,
                "text_native_address": text,
                "vision_native_address": vision,
                "world_receiver": rest.standing.shared_generator.common_world_receiver,
                "identity_law": "same addressed M0 source-parameter passage; occurrence and source consequence remain distinct",
                "truth_status": "established-bounded"
            }));
        }
    }
    let source_responses = rest
        .decoder
        .consequences
        .iter()
        .map(|native| {
            let response = source
                .responses
                .iter()
                .find(|response| {
                    response.family == native.family
                        && response.state == native.state
                        && response.boundary == native.boundary
                })
                .ok_or_else(|| {
                    format!(
                        "source response for family {} port {:?} state {} is absent",
                        native.family, native.boundary, native.state
                    )
                })?;
            Ok(json!({
                "family": response.family,
                "state": response.state,
                "boundary": response.boundary,
                "occurrence": response.occurrence,
                "occurrence_sha256": response.occurrence_sha256,
                "source_consequence_sha256": response.consequence_sha256,
                "incidence_sha256": response.incidence_sha256,
                "semantic_units": response.semantic_units,
                "truth_status": "implemented-exact"
            }))
        })
        .collect::<Result<Vec<_>, String>>()?;
    let native = rest
        .decoder
        .consequences
        .iter()
        .map(|consequence| {
            json!({
                "address": consequence.address,
                "family": consequence.family,
                "state": consequence.state,
                "boundary": consequence.boundary,
                "source_consequence_sha256": consequence.source_consequence_sha256,
                "source_incidence_sha256": consequence.source_incidence_sha256,
                "truth_status": "established-bounded"
            })
        })
        .collect::<Vec<_>>();
    Ok(json!({
        "schema": "holonics.i4.multimodal-realization-atlas.v1",
        "truth_status": "established-bounded",
        "source_model_sha256": source.source_model_sha256,
        "ports": rest.standing.ports,
        "shared_generator": rest.standing.shared_generator,
        "source_responses": source_responses,
        "native_consequences": native,
        "correspondence_pullbacks": pullbacks,
        "naturality_squares": rest.fibres.naturality_squares,
        "reconstruction_fibres": rest.fibres.fibres,
        "resident_routes": {
            "predecessor": detached.predecessor_addresses,
            "successor": detached.successor_addresses,
            "shared_ablated": detached.shared_ablated_addresses,
            "local_ablated": detached.local_ablated_addresses,
        },
        "conservation_of_faces": {
            "shared": "world-state generator only",
            "conserved": ["occurrence lineage", "typed port", "serial/spatial incidence", "source consequence", "receiver family", "reconstruction member"],
            "forbidden_identifications": ["equal transcript", "equal label", "equal source digest", "co-presence in one embedding stream"]
        },
        "unavailable_ports": rest.fibres.unavailable_ports,
        "open_exterior": rest.standing.open_exterior,
    }))
}

pub fn mesh(atlas: &Value) -> Result<Value, String> {
    let responses = atlas["source_responses"]
        .as_array()
        .ok_or("I4 atlas has no source responses")?;
    let native = atlas["native_consequences"]
        .as_array()
        .ok_or("I4 atlas has no native consequences")?;
    if responses.len() != native.len() {
        return Err("I4 source/native mesh populations disagree".to_owned());
    }
    let mut vertices = Vec::new();
    let mut edges = Vec::new();
    vertices.push(json!({"id":"g","kind":"shared-generator","x":450,"y":250}));
    for (at, (source, native)) in responses.iter().zip(native).enumerate() {
        let port = source["port"].as_str().ok_or("source port absent")?;
        let family = source["family"].as_u64().ok_or("source family absent")?;
        let state = source["state"].as_u64().ok_or("source state absent")?;
        let column = if port == "text-codeword" { 0 } else { 1 };
        let x = 115 + column * 670;
        let y = 105 + family * 190 + state * 70;
        let source_id = format!("s{at}");
        let native_id = format!("n{at}");
        vertices.push(json!({
            "id":source_id,"kind":"source-occurrence","port":port,"family":family,"state":state,
            "x":x,"y":y,"occurrence":source["occurrence"]
        }));
        vertices.push(json!({
            "id":native_id,"kind":"native-consequence","port":port,"family":family,"state":state,
            "x": if column == 0 {330} else {570},"y":y,"address":native["address"]
        }));
        edges.push(json!({"from":source_id,"to":native_id,"kind":"realization-passage","port":port,"family":family}));
        edges.push(json!({"from":native_id,"to":format!("s{at}"),"kind":"reconstruction-fibre","port":port,"family":family}));
        if state == 0 {
            edges.push(json!({"from":format!("n{at}"),"to":format!("n{}",at+1),"kind":"shared-transport","port":port,"family":family}));
            edges.push(json!({"from":"g","to":format!("n{}",at+1),"kind":"generator-incidence","port":port,"family":family}));
        }
    }
    let pullbacks = atlas["correspondence_pullbacks"]
        .as_array()
        .ok_or("I4 atlas has no pullbacks")?;
    for pullback in pullbacks {
        edges.push(json!({
            "from":format!("n{}", pullback["text_native_address"].as_u64().ok_or("text address absent")?),
            "to":format!("n{}", pullback["vision_native_address"].as_u64().ok_or("vision address absent")?),
            "kind":"world-pullback",
            "family":pullback["family"],
            "state":pullback["state"]
        }));
    }
    Ok(json!({
        "schema":"holonics.i4.exact-mesh.v1",
        "truth_status":"established-bounded",
        "vertices":vertices,
        "edges":edges,
        "layout_notice":"x/y are projection coordinates only; the edge list is the exact incidence",
    }))
}

pub fn ablations(rest: &HeterogeneousFusionRest, detached: &DetachedReturn) -> Value {
    json!({
        "schema":"holonics.i4.ablations.v1",
        "truth_status":"established-bounded",
        "shared_generator":rest.standing.shared_generator.name,
        "predecessor":detached.predecessor_addresses,
        "successor":detached.successor_addresses,
        "shared_withdrawal":detached.shared_ablated_addresses,
        "single_port_withdrawals":detached.local_ablated_addresses,
        "shared_withdrawal_moves_both_ports":detached.shared_generator_ablation_moves_both_ports,
        "single_port_withdrawal_moves_only_declared_port":detached.modality_specific_ablation_moves_only_declared_port,
        "held_out_family_requires_shared_ecology":detached.held_out_cross_port_consequence_requires_shared_ecology,
    })
}

pub fn interactive_svg(atlas: &Value, mesh: &Value) -> Result<String, String> {
    let vertices = mesh["vertices"].as_array().ok_or("mesh vertices absent")?;
    let edges = mesh["edges"].as_array().ok_or("mesh edges absent")?;
    let mut positions = BTreeMap::new();
    for vertex in vertices {
        positions.insert(
            vertex["id"].as_str().ok_or("vertex id absent")?,
            (
                vertex["x"].as_u64().ok_or("vertex x absent")?,
                vertex["y"].as_u64().ok_or("vertex y absent")?,
            ),
        );
    }
    let mut drawing = String::new();
    for edge in edges {
        let from = edge["from"].as_str().ok_or("edge from absent")?;
        let to = edge["to"].as_str().ok_or("edge to absent")?;
        let kind = edge["kind"].as_str().ok_or("edge kind absent")?;
        let port = edge["port"].as_str().unwrap_or("shared");
        let family = edge["family"].as_u64().unwrap_or(9);
        let (x1, y1) = positions[from];
        let (x2, y2) = positions[to];
        let path = if kind == "world-pullback" {
            format!("M{x1},{y1} Q450,{} {x2},{y2}", y1.saturating_sub(45))
        } else if from == to {
            format!(
                "M{x1},{} C{},{} {},{} {x1},{}",
                y1 - 16,
                x1 + 48,
                y1 - 55,
                x1 - 48,
                y1 - 55,
                y1 - 16
            )
        } else {
            format!("M{x1},{y1} L{x2},{y2}")
        };
        drawing.push_str(&format!("<path class='edge {kind} port-{port} family-{family}' data-kind='{kind}' data-port='{port}' data-family='{family}' d='{path}'/>"));
    }
    for vertex in vertices {
        let id = vertex["id"].as_str().unwrap_or_default();
        let kind = vertex["kind"].as_str().unwrap_or_default();
        let port = vertex["port"].as_str().unwrap_or("shared");
        let family = vertex["family"].as_u64().unwrap_or(9);
        let state = vertex["state"].as_u64().unwrap_or(9);
        let x = vertex["x"].as_u64().unwrap_or_default();
        let y = vertex["y"].as_u64().unwrap_or_default();
        drawing.push_str(&format!("<g class='node {kind} port-{port} family-{family} state-{state}' data-port='{port}' data-family='{family}' data-state='{state}'><circle cx='{x}' cy='{y}' r='19'/><text x='{x}' y='{}'>{id}</text></g>",y+5));
    }
    let squares = atlas["naturality_squares"].as_array().map_or(0, Vec::len);
    Ok(format!(
        r##"<svg xmlns="http://www.w3.org/2000/svg" width="900" height="590" viewBox="0 0 900 590">
<title>I4 exact heterogeneous realization atlas</title><desc>The edge list in 03-exact-mesh.json is authoritative. Layout crossings carry no incidence.</desc>
<defs><marker id="arrow" markerWidth="7" markerHeight="7" refX="6" refY="3.5" orient="auto"><path d="M0,0 L7,3.5 L0,7 z" fill="context-stroke"/></marker></defs>
<style>svg{{background:#0d1520;color:#e4edf4;font:13px sans-serif}}.edge{{fill:none;stroke:#6d8193;stroke-width:2;marker-end:url(#arrow)}}.realization-passage{{stroke:#65c3ac}}.reconstruction-fibre{{stroke:#a982db;stroke-dasharray:5 4;marker-end:none}}.shared-transport{{stroke:#efad55;stroke-width:3}}.generator-incidence{{stroke:#e2668d;stroke-dasharray:3 4}}.world-pullback{{stroke:#5cb5e8;stroke-width:3}}.node circle{{fill:#213143;stroke:#9eb5c8;stroke-width:2}}.source-occurrence circle{{fill:#29443d}}.native-consequence circle{{fill:#273e58}}.shared-generator circle{{fill:#70445a;stroke:#f087aa}}text{{fill:#eef5fa;text-anchor:middle}}.label{{text-anchor:start}}[data-filter],[data-action]{{cursor:pointer}}.withdrawn{{opacity:.16}}.pulse{{stroke-dasharray:8 7;animation:flow 1.1s linear infinite}}@keyframes flow{{to{{stroke-dashoffset:-30}}}}</style>
<rect x="18" y="14" width="864" height="61" rx="8" fill="#172334"/><text class="label" x="35" y="39">I4 · one shared world generator · {squares} exact naturality squares</text><text class="label" x="35" y="60">faces are conserved fibrewise; text and vision are never identified</text>
<g id="drawing">{drawing}</g>
<g transform="translate(25 475)"><text class="label" x="0" y="0">receiver:</text><rect data-filter="all" x="75" y="-22" width="72" height="30" rx="5" fill="#435269"/><text x="111" y="0">all</text><rect data-filter="text-codeword" x="158" y="-22" width="105" height="30" rx="5" fill="#315b50"/><text x="210" y="0">text</text><rect data-filter="vision-patch" x="274" y="-22" width="105" height="30" rx="5" fill="#315575"/><text x="326" y="0">vision</text><rect data-filter="family-0" x="390" y="-22" width="120" height="30" rx="5" fill="#67513c"/><text x="450" y="0">development</text><rect data-filter="family-1" x="521" y="-22" width="105" height="30" rx="5" fill="#574875"/><text x="573" y="0">held-out</text></g>
<g transform="translate(25 535)"><text class="label" x="0" y="0">intervention:</text><rect data-action="shared" x="92" y="-22" width="142" height="30" rx="5" fill="#70445a"/><text x="163" y="0">withdraw shared</text><rect data-action="text" x="245" y="-22" width="132" height="30" rx="5" fill="#315b50"/><text x="311" y="0">withdraw text</text><rect data-action="vision" x="388" y="-22" width="142" height="30" rx="5" fill="#315575"/><text x="459" y="0">withdraw vision</text><rect data-action="flow" x="541" y="-22" width="110" height="30" rx="5" fill="#3d5368"/><text x="596" y="0">animate</text></g>
<script><![CDATA[const items=[...document.querySelectorAll('.node,.edge')];document.querySelectorAll('[data-filter]').forEach(b=>b.addEventListener('click',()=>{{const f=b.dataset.filter;items.forEach(e=>e.style.opacity=f==='all'||e.classList.contains(f)||e.classList.contains('shared-generator')?'1':'.10')}}));function clear(){{items.forEach(e=>e.classList.remove('withdrawn'))}}document.querySelector('[data-action="shared"]').addEventListener('click',()=>{{clear();document.querySelectorAll('.shared-transport,.generator-incidence,.state-1').forEach(e=>e.classList.add('withdrawn'))}});document.querySelector('[data-action="text"]').addEventListener('click',()=>{{clear();document.querySelectorAll('.port-text-codeword.shared-transport,.port-text-codeword.state-1').forEach(e=>e.classList.add('withdrawn'))}});document.querySelector('[data-action="vision"]').addEventListener('click',()=>{{clear();document.querySelectorAll('.port-vision-patch.shared-transport,.port-vision-patch.state-1').forEach(e=>e.classList.add('withdrawn'))}});document.querySelector('[data-action="flow"]').addEventListener('click',()=>document.querySelectorAll('.shared-transport,.world-pullback').forEach(e=>e.classList.toggle('pulse')));]]></script></svg>"##
    ))
}

pub fn inspection(
    source: &SourceConduct,
    detached: &DetachedReturn,
    costs: &CostProduct,
) -> String {
    format!(
        "# I4 inspection\n\n- Real source responses: {} (two ports × two states × two receiver families).\n- Development crop: `({}, {}, {})`, derived only from the source-render intervention; held-out changed pixels: {}.\n- Exact vision multiply-accumulates: {} on `{}`.\n- Native return: one launch, one synchronization, {} active modality/family lanes.\n- Shared withdrawal moved both ports: {}.\n- Single-port withdrawals remained local: {}.\n- Held-out PDF-raster pullback required the shared state passage: {}.\n- Complete cost vector strictly fell: {}.\n\nThe full vision/text tower interiors, audio and video remain explicit open fibres. This product proves bounded heterogeneous entry-port fusion; it does not claim full multimodal answer generation.\n",
        source.responses.len(),
        source.crop_found_from_development_pair_only.x,
        source.crop_found_from_development_pair_only.y,
        source.crop_found_from_development_pair_only.side,
        source.changed_held_out_pixels,
        source.apparatus.exact_multiply_accumulates,
        source.apparatus.resident_chart,
        detached.apparatus.active_lanes,
        detached.shared_generator_ablation_moves_both_ports,
        detached.modality_specific_ablation_moves_only_declared_port,
        detached.held_out_cross_port_consequence_requires_shared_ecology,
        costs.every_coordinate_strictly_falls,
    )
}
