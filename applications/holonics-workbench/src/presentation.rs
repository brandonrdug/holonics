use num_bigint::{BigInt, Sign};
use serde_json::Value;

use crate::{EventLevel, WorkbenchEvent};

pub fn summary(event: &WorkbenchEvent) -> String {
    if event.subject.starts_with("workspace/") {
        return workspace_summary(event);
    }
    if event.subject.ends_with("/diffusion") {
        return diffusion_summary(event);
    }
    let mut lines = event_heading(event);
    if let Some(payload) = &event.payload {
        for key in [
            "session",
            "workspace_root",
            "current_snapshot",
            "generation",
            "path",
            "octets",
            "foreign_execution",
            "tensor_population",
            "nodes",
            "constituents",
            "contacts",
        ] {
            if let Some(value) = payload.get(key).filter(|value| scalar(value)) {
                lines.push(format!("{:<20} {}", humanize(key), exact_value(value)));
            }
        }
        if let Some(written) = payload.get("written_artifacts").and_then(Value::as_array) {
            if !written.is_empty() {
                lines.push(String::new());
                lines.push("WRITTEN ARTIFACTS".to_owned());
                lines.extend(written.iter().map(exact_value));
            }
        }
        if let Some(value) = payload.get("value") {
            for key in ["generation", "ordinal", "experiment", "foreign_execution"] {
                if let Some(field) = value.get(key).filter(|field| scalar(field)) {
                    lines.push(format!("{:<20} {}", humanize(key), exact_value(field)));
                }
            }
        }
        if let Some(anatomy) = payload.get("anatomy") {
            lines.push(String::new());
            lines.push("MORPHOLOGY".to_owned());
            for key in [
                "native_population",
                "thread_population",
                "spool_population",
                "receiver_population",
                "open_obligation_population",
                "cycle_rank",
                "incidence_rank",
            ] {
                if let Some(value) = anatomy.get(key) {
                    lines.push(format!("{:<24} {}", humanize(key), exact_value(value)));
                }
            }
        }
        if let Some(successors) = payload.get("actual_successors").and_then(Value::as_array) {
            lines.push(format!("{:<20} {}", "Actual successors", successors.len()));
        }
        if let Some(obligations) = payload.get("open_obligations").and_then(Value::as_array) {
            lines.push(format!("{:<20} {}", "Open obligations", obligations.len()));
        }
    }
    lines.join("\n")
}

fn workspace_summary(event: &WorkbenchEvent) -> String {
    let mut lines = event_heading(event);
    let Some(payload) = event.payload.as_ref() else {
        return lines.join("\n");
    };
    lines.push(String::new());
    lines.push("WORKSPACE".to_owned());
    push_field(&mut lines, "Root", payload.get("workspace_root"));
    push_field(
        &mut lines,
        "Current snapshot",
        payload.get("current_snapshot"),
    );
    let value = payload.get("value").unwrap_or(&Value::Null);
    match event.subject.as_str() {
        "workspace/create" | "workspace/inspect" => {
            let manifest = value.get("manifest").unwrap_or(value);
            workspace_manifest(&mut lines, manifest);
            if let Some(active) = value.get("active").filter(|item| !item.is_null()) {
                circulation_summary(&mut lines, active);
            }
        }
        "workspace/lift-gemma-receipt" => lift_summary(&mut lines, value),
        "workspace/import-snapshot" => import_summary(&mut lines, value),
        "workspace/define-experiment" => experiment_summary(&mut lines, value),
        "workspace/conduct" | "workspace/continue" => circulation_summary(&mut lines, value),
        "workspace/stage-return" => candidate_summary(&mut lines, value),
        "workspace/commit" => commit_summary(&mut lines, value),
        "workspace/decline" => decline_summary(&mut lines, value),
        "workspace/evaluate" => evaluation_summary(&mut lines, value),
        "workspace/export" => export_summary(&mut lines, value),
        _ => {}
    }
    if let Some(written) = payload.get("written_artifacts").and_then(Value::as_array) {
        if !written.is_empty() {
            lines.push(String::new());
            lines.push("WRITTEN ARTIFACTS".to_owned());
            lines.extend(
                written
                    .iter()
                    .map(|item| format!("  {}", exact_value(item))),
            );
        }
    }
    lines.join("\n")
}

fn workspace_manifest(lines: &mut Vec<String>, manifest: &Value) {
    lines.push(String::new());
    lines.push("VARIANT STATE".to_owned());
    push_field(lines, "Label", manifest.get("label"));
    if let Some(current) = manifest.get("current").filter(|item| !item.is_null()) {
        push_field(lines, "Generation", current.get("generation"));
        push_field(
            lines,
            "Native population",
            current
                .get("morphology")
                .and_then(|item| item.get("anatomy"))
                .and_then(|item| item.get("native_population")),
        );
    } else {
        lines.push(format!("{:<34} {}", "State", "empty, lift or import next"));
    }
    push_names(lines, "Experiments", manifest.get("experiments"), "name");
    if let Some(active) = manifest.get("active_run").filter(|item| !item.is_null()) {
        push_field(lines, "Active run", active.get("ordinal"));
    } else {
        lines.push(format!("{:<34} {}", "Active run", "none"));
    }
    push_population(lines, "Completed runs", manifest.get("completed_runs"));
    push_population(lines, "Evaluations", manifest.get("evaluations"));
    push_population(lines, "Export artifacts", manifest.get("exports"));
    push_list(
        lines,
        "Open capabilities",
        manifest.get("open_capabilities"),
    );
}

fn lift_summary(lines: &mut Vec<String>, value: &Value) {
    lines.push(String::new());
    lines.push("LIFT".to_owned());
    push_field(lines, "Source", value.get("source_address"));
    push_field(lines, "Generation", value.get("generation"));
    push_field(lines, "Receiver", value.get("receiver"));
    push_field(
        lines,
        "Excitations",
        value.get("cold_excitation_population"),
    );
    push_field(lines, "Foreign execution", value.get("foreign_execution"));
    push_map(lines, "Modalities", value.get("modality_occurrences"));
    push_list(lines, "Open exterior", value.get("open_exterior"));
}

fn import_summary(lines: &mut Vec<String>, value: &Value) {
    lines.push(String::new());
    lines.push("IMPORTED VARIANT".to_owned());
    push_field(lines, "Generation", value.get("generation"));
    push_field(
        lines,
        "Snapshot",
        value
            .get("snapshot")
            .and_then(|item| item.get("relative_path")),
    );
}

fn experiment_summary(lines: &mut Vec<String>, value: &Value) {
    lines.push(String::new());
    lines.push("EXPERIMENT".to_owned());
    push_field(lines, "Name", value.get("name"));
    push_address(lines, "Ingress", value.get("ingress"));
    push_field(lines, "Receiver", value.get("receiver"));
}

fn circulation_summary(lines: &mut Vec<String>, value: &Value) {
    lines.push(String::new());
    lines.push("ACTIVE CIRCULATION".to_owned());
    let run = &value["run"];
    let boundary = &value["boundary"];
    push_field(lines, "Run", run.get("ordinal"));
    push_field(lines, "Experiment", run.get("experiment"));
    push_field(lines, "Run state", run.get("state"));
    push_field(lines, "Generation", boundary.get("generation"));
    push_address(
        lines,
        "Emission",
        boundary
            .get("emission")
            .and_then(|item| item.get("address")),
    );
    push_population(lines, "Future grains", boundary.get("futures"));
    push_population(lines, "Open obligations", boundary.get("open_obligations"));
    push_successors(lines, boundary.get("actual_successors"));
}

fn candidate_summary(lines: &mut Vec<String>, value: &Value) {
    lines.push(String::new());
    lines.push("STAGED CANDIDATE".to_owned());
    push_field(
        lines,
        "Generation",
        value
            .get("boundary")
            .and_then(|item| item.get("generation")),
    );
    push_field(
        lines,
        "Returned occurrence",
        value
            .get("returned")
            .and_then(|item| item.get("occurrence")),
    );
    push_field(
        lines,
        "Returned boundary",
        value
            .get("returned")
            .and_then(|item| item.get("emitting_boundary")),
    );
    push_field(
        lines,
        "Exterior current",
        value
            .get("returned")
            .and_then(|item| item.get("exterior_current")),
    );
    push_field(
        lines,
        "Returned storage",
        value.get("returned").and_then(|item| item.get("storage")),
    );
    push_population(
        lines,
        "Contact support",
        value
            .get("returned")
            .and_then(|item| item.get("contact_support")),
    );
}

fn commit_summary(lines: &mut Vec<String>, value: &Value) {
    lines.push(String::new());
    lines.push("COMMITTED MORPHOLOGY".to_owned());
    push_field(
        lines,
        "Generation",
        value
            .get("successor_lineage")
            .and_then(|lineage| lineage.get("generation")),
    );
    push_field(
        lines,
        "Parent generation",
        value
            .get("predecessor_lineage")
            .and_then(|lineage| lineage.get("generation")),
    );
}

fn decline_summary(lines: &mut Vec<String>, value: &Value) {
    lines.push(String::new());
    lines.push("DECLINED RETURN".to_owned());
    push_field(lines, "Generation before", value.get("generation_before"));
    push_field(lines, "Generation after", value.get("generation_after"));
    push_field(
        lines,
        "Morphology unchanged",
        value.get("morphology_unchanged"),
    );
}

fn evaluation_summary(lines: &mut Vec<String>, value: &Value) {
    lines.push(String::new());
    lines.push("CULTIVATION EVALUATION".to_owned());
    push_field(lines, "Experiment", value.get("experiment"));
    push_field(
        lines,
        "Current generation",
        value.get("current").and_then(|item| item.get("generation")),
    );
    push_field(
        lines,
        "Current differs from withdrawn",
        value.get("cultivation_separates_current_from_withdrawn"),
    );
    push_field(
        lines,
        "Replay restored exactly",
        value.get("restoration_exact"),
    );
    push_field(
        lines,
        "Current snapshot unchanged",
        value.get("current_snapshot_unchanged"),
    );
    push_list(lines, "Open", value.get("open"));
}

fn export_summary(lines: &mut Vec<String>, value: &Value) {
    lines.push(String::new());
    lines.push("EXACT EXPORT".to_owned());
    push_field(lines, "Codec", value.get("codec"));
    push_field(lines, "Generation", value.get("generation"));
    push_field(lines, "Media type", value.get("media_type"));
    push_field(
        lines,
        "Complete package round trip",
        value.get("complete_package_round_trip"),
    );
    push_field(
        lines,
        "Artifact",
        value
            .get("artifact")
            .and_then(|item| item.get("relative_path")),
    );
}

fn push_field(lines: &mut Vec<String>, label: &str, value: Option<&Value>) {
    if let Some(value) = value {
        lines.push(format!("{label:<34} {}", exact_value(value)));
    }
}

fn push_population(lines: &mut Vec<String>, label: &str, value: Option<&Value>) {
    if let Some(values) = value.and_then(Value::as_array) {
        lines.push(format!("{label:<34} {}", values.len()));
    }
}

fn push_names(lines: &mut Vec<String>, label: &str, value: Option<&Value>, key: &str) {
    let Some(values) = value.and_then(Value::as_array) else {
        return;
    };
    let names = values
        .iter()
        .filter_map(|item| item.get(key))
        .map(exact_value)
        .collect::<Vec<_>>();
    lines.push(format!(
        "{label:<34} {}",
        if names.is_empty() {
            "none".to_owned()
        } else {
            names.join(", ")
        }
    ));
}

fn push_list(lines: &mut Vec<String>, label: &str, value: Option<&Value>) {
    let Some(values) = value.and_then(Value::as_array) else {
        return;
    };
    if values.is_empty() {
        return;
    }
    lines.push(label.to_owned());
    lines.extend(values.iter().map(|item| format!("  {}", exact_value(item))));
}

fn push_map(lines: &mut Vec<String>, label: &str, value: Option<&Value>) {
    let Some(values) = value.and_then(Value::as_object) else {
        return;
    };
    if values.is_empty() {
        return;
    }
    lines.push(label.to_owned());
    lines.extend(
        values
            .iter()
            .map(|(key, value)| format!("  {key:<28} {}", exact_value(value))),
    );
}

fn push_address(lines: &mut Vec<String>, label: &str, value: Option<&Value>) {
    let Some(value) = value else {
        return;
    };
    let spool = value
        .get("spool")
        .map(exact_value)
        .unwrap_or_else(|| "?".to_owned());
    let thread = value
        .get("thread")
        .map(exact_value)
        .unwrap_or_else(|| "?".to_owned());
    let occurrence = value
        .get("occurrence")
        .or_else(|| value.get("entering_occurrence"))
        .map(exact_value)
        .unwrap_or_else(|| "?".to_owned());
    lines.push(format!("{label:<34} {spool}/{thread} @ {occurrence}"));
}

fn push_successors(lines: &mut Vec<String>, value: Option<&Value>) {
    let Some(successors) = value.and_then(Value::as_array) else {
        return;
    };
    lines.push(format!("{:<34} {}", "Actual successors", successors.len()));
    for (ordinal, successor) in successors.iter().enumerate() {
        let address = &successor["address"];
        lines.push(format!(
            "  #{ordinal:<4} {}/{} @ {}  receiver {}",
            exact_value(&address["spool"]),
            exact_value(&address["thread"]),
            exact_value(&address["occurrence"]),
            exact_value(&successor["receiver"]),
        ));
    }
}

pub fn structure(event: &WorkbenchEvent) -> String {
    if event.subject.ends_with("/diffusion") {
        return diffusion_structure(event);
    }
    let mut lines = event_heading(event);
    lines.push(String::new());
    lines.push("STRUCTURE".to_owned());
    if let Some(payload) = &event.payload {
        flatten(payload, "", 0, &mut lines, 120);
    } else {
        lines.push("No structured payload returned.".to_owned());
    }
    lines.join("\n")
}

pub fn exact(event: &WorkbenchEvent) -> String {
    let value = event
        .payload
        .as_ref()
        .and_then(|payload| payload.get("exact"))
        .or(event.payload.as_ref());
    match value {
        Some(value) => serde_json::to_string_pretty(value).unwrap_or_else(|_| "null".to_owned()),
        None => format!(
            "{}\n{}\n\nNo exact payload accompanied this event.",
            event.subject, event.summary
        ),
    }
}

fn diffusion_summary(event: &WorkbenchEvent) -> String {
    let mut lines = event_heading(event);
    let Some(view) = event
        .payload
        .as_ref()
        .and_then(|payload| payload.get("view"))
    else {
        return lines.join("\n");
    };
    lines.extend([
        String::new(),
        "CLOSED ONE-STEP DIFFUSION PROBE".to_owned(),
        "Session state         unchanged".to_owned(),
        format!("Generation            {}", exact_value(&view["generation"])),
        format!("Receiver              {}", exact_value(&view["receiver"])),
        format!("Interval              {}", exact_value(&view["interval"])),
        String::new(),
        "DECLARED LAW".to_owned(),
        format!("Capacity              {}", text(&view["law"]["capacity"])),
        format!(
            "Conductance           {}",
            text(&view["law"]["conductance"])
        ),
        format!("Source                {}", text(&view["law"]["source"])),
        format!(
            "Initial standing      {}",
            text(&view["law"]["initial_standing"])
        ),
        String::new(),
        "TOPOLOGY".to_owned(),
        format!(
            "Native nodes          {}",
            exact_value(&view["topology"]["native_nodes"])
        ),
        format!(
            "Incidence branches    {}",
            exact_value(&view["topology"]["incidence_branches"])
        ),
        format!(
            "Nonzero currents      {}",
            exact_value(&view["topology"]["nonzero_currents"])
        ),
        format!(
            "Boundary / interior   {} / {}",
            exact_value(&view["topology"]["boundary_nodes"]),
            exact_value(&view["topology"]["interior_nodes"])
        ),
        String::new(),
        "BALANCE".to_owned(),
        format!(
            "Total                 {} + {} → {}",
            exact_value(&view["total_before"]),
            exact_value(&view["total_source"]),
            exact_value(&view["total_after"])
        ),
        format!(
            "Stored energy         {} → {}",
            exact_value(&view["stored_energy_before"]),
            exact_value(&view["stored_energy_after"])
        ),
        format!(
            "Energy departed       {}",
            exact_value(&view["energy_departed"])
        ),
        format!(
            "Conservation residual {}  (required for a returned event)",
            exact_value(&view["conservation_residual"])
        ),
    ]);
    lines.join("\n")
}

fn diffusion_structure(event: &WorkbenchEvent) -> String {
    let mut lines = event_heading(event);
    let Some(exact) = event
        .payload
        .as_ref()
        .and_then(|payload| payload.get("exact"))
    else {
        return lines.join("\n");
    };
    let receipt = &exact["receipt"];
    lines.push(String::new());
    lines.push("ORIENTED BRANCH CURRENTS".to_owned());
    lines.push("branch   source → target   current   transferred".to_owned());
    if let Some(currents) = receipt["currents"].as_array() {
        for current in currents {
            lines.push(format!(
                "{:<8} {:>4} → {:<6} {:>9}   {}",
                exact_value(&current["branch"]),
                exact_value(&current["source"]),
                exact_value(&current["target"]),
                exact_value(&current["current"]),
                exact_value(&current["transferred"]),
            ));
        }
    }
    lines.push(String::new());
    lines.push("NODE BALANCES".to_owned());
    lines.push("node   before + source + boundary = after   residual".to_owned());
    if let Some(balances) = receipt["balances"].as_array() {
        for balance in balances {
            lines.push(format!(
                "{:<6} {} + {} + {} = {}   {}",
                exact_value(&balance["node"]),
                exact_value(&balance["content_before"]),
                exact_value(&balance["source"]),
                exact_value(&balance["boundary_transfer"]),
                exact_value(&balance["content_after"]),
                exact_value(&balance["exact_residual"]),
            ));
        }
    }
    lines.push(String::new());
    lines.push("STANDING BEFORE → AFTER".to_owned());
    let before = &exact["standing_before"]["content"];
    let after = &exact["standing_after"]["content"];
    if let (Some(before), Some(after)) = (before.as_object(), after.as_object()) {
        for (node, value) in before {
            lines.push(format!(
                "native {:<6} {} → {}",
                node,
                exact_value(value),
                after
                    .get(node)
                    .map(exact_value)
                    .unwrap_or_else(|| "?".to_owned())
            ));
        }
    }
    lines.join("\n")
}

fn event_heading(event: &WorkbenchEvent) -> Vec<String> {
    let level = match event.level {
        EventLevel::Information => "INFORMATION",
        EventLevel::Consequence => "CONSEQUENCE",
        EventLevel::Obstruction => "OBSTRUCTION",
    };
    let mut lines = vec![
        format!("{}  #{}", level, event.sequence),
        event.subject.clone(),
        event.summary.clone(),
    ];
    if let Some(code) = &event.code {
        lines.push(format!("Code: {code}"));
    }
    lines
}

fn flatten(value: &Value, path: &str, depth: usize, lines: &mut Vec<String>, limit: usize) {
    if lines.len() >= limit {
        return;
    }
    match value {
        Value::Object(map) if depth < 3 => {
            for (key, value) in map {
                let next = if path.is_empty() {
                    humanize(key)
                } else {
                    format!("{path} / {}", humanize(key))
                };
                flatten(value, &next, depth + 1, lines, limit);
                if lines.len() >= limit {
                    lines.push("… exact structure continues in the Exact view".to_owned());
                    break;
                }
            }
        }
        Value::Array(values) if depth < 2 && values.len() <= 12 => {
            if values.iter().all(scalar) {
                lines.push(format!("{:<34} {}", path, exact_value(value)));
            } else {
                lines.push(format!("{path}  ({} entries)", values.len()));
                for (at, value) in values.iter().enumerate() {
                    flatten(
                        value,
                        &format!("{path} / {}", at + 1),
                        depth + 1,
                        lines,
                        limit,
                    );
                }
            }
        }
        Value::Array(values) => lines.push(format!("{path}  ({} entries)", values.len())),
        _ => lines.push(format!("{:<34} {}", path, exact_value(value))),
    }
}

fn scalar(value: &Value) -> bool {
    matches!(
        value,
        Value::Null | Value::Bool(_) | Value::Number(_) | Value::String(_)
    )
}

fn humanize(key: &str) -> String {
    let mut words = key.replace('_', " ");
    if let Some(first) = words.get_mut(0..1) {
        first.make_ascii_uppercase();
    }
    words
}

fn text(value: &Value) -> String {
    value
        .as_str()
        .map(str::to_owned)
        .unwrap_or_else(|| exact_value(value))
}

fn exact_value(value: &Value) -> String {
    if let Some(rational) = rational(value) {
        return rational;
    }
    match value {
        Value::Null => "none".to_owned(),
        Value::Bool(value) => value.to_string(),
        Value::Number(value) => value.to_string(),
        Value::String(value) => value.clone(),
        Value::Array(values) => format!(
            "[{}]",
            values
                .iter()
                .map(exact_value)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Value::Object(map) => format!("{} fields", map.len()),
    }
}

fn rational(value: &Value) -> Option<String> {
    let values = value.as_array()?;
    if values.len() != 2 {
        return None;
    }
    let numerator = canonical_big_integer(&values[0])?;
    let denominator = canonical_big_integer(&values[1])?;
    if denominator == BigInt::from(1u8) {
        Some(numerator.to_string())
    } else {
        Some(format!("{numerator}/{denominator}"))
    }
}

fn canonical_big_integer(value: &Value) -> Option<BigInt> {
    let parts = value.as_array()?;
    if parts.len() != 2 || !parts[1].is_array() {
        return None;
    }
    big_integer(value)
}

fn big_integer(value: &Value) -> Option<BigInt> {
    if let Some(integer) = value.as_i64() {
        return Some(BigInt::from(integer));
    }
    if let Some(integer) = value.as_u64() {
        return Some(BigInt::from(integer));
    }
    let parts = value.as_array()?;
    if parts.len() != 2 {
        return None;
    }
    let sign = match parts[0].as_i64()? {
        -1 => Sign::Minus,
        0 => Sign::NoSign,
        1 => Sign::Plus,
        _ => return None,
    };
    let digits = parts[1]
        .as_array()?
        .iter()
        .map(|digit| digit.as_u64().and_then(|digit| u32::try_from(digit).ok()))
        .collect::<Option<Vec<_>>>()?;
    Some(BigInt::new(sign, digits))
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;

    #[test]
    fn exact_rational_codec_is_rendered_as_mathematics_not_serde_limbs() {
        assert_eq!(exact_value(&json!([[1, [7]], [1, [13]]])), "7/13");
        assert_eq!(exact_value(&json!([[1, [3]], [1, [1]]])), "3");
        assert_eq!(exact_value(&json!([1, 2])), "[1, 2]");
        assert_eq!(exact_value(&json!([1, 0])), "[1, 0]");
    }
}
