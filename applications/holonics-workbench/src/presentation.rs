use num_bigint::{BigInt, Sign};
use serde_json::Value;

use crate::{EventLevel, WorkbenchEvent};

pub fn summary(event: &WorkbenchEvent) -> String {
    if event.subject.ends_with("/diffusion") {
        return diffusion_summary(event);
    }
    let mut lines = event_heading(event);
    if let Some(payload) = &event.payload {
        for key in [
            "session",
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
