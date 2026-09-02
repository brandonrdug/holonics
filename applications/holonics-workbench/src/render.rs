use crate::{EventLevel, WorkbenchEvent, WorkbenchResponse};

pub fn render_human(events: &[WorkbenchEvent]) -> String {
    events
        .iter()
        .map(|event| {
            let marker = match event.level {
                EventLevel::Information => "·",
                EventLevel::Consequence => "→",
                EventLevel::Obstruction => "!",
            };
            let subject = match &event.code {
                Some(code) => format!("{} [{code}]", event.subject),
                None => event.subject.clone(),
            };
            match &event.payload {
                Some(payload) => format!(
                    "{marker} {} — {}\n{}",
                    subject,
                    event.summary,
                    serde_json::to_string_pretty(payload).unwrap_or_else(|_| "null".to_owned())
                ),
                None => format!("{marker} {subject} — {}", event.summary),
            }
        })
        .collect::<Vec<_>>()
        .join("\n\n")
}

pub fn render_json_lines(events: &[WorkbenchEvent]) -> Result<String, serde_json::Error> {
    events
        .iter()
        .map(serde_json::to_string)
        .collect::<Result<Vec<_>, _>>()
        .map(|lines| lines.join("\n"))
}

pub fn render_json(response: &WorkbenchResponse) -> Result<String, serde_json::Error> {
    serde_json::to_string_pretty(response)
}
