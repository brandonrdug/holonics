use crate::{presentation, EventLevel, WorkbenchEvent, WorkbenchResponse};

pub fn render_human(events: &[WorkbenchEvent]) -> String {
    events
        .iter()
        .map(|event| {
            let marker = match event.level {
                EventLevel::Information => "·",
                EventLevel::Consequence => "→",
                EventLevel::Obstruction => "!",
            };
            format!("{marker} {}", presentation::summary(event))
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
