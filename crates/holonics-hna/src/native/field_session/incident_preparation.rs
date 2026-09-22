//! Source-region preparation for the incident-field boundary.
//!
//! This module keeps the exterior Unicode chart, ordered source parts/cells and recorded joins
//! together until the native caller binds them to its declared ports.  Event coordinates are
//! provenance witnesses for one preparation; they are not persistent native identities.

use super::{
    ExposureAperture, FieldSectionRequest, FieldSessionSpec, FieldSourceChart, FieldTextCodec,
    Result, invalid,
};
use crate::alpha::exposure::{
    ExposureAvailability, ExposureFamily, ExposureManifest, ExposureOccurrence,
};
use holonic_engine::codec_recovery::Symbol;
use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;
use std::ops::Range;

/// One admitted Unicode scalar cell in an ordered source part.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct IncidentSourceCell {
    /// Index of the containing source region in `IncidentPreparation::regions`.
    pub region: usize,
    pub part_ordinal: u64,
    /// Position within the part, retained separately from the global cell index.
    pub cell: usize,
    pub symbol: Symbol,
    /// Ordinal in the declared exterior codec alphabet.
    pub symbol_index: usize,
}

/// One visible recorded occurrence with its ordered source parts and cells.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct IncidentSourceRegion {
    pub origin: IncidentSourceOrigin,
    pub parts: Vec<IncidentSourcePart>,
    pub cells: Vec<IncidentSourceCell>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "kebab-case", deny_unknown_fields)]
pub enum IncidentSourceOrigin {
    Direct {
        role: String,
        context_index: usize,
    },
    Recorded {
        event: u64,
        sequence: u64,
        family: ExposureFamily,
        author_class: String,
    },
}

/// A visible source part and its global ordered cell range.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct IncidentSourcePart {
    pub ordinal: u64,
    pub pointer: String,
    pub kind: String,
    pub cell_range: Range<usize>,
}

/// The declared reason why two source cells are admitted into one contact restriction.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "kebab-case", deny_unknown_fields)]
pub enum IncidentContactKind {
    IntraPart,
    DirectJoin {
        from_region: usize,
        to_region: usize,
        context_index: usize,
    },
    RecordedParent {
        from_event: u64,
        to_event: u64,
        parent_family: ExposureFamily,
    },
    RecordedReply {
        from_event: u64,
        to_event: u64,
        parent_family: ExposureFamily,
    },
}

/// One oriented source/contact restriction. Cell ordinals are local to this preparation packet.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct IncidentContact {
    pub from_cell: usize,
    pub to_cell: usize,
    pub kind: IncidentContactKind,
}

/// Complete finite source boundary admitted for one incident-field request.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct IncidentPreparation {
    pub regions: Vec<IncidentSourceRegion>,
    pub contacts: Vec<IncidentContact>,
    /// Context cells followed by request cells, in the same order as `regions`.
    pub source_cells: Vec<IncidentSourceCell>,
    /// Source cells are held; the trailing response aperture is free.
    pub held_mask: Vec<bool>,
    pub context_extent: usize,
    pub request_extent: usize,
    pub source_extent: usize,
    pub response_aperture: usize,
}

impl IncidentPreparation {
    /// Validate a packet against the declared Unicode exterior chart and finite aperture.
    pub fn validate(&self, spec: &FieldSessionSpec) -> Result<()> {
        if spec.codec != FieldTextCodec::UnicodeScalars {
            return Err(invalid(
                "incident preparation requires the Unicode scalar exterior codec",
            ));
        }
        if self.regions.is_empty()
            || self.source_extent == 0
            || self.response_aperture == 0
            || self.context_extent.checked_add(self.request_extent) != Some(self.source_extent)
            || self.source_cells.len() != self.source_extent
            || Some(self.held_mask.len()) != self.source_extent.checked_add(self.response_aperture)
            || self.held_mask[..self.source_extent]
                .iter()
                .any(|held| !held)
            || self.held_mask[self.source_extent..]
                .iter()
                .any(|held| *held)
        {
            return Err(invalid("incident source extent or held mask"));
        }
        if self.context_extent > spec.context_symbols
            || self
                .source_extent
                .checked_add(self.response_aperture)
                .is_none_or(|n| n > spec.section_symbols)
        {
            return Err(invalid(format!(
                "incident source/response aperture: source={} context={} response={}, available total={} context={}",
                self.source_extent,
                self.context_extent,
                self.response_aperture,
                spec.section_symbols,
                spec.context_symbols
            )));
        }
        if spec.source_chart == FieldSourceChart::GeneratorMachine {
            if self.response_aperture != spec.response_aperture()? {
                return Err(invalid("generator response aperture"));
            }
        } else if let Some(start) = spec
            .incident
            .as_ref()
            .and_then(|options| options.response_port_start)
        {
            if self.source_extent > start
                || start
                    .checked_add(self.response_aperture)
                    .is_none_or(|end| end > spec.section_symbols)
            {
                return Err(invalid("incident source crosses fixed response port"));
            }
        }
        let chart = spec.chart()?;
        let alphabet = chart.alphabet();
        let mut global = 0usize;
        let mut seen_events = BTreeSet::new();
        for (region, source_region) in self.regions.iter().enumerate() {
            if let IncidentSourceOrigin::Recorded { event, .. } = &source_region.origin {
                if *event == 0 || !seen_events.insert(*event) {
                    return Err(invalid("incident source event provenance"));
                }
            }
            if source_region.cells.is_empty() {
                return Err(invalid("incident source region has no ordered cells"));
            }
            let region_end = global
                .checked_add(source_region.cells.len())
                .ok_or_else(|| invalid("incident source extent overflow"))?;
            let mut seen_parts = BTreeSet::new();
            let mut region_cursor = global;
            let mut cell_cursor = 0usize;
            for part in &source_region.parts {
                if part.pointer.is_empty()
                    || !part.pointer.starts_with('/')
                    || !seen_parts.insert(part.ordinal)
                    || part.cell_range.start > part.cell_range.end
                    || part.cell_range.start != region_cursor
                    || part.cell_range.end > region_end
                {
                    return Err(invalid("incident source part boundary"));
                }
                let part_len = part.cell_range.end - part.cell_range.start;
                if part_len == 0 {
                    return Err(invalid("incident source part is empty"));
                }
                region_cursor = part.cell_range.end;
                cell_cursor += part_len;
            }
            if cell_cursor != source_region.cells.len() || region_cursor != region_end {
                return Err(invalid("incident source parts do not cover region cells"));
            }
            let mut local = 0usize;
            for part in &source_region.parts {
                let part_len = part.cell_range.end - part.cell_range.start;
                for part_cell in 0..part_len {
                    let cell = &source_region.cells[local];
                    if cell.region != region
                        || cell.part_ordinal != part.ordinal
                        || cell.cell != part_cell
                        || cell.symbol_index != cell.symbol.0 as usize
                        || cell.symbol_index >= alphabet.len()
                        || global + local >= self.source_extent
                    {
                        return Err(invalid("incident source cell chart"));
                    }
                    if self.source_cells[global + local] != *cell {
                        return Err(invalid("incident source cell order"));
                    }
                    local += 1;
                }
            }
            global = global
                .checked_add(source_region.cells.len())
                .ok_or_else(|| invalid("incident source extent overflow"))?;
        }
        if global != self.source_extent {
            return Err(invalid("incident source extent does not cover regions"));
        }
        for contact in &self.contacts {
            if contact.from_cell >= self.source_extent || contact.to_cell >= self.source_extent {
                return Err(invalid("incident contact cell extent"));
            }
        }
        Ok(())
    }

    /// Preserve a preparation already attached to a request after validating its chart.
    pub fn from_request(spec: &FieldSessionSpec, request: &FieldSectionRequest) -> Result<Self> {
        if let Some(preparation) = &request.incident_preparation {
            preparation.validate(spec)?;
            return Ok(preparation.clone());
        }
        Self::from_direct_request(spec, request)
    }

    fn from_direct_request(spec: &FieldSessionSpec, request: &FieldSectionRequest) -> Result<Self> {
        if spec.codec != FieldTextCodec::UnicodeScalars {
            return Err(invalid(
                "incident preparation requires the Unicode scalar exterior codec",
            ));
        }
        let chart = spec.chart()?;
        if request.partial.is_some() && !request.text.is_empty() {
            return Err(invalid("direct incident request supplies text and partial"));
        }
        let mut regions = Vec::new();
        let mut source_cells = Vec::new();
        let mut contacts = Vec::new();
        let mut context_extent = 0usize;
        let add_region = |text: &str,
                          role: String,
                          context_index: usize,
                          regions: &mut Vec<IncidentSourceRegion>,
                          source_cells: &mut Vec<IncidentSourceCell>,
                          contacts: &mut Vec<IncidentContact>|
         -> Result<()> {
            let symbols = spec.symbols_of(&chart, text)?;
            if symbols.is_empty() {
                return Err(invalid("direct incident source region has no cells"));
            }
            let region = regions.len();
            let start = source_cells.len();
            let cells = symbols
                .into_iter()
                .enumerate()
                .map(|(cell, symbol)| IncidentSourceCell {
                    region,
                    part_ordinal: 0,
                    cell,
                    symbol,
                    symbol_index: symbol.0 as usize,
                })
                .collect::<Vec<_>>();
            let end = start
                .checked_add(cells.len())
                .ok_or_else(|| invalid("direct incident source extent"))?;
            contacts.extend((start..end.saturating_sub(1)).map(|cell| IncidentContact {
                from_cell: cell,
                to_cell: cell + 1,
                kind: IncidentContactKind::IntraPart,
            }));
            source_cells.extend(cells.iter().copied());
            regions.push(IncidentSourceRegion {
                origin: IncidentSourceOrigin::Direct {
                    role,
                    context_index,
                },
                parts: vec![IncidentSourcePart {
                    ordinal: 0,
                    pointer: format!("/direct/{context_index}"),
                    kind: "direct-text".into(),
                    cell_range: start..end,
                }],
                cells,
            });
            Ok(())
        };
        for (index, context) in request.context.iter().enumerate() {
            add_region(
                context,
                "context".into(),
                index,
                &mut regions,
                &mut source_cells,
                &mut contacts,
            )?;
            if index > 0 {
                let left = regions[index - 1].cells.len();
                let left_start = source_cells.len() - left - regions[index].cells.len();
                let right_start = source_cells.len() - regions[index].cells.len();
                contacts.push(IncidentContact {
                    from_cell: left_start + left - 1,
                    to_cell: right_start,
                    kind: IncidentContactKind::DirectJoin {
                        from_region: index - 1,
                        to_region: index,
                        context_index: index,
                    },
                });
            }
            context_extent = context_extent
                .checked_add(regions[index].cells.len())
                .ok_or_else(|| invalid("direct incident context extent"))?;
        }
        let request_text = if let Some(parts) = &request.partial {
            if parts.iter().any(Option::is_none) {
                return Err(invalid(
                    "direct incident partial contains unknown source holes",
                ));
            }
            parts
                .iter()
                .map(|part| part.as_deref().unwrap())
                .collect::<String>()
        } else {
            request.text.clone()
        };
        let request_region = regions.len();
        add_region(
            &request_text,
            "request".into(),
            request_region,
            &mut regions,
            &mut source_cells,
            &mut contacts,
        )?;
        if request_region > 0 {
            let right_start = source_cells.len() - regions[request_region].cells.len();
            contacts.push(IncidentContact {
                from_cell: right_start - 1,
                to_cell: right_start,
                kind: IncidentContactKind::DirectJoin {
                    from_region: request_region - 1,
                    to_region: request_region,
                    context_index: request_region,
                },
            });
        }
        let request_extent = source_cells
            .len()
            .checked_sub(context_extent)
            .ok_or_else(|| invalid("direct incident request extent"))?;
        let response_aperture = spec.response_aperture()?;
        let expected_output = request_extent
            .checked_add(response_aperture)
            .ok_or_else(|| invalid("direct incident output extent overflow"))?;
        if request
            .output_symbols
            .is_some_and(|output| output != expected_output)
        {
            return Err(invalid("direct incident request output extent"));
        }
        let source_extent = source_cells.len();
        let mut held_mask = vec![true; source_extent];
        held_mask.extend(std::iter::repeat_n(false, response_aperture));
        let preparation = Self {
            regions,
            contacts,
            source_cells,
            held_mask,
            context_extent,
            request_extent,
            source_extent,
            response_aperture,
        };
        preparation.validate(spec)?;
        Ok(preparation)
    }

    /// Build the packet from validated recorded source occurrences. `context` must be ordered
    /// oldest to newest, followed by the request occurrence as the final source region.
    pub fn from_exposures(
        spec: &FieldSessionSpec,
        aperture: &ExposureAperture,
        manifest: &ExposureManifest,
        request: &ExposureOccurrence,
        context: &[&ExposureOccurrence],
    ) -> Result<Self> {
        let (held_cap, context_cap) = aperture.bounded(spec)?;
        if spec.codec != FieldTextCodec::UnicodeScalars {
            return Err(invalid(
                "incident preparation requires the Unicode scalar exterior codec",
            ));
        }
        let chart = spec.chart()?;
        let chain = context
            .iter()
            .copied()
            .chain(std::iter::once(request))
            .collect::<Vec<_>>();
        if chain.is_empty() {
            return Err(invalid("incident source chain is empty"));
        }
        for occurrence in &chain {
            occurrence.validate(manifest).map_err(invalid)?;
        }
        for pair in chain.windows(2) {
            if pair[0].sequence >= pair[1].sequence
                || pair[1].shared_prior_parent().map_err(invalid)?.as_ref() != Some(&pair[0].family)
            {
                return Err(invalid(
                    "incident source chain is not recorded parent order",
                ));
            }
        }

        let mut regions = Vec::with_capacity(chain.len());
        let mut source_cells = Vec::new();
        let mut contacts = Vec::new();
        let mut context_extent = 0usize;
        let mut event_ranges = Vec::with_capacity(chain.len());
        for (region_index, occurrence) in chain.iter().enumerate() {
            let visible = occurrence.shared_visible_parts().map_err(invalid)?;
            let mut parts = Vec::with_capacity(visible.len());
            let mut cells = Vec::new();
            for part in visible {
                let text = part
                    .text
                    .as_deref()
                    .ok_or_else(|| invalid("incident source part has no visible text"))?;
                let symbols = spec.symbols_of(&chart, text)?;
                if symbols.is_empty() {
                    return Err(invalid("incident source part has no Unicode cells"));
                }
                let start = source_cells.len() + cells.len();
                for (cell_index, symbol) in symbols.iter().copied().enumerate() {
                    cells.push(IncidentSourceCell {
                        region: region_index,
                        part_ordinal: part.ordinal,
                        cell: cell_index,
                        symbol,
                        symbol_index: symbol.0 as usize,
                    });
                }
                let end = start + symbols.len();
                parts.push(IncidentSourcePart {
                    ordinal: part.ordinal,
                    pointer: part.pointer.clone(),
                    kind: part.kind.clone(),
                    cell_range: start..end,
                });
            }
            if cells.is_empty() {
                return Err(invalid("incident source occurrence has no ordered cells"));
            }
            let region_start = source_cells.len();
            source_cells.extend(cells.iter().copied());
            let region_end = source_cells.len();
            event_ranges.push((region_start, region_end));
            if region_index < context.len() {
                context_extent = context_extent
                    .checked_add(region_end - region_start)
                    .ok_or_else(|| invalid("incident context extent overflow"))?;
            }
            for part in &parts {
                for cell in part.cell_range.clone().collect::<Vec<_>>().windows(2) {
                    contacts.push(IncidentContact {
                        from_cell: cell[0],
                        to_cell: cell[1],
                        kind: IncidentContactKind::IntraPart,
                    });
                }
            }
            regions.push(IncidentSourceRegion {
                origin: IncidentSourceOrigin::Recorded {
                    event: occurrence.views[0].event,
                    sequence: occurrence.sequence,
                    family: occurrence.family.clone(),
                    author_class: occurrence
                        .shared_author_class()
                        .map_err(invalid)?
                        .to_owned(),
                },
                parts,
                cells,
            });
        }
        for (index, pair) in chain.windows(2).enumerate() {
            let left = event_ranges[index];
            let right = event_ranges[index + 1];
            let parent_family = pair[0].family.clone();
            let kind = if has_recorded_reply_join(pair[1], &parent_family) {
                IncidentContactKind::RecordedReply {
                    from_event: pair[0].views[0].event,
                    to_event: pair[1].views[0].event,
                    parent_family,
                }
            } else {
                IncidentContactKind::RecordedParent {
                    from_event: pair[0].views[0].event,
                    to_event: pair[1].views[0].event,
                    parent_family,
                }
            };
            contacts.push(IncidentContact {
                from_cell: left.1 - 1,
                to_cell: right.0,
                kind,
            });
        }
        let request_extent = source_cells
            .len()
            .checked_sub(context_extent)
            .ok_or_else(|| invalid("incident request extent"))?;
        if request_extent > held_cap || context_extent > context_cap {
            return Err(invalid(
                "incident source exceeds declared exposure aperture",
            ));
        }
        let response_aperture = aperture.response_symbols;
        let source_extent = source_cells.len();
        let mut held_mask = vec![true; source_extent];
        held_mask.extend(std::iter::repeat_n(false, response_aperture));
        let preparation = Self {
            regions,
            contacts,
            source_cells,
            held_mask,
            context_extent,
            request_extent,
            source_extent,
            response_aperture,
        };
        preparation.validate(spec)?;
        Ok(preparation)
    }
}

fn has_recorded_reply_join(occurrence: &ExposureOccurrence, parent: &ExposureFamily) -> bool {
    occurrence.views.iter().any(|view| {
        view.links.iter().any(|link| {
            link.kind == "later-human-after-agent"
                && link.availability == ExposureAvailability::Prior
                && link.target.as_ref().is_some_and(|target| {
                    target.provider == parent.provider && target.record_group == parent.record_group
                })
        })
    })
}

#[cfg(test)]
#[path = "incident_preparation_tests.rs"]
mod tests;
