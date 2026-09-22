//! Resident source-cell contact contrasts for the fixed generator machine.
//!
//! Source cells and generator sites are distinct populations.  This owner keeps the complete
//! ordered cell tape and directed contact kinds, while exposing only a declared pooled condition
//! chart on the fixed source-role sites.  It does not infer a graph from first moments or turn a
//! source cell into a machine site.

use super::*;
use holonic_engine::native_ecology::constitutive_fibre::ResidentNormalEnclosureSection;
use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;
use std::rc::Rc;

type Result<T> = std::result::Result<T, NativeSessionError>;

/// The retained semantic kind of a directed source contact.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Ord, PartialOrd, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum GeneratorSourceContactKind {
    IntraPart,
    DirectJoin,
    RecordedParent,
    RecordedReply,
}

/// One oriented contact between ordered source-cell rows. `from < to` is part of this chart.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GeneratorSourceContact {
    pub from: usize,
    pub to: usize,
    pub kind: GeneratorSourceContactKind,
}

/// Resident pooled source-contact condition chart.
pub struct GeneratorSourceContacts<'c> {
    encoded_rows: usize,
    machine_sites: usize,
    source_blocks: usize,
    injection_indices: Vec<usize>,
    condition_kinds: Vec<GeneratorSourceContactKind>,
    contacts: Vec<GeneratorSourceContact>,
    zero_source: ResidentNormalEnclosureSection<'c>,
    output: ResidentNormalEnclosureSection<'c>,
}

fn identity_phases(count: usize) -> Vec<ExactWavePhaseTransport> {
    vec![ExactWavePhaseTransport::identity(); count]
}

fn opposite_phases(count: usize) -> Vec<ExactWavePhaseTransport> {
    vec![
        ExactWavePhaseTransport::new(
            num_rational::BigRational::from_integer((-1).into()),
            num_rational::BigRational::from_integer(0.into()),
        )
        .expect("unit polarity");
        count
    ]
}

impl<'c> GeneratorSourceContacts<'c> {
    /// Build the pooled contact condition chart. `condition_kinds` fixes the condition-port
    /// order; every declared kind must occur in the supplied contact tape. With no condition
    /// ports, an empty contact tape returns `Ok(None)` and a nonempty tape is refused.
    pub fn new(
        encoded: Rc<ResidentNormalEnclosureSection<'c>>,
        injection_indices: &[usize],
        machine_sites: usize,
        condition_kinds: &[GeneratorSourceContactKind],
        contacts: &[GeneratorSourceContact],
    ) -> Result<Option<Self>> {
        if condition_kinds.is_empty() {
            return if contacts.is_empty() {
                Ok(None)
            } else {
                Err(invalid("source contacts require condition ports"))
            };
        }
        if encoded.rows() == 0
            || machine_sites == 0
            || injection_indices.is_empty()
            || injection_indices.len() > machine_sites
            || injection_indices
                .iter()
                .any(|index| *index >= machine_sites)
            || injection_indices.iter().collect::<BTreeSet<_>>().len() != injection_indices.len()
            || encoded.components() != injection_indices.len().checked_mul(6).unwrap_or(0)
        {
            return Err(invalid("source contact chart extent"));
        }
        let mut kinds = BTreeSet::new();
        for kind in condition_kinds {
            if !kinds.insert(*kind) {
                return Err(invalid("duplicate source contact condition kind"));
            }
        }
        for contact in contacts {
            if contact.from >= contact.to || contact.to >= encoded.rows() {
                return Err(invalid("source contact causal/order extent"));
            }
            if !kinds.contains(&contact.kind) {
                return Err(invalid("source contact kind is not a declared port"));
            }
        }
        let n = encoded.rows();
        let s = injection_indices.len();
        let g = machine_sites;
        let c = condition_kinds.len();
        let output_components = 12usize
            .checked_mul(c)
            .ok_or_else(|| invalid("source contact output extent"))?;
        let edge_count = contacts.len();
        let ng = n
            .checked_mul(g)
            .ok_or_else(|| invalid("source contact event/site extent"))?;
        let ngc = ng
            .checked_mul(c)
            .ok_or_else(|| invalid("source contact event/site/kind extent"))?;
        if ng > u32::MAX as usize
            || ngc > u32::MAX as usize
            || output_components > u32::MAX as usize
        {
            return Err(invalid("source contact resident extent"));
        }
        edge_count
            .checked_mul(6 * s)
            .ok_or_else(|| invalid("source contact edge extent"))?;

        let zero_source = ResidentNormalEnclosureSection::zeros(
            encoded.surface(),
            n,
            encoded.components(),
            encoded.grain(),
        )?;

        let mut kind_outputs = Vec::with_capacity(c);
        for kind in condition_kinds {
            let selected = contacts
                .iter()
                .filter(|contact| contact.kind == *kind)
                .collect::<Vec<_>>();
            let event_difference = if selected.is_empty() {
                zero_source.gather_phase_rows(
                    &(0..n).collect::<Vec<_>>(),
                    &identity_phases(n),
                    encoded.components(),
                )?
            } else {
                let from = selected
                    .iter()
                    .map(|contact| contact.from)
                    .collect::<Vec<_>>();
                let to = selected
                    .iter()
                    .map(|contact| contact.to)
                    .collect::<Vec<_>>();
                let target = encoded.gather_phase_rows(
                    &to,
                    &identity_phases(to.len()),
                    encoded.components(),
                )?;
                let source = encoded.gather_phase_rows(
                    &from,
                    &opposite_phases(from.len()),
                    encoded.components(),
                )?;
                target.sum_same_shape(&source)?.scatter_phase_adjoint(
                    &to,
                    &identity_phases(to.len()),
                    n,
                )?
            };
            let source_rows = event_difference.split_components(s)?;
            let site_rows = Rc::new(source_rows).realify()?;
            let site_addresses = (0..n)
                .flat_map(|event| injection_indices.iter().map(move |site| event * g + *site))
                .collect::<Vec<_>>();
            let site_rows = site_rows.output().scatter_phase_adjoint(
                &site_addresses,
                &identity_phases(site_addresses.len()),
                ng,
            )?;
            kind_outputs.push(site_rows);
        }
        let kind_rows = ResidentNormalEnclosureSection::concatenate_rows(
            &kind_outputs.iter().collect::<Vec<_>>(),
        )?;
        let addresses = (0..n)
            .flat_map(|event| {
                (0..g).flat_map(move |site| (0..c).map(move |kind| kind * ng + event * g + site))
            })
            .collect::<Vec<_>>();
        let output = kind_rows
            .gather_phase_rows(&addresses, &identity_phases(addresses.len()), 12)?
            .pack_components(c)?;
        if output.rows() != ng || output.components() != output_components {
            return Err(invalid("source contact output chart"));
        }
        Ok(Some(Self {
            encoded_rows: n,
            machine_sites: g,
            source_blocks: s,
            injection_indices: injection_indices.to_vec(),
            condition_kinds: condition_kinds.to_vec(),
            contacts: contacts.to_vec(),
            zero_source,
            output,
        }))
    }

    pub fn rows(&self) -> usize {
        self.encoded_rows
    }

    pub fn condition_ports(&self) -> usize {
        self.condition_kinds.len()
    }

    pub fn contacts(&self) -> &[GeneratorSourceContact] {
        &self.contacts
    }

    /// Return event `k` as `G` machine rows, each carrying all declared condition ports.
    pub fn output(&self, event: usize) -> Result<ResidentNormalEnclosureSection<'c>> {
        if event >= self.encoded_rows {
            return Err(invalid("source contact event index"));
        }
        let rows =
            (event * self.machine_sites..(event + 1) * self.machine_sites).collect::<Vec<_>>();
        Ok(self.output.gather_phase_rows(
            &rows,
            &identity_phases(rows.len()),
            self.output.components(),
        )?)
    }

    /// Pull all event/site/condition covectors back to the original `N × (6*S)` encoded tape.
    pub fn pull_back(
        &self,
        all_event_covectors: &ResidentNormalEnclosureSection<'c>,
    ) -> Result<ResidentNormalEnclosureSection<'c>> {
        let c = self.condition_kinds.len();
        let g = self.machine_sites;
        if all_event_covectors.rows() != self.encoded_rows.checked_mul(g).unwrap_or(0)
            || all_event_covectors.components() != 12usize.checked_mul(c).unwrap_or(0)
            || all_event_covectors.grain() != self.output.grain()
            || !std::ptr::eq(all_event_covectors.surface(), self.output.surface())
        {
            return Err(invalid("source contact adjoint chart"));
        }
        let kind_rows = all_event_covectors.split_components(c)?;
        let mut total: Option<ResidentNormalEnclosureSection<'c>> = None;
        for kind_index in 0..c {
            let kind_addresses = (0..self.encoded_rows)
                .flat_map(|event| (0..g).map(move |site| (event * g + site) * c + kind_index))
                .collect::<Vec<_>>();
            let selected = self
                .contacts
                .iter()
                .filter(|contact| contact.kind == self.condition_kinds[kind_index])
                .collect::<Vec<_>>();
            let to = selected
                .iter()
                .map(|contact| contact.to)
                .collect::<Vec<_>>();
            let from = selected
                .iter()
                .map(|contact| contact.from)
                .collect::<Vec<_>>();
            let source_rows = if selected.is_empty() {
                self.zero_source.gather_phase_rows(
                    &(0..self.encoded_rows).collect::<Vec<_>>(),
                    &identity_phases(self.encoded_rows),
                    self.zero_source.components(),
                )?
            } else {
                let source_addresses = (0..self.encoded_rows)
                    .flat_map(|event| {
                        self.injection_indices
                            .iter()
                            .map(move |site| event * g + *site)
                    })
                    .collect::<Vec<_>>();
                let kind = kind_rows.gather_phase_rows(
                    &kind_addresses,
                    &identity_phases(kind_addresses.len()),
                    12,
                )?;
                let source_rows = kind.gather_phase_rows(
                    &source_addresses,
                    &identity_phases(source_addresses.len()),
                    12,
                )?;
                Rc::new(source_rows)
                    .decode_realification()?
                    .output()
                    .pack_components(self.source_blocks)?
            };
            let kind_source = if selected.is_empty() {
                source_rows
            } else {
                let edge = source_rows.gather_phase_rows(
                    &to,
                    &identity_phases(to.len()),
                    source_rows.components(),
                )?;
                let target =
                    edge.scatter_phase_adjoint(&to, &identity_phases(to.len()), self.encoded_rows)?;
                let source = edge.scatter_phase_adjoint(
                    &from,
                    &opposite_phases(from.len()),
                    self.encoded_rows,
                )?;
                target.sum_same_shape(&source)?
            };
            total = Some(match total {
                Some(previous) => previous.sum_same_shape(&kind_source)?,
                None => kind_source,
            });
        }
        total.ok_or_else(|| invalid("source contact adjoint has no condition ports"))
    }
}

#[cfg(test)]
#[path = "machine_source_contacts/tests.rs"]
mod tests;
