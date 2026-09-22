//! Resident source-cell contact contrasts for the fixed generator machine.
//!
//! Source cells and generator sites are distinct populations.  The directed contact kinds and
//! declared ordered offsets enter as one pooled linear condition on the fixed source-role sites;
//! its transpose needs only the declared relation, never the encoded rows.  It does not infer a
//! graph from first moments or turn a source cell into a machine site.

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

/// Resident per-occurrence source-contact condition chart. The moment law consumes the pooled
/// form below; this per-event chart remains the reference layout its tests pin.
#[cfg_attr(not(test), allow(dead_code))]
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

#[cfg_attr(not(test), allow(dead_code))]
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

/// One declared condition port of the ordered source. A kind port pools the recorded directed
/// contacts of that kind; an offset port pools the directed pairs `(k, k+δ)` of the passage.
/// Both are linear in the encoded rows, so neither needs the rows to return its covector.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum GeneratorSourcePort {
    Kind(GeneratorSourceContactKind),
    Offset(usize),
}

/// The declared condition ports: contact kinds first, then offsets, in their declared order.
pub(super) fn source_ports(
    kinds: &[GeneratorSourceContactKind],
    offsets: &[usize],
) -> Result<Vec<GeneratorSourcePort>> {
    let ports = kinds
        .iter()
        .map(|kind| GeneratorSourcePort::Kind(*kind))
        .chain(
            offsets
                .iter()
                .map(|delta| GeneratorSourcePort::Offset(*delta)),
        )
        .collect::<Vec<_>>();
    if ports.iter().collect::<BTreeSet<_>>().len() != ports.len()
        || offsets.iter().any(|delta| *delta == 0)
    {
        return Err(invalid(
            "source condition ports must be distinct nonzero offsets/kinds",
        ));
    }
    Ok(ports)
}

fn validate_pooled(
    rows: usize,
    components: usize,
    injection_indices: &[usize],
    machine_sites: usize,
    ports: &[GeneratorSourcePort],
    contacts: &[GeneratorSourceContact],
) -> Result<()> {
    if rows == 0
        || machine_sites == 0
        || injection_indices.is_empty()
        || injection_indices.len() > machine_sites
        || injection_indices
            .iter()
            .any(|index| *index >= machine_sites)
        || injection_indices.iter().collect::<BTreeSet<_>>().len() != injection_indices.len()
        || components != injection_indices.len().checked_mul(6).unwrap_or(0)
        || rows > u32::MAX as usize
        || machine_sites.checked_mul(ports.len()).is_none()
        || ports.len().checked_mul(12).is_none()
    {
        return Err(invalid("source condition chart extent"));
    }
    for contact in contacts {
        if contact.from >= contact.to || contact.to >= rows {
            return Err(invalid("source contact causal/order extent"));
        }
        if !ports.contains(&GeneratorSourcePort::Kind(contact.kind)) {
            return Err(invalid("source contact kind is not a declared port"));
        }
    }
    Ok(())
}

/// Directed pairs `(from, to)` of one port over a passage of `rows` cells.
fn port_edges(
    port: GeneratorSourcePort,
    contacts: &[GeneratorSourceContact],
    rows: usize,
) -> (Vec<usize>, Vec<usize>) {
    match port {
        GeneratorSourcePort::Kind(kind) => contacts
            .iter()
            .filter(|contact| contact.kind == kind)
            .map(|contact| (contact.from, contact.to))
            .unzip(),
        GeneratorSourcePort::Offset(delta) => (0..rows.saturating_sub(delta))
            .map(|k| (k, k + delta))
            .unzip(),
    }
}

/// Pooled directed source condition, `c_p = Σ_(from→to ∈ p) (E(u_to) − E(u_from))`, placed on
/// the fixed injection-site rows: `G × 12P`. Returns `None` for a field without condition ports.
/// An offset port telescopes to the last δ cells minus the first δ cells under identity phases;
/// that ordered linear reading separates `[a,b]` from `[b,a]` without any bilinear tensor.
pub(super) fn pooled_source_condition<'c>(
    encoded: &ResidentNormalEnclosureSection<'c>,
    injection_indices: &[usize],
    machine_sites: usize,
    ports: &[GeneratorSourcePort],
    contacts: &[GeneratorSourceContact],
) -> Result<Option<ResidentNormalEnclosureSection<'c>>> {
    if ports.is_empty() {
        return if contacts.is_empty() {
            Ok(None)
        } else {
            Err(invalid("source contacts require condition ports"))
        };
    }
    let n = encoded.rows();
    let width = encoded.components();
    validate_pooled(n, width, injection_indices, machine_sites, ports, contacts)?;
    let s = injection_indices.len();
    let mut port_rows = Vec::with_capacity(ports.len());
    for port in ports {
        let (from, to) = port_edges(*port, contacts, n);
        let pooled = if to.is_empty() {
            ResidentNormalEnclosureSection::zeros(encoded.surface(), 1, width, encoded.grain())?
        } else {
            let target = encoded.gather_phase_rows(&to, &identity_phases(to.len()), width)?;
            let source = encoded.gather_phase_rows(&from, &opposite_phases(from.len()), width)?;
            target.sum_same_shape(&source)?.scatter_phase_adjoint(
                &vec![0; to.len()],
                &identity_phases(to.len()),
                1,
            )?
        };
        let site_rows = Rc::new(pooled.split_components(s)?).realify()?;
        port_rows.push(site_rows.output().scatter_phase_adjoint(
            injection_indices,
            &identity_phases(s),
            machine_sites,
        )?);
    }
    let port_major =
        ResidentNormalEnclosureSection::concatenate_rows(&port_rows.iter().collect::<Vec<_>>())?;
    let p = ports.len();
    let addresses = (0..machine_sites)
        .flat_map(|site| (0..p).map(move |port| port * machine_sites + site))
        .collect::<Vec<_>>();
    let output = port_major
        .gather_phase_rows(&addresses, &identity_phases(addresses.len()), 12)?
        .pack_components(p)?;
    if output.rows() != machine_sites || output.components() != 12 * p {
        return Err(invalid("source condition output chart"));
    }
    Ok(Some(output))
}

/// Transpose of `pooled_source_condition`: the `G × 12P` condition covector returns to the
/// `N × 6S` encoded chart. Each cell receives the port covector times its net directed
/// multiplicity; no encoded value is read.
pub(super) fn pull_back_pooled_source_condition<'c>(
    covector: &ResidentNormalEnclosureSection<'c>,
    rows: usize,
    injection_indices: &[usize],
    machine_sites: usize,
    ports: &[GeneratorSourcePort],
    contacts: &[GeneratorSourceContact],
) -> Result<ResidentNormalEnclosureSection<'c>> {
    let s = injection_indices.len();
    let width = s
        .checked_mul(6)
        .ok_or_else(|| invalid("source condition adjoint width"))?;
    validate_pooled(
        rows,
        width,
        injection_indices,
        machine_sites,
        ports,
        contacts,
    )?;
    let p = ports.len();
    if p == 0 || covector.rows() != machine_sites || covector.components() != 12 * p {
        return Err(invalid("source condition adjoint chart"));
    }
    let site_port = covector.split_components(p)?;
    let mut total =
        ResidentNormalEnclosureSection::zeros(covector.surface(), rows, width, covector.grain())?;
    for (index, port) in ports.iter().enumerate() {
        let (from, to) = port_edges(*port, contacts, rows);
        if to.is_empty() {
            continue;
        }
        let addresses = injection_indices
            .iter()
            .map(|site| site * p + index)
            .collect::<Vec<_>>();
        let site_rows = site_port.gather_phase_rows(&addresses, &identity_phases(s), 12)?;
        let pooled = Rc::new(site_rows)
            .decode_realification()?
            .output()
            .pack_components(s)?;
        let edges =
            pooled.gather_phase_rows(&vec![0; to.len()], &identity_phases(to.len()), width)?;
        let target = edges.scatter_phase_adjoint(&to, &identity_phases(to.len()), rows)?;
        let source = edges.scatter_phase_adjoint(&from, &opposite_phases(from.len()), rows)?;
        total = total.sum_same_shape(&target)?.sum_same_shape(&source)?;
    }
    Ok(total)
}

#[cfg(test)]
#[path = "machine_source_contacts/tests.rs"]
mod tests;
