//! Resident source-cell contact contrasts for the fixed generator machine.
//!
//! Source cells and generator sites are distinct populations.  The directed contact kinds and
//! declared ordered offsets enter as one phase-weighted linear condition on the fixed source-role
//! sites: each directed difference is carried by the machine phase at its receiving cell, with
//! the same composite powers as the source moment.  Its transpose needs only the declared
//! relation and those coefficients, never the encoded rows.  It does not infer a
//! graph from first moments or turn a source cell into a machine site.

use super::machine_source::MachineSourceMaps;
use super::machine_transport::MachineValueTransport;
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

pub(super) fn validate_pooled(
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

/// Number of directed contacts pooled into each declared kind port, in declared kind order.
/// This fixed-size count is what a retained comparison keeps of the per-edge relation.
pub(super) fn contact_counts(
    kinds: &[GeneratorSourceContactKind],
    contacts: &[GeneratorSourceContact],
) -> Vec<usize> {
    kinds
        .iter()
        .map(|kind| contacts.iter().filter(|c| c.kind == *kind).count())
        .collect()
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

/// `(injection position i, N−1−to)` for every edge, edge-major: the phase at each edge's cell.
fn edge_phase_rows(to: &[usize], rows: usize, sites: usize) -> Vec<(usize, usize)> {
    to.iter()
        .flat_map(|&t| (0..sites).map(move |i| (i, rows - 1 - t)))
        .collect()
}

/// Per-port, per-symbol phase-weighted sums of the directed condition over the present
/// symbols `a_j` of the passage (sorted, as returned by `symbol_moment_sums`), rows
/// `(p·J + j)·S + i`:
///
/// `D_(p,a,i) = Σ_((from→to) ∈ p, u_to = a) L_(s_i)^(N−1−to) − Σ_((from→to) ∈ p, u_from = a) L_(s_i)^(N−1−to)`.
///
/// Because `c_p` is linear in the encoder table, `c_p = Σ_a D_(p,a,·) I E(a)` exactly: one
/// `|A|×S` operator per port suffices, fixed in `N`; no symbol-pair sum is needed. Its
/// transpose to the table is `Σ_p D_(p,a,i)ᵀ g_(p, s_i)`.
pub(super) fn port_symbol_sums(
    maps: &MachineSourceMaps<'_>,
    symbols: &[usize],
    present: &[usize],
    alphabet: usize,
    ports: &[GeneratorSourcePort],
    contacts: &[GeneratorSourceContact],
) -> Result<Vec<holonics::geometry::RatMat3>> {
    use super::machine_source::{add_matrix, zero_matrix};
    let n = symbols.len();
    let s = maps.injection_indices().len();
    if n != maps.source_count() || alphabet == 0 || symbols.iter().any(|a| *a >= alphabet) {
        return Err(invalid("generator symbol passage"));
    }
    validate_pooled(
        n,
        s * 6,
        maps.injection_indices(),
        maps.site_count(),
        ports,
        contacts,
    )?;
    let symbols = symbols
        .iter()
        .map(|a| present.binary_search(a))
        .collect::<std::result::Result<Vec<_>, _>>()
        .map_err(|_| invalid("generator symbol presence"))?;
    let alphabet = present.len();
    let rows = ports
        .len()
        .checked_mul(alphabet)
        .and_then(|r| r.checked_mul(s))
        .ok_or_else(|| invalid("source condition symbol sum extent"))?;
    let mut sums = Vec::new();
    sums.try_reserve_exact(rows)
        .map_err(|_| invalid("source condition symbol sum allocation"))?;
    sums.resize(rows, zero_matrix());
    let powers = maps.powers()?;
    for (p, port) in ports.iter().enumerate() {
        let (from, to) = port_edges(*port, contacts, n);
        for (&f, &t) in from.iter().zip(&to) {
            for i in 0..s {
                let power = powers
                    .injection(i, n - 1 - t)
                    .ok_or_else(|| invalid("generator moment phase exponent"))?;
                let target = (p * alphabet + symbols[t]) * s + i;
                sums[target] = add_matrix(&sums[target], power, false);
                let source = (p * alphabet + symbols[f]) * s + i;
                sums[source] = add_matrix(&sums[source], power, true);
            }
        }
    }
    Ok(sums)
}

/// Phase-weighted directed source condition on the fixed injection-site rows, `G × 12P`:
///
/// `c_p = Σ_((from→to) ∈ p) L^(N−1−to) I (E(u_to) − E(u_from))`,
///
/// each directed difference carried by the phase at its receiving cell. An offset port `δ`
/// has the edges `(k, k+δ)`, `k < N−δ`, so `c_δ = Σ_k L^(N−1−k−δ) I (E(u_(k+δ)) − E(u_k))`.
/// Under a nonidentity phase its two sums carry different phases and do not telescope; only
/// under the identity phase does it reduce to the last `δ` cells minus the first `δ`. Returns
/// `None` for a field without condition ports.
pub(super) fn phase_weighted_source_condition<'c>(
    maps: &MachineSourceMaps<'c>,
    encoded: &ResidentNormalEnclosureSection<'c>,
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
    let injection_indices = maps.injection_indices();
    let machine_sites = maps.site_count();
    if n != maps.source_count() {
        return Err(invalid("source condition passage length"));
    }
    validate_pooled(n, width, injection_indices, machine_sites, ports, contacts)?;
    let s = injection_indices.len();
    let mut port_rows = Vec::with_capacity(ports.len());
    for port in ports {
        let (from, to) = port_edges(*port, contacts, n);
        if to.is_empty() {
            port_rows.push(ResidentNormalEnclosureSection::zeros(
                encoded.surface(),
                machine_sites,
                12,
                encoded.grain(),
            )?);
            continue;
        }
        let target = encoded.gather_phase_rows(&to, &identity_phases(to.len()), width)?;
        let source = encoded.gather_phase_rows(&from, &opposite_phases(from.len()), width)?;
        let cells = Rc::new(target.sum_same_shape(&source)?.split_components(s)?).realify()?;
        let rows = cells.output().rows();
        let carried = MachineValueTransport::new_with_enclosure(
            cells.output_handle(),
            &(0..rows).collect::<Vec<_>>(),
            maps.phase_coefficients(&edge_phase_rows(&to, n, s), encoded.grain())?,
            maps.enclosure().clone(),
        )?;
        let addresses = to
            .iter()
            .flat_map(|_| injection_indices.iter().copied())
            .collect::<Vec<_>>();
        port_rows.push(carried.output().scatter_phase_adjoint(
            &addresses,
            &identity_phases(rows),
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

/// Transpose of `phase_weighted_source_condition`: the `G × 12P` condition covector returns to
/// the `N × 6S` encoded chart. Edge `(from→to)` of port `p` receives `(L^(N−1−to))ᵀ g_p` at
/// `to` and its negative at `from`; no encoded value is read.
pub(super) fn pull_back_phase_weighted_source_condition<'c>(
    maps: &MachineSourceMaps<'c>,
    covector: &ResidentNormalEnclosureSection<'c>,
    ports: &[GeneratorSourcePort],
    contacts: &[GeneratorSourceContact],
) -> Result<ResidentNormalEnclosureSection<'c>> {
    let rows = maps.source_count();
    let injection_indices = maps.injection_indices();
    let machine_sites = maps.site_count();
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
    let grain = covector.grain();
    let site_port = covector.split_components(p)?;
    let mut total = ResidentNormalEnclosureSection::zeros(covector.surface(), rows, width, grain)?;
    for (index, port) in ports.iter().enumerate() {
        let (from, to) = port_edges(*port, contacts, rows);
        if to.is_empty() {
            continue;
        }
        let addresses = to
            .iter()
            .flat_map(|_| injection_indices.iter().map(|site| site * p + index))
            .collect::<Vec<_>>();
        let edge_rows = addresses.len();
        let gathered = site_port.gather_phase_rows(&addresses, &identity_phases(edge_rows), 12)?;
        // The affine and realification adjoints read only coefficients.
        let zero = Rc::new(ResidentNormalEnclosureSection::zeros(
            covector.surface(),
            edge_rows,
            12,
            grain,
        )?);
        let carried = MachineValueTransport::new_with_enclosure(
            zero,
            &(0..edge_rows).collect::<Vec<_>>(),
            maps.phase_coefficients(&edge_phase_rows(&to, rows, s), grain)?,
            maps.enclosure().clone(),
        )?;
        let edges = Rc::new(carried.pull_back(&gathered)?)
            .decode_realification()?
            .output()
            .pack_components(s)?;
        let target = edges.scatter_phase_adjoint(&to, &identity_phases(to.len()), rows)?;
        let source = edges.scatter_phase_adjoint(&from, &opposite_phases(from.len()), rows)?;
        total = total.sum_same_shape(&target)?.sum_same_shape(&source)?;
    }
    Ok(total)
}

#[cfg(test)]
#[path = "machine_source_contacts/tests.rs"]
mod tests;
